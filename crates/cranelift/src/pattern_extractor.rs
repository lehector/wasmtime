use std::fmt::{Formatter, Error, Display, Debug};
use cranelift_codegen::ir::{Layout, Opcode, DataFlowGraph, Block, Inst, ValueDef, Type, condcodes::IntCC, InstructionData};

// Pattern DataFlowGraph
// just a very simple tree data structure that associates opcodes with a list of arguments, which
// themselves are Some pdfg nodes, or None if the argument should be an arbitrary BitVector
#[derive(Clone)]
pub struct PDFG {
    inst: Inst,
    op: Opcode,
    ty: Type,
    cmp: Option<IntCC>,
    args: Box<Vec<Result<PDFG, Type>>>
}

impl PartialEq for PDFG {
    fn eq(&self, other: &Self) -> bool {
        return self.op == other.op && self.ty == other.ty && self.cmp == other.cmp && *self.args == *other.args    
    }
}

impl PDFG {
    fn fmt_mach(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "({} {} {}", self.ty, self.op, self.cmp.map_or("", |x| x.to_static_str()))?;
        for arg in self.args.iter() {
            write!(f, " ")?;

            match arg {
                Ok(x) => {
                    x.fmt_mach(f)?;
                }
                Err(ty) => {
                    write!(f, "({} value)", ty)?;
                }
            }
        }
        write!(f, ")")?;

        Result::Ok(())
    }

    fn fmt_with_indent(&self, f: &mut Formatter<'_>, depth: usize) -> Result<(), Error> {
        writeln!(f, "({} {} {}", self.ty, self.op, self.cmp.map_or("", |x| x.to_static_str()))?;

        for arg in self.args.iter() {
            write!(f, "{}", "\t".repeat(depth + 1))?;

            match arg {
                Ok(x) => {
                    x.fmt_with_indent(f, depth + 1)?;
                }
                Err(ty) => {
                    writeln!(f, "({} value)", ty)?;
                }
            }
        }
        writeln!(f, "{})", "\t".repeat(depth + 1))?;

        Result::Ok(())
    }
}

impl Debug for PDFG {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result <(), Error> {
        writeln!(f, "(")?;
        self.fmt_with_indent(f, 0)?;
        writeln!(f, ")")?;
        Result::Ok(())
    }
}

impl Display for PDFG {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result <(), Error> {
        write!(f, "(")?;
        self.fmt_mach(f)?;
        write!(f, ")")?;
        Result::Ok(())
    }
}

fn opcode_allowed(opcode: Opcode) -> bool {
    matches!(opcode, Opcode::Icmp | Opcode::Smin 
        | Opcode::Umin | Opcode::Smax | Opcode::Umax | Opcode::Iconst
        | Opcode::Bitselect | Opcode::Iadd 
        | Opcode::Isub | Opcode::Ineg | Opcode::Iabs
        | Opcode::ImulImm | Opcode::Imul | Opcode::Udiv
        | Opcode::Sdiv | Opcode::Urem
        | Opcode::Srem | Opcode::Band
        | Opcode::Bor  | Opcode::Bxor 
        | Opcode::Bnot | Opcode::BandNot | Opcode::Rotl 
        | Opcode::Rotr | Opcode::Ishl 
        | Opcode::Ushr | Opcode::Sshr 
        | Opcode::Clz | Opcode::Cls | Opcode::Ctz | Opcode::Popcnt
        | Opcode::Uextend | Opcode::Sextend) 
}

fn get_maybe_cmp_code(inst: InstructionData) -> Option<IntCC> {
    match inst {
        InstructionData::IntCompare { opcode: _, args: _, cond } => Some(cond),
        InstructionData::IntCompareImm { opcode: _, arg: _, cond, imm: _ } => Some(cond),
        _ => None
    }
}

const MAX_PATTERN_SIZE: u32 = 4;

fn extract_pattern_from_insts(pdfg: &mut PDFG, layout: &Layout, dfg: &DataFlowGraph, visited_insts: &mut Vec<Inst>, size: u32) {
    let mut size = size;
    let inst = pdfg.inst;

    for arg in dfg.insts[inst].arguments(&dfg.value_lists).into_iter() {
       let ty = dfg.value_type(*arg);

       match dfg.value_def(*arg) {
           ValueDef::Result(inst, _) => {
                visited_insts.push(inst);

                let opcode = dfg.insts[inst].opcode();
                if !opcode_allowed(opcode) || size >= MAX_PATTERN_SIZE { pdfg.args.push(Err(ty)); continue };

                let mut arg_pdfg = PDFG {
                    inst: inst,
                    op: opcode,
                    ty: ty,
                    cmp: get_maybe_cmp_code(dfg.insts[inst]),
                    args: Box::new(Vec::new())
                };

                size = size + 1;
                extract_pattern_from_insts(&mut arg_pdfg, &layout, &dfg, visited_insts, size);

                pdfg.args.push(Ok(arg_pdfg))
           }
           _ => { pdfg.args.push(Err(ty)); continue; }
       }
    }
}

fn extract_patterns_of_block(block: Block, layout: &Layout, dfg: &DataFlowGraph) -> Vec<PDFG> {
    let mut pdfg_buf = Vec::new();
    let mut visited_insts = Vec::new();

    for inst in layout.block_insts(block).rev() {
        if visited_insts.contains(&inst) {
            continue; 
        }
        
        let inst_data = dfg.insts[inst];
        let opcode = inst_data.opcode();
        if !opcode_allowed(opcode) {
             visited_insts.push(inst);
             continue;
        }

        assert!(dfg.inst_results(inst).len() == 1, "expected instruction to have exactly 1 value");
        let inst_value = dfg.first_result(inst);

        let mut pdfg = PDFG {
            inst: inst,
            op: opcode,
            ty: dfg.value_type(inst_value),
            cmp: get_maybe_cmp_code(inst_data),
            args: Box::new(Vec::new())
        };

        visited_insts.push(inst);

        extract_pattern_from_insts(&mut pdfg, &layout, &dfg, &mut visited_insts, 0);
        pdfg_buf.push(pdfg);
    }

    pdfg_buf
}

pub fn extract_patterns_of_function(layout: &Layout, dfg: &DataFlowGraph) -> Vec<PDFG> {
   let mut pdfg_buf = Vec::new();

   // Start by going through all blocks
   for block in layout.blocks() {
       for new_pdfg in extract_patterns_of_block(block, layout, dfg) {
           if !pdfg_buf.iter().any(|x| *x == new_pdfg) {
                pdfg_buf.push(new_pdfg)
           }
       }
   }
    
   pdfg_buf
}

