// ty_int_ref_scalar_64_extract -> value is a 64 bit scalar type
// fits_in_... -> value has certain bitwidth but may be a vector, though this is irrelevant to us
// icmp_zero_cond : Equal, SGE, SGT, SLE, SLT

use std::str::FromStr;

use std::fmt::Formatter;
use std::fmt::{Error, Display};

use cranelift_isle::ast::{Def, Pattern, Ident};
use cranelift_isle::sema::{TypeEnv, TermEnv};
use cranelift_codegen::ir::{Opcode};

#[derive(Debug, Clone, PartialEq)]
enum InsnType {
    BV8,
    BV16,
    BV32,
    BV64,
}

impl InsnType {
    pub fn bitwidth_of(&self) -> u32 {
        match self {
            InsnType::BV8 => 8,
            InsnType::BV16 => 16,
            InsnType::BV32 => 32,
            InsnType::BV64 => 64,
        }
    }
}

impl Display for InsnType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InsnType::BV8 => write!(f, "i8"),
            InsnType::BV16 => write!(f, "i16"),
            InsnType::BV32 => write!(f, "i32"),
            InsnType::BV64 => write!(f, "i64"),
        }
    }
}

fn all_types() -> Vec<InsnType> {
    return vec!(InsnType::BV8, InsnType::BV16, InsnType::BV32, InsnType::BV64)
}

#[derive(Clone)]
enum PatternPart {
    Insn(Opcode, Option<Vec<InsnType>>),
    Var(String),
    Imm12Var(Box<PatternPart>),
    ExtendedVar(Box<PatternPart>),
    Wildcard,
    Other(Ident),
    And,
    BindPattern(String),
    BoolConst(bool),
    IntConst(i128),
    PrimConst(String),
}

#[derive(Clone)]
struct Pattern2Sygus {
    pattern: PatternPart,
    args: Vec<Box<Pattern2Sygus>>,
}

fn opcode_allowed(opcode: Opcode) -> bool {
    matches!(opcode, Opcode::Icmp | Opcode::Smin 
        | Opcode::Umin | Opcode::Smax | Opcode::Umax 
        | Opcode::Bitselect | Opcode::Iadd 
        | Opcode::Isub | Opcode::Ineg | Opcode::Iabs
        | Opcode::Imul | Opcode::Udiv
        | Opcode::Sdiv | Opcode::Urem
        | Opcode::Srem | Opcode::Band
        | Opcode::Bor  | Opcode::Bxor 
        | Opcode::Bnot | Opcode::Rotl 
        | Opcode::Rotr | Opcode::Ishl 
        | Opcode::Ushr | Opcode::Sshr 
        | Opcode::Clz | Opcode::Cls | Opcode::Ctz | Opcode::Popcnt
        | Opcode::Uextend | Opcode::Sextend) 
}

impl Display for PatternPart {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result <(), Error> {
        match self {
            PatternPart::Var(id) => write!(f, "var_{}", id),
            PatternPart::Imm12Var(id) => write!(f, "imm_12_{}", id),
            PatternPart::ExtendedVar(id) => write!(f, "x_{}", id),
            PatternPart::Wildcard => write!(f, "wildcard"),
            PatternPart::Insn(i, ty) => write!(f, "{} {:?}", i, ty),
            PatternPart::Other(id) => write!(f, "{}", id.0),
            PatternPart::And => write!(f, "and "),
            PatternPart::BindPattern(id) => write!(f, "{} = ", id),
            PatternPart::BoolConst(b) => write!(f, "b{}", b),
            PatternPart::IntConst(i) => write!(f, "i{}", i),
            PatternPart::PrimConst(s) => write!(f, "p{}", s),
        }
    }
}

impl PatternPart {
    fn explode_extended_var(&self) -> Vec::<String> {
        let mut out = Vec::new();

            match &self {
                PatternPart::ExtendedVar(_) => { 
                    let smaller_types = vec!(InsnType::BV8, InsnType::BV16, InsnType::BV32);

                    for ty in smaller_types {
                        let zext_string: String = format!("({} ((_ zero_extend {}) value))", ty, 64 - ty.bitwidth_of());
                        let sext_string: String = format!("({} ((_ sign_extend {}) value))", ty, 64 - ty.bitwidth_of());

                        out.push(zext_string);
                        out.push(sext_string);
                    }

                    out
                }
                _ => { panic!("Pattern needs to be an extended var, got {}", &self) }
        }
    }
}

// Helper function for the as_sygus_pattern function
fn add_or_return_string(vector: Vec::<String>, string: String) -> Vec::<String> {
    if vector.is_empty() {
        vec!(string)
    } else {
        Vec::from_iter(vector.iter().map(|x| format!("{} {}", x, string)))
    }
}

impl Pattern2Sygus {
    fn fmt_with_indent(&self, f: &mut Formatter<'_>, depth: usize) -> Result<(), Error> {
        writeln!(f, "{}", self.pattern)?;

        for arg in self.args.iter() {
            write!(f, "{}", "\t".repeat(depth + 1))?;
            arg.fmt_with_indent(f, depth + 1)?;
       }

       // writeln!(f, "{}", "\t".repeat(depth + 1))?;

        Result::Ok(())
    }

    fn as_sygus_pattern(&self, input_strings: Vec::<String>, ty: &InsnType) -> Vec::<String> {
        let mut out_vec = Vec::new();

        match &self.pattern {
            PatternPart::Insn(op, types) => {
                let types = types.clone().expect("Expected a valid type");
                assert!(types.iter().any(|x| x == ty));
                let out_s = format!("({} {}", ty, op);
                out_vec = add_or_return_string(input_strings, out_s);
             
                for arg in &self.args {
                    out_vec = arg.as_sygus_pattern(out_vec, ty);
                }
                out_vec = add_or_return_string(out_vec, ")".to_owned())
            }
            PatternPart::Var(_) => {
                out_vec = add_or_return_string(input_strings, format!("({} value)", ty))
            }
            PatternPart::Wildcard => { 
                out_vec = add_or_return_string(input_strings, format!("({} value)", ty))
            }
            PatternPart::Imm12Var(_) => { 
                out_vec = add_or_return_string(input_strings, format!("({} ((_ zero_extend {}) ((_ extract 11 0) value)))", ty, ty.bitwidth_of() - 12)); 
            }
            PatternPart::ExtendedVar(_) => {
                let mut new_paths = Vec::new();

                for o in &input_strings {
                    for x in &self.pattern.explode_extended_var() {
                        new_paths.push(format!("{} {}", o, x));
                    }
                }

                out_vec = new_paths;
            }
            _ => { out_vec = add_or_return_string(input_strings, format!("{}", self.pattern)) }
        }

        out_vec
    }
}

impl Display for Pattern2Sygus {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result <(), Error> {
        self.fmt_with_indent(f, 0)?;
        Result::Ok(())
    }
}

/**
 * We require a valid pattern to be propertly typed 
 * (i.e. all (sub)-instructions) need to have one
 * at least one type
*/
fn is_valid_pattern(p: &Pattern2Sygus) -> bool {
    match &p.pattern {
        PatternPart::Insn(_, types) => {
            match types {
                None => false,
                Some(_) => !p.args.is_empty() && p.args.iter().fold(true, |acc, x| acc && is_valid_pattern(x))
            }
        }
        PatternPart::And => false,
        PatternPart::BindPattern(_) => false,
        _  => true
    }
}

fn parse_type(t: &Pattern) -> Option<Vec<InsnType>> {
    match t {
        Pattern::Term{sym: id, args: _, pos: _} => {
            match id.0.as_str() {
                    "ty_int_ref_scalar_64_extract" => Some(vec!(InsnType::BV64)),
                    "fits_in_8" => Some(vec!(InsnType::BV8)),
                    "fits_in_16" => Some(vec!(InsnType::BV8, InsnType::BV16)),
                    "fits_in_32" => Some(vec!(InsnType::BV8, InsnType::BV16, InsnType::BV32)),
                    "fits_in_64" => Some(vec!(InsnType::BV8, InsnType::BV16, InsnType::BV32, InsnType::BV64)),
                    _ => { log::warn!("Unrecognized string type: {}", id.0); None }
            }
        }
        Pattern::ConstPrim { val, pos: _ } => {
            match val.0.as_str() {
                    "I8" => Some(vec!(InsnType::BV8)),
                    "I16" => Some(vec!(InsnType::BV16)),
                    "I32" => Some(vec!(InsnType::BV32)),
                    "I64" => Some(vec!(InsnType::BV64)),
                    _ => { log::warn!("Unrecognized prim type: {}", val.0); None }
            }
        }
        Pattern::And { subpats, pos: _ } => {
            subpats.first().map_or(None, |x| parse_type(x))
        }
        Pattern::Wildcard{pos: _} => Some(all_types()),
        _ => { log::warn!("Unrecognized type: {:?}", t); None }
    }
}

fn handle_term(t: &Pattern) -> Option<Pattern2Sygus> {
    match t {
       Pattern::Term{sym: id, args, pos: _} => {
           match Opcode::from_str(id.0.as_str()) {
                Ok(opcode) => { 
                   if !opcode_allowed(opcode) { /*print!(" unsopportaed {} :(", opcode);*/ return None; }
                   let ty = parse_type(&args[0]);

                   let mut pattern_out = Pattern2Sygus{ pattern: PatternPart::Insn(opcode, ty), args: Vec::new() };

                   if id.0 == "ishl" {
                       match args.first().map(|x| handle_term(x)).flatten() {
                            Some(arg) => {
                                match arg.pattern {
                                    PatternPart::Wildcard => pattern_out.args.push(Box::new(arg)),
                                    _ => ()
                                } 
                            },
                            None => ()
                       }
                   }

                   for arg in args.iter().skip(1) {
                       if let Some(arg) = handle_term(arg) {
                           pattern_out.args.push(Box::new(arg));
                       }
                   }

                   return Some(pattern_out);
                }
                _ => {
                    match id.0.as_str() {
                       "imm12_from_value" => {
                           match args.first().map(handle_term).flatten() {
                               Some (var) => Some(Pattern2Sygus { pattern: PatternPart::Imm12Var(Box::new(var.pattern)), args: Vec::new() }),
                               None => { log::error!("Could not get argument of imm12_from_value ({:?})", t); None }
                           }
                       }
                       "extended_value_from_value" => {
                           match args.first().map(handle_term).flatten() {
                               Some (var) => Some(Pattern2Sygus { pattern: PatternPart::ExtendedVar(Box::new(var.pattern)), args: Vec::new() }),
                               None => { log::error!("Could not get argument of extended_value_from_value ({:?})", t); None }
                           }
                       }
                       _ => {
                            let mut pattern_args = Vec::new();

                           for arg in args {
                                if let Some(arg) = handle_term(arg) {
                                    pattern_args.push(Box::new(arg));
                                }
                           }

                           return Some(Pattern2Sygus { pattern: PatternPart::Other(id.clone()), args: pattern_args }); 
                       }
                    }
                }
           }
       }
       Pattern::Var { var: id, pos: _ } => {
           return Some(Pattern2Sygus { pattern: PatternPart::Var(id.0.clone()), args: Vec::new() });
       }
       Pattern::Wildcard { pos: _ } => {
           return Some(Pattern2Sygus { pattern: PatternPart::Wildcard, args: Vec::new() });
       }
       Pattern::And { subpats, pos: _ } => {
           let mut and_args = Vec::new();

           for arg in subpats {
               if let Some(arg) = handle_term(arg) {
                   and_args.push(Box::new(arg));
               }
           }

           return Some(Pattern2Sygus { pattern: PatternPart::And, args: and_args})
       }
       Pattern::BindPattern { var, subpat, pos: _ } => {
           let mut args = Vec::new();
           if let Some(arg) = handle_term(subpat) {
               args.push(Box::new(arg));
           }

           return Some(Pattern2Sygus { pattern: PatternPart::BindPattern(var.0.clone()), args: args });
       }
       Pattern::ConstBool { val, pos: _ } => {
           return Some(Pattern2Sygus { pattern: PatternPart::BoolConst(val.clone()), args: Vec::new() });
       }
       Pattern::ConstInt { val, pos: _ } => {
           return Some(Pattern2Sygus { pattern: PatternPart::IntConst(val.clone()), args: Vec::new() });
       }
       Pattern::ConstPrim { val, pos: _ } => {
           return Some(Pattern2Sygus { pattern: PatternPart::PrimConst(val.0.clone()), args: Vec::new() });
       }
      _ => { log::warn!(" other: {:?}", t); return None; }
    }
}

pub fn pattern2sygus(defs: Vec<Def>, tyenv: &TypeEnv, termenv: &TermEnv) {
    for def in defs {
        match def {
            Def::Rule(rule) => {
                match rule.pattern {
                    Pattern::Term{sym: id, args, pos: _} => {
                        if id.0 != "lower" { continue; }

                        let inner_term = args[0].clone();
                        let pattern2sygus = handle_term(&inner_term);

                        if let Some(pattern2sygus) = pattern2sygus {
                            if is_valid_pattern(&pattern2sygus) { 
                                // println!("{}", pattern2sygus); 

                                match &pattern2sygus.pattern {
                                    PatternPart::Insn(_, Some(types)) => {
                                        for ty in types {
                                            for string in pattern2sygus.as_sygus_pattern(Vec::new(), ty) {
                                                println!("({})", string);
                                            }
                                        }
                                        ()
                                    }
                                    _ => ()
                                }
                            }
                        }
                    }
                    _ => continue
                }
            }
            _ => continue
        }
    }
}

