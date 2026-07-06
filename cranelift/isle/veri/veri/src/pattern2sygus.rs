// ty_int_ref_scalar_64_extract -> value is a 64 bit scalar type
// fits_in_... -> value has certain bitwidth but may be a vector, though this is irrelevant to us


use std::str::FromStr;

use std::fmt::Formatter;
use std::fmt::{Error, Display};

use cranelift_isle::ast::{Def, Pattern, Ident};
use cranelift_isle::sema::{TypeEnv, TermEnv};
use cranelift_codegen::ir::{Opcode};

enum PatternPart {
    Insn(Opcode),
    Var(String),
    Wildcard,
    Other(Ident),
    And,
    BindPattern(String),
    BoolConst(bool),
    IntConst(i128),
    PrimConst(String),
}

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
            PatternPart::Wildcard => write!(f, "wildcard"),
            PatternPart::Insn(i) => write!(f, "{}", i),
            PatternPart::Other(id) => write!(f, "{}", id.0),
            PatternPart::And => write!(f, "and "),
            PatternPart::BindPattern(id) => write!(f, "{} = ", id),
            PatternPart::BoolConst(b) => write!(f, "b{}", b),
            PatternPart::IntConst(i) => write!(f, "i{}", i),
            PatternPart::PrimConst(s) => write!(f, "p{}", s),
        }
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
}

impl Display for Pattern2Sygus {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result <(), Error> {
        self.fmt_with_indent(f, 0)?;
        Result::Ok(())
    }
}

fn handle_term(t: &Pattern) -> Option<Pattern2Sygus> {
    match t {
       Pattern::Term{sym: id, args: args, pos: _} => {
           match Opcode::from_str(id.0.as_str()) {
                Ok(opcode) => { 
                   if !opcode_allowed(opcode) { /*print!(" unsopportaed {} :(", opcode);*/ return None; }
                   let mut pattern_out = Pattern2Sygus{ pattern: PatternPart::Insn(opcode), args: Vec::new() };

                   for arg in args.iter() {
                       if let Some(arg) = handle_term(arg) {
                           pattern_out.args.push(Box::new(arg));
                       }
                   }

                   return Some(pattern_out);
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
      _ => { /*print!(" other: {:?}", t);*/ return None; }
    }
}

pub fn pattern2sygus(defs: Vec<Def>, tyenv: &TypeEnv, termenv: &TermEnv) {
    for def in defs {
        match def {
            Def::Rule(rule) => {
                match rule.pattern {
                    Pattern::Term{sym: id, args: args, pos: pos} => {
                        if id.0 != "lower" { continue; }

                        let inner_term = args[0].clone();
                        let pattern2sygus = handle_term(&inner_term);

                        if let Some(pattern2sygus) = pattern2sygus {
                            println!("{}", pattern2sygus);
                        }
                    }
                    _ => continue
                }
            }
            _ => continue
        }
    }
}


