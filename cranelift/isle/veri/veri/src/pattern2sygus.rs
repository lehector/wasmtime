use cranelift_isle::ast::{Ident, Pattern};
use cranelift_isle::sema::TypeEnv;

pub fn pattern2sygus(tyenv: TypeEnv, pattern: Pattern) {
    match pattern {
        Pattern::Term{sym, args, pos} => {
            if sym.0 != "lower" {
                log::warn!("expected first term to be 'lower', but got {:?} @ {:?}", sym.0, pos);
                return;
            }

            println!("{:?} {:?}", sym.0, tyenv.);
        }
        _ => { panic!("expected first term to be 'lower', but got {:?}", pattern); }
    }
}