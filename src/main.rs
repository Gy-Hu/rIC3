#![feature(ptr_metadata)]

use aig::Aig;
use btor::btor_to_aiger;
use clap::Parser;
use rIC3::{
    bmc::BMC,
    frontend::aig::aig_preprocess,
    general,
    kind::Kind,
    options::{self, Options},
    portfolio::Portfolio,
    transys::Transys,
    verify::{check_certifaiger, check_witness, verify_certifaiger},
    Engine, IC3,
};
use std::{
    mem::{self, transmute},
    process::exit,
    ptr, usize,
};

fn main() {
    procspawn::init();
    let mut options = Options::parse();
    let verbose = options.verbose;
    if verbose > 0 {
        println!("the model to be checked: {}", options.model);
    }
    let mut aig = if options.model.ends_with(".btor") || options.model.ends_with(".btor2") {
        options.certify_path = None;
        options.certify = false;
        btor_to_aiger(&options.model)
    } else {
        Aig::from_file(&options.model)
    };
    if aig.bads.len() + aig.outputs.len() == 0 {
        println!("warning: no property to be checked");
        verify_certifaiger(&aig, &options);
        exit(20);
    }
    let mut engine: Box<dyn Engine> = if let options::Engine::Portfolio = options.engine {
        Box::new(Portfolio::new(options.clone()))
    } else {
        let (aig, restore) = aig_preprocess(&aig, &options);
        let mut ts = Transys::from_aig(&aig, &restore);
        let pre_lemmas = vec![];
        if options.preprocess.sec {
            panic!("sec not support");
        }
        let ic3 = matches!(options.engine, options::Engine::IC3);
        ts = ts.simplify(&[], ic3, !ic3);
        let mut engine: Box<dyn Engine> = match options.engine {
            options::Engine::IC3 => Box::new(IC3::new(options.clone(), ts, pre_lemmas)),
            options::Engine::GIC3 => Box::new(general::IC3::new(options.clone(), ts)),
            options::Engine::Kind => Box::new(Kind::new(options.clone(), ts)),
            options::Engine::BMC => Box::new(BMC::new(options.clone(), ts)),
            _ => unreachable!(),
        };
        if options.interrupt_statistic {
            let e: (usize, usize) =
                unsafe { transmute((engine.as_mut() as *mut dyn Engine).to_raw_parts()) };
            let _ = ctrlc::set_handler(move || {
                let e: *mut dyn Engine = unsafe {
                    ptr::from_raw_parts_mut(transmute::<usize, *mut ()>(e.0), transmute(e.1))
                };
                let e = unsafe { &mut *e };
                e.statistic();
                exit(124);
            });
        }
        engine
    };
    let res = engine.check();
    match res {
        Some(true) => check_certifaiger(&mut engine, &mut aig, &options),
        Some(false) => check_witness(&mut engine, &aig, &options),
        _ => (),
    }
    if let options::Engine::Portfolio = options.engine {
        drop(engine);
    } else {
        mem::forget(engine);
    }
    if let Some(res) = res {
        if verbose > 0 {
            println!("result: {res}");
        }
        exit(if res { 20 } else { 10 });
    } else {
        if verbose > 0 {
            println!("result: unknown");
        }
        exit(0)
    }
}
