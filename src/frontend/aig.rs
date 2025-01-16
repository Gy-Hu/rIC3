use super::abc::abc_preprocess;
use crate::options;
use aig::Aig;
use std::collections::{HashMap, HashSet};

pub fn aig_preprocess(aig: &Aig, options: &options::Options) -> (Aig, HashMap<usize, usize>) {
    let (mut aig, mut remap) = aig.coi_refine();
    if !(options.preprocess.no_abc
        || matches!(options.engine, options::Engine::IC3) && options.ic3.inn)
    {
        let mut remap_retain = HashSet::new();
        remap_retain.insert(0);
        for i in aig.inputs.iter() {
            remap_retain.insert(*i);
        }
        for l in aig.latchs.iter() {
            remap_retain.insert(l.input);
        }
        remap.retain(|x, _| remap_retain.contains(x));
        aig = abc_preprocess(aig, options);
        let remap2;
        (aig, remap2) = aig.coi_refine();
        remap = {
            let mut remap_final = HashMap::new();
            for (x, y) in remap2 {
                if let Some(z) = remap.get(&y) {
                    remap_final.insert(x, *z);
                }
            }
            remap_final
        }
    }
    aig.constraints.retain(|e| !e.is_constant(true));
    (aig, remap)
}
