use abc_rs::Abc;
use aig::Aig;
use std::{env, mem::take, time::Duration};
use crate::options::Options;
use crate::options::AbcPreMode;
use serde_json; // 添加 serde_json 依赖

fn preprocess((f, mode_json): (String, String)) {
    // 反序列化 mode_json 为 AbcPreMode
    let mode: AbcPreMode = serde_json::from_str(&mode_json).expect("Failed to deserialize AbcPreMode");
    println!("debug: mode = {:?}", mode);

    let mut aig = Aig::from_file(&f);
    let num_input = aig.inputs.len();
    let num_latchs = aig.latchs.len();
    let num_constraints = aig.constraints.len();
    aig.outputs.push(aig.bads[0]);
    aig.bads.clear();
    let latchs = take(&mut aig.latchs);
    for l in latchs.iter() {
        aig.inputs.push(l.input);
        aig.outputs.push(l.next);
    }
    for c in take(&mut aig.constraints) {
        aig.outputs.push(c);
    }
    assert!(aig.inputs.len() == num_input + num_latchs);
    assert!(aig.outputs.len() == 1 + num_latchs + num_constraints);
    let mut abc = Abc::new();
    abc.read_aig(&aig);
    drop(aig);

    match mode {
        AbcPreMode::Mode1 => {
            println!("Preprocessing with Mode1: strash, scleanup, drw");
            abc.execute_command("strash; scleanup -m; drw;");
        }
        AbcPreMode::Mode2 => {
            println!("Preprocessing with Mode2: &get -n; &gla -T 500 -F 200 -v; &gla_derive; &put; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; scorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v; lcorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v;");
            abc.execute_command("&get -n; &gla -T 500 -F 200 -v; &gla_derive; &put; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; scorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v; lcorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v;");
        }
        AbcPreMode::Mode3 => {
            println!("Preprocessing with Mode3: &get -n; &gla -T 30 -F 20 -v; &gla_derive; &put; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; scorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v; lcorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v;");
            abc.execute_command("&get -n; &gla -T 30 -F 20 -v; &gla_derive; &put; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; scorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v; lcorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v;");
        }
        AbcPreMode::Mode4 => {
            println!("Preprocessing with Mode4: &get -n; &gla -T 100 -F 50 -v; &gla_derive; &put; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; dc2 -v; scorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v; lcorr; dc2 -v; dc2 -v; dc2 -v; dc2 -v;");
            abc.execute_command("strash; balance; drw; drf; balance; drf;");
        }
        _ => {
            println!("Preprocessing with default mode: &get; &fraig -y; &put; orchestrate;");
            abc.execute_command("&get; &fraig -y; &put; orchestrate;");
        }
    }

    let mut abc_aig = abc.write_aig();
    for (i, li) in latchs.iter().enumerate() {
        let mut l = *li;
        l.input = abc_aig.inputs[num_input + i];
        l.next = abc_aig.outputs[1 + i];
        abc_aig.latchs.push(l);
    }
    abc_aig.inputs.truncate(num_input);
    for i in 0..num_constraints {
        abc_aig
            .constraints
            .push(abc_aig.outputs[1 + num_latchs + i]);
    }
    abc_aig.bads.push(abc_aig.outputs[0]);
    abc_aig.outputs.clear();
    assert!(abc_aig.inputs.len() == num_input);
    assert!(abc_aig.latchs.len() == num_latchs);
    assert!(abc_aig.constraints.len() == num_constraints);

    abc_aig.to_file(&f, false);
}

#[allow(unused)]
pub fn abc_preprocess(mut aig: Aig, options: &Options) -> Aig {
    let dir = match env::var("RIC3_TMP_DIR") {
        Ok(d) => d,
        Err(_) => "/tmp/rIC3".to_string(),
    };
    let tmpfile = tempfile::NamedTempFile::new_in(dir).unwrap();
    let path = tmpfile.path().as_os_str().to_str().unwrap();
    aig.to_file(path, false);

    // 序列化 AbcPreMode 为 JSON 字符串
    let mode_json = serde_json::to_string(&options.preprocess.abc_pre_mode)
        .expect("Failed to serialize AbcPreMode");

    let mut join = procspawn::spawn((path.to_string(), mode_json), preprocess);

    if join.join_timeout(Duration::from_secs(5)).is_ok() {
        aig = Aig::from_file(path);
    } else {
        println!("abc preprocess timeout");
        let _ = join.kill();
    }
    drop(tmpfile);

    aig
}