#![allow(dead_code, unused_variables, unused_imports)]

mod cartridge;
mod console;
mod cpu;
mod disassembler;
mod memory;
mod registers;
mod tree;

use cartridge::*;
use color_eyre::Result;
use cpu::*;
use crossbeam::channel::{unbounded, Receiver, Sender};
use memory::*;
use parking_lot::Mutex;
use rayon::prelude::*;
use registers::*;
use std::path::Path;
use std::sync::Arc;
use tree::*;

use crate::disassembler::DisassemblySection;

#[derive(Clone)]
struct Status {
    x: bool,
    m: bool,
}

struct Job {
    section: Arc<Vec<u8>>,
    start: usize,
    parent: usize,
    is_root: bool,
    is_subroutine: bool,
    status: Status,
    status_stack: Vec<Status>,
}

#[allow(unreachable_code)]
fn process_section(
    section: Arc<Vec<u8>>,
    start: usize,
    parent: usize,
    is_subroutine: bool,
    status: Status,
    status_stack: Vec<Status>,
    sender: Sender<Job>,
) -> DisassemblySection {
    let mut pc = start;
    loop {
        let instr = section[pc];
        let context = cpu::decode_instruction_noaddr(instr, pc as u32).unwrap();

        let (status_stack_new, status_new) = match context.opcode {
            OpCode::PHP => {
                let mut new_status = status_stack.clone();
                new_status.push(status);
                (new_status, status)
            }
            OpCode::PLP => {
                let mut new_status = status_stack.clone();
                let popped_status = new_status.pop().unwrap();
                (new_status, popped_status)
            }
            OpCode::RTI => {
                let mut new_status = status_stack.clone();
                let popped_status = new_status.pop().unwrap();
                (new_status, popped_status)
            }
            OpCode::REP => {
                let status_byte = section[pc + 1];
                let new_status = Status {
                    x: if (status_byte & 0b00010000) != 0 {
                        false
                    } else {
                        status.x
                    },
                    m: if (status_byte & 0b00100000) != 0 {
                        false
                    } else {
                        status.m
                    },
                };
                (status_stack, new_status)
            }
            OpCode::SEP => {
                let status_byte = section[pc + 1];
                let new_status = Status {
                    x: (status_byte & 0b00010000) != 0,
                    m: (status_byte & 0b00100000) != 0,
                };
                (status_stack, new_status)
            }
        };

        pc += context.length(status.m, status.x);
    }

    todo!()
}

fn main() -> Result<()> {
    let cart = load_rom(Path::new("./rom.sfc"))?;

    let rom = Arc::new(cart.rom_data.clone());

    let mut tree = DisassemblyTree::new();

    let tree_ref = Arc::new(Mutex::new(tree));

    let (sender, reciever) = unbounded::<Job>();

    sender.send(Job {});

    rayon::scope(move |s| {
        for _ in 0..rayon::current_num_threads() {
            let sender = sender.clone();
            let reciever = reciever.clone();
            let tree_ref = tree_ref.clone();
            s.spawn(move |_| {
                while let Ok(job) = reciever.recv() {
                    let new_disassembly = process_section(
                        job.section,
                        job.start,
                        job.parent,
                        job.is_subroutine,
                        job.status,
                        job.status_stack,
                        sender.clone(),
                    );
                    let mut tree_lock = tree_ref.lock();
                    let new_node = tree_lock.tree.insert_child(job.parent, new_disassembly);
                    if job.is_subroutine {
                        tree_lock.add_subroutine(job.start, new_node);
                    }
                }
            });
        }
    });

    Ok(())
}
