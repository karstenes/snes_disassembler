#![allow(dead_code, unused_variables, unused_imports)]

mod cartridge;
mod console;
mod cpu;
mod disassembler;
mod memory;
mod registers;
mod tree;

use cartridge::*;
use cpu::*;
use crossbeam::channel::{unbounded, Sender};
use memory::*;
use registers::*;
use std::sync::Arc;
use tree::*;

fn process_section(section: Arc<Vec<u8>>, )

fn main() {
    println!("Hello, world!");
}
