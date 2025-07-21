use crate::cpu::*;
use crate::memory::*;

pub struct DisassemblySection {
    pub branchfrom: u32,
    pub branchto: u32,
    pub start: u32,
    pub end: u32,
    pub is_subroutine: bool,
    pub instructions: Vec<InstructionContext>,
}

impl DisassemblySection {
    pub fn new(
        branchfrom: u32,
        branchto: u32,
        start: u32,
        end: u32,
        is_subroutine: bool,
        instructions: Vec<InstructionContext>,
    ) -> Self {
        DisassemblySection {
            branchfrom,
            branchto,
            start,
            end,
            is_subroutine,
            instructions,
        }
    }

    pub fn contains(&self, address: u32) -> bool {
        address >= self.start && address <= self.end
    }
}

impl Default for DisassemblySection {
    fn default() -> Self {
        DisassemblySection {
            branchfrom: 0,
            branchto: 0,
            start: 0,
            end: 0,
            is_subroutine: false,
            instructions: Vec::new(),
        }
    }
}
