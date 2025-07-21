use crate::{Cartridge, MMIORegisters, CPU};

#[derive(Debug, Clone)]
pub struct Console {
    pub cpu: CPU,
    pub cartridge: Cartridge,
    pub ram: Vec<u8>,
    pub mmio: MMIORegisters,
}
