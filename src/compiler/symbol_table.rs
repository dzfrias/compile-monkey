use smol_str::SmolStr;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy)]
pub enum Scope {
    Global,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: SmolStr,
    pub scope: Scope,
    pub index: u32,
}

#[derive(Debug, Clone, Default)]
pub struct SymbolTable {
    symbols: HashMap<SmolStr, Symbol>,
    index: u32,
}

impl SymbolTable {
    pub fn define(&mut self, name: &str) -> &Symbol {
        let name = SmolStr::new(name);

        let index = match self.symbols.get(&name) {
            Some(symbol) => symbol.index,
            None => {
                let i = self.index;
                self.index += 1;
                i
            }
        };
        let symbol = Symbol {
            name: name.clone(),
            scope: Scope::Global,
            index,
        };
        self.symbols.insert(name.clone(), symbol);
        self.symbols.get(&name).unwrap()
    }

    pub fn resolve(&self, name: &str) -> Option<&Symbol> {
        self.symbols.get(name)
    }
}
