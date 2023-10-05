use smol_str::SmolStr;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    Global,
    Local,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: SmolStr,
    pub scope: Scope,
    pub index: u32,
}

#[derive(Debug, Clone, Default)]
pub struct SymbolTable {
    pub outer: Option<Box<SymbolTable>>,

    symbols: HashMap<SmolStr, Symbol>,
    index: u32,
}

impl SymbolTable {
    pub fn new_enclosing(outer: Self) -> Self {
        Self {
            outer: Some(outer.into()),
            ..Default::default()
        }
    }

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
            scope: if self.outer.is_some() {
                Scope::Local
            } else {
                Scope::Global
            },
            index,
        };
        self.symbols.insert(name.clone(), symbol);
        self.symbols.get(&name).unwrap()
    }

    pub fn locals(&self) -> u32 {
        self.symbols.len() as u32
    }

    pub fn resolve(&self, name: &str) -> Option<&Symbol> {
        match self.symbols.get(name) {
            Some(symbol) => Some(symbol),
            None if self.outer.is_some() => self.outer.as_ref().unwrap().resolve(name),
            None => None,
        }
    }
}
