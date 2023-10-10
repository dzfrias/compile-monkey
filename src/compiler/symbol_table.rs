use smol_str::SmolStr;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    Global,
    Local,
    Builtin,
    Free,
    Function,
}

/// A cheap to clone representation of a scoped identifier.
#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: SmolStr,
    pub scope: Scope,
    pub index: u32,
}

#[derive(Debug, Clone, Default)]
pub struct SymbolTable {
    pub outer: Option<Box<SymbolTable>>,
    pub free: Vec<Symbol>,

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

    pub fn define_builtin(&mut self, name: &str, index: u32) {
        let name = SmolStr::new(name);
        self.symbols.insert(
            name.clone(),
            Symbol {
                name,
                scope: Scope::Builtin,
                index,
            },
        );
    }

    pub fn define(&mut self, name: &str) -> &Symbol {
        let name = SmolStr::new(name);

        let index = {
            let i = self.index;
            self.index += 1;
            i
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

    pub fn define_function(&mut self, name: &str) -> &Symbol {
        let s_name = SmolStr::new(name);
        let symbol = Symbol {
            name: s_name.clone(),
            scope: Scope::Function,
            index: 0,
        };
        self.symbols.insert(s_name, symbol);
        self.symbols.get(name).unwrap()
    }

    pub fn locals(&self) -> u32 {
        (self.symbols.len() - self.free.len()) as u32
    }

    pub fn resolve(&mut self, name: &str) -> Option<Symbol> {
        let outer = match self.symbols.get(name) {
            Some(symbol) => return Some(symbol.clone()),
            None if self.outer.is_some() => self.outer.as_mut().unwrap(),
            None => return None,
        };
        let symbol = outer.resolve(name)?;
        if matches!(symbol.scope, Scope::Global | Scope::Builtin) {
            return Some(symbol);
        }

        Some({
            let original = symbol.clone();
            self.free.push(original.clone());
            let symbol = Symbol {
                name: original.name.clone(),
                index: self.free.len() as u32 - 1,
                scope: Scope::Free,
            };
            self.symbols.insert(original.name.clone(), symbol);
            self.symbols.get(&original.name).unwrap().clone()
        })
    }
}
