//! Nested modules.
//!
//! This package enables the integration of a (nested) module system into
//! projects such as compilers, interpreters etc.
//! Its speciality is the way it resolves module references:
//! In particular, we can always only reference modules by
//! their shortest possible path relative to the current position.
//!
//! For example, suppose we have the modules a/b/c, a/d/e and f.
//! Furthermore, let us be in the module a/b/c.
//! We can then reference
//! a/b/c, a/b, a and the root module (ancestors of our current module)
//! only by the empty path.
//! Furthermore, we can reference
//! a/d   by the path d,
//! a/d/e by the path d/e, and
//! f     by the path f.
//!
//! This restriction on module references enables
//! a very simple implementation as well as
//! the property that we can always wrap modules around other modules and
//! be certain that this preserves valid references of the original module.
//!
//! In the following example, we create
//! a module with root data 0 and the following submodules:
//! * b: 1
//! * a: 2
//!     * b: 3
//!
//! We then search for the module "b" twice from different modules:
//! When we are inside "a", we find two occurrences of "b", namely "a"/"b" (3) and "b" (1).
//! When we are inside the root module, we find only one occurrence of "b", namely "b" (1).
//!
//! ~~~
//! # use nested_modules::{Context, Module};
//! let mut ctx = Context::new();
//! ctx.get_mut().data = 0;
//! ctx.insert("b", Module::from(1));
//! assert!(!ctx.close());
//! ctx.open_or("a", Module::from(2));
//! ctx.insert("b", Module::from(3));
//!
//! // we are now in module "a"
//! assert_eq!(ctx.get().data, 2);
//! // searching for a module "b" yields two results
//! let result: Vec<_> = ctx.find(["b"].iter()).map(|m| m.data).collect();
//! assert_eq!(result, vec![3, 1]);
//! // searching for "a" yields no result, because we are inside it
//! let result: Vec<_> = ctx.find(["a"].iter()).map(|m| m.data).collect();
//! assert_eq!(result, vec![]);
//! assert!(ctx.close());
//!
//! // we are now in the root module
//! assert_eq!(ctx.get().data, 0);
//! // searching for either module "b", "a", or "a"/"b" yields only one result now
//! let result: Vec<_> = ctx.find(["b"].iter()).map(|m| m.data).collect();
//! assert_eq!(result, vec![1]);
//! let result: Vec<_> = ctx.find(["a"].iter()).map(|m| m.data).collect();
//! assert_eq!(result, vec![2]);
//! let result: Vec<_> = ctx.find(["a", "b"].iter()).map(|m| m.data).collect();
//! assert_eq!(result, vec![3]);
//! assert!(!ctx.close());
//! ~~~

#![no_std]
extern crate alloc;

use alloc::borrow::Borrow;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

/// A module with data and submodules.
pub struct Module<K, V> {
    pub data: V,
    modules: BTreeMap<K, Module<K, V>>,
}

impl<K: Ord, V> From<V> for Module<K, V> {
    fn from(data: V) -> Self {
        Self {
            data,
            modules: Default::default(),
        }
    }
}

impl<K: Ord, V: Default> Default for Module<K, V> {
    fn default() -> Self {
        Module {
            data: Default::default(),
            modules: Default::default(),
        }
    }
}

impl<K: Ord, V> Module<K, V> {
    /// Return a reference to a submodule at the given path.
    pub fn get<'q, Q: 'q, I>(mut self: &Self, path: I) -> Option<&Self>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        I: Iterator<Item = &'q Q>,
    {
        for p in path {
            self = self.modules.get(p)?;
        }
        Some(self)
    }
}

/// A module with a path to an open submodule.
pub struct Context<K, V> {
    root: Module<K, V>,
    open: Vec<(K, Module<K, V>)>,
}

impl<K, V> From<Module<K, V>> for Context<K, V> {
    fn from(root: Module<K, V>) -> Self {
        let open = Vec::new();
        Self { root, open }
    }
}

impl<K: Ord, V: Default> Default for Context<K, V> {
    fn default() -> Self {
        Self::from(Module::default())
    }
}

impl<K: Ord, V: Default> Context<K, V> {
    /// Create a new context with a default root module as current open module.
    pub fn new() -> Self {
        Default::default()
    }

    /// Open a default module inside the previously open module.
    pub fn open_or_default(&mut self, name: K) {
        let module = self.remove(&name).unwrap_or_default();
        self.open.push((name, module))
    }
}

impl<K: Ord, V> Context<K, V> {
    /// Open a module inside the previously open module.
    ///
    /// Use the provided module if the module with the given name does not exist.
    pub fn open_or(&mut self, name: K, module: Module<K, V>) {
        let module = self.remove(&name).unwrap_or(module);
        self.open.push((name, module))
    }

    /// Open a module inside the previously open module.
    ///
    /// Use the provided closure if the module with the given name does not exist.
    pub fn open_or_else(&mut self, name: K, f: impl FnOnce() -> Module<K, V>) {
        let module = self.remove(&name).unwrap_or_else(f);
        self.open.push((name, module))
    }

    /// Insert a module into the currently open module.
    pub fn insert(&mut self, name: K, module: Module<K, V>) -> Option<Module<K, V>> {
        self.get_mut().modules.insert(name, module)
    }

    /// Remove a module from the currently open module.
    pub fn remove(&mut self, name: &K) -> Option<Module<K, V>> {
        self.get_mut().modules.remove(name)
    }

    /// Close the currently open module.
    ///
    /// Return false if the current open module is the root module.
    pub fn close(&mut self) -> bool {
        if let Some((name, module)) = self.open.pop() {
            self.get_mut().modules.insert(name, module);
            return true;
        }
        false
    }

    /// Find modules matching the given path from the currently open module.
    pub fn find<'a, 'q, Q: 'q, I>(&'a self, path: I) -> impl Iterator<Item = &'a Module<K, V>>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        I: Iterator<Item = &'q Q> + Clone,
    {
        let patc = path.clone();
        let open = self.open.iter().rev();
        let init = open.filter_map(move |o| o.1.get(patc.clone()));

        // this could be written shorter with `core::iter::once_with`,
        // but it would require a newer Rust version
        let mut last = Some(move || self.root.get(path));
        init.chain(core::iter::from_fn(move || last.take()?()))
    }
}

impl<K, V> Context<K, V> {
    /// Return a reference to the currently open module.
    pub fn get(&self) -> &Module<K, V> {
        match self.open.iter().last() {
            None => &self.root,
            Some((_name, module)) => module,
        }
    }

    /// Return a mutable reference to the currently open module.
    pub fn get_mut(&mut self) -> &mut Module<K, V> {
        match self.open.iter_mut().last() {
            None => &mut self.root,
            Some((_name, module)) => module,
        }
    }

    /// Return the path of the currently open module.
    pub fn get_path(&self) -> impl Iterator<Item = &K> {
        self.open.iter().map(|(key, _)| key)
    }
}

impl<K: Ord, V> From<Context<K, V>> for Module<K, V> {
    fn from(mut ctx: Context<K, V>) -> Self {
        while ctx.close() {}
        ctx.root
    }
}
