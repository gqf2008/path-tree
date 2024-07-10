//! path-tree is a lightweight high performance HTTP request router for Rust.
//!
//! # Example
//!
//! ```
//! use path_tree::PathTree;
//!
//! /*
//! / •0
//! ├── api/
//! │   └── + •13
//! ├── login •1
//! ├── public/
//! │   └── ** •7
//! ├── s
//! │   ├── ettings •3
//! │   │   └── /
//! │   │       └── : •4
//! │   └── ignup •2
//! └── : •5
//!     └── /
//!         └── : •6
//!             └── /
//!                 ├── actions/
//!                 │   └── :
//!                 │       └── \:
//!                 │           └── : •10
//!                 ├── releases/download/
//!                 │   └── :
//!                 │       └── /
//!                 │           └── :
//!                 │               └── .
//!                 │                   └── : •8
//!                 ├── tags/
//!                 │   └── :
//!                 │       └── -
//!                 │           └── :
//!                 │               └── -
//!                 │                   └── : •9
//!                 ├── : •11
//!                 └── ** •12
//! */
//! let mut tree = PathTree::new();
//!
//! tree.insert("/", 0);
//! tree.insert("/login", 1);
//! tree.insert("/signup", 2);
//! tree.insert("/settings", 3);
//! tree.insert("/settings/:page", 4);
//! tree.insert("/:user", 5);
//! tree.insert("/:user/:repo", 6);
//! tree.insert("/public/:any*", 7);
//! tree.insert("/:org/:repo/releases/download/:tag/:filename.:ext", 8);
//! tree.insert("/:org/:repo/tags/:day-:month-:year", 9);
//! tree.insert("/:org/:repo/actions/:name\\::verb", 10);
//! tree.insert("/:org/:repo/:page", 11);
//! tree.insert("/:org/:repo/*", 12);
//! tree.insert("/api/+", 13);
//!
//! let (h, p) = tree.find("/").unwrap();
//! assert_eq!(h, &0);
//! assert_eq!(p.params(), vec![]);
//!
//! let (h, p) = tree.find("/login").unwrap();
//! assert_eq!(h, &1);
//! assert_eq!(p.params(), vec![]);
//!
//! let (h, p) = tree.find("/settings/admin").unwrap();
//! assert_eq!(h, &4);
//! assert_eq!(p.params(), vec![("page", "admin")]);
//!
//! let (h, p) = tree.find("/viz-rs").unwrap();
//! assert_eq!(h, &5);
//! assert_eq!(p.params(), vec![("user", "viz-rs")]);
//!
//! let (h, p) = tree.find("/viz-rs/path-tree").unwrap();
//! assert_eq!(h, &6);
//! assert_eq!(p.params(), vec![("user", "viz-rs"), ("repo", "path-tree")]);
//!
//! let (h, p) = tree.find("/rust-lang/rust-analyzer/releases/download/2022-09-12/rust-analyzer-aarch64-apple-darwin.gz").unwrap();
//! assert_eq!(h, &8);
//! assert_eq!(
//!     p.params(),
//!     vec![
//!         ("org", "rust-lang"),
//!         ("repo", "rust-analyzer"),
//!         ("tag", "2022-09-12"),
//!         ("filename", "rust-analyzer-aarch64-apple-darwin"),
//!         ("ext", "gz")
//!     ]
//! );
//!
//! let (h, p) = tree.find("/rust-lang/rust-analyzer/tags/2022-09-12").unwrap();
//! assert_eq!(h, &9);
//! assert_eq!(
//!     p.params(),
//!     vec![
//!         ("org", "rust-lang"),
//!         ("repo", "rust-analyzer"),
//!         ("day", "2022"),
//!         ("month", "09"),
//!         ("year", "12")
//!     ]
//! );
//!
//! let (h, p) = tree.find("/rust-lang/rust-analyzer/actions/ci:bench").unwrap();
//! assert_eq!(h, &10);
//! assert_eq!(
//!     p.params(),
//!     vec![
//!         ("org", "rust-lang"),
//!         ("repo", "rust-analyzer"),
//!         ("name", "ci"),
//!         ("verb", "bench"),
//!     ]
//! );
//!
//! let (h, p) = tree.find("/rust-lang/rust-analyzer/stargazers").unwrap();
//! assert_eq!(h, &11);
//! assert_eq!(p.params(), vec![("org", "rust-lang"), ("repo", "rust-analyzer"), ("page", "stargazers")]);
//!
//! let (h, p) = tree.find("/rust-lang/rust-analyzer/stargazers/404").unwrap();
//! assert_eq!(h, &12);
//! assert_eq!(p.params(), vec![("org", "rust-lang"), ("repo", "rust-analyzer"), ("*1", "stargazers/404")]);
//!
//! let (h, p) = tree.find("/public/js/main.js").unwrap();
//! assert_eq!(h, &7);
//! assert_eq!(p.params(), vec![("any", "js/main.js")]);
//!
//! let (h, p) = tree.find("/api/v1").unwrap();
//! assert_eq!(h, &13);
//! assert_eq!(p.params(), vec![("+1", "v1")]);
//! ```

#![no_std]
#![forbid(unsafe_code)]
#![warn(rust_2018_idioms, unreachable_pub)]

extern crate alloc;

use alloc::{
    string::{String, ToString},
    vec::Vec,
};
use core::{slice::Iter, str::from_utf8};
use smallvec::SmallVec;

mod node;
pub use node::{Key, Node};

mod parser;
pub use parser::{Kind, Parser, Piece, Position};

/// A path tree.
#[derive(Clone, Debug)]
pub struct PathTree<T> {
    id: usize,
    routes: Vec<Vec<(T, Vec<Piece>)>>,
    pub node: Node<usize>,
}

impl<T> Default for PathTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> PathTree<T> {
    /// Creates a new [`PathTree`].
    #[must_use]
    pub fn new() -> Self {
        Self {
            id: 0,
            routes: Vec::new(),
            node: Node::new(Key::String(Vec::new()), None),
        }
    }

    /// Inserts a part path-value to the tree and returns the id.
    #[must_use]
    pub fn insert(&mut self, path: &str, value: T) -> (usize, usize) {
        let mut node = &mut self.node;

        let (_overwritten, pieces) = if path.is_empty() {
            (false, Vec::new())
        } else {
            let pieces = Parser::new(path).collect::<Vec<_>>();
            node = pieces.iter().fold(node, |node, piece| match piece {
                Piece::String(s) => node.insert_bytes(&s[..]),
                Piece::Parameter(_, k) => node.insert_parameter(*k),
            });
            (true, pieces)
        };

        if let Some(id) = node.value {
            let sub = &mut self.routes[id];
            sub.push((value, pieces));
            // self.routes[id].0 = value;
            // if overwritten {
            //     self.routes[id].1 = pieces;
            // }
            (id, sub.len() - 1)
        } else {
            let mut sub = Vec::new();
            sub.push((value, pieces));
            self.routes.push(sub);
            let id = self.id;
            node.value = Some(id);
            self.id += 1;
            (id, 0)
        }
    }

    /// Returns the [`Path`] by the given path.
    #[must_use]
    pub fn find<'a, 'b>(&'a self, path: &'b str) -> Option<Vec<(&T, Path<'a, 'b>)>> {
        let bytes = path.as_bytes();
        self.node.find(bytes).and_then(|(id, ranges)| {
            self.routes.get(*id).and_then(|subs| {
                let ret: Vec<(&T, Path<'a, 'b>)> = subs
                    .iter()
                    .map(|(value, pieces)| {
                        (
                            value,
                            Path {
                                id,
                                pieces,
                                raws: ranges
                                    .clone()
                                    .into_iter()
                                    .filter_map(|r| from_utf8(&bytes[r]).ok())
                                    .rev()
                                    .collect(),
                            },
                        )
                    })
                    .collect();
                Some(ret)
            })
        })
    }

    pub fn remove_with_sid(&mut self, path: &str, sid: usize) -> Option<T> {
        let mut rm_node = false;
        let mut ret = None;
        if let Some((id, _ranges)) = self.node.find(path.as_bytes()) {
            if let Some(subs) = self.routes.get_mut(*id) {
                if subs.len() > sid {
                    let value = subs.remove(sid).0;
                    rm_node = subs.is_empty();
                    ret = Some(value);
                }
            }
        }
        if rm_node {
            self.node.remove(path.as_bytes());
        }
        ret
    }
    /// Removes a path from the tree.
    pub fn remove(&mut self, path: &str) -> Option<Vec<T>> {
        self.node.remove(path.as_bytes()).and_then(|id| {
            self.routes
                .remove(id)
                .into_iter()
                .map(|(value, _)| Some(value))
                .collect()
        })
    }

    /// Gets the route by id.
    #[must_use]
    #[inline]
    pub fn get_route(&self, index: usize) -> Option<&[(T, Vec<Piece>)]> {
        self.routes.get(index).and_then(|subs| Some(&subs[..]))
    }

    pub fn get_route_with_sid(&self, index: usize, sid: usize) -> Option<&(T, Vec<Piece>)> {
        self.routes.get(index).and_then(|subs| subs.get(sid))
    }

    /// Generates URL with the params.
    #[must_use]
    pub fn url_for(&self, index: usize, params: &[&str]) -> Option<String> {
        self.get_route(index).and_then(|subs| {
            let (_, pieces) = &subs[0];
            let mut bytes = Vec::new();
            let mut iter = params.iter();

            pieces.iter().for_each(|piece| match piece {
                Piece::String(s) => {
                    bytes.extend_from_slice(s);
                }
                Piece::Parameter(_, _) => {
                    if let Some(s) = iter.next() {
                        bytes.extend_from_slice(s.as_bytes());
                    }
                }
            });

            from_utf8(&bytes).map(ToString::to_string).ok()
        })
    }

    pub fn iter(&self) -> Iter<'_, Vec<(T, Vec<Piece>)>> {
        self.routes.iter()
    }
}

impl<'a, T> IntoIterator for &'a PathTree<T> {
    type Item = &'a Vec<(T, Vec<Piece>)>;
    type IntoIter = Iter<'a, Vec<(T, Vec<Piece>)>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Matched route path infomation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Path<'a, 'b> {
    pub id: &'a usize,
    pub pieces: &'a [Piece],
    pub raws: SmallVec<[&'b str; 4]>,
}

impl<'a, 'b> Path<'a, 'b> {
    /// Gets current path pattern.
    ///
    /// # Panics
    ///
    /// Will panic if bytes to string conversion fails.
    pub fn pattern(&self) -> String {
        let mut bytes = Vec::new();

        self.pieces.iter().for_each(|piece| match piece {
            Piece::String(s) => {
                if s == b":" || s == b"+" || s == b"?" {
                    bytes.push(b'\\');
                }
                bytes.extend_from_slice(s);
            }
            Piece::Parameter(p, k) => match p {
                Position::Index(_, _) => {
                    if *k == Kind::OneOrMore {
                        bytes.push(b'+');
                    } else if *k == Kind::ZeroOrMore || *k == Kind::ZeroOrMoreSegment {
                        bytes.push(b'*');
                    }
                }
                Position::Named(n) => match k {
                    Kind::Normal | Kind::Optional | Kind::OptionalSegment => {
                        bytes.push(b':');
                        bytes.extend_from_slice(n);
                        if *k == Kind::Optional || *k == Kind::OptionalSegment {
                            bytes.push(b'?');
                        }
                    }
                    Kind::OneOrMore => {
                        bytes.push(b'+');
                        bytes.extend_from_slice(n);
                    }
                    Kind::ZeroOrMore | Kind::ZeroOrMoreSegment => {
                        bytes.push(b'*');
                        bytes.extend_from_slice(n);
                    }
                },
            },
        });

        from_utf8(&bytes)
            .map(ToString::to_string)
            .expect("pattern generated failure")
    }

    /// Returns the parameters of the current path.
    #[must_use]
    pub fn params(&self) -> Vec<(&str, &str)> {
        self.params_iter().collect()
    }

    /// Returns the parameters iterator of the current path.
    pub fn params_iter(&self) -> impl Iterator<Item = (&str, &str)> {
        #[inline]
        fn piece_filter(piece: &Piece) -> Option<&str> {
            match piece {
                Piece::String(_) => None,
                Piece::Parameter(p, _) => from_utf8(match p {
                    Position::Index(_, n) | Position::Named(n) => n,
                })
                .ok(),
            }
        }

        self.pieces
            .iter()
            .filter_map(piece_filter)
            .zip(self.raws.iter().copied())
    }
}
