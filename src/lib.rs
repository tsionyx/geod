//! Geodesy types and primitives

// The list was generated with the command
//   $ rustc -W help | grep ' allow ' | awk '{print $1}' | tr - _ | sort | xargs -I{} echo '#![warn({})]'
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(anonymous_parameters)]
#![warn(box_pointers)]
#![warn(deprecated_in_future)]
#![warn(elided_lifetimes_in_paths)]
#![warn(explicit_outlives_requirements)]
#![warn(indirect_structural_match)]
#![warn(keyword_idents)]
#![warn(macro_use_extern_crate)]
#![warn(meta_variable_misuse)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(missing_doc_code_examples)]
#![warn(missing_docs)]
#![warn(non_ascii_idents)]
// #![warn(private_doc_tests)]
#![warn(single_use_lifetimes)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
// #![warn(unreachable_pub)]
#![warn(unstable_features)]
#![warn(unused_extern_crates)]
#![warn(unused_import_braces)]
#![warn(unused_labels)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]
#![warn(unused_results)]
#![warn(variant_size_differences)]
// recommendations
#![forbid(unsafe_code)]
#![deny(clippy::mem_forget)]
// suppress some pedantic warnings
#![allow(clippy::non_ascii_literal)]
#![allow(clippy::must_use_candidate)]
#![cfg_attr(test, allow(clippy::wildcard_imports))]
// TODO: remove this cast's warnings
#![allow(clippy::cast_possible_truncation)]

pub use angle::{dd::DecimalDegree, dms_dd::AccurateDegree, Angle, AngleNames};
pub use coord::{Latitude, Longitude, Point};

mod angle;
mod coord;
mod utils;

// TODO: apply those recommendations
//  https://rust-lang.github.io/api-guidelines/
//  https://anssi-fr.github.io/rust-guide/
