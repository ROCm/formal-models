module memory_consistency/llvm/utils

// Module with general helper functions and predicates.

// Helper function to form the reflexive closure of a relation.
// Note: Alloy's precedence rules can cause unexpected behavior here since "."
// binds more tightly than "[]":
//   foo.maybe[bar] is (foo.maybe)[bar],
//      which is the same as maybe[foo][bar],
//      which is the same as bar.(maybe[foo])
// To get the likely intended behavior, use parentheses: foo.(maybe[bar])
fun maybe[r: univ -> univ] : univ -> univ {
  r + iden
}

