# Erdős #949 — the complement has continuum cardinality

Reader presentation prepared 2026-09-13.

## Statement

Let `S⊆R` be sum-free in the convention that `x+y∉S` for every `x,y∈S`, including `x=y`. Then

`|R\S| = |R|`.

## Proof

Put `C=R\S` and let `c=|R|`. For each `s∈S`, sum-freeness gives `2s∈C`. Doubling is injective, so `|S|≤|C|`.

If `C` were finite, then `S` would be finite too, contradicting `R=S∪C`. Thus `C` is infinite. In the usual set theory with choice, the union of two sets of cardinality at most the same infinite cardinal has cardinality at most that cardinal. Hence

`c = |S∪C| ≤ |C|+|C| = |C| ≤ c`.

Therefore `|C|=c`. No regularity assumption on the continuum cardinal is used.

## Scope and proof authority

This proves the cardinality of the complement itself. It does not construct a continuum-sized set `A` satisfying `A+A⊆R\S`, and it does not close that stronger parent problem.

This page supplies a complete written proof. The recovery report assigns a historical formal status to a complement-cardinality child, but its exact Lean declaration and check receipt have not been located in the public source examined for this release. This page therefore makes no kernel-check claim for this child. The [existing formal source](../lean/) covers its own finite and countable finite-sums declarations separately.

See the [finite and finite-sums theorem package](README.md) for those related results. This presentation is newly prepared; it is not a byte-for-byte recovered historical source file. No historical priority claim is made.
