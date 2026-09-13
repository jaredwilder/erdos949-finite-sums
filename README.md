# Erdős #949 — finite-sums avoidance

**Author:** Jared Wilder  
**Status:** theorem + formalization program.

This repository is the canonical public home for the estate's #949 finite-sums avoidance work. It brings the human theorem package together with the clean Lean formalization layer rather than leaving them split between a provenance archive and a broad theorem bank.

## Complement-cardinality child

The [complete written proof](human/complement-cardinality.md) shows that the complement of any sum-free subset of `R` has cardinality continuum. This does not construct a continuum-sized `A` with `A+A` in that complement. The child has written-proof authority here; its historical formal source and receipt remain to be identified.

## Formal layer

The focused formal source contains **33 clean Lean declarations** across the core, Hindman-style, and full finite-sums layers. Kernel status and axiom footprints belong to the declarations actually checked; they are not a blanket label for every surrounding note.

## Source layout

Exact public source bytes are migrated under:

- `human/README.md` — the original `unpublished-math-papers/erdos949-sumfree-ip/README.md`;
- `lean/` — `erdos-theorems/theorems/erdos949-campaign-001/`.

The added `human/complement-cardinality.md` is a new written presentation, with its own authority statement.

The repository preserves the distinction between the finite core, transfer arguments, and broader infinite statements. Historical novelty is adjudicated separately from proof status.
