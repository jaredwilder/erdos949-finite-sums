# Erdős #949 — Finite-Sums Avoidance

**Jared Wilder**

Human proofs and Lean formalization for finite-sums avoidance questions around Erdős Problem #949.

## Complement-cardinality theorem

The [written proof](human/complement-cardinality.md) establishes that the complement of any sum-free subset of `R` has cardinality continuum.

This gives a clean cardinality statement at the base of the program and separates it from the harder constructive question of producing a continuum-sized set whose pairwise sums land in such a complement.

## Lean formalization

The focused formal layer contains **33 clean Lean declarations** spanning the finite core, Hindman-style structure, and full finite-sums statements.

The formal and human layers are kept side by side so each theorem can be read either as mathematics or as checked source.

## Repository map

- `human/` — written theorem package and exposition
- `human/complement-cardinality.md` — complete proof of the complement-cardinality theorem
- `lean/` — focused Lean formalization

Historical source material was consolidated here from the broader Wilder theorem and archive repositories.