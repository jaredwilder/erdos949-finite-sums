# Erdős #949 — the complement has continuum cardinality

Reader presentation prepared 2026-09-13; historical formalizer provenance recovered 2026-09-13.

## Statement

Let `S⊆R` be sum-free in the convention that `x+y∉S` for every `x,y∈S`, including `x=y`. Then

`|R\S| = |R|`.

## Proof

Put `C=R\S` and let `c=|R|`. For each `s∈S`, sum-freeness gives `2s∈C`. Doubling is injective, so `|S|≤|C|`.

If `C` were finite, then `S` would be finite too, contradicting `R=S∪C`. Thus `C` is infinite. In the usual set theory with choice, the union of two sets of cardinality at most the same infinite cardinal has cardinality at most that cardinal. Hence

`c = |S∪C| ≤ |C|+|C| = |C| ≤ c`.

Therefore `|C|=c`. No regularity assumption on the continuum cardinal is used.

## Scope

This proves the cardinality of the complement itself. It does **not** construct a continuum-sized set `A` satisfying `A+A⊆R\S`, and it does not close that stronger parent problem.

## Historical formalizer provenance recovered

The release-day public page originally said that the historical formal declaration and receipt had not been located. A later estate cross-check recovered the formalizer/vault record for exactly this child theorem.

Historical record:

- campaign: `erdos949-campaign-001`
- route / lemma: `R014/L1`
- statement: `Every sum-free S⊆R has complement of cardinality 𝔠; removes the trivial cardinality obstruction to the affirmative branch.`
- formalizer outcome: `KERNEL_CHECKED`
- grant after label audit: `LEMMA_CERTIFIED` / `KERNEL_THEOREM`
- recorded axioms: none
- historical receipt path: `oracle/frontier_formalizer/cable/receipts/fmz-erdos949-campaign-001-R014-L1.cable.json`
- recovered receipt SHA-256: `221cb97a2d3d9b59c325e1c2a24230dd3ed9848d6e00c8dc90c7a69fd2f31200`
- formalizer event time: 2026-09-01 21:38 UTC

The audit also corrected an earlier overlabel: this was historically called `TARGET_CLOSED` in one workflow layer, but that label was migrated to `LEMMA_CERTIFIED` because the theorem covers a **fragment/child obligation**, not the full continuum `A+A` target.

### Important source-byte boundary

The estate indexes preserve the kernel-check record and exact receipt hash, but the original R014 Lean source body and receipt bytes have **not yet been recovered into this public repository**. Therefore this page does not fabricate a replacement historical Lean file or claim byte-level replay from the current checkout.

The complete written proof above stands independently. The [`lean/`](../lean/) directory contains exact source and replay receipts for the separate sharp `q≤5`, countable pairwise-sum, and full finite-sums theorems.

This presentation is not a historical-priority claim.