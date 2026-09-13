# Erdős #949 — verified Lean theorem cluster

This directory contains the exact public Lean source and verification receipts for the strongest #949 formal assets whose **source bytes are presently recovered here**.

## Headline theorems

### Sharp finite constant 5

`Erdos949Core.lean` proves, for every sum-free `S⊆R`, the existence of an integer `1<=q<=5` with both `q` and `2q` outside `S`, and proves sharpness by the witness `{1,4,6}`.

Receipt: `Erdos949Core.verify.json` — `VERIFIED`, exit 0, no `sorryAx` in the audited declarations.

### Full Hindman finite-sums complement

`Erdos949HindmanFS.lean` proves a strictly stronger countable theorem: for every sum-free `S⊆R`, there is an infinite set `A` of positive naturals such that for every nonempty finite `T⊆A`, both `sum T` and `2*sum T` lie outside `S`.

So the **entire nonempty finite-sums set** `FS(A)` avoids `S`, not merely `A+A`.

Receipt: `Erdos949HindmanFS.verify.json` — `VERIFIED`, `sorryFree=true`, SHA-256 `f4130c29f345afc9b264aa2331199433f6f0bfdd9dc7e224a49123a60970b9ac`, two replay runs with identical stdout.

### Earlier pairwise form

`Erdos949Hindman.lean` proves the infinite `A` / pairwise-sum form and is retained as provenance. The stronger FS file re-derives it as a corollary.

## Historical R014 complement-cardinality formalization

The estate vault also records a separate historical formalizer theorem:

> Every sum-free `S⊆ℝ` has complement of cardinality continuum.

Historical provenance:

- campaign: `erdos949-campaign-001`
- route / lemma: `R014/L1`
- formal status: `KERNEL_CHECKED`
- corrected grant: `LEMMA_CERTIFIED` / `KERNEL_THEOREM`
- recorded axioms: none
- historical receipt path: `oracle/frontier_formalizer/cable/receipts/fmz-erdos949-campaign-001-R014-L1.cable.json`
- recovered receipt SHA-256: `221cb97a2d3d9b59c325e1c2a24230dd3ed9848d6e00c8dc90c7a69fd2f31200`

The exact historical **Lean source body and receipt bytes are not yet recovered into this checkout**, so no R014 `.lean` or `.verify.json` file is fabricated here and no current-checkout replay claim is made. See [`../human/complement-cardinality.md`](../human/complement-cardinality.md) for the complete human proof and the recovered formalizer provenance.

## Files currently replayable here

- `Erdos949Core.lean`
- `Erdos949Core.axioms.txt`
- `Erdos949Core.verify.json`
- `Erdos949Hindman.lean`
- `Erdos949Hindman.axioms.txt`
- `Erdos949Hindman.verify.json`
- `Erdos949HindmanFS.lean`
- `Erdos949HindmanFS.axioms.txt`
- `Erdos949HindmanFS.verify.json`

## Scope

The unrestricted Erdős #949 continuum-cardinality `A+A` problem remains open. The public Lean files above certify the exact finite and countable finite-sums theorems stated here. The historical R014 child theorem removes only the trivial complement-cardinality obstruction; it does not construct a continuum-sized `A` with `A+A⊆S^c`.

Formal verification is not a historical novelty certificate.