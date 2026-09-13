# Erdős #949 — verified Lean theorem cluster

This directory contains the exact public Lean source and verification receipts for the strongest recovered #949 results.

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

## Files

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

The unrestricted Erdős #949 continuum-cardinality problem remains open. These files certify the exact finite and countable/IP-strength theorems stated above. Formal verification is not a historical novelty certificate.
