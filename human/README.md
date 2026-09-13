# Erdős #949 — sharp finite avoidance and full finite-sums complement theorems

**Author:** Jared Wilder  
**Recovered synthesis:** 2026-09-02  
**Public extraction:** 2026-09-11  
**Full finite-sums / verified-Lean promotion:** 2026-09-11

Let `S⊆R` be sum-free: there do not exist `x,y,z∈S` with `x+y=z`.

This note records the exact theorem cluster recovered from the estate. It does **not** solve the continuum-cardinality parent problem.

## Theorem 1 — the sharp finite constant is 5

For every sum-free `S⊆R`, there exists

\[
q\in\{1,2,3,4,5\}
\]

such that

\[
q\notin S,\qquad2q\notin S.
\]

Moreover 5 is best possible.

### Proof

Assume for contradiction that for every `q=1,...,5`, at least one of `q,2q` lies in `S`. Since `S` is sum-free, `1` and `2` cannot both lie in `S`.

**Case 1: `1∈S`.** Then `2∉S`, so `q=2` forces `4∈S`. Since `1+3=4`, `3∉S`, so `q=3` forces `6∈S`. Since `1+4=5`, `5∉S`, so `q=5` forces `10∈S`. But `4+6=10` with all three in `S`, contradiction.

**Case 2: `2∈S`.** Then `4∉S`, so `q=4` forces `8∈S`. Since `2+8=10`, `10∉S`, so `q=5` forces `5∈S`. Since `2+3=5`, `3∉S`, so `q=3` forces `6∈S`. But `2+6=8`, contradiction.

Thus some `q<=5` has both `q` and `2q` outside `S`.

For sharpness, take

\[
S=\{1,4,6\}.
\]

It is sum-free, and for each `q=1,2,3,4`, at least one of `q,2q` lies in `S`. Hence no bound `q<=4` is possible.

## Theorem 2 — full Hindman finite-sums complement

Every sum-free `S⊆R` admits an infinite set

\[
A\subseteq\mathbb N_{>0}
\]

such that for **every nonempty finite subset** `T⊆A`,

\[
\sum_{t\in T}t\notin S
\]

and

\[
2\sum_{t\in T}t\notin S.
\]

Equivalently,

\[
\boxed{FS(A)\cap S=\varnothing,\qquad 2FS(A)\cap S=\varnothing.}
\]

This is strictly stronger than merely asking for `A∩S=∅` and `A+A⊆R\S`.

### Proof idea

Color the positive integers by the three possible sum-free-compatible states

1. `n∈S`;
2. `n∉S` but `2n∈S`;
3. `n∉S` and `2n∉S`.

Hindman's theorem supplies an infinite sequence whose entire nonempty finite-sums set is contained in one color class.

The first color is impossible: if `u`, `v`, and `u+v` all lie in `S`, sum-freeness fails.

The second color is also impossible: if `u`, `v`, and `u+v` are all outside `S` but their doubles lie in `S`, then `2u,2v,2(u+v)` all lie in `S`, while

\[
2u+2v=2(u+v),
\]

again contradicting sum-freeness.

Therefore the monochromatic finite-sums set lies in the third color. A block-subsequence construction makes the generating set itself infinite and strictly increasing while preserving the full finite-sums property.

The exact construction, including arbitrary finite block sums rather than merely pairwise sums, is formally verified in `Erdos949HindmanFS.lean`.

## Corollary — complete countable `A+A` analogue

Taking one- and two-element subsets in Theorem 2 gives a countably infinite

\[
A\subseteq\mathbb N\setminus S
\]

with

\[
A+A\subseteq\mathbb R\setminus S.
\]

This is the countable-cardinality analogue of the parent problem.

## Theorem 3 — simultaneous finite-real-dilate IP avoidance

Let `D⊆R` be finite. Then there is an infinite sequence `x_1,x_2,...∈N` such that

\[
\boxed{d\,FS(x_i)\cap S=\varnothing\qquad\text{for every }d\in D.}
\]

### Proof

Color each `n∈N` by the finite bit vector

\[
c(n)=\bigl(1_S(dn)\bigr)_{d\in D}.
\]

Hindman's theorem gives an infinite sequence whose full finite-sums set is monochromatic for this finite coloring. Fix `d∈D`. If the `d`-coordinate of the common color were 1, then

\[
dx_1,\quad dx_2,\quad d(x_1+x_2)
\]

would all lie in `S`, while

\[
dx_1+dx_2=d(x_1+x_2),
\]

contradicting sum-freeness. Hence every coordinate is 0. If `d=0`, a sum-free set cannot contain 0.

## Theorem 4 — finite-homomorphism IP envelope

Let `T` be an additive semigroup, let `S⊆T` be sum-free, and let

\[
\phi_1,\ldots,\phi_m:(\mathbb N,+)\to T
\]

be finitely many additive homomorphisms. Then there is an infinite sequence `x_1,x_2,...` such that

\[
\boxed{
\phi_j(FS(x_i))\cap S=\varnothing
\qquad(1\le j\le m).
}
\]

### Proof

Color `n∈N` by

\[
\bigl(1_S(\phi_1(n)),\ldots,1_S(\phi_m(n))\bigr).
\]

Hindman's theorem produces an infinite finite-sums set on which this finite coloring is constant. If coordinate `j` of the common color were 1, then

\[
\phi_j(x_1),\quad\phi_j(x_2),\quad\phi_j(x_1+x_2)
\]

would all be in `S`. But additivity gives

\[
\phi_j(x_1+x_2)=\phi_j(x_1)+\phi_j(x_2),
\]

contradicting sum-freeness. Therefore every coordinate is 0.

Taking `T=R` and `phi_d(n)=dn` recovers the finite-real-dilate theorem.

## Formal verification — exact source is public

The formal estate is published at

`jaredwilder/erdos-theorems/theorems/erdos949-campaign-001/`.

### Sharp finite theorem

`Erdos949Core.lean` has a green receipt:

```text
status=VERIFIED
exitCode=0
seconds=76.5
```

Verified declarations include

```text
erdos949_universal
erdos949_five_sharp
erdos949_five_sharp_real
```

with no `sorryAx` in the audited declarations.

### Full finite-sums theorem

`Erdos949HindmanFS.lean` has a green, sorry-free receipt:

```text
status=VERIFIED
backend=scaleway-box
exitCode=0
seconds=6.83
sorryFree=true
sha256=f4130c29f345afc9b264aa2331199433f6f0bfdd9dc7e224a49123a60970b9ac
replication runs=2
identicalOutput=true
```

Its main declaration is

```text
erdos949_hindman_full_finite_sums
```

and the file re-derives the earlier `erdos949_countable_analogue` as a corollary. The main theorem has the ordinary Mathlib axiom footprint `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

The earlier `Erdos949Hindman.lean` pairwise version and all `.axioms.txt` / `.verify.json` receipts are retained beside it for provenance.

## Current external boundary

The unrestricted continuum-cardinality problem is still listed open. A July 2026 public working report proves the continuum-sized conclusion for Lebesgue-measurable sum-free sets and repairs the Baire-property case. Thus the theorem here is **not the strongest result by cardinality**. Its distinct axis is that the countable/full-finite-sums conclusion applies to an **arbitrary** sum-free `S`, with no measurability or Baire-property assumption.

The targeted searches behind this estate found no exact prior formulation of the arbitrary-`S` countable/IP consequence and no indexed match for the sharp `q<=5` lemma. The finite lemma is elementary, and the Hindman consequence has clear general-folklore risk. The correct claim is therefore **candidate / apparently unrecorded after targeted search**, pending specialist literature verification.

Hindman's theorem itself is classical and imported.

## Scope boundary

- The continuum-cardinality parent problem remains open.
- The sharp finite theorem and the full finite-sums theorem are formally verified in public Lean source.
- The real-dilate and finite-homomorphism envelopes are exact mathematical consequences, but formal verification is not claimed here unless a corresponding source/receipt is identified.
- Formal verification does not establish historical novelty.

## License

Apache-2.0 for repository-authored material.
