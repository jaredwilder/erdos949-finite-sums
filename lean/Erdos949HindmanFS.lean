import Mathlib

/-!
Erdos 949 -- the countable analogue at FULL HINDMAN STRENGTH, kernel-checked.

The earlier file `Erdos949Hindman.lean` proved: for every sum-free `S` in the reals there is an
INFINITE set `A` of positive naturals with `A` disjoint from `S` and `A + A` disjoint from `S`
(diagonal included).  That statement throws away most of what Hindman's theorem actually hands
you: the monochromatic object is `FS(A)`, the set of ALL nonempty finite sums of DISTINCT
elements of `A`, not merely the pairwise sums.

This file promotes the theorem to that full strength:

  `erdos949_hindman_full_finite_sums` :
      for every sum-free `S ⊆ ℝ` there is an infinite set `A` of positive naturals such that for
      EVERY nonempty finite `T ⊆ A`, both `∑ T` and `2 * ∑ T` land outside `S`.
      Equivalently `FS(A) ∩ S = ∅` (and `2 · FS(A) ∩ S = ∅`).

The old pairwise statement is then re-derived as a corollary (`erdos949_countable_analogue`), so
the upgrade is visibly strictly stronger, and the non-vacuity controls are kept for both shapes.

Route: Hindman's finite-sums theorem (`Hindman.exists_FS_of_finite_cover`) over the additive
semigroup `PNat`, a three-cell colouring of `n` by `(n ∈ S, 2n ∈ S)`, then an explicit block-sum
construction.  The new ingredient over the earlier file is `ypos_finset_sum_mem`: a sum over an
ARBITRARY finite nonempty set of blocks (not just two) stays inside the monochromatic FS-set.
That is the lemma the pairwise version had collapsed to `j < k`.

Self-contained by source inclusion: the block machinery of `Erdos949Hindman.lean` is reproduced
below verbatim (no local imports).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Hindman

namespace Erdos949HindmanFS

/-! ### Block machinery (source-included from `Erdos949Hindman.lean`) -/

/-- `bsum a n` is `a 0 + a 1 + ... + a n`, the sum of the first `n+1` entries of the stream. -/
def bsum : Stream' ℕ+ → ℕ → ℕ+
  | a, 0 => a.head
  | a, (n + 1) => a.head + bsum a.tail n

theorem bsum_zero (a : Stream' ℕ+) : bsum a 0 = a.head := rfl

theorem bsum_succ (a : Stream' ℕ+) (n : ℕ) : bsum a (n + 1) = a.head + bsum a.tail n := rfl

/-- Every consecutive block sum is a finite sum of the stream. -/
theorem bsum_mem (a : Stream' ℕ+) (n : ℕ) : bsum a n ∈ FS a := by
  induction n generalizing a with
  | zero => exact FS.head a
  | succ n ih =>
      have h := FS.cons a (bsum a.tail n) (ih a.tail)
      rw [bsum_succ]
      exact h

/-- A consecutive block sum absorbs anything drawn from the stream strictly after the block. -/
theorem bsum_add_mem (a : Stream' ℕ+) (n : ℕ) (m : ℕ+)
    (hm : m ∈ FS (a.drop (n + 1))) : bsum a n + m ∈ FS a := by
  induction n generalizing a with
  | zero =>
      have hm' : m ∈ FS a.tail := by
        rw [Stream'.tail_eq_drop]
        exact hm
      rw [bsum_zero]
      exact FS.cons a m hm'
  | succ n ih =>
      have hm' : m ∈ FS (a.tail.drop (n + 1)) := by
        rwa [Stream'.drop_succ] at hm
      have h1 : bsum a.tail n + m ∈ FS a.tail := ih a.tail hm'
      have h2 := FS.cons a (bsum a.tail n + m) h1
      rw [bsum_succ, add_assoc]
      exact h2

/-- A block of `n+1` entries has value at least `n+1`, since every entry is at least one. -/
theorem le_bsum (a : Stream' ℕ+) (n : ℕ) : n + 1 ≤ ((bsum a n : ℕ+) : ℕ) := by
  induction n generalizing a with
  | zero =>
      have h : 1 ≤ ((a.head : ℕ+) : ℕ) := a.head.one_le
      rw [bsum_zero]
      omega
  | succ n ih =>
      have h := ih a.tail
      have hh : 1 ≤ ((a.head : ℕ+) : ℕ) := a.head.one_le
      rw [bsum_succ, PNat.add_coe]
      omega

/-- The block schedule: `blk a k = (start of block k, length of block k minus one)`. -/
def blk (a : Stream' ℕ+) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | (k + 1) =>
      ((blk a k).1 + (blk a k).2 + 1, ((bsum (a.drop (blk a k).1) (blk a k).2 : ℕ+) : ℕ))

/-- `ypos a k` is the sum of the entries in block `k`. -/
def ypos (a : Stream' ℕ+) (k : ℕ) : ℕ+ := bsum (a.drop (blk a k).1) (blk a k).2

theorem blk_succ_fst (a : Stream' ℕ+) (k : ℕ) :
    (blk a (k + 1)).1 = (blk a k).1 + (blk a k).2 + 1 := rfl

theorem blk_succ_snd (a : Stream' ℕ+) (k : ℕ) :
    (blk a (k + 1)).2 = ((ypos a k : ℕ+) : ℕ) := rfl

theorem ypos_mem (a : Stream' ℕ+) (k : ℕ) : ypos a k ∈ FS a :=
  FS_iter_tail_sub_FS a (blk a k).1 (bsum_mem (a.drop (blk a k).1) (blk a k).2)

/-- Strict growth of the block starts. -/
theorem blk_fst_strictMono (a : Stream' ℕ+) : StrictMono (fun k => (blk a k).1) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [blk_succ_fst]
  omega

/-- Strict growth of the block sums: block `k+1` is longer than the value of block `k`. -/
theorem ypos_strictMono (a : Stream' ℕ+) :
    StrictMono (fun k => ((ypos a k : ℕ+) : ℕ)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h := le_bsum (a.drop (blk a (k + 1)).1) (blk a (k + 1)).2
  have h2 : (blk a (k + 1)).2 = ((ypos a k : ℕ+) : ℕ) := blk_succ_snd a k
  have h3 : ((ypos a (k + 1) : ℕ+) : ℕ)
      = ((bsum (a.drop (blk a (k + 1)).1) (blk a (k + 1)).2 : ℕ+) : ℕ) := rfl
  omega

/-! ### The new ingredient: sums over ARBITRARY finite sets of blocks -/

/-- Dropping fewer entries can only enlarge the finite-sums set. -/
theorem FS_drop_mono (a : Stream' ℕ+) {i m : ℕ} (h : i ≤ m) {p : ℕ+}
    (hp : p ∈ FS (a.drop m)) : p ∈ FS (a.drop i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hd : a.drop (i + d) = (a.drop i).drop d := by
    rw [Stream'.drop_drop]
  rw [hd] at hp
  exact FS_iter_tail_sub_FS (a.drop i) d hp

/-- **Full Hindman strength.**  The sum of the block values over ANY finite nonempty set `K` of
block indices is itself a finite sum of the stream — not merely the sum of two blocks.  Stated
with the value in `ℕ` because `ℕ+` carries no additive identity, so `Finset.sum` is unavailable
there. -/
theorem ypos_finset_sum_mem (a : Stream' ℕ+) :
    ∀ (n : ℕ) (K : Finset ℕ), K.card = n → K.Nonempty → ∀ j : ℕ, (∀ k ∈ K, j ≤ k) →
      ∃ p : ℕ+, p ∈ FS (a.drop (blk a j).1) ∧
        ((p : ℕ+) : ℕ) = ∑ k ∈ K, ((ypos a k : ℕ+) : ℕ) := by
  intro n
  induction n with
  | zero =>
      intro K hcard hK _ _
      rw [Finset.card_eq_zero] at hcard
      subst hcard
      exact absurd hK (by simp)
  | succ n ih =>
      intro K hcard hK j hj
      have hmin0 : K.min' hK ∈ K := K.min'_mem hK
      obtain ⟨j', hj'K, hmin⟩ : ∃ j' ∈ K, ∀ k ∈ K, j' ≤ k :=
        ⟨K.min' hK, hmin0, fun k hk => K.min'_le k hk⟩
      have hjj' : j ≤ j' := hj j' hj'K
      have hstart : (blk a j).1 ≤ (blk a j').1 := (blk_fst_strictMono a).monotone hjj'
      have hcard' : (K.erase j').card = n := by
        rw [Finset.card_erase_of_mem hj'K, hcard]
        rfl
      have hsplit : ∑ k ∈ K, ((ypos a k : ℕ+) : ℕ)
          = ((ypos a j' : ℕ+) : ℕ) + ∑ k ∈ K.erase j', ((ypos a k : ℕ+) : ℕ) :=
        (Finset.add_sum_erase K (fun k => ((ypos a k : ℕ+) : ℕ)) hj'K).symm
      have hyp : ypos a j' = bsum (a.drop (blk a j').1) (blk a j').2 := rfl
      rcases Finset.eq_empty_or_nonempty (K.erase j') with hE | hNE
      · refine ⟨ypos a j', ?_, ?_⟩
        · refine FS_drop_mono a hstart ?_
          rw [hyp]
          exact bsum_mem (a.drop (blk a j').1) (blk a j').2
        · rw [hsplit, hE, Finset.sum_empty, Nat.add_zero]
      · have hgt : ∀ k ∈ K.erase j', j' + 1 ≤ k := by
          intro k hk
          have hkK : k ∈ K := Finset.mem_of_mem_erase hk
          have hne : k ≠ j' := Finset.ne_of_mem_erase hk
          have hle := hmin k hkK
          omega
        obtain ⟨q, hq, hqval⟩ := ih (K.erase j') hcard' hNE (j' + 1) hgt
        have hstep : (blk a (j' + 1)).1 = (blk a j').1 + ((blk a j').2 + 1) := by
          rw [blk_succ_fst]
          omega
        have hq2 : q ∈ FS ((a.drop (blk a j').1).drop ((blk a j').2 + 1)) := by
          rw [Stream'.drop_drop, ← hstep]
          exact hq
        have hp := bsum_add_mem (a.drop (blk a j').1) (blk a j').2 q hq2
        refine ⟨ypos a j' + q, ?_, ?_⟩
        · refine FS_drop_mono a hstart ?_
          rw [hyp]
          exact hp
        · rw [hsplit, PNat.add_coe, hqval]

/-! ### The promoted theorem -/

/-- **Erdos 949, countable analogue, FULL FINITE-SUMS FORM.**

For every sum-free `S ⊆ ℝ` there is an INFINITE set `A` of positive naturals such that for every
nonempty finite subset `T ⊆ A`, the sum `∑ T` (a sum of DISTINCT elements of `A`) lies outside
`S`, and so does `2 * ∑ T`.

The first conjunct is exactly `FS(A) ∩ S = ∅`, the full strength of Hindman's theorem.  The
second conjunct carries the doubling information, which is what makes the diagonal case of the
old pairwise statement a consequence (see `erdos949_countable_analogue` below). -/
theorem erdos949_hindman_full_finite_sums (S : Set ℝ)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      ∀ T : Finset ℕ, T.Nonempty → (↑T : Set ℕ) ⊆ A →
        ((((∑ n ∈ T, n : ℕ)) : ℝ) ∉ S ∧ ((2 * (∑ n ∈ T, n : ℕ) : ℕ) : ℝ) ∉ S) := by
  classical
  set c1 : Set ℕ+ := {n : ℕ+ | ((n : ℕ) : ℝ) ∈ S} with hc1
  set c2 : Set ℕ+ := {n : ℕ+ | ((n : ℕ) : ℝ) ∉ S ∧ ((2 * (n : ℕ) : ℕ) : ℝ) ∈ S} with hc2
  set c3 : Set ℕ+ := {n : ℕ+ | ((n : ℕ) : ℝ) ∉ S ∧ ((2 * (n : ℕ) : ℕ) : ℝ) ∉ S} with hc3
  set cover : Set (Set ℕ+) := {c1, c2, c3} with hcover
  have hfin : cover.Finite := by
    rw [hcover]
    exact ((Set.finite_singleton c3).insert c2).insert c1
  have hcov : (⊤ : Set ℕ+) ⊆ ⋃₀ cover := by
    intro n _
    by_cases h1 : ((n : ℕ) : ℝ) ∈ S
    · exact ⟨c1, by simp [hcover], h1⟩
    · by_cases h2 : ((2 * (n : ℕ) : ℕ) : ℝ) ∈ S
      · exact ⟨c2, by simp [hcover], ⟨h1, h2⟩⟩
      · exact ⟨c3, by simp [hcover], ⟨h1, h2⟩⟩
  obtain ⟨c, hcmem, a, hFS⟩ := Hindman.exists_FS_of_finite_cover cover hfin hcov
  have hy : ∀ k, ypos a k ∈ c := fun k => hFS (ypos_mem a k)
  have hu := hy 0
  have hv := hy 1
  have hcastadd : ∀ x y : ℕ+, (((x + y : ℕ+) : ℕ) : ℝ) = ((x : ℕ) : ℝ) + ((y : ℕ) : ℝ) := by
    intro x y; rw [PNat.add_coe]; push_cast; ring
  have hcast2 : ∀ x y : ℕ+, ((2 * (((x + y : ℕ+) : ℕ)) : ℕ) : ℝ)
      = ((2 * (x : ℕ) : ℕ) : ℝ) + ((2 * (y : ℕ) : ℕ) : ℝ) := by
    intro x y; rw [PNat.add_coe]; push_cast; ring
  -- The pair `{0, 1}` of blocks is enough to rule out the two bad colour cells.
  have huv : ypos a 0 + ypos a 1 ∈ c := by
    obtain ⟨p, hp, hpval⟩ :=
      ypos_finset_sum_mem a ({0, 1} : Finset ℕ).card ({0, 1} : Finset ℕ) rfl ⟨0, by simp⟩ 0
        (fun k _ => Nat.zero_le k)
    have hpa : p ∈ FS a := FS_iter_tail_sub_FS a (blk a 0).1 hp
    have hsum : ∑ k ∈ ({0, 1} : Finset ℕ), ((ypos a k : ℕ+) : ℕ)
        = ((ypos a 0 : ℕ+) : ℕ) + ((ypos a 1 : ℕ+) : ℕ) := by
      rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    have hpe : p = ypos a 0 + ypos a 1 := by
      have : ((p : ℕ+) : ℕ) = (((ypos a 0 + ypos a 1 : ℕ+) : ℕ)) := by
        rw [hpval, hsum, PNat.add_coe]
      exact PNat.coe_injective this
    rw [← hpe]
    exact hFS hpa
  have hcfinal : c = c3 := by
    rcases hcmem with h | h | h
    · exfalso
      rw [h, hc1] at hu hv huv
      simp only [Set.mem_setOf_eq] at hu hv huv
      exact hS _ hu _ hv (by rwa [hcastadd] at huv)
    · exfalso
      rw [h, hc2] at hu hv huv
      simp only [Set.mem_setOf_eq] at hu hv huv
      have huv2 := huv.2
      rw [hcast2] at huv2
      exact hS _ hu.2 _ hv.2 huv2
    · exact h
  subst hcfinal
  -- The witness set: the (strictly increasing, hence distinct) block values.
  set f : ℕ → ℕ := fun k => ((ypos a k : ℕ+) : ℕ) with hf
  have hinj : Function.Injective f := (ypos_strictMono a).injective
  refine ⟨Set.range f, Set.infinite_range_of_injective hinj, ?_, ?_⟩
  · rintro n ⟨k, rfl⟩
    exact (ypos a k).pos
  · intro T hT hTA
    -- pull `T` back to a finite set of block indices
    set K : Finset ℕ := T.preimage f hinj.injOn with hK
    have hmemK : ∀ k : ℕ, k ∈ K ↔ f k ∈ T := by
      intro k
      rw [hK, Finset.mem_preimage]
    have himg : K.image f = T := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact (hmemK k).mp hk
      · intro hx
        obtain ⟨k, hk⟩ := hTA (Finset.mem_coe.mpr hx)
        refine ⟨k, (hmemK k).mpr ?_, hk⟩
        rw [hk]
        exact hx
    have hKne : K.Nonempty := by
      obtain ⟨x, hx⟩ := hT
      obtain ⟨k, hk⟩ := hTA (Finset.mem_coe.mpr hx)
      exact ⟨k, (hmemK k).mpr (by rw [hk]; exact hx)⟩
    have hsumT : ∑ n ∈ T, n = ∑ k ∈ K, f k := by
      rw [← himg, Finset.sum_image (fun x _ y _ h => hinj h)]
    obtain ⟨p, hp, hpval⟩ :=
      ypos_finset_sum_mem a K.card K rfl hKne 0 (fun k _ => Nat.zero_le k)
    have hpa : p ∈ FS a := FS_iter_tail_sub_FS a (blk a 0).1 hp
    have hpc := hFS hpa
    rw [hc3] at hpc
    simp only [Set.mem_setOf_eq] at hpc
    have hval : ((p : ℕ+) : ℕ) = ∑ n ∈ T, n := by
      rw [hpval, hsumT]
    constructor
    · have h1 := hpc.1
      rwa [hval] at h1
    · have h2 := hpc.2
      rwa [hval] at h2

/-! ### The old pairwise statement, now a corollary -/

/-- **Erdos 949, countable analogue (pairwise form)** — the statement kernel-sealed in
`Erdos949Hindman.lean`, here DERIVED from the full finite-sums form above.  This is what makes
the promotion visibly strictly stronger: the old theorem is the `|T| ≤ 2` shadow of the new
one. -/
theorem erdos949_countable_analogue (S : Set ℝ)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      (∀ n ∈ A, ((n : ℕ) : ℝ) ∉ S) ∧
      (∀ m ∈ A, ∀ n ∈ A, ((m + n : ℕ) : ℝ) ∉ S) := by
  classical
  obtain ⟨A, hinf, hpos, hfull⟩ := erdos949_hindman_full_finite_sums S hS
  have hsingle : ∀ n ∈ A, (↑({n} : Finset ℕ) : Set ℕ) ⊆ A := by
    intro n hn
    simp only [Finset.coe_singleton, Set.singleton_subset_iff]
    exact hn
  refine ⟨A, hinf, hpos, ?_, ?_⟩
  · intro n hn
    have h := (hfull {n} (Finset.singleton_nonempty n) (hsingle n hn)).1
    rwa [Finset.sum_singleton] at h
  · intro m hm n hn
    rcases eq_or_ne m n with rfl | hne
    · have h := (hfull {m} (Finset.singleton_nonempty m) (hsingle m hm)).2
      rw [Finset.sum_singleton] at h
      have hmm : m + m = 2 * m := by omega
      rwa [hmm]
    · have hsub : (↑({m, n} : Finset ℕ) : Set ℕ) ⊆ A := by
        intro x hx
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hm
        · exact hn
      have h := (hfull {m, n} ⟨m, by simp⟩ hsub).1
      rwa [Finset.sum_insert (by simpa using hne), Finset.sum_singleton] at h

/-! ### Non-vacuity controls -/

/-- Known-answer control for the FULL form: the conclusion shape is NOT satisfiable for an
arbitrary `S`, so the promoted theorem is not vacuous and the sum-free hypothesis is
load-bearing.  For `S = univ` (which is not sum-free) no such infinite `A` exists. -/
theorem erdos949_hindman_full_finite_sums_control :
    ¬ ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      ∀ T : Finset ℕ, T.Nonempty → (↑T : Set ℕ) ⊆ A →
        ((((∑ n ∈ T, n : ℕ)) : ℝ) ∉ (Set.univ : Set ℝ) ∧
          ((2 * (∑ n ∈ T, n : ℕ) : ℕ) : ℝ) ∉ (Set.univ : Set ℝ)) := by
  rintro ⟨A, hA, -, h⟩
  obtain ⟨n, hn⟩ := hA.nonempty
  have hsub : (↑({n} : Finset ℕ) : Set ℕ) ⊆ A := by
    simp only [Finset.coe_singleton, Set.singleton_subset_iff]
    exact hn
  exact (h {n} (Finset.singleton_nonempty n) hsub).1 (Set.mem_univ _)

/-- Known-answer control for the pairwise form (kept from `Erdos949Hindman.lean`). -/
theorem erdos949_countable_analogue_control :
    ¬ ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      (∀ n ∈ A, ((n : ℕ) : ℝ) ∉ (Set.univ : Set ℝ)) ∧
      (∀ m ∈ A, ∀ n ∈ A, ((m + n : ℕ) : ℝ) ∉ (Set.univ : Set ℝ)) := by
  rintro ⟨A, hA, -, h, -⟩
  obtain ⟨n, hn⟩ := hA.nonempty
  exact h n hn (Set.mem_univ _)

end Erdos949HindmanFS

#print axioms Erdos949HindmanFS.bsum_zero
#print axioms Erdos949HindmanFS.bsum_succ
#print axioms Erdos949HindmanFS.bsum_mem
#print axioms Erdos949HindmanFS.bsum_add_mem
#print axioms Erdos949HindmanFS.le_bsum
#print axioms Erdos949HindmanFS.blk_succ_fst
#print axioms Erdos949HindmanFS.blk_succ_snd
#print axioms Erdos949HindmanFS.ypos_mem
#print axioms Erdos949HindmanFS.blk_fst_strictMono
#print axioms Erdos949HindmanFS.ypos_strictMono
#print axioms Erdos949HindmanFS.FS_drop_mono
#print axioms Erdos949HindmanFS.ypos_finset_sum_mem
#print axioms Erdos949HindmanFS.erdos949_hindman_full_finite_sums
#print axioms Erdos949HindmanFS.erdos949_countable_analogue
#print axioms Erdos949HindmanFS.erdos949_hindman_full_finite_sums_control
#print axioms Erdos949HindmanFS.erdos949_countable_analogue_control
