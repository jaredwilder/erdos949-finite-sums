import Mathlib

/-!
Erdos 949 -- the countable analogue, kernel-checked.

For every sum-free `S` in the reals there is an INFINITE set `A` of positive naturals with
`A` disjoint from `S` and `A + A` disjoint from `S` (diagonal included).

Route: Hindman's finite-sums theorem (`Hindman.exists_FS_of_finite_cover`) over the additive
semigroup `PNat`, a three-cell colouring of `n` by `(n in S, 2n in S)`, then an explicit
block-sum construction to extract a strictly increasing sequence inside the monochromatic
FS-set.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Hindman

namespace Erdos949Hindman

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

/-- Sums drawn from two different blocks stay inside the finite-sums set. -/
theorem ypos_add_mem (a : Stream' ℕ+) (j k : ℕ) (hjk : j < k) :
    ypos a j + ypos a k ∈ FS a := by
  have hmono : (blk a (j + 1)).1 ≤ (blk a k).1 :=
    (blk_fst_strictMono a).monotone (by omega : j + 1 ≤ k)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmono
  have hstep : (blk a (j + 1)).1 = (blk a j).1 + ((blk a j).2 + 1) := by
    rw [blk_succ_fst]; omega
  have hin2 : ypos a k ∈ FS ((a.drop (blk a j).1).drop ((blk a j).2 + 1)) := by
    have hbase : ypos a k ∈ FS (a.drop (blk a k).1) :=
      bsum_mem (a.drop (blk a k).1) (blk a k).2
    have hsplit : a.drop (blk a k).1
        = (a.drop ((blk a j).1 + ((blk a j).2 + 1))).drop d := by
      rw [Stream'.drop_drop, hd, hstep]
    rw [hsplit] at hbase
    have := FS_iter_tail_sub_FS (a.drop ((blk a j).1 + ((blk a j).2 + 1))) d hbase
    rwa [Stream'.drop_drop]
  have hfin := bsum_add_mem (a.drop (blk a j).1) (blk a j).2 (ypos a k) hin2
  exact FS_iter_tail_sub_FS a (blk a j).1 hfin

/-- **Erdos 949, countable analogue.**  For every sum-free `S ⊆ ℝ` there is an infinite set `A`
of positive naturals, disjoint from `S`, with `A + A` disjoint from `S` (diagonal included). -/
theorem erdos949_countable_analogue (S : Set ℝ)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      (∀ n ∈ A, ((n : ℕ) : ℝ) ∉ S) ∧
      (∀ m ∈ A, ∀ n ∈ A, ((m + n : ℕ) : ℝ) ∉ S) := by
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
  have hpair : ∀ j k, j < k → ypos a j + ypos a k ∈ c := fun j k h => hFS (ypos_add_mem a j k h)
  have hu := hy 0
  have hv := hy 1
  have huv := hpair 0 1 (by norm_num)
  have hcastadd : ∀ x y : ℕ+, (((x + y : ℕ+) : ℕ) : ℝ) = ((x : ℕ) : ℝ) + ((y : ℕ) : ℝ) := by
    intro x y; rw [PNat.add_coe]; push_cast; ring
  have hcast2 : ∀ x y : ℕ+, ((2 * (((x + y : ℕ+) : ℕ)) : ℕ) : ℝ)
      = ((2 * (x : ℕ) : ℕ) : ℝ) + ((2 * (y : ℕ) : ℕ) : ℝ) := by
    intro x y; rw [PNat.add_coe]; push_cast; ring
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
  refine ⟨Set.range (fun k => ((ypos a k : ℕ+) : ℕ)), ?_, ?_, ?_, ?_⟩
  · exact Set.infinite_range_of_injective (ypos_strictMono a).injective
  · rintro n ⟨k, rfl⟩
    exact (ypos a k).pos
  · rintro n ⟨k, rfl⟩
    have hk := hy k
    rw [hc3] at hk
    exact hk.1
  · rintro m ⟨j, rfl⟩ n ⟨k, rfl⟩
    rcases lt_trichotomy j k with h | h | h
    · have hmem := hpair j k h
      rw [hc3] at hmem
      have h1 := hmem.1
      rwa [PNat.add_coe] at h1
    · subst h
      have hk := hy j
      rw [hc3] at hk
      have h2 := hk.2
      have hdup : ((ypos a j : ℕ+) : ℕ) + ((ypos a j : ℕ+) : ℕ)
          = 2 * ((ypos a j : ℕ+) : ℕ) := by ring
      rw [hdup]
      exact h2
    · have hmem := hpair k j h
      rw [hc3] at hmem
      have h1 := hmem.1
      rw [PNat.add_coe] at h1
      rw [Nat.add_comm]
      exact h1

/-- Known-answer control: the conclusion shape is NOT satisfiable for an arbitrary `S`, so the
theorem above is not vacuous and the sum-free hypothesis is load-bearing.  For `S = univ`
(which is not sum-free) no such infinite `A` exists. -/
theorem erdos949_countable_analogue_control :
    ¬ ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
      (∀ n ∈ A, ((n : ℕ) : ℝ) ∉ (Set.univ : Set ℝ)) ∧
      (∀ m ∈ A, ∀ n ∈ A, ((m + n : ℕ) : ℝ) ∉ (Set.univ : Set ℝ)) := by
  rintro ⟨A, hA, -, h, -⟩
  obtain ⟨n, hn⟩ := hA.nonempty
  exact h n hn (Set.mem_univ _)

end Erdos949Hindman
