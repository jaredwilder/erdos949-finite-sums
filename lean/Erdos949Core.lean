import Mathlib

/-!
Erdős 949, P0 promotion (GPT gold pack A6, audited 2026-09-01; kernel round 2026-09-02).
The raw verifier searched S ⊆ {1..24} with q ≤ 12. The audit's two-case hand proof shrinks
the finite core to S ⊆ {1..10}, q ≤ 5. Here the finite core is decided by the kernel over
all 1024 subsets, and then transferred to every sum-free S ⊂ ℝ: some q ∈ {1,...,5} has
q ∉ S and 2q ∉ S.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

theorem erdos949_finite_core :
    ∀ S ∈ (Finset.Icc 1 10).powerset,
      (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) → ∃ q ∈ Finset.Icc 1 5, q ∉ S ∧ 2 * q ∉ S := by
  decide +kernel

theorem erdos949_universal (S : Set ℝ) (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 5 ∧ ((q : ℕ) : ℝ) ∉ S ∧ ((2 * q : ℕ) : ℝ) ∉ S := by
  classical
  let S' : Finset ℕ := (Finset.Icc 1 10).filter (fun n => ((n : ℕ) : ℝ) ∈ S)
  have hS'mem : S' ∈ (Finset.Icc 1 10).powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hfree : ∀ a ∈ S', ∀ b ∈ S', a + b ∉ S' := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hab' := (Finset.mem_filter.mp hab).2
    push_cast at hab'
    exact hS _ ha' _ hb' hab'
  obtain ⟨q, hq, hqS, h2qS⟩ := erdos949_finite_core S' hS'mem hfree
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq5 : q ≤ 5 := (Finset.mem_Icc.mp hq).2
  refine ⟨q, hq1, hq5, ?_, ?_⟩
  · intro h
    exact hqS (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, by omega⟩, h⟩)
  · intro h
    exact h2qS (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h⟩)

/-- Sharpness (novelty hunt 2026-09-02): 5 is best possible. The sum-free witness {1,4,6}
defeats every q ≤ 4: for each q ∈ {1,2,3,4}, q or 2q lies in the set. Kernel-decided. -/
theorem erdos949_five_sharp :
    (∀ a ∈ ({1, 4, 6} : Finset ℕ), ∀ b ∈ ({1, 4, 6} : Finset ℕ), a + b ∉ ({1, 4, 6} : Finset ℕ))
    ∧ ∀ q ∈ Finset.Icc 1 4, q ∈ ({1, 4, 6} : Finset ℕ) ∨ 2 * q ∈ ({1, 4, 6} : Finset ℕ) := by
  decide

/-- The same witness transferred to ℝ: a sum-free S ⊂ ℝ for which no q ≤ 4 works, so the
universal q ≤ 5 theorem above is sharp over ℝ as well. -/
theorem erdos949_five_sharp_real :
    ∃ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) ∧
      ∀ q : ℕ, 1 ≤ q → q ≤ 4 → ((q : ℝ) ∈ S ∨ ((2 * q : ℕ) : ℝ) ∈ S) := by
  refine ⟨{1, 4, 6}, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hab
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hab with h | h | h <;> norm_num at h
  · intro q h1 h4
    interval_cases q <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> norm_num
