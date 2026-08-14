/- GID: D5/S1/Words/Complexity/GoldenSubshiftMinimality
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/GoldenSubshiftMinimality
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Uniform recurrence makes every golden-subshift member share the golden factor language, so every member has dense forward orbit and no proper nonempty closed shift-invariant subsystem exists. Mathlib AddAction.IsMinimal instance registration on the subshift subtype is deliberately not covered and remains a future node. -/

import D5.S1.Words.Complexity.SubshiftTopology
import D5.S1.Words.GoldenUniformRecurrence

namespace D5.S1.Words.Complexity.GoldenSubshiftMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Words
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open D5.S1.Words.Complexity.SubshiftTopology
open Set SymbolicDynamics

noncomputable section

variable {A : Type*} [Fintype A]

/-- Iterated shift stays in the subshift (repo already has the one-step version). -/
private theorem shift_mem_wordSubshift (x : ℕ → A) {y : ℕ → A}
    (hy : y ∈ wordSubshift x) (i : ℕ) :
    FullShift.shift i y ∈ wordSubshift x := by
  induction i with
  | zero => simpa using hy
  | succ i ih =>
      have hshift : FullShift.shift (Nat.succ i) y =
          fun j ↦ FullShift.shift i y (j + 1) := by
        funext j
        simp only [FullShift.shift_apply]
        congr 1
        omega
      rw [hshift]
      exact wordSubshift_shift_invariant x ih

/-- Every factor of a subshift element is a factor of the base word. -/
theorem wordFactorSet_subset_of_mem_wordSubshift {x y : ℕ → A}
    (hy : y ∈ wordSubshift x) (n : ℕ) :
    wordFactorSet y n ⊆ wordFactorSet x n := by
  intro w hw
  obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hw
  have h := shift_mem_wordSubshift x hy i n
  have hcoe : (fun k : Fin n ↦ (FullShift.shift i y) k.val) = wordFactor y n i := by
    funext k
    simp [FullShift.shift_apply, wordFactor]
  rwa [hcoe] at h

/-- Uniform recurrence forces every golden factor into every golden-subshift element. -/
theorem golden_wordFactorSet_subset_of_mem_wordSubshift {y : ℕ → Bool}
    (hy : y ∈ wordSubshift goldenWord) (n : ℕ) :
    wordFactorSet goldenWord n ⊆ wordFactorSet y n := by
  intro w hw
  obtain ⟨p, rfl⟩ := mem_wordFactorSet.mp hw
  set R := goldenRecurrenceBound n with hRdef
  obtain ⟨q, hq⟩ := mem_wordFactorSet.mp (hy R)
  have hlist : goldenFactor n p ∈ goldenFactorSet n := mem_goldenFactorSet.mpr ⟨p, rfl⟩
  obtain ⟨j, hqj, hjend, hfac⟩ := golden_factor_uniformly_recurrent hlist q
  have hfun : wordFactor goldenWord n p = wordFactor goldenWord n j :=
    List.ofFn_inj.mp hfac
  refine mem_wordFactorSet.mpr ⟨j - q, ?_⟩
  funext k
  have hk : j - q + k.val < R := by
    have := k.isLt
    omega
  have hy' := congrFun hq ⟨j - q + k.val, hk⟩
  have hgold : q + (j - q + k.val) = j + k.val := by omega
  have hfk := congrFun hfun k
  simp only [wordFactor] at hy' hfk ⊢
  rw [hy', hgold, hfk]

/-- Every element of the golden subshift has the golden factor language. -/
theorem golden_wordFactorSet_eq_of_mem_wordSubshift {y : ℕ → Bool}
    (hy : y ∈ wordSubshift goldenWord) (n : ℕ) :
    wordFactorSet y n = wordFactorSet goldenWord n :=
  Finset.Subset.antisymm (wordFactorSet_subset_of_mem_wordSubshift hy n)
    (golden_wordFactorSet_subset_of_mem_wordSubshift hy n)

/-- A member of the golden subshift generates the same prefix-language subshift. -/
theorem wordSubshift_eq_of_mem_golden_wordSubshift {y : ℕ → Bool}
    (hy : y ∈ wordSubshift goldenWord) :
    wordSubshift y = wordSubshift goldenWord := by
  ext z
  constructor
  · intro hz n
    exact (golden_wordFactorSet_eq_of_mem_wordSubshift hy n) ▸ hz n
  · intro hz n
    exact (golden_wordFactorSet_eq_of_mem_wordSubshift hy n).symm ▸ hz n

/-- Every member's forward orbit is dense in the golden subshift. -/
theorem golden_wordSubshift_minimal {y : ℕ → Bool}
    (hy : y ∈ wordSubshift goldenWord) :
    closure (Set.range fun i : ℕ ↦ FullShift.shift i y) = wordSubshift goldenWord := by
  rw [closure_shift_orbit_eq_wordSubshift y, wordSubshift_eq_of_mem_golden_wordSubshift hy]

/-- There is no proper nonempty closed shift-invariant golden subsystem. -/
theorem golden_wordSubshift_eq_of_isClosed_shift_invariant {S : Set (ℕ → Bool)}
    (hS : S ⊆ wordSubshift goldenWord) (hne : S.Nonempty) (hclosed : IsClosed S)
    (hinv : ∀ y ∈ S, (fun j ↦ y (j + 1)) ∈ S) :
    S = wordSubshift goldenWord := by
  obtain ⟨y, hyS⟩ := hne
  have horb : ∀ i : ℕ, FullShift.shift i y ∈ S := by
    intro i
    induction i with
    | zero => simpa using hyS
    | succ i ih =>
        have hshift : FullShift.shift (Nat.succ i) y =
            fun j ↦ FullShift.shift i y (j + 1) := by
          funext j
          simp only [FullShift.shift_apply]
          congr 1
          omega
        rw [hshift]
        exact hinv _ ih
  refine Set.Subset.antisymm hS ?_
  rw [← golden_wordSubshift_minimal (hS hyS)]
  exact hclosed.closure_subset_iff.mpr (by rintro _ ⟨i, rfl⟩; exact horb i)

#print axioms wordFactorSet_subset_of_mem_wordSubshift
#print axioms golden_wordFactorSet_subset_of_mem_wordSubshift
#print axioms golden_wordFactorSet_eq_of_mem_wordSubshift
#print axioms wordSubshift_eq_of_mem_golden_wordSubshift
#print axioms golden_wordSubshift_minimal
#print axioms golden_wordSubshift_eq_of_isClosed_shift_invariant

end

end D5.S1.Words.Complexity.GoldenSubshiftMinimality
