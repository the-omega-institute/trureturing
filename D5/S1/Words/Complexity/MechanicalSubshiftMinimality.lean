/- GID: D5/S1/Words/Complexity/MechanicalSubshiftMinimality
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/MechanicalSubshiftMinimality
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Uniform recurrence makes every member of an irrational lower-mechanical-word subshift share its factor language, hence every member has dense forward orbit and no proper nonempty closed shift-invariant subsystem exists; no intercept-independence or AddAction.IsMinimal registration is claimed. -/

import D5.S1.Words.Complexity.GoldenSubshiftMinimality
import D5.S1.Words.Mechanical.MechanicalUniformRecurrence

namespace D5.S1.Words.Complexity.MechanicalSubshiftMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Words
open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.GoldenSubshiftMinimality
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open D5.S1.Words.Complexity.SubshiftTopology
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalUniformRecurrence
open Set SymbolicDynamics

noncomputable section

/-- Uniform recurrence forces every mechanical factor into every member of its subshift. -/
theorem mechanical_wordFactorSet_subset_of_mem_wordSubshift {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hα_irr : Irrational α) {y : ℕ → Bool}
    (hy : y ∈ wordSubshift (lowerMechanicalWord α ρ)) (n : ℕ) :
    wordFactorSet (lowerMechanicalWord α ρ) n ⊆ wordFactorSet y n := by
  intro w hw
  obtain ⟨p, rfl⟩ := mem_wordFactorSet.mp hw
  have hlist : lowerMechanicalFactor α ρ n p ∈ lowerMechanicalFactorSet α ρ n :=
    mem_lowerMechanicalFactorSet.mpr ⟨p, rfl⟩
  obtain ⟨R, hR⟩ :=
    lower_mechanical_factor_uniformly_recurrent hα0 hα1 hα_irr hlist
  obtain ⟨q, hq⟩ := mem_wordFactorSet.mp (hy R)
  obtain ⟨j, hqj, hjend, hfac⟩ := hR q
  have hlistfun : List.ofFn (wordFactor (lowerMechanicalWord α ρ) n p) =
      List.ofFn (wordFactor (lowerMechanicalWord α ρ) n j) := by
    change lowerMechanicalFactor α ρ n p = lowerMechanicalFactor α ρ n j
    exact hfac
  have hfun : wordFactor (lowerMechanicalWord α ρ) n p =
      wordFactor (lowerMechanicalWord α ρ) n j :=
    List.ofFn_inj.mp hlistfun
  refine mem_wordFactorSet.mpr ⟨j - q, ?_⟩
  funext k
  have hk : j - q + k.val < R := by
    have := k.isLt
    omega
  have hy' := congrFun hq ⟨j - q + k.val, hk⟩
  have hmechanical : q + (j - q + k.val) = j + k.val := by omega
  have hfk := congrFun hfun k
  simp only [wordFactor] at hy' hfk ⊢
  rw [hy', hmechanical, hfk]

/-- Every member of an irrational lower-mechanical-word subshift has the base language. -/
theorem mechanical_wordFactorSet_eq_of_mem_wordSubshift {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hα_irr : Irrational α) {y : ℕ → Bool}
    (hy : y ∈ wordSubshift (lowerMechanicalWord α ρ)) (n : ℕ) :
    wordFactorSet y n = wordFactorSet (lowerMechanicalWord α ρ) n :=
  Finset.Subset.antisymm (wordFactorSet_subset_of_mem_wordSubshift hy n)
    (mechanical_wordFactorSet_subset_of_mem_wordSubshift hα0 hα1 hα_irr hy n)

/-- A member generates the same prefix-language subshift as its lower mechanical word. -/
theorem wordSubshift_eq_of_mem_mechanical_wordSubshift {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hα_irr : Irrational α) {y : ℕ → Bool}
    (hy : y ∈ wordSubshift (lowerMechanicalWord α ρ)) :
    wordSubshift y = wordSubshift (lowerMechanicalWord α ρ) := by
  ext z
  constructor
  · intro hz n
    exact (mechanical_wordFactorSet_eq_of_mem_wordSubshift hα0 hα1 hα_irr hy n) ▸ hz n
  · intro hz n
    exact
      (mechanical_wordFactorSet_eq_of_mem_wordSubshift hα0 hα1 hα_irr hy n).symm ▸ hz n

/-- Every member's forward orbit is dense in its irrational lower mechanical word subshift. -/
theorem mechanical_wordSubshift_minimal {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hα_irr : Irrational α) {y : ℕ → Bool}
    (hy : y ∈ wordSubshift (lowerMechanicalWord α ρ)) :
    closure (Set.range fun i : ℕ ↦ FullShift.shift i y) =
      wordSubshift (lowerMechanicalWord α ρ) := by
  rw [closure_shift_orbit_eq_wordSubshift y,
    wordSubshift_eq_of_mem_mechanical_wordSubshift hα0 hα1 hα_irr hy]

/-- There is no proper nonempty closed shift-invariant mechanical subsystem. -/
theorem mechanical_wordSubshift_eq_of_isClosed_shift_invariant {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hα_irr : Irrational α) {S : Set (ℕ → Bool)}
    (hS : S ⊆ wordSubshift (lowerMechanicalWord α ρ)) (hne : S.Nonempty)
    (hclosed : IsClosed S) (hinv : ∀ y ∈ S, (fun j ↦ y (j + 1)) ∈ S) :
    S = wordSubshift (lowerMechanicalWord α ρ) := by
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
  rw [← mechanical_wordSubshift_minimal hα0 hα1 hα_irr (hS hyS)]
  exact hclosed.closure_subset_iff.mpr (by rintro _ ⟨i, rfl⟩; exact horb i)

#print axioms mechanical_wordFactorSet_subset_of_mem_wordSubshift
#print axioms mechanical_wordFactorSet_eq_of_mem_wordSubshift
#print axioms wordSubshift_eq_of_mem_mechanical_wordSubshift
#print axioms mechanical_wordSubshift_minimal
#print axioms mechanical_wordSubshift_eq_of_isClosed_shift_invariant

end

end D5.S1.Words.Complexity.MechanicalSubshiftMinimality
