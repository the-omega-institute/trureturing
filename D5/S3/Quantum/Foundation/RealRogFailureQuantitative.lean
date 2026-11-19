/- GID: D5/S3/Quantum/Foundation/RealRogFailureQuantitative
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/RealRogFailureQuantitative
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The original cone base norm attains a global primal minimum with the same unit. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import D5.S3.Quantum.Dynamics.BaseNormContraction

/-!
The original-carrier primal optimization retains the same arbitrary strictly
positive unit and the entire compact base. The same pair realizes the base-norm
infimum, minimizes every feasible decomposition cost and has both stated mass
formulas. Full-support compression, determinant normalization, dual attainment,
failed-pair extraction and return transport remain open. No completion of
Proposition 93.3 or block classification is asserted.
-/

noncomputable section

namespace D5.S3.Quantum.Foundation.RealRogFailureQuantitative

open CircuitBalancedConfirmation

section OriginalPrimal

open scoped Pointwise
open D5.S3.Quantum.Dynamics.BaseNormContraction

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

omit [FiniteDimensional ℝ A] in
theorem mass_cap_compact (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hK : IsCompact (base C u))
    (hu : ∀ a ∈ C, a ≠ 0 → 0 < u a) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {a : A | a ∈ C ∧ u a ≤ R} := by
  have heq : {a : A | a ∈ C ∧ u a ≤ R} =
      (Set.Icc 0 R : Set ℝ) • insert 0 (base C u) := by
    ext a
    constructor
    · rintro ⟨ha, hmass⟩
      by_cases ha0 : a = 0
      · subst a
        exact ⟨0, ⟨le_rfl, hR⟩, 0, Set.mem_insert _ _, zero_smul _ _⟩
      have hpos := hu a ha ha0
      refine ⟨u a, ⟨hpos.le, hmass⟩, (u a)⁻¹ • a, Set.mem_insert_of_mem _ ?_, ?_⟩
      · exact normalized_mem hu ha ha0
      · simp [smul_smul, hpos.ne']
    · rintro ⟨r, hr, k, hk, rfl⟩
      rcases hk with rfl | hk
      · simpa using And.intro C.zero_mem hR
      · exact ⟨C.smul_mem hr.1 hk.1, by simpa [hk.2] using hr.2⟩
  rw [heq]
  exact isCompact_Icc.smul_set (hK.insert 0)

/-- The infimum defining the original cone base norm is attained on that same
cone and with that same arbitrary strictly positive unit. This is the primal
part of (93.23); no dual effect or failed-pair extraction is assumed or supplied. -/
theorem original_primal_attainment (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hK : IsCompact (base C u))
    (hu : ∀ a ∈ C, a ≠ 0 → 0 < u a)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) (z : A) :
    ∃ X Y : A, X ∈ C ∧ Y ∈ C ∧ z = X - Y ∧
      u X + u Y = baseNorm C.toConvexCone u z ∧
      (∀ a b : A, a ∈ C → b ∈ C → z = a - b → u X + u Y ≤ u a + u b) ∧
      u X = (baseNorm C.toConvexCone u z + u z) / 2 ∧
      u Y = (baseNorm C.toConvexCone u z - u z) / 2 := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hz₀⟩ :=
    C.mem_span.mp (show z ∈ Submodule.span ℝ (C : Set A) by rw [hspan]; trivial)
  let R := u a₀ + u b₀
  have hR : 0 ≤ R := add_nonneg (functional_nonneg_on_cone C.toConvexCone u hu ha₀) (functional_nonneg_on_cone C.toConvexCone u hu hb₀)
  let cap : Set A := {a | a ∈ C ∧ u a ≤ R}
  let feasible : Set (A × A) := (cap ×ˢ cap) ∩ {ab | z = ab.1 - ab.2}
  have hcap : IsCompact cap := mass_cap_compact C u hK hu R hR
  have hfeasible : IsCompact feasible := (hcap.prod hcap).inter_right
    (isClosed_eq continuous_const (continuous_fst.sub continuous_snd))
  have hseed : (a₀, b₀) ∈ feasible := by
    refine ⟨⟨⟨ha₀, ?_⟩, ⟨hb₀, ?_⟩⟩, hz₀⟩ <;>
      dsimp [R] <;> linarith [functional_nonneg_on_cone C.toConvexCone u hu ha₀, functional_nonneg_on_cone C.toConvexCone u hu hb₀]
  have hcost : Continuous (fun ab : A × A => u ab.1 + u ab.2) :=
    (u.continuous_of_finiteDimensional.comp continuous_fst).add
      (u.continuous_of_finiteDimensional.comp continuous_snd)
  obtain ⟨XY, hXY, hmin⟩ := hfeasible.exists_isMinOn ⟨(a₀, b₀), hseed⟩ hcost.continuousOn
  have hbound : u XY.1 + u XY.2 ≤ R := hmin hseed
  have hglobal (a b : A) (ha : a ∈ C) (hb : b ∈ C) (hz : z = a - b) :
      u XY.1 + u XY.2 ≤ u a + u b := by
    by_cases hcostR : u a + u b ≤ R
    · apply hmin (a := (a, b))
      exact ⟨⟨⟨ha, (le_add_of_nonneg_right (functional_nonneg_on_cone C.toConvexCone u hu hb)).trans hcostR⟩,
        ⟨hb, (le_add_of_nonneg_left (functional_nonneg_on_cone C.toConvexCone u hu ha)).trans hcostR⟩⟩, hz⟩
    · exact hbound.trans (le_of_not_ge hcostR)
  have hinf : u XY.1 + u XY.2 = baseNorm C.toConvexCone u z := by
    apply Eq.symm
    apply IsLeast.csInf_eq
    refine ⟨⟨XY.1, XY.2, hXY.1.1.1, hXY.1.2.1, hXY.2, rfl⟩, ?_⟩
    rintro r ⟨a, b, ha, hb, hz, rfl⟩
    exact hglobal a b ha hb hz
  have hunit : u z = u XY.1 - u XY.2 := by rw [hXY.2, map_sub]
  refine ⟨XY.1, XY.2, hXY.1.1.1, hXY.1.2.1, hXY.2, hinf, hglobal, ?_, ?_⟩ <;>
    linarith

end OriginalPrimal

end D5.S3.Quantum.Foundation.RealRogFailureQuantitative
