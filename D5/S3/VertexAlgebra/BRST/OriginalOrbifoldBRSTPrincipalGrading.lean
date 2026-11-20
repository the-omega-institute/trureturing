/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPrincipalGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPrincipalGrading
   mirror-E: none(waiver:algebraic-original-orbifold-brst-principal-grading)
   anchors: []
   utility: none
   digest: The physical BRST Lie algebra has a finite-dimensional integer principal grading. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTRootNilpotence

/-! Borcherds's principal degree uses coordinates of pairing `-1`.
In the native hyperbolic basis of pairing `+1`, the second coordinate changes sign. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPrincipalGrading

open LatticeGeneratingFieldLocality (Charge)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)
open OriginalOrbifoldCriticalMatter (hyperbolicData orbifoldMode)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTMomentum
  (physicalMomentum physicalMomentum_grading degreeOne_bracket_mem_physicalMomentum)
open OriginalOrbifoldBRSTPhysicalSpectrum
  (physicalMomentumEquivZero physicalMomentumEquivOrbifoldGrade)
open OriginalOrbifoldBRSTRootNilpotence (physicalMomentum_eq_bot_of_one_lt)
open OriginalOrbifoldRelativeMassShell (hyperbolic_chargeEnergy)
open OriginalOrbifoldRelativeQuartet (orbifoldGrade)
open TwistedGround.OriginalOrbifoldLowSpectrum
  (actual_leech_low_spectrum actual_leech_positive_integral_grading)

private abbrev UCharge := Charge hyperbolicData

/-- The integer principal degree in the native hyperbolic coordinates. -/
def principalDegree (p : UCharge) : ℤ := 2 * p 0 - p 1

private theorem principalDegree_add (p q : UCharge) :
    principalDegree (p + q) = principalDegree p + principalDegree q := by
  change 2 * (p 0 + q 0) - (p 1 + q 1) = (2 * p 0 - p 1) + (2 * q 0 - q 1)
  ring

private theorem second_coord_of_degree {p : UCharge} {k : ℤ} (hp : principalDegree p = k) :
    p 1 = 2 * p 0 - k := by
  unfold principalDegree at hp
  omega

private theorem charge_ext {p q : UCharge} (h0 : p 0 = q 0) (h1 : p 1 = q 1) :
    p = q := by
  funext i
  fin_cases i <;> assumption

private theorem coord_product_le_one {p : UCharge} (hp : physicalMomentum p ≠ ⊥) :
    p 0 * p 1 ≤ 1 :=
  le_of_not_gt fun h => hp (physicalMomentum_eq_bot_of_one_lt h)

private theorem one_lt_product {a b : ℤ} (ha : 1 ≤ a) (hb : 2 ≤ b) : 1 < a * b :=
  (show (1 : ℤ) < 1 * 2 by decide).trans_le (mul_le_mul ha hb (by decide) (by omega))

/-- On a principal degree fiber, every supported momentum has bounded first coordinate. -/
theorem abs_first_coord_le_of_support {k : ℤ} {p : UCharge}
    (hdegree : principalDegree p = k) (hsupport : physicalMomentum p ≠ ⊥) :
    |p 0| ≤ |k| + 1 := by
  have hsecond := second_coord_of_degree hdegree
  have hproduct := coord_product_le_one hsupport
  have hknonneg := abs_nonneg k
  rw [abs_le]
  constructor
  · by_contra! h
    have hneg : 1 < (-p 0) * (-p 1) :=
      one_lt_product (by omega) (by have := neg_le_abs k; omega)
    rw [neg_mul_neg] at hneg
    omega
  · by_contra! h
    have hpos : 1 < p 0 * p 1 :=
      one_lt_product (by omega) (by have := le_abs_self k; omega)
    omega

/-- Only finitely many nonzero momentum submodules contribute to each principal degree. -/
theorem finite_principal_support (k : ℤ) :
    {p : UCharge | principalDegree p = k ∧ physicalMomentum p ≠ ⊥}.Finite := by
  refine Set.Finite.of_injOn (f := fun p : UCharge => p 0)
    (t := Set.Icc (-(|k| + 1)) (|k| + 1)) ?_ ?_ (Set.finite_Icc _ _)
  · intro p hp
    exact abs_le.mp (abs_first_coord_le_of_support hp.1 hp.2)
  · intro p hp q hq h
    apply charge_ext h
    calc
      p 1 = 2 * p 0 - k := second_coord_of_degree hp.1
      _ = 2 * q 0 - k := congrArg (fun m : ℤ => 2 * m - k) h
      _ = q 1 := (second_coord_of_degree hq.1).symm

/-- The principal component is the supremum of all native momentum spaces in its fiber. -/
def principalComponent (k : ℤ) : Submodule ℂ DegreeOne :=
  ⨆ p : {p : UCharge // principalDegree p = k}, physicalMomentum p

private theorem physicalMomentum_le_principalComponent {p : UCharge} {k : ℤ}
    (h : principalDegree p = k) : physicalMomentum p ≤ principalComponent k :=
  le_iSup (fun q : {q : UCharge // principalDegree q = k} => physicalMomentum q) ⟨p, h⟩

set_option maxHeartbeats 800000 in
-- The supremum comparisons elaborate submodule instances on the relative BRST quotient.
/-- The principal component of degree zero is exactly the native momentum-zero space. -/
theorem principalComponent_zero : principalComponent 0 = physicalMomentum (0 : UCharge) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    by_cases hbot : physicalMomentum p.1 = ⊥
    · rw [hbot]
      exact bot_le
    · have hproduct := coord_product_le_one hbot
      have hsecond := second_coord_of_degree p.2
      have hfirst : p.1 0 = 0 := by
        by_contra h
        rcases lt_or_gt_of_ne h with hneg | hpos
        · have h' : 1 < (-p.1 0) * (-p.1 1) := one_lt_product (by omega) (by omega)
          rw [neg_mul_neg] at h'
          omega
        · have h' : 1 < p.1 0 * p.1 1 := one_lt_product (by omega) (by omega)
          omega
      have hp0 : p.1 = 0 := charge_ext hfirst (by change p.1 1 = 0; omega)
      rw [hp0]
  · exact physicalMomentum_le_principalComponent rfl

set_option maxHeartbeats 1000000 in
-- The disjointness argument compares nested suprema of submodules on the BRST quotient.
/-- The principal components form an internal direct sum of the physical Lie algebra. -/
theorem principalComponent_grading : DirectSum.IsInternal principalComponent := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · intro k
    have hdisjoint : Disjoint
        (⨆ (p : UCharge) (_ : principalDegree p = k), physicalMomentum p)
        (⨆ (p : UCharge) (_ : principalDegree p ≠ k), physicalMomentum p) :=
      physicalMomentum_grading.submodule_iSupIndep.disjoint_biSup_biSup
        (Set.disjoint_left.mpr fun _ hp hq => hq hp)
    have hleft : principalComponent k ≤
        ⨆ (p : UCharge) (_ : principalDegree p = k), physicalMomentum p :=
      iSup_le fun (p : {p : UCharge // principalDegree p = k}) =>
        le_iSup₂_of_le p.1 p.2 le_rfl
    have hright : (⨆ (j : ℤ) (_ : j ≠ k), principalComponent j) ≤
        ⨆ (p : UCharge) (_ : principalDegree p ≠ k), physicalMomentum p :=
      iSup₂_le fun j hj => iSup_le fun (p : {p : UCharge // principalDegree p = j}) =>
        le_iSup₂_of_le p.1 (p.2.trans_ne hj) le_rfl
    exact hdisjoint.mono hleft hright
  · apply top_unique
    rw [← physicalMomentum_grading.submodule_iSup_eq_top]
    exact iSup_le fun p => le_iSup_of_le (principalDegree p)
      (physicalMomentum_le_principalComponent (p := p) rfl)

set_option maxHeartbeats 800000 in
-- The two supremum inductions elaborate the bracket on the degree-one subtype.
/-- The native physical Lie bracket adds principal degrees. -/
theorem degreeOne_bracket_mem_principalComponent {k l : ℤ} {x y : DegreeOne}
    (hx : x ∈ principalComponent k) (hy : y ∈ principalComponent l) :
    ⁅x, y⁆ ∈ principalComponent (k + l) := by
  refine Submodule.iSup_induction
    (fun p : {p : UCharge // principalDegree p = k} => physicalMomentum p)
    (motive := fun x => ⁅x, y⁆ ∈ principalComponent (k + l)) hx ?_ ?_ ?_
  · intro p u hu
    refine Submodule.iSup_induction
      (fun q : {q : UCharge // principalDegree q = l} => physicalMomentum q)
      (motive := fun y => ⁅u, y⁆ ∈ principalComponent (k + l)) hy ?_ ?_ ?_
    · intro q v hv
      have hpq : principalDegree (p.1 + q.1) = k + l := by
        rw [principalDegree_add, p.2, q.2]
      exact physicalMomentum_le_principalComponent hpq
        (degreeOne_bracket_mem_physicalMomentum hu hv)
    · rw [lie_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [lie_add]
      exact Submodule.add_mem _ hv hw
  · rw [zero_lie]
    exact Submodule.zero_mem _
  · intro u v hu hv
    rw [add_lie]
    exact Submodule.add_mem _ hu hv

set_option maxHeartbeats 800000 in
-- The equivalences transport finiteness between concrete BRST and eigenspace subtypes.
private theorem physicalMomentum_finiteDimensional (p : UCharge) :
    FiniteDimensional ℂ (physicalMomentum p) := by
  by_cases hp : p = 0
  · subst p
    exact Module.Finite.of_injective physicalMomentumEquivZero.toLinearMap
      physicalMomentumEquivZero.injective
  by_cases he : p 0 * p 1 ≤ 1
  · have he' : chargeEnergy hyperbolicData p ≤ 1 := (hyperbolic_chargeEnergy p).symm ▸ he
    let : FiniteDimensional ℂ (orbifoldGrade (massShellCutoff hyperbolicData p)) :=
      actual_leech_positive_integral_grading.2.2 _
    let e := physicalMomentumEquivOrbifoldGrade p hp he'
    exact Module.Finite.of_injective e.toLinearMap e.injective
  · rw [physicalMomentum_eq_bot_of_one_lt (lt_of_not_ge he)]
    infer_instance

set_option maxHeartbeats 1000000 in
-- Comparing the full and supported suprema requires elaborating the BRST submodule types.
/-- Every principal component of the actual relative BRST physical Lie algebra is finite. -/
theorem principalComponent_finiteDimensional (k : ℤ) :
    FiniteDimensional ℂ (principalComponent k) := by
  let S := {p : UCharge | principalDegree p = k ∧ physicalMomentum p ≠ ⊥}
  let : Finite S := (finite_principal_support k).to_subtype
  let (p : S) : FiniteDimensional ℂ (physicalMomentum p) :=
    physicalMomentum_finiteDimensional p
  have hS : principalComponent k = ⨆ p : S, physicalMomentum p := by
    apply le_antisymm
    · apply iSup_le
      intro p
      by_cases hp : physicalMomentum p.1 = ⊥
      · rw [hp]
        exact bot_le
      · exact le_iSup (fun q : S => physicalMomentum q) ⟨p.1, p.2, hp⟩
    · exact iSup_le fun p : S => physicalMomentum_le_principalComponent p.2.1
  rw [hS]
  exact Submodule.finite_iSup _

set_option maxHeartbeats 800000 in
-- The weight-one eigenspace and its native BRST equivalence are definitionally large.
/-- The actual weight-one eigenspace vanishes, so nonzero isotropic momenta give no
physical states. -/
theorem physicalMomentum_eq_bot_of_isotropic {p : UCharge} (hp : p ≠ 0)
    (hnull : p 0 * p 1 = 0) : physicalMomentum p = ⊥ := by
  have he : chargeEnergy hyperbolicData p = 0 := (hyperbolic_chargeEnergy p).trans hnull
  have hcut : massShellCutoff hyperbolicData p = 1 := by simp [massShellCutoff, he]
  let e := physicalMomentumEquivOrbifoldGrade p hp (he ▸ (by decide : (0 : ℤ) ≤ 1))
  have hgrade : orbifoldGrade 1 = ⊥ := by
    change (orbifoldMode 0).eigenspace ((1 : ℕ) : ℂ) = ⊥
    rw [Nat.cast_one]
    let : FiniteDimensional ℂ ((orbifoldMode 0).eigenspace 1) := actual_leech_low_spectrum.2.1
    exact Submodule.finrank_eq_zero.mp actual_leech_low_spectrum.2.2.2.2.1
  let : Subsingleton (orbifoldGrade (massShellCutoff hyperbolicData p)) := by
    rw [hcut, hgrade]
    infer_instance
  let : Subsingleton (physicalMomentum p) := e.injective.subsingleton
  exact Submodule.subsingleton_iff_eq_bot.mp inferInstance

#print axioms principalDegree
#print axioms abs_first_coord_le_of_support
#print axioms finite_principal_support
#print axioms principalComponent
#print axioms principalComponent_zero
#print axioms principalComponent_grading
#print axioms degreeOne_bracket_mem_principalComponent
#print axioms principalComponent_finiteDimensional
#print axioms physicalMomentum_eq_bot_of_isotropic

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPrincipalGrading
