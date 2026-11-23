/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldLowWeights
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldLowWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The vacuum and weight-one spaces of the actual Leech orbifold. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMatter
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralPower
import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace

/-! The low eigenspaces of the stress field on the fixed and twisted summands. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldMatter

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality LatticeInvolution LatticeSugawaraCurrents
open LatticeSugawaraVirasoro LatticePositiveEnergy
open LatticeHalfFockGradedTrace HalfFockSpectralFiberSource
open LatticeHalfFock LatticeHalfFockChargedLZero
open TwistedGround.Orbifold
open Lattice.InvolutionRootlessLowGrades

open private FixedGrade fixedGrade_one_eq_bot
  from D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

private theorem leech_rootless (a : Charge leechData) : bilinear leechData a a ≠ 2 := by
  by_cases ha : a = 0
  · subst a
    norm_num [bilinear]
  · have h := Lattice.ActualFixedC2.leech_charge_norm_ge_four a ha
    omega

private theorem twisted_zero_of_weight_le_one (x : Orbifold) (r : ℂ) (hr : r.re ≤ 1)
    (h : mode 0 x = r • x) : x.2.val = 0 := by
  have he : actualTensorL0 leechData leechUnit x.2.val = r • x.2.val :=
    (congrArg Prod.snd (mode_apply 0 x)).symm.trans
      (congrArg (fun z : Orbifold => z.2.val) h)
  let b := actualAmbientBasis leechData leechUnit
  apply b.repr.injective
  rw [map_zero]
  ext i
  have hi := congrArg (fun z => b.repr z i) he
  change (actualAmbientBasis leechData leechUnit).repr
    (actualTensorL0 leechData leechUnit x.2.val) i = b.repr (r • x.2.val) i at hi
  rw [actualTensorL0_repr] at hi
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hi
  apply (mul_eq_mul_right_iff.mp hi).resolve_left
  intro hn
  have hw : ((leechData.rank : ℂ) / 16 + (oddWeight leechData i.1 : ℂ) / 2) =
      ((24 / 16 + (oddWeight leechData i.1 : ℝ) / 2 : ℝ) : ℂ) := by
    simp [leech_spec.1]
  rw [hw] at hn
  have hre := congrArg Complex.re hn
  rw [Complex.ofReal_re] at hre
  have hnonneg : (0 : ℝ) ≤ (oddWeight leechData i.1 : ℝ) := Nat.cast_nonneg _
  linarith

set_option maxHeartbeats 1000000 in
/-- The actual assembled Leech orbifold has no states of weight one. -/
theorem eq_zero_of_weight_one (x : Orbifold) (h : mode 0 x = x) : x = 0 := by
  have hfix : sugawaraMode leechData (actualInverse leechData) 0 x.1.val = x.1.val :=
    (congrArg Prod.fst (mode_apply 0 x)).symm.trans
      (congrArg (fun z : Orbifold => z.1.val) h)
  have hg : x.1.val ∈ grade leechData 1 := by
    apply (actualL0_eigen_iff_grade leechData _ (actualInverse_left leechData leechUnit)
      (actualInverse_right leechData leechUnit) 1 _).mp
    simpa only [Int.cast_one, one_smul] using hfix
  have hz : x.1.val ∈ FixedGrade leechData 1 := ⟨x.1.property, hg⟩
  rw [fixedGrade_one_eq_bot leechData leechPosDef leech_rootless] at hz
  apply Prod.ext
  · exact Subtype.ext ((Submodule.mem_bot ℂ).mp hz)
  · apply Subtype.ext
    exact twisted_zero_of_weight_le_one x 1 (by simp) (by simpa only [one_smul] using h)

/-- The literal weight-one eigenspace of the assembled stress field is zero. -/
theorem weight_one_eq_bot : (mode 0).eigenspace 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  exact (Submodule.mem_bot ℂ).mpr
    (eq_zero_of_weight_one x (by simpa only [one_smul] using Module.End.mem_eigenspace_iff.mp hx))

set_option maxHeartbeats 1000000 in
/-- Every zero-weight state is a multiple of the actual assembled vacuum. -/
theorem weight_zero_vacuum (x : Orbifold) (h : mode 0 x = 0) :
    x = carrierCoeffEquiv leechData x.1.val (0, 0) •
      OriginalOrbifoldField.vacuumState leechData leechUnit := by
  have hfix : sugawaraMode leechData (actualInverse leechData) 0 x.1.val = 0 :=
    (congrArg Prod.fst (mode_apply 0 x)).symm.trans
      (congrArg (fun z : Orbifold => z.1.val) h)
  have hg : x.1.val ∈ grade leechData 0 := by
    apply (actualL0_eigen_iff_grade leechData _ (actualInverse_left leechData leechUnit)
      (actualInverse_right leechData leechUnit) 0 _).mp
    simpa only [Int.cast_zero, zero_smul] using hfix
  apply Prod.ext
  · apply Subtype.ext
    change x.1.val = _ • (Finsupp.single 0 1 : Carrier leechData)
    have he : carrierCoeffEquiv leechData (Finsupp.single 0 1) =
        Finsupp.single (0, 0) (1 : ℂ) := by
      rw [← carrierCoeffEquiv_basis]
      simp
    apply (carrierCoeffEquiv leechData).injective
    rw [map_smul, he]
    ext i
    by_cases hi : i = (0, 0)
    · subst i
      simp
    · have hn : energy leechData i ≠ 0 := by
        rwa [ne_eq, energy_eq_zero_iff leechData leechPosDef]
      simp [Ne.symm hi]
      exact (mem_grade_iff leechData 0 _).mp hg i hn
  · apply Subtype.ext
    exact twisted_zero_of_weight_le_one x 0 (by simp) (by simpa only [zero_smul] using h)

/-- Negative real weights are absent from the literal two-sector carrier. -/
theorem eq_zero_of_weight_neg (x : Orbifold) (r : ℂ) (hr : r.re < 0)
    (h : mode 0 x = r • x) : x = 0 := by
  apply Prod.ext
  · apply Subtype.ext
    change x.1.val = 0
    have hfix : sugawaraMode leechData (actualInverse leechData) 0 x.1.val = r • x.1.val :=
      (congrArg Prod.fst (mode_apply 0 x)).symm.trans
        (congrArg (fun z : Orbifold => z.1.val) h)
    apply (carrierCoeffEquiv leechData).injective
    rw [map_zero]
    ext i
    have hi := congrArg (fun v => carrierCoeffEquiv leechData v i) hfix
    rw [actualL0_coeff leechData _ (actualInverse_left leechData leechUnit)
      (actualInverse_right leechData leechUnit)] at hi
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hi
    apply (mul_eq_mul_right_iff.mp hi).resolve_left
    intro hn
    have he : 0 ≤ energy leechData i :=
      add_nonneg (chargeEnergy_nonneg leechData leechPosDef i.1) (Int.natCast_nonneg _)
    have hre := congrArg Complex.re hn
    rw [Complex.intCast_re] at hre
    have he' : 0 ≤ (energy leechData i : ℝ) := by exact_mod_cast he
    linarith
  · apply Subtype.ext
    exact twisted_zero_of_weight_le_one x r (by linarith) h

private theorem mode_vacuum (n : ℤ) (hn : -1 ≤ n) :
    mode n (OriginalOrbifoldField.vacuumState leechData leechUnit) = 0 := by
  rw [mode, OriginalOrbifoldField.creation_ncoeff _ _ _ _ _ (by omega),
    ite_eq_right (by omega)]

#print axioms weight_one_eq_bot
#print axioms weight_zero_vacuum

end D5.S3.VertexAlgebra.ActualLeechOrbifoldMatter
