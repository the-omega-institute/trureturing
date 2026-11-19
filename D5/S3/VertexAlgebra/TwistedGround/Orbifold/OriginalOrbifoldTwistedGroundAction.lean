/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedGroundAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedGroundAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed charge zero modes span the endomorphisms of the positive twisted Leech top. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldSectorModules
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal
import D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
import D5.S3.VertexAlgebra.HalfFock.GroundCompression
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! The actual fixed algebra acts irreducibly on the lowest positive twisted grade. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedGroundAction

open LatticeGeneratingFieldLocality (Charge Oscillator)
open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier theta thetaLinear theta_involutive theta_single mem_fixedSpace
  bilinear_neg_neg sigmaLinear)
open LatticePositiveEnergy (chargeEnergy grade grade_eq_span carrierBasis carrierBasis_apply
  energy oscillatorEnergy two_chargeEnergy)
open LatticeHalfFockChargedCoefficients (omega halfCreationCoeff)
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField (correctedField corrected_singleton_coeff_charged)
open LatticeHalfFockGradedTrace
open LatticeHalfFockParityT (actualParity)
open LatticeHalfFockGroundCompression (iota pi ground_retraction)
open HalfFock.LatticeHalfFockParityField (paritySpace correctedField_target_parity)
open HalfFock.ActualEnergyCovariance (correctedField_L_zero_commutator)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldConformal (conformalVector)
open LatticeTwistedGroundRealization (actual_twisted_ground_representation)
open LatticeTwistedGroundRealization.SignQuotient (Extension)
open OperatorAlgebra (actual_operator_algebra chargeOperator integralLift)
open scoped TensorProduct VertexOperator
open private creation_zero from D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open private fixedParitySlice_mode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldSectorModules

noncomputable section

local notation "hu" => And.left (And.right leech_spec)

abbrev PositiveTwisted := paritySpace leechData hu 1

private theorem actual_mode_val (a : FixedCarrier leechData) (n : ℤ)
    (v : PositiveTwisted) :
    (((fixedParityY leechData hu 1 a)[[n]]) v).val =
      (correctedField leechData hu a.val).coeff (-2 * n - 2) v.val :=
  fixedParitySlice_mode_val leechData hu 1 a n v

/-- The conformal zero mode of the actual fixed algebra on the positive twisted slice. -/
def twistedL0 : Module.End ℂ PositiveTwisted :=
  (fixedParityY leechData hu 1 (conformalVector leechData hu).1)[[1]]

private theorem twistedL0_val (v : PositiveTwisted) :
    (twistedL0 v).val = actualTensorL0 leechData hu v.val := by
  rw [twistedL0, actual_mode_val]
  let H := HalfFockSpectralFiberSource.actualInverse leechData
  change (correctedField leechData hu (LatticeActualConformalState.omega leechData H)).coeff
    (-4) v.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega leechData hu _
    (HalfFockSpectralFiberSource.actualInverse_left leechData hu)]
  simp only [LatticeHalfFock.tensorStressField, HVertexOperator.coeff_of_coeff,
    LatticeHalfFock.stressCoeff, actualTensorL0, LatticeHalfFock.tensorL]
  rfl

/-- The weight-`3/2` eigenspace inside the actual positive twisted slice. -/
def Top : Submodule ℂ PositiveTwisted := twistedL0.eigenspace (3 / 2)

private theorem mem_top_iff_grade (v : PositiveTwisted) :
    v ∈ Top ↔ v.val ∈ actualGrade leechData hu 0 := by
  have hweight : (leechData.rank : ℂ) / 16 + ((0 : ℕ) : ℂ) / 2 = 3 / 2 := by
    rw [leech_spec.1]
    norm_num
  rw [Top, Module.End.mem_eigenspace_iff]
  simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, hweight]
  constructor
  · intro h
    exact (twistedL0_val v).symm.trans (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((twistedL0_val v).trans h)

private theorem oddWeight_zero {d : OddMonomial leechData} (hd : oddWeight leechData d = 0) :
    d = 0 := by
  ext i
  have h := Finsupp.le_weight (omega leechData) (s := i) (by simp [omega]) d
  change d i ≤ oddWeight leechData d at h
  simpa [hd] using h

private theorem grade_zero_eq_range :
    actualGrade leechData hu 0 = LinearMap.range (iota leechData hu) := by
  rw [actual_grade_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨d, hd⟩, b⟩, rfl⟩
    have hz := oddWeight_zero hd
    subst d
    refine ⟨Pi.single b 1, ?_⟩
    simp [actualGradeVector, actual_basis_apply, iota]
  · rintro _ ⟨g, rfl⟩
    have hmem (b : LatticeTwistedGroundRealization.Half (groundRank leechData hu)) :
        iota leechData hu (Pi.single b 1) ∈
          Submodule.span ℂ (Set.range (actualGradeVector leechData hu 0)) := by
      refine Submodule.subset_span ⟨(⟨0, by simp [oddWeight]⟩, b), ?_⟩
      simp [actualGradeVector, actual_basis_apply, iota]
    let b := Pi.basisFun ℂ (LatticeTwistedGroundRealization.Half (groundRank leechData hu))
    rw [← b.sum_repr g, map_sum]
    exact Submodule.sum_mem _ fun j _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (by simpa only [b, Pi.basisFun_apply] using hmem j)

private theorem parity_vacuum (g : ActualGround leechData hu) :
    actualParity leechData hu (iota leechData hu g) = iota leechData hu g := by
  simp [actualParity, iota, sigmaLinear]

private def vacuumInclusion : ActualGround leechData hu →ₗ[ℂ] Top :=
  ((iota leechData hu).codRestrict PositiveTwisted (by
    intro g
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, one_smul] using parity_vacuum g
    )).codRestrict Top (by
    intro g
    exact (mem_top_iff_grade _).mpr (grade_zero_eq_range.symm ▸ LinearMap.mem_range_self _ g))

/-- The vacuum tensor gives linear coordinates on the entire actual top. -/
def groundEquiv : ActualGround leechData hu ≃ₗ[ℂ] Top :=
  LinearEquiv.ofBijective vacuumInclusion ⟨by
    intro g h eq
    have he := congrArg (fun v : Top => pi leechData hu v.val.val) eq
    change ((pi leechData hu).comp (iota leechData hu)) g =
      ((pi leechData hu).comp (iota leechData hu)) h at he
    simpa only [ground_retraction, LinearMap.id_apply] using he, by
    intro v
    obtain ⟨g, hg⟩ := grade_zero_eq_range ▸ (mem_top_iff_grade v.val).mp v.property
    exact ⟨g, Subtype.ext (Subtype.ext hg)⟩⟩

private theorem groundEquiv_val (g : ActualGround leechData hu) :
    (groundEquiv g).val.val = iota leechData hu g := rfl

/-- Every eigenweight in the actual positive twisted slice is at least the vacuum weight. -/
theorem twisted_eigenweight (μ : ℂ) (v : PositiveTwisted) (hv : v ≠ 0)
    (he : twistedL0 v = μ • v) :
    ∃ k : ℕ, μ = 3 / 2 + (k : ℂ) / 2 := by
  let b := actualAmbientBasis leechData hu
  have hv' : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  have hb : b.repr v.val ≠ 0 := b.repr.map_ne_zero_iff.mpr hv'
  obtain ⟨j, hj⟩ : ∃ j, b.repr v.val j ≠ 0 := by
    by_contra! h
    exact hb (Finsupp.ext h)
  have he' : actualTensorL0 leechData hu v.val = μ • v.val :=
    (twistedL0_val v).symm.trans (congrArg Subtype.val he)
  have hc := congrArg (fun x => b.repr x j) he'
  change (actualAmbientBasis leechData hu).repr (actualTensorL0 leechData hu v.val) j =
    b.repr (μ • v.val) j at hc
  rw [actualTensorL0_repr] at hc
  simp only [leech_spec.1, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have hw := mul_right_cancel₀ hj hc
  exact ⟨oddWeight leechData j.1, by linear_combination -hw⟩

private def chargeState (α : Charge leechData) :
    LatticeGeneratingFieldLocality.Carrier leechData :=
  Finsupp.single α (1 : Oscillator leechData)

/-- The literal fixed vector obtained by averaging the single-charge state and its image. -/
def fixedCharge (α : Charge leechData) : FixedCarrier leechData :=
  ⟨(1 / 2 : ℂ) • (chargeState α + theta leechData (chargeState α)), by
    apply (mem_fixedSpace leechData _).mpr
    have h : theta leechData (theta leechData (chargeState α)) = chargeState α :=
      theta_involutive leechData (chargeState α)
    simp only [map_smul, map_add, h, add_comm]⟩

private theorem chargeState_grade (α : Charge leechData) :
    chargeState α ∈ grade leechData (chargeEnergy leechData α) := by
  rw [grade_eq_span]
  refine Submodule.subset_span ⟨(α, 0), ?_, ?_⟩
  · simp [energy, oscillatorEnergy]
  · simp [chargeState, carrierBasis_apply]

private theorem fixedCharge_grade (α : Charge leechData) :
    (fixedCharge α).val ∈ grade leechData (chargeEnergy leechData α) := by
  have hθ : theta leechData (chargeState α) = chargeState (-α) := by
    change thetaLinear leechData (Finsupp.single α 1) = _
    simp [chargeState, theta_single]
  have henergy : chargeEnergy leechData (-α) = chargeEnergy leechData α := by
    simp [chargeEnergy, bilinear_neg_neg]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (chargeState_grade α)
    (hθ.symm ▸ henergy ▸ chargeState_grade (-α)))

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
-- The weight-preservation proof compares the sector and ambient tensor realizations.
private theorem fixedZeroMode_mem (a : FixedCarrier leechData) (h : ℤ)
    (ha : a.val ∈ grade leechData h) (v : PositiveTwisted) (hv : v ∈ Top) :
    ((fixedParityY leechData hu 1 a)[[h - 1]]) v ∈ Top := by
  let w : PositiveTwisted := ((fixedParityY leechData hu 1 a)[[h - 1]]) v
  let A : Module.End ℂ (ActualTensor leechData hu) :=
    (correctedField leechData hu a.val).coeff (-2 * h)
  have hw : w.val = A v.val := by
    calc
      w.val = (correctedField leechData hu a.val).coeff (-2 * (h - 1) - 2) v.val :=
        actual_mode_val a (h - 1) v
      _ = A v.val := congrArg
        (fun e : ℤ => (correctedField leechData hu a.val).coeff e v.val) (by ring)
  have hx := Module.End.mem_eigenspace_iff.mp (show v ∈ twistedL0.eigenspace (3 / 2) from hv)
  have hx' : actualTensorL0 leechData hu v.val = (3 / 2 : ℂ) • v.val :=
    (twistedL0_val v).symm.trans (congrArg Subtype.val hx)
  have comm := correctedField_L_zero_commutator leechData hu h a.val ha (-2 * h)
  have hz : (((-2 * h : ℤ) : ℂ) / 2 + (h : ℂ)) = 0 := by push_cast; ring
  rw [hz, zero_smul, sub_eq_zero] at comm
  have comm_v : actualTensorL0 leechData hu (A v.val) =
      A (actualTensorL0 leechData hu v.val) :=
    LinearMap.congr_fun comm v.val
  change w ∈ twistedL0.eigenspace (3 / 2)
  refine Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_)
  calc
    (twistedL0 w).val = actualTensorL0 leechData hu w.val := twistedL0_val w
    _ = actualTensorL0 leechData hu (A v.val) := congrArg (actualTensorL0 leechData hu) hw
    _ = A (actualTensorL0 leechData hu v.val) := comm_v
    _ = (3 / 2 : ℂ) • A v.val := (congrArg A hx').trans (map_smul A _ _)
    _ = ((3 / 2 : ℂ) • w).val := congrArg ((3 / 2 : ℂ) • ·) hw.symm

/-- The actual physical mode `h - 1` of a homogeneous fixed source preserves the top. -/
def fixedZeroMode (a : FixedCarrier leechData) (h : ℤ) (ha : a.val ∈ grade leechData h) :
    Module.End ℂ Top :=
  ((fixedParityY leechData hu 1 a)[[h - 1]]).restrict (fixedZeroMode_mem a h ha)

/-- The weight-preserving mode of the literal fixed single-charge average. -/
def chargeZeroMode (α : Charge leechData) : Module.End ℂ Top :=
  fixedZeroMode (fixedCharge α) (chargeEnergy leechData α) (fixedCharge_grade α)

private theorem charge_coefficient (α : Charge leechData) (g : ActualGround leechData hu) :
    (correctedField leechData hu (chargeState α)).coeff (-chargeNorm leechData α)
      (iota leechData hu g) =
        chargeScalar leechData α • iota leechData hu (groundAction leechData hu α g) := by
  rw [chargeState, corrected_singleton_coeff_charged]
  change chargedCoefficient leechData hu α (-chargeNorm leechData α)
    ((1 : Oscillator leechData) ⊗ₜ[ℂ] g) = _
  rw [charged_vacuum_coefficient, neg_add_cancel, creation_zero]
  rfl

/- proof_shape: charge_zero_mode_on_ground: content
   admission_basis: escape-witness
   escape_witness: At the actual weight-preserving mode the charged creation
   degree is zero. Target parity fixes each vacuum tensor, so the reflected
   source contributes the identical normalized action to the literal average. -/
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
-- Mode evaluation passes through both the parity and conformal subtypes.
/-- The actual fixed zero mode on the top is the normalized integral charge action. -/
theorem charge_zero_mode_on_ground (α : Charge leechData) (g : ActualGround leechData hu) :
    chargeZeroMode α (groundEquiv g) =
      chargeScalar leechData α • groundEquiv (groundAction leechData hu α g) := by
  apply Subtype.ext
  apply Subtype.ext
  change (((fixedParityY leechData hu 1 (fixedCharge α))[[chargeEnergy leechData α - 1]])
    (groundEquiv g).val).val =
      chargeScalar leechData α • (groundEquiv (groundAction leechData hu α g)).val.val
  rw [actual_mode_val (fixedCharge α) _ (groundEquiv g).val,
    groundEquiv_val g, groundEquiv_val (groundAction leechData hu α g)]
  have he : -2 * (chargeEnergy leechData α - 1) - 2 = -chargeNorm leechData α := by
    dsimp [chargeNorm]
    rw [← two_chargeEnergy]
    ring
  rw [he]
  have reflected := correctedField_target_parity leechData hu (chargeState α)
    (-chargeNorm leechData α) (iota leechData hu g)
  rw [charge_coefficient, parity_vacuum, map_smul, parity_vacuum] at reflected
  change (correctedField leechData hu
    ((1 / 2 : ℂ) • (chargeState α + theta leechData (chargeState α)))).coeff _ _ = _
  simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, LinearMap.smul_apply,
    LinearMap.add_apply, charge_coefficient, ← reflected]
  rw [← two_smul ℂ, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
-- The projected leading coefficient is compared with a literal tensor coefficient.
/-- Each fixed charge zero mode is nonzero on every nonzero top vector. -/
theorem charge_zero_mode_ne_zero (α : Charge leechData) (v : Top) (hv : v ≠ 0) :
    chargeZeroMode α v ≠ 0 := by
  obtain ⟨g, rfl⟩ := groundEquiv.surjective v
  have hg : g ≠ 0 := by
    rintro rfl
    exact hv (map_zero groundEquiv)
  have hn := charged_ground_leading leechData hu α g hg
  change (chargedField leechData hu α).coeff (-chargeNorm leechData α)
    (iota leechData hu g) ≠ 0 at hn
  rw [← corrected_singleton_coeff_charged, ← show chargeState α = Finsupp.single α 1 from rfl,
    charge_coefficient] at hn
  intro hz
  apply hn
  have h := congrArg (fun x : Top => x.val.val) hz
  simpa only [charge_zero_mode_on_ground α g, Submodule.coe_smul, groundEquiv_val,
    Submodule.coe_zero] using h

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
-- The conjugation and span operations involve both Leech ground realizations.
/-- The linear span of the actual fixed charge zero modes is the full top endomorphism space. -/
theorem charge_zero_modes_span :
    Submodule.span ℂ (Set.range chargeZeroMode) = ⊤ := by
  let transport := groundEquiv.conj
  have hconj (α : Charge leechData) :
      chargeZeroMode α = chargeScalar leechData α •
        transport (groundAction leechData hu α) := by
    refine LinearMap.ext fun v => ?_
    let g := groundEquiv.symm v
    have hv : groundEquiv g = v := groundEquiv.apply_symm_apply v
    have ha := charge_zero_mode_on_ground α g
    rw [hv] at ha
    simpa only [transport, LinearMap.smul_apply, LinearEquiv.conj_apply_apply] using ha
  have rank_eq : leechData.rank = groundRank leechData hu + groundRank leechData hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation leechData hu))).1
  have central : groundRepresentation leechData hu
      (QuotientGroup.mk (⟨1, 0⟩ : Extension leechData)) =
        -(1 : Module.End ℂ (ActualGround leechData hu)) :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation leechData hu))).2.2.1
  obtain ⟨algebra⟩ := actual_operator_algebra leechData hu (groundRank leechData hu)
    rank_eq (groundRepresentation leechData hu) central
  let charges := chargeOperator leechData (groundRepresentation leechData hu)
  let modeSpan := Submodule.span ℂ (Set.range chargeZeroMode)
  have hmap : Submodule.span ℂ (Set.range charges) ≤
      modeSpan.comap transport.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    let α := integralLift leechData q
    have hs : chargeScalar leechData α ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hz : chargeZeroMode α ∈ modeSpan := Submodule.subset_span (Set.mem_range_self α)
    have hm := modeSpan.smul_mem (chargeScalar leechData α)⁻¹ hz
    change transport (groundAction leechData hu α) ∈ modeSpan
    simpa only [hconj α, smul_smul, inv_mul_cancel₀ hs, one_smul] using hm
  have hspan : Submodule.span ℂ (Set.range charges) = ⊤ := algebra.full_span
  apply top_unique
  intro A _
  have hground : transport.symm A ∈ Submodule.span ℂ (Set.range charges) :=
    hspan.symm ▸ Submodule.mem_top
  have hmem : transport (transport.symm A) ∈ modeSpan := hmap hground
  exact transport.apply_symm_apply A ▸ hmem

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
-- The rank-one endomorphism and evaluation are formed on the nested sector subtype.
/-- The concrete positive twisted top is irreducible under the fixed-source zero modes.
The charge modes alone suffice for invariance. -/
theorem twisted_top_irreducible (S : Submodule ℂ Top)
    (stable : ∀ (a : FixedCarrier leechData) (h : ℤ) (ha : a.val ∈ grade leechData h)
      (v : Top), v ∈ S → fixedZeroMode a h ha v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    let evaluation : Module.End ℂ Top →ₗ[ℂ] Top := LinearMap.applyₗ v
    have hstable : Submodule.span ℂ (Set.range chargeZeroMode) ≤ S.comap evaluation := by
      apply Submodule.span_le.mpr
      rintro _ ⟨α, rfl⟩
      exact stable (fixedCharge α) (chargeEnergy leechData α) (fixedCharge_grade α) v hv
    have hall : (⊤ : Submodule ℂ (Module.End ℂ Top)) ≤ S.comap evaluation :=
      charge_zero_modes_span ▸ hstable
    let : Module.Free ℂ Top := Module.Free.of_divisionRing ℂ Top
    let : Module.Projective ℂ Top := Module.Projective.of_free
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hv0
    apply top_unique
    intro w _
    have hm := hall (show f.smulRight w ∈ (⊤ : Submodule ℂ (Module.End ℂ Top)) by trivial)
    change f v • w ∈ S at hm
    simpa only [hf, one_smul] using hm

#print axioms groundEquiv
#print axioms twisted_eigenweight
#print axioms charge_zero_mode_on_ground
#print axioms charge_zero_mode_ne_zero
#print axioms charge_zero_modes_span
#print axioms twisted_top_irreducible

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedGroundAction
