import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
import D5.S3.VertexAlgebra.HalfFock.NormalScalarTranspose
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
import Batteries.Tactic.OpenPrivate

/-! The first vacuum-channel BBO coefficient in the literal upper-branch
native fields. We evaluate it in the original source BPZ form against an
original weight-one current. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOVacuumNormalization

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open MixedIntertwiner (fixedGrade)
open LatticeHalfFockGradedTrace LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField (vacuum)
open LatticeSugawaraCurrents (neutralMode_heisenberg)
open LatticeFiniteNegativeGeneration (neutralMode)
open ActualChargedAdjoint NativeOddTwistedIntertwiner
open NativeOddUpperRightSkew (R rightField rightField_coeff R_eq_sum_of_grade rightTerm)
open NativeMixedPairField (mu mu_coeff_of_grade)
open NativeMixedPairState (mixedPairState_pairing)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_vacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_neutralMode)
open HalfFock.NormalScalarTranspose (actual_current_transpose)
open OriginalFourMChargeCoset (originalI originalI_three_eq_vacuum_smul)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open private J_current oddCurrent_grade_one groundBasis_energy leechGroundVector_nonzero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private actualGrade_eigen R_lowest mixedPairing_lowest upper_phase_neg_one
  upper_phase_neg_three upper_phase_neg_four exists_grade_detector translation_val lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private raising actual_stress_transpose lowering_raising_bracket from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private actual_current_l1 from D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
open private weight_two_vacuum_pairing from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
open private neutral_creativity from D5.S3.VertexAlgebra.LatticeAllStateField
open private originalI_sharp from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients

local notation "ℒ" => leechData
local notation "F" => actualForm ℒ leechUnit
local notation "C" => tensorCurrent ℒ (ActualGround ℒ leechUnit)
local notation "L" => raising ℒ leechUnit
local notation "D₁" => T ℒ leechUnit
local notation "E" => actualGrade ℒ leechUnit
local notation "S" => sourcePairing ℒ
local notation "Q" => rightField ℒ leechUnit true
local notation "P" => mu true

private abbrev V := ActualTensor ℒ leechUnit
private abbrev k (i : Fin (ℒ).rank) : ℂ := ((ℒ).G i i : ℂ) / 2
private abbrev create (i : Fin (ℒ).rank) (t : TwistedEven) : TwistedOdd :=
  J ℒ leechUnit false (-1) (oddCurrent ℒ i) t

private theorem k_ne_zero (i : Fin (ℒ).rank) : k i ≠ 0 := by
  have hp : 0 < ((ℒ).G i i : ℝ) := leech_spec.2.2.1.diag_pos
  have hn : ((ℒ).G i i : ℂ) ≠ 0 := by
    exact_mod_cast (show (ℒ).G i i ≠ 0 from by exact_mod_cast hp.ne')
  exact div_ne_zero hn (by norm_num)

private theorem c_bracket (i : Fin (ℒ).rank) (x : V) :
    C i 0 (C i (-1) x) - C i (-1) (C i 0 x) = k i • x := by
  have h : C i 0 * C i (-1) - C i (-1) * C i 0 =
      k i • (1 : Module.End ℂ V) := by
    apply TensorProduct.ext'
    intro p t
    have q := congrArg (fun A : Module.End ℂ (Oscillator ℒ) => A p ⊗ₜ[ℂ] t)
      (current_heisenberg ℒ i i 0 (-1))
    simpa [tensorCurrent, tensorEnd, Module.End.mul_apply, TensorProduct.map_tmul,
      TensorProduct.sub_tmul, TensorProduct.smul_tmul', frequency, mul_comm, div_eq_mul_inv] using q
  exact LinearMap.congr_fun h x

private theorem create_grade (i : Fin (ℒ).rank) (t : TwistedEven)
    (ht : t.val ∈ E 0) : (create i t).val ∈ E 1 :=
  J_grade ℒ leechUnit false (-1) 1 0 1 _ _ (oddCurrent_grade_one ℒ i) ht (by decide)

private theorem ground_annihilate (i : Fin (ℒ).rank) (t : TwistedEven)
    (ht : t.val ∈ E 0) : C i 0 t.val = 0 := by
  rw [← J_current ℒ leechUnit false i 0 t,
    J_negative_grade_zero ℒ leechUnit false 0 1 0 _ t
      (oddCurrent_grade_one ℒ i) ht (by decide)]
  rfl

private theorem create_val (i : Fin (ℒ).rank) (t : TwistedEven) :
    (create i t).val = C i (-1) t.val := J_current ℒ leechUnit false i (-1) t

private theorem annihilate_create (i : Fin (ℒ).rank) (t : TwistedEven)
    (ht : t.val ∈ E 0) : C i 0 (create i t).val = k i • t.val := by
  rw [create_val]
  have h := c_bracket i t.val
  rw [ground_annihilate i t ht, map_zero, sub_zero] at h
  exact h

private theorem ground_lower (t : TwistedEven) (ht : t.val ∈ E 0) :
    D₁ t.val = 0 := by
  have h := NativeOddUpperRightSkew.mixedPairing_lowering_tail false 0 t ht 1 (by decide)
  have h' := congrArg Subtype.val h
  rw [lowering_pow_val] at h'
  simpa using h'

private theorem lower_current (i : Fin (ℒ).rank) (x : V) :
    D₁ (C i (-1) x) = C i (-1) (D₁ x) + (1/2 : ℂ) • C i 0 x := by
  have h := LinearMap.congr_fun (actual_current_l1 ℒ leechUnit i (-1)) x
  change D₁ (C i (-1) x) - C i (-1) (D₁ x) =
    (-(((-1 : ℤ) : ℂ) + 1/2)) • C i (-1 + 1) x at h
  norm_num at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

private theorem ground_lower_create (i : Fin (ℒ).rank) (t : TwistedEven)
    (ht : t.val ∈ E 0) : D₁ (create i t).val = 0 := by
  rw [create_val, lower_current, ground_lower t ht, ground_annihilate i t ht]
  simp

private theorem ground_lower_raise (t : TwistedEven) (ht : t.val ∈ E 0) :
    D₁ (L t.val) = (3 : ℂ) • t.val := by
  have h := lowering_raising_bracket ℒ leechUnit t.val
  have ht' := (actualGrade_eigen ℒ leechUnit 0 t.val).mp ht
  rw [leech_spec.1] at ht'
  norm_num at ht'
  rw [ground_lower t ht, map_zero, sub_zero, ht', smul_smul] at h
  norm_num at h
  exact h

private theorem stress_raise_grade (x : V) (hx : x ∈ E 0) : L x ∈ E 2 := by
  have bracket : actualTensorL0 ℒ leechUnit * L -
      L * actualTensorL0 ℒ leechUnit = L := by
    apply TensorProduct.ext'
    intro p t
    have h := congrArg (fun A : Module.End ℂ (Oscillator ℒ) => A p ⊗ₜ[ℂ] t)
      (L_virasoro ℒ (actualInverse ℒ)
        (actualInverse_left ℒ leechUnit) (actualInverse_right ℒ leechUnit) 0 (-1))
    norm_num at h
    simpa only [actualTensorL0, raising, tensorL, tensorEnd, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.neg_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.sub_tmul, TensorProduct.neg_tmul] using h
  have h := LinearMap.congr_fun bracket x
  change actualTensorL0 ℒ leechUnit (L x) - L (actualTensorL0 ℒ leechUnit x) = L x at h
  have hx' := (actualGrade_eigen ℒ leechUnit 0 x).mp hx
  rw [hx', map_smul, sub_eq_iff_eq_add] at h
  apply (actualGrade_eigen ℒ leechUnit 2 (L x)).mpr
  rw [h]
  calc
    L x + ((leechData.rank : ℂ) / 16 + ((0 : ℕ) : ℂ) / 2) • L x =
        (1 + ((leechData.rank : ℂ) / 16 + ((0 : ℕ) : ℂ) / 2)) • L x :=
          by simp only [add_smul, one_smul]
    _ = _ := by congr 1; push_cast; ring

private theorem current_pair (i : Fin (ℒ).rank) :
    S (oddCurrent ℒ i).val (oddCurrent ℒ i).val = -2 * k i := by
  change S (neutralMode ℒ i (-1) (vacuum ℒ))
    (neutralMode ℒ i (-1) (vacuum ℒ)) = _
  rw [sourcePairing_neutralMode]
  have h := LinearMap.congr_fun (neutralMode_heisenberg ℒ i i 1 (-1)) (vacuum ℒ)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  norm_num at h
  rw [neutral_creativity ℒ i 1 (by decide), map_zero, sub_zero] at h
  rw [neg_neg, h, map_smul, smul_eq_mul, sourcePairing_vacuum]
  unfold k
  ring


private theorem create_pair (i : Fin (ℒ).rank) (t u : TwistedEven)
    (hu : u.val ∈ E 0) :
    F (create i t).val (create i u).val = -k i * F t.val u.val := by
  rw [create_val i t, actual_current_transpose]
  change -F t.val (C i 0 (create i u).val) = _
  rw [annihilate_create i u hu, map_smul, smul_eq_mul]
  ring

private abbrev twoOsc (i : Fin (ℒ).rank) (t : TwistedEven) : V :=
  C i (-1) (create i t).val

private theorem annihilate_twoOsc (i : Fin (ℒ).rank) (t : TwistedEven)
    (ht : t.val ∈ E 0) :
    C i 0 (twoOsc i t) = (2 * k i) • (create i t).val := by
  have h := c_bracket i (create i t).val
  rw [annihilate_create i t ht, map_smul, ← create_val, sub_eq_iff_eq_add, ← add_smul] at h
  rw [show k i + k i = 2 * k i by ring] at h
  exact h

private theorem twoOsc_pair (i : Fin (ℒ).rank) (t u : TwistedEven)
    (hu : u.val ∈ E 0) :
    F (twoOsc i t) (twoOsc i u) = 2 * k i ^ 2 * F t.val u.val := by
  rw [show twoOsc i t = C i (-1) (create i t).val from rfl, actual_current_transpose]
  change -F (create i t).val (C i 0 (twoOsc i u)) = _
  rw [annihilate_twoOsc i u hu, map_smul, smul_eq_mul, create_pair i t u hu]
  ring

private theorem twoOsc_lower (i : Fin (ℒ).rank) (t : TwistedEven)
    (ht : t.val ∈ E 0) :
    D₁ (twoOsc i t) = (k i / 2) • t.val := by
  change D₁ (C i (-1) (create i t).val) = _
  rw [lower_current, ground_lower_create i t ht, map_zero, zero_add,
    annihilate_create i t ht, smul_smul]
  congr 1
  ring

private theorem twoOsc_raise_pair (i : Fin (ℒ).rank) (t u : TwistedEven)
    (ht : t.val ∈ E 0) :
    F (twoOsc i t) (L u.val) = (k i / 2) * F t.val u.val := by
  rw [← actual_stress_transpose ℒ leechUnit 1 (twoOsc i t) u.val]
  change F (D₁ (twoOsc i t)) u.val = _
  rw [twoOsc_lower i t ht, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem raise_twoOsc_pair (i : Fin (ℒ).rank) (t u : TwistedEven)
    (hu : u.val ∈ E 0) :
    F (L t.val) (twoOsc i u) = (k i / 2) * F t.val u.val := by
  rw [(ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq (L t.val),
    twoOsc_raise_pair i u t hu,
    (ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq u.val]

private theorem raise_pair (t u : TwistedEven) (hu : u.val ∈ E 0) :
    F (L t.val) (L u.val) = 3 * F t.val u.val := by
  rw [actual_stress_transpose ℒ leechUnit (-1) t.val (L u.val)]
  change F t.val (D₁ (L u.val)) = _
  rw [ground_lower_raise u hu, map_smul, smul_eq_mul]

private theorem q_ground (i : Fin (ℒ).rank) (t : TwistedEven) (ht : t.val ∈ E 0) :
    ((Q (create i t)).coeff (-3) (oddCurrent ℒ i)).val =
      (Complex.I * k i) • t.val := by
  rw [show (-3 : ℤ) = -2 * 0 - 3 by decide, rightField_coeff,
    R_lowest ℒ leechUnit true 0 1 1 _ _ (oddCurrent_grade_one ℒ i)
      (create_grade i t ht) (by decide) (by decide)]
  rw [show (-2 * 0 - 3 : ℤ) = -3 by decide, upper_phase_neg_three,
    Submodule.coe_smul, J_current, annihilate_create i t ht, smul_smul]

private theorem q_two (i : Fin (ℒ).rank) (t : TwistedEven) (ht : t.val ∈ E 0) :
    ((Q (create i t)).coeff (-1) (oddCurrent ℒ i)).val =
      (-Complex.I) • twoOsc i t + (Complex.I * k i) • L t.val := by
  rw [show (-1 : ℤ) = -2 * (-1) - 3 by decide, rightField_coeff,
    (R_eq_sum_of_grade ℒ leechUnit true (-1) 1 1 _ _
      (oddCurrent_grade_one ℒ i) (create_grade i t ht)).2]
  change (∑ ell ∈ Finset.range 2, rightTerm ℒ leechUnit true (-1) (create i t) (oddCurrent ℒ i) ell).val = _
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [rightTerm, Nat.cast_zero, Nat.cast_one, add_zero, pow_zero,
    Module.End.one_apply, Nat.factorial_zero, Nat.factorial_one, inv_one, mul_one,
    show (-2 * (-1) - 3 : ℤ) = -1 by decide, upper_phase_neg_one,
    show (-1 + 1 : ℤ) = 0 by decide, show (-2 * 0 - 3 : ℤ) = -3 by decide,
    upper_phase_neg_three, pow_one, Submodule.coe_add, Submodule.coe_smul,
    translation_val, J_current]
  have h := annihilate_create i t ht
  rw [create_val] at h
  rw [h, map_smul, smul_smul]
  simp only [twoOsc, create_val]

private theorem q_ground_grade (i : Fin (ℒ).rank) (t : TwistedEven) (ht : t.val ∈ E 0) :
    ((Q (create i t)).coeff (-3) (oddCurrent ℒ i)).val ∈ E 0 := by
  rw [q_ground i t ht]
  exact (E 0).smul_mem _ ht

private theorem q_two_grade (i : Fin (ℒ).rank) (t : TwistedEven) (ht : t.val ∈ E 0) :
    ((Q (create i t)).coeff (-1) (oddCurrent ℒ i)).val ∈ E 2 := by
  rw [q_two i t ht]
  apply (E 2).add_mem
  · apply (E 2).smul_mem
    change C i (-1) (create i t).val ∈ E 2
    rw [← J_current ℒ leechUnit true i (-1) (create i t)]
    exact J_grade ℒ leechUnit true (-1) 1 1 2 _ _
      (oddCurrent_grade_one ℒ i) (create_grade i t ht) (by decide)
  · exact (E 2).smul_mem _ (stress_raise_grade _ ht)

private theorem q_ground_pair (i : Fin (ℒ).rank) (t u : TwistedEven)
    (ht : t.val ∈ E 0) (hu : u.val ∈ E 0) :
    F ((Q (create i t)).coeff (-3) (oddCurrent ℒ i)).val
      ((Q (create i u)).coeff (-3) (oddCurrent ℒ i)).val =
      -k i ^ 2 * F t.val u.val := by
  rw [q_ground i t ht, q_ground i u hu]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  linear_combination (k i ^ 2 * F t.val u.val) * Complex.I_sq

private theorem q_two_pair (i : Fin (ℒ).rank) (t u : TwistedEven)
    (ht : t.val ∈ E 0) (hu : u.val ∈ E 0) :
    F ((Q (create i t)).coeff (-1) (oddCurrent ℒ i)).val
      ((Q (create i u)).coeff (-1) (oddCurrent ℒ i)).val =
      -4 * k i ^ 2 * F t.val u.val := by
  rw [q_two i t ht, q_two i u hu]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    twoOsc_pair i t u hu, twoOsc_raise_pair i t u ht, raise_twoOsc_pair i t u hu,
    raise_pair t u hu]
  linear_combination (4 * k i ^ 2 * F t.val u.val) * Complex.I_sq

private theorem p_pair (i : Fin (ℒ).rank) (b : TwistedOdd)
    (hb : b.val ∈ E 1) (v : TwistedEven) (K : ℕ) (hv : v.val ∈ E K) (m : ℤ) :
    S ((P b).coeff (-2*m-3) v).val (oddCurrent ℒ i).val =
      F v.val ((Q b).coeff (-2*(1-m)-3) (oddCurrent ℒ i)).val := by
  rw [mu_coeff_of_grade true 1 K m b v hb hv,
    mixedPairState_pairing true 1 K m b v hb hv,
    mixedPairing_lowest true 1 m (by decide)]
  change Complex.I ^ (-4 : ℤ) * F v.val (R ℒ leechUnit true (1-m) b (oddCurrent ℒ i)).val = _
  rw [upper_phase_neg_four, one_mul, rightField_coeff]

/-- The ordered four literal products at the specified mode indices. -/
def orderedProducts (b c : TwistedOdd) (o : OddCarrier ℒ) : OddCarrier ℒ :=
  -((P b).coeff (-7) ((Q c).coeff (-1) o) +
    (P c).coeff (-7) ((Q b).coeff (-1) o)) +
  (3 : ℂ) • ((P b).coeff (-5) ((Q c).coeff (-3) o) +
    (P c).coeff (-5) ((Q b).coeff (-3) o))

private theorem ordered_pair (i : Fin (ℒ).rank) (t u : TwistedEven)
    (ht : t.val ∈ E 0) (hu : u.val ∈ E 0) :
    S (orderedProducts (create i t) (create i u) (oddCurrent ℒ i)).val
      (oddCurrent ℒ i).val =
      2 * k i ^ 2 * F t.val u.val := by
  simp only [orderedProducts, Submodule.coe_add, Submodule.coe_neg, Submodule.coe_smul,
    map_add, map_neg, map_smul, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, smul_eq_mul]
  have h1 := p_pair i (create i t) (create_grade i t ht) _ 2 (q_two_grade i u hu) 2
  have h2 := p_pair i (create i u) (create_grade i u hu) _ 2 (q_two_grade i t ht) 2
  have h3 := p_pair i (create i t) (create_grade i t ht) _ 0 (q_ground_grade i u hu) 1
  have h4 := p_pair i (create i u) (create_grade i u hu) _ 0 (q_ground_grade i t ht) 1
  change S ((P (create i t)).coeff (-7) ((Q (create i u)).coeff (-1) (oddCurrent ℒ i))).val
    (oddCurrent ℒ i).val = F ((Q (create i u)).coeff (-1) (oddCurrent ℒ i)).val
      ((Q (create i t)).coeff (-1) (oddCurrent ℒ i)).val at h1
  change S ((P (create i u)).coeff (-7) ((Q (create i t)).coeff (-1) (oddCurrent ℒ i))).val
    (oddCurrent ℒ i).val = F ((Q (create i t)).coeff (-1) (oddCurrent ℒ i)).val
      ((Q (create i u)).coeff (-1) (oddCurrent ℒ i)).val at h2
  change S ((P (create i t)).coeff (-5) ((Q (create i u)).coeff (-3) (oddCurrent ℒ i))).val
    (oddCurrent ℒ i).val = F ((Q (create i u)).coeff (-3) (oddCurrent ℒ i)).val
      ((Q (create i t)).coeff (-3) (oddCurrent ℒ i)).val at h3
  change S ((P (create i u)).coeff (-5) ((Q (create i t)).coeff (-3) (oddCurrent ℒ i))).val
    (oddCurrent ℒ i).val = F ((Q (create i t)).coeff (-3) (oddCurrent ℒ i)).val
      ((Q (create i u)).coeff (-3) (oddCurrent ℒ i)).val at h4
  rw [h1, h2, h3, h4, q_two_pair i t u ht hu, q_two_pair i u t hu ht,
    q_ground_pair i t u ht hu, q_ground_pair i u t hu ht,
    (ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq u.val t.val]
  ring

private abbrev leechPosDef : ((ℒ).G.map (Int.cast : ℤ → ℝ)).PosDef := leech_spec.2.2.1

private theorem original_vacuum (b c : TwistedOdd) (hb : b.val ∈ E 1)
    (hc : c.val ∈ E 1) :
    originalI ℒ leechUnit leechPosDef 3 b c = F c.val b.val • fixedVacuum ℒ := by
  have hvac : vacuum ℒ ∈ MixedIntertwiner.fixedGrade ℒ 0 := by
    constructor
    · rw [grade_zero ℒ leechPosDef]
      exact Submodule.subset_span (by simp)
    · exact (mem_fixedSpace ℒ _).mpr (theta_vacuum ℒ)
  let a : MixedIntertwiner.fixedGrade ℒ 0 := ⟨vacuum ℒ, hvac⟩
  have hb' := (actualGrade_eigen ℒ leechUnit 1 b.val).mp hb
  have hc' := (actualGrade_eigen ℒ leechUnit 1 c.val).mp hc
  rw [leech_spec.1] at hb' hc'
  norm_num at hb' hc'
  rw [originalI_three_eq_vacuum_smul ℒ leechUnit leechPosDef leech_spec.1 b c hb' hc' a rfl,
    weight_two_vacuum_pairing ℒ leechUnit leech_spec.1 b c hb' hc' a rfl]

/-- The actual inner products vanish at every subsequent integer j in
the r=3, p=q=-1 product grid. -/
theorem inner_truncation (b : TwistedOdd) (hb : b.val ∈ E 1)
    (o : OddCarrier ℒ) (ho : o.val ∈ grade ℒ 1) (j : ℕ) (hj : 2 ≤ j) :
    (Q b).coeff (-1-2*(j : ℤ)) o = 0 := by
  rw [show (-1-2*(j : ℤ)) = -2*((j : ℤ)-1)-3 by ring, rightField_coeff,
    (R_eq_sum_of_grade ℒ leechUnit true ((j : ℤ)-1) 1 1 b o ho hb).2]
  have h : ((1 + 2 * 1 - 2 * ((j : ℤ)-1) - 3) / 2 + 1).toNat = 0 := by omega
  change (∑ ell ∈ Finset.range ((1 + 2 * 1 - 2 * ((j : ℤ)-1) - 3) / 2 + 1).toNat,
    rightTerm ℒ leechUnit true ((j : ℤ)-1) b o ell) = 0
  rw [h, Finset.sum_range_zero]

/-- Every higher iterate coefficient is zero by the actual mixed-pair
weight cutoff for the two first-grade twisted states. -/
theorem iterate_truncation (b c : TwistedOdd) (hb : b.val ∈ E 1)
    (hc : c.val ∈ E 1) (j : ℕ) (hj : 0 < j) :
    originalI ℒ leechUnit leechPosDef (3 + (j : ℤ)) b c = 0 := by
  have hb' := (actualGrade_eigen ℒ leechUnit 1 b.val).mp hb
  have hc' := (actualGrade_eigen ℒ leechUnit 1 c.val).mp hc
  rw [leech_spec.1] at hb' hc'
  norm_num at hb' hc'
  exact originalI_sharp ℒ leechUnit leechPosDef leech_spec.1 2 2 _ b c hb' hc' (by omega)

/-- The ordinary -1 mode of the original vacuum coefficient is the
stated scalar multiple on the actual odd source. -/
theorem vacuum_iterate (b c : TwistedOdd) (hb : b.val ∈ E 1)
    (hc : c.val ∈ E 1) (o : OddCarrier ℒ) :
    oddMode ℒ (originalI ℒ leechUnit leechPosDef 3 b c) (-1) o = F c.val b.val • o := by
  rw [original_vacuum b c hb hc]
  apply Subtype.ext
  change ((LatticeAllStateField.Y ℒ (F c.val b.val • vacuum ℒ))[[-1]]) o.val =
    F c.val b.val • o.val
  rw [map_smul, LatticeAllStateField.stateField_vacuum]
  simp [FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]

/-- For any original current direction there is an actual first-oscillator
pair with a nonzero vacuum coefficient and an equal nonzero ordered BBO
scalar coefficient in the literal raw convention. -/
theorem vacuum_normalization (i : Fin (ℒ).rank) :
    ∃ (u : TwistedEven) (b c : TwistedOdd) (β : ℂ),
      u.val ∈ E 0 ∧ F u.val leechGroundVector.val = 1 ∧
      b = J ℒ leechUnit false (-1) (oddCurrent ℒ i) leechGroundVector ∧
      c = J ℒ leechUnit false (-1) (oddCurrent ℒ i) u ∧
      b.val ∈ E 1 ∧ c.val ∈ E 1 ∧
      (oddCurrent ℒ i).val ∈ grade ℒ 1 ∧
      β = -((leechData.G i i : ℂ) / 2) ∧ β ≠ 0 ∧
      originalI ℒ leechUnit leechPosDef 3 b c = β • fixedVacuum ℒ ∧
      S (orderedProducts b c (oddCurrent ℒ i)).val (oddCurrent ℒ i).val =
        S (β • (oddCurrent ℒ i).val) (oddCurrent ℒ i).val ∧
      S (β • (oddCurrent ℒ i).val) (oddCurrent ℒ i).val = 2 * ((leechData.G i i : ℂ) / 2) ^ 2 ∧
      S (β • (oddCurrent ℒ i).val) (oddCurrent ℒ i).val ≠ 0 := by
  let t := leechGroundVector
  obtain ⟨u, hu, hpair⟩ := exists_grade_detector ℒ leechUnit false 0 t
    groundBasis_energy leechGroundVector_nonzero (by norm_num [NativeOddTwistedIntertwiner.paritySign])
  have htu : F t.val u.val = 1 :=
    ((ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq t.val u.val).trans hpair
  have hβ : F (create i u).val (create i t).val = -k i := by
    rw [create_pair i u t groundBasis_energy, hpair, mul_one]
  have hiter : S ((-k i) • (oddCurrent ℒ i).val) (oddCurrent ℒ i).val = 2 * k i ^ 2 := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, current_pair]
    ring
  refine ⟨u, create i t, create i u, -k i, hu, hpair, rfl, rfl, create_grade i t groundBasis_energy,
    create_grade i u hu, oddCurrent_grade_one ℒ i, rfl, neg_ne_zero.mpr (k_ne_zero i), ?_, ?_,
    hiter, ?_⟩
  · rw [original_vacuum _ _ (create_grade i t groundBasis_energy) (create_grade i u hu), hβ]
  · rw [ordered_pair i t u groundBasis_energy hu, htu, mul_one, hiter]
  · rw [hiter]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (k_ne_zero i))

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOVacuumNormalization
