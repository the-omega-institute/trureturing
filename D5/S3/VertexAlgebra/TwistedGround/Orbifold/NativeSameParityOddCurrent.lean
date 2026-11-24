/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityOddCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityOddCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral mixed current coefficients on the first Leech oscillator tensors. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityOddDirectionalSpectrum
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityZhuTopBalance
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityCurrentTopDetection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity.OddDirectional

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.NormFourLowestGrades (actualGrade_one_eq_span)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockGradedTrace (actualGrade)
open ActualLeechHalfFockCurrents (orthonormalBasis orthonormalBasis_pairing)
open ActualLeechHalfFockQuadraticTransport (FrameIndex)
open LatticeLightConeCoordinates (E g lin lin_homogeneous standardBasis)
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients
open NativeOddTwistedIntertwiner (OddCarrier Twisted paritySign oddCurrent oddMode oddTranslation twistedTop
  twistedTopReadout fixedAction fixedTopZero oddZhuResidue quadraticOddTopOscillator
  neutralPair_oddCurrent_one neutralPair_oddCurrent_zero leechUnit)
open Lattice.ActualFixedC2 (neutralPair)
open MvPolynomial

open private oddMode_val oddCurrent_grade_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private current_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeQuadraticZhuCurrent
open private mixed_commutator_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityZhuTopBalance

noncomputable section

local notation "ℒ" => leechData
local notation "G₀" => ActualGround ℒ leechUnit
local notation "T₁" => twistedTop ℒ leechUnit true
local notation "Ω[" j "]" => fixedTopZero true (leechRankOneOmega j) 2 (leechRankOneOmega_grade j)
local instance : AddCommGroup T₁ := @Submodule.addCommGroup ℂ (Twisted ℒ leechUnit true) _ _ _ T₁

private def currentAlong : E ℒ →ₗ[ℂ] OddCarrier ℒ where
  toFun u := ∑ k, u k • oddCurrent ℒ k
  map_add' u w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z u := by simp [Finset.smul_sum, smul_smul]

def frameCurrent (i : FrameIndex) : OddCarrier ℒ := currentAlong (orthonormalBasis i)

private theorem currentAlong_grade (u : E ℒ) : (currentAlong u).val ∈ grade ℒ 1 := by
  change ((minusSpace ℒ).subtype (∑ k, u k • oddCurrent ℒ k)) ∈ _
  simp only [map_sum, map_smul, Submodule.subtype_apply]
  exact Submodule.sum_mem _ fun k _ => (grade ℒ 1).smul_mem _ (oddCurrent_grade_one ℒ k)

theorem frameCurrent_grade (i : FrameIndex) : (frameCurrent i).val ∈ grade ℒ 1 :=
  currentAlong_grade _

private theorem currentAlong_val (u : E ℒ) :
    (currentAlong u).val = Finsupp.single 0 (lin 0 u) := by
  change (minusSpace ℒ).subtype (∑ k, u k • oddCurrent ℒ k) = _
  simp only [map_sum, map_smul, Submodule.subtype_apply, current_val]
  change (∑ k, u k • (Finsupp.lsingle (R := ℂ) (0 : Charge ℒ)) (X (k,0))) =
    (Finsupp.lsingle (R := ℂ) (0 : Charge ℒ)) (∑ k, u k • X (k,0))
  simp only [map_sum, map_smul]

private theorem omega_expansion (j : FrameIndex) :
    leechRankOneOmega j = ∑ a, ∑ b, ((1 / 2 : ℂ) * orthonormalBasis j a *
        orthonormalBasis j b) • neutralPair ℒ a b 0 0 := by
  let u := orthonormalBasis j
  apply Subtype.ext
  change (Finsupp.lsingle (R := ℂ) (0 : Charge ℒ))
    ((1 / 2 : ℂ) • ((∑ a, u a • X (a,0)) * (∑ b, u b • X (b,0)))) =
    (fixedSpace ℒ).subtype (∑ a, ∑ b, ((1 / 2 : ℂ) * u a * u b) • neutralPair ℒ a b 0 0)
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul, map_sum, map_smul, Submodule.subtype_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, mul_comm (X (b,0)) (X (a,0))]
  rfl

private def sourceAction (n : ℤ) (b : OddCarrier ℒ) : FixedCarrier ℒ →ₗ[ℂ] OddCarrier ℒ where
  toFun a := oddMode ℒ a n b
  map_add' a a' := by
    apply Subtype.ext
    simp only [oddMode_val, mu, VertexOperator.ncoeff, Submodule.coe_add, map_add,
      Pi.add_apply, LinearMap.add_apply]
  map_smul' z a := by
    apply Subtype.ext
    simp only [oddMode_val, mu, VertexOperator.ncoeff, Submodule.coe_smul, map_smul,
      Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]

private theorem source_one (j i : FrameIndex) :
    oddMode ℒ (leechRankOneOmega j) 1 (frameCurrent i) =
      g ℒ (orthonormalBasis j) (orthonormalBasis i) • frameCurrent j := by
  let u := orthonormalBasis j
  let w := orthonormalBasis i
  rw [show oddMode ℒ (leechRankOneOmega j) 1 (frameCurrent i) =
    sourceAction 1 (frameCurrent i) (leechRankOneOmega j) from rfl, omega_expansion]
  simp only [map_sum, map_smul]
  change (∑ a, ∑ b, ((1 / 2 : ℂ) * u a * u b) •
    oddMode ℒ (neutralPair ℒ a b 0 0) 1 (∑ k, w k • oddCurrent ℒ k)) =
      g ℒ u w • (∑ a, u a • oddCurrent ℒ a)
  simp only [map_sum, map_smul, neutralPair_oddCurrent_one, smul_add, smul_smul,
    Finset.smul_sum, Finset.sum_add_distrib]
  have hsym :
      (∑ a, ∑ b, ∑ k, ((1 / 2 : ℂ) * u a * u b * (w k * ((ℒ).G a k : ℂ))) •
        oddCurrent ℒ b) =
      ∑ a, ∑ b, ∑ k, ((1 / 2 : ℂ) * u a * u b * (w k * ((ℒ).G b k : ℂ))) •
        oddCurrent ℒ a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ring
  rw [hsym, ← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, ← add_smul, g, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [← Finset.sum_smul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem source_zero (j i : FrameIndex) :
    oddMode ℒ (leechRankOneOmega j) 0 (frameCurrent i) =
      oddTranslation ℒ (oddMode ℒ (leechRankOneOmega j) 1 (frameCurrent i)) := by
  change sourceAction 0 (frameCurrent i) (leechRankOneOmega j) =
    oddTranslation ℒ (sourceAction 1 (frameCurrent i) (leechRankOneOmega j))
  rw [omega_expansion]
  simp only [map_sum, map_smul]
  change (∑ a, ∑ b, _ • oddMode ℒ (neutralPair ℒ a b 0 0) 0
    (∑ k, orthonormalBasis i k • oddCurrent ℒ k)) =
      ∑ a, ∑ b, _ • oddTranslation ℒ (oddMode ℒ (neutralPair ℒ a b 0 0) 1
        (∑ k, orthonormalBasis i k • oddCurrent ℒ k))
  simp only [map_sum, map_smul, neutralPair_oddCurrent_zero]

/-- The two source terms in the integral mode-one commutator vanish. -/
theorem orthogonal_singular_products {i j : FrameIndex} (h : j ≠ i) :
    oddMode ℒ (leechRankOneOmega j) 0 (frameCurrent i) = 0 ∧
      oddMode ℒ (leechRankOneOmega j) 1 (frameCurrent i) = 0 := by
  have h₁ : oddMode ℒ (leechRankOneOmega j) 1 (frameCurrent i) = 0 := by
    rw [source_one, orthonormalBasis_pairing, if_neg (Ne.symm h), zero_smul]
  exact ⟨by rw [source_zero, h₁, map_zero], h₁⟩

/-- The selected current coefficient as an endomorphism of the odd top. -/
def currentEvaluation (F : LawfulField ℒ leechUnit true) (i : FrameIndex) :
    Module.End ℂ T₁ :=
  LinearMap.codRestrict _ ((F.coeff 0 (frameCurrent i)).comp (twistedTop ℒ leechUnit true).subtype)
    (fun v => by
      have h := (zhuTopEvaluation F v (frameCurrent i)).property
      rw [zhuTopEvaluation_homogeneous F v 1 _ (frameCurrent_grade i)] at h
      exact h)

theorem currentEvaluation_eq (F : LawfulField ℒ leechUnit true) (i : FrameIndex) (v : T₁) :
    currentEvaluation F i v = zhuTopEvaluation F v (frameCurrent i) := by
  apply Subtype.ext
  exact (zhuTopEvaluation_homogeneous F v 1 _ (frameCurrent_grade i)).symm

theorem current_commutes (F : LawfulField ℒ leechUnit true) {i j : FrameIndex} (h : j ≠ i)
    (v : T₁) : Ω[j] (currentEvaluation F i v) = currentEvaluation F i (Ω[j] v) := by
  apply Subtype.ext
  change fixedAction true (leechRankOneOmega j) 1 (F.coeff 0 (frameCurrent i) v.val) =
    F.coeff 0 (frameCurrent i) (fixedAction true (leechRankOneOmega j) 1 v.val)
  have hc := mixed_commutator_one F (leechRankOneOmega j) (frameCurrent i) v.val 0
  obtain ⟨h₀, h₁⟩ := orthogonal_singular_products h
  rw [h₀, h₁] at hc
  exact sub_eq_zero.mp (by simpa only [map_zero, LinearMap.zero_apply, add_zero] using hc)

private def directionProjector (j : FrameIndex) : Module.End ℂ T₁ :=
  (2 : ℂ) • (Ω[j] - (1 / 16 : ℂ) • LinearMap.id)

private theorem projector_generator (j k : FrameIndex) (x : G₀) :
    directionProjector j (frameOscillator k x) = if k = j then frameOscillator k x else 0 := by
  simp only [directionProjector, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    leechRankOneOmega_odd_zeroMode]
  split_ifs <;> module

private theorem oddTop_span {D : LatticeData} {hu : IsUnit D.G.det} :
    Submodule.span ℂ (Set.range (fun p : Fin D.rank × ActualGround D hu =>
      quadraticOddTopOscillator D hu p.1 p.2)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun p : Fin D.rank × ActualGround D hu =>
    quadraticOddTopOscillator D hu p.1 p.2))
  let A : twistedTop D hu true →ₗ[ℂ] ActualTensor D hu :=
    (paritySpace D hu (paritySign true)).subtype.comp (twistedTop D hu true).subtype
  have hA : Function.Injective A := fun _ _ he => Subtype.ext (Subtype.ext he)
  have hgrade : actualGrade D hu 1 ≤ S.map A := by
    rw [actualGrade_one_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, x⟩, rfl⟩
    apply Submodule.mem_map.mpr
    exact ⟨quadraticOddTopOscillator D hu i x, Submodule.subset_span ⟨(i, x), rfl⟩, rfl⟩
  apply top_unique
  intro v _
  obtain ⟨u, huS, huv⟩ := Submodule.mem_map.mp (hgrade v.property)
  exact hA huv ▸ huS

private theorem firstOscillator_span :
    Submodule.span ℂ (Set.range (fun p : FrameIndex × G₀ => frameOscillator p.1 p.2)) = ⊤ := by
  classical
  apply top_unique
  rw [← oddTop_span (D := ℒ) (hu := leechUnit)]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨k, x⟩, rfl⟩
  let b := orthonormalBasis
  let w := standardBasis ℒ k
  let S := Submodule.span ℂ (Set.range (fun p : FrameIndex × G₀ => frameOscillator p.1 p.2))
  have hw : ∑ d, b.equivFun w d • b d = w := by
    simpa only [Module.Basis.equivFun_symm_apply] using b.equivFun.symm_apply_apply w
  have hk : firstOscillator w x = quadraticOddTopOscillator ℒ leechUnit k x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [firstOscillator_val]
    change (lin 0 (standardBasis ℒ k)) ⊗ₜ[ℂ] x = (X (k,0) : Oscillator ℒ) ⊗ₜ[ℂ] x
    congr 1
    simp [lin, standardBasis, Pi.single_apply]
  change quadraticOddTopOscillator ℒ leechUnit k x ∈ S
  rw [← hk, ← hw]
  have ha (u : E ℒ) : (firstOscillator u x).val.val = lin 0 u ⊗ₜ[ℂ] x :=
    firstOscillator_val u x
  have h_expand : firstOscillator (∑ d, b.equivFun w d • b d) x =
      ∑ d, b.equivFun w d • frameOscillator d x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [ha]
    let B := (TensorProduct.mk ℂ (Oscillator ℒ) G₀).flip x
    let A : T₁ →ₗ[ℂ] ActualTensor ℒ leechUnit :=
      (paritySpace ℒ leechUnit (paritySign true)).subtype.comp (T₁).subtype
    change B (lin 0 (∑ d, b.equivFun w d • b d)) =
      A (∑ d, b.equivFun w d • frameOscillator d x)
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro d _
    rw [show A (frameOscillator d x) = B (lin 0 (b d)) from ha (b d)]
  rw [h_expand]
  exact S.sum_mem fun d _ => S.smul_mem _ (Submodule.subset_span ⟨(d, x), rfl⟩)

private theorem projector_range (j : FrameIndex) (v : T₁) :
    directionProjector j v ∈ LinearMap.range (frameOscillator j) := by
  have h : Submodule.span ℂ (Set.range (fun p : FrameIndex × G₀ => frameOscillator p.1 p.2)) ≤
      (LinearMap.range (frameOscillator j)).comap (directionProjector j) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, x⟩, rfl⟩
    change directionProjector j (frameOscillator k x) ∈ LinearMap.range (frameOscillator j)
    rw [projector_generator]
    split_ifs with hk
    · subst k
      exact ⟨x, rfl⟩
    · exact (LinearMap.range (frameOscillator j)).zero_mem
  rw [firstOscillator_span] at h
  exact h Submodule.mem_top

private theorem projector_sum (v : T₁) : ∑ j, directionProjector j v = v := by
  let A : Module.End ℂ T₁ := (∑ j, directionProjector j) - LinearMap.id
  have h : Submodule.span ℂ (Set.range (fun p : FrameIndex × G₀ => frameOscillator p.1 p.2)) ≤
      LinearMap.ker A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, x⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    change A (frameOscillator k x) = 0
    dsimp only [A]
    rw [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.id_apply]
    rw [Finset.sum_eq_single k]
    · change directionProjector k (frameOscillator k x) - frameOscillator k x = 0
      rw [projector_generator, ite_eq_left rfl, sub_self]
    · intro j _ hj
      change directionProjector j (frameOscillator k x) = 0
      rw [projector_generator, ite_eq_right (Ne.symm hj)]
    · simp
  rw [firstOscillator_span] at h
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (h (show v ∈ (⊤ : Submodule ℂ T₁) from trivial)))

private theorem projector_commutes (F : LawfulField ℒ leechUnit true) {i j : FrameIndex}
    (h : j ≠ i) (v : T₁) :
    directionProjector j (currentEvaluation F i v) =
      currentEvaluation F i (directionProjector j v) := by
  simp only [directionProjector, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_smul, map_sub, current_commutes F h]

/-- Each direction means the whole oscillator copy of the actual ground module. -/
theorem current_preserves_direction (F : LawfulField ℒ leechUnit true)
    (i d : FrameIndex) (x : G₀) :
    ∃ y : G₀, currentEvaluation F i (frameOscillator d x) = frameOscillator d y := by
  classical
  let v := frameOscillator d x
  let z := currentEvaluation F i v
  have hz : directionProjector d z = z := by
    by_cases h : d = i
    · have hz' (j : FrameIndex) (hj : j ≠ d) : directionProjector j z = 0 := by
        rw [show directionProjector j z = currentEvaluation F i (directionProjector j v) from
          projector_commutes F (h ▸ hj) v]
        rw [show directionProjector j v = 0 by
          change directionProjector j (frameOscillator d x) = 0
          rw [projector_generator, ite_eq_right (Ne.symm hj)], map_zero]
      calc
        directionProjector d z = ∑ j, directionProjector j z := by
          symm
          exact Finset.sum_eq_single d (fun j _ hj => hz' j hj)
            (fun hd => (hd (Finset.mem_univ d)).elim)
        _ = z := projector_sum z
    · rw [show directionProjector d z = currentEvaluation F i (directionProjector d v) from
        projector_commutes F h v]
      simp only [v, projector_generator, ite_true, z]
  obtain ⟨y, hy⟩ := projector_range d z
  exact ⟨y, (hy.trans hz).symm⟩


open FieldNormalProduct LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open LatticeActualAnnihilation
open LatticeLightConeCoordinates (a_single polynomialCurrent_negative polynomialCurrent_zero
  polynomialCurrent_positive oldDerivative oldDerivative_lin)
open Lattice.ActualZhuRankOneOdd (L abe_zhu_identity oddCurrent_parity)
open private normalization normalization_mul inverseGram abeState_grade sum_rank_one
  from D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd
open private rankOne_abe_lift rankOne_odd_lift neutralLift neutralLift_apply oddResidue_nat
  neutral_derivative_lift
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
open private derivative_modes normal_right_identity
  from D5.S3.VertexAlgebra.LatticeAllStateField
open private multiplication_recursion from
  D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule

local notation "R" => Lattice.ActualZhuRankOneOdd.datum
local notation "b₁" => Lattice.ActualZhuRankOneOdd.oddCurrent
local notation "A₁" => Lattice.ActualZhuRankOneOdd.abeState
local notation "ι" => StateFieldResidueReconstruction.epsilon

local instance : NeZero (R).rank := ⟨by decide⟩
local instance : Subsingleton (Fin (R).rank) := by change Subsingleton (Fin 1); infer_instance

private abbrev scale : ℂ := 2 * normalization

private theorem scale_sq : scale * scale = (2 : ℂ) := by
  change (2 * normalization) * (2 * normalization) = _
  linear_combination 4 * normalization_mul

private theorem norm_scale : normalization * scale = 1 := by
  change normalization * (2 * normalization) = _
  linear_combination 2 * normalization_mul

private def substFrame (i : FrameIndex) : Oscillator R →ₐ[ℂ] Oscillator ℒ :=
  aeval (fun j : Index R => scale • lin j.2 (orthonormalBasis i))

private theorem substFrame_X (i : FrameIndex) (j : Index R) :
    substFrame i (X j) = scale • lin j.2 (orthonormalBasis i) :=
  aeval_X _ _

private def transport (i : FrameIndex) : Carrier R →ₗ[ℂ] Carrier ℒ :=
  (neutralLift ℒ).comp ((substFrame i).toLinearMap.comp (Finsupp.lapply 0))

private theorem transport_single (i : FrameIndex) (p : Oscillator R) :
    transport i (neutralLift R p) = neutralLift ℒ (substFrame i p) := by
  simp [transport, neutralLift_apply]

private theorem transport_derivation (i : FrameIndex) (j : Fin (R).rank) (r : ℕ)
    (p : Oscillator R) :
    substFrame i (annihilate R j r p) =
      scale • oldDerivative (orthonormalBasis i) r (substFrame i p) := by
  have hX (k : Index R) : substFrame i (annihilate R j r (X k)) =
      scale • oldDerivative (orthonormalBasis i) r (substFrame i (X k)) := by
    rcases k with ⟨k, t⟩
    have hG : ((R).G j k : ℂ) = 2 := by norm_num [show (R).G j k = 2 from rfl]
    by_cases h : r = t
    · rw [annihilate_X, substFrame_X, Derivation.map_smul, oldDerivative_lin,
        if_pos h, if_pos h, orthonormalBasis_pairing, if_pos rfl]
      simp only [hG, map_smul, map_one, one_smul, smul_smul, scale_sq]
    · rw [annihilate_X, substFrame_X, Derivation.map_smul, oldDerivative_lin, if_neg h, if_neg h]
      simp
  induction p using MvPolynomial.induction_on with
  | C z =>
    change substFrame i (annihilationDerivation R j r (algebraMap ℂ (Oscillator R) z)) =
      scale • oldDerivative (orthonormalBasis i) r (substFrame i (algebraMap ℂ (Oscillator R) z))
    rw [Derivation.map_algebraMap, map_zero, AlgHom.commutes, Derivation.map_algebraMap, smul_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add]
  | mul_X p k hp =>
    simp only [annihilate_mul, map_mul, map_add, Derivation.leibniz, hp, hX, smul_add,
      smul_mul_assoc, mul_smul_comm]
    ring

private theorem transport_current (i : FrameIndex) (j : Fin (R).rank) (n : ℤ)
    (p : Oscillator R) :
    substFrame i (neutralPolynomialMode R j 0 n p) =
      scale • LatticeLightConeCoordinates.polynomialCurrent
        (orthonormalBasis i) 0 n (substFrame i p) := by
  cases n with
  | negSucc n =>
    rw [show Int.negSucc n = -(n : ℤ) - 1 by omega, neutralPolynomialMode_negative,
      polynomialCurrent_negative]
    simp only [LinearMap.mulLeft_apply, map_mul, substFrame_X, smul_mul_assoc]
  | ofNat n =>
    cases n with
    | zero =>
      change substFrame i (neutralPolynomialMode R j 0 0 p) =
        scale • LatticeLightConeCoordinates.polynomialCurrent (orthonormalBasis i) 0 0 (substFrame i p)
      rw [polynomialCurrent_zero]
      simp [neutralPolynomialMode, bilinear, LatticeLightConeCoordinates.chargeVector]
    | succ n =>
      change substFrame i (neutralPolynomialMode R j 0 ((n : ℤ) + 1) p) =
        scale • LatticeLightConeCoordinates.polynomialCurrent (orthonormalBasis i) 0
          ((n : ℤ) + 1) (substFrame i p)
      rw [neutralPolynomialMode_positive, polynomialCurrent_positive]
      simp only [LinearMap.smul_apply, map_smul, transport_derivation, smul_smul,
        mul_comm (n + 1 : ℂ)]

private theorem jet_field (D : LatticeData) (j : Index D) :
    Y D (Finsupp.single 0 (X j)) = dividedDerivative j.2 (neutralField D j.1) := by
  rw [show (X j : Oscillator D) = monomial (Finsupp.single j 1) 1 from rfl,
    stateField_monomial]
  simp only [LatticeAllStateField.occurrences, Finsupp.toMultiset_single, one_nsmul,
    Multiset.toList_singleton, LatticeAllStateField.wordField]
  rw [actual_zero, normal_right_identity]

private abbrev directionJet (i : FrameIndex) (r : ℕ) : VertexOperator ℂ (Carrier ℒ) :=
  Y ℒ (neutralLift ℒ (lin r (orthonormalBasis i)))

private theorem directionJet_mode (i : FrameIndex) (r : ℕ) (n : ℤ) (p : Oscillator ℒ) :
    (directionJet i r [[n]]) (neutralLift ℒ p) =
      ((Ring.choose (-n - 1 + r) r : ℤ) : ℂ) • neutralLift ℒ
        (LatticeLightConeCoordinates.polynomialCurrent (orthonormalBasis i) 0 (n-r) p) := by
  let u := orthonormalBasis i
  change ((Y ℒ (neutralLift ℒ (∑ k, u k • X (k,r))))[[n]]) (neutralLift ℒ p) = _
  simp only [map_sum, map_smul, neutralLift_apply, jet_field, VertexOperator.ncoeff,
    Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ k, u k • ((dividedDerivative r (neutralField ℒ k))[[n]]) (neutralLift ℒ p)) = _
  have hjet (k : Fin (ℒ).rank) :
      ((dividedDerivative r (neutralField ℒ k))[[n]]) =
        ((Ring.choose (-n - 1 + r) r : ℤ) : ℂ) • neutralMode ℒ k (n-r) :=
    derivative_modes ℒ (k,r) n
  simp only [hjet, LinearMap.smul_apply, smul_smul]
  change (∑ k, (u k * _) • neutralMode ℒ k (n-r) (neutralLift ℒ p)) =
    _ • neutralLift ℒ (LatticeLightConeCoordinates.polynomialCurrent u 0 (n-r) p)
  rw [← show LatticeLightConeCoordinates.a u (n-r) (neutralLift ℒ p) =
    neutralLift ℒ (LatticeLightConeCoordinates.polynomialCurrent u 0 (n-r) p) from
      a_single u _ 0 p]
  simp only [LatticeLightConeCoordinates.a, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (u k)]

private theorem transport_jet (i : FrameIndex) (j : Index R) (n : ℤ) (p : Oscillator R) :
    transport i (((dividedDerivative j.2 (neutralField R j.1))[[n]]) (neutralLift R p)) =
      scale • (directionJet i j.2 [[n]]) (transport i (neutralLift R p)) := by
  rw [derivative_modes, LinearMap.smul_apply, map_smul, transport_single,
    directionJet_mode]
  have hneutral : neutralMode R j.1 (n-j.2) (neutralLift R p) =
      neutralLift R (neutralPolynomialMode R j.1 0 (n-j.2) p) := by
    simp only [neutralLift_apply, neutralMode_single]
  rw [hneutral, transport_single, transport_current, map_smul, smul_smul, smul_smul,
    mul_comm scale]

private theorem frame_quadratic_field (i : FrameIndex) (r t : ℕ) :
    Y ℒ (neutralLift ℒ (lin r (orthonormalBasis i) * lin t (orthonormalBasis i))) =
      (normalMinusOne (directionJet i r) (directionJet i t)).1 := by
  let u := orthonormalBasis i
  have hmode : mu ℒ (neutralLift ℒ (lin r u)) (-1) (neutralLift ℒ (lin t u)) =
      neutralLift ℒ (lin r u * lin t u) := by
    change (directionJet i r [[-1]]) (neutralLift ℒ (lin t u)) = _
    rw [directionJet_mode, show (-1 : ℤ) - r = -(r : ℤ) - 1 by omega,
      polynomialCurrent_negative]
    rw [show (-(-1 : ℤ) - 1 + r) = ((r : ℕ) : ℤ) by omega]
    simp only [Ring.choose_natCast, Nat.choose_self, Nat.cast_one, Int.cast_one, one_smul]
    rfl
  rw [← hmode, LatticeActualStateFieldCalculus.minus_one_product_field]

/-- Transport of the two actual neutral source factors used by the stress
and the Abe row, with their common Gram normalization. -/
private theorem transport_pair_mode (i : FrameIndex) (j k : Index R) (n : ℤ)
    (p : Oscillator R) :
    transport i (mu R (neutralLift R (X j * X k)) n (neutralLift R p)) =
      (2 : ℂ) • mu ℒ (neutralLift ℒ (lin j.2 (orthonormalBasis i) *
        lin k.2 (orthonormalBasis i))) n (neutralLift ℒ (substFrame i p)) := by
  let A := dividedDerivative j.2 (neutralField R j.1)
  let B := dividedDerivative k.2 (neutralField R k.1)
  let A' := directionJet i j.2
  let B' := directionJet i k.2
  let v := neutralLift R p
  have hs : Y R (neutralLift R (X j * X k)) = (normalMinusOne A B).1 := by
    change Y R (Finsupp.single 0 (X j * X k)) = _
    have he := multiplication_recursion R j 0 (X k)
    rw [show Y R (Finsupp.single 0 (X k)) = B from jet_field R k] at he
    exact he
  change transport i ((Y R (neutralLift R (X j * X k))[[n]]) v) =
    (2 : ℂ) • (Y ℒ (neutralLift ℒ (lin j.2 (orthonormalBasis i) *
      lin k.2 (orthonormalBasis i))) [[n]]) (neutralLift ℒ (substFrame i p))
  rw [hs, frame_quadratic_field, ← transport_single i p,
    (normalMinusOne A B).2, (normalMinusOne A' B').2,
    map_add, map_finsum (transport i) (normal_forward_finite R A B n v),
    map_finsum (transport i) (normal_reverse_finite R A B n v),
    smul_add, smul_finsum, smul_finsum]
  congr 1
  · apply congrArg (fun f : ℕ → Carrier ℒ => ∑ᶠ k, f k)
    funext m
    obtain ⟨q, hq⟩ := neutral_derivative_lift R k (n+m) p
    change (B[[n+m]]) v = neutralLift R q at hq
    have hB := transport_jet i k (n+m) p
    change transport i ((B[[n+m]]) v) = scale • (B'[[n+m]]) (transport i v) at hB
    rw [hq, transport_jet, ← hq, hB, map_smul, smul_smul, scale_sq]
  · apply congrArg (fun f : ℕ → Carrier ℒ => ∑ᶠ k, f k)
    funext m
    obtain ⟨q, hq⟩ := neutral_derivative_lift R j m p
    change (A[[m]]) v = neutralLift R q at hq
    have hA := transport_jet i j m p
    change transport i ((A[[m]]) v) = scale • (A'[[m]]) (transport i v) at hA
    rw [hq, transport_jet, ← hq, hA, map_smul, smul_smul, scale_sq]

open private x from D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd
open private theta_omega_fixed from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private antisymmetrize from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
open private theta_neutralLift from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
open Lattice.ActualZhuCurrentRelations (single_weighted_grade)
private def rankOneOmega : Carrier R :=
  LatticeActualConformalState.omega R inverseGram

private theorem rankOneOmega_polynomial :
    rankOneOmega = neutralLift R ((1 / 4 : ℂ) • (x 0 * x 0)) := by
  letI : NeZero (R).rank := ⟨by decide⟩
  letI : Subsingleton (Fin (R).rank) := by change Subsingleton (Fin 1); infer_instance
  have singleSum (f : Fin (R).rank → Oscillator R) : (∑ j, f j) = f 0 :=
    Finset.sum_eq_single 0 (fun j _ hj => (hj (Subsingleton.elim j 0)).elim)
      (fun hn => (hn (Finset.mem_univ 0)).elim)
  norm_num [rankOneOmega, LatticeActualConformalState.omega,
    LatticeActualConformalState.conformalPolynomial, inverseGram, neutralLift_apply,
    x, singleSum, smul_smul]

private theorem rankOneOmega_fixed : theta R rankOneOmega = rankOneOmega :=
  theta_omega_fixed R inverseGram


private theorem rankOneInverse :
    inverseGram * gramComplex R = 1 ∧ gramComplex R * inverseGram = 1 := by
  have hG (i j : Fin (R).rank) : (gramComplex R) i j = 2 := by
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    change ((2 : ℤ) : ℂ) = 2
    norm_num
  constructor <;> ext i j <;> rw [Subsingleton.elim i 0, Subsingleton.elim j 0] <;>
    simp only [Matrix.mul_apply, sum_rank_one, hG, inverseGram, Matrix.one_apply] <;> norm_num

private def neutralOddAt (w : Carrier R) (h : ℕ) : Prop :=
  (∃ p : Oscillator R, w = neutralLift R p ∧
    IsWeightedHomogeneous (oscillatorWeight R) p h) ∧ theta R w = -w

private theorem rankOne_oddCurrent_at : neutralOddAt b₁ 1 := by
  refine ⟨⟨normalization • x 0, rankOne_odd_lift, ?_⟩, oddCurrent_parity⟩
  rw [MvPolynomial.smul_eq_C_mul]
  exact (isWeightedHomogeneous_X ℂ (oscillatorWeight R) ((0 : Fin (R).rank), 0)).C_mul _

private theorem neutralAt_grade {u : Carrier R} {h : ℕ}
    (hu : neutralOddAt u h) : u ∈ grade R (h : ℤ) := by
  obtain ⟨⟨p, rfl, hp⟩, _⟩ := hu
  simpa only [neutralLift_apply, chargeEnergy_zero, zero_add] using
    Lattice.ActualZhuCurrentRelations.single_weighted_grade R 0 p h hp

private theorem rankOne_mode (r : ℤ) (u : Carrier R) :
    mu R rankOneOmega r u = L (r-1) u := by
  simp only [mu, rankOneOmega, L, LatticeActualConformalWard.omega_ncoeff]

private theorem rankOne_mode_neutral {u : Carrier R}
    (hneutral : ∃ p, u = neutralLift R p) (r : ℤ) :
    ∃ p, mu R rankOneOmega r u = neutralLift R p := by
  obtain ⟨p, rfl⟩ := hneutral
  simp only [rankOneOmega_polynomial, neutralLift_apply]
  have he := LatticeSectorIntertwiner.charge_homogeneity R 0 0
    ((1 / 4 : ℂ) • (x 0 * x 0)) p r
  rw [zero_add] at he
  exact ⟨_, he⟩

private theorem rankOne_mode_odd {u : Carrier R} (hu : theta R u = -u) (r : ℤ) :
    theta R (mu R rankOneOmega r u) = -mu R rankOneOmega r u := by
  simp only [mu, stateField_theta, rankOneOmega_fixed, hu, map_neg]

private theorem rankOne_zero_mode {u : Carrier R} {h : ℕ} (hu : neutralOddAt u h) :
    mu R rankOneOmega 1 u = (h : ℂ) • u := by
  rw [rankOne_mode, show (1 : ℤ) - 1 = 0 by norm_num]
  exact_mod_cast (actualL0_eigen_iff_grade R inverseGram rankOneInverse.1 rankOneInverse.2
    (h : ℤ) u).mpr (neutralAt_grade hu)

private theorem neutralOddAt_L_neg {u : Carrier R} {h : ℕ}
    (hu : neutralOddAt u h) (m : ℕ) : neutralOddAt (L (-(m : ℤ)) u) (h + m) := by
  let r : ℤ := 1 - (m : ℤ)
  have hm : mu R rankOneOmega r u = L (-(m : ℤ)) u := by
    rw [rankOne_mode, show r - 1 = -(m : ℤ) by dsimp only [r]; omega]
  have hgrade := neutralAt_grade hu
  suffices hmode : neutralOddAt (mu R rankOneOmega r u) (h + m) from hm ▸ hmode
  obtain ⟨⟨p, hp, _⟩, hodd⟩ := hu
  obtain ⟨q, hq⟩ := rankOne_mode_neutral ⟨p, hp⟩ r
  refine ⟨⟨q, hq, ?_⟩, rankOne_mode_odd hodd r⟩
  have hw : rankOneOmega ∈ grade R 2 := by
    rw [rankOneOmega_polynomial, neutralLift_apply, MvPolynomial.smul_eq_C_mul]
    have hh := isWeightedHomogeneous_X ℂ (oscillatorWeight R) ((0 : Fin (R).rank), 0)
    simpa only [chargeEnergy_zero, zero_add, Nat.cast_ofNat, x] using
      Lattice.ActualZhuCurrentRelations.single_weighted_grade R 0 _ 2 ((hh.mul hh).C_mul _)
  have hg := actual_mode_grade R inverseGram rankOneInverse.1 rankOneInverse.2
    2 (h : ℤ) r rankOneOmega u hw hgrade
  change mu R rankOneOmega r u ∈ _ at hg
  rw [hq, neutralLift_apply, show (2 : ℤ) + h - r - 1 = (h + m : ℕ) by dsimp [r]; omega] at hg
  -- Read the weight of the coefficient at charge zero.
  exact rankOne_single_weight hg
where
  rankOne_single_weight {q : Oscillator R} {n : ℕ}
      (hq : Finsupp.single (0 : Charge R) q ∈ grade R (n : ℤ)) :
      IsWeightedHomogeneous (oscillatorWeight R) q n := by
    intro m hm
    by_contra hweight
    apply hm
    have he : energy R ((0 : Charge R), m) ≠ (n : ℤ) := by
      intro he
      apply hweight
      have he' : (oscillatorEnergy m : ℤ) = (n : ℤ) := by
        simpa only [energy, chargeEnergy_zero, zero_add] using he
      exact_mod_cast he'
    simpa only [Finsupp.single_eq_same] using (mem_grade_iff R (n : ℤ) _).mp hq _ he



open private sigma_lin from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityOddDirectionalSpectrum

private theorem substFrame_sigma (i : FrameIndex) (p : Oscillator R) :
    sigma ℒ (substFrame i p) = substFrame i (sigma R p) := by
  induction p using MvPolynomial.induction_on with
  | C z => simp [substFrame, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp, substFrame_X, sigma_smul, sigma_lin, sigma_X, map_neg, smul_neg]

private theorem transport_theta (i : FrameIndex) (p : Oscillator R) :
    theta ℒ (transport i (neutralLift R p)) = transport i (theta R (neutralLift R p)) := by
  rw [theta_neutralLift, transport_single, theta_neutralLift, transport_single, substFrame_sigma]

private def B (i : FrameIndex) : Carrier R →ₗ[ℂ] OddCarrier ℒ :=
  (1 / 2 : ℂ) • (antisymmetrize ℒ).comp (transport i)

private theorem B_val (i : FrameIndex) {w : Carrier R}
    (hn : ∃ p, w = neutralLift R p) (ho : theta R w = -w) :
    (B i w).val = transport i w := by
  obtain ⟨p, rfl⟩ := hn
  change (1 / 2 : ℂ) • (transport i (neutralLift R p) -
    theta ℒ (transport i (neutralLift R p))) = _
  rw [transport_theta, ho, map_neg]
  module

private theorem B_current (i : FrameIndex) : B i b₁ = frameCurrent i := by
  apply Subtype.ext
  change (B i b₁).val = (currentAlong (orthonormalBasis i)).val
  rw [B_val i ⟨_, rankOne_odd_lift⟩ oddCurrent_parity, rankOne_odd_lift,
    transport_single, currentAlong_val]
  simp only [x, map_smul, substFrame_X, smul_smul, norm_scale, one_smul, neutralLift_apply]

private theorem B_grade (i : FrameIndex) {w : Carrier R} {n : ℕ} (hw : neutralOddAt w n) :
    (B i w).val ∈ grade ℒ (n : ℤ) := by
  obtain ⟨⟨p, hp, hg⟩, ho⟩ := hw
  rw [B_val i ⟨p, hp⟩ ho, hp, transport_single, neutralLift_apply]
  have hs (j : Index R) :
      IsWeightedHomogeneous (oscillatorWeight ℒ) (scale • lin j.2 (orthonormalBasis i))
        (oscillatorWeight R j) := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact (lin_homogeneous j.2 (orthonormalBasis i)).C_mul _
  have ht : IsWeightedHomogeneous (oscillatorWeight ℒ) (substFrame i p) n := by
    refine hg.induction_on (motive := fun q _ =>
      IsWeightedHomogeneous (oscillatorWeight ℒ) (substFrame i q) n) ?_ ?_ ?_
    · rw [map_zero]
      exact isWeightedHomogeneous_zero ℂ _ _
    · intro a b _ _ ha hb
      rw [map_add]
      exact ha.add hb
    · intro e z he
      change IsWeightedHomogeneous _ (aeval (fun j : Index R =>
        scale • lin j.2 (orthonormalBasis i)) (monomial e z)) n
      rw [aeval_monomial, MvPolynomial.algebraMap_eq]
      have hh := IsWeightedHomogeneous.prod e.support
        (fun j : Index R => (scale • lin j.2 (orthonormalBasis i)) ^ e j)
        (fun j => e j • oscillatorWeight R j) (fun j _ => (hs j).pow (e j))
      have hh' : (∑ j ∈ e.support, e j • oscillatorWeight R j) = n := by
        simpa only [Finsupp.weight_apply, Finsupp.sum] using he
      simpa only [Finsupp.prod, hh'] using hh.C_mul z
  simpa only [chargeEnergy_zero, zero_add] using single_weighted_grade ℒ 0 _ n ht

private theorem B_pair_mode (i : FrameIndex) (j k : Index R) (q : ℤ)
    {a : Carrier R} {a' : FixedCarrier ℒ} {z : ℂ}
    (ha : a = neutralLift R (z • (X j * X k))) (hf : theta R a = a)
    (ha' : a'.val = neutralLift ℒ ((z * 2) • (lin j.2 (orthonormalBasis i) *
      lin k.2 (orthonormalBasis i)))) {w : Carrier R}
    (hn : ∃ p, w = neutralLift R p) (ho : theta R w = -w) :
    B i (mu R a q w) = oddMode ℒ a' q (B i w) := by
  have hmode : ∃ p, mu R a q w = neutralLift R p := by
    obtain ⟨p, rfl⟩ := hn
    rw [ha, neutralLift_apply, neutralLift_apply]
    have h := LatticeSectorIntertwiner.charge_homogeneity R 0 0
      (z • (X j * X k)) p q
    rw [zero_add] at h
    exact ⟨_, h⟩
  have hp : theta R (mu R a q w) = -mu R a q w := by
    simp only [mu, stateField_theta, hf, ho, map_neg]
  apply Subtype.ext
  rw [B_val i hmode hp, oddMode_val, B_val i hn ho, ha']
  obtain ⟨p, rfl⟩ := hn
  rw [ha, transport_single]
  simp only [map_smul, mu, VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply]
  change z • transport i (mu R (neutralLift R (X j * X k)) q (neutralLift R p)) =
    (z * 2) • mu ℒ (neutralLift ℒ (lin j.2 (orthonormalBasis i) *
      lin k.2 (orthonormalBasis i))) q (neutralLift ℒ (substFrame i p))
  rw [transport_pair_mode, smul_smul]

private theorem B_omega_mode (i : FrameIndex) {u : Carrier R} {n : ℕ}
    (hu : neutralOddAt u n) (r : ℤ) :
    B i (mu R rankOneOmega r u) = oddMode ℒ (leechRankOneOmega i) r (B i u) := by
  obtain ⟨⟨p, hp, _⟩, ho⟩ := hu
  exact B_pair_mode i (0,0) (0,0) r rankOneOmega_polynomial rankOneOmega_fixed
    (by change neutralLift ℒ _ = neutralLift ℒ _; norm_num) ⟨p, hp⟩ ho

private theorem B_abe_mode (i : FrameIndex) (r : ℤ) :
    B i (mu R A₁ r b₁) = oddMode ℒ (leechAbeState i) r (frameCurrent i) := by
  rw [← B_current]
  exact B_pair_mode i (0,2) (0,0) r rankOne_abe_lift
    (by rw [rankOne_abe_lift, theta_neutralLift]; simp [x, sigma_smul, map_mul, sigma_X])
    (by change neutralLift ℒ _ = neutralLift ℒ _; norm_num) ⟨_, rankOne_odd_lift⟩ oddCurrent_parity

private theorem project_diagonal (A : Module.End ℂ T₁) (eigen : FrameIndex → ℂ)
    (h : ∀ d x, A (frameOscillator d x) = eigen d • frameOscillator d x)
    (d : FrameIndex) (v : T₁) :
    directionProjector d (A v) = eigen d • directionProjector d v := by
  let Z : Module.End ℂ T₁ := (directionProjector d).comp A - eigen d • directionProjector d
  have hZ : Submodule.span ℂ (Set.range (fun p : FrameIndex × G₀ => frameOscillator p.1 p.2)) ≤
      LinearMap.ker Z := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k,x⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    change Z (frameOscillator k x) = 0
    simp only [Z, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      h, map_smul, projector_generator]
    split_ifs with hkd
    · subst k
      exact sub_self _
    · simp
  rw [firstOscillator_span] at hZ
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hZ (show v ∈ (⊤ : Submodule ℂ T₁) from trivial)))

private def omegaEigen (i d : FrameIndex) : ℂ := if d = i then 9 / 16 else 1 / 16
private def abeEigen (i d : FrameIndex) : ℂ := if d = i then 159 / 128 else 15 / 128

private def evalRankOne (i d : FrameIndex) (F : LawfulField ℒ leechUnit true) (v : T₁) :
    Carrier R →ₗ[ℂ] T₁ :=
  (directionProjector d).comp ((zhuTopEvaluation F v).comp (B i))

private theorem virasoro_step (i d : FrameIndex) (F : LawfulField ℒ leechUnit true)
    (x : G₀) (u : Carrier R) (n : ℕ) (hu : neutralOddAt u n) (r : ℤ) (hr : r ≤ 0) :
    let Z := evalRankOne i d F (frameOscillator d x)
    Z (mu R rankOneOmega r u) + Z (mu R rankOneOmega (r+1) u) =
      (if r = 0 then 0 else -(ι r * omegaEigen i d)) • Z u := by
  dsimp only
  let v := frameOscillator d x
  let a := leechRankOneOmega i
  let P := directionProjector d
  let Z := zhuTopEvaluation F v
  have he := zhuTopEvaluation_residue F a (B i u) v 2 (n : ℤ) ((1 : ℕ) : ℤ) r
    (leechRankOneOmega_grade i) (B_grade i hu) (by norm_num) (by omega)
  rw [oddResidue_nat a (B i u) 1 r] at he
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, one_smul, Nat.cast_zero, add_zero] at he
  change Z (oddMode ℒ a r (B i u) + oddMode ℒ a (r+1) (B i u)) = _ at he
  rw [map_add, ← B_omega_mode i hu r, ← B_omega_mode i hu (r+1)] at he
  have hin : zhuTopEvaluation F (fixedTopZero true a 2 (leechRankOneOmega_grade i) v) (B i u) =
      omegaEigen i d • Z (B i u) := by
    rw [show fixedTopZero true a 2 (leechRankOneOmega_grade i) v = omegaEigen i d • v
      from leechRankOneOmega_odd_zeroMode i d x]
    apply Subtype.ext
    simp only [Z, Submodule.coe_smul, zhuTopEvaluation_homogeneous F _ (n : ℤ) _ (B_grade i hu),
      map_smul]
  have hp : (1 : ℤ) = ((2 : ℕ) : ℤ) - 1 := by norm_num
  by_cases hz : r = 0
  · subst r
    simp only [add_zero, ite_eq_left hp, hin,
      StateFieldResidueReconstruction.epsilon, zpow_zero, one_smul] at he
    have hp := congrArg P he
    simp only [map_add, map_sub, map_smul] at hp
    rw [show P (fixedTopZero true a 2 (leechRankOneOmega_grade i) (Z (B i u))) =
      omegaEigen i d • P (Z (B i u)) from
        project_diagonal (Ω[i]) (omegaEigen i) (leechRankOneOmega_odd_zeroMode i) d _,
      sub_self] at hp
    simpa only [evalRankOne, LinearMap.comp_apply, ite_true, zero_smul] using hp
  · have hne : (1 : ℤ) + r ≠ ((2 : ℕ) : ℤ) - 1 := by omega
    rw [ite_eq_right hne, ite_eq_left hp, hin, smul_smul, zero_sub, ← neg_smul] at he
    have hp := congrArg P he
    simpa only [evalRankOne, Z, P, LinearMap.comp_apply, hz, if_false,
      map_add, map_smul] using hp

private theorem virasoro_diagonal (i d : FrameIndex) (F : LawfulField ℒ leechUnit true)
    (x : G₀) (u : Carrier R) (h : ℕ) (hu : neutralOddAt u h) :
    let Z := evalRankOne i d F (frameOscillator d x)
    Z (L (-1) u) = (-(h : ℂ)) • Z u ∧
    Z (L (-2) u) = ((h : ℂ) + omegaEigen i d) • Z u ∧
    Z (L (-3) u) = (-(h : ℂ) - 2 * omegaEigen i d) • Z u ∧
    Z (L (-4) u) = ((h : ℂ) + 3 * omegaEigen i d) • Z u := by
  dsimp only
  let Z := evalRankOne i d F (frameOscillator d x)
  change Z (L (-1) u) = (-(h : ℂ)) • Z u ∧
    Z (L (-2) u) = ((h : ℂ) + omegaEigen i d) • Z u ∧
    Z (L (-3) u) = (-(h : ℂ) - 2 * omegaEigen i d) • Z u ∧
    Z (L (-4) u) = ((h : ℂ) + 3 * omegaEigen i d) • Z u
  have h1 := virasoro_step i d F x u h hu 0 (by omega)
  have h2 := virasoro_step i d F x u h hu (-1) (by omega)
  have h3 := virasoro_step i d F x u h hu (-2) (by omega)
  have h4 := virasoro_step i d F x u h hu (-3) (by omega)
  dsimp only at h1 h2 h3 h4
  rw [show (0 : ℤ) + 1 = 1 by norm_num, rankOne_zero_mode hu] at h1
  change Z (mu R rankOneOmega 0 u) + Z ((h : ℂ) • u) = _ at h1
  change Z (mu R rankOneOmega (-1) u) + Z (mu R rankOneOmega (-1 + 1) u) = _ at h2
  change Z (mu R rankOneOmega (-2) u) + Z (mu R rankOneOmega (-2 + 1) u) = _ at h3
  change Z (mu R rankOneOmega (-3) u) + Z (mu R rankOneOmega (-3 + 1) u) = _ at h4
  have hε₁ : ι (-1) = -1 := by norm_num [StateFieldResidueReconstruction.epsilon]
  have hε₂ : ι (-2) = 1 := by norm_num [StateFieldResidueReconstruction.epsilon]
  have hε₃ : ι (-3) = -1 := by norm_num [StateFieldResidueReconstruction.epsilon]
  norm_num only [rankOne_mode, reduceIte, Int.reduceAdd, Int.reduceSub, Int.reduceNeg,
    Int.reduceNegSucc, Int.reduceEq, hε₁, hε₂, hε₃, zero_smul, neg_mul, one_mul,
    one_smul, neg_neg] at h1 h2 h3 h4
  have e1 := eq_sub_of_add_eq h1
  simp only [map_smul, zero_sub, ← neg_smul] at e1
  have e2 := eq_sub_of_add_eq h2
  rw [e1] at e2
  have e3 := eq_sub_of_add_eq h3
  rw [e2] at e3
  have e4 := eq_sub_of_add_eq h4
  rw [e3] at e4
  exact ⟨e1, e2.trans (by module), e3.trans (by module), e4.trans (by module)⟩

/-- At equal selected stress eigenvalues the actual eight-term Abe row is twice
that eigenvalue. Projection supplies the output eigenvalue at every descendant. -/
private theorem abe_star_evaluation (i d : FrameIndex) (F : LawfulField ℒ leechUnit true)
    (x : G₀) :
    evalRankOne i d F (frameOscillator d x) (Lattice.ActualZhuProduct.star R A₁ b₁) =
      (2 * omegaEigen i d) • evalRankOne i d F (frameOscillator d x) b₁ := by
  have hadj₁ : neutralOddAt (L (-1) b₁) 2 := neutralOddAt_L_neg rankOne_oddCurrent_at 1
  have hadj₂ : neutralOddAt (L (-1) (L (-1) b₁)) 3 := neutralOddAt_L_neg hadj₁ 1
  obtain ⟨e1, _, e3, e4⟩ := virasoro_diagonal i d F x b₁ 1 rankOne_oddCurrent_at
  obtain ⟨e11, e21, e31, _⟩ := virasoro_diagonal i d F x _ 2 hadj₁
  obtain ⟨_, e211, _, _⟩ := virasoro_diagonal i d F x _ 3 hadj₂
  rw [abe_zhu_identity]
  simp only [map_add, map_sub, map_smul]
  rw [e211, e31, e21, e11, e4, e3]
  simp only [e1]
  push_cast <;> module


private theorem abe_row_action (i d : FrameIndex) (F : LawfulField ℒ leechUnit true)
    (x : G₀) :
    evalRankOne i d F (frameOscillator d x) (Lattice.ActualZhuProduct.star R A₁ b₁) =
      abeEigen i d • evalRankOne i d F (frameOscillator d x) b₁ := by
  let a := leechAbeState i
  let b := frameCurrent i
  let v := frameOscillator d x
  have hrow : B i (Lattice.ActualZhuProduct.star R A₁ b₁) = oddZhuResidue a b 4 (-1) := by
    change _ = oddZhuResidue a b ((4 : ℕ) : ℤ) (-1)
    rw [Lattice.ActualZhuProduct.star_homogeneous R 4 A₁ b₁ abeState_grade,
      oddResidue_nat a b 4 (-1)]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro k _
    rw [show (-1 : ℤ) + (k : ℤ) = (k : ℤ) - 1 by omega]
    exact congrArg (fun w : OddCarrier ℒ => (Nat.choose 4 k : ℂ) • w) (B_abe_mode i _)
  simp only [evalRankOne, LinearMap.comp_apply]
  change directionProjector d (zhuTopEvaluation F v (B i (Lattice.ActualZhuProduct.star R A₁ b₁))) =
    abeEigen i d • directionProjector d (zhuTopEvaluation F v (B i b₁))
  rw [hrow, B_current]
  have hbal := (zhuTopEvaluation_balanced F a b v 4 1
    (leechAbeState_grade i) (frameCurrent_grade i)).1
  change zhuTopEvaluation F v (oddZhuResidue a b 4 (-1)) = _ at hbal
  rw [hbal]
  exact project_diagonal (fixedTopZero true a 4 (leechAbeState_grade i)) (abeEigen i)
    (leechAbeState_odd_zeroMode i) d _

/-- The two evaluations of the native Abe row have different eigenvalues
on each first-oscillator direction. -/
private theorem frameCurrent_odd_top_zero (F : LawfulField ℒ leechUnit true)
    (i d : FrameIndex) (x : G₀) :
    currentEvaluation F i (frameOscillator d x) = 0 := by
  obtain ⟨y, hy⟩ := current_preserves_direction F i d x
  have h := (abe_star_evaluation i d F x).symm.trans (abe_row_action i d F x)
  simp only [evalRankOne, LinearMap.comp_apply, B_current, ← currentEvaluation_eq,
    hy, projector_generator, if_pos rfl] at h
  have hz : ((2 * omegaEigen i d - abeEigen i d) : ℂ) • frameOscillator d y = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact h
  rw [hy]
  apply (smul_eq_zero.mp hz).resolve_left
  by_cases hd : d = i <;> norm_num [omegaEigen, abeEigen, hd]

/-- The integral source current has zero coefficient between actual odd tops. -/
theorem leech_odd_sameParity_frameCurrent_zero (F : LawfulField ℒ leechUnit true)
    (i : FrameIndex) (v : T₁) : F.coeff 0 (frameCurrent i) v.val = 0 := by
  have h : Submodule.span ℂ (Set.range (fun p : FrameIndex × G₀ => frameOscillator p.1 p.2)) ≤
      LinearMap.ker (currentEvaluation F i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨d,x⟩, rfl⟩
    exact LinearMap.mem_ker.mpr (frameCurrent_odd_top_zero F i d x)
  rw [firstOscillator_span] at h
  have hv := LinearMap.mem_ker.mp (h (show v ∈ (⊤ : Submodule ℂ T₁) from trivial))
  exact congrArg (fun w : T₁ => w.val) hv

/-- The same coefficient in the original lattice-coordinate current basis. -/
theorem leech_odd_sameParity_current_zero (F : LawfulField ℒ leechUnit true)
    (k : Fin (ℒ).rank) (v : T₁) : F.coeff 0 (oddCurrent ℒ k) v.val = 0 := by
  classical
  let b := orthonormalBasis
  let w := standardBasis ℒ k
  have hw : ∑ d, b.equivFun w d • b d = w := by
    simpa only [Module.Basis.equivFun_symm_apply] using b.equivFun.symm_apply_apply w
  have hk : currentAlong w = oddCurrent ℒ k := by
    change ∑ j, w j • oddCurrent ℒ j = oddCurrent ℒ k
    simp [w, standardBasis, Pi.single_apply]
  rw [← hk, ← hw]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    show ∀ i, currentAlong (b i) = frameCurrent i from fun _ => rfl,
    leech_odd_sameParity_frameCurrent_zero, smul_zero, Finset.sum_const_zero]

/-- Every integral lawful field with actual Leech odd source and odd twisted
input and output vanishes at every integer label. -/
theorem leech_odd_sameParity_coeff_eq_zero (F : LawfulField ℒ leechUnit true) :
    F.coeff = 0 := by
  apply coeff_eq_zero_of_current_zero (by rw [leech_spec.1]; decide) leech_spec.2.2.1 F
  exact leech_odd_sameParity_current_zero F

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity.OddDirectional
