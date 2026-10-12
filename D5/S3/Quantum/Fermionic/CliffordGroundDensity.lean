/- GID: D5/S3/Quantum/Fermionic/CliffordGroundDensity
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/CliffordGroundDensity
   mirror-E: none(waiver:general-Clifford-ground-density)
   anchors: []
   utility: none
   digest: Paired Clifford bilinears have a physical trace-one ground projector. -/

/-
paired_clifford_ground:
  proof_shape: content
  escape_witness: construct the commuting bilinears and their independent sign
    reversals, normalize the joint minus sector, and bound all density energies
    by positivity of the complementary plus projections.
admission_basis: escape-witness
Same-delivery inlined content: JointSignProjectors, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
    statement_id: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
  GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.meanEnergy
    statement_id: sha256:9968a03e56960da489176141fea72cbed63e67cc32e2fe1378c92e3fed11906b
  GID: D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
    statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
computational_content.kind: none; arbitrary finite Clifford representations.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15194.
-/

import D5.S3.Quantum.Fermionic.JointSignProjectors
import D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
import D5.S3.Weil.ZetaLinear.RankTrace

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Fermionic.JointSignProjectors
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
noncomputable section

namespace D5.S3.Quantum.Fermionic.CliffordGroundDensity

theorem paired_clifford_ground {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (hdim : Fintype.card Ω = 2 ^ Fintype.card κ)
    (eta : κ ⊕ κ → Matrix Ω Ω ℂ)
    (hherm : ∀ p, (eta p).IsHermitian)
    (hcar : ∀ p q, eta p * eta q + eta q * eta p =
      if p = q then (2 : ℂ) • 1 else 0)
    (T : Matrix Ω Ω ℂ)
    (hpar : ∀ p, T * eta p = -(eta p * T)) :
    let Q := ∑ k, Complex.I • (eta (Sum.inl k) * eta (Sum.inr k))
    ∃ rho : DensityState Ω,
      IsStarProjection (CStarMatrix.ofMatrix.symm rho.val) ∧
      Commute rho.val (CStarMatrix.ofMatrix T) ∧
      Q * CStarMatrix.ofMatrix.symm rho.val =
        (-(Fintype.card κ : ℂ)) • CStarMatrix.ofMatrix.symm rho.val ∧
      ∀ omega : DensityState Ω,
        -(Fintype.card κ : ℝ) ≤ meanEnergy (CStarMatrix.ofMatrix Q) omega := by
  classical
  dsimp only
  let B (k : κ) := Complex.I • (eta (Sum.inl k) * eta (Sum.inr k))
  have hs (p : κ ⊕ κ) : eta p * eta p = 1 := by
    have h := hcar p p
    simp only [ite_true, two_smul] at h
    ext i j
    have hh := congrArg (fun A : Matrix Ω Ω ℂ => A i j) h
    simp only [Matrix.add_apply] at hh
    linear_combination (1/2 : ℂ) * hh
  have hac (p q : κ ⊕ κ) (hne : p ≠ q) : eta p * eta q = -(eta q * eta p) := by
    have h := hcar p q
    rw [if_neg hne] at h
    exact eq_neg_of_add_eq_zero_left h
  have hB (k : κ) : (B k).IsHermitian ∧ B k * B k = 1 := by
    have ha := hac (Sum.inl k) (Sum.inr k) (by simp)
    constructor
    · change (Complex.I • (eta (Sum.inl k) * eta (Sum.inr k)))ᴴ = _
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        (hherm _).eq, Complex.star_def, Complex.conj_I]
      rw [neg_smul, show eta (Sum.inr k) * eta (Sum.inl k) =
        -(eta (Sum.inl k) * eta (Sum.inr k)) by rw [ha,neg_neg], smul_neg,neg_neg]
    · change (Complex.I • (eta (Sum.inl k) * eta (Sum.inr k))) *
        (Complex.I • (eta (Sum.inl k) * eta (Sum.inr k))) = 1
      rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I,neg_one_smul]
      have hh : eta (Sum.inl k) * eta (Sum.inr k) *
          (eta (Sum.inl k) * eta (Sum.inr k)) = -1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (eta (Sum.inr k)),
          show eta (Sum.inr k) * eta (Sum.inl k) =
            -(eta (Sum.inl k) * eta (Sum.inr k)) by rw [ha,neg_neg],
          Matrix.neg_mul,Matrix.mul_neg,← Matrix.mul_assoc,
          ← Matrix.mul_assoc,hs,Matrix.one_mul,hs]
      rw [hh,neg_neg]
  have hfix (p : κ ⊕ κ) (k : κ)
      (hl : p ≠ Sum.inl k) (hr : p ≠ Sum.inr k) : Commute (eta p) (B k) := by
    rw [commute_iff_eq]
    change eta p * (Complex.I • (eta (Sum.inl k) * eta (Sum.inr k))) = _
    rw [Matrix.mul_smul,Matrix.smul_mul,← Matrix.mul_assoc,hac p (Sum.inl k) hl,
      Matrix.neg_mul,Matrix.mul_assoc,hac p (Sum.inr k) hr,Matrix.mul_neg,neg_neg]
    simp only [Matrix.mul_assoc]
  have hBB (i j : κ) : Commute (B i) (B j) := by
    by_cases hij : i = j
    · subst j; exact Commute.refl _
    · exact ((hfix (Sum.inl i) j (by simpa using hij) (by simp)).mul_left
        (hfix (Sum.inr i) j (by simp) (by simpa using hij))).smul_left Complex.I
  have hflip (k : κ) : eta (Sum.inl k) * B k = -(B k * eta (Sum.inl k)) := by
    dsimp only [B]
    rw [Matrix.mul_smul,Matrix.smul_mul,← Matrix.mul_assoc,hs,Matrix.one_mul]
    have hh : eta (Sum.inl k) * eta (Sum.inr k) * eta (Sum.inl k) =
        -eta (Sum.inr k) := by
      rw [Matrix.mul_assoc,hac (Sum.inr k) (Sum.inl k) (by simp),
        Matrix.mul_neg,← Matrix.mul_assoc,hs,Matrix.one_mul]
    rw [hh,smul_neg,neg_neg]
  have hTB (k : κ) : Commute T (B k) := by
    rw [commute_iff_eq]
    dsimp only [B]
    rw [Matrix.mul_smul,Matrix.smul_mul,← Matrix.mul_assoc,hpar,
      Matrix.neg_mul,Matrix.mul_assoc,hpar,Matrix.mul_neg,neg_neg]
    simp only [Matrix.mul_assoc]
  obtain ⟨P,hP,htr,hminus,hcomm⟩ := joint_sign_projection B (fun k => eta (Sum.inl k))
    hB hBB (fun k => hs _) hflip (fun i j hij => hfix _ _ (by simpa using hij) (by simp))
  have htr' : Matrix.trace P = 1 := by
    rw [hdim,Nat.cast_pow,Nat.cast_ofNat,div_self] at htr
    · exact htr
    · exact pow_ne_zero _ (by norm_num)
  let rho : DensityState Ω := ⟨CStarMatrix.ofMatrix P,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hP.nonneg, htr'⟩
  refine ⟨rho,hP,?_,?_,?_⟩
  · exact (hcomm T hTB).symm.map CStarMatrix.ofMatrixStarAlgEquiv
  · change (∑ k, B k) * P = (-(Fintype.card κ : ℂ)) • P
    rw [Matrix.sum_mul]
    simp only [hminus,Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,smul_neg,neg_smul]
    rfl
  · intro omega
    have hplus (k : κ) : (1 + B k).PosSemidef := by
      have he : IsStarProjection ((1/2 : ℂ) • (1 + B k)) := by
        constructor
        · change ((1/2 : ℂ) • (1 + B k)) * ((1/2 : ℂ) • (1 + B k)) = _
          rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
          have hh : (1+B k)*(1+B k) = (2 : ℂ) • (1+B k) := by
            rw [two_smul]
            noncomm_ring [(hB k).2]
          rw [hh,smul_smul]
          norm_num
        · change (((1/2 : ℂ) • (1 + B k)))ᴴ = _
          simp [Matrix.conjTranspose_add,(hB k).1.eq]
      have hn : (0 : Matrix Ω Ω ℂ) ≤ (1/2 : ℝ) • (1+B k) := by
        have heq : (1/2 : ℝ) • (1+B k) = (1/2 : ℂ) • (1+B k) := by
          ext i j
          simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
          norm_num
        rw [heq]
        exact he.nonneg
      have hn' := smul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hn
      simp only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] at hn'
      exact Matrix.nonneg_iff_posSemidef.mp hn'
    have hp : (CStarMatrix.ofMatrix.symm omega.val).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm omega.property.1)
    have he (k : κ) : -(1:ℝ) ≤
        (Matrix.trace (B k * CStarMatrix.ofMatrix.symm omega.val)).re := by
      have hh := RHLinalg.trace_mul_nonneg_of_posSemidef (hplus k) hp
      have htrw : Matrix.trace (CStarMatrix.ofMatrix.symm omega.val) = 1 := omega.property.2
      rw [Matrix.add_mul,Matrix.one_mul,Matrix.trace_add,htrw] at hh
      change 0 ≤ 1 + (Matrix.trace (B k * CStarMatrix.ofMatrix.symm omega.val)).re at hh
      linarith
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => he k)
    change -(Fintype.card κ : ℝ) ≤
      (Matrix.trace ((∑ k, B k) * CStarMatrix.ofMatrix.symm omega.val)).re
    rw [Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum]
    simpa using hh

end D5.S3.Quantum.Fermionic.CliffordGroundDensity
