/- GID: D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity
   generality: I
   mirror-B: D5/B/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rényi-α strong subadditivity for physical bosonic Gaussian covariances. -/

import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
import D5.S3.Resource.LogDet.LogDetInformationSubmodularity
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
import D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation

/-! Settlement of the bosonic Gaussian Rényi strong-subadditivity line. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Resource.LogDet
open MeasureTheory D5.S3.Quantum.Analysis.BosonicRenyiStieltjes

namespace D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity

/-! The covariance and entropy interface for the Gaussian Rényi settlement. -/

def symplecticForm (n : ℕ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  let e := ((Equiv.prodComm (Fin n) (Fin 2)).trans
    (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin n)))).trans
      (Equiv.boolProdEquivSum (Fin n))
  (-Matrix.J (Fin n) ℝ).submatrix e e

def physicalOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) : Prop :=
  V.IsSymm ∧ (V.map Complex.ofReal + Complex.I • ω.map Complex.ofReal).PosSemidef

def physicalCovariance {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : Prop :=
  D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
    (V.submatrix ((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)
      ((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm))

def reducedCovariance {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (X : Finset (Fin n)) :
      Matrix {p : Fin n × Fin 2 // p.1 ∈ X} {p : Fin n × Fin 2 // p.1 ∈ X} ℝ :=
  V.submatrix (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)
    (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)

def symplecticOperator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  CFC.sqrt (V.map Complex.ofReal) * (Complex.I • ω.map Complex.ofReal) *
    CFC.sqrt (V.map Complex.ofReal)

def gaussianRenyiEntropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (V ω : Matrix ι ι ℝ) : ℝ :=
  if h : (symplecticOperator V ω).IsHermitian then
    (1 / 2 : ℝ) * ∑ i, D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiFunction α
      |h.eigenvalues i|
  else 0

def claim : Prop :=
  ∀ (n : ℕ) (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
    physicalCovariance V → ∀ A B C : Finset (Fin n),
      Disjoint A B → Disjoint A C → Disjoint B C → ∀ α : ℝ,
        0 < α → α ≤ 2 → α ≠ 1 →
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B))
              (reducedCovariance (symplecticForm n) (A ∪ B)) +
            gaussianRenyiEntropy α (reducedCovariance V (B ∪ C))
              (reducedCovariance (symplecticForm n) (B ∪ C)) ≥
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B ∪ C))
              (reducedCovariance (symplecticForm n) (A ∪ B ∪ C)) +
            gaussianRenyiEntropy α (reducedCovariance V B)
              (reducedCovariance (symplecticForm n) B)

private lemma index_bridge (n : ℕ) :
    let e : Fin (2 * n) ≃ Fin n × Fin 2 :=
      (finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm
    let f := ((Equiv.prodComm (Fin n) (Fin 2)).trans
      (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin n)))).trans
        (Equiv.boolProdEquivSum (Fin n))
    ∀ i, f (e i) = if i.val % 2 = 0 then
      Sum.inl ((Fin.cast (Nat.mul_comm 2 n) i).divNat)
      else Sum.inr ((Fin.cast (Nat.mul_comm 2 n) i).divNat) := by
  intro e f i
  dsimp [e, f, Equiv.boolProdEquivSum, finTwoEquiv, finProdFinEquiv, finCongr]
  split_ifs with h h0 h0
  · exfalso
    change ((Fin.cast (Nat.mul_comm 2 n) i).modNat == (1 : Fin 2)) = true at h
    rw [beq_iff_eq] at h
    have hv := congrArg Fin.val h
    change i.val % 2 = 1 at hv
    omega
  · rfl
  · rfl
  · exfalso
    change ¬((Fin.cast (Nat.mul_comm 2 n) i).modNat == (1 : Fin 2)) = true at h
    rw [beq_iff_eq, Fin.ext_iff] at h
    change ¬i.val % 2 = 1 at h
    have hm := Nat.mod_lt i.val (by decide : 0 < 2)
    omega

private lemma physicalCovariance_iff {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) :
    physicalOn V (symplecticForm n) ↔ physicalCovariance V := by
  let e : Fin (2 * n) ≃ Fin n × Fin 2 :=
    (finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm
  have hform : ((symplecticForm n).map Complex.ofReal).submatrix e e =
      (-Matrix.J (Fin n) ℂ).submatrix
        (fun i : Fin (2 * n) => if i.val % 2 = 0 then
          Sum.inl ((Fin.cast (Nat.mul_comm 2 n) i).divNat)
          else Sum.inr ((Fin.cast (Nat.mul_comm 2 n) i).divNat))
        (fun i : Fin (2 * n) => if i.val % 2 = 0 then
          Sum.inl ((Fin.cast (Nat.mul_comm 2 n) i).divNat)
          else Sum.inr ((Fin.cast (Nat.mul_comm 2 n) i).divNat)) := by
    dsimp only [symplecticForm]
    rw [Matrix.submatrix_map, Matrix.submatrix_submatrix]
    rw [← Matrix.submatrix_map]
    have hm : (-Matrix.J (Fin n) ℝ).map Complex.ofReal = -Matrix.J (Fin n) ℂ := by
      change Complex.ofRealHom.mapMatrix (-Matrix.J (Fin n) ℝ) = -Matrix.J (Fin n) ℂ
      rw [map_neg]
      exact congrArg Neg.neg (Matrix.map_J (Fin n) Complex.ofRealHom)
    rw [hm]
    congr 1 <;> funext i <;> exact index_bridge n i
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨hs.submatrix e, ?_⟩
    have h := hp.submatrix e
    change ((V.map Complex.ofReal).submatrix e e +
      Complex.I • ((symplecticForm n).map Complex.ofReal).submatrix e e).PosSemidef at h
    rw [hform] at h
    exact h
  · rintro ⟨hs, hp⟩
    change (V.submatrix e e).IsSymm at hs
    have hs' := hs.submatrix e.symm
    have hp' : ((V.map Complex.ofReal).submatrix e e +
      Complex.I • ((symplecticForm n).map Complex.ofReal).submatrix e e).PosSemidef := by
      rw [hform]
      exact hp
    have h := hp'.submatrix e.symm
    constructor
    · simp only [Matrix.submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply] at hs'
      exact hs'
    · change (((V.map Complex.ofReal).submatrix e e).submatrix e.symm e.symm +
        Complex.I • (((symplecticForm n).map Complex.ofReal).submatrix e e).submatrix
          e.symm e.symm).PosSemidef at h
      simp only [Matrix.submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply] at h
      exact h

private lemma reduced_square {n : ℕ} (X : Finset (Fin n)) :
    reducedCovariance (symplecticForm n) X * reducedCovariance (symplecticForm n) X = -1 := by
  let e := ((Equiv.prodComm ↥X (Fin 2)).trans
    (Equiv.prodCongr finTwoEquiv (Equiv.refl ↥X))).trans
      (Equiv.boolProdEquivSum ↥X)
  let f := (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun i => i ∈ X)
    (β := Fin 2)).symm
  apply Matrix.submatrix_injective f.surjective f.surjective
  dsimp only
  rw [Matrix.submatrix_mul _ _ f f f f.bijective]
  have heq :
      (reducedCovariance
        (symplecticForm n) X).submatrix f f = (-Matrix.J ↥X ℝ).submatrix e e := by
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases a <;> fin_cases b
    · rfl
    · change -(-(1 : Matrix (Fin n) (Fin n) ℝ) i.val j.val) =
        -(-(1 : Matrix ↥X ↥X ℝ) i j)
      simp only [Matrix.one_apply, Subtype.ext_iff]
    · change -(1 : Matrix (Fin n) (Fin n) ℝ) i.val j.val =
        -(1 : Matrix ↥X ↥X ℝ) i j
      simp only [Matrix.one_apply, Subtype.ext_iff]
    · rfl
  rw [heq, Matrix.submatrix_mul_equiv, neg_mul_neg, Matrix.J_squared]
  change -((1 : Matrix (↥X ⊕ ↥X) (↥X ⊕ ↥X) ℝ).submatrix e e) =
    -((1 : Matrix {p : Fin n × Fin 2 // p.1 ∈ X}
      {p : Fin n × Fin 2 // p.1 ∈ X} ℝ).submatrix f f)
  rw [Matrix.submatrix_one_equiv, Matrix.submatrix_one_equiv]

private lemma reduced_card {n : ℕ} (X : Finset (Fin n)) :
    Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X} = 2 * X.card := by
  rw [Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd
    (p := fun i => i ∈ X) (β := Fin 2)), Fintype.card_prod]
  simp [Nat.mul_comm]

private lemma physical_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω) : ωᵀ = -ω := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => (M i j).im) hV.2.isHermitian.eq
  have hh : -ω j i = ω i j := by
    simpa [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.mul_im] using h
  exact neg_eq_iff_eq_neg.mp hh

private lemma uncertainty_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω)
    (hω : IsUnit (ω.map Complex.ofReal)) : (V.map Complex.ofReal).PosDef := by
  let P := V.map Complex.ofReal + Complex.I • ω.map Complex.ofReal
  let Q := V.map Complex.ofReal - Complex.I • ω.map Complex.ofReal
  have hP : P.PosSemidef := hV.2
  have hQ : Q.PosSemidef := by
    have heq : Pᵀ = Q := by
      dsimp only [P, Q]
      rw [Matrix.transpose_add, Matrix.transpose_smul, ← Matrix.transpose_map,
        ← Matrix.transpose_map, hV.1, physical_skew V ω hV,
        Matrix.map_neg _ Complex.ofReal_neg, smul_neg, sub_eq_add_neg]
    exact heq ▸ hP.transpose
  have hsum : P + Q = (2 : ℝ) • V.map Complex.ofReal := by
    dsimp only [P, Q]
    rw [two_smul]
    abel
  have hps : (V.map Complex.ofReal).PosSemidef := by
    have h := (hP.add hQ).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [hsum, smul_smul] at h
    norm_num at h
    exact h
  apply hps.posDef_iff_mulVec_injective.mpr
  intro u v huv
  let z := u - v
  have hz : V.map Complex.ofReal *ᵥ z = 0 := by
    rw [mulVec_sub, huv, sub_self]
  suffices z = 0 by exact sub_eq_zero.mp this
  have heq : star z ⬝ᵥ P *ᵥ z + star z ⬝ᵥ Q *ᵥ z = 0 := by
    rw [← dotProduct_add, ← add_mulVec, hsum, smul_mulVec, hz, smul_zero, dotProduct_zero]
  have hzero : star z ⬝ᵥ P *ᵥ z = 0 :=
    le_antisymm ((le_of_eq (eq_neg_of_add_eq_zero_left heq)).trans
      (neg_nonpos.mpr (hQ.dotProduct_mulVec_nonneg z))) (hP.dotProduct_mulVec_nonneg z)
  have hpz := hP.dotProduct_mulVec_zero_iff.mp hzero
  have hoz : ω.map Complex.ofReal *ᵥ z = 0 := by
    have h : Complex.I • (ω.map Complex.ofReal *ᵥ z) = 0 := by
      simpa only [P, add_mulVec, hz, zero_add, smul_mulVec] using hpz
    exact (smul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  exact (Matrix.mulVec_injective_iff_isUnit.mpr hω) (hoz.trans (mulVec_zero _).symm)

private lemma canonical_square (n : ℕ) : symplecticForm n * symplecticForm n = -1 := by
  dsimp only [symplecticForm]
  rw [Matrix.submatrix_mul_equiv, neg_mul_neg, Matrix.J_squared]
  change -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ).submatrix _ _) = -1
  rw [Matrix.submatrix_one_equiv]

private lemma physical_posDef {n : ℕ}
    (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hV : physicalCovariance V) : (V.map Complex.ofReal).PosDef := by
  apply uncertainty_posDef V (symplecticForm n) ((physicalCovariance_iff V).mpr hV)
  have h : (symplecticForm n).map Complex.ofReal *
      (symplecticForm n).map Complex.ofReal = -1 := by
    change Complex.ofRealHom.mapMatrix (symplecticForm n) *
      Complex.ofRealHom.mapMatrix (symplecticForm n) = -1
    rw [← map_mul, canonical_square, map_neg, map_one]
  exact IsUnit.of_mul_eq_one (-(symplecticForm n).map Complex.ofReal)
    (by rw [mul_neg, h, neg_neg])

private lemma reduced_physical {n : ℕ}
    (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hV : physicalCovariance V)
    (X : Finset (Fin n)) :
    physicalOn (reducedCovariance V X) (reducedCovariance (symplecticForm n) X) := by
  rcases (physicalCovariance_iff V).mpr hV with ⟨hs, hp⟩
  constructor
  · exact hs.submatrix (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)
  · let f : {q : Fin n × Fin 2 // q.1 ∈ X} → Fin n × Fin 2 := fun p => p.1
    have heq : ((V.map Complex.ofReal) + Complex.I • (symplecticForm n).map
        Complex.ofReal).submatrix f f =
        (V.submatrix f f).map Complex.ofReal +
          Complex.I • ((symplecticForm n).submatrix f f).map Complex.ofReal := by
      simp only [Matrix.submatrix_add, Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply,
        Matrix.submatrix_map]
    change (((V.submatrix f f).map Complex.ofReal) +
      Complex.I • ((symplecticForm n).submatrix f f).map Complex.ofReal).PosSemidef
    rw [← heq]
    exact hp.submatrix f

private lemma symplecticOperator_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω)
    (hpos : (V.map Complex.ofReal).PosDef) : (symplecticOperator V ω).IsHermitian := by
  have hJ : (Complex.I • ω.map Complex.ofReal).IsHermitian := by
    simpa only [add_sub_cancel_left] using hV.2.isHermitian.sub hpos.isHermitian
  have hS := (CFC.sqrt_nonneg (V.map Complex.ofReal)).posSemidef.isHermitian.eq
  change (CFC.sqrt (V.map Complex.ofReal) * (Complex.I • ω.map Complex.ofReal) *
    CFC.sqrt (V.map Complex.ofReal)).IsHermitian
  simpa only [hS] using
    isHermitian_conjTranspose_mul_mul (CFC.sqrt (V.map Complex.ofReal)) hJ

private lemma symplectic_spectrum_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hω : ω * ω = -1)
    (hH : (symplecticOperator V ω).IsHermitian) :
    ∀ i, 1 ≤ |hH.eigenvalues i| := by
  let S := CFC.sqrt (V.map Complex.ofReal)
  let J := Complex.I • ω.map Complex.ofReal
  let M := symplecticOperator V ω
  have hSS : S * S = V.map Complex.ofReal := CFC.sqrt_mul_sqrt_self _ hpos.posSemidef.nonneg
  have hS : Sᴴ = S := (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  have hJ : Jᴴ = J := by
    have h := hV.2.isHermitian.sub hpos.isHermitian
    simpa only [add_sub_cancel_left] using h.eq
  have hωC : ω.map Complex.ofReal * ω.map Complex.ofReal = -1 := by
    change Complex.ofRealHom.mapMatrix ω * Complex.ofRealHom.mapMatrix ω = -1
    rw [← map_mul, hω, map_neg, map_one]
  have hJJ : J * J = 1 := by
    dsimp only [J]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, hωC]
    simp
  have hunitS : IsUnit S := (CFC.isUnit_sqrt_iff _ hpos.posSemidef.nonneg).mpr hpos.isUnit
  have hunitM : IsUnit M := (hunitS.mul (IsUnit.of_mul_eq_one J hJJ)).mul hunitS
  have hminus : (V.map Complex.ofReal - J).PosSemidef := by
    have heq : (V.map Complex.ofReal + J)ᵀ = V.map Complex.ofReal - J := by
      dsimp only [J]
      rw [Matrix.transpose_add, Matrix.transpose_smul, ← Matrix.transpose_map,
        ← Matrix.transpose_map, hV.1, physical_skew V ω hV,
        Matrix.map_neg _ Complex.ofReal_neg, smul_neg, sub_eq_add_neg]
    exact heq ▸ hV.2.transpose
  have hp : (M * M + M).PosSemidef := by
    have h := hV.2.conjTranspose_mul_mul_same (J * S)
    have heq : (J * S)ᴴ * (V.map Complex.ofReal + J) * (J * S) = M * M + M := by
      rw [conjTranspose_mul, hS, hJ, ← hSS]
      change S * J * (S * S + J) * (J * S) = (S * J * S) * (S * J * S) + S * J * S
      noncomm_ring [hJJ]
    exact heq ▸ h
  have hm : (M * M - M).PosSemidef := by
    have h := hminus.conjTranspose_mul_mul_same (J * S)
    have heq : (J * S)ᴴ * (V.map Complex.ofReal - J) * (J * S) = M * M - M := by
      rw [conjTranspose_mul, hS, hJ, ← hSS]
      change S * J * (S * S - J) * (J * S) = (S * J * S) * (S * J * S) - S * J * S
      noncomm_ring [hJJ]
    exact heq ▸ h
  intro i
  let z : ι → ℂ := ⇑(hH.eigenvectorBasis i)
  have hz1 : star z ⬝ᵥ z = (1 : ℂ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hH.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have he : M *ᵥ z = hH.eigenvalues i • z := hH.mulVec_eigenvectorBasis i
  have hne : hH.eigenvalues i ≠ 0 := by
    intro hzero
    have hmz : M *ᵥ z = 0 := by simpa (config := { congrConsts := false }) only
      [hzero, zero_smul] using he
    have hz : z = 0 := (Matrix.mulVec_injective_iff_isUnit.mpr hunitM)
      (hmz.trans (mulVec_zero M).symm)
    simp only
      [hz, star_zero, dotProduct_zero, zero_ne_one] at hz1
  have hpv : 0 ≤ (star z ⬝ᵥ (M * M + M) *ᵥ z).re := hp.re_dotProduct_nonneg z
  have hmv : 0 ≤ (star z ⬝ᵥ (M * M - M) *ᵥ z).re := hm.re_dotProduct_nonneg z
  have hpq : (star z ⬝ᵥ (M * M + M) *ᵥ z).re = hH.eigenvalues i ^ 2 + hH.eigenvalues i := by
    simp (config := { congrConsts := false }) only
      [add_mulVec, ← mulVec_mulVec, he, mulVec_smul, dotProduct_add,
      dotProduct_smul, hz1, mul_one, Complex.real_smul, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hmq : (star z ⬝ᵥ (M * M - M) *ᵥ z).re = hH.eigenvalues i ^ 2 - hH.eigenvalues i := by
    simp (config := { congrConsts := false }) only
      [sub_mulVec, ← mulVec_mulVec, he, mulVec_smul, dotProduct_sub,
      dotProduct_smul, hz1, mul_one, Complex.real_smul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [hpq] at hpv
  rw [hmq] at hmv
  rcases lt_or_gt_of_ne hne with hn | hn
  · rw [abs_of_neg hn]
    nlinarith
  · rw [abs_of_pos hn]
    nlinarith

private lemma shifted_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω)
    (hpos : (V.map Complex.ofReal).PosDef) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ((V.map Complex.ofReal) + (x : ℂ) • (Complex.I • ω.map Complex.ofReal)).PosDef := by
  have hp := (hpos.smul (sub_pos.mpr hx1)).add_posSemidef
    (hV.2.smul hx0)
  convert hp using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

private lemma principal_block_identity {ι : Type*}
    (V ω : Matrix ι ι ℝ) (X : Finset ι) (x : ℝ) :
    ((V.map Complex.ofReal) + (x : ℂ) • (Complex.I • ω.map Complex.ofReal)).submatrix
        (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1) =
      ((V.submatrix (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1)).map
          Complex.ofReal) +
        (x : ℂ) • (Complex.I •
          (ω.submatrix (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1)).map
            Complex.ofReal) := by
  simp only [Matrix.submatrix_add, Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply,
    Matrix.submatrix_map]

private lemma determinant_spectral_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hω : ω * ω = -1)
    (hH : (symplecticOperator V ω).IsHermitian) :
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      Real.log (((V.map Complex.ofReal) + (x : ℂ) •
        (Complex.I • ω.map Complex.ofReal)).det.re) =
        (1 / 2 : ℝ) * ∑ i, Real.log (hH.eigenvalues i ^ 2 - x ^ 2) := by
  let S := CFC.sqrt (V.map Complex.ofReal)
  let J := Complex.I • ω.map Complex.ofReal
  let H := fun x : ℝ => V.map Complex.ofReal + (x : ℂ) • J
  have hSS : S * S = V.map Complex.ofReal := CFC.sqrt_mul_sqrt_self _ hpos.posSemidef.nonneg
  have hωC : ω.map Complex.ofReal * ω.map Complex.ofReal = -1 := by
    change Complex.ofRealHom.mapMatrix ω * Complex.ofRealHom.mapMatrix ω = -1
    rw [← map_mul, hω, map_neg, map_one]
  have hJJ : J * J = 1 := by
    dsimp only [J]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, hωC]
    simp
  have hc : (symplecticOperator V ω).charpoly = (J * V.map Complex.ofReal).charpoly := by
    change (S * J * S).charpoly = _
    calc
      _ = (S * (J * S)).charpoly := by rw [mul_assoc]
      _ = (J * S * S).charpoly := Matrix.charpoly_mul_comm S (J * S)
      _ = _ := by rw [mul_assoc, hSS]
  have hscalar (t : ℝ) : Matrix.scalar ι (t : ℂ) = (t : ℂ) • (1 : Matrix ι ι ℂ) := by
    exact (Matrix.smul_one_eq_diagonal _).symm
  have hd (t : ℝ) : (∏ i, ((t - hH.eigenvalues i : ℝ) : ℂ)) =
      (-J).det * (H (-t)).det := by
    rw [← D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.det_pencil hH t]
    change ((t : ℂ) • (1 : Matrix ι ι ℂ) - symplecticOperator V ω).det = _
    rw [← hscalar, ← Matrix.eval_charpoly, hc, Matrix.eval_charpoly, hscalar]
    have heq : (t : ℂ) • (1 : Matrix ι ι ℂ) - J * V.map Complex.ofReal = -J * H (-t) := by
      dsimp only [H]
      simp only [Complex.ofReal_neg, neg_smul, Matrix.neg_mul, Matrix.mul_add,
        Matrix.mul_smul, Matrix.mul_neg, smul_neg, neg_neg, hJJ]
      abel
    rw [heq, Matrix.det_mul]
  have hdetJ : (-J).det ^ 2 = 1 := by
    rw [pow_two, ← Matrix.det_mul, neg_mul_neg, hJJ, Matrix.det_one]
  intro x hx0 hx1
  have ht : (H x)ᵀ = H (-x) := by
    dsimp only [H, J]
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
      ← Matrix.transpose_map, ← Matrix.transpose_map, hV.1, physical_skew V ω hV,
      Matrix.map_neg _ Complex.ofReal_neg, smul_neg, smul_neg,
      Complex.ofReal_neg, neg_smul]
  have hdt : (H (-x)).det = (H x).det := by rw [← ht, Matrix.det_transpose]
  have hprod : (∏ i, ((hH.eigenvalues i ^ 2 - x ^ 2 : ℝ) : ℂ)) = (H x).det ^ 2 := by
    calc
      _ = (∏ i, ((x - hH.eigenvalues i : ℝ) : ℂ)) *
          (∏ i, ((-x - hH.eigenvalues i : ℝ) : ℂ)) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        simp (config := { congrConsts := false }) only
          [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_neg]
        ring
      _ = (-J).det ^ 2 * (H x).det ^ 2 := by rw [hd x, hd (-x), neg_neg, hdt]; ring
      _ = (H x).det ^ 2 := by rw [hdetJ, one_mul]
  have hpx : (H x).PosDef := shifted_posDef V ω hV hpos hx0 hx1
  have hdr : ((H x).det.re : ℂ) = (H x).det := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im, Complex.zero_im] using hpx.det_pos.2
  rw [← hdr, ← Complex.ofReal_pow, ← Complex.ofReal_prod] at hprod
  have hreal := Complex.ofReal_injective hprod
  have hterms (i : ι) : 0 < hH.eigenvalues i ^ 2 - x ^ 2 := by
    have he := symplectic_spectrum_lower_bound V ω hV hpos hω hH i
    nlinarith [sq_abs (hH.eigenvalues i)]
  have hl := congrArg Real.log hreal
  rw [Real.log_prod (fun i _ => (hterms i).ne'), Real.log_pow] at hl
  change Real.log (H x).det.re = _
  norm_num (config := { congrConsts := false }) at hl ⊢
  calc
    Real.log (H x).det.re = (1 / 2 : ℝ) * (2 * Real.log (H x).det.re) := by ring
    _ = _ := congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) hl.symm

private lemma entropy_mixture {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hω : ω * ω = -1)
    (hH : (symplecticOperator V ω).IsHermitian) {α : ℝ}
    (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    IntegrableOn (fun x : ℝ => renyiWeight α x *
      Real.log (((V.map Complex.ofReal) + (x : ℂ) •
        (Complex.I • ω.map Complex.ofReal)).det.re)) (Set.Ioo 0 1) ∧
    gaussianRenyiEntropy α V ω =
      (Fintype.card ι : ℝ) / 2 *
          D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiConstant α +
        ∫ x in Set.Ioo (0 : ℝ) 1,
          D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiWeight α x *
            Real.log (((V.map Complex.ofReal) + (x : ℂ) •
              (Complex.I • ω.map Complex.ofReal)).det.re) := by
  have hs (i : ι) := stieltjes_representation ha0 ha2 ha1
    (symplectic_spectrum_lower_bound V ω hV hpos hω hH i)
  have hi (i : ι) : IntegrableOn (fun x : ℝ => renyiWeight α x *
      Real.log (hH.eigenvalues i ^ 2 - x ^ 2)) (Set.Ioo 0 1) := by
    simpa (config := { congrConsts := false }) only [sq_abs] using (hs i).1
  have heq (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      renyiWeight α x * Real.log (((V.map Complex.ofReal) + (x : ℂ) •
          (Complex.I • ω.map Complex.ofReal)).det.re) =
        (1 / 2 : ℝ) * ∑ i, renyiWeight α x * Real.log (hH.eigenvalues i ^ 2 - x ^ 2) := by
    rw [determinant_spectral_identity V ω hV hpos hω hH x hx.1.le hx.2,
      ← Finset.mul_sum]
    ring
  have hint := (integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul (1 / 2 : ℝ)
  constructor
  · exact IntegrableOn.congr_fun hint (fun x hx => (heq x hx).symm) measurableSet_Ioo
  · have hInt : (∫ x in Set.Ioo (0 : ℝ) 1, renyiWeight α x *
          Real.log (((V.map Complex.ofReal) + (x : ℂ) •
            (Complex.I • ω.map Complex.ofReal)).det.re)) =
        (1 / 2 : ℝ) * ∑ i, ∫ x in Set.Ioo (0 : ℝ) 1,
          renyiWeight α x * Real.log (hH.eigenvalues i ^ 2 - x ^ 2) := by
      rw [setIntegral_congr_fun measurableSet_Ioo heq, integral_const_mul,
        integral_finsetSum Finset.univ (fun i _ => hi i)]
    have hsum : (∑ i, renyiFunction α |hH.eigenvalues i|) =
        (Fintype.card ι : ℝ) * renyiConstant α +
          ∑ i, ∫ x in Set.Ioo (0 : ℝ) 1,
            renyiWeight α x * Real.log (hH.eigenvalues i ^ 2 - x ^ 2) := by
      calc
        _ = ∑ i, (renyiConstant α + ∫ x in Set.Ioo (0 : ℝ) 1,
              renyiWeight α x * Real.log (hH.eigenvalues i ^ 2 - x ^ 2)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa (config := { congrConsts := false }) only [sq_abs] using (hs i).2
        _ = _ := by rw [Finset.sum_add_distrib]; simp (config := { congrConsts := false })
    rw [gaussianRenyiEntropy, dite_eq_left hH, hsum, hInt]
    ring

private lemma alpha_two_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V ω : Matrix ι ι ℝ) (hV : physicalOn V ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hω : ω * ω = -1) :
    gaussianRenyiEntropy 2 V ω = (1 / 2 : ℝ) * Real.log (V.det) := by
  have hH := symplecticOperator_hermitian V ω hV hpos
  have hs (ν : ℝ) : renyiFunction 2 ν = Real.log ν := by
    dsimp only [renyiFunction]
    rw [Real.rpow_two, Real.rpow_two]
    norm_num
    congr 1
    ring
  have hd := determinant_spectral_identity V ω hV hpos hω hH 0 (by norm_num) (by norm_num)
  simp (config := { congrConsts := false }) only
      [Complex.ofReal_zero, zero_smul, add_zero, zero_pow (by norm_num : 2 ≠ 0),
    sub_zero] at hd
  have hmap : (V.map Complex.ofReal).det.re = V.det := by
    have h := Complex.ofRealHom.map_det V
    exact congrArg Complex.re h.symm
  rw [hmap] at hd
  have hlog (i : ι) : Real.log (hH.eigenvalues i ^ 2) = 2 * Real.log |hH.eigenvalues i| := by
    rw [← sq_abs, Real.log_pow]
    norm_num (config := { congrConsts := false })
  simp_rw (config := { congrConsts := false }) [hlog] at hd
  rw [← Finset.mul_sum] at hd
  rw [gaussianRenyiEntropy, dite_eq_left hH]
  simp_rw (config := { congrConsts := false }) [hs]
  calc
    (1 / 2 : ℝ) * ∑ i, Real.log |hH.eigenvalues i| =
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (2 * ∑ i, Real.log |hH.eigenvalues i|)) := by ring
    _ = _ := congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) hd.symm

private theorem det_mono {α : Type*} [Fintype α] [DecidableEq α]
    {P Q : Matrix α α ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hPQ : (Q - P).PosSemidef) : P.det.re ≤ Q.det.re := by
  classical
  cases isEmpty_or_nonempty α with
  | inl h => exact le_of_eq (congrArg (fun M : Matrix α α ℂ => M.det.re)
      (Subsingleton.elim P Q))
  | inr h =>
    exact (Real.log_le_log_iff hP.det_pos.1 hQ.det_pos.1).mp
      (LogDetInformationSubmodularity.log_det_mono hP hQ hPQ)

private theorem schur_factor {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (H : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hH : H.PosDef) :
    let P := H.submatrix Sum.inl Sum.inl
    let X := H.submatrix Sum.inl Sum.inr
    let Q := H.submatrix Sum.inr Sum.inr
    (Q - Xᴴ * P⁻¹ * X).PosDef ∧
      H.det.re = P.det.re * (Q - Xᴴ * P⁻¹ * X).det.re := by
  let P := H.submatrix Sum.inl Sum.inl
  let X := H.submatrix Sum.inl Sum.inr
  let Q := H.submatrix Sum.inr Sum.inr
  have hP : P.PosDef := hH.submatrix Sum.inl_injective
  have h21 : H.submatrix Sum.inr Sum.inl = Xᴴ := by
    dsimp only [X]
    rw [conjTranspose_submatrix, hH.isHermitian.eq]
  have hb : fromBlocks P X Xᴴ Q = H := by
    rw [← h21]
    exact fromBlocks_toBlocks H
  let := hP.isUnit.invertible
  have hs : (Q - Xᴴ * P⁻¹ * X).PosSemidef :=
    (hP.fromBlocks₁₁ X Q).mp (hb.symm ▸ hH.posSemidef)
  have hd : H.det = P.det * (Q - Xᴴ * P⁻¹ * X).det := by
    rw [← hb, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hspos : (Q - Xᴴ * P⁻¹ * X).PosDef := by
    apply hs.posDef_iff_det_ne_zero.mpr
    intro hz
    rw [hz, mul_zero] at hd
    exact (ne_of_gt hH.det_pos) hd
  refine ⟨hspos, ?_⟩
  change H.det.re = P.det.re * (Q - Xᴴ * P⁻¹ * X).det.re
  simp only [hd, Complex.mul_re, hP.det_pos.2.symm, hspos.det_pos.2.symm,
    Complex.zero_im, mul_zero, sub_zero]

private theorem fischer {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (H : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hH : H.PosDef) :
    H.det.re ≤ (H.submatrix Sum.inl Sum.inl).det.re *
      (H.submatrix Sum.inr Sum.inr).det.re := by
  let P := H.submatrix Sum.inl Sum.inl
  let X := H.submatrix Sum.inl Sum.inr
  let Q := H.submatrix Sum.inr Sum.inr
  have hP : P.PosDef := hH.submatrix Sum.inl_injective
  have hQ : Q.PosDef := hH.submatrix Sum.inr_injective
  obtain ⟨hs, hd⟩ := schur_factor H hH
  have hc : (Xᴴ * P⁻¹ * X).PosSemidef :=
    hP.posSemidef.inv.conjTranspose_mul_mul_same X
  have ho : (Q - (Q - Xᴴ * P⁻¹ * X)).PosSemidef := by
    convert hc using 1
    abel
  have hm := det_mono hs hQ ho
  rw [hd]
  exact mul_le_mul_of_nonneg_left hm hP.det_pos.1.le

private theorem schur_submatrix {α β γ : Type*} [Fintype α] [DecidableEq α]
    (P : Matrix α α ℂ) (X : Matrix α β ℂ) (Q : Matrix β β ℂ) (e : γ → β) :
    (Q - Xᴴ * P⁻¹ * X).submatrix e e =
      Q.submatrix e e - (X.submatrix id e)ᴴ * P⁻¹ * X.submatrix id e := by
  change Q.submatrix e e - (Xᴴ * P⁻¹ * X).submatrix e e = _
  rw [submatrix_mul _ _ e id e Function.bijective_id,
    submatrix_mul _ _ e id id Function.bijective_id, submatrix_id_id,
    conjTranspose_submatrix]

private theorem block_koteljanskii {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (H : Matrix (β ⊕ (α ⊕ γ)) (β ⊕ (α ⊕ γ)) ℂ) (hH : H.PosDef) :
    H.det.re * (H.submatrix Sum.inl Sum.inl).det.re ≤
      (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det.re *
        (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det.re := by
  let P := H.submatrix Sum.inl Sum.inl
  let X := H.submatrix Sum.inl Sum.inr
  let Q := H.submatrix Sum.inr Sum.inr
  let S := Q - Xᴴ * P⁻¹ * X
  have hP : P.PosDef := hH.submatrix Sum.inl_injective
  obtain ⟨hs, hd⟩ := schur_factor H hH
  have hA := hH.submatrix
    (Function.injective_id.sumMap (@Sum.inl_injective α γ))
  have hC := hH.submatrix
    (Function.injective_id.sumMap (@Sum.inr_injective α γ))
  have hdA := (schur_factor _ hA).2
  have hdC := (schur_factor _ hC).2
  change (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det.re =
    P.det.re * (Q.submatrix Sum.inl Sum.inl -
      (X.submatrix id Sum.inl)ᴴ * P⁻¹ * X.submatrix id Sum.inl).det.re at hdA
  change (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det.re =
    P.det.re * (Q.submatrix Sum.inr Sum.inr -
      (X.submatrix id Sum.inr)ᴴ * P⁻¹ * X.submatrix id Sum.inr).det.re at hdC
  rw [← schur_submatrix P X Q Sum.inl] at hdA
  rw [← schur_submatrix P X Q Sum.inr] at hdC
  have hf := fischer S hs
  rw [hdA, hdC, hd]
  nlinarith [mul_le_mul_of_nonneg_left hf (sq_nonneg P.det.re)]

private theorem principal_product {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  let eAC := Equiv.Finset.union A C hAC
  have hBU : Disjoint B (A ∪ C) :=
    Finset.disjoint_union_right.mpr ⟨hAB.symm, hBC⟩
  let e := (Equiv.sumCongr (Equiv.refl ↥B) eAC).trans
    (Equiv.Finset.union B (A ∪ C) hBU)
  let f : ↥B ⊕ (↥A ⊕ ↥C) → ι := fun x => (e x).val
  let M := H.submatrix f f
  have hM : M.PosDef := hH.submatrix (Subtype.val_injective.comp e.injective)
  have hm := block_koteljanskii M hM
  have hd : M.det =
      (H.submatrix (Subtype.val : ↥(B ∪ (A ∪ C)) → ι) Subtype.val).det :=
    det_submatrix_equiv_self e
      (H.submatrix (Subtype.val : ↥(B ∪ (A ∪ C)) → ι) Subtype.val)
  have hB : M.submatrix Sum.inl Sum.inl =
      H.submatrix (Subtype.val : ↥B → ι) Subtype.val := rfl
  have hBA :
      (M.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det =
        (H.submatrix (Subtype.val : ↥(B ∪ A) → ι) Subtype.val).det := by
    calc
      _ = ((H.submatrix (Subtype.val : ↥(B ∪ A) → ι) Subtype.val).submatrix
          (Equiv.Finset.union B A hAB.symm) (Equiv.Finset.union B A hAB.symm)).det := by
        congr 1
        ext i j
        cases i <;> cases j <;> rfl
      _ = _ := det_submatrix_equiv_self _ _
  have hBC' :
      (M.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det =
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det := by
    calc
      _ = ((H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).submatrix
          (Equiv.Finset.union B C hBC) (Equiv.Finset.union B C hBC)).det := by
        congr 1
        ext i j
        cases i <;> cases j <;> rfl
      _ = _ := det_submatrix_equiv_self _ _
  rw [hd, hB, hBA, hBC'] at hm
  have hU : B ∪ (A ∪ C) = A ∪ B ∪ C :=
    (Finset.union_left_comm B A C).trans (Finset.union_assoc A B C).symm
  rw [hU, Finset.union_comm B A] at hm
  exact hm

/-- The logarithmic principal-block inequality, including empty blocks. -/
private theorem log_koteljanskii {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    Real.log (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      Real.log (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  have h := principal_product H hH A B C hAB hAC hBC
  have hp (X : Finset ι) :
      0 < (H.submatrix (Subtype.val : ↥X → ι) Subtype.val).det.re :=
    (hH.submatrix Subtype.val_injective).det_pos.1
  have hl := Real.log_le_log (mul_pos (hp (A ∪ B ∪ C)) (hp B)) h
  simpa only [Real.log_mul (hp (A ∪ B ∪ C)).ne' (hp B).ne',
    Real.log_mul (hp (A ∪ B)).ne' (hp (B ∪ C)).ne'] using hl

private lemma mode_interpolation_det {n : ℕ}
    (V ω : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (Y : Finset (Fin n × Fin 2)) (X : Finset (Fin n))
    (hYX : ∀ p, p ∈ Y ↔ p.1 ∈ X) (x : ℝ) :
    (((V.map Complex.ofReal) + (x : ℂ) • (Complex.I • ω.map Complex.ofReal)).submatrix
      (Subtype.val : ↥Y → Fin n × Fin 2) Subtype.val).det =
      (((reducedCovariance V X).map Complex.ofReal) + (x : ℂ) •
        (Complex.I • (reducedCovariance ω X).map Complex.ofReal)).det := by
  let e : ↥Y ≃ {p : Fin n × Fin 2 // p.1 ∈ X} :=
    Equiv.subtypeEquivRight hYX
  rw [principal_block_identity]
  have heq : ((reducedCovariance V X).map Complex.ofReal + (x : ℂ) •
      (Complex.I • (reducedCovariance ω X).map Complex.ofReal)).submatrix e e =
      (V.submatrix (Subtype.val : ↥Y → Fin n × Fin 2)
        Subtype.val).map Complex.ofReal + (x : ℂ) •
          (Complex.I • (ω.submatrix Subtype.val Subtype.val).map Complex.ofReal) := by
    ext i j
    rfl
  rw [← heq]
  exact Matrix.det_submatrix_equiv_self e _

private lemma settlement_main : claim := by
  intro n V hV A B C hAB hAC hBC α ha0 ha2 ha1
  have hp := physical_posDef V hV
  have hr (X : Finset (Fin n)) := reduced_physical V hV X
  have hpr (X : Finset (Fin n)) : ((reducedCovariance V X).map Complex.ofReal).PosDef :=
    hp.submatrix Subtype.val_injective
  have hH (X : Finset (Fin n)) := symplecticOperator_hermitian
    (reducedCovariance V X) (reducedCovariance (symplecticForm n) X) (hr X) (hpr X)
  let L := fun (X : Finset (Fin n)) (x : ℝ) =>
    Real.log (((reducedCovariance V X).map Complex.ofReal + (x : ℂ) •
      (Complex.I • (reducedCovariance (symplecticForm n) X).map Complex.ofReal)).det.re)
  have hk (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
      L (A ∪ B ∪ C) x + L B x ≤ L (A ∪ B) x + L (B ∪ C) x := by
    have h := log_koteljanskii
      (V.map Complex.ofReal + (x : ℂ) • (Complex.I • (symplecticForm n).map Complex.ofReal))
      (shifted_posDef V (symplecticForm n) ((physicalCovariance_iff V).mpr hV) hp hx0 hx1)
      (A ×ˢ (Finset.univ : Finset (Fin 2))) (B ×ˢ Finset.univ) (C ×ˢ Finset.univ)
      (Finset.disjoint_product.mpr (Or.inl hAB))
      (Finset.disjoint_product.mpr (Or.inl hAC))
      (Finset.disjoint_product.mpr (Or.inl hBC))
    rw [mode_interpolation_det V (symplecticForm n) _ (A ∪ B ∪ C)
        (fun p => by
          simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]) x,
      mode_interpolation_det V (symplecticForm n) _ B
        (fun p => by simp only [Finset.mem_product, Finset.mem_univ, and_true]) x,
      mode_interpolation_det V (symplecticForm n) _ (A ∪ B)
        (fun p => by
          simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]) x,
      mode_interpolation_det V (symplecticForm n) _ (B ∪ C)
        (fun p => by
          simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true]) x] at h
    exact h
  rcases lt_or_eq_of_le ha2 with ha2 | ha2
  · have hm (X : Finset (Fin n)) :
        IntegrableOn (fun x => renyiWeight α x * L X x) (Set.Ioo (0 : ℝ) 1) ∧
        gaussianRenyiEntropy α (reducedCovariance V X) (reducedCovariance (symplecticForm n) X) =
          (X.card : ℝ) * renyiConstant α +
            ∫ x in Set.Ioo (0 : ℝ) 1, renyiWeight α x * L X x := by
      have h := entropy_mixture (reducedCovariance V X) (reducedCovariance (symplecticForm n) X)
        (hr X) (hpr X) (reduced_square X) (hH X) ha0 ha2 ha1
      have hc : (Fintype.card {p : Fin n × Fin 2 // p.1 ∈ X} : ℝ) / 2 = (X.card : ℝ) := by
        rw [reduced_card]
        push_cast
        ring
      rw [hc] at h
      exact h
    have hpoint : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        renyiWeight α x * L (A ∪ B ∪ C) x + renyiWeight α x * L B x ≤
          renyiWeight α x * L (A ∪ B) x + renyiWeight α x * L (B ∪ C) x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (hk x hx.1.le hx.2)
        (weight_pos ha0 ha2 ha1 hx.1.le hx.2).le
    have hi := integral_mono_ae ((hm (A ∪ B ∪ C)).1.add (hm B).1)
      ((hm (A ∪ B)).1.add (hm (B ∪ C)).1) hpoint
    simp only [Pi.add_apply] at hi
    rw [integral_add (hm (A ∪ B ∪ C)).1 (hm B).1,
      integral_add (hm (A ∪ B)).1 (hm (B ∪ C)).1] at hi
    have hUC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
    have hc : (A ∪ B).card + (B ∪ C).card = (A ∪ B ∪ C).card + B.card := by
      rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hBC,
        Finset.card_union_of_disjoint hUC, Finset.card_union_of_disjoint hAB]
      omega
    have hcr : ((A ∪ B).card : ℝ) + (B ∪ C).card = (A ∪ B ∪ C).card + B.card := by
      exact_mod_cast hc
    have hconst := congrArg (fun t : ℝ => t * renyiConstant α) hcr
    rw [(hm (A ∪ B)).2, (hm (B ∪ C)).2, (hm (A ∪ B ∪ C)).2, (hm B).2]
    linarith only [hi, hconst]
  · subst α
    have ht (X : Finset (Fin n)) :
        gaussianRenyiEntropy 2 (reducedCovariance V X) (reducedCovariance (symplecticForm n) X) =
          (1 / 2 : ℝ) * L X 0 := by
      rw [alpha_two_entropy _ _ (hr X) (hpr X) (reduced_square X)]
      change (1 / 2 : ℝ) * Real.log (reducedCovariance V X).det =
        (1 / 2 : ℝ) * Real.log (((reducedCovariance V X).map Complex.ofReal +
          (0 : ℂ) •
            (Complex.I • (reducedCovariance (symplecticForm n) X).map Complex.ofReal)).det.re)
      rw [zero_smul, add_zero]
      congr 2
      exact congrArg Complex.re (Complex.ofRealHom.map_det (reducedCovariance V X))
    rw [ht (A ∪ B), ht (B ∪ C), ht (A ∪ B ∪ C), ht B]
    linarith only [hk 0 (by norm_num) (by norm_num)]

theorem result : claim := settlement_main

end D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
