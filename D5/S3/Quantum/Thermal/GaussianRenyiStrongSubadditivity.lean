/- GID: D5/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity
   generality: I
   mirror-B: D5/B/S3/Quantum/Thermal/GaussianRenyiStrongSubadditivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rényi-α strong subadditivity for physical bosonic Gaussian covariances. -/

import D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
import D5.S3.Resource.LogDet.LogDetInformationSubmodularity

/-! Settlement of the bosonic Gaussian Rényi strong-subadditivity line. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Resource.LogDet

namespace D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity

/-! The covariance and entropy interface for the Gaussian Rényi settlement. -/

def symplecticForm (n : ℕ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  fun (p q : Fin n × Fin 2) => if p.1 = q.1 then
    if p.2 = 0 ∧ q.2 = 1 then 1
    else if p.2 = 1 ∧ q.2 = 0 then -1 else 0
  else 0

def physicalOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) : Prop :=
  V.IsSymm ∧ (V.map Complex.ofReal + Complex.I • Ω.map Complex.ofReal).PosSemidef

def physicalCovariance {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) : Prop :=
  physicalOn V (symplecticForm n)

def reducedCovariance {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (X : Finset (Fin n)) :
      Matrix {p : Fin n × Fin 2 // p.1 ∈ X} {p : Fin n × Fin 2 // p.1 ∈ X} ℝ :=
  V.submatrix (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)
    (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)

def reducedForm {n : ℕ} (Ω : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (X : Finset (Fin n)) :
      Matrix {p : Fin n × Fin 2 // p.1 ∈ X} {p : Fin n × Fin 2 // p.1 ∈ X} ℝ :=
  Ω.submatrix (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)
    (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)

def symplecticOperator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  CFC.sqrt (V.map Complex.ofReal) * (Complex.I • Ω.map Complex.ofReal) *
    CFC.sqrt (V.map Complex.ofReal)

def gaussianRenyiEntropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (V Ω : Matrix ι ι ℝ) : ℝ :=
  if h : (symplecticOperator V Ω).IsHermitian then
    (1 / 2 : ℝ) * ∑ i, D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiFunction α
      |h.eigenvalues i|
  else 0

def claim : Prop :=
  ∀ (n : ℕ) (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
    physicalCovariance V → ∀ A B C : Finset (Fin n),
      Disjoint A B → Disjoint A C → Disjoint B C → ∀ α : ℝ,
        0 < α → α ≤ 2 → α ≠ 1 →
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B))
              (reducedForm (symplecticForm n) (A ∪ B)) +
            gaussianRenyiEntropy α (reducedCovariance V (B ∪ C))
              (reducedForm (symplecticForm n) (B ∪ C)) ≥
          gaussianRenyiEntropy α (reducedCovariance V (A ∪ B ∪ C))
              (reducedForm (symplecticForm n) (A ∪ B ∪ C)) +
            gaussianRenyiEntropy α (reducedCovariance V B)
              (reducedForm (symplecticForm n) B)

private lemma physical_posDef {n : ℕ}
    (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (hV : physicalCovariance V) : (V.map Complex.ofReal).PosDef := by
  sorry

private lemma reduced_physical {n : ℕ}
    (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hV : physicalCovariance V)
    (X : Finset (Fin n)) :
    physicalOn (reducedCovariance V X) (reducedForm (symplecticForm n) X) := by
  rcases hV with ⟨hs, hp⟩
  constructor
  · exact hs.submatrix (fun p : {q : Fin n × Fin 2 // q.1 ∈ X} => p.1)
  · let f : {q : Fin n × Fin 2 // q.1 ∈ X} → Fin n × Fin 2 := fun p => p.1
    have heq : ((V.map Complex.ofReal) + Complex.I • (symplecticForm n).map
        Complex.ofReal).submatrix f f =
        (V.submatrix f f).map Complex.ofReal +
          Complex.I • ((symplecticForm n).submatrix f f).map Complex.ofReal := by
      ext i j
      rfl
    change (((V.submatrix f f).map Complex.ofReal) +
      Complex.I • ((symplecticForm n).submatrix f f).map Complex.ofReal).PosSemidef
    rw [← heq]
    exact hp.submatrix f

private lemma symplectic_spectrum_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1)
    (hH : (symplecticOperator V Ω).IsHermitian) :
    ∀ i, 1 ≤ |hH.eigenvalues i| := by
  sorry

private lemma shifted_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
    (hpos : (V.map Complex.ofReal).PosDef) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ((V.map Complex.ofReal) + (x : ℂ) • (Complex.I • Ω.map Complex.ofReal)).PosDef := by
  sorry

private lemma principal_block_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) (X : Finset ι) (x : ℝ) :
    ((V.map Complex.ofReal) + (x : ℂ) • (Complex.I • Ω.map Complex.ofReal)).submatrix
        (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1) =
      ((V.submatrix (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1)).map
          Complex.ofReal) +
        (x : ℂ) • (Complex.I •
          (Ω.submatrix (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1)).map
            Complex.ofReal) := by
  ext i j
  rfl

private lemma determinant_spectral_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1)
    (hH : (symplecticOperator V Ω).IsHermitian) :
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      Real.log (((V.map Complex.ofReal) + (x : ℂ) •
        (Complex.I • Ω.map Complex.ofReal)).det.re) =
        (1 / 2 : ℝ) * ∑ i, Real.log (hH.eigenvalues i ^ 2 - x ^ 2) := by
  sorry

private lemma entropy_mixture {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1)
    (hH : (symplecticOperator V Ω).IsHermitian) {α : ℝ}
    (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    gaussianRenyiEntropy α V Ω =
      (Fintype.card ι : ℝ) / 2 *
          D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiConstant α +
        ∫ x in Set.Ioo (0 : ℝ) 1,
          D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiWeight α x *
            Real.log (((V.map Complex.ofReal) + (x : ℂ) •
              (Complex.I • Ω.map Complex.ofReal)).det.re) := by
  sorry

private lemma alpha_two_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
    (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1) :
    gaussianRenyiEntropy 2 V Ω = (1 / 2 : ℝ) * Real.log (V.det) := by
  sorry

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

/-- Koteljanskii's inequality, with determinants read as positive real numbers. -/
private theorem koteljanskii {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  exact principal_product H hH A B C hAB hAC hBC

/-- The logarithmic principal-block inequality, including empty blocks. -/
private theorem log_koteljanskii {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    Real.log (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      Real.log (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  have h := koteljanskii H hH A B C hAB hAC hBC
  have hp (X : Finset ι) :
      0 < (H.submatrix (Subtype.val : ↥X → ι) Subtype.val).det.re :=
    (hH.submatrix Subtype.val_injective).det_pos.1
  have hl := Real.log_le_log (mul_pos (hp (A ∪ B ∪ C)) (hp B)) h
  simpa only [Real.log_mul (hp (A ∪ B ∪ C)).ne' (hp B).ne',
    Real.log_mul (hp (A ∪ B)).ne' (hp (B ∪ C)).ne'] using hl

private lemma koteljanskii_log_step {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    Real.log (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      Real.log (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  exact log_koteljanskii H hH A B C hAB hAC hBC

private lemma settlement_main
    (hpos : ∀ {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
      physicalCovariance V → (V.map Complex.ofReal).PosDef)
    (hred : ∀ {n : ℕ} (V : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ),
      physicalCovariance V → ∀ X : Finset (Fin n),
        physicalOn (reducedCovariance V X) (reducedForm (symplecticForm n) X))
    (hspec : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
      (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1)
      (hH : (symplecticOperator V Ω).IsHermitian), ∀ i, 1 ≤ |hH.eigenvalues i|)
    (hshift : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
      (hpos : (V.map Complex.ofReal).PosDef) {x : ℝ}, 0 ≤ x → x < 1 →
      ((V.map Complex.ofReal) + (x : ℂ) • (Complex.I • Ω.map Complex.ofReal)).PosDef)
    (hdet : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
      (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1)
      (hH : (symplecticOperator V Ω).IsHermitian), ∀ x : ℝ, 0 ≤ x → x < 1 →
      Real.log (((V.map Complex.ofReal) + (x : ℂ) •
        (Complex.I • Ω.map Complex.ofReal)).det.re) =
        (1 / 2 : ℝ) * ∑ i, Real.log (hH.eigenvalues i ^ 2 - x ^ 2))
    (hblock : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (V Ω : Matrix ι ι ℝ) (X : Finset ι) (x : ℝ),
      ((V.map Complex.ofReal) + (x : ℂ) • (Complex.I • Ω.map Complex.ofReal)).submatrix
          (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1) =
        ((V.submatrix (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1)).map
            Complex.ofReal) +
          (x : ℂ) • (Complex.I •
            (Ω.submatrix (fun i : {j // j ∈ X} => i.1) (fun i : {j // j ∈ X} => i.1)).map
              Complex.ofReal))
    (hmix : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
      (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1)
      (hH : (symplecticOperator V Ω).IsHermitian) {α : ℝ},
      0 < α → α < 2 → α ≠ 1 →
      gaussianRenyiEntropy α V Ω =
        (Fintype.card ι : ℝ) / 2 *
            D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiConstant α +
          ∫ x in Set.Ioo (0 : ℝ) 1,
            D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.renyiWeight α x *
              Real.log (((V.map Complex.ofReal) + (x : ℂ) •
                (Complex.I • Ω.map Complex.ofReal)).det.re))
    (hkotel : ∀ {ι : Type} [DecidableEq ι]
      (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι),
      Disjoint A B → Disjoint A C → Disjoint B C →
      Real.log (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re +
          Real.log (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
        Real.log (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re +
          Real.log (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re)
    (ha2 : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (V Ω : Matrix ι ι ℝ) (hV : physicalOn V Ω)
      (hpos : (V.map Complex.ofReal).PosDef) (hΩ : Ω * Ω = -1),
      gaussianRenyiEntropy 2 V Ω = (1 / 2 : ℝ) * Real.log (V.det)) : claim := by
  sorry

theorem result : claim :=
  settlement_main physical_posDef reduced_physical symplectic_spectrum_lower_bound
    shifted_posDef determinant_spectral_identity principal_block_identity
    entropy_mixture koteljanskii_log_step alpha_two_entropy

end D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity
