/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignMatrices
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian sign matrices have zero trace and fixed energy. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.ConditionalConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

/-- The two signs used in one upper-triangular entry. -/
def signScalar (ε η : Bool) : ℂ :=
  (3 / 5 : ℂ) * ((if ε then 1 else -1) + Complex.I * (if η then 1 else -1))

/-- A finite sign sample, with the lower triangle filled by conjugation. -/
def finiteSignMatrix {α : Type} [LinearOrder α] [DecidableEq α]
    (ε η : α → α → Bool) : Matrix α α ℂ := fun i j =>
  if i = j then 0 else if i < j then signScalar (ε i j) (η i j)
    else starRingEnd ℂ (signScalar (ε j i) (η j i))

theorem finiteSignMatrix_apply_diag {α : Type} [LinearOrder α] [DecidableEq α]
    (ε η : α → α → Bool) (i : α) :
    finiteSignMatrix ε η i i = 0 := by
  simp [finiteSignMatrix]

theorem signScalar_normSq (ε η : Bool) :
    Complex.normSq (signScalar ε η) = (18 / 25 : ℝ) := by
  simp [signScalar, Complex.normSq]
  split <;> split <;> norm_num

theorem finiteSignMatrix_isHermitian {α : Type} [LinearOrder α] [DecidableEq α]
    (ε η : α → α → Bool) :
    (finiteSignMatrix ε η).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [finiteSignMatrix]
  · by_cases hlt : i < j
    · have hjni : ¬j < i := not_lt_of_ge hlt.le
      simp [finiteSignMatrix, hij, hlt, hjni, hlt.ne']
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simp [finiteSignMatrix, hij, hlt, hji, Ne.symm hij]

theorem finiteSignMatrix_offdiag_normSq {α : Type} [LinearOrder α] [DecidableEq α]
    (ε η : α → α → Bool) {i j : α} (hij : i ≠ j) :
    Complex.normSq (finiteSignMatrix ε η i j) = (18 / 25 : ℝ) := by
  classical
  by_cases hlt : i < j
  · simp [finiteSignMatrix, hij, hlt, signScalar_normSq]
  · simp [finiteSignMatrix, hij, hlt, signScalar_normSq]

private theorem trace_mul_conjTranspose_frobenius {α : Type} [Fintype α]
    (A : Matrix α α ℂ) :
    (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_pow]

theorem finiteSignMatrix_energy {α : Type} [Fintype α] [LinearOrder α] [DecidableEq α]
    (ε η : α → α → Bool) :
    ((finiteSignMatrix ε η * finiteSignMatrix ε η).trace).re =
      (18 / 25 : ℝ) * (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
  let H := finiteSignMatrix ε η
  have hH : H.IsHermitian := finiteSignMatrix_isHermitian ε η
  have hstar : Hᴴ = H := hH
  have hf := trace_mul_conjTranspose_frobenius H
  have htr : (H * H).trace = ((∑ i, ∑ j, ‖H i j‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [hstar] using hf
  rw [show finiteSignMatrix ε η = H from rfl, htr]
  simp only [Complex.ofReal_re]
  have hdiag : ∀ i : α, ‖H i i‖ ^ 2 = 0 := by
    intro i
    simp [H, finiteSignMatrix]
  have hoff : ∀ i j : α, i ≠ j → ‖H i j‖ ^ 2 = (18 / 25 : ℝ) := by
    intro i j hij
    have hs := finiteSignMatrix_offdiag_normSq ε η hij
    simpa [Complex.normSq_eq_norm_sq] using hs
  have hterm : ∀ i j : α, ‖H i j‖ ^ 2 =
      if i = j then 0 else (18 / 25 : ℝ) := by
    intro i j
    by_cases hij : i = j
    · simp [hij, hdiag]
    · simp [hij, hoff i j hij]
  simp_rw [hterm]
  let c : ℝ := 18 / 25
  have hinner (i : α) :
      (∑ j : α, if i = j then 0 else c) = c * ((Fintype.card α : ℝ) - 1) := by
    calc
      (∑ j : α, if i = j then 0 else c) =
          ∑ j : α, (c - if i = j then c else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases h : i = j <;> simp [h]
      _ = (∑ _j : α, c) - (∑ j : α, if i = j then c else 0) := by
            rw [Finset.sum_sub_distrib]
      _ = c * ((Fintype.card α : ℝ) - 1) := by
            rw [Finset.sum_const]
            have hdiag_sum : (∑ j : α, if i = j then c else 0) = c := by
              rw [Finset.sum_ite_eq Finset.univ i (fun _ => c)]
              simp
            rw [hdiag_sum]
            simp [Finset.card_univ, nsmul_eq_mul, c]
            ring
  calc
    (∑ i : α, ∑ j : α, if i = j then 0 else (18 / 25 : ℝ)) =
        ∑ i : α, c * ((Fintype.card α : ℝ) - 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [c] using hinner i
    _ = (18 / 25 : ℝ) * (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, c]
          ring

theorem finiteSignMatrix_trace_zero {α : Type} [Fintype α] [LinearOrder α] [DecidableEq α]
    (ε η : α → α → Bool) :
    (finiteSignMatrix ε η).trace = 0 := by
  simp [Matrix.trace, finiteSignMatrix_apply_diag]

/-- The requested sign sample on the bipartite index set `Fin d × Fin d`. -/
def finiteSignSample {d : ℕ} (ε η : (Fin d × Fin d) → (Fin d × Fin d) → Bool) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := by
  letI : LinearOrder (Fin d × Fin d) := Equiv.linearOrder finProdFinEquiv
  exact finiteSignMatrix ε η

theorem finiteSignSample_isHermitian {d : ℕ}
    (ε η : (Fin d × Fin d) → (Fin d × Fin d) → Bool) :
    (finiteSignSample ε η).IsHermitian := by
  let _ : LinearOrder (Fin d × Fin d) := Equiv.linearOrder finProdFinEquiv
  exact finiteSignMatrix_isHermitian ε η

theorem finiteSignSample_trace_zero {d : ℕ}
    (ε η : (Fin d × Fin d) → (Fin d × Fin d) → Bool) :
    (finiteSignSample ε η).trace = 0 := by
  let _ : LinearOrder (Fin d × Fin d) := Equiv.linearOrder finProdFinEquiv
  exact finiteSignMatrix_trace_zero ε η

theorem finiteSignSample_energy {d : ℕ}
    (ε η : (Fin d × Fin d) → (Fin d × Fin d) → Bool) :
    ((finiteSignSample ε η * finiteSignSample ε η).trace).re =
      (18 / 25 : ℝ) * (d : ℝ)^2 * ((d : ℝ)^2 - 1) := by
  let _ : LinearOrder (Fin d × Fin d) := Equiv.linearOrder finProdFinEquiv
  rw [show finiteSignSample ε η = finiteSignMatrix ε η from rfl,
    finiteSignMatrix_energy]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  ring

theorem finiteSignSample_energy_lower {d : ℕ} (hd : 2 ≤ d)
    (ε η : (Fin d × Fin d) → (Fin d × Fin d) → Bool) :
    (d : ℝ)^4 / 2 ≤
      ((finiteSignSample ε η * finiteSignSample ε η).trace).re := by
  let _ : LinearOrder (Fin d × Fin d) := Equiv.linearOrder finProdFinEquiv
  rw [finiteSignSample_energy]
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 0 ≤ (d : ℝ)^2 := sq_nonneg _
  have hlin : 0 ≤ 11 * (d : ℝ)^2 - 36 := by nlinarith
  have hprod : 0 ≤ (d : ℝ)^2 * (11 * (d : ℝ)^2 - 36) :=
    mul_nonneg hx hlin
  nlinarith [hprod]

/-- The finite sign construction supplies the conditional bridge once the two analytic
    sample estimates are supplied as explicit propositions. -/
theorem finiteSignSample_conditional {k d : ℕ} (hk : 2 ≤ k)
    (hdim : 524288 * k ^ 3 ≤ d)
    (ε η : (Fin d × Fin d) → (Fin d × Fin d) → Bool)
    (hQ : SchmidtQuadraticBound k (finiteSignSample ε η))
    (hR : (pptTest (finiteSignSample ε η)).PosSemidef)
    (hΓ : (partialTranspose (pptTest (finiteSignSample ε η))).PosSemidef) :
    ∃ Φ : MatrixMap (Fin d) (Fin d) ℂ,
      inputChoi Φ = choiCandidate (finiteSignSample ε η) ∧
        IsKEB k Φ ∧ ¬ IsDecomposable Φ := by
  let _ : LinearOrder (Fin d × Fin d) := Equiv.linearOrder finProdFinEquiv
  have hkd : k ≤ d := by
    have hkpow : k ≤ k ^ 3 := Nat.le_pow (by decide)
    omega
  have hd : 2 ≤ d := le_trans hk hkd
  exact conditional_indecomposable_kEB (by omega) hkd
    (finiteSignSample ε η) (finiteSignSample_isHermitian ε η)
    (finiteSignSample_trace_zero ε η)
    (finiteSignSample_energy_lower hd ε η) hQ hR hΓ

end D5.S3.Quantum.Entanglement.EntanglementBreaking
