/- GID: D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite measure-and-prepare cannot clone amplitude-damping channels. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning

open scoped BigOperators ComplexOrder
open Matrix Polynomial
open D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

/-- The unnormalized Choi matrix, with the reference index first, from the two Kraus operators. -/
def adChoi (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![!![1, 0; 0, (Real.sqrt (1 - γ) : ℂ)], !![0, (Real.sqrt γ : ℂ); 0, 0]]
  fun x y => ∑ k, A k x.2 x.1 * star (A k y.2 y.1)

/-- The tensor power of a Choi matrix, including the empty tensor power. -/
def choiPow (J : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (n : ℕ) :
    Matrix (Fin n → Fin 2 × Fin 2) (Fin n → Fin 2 × Fin 2) ℂ :=
  fun x y => ∏ i, J (x i) (y i)

/-- Positivity and the reference marginal identity for an unnormalized channel Choi matrix. -/
def IsChannelChoi {n : ℕ}
    (K : Matrix (Fin n → Fin 2 × Fin 2) (Fin n → Fin 2 × Fin 2) ℂ) : Prop :=
  K.PosSemidef ∧ ∀ r r' : Fin n → Fin 2,
    ∑ o : Fin n → Fin 2, K (fun i => (r i, o i)) (fun i => (r' i, o i)) =
      if r = r' then 1 else 0

/-- No finite measurement and channel preparation perfectly reproduces every tensor power. -/
def claim : Prop :=
  ∀ N M : ℕ, 1 ≤ M → ¬ ∃ (L : ℕ)
    (T : Fin L → Matrix (Fin N → Fin 2 × Fin 2) (Fin N → Fin 2 × Fin 2) ℂ)
    (K : Fin L → Matrix (Fin M → Fin 2 × Fin 2) (Fin M → Fin 2 × Fin 2) ℂ),
    (∀ ℓ, IsChannelChoi (K ℓ)) ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      (∀ ℓ, 0 ≤ Matrix.trace (T ℓ * choiPow (adChoi γ) N)) ∧
      (∑ ℓ, Matrix.trace (T ℓ * choiPow (adChoi γ) N)) = 1 ∧
      (∑ ℓ, Matrix.trace (T ℓ * choiPow (adChoi γ) N) • K ℓ) =
        choiPow (adChoi γ) M

private def polyChoi : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Polynomial ℂ) :=
  let w : (Fin 2 × Fin 2) → Polynomial ℂ :=
    fun x => if x = (0, 0) then 1 else if x = (1, 1) then X else 0
  fun x y => w x * w y +
    (1 - X ^ 2) * (if x = (1, 0) ∧ y = (1, 0) then 1 else 0)

private lemma ad_entries (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (x y : Fin 2 × Fin 2) :
    adChoi (1 - s ^ 2) x y = (polyChoi x y).eval (s : ℂ) := by
  have hγ : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  rcases x with ⟨r, o⟩
  rcases y with ⟨r', o'⟩
  fin_cases r <;> fin_cases o <;> fin_cases r' <;> fin_cases o' <;>
    simp [adChoi, polyChoi, Fin.sum_univ_two, Real.sqrt_sq hs.1,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hγ] <;> ring

private lemma ad_tp (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (r r' : Fin 2) :
    ∑ o : Fin 2, adChoi (1 - s ^ 2) (r, o) (r', o) = if r = r' then 1 else 0 := by
  simp_rw [ad_entries s hs]
  fin_cases r <;> fin_cases r' <;>
    simp [Fin.sum_univ_two, polyChoi] <;> ring

private lemma ad_injective (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h : adChoi (1 - s ^ 2) = adChoi (1 - t ^ 2)) : s = t := by
  have he := congrArg (fun A => A (0, 0) (1, 1)) h
  simp only [ad_entries s hs, ad_entries t ht] at he
  simpa [polyChoi] using he

/-- Feed zero into the other reference sites and trace their output sites. -/
private def red (n : ℕ)
    (K : Matrix (Fin (n + 1) → Fin 2 × Fin 2) (Fin (n + 1) → Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  partialTraceRight (K.submatrix
    (fun z : (Fin 2 × Fin 2) × (Fin n → Fin 2) => Fin.cons z.1 (fun i => (0, z.2 i)))
    (fun z : (Fin 2 × Fin 2) × (Fin n → Fin 2) => Fin.cons z.1 (fun i => (0, z.2 i))))

private lemma red_channel (n : ℕ)
    (K : Matrix (Fin (n + 1) → Fin 2 × Fin 2) (Fin (n + 1) → Fin 2 × Fin 2) ℂ)
    (hK : IsChannelChoi K) :
    (red n K).PosSemidef ∧ ∀ r r' : Fin 2,
      ∑ o : Fin 2, red n K (r, o) (r', o) = if r = r' then 1 else 0 := by
  refine ⟨partialTraceRight_posSemidef (hK.1.submatrix _), ?_⟩
  intro r r'
  have ht := hK.2 (Fin.cons r (fun _ => 0)) (Fin.cons r' (fun _ => 0))
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp] at ht
  rw [Fintype.sum_prod_type] at ht
  have hcons (a b : Fin 2) (v : Fin n → Fin 2) :
      (fun i => ((@Fin.cons n (fun _ => Fin 2) a (fun _ => 0)) i,
        (@Fin.cons n (fun _ => Fin 2) b v) i)) =
        @Fin.cons n (fun _ => Fin 2 × Fin 2) (a, b) (fun i => (0, v i)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [Fin.consEquiv_apply] at ht
  simp_rw [hcons] at ht
  simpa [red, partialTraceRight, Fin.cons_inj] using ht

private lemma red_pow (n : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    red n (choiPow (adChoi (1 - s ^ 2)) (n + 1)) = adChoi (1 - s ^ 2) := by
  ext x y
  simp only [red, partialTraceRight, Matrix.submatrix_apply, choiPow,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (o : Fin 2) =>
    adChoi (1 - s ^ 2) (0, o) (0, o))]
  simp_rw [ad_tp s hs 0 0]
  simp

private lemma red_sum (n L : ℕ) (p : Fin L → ℂ)
    (K : Fin L → Matrix (Fin (n + 1) → Fin 2 × Fin 2)
      (Fin (n + 1) → Fin 2 × Fin 2) ℂ) :
    red n (∑ ℓ, p ℓ • K ℓ) = ∑ ℓ, p ℓ • red n (K ℓ) := by
  ext x y
  simp only [red, partialTraceRight, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

private lemma ad_extreme (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (L : ℕ) (q : Fin L → ℂ)
    (R : Fin L → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hR : ∀ ℓ, (R ℓ).PosSemidef ∧ ∀ r r' : Fin 2,
      ∑ o : Fin 2, R ℓ (r, o) (r', o) = if r = r' then 1 else 0)
    (hq : ∀ ℓ, 0 ≤ q ℓ) (h : ∑ ℓ, q ℓ • R ℓ = adChoi (1 - s ^ 2))
    (ℓ : Fin L) (hℓ : q ℓ ≠ 0) : R ℓ = adChoi (1 - s ^ 2) := by
  have hkern (v : (Fin 2 × Fin 2) → ℂ)
      (hv : adChoi (1 - s ^ 2) *ᵥ v = 0) : R ℓ *ᵥ v = 0 := by
    apply (hR ℓ).1.dotProduct_mulVec_zero_iff.mp
    have he := congrArg (fun A => star v ⬝ᵥ (A *ᵥ v)) h
    have hsum : ∑ j, q j * (star v ⬝ᵥ (R j *ᵥ v)) = 0 := by
      simpa only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
        dotProduct_smul, smul_eq_mul, hv, dotProduct_zero] using he
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hq j) ((hR j).1.dotProduct_mulVec_nonneg v))).mp hsum
    exact (mul_eq_zero.mp (ht ℓ (Finset.mem_univ ℓ))).resolve_left hℓ
  have hcol01 (x : Fin 2 × Fin 2) : R ℓ x (0, 1) = 0 := by
    have hv : adChoi (1 - s ^ 2) *ᵥ Pi.single (0, 1) 1 = 0 := by
      ext x
      simp [Matrix.mulVec_single_one, ad_entries s hs, polyChoi]
    have hx := congrFun (hkern _ hv) x
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using hx
  have hcol11 (x : Fin 2 × Fin 2) : R ℓ x (1, 1) = (s : ℂ) * R ℓ x (0, 0) := by
    let v : (Fin 2 × Fin 2) → ℂ :=
      (s : ℂ) • Pi.single (0, 0) 1 - Pi.single (1, 1) 1
    have hv : adChoi (1 - s ^ 2) *ᵥ v = 0 := by
      ext ⟨r, o⟩
      fin_cases r <;> fin_cases o <;>
        simp [v, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one,
          ad_entries s hs, polyChoi] <;> ring
    have hx := congrFun (hkern v hv) x
    simp only [v, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one,
      Pi.sub_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul, Pi.zero_apply] at hx
    exact (sub_eq_zero.mp hx).symm
  have hherm := (hR ℓ).1.isHermitian
  have hrow01 (x : Fin 2 × Fin 2) : R ℓ (0, 1) x = 0 := by
    rw [← hherm.apply, hcol01, star_zero]
  have h00 : R ℓ (0, 0) (0, 0) = 1 := by
    simpa [Fin.sum_univ_two, hrow01] using (hR ℓ).2 0 0
  have h0010 : R ℓ (0, 0) (1, 0) = 0 := by
    simpa [Fin.sum_univ_two, hrow01] using (hR ℓ).2 0 1
  have h1000 : R ℓ (1, 0) (0, 0) = 0 := by
    rw [← hherm.apply, h0010, star_zero]
  have h1100 : R ℓ (1, 1) (0, 0) = (s : ℂ) := by
    rw [← hherm.apply, hcol11, h00, mul_one]
    simp
  have h1110 : R ℓ (1, 1) (1, 0) = 0 := by
    rw [← hherm.apply, hcol11, h1000, mul_zero, star_zero]
  have h1010 : R ℓ (1, 0) (1, 0) = 1 - (s : ℂ) ^ 2 := by
    have ht := (hR ℓ).2 1 1
    simp only [Fin.sum_univ_two, hcol11, h1100, ite_true] at ht
    linear_combination ht
  ext ⟨r, o⟩ ⟨r', o'⟩
  fin_cases r <;> fin_cases o <;> fin_cases r' <;> fin_cases o' <;>
    simp [ad_entries s hs, polyChoi, hcol01, hrow01, hcol11, h00,
      h0010, h1000, h1100, h1110, h1010] <;> ring

private lemma measurement_polynomial (N : ℕ)
    (T : Matrix (Fin N → Fin 2 × Fin 2) (Fin N → Fin 2 × Fin 2) ℂ) :
    ∃ P : Polynomial ℂ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      P.eval (s : ℂ) = Matrix.trace (T * choiPow (adChoi (1 - s ^ 2)) N) := by
  refine ⟨∑ x, ∑ y, C (T x y) * ∏ i, polyChoi (y i) (x i), ?_⟩
  intro s hs
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, ← ad_entries s hs, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, choiPow]

private lemma polynomial_zero (P : Polynomial ℂ)
    (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      P.eval (s : ℂ) ≠ 0 → R = adChoi (1 - s ^ 2)) : P = 0 := by
  by_cases hz : ∀ s ∈ Set.Icc (0 : ℝ) 1, P.eval (s : ℂ) = 0
  · apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn).mono
    rintro z ⟨s, hs, rfl⟩
    exact hz s hs
  · push_neg at hz
    obtain ⟨t, ht, hpt⟩ := hz
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).sdiff
      (Set.finite_singleton t)).image Complex.ofReal_injective.injOn).mono
    rintro z ⟨s, ⟨hs, hst⟩, rfl⟩
    change P.eval (s : ℂ) = 0
    by_contra hp
    have he := ad_injective s t hs ht ((h s hs hp).symm.trans (h t ht hpt))
    exact hst (Set.mem_singleton_iff.mpr he)

/-- Perfect measure-and-prepare cloning of the amplitude-damping family is impossible. -/
theorem result : claim := by
  intro N M hM h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
  obtain ⟨L, T, K, hK, h⟩ := h
  have hzero (ℓ : Fin L) : Matrix.trace (T ℓ * choiPow (adChoi 1) N) = 0 := by
    obtain ⟨P, hP⟩ := measurement_polynomial N (T ℓ)
    have hp0 : P = 0 := by
      apply polynomial_zero P (red n (K ℓ))
      intro s hs hp
      have hγ : 1 - s ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> nlinarith [hs.1, hs.2, sq_nonneg s]
      obtain ⟨hq, _, heq⟩ := h (1 - s ^ 2) hγ
      have hr := congrArg (red n) heq
      rw [red_sum, red_pow n s hs] at hr
      apply ad_extreme s hs L _ (fun j => red n (K j))
        (fun j => red_channel n (K j) (hK j)) hq hr ℓ
      rwa [← hP s hs]
    have hp := hP 0 (by constructor <;> norm_num)
    simpa [hp0] using hp.symm
  have hnorm := (h 1 (by constructor <;> norm_num)).2.1
  simp_rw [hzero] at hnorm
  simpa using hnorm

#print axioms result

end

end D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning
