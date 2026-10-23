/- GID: D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite measure-and-prepare processes cannot perfectly clone amplitude-damping channels. -/

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
  sorry

private lemma ad_tp (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (r r' : Fin 2) :
    ∑ o : Fin 2, adChoi (1 - s ^ 2) (r, o) (r', o) = if r = r' then 1 else 0 := by
  sorry

private lemma ad_injective (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h : adChoi (1 - s ^ 2) = adChoi (1 - t ^ 2)) : s = t := by
  sorry

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
  sorry

private lemma red_pow (n : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    red n (choiPow (adChoi (1 - s ^ 2)) (n + 1)) = adChoi (1 - s ^ 2) := by
  sorry

private lemma red_sum (n L : ℕ) (p : Fin L → ℂ)
    (K : Fin L → Matrix (Fin (n + 1) → Fin 2 × Fin 2)
      (Fin (n + 1) → Fin 2 × Fin 2) ℂ) :
    red n (∑ ℓ, p ℓ • K ℓ) = ∑ ℓ, p ℓ • red n (K ℓ) := by
  sorry

private lemma ad_extreme (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (L : ℕ) (q : Fin L → ℂ)
    (R : Fin L → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hR : ∀ ℓ, (R ℓ).PosSemidef ∧ ∀ r r' : Fin 2,
      ∑ o : Fin 2, R ℓ (r, o) (r', o) = if r = r' then 1 else 0)
    (hq : ∀ ℓ, 0 ≤ q ℓ) (h : ∑ ℓ, q ℓ • R ℓ = adChoi (1 - s ^ 2))
    (ℓ : Fin L) (hℓ : q ℓ ≠ 0) : R ℓ = adChoi (1 - s ^ 2) := by
  sorry

private lemma measurement_polynomial (N : ℕ)
    (T : Matrix (Fin N → Fin 2 × Fin 2) (Fin N → Fin 2 × Fin 2) ℂ) :
    ∃ P : Polynomial ℂ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      P.eval (s : ℂ) = Matrix.trace (T * choiPow (adChoi (1 - s ^ 2)) N) := by
  sorry

private lemma polynomial_zero (P : Polynomial ℂ)
    (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      P.eval (s : ℂ) ≠ 0 → R = adChoi (1 - s ^ 2)) : P = 0 := by
  sorry

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

end

end D5.S3.Quantum.QuantumChannels.AmplitudeDampingMeasurePrepareCloning
