/- GID: D5/S3/Quantum/Analysis/FinitePhaseAnchorStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/FinitePhaseAnchorStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal finite phase anchors control real Hilbert operator error and preserve effect menus. -/

import D5.S3.PrimeGaps.GreedyResidues
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The source is the finite phase stability statement in the V79 theory volume.
All norms below are real Hilbert norms or continuous real operator norms.
The positive averaging facts and the symmetric quadratic row inequality are
reused; the finite anchor reconstruction retains the diagonal mixed probes.
The averaging operation is a mathematical repair, with no control or actual
successor implementation asserted.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
open ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Analysis.FinitePhaseAnchorStability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The source real effect readout. -/
def weight (A : V →L[ℝ] V) (x : V) : ℝ := ⟪x, A x⟫_ℝ

/-- Conjugation uses the genuine real Hilbert adjoint. -/
def phaseConjugate (J A : V →L[ℝ] V) : V →L[ℝ] V := J.adjoint ∘L A ∘L J

/-- The source's common-complex repair, still represented as a real operator. -/
def repair (J A : V →L[ℝ] V) : V →L[ℝ] V := (1 / 2 : ℝ) • (A + phaseConjugate J A)

/-- Exactly the three unit anchor families, with their literal index orders. -/
def AnchorErrors {d : ℕ} (b : OrthonormalBasis (Fin d ⊕ Fin d) ℝ V)
    (J A : V →L[ℝ] V) (ε : ℝ) : Prop :=
  (∀ i, |weight A (b (.inl i)) - weight A (J (b (.inl i)))| ≤ ε) ∧
  (∀ i j, i < j →
    let v := (Real.sqrt 2)⁻¹ • (b (.inl i) + b (.inl j))
    |weight A v - weight A (J v)| ≤ ε) ∧
  (∀ i j, i ≤ j →
    let v := (Real.sqrt 2)⁻¹ • (b (.inl i) + b (.inr j))
    |weight A v - weight A (J v)| ≤ ε)

private theorem weight_bridge (D : V →L[ℝ] V) (hD : D.IsSymmetric) (u v : V) :
    weight D ((Real.sqrt 2)⁻¹ • (u + v)) =
      (weight D u + weight D v) / 2 + ⟪u, D v⟫_ℝ := by
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs : ⟪v, D u⟫_ℝ = ⟪u, D v⟫_ℝ := by
    rw [real_inner_comm, hD u v]
  simp only [weight, map_smul, map_add, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, RCLike.conj_to_real, hs]
  nlinarith only [hc]

private theorem norm_le_of_quadratic (D : V →L[ℝ] V) (hD : D.IsSymmetric)
    (R : ℝ) (hR : 0 ≤ R) (hq : ∀ x, |weight D x| ≤ R * ‖x‖ ^ 2) : ‖D‖ ≤ R := by
  rw [D.norm_eq_iSup_rayleighQuotient hD]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx, rayleighQuotient, reApplyInnerSelf] using hR
  · have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    simpa [rayleighQuotient, reApplyInnerSelf, abs_div, abs_of_nonneg hn.le,
      real_inner_comm, weight] using (div_le_iff₀ hn).mpr (hq x)

private theorem norm_le_of_rows {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (D : V →L[ℝ] V) (hD : D.IsSymmetric)
    (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i, (∑ j, |⟪b i, D (b j)⟫_ℝ|) ≤ R) : ‖D‖ ≤ R := by
  apply norm_le_of_quadratic D hD R hR
  intro x
  have hex : weight D x =
      ∑ i, ∑ j, ⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ * ⟪b i, D (b j)⟫_ℝ := by
    conv_lhs => rw [weight, ← b.sum_repr' x]
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hex]
  calc
    _ ≤ ∑ i, ⟪b i, x⟫_ℝ ^ 2 * ∑ j, |⟪b i, D (b j)⟫_ℝ| :=
      LongGapsBetweenPrimes.abs_quadratic_form_le_rows _ _ (by
        intro i j
        rw [real_inner_comm (b i), hD, real_inner_comm (b j)])
    _ ≤ ∑ i, ⟪b i, x⟫_ℝ ^ 2 * R :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)
    _ = R * ‖x‖ ^ 2 := by rw [← Finset.sum_mul, b.sum_sq_inner_right]; ring

private theorem anchor_rows {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d ⊕ Fin d) ℝ V)
    (D : V →L[ℝ] V) (hD : D.IsSymmetric) (ε : ℝ)
    (haxis : ∀ i, |weight D (b (.inl i))| ≤ ε)
    (hreal : ∀ i j, i < j →
      |weight D ((Real.sqrt 2)⁻¹ • (b (.inl i) + b (.inl j)))| ≤ ε)
    (hmixed : ∀ i j, i ≤ j →
      |weight D ((Real.sqrt 2)⁻¹ • (b (.inl i) + b (.inr j)))| ≤ ε)
    (hff : ∀ i j, ⟪b (.inr i), D (b (.inr j))⟫_ℝ =
      -⟪b (.inl i), D (b (.inl j))⟫_ℝ)
    (hfe : ∀ i j, ⟪b (.inr i), D (b (.inl j))⟫_ℝ =
      ⟪b (.inl i), D (b (.inr j))⟫_ℝ) :
    0 ≤ ε ∧ ∀ k, (∑ l, |⟪b k, D (b l)⟫_ℝ|) ≤ (4 * (d : ℝ) - 2) * ε := by
  classical
  have hε : 0 ≤ ε := (abs_nonneg _).trans (haxis ⟨0, by omega⟩)
  have hs (i j : Fin d) : ⟪b (.inl j), D (b (.inl i))⟫_ℝ =
      ⟪b (.inl i), D (b (.inl j))⟫_ℝ := by rw [real_inner_comm, hD]
  have ht (i j : Fin d) : ⟪b (.inl j), D (b (.inr i))⟫_ℝ =
      ⟪b (.inl i), D (b (.inr j))⟫_ℝ := by rw [← hfe, real_inner_comm, hD]
  have hS (i j : Fin d) (hij : i ≠ j) :
      |⟪b (.inl i), D (b (.inl j))⟫_ℝ| ≤ 2 * ε := by
    have ordered (i j : Fin d) (hij : i < j) :
        |⟪b (.inl i), D (b (.inl j))⟫_ℝ| ≤ 2 * ε := by
      have hh := hreal i j hij
      rw [weight_bridge D hD] at hh
      have hi := abs_le.mp (haxis i)
      have hj := abs_le.mp (haxis j)
      exact abs_le.mpr ⟨by linarith [(abs_le.mp hh).1], by linarith [(abs_le.mp hh).2]⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact ordered i j h
    · rw [← hs]; exact ordered j i h
  have hTdiag (i : Fin d) : |⟪b (.inl i), D (b (.inr i))⟫_ℝ| ≤ ε := by
    have h := hmixed i i le_rfl
    rw [weight_bridge D hD] at h
    simpa [weight, hff] using h
  have hT (i j : Fin d) (hij : i ≠ j) :
      |⟪b (.inl i), D (b (.inr j))⟫_ℝ| ≤ 2 * ε := by
    have ordered (i j : Fin d) (hij : i ≤ j) :
        |⟪b (.inl i), D (b (.inr j))⟫_ℝ| ≤ 2 * ε := by
      have hh := hmixed i j hij
      rw [weight_bridge D hD] at hh
      simp only [weight, hff] at hh
      have hi := abs_le.mp (haxis i)
      have hj := abs_le.mp (haxis j)
      dsimp [weight] at hi hj
      exact abs_le.mpr ⟨by linarith [(abs_le.mp hh).1], by linarith [(abs_le.mp hh).2]⟩
    rcases le_total i j with h | h
    · exact ordered i j h
    · rw [← ht]; exact ordered j i h
  have sum_bound (a : Fin d → ℝ) (i : Fin d) (hi : |a i| ≤ ε)
      (ho : ∀ j, j ≠ i → |a j| ≤ 2 * ε) :
      (∑ j, |a j|) ≤ ε + ((d : ℝ) - 1) * (2 * ε) := by
    calc
      _ = |a i| + ∑ j ∈ Finset.univ.erase i, |a j| := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      _ ≤ ε + ∑ j ∈ Finset.univ.erase i, 2 * ε := by
        apply add_le_add hi
        exact Finset.sum_le_sum fun j hj => ho j (Finset.mem_erase.mp hj).1
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Nat.cast_sub hd]
        norm_num
  refine ⟨hε, ?_⟩
  intro k
  have hSr (i : Fin d) := sum_bound (fun j => ⟪b (.inl i), D (b (.inl j))⟫_ℝ)
    i (haxis i) (fun j hj => hS i j hj.symm)
  have hTr (i : Fin d) := sum_bound (fun j => ⟪b (.inl i), D (b (.inr j))⟫_ℝ)
    i (hTdiag i) (fun j hj => hT i j hj.symm)
  cases k with
  | inl i =>
    rw [Fintype.sum_sum_type]
    linarith [hSr i, hTr i]
  | inr i =>
    simp only [Fintype.sum_sum_type, hfe, hff, abs_neg]
    linarith [hSr i, hTr i]

end D5.S3.Quantum.Analysis.FinitePhaseAnchorStability
