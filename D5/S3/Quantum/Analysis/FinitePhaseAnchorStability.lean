/- GID: D5/S3/Quantum/Analysis/FinitePhaseAnchorStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/FinitePhaseAnchorStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite phase anchors bound real operator error and preserve effect menus. -/

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

omit [CompleteSpace V] in
private theorem weight_bridge (D : V →L[ℝ] V) (hD : D.IsSymmetric) (u v : V) :
    weight D ((Real.sqrt 2)⁻¹ • (u + v)) =
      (weight D u + weight D v) / 2 + ⟪u, D v⟫_ℝ := by
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs : ⟪v, D u⟫_ℝ = ⟪u, D v⟫_ℝ := by
    rw [real_inner_comm]
    exact hD u v
  simp only [weight, map_smul, map_add, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, RCLike.conj_to_real, hs]
  linear_combination (⟪u, D u⟫_ℝ + ⟪v, D v⟫_ℝ + 2 * ⟪u, D v⟫_ℝ) * hc

omit [CompleteSpace V] in
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

omit [CompleteSpace V] in
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
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hs : ⟪b j, D (b i)⟫_ℝ = ⟪b i, D (b j)⟫_ℝ := by
      rw [real_inner_comm]
      exact hD (b i) (b j)
    rw [hs]
    ring
  rw [hex]
  calc
    _ ≤ ∑ i, ⟪b i, x⟫_ℝ ^ 2 * ∑ j, |⟪b i, D (b j)⟫_ℝ| :=
      LongGapsBetweenPrimes.abs_quadratic_form_le_rows _ _ (by
        intro i j
        congr 1
        rw [real_inner_comm]
        exact hD (b j) (b i))
    _ ≤ ∑ i, ⟪b i, x⟫_ℝ ^ 2 * R :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)
    _ = R * ‖x‖ ^ 2 := by rw [← Finset.sum_mul, b.sum_sq_inner_right]; ring

omit [CompleteSpace V] in
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
      ⟪b (.inl i), D (b (.inl j))⟫_ℝ := by
    rw [real_inner_comm]
    exact hD _ _
  have ht (i j : Fin d) : ⟪b (.inl j), D (b (.inr i))⟫_ℝ =
      ⟪b (.inl i), D (b (.inr j))⟫_ℝ := by
    rw [← hfe, real_inner_comm]
    exact hD _ _
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
        exact (Finset.add_sum_erase Finset.univ (fun j => |a j|) (Finset.mem_univ i)).symm
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

private theorem effect_repair {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d ⊕ Fin d) ℝ V)
    (J : V →L[ℝ] V) (hJ2 : ∀ x, J (J x) = -x)
    (hJstar : J.adjoint = -J) (hJe : ∀ i, J (b (.inl i)) = b (.inr i))
    (A : V →L[ℝ] V) (hA : A.IsPositive) (hAc : (1 - A).IsPositive)
    (ε : ℝ) (ha : AnchorErrors b J A ε) :
    (repair J A).IsPositive ∧ (1 - repair J A).IsPositive ∧ ‖repair J A‖ ≤ 1 ∧
    (∀ x, repair J A (J x) = J (repair J A x)) ∧
    ‖A - repair J A‖ ≤ min (1 / 2) ((2 * (d : ℝ) - 1) * ε) ∧
    (∀ x, ⟪J x, repair J A x⟫_ℝ = 0) ∧
    (∀ x, |weight A x - weight (repair J A) x| ≤
      min (1 / 2) ((2 * (d : ℝ) - 1) * ε) * ‖x‖ ^ 2) := by
  classical
  let C := phaseConjugate J A
  let D := A - C
  have hC : C.IsPositive := hA.adjoint_conj J
  have hunit : J.adjoint ∘L J = 1 := by
    ext x
    simp [hJstar, hJ2]
  have hCc : (1 - C).IsPositive := by
    have h := hAc.adjoint_conj J
    convert h using 1
    ext x
    simp only [C, phaseConjugate, comp_apply, sub_apply,
      one_apply_eq_self, map_sub]
    have hu := congrArg (fun T : V →L[ℝ] V => T x) hunit
    simp only [comp_apply, one_apply_eq_self] at hu
    rw [hu]
  have hD : D.IsSymmetric := hA.isSymmetric.sub hC.isSymmetric
  have hconj (x y : V) : ⟪x, C y⟫_ℝ = ⟪J x, A (J y)⟫_ℝ := by
    simp [C, phaseConjugate, adjoint_inner_right]
  have hanti (x y : V) : ⟪J x, D (J y)⟫_ℝ = -⟪x, D y⟫_ℝ := by
    simp only [D, sub_apply, inner_sub_right, hconj, hJ2, map_neg,
      inner_neg_left, inner_neg_right]
    ring
  have hJf (i : Fin d) : J (b (.inr i)) = -b (.inl i) := by
    rw [← hJe, hJ2]
  have hff (i j : Fin d) : ⟪b (.inr i), D (b (.inr j))⟫_ℝ =
      -⟪b (.inl i), D (b (.inl j))⟫_ℝ := by
    simpa [hJe] using hanti (b (.inl i)) (b (.inl j))
  have hfe (i j : Fin d) : ⟪b (.inr i), D (b (.inl j))⟫_ℝ =
      ⟪b (.inl i), D (b (.inr j))⟫_ℝ := by
    have h := hanti (b (.inl i)) (b (.inr j))
    simpa [hJe, hJf] using congrArg Neg.neg h
  have hq (x : V) : weight D x = weight A x - weight A (J x) := by
    simp only [weight, D, sub_apply, inner_sub_right, hconj]
  have rows := anchor_rows hd b D hD ε
    (by intro i; rw [hq]; exact ha.1 i)
    (by intro i j hij; rw [hq]; exact ha.2.1 i j hij)
    (by intro i j hij; rw [hq]; exact ha.2.2 i j hij) hff hfe
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hnorm : ‖D‖ ≤ (4 * (d : ℝ) - 2) * ε :=
    norm_le_of_rows b D hD _ (mul_nonneg (by linarith) rows.1) rows.2
  have hcap : ‖D‖ ≤ 1 := by
    apply norm_le_of_quadratic D hD 1 (by norm_num)
    intro x
    have h0 := hA.re_inner_nonneg_right x
    have h1 := hAc.re_inner_nonneg_right x
    have hc0 := hC.re_inner_nonneg_right x
    have hc1 := hCc.re_inner_nonneg_right x
    simp only [RCLike.re_to_real, sub_apply, one_apply_eq_self, inner_sub_right,
      real_inner_self_eq_norm_sq] at h0 h1 hc0 hc1
    simp only [weight, D, sub_apply, inner_sub_right, one_mul]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hdiff : A - repair J A = (1 / 2 : ℝ) • D := by
    dsimp [repair, D, C]
    module
  have herror : ‖A - repair J A‖ ≤ min (1 / 2) ((2 * (d : ℝ) - 1) * ε) := by
    rw [hdiff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact le_min (by linarith only [hcap]) (by nlinarith only [hnorm])
  have hE : (repair J A).IsPositive :=
    (hA.add hC).smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hEc : (1 - repair J A).IsPositive := by
    have h := (hAc.add hCc).smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1
    dsimp [repair, C]
    module
  have hcomm (x : V) : repair J A (J x) = J (repair J A x) := by
    simp [repair, phaseConjugate, hJstar, hJ2] <;> module
  have hEnorm : ‖repair J A‖ ≤ 1 := by
    apply norm_le_of_quadratic _ hE.isSymmetric 1 (by norm_num)
    intro x
    have h0 := hE.re_inner_nonneg_right x
    have h1 := hEc.re_inner_nonneg_right x
    simp only [RCLike.re_to_real, sub_apply, one_apply_eq_self, inner_sub_right,
      real_inner_self_eq_norm_sq] at h0 h1
    simp only [weight, abs_of_nonneg h0, one_mul]
    linarith
  have him (x : V) : ⟪J x, repair J A x⟫_ℝ = 0 := by
    have hs := hE.isSymmetric x (J x)
    change ⟪repair J A x, J x⟫_ℝ = ⟪x, repair J A (J x)⟫_ℝ at hs
    rw [hcomm, ← adjoint_inner_left J (repair J A x) x, hJstar] at hs
    simp only [neg_apply, inner_neg_left] at hs
    linarith only [hs, real_inner_comm (repair J A x) (J x)]
  refine ⟨hE, hEc, hEnorm, hcomm, herror, him, ?_⟩
  intro x
  calc
    _ = |⟪x, (A - repair J A) x⟫_ℝ| := by simp [weight, inner_sub_right]
    _ ≤ ‖x‖ * ‖(A - repair J A) x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A - repair J A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right herror (sq_nonneg ‖x‖)]

/-- Literal finite anchors give the Euclidean operator estimate for every real
effect. The same averaging map simultaneously preserves every finite menu.
Complex linearity is expressed by commutation with the supplied common J;
the vanishing imaginary readout identifies the source complex expectation.
-/
theorem finite_phase_anchor_repair {d : ℕ} (hd : 1 ≤ d)
    (b : OrthonormalBasis (Fin d ⊕ Fin d) ℝ V)
    (J : V →L[ℝ] V) (hJ2 : ∀ x, J (J x) = -x)
    (hJstar : J.adjoint = -J) (hJe : ∀ i, J (b (.inl i)) = b (.inr i)) :
    (∀ (A : V →L[ℝ] V), A.IsPositive → (1 - A).IsPositive →
      ∀ ε : ℝ, AnchorErrors b J A ε →
      (repair J A).IsPositive ∧ (1 - repair J A).IsPositive ∧ ‖repair J A‖ ≤ 1 ∧
      (∀ x, repair J A (J x) = J (repair J A x)) ∧
      ‖A - repair J A‖ ≤ min (1 / 2) ((2 * (d : ℝ) - 1) * ε) ∧
      (∀ x, ⟪J x, repair J A x⟫_ℝ = 0) ∧
      (∀ x, |weight A x - weight (repair J A) x| ≤
        min (1 / 2) ((2 * (d : ℝ) - 1) * ε) * ‖x‖ ^ 2)) ∧
    (∀ (ι : Type*) [Fintype ι] (menu : ι → V →L[ℝ] V),
      (∑ i, menu i) = 1 → (∑ i, repair J (menu i)) = 1) := by
  refine ⟨effect_repair hd b J hJ2 hJstar hJe, ?_⟩
  intro ι _ menu hm
  have hunit : J.adjoint ∘L J = 1 := by
    ext x
    simp [hJstar, hJ2]
  have hs : (∑ i, phaseConjugate J (menu i)) = 1 := by
    ext x
    simp only [sum_apply, phaseConjugate, comp_apply]
    rw [← map_sum]
    have h := congrArg (fun T : V →L[ℝ] V => T (J x)) hm
    simp only [sum_apply, one_apply_eq_self] at h
    rw [h]
    change (J.adjoint ∘L J) x = x
    rw [hunit]
    rfl
  simp only [repair, ← Finset.smul_sum, Finset.sum_add_distrib,
    hm, hs]
  module

#print axioms finite_phase_anchor_repair

end D5.S3.Quantum.Analysis.FinitePhaseAnchorStability
