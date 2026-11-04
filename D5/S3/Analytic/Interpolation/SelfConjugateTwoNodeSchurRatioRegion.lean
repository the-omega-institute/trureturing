/- GID: D5/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion
   generality: I
   mirror-B: D5/B/S3/Analytic/Interpolation/SelfConjugateTwoNodeSchurRatioRegion
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Exact regions and maximal disk for two-node self-conjugate Schur-ratio bounds. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation
  (statement_id: sha256:0db8847f194177b39d4133cf0557f6dce02ca1edeaf96dcf8f8ff837cb6be821)
Utility: none; universally quantified algebraic and analytic region characterizations across t >= 2.
Escape-witness summary:
- first_inequality_region (Theorem 4.1): unit-disk Lipschitz monotonicity of F, upper-cap bound on
  3/4 <= b^2, and mod-3 cube-root-of-unity expansion with t >= 10 lower envelope.
- largest_admissible_disk (Corollary 4.3): two-node selfConjugate classification, tangent SOS
  3*(1 - a)^2 - b^2 = (2*a - 3/2)^2 + (3/4 - (a^2 + b^2)), and t = 3 boundary witness.
- second_inequality_region (Theorem 5.1): Lipschitz reduction to hyperbola arc
  a_0 = sqrt(1 + b^2 / 3) - 1, recurrence polynomial bounds (t = 3..7), and t >= 8 norm decay.
Per-declaration proof_shape and consumer inventory:
- Defs (twoH, conjPair, negConjPair, F, inFirstSector, charPolyNegConj, charPolyConj,
  finTwoSymEquiv, omegaC, chi3): proof_shape: definition | consumer: reductions and theorems below.
- Bind-only helpers (sq_sqrt_three, finTwoSymEquiv_val, e_one_fin_two, conjPair_norm_sq,
  h_conjPair_norm_eq_abs_re): proof_shape: bind-only | consumer: h_eq_twoH, schurHook_zero_eq_h,
  Q_two_node_closed_form, first_inequality_iff_F_nonneg, F_nonneg_of_sector,
  largest_admissible_disk, hyperbola_arc_bound, second_inequality_region.
- Private content lemmas (twoH_succ, twoH_comm, twoH_sub_mul, twoH_rec, multiset_fin_two_card,
  h_eq_twoH, schurHook_zero_eq_h, choose_two_mul_two, lt_one_of_disk_ne_one, conjPair_norm_le_one,
  h_conjPair_eq_re, h_conjPair_norm_le, norm_pow_sub_pow_le, h_conjPair_lipschitz, F_anti_a,
  h_conjPair_mul_im_bound, F_nonneg_upper_cap, conj_omegaC, omegaC_pow_three, omegaC_pow_sub_conj,
  edge_h_expansion, sum_range_three_mul, choose_succ_mul_real, edge_F_small_beta, edge_F_large_beta,
  h_two_conjPair_re, F_three, F_nonneg_of_sector, selfConjugate_fin_two_iff, conjPair_h_rec,
  hyperbola_arc_bound, second_inequality_all_t): proof_shape: content | consumer: live proof paths.
- Public theorems (alternating_choose_twoH_eq -> Q_two_node_closed_form ->
  first_inequality_iff_F_nonneg -> first_inequality_region -> largest_admissible_disk; and
  second_inequality_region): proof_shape: content | consumer: chain above and module endpoints.
-/

import D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Exact Two-Node Self-Conjugate Schur-Ratio Regions

Exact semi-algebraic regions and maximal origin-centred disk for two-node self-conjugate
shifted Schur-ratio and hook-Schur inequalities across all degrees `t ≥ 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ComplexConjugate

namespace D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
open D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
  (selfConjugate e h schurHook Q)
noncomputable section

/-- Complete homogeneous symmetric polynomial `h_m(x, y)` in two variables. -/
def twoH {R : Type*} [CommRing R] (m : ℕ) (x y : R) : R :=
  ∑ i ∈ Finset.range (m + 1), x ^ i * y ^ (m - i)
/-- Two-node conjugate pair `(a + b i, a - b i)`. -/
def conjPair (a b : ℝ) : Fin 2 → ℂ :=
  ![(a : ℂ) + (b : ℂ) * Complex.I, (a : ℂ) - (b : ℂ) * Complex.I]
/-- Negated two-node conjugate pair `(-(a + b i), -(a - b i))`. -/
def negConjPair (a b : ℝ) : Fin 2 → ℂ :=
  ![-((a : ℂ) + (b : ℂ) * Complex.I), -((a : ℂ) - (b : ℂ) * Complex.I)]
/-- Real slack function `F_t(a, b) = t(t - 1)(1 - a) - t + Re h_{t-1}(a + b i, a - b i)`. -/
def F (t : ℕ) (a b : ℝ) : ℝ :=
  (t : ℝ) * ((t : ℝ) - 1) * (1 - a) - (t : ℝ) + (h (t - 1) (conjPair a b)).re
/-- Closed sector with vertex `-1`, bisected by `[-1, ∞)`, of half-opening angle `π / 3`. -/
def inFirstSector (z : Fin 2 → ℂ) : Prop := ∀ i, |(z i).im| ≤ Real.sqrt 3 * ((z i).re + 1)
/-- Real characteristic polynomial `(X + a)^2 + b^2` of `negConjPair a b`. -/
def charPolyNegConj (a b : ℝ) : Polynomial ℝ :=
  (Polynomial.X + Polynomial.C a) ^ 2 + Polynomial.C (b ^ 2)
/-- Real characteristic polynomial `(X - a)^2 + b^2` of `conjPair a b`. -/
def charPolyConj (a b : ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C a) ^ 2 + Polynomial.C (b ^ 2)

private theorem sq_sqrt_three : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private theorem twoH_succ {R : Type*} [CommRing R] (m : ℕ) (x y : R) :
    twoH (m + 1) x y = x * twoH m x y + y ^ (m + 1) := by
  unfold twoH; rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, Nat.sub_zero, one_mul, Nat.succ_sub_succ_eq_sub]
  exact congrArg (· + y ^ (m + 1)) (Finset.sum_congr rfl fun i _ => by rw [pow_succ']; ring)
private theorem twoH_comm {R : Type*} [CommRing R] (m : ℕ) (x y : R) :
    twoH m x y = twoH m y x := by
  unfold twoH; rw [← Finset.sum_range_reflect]; exact Finset.sum_congr rfl fun i hi => by
    simp only [Nat.succ_sub_one, Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
      mul_comm]
private theorem twoH_sub_mul {R : Type*} [CommRing R] (m : ℕ) (x y : R) :
    (x - y) * twoH m x y = x ^ (m + 1) - y ^ (m + 1) := by
  induction m with | zero => simp [twoH] | succ m ih => rw [twoH_succ]; linear_combination x * ih
private theorem twoH_rec {R : Type*} [CommRing R] (k : ℕ) (x y : R) :
    twoH (k + 2) x y = (x + y) * twoH (k + 1) x y - x * y * twoH k x y := by
  rw [twoH_succ (k + 1), twoH_succ k]; ring
private theorem multiset_fin_two_card (s : Multiset (Fin 2)) :
    Multiset.count (0 : Fin 2) s + Multiset.count (1 : Fin 2) s = Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp | cons a s ih => fin_cases a <;> simp [← ih] <;> omega
private def finTwoSymEquiv (d : ℕ) : Fin (d + 1) ≃ Sym (Fin 2) d where
  toFun i := ⟨Multiset.replicate i.val (0 : Fin 2) + Multiset.replicate (d - i.val) (1 : Fin 2),
    by simp [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]⟩
  invFun s := ⟨Multiset.count (0 : Fin 2) s.val,
    Nat.lt_succ_of_le ((Multiset.count_le_card (0 : Fin 2) s.val).trans_eq s.prop)⟩
  left_inv i := by ext; simp [Multiset.count_replicate]
  right_inv s := by
    apply Sym.ext; refine Multiset.ext.mpr fun a => ?_
    have hsum : Multiset.count (0 : Fin 2) (s : Multiset (Fin 2)) +
        Multiset.count (1 : Fin 2) (s : Multiset (Fin 2)) = d :=
      (multiset_fin_two_card s.val).trans s.prop
    (fin_cases a <;> simp [Multiset.count_replicate]); omega
private theorem finTwoSymEquiv_val (d : ℕ) (i : Fin (d + 1)) :
    (finTwoSymEquiv d i).val =
      Multiset.replicate i.val (0 : Fin 2) + Multiset.replicate (d - i.val) (1 : Fin 2) := rfl
private theorem h_eq_twoH (d : ℕ) (z : Fin 2 → ℂ) : h d z = twoH d (z 0) (z 1) := by
  unfold h twoH; rw [← Fin.sum_univ_eq_sum_range]
  refine (Fintype.sum_equiv (finTwoSymEquiv d)
    (fun i : Fin (d + 1) => z 0 ^ (i : ℕ) * z 1 ^ (d - (i : ℕ)))
    (fun s : Sym (Fin 2) d => (s.val.map z).prod) fun i => ?_).symm
  rw [finTwoSymEquiv_val]; simp
private theorem schurHook_zero_eq_h (d : ℕ) (z : Fin 2 → ℂ) :
    schurHook d 0 z = h (d + 1) z := by
  rw [h_eq_twoH, twoH_succ]; unfold schurHook
  simp only [Finset.powersetCard_zero, Finset.sum_singleton, Finset.notMem_empty,
    IsEmpty.forall_iff, implies_true, and_true, Finset.prod_empty, mul_one]
  rw [Fin.sum_univ_two]; refine congrArg₂ (· + ·) ?_ ?_
  · have hall : ∀ arm : Sym (Fin 2) d,
        (if ∀ x ∈ arm.val, (0 : Fin 2) ≤ x then z 0 * (arm.val.map z).prod else 0) =
          z 0 * (arm.val.map z).prod :=
      fun _ => ite_eq_left_iff.mpr fun h => absurd (fun x _ => Fin.zero_le x) h
    simp_rw [hall]; rw [← Finset.mul_sum]; exact congrArg (z 0 * ·) (h_eq_twoH d z)
  · rw [← (Fintype.sum_equiv (finTwoSymEquiv d)
      (fun i : Fin (d + 1) => if i = 0 then z 1 ^ (d + 1) else 0)
      (fun arm : Sym (Fin 2) d =>
        if ∀ x ∈ arm.val, (1 : Fin 2) ≤ x then z 1 * (arm.val.map z).prod else 0)
      fun i => ?_), Fintype.sum_ite_eq' 0]
    by_cases hi : i = 0
    · subst hi; simp only [↓reduceIte]
      have hall : ∀ x ∈ (finTwoSymEquiv d 0).val, (1 : Fin 2) ≤ x := by
        rw [finTwoSymEquiv_val]; intro x hx
        simp only [Fin.val_zero, Multiset.replicate_zero, zero_add, Nat.sub_zero,
          Multiset.mem_replicate] at hx; rw [hx.2]
      rw [ite_eq_left_iff.mpr fun h => absurd hall h, finTwoSymEquiv_val]; simp [pow_succ']
    · have hnot : ¬ ∀ x ∈ (finTwoSymEquiv d i).val, (1 : Fin 2) ≤ x := fun hall => by
        have hmem : (0 : Fin 2) ∈ (finTwoSymEquiv d i).val := by
          rw [finTwoSymEquiv_val]; exact Multiset.mem_add.mpr
            (Or.inl (Multiset.mem_replicate.mpr ⟨fun h => hi (Fin.ext h), rfl⟩))
        exact absurd (hall 0 hmem) (by decide)
      simp only [hi, hnot, ↓reduceIte]
private theorem e_one_fin_two (z : Fin 2 → ℂ) : e 1 z = z 0 + z 1 := by
  simp [e, Finset.powersetCard_one, Fin.sum_univ_two]
private theorem choose_two_mul_two (t : ℕ) (ht : 2 ≤ t) :
    (2 : ℝ) * (t.choose 2 : ℝ) = (t : ℝ) * ((t : ℝ) - 1) := by
  have hnat : 2 * t.choose 2 = t * (t - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self t))]
  simpa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ t)] using
    (congrArg Nat.cast hnat : (_ : ℝ) = _)
/-- Alternating binomial identity for two-variable complete homogeneous symmetric polynomials. -/
theorem alternating_choose_twoH_eq {R : Type*} [CommRing R] (t : ℕ) (x y : R) (ht : 2 ≤ t) :
    (∑ d ∈ Finset.range (t - 1),
      (-1 : R) ^ d * (t.choose (d + 2) : R) * twoH (d + 1) x y) =
      (t : R) - twoH (t - 1) (1 - x) (1 - y) := by
  induction t, ht using Nat.le_induction with
  | base => simp [twoH, Finset.sum_range_succ]; ring
  | succ t ht ih =>
    have ht1 : t - 1 + 1 = t := by omega
    have hrt : Finset.range t = Finset.range (t - 1 + 1) := congrArg Finset.range ht1.symm
    rw [Nat.add_sub_cancel t 1]
    trans ((∑ d ∈ Finset.range t, (-1 : R) ^ d * (t.choose (d + 2) : R) * twoH (d + 1) x y) +
      (∑ d ∈ Finset.range t, (-1 : R) ^ d * (t.choose (d + 1) : R) * (x * twoH d x y)) +
      (∑ d ∈ Finset.range t, (-1 : R) ^ d * (t.choose (d + 1) : R) * y ^ (d + 1)))
    · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ => by
        rw [show d + 2 = (d + 1) + 1 from rfl, Nat.choose_succ_succ, Nat.cast_add, twoH_succ]; ring
    trans (((t : R) - twoH (t - 1) (1 - x) (1 - y)) +
      ((t : R) * x - x * ((t : R) - twoH (t - 1) (1 - x) (1 - y))) + (1 - (1 - y) ^ t))
    · refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
      · rw [hrt, Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt (by omega : t < t - 1 + 2)]
        simp
      · rw [hrt, Finset.sum_range_succ']; have h0 : twoH 0 x y = 1 := by simp [twoH]
        simp only [pow_zero, zero_add, Nat.choose_one_right, one_mul, h0, mul_one]
        have htail : (∑ k ∈ Finset.range (t - 1),
            (-1 : R) ^ (k + 1) * (t.choose (k + 1 + 1) : R) * (x * twoH (k + 1) x y)) =
          -x * (∑ k ∈ Finset.range (t - 1), (-1 : R) ^ k * (t.choose (k + 2) : R) *
            twoH (k + 1) x y) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
        rw [htail, ih]; ring
      · have hbin := add_pow (-y) (1 : R) t
        rw [show (-y : R) + 1 = 1 - y by ring, Finset.sum_range_succ'] at hbin
        simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one] at hbin
        have hneg : (∑ d ∈ Finset.range t, (-y) ^ (d + 1) * (t.choose (d + 1) : R)) =
            -(∑ d ∈ Finset.range t, (-1 : R) ^ d * (t.choose (d + 1) : R) * y ^ (d + 1)) := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun d _ => by
            rw [show (-y : R) = (-1 : R) * y by ring, mul_pow, pow_succ]; ring
        rw [hneg] at hbin; linear_combination hbin
    · have hsucc := twoH_succ (t - 1) (1 - x) (1 - y); rw [ht1] at hsucc
      rw [Nat.cast_add, Nat.cast_one, hsucc]; ring
private theorem lt_one_of_disk_ne_one (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1) (hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1) : a < 1 := by
  by_contra hge
  exact hw (by simp [show a = 1 by nlinarith [sq_nonneg b], show b = 0 by nlinarith [sq_nonneg b]])
/-- Closed form of `Q_{t,2,1}(z + 1)` on negated conjugate pairs in the unit disk (`w ≠ 1`). -/
theorem Q_two_node_closed_form (t : ℕ) (a b : ℝ) (ht : 2 ≤ t)
    (hab : a ^ 2 + b ^ 2 ≤ 1) (hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1) :
    Q t 2 1 (negConjPair a b + 1) =
      ((t : ℂ) - h (t - 1) (conjPair a b)) / ((t : ℂ) * ((t : ℂ) - 1) * (1 - (a : ℂ))) ∧
      Q 2 2 1 (negConjPair a b + 1) = 1 := by
  have hmain : ∀ m : ℕ, 2 ≤ m → Q m 2 1 (negConjPair a b + 1) =
      ((m : ℂ) - h (m - 1) (conjPair a b)) / ((m : ℂ) * ((m : ℂ) - 1) * (1 - (a : ℂ))) := by
    intro m hm; let ζ : Fin 2 → ℂ := negConjPair a b + 1; unfold Q
    change (∑ d ∈ Finset.range (m - 2 + 1),
      (-1 : ℂ) ^ d * ((m.choose (2 + d) : ℂ) * schurHook d 0 ζ) / ((m.choose 2 : ℂ) * e 1 ζ)) = _
    rw [show m - 2 + 1 = m - 1 by omega, ← Finset.sum_div]; refine congrArg₂ (· / ·) ?_ ?_
    · trans (∑ d ∈ Finset.range (m - 1),
        (-1 : ℂ) ^ d * (m.choose (d + 2) : ℂ) * twoH (d + 1) (ζ 0) (ζ 1))
      · exact Finset.sum_congr rfl fun d _ => by
          rw [Nat.add_comm 2 d, schurHook_zero_eq_h, h_eq_twoH, mul_assoc]
      · rw [alternating_choose_twoH_eq m (ζ 0) (ζ 1) hm, h_eq_twoH]
        have hζ : ∀ i, 1 - ζ i = conjPair a b i := fun i => by
          fin_cases i <;> (simp only [ζ, Pi.add_apply, Pi.one_apply]; simp [negConjPair, conjPair])
        rw [hζ 0, hζ 1]
    · have he1 : e 1 ζ = 2 * (1 - (a : ℂ)) := by
        rw [e_one_fin_two]; simp only [ζ, Pi.add_apply, Pi.one_apply]; simp [negConjPair]; ring
      have hcC : (2 : ℂ) * (m.choose 2 : ℂ) = (m : ℂ) * ((m : ℂ) - 1) := by
        exact_mod_cast choose_two_mul_two m hm
      rw [he1]; linear_combination (1 - (a : ℂ)) * hcC
  refine ⟨hmain t ht, ?_⟩; rw [hmain 2 (by decide)]
  have ha1 := lt_one_of_disk_ne_one a b hab hw
  have hne : (1 : ℂ) - (a : ℂ) ≠ 0 := fun h0 => by
    have hre := congrArg Complex.re h0; simp at hre; linarith
  have hh1 : h 1 (conjPair a b) = 2 * (a : ℂ) := by
    rw [h_eq_twoH]; simp [twoH, Finset.sum_range_succ, conjPair]; ring
  simp only [Nat.reduceSub, Nat.cast_ofNat, hh1]
  rw [show (2 : ℂ) - 2 * (a : ℂ) = (2 : ℂ) * (2 - 1) * (1 - (a : ℂ)) by ring]
  exact div_self (mul_ne_zero (by norm_num) hne)
private theorem conjPair_norm_sq (a b : ℝ) (i : Fin 2) :
    ‖conjPair a b i‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm]; fin_cases i <;> simp [conjPair, Complex.normSq_apply] <;> ring
private theorem conjPair_norm_le_one (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) (i : Fin 2) :
    ‖conjPair a b i‖ ≤ 1 := by
  nlinarith [norm_nonneg (conjPair a b i), (conjPair_norm_sq a b i).symm ▸ hab]
private theorem h_conjPair_eq_re (m : ℕ) (a b : ℝ) :
    h m (conjPair a b) = ((h m (conjPair a b)).re : ℂ) := by
  refine (Complex.conj_eq_iff_re.mp ?_).symm; rw [h_eq_twoH]; unfold twoH; rw [map_sum]
  have hc0 : conj (conjPair a b 0) = conjPair a b 1 := by simp [conjPair]; ring
  simp only [map_mul, map_pow, hc0, show conj (conjPair a b 1) = conjPair a b 0 by simp [conjPair]]
  exact twoH_comm m (conjPair a b 1) (conjPair a b 0)
private theorem h_conjPair_norm_eq_abs_re (m : ℕ) (a b : ℝ) :
    ‖h m (conjPair a b)‖ = |(h m (conjPair a b)).re| := by
  (conv_lhs => rw [h_conjPair_eq_re m a b]); exact Complex.norm_real _
private theorem h_conjPair_norm_le (m : ℕ) (a b : ℝ) :
    ‖h m (conjPair a b)‖ ≤ ((m + 1 : ℕ) : ℝ) * ‖conjPair a b 0‖ ^ m := by
  rw [h_eq_twoH]; unfold twoH
  have hn1 : ‖conjPair a b 1‖ = ‖conjPair a b 0‖ := by
    nlinarith [norm_nonneg (conjPair a b 1), norm_nonneg (conjPair a b 0),
      (conjPair_norm_sq a b 1).trans (conjPair_norm_sq a b 0).symm]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl fun i hi => by
    rw [norm_mul, norm_pow, norm_pow, hn1, ← pow_add,
      Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))],
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
/-- Reduction of `‖Q_{t,2,1}(z + 1)‖ ≤ 1` to nonnegativity of the real slack `F_t(a, b)`. -/
theorem first_inequality_iff_F_nonneg (t : ℕ) (a b : ℝ) (ht : 2 ≤ t)
    (hab : a ^ 2 + b ^ 2 ≤ 1) (hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1) :
    ‖Q t 2 1 (negConjPair a b + 1)‖ ≤ 1 ↔ 0 ≤ F t a b := by
  rw [(Q_two_node_closed_form t a b ht hab hw).1, h_conjPair_eq_re]
  have ha1 := lt_one_of_disk_ne_one a b hab hw; have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hden_pos : 0 < (t : ℝ) * ((t : ℝ) - 1) * (1 - a) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hre_le : |(h (t - 1) (conjPair a b)).re| ≤ (t : ℝ) := by
    rw [← h_conjPair_norm_eq_abs_re]
    have hp := pow_le_one₀ (norm_nonneg _) (conjPair_norm_le_one a b hab 0) (n := t - 1)
    simpa [show t - 1 + 1 = t by omega] using
      (h_conjPair_norm_le (t - 1) a b).trans (mul_le_mul_of_nonneg_left hp (by positivity))
  have hnum_nn : 0 ≤ (t : ℝ) - (h (t - 1) (conjPair a b)).re := by linarith [(abs_le.mp hre_le).2]
  have hcast : (((t : ℂ) - ((h (t - 1) (conjPair a b)).re : ℂ)) /
      ((t : ℂ) * ((t : ℂ) - 1) * (1 - (a : ℂ)))) =
    ((((t : ℝ) - (h (t - 1) (conjPair a b)).re) /
      ((t : ℝ) * ((t : ℝ) - 1) * (1 - a)) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum_nn hden_pos.le),
    div_le_one hden_pos]; unfold F; constructor <;> intro hle <;> linarith
private theorem norm_pow_sub_pow_le (k : ℕ) (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x ^ k - y ^ k‖ ≤ (k : ℝ) * ‖x - y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hyk : ‖y ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg y) hy
    calc ‖x ^ (k + 1) - y ^ (k + 1)‖ = ‖x * (x ^ k - y ^ k) + (x - y) * y ^ k‖ :=
          congrArg norm (by ring)
      _ ≤ ‖x‖ * ‖x ^ k - y ^ k‖ + ‖x - y‖ * ‖y ^ k‖ :=
          (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ 1 * ((k : ℝ) * ‖x - y‖) + ‖x - y‖ * 1 :=
          add_le_add (mul_le_mul hx ih (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hyk (norm_nonneg _))
      _ = ((k + 1 : ℕ) : ℝ) * ‖x - y‖ := by push_cast; ring
private theorem h_conjPair_lipschitz (m : ℕ) (a₁ a₂ b : ℝ)
    (ha : a₁ ≤ a₂) (h1 : a₁ ^ 2 + b ^ 2 ≤ 1) (h2 : a₂ ^ 2 + b ^ 2 ≤ 1) :
    ‖h m (conjPair a₂ b) - h m (conjPair a₁ b)‖ ≤ ((m + 1 : ℕ) : ℝ) * (m : ℝ) * (a₂ - a₁) := by
  rw [h_eq_twoH, h_eq_twoH]; unfold twoH; rw [← Finset.sum_sub_distrib]
  have hd : ∀ j, ‖conjPair a₂ b j - conjPair a₁ b j‖ = a₂ - a₁ := fun j => by
    have hj : conjPair a₂ b j - conjPair a₁ b j = ((a₂ - a₁ : ℝ) : ℂ) := by
      fin_cases j <;> simp [conjPair]
    rw [hj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha)]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => (m : ℝ) * (a₂ - a₁))
    fun i hi => ?_).trans_eq ?_)
  · have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hvp : ‖conjPair a₂ b 1 ^ (m - i)‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (conjPair_norm_le_one a₂ b h2 1)
    have hup : ‖conjPair a₁ b 0 ^ i‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (conjPair_norm_le_one a₁ b h1 0)
    have hb0 : ‖conjPair a₂ b 0 ^ i - conjPair a₁ b 0 ^ i‖ ≤ (i : ℝ) * (a₂ - a₁) := by
      simpa only [hd 0] using norm_pow_sub_pow_le i _ _ (conjPair_norm_le_one a₂ b h2 0)
        (conjPair_norm_le_one a₁ b h1 0)
    have hb1 : ‖conjPair a₂ b 1 ^ (m - i) - conjPair a₁ b 1 ^ (m - i)‖ ≤
        ((m - i : ℕ) : ℝ) * (a₂ - a₁) := by
      simpa only [hd 1] using norm_pow_sub_pow_le (m - i) _ _ (conjPair_norm_le_one a₂ b h2 1)
        (conjPair_norm_le_one a₁ b h1 1)
    rw [show conjPair a₂ b 0 ^ i * conjPair a₂ b 1 ^ (m - i) -
        conjPair a₁ b 0 ^ i * conjPair a₁ b 1 ^ (m - i) =
      (conjPair a₂ b 0 ^ i - conjPair a₁ b 0 ^ i) * conjPair a₂ b 1 ^ (m - i) +
        conjPair a₁ b 0 ^ i * (conjPair a₂ b 1 ^ (m - i) - conjPair a₁ b 1 ^ (m - i)) by ring]
    refine ((norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])).trans ?_
    refine (add_le_add
      (mul_le_mul hb0 hvp (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ha)))
      (mul_le_mul hup hb1 (norm_nonneg _) zero_le_one)).trans_eq ?_
    rw [Nat.cast_sub him]; ring
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
private theorem F_anti_a (t : ℕ) (a₁ a₂ b : ℝ) (ht : 1 ≤ t)
    (ha : a₁ ≤ a₂) (h1 : a₁ ^ 2 + b ^ 2 ≤ 1) (h2 : a₂ ^ 2 + b ^ 2 ≤ 1) :
    F t a₂ b ≤ F t a₁ b := by
  have hlip := h_conjPair_lipschitz (t - 1) a₁ a₂ b ha h1 h2
  rw [show t - 1 + 1 = t by omega, Nat.cast_sub ht, Nat.cast_one] at hlip
  have hre0 : |(h (t - 1) (conjPair a₂ b)).re - (h (t - 1) (conjPair a₁ b)).re| ≤
      ‖h (t - 1) (conjPair a₂ b) - h (t - 1) (conjPair a₁ b)‖ := by
    simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm (h (t - 1) (conjPair a₂ b) - h (t - 1) (conjPair a₁ b))
  unfold F; linarith [(abs_le.mp (hre0.trans hlip)).2]
private theorem h_conjPair_mul_im_bound (t : ℕ) (a b : ℝ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 ≤ 1) : b * |(h (t - 1) (conjPair a b)).re| ≤ 1 := by
  rw [← h_conjPair_norm_eq_abs_re]
  have hid := twoH_sub_mul (t - 1) (conjPair a b 0) (conjPair a b 1)
  rw [show t - 1 + 1 = t by omega, ← h_eq_twoH] at hid
  have hdiff : conjPair a b 0 - conjPair a b 1 = (2 * (b : ℂ)) * Complex.I := by
    simp [conjPair]; ring
  have hlhs : ‖(conjPair a b 0 - conjPair a b 1) * h (t - 1) (conjPair a b)‖ =
      2 * b * ‖h (t - 1) (conjPair a b)‖ := by
    rw [norm_mul, hdiff, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  have hp0 := pow_le_one₀ (norm_nonneg _) (conjPair_norm_le_one a b hab 0) (n := t)
  have hp1 := pow_le_one₀ (norm_nonneg _) (conjPair_norm_le_one a b hab 1) (n := t)
  have hrhs : ‖conjPair a b 0 ^ t - conjPair a b 1 ^ t‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_; rw [norm_pow, norm_pow]; linarith
  rw [hid] at hlhs; linarith
private theorem F_nonneg_upper_cap (t : ℕ) (a b : ℝ) (ht : 4 ≤ t)
    (hb : 0 ≤ b) (hbcap : 3 / 4 ≤ b ^ 2) (hab : a ^ 2 + b ^ 2 ≤ 1) : 0 ≤ F t a b := by
  have ha_half : a ≤ 1 / 2 := by nlinarith
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (t : ℝ) * ((t : ℝ) - 1) * (1 / 2) ≤ (t : ℝ) * ((t : ℝ) - 1) * (1 - a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
  have hm : 2 ≤ (t : ℝ) * ((t : ℝ) - 1) * (1 - a) - (t : ℝ) := by nlinarith
  have him := h_conjPair_mul_im_bound t a b (by omega) hb hab
  have hre : -1 ≤ b * (h (t - 1) (conjPair a b)).re := by
    nlinarith [neg_abs_le (h (t - 1) (conjPair a b)).re]
  have hprod : 0 ≤ b * F t a b := by unfold F; nlinarith [show 1 ≤ 2 * b by nlinarith]
  nlinarith [show 0 < b by nlinarith]
private def omegaC : ℂ := (-1 : ℂ) / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I
private def chi3 (j : ℕ) : ℝ := if j % 3 = 1 then 1 else if j % 3 = 2 then -1 else 0
private theorem conj_omegaC : conj omegaC = (-1 : ℂ) / 2 - (Real.sqrt 3 : ℂ) / 2 * Complex.I := by
  unfold omegaC; simp [map_ofNat]; ring
private theorem omegaC_pow_three : omegaC ^ 3 = 1 := by
  unfold omegaC; have hs3 : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by exact_mod_cast sq_sqrt_three
  calc ((-1 : ℂ) / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I) ^ 3 =
        (-1 - 3 * ((Real.sqrt 3 : ℂ) ^ 2) * (Complex.I ^ 2) + (3 * (Real.sqrt 3 : ℂ) +
          ((Real.sqrt 3 : ℂ) ^ 2) * (Real.sqrt 3 : ℂ) * (Complex.I ^ 2)) * Complex.I) / 8 := by ring
    _ = 1 := by rw [hs3, Complex.I_sq]; norm_num
private theorem omegaC_pow_sub_conj (j : ℕ) :
    omegaC ^ j - (conj omegaC) ^ j = (chi3 j : ℂ) * ((Real.sqrt 3 : ℂ) * Complex.I) := by
  have hc3 : (conj omegaC) ^ 3 = 1 := by rw [← map_pow, omegaC_pow_three, map_one]
  conv_lhs => rw [(Nat.div_add_mod j 3).symm]
  simp only [pow_add, pow_mul, omegaC_pow_three, hc3, one_pow, one_mul]
  have hlt := Nat.mod_lt j (by decide : 0 < 3); unfold chi3; interval_cases (j % 3)
  · simp
  · rw [conj_omegaC]; unfold omegaC; simp; ring
  · simp only [Nat.reduceEqDiff, ↓reduceIte]; rw [conj_omegaC]; unfold omegaC; push_cast; ring
private theorem edge_h_expansion (t : ℕ) (β : ℝ) (ht : 1 ≤ t) (hβ0 : 0 < β) :
    (h (t - 1) (conjPair (1 - β / 2) (Real.sqrt 3 / 2 * β))).re =
      ∑ k ∈ Finset.range t, (t.choose (k + 1) : ℝ) * β ^ k * chi3 (k + 1) := by
  let a := 1 - β / 2; let b := Real.sqrt 3 / 2 * β
  have hw0 : conjPair a b 0 = 1 + (β : ℂ) * omegaC := by unfold conjPair omegaC; simp [a, b]; ring
  have hw1 : conjPair a b 1 = 1 + (β : ℂ) * conj omegaC := by
    rw [conj_omegaC]; unfold conjPair; simp [a, b]; ring
  have hid := twoH_sub_mul (t - 1) (conjPair a b 0) (conjPair a b 1)
  rw [show t - 1 + 1 = t by omega, ← h_eq_twoH, h_conjPair_eq_re] at hid
  have hdiff : conjPair a b 0 - conjPair a b 1 = (β : ℂ) * ((Real.sqrt 3 : ℂ) * Complex.I) := by
    simp [conjPair, a, b]; ring
  have hbin : conjPair a b 0 ^ t - conjPair a b 1 ^ t =
      (((∑ k ∈ Finset.range t, (t.choose (k + 1) : ℝ) * β ^ k * chi3 (k + 1)) : ℝ) : ℂ) *
        ((β : ℂ) * ((Real.sqrt 3 : ℂ) * Complex.I)) := by
    rw [hw0, hw1, add_comm (1 : ℂ) ((β : ℂ) * omegaC), add_comm (1 : ℂ) ((β : ℂ) * conj omegaC),
      add_pow, add_pow, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, sub_self, add_zero]
    push_cast; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, mul_pow, show (β : ℂ) ^ (k + 1) * omegaC ^ (k + 1) * (t.choose (k + 1) : ℂ) -
        (β : ℂ) ^ (k + 1) * (conj omegaC) ^ (k + 1) * (t.choose (k + 1) : ℂ) =
      (t.choose (k + 1) : ℂ) * (β : ℂ) ^ (k + 1) * (omegaC ^ (k + 1) - (conj omegaC) ^ (k + 1))
      by ring, omegaC_pow_sub_conj, pow_succ]; ring
  rw [hdiff, hbin] at hid
  have hfac : ((β : ℂ) * ((Real.sqrt 3 : ℂ) * Complex.I)) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hβ0.ne')
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))))
        Complex.I_ne_zero)
  exact Complex.ofReal_injective (mul_right_cancel₀ hfac ((mul_comm _ _).trans hid))
private theorem sum_range_three_mul (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (3 * n), f k) =
      ∑ m ∈ Finset.range n, (f (3 * m) + f (3 * m + 1) + f (3 * m + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring
private theorem choose_succ_mul_real (t k : ℕ) (hk : k ≤ t) :
    ((k + 1 : ℕ) : ℝ) * (t.choose (k + 1) : ℝ) = ((t - k : ℕ) : ℝ) * (t.choose k : ℝ) := by
  have hnat : t.choose (k + 1) * (k + 1) = t.choose k * (t - k) := by
    by_cases hlt : k < t
    · exact Nat.choose_succ_right_eq t k
    · obtain rfl : k = t := by omega
      simp
  simpa [Nat.cast_mul, mul_comm] using (congrArg Nat.cast hnat : (_ : ℝ) = _)
private theorem edge_F_small_beta (t : ℕ) (β : ℝ) (ht : 4 ≤ t)
    (hβ0 : 0 < β) (hsmall : ((t : ℝ) - 4) * β ≤ 5) :
    0 ≤ F t (1 - β / 2) (Real.sqrt 3 / 2 * β) := by
  unfold F; rw [edge_h_expansion t β (by omega) hβ0]
  let g (m : ℕ) : ℝ :=
    (t.choose (3 * m + 1) : ℝ) * β ^ (3 * m) - (t.choose (3 * m + 2) : ℝ) * β ^ (3 * m + 1)
  have hgrp : (∑ k ∈ Finset.range t, (t.choose (k + 1) : ℝ) * β ^ k * chi3 (k + 1)) =
      ∑ m ∈ Finset.range t, g m := by
    refine (Finset.sum_subset (Finset.range_mono (by omega : t ≤ 3 * t)) fun k _ hkt => ?_).trans ?_
    · have hge : t ≤ k := not_lt.mp fun h => hkt (Finset.mem_range.mpr h)
      simp [Nat.choose_eq_zero_of_lt (by omega : t < k + 1)]
    · rw [sum_range_three_mul]; refine Finset.sum_congr rfl fun m _ => ?_
      dsimp [g]; unfold chi3
      simp only [show (3 * m + 1) % 3 = 1 by omega, show (3 * m + 1 + 1) % 3 = 2 by omega,
        show (3 * m + 2 + 1) % 3 = 0 by omega, ↓reduceIte, Nat.reduceEqDiff,
        show 3 * m + 1 + 1 = 3 * m + 2 by omega]; ring
  have hg0 : g 0 = (t : ℝ) - (t : ℝ) * ((t : ℝ) - 1) * (β / 2) := by
    dsimp [g]; simp only [pow_zero, pow_one, Nat.choose_one_right, mul_one]
    linear_combination -(β / 2) * choose_two_mul_two t (by omega)
  rw [hgrp, show Finset.range t = Finset.range (t - 1 + 1) from
    congrArg Finset.range (by omega : t = t - 1 + 1), Finset.sum_range_succ', hg0,
    show (t : ℝ) * ((t : ℝ) - 1) * (1 - (1 - β / 2)) - (t : ℝ) +
      ((∑ k ∈ Finset.range (t - 1), g (k + 1)) + ((t : ℝ) - (t : ℝ) * ((t : ℝ) - 1) * (β / 2))) =
      ∑ k ∈ Finset.range (t - 1), g (k + 1) by ring]
  refine Finset.sum_nonneg fun r _ => ?_
  let m := r + 1; dsimp [g]; by_cases hle : 3 * m + 1 ≤ t
  · have habs := choose_succ_mul_real t (3 * m + 1) hle
    have h3m2 : (5 : ℝ) ≤ ((3 * m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 5 ≤ 3 * m + 2)
    have h4 : (4 : ℝ) ≤ ((3 * m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ 3 * m + 1)
    have hsub : ((t - (3 * m + 1) : ℕ) : ℝ) ≤ (t : ℝ) - 4 := by rw [Nat.cast_sub hle]; linarith
    refine nonneg_of_mul_nonneg_right ?_ (by positivity : (0 : ℝ) < ((3 * m + 2 : ℕ) : ℝ))
    have hnn := mul_nonneg (mul_nonneg (Nat.cast_nonneg (t.choose (3 * m + 1)))
      (pow_nonneg hβ0.le (3 * m)))
      (by nlinarith : 0 ≤ ((3 * m + 2 : ℕ) : ℝ) - ((t - (3 * m + 1) : ℕ) : ℝ) * β)
    refine hnn.trans_eq ?_
    dsimp [m]; rw [pow_succ, show 3 * (r + 1) + 2 = (3 * (r + 1) + 1) + 1 by omega]
    dsimp [m] at habs; linear_combination (β ^ (3 * (r + 1) + 1)) * habs
  · rw [Nat.choose_eq_zero_of_lt (by omega : t < 3 * (r + 1) + 1),
      Nat.choose_eq_zero_of_lt (by omega : t < 3 * (r + 1) + 2)]; simp
private theorem edge_F_large_beta (t : ℕ) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hlarge : 5 < ((t : ℝ) - 4) * β) :
    0 ≤ F t (1 - β / 2) (Real.sqrt 3 / 2 * β) := by
  have ht10 : 10 ≤ t := by
    by_contra hlt; nlinarith [show (t : ℝ) ≤ 9 by exact_mod_cast (by omega : t ≤ 9)]
  have htR : (10 : ℝ) ≤ t := by exact_mod_cast ht10
  have hs3_ge : 1 ≤ Real.sqrt 3 := by nlinarith [sq_sqrt_three, Real.sqrt_nonneg 3]
  have hdisk : (1 - β / 2) ^ 2 + (Real.sqrt 3 / 2 * β) ^ 2 ≤ 1 := by
    nlinarith [show (Real.sqrt 3 / 2 * β) ^ 2 = 3 / 4 * β ^ 2 by
      rw [mul_pow, div_pow, sq_sqrt_three]; ring]
  let H := (h (t - 1) (conjPair (1 - β / 2) (Real.sqrt 3 / 2 * β))).re
  have him := h_conjPair_mul_im_bound t (1 - β / 2) (Real.sqrt 3 / 2 * β) (by omega)
    (by positivity) hdisk
  have hre_lower : -2 ≤ Real.sqrt 3 * β * H := by
    linarith [mul_le_mul_of_nonneg_left (neg_abs_le H) (by positivity : 0 ≤ Real.sqrt 3 * β)]
  have hfac_mul : 3 * ((t : ℝ) - 4) < ((t : ℝ) - 4) * (((t : ℝ) - 1) * β - 2) := by
    nlinarith
  have hprod : 5 * (3 / 2) < ((t : ℝ) * β) * (((t : ℝ) - 1) / 2 * β - 1) :=
    mul_lt_mul'' (by nlinarith : 5 < (t : ℝ) * β) (by nlinarith) (by positivity) (by positivity)
  have hscaled : 0 < Real.sqrt 3 * β * F t (1 - β / 2) (Real.sqrt 3 / 2 * β) := by
    unfold F; change 0 < Real.sqrt 3 * β * (_ + H); nlinarith
  nlinarith [show 0 < Real.sqrt 3 * β by positivity]
private theorem h_two_conjPair_re (a b : ℝ) : (h 2 (conjPair a b)).re = 3 * a ^ 2 - b ^ 2 := by
  rw [h_eq_twoH]; simp [twoH, Finset.sum_range_succ, conjPair, sq]; ring
private theorem F_three (a b : ℝ) : F 3 a b = 3 * (1 - a) ^ 2 - b ^ 2 := by
  unfold F; change (3 : ℝ) * (3 - 1) * (1 - a) - 3 + (h 2 (conjPair a b)).re = _
  rw [h_two_conjPair_re]; ring
private theorem F_nonneg_of_sector (t : ℕ) (a b : ℝ) (ht : 2 ≤ t)
    (hab : a ^ 2 + b ^ 2 ≤ 1) (hsec : b ^ 2 ≤ 3 * (1 - a) ^ 2) : 0 ≤ F t a b := by
  rcases eq_or_lt_of_le ht with rfl | ht3
  · have h2 : F 2 a b = 0 := by
      unfold F; rw [h_eq_twoH]; simp [twoH, Finset.sum_range_succ, conjPair]; ring
    linarith
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt ht3) with rfl | ht4
  · linarith [F_three a b]
  have ht4' : 4 ≤ t := Nat.succ_le_of_lt ht4
  wlog hb : 0 ≤ b generalizing b
  · have hsym : F t a (-b) = F t a b := by
      unfold F; rw [h_eq_twoH, h_eq_twoH]
      have h0 : conjPair a (-b) 0 = conjPair a b 1 := by simp [conjPair]; ring
      rw [h0, show conjPair a (-b) 1 = conjPair a b 0 by simp [conjPair], twoH_comm]
    rw [← hsym]; exact this (-b) (by simpa using hab) (by simpa using hsec) (by linarith)
  by_cases hcap : 3 / 4 ≤ b ^ 2
  · exact F_nonneg_upper_cap t a b ht4' hb hcap hab
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · have hanti := F_anti_a t a 1 0 (by omega) (by nlinarith) hab (by norm_num)
      have hf10 : F t 1 0 = 0 := by
        unfold F; rw [h_eq_twoH]
        have h11 : twoH (t - 1) (conjPair 1 0 0) (conjPair 1 0 1) = (t : ℂ) := by
          unfold twoH; simp [conjPair, show t - 1 + 1 = t by omega]
        rw [h11]; simp
      linarith
    · let β := 2 * b / Real.sqrt 3
      have hs3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      have hβ0 : 0 < β := by positivity
      have hb_eq : b = Real.sqrt 3 / 2 * β := by dsimp [β]; field_simp [hs3_pos.ne']
      have hβ_sq : β ^ 2 ≤ 1 := by
        have : β ^ 2 * 3 = 4 * b ^ 2 := by dsimp [β]; rw [div_pow, sq_sqrt_three]; ring
        linarith
      have hb2_eq : b ^ 2 = 3 / 4 * β ^ 2 := by rw [hb_eq, mul_pow, div_pow, sq_sqrt_three]; ring
      have hanti := F_anti_a t a (1 - β / 2) b (by omega) (by nlinarith [show a ≤ 1 by nlinarith])
        hab (by nlinarith)
      have hedge : 0 ≤ F t (1 - β / 2) (Real.sqrt 3 / 2 * β) :=
        if hs : ((t : ℝ) - 4) * β ≤ 5 then edge_F_small_beta t β ht4' hβ0 hs
        else edge_F_large_beta t β hβ0 (by nlinarith) (lt_of_not_ge hs)
      rw [hb_eq] at hanti ⊢; exact hedge.trans hanti
/-- Exact characterization of the two-node self-conjugate region in the closed unit disk
on which `‖Q_{t,2,1}(z + 1)‖ ≤ 1` holds for all degrees `t ≥ 2`. -/
theorem first_inequality_region (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1) (hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1) :
    (charPolyNegConj a b).map (algebraMap ℝ ℂ) =
      (∏ i : Fin 2, (Polynomial.X - Polynomial.C (negConjPair a b i))) ∧
    ((∀ t : ℕ, 2 ≤ t → ‖Q t 2 1 (negConjPair a b + 1)‖ ≤ 1) ↔
      ‖Q 3 2 1 (negConjPair a b + 1)‖ ≤ 1) ∧
    (‖Q 3 2 1 (negConjPair a b + 1)‖ ≤ 1 ↔ b ^ 2 ≤ 3 * (1 - a) ^ 2) ∧
    (b ^ 2 ≤ 3 * (1 - a) ^ 2 ↔ inFirstSector (negConjPair a b)) ∧
    (b ^ 2 ≤ 3 * (1 - a) ^ 2 ↔
      (charPolyNegConj a b).eval (-1) ≤ ((charPolyNegConj a b).derivative.eval (-1)) ^ 2) := by
  have hQ3 : ‖Q 3 2 1 (negConjPair a b + 1)‖ ≤ 1 ↔ b ^ 2 ≤ 3 * (1 - a) ^ 2 := by
    rw [first_inequality_iff_F_nonneg 3 a b (by decide) hab hw, F_three]
    constructor <;> intro hle <;> linarith
  refine ⟨?_, ⟨fun hall => hall 3 (by decide), fun h3 t ht =>
    (first_inequality_iff_F_nonneg t a b ht hab hw).mpr
      (F_nonneg_of_sector t a b ht hab (hQ3.mp h3))⟩, hQ3, ?_, ?_⟩
  · have halg : ∀ x : ℝ, (algebraMap ℝ ℂ) x = (x : ℂ) := fun _ => rfl
    have hb2 : Polynomial.C ((b : ℂ) ^ 2) = -(Polynomial.C ((b : ℂ) * Complex.I) ^ 2) := by
      rw [← Polynomial.C_pow, mul_pow, Complex.I_sq, ← Polynomial.C_neg]; ring_nf
    rw [Fin.prod_univ_two]
    simp only [charPolyNegConj, negConjPair, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, halg, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.ofReal_pow, hb2, map_neg, map_add, map_sub]; ring
  · unfold inFirstSector
    have hs3_nn : 0 ≤ Real.sqrt 3 * (1 - a) := mul_nonneg (Real.sqrt_nonneg 3) (by nlinarith)
    have hi_iff : ∀ i : Fin 2,
        |(negConjPair a b i).im| ≤ Real.sqrt 3 * ((negConjPair a b i).re + 1) ↔
          |b| ≤ Real.sqrt 3 * (1 - a) := fun i => by
      fin_cases i <;> simp [negConjPair, sub_eq_add_neg, add_comm]
    simp_rw [hi_iff]
    have hsq_eq : (Real.sqrt 3 * (1 - a)) ^ 2 = 3 * (1 - a) ^ 2 := by rw [mul_pow, sq_sqrt_three]
    refine ⟨fun hle _ => ?_, fun hall => ?_⟩
    · have habs_sq : |b| ^ 2 ≤ (Real.sqrt 3 * (1 - a)) ^ 2 := by rwa [sq_abs, hsq_eq]
      nlinarith [abs_nonneg b]
    · have habs_sq := pow_le_pow_left₀ (abs_nonneg b) (hall 0) 2; rwa [sq_abs, hsq_eq] at habs_sq
  · have hev : (charPolyNegConj a b).eval (-1) = (1 - a) ^ 2 + b ^ 2 := by
      simp [charPolyNegConj]; ring
    have hder : (charPolyNegConj a b).derivative.eval (-1) = -2 * (1 - a) := by
      simp [charPolyNegConj, sq, Polynomial.derivative_add, Polynomial.derivative_mul]; ring
    rw [hev, hder]; constructor <;> intro hle <;> nlinarith
private theorem selfConjugate_fin_two_iff (z : Fin 2 → ℂ) :
    selfConjugate z ↔ z 1 = conj (z 0) := by
  classical
  refine ⟨fun hsc => ?_, fun hz1 => ⟨fun i _ => ?_, fun x => ?_⟩⟩
  · by_cases him : (z 0).im = 0
    · have hz0 : z 0 = ((z 0).re : ℂ) := Complex.ext (by simp) (by simp [him])
      let S := (Finset.univ : Finset (Fin 2)).filter fun i => z i = ((z 0).re : ℂ)
      have hpos : 0 < S.card :=
        Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz0⟩⟩
      have hle : S.card ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      obtain ⟨k, hk⟩ := hsc.2 (z 0).re; change S.card = k + k at hk
      have hall : S = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by simp [show S.card = 2 by omega])
      exact ((Finset.mem_filter.mp (hall ▸ Finset.mem_univ (1 : Fin 2))).2).trans
        ((congrArg conj hz0).trans (Complex.conj_ofReal _)).symm
    · obtain ⟨j, hj⟩ := hsc.1 0 him; fin_cases j
      · have h0im := congrArg Complex.im hj; simp at h0im; exact False.elim (him (by linarith))
      · exact hj
  · fin_cases i
    · exact ⟨1, hz1⟩
    · dsimp; exact ⟨0, by rw [hz1, Complex.conj_conj]⟩
  · by_cases hx : z 0 = (x : ℂ)
    · have h1 : z 1 = (x : ℂ) := by rw [hz1, hx, Complex.conj_ofReal]
      rw [show (Finset.univ.filter fun i : Fin 2 => z i = (x : ℂ)) = Finset.univ by
        ext i; fin_cases i <;> simp [hx, h1]]; exact ⟨1, by simp⟩
    · have h1 : z 1 ≠ (x : ℂ) := fun h1eq => hx (by simpa [hz1] using congrArg conj h1eq)
      rw [show (Finset.univ.filter fun i : Fin 2 => z i = (x : ℂ)) = ∅ by
        ext i; fin_cases i <;> simp [hx, h1]]; exact ⟨0, rfl⟩
/-- The largest origin-centred closed disk (`0 < ρ ≤ 1`) on which `‖Q_{t,2,1}(z + 1)‖ ≤ 1`
holds for all `t ≥ 2` and all two-node self-conjugate `z ≠ (-1, -1)` has radius `ρ = √3 / 2`. -/
theorem largest_admissible_disk (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (∀ (t : ℕ) (z : Fin 2 → ℂ),
      2 ≤ t → selfConjugate z → (∀ i, ‖z i‖ ≤ ρ) → z ≠ ![(-1 : ℂ), -1] →
        ‖Q t 2 1 (z + 1)‖ ≤ 1) ↔
      ρ ≤ Real.sqrt 3 / 2 := by
  constructor
  · intro hall; by_contra hgt; have hρ_gt : Real.sqrt 3 / 2 < ρ := lt_of_not_ge hgt
    let a := Real.sqrt 3 / 2 * ρ; let b := (1 / 2 : ℝ) * ρ; let z := negConjPair a b
    have hsc : selfConjugate z := by
      rw [selfConjugate_fin_two_iff]; simp [z, negConjPair, sub_eq_add_neg]
    have hnorm_ab : a ^ 2 + b ^ 2 = ρ ^ 2 := by
      dsimp [a, b]; rw [mul_pow, mul_pow, div_pow, sq_sqrt_three]; ring
    have hdisk_ρ : ∀ i : Fin 2, ‖z i‖ ≤ ρ := fun i => by
      have hneg : z i = -conjPair a b i := by fin_cases i <;> simp [z, negConjPair, conjPair]
      nlinarith [norm_nonneg (z i), show ‖z i‖ ^ 2 = ρ ^ 2 by
        rw [hneg, norm_neg, conjPair_norm_sq, hnorm_ab]]
    have hab1 : a ^ 2 + b ^ 2 ≤ 1 := by rw [hnorm_ab]; nlinarith
    have hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1 := fun heq => by
      have := congrArg Complex.im heq; simp [b] at this; linarith
    have hzne : z ≠ ![(-1 : ℂ), -1] := fun heq => by
      have := congrArg Complex.im (congrFun heq 0); simp [z, negConjPair, b] at this; linarith
    have hsec := (first_inequality_region a b hab1 hw).2.2.1.mp
      (hall 3 z (by decide) hsc hdisk_ρ hzne)
    have ha_lt1 := lt_one_of_disk_ne_one a b hab1 hw
    have hsq : b ^ 2 ≤ (Real.sqrt 3 * (1 - a)) ^ 2 := by rwa [mul_pow (Real.sqrt 3), sq_sqrt_three]
    have hr_pos : 0 < Real.sqrt 3 * (1 - a) :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (by linarith)
    have hb_le : b ≤ Real.sqrt 3 * (1 - a) := by nlinarith [show 0 < b by dsimp [b]; linarith]
    rw [show Real.sqrt 3 * (1 - a) = Real.sqrt 3 - 3 / 2 * ρ by
      dsimp [a]; linear_combination -(ρ / 2) * sq_sqrt_three] at hb_le
    dsimp [b] at hb_le; linarith
  · intro hρ_le t z ht hsc hdisk hzne
    have hz1 := (selfConjugate_fin_two_iff z).mp hsc; let a := -(z 0).re; let b := -(z 0).im
    have hzeq : z = negConjPair a b := by
      ext i; fin_cases i <;> apply Complex.ext <;> simp [negConjPair, a, b, hz1]
    have hab_ρ : a ^ 2 + b ^ 2 ≤ ρ ^ 2 := by
      have h0 : ‖z 0‖ ^ 2 = a ^ 2 + b ^ 2 := by
        rw [Complex.sq_norm]; simp [Complex.normSq_apply, a, b]; ring
      linarith [pow_le_pow_left₀ (norm_nonneg _) (hdisk 0) 2]
    have hab_34 : a ^ 2 + b ^ 2 ≤ 3 / 4 := by
      have := pow_le_pow_left₀ hρ0.le hρ_le 2; rw [div_pow, sq_sqrt_three] at this; linarith
    have hab1 : a ^ 2 + b ^ 2 ≤ 1 := by linarith
    have hw : (a : ℂ) + (b : ℂ) * Complex.I ≠ 1 := fun heq => hzne (by
      have hre : a = 1 := by simpa using congrArg Complex.re heq
      have him : b = 0 := by simpa using congrArg Complex.im heq
      rw [hzeq]; ext i; fin_cases i <;> simp [negConjPair, hre, him])
    have hsec : b ^ 2 ≤ 3 * (1 - a) ^ 2 := by
      nlinarith [sq_nonneg (2 * a - 3 / 2),
        show 3 * (1 - a) ^ 2 - b ^ 2 = (2 * a - 3 / 2) ^ 2 + (3 / 4 - (a ^ 2 + b ^ 2)) by ring]
    rw [hzeq]; have hreg := first_inequality_region a b hab1 hw
    exact hreg.2.1.mpr (hreg.2.2.1.mpr hsec) t ht
private theorem conjPair_h_rec (a b : ℝ) :
    (h 0 (conjPair a b)).re = 1 ∧ (h 1 (conjPair a b)).re = 2 * a ∧
    ∀ k : ℕ, (h (k + 2) (conjPair a b)).re =
      2 * a * (h (k + 1) (conjPair a b)).re - (a ^ 2 + b ^ 2) * (h k (conjPair a b)).re := by
  refine ⟨by rw [h_eq_twoH]; simp [twoH], ?_, fun k => ?_⟩
  · rw [h_eq_twoH]; simp [twoH, Finset.sum_range_succ, conjPair]; ring
  · have hid := twoH_rec k (conjPair a b 0) (conjPair a b 1)
    rw [← h_eq_twoH, ← h_eq_twoH, ← h_eq_twoH] at hid
    let s : ℝ := 2 * a; let p : ℝ := a ^ 2 + b ^ 2
    have hsum : conjPair a b 0 + conjPair a b 1 = (s : ℂ) := by simp [conjPair, s]; ring
    have hprod : conjPair a b 0 * conjPair a b 1 = (p : ℂ) := by
      simp only [conjPair, p, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.ofReal_add, Complex.ofReal_pow]
      linear_combination -(b : ℂ) ^ 2 * Complex.I_sq
    rw [hsum, hprod] at hid
    simpa only [Complex.sub_re, show ∀ (r : ℝ) (w : ℂ), ((r : ℂ) * w).re = r * w.re by simp,
      s, p] using congrArg Complex.re hid
private theorem hyperbola_arc_bound (t : ℕ) (c b : ℝ) (ht : 3 ≤ t)
    (hc0 : 0 ≤ c) (hc4 : c ≤ 1 / 4) (harc : b ^ 2 = 3 * c ^ 2 + 6 * c)
    (hdisk : 4 * c ^ 2 + 6 * c ≤ 1) :
    ‖h (t - 1) (conjPair c b)‖ ≤ (t : ℝ) * ((t : ℝ) - 1) * c := by
  by_cases ht8 : 8 ≤ t
  · have hnorm_le := h_conjPair_norm_le (t - 1) c b; rw [show t - 1 + 1 = t by omega] at hnorm_le
    have hw_sq : ‖conjPair c b 0‖ ^ 2 = 4 * c ^ 2 + 6 * c := by rw [conjPair_norm_sq, harc]; ring
    have hw1 : ‖conjPair c b 0‖ ≤ 1 := by
      nlinarith [norm_nonneg (conjPair c b 0), hw_sq.symm ▸ hdisk]
    have hpow : ‖conjPair c b 0‖ ^ (t - 1) ≤ 4 * c ^ 2 + 6 * c := by
      rw [show t - 1 = 2 + (t - 3) by omega, pow_add, hw_sq]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hw1) (by positivity)).trans_eq
        (mul_one _)
    have htR : (8 : ℝ) ≤ t := by exact_mod_cast ht8
    have h7 : 4 * c ^ 2 + 6 * c ≤ 7 * c := by nlinarith
    calc ‖h (t - 1) (conjPair c b)‖ ≤ (t : ℝ) * ‖conjPair c b 0‖ ^ (t - 1) := hnorm_le
      _ ≤ (t : ℝ) * (4 * c ^ 2 + 6 * c) := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ ≤ (t : ℝ) * 7 * c := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h7 (Nat.cast_nonneg _)
      _ ≤ (t : ℝ) * ((t : ℝ) - 1) * c := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)) hc0
  · rw [h_conjPair_norm_eq_abs_re]; obtain ⟨h0, h1, hrec⟩ := conjPair_h_rec c b
    have hr2 : c ^ 2 + b ^ 2 = 4 * c ^ 2 + 6 * c := by linarith
    have hH2 : (h 2 (conjPair c b)).re = -6 * c := by
      have := hrec 0; rw [hr2, h1, h0] at this; linarith
    have hH3 : (h 3 (conjPair c b)).re = -8 * c ^ 3 - 24 * c ^ 2 := by
      have := hrec 1; rw [hr2, hH2, h1] at this; linear_combination this
    have hH4 : (h 4 (conjPair c b)).re = -16 * c ^ 4 - 24 * c ^ 3 + 36 * c ^ 2 := by
      have := hrec 2; rw [hr2, hH3, hH2] at this; linear_combination this
    have hH5 : (h 5 (conjPair c b)).re = 96 * c ^ 4 + 216 * c ^ 3 := by
      have := hrec 3; rw [hr2, hH4, hH3] at this; linear_combination this
    have hH6 : (h 6 (conjPair c b)).re = 64 * c ^ 6 + 384 * c ^ 5 + 432 * c ^ 4 - 216 * c ^ 3 := by
      have := hrec 4; rw [hr2, hH5, hH4] at this; linear_combination this
    have hp : ∀ k, 0 ≤ c ^ k := pow_nonneg hc0
    have hc2 : c ^ 2 ≤ c / 4 := by nlinarith
    have hc3 : c ^ 3 ≤ c / 16 := by nlinarith [hp 2]
    have hc4' : c ^ 4 ≤ c / 64 := by nlinarith [hp 3]
    have hc5 : c ^ 5 ≤ c / 256 := by nlinarith [hp 4]
    have hc6 : c ^ 6 ≤ c / 1024 := by nlinarith [hp 5]
    have ht7 : t ≤ 7 := by omega
    interval_cases t <;> simp only [Nat.reduceSub, hH2, hH3, hH4, hH5, hH6, Nat.cast_ofNat] <;>
      exact abs_le.mpr ⟨by linarith [hp 2, hp 3, hp 4, hp 5, hp 6],
        by linarith [hp 2, hp 3, hp 4, hp 5, hp 6]⟩
private theorem second_inequality_all_t (t : ℕ) (a b : ℝ) (ht : 3 ≤ t)
    (ha : 0 ≤ a) (hab : a ^ 2 + b ^ 2 ≤ 1) (hreg : b ^ 2 ≤ 3 * a ^ 2 + 6 * a) :
    ‖h (t - 1) (conjPair a b)‖ ≤ (t : ℝ) * ((t : ℝ) - 1) * a := by
  let a₀ := Real.sqrt (1 + b ^ 2 / 3) - 1
  have ha₀_nn : 0 ≤ a₀ := by
    have : 1 ≤ Real.sqrt (1 + b ^ 2 / 3) := by
      simpa using Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b] : (1 : ℝ) ≤ 1 + b ^ 2 / 3)
    dsimp [a₀]; linarith
  have harc : b ^ 2 = 3 * a₀ ^ 2 + 6 * a₀ := by
    have : (a₀ + 1) ^ 2 = 1 + b ^ 2 / 3 := by
      dsimp [a₀]; rw [sub_add_cancel]; exact Real.sq_sqrt (by positivity)
    linarith
  have ha₀_le_a : a₀ ≤ a := by nlinarith [show (a₀ + 1) ^ 2 ≤ (a + 1) ^ 2 by linarith]
  have hlip := h_conjPair_lipschitz (t - 1) a₀ a b ha₀_le_a (by nlinarith) hab
  rw [show t - 1 + 1 = t by omega, Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one] at hlip
  have harc_bnd := hyperbola_arc_bound t a₀ b ht ha₀_nn (by nlinarith) harc (by nlinarith)
  linarith [show ‖h (t - 1) (conjPair a b)‖ ≤
      ‖h (t - 1) (conjPair a₀ b)‖ + ‖h (t - 1) (conjPair a b) - h (t - 1) (conjPair a₀ b)‖ by
    simpa using norm_add_le (h (t - 1) (conjPair a₀ b))
      (h (t - 1) (conjPair a b) - h (t - 1) (conjPair a₀ b))]
/-- Exact characterization of the two-node self-conjugate region in `{z ∈ 𝔻^2 : Re z ≥ 0}`
on which `‖s_{(t-2|0)}(z)‖ ≤ C(t, 2) ‖e_1(z)‖` holds for all degrees `t ≥ 2`. -/
theorem second_inequality_region (a b : ℝ) (ha : 0 ≤ a) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (charPolyConj a b).map (algebraMap ℝ ℂ) =
      (∏ i : Fin 2, (Polynomial.X - Polynomial.C (conjPair a b i))) ∧
    (∀ t : ℕ, 2 ≤ t →
      (‖schurHook (t - 2) 0 (conjPair a b)‖ ≤ (Nat.choose t 2 : ℝ) * ‖e 1 (conjPair a b)‖ ↔
        ‖h (t - 1) (conjPair a b)‖ ≤ (t : ℝ) * ((t : ℝ) - 1) * a)) ∧
    ‖schurHook 0 0 (conjPair a b)‖ = (Nat.choose 2 2 : ℝ) * ‖e 1 (conjPair a b)‖ ∧
    ‖h 1 (conjPair a b)‖ = 2 * a ∧
    ((∀ t : ℕ, 2 ≤ t →
        ‖schurHook (t - 2) 0 (conjPair a b)‖ ≤ (Nat.choose t 2 : ℝ) * ‖e 1 (conjPair a b)‖) ↔
      ‖schurHook 1 0 (conjPair a b)‖ ≤ (Nat.choose 3 2 : ℝ) * ‖e 1 (conjPair a b)‖) ∧
    (‖schurHook 1 0 (conjPair a b)‖ ≤ (Nat.choose 3 2 : ℝ) * ‖e 1 (conjPair a b)‖ ↔
      b ^ 2 ≤ 3 * a ^ 2 + 6 * a) ∧
    (b ^ 2 ≤ 3 * a ^ 2 + 6 * a ↔
      (charPolyConj a b).eval 0 ≤
        ((charPolyConj a b).derivative.eval 0) ^ 2 -
          3 * ((charPolyConj a b).derivative.eval 0)) := by
  have he1_norm : ‖e 1 (conjPair a b)‖ = 2 * a := by
    rw [e_one_fin_two, show conjPair a b 0 + conjPair a b 1 = ((2 * a : ℝ) : ℂ) by
      simp [conjPair]; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hh1_norm : ‖h 1 (conjPair a b)‖ = 2 * a := by
    rw [h_eq_twoH, show twoH 1 (conjPair a b 0) (conjPair a b 1) = ((2 * a : ℝ) : ℂ) by
      simp [twoH, Finset.sum_range_succ, conjPair]; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hred : ∀ t : ℕ, 2 ≤ t →
      (‖schurHook (t - 2) 0 (conjPair a b)‖ ≤ (Nat.choose t 2 : ℝ) * ‖e 1 (conjPair a b)‖ ↔
        ‖h (t - 1) (conjPair a b)‖ ≤ (t : ℝ) * ((t : ℝ) - 1) * a) := fun t ht => by
    rw [schurHook_zero_eq_h, show t - 2 + 1 = t - 1 by omega, he1_norm,
      show (Nat.choose t 2 : ℝ) * (2 * a) = (t : ℝ) * ((t : ℝ) - 1) * a by
        linear_combination a * choose_two_mul_two t ht]
  have ht3_iff : ‖schurHook 1 0 (conjPair a b)‖ ≤ (Nat.choose 3 2 : ℝ) * ‖e 1 (conjPair a b)‖ ↔
      b ^ 2 ≤ 3 * a ^ 2 + 6 * a := by
    have hr3 := hred 3 (by decide); simp only [Nat.reduceSub, Nat.cast_ofNat] at hr3
    rw [hr3, h_conjPair_norm_eq_abs_re, h_two_conjPair_re, abs_le]
    exact ⟨fun hboth => by linarith [hboth.1], fun hle => ⟨by linarith, by nlinarith⟩⟩
  refine ⟨?_, hred, by rw [schurHook_zero_eq_h, zero_add, hh1_norm, he1_norm]; norm_num,
    hh1_norm, ⟨fun hall => hall 3 (by decide), fun h3 t ht => ?_⟩, ht3_iff, ?_⟩
  · have halg : ∀ x : ℝ, (algebraMap ℝ ℂ) x = (x : ℂ) := fun _ => rfl
    have hb2 : Polynomial.C ((b : ℂ) ^ 2) = -(Polynomial.C ((b : ℂ) * Complex.I) ^ 2) := by
      rw [← Polynomial.C_pow, mul_pow, Complex.I_sq, ← Polynomial.C_neg]; ring_nf
    rw [Fin.prod_univ_two]
    simp only [charPolyConj, conjPair, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, halg, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.ofReal_pow, hb2, map_add, map_sub]; ring
  · rw [hred t ht]; rcases eq_or_lt_of_le ht with rfl | ht3
    · simp only [Nat.reduceSub, Nat.cast_ofNat, hh1_norm]; linarith
    · exact second_inequality_all_t t a b (Nat.succ_le_of_lt ht3) ha hab (ht3_iff.mp h3)
  · have hev : (charPolyConj a b).eval 0 = a ^ 2 + b ^ 2 := by simp [charPolyConj]
    have hder : (charPolyConj a b).derivative.eval 0 = -2 * a := by
      simp [charPolyConj, sq, Polynomial.derivative_add, Polynomial.derivative_mul]; ring
    rw [hev, hder]; constructor <;> intro hle <;> linarith

end
end D5.S3.Analytic.Interpolation.SelfConjugateTwoNodeSchurRatioRegion
