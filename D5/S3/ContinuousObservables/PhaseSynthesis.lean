/- GID: D5/S3/ContinuousObservables/PhaseSynthesis
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/PhaseSynthesis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial phase synthesis factors signed circle unitary completions. -/

import D5.S3.ContinuousObservables.IntervalSOSCompletion
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
Copyright (c) 2026 shosonoda. All rights reserved.
Released under Apache 2.0; the full license is in
`docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt`.
Authors of the transplanted proofs: shosonoda.

Selected definitions and proof bodies from auto-res/lean-qsvt,
commit 42c4b9149d5957db497e4226bc02da92d10f7a3c:
QSVT/QSP/Existence.lean, QSP/PolyW.lean, QSP/Poly.lean and Polynomial/Parity.lean.
Namespaces, imports and visibility are adapted to the existing interval SOS definitions.
The signed-circle continuous matrix application uses the same real SOS factors.
-/

open Polynomial

namespace D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly

private theorem HasParity.of_add_two {P : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 2)) : HasParity P n :=
  ⟨fun hn => hP.1 (Nat.even_add.mpr (iff_of_true hn even_two)),
    fun hn => hP.2 (Nat.odd_add.mpr (iff_of_true hn even_two))⟩

private theorem HasParity.coeff_eq_zero_of_odd_add {P : ℂ[X]} {n m : ℕ} (hP : HasParity P n)
    (hm : Odd (m + n)) : P.coeff m = 0 := by
  rcases Nat.even_or_odd n with hn | hn
  · exact hP.1 hn m (Nat.odd_add.mp hm |>.mpr hn)
  · refine hP.2 hn m ?_
    rw [Nat.odd_add] at hm
    exact Nat.not_odd_iff_even.mp (fun h => Nat.not_even_iff_odd.mpr hn (hm.mp h))

end D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly

namespace D5.S3.ContinuousObservables.PhaseSynthesis

open Complex D5.S3.ContinuousObservables.IntervalSOSCompletion
open D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly
open D5.S3.ContinuousObservables.CentralWinding

private theorem conjP_add (P Q : ℂ[X]) : conjP (P + Q) = conjP P + conjP Q :=
  Polynomial.map_add _

private theorem conjP_sub (P Q : ℂ[X]) : conjP (P - Q) = conjP P - conjP Q :=
  Polynomial.map_sub _

private theorem conjP_mul (P Q : ℂ[X]) : conjP (P * Q) = conjP P * conjP Q :=
  Polynomial.map_mul _

private theorem conjP_pow (P : ℂ[X]) (n : ℕ) : conjP (P ^ n) = conjP P ^ n :=
  Polynomial.map_pow _ _

private theorem conjP_C (a : ℂ) : conjP (C a) = C ((starRingEnd ℂ) a) :=
  Polynomial.map_C _

private theorem conjP_X : conjP X = X :=
  Polynomial.map_X _

private theorem conjP_one : conjP 1 = 1 :=
  Polynomial.map_one _

private theorem conjP_zero : conjP 0 = 0 :=
  Polynomial.map_zero _

private theorem conj_exp_I_mul (φ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * φ)) = Complex.exp (-(Complex.I * φ)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

private theorem conj_exp_neg_I_mul (φ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * φ))) = Complex.exp (Complex.I * φ) := by
  rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul,
    neg_neg]

private theorem natDegree_conjP_le (P : ℂ[X]) : (conjP P).natDegree ≤ P.natDegree :=
  Polynomial.natDegree_map_le

private theorem exp_I_mul_mul_exp_neg (φ : ℝ) :
    Complex.exp (Complex.I * φ) * Complex.exp (-(Complex.I * φ)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem C_exp_mul_C_exp_neg (φ : ℝ) :
    (C (Complex.exp (Complex.I * φ)) : ℂ[X]) * C (Complex.exp (-(Complex.I * φ))) = 1 := by
  rw [← C_mul, exp_I_mul_mul_exp_neg, C_1]

noncomputable def stepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (C (Complex.exp (Complex.I * φ)) * (X * PQ.1 + (X ^ 2 - 1) * PQ.2),
    C (Complex.exp (-(Complex.I * φ))) * (X * PQ.2 + PQ.1))

noncomputable def qspPolyW (φ₀ : ℝ) (Φ : List ℝ) : ℂ[X] × ℂ[X] :=
  Φ.foldl (fun PQ φ => stepW φ PQ) (C (Complex.exp (Complex.I * φ₀)), 0)

private theorem qspPolyW_nil (φ₀ : ℝ) : qspPolyW φ₀ [] = (C (Complex.exp (Complex.I * φ₀)), 0) := rfl

private theorem qspPolyW_concat (φ₀ φ : ℝ) (Φ : List ℝ) :
    qspPolyW φ₀ (Φ ++ [φ]) = stepW φ (qspPolyW φ₀ Φ) := by
  simp only [qspPolyW, List.foldl_append, List.foldl_cons, List.foldl_nil]

noncomputable def unstepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (C (Complex.exp (-(Complex.I * φ))) * (X * PQ.1) +
      C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * PQ.2),
    C (Complex.exp (Complex.I * φ)) * (X * PQ.2) - C (Complex.exp (-(Complex.I * φ))) * PQ.1)

private theorem unstepW_fst (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).1 =
      C (Complex.exp (-(Complex.I * φ))) * (X * P) +
        C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * Q) := rfl

private theorem unstepW_snd (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).2 =
      C (Complex.exp (Complex.I * φ)) * (X * Q) - C (Complex.exp (-(Complex.I * φ))) * P := rfl

/-- QSP-7. `stepW φ ∘ unstepW φ = id` (uses only `e^{iφ} e^{-iφ} = 1`, i.e. `x² + (1 - x²) = 1`
after expanding). -/
private theorem stepW_unstepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : stepW φ (unstepW φ PQ) = PQ := by
  have h := C_exp_mul_C_exp_neg φ
  obtain ⟨P, Q⟩ := PQ
  simp only [stepW, unstepW, Prod.mk.injEq]
  constructor
  · linear_combination P * h
  · linear_combination Q * h

/-- QSP-7. `unstepW φ` preserves `P P^* + (1 - X²) Q Q^*`. -/
private theorem unstepW_unit (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).1 * conjP (unstepW φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepW φ (P, Q)).2 * conjP (unstepW φ (P, Q)).2 =
      P * conjP P + (1 - X ^ 2) * Q * conjP Q := by
  have h := C_exp_mul_C_exp_neg φ
  rw [unstepW_fst, unstepW_snd]
  simp only [conjP_mul, conjP_C, conjP_add, conjP_sub, conjP_X, conjP_pow, conjP_one,
    conj_exp_I_mul, conj_exp_neg_I_mul]
  linear_combination (P * conjP P + (1 - X ^ 2) * Q * conjP Q) * h

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the first component of `unstepW φ (P, Q)` has parity `n`. -/
private theorem unstepW_fst_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepW φ (P, Q)).1 n := by
  rw [unstepW_fst]
  exact (hP.X_mul.of_add_two.C_mul _).add (hQ.one_sub_X_sq_mul.C_mul _)

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the second component of `unstepW φ (P, Q)` has parity
`n + 1`. -/
private theorem unstepW_snd_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepW φ (P, Q)).2 (n + 1) := by
  rw [unstepW_snd]
  exact (hQ.X_mul.C_mul _).sub (hP.C_mul _)

/-- Crude degree bound for the first component of `unstepW`. -/
private theorem natDegree_unstepW_fst_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepW φ (P, Q)).1.natDegree ≤ n + 1 + 1 := by
  have h1X2 : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 := by compute_degree
  rw [unstepW_fst]
  refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans ?_)
    ((natDegree_C_mul_le _ _).trans ?_)
  · exact (natDegree_mul_le_of_le natDegree_X_le hP).trans (by omega)
  · exact (natDegree_mul_le_of_le h1X2 hQ).trans (by omega)

/-- Crude degree bound for the second component of `unstepW`. -/
private theorem natDegree_unstepW_snd_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepW φ (P, Q)).2.natDegree ≤ n + 1 := by
  rw [unstepW_snd]
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans ?_)
    ((natDegree_C_mul_le _ _).trans hP))
  exact (natDegree_mul_le_of_le natDegree_X_le hQ).trans (by omega)

/-- The top coefficient of the first component of `unstepW φ (P, Q)` for `deg Q ≤ n`:
`e^{-iφ} p_{n+1} - e^{iφ} q_n`. -/
private theorem coeff_unstepW_fst {P Q : ℂ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) (φ : ℝ) :
    (unstepW φ (P, Q)).1.coeff (n + 1 + 1) =
      Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) -
        Complex.exp (Complex.I * φ) * Q.coeff n := by
  rw [unstepW_fst, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, sub_mul, one_mul, coeff_sub,
    coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n + 1 + 1),
    show n + 1 + 1 = n + 2 from rfl, coeff_X_pow_mul]
  ring

/-- The top coefficient of the second component of `unstepW φ (P, Q)`:
`e^{iφ} q_n - e^{-iφ} p_{n+1}`. -/
private theorem coeff_unstepW_snd (P Q : ℂ[X]) (n : ℕ) (φ : ℝ) :
    (unstepW φ (P, Q)).2.coeff (n + 1) =
      Complex.exp (Complex.I * φ) * Q.coeff n -
        Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) := by
  rw [unstepW_snd, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul]

/-! ### The top coefficients -/

/-- QSP-7. The `X^{2n+2}` coefficient of `P P^* + (1 - X²) Q Q^* = 1` for `deg P ≤ n + 1`,
`deg Q ≤ n`: `p_{n+1} p̄_{n+1} = q_n q̄_n`. -/
private theorem coeff_top_mul_conj_eq {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    P.coeff (n + 1) * (starRingEnd ℂ) (P.coeff (n + 1)) =
      Q.coeff n * (starRingEnd ℂ) (Q.coeff n) := by
  have h := congrArg (fun R : ℂ[X] => R.coeff (n + 1 + (n + 1))) hunit
  have hQQ : (Q * conjP Q).natDegree ≤ n + n :=
    natDegree_mul_le_of_le hQ ((natDegree_conjP_le Q).trans hQ)
  have h0 : (Q * conjP Q).coeff (n + 1 + (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : (1 : ℂ[X]).coeff (n + 1 + (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_one]; omega)
  rw [coeff_add, coeff_mul_add_eq_of_natDegree_le hP ((natDegree_conjP_le P).trans hP),
    coeff_conjP, show (1 - X ^ 2) * Q * conjP Q = Q * conjP Q - X ^ 2 * (Q * conjP Q) by ring,
    coeff_sub, h0, h1, show n + 1 + (n + 1) = n + n + 2 by ring, coeff_X_pow_mul,
    coeff_mul_add_eq_of_natDegree_le hQ ((natDegree_conjP_le Q).trans hQ), coeff_conjP] at h
  linear_combination h

/-- QSP-7. Given `p p̄ = q q̄`, there is a phase `φ` with `e^{-iφ} p = e^{iφ} q`
(`φ = arg (p / q) / 2` if `q ≠ 0`, else `φ = 0`). -/
private theorem exists_phase_coeff {p q : ℂ} (h : p * (starRingEnd ℂ) p = q * (starRingEnd ℂ) q) :
    ∃ φ : ℝ, Complex.exp (-(Complex.I * φ)) * p = Complex.exp (Complex.I * φ) * q := by
  by_cases hq : q = 0
  · refine ⟨0, ?_⟩
    have hp : p = 0 := by
      rw [hq, zero_mul, Complex.mul_conj] at h
      exact Complex.normSq_eq_zero.mp (by exact_mod_cast h)
    rw [hp, hq, mul_zero, mul_zero]
  · have hnorm : ‖p / q‖ = 1 := by
      rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hq)]
      rw [Complex.mul_conj', Complex.mul_conj'] at h
      exact (sq_eq_sq₀ (norm_nonneg p) (norm_nonneg q)).mp (by exact_mod_cast h)
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (p / q)).mp hnorm
    refine ⟨θ / 2, ?_⟩
    have hp : p = p / q * q := (div_mul_cancel₀ p hq).symm
    have hee : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) = p / q := by
      rw [← Complex.exp_add, ← hθ]
      congr 1
      push_cast
      ring
    have h1 := exp_I_mul_mul_exp_neg (θ / 2)
    linear_combination Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) * hp -
      (Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) * q) * hee +
      (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) * q) * h1

/-! ### The existence theorem -/

/-- QSP-7c. Existence of QSP phases (GSLW Theorem 3, "⇐", rotation convention).  If
(i) `deg P ≤ k`, `deg Q ≤ k - 1` (with `Q = 0` for `k = 0`), (ii) `P` has parity `k` and `Q`
parity `k - 1`, and (iii) `P P^* + (1 - X²) Q Q^* = 1`, then there are `φ₀ : ℝ` and
`Φ : List ℝ` of length `k` with `qspPolyW φ₀ Φ = (P, Q)`; by `seqW_eval`,
`seqW φ₀ Φ x = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]` on `[-1, 1]`. -/
theorem exists_phases (k : ℕ) (P Q : ℂ[X]) (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ k - 1)
    (hQ0 : k = 0 → Q = 0) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ φ₀ : ℝ, ∃ Φ : List ℝ, Φ.length = k ∧ qspPolyW φ₀ Φ = (P, Q) := by
  induction k generalizing P Q with
  | zero =>
    obtain rfl := hQ0 rfl
    rw [eq_C_of_natDegree_le_zero hP] at hunit ⊢
    have hc : P.coeff 0 * (starRingEnd ℂ) (P.coeff 0) = 1 := by
      rw [conjP_C, conjP_zero, mul_zero, add_zero, ← C_mul, ← C_1, C_inj] at hunit
      exact hunit
    have hnorm : ‖P.coeff 0‖ = 1 := by
      rw [Complex.mul_conj'] at hc
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by rw [one_pow]; exact_mod_cast hc)
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff _).mp hnorm
    exact ⟨θ, [], rfl, by rw [qspPolyW_nil, ← hθ, mul_comm]⟩
  | succ n ih =>
    rw [Nat.add_sub_cancel] at hQ hQpar
    obtain ⟨φ, hφ⟩ := exists_phase_coeff (coeff_top_mul_conj_eq hP hQ hunit)
    -- the lowered pair `(P̃, Q̃) = unstepW φ (P, Q)`
    have hPpar' : HasParity (unstepW φ (P, Q)).1 n := unstepW_fst_hasParity hPpar hQpar φ
    have hQpar' : HasParity (unstepW φ (P, Q)).2 (n + 1) := unstepW_snd_hasParity hPpar hQpar φ
    have hP' : (unstepW φ (P, Q)).1.natDegree ≤ n := by
      have h2 : (unstepW φ (P, Q)).1.natDegree ≤ n + 1 + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepW_fst_le hP hQ φ)
          (by rw [coeff_unstepW_fst hQ]; linear_combination hφ)
      rw [Nat.add_sub_cancel] at h2
      have h1 := natDegree_le_pred h2 (hPpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩)
      rwa [Nat.add_sub_cancel] at h1
    have hQn : (unstepW φ (P, Q)).2.coeff n = 0 :=
      hQpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩
    have hQ'' : (unstepW φ (P, Q)).2.natDegree ≤ n := by
      have h1 : (unstepW φ (P, Q)).2.natDegree ≤ n + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepW_snd_le hP hQ φ)
          (by rw [coeff_unstepW_snd]; linear_combination -hφ)
      rwa [Nat.add_sub_cancel] at h1
    have hQ' : (unstepW φ (P, Q)).2.natDegree ≤ n - 1 := natDegree_le_pred hQ'' hQn
    have hQ0' : n = 0 → (unstepW φ (P, Q)).2 = 0 := by
      rintro rfl
      rw [eq_C_of_natDegree_le_zero hQ'', hQn, C_0]
    have hQpar'' : HasParity (unstepW φ (P, Q)).2 (n - 1) := by
      rcases n with _ | m
      · rw [hQ0' rfl]
        exact hasParity_zero _
      · rw [Nat.add_sub_cancel]
        exact hQpar'.of_add_two
    have hunit' : (unstepW φ (P, Q)).1 * conjP (unstepW φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepW φ (P, Q)).2 * conjP (unstepW φ (P, Q)).2 = 1 := by
      rw [unstepW_unit, hunit]
    obtain ⟨φ₀, Φ, hlen, hΦ⟩ := ih _ _ hP' hQ' hQ0' hPpar' hQpar'' hunit'
    refine ⟨φ₀, Φ ++ [φ], by rw [List.length_append, List.length_singleton, hlen], ?_⟩
    rw [qspPolyW_concat, hΦ]
    exact stepW_unstepW φ (P, Q)



/-- A constant diagonal phase in the native continuous observable algebra. -/
noncomputable def phaseDiagonal (φ : ℝ) : CyclicObservable 2 :=
  ContinuousMap.const _ !![Complex.exp (I * φ), 0; 0, Complex.exp (-(I * φ))]

/-- Ordered right multiplication by the existing signed-circle signal. -/
noncomputable def phaseProduct (φ₀ : ℝ) (Φ : List ℝ) : CyclicObservable 2 :=
  Φ.foldl (fun U φ => U * (phaseCompletion X 0 1 * phaseDiagonal φ)) (phaseDiagonal φ₀)

private def pairMatrix (x y : ℝ) (PQ : ℂ[X] × ℂ[X]) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  !![PQ.1.eval (x : ℂ), I * PQ.2.eval (x : ℂ) * (y : ℂ);
     I * (conjP PQ.2).eval (x : ℂ) * (y : ℂ), (conjP PQ.1).eval (x : ℂ)]

private theorem signal_apply (t : AddCircle (1 : ℝ)) :
    phaseCompletion X 0 1 t =
      !![((windingPhase t).re : ℂ), I * ((windingPhase t).im : ℂ);
         I * ((windingPhase t).im : ℂ), ((windingPhase t).re : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    change (if _ then if _ then _ else _ else if _ then _ else _) = _ <;> simp

/-- The elementary product identity depends on y²=1−x², not on a sign of y. -/
private theorem mul_signal_phase {x y : ℝ} (hc : x ^ 2 + y ^ 2 = 1)
    (φ : ℝ) (a b c d : ℂ) :
    (!![a, I * b * (y : ℂ); I * c * (y : ℂ), d] : Matrix (ZMod 2) (ZMod 2) ℂ) *
        (!![(x : ℂ), I * (y : ℂ); I * (y : ℂ), (x : ℂ)] *
          !![Complex.exp (I * φ), 0; 0, Complex.exp (-(I * φ))]) =
      !![Complex.exp (I * φ) * (x * a + ((x : ℂ) ^ 2 - 1) * b),
          I * (Complex.exp (-(I * φ)) * (x * b + a)) * (y : ℂ);
        I * (Complex.exp (I * φ) * (x * c + d)) * (y : ℂ),
          Complex.exp (-(I * φ)) * (x * d + ((x : ℂ) ^ 2 - 1) * c)] := by
  have hs : (y : ℂ) * (y : ℂ) = 1 - (x : ℂ) ^ 2 := by
    exact_mod_cast (by nlinarith [hc] : y * y = 1 - x ^ 2)
  simp only [Matrix.mul_fin_two, mul_zero, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero]
    linear_combination (b * Complex.exp (I * φ) * (y : ℂ) * (y : ℂ)) * I_sq -
      (b * Complex.exp (I * φ)) * hs
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linear_combination (c * Complex.exp (-(I * φ)) * (y : ℂ) * (y : ℂ)) * I_sq -
      (c * Complex.exp (-(I * φ))) * hs

private theorem phaseProduct_concat (φ₀ φ : ℝ) (Φ : List ℝ) :
    phaseProduct φ₀ (Φ ++ [φ]) = phaseProduct φ₀ Φ * (phaseCompletion X 0 1 * phaseDiagonal φ) := by
  simp only [phaseProduct, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem phaseProduct_eval (φ₀ : ℝ) (Φ : List ℝ) (t : AddCircle (1 : ℝ)) :
    phaseProduct φ₀ Φ t =
      pairMatrix (windingPhase t).re (windingPhase t).im (qspPolyW φ₀ Φ) := by
  have hc : (windingPhase t).re ^ 2 + (windingPhase t).im ^ 2 = 1 := by
    have hz : ‖windingPhase t‖ = 1 := by simp [windingPhase]
    rw [sq, sq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
    norm_num
  induction Φ using List.reverseRecOn with
  | nil =>
    rw [qspPolyW_nil]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phaseProduct, phaseDiagonal, pairMatrix, eval_conjP, conj_exp_I_mul]
  | append_singleton Φ φ ih =>
    rw [phaseProduct_concat, ContinuousMap.mul_apply, ContinuousMap.mul_apply, ih,
      signal_apply]
    change pairMatrix _ _ _ * (_ * !![_, 0; 0, _]) = _
    rw [pairMatrix, mul_signal_phase hc, qspPolyW_concat]
    simp only [pairMatrix, stepW, conjP_mul, conjP_C, conjP_add, conjP_pow, conjP_sub,
      conjP_X, conjP_one, conj_exp_I_mul, conj_exp_neg_I_mul, eval_mul, eval_C,
      eval_add, eval_X, eval_pow, eval_sub, eval_one]

private theorem pairMatrix_completion (p B C : ℝ[X]) (t : AddCircle (1 : ℝ)) :
    pairMatrix (windingPhase t).re (windingPhase t).im
      (p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ),
        C.map (algebraMap ℝ ℂ)) = phaseCompletion p B C t := by
  have hre (R : ℝ[X]) := eval_map_algebraMap_ofReal R (windingPhase t).re
  simp only [pairMatrix, conjP_add, conjP_mul, conjP_C, conjP_map_algebraMap,
    Complex.conj_I, eval_add, eval_mul, eval_C, hre]
  ext i j
  fin_cases i <;> fin_cases j <;>
    change _ = (if _ then if _ then _ else _ else if _ then _ else _) <;>
      simp <;> push_cast <;> ring

/-- The same interval SOS witnesses admit an exact phase factorization as continuous
matrix fields on the entire signed winding circle. -/
theorem exists_phase_factorization (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k)
    (hpar : HasParity (p.map (algebraMap ℝ ℂ)) k)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, p.eval x ^ 2 ≤ 1) :
    ∃ (B C : ℝ[X]) (U : CyclicObservable 2) (φ₀ : ℝ) (Φ : List ℝ),
      1 - p ^ 2 = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧
      B.natDegree ≤ k ∧ C.natDegree ≤ k - 1 ∧ (k = 0 → C = 0) ∧
      HasParity (B.map (algebraMap ℝ ℂ)) k ∧
      HasParity (C.map (algebraMap ℝ ℂ)) (k - 1) ∧
      U = phaseCompletion p B C ∧ star U * U = 1 ∧ U * star U = 1 ∧
      (∀ t, (U t).det = 1) ∧ (∀ t, (U t 0 0).re = p.eval (windingPhase t).re) ∧
      Φ.length = k ∧
      qspPolyW φ₀ Φ =
        (p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ),
          C.map (algebraMap ℝ ℂ)) ∧ phaseProduct φ₀ Φ = U := by
  obtain ⟨B, C, U, hsos, hB, hC, hC0, hBp, hCp, hU, hleft, hright, hdet, hre⟩ :=
    exists_phase_unitary_completion k p hp hpar hbound
  let P : ℂ[X] := p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ)
  let Q : ℂ[X] := C.map (algebraMap ℝ ℂ)
  have hPd : P.natDegree ≤ k :=
    natDegree_add_le_of_degree_le (natDegree_map_le.trans hp)
      ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hB))
  have hQd : Q.natDegree ≤ k - 1 := natDegree_map_le.trans hC
  have hPp : HasParity P k := hpar.add (hBp.C_mul I)
  have hQ0 : k = 0 → Q = 0 := fun hk => by simp [Q, hC0 hk]
  have hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1 := by
    have hm := congrArg (Polynomial.map (algebraMap ℝ ℂ)) hsos
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X] at hm
    dsimp [P, Q]
    simp only [conjP_add, conjP_mul, conjP_C, conjP_map_algebraMap, Complex.conj_I]
    linear_combination hm + (B.map (algebraMap ℝ ℂ)) ^ 2 * I_sq
  obtain ⟨φ₀, Φ, hlen, hpair⟩ :=
    exists_phases k P Q hPd hQd hQ0 hPp hCp hunit
  refine ⟨B, C, U, φ₀, Φ, hsos, hB, hC, hC0, hBp, hCp, hU, hleft, hright,
    hdet, hre, hlen, hpair, ?_⟩
  rw [hU]
  apply ContinuousMap.ext
  intro t
  rw [phaseProduct_eval, hpair]
  exact pairMatrix_completion p B C t

end D5.S3.ContinuousObservables.PhaseSynthesis
