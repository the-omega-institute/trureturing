/- GID: D5/S0/Asymptotics/Interference/FiniteLagAutocorrelation
   generality: G
   mirror-B: D5/B/S0/Asymptotics/Interference/FiniteLagAutocorrelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expands a finite real signal into its exact lag autocorrelation Fourier series. -/

import D5.S0.Asymptotics.Interference.FiniteAutocorrelation
import Mathlib.Algebra.Polynomial.Laurent

open scoped BigOperators ComplexConjugate LaurentPolynomial

open AddMonoidAlgebra

namespace D5.S0.Asymptotics.Interference.FiniteLagAutocorrelation

set_option backward.isDefEq.respectTransparency false

/-- The finite signal coefficients embedded in the integer-exponent Laurent algebra. -/
noncomputable def finiteCoefficientPolynomial {T : Nat} (f : Fin (T + 1) -> Real) :
    AddMonoidAlgebra Complex Int :=
  Finset.univ.sum fun n : Fin (T + 1) =>
    AddMonoidAlgebra.single (n : Int) (f n : Complex)

private theorem addMonoidAlgebra_sum_apply {I R G : Type*} [Semiring R]
    [AddMonoid G] (s : Finset I) (p : I -> AddMonoidAlgebra R G) (g : G) :
    (s.sum p) g = s.sum fun i => p i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private theorem addMonoidAlgebra_sum_mul_apply {I R G : Type*} [Semiring R]
    [AddMonoid G] (s : Finset I) (p : I -> AddMonoidAlgebra R G)
    (q : AddMonoidAlgebra R G) (g : G) :
    (s.sum p * q) g = s.sum fun i => (p i * q) g := by
  rw [Finset.sum_mul]
  exact addMonoidAlgebra_sum_apply s (fun i => p i * q) g

private theorem finiteCoefficientPolynomial_apply {T : Nat}
    (f : Fin (T + 1) -> Real) (m : Int) :
    finiteCoefficientPolynomial f m =
      Finset.univ.sum fun n : Fin (T + 1) =>
        if (n : Int) = m then (f n : Complex) else 0 := by
  change (Finset.univ.sum fun n : Fin (T + 1) =>
    AddMonoidAlgebra.single (n : Int) (f n : Complex)) m = _
  rw [addMonoidAlgebra_sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [AddMonoidAlgebra.single_apply]

private theorem invert_finiteCoefficientPolynomial {T : Nat}
    (f : Fin (T + 1) -> Real) :
    LaurentPolynomial.invert (finiteCoefficientPolynomial f) =
      Finset.univ.sum fun n : Fin (T + 1) =>
        AddMonoidAlgebra.single (-(n : Int)) (f n : Complex) := by
  ext m
  rw [LaurentPolynomial.invert_apply, finiteCoefficientPolynomial_apply]
  change (∑ n : Fin (T + 1), if (n : Int) = -m then (f n : Complex) else 0) =
    (Finset.univ.sum fun n : Fin (T + 1) =>
      AddMonoidAlgebra.single (-(n : Int)) (f n : Complex)) m
  rw [addMonoidAlgebra_sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [AddMonoidAlgebra.single_apply]
  by_cases h : (n : Int) = -m
  · simp [h]
  · have h' : -(n : Int) ≠ m := by omega
    simp [h, h']

private theorem lag_coefficient {T : Nat} (f : Fin (T + 1) -> Real) (m : Int) :
    (LaurentPolynomial.invert (finiteCoefficientPolynomial f) *
      finiteCoefficientPolynomial f) m =
      Finset.univ.sum fun n : Fin (T + 1) =>
        (f n : Complex) * finiteCoefficientPolynomial f ((n : Int) + m) := by
  rw [invert_finiteCoefficientPolynomial]
  rw [addMonoidAlgebra_sum_mul_apply]
  simp only [AddMonoidAlgebra.single_mul_apply, neg_neg]

private theorem coefficient_support {T : Nat} (f : Fin (T + 1) -> Real) :
    (finiteCoefficientPolynomial f).support ⊆ Finset.Icc (0 : Int) T := by
  intro m hm
  rw [Finset.mem_Icc]
  constructor
  · by_contra hneg
    have hzero : finiteCoefficientPolynomial f m = 0 := by
      rw [finiteCoefficientPolynomial_apply]
      apply Finset.sum_eq_zero
      intro n _
      have hne : (n : Int) ≠ m := by omega
      simp [hne]
    exact (Finsupp.mem_support_iff.mp hm) hzero
  · by_contra hlarge
    have hzero : finiteCoefficientPolynomial f m = 0 := by
      rw [finiteCoefficientPolynomial_apply]
      apply Finset.sum_eq_zero
      intro n _
      have hne : (n : Int) ≠ m := by
        have hn := n.isLt
        omega
      simp [hne]
    exact (Finsupp.mem_support_iff.mp hm) hzero

private theorem inverted_support {T : Nat} (f : Fin (T + 1) -> Real) :
    (LaurentPolynomial.invert (finiteCoefficientPolynomial f)).support ⊆
      Finset.Icc (-(T : Int)) 0 := by
  intro m hm
  have hnonzero : finiteCoefficientPolynomial f (-m) ≠ 0 := by
    simpa [LaurentPolynomial.invert_apply] using Finsupp.mem_support_iff.mp hm
  have hmem : -m ∈ (finiteCoefficientPolynomial f).support :=
    Finsupp.mem_support_iff.mpr hnonzero
  have hb := coefficient_support f hmem
  simp only [Finset.mem_Icc] at hb ⊢
  omega

private theorem autocorrelation_support {T : Nat} (f : Fin (T + 1) -> Real) :
    (LaurentPolynomial.invert (finiteCoefficientPolynomial f) *
      finiteCoefficientPolynomial f).support ⊆ Finset.Icc (-(T : Int)) T := by
  intro m hm
  have hadd := AddMonoidAlgebra.support_mul
    (LaurentPolynomial.invert (finiteCoefficientPolynomial f))
    (finiteCoefficientPolynomial f) hm
  rcases Finset.mem_add.mp hadd with ⟨a, ha, b, hb, rfl⟩
  have ha' := inverted_support f ha
  have hb' := coefficient_support f hb
  simp only [Finset.mem_Icc] at ha' hb' ⊢
  omega

private theorem eval₂_eq_finsupp_sum (p : LaurentPolynomial Complex) (z : Complexˣ) :
    LaurentPolynomial.eval₂ (RingHom.id Complex) z p =
      p.sum fun m a => a * (z ^ m).val := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      rw [Finsupp.sum_add_index']
      · intro m
        simp
      · intro m a b
        ring
  | C_mul_T m a =>
      rw [LaurentPolynomial.eval₂_C_mul_T]
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      rw [Finsupp.sum_single_index]
      · simp
      · simp

private theorem eval_finiteCoefficientPolynomial {T : Nat}
    (f : Fin (T + 1) -> Real) (z : Complexˣ) :
    LaurentPolynomial.eval₂ (RingHom.id Complex) z (finiteCoefficientPolynomial f) =
      D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
        (fun n => (f n : Complex)) z.val := by
  rw [finiteCoefficientPolynomial]
  rw [map_sum]
  simp only [D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal]
  apply Finset.sum_congr rfl
  intro n _
  rw [LaurentPolynomial.single_eq_C_mul_T]
  simp

private theorem eval_invert_finiteCoefficientPolynomial {T : Nat}
    (f : Fin (T + 1) -> Real) (theta : Real) :
    let z : Complex := Complex.exp ((theta : Complex) * Complex.I)
    let zu : Complexˣ := Units.mk0 z (Complex.exp_ne_zero _)
    LaurentPolynomial.eval₂ (RingHom.id Complex) zu
        (LaurentPolynomial.invert (finiteCoefficientPolynomial f)) =
      star (D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
        (fun n => (f n : Complex)) z) := by
  dsimp only
  rw [invert_finiteCoefficientPolynomial, map_sum]
  simp only [D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal]
  change (∑ x : Fin (T + 1),
      LaurentPolynomial.eval₂ (RingHom.id Complex)
        (Units.mk0 (Complex.exp ((theta : Complex) * Complex.I))
          (Complex.exp_ne_zero _))
        (AddMonoidAlgebra.single (-(x : Int)) (f x : Complex))) =
    (starRingEnd Complex)
      (∑ x : Fin (T + 1),
        (f x : Complex) * Complex.exp ((theta : Complex) * Complex.I) ^ (x : Nat))
  rw [map_sum (starRingEnd Complex)]
  apply Finset.sum_congr rfl
  intro n _
  rw [LaurentPolynomial.single_eq_C_mul_T,
    LaurentPolynomial.eval₂_C_mul_T]
  simp only [RingHom.id_apply]
  rw [map_mul, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  congr 1
  rw [Units.val_zpow_eq_zpow_val, starRingEnd_apply]
  change (Complex.exp ((theta : Complex) * Complex.I) ^ (-(n : Int))) =
    star (Complex.exp ((theta : Complex) * Complex.I) ^ (n : Nat))
  rw [Complex.star_def, map_pow]
  have hzstar : star (Complex.exp ((theta : Complex) * Complex.I)) =
      (Complex.exp ((theta : Complex) * Complex.I))⁻¹ := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simpa only [mul_neg, mul_one] using
      Complex.exp_neg ((theta : Complex) * Complex.I)
  rw [starRingEnd_apply, hzstar]
  simp

/-- A finite real signal has its exact lag autocorrelation as the Fourier coefficients of its
squared modulus. The first conjunct identifies every lag coefficient; the second sums exactly over
the possible lags. -/
theorem finite_lag_autocorrelation_expansion {T : Nat}
    (f : Fin (T + 1) -> Real) (theta : Real) :
    let p := finiteCoefficientPolynomial f
    let A := LaurentPolynomial.invert p * p
    (∀ m : Int, A m = Finset.univ.sum fun n : Fin (T + 1) =>
      (f n : Complex) * p ((n : Int) + m)) ∧
    (Complex.normSq
        (D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
          (fun n => (f n : Complex))
          (Complex.exp ((theta : Complex) * Complex.I))) : Complex) =
      ∑ m ∈ Finset.Icc (-(T : Int)) T,
        A m * Complex.exp ((theta : Complex) * Complex.I) ^ m := by
  dsimp only
  constructor
  · exact lag_coefficient f
  · let z : Complex := Complex.exp ((theta : Complex) * Complex.I)
    let zu : Complexˣ := Units.mk0 z (Complex.exp_ne_zero _)
    let p := finiteCoefficientPolynomial f
    let A := LaurentPolynomial.invert p * p
    have hp : LaurentPolynomial.eval₂ (RingHom.id Complex) zu p =
        D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
          (fun n => (f n : Complex)) z := by
      exact eval_finiteCoefficientPolynomial f zu
    have hinvert : LaurentPolynomial.eval₂ (RingHom.id Complex) zu
        (LaurentPolynomial.invert p) =
        star (D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
          (fun n => (f n : Complex)) z) := by
      exact eval_invert_finiteCoefficientPolynomial f theta
    calc
      (Complex.normSq
          (D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
            (fun n => (f n : Complex)) z) : Complex) =
          LaurentPolynomial.eval₂ (RingHom.id Complex) zu A := by
            rw [Complex.normSq_eq_conj_mul_self]
            change star
                (D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
                  (fun n => (f n : Complex)) z) *
                D5.S0.Asymptotics.Interference.FiniteAutocorrelation.finiteSignal
                  (fun n => (f n : Complex)) z = _
            rw [← hinvert, ← hp, map_mul]
      _ = A.sum fun m a => a * (zu ^ m).val := eval₂_eq_finsupp_sum A zu
      _ = ∑ m ∈ Finset.Icc (-(T : Int)) T, A m * z ^ m := by
        rw [Finsupp.sum_of_support_subset A (autocorrelation_support f)]
        · apply Finset.sum_congr rfl
          intro m _
          rw [Units.val_zpow_eq_zpow_val]
          change A m * z ^ m = A m * z ^ m
          rfl
        · intro m _
          simp

#print axioms finite_lag_autocorrelation_expansion

end D5.S0.Asymptotics.Interference.FiniteLagAutocorrelation
