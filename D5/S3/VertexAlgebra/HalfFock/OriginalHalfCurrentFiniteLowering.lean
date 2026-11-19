/- GID: D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentFiniteLowering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite evaluation of the original lowering action on marked words. -/

import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Literal finite evaluation of the normally ordered original current. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentFiniteLowering

open LatticeGeneratingFieldLocality LatticeHalfFock MvPolynomial
open TwistedGround.OriginalFourMChargeCoset (oscillatorLower)
open OriginalHalfCurrentTransport
open private End vacuum vacuumProjection vacuumProjection_apply from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

private def creationPolynomial (D : LatticeData) (x : Index D) : Polynomial (End D) :=
  ∑ n ∈ Finset.range (x.2 + 1), Polynomial.monomial n
    (Ring.choose ((x.2 : ℂ) + 1/2) n • current D x.1 ((n : ℤ) - x.2 - 1))

private theorem creationPolynomial_coe (D : LatticeData) (x : Index D) :
    (creationPolynomial D x : PowerSeries (End D)) = creationPart D x := by
  apply PowerSeries.ext
  intro n
  simp only [Polynomial.coeff_coe, creationPart, PowerSeries.coeff_mk, creationPolynomial,
    Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n ≤ x.2
  · rw [ite_eq_left hn, Finset.sum_eq_single_of_mem n (by simpa using hn)]
    · simp
    · intro j _ hj
      simp [hj, Ne.symm hj]
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : n ≠ j := by
      intro he
      subst j
      exact hn (by simpa using hj)
    simp [hne, Ne.symm hne]

private def contractionPolynomial (D : LatticeData) (x y : Index D) : Polynomial (End D) :=
  Polynomial.monomial (x.2 + y.2 + 1)
    (((D.G x.1 y.1 : ℂ) * contractionScalar x.2 y.2) • 1)

/-- A polynomial in the lowering parameter whose coefficients are the
normal-order operators on the original marked oscillator word. -/
def wordPolynomial (D : LatticeData) : List (Index D) → Polynomial (End D)
  | [] => Polynomial.C (vacuumProjection D)
  | x :: xs => creationPolynomial D x * wordPolynomial D xs +
      ∑ j : Fin xs.length, contractionPolynomial D x (xs.get j) *
        wordPolynomial D (xs.eraseIdx j)
termination_by xs => xs.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private theorem wordPolynomial_coe (D : LatticeData) (xs : List (Index D)) :
    (wordPolynomial D xs : PowerSeries (End D)) = normalOrder D xs := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    cases xs with
    | nil => simp [wordPolynomial, normalOrder, vacuum]
    | cons x xs =>
      rw [wordPolynomial, normalOrder, Polynomial.coe_add, Polynomial.coe_mul,
        creationPolynomial_coe, ih xs (Nat.lt_succ_self _)]
      congr 1
      change Polynomial.coeToPowerSeries.ringHom (∑ j : Fin xs.length, _) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, contractionPolynomial,
        Polynomial.coe_monomial, ih _ (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))]
      rfl

private def evalLower (D : LatticeData) (t : ℂ) :
    Polynomial (End D) →+* End D :=
  Polynomial.eval₂RingHom' (RingHom.id _) (algebraMap ℂ (End D) t)
    (fun a => (Algebra.commutes t a).symm)

private theorem mul_algebraMap (D : LatticeData) (f : End D) (t : ℂ) :
    f * algebraMap ℂ (End D) t = t • f := by
  rw [Algebra.smul_def, Algebra.commutes]

private theorem evalLower_monomial (D : LatticeData) (t : ℂ) (n : ℕ) (f : End D) :
    evalLower D t (Polynomial.monomial n f) = t^n • f := by
  change (Polynomial.monomial n f).eval₂ (RingHom.id _) (algebraMap ℂ (End D) t) = _
  rw [Polynomial.eval₂_monomial, RingHom.id_apply, ← map_pow, mul_algebraMap]

/-- The exact finite inverse-coordinate lowering on a word of marked creation
modes. The cutoff can be the original homogeneous cutoff. -/
theorem evaluate_lowering_word (D : LatticeData) (hu : IsUnit D.G.det)
    (xs : List (Index D)) (t : ℂ) (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n →
      (oscillatorLower D ^ n) ((xs.map (fun x => (X x : Oscillator D))).prod) = 0) :
    (evalLower D t (wordPolynomial D xs)) 1 =
      ∑ n ∈ Finset.range cutoff,
        (t^n / (n.factorial : ℂ)) •
          (oscillatorLower D ^ n) ((xs.map (fun x => (X x : Oscillator D))).prod) := by
  let P := wordPolynomial D xs
  let N := max cutoff (P.natDegree + 1)
  have hN : P.natDegree < N := (Nat.lt_succ_self _).trans_le (le_max_right ..)
  have hc (n : ℕ) : P.coeff n (1 : Oscillator D) =
      (n.factorial : ℂ)⁻¹ •
        (oscillatorLower D ^ n) ((xs.map (fun x => (X x : Oscillator D))).prod) := by
    rw [← Polynomial.coeff_coe, show (P : PowerSeries (End D)) = _ from wordPolynomial_coe D xs]
    exact (lowering_normal_order_word D hu xs n).symm
  change (Polynomial.eval₂ (RingHom.id (End D)) (algebraMap ℂ (End D) t) P) 1 = _
  rw [Polynomial.eval₂_eq_sum_range' _ hN]
  simp only [RingHom.id_apply, ← map_pow, mul_algebraMap,
    LinearMap.sum_apply, LinearMap.smul_apply, hc, smul_smul, ← div_eq_mul_inv]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_left ..))
  intro n _ hn
  rw [hcut n (Nat.le_of_not_gt fun h => hn (Finset.mem_range.mpr h)), smul_zero]

/-- A labelled unpaired creator contributes its finite binomial sum. A
labelled contracted pair contributes exactly the original Gram entry times
the ordinary regular Cauchy coefficient. -/
theorem evaluate_word_step (D : LatticeData) (x : Index D) (xs : List (Index D)) (t : ℂ) :
    evalLower D t (wordPolynomial D (x :: xs)) =
      (∑ n ∈ Finset.range (x.2 + 1), (t^n * Ring.choose ((x.2 : ℂ) + 1/2) n) •
        current D x.1 ((n : ℤ) - x.2 - 1)) * evalLower D t (wordPolynomial D xs) +
      ∑ j : Fin xs.length,
        ((D.G x.1 (xs.get j).1 : ℂ) *
          ((PowerSeries.coeff (xs.get j).2 (OriginalHalfCurrentCauchy.regularSeries t)).coeff
            (x.2 : ℤ))) • evalLower D t (wordPolynomial D (xs.eraseIdx j)) := by
  rw [wordPolynomial, map_add, map_mul, map_sum]
  rw [creationPolynomial, map_sum]
  simp only [evalLower_monomial, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, contractionPolynomial, evalLower_monomial,
    OriginalHalfCurrentCauchy.regular_series_coefficient, smul_smul, Algebra.smul_mul_assoc, one_mul]
  congr 1
  ring

open PowerSeries
open private unitPower_add unitPower_nat_mul from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy
open private binomial_reflection from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

/-- Formal half-current pullback along the local map
`u ↦ lambda*u/(1-eta*u)` with the chosen half-coordinate lift. -/
def halfPullback (root lambda eta : ℂ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C root * unitPower eta (-3/2) * F.subst (PowerSeries.X * (PowerSeries.C lambda * unitPower eta (-1)))

private theorem pullback_coeff_sum (H F A : PowerSeries ℂ) (n : ℕ) :
    coeff n (H * F.subst (PowerSeries.X * A)) =
      ∑ p ∈ Finset.range (n+1), coeff p F * coeff n (H*(PowerSeries.X*A)^p) := by
  have hz : HasSubst (PowerSeries.X*A) := HasSubst.X'.mul_left
  have hp (j : ℕ) (hj : j ≤ n) :
      coeff j (F.subst (PowerSeries.X*A)) =
      ∑ p ∈ Finset.range (n+1), coeff p F * coeff j ((PowerSeries.X*A)^p) := by
    rw [coeff_subst' hz]
    simp only [smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro p h
    apply Finset.mem_range.mpr
    by_contra! hn
    apply h
    dsimp only
    rw [mul_pow, mul_comm (PowerSeries.X^p) (A^p), coeff_mul_X_pow',
      ite_eq_right (by omega : ¬ p ≤ j), mul_zero]
  rw [PowerSeries.coeff_mul]
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ p ∈ Finset.range (n+1),
        coeff p F * (coeff ij.1 H * coeff ij.2 ((PowerSeries.X*A)^p)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hi := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [hp ij.2 (by omega), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, ← PowerSeries.coeff_mul]

/-- Each ordinary coefficient of the actual Möbius half-current pullback
is the finite binomial creator sum, with the selected scale at each mode. -/
theorem half_pullback_coefficient (root lambda eta : ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    coeff n (halfPullback root lambda eta F) =
      ∑ p ∈ Finset.range (n+1), coeff p F *
        (root * lambda^p * eta^(n-p) * Ring.choose ((n:ℂ)+1/2) (n-p)) := by
  rw [halfPullback, pullback_coeff_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ n := by simpa using hp
  have he :
      PowerSeries.C root * unitPower eta (-3/2) * (PowerSeries.X * (PowerSeries.C lambda * unitPower eta (-1)))^p =
        PowerSeries.C (root*lambda^p) * unitPower eta (-(p:ℂ)-3/2) * PowerSeries.X^p := by
    rw [mul_pow, mul_pow, ← map_pow, ← unitPower_nat_mul]
    rw [show (-1:ℂ)*(p:ℂ) = -(p:ℂ) by ring]
    calc
      _ = (PowerSeries.C root * PowerSeries.C (lambda^p)) *
          (unitPower eta (-3/2) * unitPower eta (-(p:ℂ))) * PowerSeries.X^p := by ring
      _ = _ := by
        rw [← map_mul, ← unitPower_add, show (-3/2:ℂ) + -(p:ℂ) = -(p:ℂ)-3/2 by ring]
  rw [he, coeff_mul_X_pow', ite_eq_left hp', PowerSeries.coeff_C_mul, unitPower, coeff_rescale,
    binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [show -eta = eta * (-1) by ring, mul_pow]
  rw [show (root * lambda^p) * (eta^(n-p) * (-1:ℂ)^(n-p) *
      Ring.choose (-(p:ℂ)-3/2) (n-p)) =
      root * lambda^p * eta^(n-p) *
        ((-1:ℂ)^(n-p) * Ring.choose (-(p:ℂ)-3/2) (n-p)) by ring,
    binomial_reflection, show -(-(p:ℂ)-3/2) + ((n-p:ℕ):ℂ)-1 = (n:ℂ)+1/2 by
      rw [Nat.cast_sub hp']
      ring]

end D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentFiniteLowering
