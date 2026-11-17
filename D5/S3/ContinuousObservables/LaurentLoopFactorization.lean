/- GID: D5/S3/ContinuousObservables/LaurentLoopFactorization
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/LaurentLoopFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=none
   digest: Exact ordered rank-one factorization of special-unitary Laurent loops. -/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-! Laurent coordinates retain all exponents and their exact matrix coefficients. -/

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open LaurentPolynomial Matrix

namespace D5.S3.ContinuousObservables.LaurentLoopFactorization

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ
abbrev Loop := Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℂ)

/-- The matrix at one Laurent exponent. -/
def coefficient (F : Loop) (j : ℤ) : M₂ := fun a b => (F a b).coeff j

/-- Entrywise scalar Laurent evaluation, defined only at nonzero complex arguments. -/
def evaluate (F : Loop) (z : ℂˣ) : M₂ :=
  (LaurentPolynomial.eval₂ (RingHom.id ℂ) z).mapMatrix F

/-- A finitely supported matrix coefficient family, in entrywise Laurent coordinates. -/
def ofCoefficients (C : ℤ →₀ M₂) : Loop := fun a b =>
  AddMonoidAlgebra.ofCoeff (C.mapRange (fun A => A a b) rfl)

/-- Constant matrices embedded in the Laurent matrix ring. -/
def constant (A : M₂) : Loop := LaurentPolynomial.C.mapMatrix A

/-- The primitive factor associated to an orthogonal projector. -/
def primitive (P : M₂) : Loop :=
  (LaurentPolynomial.T 1 : LaurentPolynomial ℂ) • constant P +
    (LaurentPolynomial.T (-1) : LaurentPolynomial ℂ) • constant (1 - P)

/-- Both projector laws and its exact complex rank. -/
def RankOneProjector (P : M₂) : Prop := Pᴴ = P ∧ P * P = P ∧ P.rank = 1

/-- The complete circle-valued special-unitary condition. -/
def CircleSU (F : Loop) : Prop := ∀ z : ℂˣ, ‖(z : ℂ)‖ = 1 →
  (evaluate F z)ᴴ * evaluate F z = 1 ∧ (evaluate F z).det = 1

/-- Symmetric support bound and exponent parity; actual degree is separate. -/
def InClass (n : ℕ) (F : Loop) : Prop :=
  (∀ j : ℤ, (n : ℤ) < |j| ∨ j % 2 ≠ (n : ℤ) % 2 → coefficient F j = 0) ∧ CircleSU F

def ActualDegree (n : ℕ) (F : Loop) : Prop :=
  coefficient F n ≠ 0 ∨ coefficient F (-(n : ℤ)) ≠ 0

/-- Matrix conjugate transpose together with inversion of the Laurent variable. -/
def adjoint (F : Loop) : Loop := fun a b =>
  LaurentPolynomial.invert (AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) (F b a))

private theorem coefficient_ofCoefficients (C : ℤ →₀ M₂) (j : ℤ) :
    coefficient (ofCoefficients C) j = C j := rfl

private theorem coefficient_ext {F G : Loop} (h : ∀ j, coefficient F j = coefficient G j) :
    F = G := by
  ext a b j
  exact congrFun (congrFun (h j) a) b

private theorem evaluate_mul (F G : Loop) (z : ℂˣ) :
    evaluate (F * G) z = evaluate F z * evaluate G z :=
  map_mul _ _ _

private theorem evaluate_constant (A : M₂) (z : ℂˣ) : evaluate (constant A) z = A := by
  ext a b
  simp [evaluate, constant]

private theorem laurent_eq_zero_of_circle (p : LaurentPolynomial ℂ)
    (h : ∀ z : Circle, LaurentPolynomial.eval₂ (RingHom.id ℂ) (Circle.toUnits z) p = 0) :
    p = 0 := by
  obtain ⟨n, q, hq⟩ := p.exists_T_pow
  have : Infinite (Set.Ioc (-Real.pi) Real.pi) :=
    Set.infinite_coe_iff.mpr (Set.Ioc_infinite (neg_lt_self Real.pi_pos))
  have : Infinite Circle := Infinite.of_injective Circle.argEquiv.symm
    Circle.argEquiv.symm.injective
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective
      (f := fun z : Circle => (z : ℂ)) Circle.coe_injective).mono
    rintro _ ⟨z, rfl⟩
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Circle.toUnits z)) hq
    rw [map_mul, h z, zero_mul] at he
    simpa [Polynomial.IsRoot] using he
  rw [hq0, map_zero] at hq
  exact (mul_eq_zero.mp hq.symm).resolve_right (isUnit_T (R := ℂ) n).ne_zero

private theorem loop_ext_circle {F G : Loop}
    (h : ∀ z : Circle, evaluate F (Circle.toUnits z) = evaluate G (Circle.toUnits z)) :
    F = G := by
  apply Matrix.ext
  intro a b
  apply sub_eq_zero.mp
  apply laurent_eq_zero_of_circle
  intro z
  simpa [evaluate, sub_eq_zero] using congrFun (congrFun (h z) a) b

private def sharp (p : LaurentPolynomial ℂ) : LaurentPolynomial ℂ :=
  LaurentPolynomial.invert (AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) p)

private theorem eval_sharp (p : LaurentPolynomial ℂ) (z : Circle) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) (Circle.toUnits z) (sharp p) =
      star (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Circle.toUnits z) p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa [sharp, map_add] using congrArg₂ (· + ·) hp hq
  | C_mul_T n a =>
    have hc : AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) (C a * T n) =
        C (star a) * T n := by
      simp only [← single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single]
      rfl
    simp only [sharp, hc, map_mul, invert_C, invert_T, eval₂_C, RingHom.id_apply,
      eval₂_T, star_mul]
    have hn (k : ℤ) : ((Circle.toUnits z ^ k : ℂˣ) : ℂ) = ((z ^ k : Circle) : ℂ) := by
      rw [← map_zpow]
      rfl
    rw [hn, hn]
    rw [zpow_neg, Circle.coe_inv_eq_conj]

private theorem evaluate_adjoint (F : Loop) (z : Circle) :
    evaluate (adjoint F) (Circle.toUnits z) = (evaluate F (Circle.toUnits z))ᴴ := by
  ext a b
  exact eval_sharp (F b a) z

private theorem circle_identities {F : Loop} (hF : CircleSU F) :
    adjoint F * F = 1 ∧ F * adjoint F = 1 ∧ F.det = 1 := by
  have hleft : adjoint F * F = 1 := by
    apply loop_ext_circle
    intro z
    rw [evaluate_mul, evaluate_adjoint]
    simpa [evaluate] using (hF (Circle.toUnits z) z.norm_coe).1
  have hdet : F.det = 1 := by
    apply sub_eq_zero.mp
    apply laurent_eq_zero_of_circle
    intro z
    rw [map_sub, map_one, RingHom.map_det]
    exact sub_eq_zero.mpr (hF (Circle.toUnits z) z.norm_coe).2
  exact ⟨hleft, mul_eq_one_comm.mp hleft, hdet⟩

private theorem scalar_top (p q : LaurentPolynomial ℂ) (a b : ℤ)
    (hp : ∀ j, a < j → p.coeff j = 0) (hq : ∀ j, b < j → q.coeff j = 0) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
  intro x y hx hy hxy
  have hx' : x ≤ a := le_of_not_gt (fun h => (Finsupp.mem_support_iff.mp hx) (hp x h))
  have hy' : y ≤ b := le_of_not_gt (fun h => (Finsupp.mem_support_iff.mp hy) (hq y h))
  constructor <;> omega

private theorem scalar_bottom (p q : LaurentPolynomial ℂ) (a b : ℤ)
    (hp : ∀ j, j < a → p.coeff j = 0) (hq : ∀ j, j < b → q.coeff j = 0) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
  intro x y hx hy hxy
  have hx' : a ≤ x := le_of_not_gt (fun h => (Finsupp.mem_support_iff.mp hx) (hp x h))
  have hy' : b ≤ y := le_of_not_gt (fun h => (Finsupp.mem_support_iff.mp hy) (hq y h))
  constructor <;> omega

private theorem coefficient_mul_top (F G : Loop) (a b : ℤ)
    (hF : ∀ j, a < j → coefficient F j = 0)
    (hG : ∀ j, b < j → coefficient G j = 0) :
    coefficient (F * G) (a + b) = coefficient F a * coefficient G b := by
  ext i k
  simp only [coefficient, Matrix.mul_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  apply scalar_top
  · intro j hj
    exact congrFun (congrFun (hF j hj) i) t
  · intro j hj
    exact congrFun (congrFun (hG j hj) t) k

private theorem coefficient_adjoint (F : Loop) (j : ℤ) :
    coefficient (adjoint F) j = (coefficient F (-j))ᴴ := by
  ext a b
  simp [coefficient, adjoint, AddMonoidAlgebra.coeff_mapRingHom]

private theorem upper_bound {n : ℕ} {F : Loop} (h : InClass n F) :
    ∀ j : ℤ, (n : ℤ) < j → coefficient F j = 0 := by
  intro j hj
  exact h.1 j (Or.inl (lt_of_lt_of_le hj (le_abs_self j)))

private theorem lower_bound {n : ℕ} {F : Loop} (h : InClass n F) :
    ∀ j : ℤ, j < -(n : ℤ) → coefficient F j = 0 := by
  intro j hj
  exact h.1 j (Or.inl (by have := neg_le_abs j; omega))

private theorem adjoint_upper_bound {n : ℕ} {F : Loop} (h : InClass n F) :
    ∀ j : ℤ, (n : ℤ) < j → coefficient (adjoint F) j = 0 := by
  intro j hj
  rw [coefficient_adjoint, lower_bound h (-j) (by omega), Matrix.conjTranspose_zero]

private theorem det_top {n : ℕ} {F : Loop} (h : InClass n F) :
    F.det.coeff ((n : ℤ) + n) = (coefficient F n).det := by
  have he (a b : Fin 2) : ∀ j : ℤ, (n : ℤ) < j → (F a b).coeff j = 0 := by
    intro j hj
    exact congrFun (congrFun (upper_bound h j hj) a) b
  simp only [Matrix.det_fin_two, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    scalar_top _ _ _ _ (he 0 0) (he 1 1), scalar_top _ _ _ _ (he 0 1) (he 1 0),
    coefficient]

private theorem det_bottom {n : ℕ} {F : Loop} (h : InClass n F) :
    F.det.coeff (-(n : ℤ) + -(n : ℤ)) = (coefficient F (-(n : ℤ))).det := by
  have he (a b : Fin 2) : ∀ j : ℤ, j < -(n : ℤ) → (F a b).coeff j = 0 := by
    intro j hj
    exact congrFun (congrFun (lower_bound h j hj) a) b
  simp only [Matrix.det_fin_two, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    scalar_bottom _ _ _ _ (he 0 0) (he 1 1), scalar_bottom _ _ _ _ (he 0 1) (he 1 0),
    coefficient]

private theorem endpoints {n : ℕ} {F : Loop} (hn : 0 < n) (h : InClass n F) :
    (coefficient F n).det = 0 ∧ (coefficient F (-(n : ℤ))).det = 0 ∧
      (coefficient F (-(n : ℤ)))ᴴ * coefficient F n = 0 ∧
      coefficient F n * (coefficient F (-(n : ℤ)))ᴴ = 0 := by
  obtain ⟨hleft, hright, hdet⟩ := circle_identities h.2
  have hn2 : (n : ℤ) + n ≠ 0 := by omega
  have hnm2 : -(n : ℤ) + -(n : ℤ) ≠ 0 := by omega
  have hdtop : (coefficient F n).det = 0 := by
    rw [← det_top h, hdet]
    simp [← LaurentPolynomial.C_1, hn2]
  have hdbot : (coefficient F (-(n : ℤ))).det = 0 := by
    rw [← det_bottom h, hdet]
    simp [← LaurentPolynomial.C_1, hnm2]
  have hl := congrArg (fun A => coefficient A ((n : ℤ) + n)) hleft
  have hr := congrArg (fun A => coefficient A ((n : ℤ) + n)) hright
  rw [coefficient_mul_top _ _ _ _ (adjoint_upper_bound h) (upper_bound h),
    coefficient_adjoint] at hl
  rw [coefficient_mul_top _ _ _ _ (upper_bound h) (adjoint_upper_bound h),
    coefficient_adjoint] at hr
  have hz : coefficient (1 : Loop) ((n : ℤ) + n) = 0 := by
    ext a b
    simp [coefficient, Matrix.one_apply, hn2, ← LaurentPolynomial.C_1]
  exact ⟨hdtop, hdbot, hl.trans hz, hr.trans hz⟩

end D5.S3.ContinuousObservables.LaurentLoopFactorization
