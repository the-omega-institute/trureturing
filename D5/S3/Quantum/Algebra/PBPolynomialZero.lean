/- GID: D5/S3/Quantum/Algebra/PBPolynomialZero
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBPolynomialZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Polynomial.Basic]
   utility: none
   digest: Original PB and explicit rotation, oddness and affine-zero rows force all polynomial pairs to vanish. -/

import D5.S3.Topology.JBAlgebra
import D5.S3.Quantum.Algebra.PBActualOuterBudget
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-! Polynomial zero responses on the original real Jordan carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Polynomial
open scoped BigOperators
namespace D5.S3.Quantum.Algebra.PBPolynomialZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Evaluation is the finite linear combination of the original Jordan powers.
def eval (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u x : E) : ℝ[X] →ₗ[ℝ] E :=
  (Finsupp.linearCombination ℝ (D5.S3.Topology.JBAlgebra.npow J u x)).comp
    ((AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap.comp
      (Polynomial.toFinsuppIsoLinear ℝ).toLinearMap)

@[simp] private theorem eval_monomial (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u x : E) (n : ℕ) (r : ℝ) :
    eval J u x (monomial n r) = r • D5.S3.Topology.JBAlgebra.npow J u x n := by
  change Finsupp.linearCombination ℝ _ (Finsupp.single n r) = _
  exact Finsupp.linearCombination_single ℝ r n

@[simp] private theorem eval_C (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u x : E) (r : ℝ) :
    eval J u x (C r) = r • u := eval_monomial J u x 0 r


private theorem eval_mul (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u x : E)
    (A : D5.S3.Topology.JBAlgebra.Data E J u) (p q : ℝ[X]) :
    eval J u x (p * q) = J (eval J u x p) (eval J u x q) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [add_mul, hp, hr]
  | monomial n a =>
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simp [mul_add, hq, hr]
    | monomial m b =>
      simp [monomial_mul_monomial, map_smul,
        D5.S3.Topology.JBAlgebra.power_mul A, mul_smul]
      exact smul_comm _ _ _

private def coeffLinear (f : ℂ →ₗ[ℝ] ℝ) : ℂ[X] →ₗ[ℝ] ℝ[X] :=
  ((Polynomial.toFinsuppIsoLinear ℝ).symm.toLinearMap.comp
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap).comp
    ((Finsupp.mapRange.linearMap f).comp
      ((AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap.comp
        ((Polynomial.toFinsuppIsoLinear ℂ).toLinearMap.restrictScalars ℝ)))

private abbrev reP : ℂ[X] →ₗ[ℝ] ℝ[X] := coeffLinear Complex.reLm
private abbrev imP : ℂ[X] →ₗ[ℝ] ℝ[X] := coeffLinear Complex.imLm


@[simp] private theorem re_C (z : ℂ) : reP (C z) = C z.re := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  ext n
  by_cases hn : n = 0 <;> simp [realcoeff, coeff_C, hn]
@[simp] private theorem im_C (z : ℂ) : imP (C z) = C z.im := by
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  ext n
  by_cases hn : n = 0 <;> simp [imagcoeff, coeff_C, hn]


private theorem re_C_mul (z : ℂ) (P : ℂ[X]) :
    reP (C z * P) = z.re • reP P - z.im • imP P := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  ext k
  simp [realcoeff, imagcoeff, Complex.mul_re]

private theorem im_C_mul (z : ℂ) (P : ℂ[X]) :
    imP (C z * P) = z.re • imP P + z.im • reP P := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  ext k
  simp [realcoeff, imagcoeff, Complex.mul_im]


private theorem re_mul (P Q : ℂ[X]) :
    reP (P*Q) = reP P * reP Q - imP P * imP Q := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  ext k
  simp [realcoeff, imagcoeff, coeff_mul, Complex.mul_re, Finset.sum_sub_distrib]

private theorem im_mul (P Q : ℂ[X]) :
    imP (P*Q) = reP P * imP Q + imP P * reP Q := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  ext k
  simp [realcoeff, imagcoeff, coeff_mul, Complex.mul_im, Finset.sum_add_distrib]

private theorem part_degree (P : ℂ[X]) :
    (reP P).natDegree ≤ P.natDegree ∧ (imP P).natDegree ≤ P.natDegree := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  constructor <;> apply natDegree_le_iff_coeff_eq_zero.mpr <;> intro k hk <;>
    simp [realcoeff, imagcoeff, coeff_eq_zero_of_natDegree_lt hk]

@[simp] private theorem re_real (p : ℝ[X]) : reP (p.map Complex.ofRealHom) = p := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  ext n; simp [realcoeff]
@[simp] private theorem im_real (p : ℝ[X]) : imP (p.map Complex.ofRealHom) = 0 := by
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  ext n; simp [imagcoeff]
@[simp] private theorem re_conj (P : ℂ[X]) : reP (P.map (starRingEnd ℂ)) = reP P := by
  have realcoeff (P : ℂ[X]) (k : ℕ) : (reP P).coeff k = (P.coeff k).re := rfl
  ext n; simp [realcoeff]
@[simp] private theorem im_conj (P : ℂ[X]) : imP (P.map (starRingEnd ℂ)) = -imP P := by
  have imagcoeff (P : ℂ[X]) (k : ℕ) : (imP P).coeff k = (P.coeff k).im := rfl
  ext n; simp [imagcoeff]

private def phi (ev : ℝ[X] →ₗ[ℝ] E) (D : E → E → E) (P : ℂ[X]) : E :=
  D (ev (reP P)) (ev (imP P))

private theorem phi_neg (ev : ℝ[X] →ₗ[ℝ] E) (D : E → E → E)
    (hl : ∀ a b, D (-a) b = -D a b) (hr : ∀ a b, D a (-b) = -D a b)
    (P : ℂ[X]) : phi ev D (-P) = phi ev D P := by
  simp [phi, hl, hr]

private theorem phi_conj (ev : ℝ[X] →ₗ[ℝ] E) (D : E → E → E)
    (hr : ∀ a b, D a (-b) = -D a b) (P : ℂ[X]) :
    phi ev D (P.map (starRingEnd ℂ)) = -phi ev D P := by simp [phi, hr]

private theorem phi_phase (ev : ℝ[X] →ₗ[ℝ] E) (D : E → E → E)
    (rot : ∀ (a b : E) (θ : ℝ),
      D (Real.cos θ • a - Real.sin θ • b) (Real.sin θ • a + Real.cos θ • b) = D a b)
    (z : ℂ) (hz : ‖z‖ = 1) (P : ℂ[X]) : phi ev D (C z * P) = phi ev D P := by
  have hc : z.re = Real.cos z.arg := by simpa [hz] using (Complex.norm_mul_cos_arg z).symm
  have hs : z.im = Real.sin z.arg := by simpa [hz] using (Complex.norm_mul_sin_arg z).symm
  simp only [phi, re_C_mul, im_C_mul, map_sub, map_add, map_smul, hc, hs]
  rw [add_comm (Real.cos z.arg • ev (imP P))]
  exact rot _ _ _

private theorem affine_base (ev : ℝ[X] →ₗ[ℝ] E) (u : E) (hu : ev 1 = u)
    (D : E → E → E)
    (aff : ∀ (a : E) (s t r v : ℝ), D (s • u + r • a) (t • u + v • a) = 0)
    (P : ℂ[X]) (hP : P.natDegree ≤ 1) : phi ev D P = 0 := by
  have ec (r : ℝ) : ev (C r) = r • u := by
    rw [show C r = r • (1 : ℝ[X]) by rw [smul_eq_C_mul, mul_one], map_smul, hu]
  obtain ⟨a,b,h⟩ := exists_eq_X_add_C_of_natDegree_le_one ((part_degree P).1.trans hP)
  obtain ⟨c,d,k⟩ := exists_eq_X_add_C_of_natDegree_le_one ((part_degree P).2.trans hP)
  simp only [phi, h, k, map_add, show C a * X = a • (X : ℝ[X]) by rw [smul_eq_C_mul],
    show C c * X = c • (X : ℝ[X]) by rw [smul_eq_C_mul], map_smul, ec]
  simpa only [add_comm] using aff (ev X) b d a c

private def pair (p q : ℝ[X]) : ℂ[X] := p.map Complex.ofRealHom + C Complex.I * q.map Complex.ofRealHom

@[simp] private theorem re_pair (p q : ℝ[X]) : reP (pair p q) = p := by
  simp [pair, re_C_mul]
@[simp] private theorem im_pair (p q : ℝ[X]) : imP (pair p q) = q := by
  simp [pair, im_C_mul]

private theorem pair_degree (p q : ℝ[X]) : (pair p q).natDegree ≤ max p.natDegree q.natDegree := by
  have hm : (C Complex.I * q.map Complex.ofRealHom).natDegree ≤ (q.map Complex.ofRealHom).natDegree := by
    simpa only [natDegree_C, zero_add] using
      (natDegree_mul_le (p := C Complex.I) (q := q.map Complex.ofRealHom))
  exact natDegree_add_le_of_degree_le
    (natDegree_map_le.trans (le_max_left _ _))
    (hm.trans (natDegree_map_le.trans (le_max_right _ _)))

private theorem pb_outer (ev : ℝ[X] →ₗ[ℝ] E) (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (mul : ∀ p q, ev (p * q) = J (ev p) (ev q))
    (pb : D5.S3.Quantum.Algebra.PBActualOuterBudget.PB J D)
    (a b c : ℝ[X]) (hab : D (ev a) (ev b) = 0) (hac : D (ev a) (ev c) = 0) :
    D (ev b - J (ev a) (ev c)) (ev c + J (ev a) (ev b)) =
      D (ev b + J (ev a) (ev c)) (ev c - J (ev a) (ev b)) := by
  have comm : J (ev b) (J (ev a) (ev c)) = J (ev c) (J (ev a) (ev b)) := by
    rw [← mul a c, ← mul b (a*c), ← mul a b, ← mul c (a*b)]
    congr 1; ring
  have h := pb (ev a) (ev b) (ev c)
  dsimp only at h
  rw [hab, hac, zero_sub, add_zero, map_neg, comm, neg_add_cancel, smul_zero,
    sub_neg_eq_add] at h
  simpa only [sub_eq_add_neg] using sub_eq_zero.mp h

@[simp] private theorem re_one : reP (1 : ℂ[X]) = 1 := by simpa using re_C 1
@[simp] private theorem im_one : imP (1 : ℂ[X]) = 0 := by simpa using im_C 1

private theorem plus_record (ev : ℝ[X] →ₗ[ℝ] E) (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (D : E → E → E) (mul : ∀ p q, ev (p * q) = J (ev p) (ev q)) (a : ℝ[X]) (W : ℂ[X]) :
    phi ev D ((1 + C Complex.I * a.map Complex.ofRealHom)*W) =
    D (ev (reP W) - J (ev a) (ev (imP W))) (ev (imP W) + J (ev a) (ev (reP W))) := by
  simp [phi, re_mul, im_mul, mul, sub_eq_add_neg]

private theorem minus_record (ev : ℝ[X] →ₗ[ℝ] E) (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (D : E → E → E) (mul : ∀ p q, ev (p * q) = J (ev p) (ev q)) (a : ℝ[X]) (W : ℂ[X]) :
    phi ev D ((1 - C Complex.I * a.map Complex.ofRealHom)*W) =
    D (ev (reP W) + J (ev a) (ev (imP W))) (ev (imP W) - J (ev a) (ev (reP W))) := by
  simp [phi, re_mul, im_mul, mul, sub_eq_add_neg]

private def actor (z : ℂ) : ℝ[X] := C z.im⁻¹ * (X - C z.re)

private theorem factor_twist (z : ℂ) (ht : z.im ≠ 0) :
    (1 + C Complex.I * (actor z).map Complex.ofRealHom) * C (-Complex.I * z.im) = X - C z ∧
    (1 - C Complex.I * (actor z).map Complex.ofRealHom) * C (-Complex.I * z.im) =
      -(X - C (starRingEnd ℂ z)) := by
  have hti : ((z.im⁻¹ : ℝ) : ℂ) * (z.im : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht, Complex.ofReal_one]
  have hk : Complex.I * ((z.im⁻¹ : ℝ) : ℂ) * (-Complex.I * z.im) = 1 := by
    calc
      _ = -(Complex.I * Complex.I) * (((z.im⁻¹ : ℝ) : ℂ) * z.im) := by ring
      _ = 1 := by rw [Complex.I_mul_I, hti]; norm_num
  have hz : (-Complex.I * z.im - z.re : ℂ) = -z := by
    apply Complex.ext <;> simp
  have hzc : (-Complex.I * z.im + z.re : ℂ) = starRingEnd ℂ z := by
    apply Complex.ext <;> simp
  have ha : (actor z).map Complex.ofRealHom =
      C ((z.im⁻¹ : ℝ) : ℂ) * (X - C (z.re : ℂ)) := by
    simp only [actor, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X]
    rfl
  rw [ha]
  constructor
  · calc
      _ = C (Complex.I * ((z.im⁻¹ : ℝ) : ℂ) * (-Complex.I * z.im)) * X +
          C (-Complex.I * z.im - (Complex.I * ((z.im⁻¹ : ℝ) : ℂ) * (-Complex.I * z.im)) * z.re) := by
            simp only [map_mul, map_sub]; ring
      _ = X - C z := by rw [hk, one_mul, hz]; simp [sub_eq_add_neg]
  · calc
      _ = -(C (Complex.I * ((z.im⁻¹ : ℝ) : ℂ) * (-Complex.I * z.im)) * X) +
          C (-Complex.I * z.im + (Complex.I * ((z.im⁻¹ : ℝ) : ℂ) * (-Complex.I * z.im)) * z.re) := by
            simp only [map_mul, map_add]; ring
      _ = -(X - C (starRingEnd ℂ z)) := by rw [hk, one_mul, hzc]; simp [sub_eq_add_neg, add_comm]

private theorem actor_degree (z : ℂ) : (actor z).natDegree ≤ 1 := by
  have h := natDegree_mul_le (p := C z.im⁻¹) (q := (X - C z.re))
  simpa [actor] using h

private theorem reflect_root (ev : ℝ[X] →ₗ[ℝ] E) (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (mul : ∀ p q, ev (p * q) = J (ev p) (ev q))
    (pb : D5.S3.Quantum.Algebra.PBActualOuterBudget.PB J D)
    (hl : ∀ a b, D (-a) b = -D a b) (hr : ∀ a b, D a (-b) = -D a b)
    (n : ℕ) (hn : 1 < n)
    (ih : ∀ p q : ℝ[X], p.natDegree < n → q.natDegree < n → D (ev p) (ev q) = 0)
    (z : ℂ) (Q : ℂ[X]) (hQ : Q.natDegree < n) :
    phi ev D ((X - C z)*Q) = phi ev D ((X - C (starRingEnd ℂ z))*Q) := by
  by_cases ht : z.im = 0
  · have hz : starRingEnd ℂ z = z := by apply Complex.ext <;> simp [ht]
    rw [hz]
  · let a := actor z
    let W := C (-Complex.I * z.im) * Q
    have hW : W.natDegree < n := by
      apply lt_of_le_of_lt _ hQ
      have h := natDegree_mul_le (p := C (-Complex.I * z.im)) (q := Q)
      simpa only [W, natDegree_C, zero_add] using h
    have ha : a.natDegree < n := (actor_degree z).trans_lt hn
    have hab := ih a (reP W) ha ((part_degree W).1.trans_lt hW)
    have hac := ih a (imP W) ha ((part_degree W).2.trans_lt hW)
    have hpb := pb_outer ev J D mul pb a (reP W) (imP W) hab hac
    have hp : (1+C Complex.I*a.map Complex.ofRealHom)*W = (X-C z)*Q := by
      dsimp only [W, a]
      rw [← mul_assoc, (factor_twist z ht).1]
    have hm : (1-C Complex.I*a.map Complex.ofRealHom)*W = -((X-C (starRingEnd ℂ z))*Q) := by
      dsimp only [W, a]
      rw [← mul_assoc, (factor_twist z ht).2, neg_mul]
    calc
      _ = phi ev D ((1+C Complex.I*a.map Complex.ofRealHom)*W) := congrArg (phi ev D) hp.symm
      _ = phi ev D ((1-C Complex.I*a.map Complex.ofRealHom)*W) := by
        rw [plus_record ev J D mul, minus_record ev J D mul]
        exact hpb
      _ = phi ev D (-((X-C (starRingEnd ℂ z))*Q)) := congrArg (phi ev D) hm
      _ = _ := phi_neg ev D hl hr _

private def rootProduct (l : List ℂ) : ℂ[X] := (l.map (fun z => X - C z)).prod

private theorem rootProduct_degree (l : List ℂ) : (rootProduct l).natDegree = l.length := by
  simpa [rootProduct] using natDegree_multiset_prod_X_sub_C_eq_card (l : Multiset ℂ)

private theorem rootProduct_conj (l : List ℂ) :
    (rootProduct l).map (starRingEnd ℂ) = rootProduct (l.map (starRingEnd ℂ)) := by
  simp [rootProduct, Polynomial.map_list_prod, List.map_map, Function.comp_def, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C]

private theorem reflect_list (ev : ℝ[X] →ₗ[ℝ] E) (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (mul : ∀ p q, ev (p * q) = J (ev p) (ev q))
    (pb : D5.S3.Quantum.Algebra.PBActualOuterBudget.PB J D)
    (hl : ∀ a b, D (-a) b = -D a b) (hr : ∀ a b, D a (-b) = -D a b)
    (n : ℕ) (hn : 1 < n)
    (ih : ∀ p q : ℝ[X], p.natDegree < n → q.natDegree < n → D (ev p) (ev q) = 0)
    (κ : ℂ) (l : List ℂ) (hL : l.length ≤ n) :
    phi ev D (C κ * rootProduct l) =
      phi ev D (C κ * rootProduct (l.map (starRingEnd ℂ))) := by
  have aux (ys : List ℂ) : ∀ xs : List ℂ, xs.length + ys.length ≤ n →
      phi ev D (C κ * rootProduct (xs ++ ys)) =
        phi ev D (C κ * rootProduct (xs ++ ys.map (starRingEnd ℂ))) := by
    induction ys with
    | nil => intro xs hx; simp
    | cons z ys hy =>
      intro xs hx
      let Q := C κ * rootProduct (xs ++ ys)
      have hQ : Q.natDegree < n := by
        have hd : Q.natDegree ≤ (xs ++ ys).length := by
          have h := natDegree_mul_le (p := C κ) (q := rootProduct (xs ++ ys))
          simpa only [Q, natDegree_C, zero_add, rootProduct_degree] using h
        simp only [List.length_append, List.length_cons] at *
        omega
      have hstep := reflect_root ev J D mul pb hl hr n hn ih z Q hQ
      calc
        _ = phi ev D ((X - C z)*Q) := by
          congr 1
          simp only [Q, rootProduct, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
          ring
        _ = phi ev D ((X - C (starRingEnd ℂ z))*Q) := hstep
        _ = phi ev D (C κ * rootProduct ((xs ++ [starRingEnd ℂ z]) ++ ys)) := by
          congr 1
          simp only [Q, rootProduct, List.map_append, List.map_cons, List.map_nil,
            List.prod_append, List.prod_cons, List.prod_nil]
          ring
        _ = phi ev D (C κ * rootProduct ((xs ++ [starRingEnd ℂ z]) ++ ys.map (starRingEnd ℂ))) :=
          hy _ (by simpa only [List.length_append, List.length_singleton, List.length_cons,
            List.length_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hx)
        _ = _ := by simp only [List.map_cons, List.append_assoc, List.singleton_append]
  simpa only [List.nil_append, List.length_nil, zero_add] using aux l [] (by simpa using hL)

private theorem all_complex_zero (ev : ℝ[X] →ₗ[ℝ] E) (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (u : E) (hu : ev 1 = u) (D : E → E → E)
    (mul : ∀ p q, ev (p * q) = J (ev p) (ev q))
    (pb : D5.S3.Quantum.Algebra.PBActualOuterBudget.PB J D)
    (rot : ∀ (a b : E) (θ : ℝ),
      D (Real.cos θ • a - Real.sin θ • b) (Real.sin θ • a + Real.cos θ • b) = D a b)
    (hl : ∀ a b, D (-a) b = -D a b) (hr : ∀ a b, D a (-b) = -D a b)
    (aff : ∀ (a : E) (s t r v : ℝ), D (s • u + r • a) (t • u + v • a) = 0)
    (P : ℂ[X]) : phi ev D P = 0 := by
  have aux (n : ℕ) : ∀ P : ℂ[X], P.natDegree ≤ n → phi ev D P = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hP
      by_cases hs : P.natDegree ≤ 1
      · exact affine_base ev u hu D aff P hs
      have hn : 1 < n := by omega
      have HP : P ≠ 0 := by intro hz; simp [hz] at hs
      have inner (p q : ℝ[X]) (hp : p.natDegree < n) (hq : q.natDegree < n) :
          D (ev p) (ev q) = 0 := by
        have h := ih (max p.natDegree q.natDegree) (max_lt hp hq) (pair p q) (pair_degree p q)
        simpa only [phi, re_pair, im_pair] using h
      let κ := P.leadingCoeff
      have hk : κ ≠ 0 := leadingCoeff_ne_zero.mpr HP
      let l := P.roots.toList
      have hf := IsAlgClosed.splits P
      have hfactor : P = C κ * rootProduct l := by
        simpa [κ, l, rootProduct] using hf.eq_prod_roots
      have hlen : l.length ≤ n := by
        simpa only [l, Multiset.length_toList, ← hf.natDegree_eq_card_roots] using hP
      have reflected := reflect_list ev J D mul pb hl hr n hn inner κ l hlen
      have hconj : C κ * rootProduct (l.map (starRingEnd ℂ)) =
          C (κ / starRingEnd ℂ κ) * P.map (starRingEnd ℂ) := by
        rw [hfactor, Polynomial.map_mul, Polynomial.map_C, rootProduct_conj, ← mul_assoc, ← map_mul]
        have hkc : starRingEnd ℂ κ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hk
        rw [div_mul_cancel₀ κ hkc]
      have hnorm : ‖κ / starRingEnd ℂ κ‖ = 1 := by simp [hk]
      have heq : phi ev D P = -phi ev D P := by
        calc
          _ = phi ev D (C κ * rootProduct l) := congrArg (phi ev D) hfactor
          _ = phi ev D (C κ * rootProduct (l.map (starRingEnd ℂ))) := reflected
          _ = phi ev D (C (κ / starRingEnd ℂ κ) * P.map (starRingEnd ℂ)) := congrArg (phi ev D) hconj
          _ = phi ev D (P.map (starRingEnd ℂ)) := phi_phase ev D rot _ hnorm _
          _ = -phi ev D P := phi_conj ev D hr P
      have hz : (2 : ℝ) • phi ev D P = 0 := by
        simpa only [two_smul, sub_eq_add_neg, neg_neg] using sub_eq_zero.mpr heq
      exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  exact aux P.natDegree P le_rfl

/-- All formal degrees, on the same original real Jordan carrier and total response,
conditional only on PB and the rotation, oddness and affine-zero suppliers. -/
theorem polynomial_zero (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E)
    (A : D5.S3.Topology.JBAlgebra.Data E J u) (D : E → E → E)
    (pb : D5.S3.Quantum.Algebra.PBActualOuterBudget.PB J D)
    (rot : ∀ (a b : E) (θ : ℝ),
      D (Real.cos θ • a - Real.sin θ • b) (Real.sin θ • a + Real.cos θ • b) = D a b)
    (hl : ∀ a b, D (-a) b = -D a b) (hr : ∀ a b, D a (-b) = -D a b)
    (aff : ∀ (a : E) (s t r v : ℝ), D (s • u + r • a) (t • u + v • a) = 0)
    (x : E) (p q : ℝ[X]) : D (eval J u x p) (eval J u x q) = 0 := by
  have hu : eval J u x 1 = u := by simpa only [C_1, one_smul] using eval_C J u x 1
  have h := all_complex_zero (eval J u x) J u hu D (eval_mul J u x A) pb rot hl hr aff (pair p q)
  simpa only [phi, re_pair, im_pair] using h

end D5.S3.Quantum.Algebra.PBPolynomialZero
