/- GID: D5/S3/ContinuousObservables/LaurentLoopFactorization
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/LaurentLoopFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
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
import D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment

/-! Laurent coordinates retain all exponents and their exact matrix coefficients. -/

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open LaurentPolynomial Matrix

namespace D5.S3.ContinuousObservables.LaurentLoopFactorization

set_option backward.isDefEq.respectTransparency false

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
    rw [_root_.zpow_neg, Circle.coe_inv_eq_conj]
    exact mul_comm _ _

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
    Finsupp.finsetSum_apply]
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
    change (T 0 : LaurentPolynomial ℂ).coeff ((n : ℤ) + n) = 0
    simp only [LaurentPolynomial.T_apply, if_neg (Ne.symm hn2)]
  have hdbot : (coefficient F (-(n : ℤ))).det = 0 := by
    rw [← det_bottom h, hdet]
    change (T 0 : LaurentPolynomial ℂ).coeff (-(n : ℤ) + -(n : ℤ)) = 0
    simp only [LaurentPolynomial.T_apply, if_neg (Ne.symm hnm2)]
  have hl := congrArg (fun A => coefficient A ((n : ℤ) + n)) hleft
  have hr := congrArg (fun A => coefficient A ((n : ℤ) + n)) hright
  rw [coefficient_mul_top _ _ _ _ (adjoint_upper_bound h) (upper_bound h),
    coefficient_adjoint] at hl
  rw [coefficient_mul_top _ _ _ _ (upper_bound h) (adjoint_upper_bound h),
    coefficient_adjoint] at hr
  have hz : coefficient (1 : Loop) ((n : ℤ) + n) = 0 := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp only [coefficient, Matrix.one_apply, Matrix.zero_apply, if_pos rfl]
      change (T 0 : LaurentPolynomial ℂ).coeff ((n : ℤ) + n) = 0
      simp only [LaurentPolynomial.T_apply, if_neg (Ne.symm hn2)]
    · simp [coefficient, Matrix.one_apply, hab]
  exact ⟨hdtop, hdbot, hl.trans hz, hr.trans hz⟩

private theorem projector_trace {P : M₂} (hP : RankOneProjector P) : P.trace = 1 := by
  rw [D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.idempotent_trace_rank P hP.2.1,
    hP.2.2, Nat.cast_one]

private theorem projector_of_trace {P : M₂} (hstar : Pᴴ = P) (hsq : P * P = P)
    (htrace : P.trace = 1) : RankOneProjector P := by
  refine ⟨hstar, hsq, ?_⟩
  have ht :=
    D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.idempotent_trace_rank P hsq
  rw [htrace] at ht
  exact_mod_cast ht.symm

private theorem projector_complement {P : M₂} (hP : RankOneProjector P) :
    RankOneProjector (1 - P) := by
  have hproj : IsStarProjection P := ⟨hP.2.1, hP.1⟩
  refine projector_of_trace hproj.one_sub.isSelfAdjoint.star_eq
    hproj.one_sub.isIdempotentElem.eq ?_
  rw [Matrix.trace_sub, projector_trace hP]
  norm_num [Matrix.trace, Fin.sum_univ_two]

private def rowProjection (A : M₂) : M₂ := (Aᴴ * A).trace⁻¹ • (Aᴴ * A)

private theorem gram_top {A : M₂} (hA : A.det = 0) :
    A * (Aᴴ * A) = (Aᴴ * A).trace • A := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by
    simpa only [Matrix.det_fin_two] using hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace,
      Matrix.diag_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Fin.reduceFinMk]
  · linear_combination -(star (A 1 1)) * hd
  · linear_combination (star (A 1 0)) * hd
  · linear_combination (star (A 0 1)) * hd
  · linear_combination -(star (A 0 0)) * hd

private theorem rowProjection_laws {A : M₂} (hne : A ≠ 0) (hd : A.det = 0) :
    RankOneProjector (rowProjection A) ∧ A * rowProjection A = A := by
  let B := Aᴴ * A
  have hs : B.trace ≠ 0 := by
    exact fun h => hne (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  have hB : Bᴴ = B := Matrix.isHermitian_conjTranspose_mul_self A
  have htrstar : star B.trace = B.trace := by
    rw [← Matrix.trace_conjTranspose, hB]
  have hAB : A * B = B.trace • A := gram_top hd
  have hBB : B * B = B.trace • B := by
    calc
      B * B = Aᴴ * (A * B) := by simp [B, Matrix.mul_assoc]
      _ = B.trace • B := by rw [hAB, Matrix.mul_smul]
  have hPstar : (rowProjection A)ᴴ = rowProjection A := by
    change (B.trace⁻¹ • B)ᴴ = B.trace⁻¹ • B
    rw [Matrix.conjTranspose_smul, star_inv₀, htrstar, hB]
  have hPsq : rowProjection A * rowProjection A = rowProjection A := by
    change (B.trace⁻¹ • B) * (B.trace⁻¹ • B) = B.trace⁻¹ • B
    rw [Matrix.smul_mul, Matrix.mul_smul, hBB, smul_smul, smul_smul]
    congr 1
    field_simp
  have hPtr : (rowProjection A).trace = 1 := by
    change (B.trace⁻¹ • B).trace = 1
    rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hs]
  refine ⟨projector_of_trace hPstar hPsq hPtr, ?_⟩
  change A * (B.trace⁻¹ • B) = A
  rw [Matrix.mul_smul, hAB, smul_smul, inv_mul_cancel₀ hs, one_smul]

private theorem projector_unique {P Q : M₂} (hP : RankOneProjector P)
    (hQ : RankOneProjector Q) (hpq : P * Q = P) : P = Q := by
  have hqp : Q * P = P := by
    simpa [Matrix.conjTranspose_mul, hP.1, hQ.1] using congrArg Matrix.conjTranspose hpq
  have hdiff : (Q - P)ᴴ * (Q - P) = Q - P := by
    rw [Matrix.conjTranspose_sub, hQ.1, hP.1, sub_mul, mul_sub, mul_sub,
      hP.2.1, hQ.2.1, hpq, hqp]
    abel
  have ht : ((Q - P)ᴴ * (Q - P)).trace = 0 := by
    rw [hdiff, Matrix.trace_sub, projector_trace hP, projector_trace hQ, sub_self]
  exact (sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht)).symm

private theorem rowProjection_unique {A Q : M₂} (hne : A ≠ 0) (hd : A.det = 0)
    (hQ : RankOneProjector Q) (haq : A * Q = A) : Q = rowProjection A := by
  apply (projector_unique (rowProjection_laws hne hd).1 hQ ?_).symm
  unfold rowProjection
  rw [Matrix.smul_mul, Matrix.mul_assoc, haq]

private theorem terminal_cancellation {n : ℕ} {F : Loop} (hn : 0 < n)
    (hF : InClass n F) (hdeg : ActualDegree n F) :
    ∃! P : M₂, RankOneProjector P ∧
      coefficient F n * (1 - P) = 0 ∧ coefficient F (-(n : ℤ)) * P = 0 := by
  obtain ⟨hdetA, hdetD, _, horth⟩ := endpoints hn hF
  by_cases hA : coefficient F n = 0
  · have hD : coefficient F (-(n : ℤ)) ≠ 0 := hdeg.resolve_left (not_not.mpr hA)
    let Q := rowProjection (coefficient F (-(n : ℤ)))
    have hQ := rowProjection_laws hD hdetD
    refine ⟨1 - Q, ⟨projector_complement hQ.1, by rw [hA, zero_mul], ?_⟩, ?_⟩
    · rw [mul_sub, mul_one, hQ.2, sub_self]
    · intro P hP
      have he : 1 - P = Q := rowProjection_unique hD hdetD (projector_complement hP.1) (by
        rw [mul_sub, mul_one, hP.2.2, sub_zero])
      simpa only [sub_sub_cancel] using congrArg (fun X : M₂ => 1 - X) he
  · let P := rowProjection (coefficient F n)
    have hP := rowProjection_laws hA hdetA
    have hDP : coefficient F (-(n : ℤ)) * P = 0 := by
      have ho : coefficient F (-(n : ℤ)) * (coefficient F n)ᴴ = 0 := by
        simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose horth
      dsimp [P, rowProjection]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ho, zero_mul, smul_zero]
    refine ⟨P, ⟨hP.1, ?_, hDP⟩, ?_⟩
    · rw [mul_sub, mul_one, hP.2, sub_self]
    · intro Q hQ
      exact rowProjection_unique hA hdetA hQ.1 (by
        have := hQ.2.1
        rw [mul_sub, mul_one, sub_eq_zero] at this
        exact this.symm)

private theorem scalar_shift (p : LaurentPolynomial ℂ) (k : ℤ) (a : ℂ) (j : ℤ) :
    (p * (T k * C a)).coeff j = p.coeff (j - k) * a := by
  rw [mul_comm (T k), ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_mul_single_apply]
  rfl

private theorem coefficient_shift (F : Loop) (A : M₂) (k j : ℤ) :
    coefficient (F * ((T k : LaurentPolynomial ℂ) • constant A)) j =
      coefficient F (j - k) * A := by
  ext a b
  simp only [coefficient, Matrix.mul_apply, Matrix.smul_apply, constant,
    RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, scalar_shift]

private theorem coefficient_step (F : Loop) (P : M₂) (j : ℤ) :
    coefficient (F * primitive P) j =
      coefficient F (j - 1) * P + coefficient F (j + 1) * (1 - P) := by
  rw [primitive, mul_add]
  change coefficient (F * (T 1 • constant P)) j +
    coefficient (F * (T (-1) • constant (1 - P))) j = _
  rw [coefficient_shift, coefficient_shift]
  rfl

private theorem coefficient_constant (A : M₂) (j : ℤ) :
    coefficient (constant A) j = if j = 0 then A else 0 := by
  ext a b
  by_cases hj : j = 0 <;> simp [coefficient, constant, C_apply, hj]

private theorem coefficient_primitive (P : M₂) (j : ℤ) :
    coefficient (primitive P) j = (if j = 1 then P else 0) +
      (if j = -1 then 1 - P else 0) := by
  have hc : primitive P = (1 : Loop) * primitive P := (one_mul _).symm
  rw [hc, coefficient_step]
  have hid : (1 : Loop) = constant 1 := (map_one LaurentPolynomial.C.mapMatrix).symm
  rw [hid, coefficient_constant, coefficient_constant]
  have hj1 : j - 1 = 0 ↔ j = 1 := by omega
  have hjm1 : j + 1 = 0 ↔ j = -1 := by omega
  by_cases h1 : j = 1 <;> by_cases hm1 : j = -1 <;> simp_all

private theorem primitive_inverse {P : M₂} (hP : RankOneProjector P) :
    primitive P * primitive (1 - P) = 1 := by
  apply coefficient_ext
  intro j
  rw [coefficient_step, coefficient_primitive, coefficient_primitive]
  have hid : (1 : Loop) = constant 1 := (map_one LaurentPolynomial.C.mapMatrix).symm
  rw [hid, coefficient_constant]
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP.2.1, sub_self]
  have h1P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP.2.1, sub_self]
  have hPP : (1 - P) * (1 - P) = 1 - P := (projector_complement hP).2.1
  by_cases h0 : j = 0
  · subst j
    norm_num [hP.2.1, hPP]
  · have h01 : j - 1 ≠ -1 := by omega
    have h02 : j + 1 ≠ 1 := by omega
    simp only [if_neg h0, if_neg h01, if_neg h02, sub_sub_cancel]
    split_ifs <;> simp_all

private theorem adjoint_primitive {P : M₂} (hP : RankOneProjector P) :
    adjoint (primitive P) = primitive (1 - P) := by
  apply coefficient_ext
  intro j
  rw [coefficient_adjoint, coefficient_primitive, coefficient_primitive]
  have hneg1 : -j = 1 ↔ j = -1 := by omega
  have hnegm1 : -j = -1 ↔ j = 1 := by omega
  by_cases h1 : j = 1 <;> by_cases hm1 : j = -1 <;>
    simp_all [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, hP.1]

private theorem evaluate_primitive (P : M₂) (z : ℂˣ) :
    evaluate (primitive P) z = (z : ℂ) • P + (↑z⁻¹ : ℂ) • (1 - P) := by
  ext a b
  simp [evaluate, primitive, constant, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem projector_det {P : M₂} (hP : RankOneProjector P) : P.det = 0 := by
  have htrace : P 0 0 + P 1 1 = 1 := by
    simpa [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using projector_trace hP
  have hsq := congrFun (congrFun hP.2.1 0) 0
  norm_num only [Matrix.mul_apply, Fin.sum_univ_two, Fin.reduceFinMk] at hsq
  rw [Matrix.det_fin_two]
  linear_combination P 0 0 * htrace - hsq

private theorem determinant_affine (P : M₂) (s t : ℂ) :
    (s • P + t • (1 - P)).det = (s - t) ^ 2 * P.det +
      t * (s - t) * P.trace + t ^ 2 := by
  simp [Matrix.det_fin_two, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  ring

private theorem primitive_circle {P : M₂} (hP : RankOneProjector P) : CircleSU (primitive P) := by
  intro z hz
  let w : Circle := ⟨(z : ℂ), mem_sphere_zero_iff_norm.mpr hz⟩
  have hw : Circle.toUnits w = z := Units.ext rfl
  constructor
  · rw [← hw, ← evaluate_adjoint, adjoint_primitive hP, ← evaluate_mul,
      mul_eq_one_comm.mp (primitive_inverse hP)]
    simp [evaluate]
  · rw [evaluate_primitive, determinant_affine, projector_det hP, projector_trace hP]
    have hzi : (z : ℂ) * (↑z⁻¹ : ℂ) = 1 := by exact_mod_cast z.mul_inv
    linear_combination hzi

private theorem circle_mul {F G : Loop} (hF : CircleSU F) (hG : CircleSU G) :
    CircleSU (F * G) := by
  intro z hz
  rw [evaluate_mul]
  obtain ⟨hFunit, hFdet⟩ := hF z hz
  obtain ⟨hGunit, hGdet⟩ := hG z hz
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (evaluate F z)ᴴ, hFunit, one_mul, hGunit]
  · rw [Matrix.det_mul, hFdet, hGdet, one_mul]

private theorem class_raise {n : ℕ} {F : Loop} (hF : InClass n F)
    {P : M₂} (hP : RankOneProjector P) : InClass (n + 1) (F * primitive P) := by
  refine ⟨?_, circle_mul hF.2 (primitive_circle hP)⟩
  intro j hj
  rw [coefficient_step]
  have hleft : coefficient F (j - 1) = 0 := by
    apply hF.1
    simp only [lt_abs] at hj ⊢
    omega
  have hright : coefficient F (j + 1) = 0 := by
    apply hF.1
    simp only [lt_abs] at hj ⊢
    omega
  rw [hleft, hright, zero_mul, zero_mul, add_zero]

private theorem class_lower {n : ℕ} {F : Loop} (hF : InClass (n + 1) F)
    {P : M₂} (hP : RankOneProjector P)
    (hpos : coefficient F (n + 1 : ℕ) * (1 - P) = 0)
    (hneg : coefficient F (-(n + 1 : ℕ) : ℤ) * P = 0) :
    InClass n (F * primitive (1 - P)) := by
  refine ⟨?_, circle_mul hF.2 (primitive_circle (projector_complement hP))⟩
  intro j hj
  rw [coefficient_step, sub_sub_cancel]
  by_cases hjp : j = (n : ℤ) + 2
  · subst j
    rw [show (n : ℤ) + 2 - 1 = (n + 1 : ℕ) by omega, hpos,
      upper_bound hF _ (by omega), zero_mul, add_zero]
  by_cases hjm : j = -(n : ℤ) - 2
  · subst j
    rw [show -(n : ℤ) - 2 + 1 = -(n + 1 : ℕ) by omega, hneg,
      lower_bound hF _ (by omega), zero_mul, add_zero]
  have hleft : coefficient F (j - 1) = 0 := by
    apply hF.1
    simp only [lt_abs] at hj ⊢
    omega
  have hright : coefficient F (j + 1) = 0 := by
    apply hF.1
    simp only [lt_abs] at hj ⊢
    omega
  rw [hleft, hright, zero_mul, zero_mul, add_zero]

private theorem terminal_step {n : ℕ} {F : Loop} (hF : InClass (n + 1) F)
    (hdeg : ActualDegree (n + 1) F) :
    ∃! P : M₂, RankOneProjector P ∧
      InClass n (F * primitive (1 - P)) ∧
      ActualDegree n (F * primitive (1 - P)) ∧
      F = (F * primitive (1 - P)) * primitive P := by
  obtain ⟨P, ⟨hP, hpos, hneg⟩, hunique⟩ := terminal_cancellation (by omega) hF hdeg
  have hclass := class_lower hF hP hpos hneg
  have hrec : F = (F * primitive (1 - P)) * primitive P := by
    rw [Matrix.mul_assoc, mul_eq_one_comm.mp (primitive_inverse hP), mul_one]
  have hactual : ActualDegree n (F * primitive (1 - P)) := by
    by_contra h
    simp only [ActualDegree, not_or, not_not] at h
    have htop : coefficient F (n + 1 : ℕ) = 0 := by
      rw [hrec, coefficient_step, show (n + 1 : ℕ) - (1 : ℤ) = (n : ℤ) by omega,
        h.1, upper_bound hclass _ (by omega), zero_mul, zero_mul, add_zero]
    have hbot : coefficient F (-(n + 1 : ℕ) : ℤ) = 0 := by
      rw [hrec, coefficient_step, show -(n + 1 : ℕ) + (1 : ℤ) = -(n : ℤ) by omega,
        h.2, lower_bound hclass _ (by omega), zero_mul, zero_mul, add_zero]
    exact hdeg.elim (fun hn => hn htop) (fun hn => hn hbot)
  refine ⟨P, ⟨hP, hclass, hactual, hrec⟩, ?_⟩
  intro Q hQ
  apply hunique Q
  refine ⟨hQ.1, ?_, ?_⟩
  · have hz := upper_bound hQ.2.1 ((n : ℤ) + 2) (by omega)
    rw [coefficient_step, sub_sub_cancel,
      show (n : ℤ) + 2 - 1 = (n + 1 : ℕ) by omega,
      upper_bound hF ((n : ℤ) + 2 + 1) (by omega), zero_mul, add_zero] at hz
    exact hz
  · have hz := lower_bound hQ.2.1 (-(n : ℤ) - 2) (by omega)
    rw [coefficient_step, sub_sub_cancel,
      show -(n : ℤ) - 2 + 1 = -(n + 1 : ℕ) by omega,
      lower_bound hF _ (by omega), zero_mul, zero_add] at hz
    exact hz

/-- The constant factor is any special-unitary matrix. -/
def SpecialUnitary (A : M₂) : Prop := Aᴴ * A = 1 ∧ A.det = 1

/-- The product follows the list order, with the constant on the left. -/
def orderedProduct (A : M₂) (Ps : List M₂) : Loop :=
  constant A * (Ps.map primitive).prod

def Factorization (n : ℕ) (F : Loop) (r : M₂ × List M₂) : Prop :=
  SpecialUnitary r.1 ∧ r.2.length = n ∧
    (∀ P ∈ r.2, RankOneProjector P) ∧ F = orderedProduct r.1 r.2

private theorem orderedProduct_append (A P : M₂) (Ps : List M₂) :
    orderedProduct A (Ps ++ [P]) = orderedProduct A Ps * primitive P := by
  simp [orderedProduct, List.map_append, List.prod_append, mul_assoc]

private theorem class_constant {A : M₂} (hA : SpecialUnitary A) : InClass 0 (constant A) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [coefficient_constant]
    have hj0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    exact ite_eq_right hj0
  · intro z _
    simpa only [evaluate_constant, SpecialUnitary] using hA

private theorem class_orderedProduct {A : M₂} (hA : SpecialUnitary A) (Ps : List M₂)
    (hPs : ∀ P ∈ Ps, RankOneProjector P) : InClass Ps.length (orderedProduct A Ps) := by
  induction Ps using List.reverseRecOn with
  | nil => simpa [orderedProduct] using class_constant hA
  | append_singleton Ps P ih =>
    rw [List.length_append, List.length_singleton, orderedProduct_append]
    apply class_raise (ih (fun Q hQ => hPs Q (List.mem_append_left _ hQ)))
    exact hPs P (by simp)

private theorem zero_class_constant {F : Loop} (hF : InClass 0 F) :
    F = constant (coefficient F 0) := by
  apply coefficient_ext
  intro j
  rw [coefficient_constant]
  by_cases hj : j = 0
  · subst j; simp
  · rw [ite_eq_right hj]
    exact hF.1 j (Or.inl (by simpa using abs_pos.mpr hj))

private theorem zero_constant_su {F : Loop} (hF : InClass 0 F) :
    SpecialUnitary (coefficient F 0) := by
  have he := hF.2 1 (by simp)
  rw [zero_class_constant hF, evaluate_constant] at he
  exact he

/-- Recursively remove the unique terminal factor at each exact input degree. -/
def decompose : (n : ℕ) → (F : Loop) → InClass n F → ActualDegree n F → M₂ × List M₂
  | 0, F, _, _ => (coefficient F 0, [])
  | n + 1, F, hF, hdeg =>
    let h := (terminal_step hF hdeg).exists
    let P := Classical.choose h
    let hp := Classical.choose_spec h
    let r := decompose n (F * primitive (1 - P)) hp.2.1 hp.2.2.1
    (r.1, r.2 ++ [P])

private theorem decompose_spec (n : ℕ) (F : Loop) (hF : InClass n F)
    (hdeg : ActualDegree n F) : Factorization n F (decompose n F hF hdeg) := by
  induction n generalizing F with
  | zero =>
    change Factorization 0 F (coefficient F 0, [])
    exact ⟨zero_constant_su hF, rfl, by simp, by simpa [orderedProduct] using zero_class_constant hF⟩
  | succ n ih =>
    let h := (terminal_step hF hdeg).exists
    let P := Classical.choose h
    have hp := Classical.choose_spec h
    let r := decompose n (F * primitive (1 - P)) hp.2.1 hp.2.2.1
    have hr : Factorization n (F * primitive (1 - P)) r := ih _ hp.2.1 hp.2.2.1
    change Factorization (n + 1) F (r.1, r.2 ++ [P])
    refine ⟨hr.1, by simp [hr.2.1], ?_, ?_⟩
    · intro Q hQ
      rcases List.mem_append.mp hQ with hQ | hQ
      · exact hr.2.2.1 Q hQ
      · have heq := List.mem_singleton.mp hQ
        simpa only [heq] using hp.1
    · rw [orderedProduct_append, ← hr.2.2.2]
      exact hp.2.2.2

private theorem last_cancellation {n : ℕ} {G : Loop} (hG : InClass n G)
    {P : M₂} (hP : RankOneProjector P) :
    coefficient (G * primitive P) (n + 1 : ℕ) * (1 - P) = 0 ∧
      coefficient (G * primitive P) (-(n + 1 : ℕ) : ℤ) * P = 0 := by
  have hP1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP.2.1, sub_self]
  have h1P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP.2.1, sub_self]
  constructor
  · rw [coefficient_step, upper_bound hG ((n + 1 : ℕ) + (1 : ℤ)) (by omega),
      zero_mul, add_zero, mul_assoc, hP1, mul_zero]
  · rw [coefficient_step, lower_bound hG (-(n + 1 : ℕ) - (1 : ℤ)) (by omega),
      zero_mul, zero_add, mul_assoc, h1P, mul_zero]

private theorem factorization_unique (n : ℕ) (F : Loop) (hF : InClass n F)
    (hdeg : ActualDegree n F) (r s : M₂ × List M₂)
    (hr : Factorization n F r) (hs : Factorization n F s) : r = s := by
  induction n generalizing F r s with
  | zero =>
    have hrnil : r.2 = [] := List.length_eq_zero_iff.mp hr.2.1
    have hsnil : s.2 = [] := List.length_eq_zero_iff.mp hs.2.1
    have he : constant r.1 = constant s.1 := by
      simpa [orderedProduct, hrnil, hsnil] using hr.2.2.2.symm.trans hs.2.2.2
    have hA : r.1 = s.1 := by
      simpa [coefficient_constant] using congrArg (fun X => coefficient X 0) he
    exact Prod.ext hA (hrnil.trans hsnil.symm)
  | succ n ih =>
    have hrne : r.2 ≠ [] := by
      intro he
      have hh := hr.2.1
      rw [he] at hh
      simp at hh
    have hsne : s.2 ≠ [] := by
      intro he
      have hh := hs.2.1
      rw [he] at hh
      simp at hh
    obtain ⟨R, P, hrlist⟩ : ∃ R P, r.2 = R ++ [P] := by
      rcases List.eq_nil_or_concat r.2 with h | ⟨R, P, h⟩
      · exact False.elim (hrne h)
      · exact ⟨R, P, by simpa using h⟩
    obtain ⟨S, Q, hslist⟩ : ∃ S Q, s.2 = S ++ [Q] := by
      rcases List.eq_nil_or_concat s.2 with h | ⟨S, Q, h⟩
      · exact False.elim (hsne h)
      · exact ⟨S, Q, by simpa using h⟩
    have hRlen : R.length = n := by
      have hh := hr.2.1
      rw [hrlist, List.length_append, List.length_singleton] at hh
      omega
    have hSlen : S.length = n := by
      have hh := hs.2.1
      rw [hslist, List.length_append, List.length_singleton] at hh
      omega
    have hP : RankOneProjector P := hr.2.2.1 P (by simp [hrlist])
    have hQ : RankOneProjector Q := hs.2.2.1 Q (by simp [hslist])
    have hRall : ∀ X ∈ R, RankOneProjector X := fun X hX => hr.2.2.1 X (by simp [hrlist, hX])
    have hSall : ∀ X ∈ S, RankOneProjector X := fun X hX => hs.2.2.1 X (by simp [hslist, hX])
    have hRc : InClass n (orderedProduct r.1 R) := hRlen ▸ class_orderedProduct hr.1 R hRall
    have hSc : InClass n (orderedProduct s.1 S) := hSlen ▸ class_orderedProduct hs.1 S hSall
    have heR : F = orderedProduct r.1 R * primitive P := by
      simpa [hrlist, orderedProduct_append] using hr.2.2.2
    have heS : F = orderedProduct s.1 S * primitive Q := by
      simpa [hslist, orderedProduct_append] using hs.2.2.2
    obtain ⟨T, hT, huniq⟩ := terminal_cancellation (by omega) hF hdeg
    have hPeq : P = T := huniq P ⟨hP, by rw [heR]; exact (last_cancellation hRc hP).1,
      by rw [heR]; exact (last_cancellation hRc hP).2⟩
    have hQeq : Q = T := huniq Q ⟨hQ, by rw [heS]; exact (last_cancellation hSc hQ).1,
      by rw [heS]; exact (last_cancellation hSc hQ).2⟩
    have hPQ : P = Q := hPeq.trans hQeq.symm
    obtain ⟨U, hU, _⟩ := terminal_step hF hdeg
    have hPU : P = U := by
      have hUc := last_cancellation hU.2.1 hU.1
      exact hPeq.trans (huniq U ⟨hU.1, by rw [hU.2.2.2]; exact hUc.1,
        by rw [hU.2.2.2]; exact hUc.2⟩).symm
    rw [← hPU] at hU
    have hFredR : F * primitive (1 - P) = orderedProduct r.1 R := by
      rw [heR, mul_assoc, primitive_inverse hP, mul_one]
    have hFredS : F * primitive (1 - P) = orderedProduct s.1 S := by
      rw [heS, ← hPQ, mul_assoc, primitive_inverse hP, mul_one]
    have hprefix := ih _ hU.2.1 hU.2.2.1 (r.1, R) (s.1, S)
      ⟨hr.1, hRlen, hRall, hFredR⟩ ⟨hs.1, hSlen, hSall, hFredS⟩
    have hpair := Prod.mk.inj hprefix
    exact Prod.ext hpair.1 (by rw [hrlist, hslist, hpair.2, hPQ])

/-- Haah's exact-degree ordered factorization, with the forward class assertion. -/
theorem haah_factorization :
    (∀ Ps : List M₂, (∀ P ∈ Ps, RankOneProjector P) →
      InClass Ps.length (Ps.map primitive).prod) ∧
    ∀ (n : ℕ) (C : ℤ →₀ M₂),
      (∀ j : ℤ, (n : ℤ) < |j| ∨ j % 2 ≠ (n : ℤ) % 2 → C j = 0) →
      (C n ≠ 0 ∨ C (-(n : ℤ)) ≠ 0) → CircleSU (ofCoefficients C) →
      ∃! r : M₂ × List M₂, Factorization n (ofCoefficients C) r := by
  constructor
  · intro Ps hPs
    simpa [orderedProduct, constant] using
      class_orderedProduct (A := 1) ⟨by simp, by simp⟩ Ps hPs
  · intro n C hbound hdeg hcircle
    have hF : InClass n (ofCoefficients C) := ⟨hbound, hcircle⟩
    have hD : ActualDegree n (ofCoefficients C) := hdeg
    exact ⟨decompose n _ hF hD, decompose_spec n _ hF hD,
      fun r hr => factorization_unique n _ hF hD _ _ hr (decompose_spec n _ hF hD)⟩
end D5.S3.ContinuousObservables.LaurentLoopFactorization
