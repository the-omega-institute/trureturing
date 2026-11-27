/- GID: D5/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/FiniteTraceDeterminantMass
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual trace and determinant fiber sizes and exact uniform conditional trace mass. -/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Fintype.Option
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.FiniteTraceDeterminantMass
open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Pairs of field elements with prescribed product. -/
abbrev MulFiber (w : F) := {q : F × F // q.1*q.2=w}

private def nonzeroMulEquiv (w : F) (hw : w ≠ 0) : MulFiber w ≃ {a : F // a ≠ 0} where
  toFun q := ⟨q.1.1, fun hz => hw (by simpa [hz] using q.2.symm)⟩
  invFun a := ⟨(a.1,w/a.1), by field_simp [a.2]⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,h⟩
    apply Subtype.ext
    change (x,w/x) = (x,y)
    rw [← h]
    have hx : x ≠ 0 := left_ne_zero_of_mul (h ▸ hw)
    simp [mul_comm x y, hx]
  right_inv := by intro q; rfl

private def zeroMulEquiv : MulFiber (0:F) ≃ F ⊕ {a : F // a ≠ 0} where
  toFun q := if h : q.1.1=0 then Sum.inl q.1.2 else Sum.inr ⟨q.1.1,h⟩
  invFun
    | Sum.inl a => ⟨(0,a), zero_mul _⟩
    | Sum.inr a => ⟨(a.1,0), mul_zero _⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,h⟩
    by_cases hx : x=0
    · subst x
      simp
    · have hy : y=0 := (mul_eq_zero.mp h).resolve_left hx
      subst y
      simp [hx]
  right_inv := by
    rintro (a | ⟨a,ha⟩)
    · simp
    · simp [ha]

theorem mul_fiber_card (w : F) : Fintype.card (MulFiber w) =
    if w=0 then 2*Fintype.card F-1 else Fintype.card F-1 := by
  have hn : Fintype.card {a : F // a ≠ 0} = Fintype.card F-1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  by_cases hw : w=0
  · subst w
    rw [ite_eq_left rfl, Fintype.card_congr (zeroMulEquiv (F:=F)), Fintype.card_sum, hn]
    omega
  · rw [ite_eq_right hw, Fintype.card_congr (nonzeroMulEquiv w hw), hn]

/-- Actual matrices with prescribed trace and determinant. -/
abbrev TraceDetFiber (t d : F) :=
  {M : Matrix (Fin 2) (Fin 2) F // M.trace=t ∧ M.det=d}

private def fibEquiv (t d : F) :
    TraceDetFiber t d ≃ Σ a : F, MulFiber (a*(t-a)-d) where
  toFun M := ⟨M.1 0 0, ⟨(M.1 0 1,M.1 1 0), by
    have h := M.2.1
    have H := M.2.2
    rw [Matrix.trace_fin_two] at h
    rw [Matrix.det_fin_two] at H
    have ha : M.1 1 1 = t-M.1 0 0 := by linear_combination h
    rw [ha] at H
    linear_combination -H⟩⟩
  invFun q := ⟨!![q.1,q.2.1.1;q.2.1.2,t-q.1], by
    constructor
    · rw [Matrix.trace_fin_two_of]
      ring
    · rw [Matrix.det_fin_two_of, q.2.2]
      ring⟩
  left_inv := by
    intro M
    apply Subtype.ext
    have h := M.2.1
    rw [Matrix.trace_fin_two] at h
    ext i k
    fin_cases i <;> fin_cases k <;> simp
    linear_combination -h
  right_inv := by rintro ⟨a,⟨⟨b,c⟩,h⟩⟩; rfl

/-- Actual matrix trace and determinant fibers reduce uniformly to the
number of roots of the corresponding characteristic quadratic. -/
theorem matrix_trace_det_fiber_card (t d : F) :
    Fintype.card (TraceDetFiber t d) =
      Fintype.card F * (Fintype.card F - 1 +
        Fintype.card {a : F // a*(t-a)=d}) := by
  let q := Fintype.card F
  have hq : 0 < q := Fintype.card_pos
  rw [Fintype.card_congr (fibEquiv t d), Fintype.card_sigma]
  simp_rw [mul_fiber_card]
  change (∑ a : F, if a*(t-a)-d=0 then 2*q-1 else q-1) = _
  have H (a : F) : (if a*(t-a)-d=0 then 2*q-1 else q-1) =
      (q-1) + (if a*(t-a)=d then q else 0) := by
    by_cases h : a*(t-a)=d
    · simp [h]
      omega
    · have hh := sub_ne_zero.mpr h
      simp [hh,h]
  simp only [H, Finset.sum_add_distrib]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_subtype]
  change q*(q-1) + (Finset.univ.filter (fun a : F => a*(t-a)=d)).card*q = _
  ring

private def traceRootEquiv (t d : F) (h2 : (2:F) ≠ 0) :
    {a : F // a*(t-a)=d} ≃ {x : F // x^2=t^2-4*d} where
  toFun a := ⟨2*a.1-t,by linear_combination -4*a.2⟩
  invFun x := ⟨(x.1+t)/2,by
    have H : 2*((x.1+t)/2)-t=x.1 := by
      field_simp
      ring
    have h : (2*((x.1+t)/2)-t)^2=t^2-4*d := by rw [H,x.2]
    have h4 : (4:F) ≠ 0 := by
      rw [show (4:F)=2*2 by ring]
      exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    linear_combination -h⟩
  left_inv := by
    intro a
    apply Subtype.ext
    change (2*a.1-t+t)/2=a.1
    field_simp
    ring
  right_inv := by
    intro x
    apply Subtype.ext
    change 2*((x.1+t)/2)-t=x.1
    field_simp
    ring

/-- Uniform determinant-trace counting law over every odd finite field,
expressed in terms of the actual discriminant quadratic character. -/
theorem matrix_trace_det_quadratic_character_card (t d : F)
    (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    (Fintype.card (TraceDetFiber t d) : ℤ) =
      (Fintype.card F : ℤ)*((Fintype.card F : ℤ)+quadraticChar F (t^2-4*d)) := by
  have hN : 1 ≤ Fintype.card F := Fintype.card_pos
  have hc : (Fintype.card {a : F // a*(t-a)=d}:ℤ) =
      quadraticChar F (t^2-4*d)+1 := by
    rw [Fintype.card_congr (traceRootEquiv t d h2), Fintype.card_subtype]
    simpa only [Set.toFinset_ofPred] using quadraticChar_card_sqrts hchar (t^2-4*d)
  rw [matrix_trace_det_fiber_card]
  push_cast [Nat.cast_sub hN]
  rw [hc]
  ring

/-- Actual matrices with prescribed determinant. -/
abbrev DetFiber (d : F) := {M : Matrix (Fin 2) (Fin 2) F // M.det = d}

private def detFiberEquivSL (d : F) (hd : d ≠ 0) :
    DetFiber d ≃ Matrix.SpecialLinearGroup (Fin 2) F where
  toFun M := ⟨!![M.1 0 0 / d, M.1 0 1 / d; M.1 1 0, M.1 1 1], by
    rw [Matrix.det_fin_two_of]
    have h := M.2
    rw [Matrix.det_fin_two] at h
    field_simp [hd, div_eq_mul_inv, mul_comm]
    linear_combination h⟩
  invFun M := ⟨!![d * M.1 0 0, d * M.1 0 1; M.1 1 0, M.1 1 1], by
    rw [Matrix.det_fin_two_of]
    have h := M.2
    rw [Matrix.det_fin_two] at h
    linear_combination d*h⟩
  left_inv := by
    intro M
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, div_eq_mul_inv, mul_comm]
  right_inv := by
    intro M
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, div_eq_mul_inv, mul_comm]

/-- Every nonzero determinant fiber has the same cardinality as the actual
special linear group, via scaling the first row. -/
theorem det_fiber_card (d : F) (hd : d ≠ 0) :
    Fintype.card (DetFiber d) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (detFiberEquivSL d hd),
    Matrix.card_SL_field]
  let q := Fintype.card F
  change (∏ i : Fin 2, (q ^ 2 - q ^ (i : ℕ))) / (q-1) = q*(q^2-1)
  have hq : 1 < q := Fintype.one_lt_card
  rw [Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  have h : q^2-q = q*(q-1) := by rw [Nat.mul_sub, Nat.mul_one, pow_two]
  rw [h, ← mul_assoc, Nat.mul_div_cancel _ (by omega : 0 < q-1)]
  ac_rfl

/-- Exact conditional mass of a trace under the uniform distribution on
the nonzero determinant fiber, for every odd finite field. -/
theorem uniform_trace_mass (t d : F) (hd : d ≠ 0)
    (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    (Fintype.card (TraceDetFiber t d) : ℚ) / (Fintype.card (DetFiber d) : ℚ) =
      ((Fintype.card F : ℚ) + (quadraticChar F (t^2-4*d) : ℚ)) /
        ((Fintype.card F : ℚ)^2 - 1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqQ : (1 : ℚ) < Fintype.card F := by exact_mod_cast hq
  have hn : 1 ≤ Fintype.card F ^ 2 := by nlinarith
  have num := matrix_trace_det_quadratic_character_card t d hchar h2
  have hcast := congrArg (fun x : ℤ => (x : ℚ)) num
  push_cast at hcast
  rw [hcast, det_fiber_card d hd]
  push_cast [Nat.cast_sub hn]
  have h0 : (Fintype.card F : ℚ) ≠ 0 := by linarith
  have hden : (Fintype.card F : ℚ)^2 - 1 ≠ 0 := by nlinarith
  field_simp

end D5.S3.Factorization.QuadraticIdeals.FiniteTraceDeterminantMass
