/- GID: D5/S1/Recurrence/FiniteCompanionCyclicModule
   generality: G
   mirror-B: D5/B/S1/Recurrence/FiniteCompanionCyclicModule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-vertex cyclic presentation with explicit coordinates and exact principal kernel. -/
import D5.S1.Recurrence.FiniteCompanionSquareDefect
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S1.Recurrence.FiniteCompanionCyclicModule
open Polynomial
open scoped BigOperators
variable {A : Type*} [CommRing A]

/-- Coordinate polynomials for forward companion time. -/
def H (u : A) (j : ℕ) : A[X] := X ^ j - C u * ∑ k ∈ Finset.range j, X ^ k

/-- The terminal coordinate relation. -/
def P (u : A) (q : ℕ) : A[X] := H u q

/-- The polynomial quotient, with its canonical polynomial-module structure. -/
abbrev CyclicQ (u : A) (q : ℕ) := A[X] ⧸ (Ideal.span {P u q} : Ideal A[X])

/-- The canonical polynomial quotient projection. -/
def projection (u : A) (q : ℕ) : A[X] →+* CyclicQ u q := Ideal.Quotient.mk _

/-- The original time supplier, extended by its coefficient linearity. -/
def time (u : A) : (q : ℕ) → 0 < q → Module.End A (Fin q → A)
  | 0, hq => (Nat.not_lt_zero 0 hq).elim
  | n + 1, _ =>
    { __ := FiniteCompanionSquareDefect.time (LinearMap.mulRight A u).toAddMonoidHom n
      map_smul' a v := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [FiniteCompanionSquareDefect.time, Finset.mul_sum, mul_assoc]
        · rfl }

/-- The first vertex, used as the cyclic generator. -/
def e0 (q : ℕ) (hq : 0 < q) : Fin q → A := Pi.single ⟨0, hq⟩ 1

private def vertex (q j : ℕ) : Fin q → A := fun i => if i.val = j then 1 else 0

private theorem vertex_zero (q : ℕ) (hq : 0 < q) : vertex q 0 = (e0 q hq : Fin q → A) := by
  classical
  ext i
  simp [vertex, e0, Pi.single_apply, Fin.ext_iff]

private theorem vertex_terminal (q : ℕ) : (vertex q q : Fin q → A) = 0 := by
  ext i
  simp [vertex, Nat.ne_of_lt i.isLt]

private theorem vertex_sum (q j : ℕ) (hj : j < q) : ∑ i, (vertex q j : Fin q → A) i = 1 := by
  classical
  simpa [vertex, Fin.ext_iff] using
    (Finset.sum_eq_single (⟨j,hj⟩ : Fin q)
      (fun i _ hi => by simp [vertex, show i.val ≠ j from fun h => hi (Fin.ext h)])
      (fun hi => (hi (Finset.mem_univ _)).elim) :
        (∑ i, (vertex q j : Fin q → A) i) = vertex q j ⟨j,hj⟩)

private theorem time_vertex (u : A) (q : ℕ) (hq : 0 < q) (j : ℕ) (hj : j < q) :
    time u q hq (vertex q j) = u • e0 q hq + vertex q (j + 1) := by
  cases q with
  | zero => omega
  | succ n =>
    classical
    ext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change (∑ x, vertex (n + 1) j x) * u = _
      rw [vertex_sum _ _ hj]
      simp [e0, vertex]
    · simp [time, FiniteCompanionSquareDefect.time, e0, vertex,
        Fin.ext_iff, Nat.add_right_cancel_iff]

private theorem H_zero (u : A) : H u 0 = 1 := by simp [H]

private theorem H_succ (u : A) (j : ℕ) : H u (j + 1) = X * H u j - C u := by
  simp only [H, Finset.sum_range_succ', pow_zero, pow_succ]
  rw [← Finset.sum_mul]
  ring

/-- Polynomial evaluation at time on the distinguished first vertex. -/
def evaluate (u : A) (q : ℕ) (hq : 0 < q) :
    A[X] →ₗ[A[X]] Module.AEval' (time u q hq) :=
  LinearMap.toSpanSingleton A[X] _ (Module.AEval'.of (time u q hq) (e0 q hq))

private theorem evaluate_H (u : A) (q : ℕ) (hq : 0 < q) (j : ℕ) (hj : j ≤ q) :
    evaluate u q hq (H u j) = Module.AEval'.of (time u q hq) (vertex q j) := by
  induction j with
  | zero => simp [H_zero, evaluate, vertex_zero q hq]
  | succ j ih =>
    rw [H_succ, map_sub, show X * H u j = X • H u j from (smul_eq_mul _ _).symm, map_smul]
    rw [ih (by omega), Module.AEval'.X_smul_of, time_vertex u q hq j (by omega)]
    have hc : evaluate u q hq (C u) = u • Module.AEval'.of (time u q hq) (e0 q hq) := by
      simp [evaluate, Module.AEval.C_smul]
    rw [hc, map_add, map_smul]
    simp

private theorem evaluate_P (u : A) (q : ℕ) (hq : 0 < q) :
    evaluate u q hq (P u q) = 0 := by
  rw [P, evaluate_H u q hq q le_rfl, vertex_terminal, map_zero]

/-- The explicit inverse coordinate polynomial before passing to the quotient. -/
def coordinatePolynomial (u : A) (q : ℕ) (v : Fin q → A) : A[X] :=
  ∑ j, C (v j) * H u j.val

private def coordinates (u : A) (q : ℕ) : (Fin q → A) →ₗ[A] CyclicQ u q where
  toFun v := ∑ j, v j • projection u q (H u j.val)
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

private theorem coordinates_vertex (u : A) (q j : ℕ) (hj : j < q) :
    coordinates u q (vertex q j) = projection u q (H u j) := by
  classical
  change (∑ i : Fin q, (if i.val = j then 1 else 0) • _) = _
  rw [Finset.sum_eq_single (⟨j,hj⟩ : Fin q)]
  · simp
  · intro i _ hi
    simp [show i.val ≠ j from fun h => hi (Fin.ext h)]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

private theorem coordinates_next (u : A) (q j : ℕ) (hj : j ≤ q) :
    coordinates u q (vertex q j) = projection u q (H u j) := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · exact coordinates_vertex u q j hj
  · rw [vertex_terminal, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (P u j)))).symm

private theorem vertex_decomposition (q : ℕ) (v : Fin q → A) :
    ∑ j : Fin q, v j • vertex q j.val = v := by
  classical
  ext i
  simp [vertex, Finset.sum_apply, Fin.val_eq_val]

private theorem coordinates_time (u : A) (q : ℕ) (hq : 0 < q) (v : Fin q → A) :
    coordinates u q (time u q hq v) = (X : A[X]) • coordinates u q v := by
  have hb (j : Fin q) : coordinates u q (time u q hq (vertex q j.val)) =
      (X : A[X]) • coordinates u q (vertex q j.val) := by
    rw [time_vertex u q hq j.val j.isLt, map_add, map_smul,
      ← vertex_zero q hq, coordinates_vertex u q 0 hq,
      coordinates_next u q (j.val + 1) (by omega), coordinates_vertex u q j.val j.isLt]
    rw [H_zero, map_one, H_succ, map_sub, map_mul]
    change u • (1 : CyclicQ u q) + (projection u q X *
      projection u q (H u j.val) - projection u q (C u)) = _
    have hc : u • (1 : CyclicQ u q) = projection u q (C u) := by
      simp only [Algebra.smul_def, mul_one]
      rfl
    rw [hc]
    change _ = projection u q X * projection u q (H u j.val)
    abel
  conv_lhs => rw [← vertex_decomposition q v]
  rw [map_sum, map_sum]
  simp_rw [map_smul, hb, smul_comm (v _ : A) (X : A[X])]
  have hs : (∑ j : Fin q, v j • coordinates u q (vertex q j.val)) = coordinates u q v := by
    simp_rw [← map_smul]
    rw [← map_sum, vertex_decomposition]
  rw [← Finset.smul_sum, hs]

private def polynomialCoordinates (u : A) (q : ℕ) (hq : 0 < q) :
    Module.AEval' (time u q hq) →ₗ[A[X]] CyclicQ u q :=
  LinearMap.ofAEval (time u q hq) (coordinates u q) (coordinates_time u q hq)

private theorem coordinates_e0 (u : A) (q : ℕ) (hq : 0 < q) :
    coordinates u q (e0 q hq) = 1 := by
  rw [← vertex_zero q hq, coordinates_vertex u q 0 hq, H_zero, map_one]

private theorem coordinates_evaluate (u : A) (q : ℕ) (hq : 0 < q) (f : A[X]) :
    polynomialCoordinates u q hq (evaluate u q hq f) = projection u q f := by
  rw [evaluate, LinearMap.toSpanSingleton_apply, map_smul]
  change f • coordinates u q (e0 q hq) = _
  rw [coordinates_e0]
  change (Submodule.Quotient.mk (f * 1) : CyclicQ u q) = projection u q f
  simp only [mul_one]
  rfl

private theorem evaluate_coordinates (u : A) (q : ℕ) (hq : 0 < q) (v : Fin q → A) :
    evaluate u q hq (coordinatePolynomial u q v) = Module.AEval'.of (time u q hq) v := by
  simp only [coordinatePolynomial, map_sum, ← smul_eq_mul, map_smul,
    evaluate_H u q hq _ (Nat.le_of_lt (Fin.isLt _)), Module.AEval.C_smul]
  simp_rw [← map_smul]
  rw [← map_sum, vertex_decomposition]

/-- Exact principal kernel; used to construct the quotient equivalence. -/
theorem evaluate_ker (u : A) (q : ℕ) (hq : 0 < q) :
    LinearMap.ker (evaluate u q hq) = (Ideal.span {P u q} : Ideal A[X]) := by
  ext f
  constructor
  · intro hf
    have h := coordinates_evaluate u q hq f
    rw [LinearMap.mem_ker.mp hf, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h.symm
  · intro hf
    rcases Ideal.mem_span_singleton.mp hf with ⟨g, rfl⟩
    rw [LinearMap.mem_ker, mul_comm, ← smul_eq_mul, map_smul, evaluate_P, smul_zero]

private theorem evaluate_surjective (u : A) (q : ℕ) (hq : 0 < q) :
    Function.Surjective (evaluate u q hq) := by
  intro v
  exact ⟨coordinatePolynomial u q ((Module.AEval'.of _).symm v),
    (evaluate_coordinates u q hq _).trans (LinearEquiv.apply_symm_apply _ v)⟩

/-- First-vertex normalized polynomial-module equivalence, including the zero ring. -/
def cyclicEquiv (u : A) (q : ℕ) (hq : 0 < q) :
    CyclicQ u q ≃ₗ[A[X]] Module.AEval' (time u q hq) :=
  (Submodule.quotEquivOfEq _ _ (evaluate_ker u q hq).symm).trans
    ((evaluate u q hq).quotKerEquivOfSurjective (evaluate_surjective u q hq))

/-- The forward evaluation and explicit coordinate inverse, with e0 normalization. -/
theorem cyclic_presentation (u : A) (q : ℕ) (hq : 0 < q) :
    (∀ f : A[X], cyclicEquiv u q hq (projection u q f) =
      Module.AEval'.of (time u q hq) ((aeval (time u q hq) f) (e0 q hq))) ∧
    (∀ v : Fin q → A, (cyclicEquiv u q hq).symm (Module.AEval'.of (time u q hq) v) =
      projection u q (coordinatePolynomial u q v)) ∧
    cyclicEquiv u q hq 1 = Module.AEval'.of (time u q hq) (e0 q hq) := by
  have hf (f : A[X]) : cyclicEquiv u q hq (projection u q f) = evaluate u q hq f := rfl
  refine ⟨hf, ?_, ?_⟩
  · intro v
    apply (cyclicEquiv u q hq).injective
    rw [LinearEquiv.apply_symm_apply, hf, evaluate_coordinates]
  · simpa only [map_one, evaluate, LinearMap.toSpanSingleton_apply, one_smul] using hf 1

end D5.S1.Recurrence.FiniteCompanionCyclicModule
