/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportIdealIntersectionLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportIdealIntersectionLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact six-cell quotient lifts to actual ideal-intersection Laplacian eigenvectors. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
import D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
import Mathlib.Tactic

/-! Exact six-cell operator transport, including derived weighted cancellation. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift

open Finset Matrix
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot

/-- Three positive exponents, in the source quotient's coordinate order. -/
def exponents (a b c : ℕ) : Fin 3 → ℕ := ![a,b,c]

/-- The six nonempty proper supports, in order 1,2,3,12,13,23. -/
def cell (i : Fin 6) : Finset (Fin 3) :=
  ![{0},{1},{2},{0,1},{0,2},{1,2}] i

/-- Extend a quotient vector by zero at empty and full support. -/
def value (z : Fin 6 → ℝ) (S : Finset (Fin 3)) : ℝ :=
  if 0 ∈ S then
    if 1 ∈ S then if 2 ∈ S then 0 else z 3
    else if 2 ∈ S then z 4 else z 0
  else if 1 ∈ S then if 2 ∈ S then z 5 else z 1
  else if 2 ∈ S then z 2 else 0

private theorem positive (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ i, 0 < exponents a b c i := by
  intro i
  fin_cases i <;> simp [exponents] <;> assumption

private theorem support_univ :
    (univ : Finset (Finset (Fin 3))) =
      {∅,{0},{1},{0,1},{2},{0,2},{1,2},{0,1,2}} := by decide

private theorem sum_support (f : Finset (Fin 3) → ℝ) :
    (∑ S, f S) = f ∅ + (f {0} + (f {1} + (f {0,1} +
      (f {2} + (f {0,2} + (f {1,2} + f {0,1,2})))))) := by
  rw [support_univ]
  simp (disch := decide) only [sum_insert, sum_singleton]

private theorem value_cell (z : Fin 6 → ℝ) (i : Fin 6) :
    value z (cell i) = z i := by
  fin_cases i <;> simp [value, cell]

private theorem cell_nonempty (i : Fin 6) : (cell i).Nonempty := by
  fin_cases i <;> simp [cell]

private theorem cell_ne_univ (i : Fin 6) : cell i ≠ univ := by
  fin_cases i <;> decide

/-- Empty support is not a vertex. Its operator value need not vanish for
an arbitrary z, so the intertwining is stated on precisely nonempty cells. -/
private theorem support_action (a b c : ℕ) (z : Fin 6 → ℝ)
    (S : Finset (Fin 3)) (hS : S.Nonempty) :
    supportComplementOp (exponents a b c) (value z) S =
      value (quotient (a : ℝ) (b : ℝ) (c : ℝ) *ᵥ z) S := by
  have hs : S ∈ (univ : Finset (Finset (Fin 3))) := mem_univ S
  rw [support_univ] at hs
  simp only [mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hS
  all_goals
    simp only [supportComplementOp, sum_support]
    norm_num [supportWeight, exponents, value, quotient, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Finset.ext_iff, Fin.forall_fin_succ] <;> ring

private theorem lift_nonzero (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (z : Fin 6 → ℝ) (hz : z ≠ 0) :
    supportLift (exponents a b c) (value z) ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := Function.ne_iff.mp hz
  apply support_lift_nonzero _ (positive a b c ha hb hc) _ (cell i)
    (cell_nonempty i) (cell_ne_univ i)
  rwa [value_cell]

private theorem weighted_sum_zero (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (e : ℝ) (he0 : e ≠ 0) (z : Fin 6 → ℝ)
    (he : quotient a b c *ᵥ z = e • z) : dotProduct (weights a b c) z = 0 := by
  have hl := (quotient_geometry a b c ha hb hc).1.2.2.2
  have h := congrArg (dotProduct (weights a b c)) he
  rw [dotProduct_mulVec, hl, zero_dotProduct, dotProduct_smul] at h
  exact (mul_eq_zero.mp (show e * dotProduct (weights a b c) z = 0 from h.symm)).resolve_left he0

private theorem lift_sum_zero (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (he0 : e ≠ 0) (z : Fin 6 → ℝ)
    (he : quotient (a : ℝ) (b : ℝ) (c : ℝ) *ᵥ z = e • z) :
    (∑ x : BoxVertex (exponents a b c),
      supportLift (exponents a b c) (value z) x) = 0 := by
  have hw := weighted_sum_zero a b c (by exact_mod_cast ha)
    (by exact_mod_cast hb) (by exact_mod_cast hc) e he0 z he
  rw [show (∑ x : BoxVertex (exponents a b c),
      supportLift (exponents a b c) (value z) x) =
      ∑ S, supportWeight (exponents a b c) S * value z S from
    support_lift_sum _ (positive a b c ha hb hc) _
      (by simp [value]) (by norm_num [value, Finset.ext_iff, Fin.forall_fin_succ])]
  rw [sum_support]
  simp [supportWeight, exponents, value, weights, dotProduct,
    Fin.sum_univ_succ] at hw ⊢
  linarith only [hw]

/-- Every nonzero six-cell eigenvalue gives the reflected actual eigenvalue.
The eigenvector is nonzero and its zero sum is derived from the weighted
left kernel; neither condition is an assumed graph correspondence. -/
theorem actual_eigenvalue (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (he0 : e ≠ 0) (z : Fin 6 → ℝ) (hz : z ≠ 0)
    (he : quotient (a : ℝ) (b : ℝ) (c : ℝ) *ᵥ z = e • z) :
    HasActualEigenvalue (modulus p (exponents a b c))
      (((((a+1)*(b+1)*(c+1))-2 : ℕ) : ℝ)-e) := by
  classical
  have hk := positive a b c ha hb hc
  have heigen : (supportGraph (exponents a b c))ᶜ.lapMatrix ℝ *ᵥ
      supportLift (exponents a b c) (value z) =
      e • supportLift (exponents a b c) (value z) := by
    ext x
    rw [support_complement_intertwining _ hk,
      support_action _ _ _ _ _ (support_nonempty _ x), he]
    simp only [supportLift, value, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp_all
  have h := actual_eigenvalue_of_support p hp hinj _ hk e _
    (lift_nonzero a b c ha hb hc z hz)
    (lift_sum_zero a b c ha hb hc e he0 z he) heigen
  simpa [exponents, Fin.prod_univ_succ, mul_assoc] using h

/-- The full positive-real low-root supplier now acts on actual ideals for
every ordered positive integer triple and every three distinct primes.
This interval alone does not exclude its two possible integer endpoints. -/
theorem result (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ e : ℝ,
      (((a+1)*(b+1)*(c+1)-2 : ℕ) : ℝ) - 3 < e ∧
      e < (((a+1)*(b+1)*(c+1)-2 : ℕ) : ℝ) ∧
      HasActualEigenvalue (modulus p (exponents a b c)) e := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  obtain ⟨μ, hμ0, hμ3, z, hz, he⟩ := positive_real_low_eigenvalue a b c
    (by exact_mod_cast ha) (by exact_mod_cast hab) (by exact_mod_cast hbc)
  refine ⟨(((a+1)*(b+1)*(c+1)-2 : ℕ) : ℝ)-μ, by linarith, by linarith, ?_⟩
  exact actual_eigenvalue p hp hinj a b c ha hb hc μ hμ0.ne' z hz he

#print axioms actual_eigenvalue
#print axioms result

end D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
