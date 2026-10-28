/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: The physical finite matrix has exactly three roots with multiplicity and the descending spectrum preserves all ties. -/

import D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Polynomial
open ActualThreeNodeFiniteAlgebra ActualThreeNodeFiniteEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteSpectrum

/-- Trace, discriminant and two real roots of the physical even block. -/
def evenTau (g mu a r : ℝ) : ℝ := U g mu a r / 3 + ActualThreeNodeFiniteAlgebra.C g mu a r / 6
def evenRad (g mu a r : ℝ) : ℝ :=
  (U g mu a r / 3 - ActualThreeNodeFiniteAlgebra.C g mu a r / 6) ^ 2 +
    4 * (T g mu a r / Real.sqrt 18) ^ 2
def rhoPlus (g mu a r : ℝ) : ℝ :=
  (evenTau g mu a r + Real.sqrt (evenRad g mu a r)) / 2
def rhoMinus (g mu a r : ℝ) : ℝ :=
  (evenTau g mu a r - Real.sqrt (evenRad g mu a r)) / 2

lemma evenRad_nonneg (g mu a r : ℝ) : 0 ≤ evenRad g mu a r := by
  unfold evenRad
  positivity

lemma rho_order (g mu a r : ℝ) : rhoMinus g mu a r ≤ rhoPlus g mu a r := by
  unfold rhoMinus rhoPlus
  linarith [Real.sqrt_nonneg (evenRad g mu a r)]

lemma rho_sum (g mu a r : ℝ) :
    rhoMinus g mu a r + rhoPlus g mu a r = evenTau g mu a r := by
  unfold rhoMinus rhoPlus
  ring

lemma evenRad_trace_det (g mu a r : ℝ) :
    evenRad g mu a r = evenTau g mu a r ^ 2 - 4 * evenDet g mu a r := by
  unfold evenRad evenTau evenDet
  ring

lemma rho_product (g mu a r : ℝ) :
    rhoMinus g mu a r * rhoPlus g mu a r = evenDet g mu a r := by
  have hs := Real.sq_sqrt (evenRad_nonneg g mu a r)
  have hd := evenRad_trace_det g mu a r
  unfold rhoMinus rhoPlus
  nlinarith only [hs, hd]

lemma rhoMinus_eq_div (g mu a r : ℝ) (hp : rhoPlus g mu a r ≠ 0) :
    rhoMinus g mu a r = evenDet g mu a r / rhoPlus g mu a r :=
  (eq_div_iff hp).mpr (rho_product g mu a r)

abbrev finiteEigen (g mu a r : ℝ) : Fin 3 → ℝ :=
  (finiteMatrix_isHermitian g mu a r).eigenvalues₀

/-- Direct determinant of the physical 1+2 matrix, in its original metric. -/
lemma finite_charpoly_quadratic (g mu a r : ℝ) :
    (finiteMatrix g mu a r).charpoly =
      (X - Polynomial.C (O g mu a r : ℂ)) *
        (X ^ 2 - Polynomial.C (evenTau g mu a r : ℂ) * X +
          Polynomial.C (evenDet g mu a r : ℂ)) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [Matrix.charmatrix_apply, finiteMatrix, Matrix.diagonal_apply,
    evenTau, evenDet] <;>
    push_cast <;> ring

/-- Polynomial factorization has no distinct-root or nonzero-entry premise. -/
lemma finite_charpoly (g mu a r : ℝ) :
    (finiteMatrix g mu a r).charpoly =
      (X - Polynomial.C (rhoPlus g mu a r : ℂ)) *
      (X - Polynomial.C (O g mu a r : ℂ)) *
      (X - Polynomial.C (rhoMinus g mu a r : ℂ)) := by
  have hs : (rhoMinus g mu a r : ℂ) + (rhoPlus g mu a r : ℂ) =
      (evenTau g mu a r : ℂ) := by exact_mod_cast rho_sum g mu a r
  have hp : (rhoMinus g mu a r : ℂ) * (rhoPlus g mu a r : ℂ) =
      (evenDet g mu a r : ℂ) := by exact_mod_cast rho_product g mu a r
  rw [finite_charpoly_quadratic, ← hs, ← hp]
  simp only [map_add, map_mul]
  ring

/-- FULL characteristic root multiset, with algebraic multiplicity intact.
This includes Delta=0 and either/both coincidences with the odd root. -/
theorem finite_roots (g mu a r : ℝ) :
    (finiteMatrix g mu a r).charpoly.roots =
      {(rhoPlus g mu a r : ℂ), (O g mu a r : ℂ), (rhoMinus g mu a r : ℂ)} := by
  have hp : (finiteMatrix g mu a r).charpoly =
      (({(rhoPlus g mu a r : ℂ), (O g mu a r : ℂ),
          (rhoMinus g mu a r : ℂ)} : Multiset ℂ).map
        (fun z : ℂ => X - Polynomial.C z)).prod := by
    simpa [mul_assoc] using finite_charpoly g mu a r
  rw [hp, Polynomial.roots_multiset_prod_X_sub_C]

/-- All three real Hermitian eigenvalues, again as a multiset with repetitions. -/
theorem finite_spectrum_multiset (g mu a r : ℝ) :
    (List.ofFn (finiteEigen g mu a r) : Multiset ℝ) =
      {rhoPlus g mu a r, O g mu a r, rhoMinus g mu a r} := by
  have hs := (finiteMatrix_isHermitian g mu a r).sort_roots_charpoly_eq_eigenvalues₀
  rw [RCLike.re_eq_complex_re] at hs
  have he := congrArg (fun l : List ℝ => (l : Multiset ℝ)) hs
  have hr := congrArg (fun s : Multiset ℂ => s.map Complex.re) (finite_roots g mu a r)
  calc
    (List.ofFn (finiteEigen g mu a r) : Multiset ℝ) =
        (finiteMatrix g mu a r).charpoly.roots.map Complex.re := by
      rw [Multiset.sort_eq] at he
      exact he.symm
    _ = {rhoPlus g mu a r, O g mu a r, rhoMinus g mu a r} := by
      simpa using hr

/-- A three-element sorting calculation; equality cases are retained. -/
private lemma sort_three (p o m : ℝ) (hmp : m ≤ p) (hmo : m ≤ o) :
    ({p, o, m} : Multiset ℝ).sort (· ≥ ·) = [max p o, min p o, m] := by
  have he : ({p, o, m} : Multiset ℝ) = {max p o, min p o, m} := by
    rcases le_total p o with h | h
    · simpa only [max_eq_right h, min_eq_left h, Multiset.insert_eq_cons] using
        (Multiset.cons_swap p o ({m} : Multiset ℝ))
    · simp only [max_eq_left h, min_eq_right h]
  have hmin : m ≤ min p o := le_min hmp hmo
  have hmax : min p o ≤ max p o := (min_le_left _ _).trans (le_max_left _ _)
  have hsortmin : (min p o ::ₘ ({m} : Multiset ℝ)).sort (· ≥ ·) = [min p o, m] := by
    rw [Multiset.sort_cons]
    · simp
    · intro b hb
      have : b = m := by simpa using hb
      simpa [this] using hmin
  rw [he]
  simp only [Multiset.insert_eq_cons]
  rw [Multiset.sort_cons, hsortmin]
  intro b hb
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact hmax
  · exact hmin.trans hmax

/-- Exact descending finite spectrum once the small even root is below O.
No comparison of the two large roots is required, so the tie is never removed. -/
theorem finite_sorted_eq (g mu a r : ℝ) (hmo : rhoMinus g mu a r ≤ O g mu a r) :
    finiteEigen g mu a r =
      ![max (rhoPlus g mu a r) (O g mu a r),
        min (rhoPlus g mu a r) (O g mu a r), rhoMinus g mu a r] := by
  apply List.ofFn_inj.mp
  have hsorted : ((List.ofFn (finiteEigen g mu a r) : Multiset ℝ).sort (· ≥ ·)) =
      List.ofFn (finiteEigen g mu a r) := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _
      (finiteMatrix_isHermitian g mu a r).eigenvalues₀_antitone.sortedGE_ofFn.pairwise
  calc
    List.ofFn (finiteEigen g mu a r) =
        (List.ofFn (finiteEigen g mu a r) : Multiset ℝ).sort (· ≥ ·) := hsorted.symm
    _ = ({rhoPlus g mu a r, O g mu a r, rhoMinus g mu a r} : Multiset ℝ).sort (· ≥ ·) := by
      rw [finite_spectrum_multiset]
    _ = [max (rhoPlus g mu a r) (O g mu a r),
        min (rhoPlus g mu a r) (O g mu a r), rhoMinus g mu a r] :=
      sort_three _ _ _ (rho_order g mu a r) hmo
    _ = List.ofFn ![max (rhoPlus g mu a r) (O g mu a r),
        min (rhoPlus g mu a r) (O g mu a r), rhoMinus g mu a r] := by
      simp [List.ofFn_succ]

/-- The exceptional characteristic sign at the odd root. -/
lemma exceptional_characteristic_at_odd (g mu r : ℝ) :
    O g mu 0 r ^ 2 - evenTau g mu 0 r * O g mu 0 r + evenDet g mu 0 r =
      -8 * (g ^ 2 + mu) ^ 2 * r ^ 2 * (5 - r ^ 2) * (3 - r ^ 2) / 15 := by
  rw [evenTau, exceptional_trace_identity, exceptional_determinant_identity]
  unfold O
  ring

/-- Strict finite ordering of all three roots in the entire exterior zero branch.
The proof does not compare asymptotic equivalents or divide by a vector energy. -/
theorem exceptional_finite_order (g mu r : ℝ) (hh : 0 < g ^ 2 + mu)
    (hr : r ≠ 0) (hrsq : r ^ 2 ≤ 1) :
    0 < rhoMinus g mu 0 r ∧ rhoMinus g mu 0 r < O g mu 0 r ∧
      O g mu 0 r < rhoPlus g mu 0 r := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have ho : 0 < O g mu 0 r := by
    unfold O
    nlinarith [mul_pos hh hr2]
  have h5 : 0 < 5 - r ^ 2 := by linarith
  have h3 : 0 < 3 - r ^ 2 := by linarith
  have hsign : O g mu 0 r ^ 2 - evenTau g mu 0 r * O g mu 0 r +
      evenDet g mu 0 r < 0 := by
    rw [exceptional_characteristic_at_odd]
    have hx : 0 < 8 * (g ^ 2 + mu) ^ 2 * r ^ 2 * (5 - r ^ 2) * (3 - r ^ 2) / 15 := by
      positivity
    nlinarith only [hx]
  have hfactor : (O g mu 0 r - rhoMinus g mu 0 r) *
      (O g mu 0 r - rhoPlus g mu 0 r) =
      O g mu 0 r ^ 2 - evenTau g mu 0 r * O g mu 0 r + evenDet g mu 0 r := by
    calc
      _ = O g mu 0 r ^ 2 - (rhoMinus g mu 0 r + rhoPlus g mu 0 r) * O g mu 0 r +
          rhoMinus g mu 0 r * rhoPlus g mu 0 r := by ring
      _ = _ := by rw [rho_sum, rho_product]
  have hf : (O g mu 0 r - rhoMinus g mu 0 r) *
      (O g mu 0 r - rhoPlus g mu 0 r) < 0 := by
    rwa [hfactor]
  have hmp := rho_order g mu 0 r
  have hmo : rhoMinus g mu 0 r < O g mu 0 r := by
    by_contra h
    have h1 : O g mu 0 r - rhoMinus g mu 0 r ≤ 0 := by linarith
    have h2 : O g mu 0 r - rhoPlus g mu 0 r ≤ 0 := by linarith
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos h1 h2)) hf
  have hop : O g mu 0 r < rhoPlus g mu 0 r := by
    by_contra h
    have h1 : 0 ≤ O g mu 0 r - rhoMinus g mu 0 r := by linarith
    have h2 : 0 ≤ O g mu 0 r - rhoPlus g mu 0 r := by linarith
    exact (not_lt_of_ge (mul_nonneg h1 h2)) hf
  have hp : 0 < rhoPlus g mu 0 r := ho.trans hop
  have hd : 0 < evenDet g mu 0 r := by
    rw [exceptional_determinant_identity]
    positivity
  refine ⟨?_, hmo, hop⟩
  rw [rhoMinus_eq_div g mu 0 r hp.ne']
  exact div_pos hd hp

/-- Sorted zero-branch spectrum, including the exact finite ordering. -/
theorem exceptional_finite_sorted (g mu r : ℝ) (hh : 0 < g ^ 2 + mu)
    (hr : r ≠ 0) (hrsq : r ^ 2 ≤ 1) :
    finiteEigen g mu 0 r = ![rhoPlus g mu 0 r, O g mu 0 r, rhoMinus g mu 0 r] := by
  have h := exceptional_finite_order g mu r hh hr hrsq
  rw [finite_sorted_eq g mu 0 r h.2.1.le,
    max_eq_left h.2.2.le, min_eq_right h.2.2.le]

end D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteSpectrum
