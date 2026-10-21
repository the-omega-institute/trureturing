/- GID: D5/S3/Combinatorics/Graph/RegularCHS/CycleBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/CycleBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Gershgorin, mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Matrix, mathlib/module/Mathlib.RingTheory.PowerSeries.Derivative, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Even adjacency coefficients of cycles are bounded by the comparison sequence. -/

import D5.S3.Combinatorics.Graph.RegularCHS.Interface
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

noncomputable section
open Classical Finset PowerSeries
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Defs
open D5.S3.Combinatorics.Graph.RegularCHS.Interface
namespace D5.S3.Combinatorics.Graph.RegularCHS.CycleBound

private def geom (a : ℝ) : PowerSeries ℝ := mk fun k => a ^ k

private lemma geom_linear (a : ℝ) : geom a * (1 - C a * X) = 1 :=
  D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.geometric_mul_linear a

private lemma geom_split (a b : ℝ) :
    C (a - b) * (geom a * geom b) = C a * geom a - C b * geom b  := by
  rw [map_sub]
  have ha := geom_linear a
  have hb := geom_linear b
  calc
    _ = C a * geom a * (geom b * (1 - C b * X)) -
        C b * geom b * (geom a * (1 - C a * X)) := by ring
    _ = _ := by rw [ha, hb]; ring

private lemma coeff_prod_geom_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (k : ℕ) : 0 ≤ coeff k (∏ i ∈ s, geom (a i)) := by
  rw [coeff_prod]
  exact Finset.sum_nonneg fun f _ => Finset.prod_nonneg fun i hi => by
    simpa only [geom, coeff_mk] using pow_nonneg (ha i hi) (f i)

private lemma rescale_geom (a b : ℝ) : rescale a (geom b) = geom (a * b) := by
  ext k
  simp [geom, coeff_rescale, mul_pow]

private lemma coeff_prod_geom_even_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (m : ℕ) : 0 ≤ coeff (2 * m) (∏ i ∈ s, geom (a i)) := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hp : ∀ i ∈ s, 0 ≤ a i
  · exact coeff_prod_geom_nonneg s a hp _
  by_cases hn : ∀ i ∈ s, a i ≤ 0
  · have h := coeff_prod_geom_nonneg s (fun i => -a i)
      (fun i hi => neg_nonneg.mpr (hn i hi)) (2 * m)
    have he : (∏ i ∈ s, geom (-a i)) = rescale (-1 : ℝ) (∏ i ∈ s, geom (a i)) := by
      simp only [map_prod, rescale_geom, neg_one_mul]
    simpa only [he, coeff_rescale, Even.neg_one_pow (even_two_mul m), one_mul] using h
  push Not at hp hn
  obtain ⟨i, hi, hneg⟩ := hp
  obtain ⟨j, hj, hpos⟩ := hn
  have hij : i ≠ j := by intro h; subst j; linarith
  let t := (s.erase i).erase j
  have hsi : s.erase i ⊂ s := Finset.erase_ssubset hi
  have hsj : s.erase j ⊂ s := Finset.erase_ssubset hj
  have hpi := ih (s.erase i) hsi
  have hpj := ih (s.erase j) hsj
  have hprod : (∏ k ∈ s, geom (a k)) = geom (a i) * geom (a j) * ∏ k ∈ t, geom (a k) := by
    rw [← Finset.mul_prod_erase s _ hi,
      ← Finset.mul_prod_erase (s.erase i) _ (mem_erase.mpr ⟨Ne.symm hij, hj⟩)]
    dsimp [t]
    ring
  have hprod_i : (∏ k ∈ s.erase i, geom (a k)) = geom (a j) * ∏ k ∈ t, geom (a k) := by
    exact (Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨Ne.symm hij, hj⟩)).symm
  have hprod_j : (∏ k ∈ s.erase j, geom (a k)) = geom (a i) * ∏ k ∈ t, geom (a k) := by
    rw [← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, hi⟩), Finset.erase_right_comm]
  have he : C (a j - a i) * (∏ k ∈ s, geom (a k)) =
      C (a j) * (∏ k ∈ s.erase i, geom (a k)) -
      C (a i) * (∏ k ∈ s.erase j, geom (a k)) := by
    rw [hprod, hprod_i, hprod_j]
    have hs := congrArg (fun f : PowerSeries ℝ => f * ∏ k ∈ t, geom (a k))
      (geom_split (a j) (a i))
    convert hs using 1 <;> ring
  have hc := congrArg (coeff (2 * m)) he
  rw [coeff_C_mul] at hc
  simp only [map_sub, coeff_C_mul] at hc
  have hnn : 0 ≤ a j * coeff (2 * m) (∏ k ∈ s.erase i, geom (a k)) -
      a i * coeff (2 * m) (∏ k ∈ s.erase j, geom (a k)) :=
    sub_nonneg.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg hneg.le hpj)
      (mul_nonneg hpos.le hpi))
  exact nonneg_of_mul_nonneg_right (hc.symm ▸ hnn)
    (sub_pos.mpr (lt_trans hneg hpos))


end D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
