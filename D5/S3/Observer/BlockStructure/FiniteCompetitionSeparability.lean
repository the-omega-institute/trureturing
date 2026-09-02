/- GID: D5/S3/Observer/BlockStructure/FiniteCompetitionSeparability
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/FiniteCompetitionSeparability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite symmetric competitors admit a positive common-denominator feature margin. -/

import D5.S3.Observer.BlockStructure.CommonDenominatorPolynomialBasis
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-09-02):
   * Repository searches for finite common-denominator profile separation,
     distance from a competitor span, and even conjugate-orbit separation found
     the polynomial-basis prerequisite but no theorem with the positive margin.
   * Pinned Mathlib supplies polynomial evaluation, finite span induction,
     `Submodule.closed_of_finiteDimensional`, and
     `IsClosed.notMem_iff_infDist_pos`; it has no whole-statement theorem.
   * Loogle returned no match for the distance-to-span shape. LeanSearch found
     Lagrange nodal nonvanishing and conjugate polynomial evaluation, but no
     result combining the common denominator, orbit quotient, and margin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Metric Polynomial Set Submodule
open scoped BigOperators ComplexConjugate

namespace D5.S3.Observer.BlockStructure.FiniteCompetitionSeparability

/-- For arbitrary finite real Cayley scales and their depths, finitely many
pairwise distinct sign-conjugacy orbits admit a finite even reference block
whose target profile has positive distance from the real span of all competitor
profiles. The common denominator is the one constructed from the supplied
scales. Its disk constraint also certifies that it has no unit-circle zero; the
finite-point no-pole premise keeps every displayed rational profile defined. -/
theorem finite_competition_separability
    (scaleCount competitorCount : Nat)
    (scale : Fin scaleCount -> Real) (scaleDepth : Fin scaleCount -> Nat)
    (scaleInDisk : forall i, abs (scale i) < 1)
    (z : Fin (competitorCount + 1) -> Complex)
    (orbitDistinct : forall i j, i ≠ j ->
      z i ≠ z j /\ z i ≠ -z j /\
        z i ≠ conj (z j) /\ z i ≠ -conj (z j))
    (noPole : forall j,
      Polynomial.eval (z j) (∏ i : Fin scaleCount,
        (1 + Polynomial.C (scale i : Complex) * Polynomial.X) ^
          (scaleDepth i + 1)) ≠ 0) :
    exists referenceDepth : Nat,
      let factor : Fin scaleCount -> Complex[X] := fun i =>
        1 + Polynomial.C (scale i : Complex) * Polynomial.X
      let denominator : Complex[X] :=
        ∏ i, factor i ^ (scaleDepth i + 1)
      let numerator : Fin (referenceDepth + 1) -> Complex[X] := fun k =>
        denominator * Polynomial.X ^ (2 * (k : Nat))
      let feature : Complex -> Fin (referenceDepth + 1) -> Complex := fun w k =>
        (numerator k).eval w / denominator.eval w
      let competitorSpace : Submodule Real
          (Fin (referenceDepth + 1) -> Complex) :=
        span Real (Set.range fun j : Fin competitorCount => feature (z j.succ))
      (forall w, ‖w‖ = 1 -> denominator.eval w ≠ 0) /\
        0 < infDist (feature (z 0)) (competitorSpace : Set _) := by
  let factor : Fin scaleCount -> Complex[X] := fun i =>
    1 + Polynomial.C (scale i : Complex) * Polynomial.X
  let denominator : Complex[X] := ∏ i, factor i ^ (scaleDepth i + 1)
  let separator : Complex[X] :=
    ∏ j : Fin competitorCount,
      (Polynomial.X - Polynomial.C (z j.succ) ^ 2) *
        (Polynomial.X - Polynomial.C (conj (z j.succ)) ^ 2)
  let referenceDepth : Nat := separator.natDegree
  let numerator : Fin (referenceDepth + 1) -> Complex[X] := fun k =>
    denominator * Polynomial.X ^ (2 * (k : Nat))
  let feature : Complex -> Fin (referenceDepth + 1) -> Complex := fun w k =>
    (numerator k).eval w / denominator.eval w
  let competitorSpace : Submodule Real
      (Fin (referenceDepth + 1) -> Complex) :=
    span Real (Set.range fun j : Fin competitorCount => feature (z j.succ))
  refine ⟨referenceDepth, ?_⟩
  suffices result :
      (forall w, ‖w‖ = 1 -> denominator.eval w ≠ 0) /\
        0 < infDist (feature (z 0)) (competitorSpace : Set _) by
    simpa only [factor, denominator, numerator, feature, competitorSpace,
      referenceDepth] using result
  have unitCirclePoleFree (w : Complex) (hw : ‖w‖ = 1) :
      denominator.eval w ≠ 0 := by
    simp only [denominator, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simp only [factor, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    apply pow_ne_zero
    intro hFactor
    have hFactor' : (scale i : Complex) * w + 1 = 0 := by
      rw [add_comm]
      exact hFactor
    have hProduct : (scale i : Complex) * w = -1 :=
      eq_neg_of_add_eq_zero_left hFactor'
    have hNorm := congrArg norm hProduct
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one,
      norm_neg, norm_one] at hNorm
    linarith [scaleInDisk i]
  have denominator_ne_zero (j : Fin (competitorCount + 1)) :
      denominator.eval (z j) ≠ 0 := by
    simpa only [denominator, factor] using noPole j
  have feature_at (j : Fin (competitorCount + 1))
      (k : Fin (referenceDepth + 1)) :
      feature (z j) k = (z j) ^ (2 * (k : Nat)) := by
    simp only [feature, numerator, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    field_simp [denominator_ne_zero j]
  have separator_eval_competitor (j : Fin competitorCount) :
      separator.eval ((z j.succ) ^ 2) = 0 := by
    simp only [separator, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp
  have separator_eval_target : separator.eval ((z 0) ^ 2) ≠ 0 := by
    simp only [separator, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_C]
    have hOrbit := orbitDistinct 0 j.succ (Fin.succ_ne_zero j).symm
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      intro hSquare
      rcases eq_or_eq_neg_of_sq_eq_sq (z 0) (z j.succ) hSquare with h | h
      · exact hOrbit.1 h
      · exact hOrbit.2.1 h
    · apply sub_ne_zero.mpr
      intro hSquare
      rcases eq_or_eq_neg_of_sq_eq_sq (z 0) (conj (z j.succ)) hSquare with h | h
      · exact hOrbit.2.2.1 h
      · exact hOrbit.2.2.2 h
  have separator_eval_as_sum (j : Fin (competitorCount + 1)) :
      (∑ k : Fin (separator.natDegree + 1),
        separator.coeff k * feature (z j) k) = separator.eval ((z j) ^ 2) := by
    rw [Polynomial.eval_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range (fun k =>
        separator.coeff k * ((z j) ^ 2) ^ k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [feature_at]
    simp only [pow_mul]
  have functional_vanishes_on_span
      (v : Fin (separator.natDegree + 1) -> Complex)
      (hv : v ∈ competitorSpace) :
      (∑ k : Fin (separator.natDegree + 1), separator.coeff k * v k) = 0 := by
    refine Submodule.span_induction (p := fun v _ =>
      (∑ k : Fin (separator.natDegree + 1), separator.coeff k * v k) = 0)
        ?_ ?_ ?_ ?_ hv
    · intro v hv
      rcases hv with ⟨j, rfl⟩
      rw [separator_eval_as_sum, separator_eval_competitor]
    · simp
    · intro x y _ _ hx hy
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
    · intro a x _ hx
      calc
        (∑ k : Fin (separator.natDegree + 1),
            separator.coeff k * (a • x) k) =
            (a : Complex) *
              ∑ k : Fin (separator.natDegree + 1),
                separator.coeff k * x k := by
              simp only [Pi.smul_apply, Complex.real_smul]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = 0 := by rw [hx, mul_zero]
  have target_not_mem : feature (z 0) ∉ competitorSpace := by
    intro hTarget
    apply separator_eval_target
    rw [← separator_eval_as_sum]
    exact functional_vanishes_on_span _ hTarget
  let _ : FiniteDimensional Real competitorSpace :=
    Module.Finite.span_of_finite Real (Set.finite_range fun j : Fin competitorCount =>
      feature (z j.succ))
  refine ⟨unitCirclePoleFree, ?_⟩
  exact (competitorSpace.closed_of_finiteDimensional.notMem_iff_infDist_pos
    ⟨0, competitorSpace.zero_mem⟩).mp target_not_mem

#print axioms finite_competition_separability

end D5.S3.Observer.BlockStructure.FiniteCompetitionSeparability
