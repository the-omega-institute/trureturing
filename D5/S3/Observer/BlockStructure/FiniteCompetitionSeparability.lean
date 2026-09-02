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

/-- Coordinates of the full finite multiscale profile: every Cayley-scale level,
followed by the reference monomial block. -/
abbrev FullProfileCoordinate {scaleCount : Nat}
    (scaleDepth : Fin scaleCount -> Nat) (referenceDepth : Nat) :=
  Sum (Sigma fun i => Fin (scaleDepth i + 1)) (Fin (referenceDepth + 1))

/-- For distinct nonzero real Cayley scales and their finite depths, finitely
many pairwise distinct sign-conjugacy orbits admit a finite full multiscale
profile whose target has positive distance from the real span of all competitor
profiles. Every canonical common-denominator basis coordinate is evaluated in
the even variable `w ^ 2`, so the profile is even, commutes with conjugation,
and is real on real inputs. The disk constraint certifies that the composed
denominator has no unit-circle zero, while the finite-point no-pole premise
keeps every displayed rational profile defined. -/
theorem finite_competition_separability
    (scaleCount competitorCount : Nat)
    (scale : Fin scaleCount -> Real) (scaleDepth : Fin scaleCount -> Nat)
    (scaleNonzero : forall i, scale i ≠ 0)
    (scaleInjective : Function.Injective scale)
    (scaleInDisk : forall i, abs (scale i) < 1)
    (z : Fin (competitorCount + 1) -> Complex)
    (orbitDistinct : forall i j, i ≠ j ->
      z i ≠ z j /\ z i ≠ -z j /\
        z i ≠ conj (z j) /\ z i ≠ -conj (z j))
    (noPole : forall j,
      Polynomial.eval ((z j) ^ 2) (∏ i : Fin scaleCount,
        (1 + Polynomial.C (scale i : Complex) * Polynomial.X) ^
          (scaleDepth i + 1)) ≠ 0) :
    exists referenceDepth : Nat,
      let multiplicity : Fin scaleCount -> Nat := fun i => scaleDepth i + 1
      let totalDepth : Nat := ∑ i, multiplicity i
      let factor : Fin scaleCount -> Complex[X] := fun i =>
        1 + Polynomial.C (scale i : Complex) * Polynomial.X
      let denominator : Complex[X] :=
        ∏ i, factor i ^ multiplicity i
      let numerator : FullProfileCoordinate scaleDepth referenceDepth ->
          Complex[X] := fun coordinate =>
        match coordinate with
        | Sum.inl ij =>
            (Polynomial.X + Polynomial.C (scale ij.1 : Complex)) ^ (ij.2 : Nat) *
              factor ij.1 ^ (scaleDepth ij.1 - (ij.2 : Nat)) *
                ∏ k ∈ Finset.univ.erase ij.1, factor k ^ multiplicity k
        | Sum.inr j => denominator * Polynomial.X ^ (j : Nat)
      let feature : Complex -> FullProfileCoordinate scaleDepth referenceDepth ->
          Complex := fun w coordinate =>
        (numerator coordinate).eval (w ^ 2) / denominator.eval (w ^ 2)
      let competitorSpace : Submodule Real
          (FullProfileCoordinate scaleDepth referenceDepth -> Complex) :=
        span Real (Set.range fun j : Fin competitorCount => feature (z j.succ))
      (LinearIndependent Complex numerator /\
          span Complex (Set.range numerator) =
            Polynomial.degreeLT Complex (totalDepth + referenceDepth + 1)) /\
        (forall w, ‖w‖ = 1 -> denominator.eval (w ^ 2) ≠ 0) /\
          (forall coordinate w, feature (-w) coordinate = feature w coordinate) /\
            (forall coordinate w,
              feature (conj w) coordinate = conj (feature w coordinate)) /\
              (forall coordinate (xi : Real),
                (feature (xi : Complex) coordinate).im = 0) /\
                0 < infDist (feature (z 0)) (competitorSpace : Set _) := by
  let denominator : Complex[X] :=
    ∏ i : Fin scaleCount,
      (1 + Polynomial.C (scale i : Complex) * Polynomial.X) ^ (scaleDepth i + 1)
  let separator : Complex[X] :=
    ∏ j : Fin competitorCount,
      (Polynomial.X - Polynomial.C ((z j.succ) ^ 2)) *
        (Polynomial.X - Polynomial.C ((conj (z j.succ)) ^ 2))
  let referenceDepth : Nat := separator.natDegree
  let numerator : FullProfileCoordinate scaleDepth referenceDepth -> Complex[X] :=
    fun coordinate =>
    match coordinate with
    | Sum.inl ij =>
        (Polynomial.X + Polynomial.C (scale ij.1 : Complex)) ^ (ij.2 : Nat) *
          (1 + Polynomial.C (scale ij.1 : Complex) * Polynomial.X) ^
              (scaleDepth ij.1 - (ij.2 : Nat)) *
            ∏ k ∈ Finset.univ.erase ij.1,
              (1 + Polynomial.C (scale k : Complex) * Polynomial.X) ^
                (scaleDepth k + 1)
    | Sum.inr j => denominator * Polynomial.X ^ (j : Nat)
  let feature : Complex -> FullProfileCoordinate scaleDepth referenceDepth ->
      Complex := fun w coordinate =>
    (numerator coordinate).eval (w ^ 2) / denominator.eval (w ^ 2)
  let competitorSpace : Submodule Real
      (FullProfileCoordinate scaleDepth referenceDepth -> Complex) :=
    span Real (Set.range fun j : Fin competitorCount => feature (z j.succ))
  refine ⟨referenceDepth, ?_⟩
  dsimp only
  have complexScaleNonzero (i : Fin scaleCount) : (scale i : Complex) ≠ 0 := by
    exact_mod_cast scaleNonzero i
  have complexScaleInjective : Function.Injective fun i => (scale i : Complex) := by
    intro i j hij
    apply scaleInjective
    simpa only [Complex.ofReal_re] using congrArg Complex.re hij
  have complexScaleInDisk (i : Fin scaleCount) : ‖(scale i : Complex)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using scaleInDisk i
  have unitCirclePoleFree (w : Complex) (hw : ‖w‖ = 1) :
      denominator.eval w ≠ 0 := by
    simp only [denominator, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simp only [Polynomial.eval_pow, Polynomial.eval_add,
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
      denominator.eval ((z j) ^ 2) ≠ 0 := by
    simpa only [denominator] using noPole j
  have denominator_conj :
      denominator.map (starRingEnd Complex) = denominator := by
    simp [denominator, Polynomial.map_prod]
  have numerator_conj
      (coordinate : FullProfileCoordinate scaleDepth referenceDepth) :
      (numerator coordinate).map (starRingEnd Complex) = numerator coordinate := by
    cases coordinate with
    | inl ij => simp [numerator, Polynomial.map_prod]
    | inr j => simp [numerator, denominator_conj]
  have denominator_eval_conj (w : Complex) :
      denominator.eval (conj w) = conj (denominator.eval w) := by
    calc
      denominator.eval (conj w) =
          (denominator.map (starRingEnd Complex)).eval (conj w) := by
            rw [denominator_conj]
      _ = conj (denominator.eval w) := by
        exact Polynomial.eval_map_apply (starRingEnd Complex) w
  have numerator_eval_conj
      (coordinate : FullProfileCoordinate scaleDepth referenceDepth) (w : Complex) :
      (numerator coordinate).eval (conj w) =
        conj ((numerator coordinate).eval w) := by
    calc
      (numerator coordinate).eval (conj w) =
          ((numerator coordinate).map (starRingEnd Complex)).eval (conj w) := by
            rw [numerator_conj coordinate]
      _ = conj ((numerator coordinate).eval w) := by
        exact Polynomial.eval_map_apply (starRingEnd Complex) w
  have feature_even
      (coordinate : FullProfileCoordinate scaleDepth referenceDepth) (w : Complex) :
      feature (-w) coordinate = feature w coordinate := by
    change (numerator coordinate).eval ((-w) ^ 2) /
        denominator.eval ((-w) ^ 2) =
      (numerator coordinate).eval (w ^ 2) / denominator.eval (w ^ 2)
    rw [neg_sq]
  have feature_conj
      (coordinate : FullProfileCoordinate scaleDepth referenceDepth) (w : Complex) :
      feature (conj w) coordinate = conj (feature w coordinate) := by
    change (numerator coordinate).eval ((conj w) ^ 2) /
        denominator.eval ((conj w) ^ 2) =
      conj ((numerator coordinate).eval (w ^ 2) / denominator.eval (w ^ 2))
    rw [← map_pow, numerator_eval_conj, denominator_eval_conj, map_div₀]
  have feature_real
      (coordinate : FullProfileCoordinate scaleDepth referenceDepth) (xi : Real) :
      (feature (xi : Complex) coordinate).im = 0 := by
    have hConj := feature_conj coordinate (xi : Complex)
    rw [Complex.conj_ofReal] at hConj
    have hIm := congrArg Complex.im hConj
    simp only [Complex.conj_im] at hIm
    linarith
  let referenceProjection :
      (FullProfileCoordinate scaleDepth referenceDepth -> Complex) →ₗ[Real]
        (Fin (referenceDepth + 1) -> Complex) :=
    { toFun := fun v k => v (Sum.inr k)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  let referenceFeature : Complex -> Fin (referenceDepth + 1) -> Complex :=
    fun w k => (w ^ 2) ^ (k : Nat)
  have projection_feature (j : Fin (competitorCount + 1)) :
      referenceProjection (feature (z j)) = referenceFeature (z j) := by
    funext k
    change (denominator * Polynomial.X ^ (k : Nat)).eval ((z j) ^ 2) /
        denominator.eval ((z j) ^ 2) = ((z j) ^ 2) ^ (k : Nat)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    field_simp [denominator_ne_zero j]
  let referenceCompetitorSpace : Submodule Real
      (Fin (referenceDepth + 1) -> Complex) :=
    span Real (Set.range fun j : Fin competitorCount => referenceFeature (z j.succ))
  have projection_mem_reference_span
      (v : FullProfileCoordinate scaleDepth referenceDepth -> Complex)
      (hv : v ∈ competitorSpace) :
      referenceProjection v ∈ referenceCompetitorSpace := by
    refine Submodule.span_induction (p := fun v _ =>
      referenceProjection v ∈ referenceCompetitorSpace) ?_ ?_ ?_ ?_ hv
    · intro v hv
      rcases hv with ⟨j, rfl⟩
      rw [projection_feature]
      exact Submodule.subset_span ⟨j, rfl⟩
    · simpa only [map_zero] using referenceCompetitorSpace.zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using referenceCompetitorSpace.add_mem hx hy
    · intro a x _ hx
      simpa only [map_smul] using referenceCompetitorSpace.smul_mem a hx
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
      Polynomial.eval_C]
    have hOrbit := orbitDistinct 0 j.succ (Fin.succ_ne_zero j).symm
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      intro hSquare
      rcases eq_or_eq_neg_of_sq_eq_sq (z 0) (z j.succ) hSquare with hEqual | hNeg
      · exact hOrbit.1 hEqual
      · exact hOrbit.2.1 hNeg
    · apply sub_ne_zero.mpr
      intro hSquare
      rcases eq_or_eq_neg_of_sq_eq_sq (z 0) (conj (z j.succ)) hSquare with
        hEqual | hNeg
      · exact hOrbit.2.2.1 hEqual
      · exact hOrbit.2.2.2 hNeg
  have separator_eval_as_sum (j : Fin (competitorCount + 1)) :
      (∑ k : Fin (separator.natDegree + 1),
        separator.coeff k * referenceFeature (z j) k) =
          separator.eval ((z j) ^ 2) := by
    rw [Polynomial.eval_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range (fun k =>
        separator.coeff k * ((z j) ^ 2) ^ k)]
  have functional_vanishes_on_span
      (v : Fin (separator.natDegree + 1) -> Complex)
      (hv : v ∈ referenceCompetitorSpace) :
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
  have reference_target_not_mem :
      referenceFeature (z 0) ∉ referenceCompetitorSpace := by
    intro hTarget
    apply separator_eval_target
    rw [← separator_eval_as_sum]
    exact functional_vanishes_on_span _ hTarget
  have target_not_mem : feature (z 0) ∉ competitorSpace := by
    intro hTarget
    apply reference_target_not_mem
    rw [← projection_feature 0]
    exact projection_mem_reference_span _ hTarget
  let _ : FiniteDimensional Real competitorSpace :=
    Module.Finite.span_of_finite Real (Set.finite_range fun j : Fin competitorCount =>
      feature (z j.succ))
  refine ⟨?_, ?_, feature_even, feature_conj, feature_real, ?_⟩
  · have basisResult :=
      CommonDenominatorPolynomialBasis.common_denominator_polynomial_basis
        scaleCount (fun i => (scale i : Complex)) scaleDepth referenceDepth
          complexScaleNonzero complexScaleInjective complexScaleInDisk
    dsimp only at basisResult
    convert basisResult using 1
    · apply iff_of_eq
      congr 1
      funext coordinate
      cases coordinate <;> rfl
    · apply iff_of_eq
      congr 3
      funext coordinate
      cases coordinate <;> rfl
  · intro w hw
    apply unitCirclePoleFree (w ^ 2)
    rw [norm_pow, hw, one_pow]
  · refine (IsClosed.notMem_iff_infDist_pos ?_ ?_).mp ?_
    · exact Submodule.closed_of_finiteDimensional _
    · exact ⟨0, Submodule.zero_mem _⟩
    · intro hTarget
      apply target_not_mem
      change feature (z 0) ∈ competitorSpace at hTarget
      exact hTarget

#print axioms finite_competition_separability

end D5.S3.Observer.BlockStructure.FiniteCompetitionSeparability
