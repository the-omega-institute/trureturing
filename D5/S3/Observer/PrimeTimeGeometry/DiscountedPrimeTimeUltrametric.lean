/- GID: D5/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric
   generality: G
   mirror-B: D5/B/S3/Observer/PrimeTimeGeometry/DiscountedPrimeTimeUltrametric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite weighted prime-time prediction distance obeys the strong triangle law. -/

import D5.S3.Observer.MetricGeometryLaws.WeightedJointUltrapseudometric
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-09-03):
   * Repository search found and reuses `discreteOutputDistance` for the source's
     equality-valued coordinate discrepancy and `weighted_joint_ultrapseudometric`
     for its finite weighted pointwise strong triangle law.
   * Pinned Mathlib supplies `ciSup_mono`, `ciSup_sup_eq`, `mul_max_of_nonneg`,
     `pow_le_one₀`, and `Finset.single_le_sum`; no full finite-coordinate,
     weighted, all-time supremum theorem was found.
   * Loogle confirmed `ciSup_sup_eq`. LeanSearch's queried API returned HTTP 404;
     GitHub repository search returned no matching Lean project, while code search
     required authentication. Full details are recorded in `/tmp/SEARCH-aj.md`.

   Source-boundary open: Definition 33.1 writes a supremum over the selected
   coordinates and nonnegative times, but the source does not define a real
   supremum for an empty coordinate family (`J = ∅`). The Lean `iSup` expression
   is therefore totalized by its ambient order structure; that empty-budget
   behavior is formalization-specific and is not attributed to the source. This
   boundary remains open pending an authoritative source clause.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.PrimeTimeGeometry.DiscountedPrimeTimeUltrametric

open D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric
open D5.S3.Observer.MetricGeometryLaws.WeightedPredictionZeroKernel
open D5.S3.Observer.MetricGeometryLaws.WeightedJointUltrapseudometric

/-- Source lines 2057-2066, Definition 33.1: the supremum over every selected
coordinate and every nonnegative time of the weighted discounted equality
discrepancy along the update orbit. -/
noncomputable def discountedPrimeTimeDistance
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (update : X -> X) (gamma : Real) (x y : X) : Real :=
  ⨆ pair : {i // i ∈ J} × Nat,
    (weight pair.1.1 * gamma ^ pair.2) *
      @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
        (readout pair.1.1 ((update^[pair.2]) x))
        (readout pair.1.1 ((update^[pair.2]) y))

private theorem discounted_prime_time_terms_bddAbove
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (update : X -> X) (gamma : Real)
    (hpositive : ∀ i ∈ J, 0 < weight i)
    (hgamma : gamma ∈ Set.Ioc 0 1) (x y : X) :
    BddAbove (Set.range fun pair : {i // i ∈ J} × Nat =>
      (weight pair.1.1 * gamma ^ pair.2) *
        @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
          (readout pair.1.1 ((update^[pair.2]) x))
          (readout pair.1.1 ((update^[pair.2]) y))) := by
  classical
  refine ⟨J.sum weight, ?_⟩
  rintro _ ⟨pair, rfl⟩
  by_cases hequal :
      readout pair.1.1 ((update^[pair.2]) x) =
        readout pair.1.1 ((update^[pair.2]) y)
  · change (weight pair.1.1 * gamma ^ pair.2) *
        (if readout pair.1.1 ((update^[pair.2]) x) =
          readout pair.1.1 ((update^[pair.2]) y) then 0 else 1) <= J.sum weight
    rw [if_pos hequal, mul_zero]
    exact Finset.sum_nonneg fun i hi => (hpositive i hi).le
  · change (weight pair.1.1 * gamma ^ pair.2) *
        (if readout pair.1.1 ((update^[pair.2]) x) =
          readout pair.1.1 ((update^[pair.2]) y) then 0 else 1) <= J.sum weight
    rw [if_neg hequal, mul_one]
    calc
      weight pair.1.1 * gamma ^ pair.2 <= weight pair.1.1 * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ hgamma.1.le hgamma.2) (hpositive pair.1.1 pair.1.2).le
      _ = weight pair.1.1 := mul_one _
      _ <= J.sum weight :=
        Finset.single_le_sum (fun i hi => (hpositive i hi).le) pair.1.2

private theorem discounted_prime_time_term_strong_triangle
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (update : X -> X) (gamma : Real)
    (hpositive : ∀ i ∈ J, 0 < weight i)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (x y z : X) (pair : {i // i ∈ J} × Nat) :
    (weight pair.1.1 * gamma ^ pair.2) *
        @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
          (readout pair.1.1 ((update^[pair.2]) x))
          (readout pair.1.1 ((update^[pair.2]) z)) <=
      max
        ((weight pair.1.1 * gamma ^ pair.2) *
          @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
            (readout pair.1.1 ((update^[pair.2]) x))
            (readout pair.1.1 ((update^[pair.2]) y)))
        ((weight pair.1.1 * gamma ^ pair.2) *
          @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
          (readout pair.1.1 ((update^[pair.2]) y))
          (readout pair.1.1 ((update^[pair.2]) z))) := by
  classical
  let a := readout pair.1.1 ((update^[pair.2]) x)
  let b := readout pair.1.1 ((update^[pair.2]) y)
  let c := readout pair.1.1 ((update^[pair.2]) z)
  have hcoordinate :
      @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1)) a c <=
        max
          (@discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1)) a b)
          (@discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1)) b c) := by
    simpa [weightedCoordinateDistance] using
      (weighted_joint_ultrapseudometric
        (I := Unit) (X := O pair.1.1) (O := fun _ => O pair.1.1)
        ({()} : Finset Unit) (fun _ => (1 : Real)) (fun _ => id)
        (by
          intro i hi
          norm_num)
        a b c)
  have hscalar : 0 <= weight pair.1.1 * gamma ^ pair.2 :=
    mul_nonneg (hpositive pair.1.1 pair.1.2).le (pow_nonneg hgamma.1.le pair.2)
  change (weight pair.1.1 * gamma ^ pair.2) *
      discreteOutputDistance a c <=
    max
      ((weight pair.1.1 * gamma ^ pair.2) * discreteOutputDistance a b)
      ((weight pair.1.1 * gamma ^ pair.2) * discreteOutputDistance b c)
  rw [← mul_max_of_nonneg _ _ hscalar]
  exact mul_le_mul_of_nonneg_left hcoordinate hscalar

/-- Source lines 2068-2077, Theorem 33.1: the finite weighted prime-time
prediction distance satisfies the strong triangle inequality.

Carrier conditions, quoted verbatim from the source volume
`docs/develop/theory/FORMAL_PRIME_OBSERVER_DYNAMICS.md`.  Both are
**section-level standing clauses of the source**, not assumptions introduced
here; the atom for Theorem 33.1 is a slice that does not carry them.

* line 2016, immediately before Definition 33.1:
  「为每个坐标指定正权重 \(w_i\)，定义：」
  -- the weights are positive by the source's own definition, which is exactly
  `hpositive : forall i, 0 < weight i`.
* section 33 heading, immediately before both Definition 33.1 and Theorem 33.1:
  「设 \(0<\gamma\le1\)。」
  -- which is exactly `hgamma : gamma ∈ Set.Ioc 0 1`.
* line 2083 restates both together:
  「若全部权重正且 \(\gamma>0\)，则：」

Honest boundary on the empty index set.  The source defines
`d_{J,gamma}^F` as a supremum over `i ∈ J, n ≥ 0` and does not say what it
means when `J = ∅`.  Lean's `iSup` totalises that case (`sSup ∅ = 0` on
`Real`), so this statement, quantified over every `J : Finset I`, also covers a
case the source leaves undefined.  In that case both sides are `0` and the
inequality holds trivially, so nothing stronger than the source is claimed
about it -- but the coverage itself is a formalisation artefact, not a source
assertion, and is recorded as such rather than removed: excluding it would
require adding a `J.Nonempty` hypothesis the source never states, which is the
same defect in the opposite direction. -/
theorem discounted_prime_time_distance_strong_triangle
    {I X : Type*} {O : I -> Type*}
    (J : Finset I) (weight : I -> Real) (readout : forall i, X -> O i)
    (update : X -> X) (gamma : Real)
    (hpositive : ∀ i, 0 < weight i)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (x y z : X) :
    discountedPrimeTimeDistance J weight readout update gamma x z <=
      max
        (discountedPrimeTimeDistance J weight readout update gamma x y)
        (discountedPrimeTimeDistance J weight readout update gamma y z) := by
  have hselected : ∀ i ∈ J, 0 < weight i := by
    intro i _
    exact hpositive i
  have hleft :=
    discounted_prime_time_terms_bddAbove
      J weight readout update gamma hselected hgamma x y
  have hright :=
    discounted_prime_time_terms_bddAbove
      J weight readout update gamma hselected hgamma y z
  unfold discountedPrimeTimeDistance
  calc
    (⨆ pair : {i // i ∈ J} × Nat,
        (weight pair.1.1 * gamma ^ pair.2) *
          @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
            (readout pair.1.1 ((update^[pair.2]) x))
            (readout pair.1.1 ((update^[pair.2]) z))) <=
      ⨆ pair : {i // i ∈ J} × Nat,
        max
          ((weight pair.1.1 * gamma ^ pair.2) *
            @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
              (readout pair.1.1 ((update^[pair.2]) x))
              (readout pair.1.1 ((update^[pair.2]) y)))
          ((weight pair.1.1 * gamma ^ pair.2) *
            @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
              (readout pair.1.1 ((update^[pair.2]) y))
              (readout pair.1.1 ((update^[pair.2]) z))) := by
      apply ciSup_mono (bbdAbove_range_sup hleft hright)
      exact discounted_prime_time_term_strong_triangle
        J weight readout update gamma hselected hgamma x y z
    _ = max
        (⨆ pair : {i // i ∈ J} × Nat,
          (weight pair.1.1 * gamma ^ pair.2) *
            @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
              (readout pair.1.1 ((update^[pair.2]) x))
              (readout pair.1.1 ((update^[pair.2]) y)))
        (⨆ pair : {i // i ∈ J} × Nat,
          (weight pair.1.1 * gamma ^ pair.2) *
            @discreteOutputDistance (O pair.1.1) (Classical.decEq (O pair.1.1))
              (readout pair.1.1 ((update^[pair.2]) y))
              (readout pair.1.1 ((update^[pair.2]) z))) :=
      ciSup_sup_eq hleft hright

/- Reverse probe for CAS-A1 and satisfiability witness: the public theorem
specializes to a concrete positive singleton Boolean observer. -/
example :
    discountedPrimeTimeDistance
        (O := fun _ : Unit => Bool) ({()} : Finset Unit) (fun _ => 1)
        (fun _ => id) id ((1 : Real) / 2) false true <=
      max
        (discountedPrimeTimeDistance
          (O := fun _ : Unit => Bool) ({()} : Finset Unit) (fun _ => 1)
          (fun _ => id) id ((1 : Real) / 2) false false)
        (discountedPrimeTimeDistance
          (O := fun _ : Unit => Bool) ({()} : Finset Unit) (fun _ => 1)
          (fun _ => id) id ((1 : Real) / 2) false true) := by
  have hpositive : ∀ i, 0 < (fun _ : Unit => (1 : Real)) i := by
    intro i
    norm_num
  have hgamma : ((1 : Real) / 2) ∈ Set.Ioc 0 1 := by
    constructor <;> norm_num
  simpa only [id_eq] using
    discounted_prime_time_distance_strong_triangle
      (I := Unit) (X := Bool) (O := fun _ => Bool)
      ({()} : Finset Unit) (fun _ => 1) (fun _ => id) id
      ((1 : Real) / 2) hpositive hgamma false false true

/- Non-collapse probe for CAS-A1's distance carrier: a positive singleton
identity readout distinguishes the two Boolean states. -/
example :
    discountedPrimeTimeDistance
        (O := fun _ : Unit => Bool) ({()} : Finset Unit) (fun _ => 1)
        (fun _ => id) id (1 : Real) false true = 1 := by
  simp [discountedPrimeTimeDistance, discreteOutputDistance]

end D5.S3.Observer.PrimeTimeGeometry.DiscountedPrimeTimeUltrametric
