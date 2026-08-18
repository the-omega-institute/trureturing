/- GID: D5/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius
   generality: I
   mirror-B: D5/B/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden mechanical readouts have finite local stability but no uniform infinite-future radius. -/

import D5.S1.Words.Complexity.MechanicalSubshiftIntercept
import D5.S3.Observer.SymbolicStability.FinitePrefixLocalConstancy
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Instances.AddCircle.Real

/- Library-search audit trail (2026-08-18):
   * No exact theorem for the full finite/infinite symbolic-stability conjunction was
     found in D5 or pinned Mathlib.
   * D5 provides the exact finite-prefix theorem
     `finite_prefix_locally_constant_off_boundary`; it is applied below.
   * D5 provides the exact irrational-rotation interval hit
     `exists_phase_mem_Ioo`; it is applied below.
   * Pinned Mathlib provides `Int.floor_eq_iff`, `Int.floor_add_fract`, and
     translation invariance of the additive quotient metric; these are applied below. -/

namespace D5.S3.Observer.SymbolicStability.NoUniformInfiniteFutureRadius

open D5.S1.Words.Complexity.MechanicalSubshiftIntercept
open D5.S1.Words.Mechanical
open D5.S3.Observer.SymbolicStability.FinitePrefixLocalConstancy
open Filter
open Set

noncomputable section

/-- The slope used by the golden observer in the source statement. -/
def goldenObserverSlope : Real := Real.goldenRatio⁻¹ ^ 2

/-- The integer-valued floor-difference readout at future coordinate `n`. -/
def goldenObserverReadout (n : Nat) (theta : Real) : Int :=
  lowerMechanicalLetter goldenObserverSlope theta n

/-- Integer lifts of the first `N + 1` circular readout boundaries. -/
def goldenObserverPrefixBoundary (N : Nat) : Set Real :=
  {theta | ∃ n : Nat, n ≤ N ∧
    ∃ z : Int, theta + (n : Real) * goldenObserverSlope = z}

/-- Addition by the golden observer slope on the unit circle. -/
def goldenObserverRotation (theta : AddCircle (1 : Real)) : AddCircle (1 : Real) :=
  theta + (goldenObserverSlope : AddCircle (1 : Real))

private theorem golden_observer_slope_add_inverse :
    goldenObserverSlope + Real.goldenRatio⁻¹ = 1 := by
  rw [goldenObserverSlope, Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem golden_observer_slope_pos : 0 < goldenObserverSlope := by
  exact pow_pos (inv_pos.mpr Real.goldenRatio_pos) 2

private theorem golden_observer_slope_lt_one : goldenObserverSlope < 1 := by
  have hinv : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  linarith [golden_observer_slope_add_inverse]

private theorem golden_observer_slope_irrational : Irrational goldenObserverSlope := by
  have hirr : Irrational (1 - Real.goldenRatio⁻¹) := by
    simpa using Real.goldenRatio_irrational.inv.ratCast_sub (1 : Rat)
  rw [show goldenObserverSlope = 1 - Real.goldenRatio⁻¹ by
    linarith [golden_observer_slope_add_inverse]]
  exact hirr

private theorem eventually_floor_eq_of_not_integer (x : Real)
    (hx : ¬ ∃ z : Int, x = z) :
    ∀ᶠ y in nhds x, ⌊y⌋ = ⌊x⌋ := by
  have hlower : ((⌊x⌋ : Int) : Real) < x := by
    refine lt_of_le_of_ne (Int.floor_le x) ?_
    intro heq
    exact hx ⟨⌊x⌋, heq.symm⟩
  have hupper : x < ((⌊x⌋ : Int) : Real) + 1 := Int.lt_floor_add_one x
  filter_upwards [Ioo_mem_nhds hlower hupper] with y hy
  exact Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩

private theorem readout_eventually_eq_of_off_cuts (n : Nat) (theta : Real)
    (hleft : ¬ ∃ z : Int,
      theta + (n : Real) * goldenObserverSlope = z)
    (hright : ¬ ∃ z : Int,
      theta + ((n + 1 : Nat) : Real) * goldenObserverSlope = z) :
    ∀ᶠ theta' in nhds theta,
      goldenObserverReadout n theta' = goldenObserverReadout n theta := by
  let left : Real → Real := fun x => x + (n : Real) * goldenObserverSlope
  let right : Real → Real := fun x => x + ((n + 1 : Nat) : Real) * goldenObserverSlope
  have hleftTendsto : Tendsto left (nhds theta) (nhds (left theta)) := by
    change ContinuousAt left theta
    exact continuousAt_id.add continuousAt_const
  have hrightTendsto : Tendsto right (nhds theta) (nhds (right theta)) := by
    change ContinuousAt right theta
    exact continuousAt_id.add continuousAt_const
  have hleftEventually : ∀ᶠ theta' in nhds theta,
      ⌊left theta'⌋ = ⌊left theta⌋ :=
    hleftTendsto.eventually (eventually_floor_eq_of_not_integer _ hleft)
  have hrightEventually : ∀ᶠ theta' in nhds theta,
      ⌊right theta'⌋ = ⌊right theta⌋ :=
    hrightTendsto.eventually (eventually_floor_eq_of_not_integer _ hright)
  filter_upwards [hleftEventually, hrightEventually] with theta' hl hr
  simp only [goldenObserverReadout, lowerMechanicalLetter, left, right] at hl hr ⊢
  rw [hl, hr]

private theorem finite_prefix_stability (N : Nat) (theta : Real)
    (houtside : theta ∉ goldenObserverPrefixBoundary N) :
    ∃ epsilon : Real, 0 < epsilon ∧
      ∀ theta', dist theta' theta < epsilon →
        ∀ n : Fin N,
          goldenObserverReadout n theta' = goldenObserverReadout n theta := by
  let boundary : Fin N → Set Real := fun n =>
    {x | (∃ z : Int, x + (n : Nat) * goldenObserverSlope = z) ∨
      ∃ z : Int, x + ((n : Nat) + 1) * goldenObserverSlope = z}
  apply finite_prefix_locally_constant_off_boundary
    (fun n : Fin N => goldenObserverReadout n)
    boundary
  · intro n x hx
    apply readout_eventually_eq_of_off_cuts
    · intro hcut
      apply hx
      exact Or.inl hcut
    · intro hcut
      apply hx
      right
      simpa only [Nat.cast_add, Nat.cast_one] using hcut
  · intro hboundary
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hboundary
    change (∃ z : Int, theta + (n : Nat) * goldenObserverSlope = z) ∨
      ∃ z : Int, theta + ((n : Nat) + 1) * goldenObserverSlope = z at hn
    apply houtside
    change ∃ k : Nat, k ≤ N ∧
      ∃ z : Int, theta + (k : Real) * goldenObserverSlope = z
    rcases hn with hn | hn
    · exact ⟨n, Nat.le_of_lt n.isLt, hn⟩
    · refine ⟨(n : Nat) + 1, n.isLt, ?_⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hn

private theorem exists_close_readout_split (theta epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ theta' n, dist theta' theta < epsilon ∧
      goldenObserverReadout n theta' ≠ goldenObserverReadout n theta := by
  let eta : Real := min epsilon goldenObserverSlope / 2
  have hetaPos : 0 < eta := by
    dsimp [eta]
    exact div_pos (lt_min hepsilon golden_observer_slope_pos) (by norm_num)
  have hetaLeOne : eta ≤ 1 := by
    have hmin := min_le_right epsilon goldenObserverSlope
    dsimp [eta]
    linarith [golden_observer_slope_pos, golden_observer_slope_lt_one]
  obtain ⟨n, hn⟩ := exists_phase_mem_Ioo
    (alpha := -goldenObserverSlope) (rho := -theta)
    golden_observer_slope_irrational.neg (by norm_num) hetaPos hetaLeOne
  let x : Real := -theta + (n : Real) * (-goldenObserverSlope)
  let t : Real := Int.fract x
  let z : Int := -⌊x⌋
  let boundaryPoint : Real := theta + t
  let leftPoint : Real := theta + t / 2
  have htPos : 0 < t := hn.1
  have htEta : t < eta := hn.2
  have htSlope : t / 2 < goldenObserverSlope := by
    have hmin := min_le_right epsilon goldenObserverSlope
    dsimp [eta] at htEta
    linarith [golden_observer_slope_pos]
  have htOne : t / 2 < 1 :=
    htSlope.trans golden_observer_slope_lt_one
  have hx : x = -theta - (n : Real) * goldenObserverSlope := by
    dsimp [x]
    ring
  have hfract : ((⌊x⌋ : Int) : Real) + t = x := by
    exact Int.floor_add_fract x
  have hz : boundaryPoint + (n : Real) * goldenObserverSlope = (z : Real) := by
    dsimp [boundaryPoint, z]
    push_cast
    linarith [hfract, hx]
  have hboundaryNumerator :
      boundaryPoint + ((n + 1 : Nat) : Real) * goldenObserverSlope =
        (z : Real) + goldenObserverSlope := by
    push_cast
    linarith [hz]
  have hleftDenominator :
      leftPoint + (n : Real) * goldenObserverSlope = (z : Real) - t / 2 := by
    dsimp [leftPoint, boundaryPoint] at hz ⊢
    linarith
  have hleftNumerator :
      leftPoint + ((n + 1 : Nat) : Real) * goldenObserverSlope =
        (z : Real) + goldenObserverSlope - t / 2 := by
    push_cast
    linarith [hleftDenominator]
  have hfloorBoundaryDenominator :
      ⌊boundaryPoint + (n : Real) * goldenObserverSlope⌋ = z := by
    rw [hz, Int.floor_intCast]
  have hfloorBoundaryNumerator :
      ⌊boundaryPoint + ((n + 1 : Nat) : Real) * goldenObserverSlope⌋ = z := by
    rw [hboundaryNumerator]
    exact Int.floor_eq_iff.mpr
      ⟨by linarith [golden_observer_slope_pos],
       by linarith [golden_observer_slope_lt_one]⟩
  have hfloorLeftDenominator :
      ⌊leftPoint + (n : Real) * goldenObserverSlope⌋ = z - 1 := by
    rw [hleftDenominator]
    exact Int.floor_eq_iff.mpr
      ⟨by push_cast; linarith,
       by push_cast; linarith⟩
  have hfloorLeftNumerator :
      ⌊leftPoint + ((n + 1 : Nat) : Real) * goldenObserverSlope⌋ = z := by
    rw [hleftNumerator]
    exact Int.floor_eq_iff.mpr
      ⟨by linarith,
       by linarith [golden_observer_slope_lt_one, htPos]⟩
  have hboundaryReadout : goldenObserverReadout n boundaryPoint = 0 := by
    simp only [goldenObserverReadout, lowerMechanicalLetter]
    rw [hfloorBoundaryNumerator, hfloorBoundaryDenominator]
    omega
  have hleftReadout : goldenObserverReadout n leftPoint = 1 := by
    simp only [goldenObserverReadout, lowerMechanicalLetter]
    rw [hfloorLeftNumerator, hfloorLeftDenominator]
    omega
  have hboundaryClose : dist boundaryPoint theta < epsilon := by
    rw [Real.dist_eq]
    dsimp [boundaryPoint]
    rw [add_sub_cancel_left, abs_of_pos htPos]
    have hmin := min_le_left epsilon goldenObserverSlope
    dsimp [eta] at htEta
    linarith
  have hleftClose : dist leftPoint theta < epsilon := by
    rw [Real.dist_eq]
    dsimp [leftPoint]
    rw [add_sub_cancel_left, abs_of_pos (half_pos htPos)]
    have hmin := min_le_left epsilon goldenObserverSlope
    dsimp [eta] at htEta
    linarith
  by_cases hboundary :
      goldenObserverReadout n boundaryPoint ≠ goldenObserverReadout n theta
  · exact ⟨boundaryPoint, n, hboundaryClose, hboundary⟩
  · have hboundaryEq :
        goldenObserverReadout n boundaryPoint = goldenObserverReadout n theta :=
      not_ne_iff.mp hboundary
    refine ⟨leftPoint, n, hleftClose, ?_⟩
    rw [← hboundaryEq, hleftReadout, hboundaryReadout]
    norm_num

private theorem rotation_iterate_preserves_distance (n : Nat)
    (theta theta' : AddCircle (1 : Real)) :
    dist ((goldenObserverRotation^[n]) theta)
        ((goldenObserverRotation^[n]) theta') = dist theta theta' := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [goldenObserverRotation, dist_add_right]
      exact ih

/-- For the golden floor readout, every finite prefix is locally stable off its
finite boundary set, but every infinite-future stability radius is split by some
later symbol. The underlying circle rotation nevertheless preserves distance. -/
theorem no_uniform_infinite_future_stability_radius :
    (∀ theta epsilon, 0 < epsilon →
      ∃ theta' n, dist theta' theta < epsilon ∧
        goldenObserverReadout n theta' ≠ goldenObserverReadout n theta) ∧
    (∀ N theta, theta ∉ goldenObserverPrefixBoundary N →
      ∃ epsilon, 0 < epsilon ∧
        ∀ theta', dist theta' theta < epsilon →
          ∀ n : Fin N,
            goldenObserverReadout n theta' = goldenObserverReadout n theta) ∧
    (∀ theta, ¬ ∃ epsilon, 0 < epsilon ∧
      ∀ theta', dist theta' theta < epsilon →
        ∀ n, goldenObserverReadout n theta' = goldenObserverReadout n theta) ∧
    (∀ n theta theta',
      dist ((goldenObserverRotation^[n]) theta)
          ((goldenObserverRotation^[n]) theta') = dist theta theta') ∧
    (∀ theta epsilon, 0 < epsilon →
      ∃ theta' n, dist theta' theta < epsilon ∧
        goldenObserverReadout n theta' ≠ goldenObserverReadout n theta ∧
        dist ((goldenObserverRotation^[n])
              (theta' : AddCircle (1 : Real)))
            ((goldenObserverRotation^[n])
              (theta : AddCircle (1 : Real))) =
          dist (theta' : AddCircle (1 : Real))
            (theta : AddCircle (1 : Real))) := by
  have hclose := exists_close_readout_split
  have hfinite := finite_prefix_stability
  have hnoRadius : ∀ theta, ¬ ∃ epsilon, 0 < epsilon ∧
      ∀ theta', dist theta' theta < epsilon →
        ∀ n, goldenObserverReadout n theta' = goldenObserverReadout n theta := by
    intro theta hstable
    obtain ⟨epsilon, hepsilon, hsame⟩ := hstable
    obtain ⟨theta', n, hdist, hne⟩ := hclose theta epsilon hepsilon
    exact hne (hsame theta' hdist n)
  refine ⟨hclose, hfinite, hnoRadius, rotation_iterate_preserves_distance, ?_⟩
  intro theta epsilon hepsilon
  obtain ⟨theta', n, hdist, hne⟩ := hclose theta epsilon hepsilon
  exact ⟨theta', n, hdist, hne,
    rotation_iterate_preserves_distance n
      (theta' : AddCircle (1 : Real)) (theta : AddCircle (1 : Real))⟩

#print axioms no_uniform_infinite_future_stability_radius

end

end D5.S3.Observer.SymbolicStability.NoUniformInfiniteFutureRadius
