/- GID: D5/S1/Digit/Infinite/MarkerHyperfiniteness
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/MarkerHyperfiniteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shrinking circle markers yield increasing finite Borel equivalences exhausting rotation orbits and asynchronous merging of legal streams. -/

import D5.S1.Digit.Infinite.WindowSuccessorGraph
import D5.S1.Digit.Infinite.PhaseOrbitRelations

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.MarkerHyperfiniteness
open Set
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.WindowSuccessorGraph (G)
open D5.S1.Digit.Infinite.MultiplierObstruction
open D5.S1.Digit.Infinite.PhaseOrbitRelations
/-- The real circle with circumference one. -/
abbrev MarkerCircle := AddCircle (1 : ℝ)
/-- The length of the nth marker arc. -/
noncomputable def markerEll (n : ℕ) : ℝ := 1 / ((n:ℝ)+2)

/-- The image of the open interval from zero to the nth marker length in the circle. -/
noncomputable def markerU (n : ℕ) : Set MarkerCircle :=
  (fun x : ℝ => (x : MarkerCircle)) '' Set.Ioo 0 (markerEll n)

/-- The least positive odd index whose corresponding power of alpha is below the marker length. -/
noncomputable def markerJ (n : ℕ) : ℕ := Nat.find (show ∃ j : ℕ, 1 ≤ j ∧ j%2=1 ∧ alpha^(j+2)< markerEll n  from by
  have ha : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
  have hb : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have he : 0 < markerEll n := by unfold markerEll; positivity
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one he hb
  refine ⟨2*k+1,by omega,by omega,?_⟩
  have hm : alpha^(2*k+1+2) ≤ alpha^k :=
    pow_le_pow_of_le_one ha.le hb.le (by omega)
  exact hm.trans_lt hk)

/-- The small rotation increment selected by the nth marker index. -/
noncomputable def markerH (n : ℕ) : ℝ := alpha^(markerJ n+2)

/-- The Fibonacci return time selected by the nth marker index. -/
noncomputable def markerQ (n : ℕ) : ℕ := G (markerJ n)

/-- The natural floor of the reciprocal of the positive marker increment. -/
noncomputable def markerM (n : ℕ) : ℕ := ⌊1 / markerH n⌋₊

/-- The uniform bound on the time needed to visit the nth marker arc. -/
noncomputable def markerB (n : ℕ) : ℕ := markerQ n * markerM n

/-- The bound on the distance between adjacent deleted edge sources. -/
noncomputable def markerL (n : ℕ) : ℕ := markerB n+1

/-- Integer iterates of rotation by the golden ratio on the circle. -/
noncomputable def rotate (k : ℤ) (x : MarkerCircle) : MarkerCircle :=
  x + k • (Real.goldenRatio : MarkerCircle)

/-- A directed rotation edge retained exactly when its source is outside the marker arc. -/
def remainingEdge (n : ℕ) (x y : MarkerCircle) : Prop := x ∉ markerU n ∧ y=rotate 1 x

/-- Connectivity by finite undirected paths of retained rotation edges, including empty paths. -/
def markerF (n : ℕ) : MarkerCircle → MarkerCircle → Prop :=
  Relation.ReflTransGen (fun x y => remainingEdge n x y ∨ remainingEdge n y x)

/-- The pullback of the nth circle path relation along the phase map of legal streams. -/
def markerG (n : ℕ) (x y : LegalDigits) : Prop := markerF n (phase x) (phase y)

/-- Every integer interval of the specified length contains a visit to the marker arc. -/
def VisitBoundSpec : Prop := ∀ n (x : MarkerCircle) (a : ℤ),
  ∃ k : ℤ, a ≤ k ∧ k ≤ a+(markerB n:ℤ) ∧ rotate k x ∈ markerU n

/-- An equivalence relation whose graph belongs to the Borel sigma algebra of the product topology. -/
def BorelEquivalence {X : Type*} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  Equivalence E ∧ @MeasurableSet (X × X) (borel (X × X)) {p | E p.1 p.2}

/-- An increasing family indexed by all natural numbers of finite Borel equivalences exhausting a relation. -/
def Hyperfinite {X : Type*} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  ∃ F : ℕ → X → X → Prop, Monotone F ∧
    (∀ n, BorelEquivalence (F n) ∧ ∀ x, Set.Finite {y | F n x y}) ∧
    ∀ x y, E x y ↔ ∃ n, F n x y

/-- A forward or backward step of the circle rotation, according to a Boolean letter. -/
noncomputable def step (b : Bool) (x : MarkerCircle) : MarkerCircle := rotate (if b then 1 else -1) x

/-- A step is permitted exactly when the source of its underlying directed edge is unmarked. -/
def allowed (n : ℕ) (b : Bool) (x : MarkerCircle) : Prop :=
  (if b then x else rotate (-1) x) ∉ markerU n

/-- The endpoint reached by following a finite Boolean word of rotation steps. -/
noncomputable def walk : List Bool → MarkerCircle → MarkerCircle
  | [], x => x
  | b::bs, x => walk bs (step b x)

/-- Every step of a finite Boolean word is permitted from its successive starting points. -/
def valid (n : ℕ) : List Bool → MarkerCircle → Prop
  | [], _ => True
  | b::bs, x => allowed n b x ∧ valid n bs (step b x)

set_option maxHeartbeats 800000 in
/-- Shrinking open markers have uniformly bounded return gaps. Their undirected path relations
form increasing finite Borel equivalences exhausting circle rotation orbits; pulling them back
along phase gives such equivalences for asynchronous merging, with at most twice the class size. -/
theorem marker_hyperfiniteness :
    (∀ n, IsOpen (markerU n)) ∧ Antitone markerU ∧ (⋂ n, markerU n) = ∅ ∧
    VisitBoundSpec ∧
    (∀ n (x : MarkerCircle),
      (∀ b : ℤ, ∃ k : ℤ, b ≤ k ∧ rotate k x ∈ markerU n) ∧
      (∀ b : ℤ, ∃ k : ℤ, k ≤ b ∧ rotate k x ∈ markerU n) ∧
      (∀ c d : ℤ, c<d → rotate c x ∈ markerU n → rotate d x ∈ markerU n →
        (∀ k : ℤ, c<k → k<d → rotate k x ∉ markerU n) → d-c ≤ (markerL n:ℤ))) ∧
    (∀ n, BorelEquivalence (markerF n) ∧ ∀ t,
      Set.Finite {s | markerF n t s} ∧ {s | markerF n t s}.ncard ≤ markerL n) ∧
    Monotone markerF ∧ (∀ t s, ER t s ↔ ∃ n, markerF n t s) ∧
    (∀ n, BorelEquivalence (markerG n) ∧ ∀ x,
      Set.Finite {y | markerG n x y} ∧ {y | markerG n x y}.ncard ≤ 2 * markerL n) ∧
    Monotone markerG ∧ (∀ x y, ET x y ↔ ∃ n, markerG n x y) ∧
    Hyperfinite ER ∧ Hyperfinite ET := by
  sorry

end D5.S1.Digit.Infinite.MarkerHyperfiniteness
