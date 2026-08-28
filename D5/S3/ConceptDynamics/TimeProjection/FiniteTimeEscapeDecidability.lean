/- GID: D5/S3/ConceptDynamics/TimeProjection/FiniteTimeEscapeDecidability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TimeProjection/FiniteTimeEscapeDecidability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite range scans decide all three finite-time relations. -/

import D5.S3.ConceptDynamics.TimeProjection.PredictionExpansionEscape
import Mathlib.Data.Finset.Range

/- Library-search audit trail (2026-08-28):
   * Two current-tree collision searches for `TimeExpansionEscape`,
     `FiniteTimeEscapeDecidability`, the planned declaration names, and the
     three statement shapes found only the imported prediction definitions;
     no repository declaration constructs this three-part decision procedure.
   * Pinned Mathlib provides `Finset.decidableDforallFinset` and
     `Finset.decidableExistsAndFinset`, the finite scans used below, but no
     finite-time escape relation or combined decidability construction.
   * A grep.app query for `TimeExpansionEscape` returned HTTP 429 and no hit;
     the checked local third-party Lean packages contained no matching name. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TimeProjection.FiniteTimeEscapeDecidability

open PredictionExpansionEscape

universe u v

/-- Two states agree through horizon `N` and first become distinguishable in
the added interval through `N'`. The horizon proof is part of the address, not
an alias for `ExpansionEscape`. -/
def TimeExpansionEscape {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X)
    (N N' : Nat) (_h : N <= N') (x y : X) : Prop :=
  (forall k : Nat, k <= N ->
      readout (timeIter transition k x) =
        readout (timeIter transition k y)) /\
    exists k : Nat, N < k /\ k <= N' /\
      Not (readout (timeIter transition k x) =
        readout (timeIter transition k y))

/-- The independent bounded-quantifier definition is exactly the pair of
finite scans through the old and new horizons. -/
theorem time_expansion_escape_iff_finset_scans
    {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X)
    (N N' : Nat) (h : N <= N') (x y : X) :
    TimeExpansionEscape readout transition N N' h x y <->
      ((forall k (_ : k ∈ Finset.range (N + 1)),
          readout (timeIter transition k x) =
            readout (timeIter transition k y)) /\
        exists k, k ∈ Finset.range (N' + 1) /\ N < k /\
          Not (readout (timeIter transition k x) =
            readout (timeIter transition k y))) := by
  constructor
  · rintro ⟨hOld, k, hAfter, hBound, hDifferent⟩
    refine ⟨?_, ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hBound),
      hAfter, hDifferent⟩⟩
    intro j hj
    exact hOld j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  · rintro ⟨hOld, k, hk, hAfter, hDifferent⟩
    refine ⟨?_, ⟨k, hAfter,
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hDifferent⟩⟩
    intro j hj
    exact hOld j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

/-- The bounded witness in `PredictionEscape` is found by scanning exactly the
coordinates in `Finset.range (N + 1)`. -/
theorem prediction_escape_iff_finset_scan
    {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X)
    (N : Nat) (x y : X) :
    PredictionEscape readout transition N x y <->
      (readout x = readout y /\
        exists k, k ∈ Finset.range (N + 1) /\
          Not (readout (timeIter transition k x) =
            readout (timeIter transition k y))) := by
  constructor
  · rintro ⟨hCurrent, k, hBound, hDifferent⟩
    exact ⟨hCurrent, k,
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hBound), hDifferent⟩
  · rintro ⟨hCurrent, k, hk, hDifferent⟩
    exact ⟨hCurrent, k,
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hDifferent⟩

/-- Equality of the finite projections is exactly equality at every coordinate
enumerated by `Finset.range (N + 1)`. -/
theorem time_projection_eq_iff_finset_scan
    {X : Type u} {O : Type v}
    (readout : X -> O) (transition : X -> X)
    (N : Nat) (x y : X) :
    timeProjection readout transition N x =
        timeProjection readout transition N y <->
      forall k (_ : k ∈ Finset.range (N + 1)),
        readout (timeIter transition k x) =
          readout (timeIter transition k y) := by
  constructor
  · intro hProjection k hk
    simpa [timeProjection] using congrFun hProjection
      (⟨k, Finset.mem_range.mp hk⟩ : TimeIndex N)
  · intro hScan
    funext i
    simpa [timeProjection] using
      hScan i.1 (Finset.mem_range.mpr i.2)

/-- The explicit old/new horizon scans decide time-expansion escape. -/
def timeExpansionEscapeDecidable
    {X : Type u} {O : Type v} [DecidableEq O]
    (readout : X -> O) (transition : X -> X)
    (N N' : Nat) (h : N <= N') (x y : X) :
    Decidable (TimeExpansionEscape readout transition N N' h x y) :=
  decidable_of_iff
    ((forall k (_ : k ∈ Finset.range (N + 1)),
        readout (timeIter transition k x) =
          readout (timeIter transition k y)) /\
      exists k, k ∈ Finset.range (N' + 1) /\ N < k /\
        Not (readout (timeIter transition k x) =
          readout (timeIter transition k y)))
    (time_expansion_escape_iff_finset_scans
      readout transition N N' h x y).symm

/-- The finite prediction horizon scan decides prediction escape. -/
def predictionEscapeDecidable
    {X : Type u} {O : Type v} [DecidableEq O]
    (readout : X -> O) (transition : X -> X)
    (N : Nat) (x y : X) :
    Decidable (PredictionEscape readout transition N x y) :=
  decidable_of_iff
    (readout x = readout y /\
      exists k, k ∈ Finset.range (N + 1) /\
        Not (readout (timeIter transition k x) =
          readout (timeIter transition k y)))
    (prediction_escape_iff_finset_scan
      readout transition N x y).symm

/-- The finite coordinate scan decides equality of two projected orbit words. -/
def timeProjectionEqDecidable
    {X : Type u} {O : Type v} [DecidableEq O]
    (readout : X -> O) (transition : X -> X)
    (N : Nat) (x y : X) :
    Decidable
      (timeProjection readout transition N x =
        timeProjection readout transition N y) :=
  decidable_of_iff
    (forall k (_ : k ∈ Finset.range (N + 1)),
      readout (timeIter transition k x) =
        readout (timeIter transition k y))
    (time_projection_eq_iff_finset_scan
      readout transition N x y).symm

/-- The three finite scans required by DECT 56.4-E, constructed without any
finiteness or inhabitance assumption on the state or output carrier. -/
def finite_time_escape_decidability
    {X : Type u} {O : Type v} [DecidableEq O]
    (readout : X -> O) (transition : X -> X)
    (N N' : Nat) (h : N <= N') (x y : X) :
    Decidable (TimeExpansionEscape readout transition N N' h x y) ×
      Decidable (PredictionEscape readout transition N x y) ×
        Decidable
          (timeProjection readout transition N x =
            timeProjection readout transition N y) :=
  ⟨timeExpansionEscapeDecidable readout transition N N' h x y,
    predictionEscapeDecidable readout transition N x y,
    timeProjectionEqDecidable readout transition N x y⟩

/- Domain-inhabitance witness; no global `Nonempty X` instance is required. -/
example : Fin 3 := 0

/- A nontrivial instance satisfying the horizon premise and the independently
defined escape relation: the two states agree now and differ after one step. -/
example :
    let readout : Fin 3 -> Bool := fun state =>
      if state = 2 then true else false
    let transition : Fin 3 -> Fin 3 := fun state =>
      if state = 1 then 2 else state
    TimeExpansionEscape readout transition 0 1 (by decide) 0 1 := by
  dsimp
  refine ⟨?_, ⟨1, by decide, by decide, ?_⟩⟩
  · intro k hk
    have hkZero : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    decide
  · decide

#print axioms time_expansion_escape_iff_finset_scans
#print axioms prediction_escape_iff_finset_scan
#print axioms time_projection_eq_iff_finset_scan
#print axioms finite_time_escape_decidability

end D5.S3.ConceptDynamics.TimeProjection.FiniteTimeEscapeDecidability
