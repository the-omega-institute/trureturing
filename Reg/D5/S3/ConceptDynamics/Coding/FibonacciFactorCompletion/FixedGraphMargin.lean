import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal71
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => List Return
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ xs => xs) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (R : Return) (w : List CuLetter) (xs ys : List Return) (hx : CanonicalFactorCompletion R w xs) (hy : CanonicalFactorCompletion R w ys), r.readout () () xs = ys

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let R : Return := ⟨1, 1, by decide, by decide⟩
  have hc : CanonicalFactorCompletion R [] [R] := by simp [CanonicalFactorCompletion, R]
  have bad := h R [] [R] [R] hc hc
  cases bad

def evidence : Registration sourceArena (type_of% @canonical_factor_completion_unique) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_factor_completion_unique, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [⟨1, 1, by decide, by decide⟩], ?_⟩
    simp [actual, realize]

def canonical_factor_completion_unique_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.canonical_factor_completion_unique)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ xs => xs) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal71.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal71.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ xs => xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms canonical_factor_completion_unique_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal71


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
noncomputable section

abbrev marginSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
    (fun _ => ℝ) (fun _ => ℝ)

def marginActual : Realization marginSignature :=
  realize marginSignature (fun _ p d => graphMargin p.1 p.2 d) (fun e => nomatch e)

/-- The one-letter lower graph has exactly one allowed high-edge gap below its guard. -/
theorem graph_gap_values_one (d : ℝ) (hd : d < aSide .high) :
    graphGapValues 1 1 d = {aSide .high - d} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have edge := (Finset.mem_filter.mp hv).2.1
    have hu : v 0 = .u := by
      cases h : v 0 with
      | u => rfl
      | c =>
        exact False.elim (edge.2.1 ⟨rfl, by
          intro k hk
          have hk0 : k = 0 := Subsingleton.elim _ _
          simpa only [hk0] using h⟩)
    simp [memoryValue, hu, letterMap]
  · intro hx
    have hx' : x = aSide .high - d := Finset.mem_singleton.mp hx
    rw [hx']
    apply Finset.mem_image.mpr
    refine ⟨(fun _ : Fin 1 => CuLetter.u),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · refine ⟨rfl, ?_, ?_⟩
      · intro h
        have bad := h.2 (0 : Fin 1) (by decide)
        cases bad
      · intro h
        simpa [memoryGuard, memoryValue, letterMap] using hd
    · constructor
      · rfl
      · intro k hk
        have := k.isLt
        omega
    · simp [memoryValue, letterMap]

theorem graph_margin_one (d : ℝ) (hd : d < aSide .high) :
    graphMargin 1 1 d = aSide .high - d := by
  simp [graphMargin, graph_gap_values_one d hd]

theorem margin_actual_dependence : ObservationalDependence marginSignature marginActual := by
  intro i
  refine ⟨⟨1, 1⟩, aSide .high - 1, aSide .high - 2, ?_⟩
  change graphMargin 1 1 (aSide .high - 1) ≠ graphMargin 1 1 (aSide .high - 2)
  rw [graph_margin_one _ (by linarith), graph_margin_one _ (by linarith)]
  linarith

abbrev minimumArena : Arena.{0,0,0,0,0} where
  signature := marginSignature
  Law r := ∀ (n K : ℕ) (d : ℝ) (nonempty : (graphGapValues n K d).Nonempty),
    0 < r.readout () ⟨n, K⟩ d ∧
      IsLeast (↑(graphGapValues n K d) : Set ℝ) (graphMargin n K d)

def minimumRejected : Realization marginSignature :=
  realize marginSignature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

theorem minimum_rejected : ¬ minimumArena.Law minimumRejected := by
  intro h
  have occupied : (graphGapValues 1 1 (aSide .high - 1)).Nonempty := by
    rw [graph_gap_values_one _ (by linarith)]
    exact Finset.singleton_nonempty _
  have bad := (h 1 1 (aSide .high - 1) occupied).1
  exact (lt_irrefl (0 : ℝ)) bad

def minimumRegistration : Registration minimumArena (type_of% @graph_gap_minimum) where
  actual := marginActual
  bridge := Iff.rfl
  variation := ⟨@graph_gap_minimum, minimumRejected, minimum_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    minimumArena.Law marginActual minimumRejected minimum_rejected
  dependence := margin_actual_dependence

/-- An inhabited bilateral history with a single high letter. -/
def isolatedHigh (i : ℤ) : CuLetter := if i = 0 then .c else .u

theorem isolated_high_eq (i : ℤ) : isolatedHigh i = .c ↔ i = 0 := by
  simp [isolatedHigh]

theorem isolated_high_member :
    isolatedHigh ∈ MemoryLanguage .lower 1 1 (aSide .high - 1) := by
  constructor
  · intro i h
    have h0 : i = 0 := (isolated_high_eq i).mp (by simpa using h 0)
    have h1 := h (1 : Fin 2)
    simp [h0, isolatedHigh] at h1
  · intro i high
    have hi : i = 0 := (isolated_high_eq i).mp (by simpa using high 0)
    subst i
    simp [finitePast, isolatedHigh, letterMap]

theorem isolated_high_at_zero : ∀ k : Fin 1, isolatedHigh (0 - (k : ℕ)) = .c := by
  intro k
  have hk : k = 0 := Subsingleton.elim _ _
  simp [hk, isolatedHigh]

abbrev highGapArena : Arena.{0,0,0,0,0} where
  signature := marginSignature
  Law r := ∀ (n K : ℕ) (d : ℝ) (positive : 0 < K) (memory : K ≤ n)
    (ω : ℤ → CuLetter) (member : ω ∈ MemoryLanguage .lower n K d)
    (i : ℤ) (high : ∀ k : Fin K, ω (i - (k : ℕ)) = .c),
    (graphGapValues n K d).Nonempty ∧
      r.readout () ⟨n, K⟩ d ≤ pastState ω i - chi ^ (K - 1) * d

def highGapRejected : Realization marginSignature :=
  realize marginSignature (fun _ _ d => hSide .high - d + 1) (fun e => nomatch e)

theorem high_gap_rejected : ¬ highGapArena.Law highGapRejected := by
  intro h
  have bad := (h 1 1 (aSide .high - 1) (by decide) (by decide)
    isolatedHigh isolated_high_member 0 isolated_high_at_zero).2
  have bound := (bilateral_past_state.2.2.1 isolatedHigh 0).2
  change hSide .high - (aSide .high - 1) + 1 ≤
    pastState isolatedHigh 0 - chi ^ (1 - 1) * (aSide .high - 1) at bad
  norm_num at bad
  linarith

def highGapRegistration : Registration highGapArena (type_of% @lower_graph_high_gap) where
  actual := marginActual
  bridge := Iff.rfl
  variation := ⟨@lower_graph_high_gap, highGapRejected, high_gap_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    highGapArena.Law marginActual highGapRejected high_gap_rejected
  dependence := margin_actual_dependence


def graph_gap_minimum_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.graph_gap_minimum)
      (type_of% (realize.{0,0,0,0,0} marginSignature
        (fun _ p d => graphMargin p.1 p.2 d) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.graph_gap_minimum_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.minimumRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨minimumArena⟩
  objectArena := .source ⟨minimumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source minimumArena ⟨minimumRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} marginSignature
    (fun _ p d => graphMargin p.1 p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms minimumRegistration
#print axioms graph_gap_minimum_registration


def lower_graph_high_gap_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.lower_graph_high_gap)
      (type_of% (realize.{0,0,0,0,0} marginSignature
        (fun _ p d => graphMargin p.1 p.2 d) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.lower_graph_high_gap_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.highGapRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨highGapArena⟩
  objectArena := .source ⟨highGapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source highGapArena ⟨highGapRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} marginSignature
    (fun _ p d => graphMargin p.1 p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms highGapRegistration
#print axioms lower_graph_high_gap_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal72
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.observationSignature

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ b => b) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => actualAutomaticCost 2 - 1) (fun e => nomatch e)

/-- Only the budget operand in the positive-margin conjunct is observed.
Every other budget occurrence and every clause of the original Law is retained. -/
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (n K : ℕ) (b : ℝ) (hK : 2 ≤ K) (memory : K ≤ n)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) < resetFloor R ∧
      0 < fixedGraphActualMargin n K (r.readout () () b) R ∧
      ((graphGapValues n K ((lam - b) / g ^ 2 / chi ^ K)).Nonempty →
        0 < graphMargin n K ((lam - b) / g ^ 2 / chi ^ K) ∧
        IsLeast (↑(graphGapValues n K ((lam - b) / g ^ 2 / chi ^ K)) : Set ℝ)
          (graphMargin n K ((lam - b) / g ^ 2 / chi ^ K))) ∧
      ∀ (model : Model) (o : Ownership) (w : List CuLetter),
        (∃ ω ∈ MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K), Occurs ω w) →
        ∃! xs : List Return, CanonicalFactorCompletion R w xs ∧
          ActualPairSupply model o (b - fixedGraphActualMargin n K b R) .strict xs ∧
          listWeight xs = wordWeight w + (20 + 6 * R.m) +
            (if CuLetter.c ∈ w then if w.getLast? = some CuLetter.c then 12 else 6 else 0)

/-- The original half minimum cannot exceed its automatic term divided by two. -/
theorem rejected_margin_nonpositive (R : Return) :
    fixedGraphActualMargin 2 2 (actualAutomaticCost 2 - 1) R ≤ 0 := by
  classical
  dsimp [fixedGraphActualMargin]
  split_ifs
  · have bound := (min_le_left
      (min (actualAutomaticCost 2 - 1 - actualAutomaticCost 2)
        (g ^ 2 * chi ^ 2 *
          (resetFloor R - (lam - (actualAutomaticCost 2 - 1)) / g ^ 2 / chi ^ 2)))
      (g ^ 2 * chi * graphMargin 2 2
        ((lam - (actualAutomaticCost 2 - 1)) / g ^ 2 / chi ^ 2))).trans
      (min_le_left _ _)
    linarith
  · have bound := min_le_left
      (actualAutomaticCost 2 - 1 - actualAutomaticCost 2)
      (g ^ 2 * chi ^ 2 *
        (resetFloor R - (lam - (actualAutomaticCost 2 - 1)) / g ^ 2 / chi ^ 2))
    linarith

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hqb, hbp⟩ :=
    Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.record_interval_nonempty
  obtain ⟨R, _, _, positive, _⟩ := h 2 2 b le_rfl le_rfl hqb hbp
  change 0 < fixedGraphActualMargin 2 2 (actualAutomaticCost 2 - 1) R at positive
  exact (not_lt_of_ge (rejected_margin_nonpositive R)) positive

def evidence : Registration sourceArena (type_of% @fixed_lower_graph_actual_margin) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_lower_graph_actual_margin, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence :=
    Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.ExactOriginal150.evidence.dependence

def fixed_lower_graph_actual_margin_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.fixed_lower_graph_actual_margin)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ b => b) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal72.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal72.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rejected_margin_nonpositive
#print axioms rejected_law
#print axioms evidence
#print axioms fixed_lower_graph_actual_margin_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin.ExactOriginal72
