import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder
import Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge OriginalAcquiredTrace PhysicalWindowDecoder
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace

/-- The complete source telescope, replacing only the original execution readout. -/
@[reducible] def scriptArena : Arena where
  signature := traceSignature.{u}
  Law R := ∀ {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (words : List (Fin m → Bool)) (decode : NarrowWindowCost.Archive m → Y)
    (w : List Bool) (free : Option (ZMod 2)) (base : NarrowWindowCost.Archive m),
    let issued := scriptArchive words (OriginalRecord k (by omega) w)
    PaidTrace (finalSelector base.length words decode) free
      (OriginalRecord k (by omega) w) base issued (decode issued) ∧
    issued.map Prod.fst = words ∧ issued.length = words.length ∧
    R.readout () ⟨⟨k, hk⟩, m, Y⟩
      (w, finalSelector base.length words decode, words.length, free, base) =
      some (decode issued, words.length)

private theorem scriptPositive : scriptArena.{u}.Law traceActual := by
  intro Y k m hk words decode w free base
  exact original_final_script k m hk words decode w free base

private theorem scriptNegative : ¬ scriptArena.{u}.Law traceRejected := by
  intro law
  let label : ULift.{u} Unit := ⟨()⟩
  have impossible := (law 3 1 (by decide) [] (fun _ => label) [] (some 0) []).2.2.2
  cases impossible

def scriptEvidence : Registration scriptArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_final_script.{u})) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨scriptPositive, traceRejected, scriptNegative⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, scriptNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let Y := ULift.{u} Bool
    let π₀ : NarrowWindowCost.Selector 1 Y := fun _ _ => .inl ⟨false⟩
    let π₁ : NarrowWindowCost.Selector 1 Y := fun _ _ => .inl ⟨true⟩
    refine ⟨⟨⟨3, by decide⟩, 1, Y⟩,
      ([], π₀, 0, some 0, []), ([], π₁, 0, some 0, []), ?_⟩
    simp [traceActual, realize, NarrowWindowCost.execute, π₀, π₁]
    intro h
    cases congrArg ULift.down h

#print axioms scriptEvidence

open WindowChargeInverse WindowSeamCodes
open scoped BigOperators

/-- The observed function is the source equality on scalar data. -/
@[reducible] def rowEqualitySignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def rowEqualityActual : Realization rowEqualitySignature :=
  realize rowEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def rowEqualityRejected : Realization rowEqualitySignature :=
  realize rowEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Actual readout dependence does not assert physical interventions. -/
theorem rowEqualityDependence :
    ObservationalDependence rowEqualitySignature rowEqualityActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have atZero := congrFun h 0
  change ((0 : ZMod 2) = 0) = ((1 : ZMod 2) = 0) at atZero
  have impossible : (1 : ZMod 2) = 0 := atZero ▸ rfl
  exact one_ne_zero impossible

/-- All five conclusions and the original universe and dictionary remain in Law. -/
@[reducible] def donorRowsArena : Arena.{0,0,0,0,0} where
  signature := rowEqualitySignature
  Law R := ∀ {Y : Type u} [DecidableEq Y] (m d : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (i : Fin d),
    R.readout () () (actualRow table c i (m + 1)) 0 ∧
    (∑ h ∈ Finset.range (m + 1), actualRow table c i h) = 0 ∧
    (∀ j : ZMod (m + 2), wordIncrement (m + 1) (-j) (prefixWord m (actualRow table c i)) =
      windowCharge (m + 1) m (actualRow table c i) j) ∧
    (prefixWord m (actualRow table c i) ⟨0, by omega⟩ = false ↔ actualRow table c i 0 = 0) ∧
    (prefixWord m (actualRow table c i) ⟨m - 1, by omega⟩ = false ↔ actualRow table c i m = 0)

theorem donorRowsPositive : donorRowsArena.{u}.Law rowEqualityActual := @donor_rows_inverse.{u}

theorem donorRowsNegative : ¬ donorRowsArena.{u}.Law rowEqualityRejected := by
  intro law
  let table : Fin (3 + 1) → ULift.{u} Unit := fun _ => ⟨()⟩
  let c : Label table → Word 2 := fun _ => ∅
  have unary : ∀ i : Fin 2, i ∉ c ((sourceClauses table 2 (by decide)).unary i) := by
    intro i
    simp [c]
  exact (law 3 2 (by decide) table (by decide) c unary 0).1

def donorRowsEvidence : Registration donorRowsArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.donor_rows_inverse.{u})) where
  actual := rowEqualityActual
  bridge := Iff.rfl
  variation := ⟨donorRowsPositive, rowEqualityRejected, donorRowsNegative⟩
  sensitivity := ⟨fun i => ⟨rowEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, donorRowsNegative⟩,
    fun i => nomatch i⟩
  dependence := rowEqualityDependence

noncomputable def donorRowsRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.donor_rows_inverse.{u})
      (type_of% (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.donor_rows_inverse
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder/donorRowsArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.donorRowsEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨donorRowsArena.{u}⟩, objectArena := .source ⟨donorRowsArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source donorRowsArena.{u} ⟨donorRowsEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

@[reducible] def regularRowsArena : Arena.{0,0,0,0,0} where
  signature := rowEqualitySignature
  Law R := ∀ {Y : Type u} [DecidableEq Y] (m d : ℕ) (hm : 3 ≤ m) (hd : 2 ≤ d)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d)
    (regular : ∀ L, c L ∈ codeList (sourceClauses table d fit) (by omega) L),
    R.readout () () (actualRow table c (first (by omega)) 0) 0 ∧ safeRows m (actualRows table c)

theorem regularRowsPositive : regularRowsArena.{u}.Law rowEqualityActual := @regular_rows_safe.{u}

theorem regularRowsNegative : ¬ regularRowsArena.{u}.Law rowEqualityRejected := by
  intro law
  let table : Fin (3 + 1) → ULift.{u} Unit := fun _ => ⟨()⟩
  let c : Label table → Word 2 := fun _ => ∅
  have regular : ∀ L, c L ∈ codeList (sourceClauses table 2 (by decide)) (by decide) L := by
    intro L
    simp [c, codeList, forbidden, pairEnds]
  exact (law 3 2 (by decide) (by decide) table (by decide) c regular).1

def regularRowsEvidence : Registration regularRowsArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.regular_rows_safe.{u})) where
  actual := rowEqualityActual
  bridge := Iff.rfl
  variation := ⟨regularRowsPositive, rowEqualityRejected, regularRowsNegative⟩
  sensitivity := ⟨fun i => ⟨rowEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, regularRowsNegative⟩,
    fun i => nomatch i⟩
  dependence := rowEqualityDependence

noncomputable def regularRowsRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.regular_rows_safe.{u})
      (type_of% (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.regular_rows_safe
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder/regularRowsArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.regularRowsEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨regularRowsArena.{u}⟩, objectArena := .source ⟨regularRowsArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source regularRowsArena.{u} ⟨regularRowsEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

@[reducible] def issuedPhaseArena : Arena.{0,0,0,0,0} where
  signature := rowEqualitySignature
  Law R := ∀ {Y : Type u} [DecidableEq Y] (m d a : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (i : Fin d) (v : Fin (m + 1)),
    R.readout () () (wordIncrement (m + 1)
      (-(((a * m : ℕ) : ZMod (m + 2)) + (v.val : ℕ)) +
        (((a + i.val + 1) * m : ℕ) : ZMod (m + 2)))
      (prefixWord m (actualRow table c i))) (vertexBit table c i v)

theorem issuedPhasePositive : issuedPhaseArena.{u}.Law rowEqualityActual := @issued_phase_code.{u}

theorem issuedPhaseNegative : ¬ issuedPhaseArena.{u}.Law rowEqualityRejected := by
  intro law
  let table : Fin (3 + 1) → ULift.{u} Unit := fun _ => ⟨()⟩
  let c : Label table → Word 2 := fun _ => ∅
  have unary : ∀ i : Fin 2, i ∉ c ((sourceClauses table 2 (by decide)).unary i) := by
    intro i
    simp [c]
  exact law 3 2 0 (by decide) table (by decide) c unary 0 0

def issuedPhaseEvidence : Registration issuedPhaseArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.issued_phase_code.{u})) where
  actual := rowEqualityActual
  bridge := Iff.rfl
  variation := ⟨issuedPhasePositive, rowEqualityRejected, issuedPhaseNegative⟩
  sensitivity := ⟨fun i => ⟨rowEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, issuedPhaseNegative⟩,
    fun i => nomatch i⟩
  dependence := rowEqualityDependence

noncomputable def issuedPhaseRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.issued_phase_code.{u})
      (type_of% (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.issued_phase_code
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder/issuedPhaseArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.issuedPhaseEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨issuedPhaseArena.{u}⟩, objectArena := .source ⟨issuedPhaseArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source issuedPhaseArena.{u} ⟨issuedPhaseEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

/-- All six exceptional row coordinates remain in the complete source Law. -/
@[reducible] def exceptionalRowsArena : Arena.{0,0,0,0,0} where
  signature := rowEqualitySignature
  Law R := ∀ {Y : Type u} [DecidableEq Y] (m : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 4 ≤ m + 1)
    (c : Label table → Word 2)
    (codes : ∀ i : Fin 4, c (fourOwners (sourceClauses table 2 fit) i) = fourWords i),
    R.readout () () (actualRow table c 0 0) 0 ∧ actualRow table c 0 m = 1 ∧
    actualRow table c 0 (m - 1) = 1 ∧
    actualRow table c 1 0 = 1 ∧ actualRow table c 1 1 = 0 ∧ actualRow table c 1 2 = 1

theorem exceptionalRowsPositive : exceptionalRowsArena.{u}.Law rowEqualityActual :=
  @exceptional_row_coordinates.{u}

theorem exceptionalRowsNegative : ¬ exceptionalRowsArena.{u}.Law rowEqualityRejected := by
  intro law
  let table : Fin (3 + 1) → ULift.{u} (Fin 4) := fun v => ⟨v⟩
  let c : Label table → Word 2 := fun L => ![{0}, {0, 1}, ∅, {1}] L.val.down
  have codes : ∀ i : Fin 4,
      c (fourOwners (sourceClauses table 2 (by decide)) i) = fourWords i := by
    intro i
    fin_cases i <;> rfl
  exact (law 3 (by decide) table (by decide) c codes).1

def exceptionalRowsEvidence : Registration exceptionalRowsArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.exceptional_row_coordinates.{u})) where
  actual := rowEqualityActual
  bridge := Iff.rfl
  variation := ⟨exceptionalRowsPositive, rowEqualityRejected, exceptionalRowsNegative⟩
  sensitivity := ⟨fun i => ⟨rowEqualityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, exceptionalRowsNegative⟩,
    fun i => nomatch i⟩
  dependence := rowEqualityDependence

noncomputable def exceptionalRowsRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.exceptional_row_coordinates.{u})
      (type_of% (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.exceptional_row_coordinates
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder/exceptionalRowsArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.exceptionalRowsEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨exceptionalRowsArena.{u}⟩, objectArena := .source ⟨exceptionalRowsArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source exceptionalRowsArena.{u} ⟨exceptionalRowsEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize rowEqualitySignature rowEqualityActual.readout rowEqualityActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms donorRowsEvidence
#print axioms donorRowsRegistration
#print axioms regularRowsEvidence
#print axioms regularRowsRegistration
#print axioms issuedPhaseEvidence
#print axioms issuedPhaseRegistration
#print axioms exceptionalRowsEvidence
#print axioms exceptionalRowsRegistration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder
