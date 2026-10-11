import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder
import Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalAcquiredTrace
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

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

@[reducible] def finalScriptLengthSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Nat (NarrowWindowCost.Archive) (fun _ => Nat)

def finalScriptLengthActual : Realization finalScriptLengthSignature :=
  realize finalScriptLengthSignature (fun _ _ issued => issued.length) (fun e => nomatch e)

def finalScriptLengthRejected : Realization finalScriptLengthSignature :=
  realize finalScriptLengthSignature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original script Law observes only the issued archive length. -/
@[reducible] def finalScriptLengthArena : Arena.{0,0,0,0,0} where
  signature := finalScriptLengthSignature
  Law R := ∀ {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (words : List (Fin m → Bool)) (decode : NarrowWindowCost.Archive m → Y)
    (w : List Bool) (free : Option (ZMod 2)) (base : NarrowWindowCost.Archive m),
    let issued := scriptArchive words (OriginalRecord k (by omega) w)
    PaidTrace (finalSelector base.length words decode) free
      (OriginalRecord k (by omega) w) base issued (decode issued) ∧
    issued.map Prod.fst = words ∧ R.readout () m issued = words.length ∧
    NarrowWindowCost.execute k (by omega) (finalSelector base.length words decode)
      words.length w free base = some (decode issued, words.length)

theorem finalScriptLengthPositive : finalScriptLengthArena.{u}.Law finalScriptLengthActual :=
  scriptEvidence.{u}.bridge.mpr scriptEvidence.{u}.variation.1

theorem finalScriptLengthNegative : ¬ finalScriptLengthArena.{u}.Law finalScriptLengthRejected := by
  intro law
  let label : ULift.{u} Unit := ⟨()⟩
  have impossible := (law 3 1 (by decide) [] (fun _ => label) [] (some 0) []).2.2.1
  change (1 : ℕ) = 0 at impossible
  cases impossible

theorem finalScriptLengthDependence :
    ObservationalDependence finalScriptLengthSignature finalScriptLengthActual := by
  intro i
  refine ⟨3, [], [(fun (_ : Fin 3) => false, none)], ?_⟩
  change (0 : ℕ) ≠ 1
  decide

def finalScriptLengthEvidence : Registration finalScriptLengthArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_final_script.{u})) where
  actual := finalScriptLengthActual
  bridge := Iff.rfl
  variation := ⟨finalScriptLengthPositive, finalScriptLengthRejected, finalScriptLengthNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    (P := Nat) (X := NarrowWindowCost.Archive) (Y := fun _ => Nat)
    finalScriptLengthArena.{u}.Law finalScriptLengthActual finalScriptLengthRejected finalScriptLengthNegative
  dependence := finalScriptLengthDependence

noncomputable def finalScriptLengthRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_final_script.{u})
      (type_of% (realize finalScriptLengthSignature finalScriptLengthActual.readout finalScriptLengthActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_final_script
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder/finalScriptLengthArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.finalScriptLengthEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨finalScriptLengthArena.{u}⟩, objectArena := .source ⟨finalScriptLengthArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source finalScriptLengthArena.{u} ⟨finalScriptLengthEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize finalScriptLengthSignature finalScriptLengthActual.readout finalScriptLengthActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms finalScriptLengthEvidence
#print axioms finalScriptLengthRegistration

@[reducible] def endpointLengthSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Nat (fun m => List (Fin m → Bool)) (fun _ => Nat)

def endpointLengthActual : Realization endpointLengthSignature :=
  realize endpointLengthSignature (fun _ _ words => words.length) (fun e => nomatch e)

def endpointLengthRejected : Realization endpointLengthSignature :=
  realize endpointLengthSignature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete endpoint Law keeps selection, survival and the endpoint vector. -/
@[reducible] def endpointLengthArena : Arena.{0,0,0,0,0} where
  signature := endpointLengthSignature
  Law R := ∀ {Y : Type u} [instDecidableEq : DecidableEq Y] (m d : ℕ) (hm : 3 ≤ m) (odd : Odd m) (hd : 2 ≤ d)
    (table : Fin (m + 1) → Y) (fit : 2 * d ≤ m + 1)
    (c : Label table → Word d) (selected : Selection (sourceClauses table d fit) (by omega) c)
    (unary : ∀ i, i ∉ c ((sourceClauses table d fit).unary i))
    (v : ZMod 2) (x : Fin (m + 1)) (alphabet : Bool),
    let q : Option (LiveRecord (m + 1)) := some ⟨v, -(x.val : ZMod (m + 2)) + (m : ℕ), 1⟩
    let issued := scriptArchive (actualWords table c) q
    R.readout () m (actualWords table c) = d ∧ none ∉ issued.map Prod.snd ∧
    endpointDifferences (some v) (issued.map Prod.snd) =
      List.ofFn (fun i : Fin d => some (vertexBit table c i x))

theorem endpointLengthPositive : endpointLengthArena.{u}.Law endpointLengthActual :=
  @physical_endpoint_codes.{u}

theorem endpointLengthNegative : ¬ endpointLengthArena.{u}.Law endpointLengthRejected := by
  intro law
  let table : Fin (3 + 1) → ULift.{u} Unit := fun _ => ⟨()⟩
  let c : Label table → Word 2 := fun _ => ∅
  have unary : ∀ i : Fin 2, i ∉ c ((sourceClauses table 2 (by decide)).unary i) := by
    intro i
    exact Finset.notMem_empty i
  have regular : ∀ L, c L ∈ codeList (sourceClauses table 2 (by decide)) (by decide) L := by
    intro L
    apply (mem_codeList_iff (sourceClauses table 2 (by decide)) (by decide) L (c L)).mpr
    exact ⟨fun i _ => Finset.notMem_empty i,
      fun _ => Finset.notMem_empty _, fun i _ _ => Or.inl (Finset.notMem_empty i)⟩
  have selected : Selection (sourceClauses table 2 (by decide)) (by decide) c := Or.inl regular
  have impossible := (law 3 2 (by decide) ⟨1, rfl⟩ (by decide) table (by decide)
    c selected unary 0 0 false).1
  change (1 : ℕ) = 2 at impossible
  cases impossible

theorem endpointLengthDependence :
    ObservationalDependence endpointLengthSignature endpointLengthActual := by
  intro i
  refine ⟨3, [], [fun (_ : Fin 3) => false], ?_⟩
  change (0 : ℕ) ≠ 1
  decide

def endpointLengthEvidence : Registration endpointLengthArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.physical_endpoint_codes.{u})) where
  actual := endpointLengthActual
  bridge := Iff.rfl
  variation := ⟨endpointLengthPositive, endpointLengthRejected, endpointLengthNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    (P := Nat) (X := fun m => List (Fin m → Bool)) (Y := fun _ => Nat)
    endpointLengthArena.{u}.Law endpointLengthActual endpointLengthRejected endpointLengthNegative
  dependence := endpointLengthDependence

noncomputable def endpointLengthRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.physical_endpoint_codes.{u})
      (type_of% (realize endpointLengthSignature endpointLengthActual.readout endpointLengthActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.physical_endpoint_codes
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder/endpointLengthArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.endpointLengthEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨endpointLengthArena.{u}⟩, objectArena := .source ⟨endpointLengthArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source endpointLengthArena.{u} ⟨endpointLengthEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize endpointLengthSignature endpointLengthActual.readout endpointLengthActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms endpointLengthEvidence
#print axioms endpointLengthRegistration

@[reducible] def literalEqualitySignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Bool) (fun _ => Bool → Prop)

def literalEqualityActual : Realization literalEqualitySignature :=
  realize literalEqualitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def literalEqualityRejected : Realization literalEqualitySignature :=
  realize literalEqualitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The complete literal execution Law keeps both words and both execution equalities. -/
@[reducible] def literalEqualityArena : Arena.{0,0,0,0,0} where
  signature := literalEqualitySignature
  Law R := ∀ {Y : Type u} [instDecidableEq : DecidableEq Y] (m : ℕ) (hm : 3 ≤ m)
    (table : Fin (m + 1) → Y) (fit : 4 ≤ m + 1)
    (c : Label table → Word 2)
    (unary : ∀ i, i ∉ c ((sourceClauses table 2 fit).unary i))
    (codes : ∀ i : Fin 4, c (fourOwners (sourceClauses table 2 fit) i) = fourWords i)
    (v : ZMod 2) (phase : ZMod (m + 2)) (s : ℕ) (hs : s < m + 1),
    let w₀ := prefixWord m (actualRow table c 0)
    let w₁ := prefixWord m (actualRow table c 1)
    R.readout () () (w₀ ⟨0, by omega⟩) false ∧ w₀ ⟨m - 2, by omega⟩ = false ∧
    w₀ ⟨m - 1, by omega⟩ = true ∧ tailAfter s w₀ = 1 ∧
    w₁ ⟨0, by omega⟩ = true ∧ w₁ ⟨1, by omega⟩ = true ∧
    w₁ ⟨2, by omega⟩ = false ∧ 1 + 2 < m + 1 ∧
    runBits (m + 1) w₀ (some ⟨v, phase, s⟩) =
      some ⟨v + wordIncrement (m + 1) phase w₀, phase + (m : ℕ), 1⟩ ∧
    runBits (m + 1) w₁
      (some ⟨v + wordIncrement (m + 1) phase w₀, phase + (m : ℕ), 1⟩) =
      some ⟨v + wordIncrement (m + 1) phase w₀ +
        wordIncrement (m + 1) (phase + (m : ℕ)) w₁,
        phase + (m : ℕ) + (m : ℕ), tailAfter 0 w₁⟩

theorem literalEqualityPositive : literalEqualityArena.{u}.Law literalEqualityActual :=
  @exceptional_literal_execution.{u}

theorem literalEqualityNegative : ¬ literalEqualityArena.{u}.Law literalEqualityRejected := by
  intro law
  let table : Fin (3 + 1) → ULift.{u} (Fin 4) := fun v => ⟨v⟩
  let c : Label table → Word 2 := fun L => ![{0}, {0, 1}, ∅, {1}] L.val.down
  have unary : ∀ i : Fin 2, i ∉ c ((sourceClauses table 2 (by decide)).unary i) := by
    intro i
    fin_cases i
    · change (0 : Fin 2) ∉ (∅ : Word 2)
      exact Finset.notMem_empty _
    · change (1 : Fin 2) ∉ ({0} : Word 2)
      decide
  have codes : ∀ i : Fin 4,
      c (fourOwners (sourceClauses table 2 (by decide)) i) = fourWords i := by
    intro i
    fin_cases i <;> rfl
  exact (law 3 (by decide) table (by decide) c unary codes 0 0 0 (by decide)).1

theorem literalEqualityDependence :
    ObservationalDependence literalEqualitySignature literalEqualityActual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  intro h
  have atFalse := congrFun h false
  change (false = false) = (true = false) at atFalse
  have impossible : true = false := atFalse ▸ rfl
  cases impossible

def literalEqualityEvidence : Registration literalEqualityArena.{u}
    (type_of% (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.exceptional_literal_execution.{u})) where
  actual := literalEqualityActual
  bridge := Iff.rfl
  variation := ⟨literalEqualityPositive, literalEqualityRejected, literalEqualityNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    (P := Unit) (X := fun _ => Bool) (Y := fun _ => Bool → Prop)
    literalEqualityArena.{u}.Law literalEqualityActual literalEqualityRejected literalEqualityNegative
  dependence := literalEqualityDependence

noncomputable def literalEqualityRegistration :
    LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.exceptional_literal_execution.{u})
      (type_of% (realize literalEqualitySignature literalEqualityActual.readout literalEqualityActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.exceptional_literal_execution
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder/literalEqualityArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.literalEqualityEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨literalEqualityArena.{u}⟩, objectArena := .source ⟨literalEqualityArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source literalEqualityArena.{u} ⟨literalEqualityEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize literalEqualitySignature literalEqualityActual.readout literalEqualityActual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms literalEqualityEvidence
#print axioms literalEqualityRegistration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse WindowSeamCodes OriginalNarrowCost OriginalAcquiredTrace PhysicalWindowDecoder
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.InitialDecoderAudit

abbrev signature : Signature where
  Params := Σ Y : Type u, ℕ
  State p := NarrowWindowCost.Selector p.2 p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := NarrowWindowCost.Selector p.2 p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ π => π) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ p _ _ _ => Sum.inr (fun _ : Fin p.2 => false)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Y : Type u} [DecidableEq Y] (m : ℕ) (hm : 3 ≤ m) (odd : Odd m)
        (alphabet : Bool) (free previous : ZMod 2) (archive : NarrowWindowCost.Archive m)
        (parent : Fin m → Bool)
        (prior : archiveEndpoint (some free) archive = some previous)
        (full : initialSupport (m + 1) m (by omega) alphabet free
          (archive ++ [(parent, some (previous + 1))]) = physicalWindow (m + 1) m archive.length)
        (f : Option (LiveRecord (m + 1)) → Y) (initialLabels : ZMod (m + 2) → Y)
        (wellDefined : ∀ initial current : LiveRecord (m + 1),
          (some initial, some current) ∈ AcquiredPairs (m + 1) m (by omega) alphabet (some free)
            (archive ++ [(parent, some (previous + 1))]) →
            f (some initial) = initialLabels (-initial.phase))
        (many : 3 ≤ (labels (fun x : Fin (m + 1) =>
          initialLabels (vertex (m + 1) m archive.length x.val))).card),
        let table := fun x : Fin (m + 1) => initialLabels (vertex (m + 1) m archive.length x.val)
        let d := Nat.clog 2 (labels table).card
        let acquired := archive ++ [(parent, some (previous + 1))]
        ∃ (c : Label table → Word d) (π : NarrowWindowCost.Selector m Y),
          Function.Injective c ∧
          (actualWords table c).length = d ∧
          (∀ y₀ ar B, π y₀ ar = .inr B → DBonacciAdmissible (m + 1) m B) ∧
          ∀ history : List (AllowedBlock (m + 1) m alphabet),
            let w := history.flatMap (fun action => List.ofFn action.val)
            NarrowWindowCost.output (m + 1) (by omega) w = some free →
            ActualArchive (m + 1) (by omega) w acquired →
            let issued := scriptArchive (actualWords table c)
              (OriginalRecord (m + 1) (by omega) (w ++ archiveWords acquired))
            issued.map Prod.fst = actualWords table c ∧ issued.length = d ∧
            none ∉ issued.map Prod.snd ∧
            (∃ L : Label table, L.val = f (OriginalRecord (m + 1) (by omega) w) ∧
              endpointDifferences (some (previous + 1)) (issued.map Prod.snd) = codeVector c L) ∧
            PaidTrace π (some free)
              (OriginalRecord (m + 1) (by omega) (w ++ archiveWords acquired))
              acquired issued (f (OriginalRecord (m + 1) (by omega) w)) ∧
            NarrowWindowCost.execute (m + 1) (by omega) (R.readout () ⟨Y, m⟩ π) d (w ++ archiveWords acquired)
              (some free) acquired = some (f (OriginalRecord (m + 1) (by omega) w), d)


private theorem positive : arena.{u}.Law actual :=
  @original_physical_initial_decoder.{u}

private def parent : Fin 3 → Bool := fun i => decide (i.val % 2 = 0)

private def zeroBlock : AllowedBlock 4 3 false :=
  ⟨fun _ => false, by intro h; cases h⟩

private def history (n : ℕ) : List (AllowedBlock 4 3 false) :=
  List.replicate n zeroBlock

private def word (n : ℕ) : List Bool :=
  (history n).flatMap (fun action => List.ofFn action.val)

private def waits : Fin 4 → ℕ := ![0, 3, 1, 4]

private theorem witnessOutput (i : Fin 4) :
    NarrowWindowCost.output 4 (by decide) (word (waits i)) = some 0 := by
  fin_cases i <;> decide

private theorem witnessRecord (i : Fin 4) :
    OriginalRecord 4 (by decide) (word (waits i)) =
      some ⟨0, -(i.val : ZMod 5), 0⟩ := by
  fin_cases i <;> decide

private theorem witnessArchive (i : Fin 4) :
    ActualArchive 4 (by decide) (word (waits i)) [(parent, some (0 + 1))] := by
  constructor
  · rw [OriginalExecutionBridge.output_record,
      OriginalExecutionBridge.record_append 4 (by decide)]
    change endpointReading (runBits 4 parent
      (OriginalRecord 4 (by decide) (word (waits i)))) = some (0 + 1)
    rw [witnessRecord]
    fin_cases i <;> decide
  · trivial

private theorem fullSupport :
    initialSupport 4 3 (by decide) false 0 [(parent, some (0 + 1))] =
      physicalWindow 4 3 0 := by
  apply Set.Subset.antisymm
  · exact (actual_positive_coordinates 4 3 (by decide) (by decide)
      false 0 0 [] parent rfl).1
  · rintro j ⟨i, hi, rfl⟩
    let v : Fin 4 := ⟨i, by omega⟩
    refine ⟨⟨0, -(i : ZMod 5), 0⟩,
      OriginalRecord 4 (by decide)
        (word (waits v) ++ archiveWords [(parent, some (0 + 1))]), ?_, ?_⟩
    · exact ⟨history (waits v), witnessOutput v, witnessArchive v,
        (witnessRecord v).symm, rfl⟩
    · simp [vertex]

private theorem manyLabels :
    3 ≤ (labels (fun x : Fin (3 + 1) =>
      (ULift.up (vertex 4 3 0 x.val) : ULift.{u} (ZMod 5)))).card := by
  have injective : Function.Injective
      (fun x : Fin 4 => (ULift.up (vertex 4 3 0 x.val) : ULift.{u} (ZMod 5))) := by
    intro x y h
    have e := congrArg ULift.down h
    have finiteInjective : Function.Injective (fun x : Fin 4 => vertex 4 3 0 x.val) := by
      decide
    exact finiteInjective e
  simp only [labels, Finset.card_image_of_injective _ injective,
    Finset.card_univ, Fintype.card_fin]
  decide

private theorem rejectedExecute {Y : Type u} (m k : ℕ) (hk : 0 < k)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool)
    (free : Option (ZMod 2)) (ar : NarrowWindowCost.Archive m) :
    NarrowWindowCost.execute k hk (rejected.readout () ⟨Y, m⟩ π) d w free ar = none := by
  induction d generalizing w ar with
  | zero => rfl
  | succ d ih =>
    change Option.map _ (NarrowWindowCost.execute k hk
      (rejected.readout () ⟨Y, m⟩ π) d _ free _) = none
    rw [ih]
    rfl

private theorem negative : ¬ arena.{u}.Law rejected := by
  intro law
  let f : Option (LiveRecord 4) → ULift.{u} (ZMod 5) :=
    fun q => ⟨match q with | none => 0 | some q => -q.phase⟩
  obtain ⟨c, π, _, _, _, allHistories⟩ :=
    law 3 (by decide) (by decide) false 0 0 [] parent rfl fullSupport
      f ULift.up (by intro initial current member; rfl) manyLabels
  have run := (allHistories [] (witnessOutput 0) (witnessArchive 0)).2.2.2.2.2
  rw [rejectedExecute] at run
  cases run

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let π₀ : NarrowWindowCost.Selector 3 (ULift.{u} Unit) := fun _ _ => .inl ⟨()⟩
  let π₁ : NarrowWindowCost.Selector 3 (ULift.{u} Unit) := fun _ _ => .inr (fun _ => false)
  refine ⟨⟨ULift.{u} Unit, 3⟩, π₀, π₁, ?_⟩
  intro h
  have impossible := congrFun (congrFun h none) []
  cases impossible

def evidence : Registration arena.{u} (type_of%
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_physical_initial_decoder.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{u+1,0,1,0,0,0,u+1,u,0,u,0,0}
    (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_physical_initial_decoder.{u})
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.original_physical_initial_decoder
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.InitialDecoderAudit/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.InitialDecoderAudit.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.InitialDecoderAudit.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder,
    definition := none, coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn", "fn", "fn", "arg"],
      stateBinder := 20, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder.InitialDecoderAudit
end
