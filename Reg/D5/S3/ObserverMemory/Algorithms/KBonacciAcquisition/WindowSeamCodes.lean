import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes
import Reg.Support.DependentFamily

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u_1

@[reducible] def cardinalitySignature : Signature where
  Params := Type u_1
  State Y := Finset Y
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def cardinalityActual : Realization cardinalitySignature.{u_1} :=
  realize cardinalitySignature (fun _ _ S => S.card) (fun e => nomatch e)

def cardinalityRejected : Realization cardinalitySignature.{u_1} :=
  realize cardinalitySignature (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def cardinalityArena : Arena where
  signature := cardinalitySignature.{u_1}
  Law R := ∀ {d : ℕ} {Y : Type u_1} [DecidableEq Y] [Fintype Y]
    (C : Clauses d Y) (hd : 2 ≤ d) (capacity : Fintype.card Y ≤ 2 ^ d)
    (regular : 3 ≤ d ∨ (owners C (by omega)).card ≤ 3 ∨ Fintype.card Y ≤ 3)
    (S : Finset Y), R.readout () Y S ≤ (S.biUnion (codeList C (by omega))).card

theorem cardinalityRejectedLaw : ¬ cardinalityArena.{u_1}.Law cardinalityRejected := by
  intro h
  let C : Clauses 2 (ULift.{u_1} Unit) := ⟨fun _ => ⟨()⟩, ⟨()⟩, fun _ => ⟨()⟩⟩
  have hh := h C (by decide) (by simp) (Or.inr (Or.inr (by simp))) ∅
  simp [cardinalityRejected, realize] at hh

def cardinalityRegistration : Registration cardinalityArena.{u_1}
    (cardinalityArena.{u_1}.Law cardinalityActual) where
  actual := cardinalityActual
  bridge := Iff.rfl
  variation := ⟨list_union_inequalities, cardinalityRejected, cardinalityRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨cardinalityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cardinalityRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨ULift.{u_1} Unit, ∅, {ULift.up ()}, ?_⟩
    simp [cardinalityActual, realize]

@[reducible] def unarySignature : Signature where
  Params := Σ d : ℕ, Σ _Y : Type u_1, Fin d
  State p := Clauses p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def unaryActual : Realization unarySignature.{u_1} :=
  realize unarySignature (fun _ p C => C.unary p.2.2) (fun e => nomatch e)

def unaryRejected : Realization unarySignature.{u_1} :=
  realize unarySignature (fun _ _ C => C.extra) (fun e => nomatch e)

@[reducible] def unaryArena : Arena where
  signature := unarySignature.{u_1}
  Law R := ∀ {d : ℕ} {Y : Type u_1} [DecidableEq Y]
    (C : Clauses d Y) (hd : 0 < d) (L : Y) (w : Word d),
    w ∈ codeList C hd L ↔
      (∀ i : Fin d, R.readout () ⟨d, Y, i⟩ C = L → i ∉ w) ∧
      (C.extra = L → first hd ∉ w) ∧
      (∀ i : Fin d, 0 < i.val → C.pair i = L → i ∉ w ∨ prev i ∉ w)

theorem unaryRejectedLaw : ¬ unaryArena.{u_1}.Law unaryRejected := by
  intro h
  let F : ULift.{u_1} Bool := ⟨false⟩
  let T : ULift.{u_1} Bool := ⟨true⟩
  let C : Clauses 2 (ULift.{u_1} Bool) :=
    ⟨fun i => if i = 0 then F else T, T, fun _ => T⟩
  have hh := h C (by decide) F {0}
  have lawful := hh.mpr (by simp [unaryRejected, realize, C, F, T])
  have impossible := ((mem_codeList_iff C (by decide) F {0}).mp lawful).1 0
    (by simp [C])
  simp at impossible

def unaryRegistration : Registration unaryArena.{u_1} (unaryArena.{u_1}.Law unaryActual) where
  actual := unaryActual
  bridge := Iff.rfl
  variation := ⟨mem_codeList_iff, unaryRejected, unaryRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨unaryRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, unaryRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, ULift.{u_1} Bool, 0⟩,
      ⟨fun _ => ⟨false⟩, ⟨false⟩, fun _ => ⟨false⟩⟩,
      ⟨fun _ => ⟨true⟩, ⟨false⟩, fun _ => ⟨false⟩⟩, ?_⟩
    simp [unaryActual, realize]

@[reducible] def seamSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := ZMod (m + 2)
  Anchor := Empty
  finiteAnchor := inferInstance

def seamActual : Realization seamSignature :=
  realize seamSignature (fun _ m n => ((n * m + m : ℕ) : ZMod (m + 2)))
    (fun e => nomatch e)

def seamRejected : Realization seamSignature :=
  realize seamSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem seamDependence : ObservationalDependence seamSignature seamActual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  change (3 : ZMod 5) ≠ 6
  decide

@[reducible] def windowArena : Arena where
  signature := seamSignature
  Law R := ∀ (m d : ℕ) (fit : 2 * d ≤ m + 1) (i : Fin d),
    (∀ j : ZMod (m + 2), j ∈ sourceWindow m (i.val + 1) ↔
      j ≠ ((missedVertex m d fit i).val : ZMod (m + 2))) ∧
    ((m + 1 : ℕ) : ZMod (m + 2)) ∈ sourceWindow m (i.val + 1) ∧
    (((i.val + 1) * m : ℕ) : ZMod (m + 2)) =
      ((seamVertex m d fit i).val : ZMod (m + 2)) ∧
    R.readout () m i.val = ((seamVertex m d fit i).val : ZMod (m + 2))

theorem windowRejectedLaw : ¬ windowArena.Law seamRejected := by
  intro h
  have hh := (h 3 1 (by decide) 0).2.2.2
  change (0 : ZMod 5) = 3 at hh
  exact (by decide : (0 : ZMod 5) ≠ 3) hh

def windowRegistration : Registration windowArena (windowArena.Law seamActual) where
  actual := seamActual
  bridge := Iff.rfl
  variation := ⟨source_window_vertices, seamRejected, windowRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨seamRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, windowRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := seamDependence

@[reducible] def tableArena : Arena where
  signature := seamSignature
  Law R := ∀ {Y : Type u_1} [DecidableEq Y] {m : ℕ} (table : Fin (m + 1) → Y)
    (hm : Odd m) (hn : 3 ≤ (labels table).card),
    let d := Nat.clog 2 (labels table).card
    ∃ (fit : 2 * d ≤ m + 1) (hd : 2 ≤ d) (c : Label table → Word d),
      Function.Injective c ∧ Function.Injective (fun L => wordBits (c L)) ∧
      Selection (sourceClauses table d fit) (by omega) c ∧
      (∀ i : Fin d, i ∉ c ((sourceClauses table d fit).unary i)) ∧
      first (by omega) ∉ c (sourceClauses table d fit).extra ∧
      (∀ i : Fin d, ∀ j : ZMod (m + 2),
        j ∈ sourceWindow m (i.val + 1) ↔
        j ≠ ((missedVertex m d fit i).val : ZMod (m + 2))) ∧
      (∀ i : Fin d, ((m + 1 : ℕ) : ZMod (m + 2)) ∈ sourceWindow m (i.val + 1)) ∧
      (∀ i : Fin d, (((i.val + 1) * m : ℕ) : ZMod (m + 2)) =
        ((seamVertex m d fit i).val : ZMod (m + 2))) ∧
      (∀ i : Fin d, R.readout () m i.val =
        ((seamVertex m d fit i).val : ZMod (m + 2)))

theorem tableRejectedLaw : ¬ tableArena.{u_1}.Law seamRejected := by
  intro h
  let table : Fin 4 → ULift.{u_1} (Fin 4) := ULift.up
  have cardinality : (labels table).card = 4 := by
    simp [labels, table, card_image_of_injective _ ULift.up_injective]
  obtain ⟨fit, hd, c, _, _, _, _, _, _, _, _, last⟩ :=
    h table (by decide) (by omega)
  have hh := last ⟨0, by omega⟩
  change (0 : ZMod 5) = 3 at hh
  exact (by decide : (0 : ZMod 5) ≠ 3) hh

def tableRegistration : Registration tableArena.{u_1} (tableArena.{u_1}.Law seamActual) where
  actual := seamActual
  bridge := Iff.rfl
  variation := ⟨actual_table_codes, seamRejected, tableRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨seamRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, tableRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := seamDependence


noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.list_union_inequalities.{u_1}) (type_of% (realize cardinalitySignature.{u_1} cardinalityActual.{u_1}.readout cardinalityActual.{u_1}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.list_union_inequalities
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.cardinalityArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.cardinalityRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨cardinalityArena⟩,
  objectArena := .source ⟨cardinalityArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source cardinalityArena ⟨cardinalityRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize cardinalitySignature.{u_1} cardinalityActual.{u_1}.readout cardinalityActual.{u_1}.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes,
    definition := none,
    coordinates := #[1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.mem_codeList_iff.{u_1}) (type_of% (realize unarySignature.{u_1} unaryActual.{u_1}.readout unaryActual.{u_1}.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.mem_codeList_iff
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.unaryArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.unaryRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨unaryArena⟩,
  objectArena := .source ⟨unaryArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source unaryArena ⟨unaryRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize unarySignature.{u_1} unaryActual.{u_1}.readout unaryActual.{u_1}.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes,
    definition := none,
    coordinates := #[0, 1, 7], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "domain", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.source_window_vertices) (type_of% (realize seamSignature (fun _ m n => ((n * m + m : ℕ) : ZMod (m + 2))) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.source_window_vertices
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.windowArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.windowRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨windowArena⟩,
  objectArena := .source ⟨windowArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source windowArena ⟨windowRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize seamSignature (fun _ m n => ((n * m + m : ℕ) : ZMod (m + 2))) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes,
    definition := none,
    coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "fn", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.actual_table_codes.{u_1}) (type_of% (realize seamSignature (fun _ m n => ((n * m + m : ℕ) : ZMod (m + 2))) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.actual_table_codes
    "Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes/Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.tableArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes.tableRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨tableArena⟩,
  objectArena := .source ⟨tableArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source tableArena ⟨tableRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize seamSignature (fun _ m n => ((n * m + m : ℕ) : ZMod (m + 2))) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes,
    definition := none,
    coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "fn", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms cardinalityRegistration
#print axioms unaryRegistration
#print axioms windowRegistration
#print axioms tableRegistration

end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes
