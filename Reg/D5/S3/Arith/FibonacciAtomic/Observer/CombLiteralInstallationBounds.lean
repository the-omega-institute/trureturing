import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount (Adm)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds

/-- The one-leaf, zero-entry task is inhabited by one query and two halts. -/
def small : Controller (Option Bool) where
  initial := none
  instruction e := match e with
    | none => .read [] (fun r => match r with
        | .alpha => some false
        | .beta => some true
        | _ => none)
    | some b => .stop b

private theorem small_terminal {u : Source} {t : Nat} {a b : Bool}
    {qs : List (Option Bool × Nat)} {updates : Nat} {f : Option Bool}
    (run : Run small u (some a) t qs updates f b) : b = a ∧ updates = 0 := by
  cases run with
  | halt row =>
    have eq : a = b := by simpa [small] using row
    exact ⟨eq.symm, rfl⟩
  | read row tail => simp [small] at row
  | update row tail => simp [small] at row
  | internal row tail => simp [small] at row

private theorem small_run {a b : Bool} {qs : List (Option Bool × Nat)}
    {updates : Nat} {f : Option Bool}
    (run : Run small (.of a) small.initial 0 qs updates f b) :
    b = !a ∧ updates = 0 := by
  cases run with
  | halt row => simp [small] at row
  | @read e f t p k qs updates b row tail =>
    have data : p = [] ∧ k = (fun r => match r with
      | .alpha => some false | .beta => some true | _ => none) := by
      simpa [small] using row.symm
    rcases data with ⟨rfl, rfl⟩
    cases a <;> exact small_terminal tail
  | update row tail => simp [small] at row
  | internal row tail => simp [small] at row

theorem small_correct : Correct small 1 0 := by
  intro u hu t ht
  have tz : t = 0 := by omega
  subst t
  cases u with
  | of a =>
    constructor
    · refine ⟨[(none,0)],0,some (!a),!a,?_⟩
      apply Run.read rfl
      cases a <;> exact Run.halt rfl
    · intro qs updates f b run
      exact (small_run run).1
  | mul u v =>
    have up := u.length_pos
    have vp := v.length_pos
    simp only [FreeMagma.length] at hu
    omega

theorem small_static : Static small 1 0 := by
  intro u hu t ht qs updates f b run
  have tz : t = 0 := by omega
  subst t
  cases u with
  | of a => exact (small_run run).2
  | mul u v =>
    have up := u.length_pos
    have vp := v.length_pos
    simp only [FreeMagma.length] at hu
    omega

theorem small_queries : (queries small).card = 1 := by
  classical
  have eq : queries small = {none} := by
    ext e
    simp only [queries, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    cases e with
    | none => simp [IsQuery, small]
    | some b => simp [IsQuery, small]
  simp [eq]

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def leafCount : Realization signature := realize signature (fun _ _ h => h) (fun e => nomatch e)
def coneCount : Realization signature := realize signature (fun _ _ h => 2 ^ (h - 1)) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev readArena : Arena where
  signature := signature
  Law R := ∀ {E : Type} {M : Controller E} {h T : Nat}, Correct M h T →
    ∀ {u : Source}, u.length = h → ∀ {t : Nat}, t ≤ T →
    ∀ {qs : List (E × Nat)} {updates : Nat} {f : E} {b : Bool},
    Run M u M.initial t qs updates f b → R.readout () () h ≤ qs.length

private theorem read_bad : ¬ readArena.Law bad := by
  intro law
  have run : Run small (.of true) small.initial 0 [(none,0)] 0 (some false) false :=
    Run.read rfl (Run.halt rfl)
  have no := law small_correct rfl (Nat.le_refl 0) run
  exact (by decide : ¬ (2 ≤ 1)) no

def readProof : Registration readArena (type_of% (@successful_run_read_lower_bound)) where
  actual := leafCount
  bridge := Iff.rfl
  variation := ⟨@successful_run_read_lower_bound, bad, read_bad⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, read_bad⟩, fun i => nomatch i⟩
  dependence := by intro i; exact ⟨(),0,1,by simp [leafCount, realize]⟩

abbrev installedArena : Arena where
  signature := signature
  Law R := ∀ {E : Type} [Fintype E] (M : Controller E) {h T : Nat},
    0 < h → Correct M h T →
    R.readout () () h ≤ (queries M).card ∧ 2 ≤ (halts M).card ∧
    2 ^ (h - 1) + 2 ≤ Fintype.card E ∧
    (∀ (width : Nat) (encode : E → {w : Fin width → Bool // Adm width w}),
      Function.Injective encode → 2 ^ (h - 1) + 2 ≤ Nat.fib (width + 2))

private theorem installed_bad : ¬ installedArena.Law bad := by
  intro law
  have no := (law small (by decide) small_correct).1
  change 2 ≤ (queries small).card at no
  rw [small_queries] at no
  omega

def installedProof : Registration installedArena (type_of% (@comb_installed_lower_bounds)) where
  actual := coneCount
  bridge := Iff.rfl
  variation := ⟨@comb_installed_lower_bounds, bad, installed_bad⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, installed_bad⟩, fun i => nomatch i⟩
  dependence := by intro i; exact ⟨(),1,2,by simp [coneCount, realize]⟩

abbrev staticArena : Arena where
  signature := signature
  Law R := ∀ {E : Type} [Fintype E] (M : Controller E) {h T : Nat},
    0 < h → Correct M h T → Static M h T →
    R.readout () () h * ((T + 3)/3) ≤ (queries M).card ∧ 2 ≤ (halts M).card ∧
    2 ^ (h - 1) * ((T + 3)/3) + 2 ≤ Fintype.card E ∧
    (∀ (width : Nat) (encode : E → {w : Fin width → Bool // Adm width w}),
      Function.Injective encode → 2 ^ (h - 1) * ((T + 3)/3) + 2 ≤ Nat.fib (width + 2))

private theorem static_bad : ¬ staticArena.Law bad := by
  intro law
  have no := (law small (by decide) small_correct small_static).1
  change 2 * ((0 + 3)/3) ≤ (queries small).card at no
  rw [small_queries] at no
  omega

def staticProof : Registration staticArena (type_of% (@static_comb_installed_lower_bounds)) where
  actual := coneCount
  bridge := Iff.rfl
  variation := ⟨@static_comb_installed_lower_bounds, bad, static_bad⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, static_bad⟩, fun i => nomatch i⟩
  dependence := by intro i; exact ⟨(),1,2,by simp [coneCount, realize]⟩

noncomputable def successful_run_read_lower_bound_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.successful_run_read_lower_bound)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.successful_run_read_lower_bound
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.readProof
  realizationSource := none
  generated := false
  arena := .source ⟨readArena⟩
  objectArena := .source ⟨readArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source readArena ⟨readProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature leafCount.readout leafCount.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def comb_installed_lower_bounds_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.comb_installed_lower_bounds)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.comb_installed_lower_bounds
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.installedProof
  realizationSource := none
  generated := false
  arena := .source ⟨installedArena⟩
  objectArena := .source ⟨installedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source installedArena ⟨installedProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature coneCount.readout coneCount.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def static_comb_installed_lower_bounds_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.static_comb_installed_lower_bounds)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.static_comb_installed_lower_bounds
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.staticProof
  realizationSource := none
  generated := false
  arena := .source ⟨staticArena⟩
  objectArena := .source ⟨staticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source staticArena ⟨staticProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature coneCount.readout coneCount.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


noncomputable section
attribute [local instance] Classical.propDecidable
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine (Op)

abbrev instructionSignature : Signature where
  Params := Σ E : Type, Controller E
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Op p.1 Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def instructionActual : Realization instructionSignature :=
  realize instructionSignature (fun _ p e => p.2.instruction e) (fun e => nomatch e)
def instructionBad : Realization instructionSignature :=
  realize instructionSignature (fun _ p _ => .localStep p.2.initial) (fun e => nomatch e)
abbrev haltArena : Arena where
  signature := instructionSignature
  Law R := ∀ {E : Type} {M : Controller E} {u : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b), R.readout () ⟨E,M⟩ f = .stop b
private theorem halt_bad : ¬ haltArena.Law instructionBad := by
  intro law
  let M : Controller Bool := ⟨false, fun _ => .stop false⟩
  have no := law (Run.halt rfl : Run M (.of true) false 0 [] 0 false false)
  change Op.localStep false = Op.stop false at no
  cases no

def haltEvidence : Registration haltArena (type_of% (@run_halt)) where
  actual := instructionActual
  bridge := Iff.rfl
  variation := ⟨@run_halt,instructionBad,halt_bad⟩
  sensitivity := ⟨fun i => ⟨instructionBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,halt_bad⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    let M : Controller Bool := ⟨false,fun b => .stop b⟩
    refine ⟨⟨Bool,M⟩,false,true,?_⟩
    change Op.stop false ≠ Op.stop true
    intro h
    cases h

abbrev querySignature : Signature where
  Params := Σ E : Type, Controller E
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def queryActual : Realization querySignature :=
  realize querySignature (fun _ p e => decide (IsQuery p.2 e)) (fun e => nomatch e)
def queryBad : Realization querySignature :=
  realize querySignature (fun _ _ _ => false) (fun e => nomatch e)
abbrev queryArena : Arena where
  signature := querySignature
  Law R := ∀ {E : Type} {M : Controller E} {u : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b), ∀ z ∈ qs, R.readout () ⟨E,M⟩ z.1 = true
private theorem query_bridge : (type_of% (@run_queries)) ↔ queryArena.Law queryActual := by
  constructor
  · intro th E M u e f t qs updates b run z hz
    exact decide_eq_true (th run z hz)
  · intro law E M u e f t qs updates b run z hz
    exact of_decide_eq_true (law run z hz)
private theorem query_bad : ¬ queryArena.Law queryBad := by
  intro law
  have run : Run small (.of true) none 0 [(none,0)] 0 (some false) false :=
    Run.read rfl (Run.halt rfl)
  have no := law run (none,0) (by simp)
  change false = true at no
  cases no

def queryEvidence : Registration queryArena (type_of% (@run_queries)) where
  actual := queryActual
  bridge := query_bridge
  variation := ⟨query_bridge.mp (@run_queries),queryBad,query_bad⟩
  sensitivity := ⟨fun i => ⟨queryBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,query_bad⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    let M : Controller Bool := ⟨false,fun b => if b then .stop true else .read [] (fun _ => false)⟩
    refine ⟨⟨Bool,M⟩,false,true,?_⟩
    simp [queryActual,realize,IsQuery,M]

abbrev literalSignature : Signature where
  Params := Σ E : Type, Controller E
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Address
  Anchor := Empty
  finiteAnchor := inferInstance

def literalActual : Realization literalSignature :=
  realize literalSignature (fun _ p e => literal p.2 e) (fun e => nomatch e)
def literalBad : Realization literalSignature :=
  realize literalSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev replayArena : Arena where
  signature := literalSignature
  Law R := ∀ {E : Type} {M : Controller E} {u v : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b)
    (agree : ∀ z ∈ qs, readout (R.readout () ⟨E,M⟩ z.1) (substitution^[z.2] u) =
      readout (literal M z.1) (substitution^[z.2] v)), Run M v e t qs updates f b
private theorem replay_bad : ¬ replayArena.Law literalBad := by
  intro law
  let M : Controller (Option Bool) := ⟨none,fun e => match e with
    | none => .read [false] (fun r => if r = .alpha then some false else some true)
    | some b => .stop b⟩
  let u : Source := .mul (.of true) (.of true)
  let v : Source := .mul (.mul (.of true) (.of true)) (.of true)
  have run : Run M u none 0 [(none,0)] 0 (some false) false :=
    Run.read rfl (Run.halt rfl)
  have replay : Run M v none 0 [(none,0)] 0 (some false) false := law run (by
    intro z hz
    have eq : z = (none,0) := by simpa using hz
    subst z
    rfl)
  cases replay with
  | @read e f t p k qs updates b row tail =>
    have data : p = [false] ∧ k = (fun r => if r = .alpha then some false else some true) := by
      simpa [M] using row.symm
    rcases data with ⟨rfl,rfl⟩
    cases tail with
    | internal row _ => simp [M,v,readout] at row
  | internal row _ => simp [M] at row

def replayEvidence : Registration replayArena (type_of% (@run_replay)) where
  actual := literalActual
  bridge := Iff.rfl
  variation := ⟨@run_replay,literalBad,replay_bad⟩
  sensitivity := ⟨fun i => ⟨literalBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,replay_bad⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    let M : Controller Bool := ⟨false,fun b => .read [b] (fun _ => b)⟩
    refine ⟨⟨Bool,M⟩,false,true,?_⟩
    change [false] ≠ [true]
    decide

abbrev queryCountSignature : Signature where
  Params := Type
  State E := Finset E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def queryCountActual : Realization queryCountSignature :=
  realize queryCountSignature (fun _ _ Q => Q.card) (fun e => nomatch e)
def queryCountBad : Realization queryCountSignature :=
  realize queryCountSignature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev queryHaltArena : Arena where
  signature := queryCountSignature
  Law R := ∀ {E : Type} [Fintype E] (M : Controller E),
    R.readout () E (queries M) + (halts M).card ≤ Fintype.card E
private theorem query_halt_bad : ¬ queryHaltArena.Law queryCountBad := by
  intro law
  have no := law (⟨(),fun _ => .stop false⟩ : Controller Unit)
  have impossible : 2 ≤ 1 := (Nat.le_add_right 2 _).trans no
  exact (by decide : ¬ (2 ≤ 1)) impossible

def queryHaltEvidence : Registration queryHaltArena (type_of% (@query_halt_card)) where
  actual := queryCountActual
  bridge := Iff.rfl
  variation := ⟨@query_halt_card,queryCountBad,query_halt_bad⟩
  sensitivity := ⟨fun i => ⟨queryCountBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,query_halt_bad⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨Unit,∅,{()},?_⟩
    change (∅ : Finset Unit).card ≠ ({()} : Finset Unit).card
    simp

abbrev weightSignature : Signature where
  Params := Unit
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ p => weight p) (fun e => nomatch e)
def weightBad : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev windowArena : Arena where
  signature := weightSignature
  Law R := ∀ (p : Address) (t : Nat)
    (different : readout p (atom t) ≠ readout p (atom (t+1))),
    R.readout () () p ≤ t+1 ∧ t ≤ weight p+1
private theorem window_bad : ¬ windowArena.Law weightBad := by
  intro law
  have no := (law [] 0 (by decide)).1
  exact (by decide : ¬ (2 ≤ 1)) no

def windowEvidence : Registration windowArena (type_of% (@adjacent_window)) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@adjacent_window,weightBad,window_bad⟩
  sensitivity := ⟨fun i => ⟨weightBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,window_bad⟩, fun e => nomatch e⟩
  dependence := by intro i; exact ⟨(),[],[false],by change (0 : Nat) ≠ 1; omega⟩

abbrev epochSignature : Signature where
  Params := Type
  State E := E × Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def epochActual : Realization epochSignature :=
  realize epochSignature (fun _ _ z => z.2) (fun e => nomatch e)
def epochBad : Realization epochSignature :=
  realize epochSignature (fun _ _ z => z.2+1) (fun e => nomatch e)
abbrev epochArena : Arena where
  signature := epochSignature
  Law R := ∀ {E : Type} {M : Controller E} {u : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b) (zero : updates = 0),
    ∀ z ∈ qs, R.readout () E z = t
private theorem epoch_bad : ¬ epochArena.Law epochBad := by
  intro law
  have run : Run small (.of true) none 0 [(none,0)] 0 (some false) false :=
    Run.read rfl (Run.halt rfl)
  have no := law run rfl (none,0) (by simp)
  exact Nat.one_ne_zero no

def epochEvidence : Registration epochArena (type_of% (@static_epochs)) where
  actual := epochActual
  bridge := Iff.rfl
  variation := ⟨@static_epochs,epochBad,epoch_bad⟩
  sensitivity := ⟨fun i => ⟨epochBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,epoch_bad⟩, fun e => nomatch e⟩
  dependence := by intro i; exact ⟨Unit,((),0),((),1),by change (0 : Nat) ≠ 1; omega⟩

noncomputable def run_halt_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.run_halt) (Realization instructionSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.run_halt.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.haltEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨haltArena⟩
  objectArena := .source ⟨haltArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source haltArena ⟨haltEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize instructionSignature instructionActual.readout instructionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def run_queries_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.run_queries) (Realization querySignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.run_queries.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.queryEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨queryArena⟩
  objectArena := .source ⟨queryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source queryArena ⟨queryEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize querySignature queryActual.readout queryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def run_replay_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.run_replay) (Realization literalSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.run_replay.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.replayEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨replayArena⟩
  objectArena := .source ⟨replayArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source replayArena ⟨replayEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize literalSignature literalActual.readout literalActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #[
        "body","body","body","body","body","body",
        "body","body","body","body","body","domain",
        "body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def query_halt_card_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.query_halt_card) (Realization queryCountSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.query_halt_card.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.queryHaltEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨queryHaltArena⟩
  objectArena := .source ⟨queryHaltArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source queryHaltArena ⟨queryHaltEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize queryCountSignature queryCountActual.readout queryCountActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def adjacent_window_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.adjacent_window) (Realization weightSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.adjacent_window.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.windowEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature weightActual.readout weightActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def static_epochs_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.static_epochs) (Realization epochSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.static_epochs.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.epochEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨epochArena⟩
  objectArena := .source ⟨epochArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source epochArena ⟨epochEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize epochSignature epochActual.readout epochActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
