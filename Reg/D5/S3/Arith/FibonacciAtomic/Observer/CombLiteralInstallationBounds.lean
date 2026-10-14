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

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
