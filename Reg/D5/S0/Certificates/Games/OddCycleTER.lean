import D5.S0.Certificates.Games.OddCycleTER
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound audit of the initial odd-cycle TERMINATE value. -/

open Finset LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

namespace OddCycleTER.Audit
noncomputable section

private abbrev signature : Signature where
  Params := ℕ
  State m := Finset (Vertex m)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev actual : Realization signature :=
  realize signature (fun _ m S => terNim (m := m) S) (fun e => nomatch e)

private abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ m : ℕ, 2 ≤ m → r.readout () m ∅ = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Nat.one_ne_zero (h 2 (by decide))

variable {m : ℕ}

private theorem mem_moves_selected {S T : Finset (Vertex m)} :
    Tᶜ ∈ moves Sᶜ ↔ geoHull Sᶜ = Set.univ ∧ ∃ x ∉ S, insert x S = T := by
  rw [OddCycleTER.mem_moves]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨x, mem_compl.mp hx, ?_⟩
    apply (compl_injective : Function.Injective (compl : Finset (Vertex m) → _))
    simpa only [compl_insert] using he
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_compl.mpr hx, (compl_insert (a := x) (s := S)).symm⟩

private theorem initial_option (v : Vertex 2) :
    ({v} : Finset (Vertex 2))ᶜ ∈ moves (∅ : Finset (Vertex 2))ᶜ := by
  have full : geoHull (∅ : Finset (Vertex 2))ᶜ = Set.univ := by
    ext z
    simp only [geoHull, compl_empty, coe_univ, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro K hK _
    exact hK trivial
  exact mem_moves_selected.mpr ⟨full, v, by simp, rfl⟩

private theorem readout_dependence : ObservationalDependence signature actual := by
  classical
  intro i
  let v : Vertex 2 := 0
  have different : terNim ({v} : Finset (Vertex 2)) ≠ 0 := by
    intro zero
    have noMex := (mex_spec ((moves (∅ : Finset (Vertex 2))ᶜ).image grundy)).1
    have start : mex ((moves (∅ : Finset (Vertex 2))ᶜ).image grundy) = 0 :=
      (OddCycleTER.grundy_eq _).symm.trans (conjecture_5_5 2 (by decide))
    exact noMex (mem_image.mpr ⟨_, initial_option v, zero.trans start.symm⟩)
  exact ⟨2, {v}, ∅, fun equal => different (equal.trans (conjecture_5_5 2 (by decide)))⟩

def evidence : Registration arena (type_of% @conjecture_5_5) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conjecture_5_5, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := readout_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@conjecture_5_5) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S0.Certificates.Games.OddCycleTER.unit
  realizationName := `OddCycleTER.Audit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m S => terNim (m := m) S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Games.OddCycleTER
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      booleanPredicate := false
      stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

private theorem moves_empty (m : ℕ) : moves (∅ : Finset (Vertex m)) = ∅ := by
  ext Q
  simp [OddCycleTER.mem_moves]

namespace MoveAudit

private abbrev moveSignature : Signature :=
  { signature with Output := fun _ m => Finset (Finset (Vertex m)) }

private abbrev moveActual : Realization moveSignature :=
  realize moveSignature (fun _ _ R => moves R) (fun e => nomatch e)

private abbrev moveRejected : Realization moveSignature :=
  realize moveSignature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev moveArena : Arena where
  signature := moveSignature
  Law r := ∀ {m : ℕ} {R Q : Finset (Vertex m)},
    Q ∈ r.readout () m R ↔ geoHull R = Set.univ ∧ ∃ x ∈ R, R.erase x = Q

private theorem move_rejected_law : ¬ moveArena.Law moveRejected := by
  intro h
  let v : Vertex 2 := 0
  exact notMem_empty _ ((@h 2 _ _).mpr (OddCycleTER.mem_moves.mp (initial_option v)))

def evidence : Registration moveArena (type_of% @OddCycleTER.mem_moves) where
  actual := moveActual
  bridge := Iff.rfl
  variation := ⟨@OddCycleTER.mem_moves, moveRejected, move_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨moveRejected, ?_, rfl, move_rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let v : Vertex 2 := 0
    refine ⟨2, ∅ᶜ, ∅, ?_⟩
    change moves (∅ : Finset (Vertex 2))ᶜ ≠ moves ∅
    rw [moves_empty]
    intro h
    exact notMem_empty _ (h ▸ initial_option v)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@OddCycleTER.mem_moves) (Realization moveSignature) Unit Unit := {
  unitName := `Reg.D5.S0.Certificates.Games.OddCycleTER.mem_moves_unit
  realizationName := `OddCycleTER.Audit.MoveAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨moveArena⟩
  objectArena := .source ⟨moveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source moveArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize moveSignature (fun _ _ R => moves R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Games.OddCycleTER
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      booleanPredicate := false
      stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end MoveAudit

namespace GrundyAudit

private abbrev grundyActual : Realization signature :=
  realize signature (fun _ _ R => grundy R) (fun e => nomatch e)

private abbrev grundyArena : Arena where
  signature := signature
  Law r := ∀ {m : ℕ} (R : Finset (Vertex m)),
    r.readout () m R = mex ((moves R).image grundy)

private theorem grundy_rejected_law : ¬ grundyArena.Law rejected := by
  classical
  intro h
  have step : 1 = mex ((moves (∅ : Finset (Vertex 2))).image grundy) := @h 2 ∅
  rw [moves_empty, image_empty] at step
  exact notMem_empty 0 ((mex_spec ∅).2 0 (by omega))

def evidence : Registration grundyArena (type_of% @OddCycleTER.grundy_eq) where
  actual := grundyActual
  bridge := Iff.rfl
  variation := ⟨@OddCycleTER.grundy_eq, rejected, grundy_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, grundy_rejected_law⟩
      intro j different
      exact (different (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨m, S, T, h⟩ := readout_dependence i
    exact ⟨m, Sᶜ, Tᶜ, h⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@OddCycleTER.grundy_eq) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S0.Certificates.Games.OddCycleTER.grundy_eq_unit
  realizationName := `OddCycleTER.Audit.GrundyAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨grundyArena⟩
  objectArena := .source ⟨grundyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source grundyArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ R => grundy R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Games.OddCycleTER
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      booleanPredicate := false
      stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end GrundyAudit

#print axioms registration
end
end OddCycleTER.Audit
