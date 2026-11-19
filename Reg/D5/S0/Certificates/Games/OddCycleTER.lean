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

private theorem mem_moves {R Q : Finset (Vertex m)} :
    Q ∈ moves R ↔ geoHull R = Set.univ ∧ ∃ x ∈ R, R.erase x = Q := by
  classical
  by_cases h : geoHull R = Set.univ <;> simp [moves, h]


private theorem grundy_eq (R : Finset (Vertex m)) :
    grundy R = mex ((moves R).image grundy) := by
  classical
  rw [grundy, WellFounded.fix_eq]
  congr 1
  ext t
  simp only [mem_image, mem_attach]
  constructor
  · rintro ⟨Q, _, hQ⟩
    exact ⟨Q.1, Q.2, hQ⟩
  · rintro ⟨Q, hQ, ht⟩
    exact ⟨⟨Q, hQ⟩, trivial, ht⟩


private theorem mem_moves_selected {S T : Finset (Vertex m)} :
    Tᶜ ∈ moves Sᶜ ↔ geoHull Sᶜ = Set.univ ∧ ∃ x ∉ S, insert x S = T := by
  rw [mem_moves]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨x, mem_compl.mp hx, ?_⟩
    apply (compl_injective : Function.Injective (compl : Finset (Vertex m) → _))
    simpa only [compl_insert] using he
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_compl.mpr hx, (compl_insert (a := x) (s := S)).symm⟩

private theorem readout_dependence : ObservationalDependence signature actual := by
  classical
  intro i
  let v : Vertex 2 := 0
  have full : geoHull (∅ : Finset (Vertex 2))ᶜ = Set.univ := by
    ext z
    simp only [geoHull, compl_empty, coe_univ, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro K hK _
    exact hK trivial
  have option : ({v} : Finset (Vertex 2))ᶜ ∈ moves (∅ : Finset (Vertex 2))ᶜ :=
    mem_moves_selected.mpr ⟨full, v, by simp, rfl⟩
  have different : terNim ({v} : Finset (Vertex 2)) ≠ 0 := by
    intro zero
    have noMex := (mex_spec ((moves (∅ : Finset (Vertex 2))ᶜ).image grundy)).1
    have start : mex ((moves (∅ : Finset (Vertex 2))ᶜ).image grundy) = 0 :=
      (grundy_eq _).symm.trans (conjecture_5_5 2 (by decide))
    exact noMex (mem_image.mpr ⟨_, option, zero.trans start.symm⟩)
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

#print axioms registration
end
end OddCycleTER.Audit
