import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts

open MulAction LeanInformationAudit
open scoped Classical
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateFlagCoupling
open _root_.D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

universe u v w

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => m % 2) (fun e => nomatch e)

def alwaysOdd : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def trivialAction (G X : Type*) [Monoid G] : MulAction G X where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

abbrev exactArena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] {T : Type} [Fintype T] [MulAction (Acting I) T]
    (m : orbitRel.Quotient (Acting I) T → ℕ) (z : orbitRel.Quotient (Acting I) T → I → ℕ),
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting I) S) (f : S → T),
      (∀ (g : Acting I) s, f (g • s) = g • f s) ∧
      (∀ t, Nat.card {s : S // f s = t} = m (Quotient.mk'' t)) ∧
      ∀ i t, Nat.card {s : S // f s = t ∧ generator i • s = s} =
        if generator i • t = t then z (Quotient.mk'' t) i else 0) ↔
    ∀ (t : T) (i : I), generator i • t = t →
      z (Quotient.mk'' t) i ≤ m (Quotient.mk'' t) ∧
        z (Quotient.mk'' t) i % 2 = R.readout () () (m (Quotient.mk'' t))

private theorem exact_always_odd_fails : ¬ exactArena.{u}.Law alwaysOdd := by
  intro fails
  let I := PUnit.{u+1}
  letI : Fintype I := inferInstanceAs (Fintype PUnit)
  letI : MulAction (Acting I) Unit := trivialAction _ _
  have actual := (exact_orbit_fibre_counts (I := I) (T := Unit) (fun _ => 0) (fun _ _ => 0)).mpr
    (fun _ _ _ => ⟨le_rfl, rfl⟩)
  have impossible := ((fails (I := I) (T := Unit) (fun _ => 0) (fun _ _ => 0)).mp actual)
    () PUnit.unit rfl
  exact (by decide : ¬ (0 % 2 = 1)) impossible.2

def exactFamily : Registration exactArena.{u} (type_of% (@exact_orbit_fibre_counts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exact_orbit_fibre_counts, alwaysOdd, exact_always_odd_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysOdd, ?_, rfl, exact_always_odd_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 0, 1, by decide⟩

def exactRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_orbit_fibre_counts) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts.prescribedCountParity
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts.exactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exactArena.{u}⟩
  objectArena := .source ⟨exactArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exactArena.{u} ⟨exactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m % 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev extractionArena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] {S : Type v} {T : Type w} [Finite S]
    [MulAction (Acting I) S] [MulAction (Acting I) T]
    (f : S → T), (∀ (g : Acting I) s, f (g • s) = g • f s) →
    ∃ (m : orbitRel.Quotient (Acting I) T → ℕ)
      (z : orbitRel.Quotient (Acting I) T → I → ℕ),
      (∀ o i, z o i ≤ m o) ∧ (∀ o i, z o i % 2 = R.readout () () (m o)) ∧
      (∀ t, Nat.card {s : S // f s = t} = m (Quotient.mk'' t)) ∧
      ∀ i t, Nat.card {s : S // f s = t ∧ generator i • s = s} =
        if generator i • t = t then z (Quotient.mk'' t) i else 0

private theorem extraction_always_odd_fails : ¬ extractionArena.{u,v,w}.Law alwaysOdd := by
  intro fails
  let I := PUnit.{u+1}
  let S := PEmpty.{v+1}
  let T := PUnit.{w+1}
  letI : Fintype I := inferInstanceAs (Fintype PUnit)
  letI : Finite S := inferInstanceAs (Finite PEmpty)
  letI : MulAction (Acting I) S := trivialAction _ _
  letI : MulAction (Acting I) T := trivialAction _ _
  let f (s : S) : T := nomatch s
  obtain ⟨m, z, bounds, parity, counts, _⟩ := fails (I := I) f (fun _ s => nomatch s)
  let t : T := PUnit.unit
  let o : orbitRel.Quotient (Acting I) T := Quotient.mk'' t
  have emptyCounts : m o = 0 := by
    rw [← counts t]
    simp
  have emptyFixed : z o PUnit.unit = 0 := Nat.eq_zero_of_le_zero
    ((bounds o PUnit.unit).trans_eq emptyCounts)
  have impossible := parity o PUnit.unit
  change z o PUnit.unit % 2 = 1 at impossible
  rw [emptyFixed] at impossible
  exact (by decide : ¬ (0 % 2 = 1)) impossible

def extractionFamily : Registration extractionArena.{u,v,w}
    (type_of% (@orbit_fixed_fibre_counts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@orbit_fixed_fibre_counts, alwaysOdd, extraction_always_odd_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨alwaysOdd, ?_, rfl, extraction_always_odd_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 0, 1, by decide⟩

def extractionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@orbit_fixed_fibre_counts) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts.observedCountParity
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts.extractionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨extractionArena.{u,v,w}⟩
  objectArena := .source ⟨extractionArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source extractionArena.{u,v,w} ⟨extractionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m % 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "fn", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.ConceptDynamics.Attribution.CoordinateFibreCounts
