import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression

open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression
open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree (externalBoundary)
open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary (columns)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Deletion

abbrev signature : Signature where
  Params := Nat
  State := fun m => Finset (Bool × Fin (m + 1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ X => X.card) (fun e => nomatch e)

abbrev assertion : Prop := ∀ {m : Nat} [NeZero m], 108 ≤ m →
  ∀ (t : Fin (m + 1)) (X : Finset (Bool × Fin (m + 1))), EmptyBuffer t X →
    ∃ Y : Finset (Bool × Fin m),
      Y.card = X.card ∧
      (externalBoundary (gp m 4) Y).card = (externalBoundary (gp (m + 1) 4) X).card ∧
      Y.image (insertVertex t) = X ∧
      (externalBoundary (gp m 4) Y).image (insertVertex t) =
        externalBoundary (gp (m + 1) 4) X ∧
      (columns Y).image t.succAbove = columns X ∧
      ∀ u ∈ Y, ∀ v : Bool × Fin m,
        (gp m 4).Adj u v ↔ (gp (m + 1) 4).Adj (insertVertex t u) (insertVertex t v)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} [NeZero m], 108 ≤ m →
    ∀ (t : Fin (m + 1)) (X : Finset (Bool × Fin (m + 1))), EmptyBuffer t X →
      ∃ Y : Finset (Bool × Fin m),
        Y.card = R.readout () m X ∧
        (externalBoundary (gp m 4) Y).card = (externalBoundary (gp (m + 1) 4) X).card ∧
        Y.image (insertVertex t) = X ∧
        (externalBoundary (gp m 4) Y).image (insertVertex t) =
          externalBoundary (gp (m + 1) 4) X ∧
        (columns Y).image t.succAbove = columns X ∧
        ∀ u ∈ Y, ∀ v : Bool × Fin m,
          (gp m 4).Adj u v ↔ (gp (m + 1) 4).Adj (insertVertex t u) (insertVertex t v)

def intervention : Realization signature := realize signature
  (fun _ _ X => X.card + 1) (fun e => nomatch e)

theorem actual_law : arena.Law actual := @buffered_deletion

theorem intervention_rejected : ¬ arena.Law intervention := by
  intro h
  obtain ⟨Y, hcard, _, himage, _⟩ := h (m := 108) (by decide) (0 : Fin 109) ∅
    (by intro x hx; simp at hx)
  have hY : Y = ∅ := Finset.image_eq_empty.mp himage
  simp [hY, intervention, realize] at hcard

def registration : Registration arena assertion where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, intervention, intervention_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention, ?_, rfl, intervention_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨108, ∅, {(false, (0 : Fin 109))}, ?_⟩
    simp [actual, realize]

noncomputable def registration_buffered_deletion : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression.buffered_deletion)
    (type_of% (realize signature (fun _ _ X => X.card) (fun e => nomatch e))) Nat Unit := {
  unitName := `Reg.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression.buffered_deletion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression.Deletion.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Deletion

namespace CompressionBoundaryReadout

abbrev signature : Signature where
  Params := Nat
  State := fun n => Finset (Bool × Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n X => (externalBoundary (gp n 4) X).card) (fun e => nomatch e)

abbrev assertion : Prop := ∀ n : Nat, 108 < n → ∀ X : Finset (Bool × Fin n),
  X.card = 16 → (externalBoundary (gp n 4) X).card ≤ 9 →
    ∃ Y : Finset (Bool × Fin 108), Y.card = 16 ∧
      (externalBoundary (gp 108 4) Y).card = (externalBoundary (gp n 4) X).card

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : Nat, 108 < n → ∀ X : Finset (Bool × Fin n),
    X.card = 16 → (externalBoundary (gp n 4) X).card ≤ 9 →
      ∃ Y : Finset (Bool × Fin 108), Y.card = 16 ∧
        (externalBoundary (gp 108 4) Y).card = R.readout () n X

theorem bridge : assertion ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := compression_to_108

/-- If the small-boundary sets are excluded, changing only the concluding
boundary readout cannot change this implication. -/
theorem law_of_boundary_exclusion
    (exclude : ∀ n : Nat, 108 < n → ∀ X : Finset (Bool × Fin n),
      X.card = 16 → 9 < (externalBoundary (gp n 4) X).card)
    (R : Realization signature) : arena.Law R := by
  intro n hn X hX hB
  have := exclude n hn X hX
  omega

theorem no_registration_of_boundary_exclusion
    (exclude : ∀ n : Nat, 108 < n → ∀ X : Finset (Bool × Fin n),
      X.card = 16 → 9 < (externalBoundary (gp n 4) X).card) :
    ¬ Nonempty (Registration arena assertion) := by
  rintro ⟨r⟩
  obtain ⟨_, bad, hbad⟩ := r.variation
  exact hbad (law_of_boundary_exclusion exclude bad)

end CompressionBoundaryReadout

#print axioms Deletion.registration_buffered_deletion
#print axioms CompressionBoundaryReadout.no_registration_of_boundary_exclusion

end
end Reg.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression
