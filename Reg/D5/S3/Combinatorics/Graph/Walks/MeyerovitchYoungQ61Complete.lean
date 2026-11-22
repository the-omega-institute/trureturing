import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete
import Mathlib.Algebra.Ring.ULift
import Reg.Support.DependentFamily

/-! The suffix payoff and matrix entries used in the complete-walk minimum. -/

namespace Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete

open LeanInformationAudit Maths
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.MeyerovitchYoungQ61Complete

set_option autoImplicit false
set_option linter.checkUnivs false

universe u v w
noncomputable section

abbrev SuffixParameters :=
  Σ E : Type u, Σ F : Type v, Σ K : Type w, Σ _ : CommRing K,
    Σ _ : E → F → K, List E

abbrev suffixSignature : Signature where
  Params := SuffixParameters.{u, v, w}
  State p := List p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def suffixActual : Realization suffixSignature.{u, v, w} :=
  realize suffixSignature (fun _ ⟨E, F, K, r, p, a'⟩ b' => @wordCost E F K r p a' b')
    (fun e => nomatch e)

def suffixRejected : Realization suffixSignature.{u, v, w} :=
  realize suffixSignature (fun _ ⟨_, _, K, r, _, _⟩ _ => letI : CommRing K := r; 0)
    (fun e => nomatch e)

abbrev suffixArena : Arena where
  signature := suffixSignature.{u, v, w}
  Law R := ∀ {E : Type u} {F : Type v} {K : Type w} [r : CommRing K]
    (p : E → F → K) {a a' : List E} {b b' : List F} (_h : a.length = b.length),
    wordCost p (a ++ a') (b ++ b') = wordCost p a b + R.readout () ⟨E, F, K, r, p, a'⟩ b'

private theorem suffixRejected_fails : ¬ suffixArena.{u, v, w}.Law suffixRejected := by
  intro law
  let p : ULift.{u} Unit → ULift.{v} Unit → ULift.{w} ℤ := fun _ _ => 1
  have bad := law p (a := []) (a' := [⟨()⟩]) (b := []) (b' := [⟨()⟩]) rfl
  change (1 : ULift.{w} ℤ) = 0 at bad
  exact one_ne_zero bad

def suffixFamily : Registration suffixArena.{u, v, w} (type_of% @wordCost_append.{u, v, w}) where
  actual := suffixActual
  bridge := Iff.rfl
  variation := ⟨@wordCost_append.{u, v, w}, suffixRejected, suffixRejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨suffixRejected, ?_, rfl, suffixRejected_fails⟩
      intro other h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let p : ULift.{u} Unit → ULift.{v} Unit → ULift.{w} ℤ := fun _ _ => 1
    refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit, ULift.{w} ℤ, inferInstance, p, [⟨()⟩]⟩,
      [], [⟨()⟩], ?_⟩
    change (0 : ULift.{w} ℤ) ≠ 1
    exact zero_ne_one

abbrev MatrixParameters :=
  Σ E : Type u, Σ W : Type v, Σ K : Type w, E → Matrix W W K

abbrev matrixSignature : Signature where
  Params := MatrixParameters.{u, v, w}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (p.2.1 × p.2.1) → p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual : Realization matrixSignature.{u, v, w} :=
  realize matrixSignature (fun _ ⟨_, _, _, A⟩ e => matrixCost A e) (fun e => nomatch e)

def matrixDiagonal : Realization matrixSignature.{u, v, w} :=
  realize matrixSignature (fun _ ⟨_, _, _, A⟩ e f => A e f.1 f.1) (fun e => nomatch e)

abbrev matrixArena : Arena where
  signature := matrixSignature.{u, v, w}
  Law R := ∀ {E : Type u} {W : Type v} {K : Type w} [CommRing K] [LinearOrder K]
    (A : E → Matrix W W K) [Finite W] [Nonempty W] (a : List E),
    IsMinimum (completeGraph W) (R.readout () ⟨E, W, K, A⟩) a (matrixMinimum A a)

private theorem matrixDiagonal_fails : ¬ matrixArena.{u, v, w}.Law matrixDiagonal := by
  intro law
  let e : ULift.{u} Unit := ⟨()⟩
  let i : ULift.{v} Bool := ⟨false⟩
  let j : ULift.{v} Bool := ⟨true⟩
  let A : ULift.{u} Unit → Matrix (ULift.{v} Bool) (ULift.{v} Bool) (ULift.{w} ℤ) :=
    fun _ s t => if s = t then 1 else 0
  have hij : i ≠ j := by decide
  have hlegal : Legal (completeGraph (ULift.{v} Bool)) [(i, j)] :=
    ⟨i, j, EdgeGraph.Walk.concat .nil (i, j) rfl, rfl⟩
  have lower := (matrixMinimum_spec A [e]).2 [(i, j)] hlegal rfl
  have hzero : matrixMinimum A [e] ≤ 0 := by
    simpa [wordCost, matrixCost, A, hij] using lower
  obtain ⟨b, _, hlen, hb⟩ := (law A [e]).1
  obtain ⟨f, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hone : (1 : ULift.{w} ℤ) = matrixMinimum A [e] := by
    change wordCost (fun _ f => A e f.1 f.1) [e] [f] = matrixMinimum A [e] at hb
    simpa [wordCost, A] using hb
  rw [← hone] at hzero
  exact (by decide : ¬ (1 : ULift.{w} ℤ) ≤ 0) hzero

def matrixFamily : Registration matrixArena.{u, v, w} (type_of% @matrixMinimum_spec.{u, v, w}) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨@matrixMinimum_spec.{u, v, w}, matrixDiagonal, matrixDiagonal_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨matrixDiagonal, ?_, rfl, matrixDiagonal_fails⟩
      intro other h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let A : ULift.{u} Bool → Matrix (ULift.{v} Unit) (ULift.{v} Unit) (ULift.{w} ℤ) :=
      fun e _ _ => if e.down then 1 else 0
    refine ⟨⟨ULift.{u} Bool, ULift.{v} Unit, ULift.{w} ℤ, A⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have hentry := congrFun h (⟨()⟩, ⟨()⟩)
    change (0 : ULift.{w} ℤ) = 1 at hentry
    exact zero_ne_one hentry

def suffixRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@wordCost_append.{u, v, w}) (Realization suffixSignature.{u, v, w}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete.suffixUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete.suffixFamily
  realizationSource := none
  generated := false
  arena := .source ⟨suffixArena.{u, v, w}⟩
  objectArena := .source ⟨suffixArena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source suffixArena.{u, v, w} ⟨suffixFamily.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize suffixSignature.{u, v, w} suffixActual.readout suffixActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete
    definition := none
    coordinates := #[0, 1, 2, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def matrixRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@matrixMinimum_spec.{u, v, w}) (Realization matrixSignature.{u, v, w}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete.matrixUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete.matrixFamily
  realizationSource := none
  generated := false
  arena := .source ⟨matrixArena.{u, v, w}⟩
  objectArena := .source ⟨matrixArena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source matrixArena.{u, v, w} ⟨matrixFamily.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature.{u, v, w} matrixActual.readout matrixActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete
    definition := none
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete
