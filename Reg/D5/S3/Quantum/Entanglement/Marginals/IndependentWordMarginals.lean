import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals
open Function (update)

noncomputable section
universe u

private abbrev signature : Signature where
  Params := Σ V : Type u, Σ _ : V → Bool, V → Bool
  State p := Matrix (p.1 → Bool) (p.1 → Bool) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p R => R p.2.1 p.2.2) (fun a => nomatch a)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature.{u}
  Law F := ∀ {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (R : Matrix (V → Bool) (V → Bool) ℂ)
    (_hrow : ∀ {x y : V → Bool} {i j : V}, G.Adj i j →
      x i = true → x j = true → R x y = 0)
    (_hcol : ∀ {x y : V → Bool} {i j : V}, G.Adj i j →
      y i = true → y j = true → R x y = 0),
    (∀ (i : V) (x y : V → Bool),
      R (update x i false) (update y i false) +
        R (update x i true) (update y i true) = 0) ↔
      (∀ (i j : V) (x y : V → Bool), G.Adj i j → x i = y i →
        F.readout () ⟨V, x, y⟩ R = 0) ∧
      (∀ (i : V), (∀ j, ¬ G.Adj i j) → ∀ x y,
        R (update x i false) (update y i false) +
          R (update x i true) (update y i true) = 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let V := ULift.{u} Bool
  let G : SimpleGraph V := ⊤
  let R : Matrix (V → Bool) (V → Bool) ℂ := 0
  let x : V → Bool := fun _ => false
  have edge : G.Adj ⟨false⟩ ⟨true⟩ := by
    change (⟨false⟩ : V) ≠ ⟨true⟩
    decide
  have trace_zero (i : V) (a b : V → Bool) :
      R (update a i false) (update b i false) +
        R (update a i true) (update b i true) = 0 := by simp [R]
  have result := ((h G R (by intros; rfl) (by intros; rfl)).1 trace_zero).1
    ⟨false⟩ ⟨true⟩ x x edge rfl
  exact one_ne_zero result

def family : Registration arena.{u} (type_of% @deletion_kernel_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deletion_kernel_iff.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    let p : signature.Params := ⟨ULift.{u} Unit, (fun _ => false), fun _ => false⟩
    exact ⟨p, (fun _ _ => 0), (fun _ _ => 1), zero_ne_one⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deletion_kernel_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals.deletion_kernel_iff.audit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p R => R p.2.1 p.2.2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals
    definition := none
    coordinates := #[0, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals
