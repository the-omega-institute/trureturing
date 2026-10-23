import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open _root_.D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ n : ℕ, Σ A : CountMat n n, Σ d : ℕ, Σ i : Fin n, Σ b : ℕ, Fin n
  State p := FinitePath p.2.1 (p.2.2.1 + p.2.2.2.2.1) p.2.2.2.1 p.2.2.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Edge p.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => pathWord r) (fun e => nomatch e)
def erased : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observer := ∀ {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q), ∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j)
    {b : ℕ} {k : Fin n} (q : FinitePath A b j k),
    ∃ r : FinitePath A (d + b) i k,
      observer.readout () ⟨n, A, d, i, b, k⟩ r = pathWord p ++ pathWord q ∧
      ∀ z : {z : Q // L.project z = k},
        L.liftPath r z = L.liftPath p (L.liftPath q z)

private def twoEdges : CountMat 1 1 := fun _ _ => 2
private def identityLift : IncomingLift twoEdges (Fin 1) where
  project := id
  onto i := ⟨i, rfl⟩
  lift a _ := ⟨a.source, rfl⟩

private def edgeZero : FinitePath twoEdges 1 0 0 :=
  .cons ⟨0, by decide⟩ (.nil 0)
private def edgeOne : FinitePath twoEdges 1 0 0 :=
  .cons ⟨1, by decide⟩ (.nil 0)

def erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨r, hw, _⟩ := h identityLift edgeZero (FinitePath.nil 0)
  change ([] : List (Edge twoEdges)) = [⟨0, 0, (⟨0, by decide⟩ : Fin 2)⟩] ++ [] at hw
  simp at hw

def sourceRegistration : Registration arena (type_of% (@concatenate_paths)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨concatenate_paths, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, ?_, erased_fails⟩
      · intro j hj
        exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, twoEdges, 1, 0, 0, 0⟩, edgeZero, edgeOne, ?_⟩
    change ([⟨0, 0, (⟨0, by decide⟩ : Fin 2)⟩] : List (Edge twoEdges)) ≠ [⟨0, 0, (⟨1, by decide⟩ : Fin 2)⟩]
    intro h
    have he := List.cons.inj h |>.1
    have hn := congrArg (fun e : Edge twoEdges => e.number.val) he
    exact (by decide : (0 : ℕ) ≠ 1) hn

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@concatenate_paths)
    (type_of% (realize signature (fun _ _ r => pathWord r) (fun e => nomatch e)))
    (type_of% (@FinitePath)) Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion.concatenationUnit,
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨sourceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ r => pathWord r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@FinitePath),
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion,
    definition := none,
    coordinates := #[0, 1, 4, 5, 8, 9],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false }] }

#print axioms sourceRegistration
end
end Reg.D5.S3.ConceptDynamics.Coding.IncomingLiftAmbiguityCriterion
