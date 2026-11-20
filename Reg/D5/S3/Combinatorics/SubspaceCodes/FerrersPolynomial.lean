import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! # Source readout for linearized evaluation -/

namespace Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial

open _root_.D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v
noncomputable section

private abbrev Params :=
  Sigma fun F : Type u => Sigma fun E : Type v => Sigma fun f : Field F =>
    Sigma fun _ : Fintype F => Sigma fun e : Field E =>
    Sigma fun _ : (letI := f; letI := e; Algebra F E) => Fin 4 → E

private abbrev signature : Signature where
  Params := Params.{u, v}
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def evaluation (_ : Unit) (p : Params.{u, v}) (x : p.2.1) : p.2.1 :=
  @evaluateLinearized p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
    p.2.2.2.2.2.1 p.2.2.2.2.2.2 x

private def actual : Realization signature.{u, v} :=
  realize signature evaluation (fun e => nomatch e)

private def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p _ => @Zero.zero _ p.2.2.2.2.1.toZero)
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ (F : Type u) (E : Type v) [f : Field F] [q : Fintype F] [e : Field E]
    [alg : Algebra F E] (a : Fin 4 → E) (x : E),
    r.readout () ⟨F, E, f, q, e, alg, a⟩ x =
      ∑ i : Fin 4, a i * x ^ Fintype.card F ^ i.val

private abbrev sampleF := ULift.{u} (ZMod 2)
private abbrev sampleE := ULift.{v} (ZMod 2)

private abbrev sampleAlgebra : Algebra sampleF.{u} sampleE.{v} :=
  (RingHom.id (ZMod 2)).ulift.toAlgebra

private def sampleCoefficients : Fin 4 → sampleE.{v} := ![1, 0, 0, 0]

private def sample : Params.{u, v} :=
  ⟨sampleF, sampleE, inferInstance, inferInstance, inferInstance, sampleAlgebra, sampleCoefficients⟩

private theorem sample_eval (x : sampleE.{v}) : actual.{u, v}.readout () sample x = x := by
  let := sampleAlgebra.{u, v}
  change evaluateLinearized sampleF.{u} sampleE.{v} sampleCoefficients x = x
  rw [evaluateLinearized_apply]
  simp [Fin.sum_univ_four, sampleCoefficients]

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have he := @h sampleF.{u} sampleE.{v} inferInstance inferInstance inferInstance
    sampleAlgebra sampleCoefficients 1
  change (0 : sampleE.{v}) = ∑ i : Fin 4, sampleCoefficients i * (1 : sampleE.{v}) ^
    Fintype.card sampleF.{u} ^ i.val at he
  simp [Fin.sum_univ_four, sampleCoefficients] at he

def source_registration : Registration arena.{u, v}
    (type_of% @evaluateLinearized_apply.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨evaluateLinearized_apply, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    cases i
    refine ⟨sample, (0 : sampleE.{v}), (1 : sampleE.{v}), ?_⟩
    rw [sample_eval, sample_eval]
    exact (zero_ne_one : (0 : sampleE.{v}) ≠ 1)

def evaluateLinearizedApply :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@evaluateLinearized_apply.{u, v}) (Realization signature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial.evaluateLinearizedApply.unit
  realizationName := `Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature evaluation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms evaluateLinearizedApply

end
end Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersPolynomial
