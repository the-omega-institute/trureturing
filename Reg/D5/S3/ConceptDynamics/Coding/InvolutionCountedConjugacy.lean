import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
import Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange

open _root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open _root_.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
universe u

theorem sourceNat_diagonal {H : Type u} [Group H] [Fintype H]
    (s : H) (hs : s * s = 1) : sourceNat s s = targetNat H := by
  exact congrArg toNat (source_diagonal s hs)

def minimumArena : Arena where
  signature := elementSignature.{u}
  Law R := ∀ {H : Type u} [Group H] [Fintype H] (s t : H)
    (hs : s * s = 1) (hst : s * t ≠ t * s),
    ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 ∧
    ¬ExchangeChain (NAlg H) (sourceMatrix s (R.readout () ⟨H, s⟩ t)) (targetMatrix H) 0

theorem minimum_actual_law : minimumArena.{u}.Law elementActual := by
  intro H instG instF s t hs hst
  exact involution_minimum_one s t hs hst

theorem minimum_rejected_law : ¬ minimumArena.{u}.Law elementBad := by
  intro h
  have hn := (h g3s.{u} g3t g3_involution g3_noncommuting).2
  apply hn
  change ExchangeChain (NAlg G3.{u}) (scalar (sourceNat g3s g3s))
    (scalar (targetNat G3)) 0
  rw [sourceNat_diagonal g3s g3_involution]
  exact ExchangeChain.nil _

def minimumRegistration : Registration minimumArena.{u}
    (∀ {H : Type u} [Group H] [Fintype H] (s t : H)
      (hs : s * s = 1) (hst : s * t ≠ t * s),
      ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 ∧
      ¬ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 0) where
  actual := elementActual
  bridge := Iff.rfl
  variation := ⟨minimum_actual_law, elementBad, minimum_rejected_law⟩
  sensitivity := elementSensitivity minimumArena.Law minimum_rejected_law
  dependence := elementDependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.involution_minimum_one.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "InvolutionCountedConjugacy") "involution_minimum_one") "Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy/Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(minimumArena.{u})⟩,
  objectArena := .source ⟨(minimumArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (minimumArena.{u}) ⟨(minimumRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.involution_minimum_one, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.anchorEnumeration }


def productsArena : Arena where
  signature := elementSignature.{u}
  Law R := ∀ {H : Type u} [Group H] [Fintype H] (s t : H) (hs : s * s = 1),
    toNat (leftFactor s t) * toNat (rightFactor s) =
      sourceNat s (R.readout () ⟨H, s⟩ t) ∧
    toNat (rightFactor s) * toNat (leftFactor s t) = targetNat H

theorem products_actual_law : productsArena.{u}.Law elementActual := by
  intro H instG instF s t hs
  exact natural_factor_products s t hs

theorem products_rejected_law : ¬ productsArena.{u}.Law elementBad := by
  intro h
  have heq : sourceNat g3s.{u} g3t = sourceNat g3s g3s :=
    (natural_factor_products g3s g3t g3_involution).1.symm.trans
      (h g3s g3t g3_involution).1
  rw [sourceNat_diagonal g3s g3_involution] at heq
  have hc := congrArg (fun p : NAlg G3.{u} => p.coeff g3t) heq
  change (toNat (source g3s g3t)).coeff g3t = (toNat (target G3)).coeff g3t at hc
  simp only [toNat, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply,
    g3_source_coefficient, target_coefficient] at hc
  exact (by decide : (3 : ℕ) ≠ 2) hc

def productsRegistration : Registration productsArena.{u}
    (∀ {H : Type u} [Group H] [Fintype H] (s t : H) (hs : s * s = 1),
      toNat (leftFactor s t) * toNat (rightFactor s) = sourceNat s t ∧
      toNat (rightFactor s) * toNat (leftFactor s t) = targetNat H) where
  actual := elementActual
  bridge := Iff.rfl
  variation := ⟨products_actual_law, elementBad, products_rejected_law⟩
  sensitivity := elementSensitivity productsArena.Law products_rejected_law
  dependence := elementDependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.natural_factor_products.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "InvolutionCountedConjugacy") "natural_factor_products") "Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy/Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(productsArena.{u})⟩,
  objectArena := .source ⟨(productsArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (productsArena.{u}) ⟨(productsRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.natural_factor_products, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.anchorEnumeration }


#print axioms minimumRegistration
#print axioms productsRegistration
end Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0} (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsArena.) (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"natural_factor_products\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.natural_factor_products, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.observation0.{u} : {H : Type u} →
  [inst : Group.{u} H] →
    [Fintype.{u} H] →
      (s t : H) →
        (hs :
            @Eq.{u + 1} H
              (@HMul.hMul.{u, u, u} H H H
                (@instHMul.{u} H
                  (@MulOne.toMul.{u} H
                    (@MulOneClass.toMulOne.{u} H
                      (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                s s)
              (@OfNat.ofNat.{u} H (nat_lit 1)
                (@One.toOfNat1.{u} H
                  (@InvOneClass.toOne.{u} H
                    (@DivInvOneMonoid.toInvOneClass.{u} H
                      (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst))))))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
            Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u} PUnit.unit.{1}
            (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) :=
  fun {H : Type u} [Group.{u} H] [Fintype.{u} H] (s t : H)
    (hs :
      @Eq.{u + 1} H
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          s s)
        (@OfNat.ofNat.{u} H (nat_lit 1)
          (@One.toOfNat1.{u} H
            (@InvOneClass.toOne.{u} H
              (@DivInvOneMonoid.toInvOneClass.{u} H
                (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst))))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementActual.{u} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) t

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"natural_factor_products\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.natural_factor_products, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"natural_factor_products\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.natural_factor_products, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"productsRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.productsRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0} (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumArena.) (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"involution_minimum_one\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.involution_minimum_one, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.observation0.{u} : {H : Type u} →
  [inst : Group.{u} H] →
    [Fintype.{u} H] →
      (s t : H) →
        (hs :
            @Eq.{u + 1} H
              (@HMul.hMul.{u, u, u} H H H
                (@instHMul.{u} H
                  (@MulOne.toMul.{u} H
                    (@MulOneClass.toMulOne.{u} H
                      (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                s s)
              (@OfNat.ofNat.{u} H (nat_lit 1)
                (@One.toOfNat1.{u} H
                  (@InvOneClass.toOne.{u} H
                    (@DivInvOneMonoid.toInvOneClass.{u} H
                      (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst))))))) →
          (hst :
              @Ne.{u + 1} H
                (@HMul.hMul.{u, u, u} H H H
                  (@instHMul.{u} H
                    (@MulOne.toMul.{u} H
                      (@MulOneClass.toMulOne.{u} H
                        (@Monoid.toMulOneClass.{u} H
                          (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                  s t)
                (@HMul.hMul.{u, u, u} H H H
                  (@instHMul.{u} H
                    (@MulOne.toMul.{u} H
                      (@MulOneClass.toMulOne.{u} H
                        (@Monoid.toMulOneClass.{u} H
                          (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                  t s)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
              Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u} PUnit.unit.{1}
              (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) :=
  fun {H : Type u} [Group.{u} H] [Fintype.{u} H] (s t : H)
    (hs :
      @Eq.{u + 1} H
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          s s)
        (@OfNat.ofNat.{u} H (nat_lit 1)
          (@One.toOfNat1.{u} H
            (@InvOneClass.toOne.{u} H
              (@DivInvOneMonoid.toInvOneClass.{u} H
                (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst)))))))
    (hst :
      @Ne.{u + 1} H
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          s t)
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          t s)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementActual.{u} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) t

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"involution_minimum_one\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.involution_minimum_one, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"involution_minimum_one\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.involution_minimum_one, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionCountedConjugacy\",\"minimumRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy.minimumRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
