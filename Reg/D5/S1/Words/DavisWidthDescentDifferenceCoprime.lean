import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.DavisWidthDescentDifferenceCoprime
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime
open _root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime
open LaurentPolynomial
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LaurentPolynomial Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n k => G n k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n k : Nat, 1 ≤ k → k < n → Nat.Coprime k n →
    r.readout () n k = (n : LaurentPolynomial Int) * T (1 - (k : Int)) * eulerian (n - 1)

theorem eulerian_one : eulerian 1 = 1 := by
  have h : widthDescents 1 (Equiv.refl (Fin 1)) = 0 := by decide +kernel
  simp only [eulerian, Fintype.sum_unique]
  change T (widthDescents 1 (Equiv.refl (Fin 1)) : Int) = 1
  rw [h]
  rfl

theorem eulerian_two : eulerian 2 = T 0 + T 1 := by
  have h0 : widthDescents 1 (Equiv.refl (Fin 2)) = 0 := by decide +kernel
  have h1 : widthDescents 1 (Equiv.swap (0 : Fin 2) 1) = 1 := by decide +kernel
  rw [eulerian, ← Equiv.Perm.decomposeFin.symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, h0, h1]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 2 1 (by decide) (by decide) (by decide)
  change (0 : LaurentPolynomial Int) = 2 * T (1 - (1 : Int)) * eulerian 1 at hf
  simp only [eulerian_one, sub_self, T_zero, mul_one] at hf
  have hc := congrArg (fun p : LaurentPolynomial Int => p.coeff 0) hf
  norm_num [AddMonoidAlgebra.natCast_def] at hc

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨3, 1, 2, ?_⟩
  change G 3 1 ≠ G 3 2
  rw [_root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result
    3 1 (by decide) (by decide) (by decide),
    _root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result
    3 2 (by decide) (by decide) (by decide)]
  norm_num only
  rw [eulerian_two]
  intro h
  have hc := congrArg (fun p : LaurentPolynomial Int => p.coeff (-1)) h
  change
    (AddMonoidAlgebra.single (0 : Int) (3 : Int) * AddMonoidAlgebra.single 0 1 *
      (AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single 1 1)).coeff (-1) =
    (AddMonoidAlgebra.single (0 : Int) (3 : Int) * AddMonoidAlgebra.single (-1) 1 *
      (AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single 1 1)).coeff (-1) at hc
  norm_num only [T, mul_add, AddMonoidAlgebra.natCast_def,
    AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single, Finsupp.add_apply, Finsupp.single_apply] at hc
  norm_num at hc

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.DavisWidthDescentDifferenceCoprime.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ n k => G n k) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "DavisWidthDescentDifferenceCoprime") "result") "Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime/Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ n k => G n k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime, definition := some { owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime, name := `D5.S1.Words.DavisWidthDescentDifferenceCoprime.claim, path := #[] }, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `D5.S1.Words.DavisWidthDescentDifferenceCoprime.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `D5.S1.Words.DavisWidthDescentDifferenceCoprime.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.observationFact0, `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime


noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.arena
noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.arena
noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.arena D5.S1.Words.DavisWidthDescentDifferenceCoprime.claim
    Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration)

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `D5.S1.Words.DavisWidthDescentDifferenceCoprime.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.arena D5.S1.Words.DavisWidthDescentDifferenceCoprime.claim
  Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration)

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.observation0 : (n k : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
    @LT.lt.{0} Nat instLTNat k n →
      Nat.Coprime k n →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.signature PUnit.unit.{1} n :=
  fun (n k : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
    (a_1 : @LT.lt.{0} Nat instLTNat k n) (a_2 : Nat.Coprime k n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.signature
    Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.actual PUnit.unit.{1} n k

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `D5.S1.Words.DavisWidthDescentDifferenceCoprime.claim, part := .value, path := [.body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `D5.S1.Words.DavisWidthDescentDifferenceCoprime.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration).actual (Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration).variation.2.choose (Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration).variation.1 (Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"DavisWidthDescentDifferenceCoprime\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime, declaration := `Reg.D5.S1.Words.DavisWidthDescentDifferenceCoprime.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
