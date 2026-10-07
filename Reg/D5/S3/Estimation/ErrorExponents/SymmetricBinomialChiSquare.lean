import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare
open _root_.D5.S3.TotalVariation.Bhattacharyya
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare

def signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (B : ℕ) (z : ℝ), |z| ≤ 1 →
    (∀ k ∈ Finset.range (B + 1), 0 ≤ p_z B (R.readout () B z) k) ∧
    (∑ k ∈ Finset.range (B + 1), p_z B z k) = 1 ∧
    (∀ k ≤ B, p_z B z k / p_0 B k =
      ((1 + z) ^ k * (1 - z) ^ (B - k) +
        (1 - z) ^ k * (1 + z) ^ (B - k)) / 2) ∧
    chiSquare B z = ((1 + z ^ 2) ^ B + (1 - z ^ 2) ^ B) / 2 - 1 ∧
      chiSquare B z =
        ∑ j ∈ Finset.Icc 1 (B / 2), (B.choose (2 * j) : ℝ) * z ^ (4 * j) ∧
    chiSquare B z ≤ Real.cosh (B * z ^ 2) - 1 ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → (B : ℝ) * δ ≤ 1 →
      z ^ 2 = 2 * δ - δ ^ 2 → chiSquare B z ≤ 3 * ((B : ℝ) * δ) ^ 2) ∧
    (|z| < 1 →
      (∀ k ∈ Finset.range (B + 1), 0 < p_z B z k) ∧
      0 < bhattacharyya
        (fun k : Fin (B + 1) => p_0 B k)
        (fun k : Fin (B + 1) => p_z B z k)) ∧
    1 - bhattacharyya
      (fun k : Fin (B + 1) => p_0 B k)
      (fun k : Fin (B + 1) => p_z B z k) ^ 2 ≤ chiSquare B z

theorem actual_law : arena.Law actual := by
  intro B z hz
  simpa [actual, realize, signature] using symmetric_binomial_chi_square B z hz

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcase := h 2 0 (by norm_num)
  have hnegative := hcase.1 1 (by norm_num)
  norm_num [rejected, realize, signature, p_z] at hnegative

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(0 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
  change (0 : ℝ) ≠ 1
  exact zero_ne_one

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.symmetric_binomial_chi_square) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ z => z) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "ErrorExponents") "SymmetricBinomialChiSquare") "symmetric_binomial_chi_square") "Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare/Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "body", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.symmetric_binomial_chi_square, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.observationFact0, `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare


noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.arena
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.arena
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.arena) (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration).actual

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"symmetric_binomial_chi_square\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.symmetric_binomial_chi_square, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration).bridge

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.observation0 : (B : Nat) →
  (z : Real) →
    (hz :
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup z)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (k : Nat) →
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (Finset.range
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            k →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.signature PUnit.unit.{1} B :=
  fun (B : Nat) (z : Real)
    (hz :
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup z)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (k : Nat)
    (a :
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
        (Finset.range
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        k) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.signature
    Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.actual PUnit.unit.{1} B z

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"symmetric_binomial_chi_square\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.symmetric_binomial_chi_square, part := .type, path := [.body, .body, .body, .function, .argument, .body, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"symmetric_binomial_chi_square\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.symmetric_binomial_chi_square, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration).actual (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration).variation.2.choose (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration).variation.1 (Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"ErrorExponents\",\"SymmetricBinomialChiSquare\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare, declaration := `Reg.D5.S3.Estimation.ErrorExponents.SymmetricBinomialChiSquare.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
