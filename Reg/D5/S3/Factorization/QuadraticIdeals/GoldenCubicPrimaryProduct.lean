import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct

open _root_.D5.S1.Scale
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance

private def factor (j : ℕ) : EisensteinOrder :=
  orientedFactor ((goldenLucas (3 ^ j) - 1).toNat)

def actual : Realization signature :=
  realize signature (fun _ _ j => factor j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : EisensteinOrder)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ) (_hj : 1 ≤ j),
    let x : ℤ := goldenLucas (3 ^ j)
    let b : ℕ := (x - 1).toNat
    let B : ℕ := blockNorm b
    let eta : EisensteinOrder := R.readout () () j
    let lambda : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
    eta = QuadraticAlgebra.omega * ((x : EisensteinOrder) + lambda) ∧
    QuadraticAlgebra.norm eta = (B : ℤ) ∧
    (9 : EisensteinOrder) ∣ eta - (1 + lambda ^ 3) ∧
    IsCoprime (Ideal.span {eta}) (Ideal.span {star eta}) ∧
    ∃ pi : ℕ → EisensteinOrder,
      (∀ p ∈ B.primeFactors,
        let P : Ideal EisensteinOrder := orientedIdeal b ⊔ Ideal.span {(p : EisensteinOrder)}
        P.IsPrime ∧
          (∀ Q : Ideal EisensteinOrder, Q.IsPrime →
            (p : EisensteinOrder) ∈ Q → eta ∈ Q → Q = P) ∧
          Ideal.span {pi p} = P ∧
          QuadraticAlgebra.norm (pi p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ pi p - 1 ∧
          p % 3 = 1) ∧
      eta = ∏ p ∈ B.primeFactors,
        (pi p) ^ padicValNat p (Nat.fib (fibonacciRank p))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h3 : goldenLucas 3 = 4 := by
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]
  have hnorm := (h 1 (by decide)).2.1
  change QuadraticAlgebra.norm (0 : EisensteinOrder) =
    (blockNorm ((goldenLucas 3 - 1).toNat) : ℤ) at hnorm
  norm_num [h3, blockNorm, QuadraticAlgebra.norm_def] at hnorm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_cubic_primary_product, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : ℕ), factor x ≠ factor y
    refine ⟨(), 1, 2, ?_⟩
    have h3 : goldenLucas 3 = 4 := by
      norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]
    have h9 : goldenLucas 9 = 76 := by
      simpa [h3] using (golden_cubic_lucas_block 1 (by decide)).2.2.2.2.2
    intro h
    have him := congrArg QuadraticAlgebra.im h
    norm_num [factor, orientedFactor, h3, h9] at him

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.golden_cubic_primary_product) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => factor j) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "QuadraticIdeals") "GoldenCubicPrimaryProduct") "golden_cubic_primary_product") "Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct/Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ j => factor j) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "value"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.golden_cubic_primary_product, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.observationFact0, `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.arena) (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration).actual

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"golden_cubic_primary_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.golden_cubic_primary_product, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration).bridge

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.observation0 : (j : Nat) →
  (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (j : Nat) (hj : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j) =>
  have x : Int :=
    D5.S1.Scale.goldenLucas
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j);
  have b : Nat :=
    Int.toNat
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))));
  have B : Nat := D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b;
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.signature
    Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.actual PUnit.unit.{1} PUnit.unit.{1} j

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"golden_cubic_primary_product\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.golden_cubic_primary_product, part := .type, path := [.body, .body, .letBody, .letBody, .letBody, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"golden_cubic_primary_product\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.golden_cubic_primary_product, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration).actual (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration).variation.2.choose (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration).variation.1 (Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"GoldenCubicPrimaryProduct\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
