import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
import Reg.Support.DependentFamily
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
open _root_.D5.S1.Scale
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
open LeanInformationAudit NumberField IsDedekindDomain
open scoped WithZero

namespace Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness

noncomputable section

local instance : IsCyclotomicExtension {3} ℚ E :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

abbrev signature : Signature where
  Params := Unit
  State := fun _ => L
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => IntermediateField E L
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ζ => actualCyclotomic ζ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (⊤ : IntermediateField E L)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ),
    let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E := Classical.choice eisenstein_cyclotomic_equiv_exists
    let B : ℕ → ℕ := blockValue
    let S : Finset ℕ := support j
    let I := radicalIndex j
    ∃ ζ : L, IsPrimitiveRoot ζ (modulus j) ∧
      ∃ π : ℕ → EisensteinOrder, ∃ root : I → L,
        ((∀ p ∈ S,
          (Ideal.span {π p}).IsPrime ∧ QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ π p - 1 ∧ p % 3 = 1 ∧
          IsCoprime (π p) (star (π p))) ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
          IsCoprime (π p) (π q) ∧ IsCoprime (π p) (star (π q)) ∧
          IsCoprime (star (π p)) (π q) ∧ IsCoprime (star (π p)) (star (π q))) ∧
        (∀ i, 1 ≤ i → i < j →
          orientedFactor ((goldenLucas (3 ^ i) - 1).toNat) =
            ∏ p ∈ (B i).primeFactors,
              π p ^ padicValNat p (Nat.fib (fibonacciRank p))) ∧
        (∀ v : I, root v ^ 3 = algebraMap E L
          ((Sum.elim (fun w => φ (if w.2 then star (π w.1.val) else π w.1.val))
            (fun k => if k.val = 0 then (2 : 𝓞 E) else 3) v) : E)) ∧
        Module.finrank E (IntermediateField.adjoin E (Set.range root)) =
          3 ^ (2 * S.card + 2) ∧
        (∀ x : IntermediateField.adjoin E (Set.range root),
          x ^ 3 ≠ algebraMap E (IntermediateField.adjoin E (Set.range root))
            (IsCyclotomicExtension.zeta 3 ℚ E)) ∧
        IsGalois E (IntermediateField.adjoin E (Set.range root)) ∧
        (∃ e : ((IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
            (IntermediateField.adjoin E (Set.range root))) ≃*
            (I → Multiplicative (ZMod 3)),
          ∀ σ : (IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
              (IntermediateField.adjoin E (Set.range root)), ∀ i : I,
            σ (⟨root i, IntermediateField.subset_adjoin E (Set.range root) ⟨i, rfl⟩⟩ :
                IntermediateField.adjoin E (Set.range root)) =
              algebraMap E (IntermediateField.adjoin E (Set.range root))
                (IsCyclotomicExtension.zeta 3 ℚ E) ^
                (Multiplicative.toAdd (e σ i)).val *
                  (⟨root i, IntermediateField.subset_adjoin E (Set.range root) ⟨i, rfl⟩⟩ :
                    IntermediateField.adjoin E (Set.range root)))) ∧
        IntermediateField.adjoin E (Set.range root) ⊓ R.readout () () ζ = ⊥

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0
  dsimp only at hzero
  obtain ⟨ζ, hζ, π, root, hdata, hmeet⟩ := hzero
  let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
  have hdegree : Module.finrank E M = 3 ^ (2 * (support 0).card + 2) :=
    hdata.2.2.2.2.1
  have hMbot : M = ⊥ := by
    change M ⊓ ⊤ = ⊥ at hmeet
    simpa only [inf_top_eq] using hmeet
  rw [hMbot, IntermediateField.finrank_bot] at hdegree
  norm_num [support] at hdegree

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    exact actual_complete_cubic_cyclotomic_disjointness
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    letI : NeZero (modulus 0 : E) := ⟨by norm_num [modulus]⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (modulus 0)
    refine ⟨(), (0 : L), ζ, ?_⟩
    intro heq
    change actualCyclotomic (0 : L) = actualCyclotomic ζ at heq
    have hzero : actualCyclotomic (0 : L) = ⊥ := by
      change IntermediateField.adjoin E {(0 : L)} = ⊥
      apply IntermediateField.adjoin_eq_bot_iff.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact (⊥ : IntermediateField E L).zero_mem
    have hζbot : actualCyclotomic ζ = ⊥ := heq.symm.trans hzero
    have hζmem : ζ ∈ (⊥ : IntermediateField E L) := by
      rw [← hζbot]
      exact IntermediateField.mem_adjoin_simple_self E ζ
    obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp hζmem
    have hxprim : IsPrimitiveRoot x (modulus 0) := by
      have hmapped : IsPrimitiveRoot (algebraMap E L x) (modulus 0) := by
        simpa only [hx] using hζ
      exact hmapped.of_map_of_injective (algebraMap E L).injective
    have hdiv : modulus 0 ∣ 2 * 3 :=
      hxprim.dvd_of_isCyclotomicExtension 3 (by norm_num [modulus])
    norm_num [modulus] at hdiv

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual_complete_cubic_cyclotomic_disjointness) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ζ => actualCyclotomic ζ)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "Galois") "GoldenCubicCompleteCyclotomicDisjointness") "actual_complete_cubic_cyclotomic_disjointness") "Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness/Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ζ => actualCyclotomic ζ)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "fn", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual_complete_cubic_cyclotomic_disjointness, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.observationFact0, `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness


noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena
      Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual)
    Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration)

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"actual_complete_cubic_cyclotomic_disjointness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual_complete_cubic_cyclotomic_disjointness, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.arena
    Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual)
  Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration)

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.observation0 : (j : Nat) →
  let I : Type := D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.radicalIndex j;
  (ζ : D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.L) →
    (π : Nat → D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder) →
      (root : I → D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.L) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.signature PUnit.unit.{1}
          PUnit.unit.{1} :=
  fun (j : Nat) =>
  have φ :
    @AlgEquiv.{0, 0, 0} Int D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
      (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
        (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
          Rat.instField))
      Int.instCommSemiring
      (@CommSemiring.toSemiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
        (@QuadraticAlgebra.instCommSemiring.{0} Int
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          Int.instCommSemiring))
      (@CommSemiring.toSemiring.{0}
        (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
          (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
            Rat.instField))
        (@CommRing.toCommSemiring.{0}
          (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
            (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
              Rat.instField))
          (@NumberField.instCommRingRingOfIntegers.{0}
            D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
            (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
              Rat.instField))))
      (@QuadraticAlgebra.instAlgebra.{0, 0} Int Int
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        Int.instCommSemiring Int.instCommSemiring (@Algebra.id.{0} Int Int.instCommSemiring))
      (@Ring.toIntAlgebra.{0}
        (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
          (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
            Rat.instField))
        (@CommRing.toRing.{0}
          (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
            (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
              Rat.instField))
          (@NumberField.instCommRingRingOfIntegers.{0}
            D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
            (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
              Rat.instField)))) :=
    @Classical.choice.{1}
      (@AlgEquiv.{0, 0, 0} Int D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
        (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
          (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
            Rat.instField))
        Int.instCommSemiring
        (@CommSemiring.toSemiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
          (@QuadraticAlgebra.instCommSemiring.{0} Int
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            Int.instCommSemiring))
        (@CommSemiring.toSemiring.{0}
          (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
            (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
              Rat.instField))
          (@CommRing.toCommSemiring.{0}
            (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
              (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                Rat.instField))
            (@NumberField.instCommRingRingOfIntegers.{0}
              D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
              (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                Rat.instField))))
        (@QuadraticAlgebra.instAlgebra.{0, 0} Int Int
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          Int.instCommSemiring Int.instCommSemiring (@Algebra.id.{0} Int Int.instCommSemiring))
        (@Ring.toIntAlgebra.{0}
          (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
            (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
              Rat.instField))
          (@CommRing.toRing.{0}
            (@NumberField.RingOfIntegers.{0} D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
              (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                Rat.instField))
            (@NumberField.instCommRingRingOfIntegers.{0}
              D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.E
              (@CyclotomicField.instField.{0} (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Rat
                Rat.instField)))))
      D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge.eisenstein_cyclotomic_equiv_exists;
  have B : Nat → Nat := D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.blockValue;
  have S : Finset.{0} Nat := D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j;
  let I : Type := D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.radicalIndex j;
  fun (ζ : D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.L)
    (π : Nat → D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder)
    (root : I → D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.L) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.signature
    Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual PUnit.unit.{1} PUnit.unit.{1} ζ

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"actual_complete_cubic_cyclotomic_disjointness\"],\"part\":\"type\",\"path\":[\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual_complete_cubic_cyclotomic_disjointness, part := .type, path := [.body, .letBody, .letBody, .letBody, .letBody, .argument, .body, .argument, .argument, .body, .argument, .body, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"actual_complete_cubic_cyclotomic_disjointness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual_complete_cubic_cyclotomic_disjointness, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration).actual (Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration).variation.2.choose (Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration).variation.1 (Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"Galois\",\"GoldenCubicCompleteCyclotomicDisjointness\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness, declaration := `Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
