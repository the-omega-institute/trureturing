import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.LucasSquareClassification
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.LucasSquareClassification

open _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Primes.LucasSquareClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => goldenLucas n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def intervention (i : Fin 2) : Realization signature :=
  realize signature (fun j _ n => if j = i then 0 else goldenLucas n)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    (IsSquare (r.readout 0 () n) ↔ n = 1 ∨ n = 3) ∧
      ((∃ x : ℤ, r.readout 1 () n = 2 * x ^ 2) ↔ n = 0 ∨ n = 6)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : IsSquare (rejected.readout 0 () 0) := ⟨0, rfl⟩
  have hb := (h 0).1.mp hs
  omega

theorem intervention_law_failure (i : Fin 2) : ¬ arena.Law (intervention i) := by
  intro h
  fin_cases i
  · have hs : IsSquare ((intervention 0).readout 0 () 0) := by
      refine ⟨0, ?_⟩
      norm_num [intervention, realize]
    have hb := (h 0).1.mp hs
    omega
  · have hs : ∃ x : ℤ, (intervention 1).readout 1 () 1 = 2 * x ^ 2 := by
      refine ⟨0, ?_⟩
      norm_num [intervention, realize]
    have hb := (h 1).2.mp hs
    omega

def registration : Registration arena
    (∀ n : ℕ, (IsSquare (goldenLucas n) ↔ n = 1 ∨ n = 3) ∧
      ((∃ x : ℤ, goldenLucas n = 2 * x ^ 2) ↔ n = 0 ∨ n = 6)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lucas_square_classifications, rejected, rejected_law⟩
  sensitivity := by
    classical
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law_failure i⟩
      intro j hji
      funext p n
      change (j : Fin 2) ≠ (i : Fin 2) at hji
      simp only [actual, intervention, realize]
      exact (if_neg hji).symm
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas 0 ≠ goldenLucas 1
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.LucasSquareClassification.lucas_square_classifications) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => goldenLucas n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "LucasSquareClassification") "lucas_square_classifications") "Reg.D5.S3.Arith.Primes.LucasSquareClassification/Reg.D5.S3.Arith.Primes.LucasSquareClassification.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => goldenLucas n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.LucasSquareClassification, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "arg", "fn", "arg", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.LucasSquareClassification, declaration := `D5.S3.Arith.Primes.LucasSquareClassification.lucas_square_classifications, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observationFact1, `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.LucasSquareClassification


noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.LucasSquareClassification.arena
noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.LucasSquareClassification.arena
noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.LucasSquareClassification.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.LucasSquareClassification.arena
    (∀ (n : Nat),
      And
        (Iff (@IsSquare.{0} Int Int.instMul (D5.S1.Scale.goldenLucas n))
          (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
        (Iff
          (@Exists.{1} Int fun (x : Int) =>
            @Eq.{1} Int (D5.S1.Scale.goldenLucas n)
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                (@HPow.hPow.{0, 0, 0} Int Nat Int
                  (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) x
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
    Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration)

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"lucas_square_classifications\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.LucasSquareClassification, declaration := `D5.S3.Arith.Primes.LucasSquareClassification.lucas_square_classifications, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.LucasSquareClassification.arena
  (∀ (n : Nat),
    And
      (Iff (@IsSquare.{0} Int Int.instMul (D5.S1.Scale.goldenLucas n))
        (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
      (Iff
        (@Exists.{1} Int fun (x : Int) =>
          @Eq.{1} Int (D5.S1.Scale.goldenLucas n)
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) x
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
  Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration)

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) where
  values := [(fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
    (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))), (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
    (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observation0 : (n : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.LucasSquareClassification.signature
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
        (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    PUnit.unit.{1} :=
  fun (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.LucasSquareClassification.signature Reg.D5.S3.Arith.Primes.LucasSquareClassification.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
        (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"lucas_square_classifications\"],\"part\":\"type\",\"path\":[\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.LucasSquareClassification, declaration := `D5.S3.Arith.Primes.LucasSquareClassification.lucas_square_classifications, part := .type, path := [.body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observation1 : (n : Nat) →
  (x : Int) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.Primes.LucasSquareClassification.signature
      ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
        (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
          (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      PUnit.unit.{1} :=
  fun (n : Nat) (x : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.LucasSquareClassification.signature Reg.D5.S3.Arith.Primes.LucasSquareClassification.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"lucas_square_classifications\"],\"part\":\"type\",\"path\":[\"body\",\"argument\",\"function\",\"argument\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.LucasSquareClassification, declaration := `D5.S3.Arith.Primes.LucasSquareClassification.lucas_square_classifications, part := .type, path := [.body, .argument, .function, .argument, .argument, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"lucas_square_classifications\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.LucasSquareClassification, declaration := `D5.S3.Arith.Primes.LucasSquareClassification.lucas_square_classifications, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration).actual (Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration).variation.1 (Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"LucasSquareClassification\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.LucasSquareClassification, declaration := `Reg.D5.S3.Arith.Primes.LucasSquareClassification.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
