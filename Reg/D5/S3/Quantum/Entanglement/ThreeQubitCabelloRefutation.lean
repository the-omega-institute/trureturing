import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
open _root_.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 2 → Fin 2 → Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 2 → Fin 2 → Fin 2 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete negated claim; only the state in the hypothesis `GenuinelyEntangled ψ` is
replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ ∀ (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) (up um dp dm : Fin 3 → Fin 2 → ℂ),
    ∑ i, ∑ j, ∑ k, Complex.normSq (ψ i j k) = 1 → GenuinelyEntangled (O.readout () () ψ) →
    (∀ k, IsONB (up k) (um k)) → (∀ k, IsONB (dp k) (dm k)) →
    prob (dp 0) (up 1) (up 2) ψ = 0 → prob (up 0) (dp 1) (up 2) ψ = 0 →
    prob (up 0) (up 1) (dp 2) ψ = 0 → 0 < prob (dm 0) (dm 1) (dm 2) ψ →
    prob (up 0) (up 1) (up 2) ψ - prob (dm 0) (dm 1) (dm 2) ψ ≤ 9 / 64

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro ψ up um dp dm _ hent
  exact absurd ⟨fun _ => 0, fun _ _ => 0, fun _ _ _ => by change (0 : ℂ) = 0 * 0; simp⟩ hent.1

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), fun _ _ _ => 0, fun _ _ _ => 1, fun h => ?_⟩
  have := congrFun (congrFun (congrFun h 0) 0) 0
  change (0 : ℂ) = 1 at this
  exact zero_ne_one this

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ψ => ψ) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "ThreeQubitCabelloRefutation") "result") "Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation/Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ψ => ψ) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, definition := some { owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, name := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.claim, path := #["arg"] }, coordinates := #[], readouts := #[{ path := #["arg", "body", "body", "body", "body", "body", "body", "domain", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation


noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.arena) (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration).actual

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.observation0 : (ψ :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) →
  (up um dp dm :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) →
    @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real
          Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
          @Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real
            Real.instAddCommMonoid
            (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            fun (j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
            @Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real
              Real.instAddCommMonoid
              (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              fun (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
              @DFunLike.coe.{1, 1, 1}
                (@MonoidWithZeroHom.{0, 0} Complex Real
                  (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                  (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                Complex (fun (x : Complex) => Real)
                (@MonoidWithZeroHom.funLike.{0, 0} Complex Real
                  (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                  (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                Complex.normSq (ψ i j k))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun
    (ψ :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex)
    (up um dp dm :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex)
    (a :
      @Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real
          Real.instAddCommMonoid
          (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
          @Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real
            Real.instAddCommMonoid
            (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            fun (j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
            @Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real
              Real.instAddCommMonoid
              (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              fun (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
              @DFunLike.coe.{1, 1, 1}
                (@MonoidWithZeroHom.{0, 0} Complex Real
                  (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                  (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                Complex (fun (x : Complex) => Real)
                (@MonoidWithZeroHom.funLike.{0, 0} Complex Real
                  (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                  (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                Complex.normSq (ψ i j k))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.signature
    Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.actual PUnit.unit.{1} PUnit.unit.{1} ψ

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.claim, part := .value, path := [.body, .body, .body, .body, .body, .body, .domain, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration).actual (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration).variation.1 (Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"ThreeQubitCabelloRefutation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation, declaration := `Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
