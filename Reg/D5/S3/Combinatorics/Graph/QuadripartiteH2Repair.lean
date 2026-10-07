import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
open _root_.D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
open _root_.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair

abbrev geodesicSignature : Signature where
  Params := Cube
  State _ := Cube
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Cochain
  Anchor := Empty
  finiteAnchor := inferInstance

def geodesicActual : Realization geodesicSignature :=
  realize geodesicSignature (fun _ x y => geodesic x y) (fun e => nomatch e)

def geodesicRejected : Realization geodesicSignature :=
  realize geodesicSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev boundaryArena : Arena where
  signature := geodesicSignature
  Law r := ∀ x y b : Cube,
    d2 (r.readout () x y) b =
      (if b = x then 1 else 0) + (if b = y then 1 else 0)

private def x0 : Cube := (false, false, false, false)
private def y1 : Cube := (true, false, false, false)

theorem boundaryRejected_law : ¬ boundaryArena.Law geodesicRejected := by
  intro h
  have hb := h x0 y1 x0
  have hn : ¬ (d2 (0 : Cochain) x0 =
      (if x0 = x0 then 1 else 0) + (if x0 = y1 then 1 else 0)) := by decide
  exact hn hb

theorem geodesicDependence : ObservationalDependence geodesicSignature geodesicActual := by
  intro ⟨⟩
  refine ⟨x0, x0, y1, ?_⟩
  intro h
  have hw := congrArg weight h
  have hn : weight (geodesic x0 x0) ≠ weight (geodesic x0 y1) := by
    rw [geodesic_weight, geodesic_weight]
    decide
  exact hn hw

def boundaryRegistration : Registration boundaryArena
    (∀ x y b : Cube, d2 (geodesic x y) b =
      (if b = x then 1 else 0) + (if b = y then 1 else 0)) where
  actual := geodesicActual
  bridge := Iff.rfl
  variation := ⟨geodesic_boundary, geodesicRejected, boundaryRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨geodesicRejected, ?_, rfl, boundaryRejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := geodesicDependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic_boundary) (type_of% (realize.{0, 0, 0, 0, 0} geodesicSignature (fun _ x y => geodesic x y) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "Graph") "QuadripartiteH2Repair") "geodesic_boundary") "Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair/Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(boundaryArena)⟩,
  objectArena := .source ⟨(boundaryArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (boundaryArena) ⟨(boundaryRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} geodesicSignature (fun _ x y => geodesic x y) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic_boundary, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.anchorEnumeration }


end Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair


noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryArena
noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryArena
noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryArena
    (∀ (x y b : D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube),
      @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.d2
          (D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic x y) b)
        (@HAdd.hAdd.{0, 0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@instHAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Semifield.toDivisionSemiring.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        Nat.fact_prime_two)))))))
          (@ite.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Eq.{1} D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube b x)
            (@instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) instDecidableEqBool
              (fun (a b : Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) =>
                @instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool Bool) instDecidableEqBool
                  (fun (a b : Prod.{0, 0} Bool Bool) =>
                    @instDecidableEqProd.{0, 0} Bool Bool instDecidableEqBool instDecidableEqBool a b)
                  a b)
              b x)
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
              (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two))))))))
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
              (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))))
          (@ite.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Eq.{1} D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube b y)
            (@instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) instDecidableEqBool
              (fun (a b : Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) =>
                @instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool Bool) instDecidableEqBool
                  (fun (a b : Prod.{0, 0} Bool Bool) =>
                    @instDecidableEqProd.{0, 0} Bool Bool instDecidableEqBool instDecidableEqBool a b)
                  a b)
              b y)
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
              (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two))))))))
            (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
              (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))))))
    Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"geodesic_boundary\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic_boundary, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryArena
  (∀ (x y b : D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube),
    @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.d2
        (D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic x y) b)
      (@HAdd.hAdd.{0, 0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@instHAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      Nat.fact_prime_two)))))))
        (@ite.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Eq.{1} D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube b x)
          (@instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) instDecidableEqBool
            (fun (a b : Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) =>
              @instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool Bool) instDecidableEqBool
                (fun (a b : Prod.{0, 0} Bool Bool) =>
                  @instDecidableEqProd.{0, 0} Bool Bool instDecidableEqBool instDecidableEqBool a b)
                a b)
            b x)
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
            (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two))))))))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two)))))))))
        (@ite.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Eq.{1} D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube b y)
          (@instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) instDecidableEqBool
            (fun (a b : Prod.{0, 0} Bool (Prod.{0, 0} Bool Bool)) =>
              @instDecidableEqProd.{0, 0} Bool (Prod.{0, 0} Bool Bool) instDecidableEqBool
                (fun (a b : Prod.{0, 0} Bool Bool) =>
                  @instDecidableEqProd.{0, 0} Bool Bool instDecidableEqBool instDecidableEqBool a b)
                a b)
            b y)
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
            (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two))))))))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two)))))))))))
  Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.observation0 : (x y b : D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
      Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesicSignature x →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesicSignature PUnit.unit.{1} x :=
  fun (x y b : D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.Cube) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesicSignature
    Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesicActual PUnit.unit.{1} x

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"geodesic_boundary\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic_boundary, part := .type, path := [.body, .body, .body, .function, .argument, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"geodesic_boundary\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic_boundary, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration).actual (Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration).variation.2.choose (Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration).variation.1 (Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"QuadripartiteH2Repair\",\"boundaryRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
