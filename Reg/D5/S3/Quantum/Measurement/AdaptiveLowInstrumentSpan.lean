import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan
structure Model.{u,v} where
  a : Type u
  h : Type v
  finiteA : Fintype a
  decidableA : DecidableEq a
  nonemptyA : Nonempty a
  finiteH : Fintype h
  decidableH : DecidableEq h
  nonemptyH : Nonempty h
  clock : @CStarMatrix (a × h) (a × h) ℂ

@[reducible] def signature.{u,v} : Signature where
  Params := Model.{u,v}
  State p := @Event p.a p.finiteA p.decidableA
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := CStarMatrix (p.a × p.h) (p.a × p.h) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation.{u,v} (p : Model.{u,v})
    (e : @Event p.a p.finiteA p.decidableA) : CStarMatrix (p.a × p.h) (p.a × p.h) ℂ := by
  letI := p.finiteA
  letI := p.decidableA
  letI := p.finiteH
  letI := p.decidableH
  exact effect (tensorLow p.h) p.clock e

def actual.{u,v} : Realization signature.{u,v} :=
  realize signature (fun _ p e => observation p e) (fun e => nomatch e)

def rejected.{u,v} : Realization signature.{u,v} :=
  realize signature (fun _ p e => by
    letI := p.finiteA
    letI := p.decidableA
    letI := p.finiteH
    letI := p.decidableH
    exact observation p e + 1)
    (fun e => nomatch e)

def arena.{u,v} : Arena.{max (u+1) (v+1),u,0,max u v,0} where
  signature := signature.{u,v}
  Law R := ∀ {a : Type u} [Fintype a] [DecidableEq a]
    {h : Type v} [Fintype h] [DecidableEq h] [Nonempty a] [Nonempty h]
    (W : CStarMatrix (a × h) (a × h) ℂ)
    (_hW : star W * W = 1 ∧ W * star W = 1),
    let p : Model := ⟨a, h, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, W⟩
    (∀ e rho, Matrix.trace (eventState (tensorLow h) W e rho) =
      Matrix.trace (R.readout () p e * rho)) ∧
    (∀ e, 0 ≤ effect (tensorLow h) W e ∧ effect (tensorLow h) W e ≤ 1) ∧
    ∃ D : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ),
      D.toSubalgebra.toSubmodule = effectSpan (tensorLow h) W ∧
      (∀ K, tensorLow h K ∈ D) ∧
      (∀ X, X ∈ D ↔ star W * X * W ∈ D) ∧
      (∀ R : StarSubalgebra ℂ (CStarMatrix (a × h) (a × h) ℂ),
        (∀ K, tensorLow h K ∈ R) →
        (∀ X ∈ R, star W * X * W ∈ R) → D ≤ R)

theorem actual_law.{u,v} : arena.{u,v}.Law actual.{u,v} := by
  intro a _ _ h _ _ _ _ W hW
  exact actual_adaptive_span W hW

def singletonModel.{u,v} : Model.{u,v} :=
  { a := ULift.{u} (Fin 1)
    h := ULift.{v} (Fin 1)
    finiteA := inferInstance
    decidableA := inferInstance
    nonemptyA := inferInstance
    finiteH := inferInstance
    decidableH := inferInstance
    nonemptyH := inferInstance
    clock := 1 }

theorem rejected_law.{u,v} : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro hbad
  let W : CStarMatrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
    (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ := 1
  have hw : star W * W = 1 ∧ W * star W = 1 := by simp [W]
  have hz := (hbad (a := ULift.{u} (Fin 1)) (h := ULift.{v} (Fin 1)) W hw).1
    (.stop false) 1
  change Matrix.trace (0 : CStarMatrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
    (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) =
    Matrix.trace ((0 + 1) * 1 : CStarMatrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
      (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) at hz
  rw [zero_add, one_mul] at hz
  change Matrix.trace (0 : Matrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
    (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) =
    Matrix.trace (1 : Matrix (ULift.{u} (Fin 1) × ULift.{v} (Fin 1))
      (ULift.{u} (Fin 1) × ULift.{v} (Fin 1)) ℂ) at hz
  have hz0 : (0 : ℂ) = 1 := by
    simpa [Matrix.trace_one, Fintype.card_prod] using hz
  exact zero_ne_one hz0

theorem sensitivity.{u,v} : Sensitivity arena.{u,v} actual.{u,v} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro k hki
    cases i
    cases k
    exact (hki rfl).elim
  · intro i
    exact nomatch i

theorem dependence.{u,v} : ObservationalDependence signature.{u,v} actual.{u,v} := by
  letI := singletonModel.finiteA
  letI := singletonModel.decidableA
  letI := singletonModel.finiteH
  letI := singletonModel.decidableH
  intro i
  cases i
  refine ⟨singletonModel, .stop true, .stop false, ?_⟩
  change (1 : CStarMatrix (singletonModel.a × singletonModel.h)
    (singletonModel.a × singletonModel.h) ℂ) ≠ 0
  intro heq
  have he := congrFun (congrFun heq (⟨0⟩, ⟨0⟩)) (⟨0⟩, ⟨0⟩)
  norm_num [singletonModel, CStarMatrix] at he

def registration.{u,v} : Registration arena.{u,v} (arena.{u,v}.Law actual.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration_1.{u_1, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.actual_adaptive_span.{u_1, u_3}) (type_of% (realize.{max (u_3 + 1) (u_1 + 1), u_1, 0, max u_3 u_1, 0} signature.{u_1, u_3}
    (fun _ p e => observation.{u_1, u_3} p e) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "AdaptiveLowInstrumentSpan") "actual_adaptive_span") "Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan/Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_3}) ⟨(registration.{u_1, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_3 + 1) (u_1 + 1), u_1, 0, max u_3 u_1, 0} signature.{u_1, u_3}
    (fun _ p e => observation.{u_1, u_3} p e) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, definition := none, coordinates := #[0, 3, 8], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "arg", "fn", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.actual_adaptive_span, part := .type, path := [], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity
#print axioms dependence

end Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan


noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalArenaOperand.{u_1, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_3 + 1), u_1, 0, max u_1 u_3, 0} :=
  Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.arena.{u_1, u_3}
noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalArenaFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalObjectArenaOperand.{u_1, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_3 + 1), u_1, 0, max u_1 u_3, 0} :=
  Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.arena.{u_1, u_3}
noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalObjectArenaFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.sourceLaw.{u_1, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_3 + 1), u_1, 0, max u_1 u_3, 0} (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.arena.) (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration.{u_1, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.sourceBridgeFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"actual_adaptive_span\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.actual_adaptive_span, part := .type, path := [], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration.{u_1, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.observation0.{u_1, u_3} : {a : Type u_1} →
  [inst : Fintype.{u_1} a] →
    [inst_1 : DecidableEq.{u_1 + 1} a] →
      {h : Type u_3} →
        [inst_2 : Fintype.{u_3} h] →
          [inst_3 : DecidableEq.{u_3 + 1} h] →
            [inst_4 : Nonempty.{u_1 + 1} a] →
              [inst_5 : Nonempty.{u_3 + 1} h] →
                (W : CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex) →
                  (hW :
                      And
                        (@Eq.{max (u_1 + 1) (u_3 + 1)}
                          (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                            Complex)
                          (@HMul.hMul.{max u_1 u_3, max u_1 u_3, max u_1 u_3}
                            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (@CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid.{max u_1 u_3, max u_1 u_3, 0,
                                  max u_1 u_3}
                              (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex (Prod.{u_1, u_3} a h)
                              (@instFintypeProd.{u_1, u_3} a h inst inst_2) Complex.instMul Complex.instAddCommMonoid)
                            (@Star.star.{max u_1 u_3}
                              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                                Complex)
                              (@CStarMatrix.instStar.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                                (@InvolutiveStar.toStar.{0} Complex
                                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                    (@AddCommMonoid.toAddMonoid.{0} Complex
                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                              Complex.instNonUnitalCommRing)))))
                                    (@StarRing.toStarAddMonoid.{0} Complex
                                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                            Complex.instNonUnitalCommRing)))
                                      Complex.instStarRing))))
                              W)
                            W)
                          (@OfNat.ofNat.{max u_1 u_3}
                            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (nat_lit 1)
                            (@One.toOfNat1.{max u_1 u_3}
                              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                                Complex)
                              (@CStarMatrix.instOne.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                                (fun (a_1 b : Prod.{u_1, u_3} a h) =>
                                  @instDecidableEqProd.{u_1, u_3} a h inst_1 inst_3 a_1 b)
                                Complex.instZero Complex.instOne))))
                        (@Eq.{max (u_1 + 1) (u_3 + 1)}
                          (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                            Complex)
                          (@HMul.hMul.{max u_1 u_3, max u_1 u_3, max u_1 u_3}
                            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (@CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid.{max u_1 u_3, max u_1 u_3, 0,
                                  max u_1 u_3}
                              (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex (Prod.{u_1, u_3} a h)
                              (@instFintypeProd.{u_1, u_3} a h inst inst_2) Complex.instMul Complex.instAddCommMonoid)
                            W
                            (@Star.star.{max u_1 u_3}
                              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                                Complex)
                              (@CStarMatrix.instStar.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                                (@InvolutiveStar.toStar.{0} Complex
                                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                    (@AddCommMonoid.toAddMonoid.{0} Complex
                                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                              Complex.instNonUnitalCommRing)))))
                                    (@StarRing.toStarAddMonoid.{0} Complex
                                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                            Complex.instNonUnitalCommRing)))
                                      Complex.instStarRing))))
                              W))
                          (@OfNat.ofNat.{max u_1 u_3}
                            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                              Complex)
                            (nat_lit 1)
                            (@One.toOfNat1.{max u_1 u_3}
                              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                                Complex)
                              (@CStarMatrix.instOne.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                                (fun (a_1 b : Prod.{u_1, u_3} a h) =>
                                  @instDecidableEqProd.{u_1, u_3} a h inst_1 inst_3 a_1 b)
                                Complex.instZero Complex.instOne))))) →
                    (e : @D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.Event.{u_1} a inst inst_1) →
                      (rho :
                          CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h)
                            Complex) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1)
                              (u_3 + 1),
                            u_1, 0, max u_1 u_3, 0}
                          Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.signature.{u_1, u_3} PUnit.unit.{1}
                          (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.Model.mk.{u_1, u_3} a h inst inst_1
                            inst_4 inst_2 inst_3 inst_5 W) :=
  fun {a : Type u_1} [inst : Fintype.{u_1} a] [inst_1 : DecidableEq.{u_1 + 1} a] {h : Type u_3} [inst_2 : Fintype.{u_3} h]
    [inst_3 : DecidableEq.{u_3 + 1} h] [inst_4 : Nonempty.{u_1 + 1} a] [inst_5 : Nonempty.{u_3 + 1} h]
    (W : CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
    (hW :
      And
        (@Eq.{max (u_1 + 1) (u_3 + 1)}
          (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
          (@HMul.hMul.{max u_1 u_3, max u_1 u_3, max u_1 u_3}
            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
            (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
            (@CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid.{max u_1 u_3, max u_1 u_3, 0, max u_1 u_3}
              (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex (Prod.{u_1, u_3} a h)
              (@instFintypeProd.{u_1, u_3} a h inst inst_2) Complex.instMul Complex.instAddCommMonoid)
            (@Star.star.{max u_1 u_3}
              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
              (@CStarMatrix.instStar.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                (@InvolutiveStar.toStar.{0} Complex
                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                    (@AddCommMonoid.toAddMonoid.{0} Complex
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                              Complex.instNonUnitalCommRing)))))
                    (@StarRing.toStarAddMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing))))
              W)
            W)
          (@OfNat.ofNat.{max u_1 u_3}
            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex) (nat_lit 1)
            (@One.toOfNat1.{max u_1 u_3}
              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
              (@CStarMatrix.instOne.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                (fun (a_1 b : Prod.{u_1, u_3} a h) => @instDecidableEqProd.{u_1, u_3} a h inst_1 inst_3 a_1 b)
                Complex.instZero Complex.instOne))))
        (@Eq.{max (u_1 + 1) (u_3 + 1)}
          (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
          (@HMul.hMul.{max u_1 u_3, max u_1 u_3, max u_1 u_3}
            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
            (CStarMatrix.{max u_1 u_3, max u_1 u_3, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
            (@CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid.{max u_1 u_3, max u_1 u_3, 0, max u_1 u_3}
              (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex (Prod.{u_1, u_3} a h)
              (@instFintypeProd.{u_1, u_3} a h inst inst_2) Complex.instMul Complex.instAddCommMonoid)
            W
            (@Star.star.{max u_1 u_3}
              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
              (@CStarMatrix.instStar.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                (@InvolutiveStar.toStar.{0} Complex
                  (@StarAddMonoid.toInvolutiveStar.{0} Complex
                    (@AddCommMonoid.toAddMonoid.{0} Complex
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                              Complex.instNonUnitalCommRing)))))
                    (@StarRing.toStarAddMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing))))
              W))
          (@OfNat.ofNat.{max u_1 u_3}
            (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex) (nat_lit 1)
            (@One.toOfNat1.{max u_1 u_3}
              (CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex)
              (@CStarMatrix.instOne.{max u_1 u_3, 0} (Prod.{u_1, u_3} a h) Complex
                (fun (a_1 b : Prod.{u_1, u_3} a h) => @instDecidableEqProd.{u_1, u_3} a h inst_1 inst_3 a_1 b)
                Complex.instZero Complex.instOne)))))
    (e : @D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.Event.{u_1} a inst inst_1)
    (rho : CStarMatrix.{max u_3 u_1, max u_3 u_1, 0} (Prod.{u_1, u_3} a h) (Prod.{u_1, u_3} a h) Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_3 + 1), u_1, 0,
        max u_1 u_3, 0}
    Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.signature.{u_1, u_3}
    Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.actual.{u_1, u_3} PUnit.unit.{1}
    (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.Model.mk.{u_1, u_3} a h inst inst_1 inst_4 inst_2 inst_3
      inst_5 W)
    e

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.observationFact0.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"actual_adaptive_span\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.actual_adaptive_span, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .argument, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.varyingLawInput.{u_1, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.canonicalArenaOperand.{u_1, u_3})
noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.varyingLaw.{u_1, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.statementExclusion.{u_1, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"actual_adaptive_span\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.actual_adaptive_span, part := .type, path := [], levels := [(.param `u_1), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration.{u_1, u_3}).actual (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration.{u_1, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration.{u_1, u_3}).variation.1 (Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration.{u_1, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1.descriptorFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"AdaptiveLowInstrumentSpan\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan, declaration := `Reg.D5.S3.Quantum.Measurement.AdaptiveLowInstrumentSpan.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
