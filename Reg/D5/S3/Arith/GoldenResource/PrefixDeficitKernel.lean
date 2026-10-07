import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel

open Real Set MeasureTheory
open _root_.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The deficit is the observation; the original kernel and all hypotheses remain fixed. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a : ℕ) (z : ℝ), 1 ≤ a → 0 < z → z < 1 →
    IntervalIntegrable (fun t : ℝ => t ^ a * P a t / S a t) volume 0 z ∧
    r.readout () a z = (∫ t in (0 : ℝ)..z, t ^ a * P a t / S a t) ∧
    (a : ℝ) * z ^ (a + 1) / (((a : ℝ) + 1) * (1 + z)) ≤ r.readout () a z ∧
    r.readout () a z ≤ (a : ℝ) * z ^ (a + 1) / ((a : ℝ) + 1)

def actual : Realization signature :=
  realize signature (fun _ a z => D a z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 (1 / 2) (by decide) (by norm_num) (by norm_num)).2.2.1
  norm_num [rejected, realize] at hh

def registration : Registration arena
    (∀ (a : ℕ) (z : ℝ), 1 ≤ a → 0 < z → z < 1 →
      IntervalIntegrable (fun t : ℝ => t ^ a * P a t / S a t) volume 0 z ∧
      D a z = (∫ t in (0 : ℝ)..z, t ^ a * P a t / S a t) ∧
      (a : ℝ) * z ^ (a + 1) / (((a : ℝ) + 1) * (1 + z)) ≤ D a z ∧
      D a z ≤ (a : ℝ) * z ^ (a + 1) / ((a : ℝ) + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1 / 2, ?_⟩
    change D 1 0 ≠ D 1 (1 / 2)
    have hzero : D 1 0 = 0 := by simp [D, Q, S]
    rw [hzero]
    have hh := (result 1 (1 / 2) (by decide) (by norm_num) (by norm_num)).2.2.1
    norm_num at hh
    exact ne_of_lt (by linarith)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ a z => D a z) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "GoldenResource") "PrefixDeficitKernel") "result") "Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel/Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ a z => D a z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.observationFact0, `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel


noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.arena
noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.arena
noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.arena
    (∀ (a : Nat) (z : Real),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z →
          @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            And
              (@IntervalIntegrable.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@NormedAddGroup.toENormedAddMonoid.{0} Real
                  (@NormedAddCommGroup.toNormedAddGroup.{0} Real Real.normedAddCommGroup))
                (fun (t : Real) =>
                  @HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t
                        a)
                      (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.P a t))
                    (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.S a t))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
              (And
                (@Eq.{1} Real (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.D a z)
                  (@intervalIntegral.{0} Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    (fun (t : Real) =>
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            t a)
                          (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.P a t))
                        (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.S a t))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
                (And
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast a)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast a)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) z)))
                    (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.D a z))
                  (@LE.le.{0} Real Real.instLE (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.D a z)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast a)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Nat.cast.{0} Real Real.instNatCast a)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))))
    Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration)

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.arena
  (∀ (a : Nat) (z : Real),
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z →
        @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
          And
            (@IntervalIntegrable.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@NormedAddGroup.toENormedAddMonoid.{0} Real
                (@NormedAddCommGroup.toNormedAddGroup.{0} Real Real.normedAddCommGroup))
              (fun (t : Real) =>
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t a)
                    (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.P a t))
                  (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.S a t))
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
            (And
              (@Eq.{1} Real (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.D a z)
                (@intervalIntegral.{0} Real Real.normedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                  (fun (t : Real) =>
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) t
                          a)
                        (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.P a t))
                      (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.S a t))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
              (And
                (@LE.le.{0} Real Real.instLE
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast a)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Nat.cast.{0} Real Real.instNatCast a)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) z)))
                  (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.D a z))
                (@LE.le.{0} Real Real.instLE (D5.S3.Arith.GoldenResource.PrefixDeficitKernel.D a z)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast a)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@Nat.cast.{0} Real Real.instNatCast a)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))))
  Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration)

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.observation0 : (a : Nat) →
  (z : Real) →
    (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a) →
      (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z) →
        (hz1 :
            @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.signature PUnit.unit.{1} a :=
  fun (a : Nat) (z : Real) (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
    (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
    (hz1 : @LT.lt.{0} Real Real.instLT z (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.signature
    Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.actual PUnit.unit.{1} a z

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result, part := .type, path := [.body, .body, .body, .body, .body, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration).actual (Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration).variation.2.choose (Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration).variation.1 (Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"PrefixDeficitKernel\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel, declaration := `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
