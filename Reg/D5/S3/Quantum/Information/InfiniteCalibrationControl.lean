import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl
open _root_.D5.S3.Quantum.Information.InfiniteCalibrationControl
open _root_.D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨k, hk⟩ := h (1/2) (1/100) (1/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) hk.1

def registration : Registration arena (∀ (a δ b : ℝ) (_ha : 0 < a) (_ha1 : a < 1)
    (_hδ : 0 < δ) (_hδL : δ < (1-a)/4) (_hδa : δ < (1-a^2)/16)
    (_hb : 0 < b) (_hbδ : b < 1 - a/(1-δ)), ∃ k : ℝ, InfiniteScalarControl a δ b k) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨(0 : ℝ), (0 : ℝ), (0 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) ≠ 1
    exact zero_ne_one

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Information.InfiniteCalibrationControl.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ k => k) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "InfiniteCalibrationControl") "result") "Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl/D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ k => k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.InfiniteCalibrationControl, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `D5.S3.Quantum.Information.InfiniteCalibrationControl.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.observationFact0, `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.anchorEnumeration }


end Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl


noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily.arena
noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily.arena
noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily.arena) (Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration).actual

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `D5.S3.Quantum.Information.InfiniteCalibrationControl.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.observation0 : (a δ b : Real) →
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a) →
    (ha1 : @LT.lt.{0} Real Real.instLT a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (hδ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ) →
        (hδL :
            @LT.lt.{0} Real Real.instLT δ
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) →
          (hδa :
              @LT.lt.{0} Real Real.instLT δ
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) a
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))) →
            (hb :
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  b) →
              (hbδ :
                  @LT.lt.{0} Real Real.instLT b
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) a
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) δ)))) →
                (k : Real) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily.signature PUnit.unit.{1}
                    (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) a
                      (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) δ b)) :=
  fun (a δ b : Real)
    (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
    (ha1 : @LT.lt.{0} Real Real.instLT a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (hδ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) δ)
    (hδL :
      @LT.lt.{0} Real Real.instLT δ
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
    (hδa :
      @LT.lt.{0} Real Real.instLT δ
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) a
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat.{0} Real (nat_lit 16)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
    (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
    (hbδ :
      @LT.lt.{0} Real Real.instLT b
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            a
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) δ))))
    (k : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily.signature
    D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) a
      (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) δ b))
    k

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `D5.S3.Quantum.Information.InfiniteCalibrationControl.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `D5.S3.Quantum.Information.InfiniteCalibrationControl.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration).actual (Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration).variation.2.choose (Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration).variation.1 (Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"InfiniteCalibrationControl\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl, declaration := `Reg.D5.S3.Quantum.Information.InfiniteCalibrationControl.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
