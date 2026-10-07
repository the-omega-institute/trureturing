import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum.RealSqrt

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ (z : ℝ) => 1 + (z^2 - Real.sqrt (z^4 + 4))/2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def arena : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena where
  signature := signature
  Law r := ∀ (c h γ : ℝ) (_hc : 12/5 < c) (_hh0 : 0 < h)
    (_hh : h < 31/20) (_hγ : 0 < γ),
    let g : ℝ → ℝ := fun z => r.readout () () z
    let F := fun j : ℕ => fun z : ℝ => (c+(h-z)^2)/(1-γ*g z)^j
    let S := {z : ℝ | 0 ≤ z ∧ z ≤ h ∧ 0 < 1-γ*g z}
    ∃ z2 z1 : ℝ, 0 < z2 ∧ z2 < z1 ∧ z1 < h ∧ z2 ∈ S ∧ z1 ∈ S ∧
      (∀ z ∈ S, z ≠ z2 → F 2 z2 < F 2 z) ∧
      (∀ z ∈ S, z ≠ z1 → F 1 z1 < F 1 z)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a2, a1, _, horder, _, hm2, hm1, hmin2, hmin1⟩ :=
    h 3 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hleft := hmin2 a1 hm1 (ne_of_gt horder)
  have hright := hmin1 a2 hm2 (ne_of_lt horder)
  change (3+(1-a2)^2)/(1-1*0)^2 < (3+(1-a1)^2)/(1-1*0)^2 at hleft
  change (3+(1-a1)^2)/(1-1*0)^1 < (3+(1-a2)^2)/(1-1*0)^1 at hright
  norm_num at hleft hright
  linarith

def registration : Registration arena (∀ (c h γ : ℝ) (_hc : 12/5 < c)
    (_hh0 : 0 < h) (_hh : h < 31/20) (_hγ : 0 < γ),
    let g := fun z : ℝ => 1+(z^2-Real.sqrt (z^4+4))/2
    let F := fun j : ℕ => fun z : ℝ => (c+(h-z)^2)/(1-γ*g z)^j
    let S := {z : ℝ | 0 ≤ z ∧ z ≤ h ∧ 0 < 1-γ*g z}
    ∃ z2 z1 : ℝ, 0 < z2 ∧ z2 < z1 ∧ z1 < h ∧ z2 ∈ S ∧ z1 ∈ S ∧
      (∀ z ∈ S, z ≠ z2 → F 2 z2 < F 2 z) ∧
      (∀ z ∈ S, z ≠ z1 → F 1 z1 < F 1 z)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change (1 : ℝ)+(0^2-Real.sqrt (0^4+4))/2 ≠ 1+(1^2-Real.sqrt (1^4+4))/2
    norm_num
    have hs := Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)
    intro he
    have heR : (1 : ℝ) + -1 = 1+(1-Real.sqrt 5)/2 := he
    have heq : Real.sqrt 5 = (3 : ℝ) := by linarith only [heR]
    rw [heq] at hs
    norm_num at hs

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (z : ℝ) => 1 + (z^2 - Real.sqrt (z^4 + 4))/2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "StationaryPreparation") "CrossoverUniqueMinima") "result") "Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima/Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ (z : ℝ) => 1 + (z^2 - Real.sqrt (z^4 + 4))/2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "value", "body"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.observationFact0, `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.anchorEnumeration }


end

end Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima


noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.arena
noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.arena
noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.arena
    (∀ (c h γ : Real)
      (_hc :
        @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 12)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
          c)
      (_hh0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
      (_hh :
        @LT.lt.{0} Real Real.instLT h
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 31)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 31) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 20)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))))
      (_hγ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ),
      have g : (z : Real) → Real := fun (z : Real) =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Real.sqrt
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))));
      have F : (j : Nat) → (z : Real) → Real := fun (j : Nat) (z : Real) =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) c
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) h z)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) γ (g z)))
            j);
      have S : Set.{0} Real :=
        @Set.ofPred.{0} Real fun (z : Real) =>
          And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
            (And (@LE.le.{0} Real Real.instLE z h)
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) γ (g z)))));
      @Exists.{1} Real fun (z2 : Real) =>
        @Exists.{1} Real fun (z1 : Real) =>
          And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z2)
            (And (@LT.lt.{0} Real Real.instLT z2 z1)
              (And (@LT.lt.{0} Real Real.instLT z1 h)
                (And (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z2)
                  (And (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z1)
                    (And
                      (∀ (z : Real),
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z →
                          @Ne.{1} Real z z2 →
                            @LT.lt.{0} Real Real.instLT
                              (F (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) z2)
                              (F (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) z))
                      (∀ (z : Real),
                        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z →
                          @Ne.{1} Real z z1 →
                            @LT.lt.{0} Real Real.instLT
                              (F (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) z1)
                              (F (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) z))))))))
    Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration)

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.arena
  (∀ (c h γ : Real)
    (_hc :
      @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 12)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
        c)
    (_hh0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
    (_hh :
      @LT.lt.{0} Real Real.instLT h
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 31)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 31) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 20)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))))
    (_hγ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ),
    have g : (z : Real) → Real := fun (z : Real) =>
      @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Real.sqrt
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))));
    have F : (j : Nat) → (z : Real) → Real := fun (j : Nat) (z : Real) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) c
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) h z)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) γ (g z)))
          j);
    have S : Set.{0} Real :=
      @Set.ofPred.{0} Real fun (z : Real) =>
        And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
          (And (@LE.le.{0} Real Real.instLE z h)
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) γ (g z)))));
    @Exists.{1} Real fun (z2 : Real) =>
      @Exists.{1} Real fun (z1 : Real) =>
        And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z2)
          (And (@LT.lt.{0} Real Real.instLT z2 z1)
            (And (@LT.lt.{0} Real Real.instLT z1 h)
              (And (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z2)
                (And (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z1)
                  (And
                    (∀ (z : Real),
                      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z →
                        @Ne.{1} Real z z2 →
                          @LT.lt.{0} Real Real.instLT
                            (F (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) z2)
                            (F (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) z))
                    (∀ (z : Real),
                      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real) S z →
                        @Ne.{1} Real z z1 →
                          @LT.lt.{0} Real Real.instLT
                            (F (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) z1)
                            (F (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) z))))))))
  Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration)

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.observation0 : (c h γ : Real) →
  (hc :
      @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 12)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
        c) →
    (hh0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h) →
      (hh :
          @LT.lt.{0} Real Real.instLT h
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 31)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 31) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 20)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))) →
        (hγ :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ) →
          (z : Real) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (c h γ : Real)
    (hc :
      @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 12)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
        c)
    (hh0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h)
    (hh :
      @LT.lt.{0} Real Real.instLT h
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 31)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 31) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 20)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))))
    (hγ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ)
    (z : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.signature
    Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.actual PUnit.unit.{1} PUnit.unit.{1} z

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letValue\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .letValue, .body], levels := [] }
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration).actual (Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration).variation.2.choose (Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration).variation.1 (Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"StationaryPreparation\",\"CrossoverUniqueMinima\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima, declaration := `Reg.D5.S3.Quantum.StationaryPreparation.CrossoverUniqueMinima.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
