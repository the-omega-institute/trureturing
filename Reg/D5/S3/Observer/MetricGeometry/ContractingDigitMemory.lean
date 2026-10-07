import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.ContractingDigitMemory
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

open _root_.D5.S3.Observer.MetricGeometry.ContractingDigitMemory
open _root_.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
namespace Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve every original hypothesis and the full least-state assertion. -/
def arena : Arena where
  signature := signature
  Law obs := ∀ {lam eps : ℝ} (hlampos : 0 < lam) (hlamhalf : lam < 1 / 2)
    (L : ℕ) (_hL : 1 ≤ L)
    (_heps_lower : lam ^ L / 2 ≤ eps)
    (_heps_upper : eps < (1 - lam) * lam ^ (L - 1) / 2),
    IsLeast
      {s : ℕ |
        HasFinitePredictor
          (digitStep lam hlampos.le (by linarith))
          (fun x : DigitState lam => x.1) eps s}
      (obs.readout () () L)

theorem positiveLaw : arena.Law actual :=
  @contracting_digit_memory_exact

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (h (lam := 1/4) (eps := 1/8) (by norm_num) (by norm_num)
    1 (by norm_num) (by norm_num) (by norm_num)).1
  obtain ⟨S, finiteS, hne, hcard, _⟩ := hzero
  let : Fintype S := finiteS
  let : Nonempty S := hne
  have hpos := Fintype.card_pos (α := S)
  change Fintype.card S ≤ 0 at hcard
  omega

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (@Subsingleton.elim Unit _ j i)).elim
  · intro e; exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) :=
  Registration.mk actual Iff.rfl ⟨positiveLaw, rejected, rejected_law⟩ sensitivity dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.contracting_digit_memory_exact) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ t => 2 ^ t) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "MetricGeometry") "ContractingDigitMemory") "contracting_digit_memory_exact") "Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory/Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ t => 2 ^ t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory.contracting_digit_memory_exact, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.observationFact0, `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory


noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.arena
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.arena
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.arena) (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration).actual

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"contracting_digit_memory_exact\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory.contracting_digit_memory_exact, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration).bridge

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.observation0 : {lam eps : Real} →
  (hlampos :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lam) →
    (hlamhalf :
        @LT.lt.{0} Real Real.instLT lam
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
      (L : Nat) →
        (hL : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) L) →
          (heps_lower :
              @LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) lam L)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                eps) →
            (heps_upper :
                @LT.lt.{0} Real Real.instLT eps
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lam)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) lam
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun {lam eps : Real}
    (hlampos :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lam)
    (hlamhalf :
      @LT.lt.{0} Real Real.instLT lam
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (L : Nat) (hL : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) L)
    (heps_lower :
      @LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) lam L)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        eps)
    (heps_upper :
      @LT.lt.{0} Real Real.instLT eps
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lam)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) lam
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.signature
    Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.actual PUnit.unit.{1} PUnit.unit.{1} L

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"contracting_digit_memory_exact\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory.contracting_digit_memory_exact, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"contracting_digit_memory_exact\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory.contracting_digit_memory_exact, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration).actual (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration).variation.2.choose (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration).variation.1 (Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"MetricGeometry\",\"ContractingDigitMemory\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory, declaration := `Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
