import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.PrimeNumberTheorem.MellinCalculus
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus

open Set Function Filter Complex Real MeasureTheory
open scoped ContDiff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ν s => ‖mellin (fun x => (ν x : ℂ)) s‖)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => s.im ^ 2 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2),
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
      r.readout () ν s ≤ C * ‖s‖⁻¹

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, hC, bound⟩ := h (ν := fun _ => 0) contDiff_const (by simp)
  let s : ℂ := 1 + (C + 1) * Complex.I
  have hre : s.re = 1 := by norm_num [s]
  have him : s.im = C + 1 := by norm_num [s]
  have hs : (1 : ℝ) ≤ ‖s‖ := by
    rw [← hre]
    exact Complex.re_le_norm s
  have hb := bound 1 (by norm_num) s (by rw [hre]) (by rw [hre]; norm_num)
  change s.im ^ 2 + 1 ≤ C * ‖s‖⁻¹ at hb
  have hright : C * ‖s‖⁻¹ ≤ C := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hs) hC.le
  rw [him] at hb
  have hbad := hb.trans hright
  nlinarith [sq_nonneg C]

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (suppν : ν.support ⊆ Set.Icc (1 / 2) 2),
      ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
        ‖mellin (fun x => (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.MellinOfPsi, rejected, rejected_law⟩
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
    let ν : ℝ → ℝ := (Set.Ioc (0 : ℝ) 1).indicator fun _ => 1
    refine ⟨ν, (1 : ℂ), (2 : ℂ), ?_⟩
    change ‖mellin (fun x => (ν x : ℂ)) 1‖ ≠
      ‖mellin (fun x => (ν x : ℂ)) 2‖
    have hcast : (fun x => (ν x : ℂ)) =
        (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1 <;>
        simp [ν, Set.indicator_apply, hx]
    rw [hcast]
    have h1 := (hasMellin_one_Ioc (s := (1 : ℂ)) (by norm_num)).2
    have h2 := (hasMellin_one_Ioc (s := (2 : ℂ)) (by norm_num)).2
    rw [h1, h2]
    norm_num [norm_div]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.MellinOfPsi) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ ν s => ‖mellin.{0} (fun x => (ν x : ℂ)) s‖) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "MellinOfPsi") "Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus/Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration,
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
    (fun _ ν s => ‖mellin.{0} (fun x => (ν x : ℂ)) s‖) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `MellinOfPsi, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.anchorEnumeration }


end

end Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.arena
    (∀ {ν : Real → Real}
      (diffν :
        @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
          Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
            (@One.toOfNat1.{0} (WithTop.{0} ENat)
              (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
          ν)
      (suppν :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
          (@Set.Icc.{0} Real Real.instPreorder
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))),
      @Exists.{1} Real fun (C : Real) =>
        And (@GT.gt.{0} Real Real.instLT C (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (∀ (σ₁ : Real),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) σ₁ →
              ∀ (s : Complex),
                @LE.le.{0} Real Real.instLE σ₁ (Complex.re s) →
                  @LE.le.{0} Real Real.instLE (Complex.re s)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
                    @LE.le.{0} Real Real.instLE
                      (@Norm.norm.{0} Complex Complex.instNorm
                        (@mellin.{0} Complex Complex.instNormedAddCommGroup
                          (@InnerProductSpace.toNormedSpace.{0, 0} Complex Complex Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                            (@RCLike.innerProductSpace.{0} Complex Complex.instRCLike))
                          (fun (x : Real) => Complex.ofReal (ν x)) s))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                        (@Inv.inv.{0} Real Real.instInv (@Norm.norm.{0} Complex Complex.instNorm s)))))
    Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"MellinOfPsi\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `MellinOfPsi, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.arena
  (∀ {ν : Real → Real}
    (diffν :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        ν)
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))),
    @Exists.{1} Real fun (C : Real) =>
      And (@GT.gt.{0} Real Real.instLT C (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (∀ (σ₁ : Real),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) σ₁ →
            ∀ (s : Complex),
              @LE.le.{0} Real Real.instLE σ₁ (Complex.re s) →
                @LE.le.{0} Real Real.instLE (Complex.re s)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
                  @LE.le.{0} Real Real.instLE
                    (@Norm.norm.{0} Complex Complex.instNorm
                      (@mellin.{0} Complex Complex.instNormedAddCommGroup
                        (@InnerProductSpace.toNormedSpace.{0, 0} Complex Complex Complex.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Complex Complex.instNormedAddCommGroup)
                          (@RCLike.innerProductSpace.{0} Complex Complex.instRCLike))
                        (fun (x : Real) => Complex.ofReal (ν x)) s))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                      (@Inv.inv.{0} Real Real.instInv (@Norm.norm.{0} Complex Complex.instNorm s)))))
  Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration)

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.observation0 : {ν : Real → Real} →
  (diffν :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        ν) →
    (suppν :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
          (@Set.Icc.{0} Real Real.instPreorder
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
      (C σ₁ : Real) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) σ₁ →
          (s : Complex) →
            @LE.le.{0} Real Real.instLE σ₁ (Complex.re s) →
              @LE.le.{0} Real Real.instLE (Complex.re s)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.signature PUnit.unit.{1} ν :=
  fun {ν : Real → Real}
    (diffν :
      @ContDiff.{0, 0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@OfNat.ofNat.{0} (WithTop.{0} ENat) (nat_lit 1)
          (@One.toOfNat1.{0} (WithTop.{0} ENat)
            (@WithTop.one.{0} ENat (@AddMonoidWithOne.toOne.{0} ENat instAddMonoidWithOneENat))))
        ν)
    (suppν :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero ν)
        (@Set.Icc.{0} Real Real.instPreorder
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (C σ₁ : Real)
    (x : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) σ₁)
    (s : Complex) (x_1 : @LE.le.{0} Real Real.instLE σ₁ (Complex.re s))
    (x_2 :
      @LE.le.{0} Real Real.instLE (Complex.re s)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.signature Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.actual
    PUnit.unit.{1} ν s

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"MellinOfPsi\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `MellinOfPsi, part := .type, path := [.body, .body, .body, .argument, .body, .argument, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"MellinOfPsi\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `MellinOfPsi, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"MellinCalculus\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
