import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.PrimeNumberTheorem.PntSmoothing
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open scoped ContDiff Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit


noncomputable section

namespace SmoothedChebyshevClose

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p C => C * p.2 * p.1 * Real.log p.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1),
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ r.readout () ⟨X, ε⟩ C

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, hd, hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨C, _hC, hh⟩ := h hd hs hn hm
  have hb := hh 4 (by norm_num) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  change ‖SmoothedChebyshev ν (3 / 4) 4 - ψ 4‖ ≤ (-1 : ℝ) at hb
  exact (not_le_of_gt (by linarith [norm_nonneg (SmoothedChebyshev ν (3 / 4) 4 - ψ 4)])) hb

def registration : Registration arena
    (∀ {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1),
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.SmoothedChebyshevClose, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨Real.exp 1, (1 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) * 1 * Real.exp 1 * Real.log (Real.exp 1) ≠
      1 * 1 * Real.exp 1 * Real.log (Real.exp 1)
    simp only [Real.log_exp, zero_mul, one_mul, mul_one]
    exact ne_of_lt (Real.exp_pos 1)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.SmoothedChebyshevClose) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p C => C * p.2 * p.1 * Real.log p.1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "SmoothedChebyshevClose") "Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing/Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p C => C * p.2 * p.1 * Real.log p.1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, definition := none, coordinates := #[6, 8], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `SmoothedChebyshevClose, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.anchorEnumeration }


end SmoothedChebyshevClose

end
end Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.arena) (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration).actual

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"SmoothedChebyshevClose\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `SmoothedChebyshevClose, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration).bridge

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.observation0 : {SmoothingF : Real → Real} →
  (diffSmoothingF :
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
        SmoothingF) →
    (suppSmoothingF :
        @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero SmoothingF)
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
      (SmoothingFnonneg :
          ∀ (x : Real),
            @GT.gt.{0} Real Real.instLT x (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (SmoothingF x)) →
        (mass_one :
            @Eq.{1} Real
              (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.Measure.restrict.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                  (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
                  (@Set.Ioi.{0} Real Real.instPreorder
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                fun (x : Real) =>
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (SmoothingF x) x)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          (C X : Real) →
            @LT.lt.{0} Real Real.instLT
                (@OfNat.ofNat.{0} Real (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                X →
              (ε : Real) →
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    ε →
                  @LT.lt.{0} Real Real.instLT ε
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                    @LT.lt.{0} Real Real.instLT
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) X ε) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                        Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.signature PUnit.unit.{1}
                        (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) X ε) :=
  fun {SmoothingF : Real → Real}
    (diffSmoothingF :
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
        SmoothingF)
    (suppSmoothingF :
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real) (@Function.support.{0, 0} Real Real Real.instZero SmoothingF)
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
    (SmoothingFnonneg :
      ∀ (x : Real),
        @GT.gt.{0} Real Real.instLT x (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (SmoothingF x))
    (mass_one :
      @Eq.{1} Real
        (@MeasureTheory.integral.{0, 0} Real Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.Measure.restrict.{0} Real
            (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
            (@Set.Ioi.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          fun (x : Real) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (SmoothingF x) x)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (C X : Real)
    (x :
      @LT.lt.{0} Real Real.instLT
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        X)
    (ε : Real)
    (x_1 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (x_2 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (x_3 :
      @LT.lt.{0} Real Real.instLT
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) X ε)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.signature
    Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) X ε) C

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"SmoothedChebyshevClose\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `SmoothedChebyshevClose, part := .type, path := [.body, .body, .body, .body, .body, .argument, .body, .argument, .body, .body, .body, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"SmoothedChebyshevClose\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `SmoothedChebyshevClose, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntSmoothing\",\"SmoothedChebyshevClose\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntSmoothing.SmoothedChebyshevClose.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
