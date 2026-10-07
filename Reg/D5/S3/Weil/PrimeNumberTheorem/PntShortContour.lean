import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.PrimeNumberTheorem.PntShortContour
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open scoped ContDiff Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit


noncomputable section

theorem small_holomorphic_strip : ∃ σ₂ : ℝ,
    σ₂ ∈ Ioo 0 1 ∧ LogDerivZetaIsHoloSmall σ₂ := by
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  refine ⟨σ₂, ⟨σ₂_pos, σ₂_lt_one⟩, ?_⟩
  apply holo2'.mono
  intro s hs
  simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff,
    mem_reProdIm, mem_Icc, mem_singleton_iff] at hs ⊢
  refine ⟨?_, hs.2⟩
  refine ⟨?_, hs.1.2⟩
  rcases hs.1.1 with ⟨left, right⟩
  constructor
  · apply le_trans _ left
    apply min_le_min_right
    apply le_max_left
  · rw [max_eq_right (by linarith)] at right ⊢
    exact right

namespace I4Bound

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p C => C * p.2.1 * p.2.1 ^ (-p.1 / (Real.log p.2.2.2 ^ 9)) / p.2.2.1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)),
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ r.readout () ⟨A, X, ε, T⟩ C

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨σ₂, hσ₂, hholo⟩ := small_holomorphic_strip
  obtain ⟨C, _hC, Tlb, _hTlb, hh⟩ := h (SmoothingF := fun _ => 0) (by simp) contDiff_const
    hholo hσ₂ (A := 1 / 2) (by constructor <;> norm_num)
  have hb := hh 4 (by norm_num) (ε := 1 / 2) (by norm_num) (by norm_num)
    (T := Tlb + 1) (by linarith)
  change ‖I₄ (fun _ => 0) (1 / 2) 4 (1 - (1 / 2) / Real.log (Tlb + 1) ^ 9) σ₂‖ ≤ (-1 : ℝ) at hb
  exact (not_le_of_gt (by linarith [norm_nonneg (I₄ (fun _ => 0) (1 / 2) 4 (1 - (1 / 2) / Real.log (Tlb + 1) ^ 9) σ₂)])) hb

def registration : Registration arena
    (∀ {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)),
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.I4Bound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (4 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) * 1 * 1 ^ (-(0 : ℝ) / (Real.log 4 ^ 9)) / 1 ≠
      1 * 1 * 1 ^ (-(0 : ℝ) / (Real.log 4 ^ 9)) / 1
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.I4Bound) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p C => C * p.2.1 * p.2.1 ^ (-p.1 / (Real.log p.2.2.2 ^ 9)) / p.2.2.1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "I4Bound") "Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour/Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p C => C * p.2.1 * p.2.1 ^ (-p.1 / (Real.log p.2.2.2 ^ 9)) / p.2.2.1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.PrimeNumberTheorem.PntShortContour, definition := none, coordinates := #[6, 12, 14, 17], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `I4Bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.sourceBridgeFact, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.observationFact0, `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.anchorEnumeration }


end I4Bound

end
end Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.arena
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.arena) (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration).actual

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"I4Bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `I4Bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration).bridge

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.observation0 : {SmoothingF : Real → Real} →
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
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
    (ContDiffSmoothingF :
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
      {σ₂ : Real} →
        (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) →
          (hσ₂ :
              @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                (@Set.Ioo.{0} Real Real.instPreorder
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                σ₂) →
            {A : Real} →
              (hA :
                  @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                    (@Set.Ioc.{0} Real Real.instPreorder
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                    A) →
                (C : Real) →
                  @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
                    (Tlb : Real) →
                      @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          Tlb →
                        (X : Real) →
                          @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 3)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              X →
                            {ε : Real} →
                              @LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
                                @LT.lt.{0} Real Real.instLT ε
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                                  {T : Real} →
                                    @LT.lt.{0} Real Real.instLT Tlb T →
                                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0,
                                          0, 0}
                                        Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.signature
                                        PUnit.unit.{1}
                                        (@Sigma.mk.{0, 0} Real
                                          (fun (x : Real) =>
                                            @Sigma.{0, 0} Real fun (x : Real) =>
                                              @Sigma.{0, 0} Real fun (x : Real) => Real)
                                          A
                                          (@Sigma.mk.{0, 0} Real
                                            (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) X
                                            (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) ε T))) :=
  fun {SmoothingF : Real → Real}
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
    (ContDiffSmoothingF :
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
    {σ₂ : Real} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂)
    (hσ₂ :
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
        (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        σ₂)
    {A : Real}
    (hA :
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
        (@Set.Ioc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
        A)
    (C : Real)
    (x : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
    (Tlb : Real)
    (x_1 :
      @LT.lt.{0} Real Real.instLT
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        Tlb)
    (X : Real)
    (x_2 :
      @LT.lt.{0} Real Real.instLT
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        X)
    {ε : Real}
    (x_3 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (x_4 : @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    {T : Real} (x_5 : @LT.lt.{0} Real Real.instLT Tlb T) =>
  have σ₁ : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) A
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (Real.log T)
          (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))));
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.signature
    Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real
      (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) A
      (@Sigma.mk.{0, 0} Real (fun (x : Real) => @Sigma.{0, 0} Real fun (x : Real) => Real) X
        (@Sigma.mk.{0, 0} Real (fun (x : Real) => Real) ε T)))
    C

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"I4Bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `I4Bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"I4Bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `I4Bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration).actual (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration).variation.2.choose (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration).variation.1 (Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Weil\",\"PrimeNumberTheorem\",\"PntShortContour\",\"I4Bound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour, declaration := `Reg.D5.S3.Weil.PrimeNumberTheorem.PntShortContour.I4Bound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
