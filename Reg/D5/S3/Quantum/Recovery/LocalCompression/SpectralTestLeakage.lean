import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage

/-! Source-bound observations of trace-norm error and the finite-test error budget. -/

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.Quantum.Foundation
open _root_.Matrix RHLinalg LeanInformationAudit
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

universe u v z

private theorem zero_traceNorm {n : Type*} [Fintype n] :
    FiniteTraceDistance.traceNorm (0 : Matrix n n ℂ) = 0 := by
  simp [FiniteTraceDistance.traceNorm]

private theorem emptyKraus_tp {n κ : Type*} [Fintype n] [Fintype κ]
    [IsEmpty n] [IsEmpty κ] :
    (MatrixMap.of_kraus (fun a : κ => nomatch IsEmpty.false a)
      (fun a : κ => nomatch IsEmpty.false a) : MatrixMap n n ℂ).IsTracePreserving := by
  intro X
  simp [Matrix.trace]

namespace TraceReadout

private abbrev signature : Signature where
  Params := Σ n : Type u, Fintype n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p X => @FiniteTraceDistance.traceNorm _ _ ℂ p.2 p.2 _ X) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let n := ULift.{u} Unit
  refine ⟨⟨n, inferInstance⟩, 0, 1, ?_⟩
  change FiniteTraceDistance.traceNorm (0 : Matrix n n ℂ) ≠ FiniteTraceDistance.traceNorm (1 : Matrix n n ℂ)
  have h1 := congrArg Complex.re (FiniteTraceDistance.traceNorm_of_posSemidef
    (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef))
  have hnorm : FiniteTraceDistance.traceNorm (1 : Matrix n n ℂ) = 1 := by simpa [n] using h1
  rw [zero_traceNorm, hnorm]
  exact zero_ne_one

private abbrev asymmetricArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {κ : Type v} [Fintype n] [DecidableEq n] [Fintype κ]
    (K : κ → Matrix n n ℂ) (_hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (gPos gNeg : ℝ)
    (_hgap : ∀ i, gPos ≤ hH.eigenvalues i ∨ hH.eigenvalues i ≤ -gNeg)
    (_hgPos : 0 < gPos) (_hgNeg : 0 < gNeg),
    let P := positiveSpectralProjection hH
    2 * (gPos * (∑ a, frobSq ((1 - P) * K a * P)) +
      gNeg * (∑ a, frobSq (P * K a * (1 - P)))) ≤
      R.readout () ⟨n, inferInstance⟩ (H - MatrixMap.of_kraus K K H)

private theorem asymmetric_rejected : ¬ asymmetricArena.{u,v}.Law rejected := by
  intro h
  have hbad := h (n := ULift.{u} Empty) (κ := ULift.{v} Empty)
    (fun a => nomatch IsEmpty.false a) emptyKraus_tp
    (H := 0) isHermitian_zero 1 1 (fun i => nomatch IsEmpty.false i)
    (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hbad

def asymmetricFamily : Registration asymmetricArena.{u,v}
    (type_of% @spectral_test_leakage_asymmetric.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_test_leakage_asymmetric.{u,v}, rejected, asymmetric_rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, asymmetric_rejected⟩
      intro other h
      exact (h (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def asymmetricRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@spectral_test_leakage_asymmetric.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage.spectral_test_leakage_asymmetric.__information_unit
  realizationName := ``asymmetricFamily
  realizationSource := none
  generated := false
  arena := .source ⟨asymmetricArena.{u,v}⟩
  objectArena := .source ⟨asymmetricArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source asymmetricArena.{u,v} ⟨asymmetricFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p X => @FiniteTraceDistance.traceNorm _ _ ℂ p.2 p.2 _ X)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev symmetricArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {κ : Type v} [Fintype n] [DecidableEq n] [Fintype κ]
    (K : κ → Matrix n n ℂ) (_hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (g : ℝ)
    (_hgap : ∀ i, g ≤ hH.eigenvalues i ∨ hH.eigenvalues i ≤ -g) (_hg : 0 < g),
    2 * g * (∑ a, frobSq ⁅positiveSpectralProjection hH, K a⁆) ≤
      R.readout () ⟨n, inferInstance⟩ (H - MatrixMap.of_kraus K K H)

private theorem symmetric_rejected : ¬ symmetricArena.{u,v}.Law rejected := by
  intro h
  have hbad := h (n := ULift.{u} Empty) (κ := ULift.{v} Empty)
    (fun a => nomatch IsEmpty.false a) emptyKraus_tp
    (H := 0) isHermitian_zero 1 (fun i => nomatch IsEmpty.false i) (by norm_num)
  norm_num [rejected, realize] at hbad

def symmetricFamily : Registration symmetricArena.{u,v}
    (type_of% @spectral_test_leakage.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_test_leakage.{u,v}, rejected, symmetric_rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, symmetric_rejected⟩
      intro other h
      exact (h (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def symmetricRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@spectral_test_leakage.{u,v}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage.spectral_test_leakage.__information_unit
  realizationName := ``symmetricFamily
  realizationSource := none
  generated := false
  arena := .source ⟨symmetricArena.{u,v}⟩
  objectArena := .source ⟨symmetricArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source symmetricArena.{u,v} ⟨symmetricFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p X => @FiniteTraceDistance.traceNorm _ _ ℂ p.2 p.2 _ X)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TraceReadout

namespace TestBudget

private abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ c δ => c * δ) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {κ : Type v} [Fintype n] [DecidableEq n] [Fintype κ]
    {ι : Type z} [Fintype ι]
    (K : κ → Matrix n n ℂ) (_hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    (ρ : ι → Matrix n n ℂ) (σ : Matrix n n ℂ) (t g w : ι → ℝ) (δ : ℝ)
    (hH : ∀ j, (ρ j - (t j : ℂ) • σ).IsHermitian)
    (_hg : ∀ j, 0 < g j) (_ht : ∀ j, 0 ≤ t j) (_hw : ∀ j, 0 ≤ w j)
    (_hgap : ∀ j i, g j ≤ (hH j).eigenvalues i ∨ (hH j).eigenvalues i ≤ -g j)
    (_hρ : ∀ j, FiniteTraceDistance.traceNorm (ρ j - MatrixMap.of_kraus K K (ρ j)) ≤ δ)
    (_hσ : FiniteTraceDistance.traceNorm (σ - MatrixMap.of_kraus K K σ) ≤ δ),
    (∑ j, w j * ∑ a, frobSq ⁅positiveSpectralProjection (hH j), K a⁆) ≤
      R.readout () () (∑ j, w j * (1 + t j) / (2 * g j)) δ

private theorem rejected_law : ¬ arena.{u,v,z}.Law rejected := by
  intro h
  let n := ULift.{u} Empty
  let κ := ULift.{v} Empty
  let K : κ → Matrix n n ℂ := fun a => nomatch IsEmpty.false a
  have hz : FiniteTraceDistance.traceNorm ((0 : Matrix n n ℂ) - MatrixMap.of_kraus K K 0) ≤ 0 := by
    rw [map_zero, sub_zero, zero_traceNorm]
  have hbad := h (ι := ULift.{z} Empty) K emptyKraus_tp
    (fun j => nomatch IsEmpty.false j) 0 (fun _ => 0) (fun _ => 1) (fun _ => 1) 0
    (fun j => nomatch IsEmpty.false j) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun j => nomatch IsEmpty.false j)
    (fun j => nomatch IsEmpty.false j) hz
  norm_num [rejected, realize] at hbad

def family : Registration arena.{u,v,z} (type_of% @finite_test_commutator_bound.{u,v,z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_test_commutator_bound.{u,v,z}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h1 := congrFun h 1
    norm_num [actual, realize] at h1

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_test_commutator_bound.{u,v,z}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage.finite_test_commutator_bound.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,z}⟩
  objectArena := .source ⟨arena.{u,v,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c δ => c * δ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TestBudget

end

end Reg.D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
