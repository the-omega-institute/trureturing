import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion
open _root_.D5.S3.Constants.NewtonHankelRealRootCriterion
open _root_.D5.S3.Weil.ZeroSum _root_.D5.S3.Weil.Convention
open Omega.CosineScaleJet
open scoped ComplexConjugate

abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e)

def rejected (i : Fin 2) : Realization signature :=
  realize signature (fun j _ M => if j = i then False else M.PosSemidef)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (rho : Fin d → ℂ) (t : ℝ) (_ht : t ≠ 0)
    (_hconj : ∀ w, w ∈ Finset.univ.image rho ↔ conj w ∈ Finset.univ.image rho),
    (r.readout 0 d (newtonHankel (fun j => value ((t : ℂ) * spectralParameter (rho j)))) ∧
      r.readout 1 d (newtonHankel (fun j => scaleJet ((t : ℂ) * spectralParameter (rho j))))) ↔
      ∀ j, (rho j).re = criticalAbscissa ∨ (rho j).im = 0

private theorem actual_law : arena.Law actual :=
  @cosine_jet_hankel_iff_critical_or_real

private theorem rejected_law (i : Fin 2) : ¬ arena.Law (rejected i) := by
  intro hall
  have hc : ∀ w, w ∈ Finset.univ.image (fun _ : Fin 1 => (0 : ℂ)) ↔
      conj w ∈ Finset.univ.image (fun _ : Fin 1 => (0 : ℂ)) := by
    intro w
    simp
  have h := (hall (fun _ : Fin 1 => (0 : ℂ)) 1 (by norm_num) hc).mpr
    (fun _ => Or.inr rfl)
  fin_cases i
  · simpa [rejected, realize] using h.1
  · simpa [rejected, realize] using h.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let M : Matrix (Fin 1) (Fin 1) ℝ := 1
  refine ⟨1, M, -M, ?_⟩
  intro heq
  have hp : M.PosSemidef := Matrix.PosSemidef.one
  have hn : (-M).PosSemidef := heq.mp hp
  have h := hn.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  norm_num [M, Matrix.mulVec, dotProduct] at h

def family : Registration arena (type_of% @cosine_jet_hankel_iff_critical_or_real) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext d M
      simp [actual, rejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cosine_jet_hankel_iff_critical_or_real)
    (Realization signature) Unit Unit := {
    unitName := `D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion.cosine_jet_hankel_iff_critical_or_real.__information_unit
    realizationName := `Reg.D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion.family
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨family⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (DependentFamily.realize arena.signature
      family.actual.readout family.actual.anchor)
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := some {
      owner := `D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion
      definition := none
      coordinates := #[]
      readouts := #[
        { path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
          stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
        { path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
          stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
    continuation := .unknown
    familyRecord := none
    options := #[] }

end Reg.D5.S3.Weil.GoldenCriticalSpectrum.CosineJetHankelCriterion
