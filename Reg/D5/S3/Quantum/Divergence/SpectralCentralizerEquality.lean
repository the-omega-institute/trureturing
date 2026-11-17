import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.SpectralCentralizerEquality

/-! The complete original-pair telescope is retained. The observed equality
is varied as a relation on the two actual real overlap masses. -/

noncomputable section
universe v
open Set
open scoped ComplexOrder InnerProductSpace
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis
open GNSOrderCoordinates NormalMomentFamily
open _root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
open _root_.D5.S3.Quantum.Divergence.NormalOverlapCompatibility
open _root_.D5.S3.Quantum.Divergence.SpectralCentralizerEquality

namespace Reg.D5.S3.Quantum.Divergence.SpectralCentralizerEquality

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ),
    let ψ := positiveOfDual (ρ + σ) (fun a ha => add_nonneg (hρ a ha) (hσ a ha))
    ∀ (C : ψ.GNS →L[ℂ] ψ.GNS) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
      (hc : ∀ a, Commute C (ψ.gnsStarAlgHom a))
      (hCr : coefficient ψ C = ρ.toLinearMap)
      (hCs : coefficient ψ (1 - C) = σ.toLinearMap)
      (hcentral : ContinuousCutoffCentralizer.CompressedCentralizes
        (GNSSpectralMoments.commutant ψ) C (cyclicVector ψ)),
      ∀ t : ℝ, 0 < t → R.readout () ()
        (overlap (GNSSpectralMoments.spectralFamily ρ σ ψ C hC0 hC1 hc hCr hCs) t 1).re
        (overlapValue M ρ σ t)

private theorem actual_law : arena.{v}.Law actual := @spectral_overlap_optimal.{v}

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem rejected_law : ¬ arena.{v}.Law rejected := by
  intro h
  let M : VonNeumannAlgebra PUnit.{v+1} := {
    toStarSubalgebra := ⊤
    centralizer_centralizer' := by
      ext x
      constructor
      · intro _; trivial
      · intro _ y hy
        exact Subsingleton.elim _ _ }
  have : IsClosed (M.toStarSubalgebra : Set (PUnit.{v+1} →L[ℂ] PUnit.{v+1})) :=
    _root_.D5.S3.Quantum.Analysis.VonNeumannNormalL1.closedCarrier M
  haveI : StarOrderedRing M.toStarSubalgebra :=
    StarOrderedRing.of_le_iff (fun x y => by
      constructor
      · intro _; exact ⟨0, Subsingleton.elim _ _⟩
      · intro _; exact le_of_eq (Subsingleton.elim _ _))
  let ρ : StrongDual ℂ M.toStarSubalgebra := 0
  have hp : Positive (A := M.toStarSubalgebra) ρ := by intro a ha; simp [ρ]
  have hseries : IsCoefficientSeries M ρ :=
    (mem_coefficientSpace_iff_series M ρ).mp (Submodule.zero_mem _)
  let ψ := positiveOfDual (ρ + ρ) (fun a ha => add_nonneg (hp a ha) (hp a ha))
  have hΩ : cyclicVector ψ = 0 := by
    have hz : (1 : M.toStarSubalgebra) = 0 := Subsingleton.elim _ _
    simp [cyclicVector, hz]
  have hr : coefficient ψ 0 = ρ.toLinearMap := by
    ext a
    simp [coefficient, ρ]
  have hs : coefficient ψ (1 - 0) = ρ.toLinearMap := by
    ext a
    simp [coefficient, hΩ, ρ]
  exact h M ρ ρ hp hp hseries hseries 0 le_rfl zero_le_one
    (fun _ => Commute.zero_left _) hr hs
    (by intro Y hY; simp [ContinuousCutoffCentralizer.CompressedCentralizes])
    1 (by norm_num)

def family : Registration arena.{v} (type_of% (@spectral_overlap_optimal.{v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro h
    have hf : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
    norm_num at hf

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spectral_overlap_optimal.{v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.SpectralCentralizerEquality.spectralOverlapUnit
  realizationName := `Reg.D5.S3.Quantum.Divergence.SpectralCentralizerEquality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v}⟩
  objectArena := .source ⟨arena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{v} ⟨family.{v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.SpectralCentralizerEquality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.SpectralCentralizerEquality
