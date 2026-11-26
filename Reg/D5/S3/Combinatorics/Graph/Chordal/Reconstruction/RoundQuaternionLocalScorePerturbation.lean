import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalScorePerturbation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The uniform rim bound depends on the explicit potential across the Fourier amplitudes. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Quaternion InnerProductSpace

noncomputable section

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalScorePerturbation

open _root_.RoundQuaternionLocalSharpness
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (unitI inner_eq_components)

local notation "U" => unitary ℍ[ℝ]

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature ℂ
  (fun _ => ℂ) (fun _ => Fin 4 → U)

def actual : Realization signature :=
  realize signature (fun _ q p => phasedPotential p q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observer := ∀ {A : Fin 3 → U} {p q : ℂ} {η γ : Fin 3 → ℝ},
    ‖p‖ ≤ localR → ‖q‖ ≤ localR → etaMax η ≤ localR →
    (∀ j, γ j = Real.sqrt (1-(η j)^2-‖transverse p q j‖^2)) →
    (∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p q j)) →
    q*(zeta-1) = ((Real.sqrt 3*‖q‖ : ℝ) : ℂ) →
    ∀ (i j : Fin 4), i ≠ j →
      let φ := observer.readout () q p
      localT + localLinear*‖q‖ - localAlpha*‖p‖^2 - (2/5)*‖p‖^3 - 3*‖p‖^4 -
        (627/100)*localR*‖q‖ - 2*localR*etaMax η ≤
        ⟪(hubGaugedGains A i j : ℍ[ℝ]),
          (↑((φ i)⁻¹*φ j) : ℍ[ℝ])⟫_ℝ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h (j : Fin 3) :
      (unitI : ℍ[ℝ]) = quatPair ⟨-(0 : ℝ), 1⟩ (transverse 0 0 j) := by
    simp [transverse, quatPair, unitI]
  have hbad := @law (fun _ => unitI) 0 0 0 (fun _ => 1)
    (by norm_num [localR]) (by norm_num [localR]) (by norm_num [etaMax,localR])
    (by intro j; norm_num [transverse]) (by intro j; simpa using h j) (by norm_num)
    1 2 (by decide)
  norm_num [rejected, realize, hubGaugedGains, etaMax, inner_eq_components, unitI] at hbad
  linarith [pure_score_estimates.constant_bounds.1]

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  let x : ℂ := ↑(1/100 : ℝ)
  refine ⟨0, 0, x, ?_⟩
  intro h
  change phasedPotential 0 0 = phasedPotential x 0 at h
  have hp : ‖x‖ ≤ localR := by norm_num [x, localR, Complex.norm_real]
  have hz : ‖(0 : ℂ)‖ ≤ localR := by norm_num [localR]
  have h := congrArg (fun φ : Fin 4 → U => ((φ 1 : U) : ℍ[ℝ]).re) h
  change ((localUnitRim 0 0 0 : U) : ℍ[ℝ]).re = ((localUnitRim x 0 0 : U) : ℍ[ℝ]).re at h
  rw [pure_score_estimates.rim_coe 0 0 hz hz 0, pure_score_estimates.rim_coe x 0 hp hz 0] at h
  change localReal 0 0 = localReal x 0 at h
  norm_num [localReal, x, Complex.norm_real] at h
  linarith [pure_score_estimates.constant_bounds.2.2.2.2.1]

def family : Registration arena (type_of% @local_minScore) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_minScore, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@local_minScore) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionLocalSharpness.local_minScore.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalScorePerturbation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalScorePerturbation
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalScorePerturbation
