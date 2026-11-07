import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing
import Reg.Support.DependentFamily
import Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis

/- The dependent arenas retain the complete original source telescopes and actual
mathematical readouts. Source selections are absent, so these proof terms are
incomplete source-bound audit attempts. An unknown continuation states only that
the residual is unknown. Compactness and constructor identities with no supplied
whole-family intervention remain positive laws rather than completed registrations. -/
noncomputable section
open Filter
open scoped BigOperators InnerProductSpace Topology NNReal VertexOperator
open _root_.D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis
namespace Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing

private theorem smoothing_vacuum (M : Model) (k : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    M.heatSmoothing k t ht (M.embed 0 (vacuum M.D)) = M.embed k (vacuum M.D) := by
  rw [heatSmoothing_embed]
  have h := heat_embed M k t (vacuum M.D)
  obtain ⟨_,_,_,_,_,_,_,_,_,hfix⟩ := original_heat M
  rw [hfix] at h
  exact h.symm

namespace heatSmoothing_embed
abbrev signature := vectorSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (ht : 0 < t) (v : Carrier M.D),
    M.heatSmoothing k t ht (M.embed 0 v) =
      (R.readout () ⟨M,k⟩ (M.embed k (∑ E ∈ stateEnergies M.D v,
        (Real.exp (-(t : ℝ)*(E : ℝ)) : ℂ) • gradeProjection M.D E v)))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_embed
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,0,M0.embed 0 (vacuum M0.D), (vacuum_ne_zero M0 0).symm⟩
def rejected : Realization signature :=
  realize signature (fun _ p z => z + p.1.embed p.2 (vacuum p.1.D)) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := h M0 0 1 (by norm_num) 0
  have heq : (0 : M0.Hilbert) = M0.embed 0 (vacuum M0.D) := by
    simpa [rejected, realize] using hh
  exact vacuum_ne_zero M0 0 heq.symm
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_embed)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration (M0 : Model) :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_embed)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_embed.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_embed.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration M0⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end heatSmoothing_embed

namespace heatSmoothing_bound
abbrev signature := scalarSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (ht : 0 < t),
    ‖M.heatSmoothing k t ht‖ ≤ R.readout () () (heatSmoothingConstant k t) ∧
    ∀ x : M.Hilbert, ‖M.heatSmoothing k t ht x‖ ≤ heatSmoothingConstant k t * ‖x‖
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_bound
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := (h M0 0 1 (by norm_num)).1
  change ‖M0.heatSmoothing 0 1 (by norm_num)‖ ≤ -1 at hh
  have hn := norm_nonneg (M0.heatSmoothing 0 1 (by norm_num))
  linarith
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_bound)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration (M0 : Model) :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_bound)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_bound.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_bound.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration M0⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end heatSmoothing_bound

namespace heatSmoothing_inclusion
abbrev signature := crossMapSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (j k : ℕ) (hjk : j ≤ k) (t : ℝ≥0) (ht : 0 < t),
    (M.inclusion j k hjk).comp (M.heatSmoothing k t ht) = (R.readout () ⟨M,(j,0)⟩ (M.heatSmoothing j t ht))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_inclusion
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨M0,(0,0)⟩,0,ContinuousLinearMap.id ℂ M0.Hilbert,?_⟩
  intro h
  have hh := congrArg (fun A => A (M0.embed 0 (vacuum M0.D))) h
  exact vacuum_ne_zero M0 0 (by simpa [actual, realize] using hh.symm)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun A => A (M0.embed 0 (vacuum M0.D)))
    (h M0 0 0 le_rfl 1 (by norm_num))
  have heq : M0.embed 0 (vacuum M0.D) = 0 := by
    simpa only [rejected, realize, ContinuousLinearMap.comp_apply, smoothing_vacuum,
      inclusion_embed, ContinuousLinearMap.zero_apply] using hh
  exact vacuum_ne_zero M0 0 heq
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_inclusion)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration (M0 : Model) :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_inclusion)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_inclusion.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_inclusion.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration M0⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end heatSmoothing_inclusion

namespace heatSmoothing_hilbert
abbrev signature := crossMapSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (ht : 0 < t),
    (M.inclusion 0 k (Nat.zero_le k)).comp (M.heatSmoothing k t ht) = M.heat 0 t ∧
    (M.heatSmoothing k t ht).comp (M.inclusion 0 k (Nat.zero_le k)) = R.readout () ⟨M,(k,k)⟩ (M.heat k t)
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_hilbert
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨M0,(0,0)⟩,0,ContinuousLinearMap.id ℂ M0.Hilbert,?_⟩
  intro h
  have hh := congrArg (fun A => A (M0.embed 0 (vacuum M0.D))) h
  exact vacuum_ne_zero M0 0 (by simpa [actual, realize] using hh.symm)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := congrArg (fun A => A (M0.embed 0 (vacuum M0.D)))
    (h M0 0 1 (by norm_num)).2
  have heq : M0.embed 0 (vacuum M0.D) = 0 := by
    simpa only [rejected, realize, ContinuousLinearMap.comp_apply, inclusion_embed,
      smoothing_vacuum, ContinuousLinearMap.zero_apply] using hh
  exact vacuum_ne_zero M0 0 heq
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_hilbert)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration (M0 : Model) :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_hilbert)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_hilbert.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_hilbert.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration M0⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end heatSmoothing_hilbert

namespace heat_smoothDomain
abbrev signature := vectorSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (t : ℝ≥0) (ht : 0 < t) (x : M.Hilbert),
    M.evaluation (M.heatFamily t ht x) = R.readout () ⟨M,0⟩ (M.heat 0 t x) ∧
    M.heat 0 t x ∈ M.smoothDomain
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_smoothDomain
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,0,M0.embed 0 (vacuum M0.D), (vacuum_ne_zero M0 0).symm⟩
def rejected : Realization signature :=
  realize signature (fun _ p z => z + p.1.embed p.2 (vacuum p.1.D)) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := (h M0 1 (by norm_num) 0).1
  have heq : (0 : M0.Hilbert) = M0.embed 0 (vacuum M0.D) := by
    simpa [rejected, realize] using hh
  exact vacuum_ne_zero M0 0 heq.symm
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_smoothDomain)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration (M0 : Model) :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_smoothDomain)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heat_smoothDomain.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heat_smoothDomain.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration M0⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end heat_smoothDomain

namespace heatSmoothing_tail
abbrev signature := scalarSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (ht : 0 < t) (N : ℕ),
    M.heatSmoothingTruncation k t ht N =
      (M.truncation k (M.energyCutoff N)).comp (M.heatSmoothing k t ht) ∧
    (M.heatSmoothingTruncation k t ht N).range ≤ M.cutoffSpace k N ∧
    FiniteDimensional ℂ (M.heatSmoothingTruncation k t ht N).range ∧
    ‖M.heatSmoothing k t ht - M.heatSmoothingTruncation k t ht N‖ ≤
      (R.readout () () (heatSmoothingConstant k ((t : ℝ)/2) * Real.exp (-(t : ℝ)*((N : ℝ)+1)/2)))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_tail
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := (h M0 0 1 (by norm_num) 0).2.2.2
  change ‖M0.heatSmoothing 0 1 (by norm_num) -
    M0.heatSmoothingTruncation 0 1 (by norm_num) 0‖ ≤ -1 at hh
  have hn := norm_nonneg (M0.heatSmoothing 0 1 (by norm_num) -
    M0.heatSmoothingTruncation 0 1 (by norm_num) 0)
  linarith
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_tail)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration (M0 : Model) :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_tail)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_tail.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing.heatSmoothing_tail.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration M0⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
end heatSmoothing_tail

namespace heatSmoothing_compact
abbrev signature := crossMapSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (ht : 0 < t),
    IsCompactOperator (R.readout () ⟨M,(k,0)⟩ (M.heatSmoothing k t ht))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatSmoothing_compact
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨M0,(0,0)⟩,0,ContinuousLinearMap.id ℂ M0.Hilbert,?_⟩
  intro h
  have hh := congrArg (fun A => A (M0.embed 0 (vacuum M0.D))) h
  exact vacuum_ne_zero M0 0 (by simpa [actual, realize] using hh.symm)
-- AUDIT GAP: full-telescope actual law and dependence are retained; whole-family
-- intervention, sensitivity and raw source reconstruction are not supplied.
-- Compactness of arbitrary bounded maps cannot be refuted on a vacuum-line model.
end heatSmoothing_compact

end Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeatSmoothing
