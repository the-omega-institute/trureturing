import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.Analysis.OriginalHeat
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
namespace Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat

namespace heat_completedGrade
abbrev signature := vectorSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (E : ℤ)
    (x : M.completedGrade k E),
    M.heat k t (x : M.Sobolev k) =
      (R.readout () ⟨M,k⟩ ((Real.exp (-(t : ℝ)*(E : ℝ)) : ℂ) • (x : M.Sobolev k)))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_completedGrade
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,0,M0.embed 0 (vacuum M0.D), (vacuum_ne_zero M0 0).symm⟩
def rejected : Realization signature :=
  realize signature (fun _ p z => z + p.1.embed p.2 (vacuum p.1.D)) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := h M0 0 0 0 (0 : M0.completedGrade 0 0)
  have heq : (0 : M0.Hilbert) = M0.embed 0 (vacuum M0.D) := by
    simpa [rejected, realize] using hh
  exact vacuum_ne_zero M0 0 heq.symm
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_completedGrade)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_completedGrade)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_completedGrade.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_completedGrade.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration auditModel⟩,
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
end heat_completedGrade

namespace heat_embed
abbrev signature := vectorSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (v : Carrier M.D),
    M.heat k t (M.embed k v) =
      (R.readout () ⟨M,k⟩ (M.embed k (∑ E ∈ stateEnergies M.D v,
        (Real.exp (-(t : ℝ)*(E : ℝ)) : ℂ) • gradeProjection M.D E v)))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_embed
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,0,M0.embed 0 (vacuum M0.D), (vacuum_ne_zero M0 0).symm⟩
def rejected : Realization signature :=
  realize signature (fun _ p z => z + p.1.embed p.2 (vacuum p.1.D)) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := h M0 0 0 0
  have heq : (0 : M0.Hilbert) = M0.embed 0 (vacuum M0.D) := by
    simpa [rejected, realize] using hh
  exact vacuum_ne_zero M0 0 heq.symm
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_embed)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_embed)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_embed.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_embed.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration auditModel⟩,
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
end heat_embed

namespace heat_inclusion
abbrev signature := crossMapSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (j k : ℕ) (hjk : j ≤ k) (t : ℝ≥0),
    (M.inclusion j k hjk).comp (M.heat k t) =
      (R.readout () ⟨M,(j,k)⟩ ((M.heat j t).comp (M.inclusion j k hjk)))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_inclusion
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
    (h M0 0 0 le_rfl 0)
  have hz := (original_heat M0).2.1 0
  have heq : M0.embed 0 (vacuum M0.D) = 0 := by
    simpa only [rejected, realize, ContinuousLinearMap.comp_apply, hz,
      ContinuousLinearMap.id_apply, inclusion_embed, ContinuousLinearMap.zero_apply] using hh
  exact vacuum_ne_zero M0 0 heq
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_inclusion)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_inclusion)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_inclusion.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_inclusion.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration auditModel⟩,
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
end heat_inclusion

namespace heat_projection
abbrev signature := vectorSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (E : ℤ) (x : M.Sobolev k),
    M.heat k t (M.projection k E x) =
        (R.readout () ⟨M,k⟩ ((Real.exp (-(t : ℝ)*(E : ℝ)) : ℂ) • M.projection k E x)) ∧
    M.projection k E (M.heat k t x) =
        (R.readout () ⟨M,k⟩ ((Real.exp (-(t : ℝ)*(E : ℝ)) : ℂ) • M.projection k E x))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_projection
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,0,M0.embed 0 (vacuum M0.D), (vacuum_ne_zero M0 0).symm⟩
def rejected : Realization signature :=
  realize signature (fun _ p z => z + p.1.embed p.2 (vacuum p.1.D)) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := (h M0 0 0 0 0).1
  have heq : (0 : M0.Hilbert) = M0.embed 0 (vacuum M0.D) := by
    simpa [rejected, realize] using hh
  exact vacuum_ne_zero M0 0 heq.symm
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_projection)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_projection)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_projection.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_projection.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration auditModel⟩,
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
end heat_projection

namespace heatTruncation_range
abbrev signature := subspaceSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (N : ℕ),
    (M.heatTruncation k t N).range ≤ (R.readout () ⟨M,k⟩ (M.cutoffSpace k N)) ∧
    FiniteDimensional ℂ (M.heatTruncation k t N).range
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatTruncation_range
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,⊥,⊤,gradeBot_ne_top M0 0⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hr := (h M0 0 0 0).1
  change (M0.heatTruncation 0 0 0).range ≤ ⊥ at hr
  obtain ⟨_,_,_,_,_,_,_,_,_,hfix⟩ := original_heat M0
  have hv : vacuum M0.D ∈ grade M0.D 0 := by
    rw [grade_zero M0.D M0.positive]
    exact Submodule.subset_span (by simp)
  have heq : M0.heatTruncation 0 0 0 (M0.embed 0 (vacuum M0.D)) =
      M0.embed 0 (vacuum M0.D) := by
    change M0.truncation 0 (M0.energyCutoff 0) (M0.heat 0 0 (M0.embed 0 (vacuum M0.D))) = _
    rw [hfix, truncation_grade M0 0 (M0.energyCutoff 0) 0 (vacuum M0.D) hv]
    simp [Model.energyCutoff]
  exact vacuum_ne_zero M0 0 (hr ⟨M0.embed 0 (vacuum M0.D),heq⟩)
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatTruncation_range)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heatTruncation_range)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heatTruncation_range.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heatTruncation_range.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration auditModel⟩,
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
end heatTruncation_range

namespace heat_tail_bound
abbrev signature := scalarSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (N : ℕ),
    ‖M.heat k t - M.heatTruncation k t N‖ ≤
      (R.readout () () (Real.exp (-(t : ℝ)*((N : ℝ)+1))))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_tail_bound
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := h M0 0 0 0
  change ‖M0.heat 0 0 - M0.heatTruncation 0 0 0‖ ≤ -1 at hh
  have hn := norm_nonneg (M0.heat 0 0 - M0.heatTruncation 0 0 0)
  linarith
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_tail_bound)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_tail_bound)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_tail_bound.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.heat_tail_bound.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration auditModel⟩,
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
end heat_tail_bound

namespace heat_compact
abbrev signature := crossMapSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (t : ℝ≥0) (ht : 0 < t),
    Tendsto (fun N : ℕ => M.heatTruncation k t N) atTop (𝓝 (R.readout () ⟨M,(k,k)⟩ (M.heat k t))) ∧
    IsCompactOperator (M.heat k t)
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.heat_compact
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨M0,(0,0)⟩,0,ContinuousLinearMap.id ℂ M0.Hilbert,?_⟩
  intro h
  have hh := congrArg (fun A => A (M0.embed 0 (vacuum M0.D))) h
  exact vacuum_ne_zero M0 0 (by simpa [actual, realize] using hh.symm)
-- AUDIT GAP: full-telescope actual law above is retained. No familyRegistration
-- or Contract.Registration is fabricated: whole-family variation/sensitivity
-- and raw source reconstruction are still missing for this operand choice.
end heat_compact

namespace original_heat
abbrev signature := scalarSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model),
    (∀ k t v, M.heat k t (M.embed k v) = M.embed k
      (∑ E ∈ stateEnergies M.D v,
        (Real.exp (-(t : ℝ)*(E : ℝ)) : ℂ) • gradeProjection M.D E v)) ∧
    (∀ k, M.heat k 0 = ContinuousLinearMap.id ℂ (M.Sobolev k)) ∧
    (∀ k s t, M.heat k (s+t) = (M.heat k s).comp (M.heat k t)) ∧
    (∀ k t x, ‖M.heat k t x‖ ≤ R.readout () () ‖x‖) ∧
    (∀ k t, ‖M.heat k t‖ ≤ 1) ∧
    (∀ k x, Continuous (fun t : ℝ≥0 => M.heat k t x)) ∧
    (∀ k t, (M.heat k t).IsPositive) ∧
    (∀ k E, E < 0 → ∀ x, M.projection k E x = 0) ∧
    (∀ k x, Tendsto (fun N : ℕ => M.truncation k (M.energyCutoff N) x) atTop (𝓝 x)) ∧
    (∀ k t, M.heat k t (M.embed k (vacuum M.D)) = M.embed k (vacuum M.D))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.original_heat
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := (h M0).2.2.2.1 0 0 0
  change ‖M0.heat 0 0 0‖ ≤ -1 at hh
  have hn := norm_nonneg (M0.heat 0 0 0)
  linarith
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.original_heat)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.original_heat)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.original_heat.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat.original_heat.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration auditModel⟩,
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
end original_heat

end Reg.D5.S3.VertexAlgebra.Analysis.OriginalHeat
