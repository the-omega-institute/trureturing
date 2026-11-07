import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis
import Reg.Support.DependentFamily

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

namespace Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis

private def auditLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

/-- A genuine model supplies a closed intervention witness for universal source laws. -/
def auditModel : Model where
  D := auditLattice
  positive := by
    have h : _root_.D5.S3.VertexAlgebra.OriginalGram.gramReal auditLattice =
        Matrix.diagonal (fun _ : Fin 0 => (0 : ℝ)) := by
      ext i
      exact Fin.elim0 i
    rw [h]
    exact Matrix.PosDef.diagonal (fun i => Fin.elim0 i)
  inverse := 0
  inverse_left := by ext i; exact Fin.elim0 i
  inverse_right := by ext i; exact Fin.elim0 i

/-- Actual nonzero original vacuum, also in rank zero. -/
theorem vacuum_ne_zero (M : Model) (k : ℕ) : M.embed k (vacuum M.D) ≠ 0 := by
  intro h
  apply vacuum_nonzero M.D
  exact embed_injective M k (h.trans (map_zero _).symm)

theorem gradeBot_ne_top (M : Model) (k : ℕ) :
    (⊥ : Submodule ℂ (M.Sobolev k)) ≠ ⊤ := by
  intro h
  have hm : M.embed k (vacuum M.D) ∈ (⊥ : Submodule ℂ (M.Sobolev k)) := by
    rw [h]
    exact Submodule.mem_top
  exact vacuum_ne_zero M k hm

abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev integerSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev vectorSignature : Signature where
  Params := Σ M : Model, ℕ
  State p := p.1.Sobolev p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.Sobolev p.2
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev subspaceSignature : Signature where
  Params := Σ M : Model, ℕ
  State p := Submodule ℂ (p.1.Sobolev p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule ℂ (p.1.Sobolev p.2)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev crossMapSignature : Signature where
  Params := Σ M : Model, ℕ × ℕ
  State p := p.1.Sobolev p.2.2 →L[ℂ] p.1.Sobolev p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.Sobolev p.2.2 →L[ℂ] p.1.Sobolev p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev basisFunctionSignature : Signature where
  Params := Σ M : Model, ℕ
  State p := p.1.energyIndex p.2 → p.1.Sobolev p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.energyIndex p.2 → p.1.Sobolev p.2
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Only proof evidence is assembled; neither raw source selections nor bindings are invented. -/
def singletonFamily {A : Arena} [Subsingleton A.signature.Role] [IsEmpty A.signature.Anchor]
    {P : Prop} (actual bad : Realization A.signature)
    (hbridge : P ↔ A.Law actual) (hlaw : A.Law actual) (hbad : ¬ A.Law bad)
    (hdep : ObservationalDependence A.signature actual) : Registration A P where
  actual := actual
  bridge := hbridge
  variation := ⟨hlaw,bad,hbad⟩
  sensitivity := ⟨by
    intro i
    refine ⟨bad,?_,?_,hbad⟩
    · intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · funext e
      exact isEmptyElim e,
    fun e => isEmptyElim e⟩
  dependence := hdep

end Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis
open Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis
namespace Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis

namespace completedGrade_negative
abbrev signature := subspaceSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (E : ℤ) (hE : E < 0),
    M.completedGrade k E = (R.readout () ⟨M,k⟩ (⊥ : Submodule ℂ (M.Sobolev k)))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.completedGrade_negative
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,⊥,⊤,gradeBot_ne_top M0 0⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := h M0 0 (-1) (by norm_num)
  have heq : (⊥ : Submodule ℂ M0.Hilbert) = ⊤ := by
    simpa only [rejected, realize, completedGrade_negative M0 0 (-1) (by norm_num)] using hh
  exact gradeBot_ne_top M0 0 heq
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.completedGrade_negative)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.completedGrade_negative)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.completedGrade_negative.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.completedGrade_negative.familyRegistration,
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
end completedGrade_negative

namespace energyBasis_coe
abbrev signature := basisFunctionSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ),
    (M.energyBasis k : M.energyIndex k → M.Sobolev k) = (R.readout () ⟨M,k⟩ (M.energyVector k))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.energyBasis_coe
-- AUDIT GAP: full-telescope actual law above is retained. No familyRegistration
-- or Contract.Registration is fabricated: whole-family variation/sensitivity
-- and raw source reconstruction are still missing for this operand choice.
end energyBasis_coe

namespace finiteCore_eq_energyBasis_span
abbrev signature := subspaceSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ),
    (M.embed k).range =
      (R.readout () ⟨M,k⟩ (Submodule.span ℂ (Set.range (M.energyBasis k : M.energyIndex k → M.Sobolev k))))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finiteCore_eq_energyBasis_span
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨M0,0⟩,⊥,⊤,gradeBot_ne_top M0 0⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have heq := h M0 0
  change (M0.embed 0).range = ⊥ at heq
  have hm : M0.embed 0 (vacuum M0.D) ∈ (M0.embed 0).range := ⟨_,rfl⟩
  rw [heq] at hm
  exact vacuum_ne_zero M0 0 hm
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finiteCore_eq_energyBasis_span)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finiteCore_eq_energyBasis_span)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.finiteCore_eq_energyBasis_span.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.finiteCore_eq_energyBasis_span.familyRegistration,
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
end finiteCore_eq_energyBasis_span

namespace energyIndex_nonnegative
abbrev signature := integerSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (i : M.energyIndex k),
    0 ≤ (R.readout () () i.1)
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.energyIndex_nonnegative
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩
-- AUDIT GAP: full-telescope actual law above is retained. No familyRegistration
-- or Contract.Registration is fabricated: whole-family variation/sensitivity
-- and raw source reconstruction are still missing for this operand choice.
end energyIndex_nonnegative

namespace finite_grade_quadratic
abbrev signature := scalarSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (k : ℕ) (F : Finset ℤ)
    (u : ℤ → Carrier M.D) (b : ℤ → ℂ)
    (hu : ∀ E ∈ F, u E ∈ grade M.D E),
    ‖M.embed k (∑ E ∈ F, b E • u E)‖^2 =
      (R.readout () () (∑ E ∈ F, ‖b E‖^2 * ((E : ℝ)+1)^(2*k) * normD (u E)^2))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finite_grade_quadratic
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := h M0 0 ∅ (fun _ => 0) (fun _ => 0) (by simp)
  norm_num [rejected, realize] at hh
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finite_grade_quadratic)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finite_grade_quadratic)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.finite_grade_quadratic.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.finite_grade_quadratic.familyRegistration,
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
end finite_grade_quadratic

namespace finite_multiplier_bound
abbrev signature := scalarSignature
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Model) (j k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (v : Carrier M.D) (b : ℤ → ℂ)
    (hb : ∀ E ∈ stateEnergies M.D v,
      ‖b E‖ * ((E : ℝ)+1)^k ≤ B * ((E : ℝ)+1)^j),
    ‖M.embed k (∑ E ∈ stateEnergies M.D v, b E • gradeProjection M.D E v)‖ ≤
      (R.readout () () (B * ‖M.embed j v‖))
theorem actual_law : arena.Law actual := @D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finite_multiplier_bound
theorem actual_dependence (M0 : Model) : ObservationalDependence signature actual := by
  intro i
  exact ⟨(),0,1,zero_ne_one⟩
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem rejected_law (M0 : Model) : ¬ arena.Law rejected := by
  intro h
  have hh := h M0 0 0 0 (by norm_num) 0 (fun _ => 0) (by simp)
  norm_num [rejected, realize] at hh
def familyRegistration (M0 : Model) : Registration arena (type_of% (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finite_multiplier_bound)) :=
  singletonFamily actual rejected Iff.rfl actual_law (rejected_law M0) (actual_dependence M0)
def registration :
    Contract.Registration.{_,0,0,0,0,0,0,0,0,0,0,0}
      (@D5.S3.VertexAlgebra.Analysis.OriginalSmearing.finite_multiplier_bound)
      (type_of% (realize signature (fun _ _ z => z) (fun e => nomatch e))) Unit True := {
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.finite_multiplier_bound.unit,
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis.finite_multiplier_bound.familyRegistration,
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
end finite_multiplier_bound

end Reg.D5.S3.VertexAlgebra.Analysis.OriginalEnergyBasis
