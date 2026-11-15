import D5.S3.Quantum.Foundation.HitPureCompactness
import Reg.D5.S3.Quantum.Foundation.HitSectionGeneration

/-! Exact source reconstruction for original all-label Hit compactness.
The full-family evidence uses a nontrivial scalar cone in every universe. Raw
source selection remains unresolved; this family is not a declared_validated
four-slot registration. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.HitPureCompactness

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.HitSectionGeneration
open _root_.D5.S3.Quantum.Foundation.HitPureCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.HitSectionGeneration

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P S => pure P.cone P.unit ∩ S) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    (∀ a : pure P.cone P.unit, Hit P.cone P.unit a) →
    IsClosed (O.readout () P Set.univ) ∧ IsCompact (O.readout () P Set.univ)

abbrev sourceScope : Prop := type_of% (@hit_pure_closed_compact.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hu hg hh
    simpa [actual, realize] using @h P.V P.add P.space P.finite P.cone P.unit hc hu hg hh
  · intro h V add space finite C u hc hu hg hh
    simpa [actual, realize] using h (@Inputs.mk V add space finite C u) hc hu hg hh

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@hit_pure_closed_compact.{v})

namespace ScalarModel

abbrev V := ULift.{v} ℝ

def unit : V →ₗ[ℝ] ℝ := ULift.moduleEquiv.toLinearMap

def cone : PointedCone ℝ V := (PointedCone.positive ℝ ℝ).comap unit

def inputs : Inputs.{v} := ⟨V, cone, unit⟩

theorem closed : IsClosed (cone : Set V) := by
  exact isClosed_Ici.preimage unit.continuous_of_finiteDimensional

theorem positive : ∀ x ∈ cone, x ≠ 0 → 0 < unit x := by
  intro x hx hn
  apply lt_of_le_of_ne hx
  intro h
  apply hn
  exact ULift.ext h.symm

theorem generating : Submodule.span ℝ (cone : Set V) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hone : (1 : V) ∈ Submodule.span ℝ (cone : Set V) :=
    Submodule.subset_span (show (1 : V) ∈ cone from (show (0 : ℝ) ≤ 1 from zero_le_one))
  have he : x.down • (1 : V) = x := by
    apply ULift.ext
    exact mul_one _
  have hsm : x.down • (1 : V) ∈ Submodule.span ℝ (cone : Set V) :=
    (Submodule.span ℝ (cone : Set V)).smul_mem x.down hone
  exact he ▸ hsm

theorem base_eq : base cone unit = ({1} : Set V) := by
  ext x
  constructor
  · intro h
    exact ULift.ext h.2
  · intro h
    rcases Set.mem_singleton_iff.mp h with rfl
    exact ⟨(show (0 : ℝ) ≤ 1 from zero_le_one), rfl⟩

theorem pure_eq : pure cone unit = ({1} : Set V) := by
  rw [_root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.pure,
    base_eq, extremePoints_singleton]

theorem all_hit : ∀ a : pure cone unit, Hit cone unit a := by
  intro a p q hpq
  have hp : (p : V) = 1 := by simpa only [pure_eq, Set.mem_singleton_iff] using p.property
  have hq : (q : V) = 1 := by simpa only [pure_eq, Set.mem_singleton_iff] using q.property
  exact (hpq (Subtype.ext (hp.trans hq.symm))).elim

end ScalarModel

def rejected : Realization signature.{v} :=
  realize signature (fun (_ : Unit) (P : Inputs.{v}) (_ : Set P.V) => Set.univ)
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.{v}.Law rejected.{v} := by
  intro h
  have hk := (h ScalarModel.inputs ScalarModel.closed ScalarModel.positive
    ScalarModel.generating ScalarModel.all_hit).2
  exact NormedSpace.unbounded_univ ℝ ScalarModel.V hk.isBounded

theorem observational_dependence : ObservationalDependence signature.{v} actual.{v} := by
  intro i
  refine ⟨ScalarModel.inputs, Set.univ, ∅, ?_⟩
  intro h
  have hp : (1 : ScalarModel.V) ∈ pure ScalarModel.cone ScalarModel.unit := by
    rw [ScalarModel.pure_eq]
    exact Set.mem_singleton _
  have hmem : (1 : ScalarModel.V) ∈ actual.readout i ScalarModel.inputs Set.univ :=
    ⟨hp, Set.mem_univ _⟩
  rw [h] at hmem
  exact hmem.2

def family : Registration arena.{v} sourceScope.{v} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        (by funext e; exact nomatch e), rejected_law⟩
    · intro e
      exact nomatch e
  dependence := observational_dependence

/-- The raw selector is absent: the source observes pure C u directly, while
this family observes its intersection with an independently varying set. -/
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Foundation.HitPureCompactness.hit_pure_closed_compact.{v})
      (Realization signature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Foundation.HitPureCompactness.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.HitPureCompactness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v}⟩
  objectArena := .source ⟨arena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v}
    (fun _ P S => pure P.cone P.unit ∩ S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

#print axioms family

#print axioms hit_pure_closed_compact
#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Quantum.Foundation.HitPureCompactness
