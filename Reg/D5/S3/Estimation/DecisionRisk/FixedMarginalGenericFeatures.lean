import D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open scoped BigOperators
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open _root_.D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures

universe u v w t

/-- The full finite data and feature telescope, without support restrictions. -/
structure Parameters where
  X : Type u
  Z : Type v
  finiteX : Fintype X
  finiteZ : Fintype Z
  q : X → ℝ
  encoder : X → Z → ℝ
  epsilon : ℝ

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := @FiniteMarkovKernel p.Z p.X p.finiteX
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d =>
    @reconstructionError p.X p.Z p.finiteX p.finiteZ p.q p.encoder d.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ p : Parameters.{u,v},
    letI := p.finiteX
    letI := p.finiteZ
    (∀ x, 0 ≤ p.q x) → (∑ x, p.q x) = 1 →
    IsRowStochastic p.encoder → 0 < p.epsilon →
    (GenericQuality.{u,v,w,t} p.q p.encoder p.epsilon ↔
      ∃ d : FiniteMarkovKernel p.Z p.X, R.readout () p d ≤ p.epsilon / 2)

/-- The source law uses every original type, mass, kernel and quality binder. -/
theorem actual_law : arena.{u,v,w,t}.Law actual := by
  intro p
  letI := p.finiteX
  letI := p.finiteZ
  intro hq hs hφ hε
  exact generic_quality_iff_reconstruction p.q p.encoder p.epsilon hq hs hφ hε

/-- A constant readout loses the reconstruction law even for a singleton. -/
theorem rejected_law : ¬ arena.{u,v,w,t}.Law rejected := by
  intro h
  let X := ULift.{u} Unit
  let Z := ULift.{v} Unit
  let p : Parameters.{u,v} := ⟨X, Z, inferInstance, inferInstance,
    (fun _ => 1), (fun _ _ => 1), (1 / 2)⟩
  have hs : IsRowStochastic p.encoder := by
    constructor
    · intro x z; norm_num [p]
    · intro x; simp [p, X, Z]
  let d : FiniteMarkovKernel Z X := ⟨fun _ _ => 1,
    ⟨by intro z x; norm_num, by intro z; simp [X]⟩⟩
  have he : reconstructionError p.q p.encoder d.1 = 0 := by
    simp [reconstructionError, p, d, X, Z]
  have hgood : GenericQuality.{u,v,w,t} p.q p.encoder p.epsilon := by
    apply (generic_quality_iff_reconstruction p.q p.encoder p.epsilon
      (by intro x; norm_num [p]) (by simp [p, X]) hs (by norm_num [p])).2
    exact ⟨d, by rw [he]; norm_num [p]⟩
  obtain ⟨k, hk⟩ := (h p (by intro x; norm_num [p])
    (by simp [p, X]) hs (by norm_num [p])).1 hgood
  norm_num [rejected, realize, p] at hk

/-- Reconstruction error varies with the decision on the same two-state law. -/
theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  let X := ULift.{u} (Fin 2)
  let Z := ULift.{v} Unit
  let p : Parameters.{u,v} := ⟨X, Z, inferInstance, inferInstance,
    (fun x => if x.down = 0 then 1 else 0), (fun _ _ => 1), 1⟩
  let d0 : FiniteMarkovKernel Z X :=
    ⟨fun _ x => if x.down = 0 then 1 else 0,
      ⟨by intro z x; split_ifs <;> norm_num,
        by intro z; simp [X, Fin.sum_univ_two]⟩⟩
  let d1 : FiniteMarkovKernel Z X :=
    ⟨fun _ x => if x.down = 1 then 1 else 0,
      ⟨by intro z x; split_ifs <;> norm_num,
        by intro z; simp [X, Fin.sum_univ_two]⟩⟩
  refine ⟨p, d0, d1, ?_⟩
  norm_num [actual, realize, reconstructionError, p, d0, d1, X, Z, Fin.sum_univ_two]

/-- Four mathematical slots for the exact dependent family. The enclosing
Contract registration also requires compiler-derived source-selection and
current binding evidence. -/
def registration : Registration arena.{u,v,w,t}
    (∀ {X : Type u} {Z : Type v} [Fintype X] [Fintype Z]
      (q : X → ℝ) (φ : X → Z → ℝ) (ε : ℝ),
      (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 → IsRowStochastic φ → 0 < ε →
      (GenericQuality.{u,v,w,t} q φ ε ↔
        ∃ d : FiniteMarkovKernel Z X, reconstructionError q φ d.1 ≤ ε / 2)) where
  actual := actual
  bridge := by
    constructor
    · intro source p
      letI := p.finiteX
      letI := p.finiteZ
      exact source p.q p.encoder p.epsilon
    · intro law X Z finiteX finiteZ q φ ε
      exact law ⟨X, Z, finiteX, finiteZ, q, φ, ε⟩
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

/-- Exact source registration with an unresolved compiler source selection.
The dependent mathematical evidence does not by itself supply current binding. -/
def contract : LeanInformationAudit.Contract.Registration
    (@generic_quality_iff_reconstruction.{u,v,w,t})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures.generic_quality_iff_reconstruction.audit
  realizationName := `Reg.D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,t}⟩
  objectArena := .source ⟨arena.{u,v,w,t}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,t} ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ p d =>
    @reconstructionError p.X p.Z p.finiteX p.finiteZ p.q p.encoder d.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures
