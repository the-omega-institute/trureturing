import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! The two complete reduced endpoints of an actual source array. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreJoint MiuraCoreNormal MiuraCanonicalJoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev Rectangle := Σ m : ℕ, Σ n : ℕ, Cell m n → ℤ

structure State (p : ℕ × ℕ) where
  h : Cell p.1 p.2 → ℤ
  hh : IsHeight h
  M : ℕ
  N : ℕ
  P : ℕ
  Q : ℕ
  g : Cell M N → ℤ
  f : Cell P Q → ℤ
  hg : JointReduction h g
  hf : JointReduction h f
  hgc : NoAdjacentFrozen g
  hgr : NoAdjacentFrozen (MiuraSlabIncidence.transposeHeight g)
  hfc : NoAdjacentFrozen f
  hfr : NoAdjacentFrozen (MiuraSlabIncidence.transposeHeight f)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) State (fun _ => Rectangle)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) _ x => ⟨x.M, x.N, x.g⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), R.readout () p x = ⟨x.P, x.Q, x.f⟩

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) _ x => ⟨x.M, x.N, fun v => x.g v + 1⟩)
    (fun e => nomatch e)

def pointState (c : ℤ) : State (1, 1) where
  h := fun _ => c
  hh := by
    intro p q hpq
    have he : p = q := Subsingleton.elim _ _
    subst q
    simp [adj, gdist] at hpq
  M := 1
  N := 1
  P := 1
  Q := 1
  g := fun _ => c
  f := fun _ => c
  hg := .refl _
  hf := .refl _
  hgc := by rintro ⟨j, k, _, hj, _⟩; have := hj.1; have := j.isLt; omega
  hgr := by rintro ⟨j, k, _, hj, _⟩; have := hj.1; have := j.isLt; omega
  hfc := by rintro ⟨j, k, _, hj, _⟩; have := hj.1; have := j.isLt; omega
  hfr := by rintro ⟨j, k, _, hj, _⟩; have := hj.1; have := j.isLt; omega

theorem actual_law : arena.Law actual := by
  intro p x
  exact joint_reduced_core_unique x.hh x.hg x.hf x.hgc x.hgr x.hfc x.hfr

theorem bridge : (type_of% (@joint_reduced_core_unique)) ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact h x.hh x.hg x.hf x.hgc x.hgr x.hfc x.hfr
  · intro h m n M N P Q src hh g f hg hf hgc hgr hfc hfr
    exact h (m, n) ⟨src, hh, M, N, P, Q, g, f, hg, hf, hgc, hgr, hfc, hfr⟩

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h (1, 1) (pointState 0)
  change (⟨1, 1, fun _ : Cell 1 1 => (0 : ℤ) + 1⟩ : Rectangle) =
    ⟨1, 1, fun _ => (0 : ℤ)⟩ at he
  have hf : (fun _ : Cell 1 1 => (0 : ℤ) + 1) = (fun _ => (0 : ℤ)) := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
  have hv := congrFun hf ((0 : Fin 1), (0 : Fin 1))
  norm_num at hv

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(1, 1), pointState 0, pointState 1, ?_⟩
  intro he
  change (⟨1, 1, fun _ : Cell 1 1 => (0 : ℤ)⟩ : Rectangle) =
    ⟨1, 1, fun _ => (1 : ℤ)⟩ at he
  have hf : (fun _ : Cell 1 1 => (0 : ℤ)) = (fun _ => (1 : ℤ)) := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
  have hv := congrFun hf ((0 : Fin 1), (0 : Fin 1))
  norm_num at hv

def registration : Registration arena (type_of% (@joint_reduced_core_unique)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@joint_reduced_core_unique)
    (type_of% (realize signature (fun (_ : Unit) _ x => ⟨x.M, x.N, x.g⟩)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint.joint_reduced_core_unique.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) _ x => ⟨x.M, x.N, x.g⟩)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalJoint
