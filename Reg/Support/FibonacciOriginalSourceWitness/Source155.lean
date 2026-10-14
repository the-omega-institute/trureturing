import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
import Reg.Support.FibonacciFactorWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open Filter
open scoped Topology

namespace Reg.Support.FibonacciOriginalSourceWitness.Source155
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ q x => q.2+q.1*(x-q.2)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (T : Set ℝ) (hT : T.OrdConnected)
    (a y : ℝ) (ha : -1<a) (ha1 : a<1) (hane : a≠0),
    let F := fun x : ℝ => r.readout () ⟨a,y⟩ x
    (∀ x, (∀ n : ℕ, F^[n] x ∈ T) ↔
      if 0<a then x∈T ∧ y∈closure T else x∈T ∧ F x∈T) ∧
    ({x : ℝ | ∀ n : ℕ, F^[n] x∈T}.Nonempty ↔
      if 0<a then T.Nonempty ∧ y∈closure T else y∈T)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hh := h ({0} : Set ℝ) (by infer_instance)
    (1/2) 0 (by norm_num) (by norm_num) (by norm_num)
  have orbit := (hh.1 0).mpr (by simp)
  have bad := orbit 1
  norm_num [rejected, realize] at bad

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨⟨(1/2),0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competing_tail_orbit_criterion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.competing_tail_orbit_criterion, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

end
end Reg.Support.FibonacciOriginalSourceWitness.Source155
