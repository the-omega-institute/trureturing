import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

/- Faithful reconstruction and whole-family audit obligations for the new
insertion scalar. Contract.Registration selectors and current compiled binding
are not asserted here. This file is not a declared_validated registration. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.L1Scalar
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ degree => halfBinomial degree) (fun empty => nomatch empty)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ r n : ℕ,
    (1 / 2 : ℂ) * readout.readout () () r * Ring.choose (1 / 2 : ℂ) n =
      ((r + 1 : ℂ) + (n : ℂ)) *
        ((r + 1 : ℂ) * readout.readout () () (r + 1) * readout.readout () () n /
          ((r + 1 : ℂ) + (n : ℂ))) +
      (if n = 0 then 0 else ((n : ℂ) - 1) *
        ((r + 1 : ℂ) * readout.readout () () (r + 1) * readout.readout () () (n - 1) /
          ((r + 1 : ℂ) + ((n - 1 : ℕ) : ℂ)))) +
      (if r = 0 then (if n = 0 then 1 else 0) else
        (r + 1 : ℂ) * ((r : ℂ) * readout.readout () () r * readout.readout () () n /
          ((r : ℂ) + (n : ℂ))))

theorem source_bridge : (type_of% (@insertion_l1_scalar)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have contradiction := law 0 0
  norm_num [rejected, realize] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, halfBinomial]

def familyRegistration : Registration arena (type_of% (@insertion_l1_scalar)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp insertion_l1_scalar, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.L1Scalar
