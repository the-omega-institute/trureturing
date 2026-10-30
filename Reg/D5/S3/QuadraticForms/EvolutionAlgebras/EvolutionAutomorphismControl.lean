import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl

open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open _root_.D5.S3.FiniteGroups.SuccessorQuotient
open _root_.D5.S3.FiniteGroups.SuccessorPowerAssignments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev CoordinateState (n : ℕ) :=
  {p : Product n × Module.Basis (Fin n) ℂ (Coord n) //
    (∀ i j : Fin n, i ≠ j → p.1 (p.2 i) (p.2 j) = 0) ∧ perfect p.1}

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ CoordinateState (fun _ => ℕ)

noncomputable def actual : Realization signature := realize signature (fun _ n s =>
  cycleWeight (beta (supportRelation s.val.1 s.val.2)
    (support_positive_degrees s.val.1 s.val.2 s.property.1 s.property.2).1
    (support_positive_degrees s.val.1 s.val.2 s.property.1 s.property.2).2))
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (μ : Product n) (b : Module.Basis (Fin n) ℂ (Coord n))
    (hb : ∀ i j : Fin n, i ≠ j → μ (b i) (b j) = 0) (hp : perfect μ),
    Nat.card (rho μ b hb hp).ker = R.readout () n ⟨(μ,b),hb,hp⟩

theorem actual_law : arena.Law actual := by
  intro n μ b hb hp
  exact diagonal_kernel_card μ b hb hp

end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
