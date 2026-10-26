import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound

open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
open _root_.D5.S3.FiniteGroups.SuccessorPowerAssignments
open _root_.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v

structure PermutationState (Q : Type u) where
  finiteCarrier : Fintype Q
  decidableCarrier : DecidableEq Q
  permutation : Equiv.Perm Q

abbrev permutationSignature : Signature where
  Params := Type u
  State := PermutationState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def permutationActual : Realization permutationSignature :=
  realize permutationSignature (fun _ Q s =>
    letI := s.finiteCarrier
    letI := s.decidableCarrier
    weight s.permutation.partition.parts) (fun e => nomatch e)

noncomputable def permutationRejected : Realization permutationSignature :=
  realize permutationSignature (fun _ Q s =>
    letI := s.finiteCarrier
    letI := s.decidableCarrier
    weight s.permutation.partition.parts + 1) (fun e => nomatch e)

abbrev permutationArena : Arena where
  signature := permutationSignature
  Law R := ∀ {Q : Type u} [Fintype Q] [DecidableEq Q] (β : Equiv.Perm Q),
    cycleWeight β * Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm Q))) =
      R.readout () Q ⟨inferInstance, inferInstance, β⟩

theorem permutation_actual_law : permutationArena.Law permutationActual :=
  @cycle_weight_centralizer

theorem permutation_rejected_law : ¬ (permutationArena.{u}).Law permutationRejected := by
  intro h
  let Q := ULift.{u} (Fin 0)
  have hh := h (1 : Equiv.Perm Q)
  have ha := cycle_weight_centralizer (1 : Equiv.Perm Q)
  change cycleWeight _ * Nat.card _ = weight _ + 1 at hh
  have hbad : weight (1 : Equiv.Perm Q).partition.parts =
      weight (1 : Equiv.Perm Q).partition.parts + 1 := ha.symm.trans hh
  omega

abbrev upperSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def upperActual : Realization upperSignature :=
  realize upperSignature (fun _ _ n => maximumWeight n) (fun e => nomatch e)

abbrev upperArena : Arena where
  signature := upperSignature
  Law R := ∀ {A : Type u} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    {ι : Type v} [Fintype ι] {n : ℕ} (hn : 1 ≤ n) (hd : Module.finrank ℂ A = n)
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (b : Module.Basis ι ℂ A)
    (hb : ∀ i j : ι, i ≠ j → μ (b i) (b j) = 0) (hp : productSpan μ = ⊤),
    Finite (Aut μ) ∧ Nat.card (Aut μ) ≤ R.readout () () n

theorem upper_actual_law : upperArena.Law upperActual := @finite_and_bound

end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
