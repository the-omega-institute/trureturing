import D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity

open _root_.D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

noncomputable section

universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Multiset ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ m => z m) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : Multiset ℕ) (s : Finset ℕ), m.toFinset ⊆ s →
    R.readout () () m = ∏ i ∈ s, i ^ m.count i * (m.count i).factorial

theorem actual_law : arena.Law actual := hz_prod

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 ∅ (by simp)
  change 0 = _ at hh
  simpa using hh

def registration : Registration arena (type_of% (@hz_prod)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hz_prod, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, {2}, ?_⟩
    change z 0 ≠ z {2}
    norm_num [z] }

abbrev permutationArena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α),
    R.readout () () σ.partition.parts =
      (Fintype.card α - σ.cycleType.sum).factorial * σ.cycleType.prod *
        ∏ i ∈ σ.cycleType.toFinset, (σ.cycleType.count i).factorial

theorem permutation_actual_law : (permutationArena.{u}).Law actual := @hz_perm

theorem permutation_rejected_law : ¬ (permutationArena.{u}).Law rejected := by
  intro h
  have hh := h (1 : Equiv.Perm (ULift.{u} (Fin 0)))
  change 0 = _ at hh
  simpa using hh

def permutationRegistration : Registration (permutationArena.{u})
    (type_of% (@hz_perm.{u})) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hz_perm, rejected, permutation_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ permutation_rejected_law
  dependence := registration.dependence }

end

end Reg.D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity
