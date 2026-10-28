import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily

open LeanInformationAudit
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
open _root_.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun n => Equiv.Perm (Fin n)) (fun _ => ℕ)

def actual : Realization signature := realize signature
  (fun _ _ σ => Nat.card (Aut (permutationProduct σ))) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ σ => weight σ.partition.parts + 1) (fun e => nomatch e)

abbrev orderArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)),
    Finite (Aut (permutationProduct σ)) ∧ R.readout () n σ = weight σ.partition.parts

theorem order_actual_law : orderArena.Law actual := @permutation_aut_card

theorem order_rejected_law : ¬ orderArena.Law rejected := by
  intro h
  have hh := (h (1 : Equiv.Perm (Fin 0))).2
  change weight _ + 1 = weight _ at hh
  omega

abbrev familyArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (σ : Equiv.Perm (Fin n)),
    commutative (permutationProduct σ) ∧ hasNaturalBasis (permutationProduct σ) ∧
      perfect (permutationProduct σ) ∧ Finite (Aut (permutationProduct σ)) ∧
      R.readout () n σ = weight σ.partition.parts

theorem family_actual_law : familyArena.Law actual := @permutation_family

theorem family_rejected_law : ¬ familyArena.Law rejected := by
  intro h
  have hh := (h (1 : Equiv.Perm (Fin 0))).2.2.2.2
  change weight _ + 1 = weight _ at hh
  omega

private theorem actual_depends : ObservationalDependence signature actual := by
  intro i
  let τ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hτ : τ.cycleType = {2} :=
    Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
  have hsupp : τ.support.card = 2 := by
    rw [← Equiv.Perm.sum_cycleType, hτ]
    rfl
  have hleft := (permutation_aut_card (1 : Equiv.Perm (Fin 2))).2
  have hright := (permutation_aut_card τ).2
  refine ⟨2, 1, τ, ?_⟩
  change Nat.card (Aut (permutationProduct (1 : Equiv.Perm (Fin 2)))) ≠
    Nat.card (Aut (permutationProduct τ))
  rw [hleft, hright, Equiv.Perm.parts_partition, Equiv.Perm.parts_partition,
    ← Equiv.Perm.sum_cycleType, hτ]
  norm_num [weight, hsupp]

def orderRegistration : Registration orderArena (type_of% (@permutation_aut_card)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@permutation_aut_card, rejected, order_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ order_rejected_law
  dependence := actual_depends }

def familyRegistration : Registration familyArena (type_of% (@permutation_family)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@permutation_family, rejected, family_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ family_rejected_law
  dependence := actual_depends }

def orderAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@permutation_aut_card) (type_of% actual) (ℕ → Type) Unit := {
  unitName := `D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_aut_card.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.orderRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨orderArena⟩
  objectArena := .source ⟨orderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source orderArena ⟨orderRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

def familyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@permutation_family) (type_of% actual) (ℕ → Type) Unit := {
  unitName := `D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.permutation_family.__information_unit
  realizationName := `Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨familyArena⟩
  objectArena := .source ⟨familyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source familyArena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionPermutationFamily
