import D5.S3.Quantum.Gauge.E8RootSystemUnification4D
import Reg.Support.UnitSixO.Common

/-! Source observations and interventions for the two exceptional weight families. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E8RootSystemUnification4D
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D (e6Roots H6 E6Rep27 qPsi cartanWeight)
open OmegaMath.ExceptionalEightBranching
open _root_.Reg.Support.UnitSixO (operandSignature)
open LeanInformationAudit
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Subsystems

abbrev signature : Signature := operandSignature (Finset E8Ambient) ℕ

abbrev arena : Arena where
  signature := signature
  Law R := e6Roots ⊆ e8Roots ∧ a2Roots ⊆ e8Roots ∧ R.readout () () a2Roots = 6 ∧
    (∀ i j, ⟪familySimple i, familySimple j⟫_ℝ = (a2Cartan i j : ℝ)) ∧ a2Cartan.det = 3 ∧
    Submodule.span ℝ (Set.range familySimple) = H6ᗮ ∧
    (∀ β, β ∈ a2Roots ↔ β ∈ e8Roots ∧ β ∈ H6ᗮ) ∧
    (∀ α ∈ e6Roots, ∀ β ∈ a2Roots, ⟪α, β⟫_ℝ = 0)

def family : Registration arena (type_of% (@e6_and_a2_subsystems_in_e8)) :=
  unitFamily% arena (@e6_and_a2_subsystems_in_e8) (unitObserve% Finset.card)
    (unitObserve% (fun _ => 0))
    (fun h => (by decide : (0 : ℕ) ≠ 6) (h.2.2.1))
    (by exact ⟨(), ∅, {0}, by simp [realize]⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6_and_a2_subsystems_in_e8) (Realization signature) Unit Unit :=
  unitBindE8%
    `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e6_and_a2_subsystems_in_e8.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Subsystems.family
    arena family (unitObserve% Finset.card) #[]
    #[{ path := unitPath% e6_and_a2_subsystems_in_e8 Finset.card 2 0
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }]

end Subsystems

namespace Partition

abbrev signature : Signature := operandSignature (Finset E8Ambient) ℕ

abbrev arena : Arena where
  signature := signature
  Law R := e6Roots ∪ a2Roots ∪ rep27x3Roots ∪ rep27barx3barRoots = e8Roots ∧
    Pairwise (fun i j : Fin 4 => Disjoint (branchPart i) (branchPart j)) ∧
    R.readout () () e6Roots = 72 ∧ a2Roots.card = 6 ∧ rep27x3Roots.card = 81 ∧
    rep27barx3barRoots.card = 81 ∧ 78 + 8 + 81 + 81 = 248

private def actual : Realization signature := unitObserve% Finset.card

private def vanishing : Realization signature := unitObserve% (fun _ => 0)

private theorem rejects_vanishing : ¬ arena.Law vanishing := by
  exact fun h => (by decide : (0 : ℕ) ≠ 72) h.2.2.1

private theorem source_bridge : (type_of% (@e8_e6_x_su3_branching_248)) ↔ arena.Law actual := by
  simp only [actual, realize]

def family : Registration arena (type_of% (@e8_e6_x_su3_branching_248)) where
  actual := unitObserve% Finset.card
  bridge := source_bridge
  variation := ⟨source_bridge.mp @e8_e6_x_su3_branching_248, vanishing, rejects_vanishing⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual vanishing rejects_vanishing
  dependence := fun _ => ⟨(), ∅, {0}, by simp [realize]⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8_e6_x_su3_branching_248) (Realization signature) Unit Unit :=
  unitBindE8%
    `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8_e6_x_su3_branching_248.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Partition.family
    arena family (unitObserve% Finset.card) #[]
    #[{ path := unitPath% e8_e6_x_su3_branching_248 Finset.card 2 0
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }]

end Partition

namespace Fibers

abbrev signature : Signature := operandSignature E8Ambient (ℝ × ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ f : Fin 3,
    (∀ v, v ∈ generationFiber f ↔ v ∈ e8Roots ∧ R.readout () () v = fundamentalWeight f) ∧
    (∀ v, v ∈ conjugateFiber f ↔ v ∈ e8Roots ∧ familyWeight v = -(fundamentalWeight f)) ∧
    (generationFiber f).card = 27 ∧ (conjugateFiber f).card = 27

private def actual : Realization signature := unitObserve% familyWeight

private def vanishing : Realization signature := unitObserve% (fun _ => (0, 0))

private theorem rejects_vanishing : ¬ arena.Law vanishing := by
  intro h
  have hv : generationRoot 0 0 ∈ generationFiber 0 :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hw : ((0, 0) : ℝ × ℝ) = fundamentalWeight 0 := ((h 0).1 _ |>.mp hv).2
  have he : (0 : ℝ) = 1 := congrArg Prod.fst hw
  norm_num at he

private theorem source_bridge : (type_of% (@e8_family_weight_fibers)) ↔ arena.Law actual := by
  simp only [actual, realize]

def family : Registration arena (type_of% (@e8_family_weight_fibers)) where
  actual := unitObserve% familyWeight
  bridge := source_bridge
  variation := ⟨source_bridge.mp @e8_family_weight_fibers, vanishing, rejects_vanishing⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual vanishing rejects_vanishing
  dependence := fun _ => ⟨(), 0, generationRoot 0 0, by
    intro h
    change familyWeight 0 = familyWeight (generationRoot 0 0) at h
    rw [generation_weight] at h
    have he : (0 : ℝ) = 1 := by simpa [familyWeight, fundamentalWeight] using congrArg Prod.fst h
    norm_num at he⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8_family_weight_fibers) (Realization signature) Unit Unit :=
  unitBindE8%
    `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8_family_weight_fibers.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Fibers.family
    arena family (unitObserve% familyWeight) #[]
    #[{ path := unitPath% e8_family_weight_fibers familyWeight 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Fibers

namespace Charges

abbrev signature : Signature := operandSignature E8Ambient ℝ

abbrev arena : Arena where
  signature := signature
  Law R := ∀ f : Fin 3,
    (∃ e : E6Rep27 ≃ ↥(generationFiber f), ∀ s,
      R.readout () () (e s).val = qPsi s ∧
      ∀ h : Fin 5 → ℝ, (∑ j, h j * (e s).val (firstIndex j)) = cartanWeight h s) ∧
    ((generationFiber f).filter fun v => psiCharge v = 1).card = 16 ∧
    ((generationFiber f).filter fun v => psiCharge v = -2).card = 10 ∧
    ((generationFiber f).filter fun v => psiCharge v = 4).card = 1

private def actual : Realization signature := unitObserve% psiCharge

private def vanishing : Realization signature := unitObserve% (fun _ => 0)

private theorem rejects_vanishing : ¬ arena.Law vanishing := by
  intro h
  obtain ⟨e, he⟩ := (h 0).1
  have hz : (0 : ℝ) = 4 := (he (.inr (.inr ()))).1
  norm_num at hz

private theorem source_bridge : (type_of% (@e8_e6_generation_weights)) ↔ arena.Law actual := by
  simp only [actual, realize]

def family : Registration arena (type_of% (@e8_e6_generation_weights)) where
  actual := unitObserve% psiCharge
  bridge := source_bridge
  variation := ⟨source_bridge.mp @e8_e6_generation_weights, vanishing, rejects_vanishing⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual vanishing rejects_vanishing
  dependence := fun _ => ⟨(), 0, generationRoot 0 0, by
    intro h
    change psiCharge 0 = psiCharge (generationRoot 0 0) at h
    rw [generation_charge] at h
    norm_num [psiCharge, chargeCode] at h⟩

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8_e6_generation_weights) (Realization signature) Unit Unit :=
  unitBindE8%
    `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8_e6_generation_weights.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Charges.family
    arena family (unitObserve% psiCharge) #[]
    #[{ path := unitPath% e8_e6_generation_weights psiCharge 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Charges

namespace Lowering

abbrev signature : Signature := operandSignature (Fin 27) E8Ambient

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Fin 27,
    R.readout () () i = generationRoot 0 i - familySimple 0 ∧
    generationRoot 2 i = generationRoot 1 i - familySimple 1

def family : Registration arena (type_of% (@e8_family_root_steps)) :=
  unitFamily% arena (@e8_family_root_steps) (unitObserve% (generationRoot 1))
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have hzero : 0 = generationRoot 1 0 := ((h 0).1).trans (e8_family_root_steps 0).1.symm
      have hn := e8Roots_simply_laced (generationRoot_mem 1 0)
      rw [← hzero] at hn
      norm_num at hn)
    (by
      refine ⟨(), 0, 1, ?_⟩
      change generationRoot 1 0 ≠ generationRoot 1 1
      exact (generation_injective 1).ne (by decide))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8_family_root_steps) (Realization signature) Unit Unit :=
  unitBindE8%
    `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8_family_root_steps.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Lowering.family
    arena family (unitObserve% (generationRoot 1)) #[]
    #[{ path := unitPath% e8_family_root_steps generationRoot 1 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Lowering

end

end Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D
