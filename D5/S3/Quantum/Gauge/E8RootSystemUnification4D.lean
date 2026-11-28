/- GID: D5/S3/Quantum/Gauge/E8RootSystemUnification4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/E8RootSystemUnification4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exceptional roots, orthogonal family weights and the two conjugate branches. -/

import OmegaBuild.Commands
import D5.S3.LinearAlgebra.RootSystem.ExceptionalEightBranching
import D5.S3.Quantum.Gauge.E6TrinificationUnification4D

/-! The exceptional root system and its root-level decomposition into the six-dimensional
exceptional subsystem, the orthogonal family subsystem and two conjugate weight families. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators InnerProductSpace

namespace D5.S3.Quantum.Gauge.E8RootSystemUnification4D

open E6TrinificationUnification4D (e6Roots H6 e6SimpleRoot E6Rep27 qPsi cartanWeight)
open OmegaMath.ExceptionalEightBranching
open scoped Matrix

abbrev E8Ambient := OmegaMath.ExceptionalEight.Ambient

noncomputable abbrev e8Roots := OmegaMath.ExceptionalEight.roots
noncomputable abbrev e8SimpleRoot := OmegaMath.ExceptionalEight.simple
abbrev e8Cartan := OmegaMath.ExceptionalEight.cartan

theorem e8Roots_card : e8Roots.card = 240 := OmegaMath.ExceptionalEight.card_roots

theorem e8_lie_algebra_dimension : 8 + e8Roots.card = 248 := by
  rw [e8Roots_card]

theorem e8Roots_simply_laced {α : E8Ambient} (hα : α ∈ e8Roots) :
    ⟪α, α⟫_ℝ = 2 := OmegaMath.ExceptionalEight.root_norm hα

theorem e8Roots_crystallographic_inner_products {α β : E8Ambient}
    (hα : α ∈ e8Roots) (hβ : β ∈ e8Roots) :
    ⟪α, β⟫_ℝ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) ∧
    (⟪α, β⟫_ℝ = 2 ↔ α = β) ∧ (⟪α, β⟫_ℝ = -2 ↔ α = -β) :=
  OmegaMath.ExceptionalEight.root_products hα hβ

theorem e8Roots_weyl_reflection_closed {α β : E8Ambient}
    (hα : α ∈ e8Roots) (hβ : β ∈ e8Roots) :
    β - ⟪α, β⟫_ℝ • α ∈ e8Roots ∧ -α ∈ e8Roots :=
  ⟨OmegaMath.ExceptionalEight.root_reflection hα hβ, OmegaMath.ExceptionalEight.root_neg hα⟩

theorem e8_dynkin_simple_roots :
    (∀ i, e8SimpleRoot i ∈ e8Roots) ∧
    (∀ i j, ⟪e8SimpleRoot i, e8SimpleRoot j⟫_ℝ = (e8Cartan i j : ℝ)) ∧
    e8Cartan.det = 1 ∧
    LinearIndependent ℝ e8SimpleRoot ∧
    (∀ α ∈ e8Roots, ∃ c : Fin 8 → ℤ, α = ∑ i, (c i : ℝ) • e8SimpleRoot i ∧
      ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0))) ∧
    (∀ i : Fin 6, e8SimpleRoot (Fin.castLE (by decide : 6 ≤ 8) i) = e6SimpleRoot i) :=
  OmegaMath.ExceptionalEight.simple_system

theorem e6_and_a2_subsystems_in_e8 :
    e6Roots ⊆ e8Roots ∧ a2Roots ⊆ e8Roots ∧ a2Roots.card = 6 ∧
    (∀ i j, ⟪familySimple i, familySimple j⟫_ℝ = (a2Cartan i j : ℝ)) ∧ a2Cartan.det = 3 ∧
    Submodule.span ℝ (Set.range familySimple) = H6ᗮ ∧
    (∀ β, β ∈ a2Roots ↔ β ∈ e8Roots ∧ β ∈ H6ᗮ) ∧
    (∀ α ∈ e6Roots, ∀ β ∈ a2Roots, ⟪α, β⟫_ℝ = 0) := by
  refine ⟨OmegaMath.ExceptionalEight.six_subset, fun _ h => ((a2_exact _).mp h).1,
    a2_card, a2_cartan.1, a2_cartan.2, family_span, a2_exact, ?_⟩
  intro α hα β hβ
  exact Submodule.inner_right_of_mem_orthogonal
    (OmegaMath.ExceptionalSix.roots_rank_six.1 α hα) ((a2_exact _).mp hβ).2

theorem e8_e6_x_su3_branching_248 :
    e6Roots ∪ a2Roots ∪ rep27x3Roots ∪ rep27barx3barRoots = e8Roots ∧
    Pairwise (fun i j : Fin 4 => Disjoint (branchPart i) (branchPart j)) ∧
    e6Roots.card = 72 ∧ a2Roots.card = 6 ∧ rep27x3Roots.card = 81 ∧
    rep27barx3barRoots.card = 81 ∧ 78 + 8 + 81 + 81 = 248 := by
  obtain ⟨he, hd, h₁, h₂, h₃, h₄⟩ := partition
  exact ⟨he, hd, h₁, h₂, h₃, h₄, by decide⟩

theorem e8_family_weight_fibers (f : Fin 3) :
    (∀ v, v ∈ generationFiber f ↔ v ∈ e8Roots ∧ familyWeight v = fundamentalWeight f) ∧
    (∀ v, v ∈ conjugateFiber f ↔ v ∈ e8Roots ∧ familyWeight v = -(fundamentalWeight f)) ∧
    (generationFiber f).card = 27 ∧ (conjugateFiber f).card = 27 :=
  weight_fibers f

private def stateIndex : E6Rep27 → Fin 27
  | .inl i => Fin.ofNat 27 i.val
  | .inr (.inl (.inl i)) => Fin.ofNat 27 (16 + i.val)
  | .inr (.inl (.inr i)) => Fin.ofNat 27 (21 + i.val)
  | .inr (.inr _) => 26

private theorem stateIndex_bijective : Function.Bijective stateIndex := by
  constructor
  · have h : ∀ s t : E6Rep27, stateIndex s = stateIndex t → s = t := by decide
    exact h
  · have h : ∀ i : Fin 27, ∃ s, stateIndex s = i := by decide
    exact h

private noncomputable def generationEquiv (f : Fin 3) : E6Rep27 ≃ ↥(generationFiber f) :=
  (Equiv.ofBijective stateIndex stateIndex_bijective).trans
    (Equiv.ofBijective
      (fun i : Fin 27 => ⟨generationRoot f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
      ⟨fun i j h => generation_injective f (congrArg Subtype.val h), fun v => by
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp v.property
        exact ⟨i, Subtype.ext hi⟩⟩)

private theorem state_charge (s : E6Rep27) : (chargeCode (stateIndex s) : ℝ) = qPsi s := by
  rcases s with (s | ((s | s) | s))
  · fin_cases s <;> norm_num [chargeCode, stateIndex, qPsi, Fin.ofNat]
  · fin_cases s <;> norm_num [chargeCode, stateIndex, qPsi, Fin.ofNat]
  · fin_cases s <;> norm_num [chargeCode, stateIndex, qPsi, Fin.ofNat]
  · cases s
    norm_num [chargeCode, stateIndex, qPsi, Fin.ofNat]

private theorem state_cartan (h : Fin 5 → ℝ) (s : E6Rep27) :
    (∑ j, h j * ((highestCode (stateIndex s) (firstIndex j) : ℤ) : ℝ) / 2) =
      cartanWeight h s := by
  rcases s with (s | ((s | s) | s))
  · change _ = OmegaMath.SpinorWeights5.cartan h (OmegaMath.SpinorWeights5.evenWeight s).1
    unfold OmegaMath.SpinorWeights5.cartan
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_assoc]
    congr 1
    let w := (OmegaMath.SpinorWeights5.evenWeight s).val
    have he : highestCode (stateIndex (.inl s)) (firstIndex j) =
        if w j then (1 : ℤ) else -1 := by
      fin_cases s <;> fin_cases j <;> rfl
    change (highestCode (stateIndex (.inl s)) (firstIndex j) : ℝ) / 2 =
      OmegaMath.SpinorWeights5.H w j
    rw [he]
    cases hw : w j <;> norm_num [OmegaMath.SpinorWeights5.H, hw]
  · fin_cases s <;> norm_num [highestCode, stateIndex, firstIndex, cartanWeight,
      Fin.sum_univ_succ, Fin.ofNat, Fin.castLE]
  · fin_cases s <;> norm_num [highestCode, stateIndex, firstIndex, cartanWeight,
      Fin.sum_univ_succ, Fin.ofNat, Fin.castLE] <;> ring
  · cases s
    norm_num [highestCode, stateIndex, firstIndex, cartanWeight, Fin.sum_univ_succ, Fin.castLE]

theorem e8_e6_generation_weights (f : Fin 3) :
    (∃ e : E6Rep27 ≃ ↥(generationFiber f), ∀ s,
      psiCharge (e s).val = qPsi s ∧
      ∀ h : Fin 5 → ℝ, (∑ j, h j * (e s).val (firstIndex j)) = cartanWeight h s) ∧
    ((generationFiber f).filter fun v => psiCharge v = 1).card = 16 ∧
    ((generationFiber f).filter fun v => psiCharge v = -2).card = 10 ∧
    ((generationFiber f).filter fun v => psiCharge v = 4).card = 1 := by
  refine ⟨⟨generationEquiv f, fun s => ⟨?_, ?_⟩⟩, generation_charge_cards f⟩
  · change psiCharge (generationRoot f (stateIndex s)) = _
    exact (generation_charge f (stateIndex s)).trans (state_charge s)
  · intro h
    change (∑ j, h j * generationRoot f (stateIndex s) (firstIndex j)) = _
    simpa only [generation_head, mul_div_assoc] using state_cartan h s

theorem e8_family_root_steps (i : Fin 27) :
    generationRoot 1 i = generationRoot 0 i - familySimple 0 ∧
    generationRoot 2 i = generationRoot 1 i - familySimple 1 :=
  generation_steps i

end D5.S3.Quantum.Gauge.E8RootSystemUnification4D
