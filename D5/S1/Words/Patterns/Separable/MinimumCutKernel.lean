/- GID: D5/S1/Words/Patterns/Separable/MinimumCutKernel
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/MinimumCutKernel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual minimum cuts give Cartesian conditional shape laws and literal labels. -/

import D5.S1.Words.Patterns.Separable.CutFactorization
import Mathlib.Probability.Distributions.Uniform
import Mathlib.SetTheory.Cardinal.Finite

/-!
The carrier is the actual avoiding-permutation subtype, not a recursive sampler.
The minimum cut is not the greatest-cut random variable. The probability is the
finite uniform cardinal law on the whole actual class, before conditioning.
These are unbounded symbolic statements, not certified finite instances.
-/

namespace D5.S1.Words.Patterns.Separable.MinimumCutKernel

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.ProperCut (pattern2413 pattern3142)
open scoped ENNReal

def HasProperCut {n : ℕ} (sign : Bool) (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ cut, 0 < cut ∧ cut < n ∧ Cut sign π cut

def MinimumCut {n : ℕ} (sign : Bool) (π : Equiv.Perm (Fin n)) (length : ℕ) : Prop :=
  Cut sign π length ∧ ∀ smaller, 0 < smaller → smaller < length → ¬Cut sign π smaller

abbrev Indecomposable (sign : Bool) (length : ℕ) :=
  {π : Avoider length // ¬HasProperCut sign π.val}

abbrev MinimumFiber (sign : Bool) (left right : ℕ) :=
  {π : Avoider (left + right) // MinimumCut sign π.val left}

def EndpointEvent (sign : Bool) (left right : ℕ)
    (leftEvent : Indecomposable sign left → Prop) (rightEvent : Avoider right → Prop)
    (π : Avoider (left + right)) : Prop :=
  ∃ α : Indecomposable sign left, ∃ β : Avoider right,
    leftEvent α ∧ rightEvent β ∧ blockSum sign α.val.val β.val = π.val

def identityAvoider (length : ℕ) : Avoider length :=
  ⟨Equiv.refl _, by
    constructor
    · rintro ⟨embedding, order⟩
      have increasing := embedding.strictMono (show (1 : Fin 4) < 2 by decide)
      have decreasing : ¬pattern2413 (1 : Fin 4) < pattern2413 2 := by decide
      exact decreasing ((order 1 2).mpr increasing)
    · rintro ⟨embedding, order⟩
      have increasing := embedding.strictMono (show (0 : Fin 4) < 1 by decide)
      have decreasing : ¬pattern3142 (0 : Fin 4) < pattern3142 1 := by decide
      exact decreasing ((order 0 1).mpr increasing)⟩

noncomputable def actualMass (length : ℕ) (event : Avoider length → Prop) : ℝ := by
  classical
  let : Nonempty (Avoider length) := ⟨identityAvoider length⟩
  exact ((PMF.uniformOfFintype (Avoider length)).toOuterMeasure {π | event π}).toReal

open Classical in
theorem minimum_cut_cartesian_kernel (sign : Bool) (left right : ℕ)
    (hleft : 0 < left) (hright : 0 < right) :
    ∃ equivalence : Indecomposable sign left × Avoider right ≃ MinimumFiber sign left right,
      (∀ factors, (equivalence factors).val.val =
        blockSum sign factors.1.val.val factors.2.val) ∧
      (∀ leftEvent rightEvent,
        Nat.card {π : Avoider (left + right) //
          EndpointEvent sign left right leftEvent rightEvent π} =
          Nat.card {α : Indecomposable sign left // leftEvent α} *
            Nat.card {β : Avoider right // rightEvent β} ∧
        actualMass (left + right) (EndpointEvent sign left right leftEvent rightEvent) =
          (Nat.card {α : Indecomposable sign left // leftEvent α} : ℝ) *
            Nat.card {β : Avoider right // rightEvent β} / Nat.card (Avoider (left + right)) ∧
        actualMass (left + right) (EndpointEvent sign left right leftEvent rightEvent) /
            actualMass (left + right) (fun π => MinimumCut sign π.val left) =
          ((Nat.card {α : Indecomposable sign left // leftEvent α} : ℝ) /
              Nat.card (Indecomposable sign left)) *
            ((Nat.card {β : Avoider right // rightEvent β} : ℝ) / Nat.card (Avoider right))) ∧
      (∀ factors (position : Fin left),
        ((equivalence factors).val.val (Fin.castAdd right position)).val =
          (if sign then right else 0) + (factors.1.val.val position).val) ∧
      (∀ factors (position : Fin right),
        ((equivalence factors).val.val (Fin.natAdd left position)).val =
          (if sign then 0 else left) + (factors.2.val position).val) := by
  classical
  have leftval (α : Equiv.Perm (Fin left)) (β : Equiv.Perm (Fin right))
      (position : Fin left) :
      (blockSum sign α β (Fin.castAdd right position)).val =
        (if sign then right else 0) + (α position).val := by
    cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
  have rightval (α : Equiv.Perm (Fin left)) (β : Equiv.Perm (Fin right))
      (position : Fin right) :
      (blockSum sign α β (Fin.natAdd left position)).val =
        (if sign then 0 else left) + (β position).val := by
    cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
  have prefixCut (α : Equiv.Perm (Fin left)) (β : Equiv.Perm (Fin right))
      (smaller : ℕ) (hsmaller : smaller < left) :
      Cut sign (blockSum sign α β) smaller ↔ Cut sign α smaller := by
    constructor
    · intro cut first last hfirst hlast
      have comparison := cut (Fin.castAdd right first) (Fin.castAdd right last) hfirst hlast
      cases sign <;> simpa only [Bool.false_eq_true, ↓reduceIte, Fin.lt_def,
        leftval, Nat.add_lt_add_iff_left] using comparison
    · intro cut first last hfirst hlast
      have firstLeft : first.val < left := by omega
      have firstEq : first = Fin.castAdd right ⟨first.val, firstLeft⟩ := Fin.ext rfl
      by_cases lastLeft : last.val < left
      · have lastEq : last = Fin.castAdd right ⟨last.val, lastLeft⟩ := Fin.ext rfl
        rw [firstEq, lastEq]
        have comparison := cut ⟨first.val, firstLeft⟩ ⟨last.val, lastLeft⟩ hfirst hlast
        cases sign <;> simpa only [Bool.false_eq_true, ↓reduceIte, Fin.lt_def,
          leftval, Nat.add_lt_add_iff_left] using comparison
      · have lastEq : last = Fin.natAdd left ⟨last.val - left, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [firstEq, lastEq]
        cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.lt_def,
          leftval, rightval, Nat.zero_add]
        all_goals omega
  let assemble (factors : Indecomposable sign left × Avoider right) :
      Avoider (left + right) :=
    ⟨blockSum sign factors.1.val.val factors.2.val,
      (avoids_block_sum_iff sign _ _).mpr ⟨factors.1.val.property, factors.2.property⟩⟩
  have minimal (factors : Indecomposable sign left × Avoider right) :
      MinimumCut sign (assemble factors).val left := by
    refine ⟨(fixed_cut_factorization hleft hright sign (assemble factors)).mpr ?_, ?_⟩
    · refine ⟨(factors.1.val, factors.2), rfl, ?_⟩
      intro other equality
      apply Prod.ext
      · apply Subtype.ext
        apply Equiv.ext
        intro position
        apply Fin.ext
        have comparison := congrArg (fun π : Equiv.Perm (Fin (left + right)) =>
          (π (Fin.castAdd right position)).val) equality
        dsimp [assemble] at comparison
        rw [leftval, leftval] at comparison
        exact Nat.add_left_cancel comparison
      · apply Subtype.ext
        apply Equiv.ext
        intro position
        apply Fin.ext
        have comparison := congrArg (fun π : Equiv.Perm (Fin (left + right)) =>
          (π (Fin.natAdd left position)).val) equality
        dsimp [assemble] at comparison
        rw [rightval, rightval] at comparison
        exact Nat.add_left_cancel comparison
    · intro smaller hpositive hsmaller cut
      exact factors.1.property ⟨smaller, hpositive, hsmaller,
        (prefixCut _ _ smaller hsmaller).mp cut⟩
  let forward (factors : Indecomposable sign left × Avoider right) : MinimumFiber sign left right :=
    ⟨assemble factors, minimal factors⟩
  have surjective : Function.Surjective forward := by
    intro π
    obtain ⟨factors, equality, _⟩ :=
      (fixed_cut_factorization hleft hright sign π.val).mp π.property.1
    have indecomposable : ¬HasProperCut sign factors.1.val := by
      rintro ⟨smaller, hpositive, hsmaller, cut⟩
      apply π.property.2 smaller hpositive hsmaller
      rw [← equality]
      exact (prefixCut _ _ smaller hsmaller).mpr cut
    refine ⟨(⟨factors.1, indecomposable⟩, factors.2), ?_⟩
    exact Subtype.ext (Subtype.ext equality)
  have injective : Function.Injective forward := by
    intro first last equality
    have reconstruction := congrArg (fun π => π.val.val) equality
    have unique := (fixed_cut_factorization hleft hright sign (assemble last)).mp
      (minimal last).1
    obtain ⟨factors, _, uniqueness⟩ := unique
    have same : (first.1.val, first.2) = (last.1.val, last.2) :=
      (uniqueness _ reconstruction).trans (uniqueness _ rfl).symm
    have sameRight : first.2 = last.2 :=
      congrArg (fun pair : Avoider left × Avoider right => pair.2) same
    exact Prod.ext (Subtype.ext (congrArg Prod.fst same)) sameRight
  let equivalence := Equiv.ofBijective forward ⟨injective, surjective⟩
  have counts (leftEvent : Indecomposable sign left → Prop) (rightEvent : Avoider right → Prop) :
      Nat.card {π : Avoider (left + right) //
        EndpointEvent sign left right leftEvent rightEvent π} =
        Nat.card {α : Indecomposable sign left // leftEvent α} *
          Nat.card {β : Avoider right // rightEvent β} := by
    let mapping : {α : Indecomposable sign left // leftEvent α} ×
        {β : Avoider right // rightEvent β} →
        {π : Avoider (left + right) // EndpointEvent sign left right leftEvent rightEvent π} :=
      fun factors => ⟨assemble (factors.1.val, factors.2.val),
        factors.1.val, factors.2.val, factors.1.property, factors.2.property, rfl⟩
    have bijective : Function.Bijective mapping := by
      constructor
      · intro first last equality
        have sameActual : assemble (first.1.val, first.2.val) =
            assemble (last.1.val, last.2.val) :=
          congrArg (fun π : {π : Avoider (left + right) //
            EndpointEvent sign left right leftEvent rightEvent π} => π.val) equality
        have same := injective (Subtype.ext sameActual)
        exact Prod.ext (Subtype.ext (congrArg Prod.fst same))
          (Subtype.ext (congrArg Prod.snd same))
      · rintro ⟨π, α, β, hα, hβ, equality⟩
        exact ⟨(⟨α, hα⟩, ⟨β, hβ⟩), Subtype.ext (Subtype.ext equality)⟩
    rw [← Nat.card_congr (Equiv.ofBijective mapping bijective), Nat.card_prod]
  have mass (event : Avoider (left + right) → Prop) :
      actualMass (left + right) event =
        (Nat.card {π : Avoider (left + right) // event π} : ℝ) /
          Nat.card (Avoider (left + right)) := by
    let : Nonempty (Avoider (left + right)) := ⟨identityAvoider _⟩
    change ((PMF.uniformOfFintype (Avoider (left + right))).toOuterMeasure
      {π | event π}).toReal = _
    rw [PMF.toOuterMeasure_uniformOfFintype_apply]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
      Nat.card_eq_fintype_card]
    have cardEvent := Fintype.card_congr (Equiv.subtypeEquivRight
      (fun π : Avoider (left + right) =>
        show (π ∈ {π | event π}) ↔ event π from Iff.rfl))
    rw [cardEvent]
  have fiberCount : Nat.card (MinimumFiber sign left right) =
      Nat.card (Indecomposable sign left) * Nat.card (Avoider right) := by
    rw [← Nat.card_congr equivalence, Nat.card_prod]
  have totalPositive : (Nat.card (Avoider (left + right)) : ℝ) ≠ 0 := by
    let : Nonempty (Avoider (left + right)) := ⟨identityAvoider _⟩
    exact_mod_cast (Nat.card_pos (α := Avoider (left + right))).ne'
  refine ⟨equivalence, fun _ => rfl, ?_, ?_, ?_⟩
  · intro leftEvent rightEvent
    refine ⟨counts leftEvent rightEvent, ?_, ?_⟩
    · rw [mass, counts, Nat.cast_mul]
    · rw [mass, mass, counts, fiberCount, Nat.cast_mul, Nat.cast_mul]
      simp only [div_div_div_cancel_right₀ totalPositive, mul_div_mul_comm]
  · intro factors position
    exact leftval _ _ position
  · intro factors position
    exact rightval _ _ position

#print axioms minimum_cut_cartesian_kernel

end D5.S1.Words.Patterns.Separable.MinimumCutKernel
