/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Three full primitive lift orbits admit precisely local cube roots or a conjugate three-cycle. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.TwoOrbitSquareRootCriterion
import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ThreeOrbitCubeRootCharts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ThreeOrbitCubeRootCriterion

open PrimitiveLiftRootCriterion
open TwoOrbitSquareRootCriterion (signed_phase disjoint_lifts)
open ThreeOrbitCubeRootCharts
open EssentialWordRealization FiniteWindowTableCriterion FixedBlockRigidity
open FixedBlockRigidity.BlockCoordinates OrderedGroupChainHistories
open CountedGroupOverlap (GroupMat Path)

universe u
variable {H : Type u} [Group H] {n : ℕ} (C : GroupMat H n n)
  (p₀ p₁ p₂ : Path C)

/-- All original expanded histories over the three signed base orbits. -/
def OrbitUnion := {x : History (expandedGraph C) //
  (∃ t : ℤ, forgetHistory x = translate (baseGraph C) t p₀) ∨
  (∃ t : ℤ, forgetHistory x = translate (baseGraph C) t p₁) ∨
  (∃ t : ℤ, forgetHistory x = translate (baseGraph C) t p₂)}

/-- The original one-step shift, restricted to the full union. -/
def unionShift : OrbitUnion C p₀ p₁ p₂ → OrbitUnion C p₀ p₁ p₂ := fun x =>
  ⟨shift (expandedGraph C) x.val, by
    have step : ∀ (p : Path C) (t : ℤ),
        forgetHistory x.val = translate (baseGraph C) t p →
        forgetHistory (shift (expandedGraph C) x.val) =
          translate (baseGraph C) (t+1) p := by
      intro p t ht
      change shift (baseGraph C) (forgetHistory x.val) = _
      rw [ht]
      apply Subtype.ext
      funext i
      simp [shift,translate,add_comm,add_left_comm]
    rcases x.property with ⟨t,ht⟩ | ⟨t,ht⟩ | ⟨t,ht⟩
    · exact Or.inl ⟨t+1,step p₀ t ht⟩
    · exact Or.inr (Or.inl ⟨t+1,step p₁ t ht⟩)
    · exact Or.inr (Or.inr ⟨t+1,step p₂ t ht⟩)⟩

/-- Every original left deck operation acts on the entire union. -/
def unionDeck (a : H) : OrbitUnion C p₀ p₁ p₂ → OrbitUnion C p₀ p₁ p₂ := fun x =>
  ⟨groupHistory C a x.val,x.property⟩

variable {d₀ d₁ d₂ : ℕ}

private def join : LiftOrbit C p₀ d₀ ⊕ (LiftOrbit C p₁ d₁ ⊕ LiftOrbit C p₂ d₂) →
    OrbitUnion C p₀ p₁ p₂ :=
  Sum.elim (fun x => ⟨x.val,Or.inl (by
    obtain ⟨q,hq⟩ := x.property
    exact ⟨q.val,hq.trans (shift_iterate_translate (baseGraph C) q.val p₀)⟩)⟩)
    (Sum.elim (fun x => ⟨x.val,Or.inr (Or.inl (by
      obtain ⟨q,hq⟩ := x.property
      exact ⟨q.val,hq.trans (shift_iterate_translate (baseGraph C) q.val p₁)⟩))⟩)
      (fun x => ⟨x.val,Or.inr (Or.inr (by
        obtain ⟨q,hq⟩ := x.property
        exact ⟨q.val,hq.trans (shift_iterate_translate (baseGraph C) q.val p₂)⟩))⟩))

variable (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
  (hm₀ : Function.minimalPeriod (CountedGroupOverlap.shift C) p₀ = d₀)
  (hm₁ : Function.minimalPeriod (CountedGroupOverlap.shift C) p₁ = d₁)
  (hm₂ : Function.minimalPeriod (CountedGroupOverlap.shift C) p₂ = d₂)
  (hdis₀₁ : ∀ t : ℤ, translate (baseGraph C) t p₀ ≠ p₁)
  (hdis₀₂ : ∀ t : ℤ, translate (baseGraph C) t p₀ ≠ p₂)
  (hdis₁₂ : ∀ t : ℤ, translate (baseGraph C) t p₁ ≠ p₂)

private def unionEquiv :
    LiftOrbit C p₀ d₀ ⊕ (LiftOrbit C p₁ d₁ ⊕ LiftOrbit C p₂ d₂) ≃
      OrbitUnion C p₀ p₁ p₂ :=
  Equiv.ofBijective (join C p₀ p₁ p₂) (by
    constructor
    · intro x y h
      have hv := congrArg (fun z : OrbitUnion C p₀ p₁ p₂ => z.val) h
      rcases x with x | (x | x) <;> rcases y with y | (y | y)
      · exact congrArg Sum.inl (Subtype.ext hv)
      · exact (disjoint_lifts C p₀ p₁ hdis₀₁ x.val x.property
          (hv.symm ▸ y.property)).elim
      · exact (disjoint_lifts C p₀ p₂ hdis₀₂ x.val x.property
          (hv.symm ▸ y.property)).elim
      · exact (disjoint_lifts C p₀ p₁ hdis₀₁ x.val
          (hv.symm ▸ y.property) x.property).elim
      · exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hv))
      · exact (disjoint_lifts C p₁ p₂ hdis₁₂ x.val x.property
          (hv.symm ▸ y.property)).elim
      · exact (disjoint_lifts C p₀ p₂ hdis₀₂ x.val
          (hv.symm ▸ y.property) x.property).elim
      · exact (disjoint_lifts C p₁ p₂ hdis₁₂ x.val
          (hv.symm ▸ y.property) x.property).elim
      · exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext hv))
    · intro x
      rcases x.property with h₀ | h₁ | h₂
      · exact ⟨.inl ⟨x.val,(signed_phase C p₀ d₀ hd₀ hm₀ x.val).1 h₀⟩,Subtype.ext rfl⟩
      · exact ⟨.inr (.inl ⟨x.val,(signed_phase C p₁ d₁ hd₁ hm₁ x.val).1 h₁⟩),
          Subtype.ext rfl⟩
      · exact ⟨.inr (.inr ⟨x.val,(signed_phase C p₂ d₂ hd₂ hm₂ x.val).1 h₂⟩),
          Subtype.ext rfl⟩)

include hd₀ hd₁ hd₂ hm₀ hm₁ hm₂ hdis₀₁ hdis₀₂ hdis₁₂ in
/-- A deck-equivariant cube root on the complete original-history union either
preserves all three components or cycles equal-period components with conjugate
ordered holonomies. -/
theorem cube_root_criterion :
    (∃ R : OrbitUnion C p₀ p₁ p₂ → OrbitUnion C p₀ p₁ p₂,
      (∀ a x, R (unionDeck C p₀ p₁ p₂ a x) = unionDeck C p₀ p₁ p₂ a (R x)) ∧
      R^[3] = unionShift C p₀ p₁ p₂) ↔
    (((∃ s : Fin d₀, ∃ m : ℤ, ∃ b : H, Commute b (orbitHolonomy C p₀ d₀) ∧
        (3:ℤ)*(s.val:ℤ) = 1 + (d₀:ℤ)*m ∧ b^3*(orbitHolonomy C p₀ d₀)^m = 1) ∧
      (∃ s : Fin d₁, ∃ m : ℤ, ∃ b : H, Commute b (orbitHolonomy C p₁ d₁) ∧
        (3:ℤ)*(s.val:ℤ) = 1 + (d₁:ℤ)*m ∧ b^3*(orbitHolonomy C p₁ d₁)^m = 1) ∧
      (∃ s : Fin d₂, ∃ m : ℤ, ∃ b : H, Commute b (orbitHolonomy C p₂ d₂) ∧
        (3:ℤ)*(s.val:ℤ) = 1 + (d₂:ℤ)*m ∧ b^3*(orbitHolonomy C p₂ d₂)^m = 1)) ∨
      (d₀ = d₁ ∧ d₁ = d₂ ∧
        (∃ b : H, b*orbitHolonomy C p₁ d₁ = orbitHolonomy C p₀ d₀*b) ∧
        (∃ c : H, c*orbitHolonomy C p₂ d₂ = orbitHolonomy C p₁ d₁*c))) := by
  let A := actualAtlas C p₀ d₀ hd₀ hm₀
  let B := actualAtlas C p₁ d₁ hd₁ hm₁
  let D := actualAtlas C p₂ d₂ hd₂ hm₂
  let e := unionEquiv C p₀ p₁ p₂ hd₀ hd₁ hd₂ hm₀ hm₁ hm₂ hdis₀₁ hdis₀₂ hdis₁₂
  have et : ∀ x, e (jointTime A B D x) = unionShift C p₀ p₁ p₂ (e x) := by
    intro x
    rcases x with x | (x | x) <;> exact Subtype.ext rfl
  have ed : ∀ a x, e (jointDeck A B D a x) = unionDeck C p₀ p₁ p₂ a (e x) := by
    intro a x
    rcases x with x | (x | x) <;> exact Subtype.ext rfl
  have eit : ∀ x, e.symm (unionShift C p₀ p₁ p₂ x) = jointTime A B D (e.symm x) := by
    intro x
    apply e.injective
    rw [e.apply_symm_apply,et,e.apply_symm_apply]
  have eid : ∀ a x, e.symm (unionDeck C p₀ p₁ p₂ a x) = jointDeck A B D a (e.symm x) := by
    intro a x
    apply e.injective
    rw [e.apply_symm_apply,ed,e.apply_symm_apply]
  change _ ↔ ((Local A ∧ Local B ∧ Local D) ∨
    (A.period = B.period ∧ B.period = D.period ∧
      (∃ b : H, b * B.holonomy = A.holonomy * b) ∧
      (∃ c : H, c * D.holonomy = B.holonomy * c)))
  rw [← chart_criterion A B D]
  constructor
  · rintro ⟨R,hR,hS⟩
    refine ⟨fun x => e.symm (R (e x)), ?_, ?_⟩
    · intro a x
      change e.symm (R (e (jointDeck A B D a x))) = _
      rw [ed,hR,eid]
    · funext x
      change e.symm (R (e (e.symm (R (e (e.symm (R (e x)))))))) = _
      simp only [e.apply_symm_apply]
      have hs : R (R (R (e x))) = unionShift C p₀ p₁ p₂ (e x) := congrFun hS (e x)
      rw [hs,eit,e.symm_apply_apply]
  · rintro ⟨r,hr,hs⟩
    refine ⟨fun x => e (r (e.symm x)), ?_, ?_⟩
    · intro a x
      change e (r (e.symm (unionDeck C p₀ p₁ p₂ a x))) = _
      rw [eid,hr,ed]
    · funext x
      change e (r (e.symm (e (r (e.symm (e (r (e.symm x)))))))) = _
      simp only [e.symm_apply_apply]
      have ht : r (r (r (e.symm x))) = jointTime A B D (e.symm x) := congrFun hs (e.symm x)
      rw [ht,et,e.apply_symm_apply]

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ThreeOrbitCubeRootCriterion
