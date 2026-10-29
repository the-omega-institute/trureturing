/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalReturnAtlasCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalReturnAtlasCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: A complete return chart admits coherent rational time precisely at period one with a rational holonomy homomorphism. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimitiveLiftRootCriterion
import Mathlib.Algebra.Group.End
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RationalReturnAtlasCriterion

open PrimitiveLiftRootCriterion
universe u v

variable {H : Type u} [Group H] {X : Type v} (A : ReturnAtlas H X)

private theorem period_one_of_action
    (ρ : Multiplicative ℚ →* Equiv.Perm X)
    (heq : ∀ q, A.Equivariant (ρ q))
    (htime : (ρ (Multiplicative.ofAdd (1 : ℚ)) : X → X) = A.time) :
    A.period = 1 := by
  have hd : (A.period : ℚ) ≠ 0 := by exact_mod_cast A.positive.ne'
  let q := Multiplicative.ofAdd (1 / (A.period : ℚ))
  have hq : q ^ A.period = Multiplicative.ofAdd (1 : ℚ) := by
    apply Multiplicative.toAdd.injective
    simp [q, Multiplicative.toAdd_pow, nsmul_eq_mul, hd]
  have hp : ρ q ^ A.period = ρ (Multiplicative.ofAdd (1 : ℚ)) := by
    rw [← map_pow, hq]
  have hroot : (ρ q : X → X)^[A.period] = A.time := by
    rw [← Equiv.Perm.coe_pow, hp]
    exact htime
  obtain ⟨s,m,b,hb,hs,hpow⟩ :=
    (A.root_criterion A.period).1 ⟨ρ q,heq q,hroot⟩
  have hz : (A.period : ℤ) ∣ (1 : ℤ) :=
    ⟨(s.val : ℤ) - m, by nlinarith [hs]⟩
  have hn : A.period ∣ 1 := by exact_mod_cast hz
  exact Nat.eq_one_of_dvd_one hn

private def zeroChart (hd : A.period = 1) : H ≃ X :=
  Equiv.ofBijective (A.point 0) (by
    constructor
    · intro z w h
      let o : Fin A.period := ⟨0,A.positive⟩
      have hh : A.coordinates (o,z) = A.coordinates (o,w) := h
      exact congrArg Prod.snd (A.coordinates.injective hh)
    · intro x
      obtain ⟨⟨j,z⟩,rfl⟩ := A.coordinates.surjective x
      have hj : j.val = 0 := by have := j.isLt; omega
      refine ⟨z,?_⟩
      change A.point 0 z = A.point (j.val : ℤ) z
      simp [hj])

private theorem zeroChart_deck (hd : A.period = 1) (a z : H) :
    zeroChart A hd (a*z) = A.deck a (zeroChart A hd z) :=
  (A.deck_point a 0 z).symm

private theorem zeroChart_time (hd : A.period = 1) (z : H) :
    zeroChart A hd (z*A.holonomy) = A.time (zeroChart A hd z) := by
  change A.point 0 (z*A.holonomy) = A.time (A.point 0 z)
  rw [A.time_point]
  symm
  apply (A.relation _ _ _ _).2
  exact ⟨1,by simp [hd],by simp⟩

private theorem holonomy_hom_of_action (hd : A.period = 1)
    (ρ : Multiplicative ℚ →* Equiv.Perm X)
    (heq : ∀ q, A.Equivariant (ρ q))
    (htime : (ρ (Multiplicative.ofAdd (1 : ℚ)) : X → X) = A.time) :
    ∃ φ : Multiplicative ℚ →* H, φ (Multiplicative.ofAdd (1 : ℚ)) = A.holonomy := by
  let e := zeroChart A hd
  let b (q : Multiplicative ℚ) := e.symm (ρ q (e 1))
  have eb (q : Multiplicative ℚ) : e (b q) = ρ q (e 1) := e.apply_symm_apply _
  have law (q : Multiplicative ℚ) (z : H) : ρ q (e z) = e (z * b q) := by
    calc
      ρ q (e z) = ρ q (A.deck z (e 1)) := by
        rw [← zeroChart_deck A hd]
        simp only [mul_one]
      _ = A.deck z (ρ q (e 1)) := heq q z (e 1)
      _ = A.deck z (e (b q)) := by rw [eb]
      _ = e (z*b q) := (zeroChart_deck A hd z (b q)).symm
  let φ : Multiplicative ℚ →* H := {
    toFun := b
    map_one' := by
      apply e.injective
      rw [eb,map_one]
      rfl
    map_mul' p q := by
      apply e.injective
      rw [eb,mul_comm p q,map_mul]
      change ρ q (ρ p (e 1)) = e (b p * b q)
      rw [← eb,law] }
  refine ⟨φ,?_⟩
  apply e.injective
  change e (b (Multiplicative.ofAdd (1 : ℚ))) = e A.holonomy
  rw [eb,congrFun htime]
  simpa only [one_mul] using (zeroChart_time A hd 1).symm

private theorem action_of_holonomy_hom (hd : A.period = 1)
    (φ : Multiplicative ℚ →* H)
    (hφ : φ (Multiplicative.ofAdd (1 : ℚ)) = A.holonomy) :
    ∃ ρ : Multiplicative ℚ →* Equiv.Perm X,
      (∀ q, A.Equivariant (ρ q)) ∧
      (ρ (Multiplicative.ofAdd (1 : ℚ)) : X → X) = A.time := by
  let e := zeroChart A hd
  let ψ : Multiplicative ℚ →* Equiv.Perm H := {
    toFun q := Equiv.mulRight (φ q)
    map_one' := by simp
    map_mul' p q := by
      ext z
      change z * φ (p*q) = (z*φ q)*φ p
      rw [mul_comm p q,map_mul,mul_assoc] }
  let ρ := e.permCongrHom.toMonoidHom.comp ψ
  have law (q : Multiplicative ℚ) (z : H) : ρ q (e z) = e (z*φ q) := by
    change e (e.symm (e z) * φ q) = _
    rw [e.symm_apply_apply]
  refine ⟨ρ,?_,?_⟩
  · intro q a x
    obtain ⟨z,rfl⟩ := e.surjective x
    rw [← zeroChart_deck A hd,law,law,← zeroChart_deck A hd,mul_assoc]
  · funext x
    obtain ⟨z,rfl⟩ := e.surjective x
    rw [law,hφ]
    exact zeroChart_time A hd z

/-- A single complete signed return chart admits a genuine deck-equivariant rational
time action exactly when its period is one and its holonomy extends coherently to ℚ. -/
theorem rational_time_action_criterion :
    (∃ ρ : Multiplicative ℚ →* Equiv.Perm X,
      (∀ q, A.Equivariant (ρ q)) ∧
      (ρ (Multiplicative.ofAdd (1 : ℚ)) : X → X) = A.time) ↔
    A.period = 1 ∧
      ∃ φ : Multiplicative ℚ →* H, φ (Multiplicative.ofAdd (1 : ℚ)) = A.holonomy := by
  constructor
  · rintro ⟨ρ,heq,htime⟩
    have hd := period_one_of_action A ρ heq htime
    exact ⟨hd,holonomy_hom_of_action A hd ρ heq htime⟩
  · rintro ⟨hd,φ,hφ⟩
    exact action_of_holonomy_hom A hd φ hφ

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RationalReturnAtlasCriterion
