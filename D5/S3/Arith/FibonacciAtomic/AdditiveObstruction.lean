/- GID: D5/S3/Arith/FibonacciAtomic/AdditiveObstruction
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/AdditiveObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   utility: none
   anchors: []
   digest: A finite additive joint-readout has an exact descent obstruction and image-size record cost. -/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.AdditiveObstruction

section Definitions

variable {X Y A B Z : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup Z] [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype Z]

/-- The left and right linear readouts restricted to a source subgroup. -/
def leftReadout (D : AddSubgroup (X × Y)) (α : X →+ A) : D →+ A :=
  α.comp ((AddMonoidHom.fst X Y).comp D.subtype)

def rightReadout (D : AddSubgroup (X × Y)) (β : Y →+ B) : D →+ B :=
  β.comp ((AddMonoidHom.snd X Y).comp D.subtype)

def leftCoordinate (D : AddSubgroup (X × Y)) : D →+ X :=
  (AddMonoidHom.fst X Y).comp D.subtype

def rightCoordinate (D : AddSubgroup (X × Y)) : D →+ Y :=
  (AddMonoidHom.snd X Y).comp D.subtype

def jointReadout (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) : D →+ (A × B) :=
  (leftReadout D α).prod (rightReadout D β)

def jointKernel (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) : AddSubgroup D :=
  (jointReadout D α β).ker

def leftKernel (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) : AddSubgroup D :=
  jointKernel D α β ⊓ (rightCoordinate D).ker

def rightKernel (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) : AddSubgroup D :=
  jointKernel D α β ⊓ (leftCoordinate D).ker

def leftObstructionKernel (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) :
    AddSubgroup (jointKernel D α β) :=
  (leftKernel D α β).addSubgroupOf (jointKernel D α β)

def rightObstructionKernel (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) :
    AddSubgroup (jointKernel D α β) :=
  (rightKernel D α β).addSubgroupOf (jointKernel D α β)

abbrev obstruction (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) :=
  jointKernel D α β ⧸
    (leftObstructionKernel D α β ⊔ rightObstructionKernel D α β)

def vanishesOn {T W : Type*} [AddCommGroup T] [AddCommGroup W]
    (F : T →+ W) (H : AddSubgroup T) : Prop :=
  ∀ h : H, F h = 0

def leftSufficient (D : AddSubgroup (X × Y)) (α : X →+ A)
    (F : D →+ Z) : Prop :=
  ∀ u v : D, u.1.2 = v.1.2 → α u.1.1 = α v.1.1 → F u = F v

def rightSufficient (D : AddSubgroup (X × Y)) (β : Y →+ B)
    (F : D →+ Z) : Prop :=
  ∀ u v : D, u.1.1 = v.1.1 → β u.1.2 = β v.1.2 → F u = F v

def jointlySufficient (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B)
    (F : D →+ Z) : Prop :=
  ∀ u v : D, (jointReadout D α β) u = (jointReadout D α β) v → F u = F v

def restrictedTask (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B)
    (F : D →+ Z) : jointKernel D α β →+ Z :=
  F.comp (jointKernel D α β).subtype

end Definitions

section Main

variable {X Y A B Z : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup Z] [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype Z]
  (D : AddSubgroup (X × Y)) (α : X →+ A) (β : Y →+ B) (F : D →+ Z)

private lemma left_sufficient_iff_vanishes :
    leftSufficient D α F ↔ vanishesOn F (leftKernel D α β) := by
  constructor
  · intro h u
    have huE : (u : D) ∈ jointKernel D α β := u.2.1
    have huY : (rightCoordinate D) (u : D) = 0 := u.2.2
    have huα : α (u : D).1.1 = 0 := by
      have h0 := AddMonoidHom.mem_ker.mp huE
      exact congrArg Prod.fst h0
    have hzero := h (u : D) 0 (by simpa [rightCoordinate] using huY)
      (by simpa using huα)
    simpa using hzero
  · intro h u v huv hα
    let w : D := u - v
    have hwY : (rightCoordinate D) w = 0 := by
      change (u.1.2 - v.1.2) = 0
      exact sub_eq_zero.mpr huv
    have hwα : α w.1.1 = 0 := by
      dsimp [w]
      rw [map_sub]
      simpa using sub_eq_zero.mpr hα
    have hwE : w ∈ jointKernel D α β := by
      apply AddMonoidHom.mem_ker.mpr
      apply Prod.ext
      · simpa [jointReadout, leftReadout] using hwα
      · simpa [jointReadout, rightReadout, rightCoordinate] using congrArg β hwY
    have hw : w ∈ leftKernel D α β := ⟨hwE, hwY⟩
    have hFw : F w = 0 := h ⟨w, hw⟩
    dsimp [w] at hFw
    exact sub_eq_zero.mp (by simpa [map_sub] using hFw)

private lemma right_sufficient_iff_vanishes :
    rightSufficient D β F ↔ vanishesOn F (rightKernel D α β) := by
  constructor
  · intro h u
    have huE : (u : D) ∈ jointKernel D α β := u.2.1
    have huX : (leftCoordinate D) (u : D) = 0 := u.2.2
    have huβ : β (u : D).1.2 = 0 := by
      have h0 := AddMonoidHom.mem_ker.mp huE
      exact congrArg Prod.snd h0
    have hzero := h (u : D) 0 (by simpa [leftCoordinate] using huX)
      (by simpa using huβ)
    simpa using hzero
  · intro h u v huv hβ
    let w : D := u - v
    have hwX : (leftCoordinate D) w = 0 := by
      change (u.1.1 - v.1.1) = 0
      exact sub_eq_zero.mpr huv
    have hwβ : β w.1.2 = 0 := by
      dsimp [w]
      rw [map_sub]
      simpa using sub_eq_zero.mpr hβ
    have hwE : w ∈ jointKernel D α β := by
      apply AddMonoidHom.mem_ker.mpr
      apply Prod.ext
      · simpa [jointReadout, leftReadout, leftCoordinate] using congrArg α hwX
      · simpa [jointReadout, rightReadout] using hwβ
    have hw : w ∈ rightKernel D α β := ⟨hwE, hwX⟩
    have hFw : F w = 0 := h ⟨w, hw⟩
    dsimp [w] at hFw
    exact sub_eq_zero.mp (by simpa [map_sub] using hFw)

private lemma joint_sufficient_iff_vanishes :
    jointlySufficient D α β F ↔ vanishesOn F (jointKernel D α β) := by
  constructor
  · intro h u
    have huE : (u : D) ∈ jointKernel D α β := u.2
    have huv : (jointReadout D α β) u = (jointReadout D α β) 0 := by
      simpa using AddMonoidHom.mem_ker.mp huE
    simpa using h u 0 huv
  · intro h u v huv
    let w : D := u - v
    have hwE : w ∈ jointKernel D α β := by
      simp only [jointKernel, AddMonoidHom.mem_ker]
      rw [map_sub, huv, sub_self]
    have hFw : F w = 0 := h ⟨w, hwE⟩
    dsimp [w] at hFw
    exact sub_eq_zero.mp (by simpa [map_sub] using hFw)

private lemma quotient_kernel_le
    (hleft : vanishesOn F (leftKernel D α β))
    (hright : vanishesOn F (rightKernel D α β)) :
    leftObstructionKernel D α β ⊔ rightObstructionKernel D α β ≤
      (restrictedTask D α β F).ker := by
  have hH :
      leftObstructionKernel D α β ⊔ rightObstructionKernel D α β ≤
        (restrictedTask D α β F).ker := by
    apply sup_le
    · intro u hu
      simpa [restrictedTask] using hleft ⟨u.1, hu⟩
    · intro u hu
      simpa [restrictedTask] using hright ⟨u.1, hu⟩
  intro u hu
  exact hH hu

/-- The task restricted to the joint kernel descends through the additive obstruction. -/
noncomputable def descendedTask
    (hleft : vanishesOn F (leftKernel D α β))
    (hright : vanishesOn F (rightKernel D α β)) :
    obstruction D α β →+ Z :=
  QuotientAddGroup.lift _ (restrictedTask D α β F)
    (quotient_kernel_le D α β F hleft hright)

/-- The cardinality of the image of the descended task is the optimal record alphabet size. -/
noncomputable def recordCapacity
    (hleft : vanishesOn F (leftKernel D α β))
    (hright : vanishesOn F (rightKernel D α β)) : ℕ :=
  Nat.card (AddMonoidHom.range (descendedTask D α β F hleft hright))

theorem additive_obstruction_complete
    (hleft : vanishesOn F (leftKernel D α β))
    (hright : vanishesOn F (rightKernel D α β)) :
    (leftSufficient D α F ↔ vanishesOn F (leftKernel D α β)) ∧
      (rightSufficient D β F ↔ vanishesOn F (rightKernel D α β)) ∧
      (jointlySufficient D α β F ↔
        descendedTask D α β F hleft hright = 0) ∧
      recordCapacity D α β F hleft hright =
        Nat.card (AddMonoidHom.range (restrictedTask D α β F)) := by
  have hrestrict_zero :
      vanishesOn F (jointKernel D α β) ↔ restrictedTask D α β F = 0 := by
    constructor
    · intro h
      apply AddMonoidHom.ext
      intro u
      exact h u
    · intro h u
      have := DFunLike.congr_fun h u
      simpa [restrictedTask] using this
  have hdesc_zero :
      descendedTask D α β F hleft hright = 0 ↔
        restrictedTask D α β F = 0 := by
    constructor
    · intro h
      dsimp [descendedTask] at h
      have hc := congrArg
        (fun g : obstruction D α β →+ Z =>
          g.comp (QuotientAddGroup.mk'
            (leftObstructionKernel D α β ⊔ rightObstructionKernel D α β))) h
      have hcomp : restrictedTask D α β F = 0 := by
        simpa [QuotientAddGroup.lift_comp_mk', restrictedTask] using hc
      exact hcomp
    · intro h
      apply AddMonoidHom.ext
      intro q
      refine QuotientAddGroup.induction_on q ?_
      intro u
      dsimp [descendedTask]
      simpa only [QuotientAddGroup.lift_quot_mk, AddMonoidHom.zero_apply,
        restrictedTask] using DFunLike.congr_fun h u
  have hrange :
      (AddMonoidHom.range (descendedTask D α β F hleft hright)) =
        AddMonoidHom.range (restrictedTask D α β F) := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      refine QuotientAddGroup.induction_on q ?_
      intro u
      exact ⟨u, by simpa [descendedTask]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨QuotientAddGroup.mk' _ u, by simpa [descendedTask]⟩
  refine ⟨left_sufficient_iff_vanishes D α β F,
    right_sufficient_iff_vanishes D α β F, ?_, ?_⟩
  · rw [joint_sufficient_iff_vanishes D α β F, hrestrict_zero, hdesc_zero]
  · exact congrArg (fun H : AddSubgroup Z => Nat.card H) hrange

theorem obstruction_zero_iff_all_tasks_jointly_descend :
    Subsingleton (obstruction D α β) ↔
      ∀ (G : jointKernel D α β →+ obstruction D α β),
        vanishesOn G (leftObstructionKernel D α β) →
        vanishesOn G (rightObstructionKernel D α β) →
        G = 0 := by
  let E := jointKernel D α β
  let H : AddSubgroup E :=
    leftObstructionKernel D α β ⊔ rightObstructionKernel D α β
  change Subsingleton (E ⧸ H) ↔ _
  constructor
  · intro h G hleft hright
    apply AddMonoidHom.ext
    intro e
    have htop : H = ⊤ := (QuotientAddGroup.subsingleton_iff.mp h)
    have heH : e ∈ H := by simpa [htop]
    have hker :
        leftObstructionKernel D α β ⊔ rightObstructionKernel D α β ≤ G.ker := by
      apply sup_le
      · intro u hu
        exact hleft ⟨u, hu⟩
      · intro u hu
        exact hright ⟨u, hu⟩
    exact hker heH
  · intro hall
    let q : E →+ obstruction D α β := QuotientAddGroup.mk' H
    have hleft : vanishesOn q (leftObstructionKernel D α β) := by
      intro u
      change q u = 0
      rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
      exact (show leftObstructionKernel D α β ≤ H from le_sup_left) u.2
    have hright : vanishesOn q (rightObstructionKernel D α β) := by
      intro u
      change q u = 0
      rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
      exact (show rightObstructionKernel D α β ≤ H from le_sup_right) u.2
    have hq : q = 0 := hall q hleft hright
    refine ⟨?_⟩
    intro a b
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective H b
    have hx := congrArg (fun f => f x) hq
    have hy := congrArg (fun f => f y) hq
    calc
      q x = 0 := by simpa using hx
      _ = q y := by simpa using hy.symm

theorem obstruction_nontrivial_has_feasible_failed_task
    (h : ¬ Subsingleton (obstruction D α β)) :
    ∃ G : jointKernel D α β →+ obstruction D α β,
      vanishesOn G (leftObstructionKernel D α β) ∧
        vanishesOn G (rightObstructionKernel D α β) ∧
          ¬ vanishesOn G (⊤ : AddSubgroup (jointKernel D α β)) := by
  let E := jointKernel D α β
  let H : AddSubgroup E :=
    leftObstructionKernel D α β ⊔ rightObstructionKernel D α β
  let q : E →+ obstruction D α β := QuotientAddGroup.mk' H
  have hleft : vanishesOn q (leftObstructionKernel D α β) := by
    intro u
    change q u = 0
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    exact (show leftObstructionKernel D α β ≤ H from le_sup_left) u.2
  have hright : vanishesOn q (rightObstructionKernel D α β) := by
    intro u
    change q u = 0
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    exact (show rightObstructionKernel D α β ≤ H from le_sup_right) u.2
  have hq : q ≠ 0 := by
    intro hq
    apply h
    have htop : H = ⊤ := by
      have hk : q.ker = ⊤ := by simpa [hq]
      simpa [q, QuotientAddGroup.ker_mk'] using hk
    apply QuotientAddGroup.subsingleton_iff.mpr
    exact htop
  have hjoint : ¬ vanishesOn q (⊤ : AddSubgroup E) := by
    intro hz
    apply hq
    apply AddMonoidHom.ext
    intro e
    exact hz ⟨e, trivial⟩
  exact ⟨q, hleft, hright, hjoint⟩

end Main

end D5.S3.Arith.FibonacciAtomic.AdditiveObstruction
