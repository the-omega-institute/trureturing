/- GID: D5/S3/FiniteGroups/KlandermanConjecture42Refutation
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/KlandermanConjecture42Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/KlandermanConjecture42Refutation.claim; result=D5/S3/FiniteGroups/KlandermanConjecture42Refutation.result; claim=D5/S3/FiniteGroups/KlandermanConjecture42Refutation.claim
   digest: Ordinary transfer generation does not give the compatibility asserted in Conjecture 4.2. -/

import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace D5.S3.FiniteGroups.KlandermanConjecture42Refutation

universe u

/-- Definition 2.1: relations on all actual subgroups, with all transfer axioms.
Antisymmetry follows from refinement of subgroup inclusion. -/
structure TransferSystem (G : Type u) [Group G] where
  rel : Subgroup G → Subgroup G → Prop
  refines : ∀ {K H}, rel K H → K ≤ H
  refl : ∀ H, rel H H
  trans : ∀ {K H L}, rel K H → rel H L → rel K L
  restrict : ∀ {K H L}, rel K H → L ≤ H → rel (K ⊓ L) L
  conjugate : ∀ (g : G) {K H}, rel K H →
    rel (K.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom)

variable {G : Type u} [Group G]

/-- Inclusion of the arrow relations. -/
def Extends (T U : TransferSystem G) : Prop := ∀ K H, T.rel K H → U.rel K H

/-- Definition 2.14, in the source order (lesser, greater). -/
def Compatible (T U : TransferSystem G) : Prop :=
  Extends T U ∧ ∀ A B C : Subgroup G, B ≤ A → C ≤ A →
    T.rel B A → U.rel (B ⊓ C) B → U.rel C A

/-- Definition 2.15. -/
def Saturated (T : TransferSystem G) : Prop :=
  ∀ L K H : Subgroup G, L ≤ K → K ≤ H → T.rel L H → T.rel K H

/-- The least saturated extension, expressed as an intersection of relations. -/
def hull (T : TransferSystem G) (K H : Subgroup G) : Prop :=
  ∀ U : TransferSystem G, Saturated U → Extends T U → U.rel K H

/-- Definitions 2.16--2.17, with equality of systems expressed extensionally. -/
def LesserSimplyPaired (T : TransferSystem G) : Prop :=
  ∀ U : TransferSystem G, Compatible T U →
    (∀ K H, U.rel K H ↔ hull T K H) ∨ (∀ K H, U.rel K H ↔ K ≤ H)

/-- The undirected arrow graph; deleting identity loops preserves components. -/
def arrowGraph (T : TransferSystem G) : SimpleGraph (Subgroup G) where
  Adj K H := K ≠ H ∧ (T.rel K H ∨ T.rel H K)
  symm := by
    intro K H h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by intro K h; exact h.1 rfl

/-- Exactly the two actual graph components represented by e and G. -/
def TwoComponents (T : TransferSystem G) : Prop :=
  (arrowGraph T).connectedComponentMk ⊥ ≠ (arrowGraph T).connectedComponentMk ⊤ ∧
  ∀ c : (arrowGraph T).ConnectedComponent,
    c = (arrowGraph T).connectedComponentMk ⊥ ∨
    c = (arrowGraph T).connectedComponentMk ⊤

/-- No nonidentity arrow meets G. Together with reflexivity this says that its
component has only G → G. -/
def TopIsolated (T : TransferSystem G) : Prop :=
  ∀ H, T.rel H ⊤ ∨ T.rel ⊤ H → H = ⊤

private def completeSystem (G : Type u) [Group G] : TransferSystem G where
  rel := (· ≤ ·)
  refines h := h
  refl _ := le_rfl
  trans := le_trans
  restrict _ _ := inf_le_right
  conjugate _ h := Subgroup.map_mono h

/-- Intersection of all ordinary transfer systems containing T and e → G.
There is no saturation or compatibility step in this construction. -/
def generated (T : TransferSystem G) : TransferSystem G where
  rel K H := ∀ U : TransferSystem G, Extends T U → U.rel ⊥ ⊤ → U.rel K H
  refines h := h (completeSystem G) (fun _ _ h => T.refines h) bot_le
  refl H U _ _ := U.refl H
  trans h₁ h₂ U hT he := U.trans (h₁ U hT he) (h₂ U hT he)
  restrict h hL U hT he := U.restrict (h U hT he) hL
  conjugate g h U hT he := U.conjugate g (h U hT he)

/-- The unchanged full universal conjunction of Conjecture 4.2. -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : TransferSystem G),
    TwoComponents T → TopIsolated T →
      ¬ LesserSimplyPaired T ∧ Compatible T (generated T)

/-- Identities and arrows from e to every proper subgroup. -/
def properStar (G : Type u) [Group G] : TransferSystem G where
  rel K H := K = H ∨ (K = ⊥ ∧ H ≠ ⊤)
  refines := by
    rintro K H (rfl | ⟨rfl, _⟩)
    · exact le_rfl
    · exact bot_le
  refl H := Or.inl rfl
  trans := by
    rintro K H L (rfl | ⟨rfl, hH⟩) h
    · exact h
    · rcases h with rfl | ⟨_, hL⟩
      · exact Or.inr ⟨rfl, hH⟩
      · exact Or.inr ⟨rfl, hL⟩
  restrict := by
    rintro K H L (rfl | ⟨rfl, hH⟩) hL
    · exact Or.inl (inf_eq_right.mpr hL)
    · exact Or.inr ⟨bot_inf_eq, fun he => hH (top_unique (he ▸ hL))⟩
  conjugate := by
    rintro g K H (rfl | ⟨rfl, hH⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨Subgroup.map_bot _, ?_⟩
      intro hm
      apply hH
      apply top_unique
      intro x _
      apply (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).mp
      rw [hm]
      exact Subgroup.mem_top _

/-- Identities and all arrows from e. -/
def fullStar (G : Type u) [Group G] : TransferSystem G where
  rel K H := K = H ∨ K = ⊥
  refines := by
    rintro K H (rfl | rfl)
    · exact le_rfl
    · exact bot_le
  refl H := Or.inl rfl
  trans := by
    rintro K H L (rfl | rfl) h
    · exact h
    · exact Or.inr rfl
  restrict := by
    rintro K H L (rfl | rfl) hL
    · exact Or.inl (inf_eq_right.mpr hL)
    · exact Or.inr bot_inf_eq
  conjugate := by
    rintro g K H (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Subgroup.map_bot _)

private theorem proper_star_top_isolated : TopIsolated (properStar G) := by
  intro H h
  rcases h with (h | ⟨_, h⟩) | (h | ⟨h, _⟩)
  · exact h
  · exact (h rfl).elim
  · exact h.symm
  · exact (h.symm ▸ (bot_le : (⊥ : Subgroup G) ≤ H)).antisymm le_top

private theorem proper_star_components (hbt : (⊥ : Subgroup G) ≠ ⊤) :
    TwoComponents (properStar G) := by
  constructor
  · intro hc
    have hr := SimpleGraph.ConnectedComponent.exact hc
    have hn : (arrowGraph (properStar G)).neighborSet ⊤ = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro H h
      exact h.1 (proper_star_top_isolated H h.2.symm).symm
    exact SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hbt hn hr
  · intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h H =>
      by_cases ht : H = ⊤
      · exact Or.inr (ht ▸ rfl)
      · left
        apply SimpleGraph.ConnectedComponent.sound
        by_cases hb : H = ⊥
        · exact hb ▸ SimpleGraph.Reachable.rfl
        · exact (SimpleGraph.Adj.reachable
            (show (arrowGraph (properStar G)).Adj ⊥ H from
              ⟨hb.symm, Or.inl (Or.inr ⟨rfl, ht⟩)⟩)).symm

private theorem generated_star (K H : Subgroup G) :
    (generated (properStar G)).rel K H ↔ (fullStar G).rel K H := by
  constructor
  · intro h
    exact h (fullStar G) (fun _ _ h => h.elim Or.inl (fun h => Or.inr h.1)) (Or.inr rfl)
  · rintro (rfl | rfl) U _ he
    · exact U.refl _
    · simpa only [bot_inf_eq] using U.restrict he (show H ≤ ⊤ from le_top)

private abbrev Q8 := QuaternionGroup 2
private abbrev Z : Subgroup Q8 := Subgroup.zpowers (QuaternionGroup.a 2)
private abbrev A : Subgroup Q8 := Subgroup.zpowers (QuaternionGroup.a 1)

private theorem q8_chain : (⊥ : Subgroup Q8) < Z ∧ Z < A ∧ A < ⊤ := by
  have hz : (QuaternionGroup.a 2 : Q8) ∈ Z := Subgroup.mem_zpowers _
  have ha : (QuaternionGroup.a 1 : Q8) ∈ A := Subgroup.mem_zpowers _
  have hzA : Z ≤ A := by
    apply Subgroup.zpowers_le.mpr
    have h := A.pow_mem ha 2
    simpa only [QuaternionGroup.a_one_pow, Nat.cast_ofNat] using h
  have hane : (QuaternionGroup.a 1 : Q8) ∉ Z := by
    rw [mem_zpowers_iff_mem_range_orderOf]
    norm_num [QuaternionGroup.orderOf_a, QuaternionGroup.a_mul_a, pow_two,
      QuaternionGroup.one_def]
  have hx : (QuaternionGroup.xa 0 : Q8) ∉ A := by
    rw [mem_zpowers_iff_mem_range_orderOf]
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨k, _, hk⟩
    rw [QuaternionGroup.a_one_pow] at hk
    cases hk
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_le_of_ne bot_le (by
      intro h
      have : (QuaternionGroup.a 2 : Q8) = 1 := Subgroup.mem_bot.mp (h ▸ hz)
      exact (by decide : (QuaternionGroup.a 2 : Q8) ≠ 1) this)
  · exact lt_of_le_of_ne hzA (by intro h; exact hane (h ▸ ha))
  · exact lt_of_le_of_ne le_top (by intro h; exact hx (h.symm ▸ Subgroup.mem_top _))

/-- The whole conjecture fails through its compatibility conjunct on actual Q8. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨hz, hza, hat⟩ := q8_chain
  have hbt : (⊥ : Subgroup Q8) ≠ ⊤ := ne_of_lt (hz.trans (hza.trans hat))
  have hp := (hc Q8 (properStar Q8) (proper_star_components hbt)
    proper_star_top_isolated).2
  have heA : (properStar Q8).rel ⊥ A := Or.inr ⟨rfl, ne_of_lt hat⟩
  have hee : (generated (properStar Q8)).rel ((⊥ : Subgroup Q8) ⊓ Z) ⊥ := by
    rw [bot_inf_eq]
    exact (generated (properStar Q8)).refl _
  have hZA := hp.2 A ⊥ Z bot_le hza.le heA hee
  rcases (generated_star Z A).mp hZA with heq | heq
  · exact (ne_of_lt hza) heq
  · exact (ne_of_gt hz) heq

end D5.S3.FiniteGroups.KlandermanConjecture42Refutation
