/- GID: D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Link-irregular tournaments exist at every nonvacuous order exactly from six onward. -/

import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.RelIso.Set
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence

/-- A tournament is loopless and has exactly one directed edge between each
pair of distinct vertices. -/
def IsTournament {V : Type*} (R : V → V → Prop) : Prop :=
  (∀ v, ¬ R v v) ∧ ∀ u v, u ≠ v → Xor (R u v) (R v u)

/-- The directed link at `v` is the relation induced on the union of its out-
and in-neighbors. -/
def DirectedLink {V : Type*} (R : V → V → Prop) (v : V) :=
  Subrel R (fun w ↦ R v w ∨ R w v)

/-- Distinct vertices have no directed-link isomorphism. -/
def LinkIrregular {V : Type*} (R : V → V → Prop) : Prop :=
  ∀ u v, u ≠ v → IsEmpty (DirectedLink R u ≃r DirectedLink R v)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
/-- On the nonvacuous domain `n ≥ 2`, a link-irregular tournament exists
exactly when `n ≥ 6`. At orders zero and one the pairwise condition is
vacuous, which is why they are excluded from the equivalence. -/
theorem result :
    ∀ n : Nat, 2 ≤ n →
      ((∃ R : Fin n → Fin n → Prop, IsTournament R ∧ LinkIrregular R) ↔ 6 ≤ n) := by

  letI tournamentDecidable {V : Type} [Fintype V] [DecidableEq V]
      (R : V → V → Prop) [DecidableRel R] : Decidable (IsTournament R) := by
    unfold IsTournament
    infer_instance

  have orientation_iff_not_reverse {V : Type} {R : V → V → Prop}
      (hR : IsTournament R) {u v : V} (huv : u ≠ v) : R u v ↔ ¬ R v u :=
    (xor_iff_iff_not.mp (hR.2 u v huv))

  have not_orientation_iff_reverse {V : Type} {R : V → V → Prop}
      (hR : IsTournament R) {u v : V} (huv : u ≠ v) : ¬ R u v ↔ R v u :=
    (xor_iff_not_iff'.mp (hR.2 u v huv))

  have neighbor_iff_ne {V : Type} {R : V → V → Prop}
      (hR : IsTournament R) {u v : V} : R u v ∨ R v u ↔ v ≠ u := by
    constructor
    · intro h huv
      subst v
      exact h.elim (hR.1 u) (hR.1 u)
    · intro h
      exact ((xor_iff_or_and_not_and _ _).mp (hR.2 u v h.symm)).1

  let deleteRel {n : Nat} (R : Fin (n + 1) → Fin (n + 1) → Prop)
      (v : Fin (n + 1)) : Fin n → Fin n → Prop :=
    fun x y ↦ R (v.succAbove x) (v.succAbove y)

  letI deleteRelDecidable {n : Nat}
      (R : Fin (n + 1) → Fin (n + 1) → Prop) [DecidableRel R]
      (v : Fin (n + 1)) : DecidableRel (deleteRel R v) :=
    fun _ _ ↦ by unfold deleteRel; infer_instance

  let linkDeleteEquiv {n : Nat} {R : Fin (n + 1) → Fin (n + 1) → Prop}
      (hR : IsTournament R) (v : Fin (n + 1)) :
      {w // R v w ∨ R w v} ≃ Fin n := {
    toFun x := (finSuccAboveEquiv v).symm
      ⟨x.1, (neighbor_iff_ne hR).mp x.2⟩
    invFun x := ⟨v.succAbove x, (neighbor_iff_ne hR).mpr (v.succAbove_ne x)⟩
    left_inv x := by
      apply Subtype.ext
      change v.succAbove ((finSuccAboveEquiv v).symm
        ⟨x.1, (neighbor_iff_ne hR).mp x.2⟩) = x.1
      exact congrArg Subtype.val
        ((finSuccAboveEquiv v).apply_symm_apply
          ⟨x.1, (neighbor_iff_ne hR).mp x.2⟩)
    right_inv x := by
      have hcomp :
          (⟨v.succAbove x,
            (neighbor_iff_ne hR).mp
              ((neighbor_iff_ne hR).mpr (v.succAbove_ne x))⟩ :
            {w : Fin (n + 1) // w ≠ v}) =
          finSuccAboveEquiv v x := by
        apply Subtype.ext
        rfl
      change (finSuccAboveEquiv v).symm
        ⟨v.succAbove x,
          (neighbor_iff_ne hR).mp
            ((neighbor_iff_ne hR).mpr (v.succAbove_ne x))⟩ = x
      rw [hcomp]
      exact (finSuccAboveEquiv v).symm_apply_apply x
  }

  let linkDeleteIso {n : Nat} {R : Fin (n + 1) → Fin (n + 1) → Prop}
      (hR : IsTournament R) (v : Fin (n + 1)) : DirectedLink R v ≃r deleteRel R v := {
    toEquiv := linkDeleteEquiv hR v
    map_rel_iff' := by
      intro x y
      change R (v.succAbove _) (v.succAbove _) ↔ R x.1 y.1
      have hx : v.succAbove ((finSuccAboveEquiv v).symm
          ⟨x.1, (neighbor_iff_ne hR).mp x.2⟩) = x.1 := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv v).apply_symm_apply
            ⟨x.1, (neighbor_iff_ne hR).mp x.2⟩)
      have hy : v.succAbove ((finSuccAboveEquiv v).symm
          ⟨y.1, (neighbor_iff_ne hR).mp y.2⟩) = y.1 := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv v).apply_symm_apply
            ⟨y.1, (neighbor_iff_ne hR).mp y.2⟩)
      simpa [linkDeleteEquiv] using congrArg₂ R hx hy
  }

  let relIsoOfIff {V : Type} (R S : V → V → Prop)
      (h : ∀ x y, R x y ↔ S x y) : R ≃r S := {
    toEquiv := Equiv.refl V
    map_rel_iff' := fun {_ _} ↦ (h _ _).symm
  }

  let relIsoOfPerm {n : Nat} {R S : Fin n → Fin n → Prop}
      (e : Equiv.Perm (Fin n)) (h : ∀ x y, S (e x) (e y) ↔ R x y) : R ≃r S := {
    toEquiv := e
    map_rel_iff' := fun {_ _} ↦ h _ _
  }

  let rel2 (c : Fin 1 → Bool) (x y : Fin 2) : Prop :=
    if x = 0 ∧ y = 1 then c 0 = true
    else if x = 1 ∧ y = 0 then c 0 = false
    else False

  let encode2 (R : Fin 2 → Fin 2 → Prop) [DecidableRel R] : Fin 1 → Bool :=
    ![decide (R 0 1)]

  have rel2_encode {R : Fin 2 → Fin 2 → Prop} [DecidableRel R]
      (hR : IsTournament R) : ∀ x y, rel2 (encode2 R) x y ↔ R x y := by
    intro x y
    fin_cases x <;> fin_cases y
    · simp [rel2, hR.1]
    · simp [rel2, encode2]
    · simpa [rel2, encode2] using
        (not_orientation_iff_reverse hR (by decide : (0 : Fin 2) ≠ 1))
    · simp [rel2, hR.1]

  letI rel2Decidable (c : Fin 1 → Bool) : DecidableRel (rel2 c) :=
    fun _ _ ↦ by unfold rel2; infer_instance

  have rel2_iso (c d : Fin 1 → Bool) :
      ∃ e : Equiv.Perm (Fin 2), ∀ x y, rel2 d (e x) (e y) ↔ rel2 c x y := by
    revert c d
    decide

  let rel3 (c : Fin 3 → Bool) (x y : Fin 3) : Prop :=
    if x = 0 ∧ y = 1 then c 0 = true
    else if x = 1 ∧ y = 0 then c 0 = false
    else if x = 0 ∧ y = 2 then c 1 = true
    else if x = 2 ∧ y = 0 then c 1 = false
    else if x = 1 ∧ y = 2 then c 2 = true
    else if x = 2 ∧ y = 1 then c 2 = false
    else False

  let encode3 (R : Fin 3 → Fin 3 → Prop) [DecidableRel R] : Fin 3 → Bool :=
    ![decide (R 0 1), decide (R 0 2), decide (R 1 2)]

  have rel3_encode {R : Fin 3 → Fin 3 → Prop} [DecidableRel R]
      (hR : IsTournament R) : ∀ x y, rel3 (encode3 R) x y ↔ R x y := by
    intro x y
    have h01 := not_orientation_iff_reverse hR (by decide : (0 : Fin 3) ≠ 1)
    have h02 := not_orientation_iff_reverse hR (by decide : (0 : Fin 3) ≠ 2)
    have h12 := not_orientation_iff_reverse hR (by decide : (1 : Fin 3) ≠ 2)
    fin_cases x <;> fin_cases y <;> simp [rel3, encode3, hR.1, h01, h02, h12]

  letI rel3Decidable (c : Fin 3 → Bool) : DecidableRel (rel3 c) :=
    fun _ _ ↦ by unfold rel3; infer_instance

  let outdegree {n : Nat} (R : Fin n → Fin n → Prop) [DecidableRel R]
      (x : Fin n) : Nat :=
    ((Finset.univ : Finset (Fin n)).filter (R x)).card

  let cubeSum {n : Nat} (R : Fin n → Fin n → Prop) [DecidableRel R] : Nat :=
    ∑ x, (outdegree R x) ^ 3

  let class3 (c : Fin 3 → Bool) : Fin 2 :=
    if cubeSum (rel3 c) = 9 then 0 else 1

  have rel3_iso_of_class_eq (c d : Fin 3 → Bool)
      (h : class3 c = class3 d) :
      ∃ e : Equiv.Perm (Fin 3), ∀ x y, rel3 d (e x) (e y) ↔ rel3 c x y := by
    revert c d
    decide

  let rel4 (c : Fin 6 → Bool) (x y : Fin 4) : Prop :=
    if x = 0 ∧ y = 1 then c 0 = true
    else if x = 1 ∧ y = 0 then c 0 = false
    else if x = 0 ∧ y = 2 then c 1 = true
    else if x = 2 ∧ y = 0 then c 1 = false
    else if x = 0 ∧ y = 3 then c 2 = true
    else if x = 3 ∧ y = 0 then c 2 = false
    else if x = 1 ∧ y = 2 then c 3 = true
    else if x = 2 ∧ y = 1 then c 3 = false
    else if x = 1 ∧ y = 3 then c 4 = true
    else if x = 3 ∧ y = 1 then c 4 = false
    else if x = 2 ∧ y = 3 then c 5 = true
    else if x = 3 ∧ y = 2 then c 5 = false
    else False

  let encode4 (R : Fin 4 → Fin 4 → Prop) [DecidableRel R] : Fin 6 → Bool :=
    ![decide (R 0 1), decide (R 0 2), decide (R 0 3),
      decide (R 1 2), decide (R 1 3), decide (R 2 3)]

  have rel4_encode {R : Fin 4 → Fin 4 → Prop} [DecidableRel R]
      (hR : IsTournament R) : ∀ x y, rel4 (encode4 R) x y ↔ R x y := by
    intro x y
    have h01 := not_orientation_iff_reverse hR (by decide : (0 : Fin 4) ≠ 1)
    have h02 := not_orientation_iff_reverse hR (by decide : (0 : Fin 4) ≠ 2)
    have h03 := not_orientation_iff_reverse hR (by decide : (0 : Fin 4) ≠ 3)
    have h12 := not_orientation_iff_reverse hR (by decide : (1 : Fin 4) ≠ 2)
    have h13 := not_orientation_iff_reverse hR (by decide : (1 : Fin 4) ≠ 3)
    have h23 := not_orientation_iff_reverse hR (by decide : (2 : Fin 4) ≠ 3)
    fin_cases x <;> fin_cases y <;>
      simp [rel4, encode4, hR.1, h01, h02, h03, h12, h13, h23]

  letI rel4Decidable (c : Fin 6 → Bool) : DecidableRel (rel4 c) :=
    fun _ _ ↦ by unfold rel4; infer_instance

  let class4 (c : Fin 6 → Bool) : Fin 4 :=
    if cubeSum (rel4 c) = 36 then 0
    else if cubeSum (rel4 c) = 30 then 1
    else if cubeSum (rel4 c) = 24 then 2
    else 3

  have rel4_iso_of_class_eq (c d : Fin 6 → Bool)
      (h : class4 c = class4 d) :
      ∃ e : Equiv.Perm (Fin 4), ∀ x y, rel4 d (e x) (e y) ↔ rel4 c x y := by
    revert c d
    decide

  let d6Arcs : List (Fin 6 × Fin 6) :=
    [(0, 5), (0, 2), (0, 3), (1, 0), (2, 1),
     (2, 3), (2, 5), (3, 4), (3, 5), (3, 1),
     (4, 0), (4, 1), (4, 2), (4, 5), (5, 1)]

  let d6 (x y : Fin 6) : Prop := (x, y) ∈ d6Arcs

  letI d6Decidable : DecidableRel d6 := fun _ _ ↦ by unfold d6; infer_instance

  have d6_tournament : IsTournament d6 := by decide

  have d6_delete_no_perm :
      ∀ x y : Fin 6, x ≠ y → ∀ e : Equiv.Perm (Fin 5),
        ¬ ∀ a b, deleteRel d6 y (e a) (e b) ↔ deleteRel d6 x a b := by
    decide

  have d6_link_irregular : LinkIrregular d6 := by
    intro x y hxy
    refine ⟨fun f ↦ ?_⟩
    have g : deleteRel d6 x ≃r deleteRel d6 y :=
      (linkDeleteIso d6_tournament x).symm.trans (f.trans (linkDeleteIso d6_tournament y))
    exact d6_delete_no_perm x y hxy g.toEquiv (fun _ _ ↦ g.map_rel_iff)

  have delete_tournament {n : Nat}
      {R : Fin (n + 1) → Fin (n + 1) → Prop} (hR : IsTournament R)
      (v : Fin (n + 1)) : IsTournament (deleteRel R v) := by
    constructor
    · intro x
      exact hR.1 _
    · intro x y hxy
      exact hR.2 _ _ ((Fin.strictMono_succAbove v).injective.ne hxy)

  have not_linkIrregular_of_delete_iso {n : Nat}
      {R : Fin (n + 1) → Fin (n + 1) → Prop} (hR : IsTournament R)
      {x y : Fin (n + 1)} (hxy : x ≠ y)
      (e : deleteRel R x ≃r deleteRel R y) : ¬ LinkIrregular R := by
    intro h
    exact (h x y hxy).false
      ((linkDeleteIso hR x).trans (e.trans (linkDeleteIso hR y).symm))

  have no_small_link_irregular (n : Nat) (hn2 : 2 ≤ n) (hn6 : n < 6) :
      ¬ ∃ R : Fin n → Fin n → Prop, IsTournament R ∧ LinkIrregular R := by
    interval_cases n
    case «2» =>
      rintro ⟨R, hR, hL⟩
      letI : DecidableRel R := Classical.decRel R
      have e : deleteRel R 0 ≃r deleteRel R 1 := by
        refine relIsoOfPerm (Equiv.refl (Fin 1)) ?_
        intro x y
        fin_cases x
        fin_cases y
        constructor
        · exact fun h ↦ ((delete_tournament hR 1).1 0 h).elim
        · exact fun h ↦ ((delete_tournament hR 0).1 0 h).elim
      exact not_linkIrregular_of_delete_iso hR (by decide : (0 : Fin 2) ≠ 1) e hL
    case «3» =>
      rintro ⟨R, hR, hL⟩
      letI : DecidableRel R := Classical.decRel R
      let c : Fin 3 → Fin 1 → Bool := fun v ↦ encode2 (deleteRel R v)
      obtain ⟨e, he⟩ := rel2_iso (c 0) (c 1)
      have ec : rel2 (c 0) ≃r rel2 (c 1) := relIsoOfPerm e he
      have ex : rel2 (c 0) ≃r deleteRel R 0 :=
        relIsoOfIff _ _ (rel2_encode (delete_tournament hR 0))
      have ey : rel2 (c 1) ≃r deleteRel R 1 :=
        relIsoOfIff _ _ (rel2_encode (delete_tournament hR 1))
      exact not_linkIrregular_of_delete_iso hR (by decide : (0 : Fin 3) ≠ 1)
        (ex.symm.trans (ec.trans ey)) hL
    case «4» =>
      rintro ⟨R, hR, hL⟩
      letI : DecidableRel R := Classical.decRel R
      let c : Fin 4 → Fin 3 → Bool := fun v ↦ encode3 (deleteRel R v)
      let k : Fin 4 → Fin 2 := fun v ↦ class3 (c v)
      obtain ⟨x, y, hxy, hk⟩ := Fintype.exists_ne_map_eq_of_card_lt k (by decide)
      obtain ⟨e, he⟩ := rel3_iso_of_class_eq (c x) (c y) hk
      have ec : rel3 (c x) ≃r rel3 (c y) := relIsoOfPerm e he
      have ex : rel3 (c x) ≃r deleteRel R x :=
        relIsoOfIff _ _ (rel3_encode (delete_tournament hR x))
      have ey : rel3 (c y) ≃r deleteRel R y :=
        relIsoOfIff _ _ (rel3_encode (delete_tournament hR y))
      exact not_linkIrregular_of_delete_iso hR hxy (ex.symm.trans (ec.trans ey)) hL
    case «5» =>
      rintro ⟨R, hR, hL⟩
      letI : DecidableRel R := Classical.decRel R
      let c : Fin 5 → Fin 6 → Bool := fun v ↦ encode4 (deleteRel R v)
      let k : Fin 5 → Fin 4 := fun v ↦ class4 (c v)
      obtain ⟨x, y, hxy, hk⟩ := Fintype.exists_ne_map_eq_of_card_lt k (by decide)
      obtain ⟨e, he⟩ := rel4_iso_of_class_eq (c x) (c y) hk
      have ec : rel4 (c x) ≃r rel4 (c y) := relIsoOfPerm e he
      have ex : rel4 (c x) ≃r deleteRel R x :=
        relIsoOfIff _ _ (rel4_encode (delete_tournament hR x))
      have ey : rel4 (c y) ≃r deleteRel R y :=
        relIsoOfIff _ _ (rel4_encode (delete_tournament hR y))
      exact not_linkIrregular_of_delete_iso hR hxy (ex.symm.trans (ec.trans ey)) hL

  let windmill (m : Nat) (x y : Fin (m + 1)) : Prop :=
    (x = Fin.last m ∧ y ≠ Fin.last m ∧ y.val % 2 = 0) ∨
    (x ≠ Fin.last m ∧ y = Fin.last m ∧ x.val % 2 = 1) ∨
    (x ≠ Fin.last m ∧ y ≠ Fin.last m ∧ x < y)

  letI windmillDecidable (m : Nat) : DecidableRel (windmill m) :=
    fun _ _ ↦ by unfold windmill; infer_instance

  have windmill_tournament (m : Nat) : IsTournament (windmill m) := by
    constructor
    · intro x
      unfold windmill
      rintro (h | h | h)
      · exact h.2.1 h.1
      · exact h.1 h.2.1
      · exact (lt_irrefl x) h.2.2
    · intro x y hxy
      rw [xor_iff_or_and_not_and]
      by_cases hx : x = Fin.last m
      · subst x
        have hy : y ≠ Fin.last m := by simpa [eq_comm] using hxy
        rcases Nat.mod_two_eq_zero_or_one y.val with he | ho
        · simp [windmill, hy, he]
        · simp [windmill, hy, ho]
      · by_cases hy : y = Fin.last m
        · subst y
          rcases Nat.mod_two_eq_zero_or_one x.val with he | ho
          · simp [windmill, hx, he]
          · simp [windmill, hx, ho]
        · rcases lt_trichotomy x y with hlt | heq | hgt
          · simp [windmill, hx, hy, hlt, hlt.not_gt]
          · exact (hxy heq).elim
          · simp [windmill, hx, hy, hgt, hgt.not_gt]

  have windmill_chain {m : Nat} {x y : Fin (m + 1)}
      (hx : x ≠ Fin.last m) (hy : y ≠ Fin.last m) :
      windmill m x y ↔ x < y := by
    simp [windmill, hx, hy]

  have exists_intact_adjacent_pair {m : Nat} (hm : 6 ≤ m)
      (x z : Fin (m + 1)) :
      ∃ a b : Fin (m + 1),
        a.val % 2 = 0 ∧ b.val = a.val + 1 ∧
        b.val < m ∧
        a ≠ x ∧ b ≠ x ∧ a ≠ z ∧ b ≠ z := by
    let v0 : Fin (m + 1) := ⟨0, by omega⟩
    let v1 : Fin (m + 1) := ⟨1, by omega⟩
    let v2 : Fin (m + 1) := ⟨2, by omega⟩
    let v3 : Fin (m + 1) := ⟨3, by omega⟩
    let v4 : Fin (m + 1) := ⟨4, by omega⟩
    let v5 : Fin (m + 1) := ⟨5, by omega⟩
    by_cases h0 : v0 ≠ x ∧ v1 ≠ x ∧ v0 ≠ z ∧ v1 ≠ z
    · exact ⟨v0, v1, by norm_num [v0], rfl, by dsimp [v1]; omega, h0⟩
    by_cases h2 : v2 ≠ x ∧ v3 ≠ x ∧ v2 ≠ z ∧ v3 ≠ z
    · exact ⟨v2, v3, by norm_num [v2], rfl, by dsimp [v3]; omega, h2⟩
    refine ⟨v4, v5, by norm_num [v4], rfl, by dsimp [v5]; omega, ?_⟩
    have hv02 : v0 ≠ v2 := by intro h; have := congrArg Fin.val h; norm_num [v0, v2] at this
    have hv03 : v0 ≠ v3 := by intro h; have := congrArg Fin.val h; norm_num [v0, v3] at this
    have hv12 : v1 ≠ v2 := by intro h; have := congrArg Fin.val h; norm_num [v1, v2] at this
    have hv13 : v1 ≠ v3 := by intro h; have := congrArg Fin.val h; norm_num [v1, v3] at this
    have hv04 : v0 ≠ v4 := by intro h; have := congrArg Fin.val h; norm_num [v0, v4] at this
    have hv05 : v0 ≠ v5 := by intro h; have := congrArg Fin.val h; norm_num [v0, v5] at this
    have hv14 : v1 ≠ v4 := by intro h; have := congrArg Fin.val h; norm_num [v1, v4] at this
    have hv15 : v1 ≠ v5 := by intro h; have := congrArg Fin.val h; norm_num [v1, v5] at this
    have hv24 : v2 ≠ v4 := by intro h; have := congrArg Fin.val h; norm_num [v2, v4] at this
    have hv25 : v2 ≠ v5 := by intro h; have := congrArg Fin.val h; norm_num [v2, v5] at this
    have hv34 : v3 ≠ v4 := by intro h; have := congrArg Fin.val h; norm_num [v3, v4] at this
    have hv35 : v3 ≠ v5 := by intro h; have := congrArg Fin.val h; norm_num [v3, v5] at this
    have hv40 : v4 ≠ v0 := hv04.symm
    have hv50 : v5 ≠ v0 := hv05.symm
    have hv41 : v4 ≠ v1 := hv14.symm
    have hv51 : v5 ≠ v1 := hv15.symm
    have hv42 : v4 ≠ v2 := hv24.symm
    have hv52 : v5 ≠ v2 := hv25.symm
    have hv43 : v4 ≠ v3 := hv34.symm
    have hv53 : v5 ≠ v3 := hv35.symm
    simp only [not_and_or] at h0 h2
    rcases h0 with h0 | h0 | h0 | h0 <;>
      rcases h2 with h2 | h2 | h2 | h2 <;>
      simp only [not_ne_iff] at h0 h2 <;>
      subst_vars <;>
      simp_all only [ne_eq, not_false_eq_true, true_and]

  have transitive_delete_pivot {k : Nat} {x : Fin (k + 2)}
      (hx : x ≠ Fin.last (k + 1)) :
      Transitive (deleteRel (deleteRel (windmill (k + 1)) x) (Fin.last k)) := by
    intro a b c hab hbc
    change windmill (k + 1)
      (x.succAbove ((Fin.last k).succAbove a))
      (x.succAbove ((Fin.last k).succAbove b)) at hab
    change windmill (k + 1)
      (x.succAbove ((Fin.last k).succAbove b))
      (x.succAbove ((Fin.last k).succAbove c)) at hbc
    change windmill (k + 1)
      (x.succAbove ((Fin.last k).succAbove a))
      (x.succAbove ((Fin.last k).succAbove c))
    have ha : x.succAbove ((Fin.last k).succAbove a) ≠ Fin.last (k + 1) :=
      Fin.succAbove_ne_last hx (by simp)
    have hb : x.succAbove ((Fin.last k).succAbove b) ≠ Fin.last (k + 1) :=
      Fin.succAbove_ne_last hx (by simp)
    have hc : x.succAbove ((Fin.last k).succAbove c) ≠ Fin.last (k + 1) :=
      Fin.succAbove_ne_last hx (by simp)
    rw [windmill_chain ha hb] at hab
    rw [windmill_chain hb hc] at hbc
    rw [windmill_chain ha hc]
    exact hab.trans hbc

  have not_transitive_delete_nonpivot {k : Nat} (hk : 5 ≤ k)
      {x : Fin (k + 2)} (hx : x ≠ Fin.last (k + 1))
      {q : Fin (k + 1)} (hq : q ≠ Fin.last k) :
      ¬ Transitive (deleteRel (deleteRel (windmill (k + 1)) x) q) := by
    let z : Fin (k + 2) := x.succAbove q
    have hz : z ≠ Fin.last (k + 1) := Fin.succAbove_ne_last hx hq
    obtain ⟨a, b, haeven, hbnext, hb_lt, hax, hbx, haz, hbz⟩ :=
      exists_intact_adjacent_pair (m := k + 1) (by omega) x z
    have ha_last : a ≠ Fin.last (k + 1) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega
    have hb_last : b ≠ Fin.last (k + 1) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega
    let ca : Fin (k + 1) := (finSuccAboveEquiv x).symm ⟨a, hax⟩
    let cb : Fin (k + 1) := (finSuccAboveEquiv x).symm ⟨b, hbx⟩
    let cp : Fin (k + 1) := (finSuccAboveEquiv x).symm
      ⟨Fin.last (k + 1), hx.symm⟩
    have ca_spec : x.succAbove ca = a := by
      exact congrArg Subtype.val ((finSuccAboveEquiv x).apply_symm_apply ⟨a, hax⟩)
    have cb_spec : x.succAbove cb = b := by
      exact congrArg Subtype.val ((finSuccAboveEquiv x).apply_symm_apply ⟨b, hbx⟩)
    have cp_spec : x.succAbove cp = Fin.last (k + 1) := by
      exact congrArg Subtype.val
        ((finSuccAboveEquiv x).apply_symm_apply ⟨Fin.last (k + 1), hx.symm⟩)
    have caq : ca ≠ q := by
      intro h
      apply haz
      rw [← ca_spec, h]
    have cbq : cb ≠ q := by
      intro h
      apply hbz
      rw [← cb_spec, h]
    have cpq : cp ≠ q := by
      intro h
      apply hz
      rw [← cp_spec, h]
    let aa : Fin k := (finSuccAboveEquiv q).symm ⟨ca, caq⟩
    let bb : Fin k := (finSuccAboveEquiv q).symm ⟨cb, cbq⟩
    let pp : Fin k := (finSuccAboveEquiv q).symm ⟨cp, cpq⟩
    have aa_spec : x.succAbove (q.succAbove aa) = a := by
      rw [← ca_spec]
      congr 1
      exact congrArg Subtype.val ((finSuccAboveEquiv q).apply_symm_apply ⟨ca, caq⟩)
    have bb_spec : x.succAbove (q.succAbove bb) = b := by
      rw [← cb_spec]
      congr 1
      exact congrArg Subtype.val ((finSuccAboveEquiv q).apply_symm_apply ⟨cb, cbq⟩)
    have pp_spec : x.succAbove (q.succAbove pp) = Fin.last (k + 1) := by
      rw [← cp_spec]
      congr 1
      exact congrArg Subtype.val ((finSuccAboveEquiv q).apply_symm_apply ⟨cp, cpq⟩)
    have hbodd : b.val % 2 = 1 := by omega
    intro htrans
    have hpa : deleteRel (deleteRel (windmill (k + 1)) x) q pp aa := by
      change windmill (k + 1) (x.succAbove (q.succAbove pp))
        (x.succAbove (q.succAbove aa))
      rw [pp_spec, aa_spec]
      simp [windmill, ha_last, haeven]
    have hab : deleteRel (deleteRel (windmill (k + 1)) x) q aa bb := by
      change windmill (k + 1) (x.succAbove (q.succAbove aa))
        (x.succAbove (q.succAbove bb))
      rw [aa_spec, bb_spec, windmill_chain ha_last hb_last]
      exact Fin.mk_lt_mk.mpr (by omega)
    have hpb := htrans hpa hab
    change windmill (k + 1) (x.succAbove (q.succAbove pp))
      (x.succAbove (q.succAbove bb)) at hpb
    rw [pp_spec, bb_spec] at hpb
    simpa [windmill, hb_last, hbodd] using hpb

  let deleteSubrelIso {n : Nat} (R : Fin (n + 1) → Fin (n + 1) → Prop)
      (q : Fin (n + 1)) :
      deleteRel R q ≃r Subrel R (fun x ↦ x ≠ q) := {
    toEquiv := finSuccAboveEquiv q
    map_rel_iff' := Iff.rfl
  }

  let subrelNeIso {V W : Type} {R : V → V → Prop} {S : W → W → Prop}
      (f : R ≃r S) (q : V) :
      Subrel R (fun x ↦ x ≠ q) ≃r Subrel S (fun y ↦ y ≠ f q) := {
    toFun x := ⟨f x.1, fun h ↦ x.2 (f.injective h)⟩
    invFun y := ⟨f.symm y.1, fun h ↦ y.2 (by
      calc
        y.1 = f (f.symm y.1) := (f.apply_symm_apply y.1).symm
        _ = f q := congrArg f h)⟩
    left_inv x := by
      apply Subtype.ext
      simp
    right_inv y := by
      apply Subtype.ext
      simp
    map_rel_iff' := by
      intro x y
      exact f.map_rel_iff
  }

  let deleteRelIso {n : Nat}
      {R S : Fin (n + 1) → Fin (n + 1) → Prop} (f : R ≃r S)
      (q : Fin (n + 1)) : deleteRel R q ≃r deleteRel S (f q) :=
    (deleteSubrelIso R q).trans
      ((subrelNeIso f q).trans (deleteSubrelIso S (f q)).symm)

  have transitive_of_relIso {V W : Type}
      {R : V → V → Prop} {S : W → W → Prop}
      (f : R ≃r S) (h : Transitive R) : Transitive S := by
    intro a b c hab hbc
    have hrab : R (f.symm a) (f.symm b) := (f.symm.map_rel_iff).2 hab
    have hrbc : R (f.symm b) (f.symm c) := (f.symm.map_rel_iff).2 hbc
    have hs : S (f (f.symm a)) (f (f.symm c)) :=
      f.map_rel_iff.mpr (h hrab hrbc)
    simpa using hs

  have relIso_fixes_pivot {k : Nat} (hk : 5 ≤ k)
      {x y : Fin (k + 2)} (hx : x ≠ Fin.last (k + 1))
      (hy : y ≠ Fin.last (k + 1))
      (f : deleteRel (windmill (k + 1)) x ≃r deleteRel (windmill (k + 1)) y) :
      f (Fin.last k) = Fin.last k := by
    by_contra h
    apply not_transitive_delete_nonpivot hk hy h
    exact transitive_of_relIso (deleteRelIso f (Fin.last k))
      (transitive_delete_pivot hx)

  have delete_pivot_iff_lt {k : Nat} {x : Fin (k + 2)}
      (hx : x ≠ Fin.last (k + 1)) (a b : Fin k) :
      deleteRel (deleteRel (windmill (k + 1)) x) (Fin.last k) a b ↔ a < b := by
    change windmill (k + 1)
      (x.succAbove ((Fin.last k).succAbove a))
      (x.succAbove ((Fin.last k).succAbove b)) ↔ a < b
    rw [windmill_chain
      (Fin.succAbove_ne_last hx (by simp))
      (Fin.succAbove_ne_last hx (by simp))]
    simp

  have card_chain_iff_lt {k : Nat} {x : Fin (k + 2)}
      (hx : x ≠ Fin.last (k + 1)) {a b : Fin (k + 1)}
      (ha : a ≠ Fin.last k) (hb : b ≠ Fin.last k) :
      deleteRel (windmill (k + 1)) x a b ↔ a < b := by
    change windmill (k + 1) (x.succAbove a) (x.succAbove b) ↔ a < b
    rw [windmill_chain (Fin.succAbove_ne_last hx ha) (Fin.succAbove_ne_last hx hb)]
    simp

  let chainSubrelIso {k : Nat} {x : Fin (k + 2)}
      (hx : x ≠ Fin.last (k + 1)) :
      ((· < ·) : {q : Fin (k + 1) // q ≠ Fin.last k} →
        {q : Fin (k + 1) // q ≠ Fin.last k} → Prop) ≃r
      Subrel (deleteRel (windmill (k + 1)) x) (fun q ↦ q ≠ Fin.last k) :=
    relIsoOfIff _ _ fun a b ↦
      (card_chain_iff_lt hx a.2 b.2).symm

  have relIso_fixes_chain_rank {k : Nat} (hk : 5 ≤ k)
      {x y : Fin (k + 2)} (hx : x ≠ Fin.last (k + 1))
      (hy : y ≠ Fin.last (k + 1))
      (f : deleteRel (windmill (k + 1)) x ≃r deleteRel (windmill (k + 1)) y)
      {q : Fin (k + 1)} (hq : q ≠ Fin.last k) : f q = q := by
    have hp := relIso_fixes_pivot hk hx hy f
    let gsub :
        Subrel (deleteRel (windmill (k + 1)) x) (fun q ↦ q ≠ Fin.last k) ≃r
        Subrel (deleteRel (windmill (k + 1)) y) (fun q ↦ q ≠ Fin.last k) := {
      toFun a := ⟨f a.1, fun h ↦ a.2 (f.injective (h.trans hp.symm))⟩
      invFun b := ⟨f.symm b.1, fun h ↦ b.2 (by
        calc
          b.1 = f (f.symm b.1) := (f.apply_symm_apply b.1).symm
          _ = f (Fin.last k) := congrArg f h
          _ = Fin.last k := hp)⟩
      left_inv a := by apply Subtype.ext; simp
      right_inv b := by apply Subtype.ext; simp
      map_rel_iff' := by intro a b; exact f.map_rel_iff
    }
    let e : ((· < ·) : Fin k → Fin k → Prop) ≃r ((· < ·) : Fin k → Fin k → Prop) :=
      (finSuccAboveOrderIso (Fin.last k)).toRelIsoLT |>.trans
        ((chainSubrelIso hx).trans
          (gsub.trans ((chainSubrelIso hy).symm.trans
            (finSuccAboveOrderIso (Fin.last k)).symm.toRelIsoLT)))
    let i : Fin k := (finSuccAboveOrderIso (Fin.last k)).symm ⟨q, hq⟩
    have hei : e i = i := by
      apply Fin.ext
      exact Fin.coe_orderIso_apply (OrderIso.ofRelIsoLT e) i
    have hsub := congrArg (finSuccAboveOrderIso (Fin.last k)) hei
    have hval := congrArg Subtype.val hsub
    simpa [e, i, chainSubrelIso, relIsoOfIff, gsub, RelIso.trans, RelIso.symm,
      OrderIso.ofRelIsoLT] using hval

  have no_relIso_chain_cards {k : Nat} (hk : 5 ≤ k)
      {x y : Fin (k + 2)} (hx : x ≠ Fin.last (k + 1))
      (hy : y ≠ Fin.last (k + 1)) (hxy : x ≠ y) :
      IsEmpty
        (deleteRel (windmill (k + 1)) x ≃r deleteRel (windmill (k + 1)) y) := by
    refine ⟨fun f ↦ ?_⟩
    let dx : Fin (k + 1) := ⟨x.val, Fin.val_lt_last hx⟩
    let dy : Fin (k + 1) := ⟨y.val, Fin.val_lt_last hy⟩
    have hx_repr : dx.castSucc = x := by apply Fin.ext; rfl
    have hy_repr : dy.castSucc = y := by apply Fin.ext; rfl
    have hdxy : dx ≠ dy := by
      intro h
      apply hxy
      rw [← hx_repr, ← hy_repr, h]
    have hp := relIso_fixes_pivot hk hx hy f
    rcases lt_trichotomy dx dy with hlt | heq | hgt
    · have hq : dx ≠ Fin.last k := by
        intro h
        have := congrArg Fin.val h
        have hdy := dy.isLt
        simp only [Fin.val_last] at this
        omega
      have hfix := relIso_fixes_chain_rank hk hx hy f hq
      have hxmap : x.succAbove dx = dx.succ := by
        rw [← hx_repr]
        exact Fin.succAbove_castSucc_self dx
      have hymap : y.succAbove dx = dx.castSucc := by
        rw [← hy_repr]
        exact Fin.succAbove_castSucc_of_lt dy dx hlt
      have hor := f.map_rel_iff (a := Fin.last k) (b := dx)
      rw [hp, hfix] at hor
      change windmill (k + 1) (y.succAbove (Fin.last k)) (y.succAbove dx) ↔
        windmill (k + 1) (x.succAbove (Fin.last k)) (x.succAbove dx) at hor
      rw [Fin.succAbove_ne_last_last hy, Fin.succAbove_ne_last_last hx, hxmap, hymap] at hor
      simp [windmill] at hor
      rcases Nat.mod_two_eq_zero_or_one dx.val with he | ho <;> omega
    · exact (hdxy heq).elim
    · have hq : dy ≠ Fin.last k := by
        intro h
        have := congrArg Fin.val h
        have hdx := dx.isLt
        simp only [Fin.val_last] at this
        omega
      have hfix := relIso_fixes_chain_rank hk hx hy f hq
      have hymap : y.succAbove dy = dy.succ := by
        rw [← hy_repr]
        exact Fin.succAbove_castSucc_self dy
      have hxmap : x.succAbove dy = dy.castSucc := by
        rw [← hx_repr]
        exact Fin.succAbove_castSucc_of_lt dx dy hgt
      have hor := f.map_rel_iff (a := Fin.last k) (b := dy)
      rw [hp, hfix] at hor
      change windmill (k + 1) (y.succAbove (Fin.last k)) (y.succAbove dy) ↔
        windmill (k + 1) (x.succAbove (Fin.last k)) (x.succAbove dy) at hor
      rw [Fin.succAbove_ne_last_last hy, Fin.succAbove_ne_last_last hx, hxmap, hymap] at hor
      simp [windmill] at hor
      rcases Nat.mod_two_eq_zero_or_one dy.val with he | ho <;> omega

  have transitive_delete_of_transitive {n : Nat}
      {R : Fin (n + 1) → Fin (n + 1) → Prop} (h : Transitive R)
      (q : Fin (n + 1)) : Transitive (deleteRel R q) := by
    intro a b c hab hbc
    exact h hab hbc

  have transitive_pivot_card (k : Nat) :
      Transitive (deleteRel (windmill (k + 1)) (Fin.last (k + 1))) := by
    intro a b c hab hbc
    change windmill (k + 1) ((Fin.last (k + 1)).succAbove a)
      ((Fin.last (k + 1)).succAbove b) at hab
    change windmill (k + 1) ((Fin.last (k + 1)).succAbove b)
      ((Fin.last (k + 1)).succAbove c) at hbc
    change windmill (k + 1) ((Fin.last (k + 1)).succAbove a)
      ((Fin.last (k + 1)).succAbove c)
    rw [windmill_chain (by simp) (by simp)] at hab
    rw [windmill_chain (by simp) (by simp)] at hbc
    rw [windmill_chain (by simp) (by simp)]
    exact hab.trans hbc

  have not_transitive_chain_card {k : Nat} (hk : 5 ≤ k)
      {x : Fin (k + 2)} (hx : x ≠ Fin.last (k + 1)) :
      ¬ Transitive (deleteRel (windmill (k + 1)) x) := by
    intro h
    have hzero : (0 : Fin (k + 1)) ≠ Fin.last k := by
      intro hz
      have := congrArg Fin.val hz
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    exact not_transitive_delete_nonpivot hk hx hzero
      (transitive_delete_of_transitive h 0)

  have windmill_link_irregular (k : Nat) (hk : 5 ≤ k) :
      LinkIrregular (windmill (k + 1)) := by
    intro x y hxy
    refine ⟨fun f ↦ ?_⟩
    have g : deleteRel (windmill (k + 1)) x ≃r deleteRel (windmill (k + 1)) y :=
      (linkDeleteIso (windmill_tournament (k + 1)) x).symm.trans
        (f.trans (linkDeleteIso (windmill_tournament (k + 1)) y))
    by_cases hx : x = Fin.last (k + 1)
    · subst x
      have hy : y ≠ Fin.last (k + 1) := hxy.symm
      exact not_transitive_chain_card hk hy
        (transitive_of_relIso g (transitive_pivot_card k))
    · by_cases hy : y = Fin.last (k + 1)
      · subst y
        exact not_transitive_chain_card hk hx
          (transitive_of_relIso g.symm (transitive_pivot_card k))
      · exact (no_relIso_chain_cards hk hx hy hxy).false g

  intro n hn
  constructor
  · intro h
    by_contra hn6
    exact no_small_link_irregular n hn (by omega) h
  · intro hn6
    by_cases h6 : n = 6
    · subst n
      exact ⟨d6, d6_tournament, d6_link_irregular⟩
    · let k := n - 2
      have hk : 5 ≤ k := by dsimp [k]; omega
      have hnk : n = k + 2 := by dsimp [k]; omega
      rw [hnk]
      exact ⟨windmill (k + 1), windmill_tournament (k + 1),
        windmill_link_irregular k hk⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence
