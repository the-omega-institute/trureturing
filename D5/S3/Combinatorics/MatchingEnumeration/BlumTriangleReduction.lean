/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleReduction
   mirror-E: none(waiver:actual-reflection-component-separation)
   anchors: []
   utility: none
   digest: Axis-component separation and switching give the reflection count reduction. -/

import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleRay
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleReduced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleReduction

open BlumTriangleDefs BlumTriangleSwitching BlumTriangleOverlay Finset

set_option maxHeartbeats 12000000 in

/-- The actual axis pairing separates the marked vertices, and component switching gives
exactly one reduced matching for every normalized side-choice fiber. -/
theorem reflection_reduction (k : ℕ) (hk : 1 ≤ k) :
    M (4 * k) = 2 ^ k * Nat.card
      {p : Vertex (4 * k) → Vertex (4 * k) //
        ∀ u, p (p u) = u ∧ p u ≠ u ∧ BlumTriangleReduced.reducedAdj k u (p u)} := by
  classical
  have axis_pairing_noncrossing (k : ℕ) (P : PerfectMatching (4 * k))
      (a b c d : Vertex (4 * k))
      (ha : reflection (4 * k) a = a) (hb : reflection (4 * k) b = b)
      (hc : reflection (4 * k) c = c) (hd : reflection (4 * k) d = d)
      (hab : Relation.EqvGen
        (fun u v => v = P.1 u ∨ v = reflection (4 * k) (P.1 (reflection (4 * k) u))) a b)
      (hcd : Relation.EqvGen
        (fun u v => v = P.1 u ∨ v = reflection (4 * k) (P.1 (reflection (4 * k) u))) c d)
      (horder : a.1.1.val < c.1.1.val ∧ c.1.1.val < b.1.1.val ∧
        b.1.1.val < d.1.1.val) : False := by
    let V := Vertex (4 * k)
    let : Fintype V := inferInstance
    let : DecidableEq V := inferInstance
    classical
    let h := 4 * k - 1
    let r : V → V := reflection (4 * k)
    let p := P.1
    let q : V → V := fun u => r (p (r u))
    let edge : V → V → Prop := fun u v => v = p u ∨ v = q u
    let conn := Relation.EqvGen edge
    have rr (u : V) : r (r u) = u := (reflection (4 * k)).left_inv u
    have pp (u : V) : p (p u) = u := (P.2 u).1
    have qq (u : V) : q (q u) = u := by simp only [q, rr, pp]
    have rx (u : V) : (r u).1.2.val = 2 * h - u.1.2.val := rfl
    have axis_iff (u : V) : r u = u ↔ u.1.2.val = h := by
      constructor
      · intro he
        have he' := congrArg (fun v : V => v.1.2.val) he
        rw [rx] at he'
        have hv := u.2
        dsimp [h] at *
        omega
      · intro he
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Fin.ext
          rw [rx, he]
          omega
    have ax := (axis_iff a).mp ha
    have bx := (axis_iff b).mp hb
    have cx := (axis_iff c).mp hc
    have dx := (axis_iff d).mp hd
    have padj (u : V) : Adj u (p u) := (P.2 u).2.2
    have qadj (u : V) : Adj u (q u) := by
      have he := (reflection (4 * k)).map_rel_iff.mpr (padj (r u))
      change Adj (r (r u)) (r (p (r u))) at he
      simpa only [rr] using he
    have edge_adj {u v : V} (he : edge u v) : Adj u v := by
      rcases he with rfl | rfl
      · exact padj u
      · exact qadj u
    have carry {u v : V} (he : conn u v) : conn a u ↔ conn a v :=
      ⟨fun hu => Relation.EqvGen.trans _ _ _ hu he,
        fun hv => Relation.EqvGen.trans _ _ _ hv (Relation.EqvGen.symm _ _ he)⟩
    have axis_no_adj (u v : V) (hu : u.1.2.val = h) (hv : v.1.2.val = h) :
        ¬ Adj u v := by
      have hup := u.2
      have hvp := v.2
      have hr := u.1.1.isLt
      intro he
      rcases he with he | he
      all_goals rcases he with ⟨he, hx | hx⟩ | ⟨hp, ⟨he, hx⟩ | ⟨he, hx⟩⟩
      all_goals dsimp [h] at *
      all_goals omega
    have crossing (u v : V) (he : Adj u v)
        (hu : u.1.2.val < h) (hv : h < v.1.2.val) : v = r u := by
      have hup := u.2
      have hvp := v.2
      have hr := u.1.1.isLt
      have he' : v.1.1 = u.1.1 ∧ v.1.2.val = 2 * h - u.1.2.val := by
        rcases he with he | he
        · rcases he with ⟨he, hx | hx⟩ | ⟨hp, ⟨he, hx⟩ | ⟨he, hx⟩⟩
          all_goals omega
        · rcases he with ⟨he, hx | hx⟩ | ⟨hp, ⟨he, hx⟩ | ⟨he, hx⟩⟩
          all_goals omega
      apply Subtype.ext
      apply Prod.ext
      · exact he'.1
      · exact Fin.ext he'.2
    let w : V → V → ZMod 2 := fun u v =>
      if conn a u ∧ u.1.2.val ≤ h ∧ v.1.2.val ≤ h then
        (if v = p u then 1 else 0) + (if v = q u then 1 else 0) else 0
    have red_iff (u v : V) : v = p u ↔ u = p v := by
      constructor <;> intro he
      · rw [he, pp]
      · rw [he, pp]
    have blue_iff (u v : V) : v = q u ↔ u = q v := by
      constructor <;> intro he
      · rw [he, qq]
      · rw [he, qq]
    have wsymm (u v : V) : w u v = w v u := by
      by_cases he : edge u v
      · have hconn := carry (Relation.EqvGen.rel _ _ he)
        dsimp [w]
        simp only [hconn, red_iff u v, blue_iff u v]
        by_cases hu : u.1.2.val ≤ h <;> by_cases hv : v.1.2.val ≤ h <;> simp [hu, hv]
      · have hp : v ≠ p u := fun hp => he (Or.inl hp)
        have hq : v ≠ q u := fun hq => he (Or.inr hq)
        have hp' : u ≠ p v := fun hu => hp ((red_iff u v).mpr hu)
        have hq' : u ≠ q v := fun hu => hq ((blue_iff u v).mpr hu)
        simp [w, hp, hq, hp', hq']
    have wsupport (u v : V) (he : ¬ Adj u v) : w u v = 0 := by
      have hp : v ≠ p u := fun hp => he (hp ▸ padj u)
      have hq : v ≠ q u := fun hq => he (hq ▸ qadj u)
      simp [w, hp, hq]
    have wleft (u v : V) (hw : w u v ≠ 0) : u.1.2.val ≤ h ∧ v.1.2.val ≤ h := by
      by_cases hl : conn a u ∧ u.1.2.val ≤ h ∧ v.1.2.val ≤ h
      · exact hl.2
      · exact False.elim (hw (if_neg hl))
    have row_sum (u : V) : (∑ v, w u v) =
        if conn a u ∧ u.1.2.val ≤ h then
          ((if (p u).1.2.val ≤ h then 1 else 0) : ZMod 2) +
            (if (q u).1.2.val ≤ h then 1 else 0) else 0 := by
      by_cases hu : conn a u ∧ u.1.2.val ≤ h
      · rw [if_pos hu]
        have term (v : V) : w u v =
            (if v = p u then (if (p u).1.2.val ≤ h then 1 else 0) else 0) +
              (if v = q u then (if (q u).1.2.val ≤ h then 1 else 0) else 0) := by
          by_cases hp : v = p u
          · subst v
            by_cases hq : p u = q u
            · by_cases hl : (p u).1.2.val ≤ h
              · have hql : (q u).1.2.val ≤ h := by rw [← hq]; exact hl
                simp [w, hu.1, hu.2, hq, hql]
              · have hql : ¬ (q u).1.2.val ≤ h := by rw [← hq]; exact hl
                simp [w, hu.1, hu.2, hq, hql]
            · by_cases hl : (p u).1.2.val ≤ h <;> simp [w, hu.1, hu.2, hq, hl]
          · by_cases hq : v = q u
            · subst v
              by_cases hl : (q u).1.2.val ≤ h <;> simp [w, hu.1, hu.2, hp, hl]
            · simp [w, hp, hq]
        simp_rw [term]
        rw [sum_add_distrib]
        simp only [sum_ite_eq', mem_univ, ite_true]
      · rw [if_neg hu]
        apply sum_eq_zero
        intro v _
        exact if_neg (by intro he; exact hu ⟨he.1, he.2.1⟩)
    have wdiv (u : V) (hu : u.1.2.val < h) : ∑ v, w u v = 0 := by
      rw [row_sum]
      by_cases hconn : conn a u
      · rw [if_pos ⟨hconn, by omega⟩]
        have same_side : (p u).1.2.val ≤ h ↔ (q u).1.2.val ≤ h := by
          have pright (hp : h < (p u).1.2.val) : q u = p u := by
            have he := crossing u (p u) (padj u) hu hp
            have pe : p (r u) = u := by rw [← he, pp]
            simpa only [q, pe] using he.symm
          have qright (hq : h < (q u).1.2.val) : p u = q u := by
            have he := crossing u (q u) (qadj u) hu hq
            have pe : p (r u) = u := by
              have he' := congrArg r he
              simpa only [q, rr] using he'
            have he' := congrArg p pe
            rw [pp] at he'
            exact he'.symm.trans he.symm
          constructor
          · intro hp
            by_contra hq
            have he := qright (by omega)
            rw [← he] at hq
            exact hq hp
          · intro hq
            by_contra hp
            have he := pright (by omega)
            rw [← he] at hp
            exact hp hq
        simpa only [same_side] using
          CharTwo.add_self_eq_zero ((if (q u).1.2.val ≤ h then 1 else 0) : ZMod 2)
      · rw [if_neg (by simp [hconn])]
    have divergence (u : V) : (∑ v, w u v) =
        if conn a u ∧ u.1.2.val = h then 1 else 0 := by
      by_cases hconn : conn a u
      · by_cases hu : u.1.2.val = h
        · rw [row_sum]
          rw [if_pos (show conn a u ∧ u.1.2.val ≤ h from ⟨hconn, by omega⟩),
            if_pos (show conn a u ∧ u.1.2.val = h from ⟨hconn, hu⟩)]
          have ru := (axis_iff u).mpr hu
          have pn : (p u).1.2.val ≠ h := fun hn => axis_no_adj u (p u) hu hn (padj u)
          have pv := (p u).2
          have px : (p u).1.2.val ≤ 2 * h := by dsimp [h]; omega
          have qx : (q u).1.2.val = 2 * h - (p u).1.2.val := by
            dsimp [q]
            rw [ru, rx]
          rw [qx]
          by_cases hl : (p u).1.2.val ≤ h
          · have hq : ¬ 2 * h - (p u).1.2.val ≤ h := by omega
            simp [hl, hq]
          · have hq : 2 * h - (p u).1.2.val ≤ h := by omega
            simp [hl, hq]
        · rw [if_neg (by simp [hu])]
          by_cases hl : u.1.2.val < h
          · exact wdiv u hl
          · rw [row_sum, if_neg (by omega)]
      · rw [row_sum]
        simp [hconn]
    have complete_axis (u : V) : conn a u ∧ u.1.2.val = h ↔ u = a ∨ u = b := by
      constructor
      · rintro ⟨hconn, hu⟩
        by_cases he : u = a
        · exact Or.inl he
        · right
          have hba : b ≠ a := by intro he; subst b; omega
          exact (axis_component_pair (4 * k) P a ha).unique
            ⟨he, (axis_iff u).mpr hu, hconn⟩ ⟨hba, hb, hab⟩
      · rintro (rfl | rfl)
        · exact ⟨Relation.EqvGen.refl _, ax⟩
        · exact ⟨hab, bx⟩
    have cn : ¬ conn a c := by
      intro he
      rcases (complete_axis c).mp ⟨he, cx⟩ with he | he <;> subst c <;> omega
    obtain ⟨F, hconstant, haxis⟩ := BlumTriangleRay.left_ray_potential k w wsymm
      wsupport wleft wdiv
    have prefix_value (u : V) (hu : u.1.2.val = h) : F u =
        ((if a.1.1.val ≤ u.1.1.val then 1 else 0) : ZMod 2) +
          (if b.1.1.val ≤ u.1.1.val then 1 else 0) := by
      rw [haxis u hu]
      have hd (v : V) : (∑ z : Vertex (4 * k), w v z) =
          if v = a ∨ v = b then 1 else 0 := by
        have he := divergence v
        simp only [complete_axis] at he
        convert he using 1
      simp_rw [hd]
      have hba : b ≠ a := by intro he; subst b; omega
      have term (v : V) :
          (if v.1.1.val ≤ u.1.1.val then (if v = a ∨ v = b then 1 else 0) else 0) =
            ((if v = a then (if a.1.1.val ≤ u.1.1.val then 1 else 0) else 0) : ZMod 2) +
              (if v = b then (if b.1.1.val ≤ u.1.1.val then 1 else 0) else 0) := by
        by_cases he : v = a
        · subst v
          simp [hba.symm]
        · by_cases he' : v = b
          · subst v
            simp [hba]
          · simp [he, he']
      simp_rw [term]
      rw [sum_add_distrib]
      simp
    have fc : F c = 1 := by
      rw [prefix_value c cx]
      simp [show a.1.1.val ≤ c.1.1.val by omega, show ¬ b.1.1.val ≤ c.1.1.val by omega]
    have fd : F d = 0 := by
      rw [prefix_value d dx]
      simp [show a.1.1.val ≤ d.1.1.val by omega, show b.1.1.val ≤ d.1.1.val by omega,
        CharTwo.add_self_eq_zero]
    let leftEdge : V → V → Prop := fun u v =>
      edge u v ∧ u.1.2.val ≤ h ∧ v.1.2.val ≤ h
    have transport {u v : V} (he : Relation.EqvGen leftEdge u v) :
        conn c u → F u = F v := by
      induction he with
      | rel u v he =>
        intro hcu
        have hcv := Relation.EqvGen.trans _ _ _ hcu (Relation.EqvGen.rel _ _ he.1)
        have hn (z : V) (hcz : conn c z) : ∀ t, w z t = 0 := by
          have hn : ¬ conn a z := fun hz => cn (Relation.EqvGen.trans _ _ _ hz
            (Relation.EqvGen.symm _ _ hcz))
          intro t
          simp [w, hn]
        exact hconstant u v (edge_adj he.1) he.2.1 he.2.2 (hn u hcu) (hn v hcv)
      | refl => exact fun _ => rfl
      | symm u v he ih =>
        intro hcu
        have hconn : conn v u := by
          exact Relation.EqvGen.mono (fun _ _ h => h.1) _ _
            (Relation.EqvGen.symm _ _ he)
        exact (ih (Relation.EqvGen.trans _ _ _ hcu hconn)).symm
      | trans u v z he he' ih ih' =>
        intro hcu
        have hconn : conn u v := by
          exact Relation.EqvGen.mono (fun _ _ h => h.1) _ _ he
        exact (ih hcu).trans (ih' (Relation.EqvGen.trans _ _ _ hcu hconn))
    have left_path : Relation.EqvGen leftEdge c d :=
      BlumTriangleGeometry.axis_component_left_connection k P c d hc hd hcd
    have equal := transport left_path (Relation.EqvGen.refl c)
    rw [fc, fd] at equal
    exact one_ne_zero equal
  let V := Vertex (4 * k)
  let r := reflection (4 * k)
  let h := 4 * k - 1
  have axis_iff (u : V) : r u = u ↔ u.1.2.val = h := by
    constructor
    · intro he
      have he' := congrArg (fun v : V => v.1.2.val) he
      change 2 * (4 * k - 1) - u.1.2.val = u.1.2.val at he'
      have hu := u.2
      dsimp [h]
      omega
    · intro he
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        change 2 * (4 * k - 1) - u.1.2.val = u.1.2.val
        dsimp [h] at he
        omega
  let axis : Fin (2 * k) → V := fun i =>
    ⟨(⟨2 * i.val + 1, by omega⟩, ⟨h, by dsimp [h]; omega⟩), by
      dsimp [h]
      have hi := i.isLt
      omega⟩
  have ax (i : Fin (2 * k)) : r (axis i) = axis i :=
    (axis_iff _).mpr rfl
  have axis_inj : Function.Injective axis := by
    intro i j he
    have he' := congrArg (fun u : V => u.1.1.val) he
    dsimp [axis] at he'
    apply Fin.ext
    omega
  let idx : ∀ u : V, r u = u → Fin (2 * k) := fun u hu =>
    ⟨u.1.1.val / 2, by have hr := u.1.1.isLt; omega⟩
  have axis_idx (u : V) (hu : r u = u) : axis (idx u hu) = u := by
    have hx := (axis_iff u).mp hu
    have hp := u.2.2.2
    have hr := u.1.1.isLt
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · dsimp [axis, idx]
      dsimp [h] at hx
      omega
    · exact hx.symm
  let mark : Fin k → V := fun i => axis ⟨2 * i.val, by omega⟩
  let side : V → Bool := fun u => decide (u.1.2.val < h)
  have no_axis_edge (u v : V) (hu : u.1.2.val = h) (hv : v.1.2.val = h) :
      ¬ Adj u v := by
    have hup := u.2
    have hvp := v.2
    intro he
    rcases he with he | he
    all_goals rcases he with ⟨he, hx | hx⟩ | ⟨hp, ⟨he, hx⟩ | ⟨he, hx⟩⟩
    all_goals dsimp [h] at *
    all_goals omega
  have hside (P : PerfectMatching (4 * k)) (i : Fin k) :
      side (r (P.1 (mark i))) = !(side (P.1 (mark i))) := by
    have hn : (P.1 (mark i)).1.2.val ≠ h := fun he =>
      no_axis_edge (mark i) _ rfl he (P.2 _).2.2
    have hp := (P.1 (mark i)).2
    have rx : (r (P.1 (mark i))).1.2.val = 2 * h - (P.1 (mark i)).1.2.val := rfl
    dsimp [side]
    rw [rx]
    by_cases he : (P.1 (mark i)).1.2.val < h
    · have he' : ¬ 2 * h - (P.1 (mark i)).1.2.val < h := by omega
      simp [he, he']
    · have he' : 2 * h - (P.1 (mark i)).1.2.val < h := by
        dsimp [h] at *
        omega
      simp [he, he']
  have separate (P : PerfectMatching (4 * k)) : ∀ i j, Relation.EqvGen
      (fun u z => z = P.1 u ∨ z = r (P.1 (r u))) (mark i) (mark j) → i = j := by
    let conn := Relation.EqvGen (fun u z : V => z = P.1 u ∨ z = r (P.1 (r u)))
    have pairs (i : Fin (2 * k)) := axis_component_pair (4 * k) P (axis i) (ax i)
    choose other prop using fun i => (pairs i).exists
    let mate : Fin (2 * k) → Fin (2 * k) := fun i => idx (other i) (prop i).2.1
    have mate_vertex (i : Fin (2 * k)) : axis (mate i) = other i :=
      axis_idx (other i) (prop i).2.1
    have mne (i : Fin (2 * k)) : mate i ≠ i := by
      intro he
      apply (prop i).1
      rw [← mate_vertex, he]
    have mconn (i : Fin (2 * k)) : conn (axis i) (axis (mate i)) := by
      rw [mate_vertex]
      exact (prop i).2.2
    have mm (i : Fin (2 * k)) : mate (mate i) = i := by
      apply axis_inj
      rw [mate_vertex]
      apply (pairs (mate i)).unique
      · exact prop (mate i)
      · refine ⟨?_, ax i, Relation.EqvGen.symm _ _ (mconn i)⟩
        exact fun he => mne i (axis_inj he.symm)
    let pairing : D5.S3.Combinatorics.SemiMeanderSecondDiagonal.UpperMatching k :=
      { mate := mate
        mate_mate := mm
        mate_ne := mne
        noncrossing := by
          intro i j hij hjmi hmimj
          apply axis_pairing_noncrossing k P (axis i) (axis (mate i))
            (axis j) (axis (mate j)) (ax i) (ax (mate i)) (ax j) (ax (mate j))
            (mconn i) (mconn j)
          dsimp [axis]
          omega }
    intro i j hc
    by_contra hn
    let ii : Fin (2 * k) := ⟨2 * i.val, by omega⟩
    let jj : Fin (2 * k) := ⟨2 * j.val, by omega⟩
    have hvne : axis jj ≠ axis ii := by
      intro he
      have he' := congrArg Fin.val (axis_inj he)
      dsimp [ii, jj] at he'
      exact hn (Fin.ext (by omega))
    have mate_eq : mate ii = jj := by
      apply axis_inj
      rw [mate_vertex]
      exact (pairs ii).unique (prop ii) ⟨hvne, ax jj, hc⟩
    have hp := noncrossing_mates_opposite_parity pairing ii
    change (mate ii).val % 2 ≠ ii.val % 2 at hp
    rw [mate_eq] at hp
    simp [ii, jj] at hp
  have count := reflection_choice_count (4 * k) k mark (fun i => ax _) side hside separate
  let R := {p : V → V // ∀ u, p (p u) = u ∧ p u ≠ u ∧
    BlumTriangleReduced.reducedAdj k u (p u)}
  let AllRight := {P : PerfectMatching (4 * k) // ∀ i, side (P.1 (mark i)) = false}
  have marked (u : V) (hu : u.1.1.val % 4 = 1) (hx : u.1.2.val = h) :
      ∃ i : Fin k, mark i = u := by
    let i : Fin k := ⟨u.1.1.val / 4, by have hr := u.1.1.isLt; omega⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · dsimp [mark, axis, i]
      omega
    · exact hx.symm
  have right_reduced (P : PerfectMatching (4 * k)) :
      (∀ i, side (P.1 (mark i)) = false) ↔
        ∀ u, BlumTriangleReduced.reducedAdj k u (P.1 u) := by
    constructor
    · intro hs u
      refine ⟨(P.2 u).2.2, ?_, ?_⟩
      · rintro ⟨hu, hx, hl⟩
        obtain ⟨i, rfl⟩ := marked u hu hx
        have he := hs i
        dsimp [side] at he
        simp only [decide_eq_false_iff_not] at he
        exact he hl
      · rintro ⟨hu, hx, hl⟩
        obtain ⟨i, hi⟩ := marked (P.1 u) hu hx
        have he := hs i
        rw [hi, (P.2 u).1] at he
        dsimp [side] at he
        simp only [decide_eq_false_iff_not] at he
        exact he hl
    · intro hr i
      have he := (hr (mark i)).2.1
      have hm : (mark i).1.1.val % 4 = 1 := by dsimp [mark, axis]; omega
      have hn : ¬ (P.1 (mark i)).1.2.val < h := by
        intro hl
        exact he ⟨hm, rfl, hl⟩
      simp [side, hn]
  let e : AllRight ≃ R :=
    { toFun := fun P => ⟨P.1.1, fun u =>
        ⟨(P.1.2 u).1, (P.1.2 u).2.1, (right_reduced P.1).mp P.2 u⟩⟩
      invFun := fun p =>
        ⟨⟨p.1, fun u => ⟨(p.2 u).1, (p.2 u).2.1, (p.2 u).2.2.1⟩⟩,
          (right_reduced _).mpr (fun u => (p.2 u).2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e]
  exact count

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleReduction
