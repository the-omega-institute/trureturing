/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage4
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage4
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Connectivity classification of the three prefix families. -/

import D5.S3.Combinatorics.SemiMeanderSecondDiagonal.Stage3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

open Classical

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_of_B_consecutive {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
    (hc : 2 ≤ q.val.1) (hq : q.val.2 = q.val.1 + 1) :
    ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j := by
  have hpu (i : Fin n) :
      i ∈ (unmatchedPositions p) ↔ 2 ≤ i.val ∧ i.val ≤ n - 3 := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff p)]
    unfold secondOpen
    split_ifs <;>
      have := i.isLt <;> have := p.property.2.1 <;> omega
  let zero : Fin n := ⟨0, by have := p.property.2.2.2; omega⟩
  let last : Fin n := ⟨n - 1, by have := p.property.2.2.2; omega⟩
  have hsym {i j : Fin n}
      (h : Relation.ReflTransGen ((joinedEdge p) q) i j) :
      Relation.ReflTransGen ((joinedEdge p) q) j i := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail mid fin hab hbc ih =>
      have hcb : (joinedEdge p) q fin mid := by
        rcases hbc with hc | hc | hc | hc
        · exact Or.inl ((halfCut_symmetric p) _ _ hc)
        · exact Or.inr (Or.inl ((halfCut_symmetric q) _ _ hc))
        · exact Or.inr (Or.inr (Or.inr hc))
        · exact Or.inr (Or.inr (Or.inl hc))
      exact (Relation.ReflTransGen.single hcb).trans ih
  have hfront : ∀ k : ℕ, ∀ x : Fin n, x.val = k → x.val < q.val.1 →
      Relation.ReflTransGen ((joinedEdge p) q) x zero := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxk hxc
      by_cases hzero : x.val = 0
      · have hx : x = zero := Fin.ext (by dsimp [zero]; omega)
        subst x
        exact Relation.ReflTransGen.refl
      by_cases hone : x.val = 1
      · have hcut : (halfCut p) x = some zero := by
          have h := (halfCut_first_reverse p)
          have hx : x = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
            Fin.ext (by change x.val = p.val.1; omega)
          rw [hx]
          have ht : (⟨p.val.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _)
              (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) = zero :=
            Fin.ext (by dsimp [zero]; omega)
          simpa [ht] using h
        exact Relation.ReflTransGen.single (Or.inl hcut)
      have hx2 : 2 ≤ x.val := by omega
      let y : Fin n := ⟨x.val - 2, by have := x.isLt; omega⟩
      have hxy : (joinedEdge p) q x y := by
        have hpx : x ∈ (unmatchedPositions p) :=
          (hpu x).2 (by
            have := q.property.2.2.2
            constructor <;> omega)
        have hr := (rankJoin_B_consecutive p) q hp1 hp2 hc hq ⟨x, hpx⟩
        have hy : ((rankJoin p) q ⟨x, hpx⟩).1 = y := by
          apply Fin.ext
          rw [hr]
          dsimp [y]
          simp [hxc]
        exact Or.inr (Or.inr (Or.inl ⟨hpx, hy⟩))
      exact (Relation.ReflTransGen.single hxy).trans
        (ih y.val (by dsimp [y]; omega) y rfl (by dsimp [y]; omega))
  have hback : ∀ k : ℕ, ∀ x : Fin n, n - 1 - x.val = k → q.val.1 ≤ x.val →
      Relation.ReflTransGen ((joinedEdge p) q) x last := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxk hcx
      have hxbound := x.isLt
      by_cases hlast : x.val = n - 1
      · have hx : x = last := Fin.ext (by dsimp [last]; omega)
        subst x
        exact Relation.ReflTransGen.refl
      by_cases hpenult : x.val = n - 2
      · have hcut : (halfCut p) x = some last := by
          have h := (halfCut_second_pair p)
          have hsep : p.val.2 ≠ p.val.1 + 1 := by omega
          have hx : x = (⟨(secondOpen p), by
              unfold secondOpen
              split_ifs
              · exact lt_of_le_of_lt (Nat.sub_le _ _)
                  (lt_trans p.property.2.2.1 p.property.2.2.2)
              · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ : Fin n) := by
            apply Fin.ext
            change x.val = (secondOpen p)
            unfold secondOpen
            rw [if_neg hsep, hp2]
            omega
          rw [hx]
          have ht : (⟨p.val.2, p.property.2.2.2⟩ : Fin n) = last :=
            Fin.ext (by dsimp [last]; omega)
          simpa [ht] using h
        exact Relation.ReflTransGen.single (Or.inl hcut)
      have hxle : x.val ≤ n - 3 := by omega
      let y : Fin n := ⟨x.val + 2, by omega⟩
      have hxy : (joinedEdge p) q x y := by
        have hpx : x ∈ (unmatchedPositions p) :=
          (hpu x).2 (by constructor <;> omega)
        have hr := (rankJoin_B_consecutive p) q hp1 hp2 hc hq ⟨x, hpx⟩
        have hy : ((rankJoin p) q ⟨x, hpx⟩).1 = y := by
          apply Fin.ext
          rw [hr]
          dsimp [y]
          simp [show ¬x.val < q.val.1 by omega]
        exact Or.inr (Or.inr (Or.inl ⟨hpx, hy⟩))
      exact (Relation.ReflTransGen.single hxy).trans
        (ih (n - 1 - y.val) (by dsimp [y]; omega) y rfl (by dsimp [y]; omega))
  let a : Fin n := ⟨q.val.1 - 2, by have := q.property.2.2.2; omega⟩
  let b : Fin n := ⟨q.val.1 + 1, by simpa [hq] using q.property.2.2.2⟩
  have hab : (joinedEdge p) q a b := by
    have h := (halfCut_second_pair q)
    have ha : a = (⟨(secondOpen q), by
        unfold secondOpen
        rw [if_pos (by omega)]
        have := q.property.2.2.2
        omega⟩ : Fin n) := by
      apply Fin.ext
      simp [a, secondOpen, hq]
    rw [ha]
    refine Or.inr (Or.inl ?_)
    have ht : (⟨q.val.2, q.property.2.2.2⟩ : Fin n) = b :=
      Fin.ext (by dsimp [b]; omega)
    simpa [ht] using h
  have hbridge : Relation.ReflTransGen ((joinedEdge p) q) zero last :=
    ((hsym (hfront a.val a rfl (by dsimp [a]; omega))).trans
      (Relation.ReflTransGen.single hab)).trans
      (by
        apply hback (n - 1 - b.val) b rfl
        dsimp [b]
        omega)
  have htozero (x : Fin n) :
      Relation.ReflTransGen ((joinedEdge p) q) x zero := by
    by_cases hxc : x.val < q.val.1
    · exact hfront x.val x rfl hxc
    · exact (hback (n - 1 - x.val) x rfl (by omega)).trans (hsym hbridge)
  intro i j
  exact (htozero i).trans (hsym (htozero j))

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem not_connected_of_A_early {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
    (hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1)
    (hearly : q.val.1 + 2 ≤ p.val.2) :
    ¬ (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
  have hn : 5 ≤ n := by have := p.property.2.1; omega
  have hsep : q.val.1 + 2 ≤ q.val.2 := by omega
  have hqfirst := q.property.1
  have hqbound := q.property.2.2.2
  have hpfar : q.val.1 < (secondOpen p) := by
    unfold secondOpen
    have := p.property.2.1
    rw [if_neg (by omega)]
    omega
  have hpreimage (i j : Fin n) (hi : i.val ≤ q.val.1)
      (hqi : i ∈ (unmatchedPositions q)) (hpj : j ∈ (unmatchedPositions p))
      (hr : ((rankJoin p) q ⟨j, hpj⟩).1 = i) : j.val ≤ q.val.1 := by
    have hqparams := ((halfCut_eq_none_iff q) i).1 (Finset.mem_filter.mp hqi).2
    have hi2 : i.val ≤ q.val.1 - 2 := by omega
    by_contra hgt
    have hc2 : 2 ≤ q.val.1 := by have := i.isLt; omega
    let g : Fin (q.val.1 - 1) → Fin (q.val.1 - 2) := fun k => by
      let x : Fin n := ⟨k.val + 2, by have := k.isLt; omega⟩
      have hxi : x ∈ (unmatchedPositions p) := by
        simp only [unmatchedPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [(halfCut_eq_none_iff p)]
        dsimp [x]
        rw [hp1]
        have := k.isLt
        omega
      have hxlt : ((rankJoin p) q ⟨x, hxi⟩).1.val < i.val := by
        have ho := ((rankJoin p) q).strictMono
          (show (⟨x, hxi⟩ : (unmatchedPositions p)) < ⟨j, hpj⟩ by
            change x.val < j.val
            dsimp [x]
            have := k.isLt
            omega)
        change ((rankJoin p) q ⟨x, hxi⟩).1.val <
          ((rankJoin p) q ⟨j, hpj⟩).1.val at ho
        rwa [hr] at ho
      exact ⟨((rankJoin p) q ⟨x, hxi⟩).1.val, by omega⟩
    have hg : Function.Injective g := by
      intro a b hab
      have hv := congrArg Fin.val hab
      dsimp [g] at hv
      have hz := ((rankJoin p) q).injective
        (Subtype.ext (Fin.ext hv))
      have hx := congrArg (fun z : (unmatchedPositions p) => z.1.val) hz
      dsimp at hx
      exact Fin.ext (by omega)
    have hc := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at hc
    omega
  have hclosed (i j : Fin n) (hi : i.val ≤ q.val.1)
      (hij : (joinedEdge p) q i j) : j.val ≤ q.val.1 := by
    rcases hij with hcut | hcut | ⟨hiP, hr⟩ | ⟨hjP, hr⟩
    · unfold halfCut at hcut
      by_cases hfix : (halfMate p) i.val = i.val
      · simp [hfix] at hcut
      · simp only [if_neg hfix] at hcut
        have hv := congrArg Fin.val (Option.some.inj hcut)
        change (halfMate p) i.val = j.val at hv
        unfold halfMate at hv
        rw [hp1] at hv
        split_ifs at hv <;> omega
    · exact (q_edge_B_closed q) hsep i hi hcut
    · rw [← hr]
      exact (rankJoin_B_closed_bound p) q hp1 hsep i hi hiP
    · exact hpreimage i j hi (by rw [← hr]; exact ((rankJoin p) q ⟨j, hjP⟩).2)
        hjP hr
  intro hconn
  let zero : Fin n := ⟨0, by omega⟩
  let outside : Fin n := ⟨q.val.1 + 1, by omega⟩
  have hpath := hconn zero outside
  have hb : zero.val ≤ q.val.1 → outside.val ≤ q.val.1 :=
    Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => a.val ≤ q.val.1 → outside.val ≤ q.val.1) hpath
      (fun ha => ha) (fun hab _ ih ha => ih (hclosed _ _ ha hab))
  have := hb (by dsimp [zero]; omega)
  dsimp [outside] at this
  omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rankJoin_A {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
    (_hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1)
    (hcover : p.val.2 - 1 ≤ q.val.1) (x : (unmatchedPositions p)) :
    ((rankJoin p) q x).1.val =
      if x.1.val < p.val.2 then x.1.val - 2
      else if q.val.1 + 2 < x.1.val ∧ q.val.1 + 2 ≤ q.val.2
        then x.1.val - 2 else x.1.val - 4 := by
  have hb := p.property.2.1
  have hc := q.property.2.2.1
  have hn := q.property.2.2.2
  have hpsep : p.val.2 ≠ p.val.1 + 1 := by omega
  have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔
      2 ≤ i.val ∧ (i.val + 2 ≤ p.val.2 ∨ p.val.2 < i.val) := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff p)]
    rw [show (secondOpen p) = p.val.2 - 1 by
      simp only [secondOpen, if_neg hpsep], hp1]
    omega
  have hqu (i : Fin n) : i ∈ (unmatchedPositions q) ↔
      if q.val.1 + 1 = q.val.2 then i.val + 4 < n
      else (i.val + 2 ≤ q.val.1 ∨ q.val.1 < i.val) ∧ i.val + 2 < n := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff q)]
    unfold secondOpen
    have := i.isLt
    split_ifs <;> omega
  let f : (unmatchedPositions p) → (unmatchedPositions q) := fun z =>
    ⟨⟨if z.1.val < p.val.2 then z.1.val - 2
       else if q.val.1 + 2 < z.1.val ∧ q.val.1 + 2 ≤ q.val.2
         then z.1.val - 2 else z.1.val - 4, by
      have hz := (hpu z.1).1 z.2
      have := z.1.isLt
      split_ifs <;> omega⟩, by
      rw [hqu]
      have hz := (hpu z.1).1 z.2
      have := z.1.isLt
      change (if q.val.1 + 1 = q.val.2 then _ else _)
      dsimp only
      split_ifs <;> omega⟩
  have hf : StrictMono f := by
    intro z w hzw
    have hz := (hpu z.1).1 z.2
    have hw := (hpu w.1).1 w.2
    change z.1.val < w.1.val at hzw
    change (if z.1.val < p.val.2 then z.1.val - 2 else
      if q.val.1 + 2 < z.1.val ∧ q.val.1 + 2 ≤ q.val.2 then z.1.val - 2
      else z.1.val - 4) <
      (if w.1.val < p.val.2 then w.1.val - 2 else
      if q.val.1 + 2 < w.1.val ∧ q.val.1 + 2 ≤ q.val.2 then w.1.val - 2
      else w.1.val - 4)
    split_ifs <;> omega
  have hs : Function.Surjective f := by
    intro y
    have hy := (hqu y.1).1 y.2
    let z : Fin n := ⟨if y.1.val + 3 < p.val.2 then y.1.val + 2
      else if q.val.1 + 1 = q.val.2 ∨ y.1.val + 2 ≤ q.val.1
        then y.1.val + 4 else y.1.val + 2, by
      have := y.1.isLt
      split_ifs <;> split_ifs at hy <;> omega⟩
    have hz : z ∈ (unmatchedPositions p) := by
      rw [hpu]
      dsimp [z]
      have hq := q.property.2.2.1
      have hq2' := hq2
      split_ifs <;> split_ifs at hy <;> omega
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    change (if z.val < p.val.2 then z.val - 2 else
      if q.val.1 + 2 < z.val ∧ q.val.1 + 2 ≤ q.val.2 then z.val - 2
      else z.val - 4) = y.1.val
    dsimp [z]
    split_ifs <;> split_ifs at hy <;> omega
  let e := hf.orderIsoOfSurjective f hs
  have he : e = (rankJoin p) q := by
    have hid := StrictMono.eq_id (e.trans ((rankJoin p) q).symm).strictMono
    apply OrderIso.ext
    funext z
    have hz := congrArg ((rankJoin p) q) (congrFun hid z)
    simpa [OrderIso.trans_apply] using hz
  have hfx : (e x).1.val =
      if x.1.val < p.val.2 then x.1.val - 2
      else if q.val.1 + 2 < x.1.val ∧ q.val.1 + 2 ≤ q.val.2
        then x.1.val - 2 else x.1.val - 4 := rfl
  rwa [he] at hfx

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def aTerminal {n : ℕ} (p q : TwoDownPrefix n) (x : ℕ) : ℕ :=
  if x + 2 ≤ p.val.2 then x % 2 else
    let y := if q.val.1 + 2 < x ∧ q.val.1 + 2 ≤ q.val.2
      then q.val.1 + 1 + (x - (q.val.1 + 1)) % 2 else x
    let r := (y + 3 - p.val.2) % 4
    if r < 2 then (p.val.2 - 3 + r) % 2 else p.val.2 - 3 + r

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem A_terminal_paths {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
    (hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1)
    (hcover : p.val.2 - 1 ≤ q.val.1) :
    (∀ x : (unmatchedPositions p),
      (aTerminal p) q ((rankJoin p) q x).1.val = (aTerminal p) q x.1.val) ∧
    (∀ x : Fin n, ∃ z : Fin n,
      z.val = (aTerminal p) q x.val ∧
      (z.val = 0 ∨ z.val = 1 ∨ z.val = p.val.2 - 1 ∨ z.val = p.val.2) ∧
      Relation.ReflTransGen ((joinedEdge p) q) x z) := by
  have hb := p.property.2.1
  have hc := q.property.2.2.1
  have hn := q.property.2.2.2
  have hpsep : p.val.2 ≠ p.val.1 + 1 := by omega
  have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔
      2 ≤ i.val ∧ (i.val + 2 ≤ p.val.2 ∨ p.val.2 < i.val) := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff p)]
    rw [show (secondOpen p) = p.val.2 - 1 by
      simp only [secondOpen, if_neg hpsep], hp1]
    omega
  have hstep (x : (unmatchedPositions p)) :
      (aTerminal p) q ((rankJoin p) q x).1.val = (aTerminal p) q x.1.val := by
    rw [(rankJoin_A p) q hp1 hpbound hq2 hcover x]
    have hx := (hpu x.1).1 x.2
    have := x.1.isLt
    unfold aTerminal
    dsimp only
    split_ifs <;> omega
  refine ⟨hstep, ?_⟩
  have hreach : ∀ k : ℕ, ∀ x : Fin n, x.val = k → ∃ z : Fin n,
      z.val = (aTerminal p) q x.val ∧
      (z.val = 0 ∨ z.val = 1 ∨ z.val = p.val.2 - 1 ∨ z.val = p.val.2) ∧
      Relation.ReflTransGen ((joinedEdge p) q) x z := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxk
      by_cases hpaired : x.val = 0 ∨ x.val = 1 ∨
          x.val = p.val.2 - 1 ∨ x.val = p.val.2
      · refine ⟨x, ?_, hpaired, Relation.ReflTransGen.refl⟩
        unfold aTerminal
        dsimp only
        split_ifs <;> omega
      · have hx : x ∈ (unmatchedPositions p) := (hpu x).2 (by omega)
        let y : Fin n := ((rankJoin p) q ⟨x, hx⟩).1
        have hlt : y.val < k := by
          dsimp [y]
          rw [(rankJoin_A p) q hp1 hpbound hq2 hcover]
          dsimp only
          have hu := (hpu x).1 hx
          split_ifs <;> omega
        obtain ⟨z, hz, hpz, hyz⟩ := ih y.val hlt y rfl
        refine ⟨z, hz.trans (hstep ⟨x, hx⟩), hpz, ?_⟩
        have hxy : (joinedEdge p) q x y := Or.inr (Or.inr (Or.inl ⟨hx, rfl⟩))
        exact (Relation.ReflTransGen.single hxy).trans hyz
  intro x
  exact hreach x.val x rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_iff_A {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
    (hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1) :
    (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
      p.val.2 - 1 ≤ q.val.1 ∧ q.val.1 % 2 ≠ p.val.2 % 2 := by
  have hb := p.property.2.1
  have hc := q.property.2.2.1
  have hn := q.property.2.2.2
  have hpsep : p.val.2 ≠ p.val.1 + 1 := by omega
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let back : Fin n := ⟨p.val.2, p.property.2.2.2⟩
  let before : Fin n := ⟨p.val.2 - 1, by have := p.property.2.2.2; omega⟩
  have hsym {i j : Fin n}
      (h : Relation.ReflTransGen ((joinedEdge p) q) i j) :
      Relation.ReflTransGen ((joinedEdge p) q) j i := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail mid fin hab hbc ih =>
      have hcb : (joinedEdge p) q fin mid := by
        rcases hbc with hc | hc | hc | hc
        · exact Or.inl ((halfCut_symmetric p) _ _ hc)
        · exact Or.inr (Or.inl ((halfCut_symmetric q) _ _ hc))
        · exact Or.inr (Or.inr (Or.inr hc))
        · exact Or.inr (Or.inr (Or.inl hc))
      exact (Relation.ReflTransGen.single hcb).trans ih
  constructor
  · intro hconn
    have hcover : p.val.2 - 1 ≤ q.val.1 := by
      by_contra h
      exact (not_connected_of_A_early p) q hp1 hpbound hq2 (by omega) hconn
    refine ⟨hcover, ?_⟩
    intro heven
    have ht := (A_terminal_paths p) q hp1 hpbound hq2 hcover
    have hpcolor (i j : Fin n) (hcut : (halfCut p) i = some j) :
        (aTerminal p) q i.val + 2 ≤ p.val.2 ↔
          (aTerminal p) q j.val + 2 ≤ p.val.2 := by
      unfold halfCut at hcut
      by_cases hfix : (halfMate p) i.val = i.val
      · simp [hfix] at hcut
      · simp only [if_neg hfix] at hcut
        have hv := congrArg Fin.val (Option.some.inj hcut)
        change (halfMate p) i.val = j.val at hv
        unfold halfMate at hv
        rw [show (secondOpen p) = p.val.2 - 1 by
          simp only [secondOpen, if_neg hpsep], hp1] at hv
        unfold aTerminal
        dsimp only
        have := i.isLt
        have := j.isLt
        split_ifs at hv <;> split_ifs <;> omega
    have hqcolor (i j : Fin n) (hcut : (halfCut q) i = some j) :
        (aTerminal p) q i.val + 2 ≤ p.val.2 ↔
          (aTerminal p) q j.val + 2 ≤ p.val.2 := by
      unfold halfCut at hcut
      by_cases hfix : (halfMate q) i.val = i.val
      · simp [hfix] at hcut
      · simp only [if_neg hfix] at hcut
        have hv := congrArg Fin.val (Option.some.inj hcut)
        change (halfMate q) i.val = j.val at hv
        unfold halfMate secondOpen at hv
        unfold aTerminal
        dsimp only
        have := i.isLt
        have := j.isLt
        split_ifs at hv <;> split_ifs <;> omega
    have hclosed (i j : Fin n) (hi : (aTerminal p) q i.val + 2 ≤ p.val.2)
        (hij : (joinedEdge p) q i j) : (aTerminal p) q j.val + 2 ≤ p.val.2 := by
      rcases hij with hcut | hcut | ⟨hiP, hr⟩ | ⟨hjP, hr⟩
      · exact (hpcolor i j hcut).mp hi
      · exact (hqcolor i j hcut).mp hi
      · rw [← hr, ht.1 ⟨i, hiP⟩]
        exact hi
      · have hm := ht.1 ⟨j, hjP⟩
        rw [hr] at hm
        rwa [← hm]
    have hpath := hconn zero back
    have hstay : (aTerminal p) q zero.val + 2 ≤ p.val.2 →
        (aTerminal p) q back.val + 2 ≤ p.val.2 :=
      Relation.ReflTransGen.head_induction_on
        (motive := fun a _ => (aTerminal p) q a.val + 2 ≤ p.val.2 →
          (aTerminal p) q back.val + 2 ≤ p.val.2) hpath
        (fun ha => ha) (fun hab _ ih ha => ih (hclosed _ _ ha hab))
    have hz : (aTerminal p) q zero.val = 0 := by
      simp [zero, aTerminal, show 2 ≤ p.val.2 by omega]
    have hback : (aTerminal p) q back.val = p.val.2 := by
      unfold aTerminal
      dsimp [back]
      split_ifs <;> omega
    have hout := hstay (by rw [hz]; omega)
    rw [hback] at hout
    omega
  · rintro ⟨hcover, hodd⟩
    have ht := (A_terminal_paths p) q hp1 hpbound hq2 hcover
    have hfront : Relation.ReflTransGen ((joinedEdge p) q) one zero := by
      have h := (halfCut_first_reverse p)
      have he1 : (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) = one :=
        Fin.ext (by dsimp [one]; omega)
      have he0 : (⟨p.val.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) = zero :=
        Fin.ext (by dsimp [zero]; omega)
      exact Relation.ReflTransGen.single (Or.inl (by simpa [he1, he0] using h))
    have hback : Relation.ReflTransGen ((joinedEdge p) q) before back := by
      have h := (halfCut_second_pair p)
      have he : (⟨(secondOpen p), by
          unfold secondOpen
          split_ifs
          · exact lt_of_le_of_lt (Nat.sub_le _ _)
              (lt_trans p.property.2.2.1 p.property.2.2.2)
          · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ : Fin n) = before := by
        apply Fin.ext
        simp only [secondOpen, if_neg hpsep]
        rfl
      exact Relation.ReflTransGen.single (Or.inl (by simpa [he, back] using h))
    have hroots (x : Fin n) :
        ((aTerminal p) q x.val ≤ 1 → Relation.ReflTransGen ((joinedEdge p) q) x zero) ∧
        (p.val.2 - 1 ≤ (aTerminal p) q x.val →
          Relation.ReflTransGen ((joinedEdge p) q) x back) := by
      obtain ⟨z, hz, hpz, hxz⟩ := ht.2 x
      constructor
      · intro hsmall
        have hzsmall : z.val = 0 ∨ z.val = 1 := by omega
        rcases hzsmall with hz0 | hz1
        · have he : z = zero := Fin.ext (by dsimp [zero]; omega)
          simpa [he] using hxz
        · have he : z = one := Fin.ext (by dsimp [one]; omega)
          exact hxz.trans (by simpa [he] using hfront)
      · intro hlarge
        have hzlarge : z.val = p.val.2 - 1 ∨ z.val = p.val.2 := by omega
        rcases hzlarge with hzbefore | hzback
        · have he : z = before := Fin.ext (by dsimp [before]; omega)
          exact hxz.trans (by simpa [he] using hback)
        · have he : z = back := Fin.ext (by dsimp [back]; omega)
          simpa [he] using hxz
    let a : Fin n := ⟨q.val.1 - 1, by have := q.property.1; omega⟩
    let b : Fin n := ⟨q.val.1, by omega⟩
    have hab : Relation.ReflTransGen ((joinedEdge p) q) a b := by
      have h := (halfCut_first_pair q)
      exact Relation.ReflTransGen.single (Or.inr (Or.inl (by simpa [a, b] using h)))
    have hcross :
        ((aTerminal p) q a.val ≤ 1 ∧ p.val.2 - 1 ≤ (aTerminal p) q b.val) ∨
        (p.val.2 - 1 ≤ (aTerminal p) q a.val ∧ (aTerminal p) q b.val ≤ 1) := by
      unfold aTerminal
      dsimp [a, b]
      split_ifs <;> omega
    have hbridge : Relation.ReflTransGen ((joinedEdge p) q) zero back := by
      rcases hcross with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · exact ((hsym ((hroots a).1 ha)).trans hab).trans ((hroots b).2 hb')
      · exact ((hsym ((hroots b).1 hb')).trans (hsym hab)).trans ((hroots a).2 ha)
    have htozero (x : Fin n) : Relation.ReflTransGen ((joinedEdge p) q) x zero := by
      by_cases hsmall : (aTerminal p) q x.val ≤ 1
      · exact (hroots x).1 hsmall
      · obtain ⟨z, hz, hpz, _⟩ := ht.2 x
        have hlarge : p.val.2 - 1 ≤ (aTerminal p) q x.val := by omega
        exact ((hroots x).2 hlarge).trans (hsym hbridge)
    intro i j
    exact (htozero i).trans (hsym (htozero j))

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rankJoin_C {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
    (hc : 2 ≤ q.val.1) (hq2 : q.val.2 = n - 1)
    (x : (unmatchedPositions p)) :
    ((rankJoin p) q x).1.val =
      if x.1.val ≤ q.val.1 + 2 then x.1.val - 4 else x.1.val - 2 := by
  have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔ 4 ≤ i.val := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff p)]
    have ho : (secondOpen p) = 0 := by
      simp [secondOpen, hp1, hp2]
    rw [ho, hp1, hp2]
    omega
  have hqu (i : Fin n) : i ∈ (unmatchedPositions q) ↔
      if q.val.1 + 1 = q.val.2 then i.val + 4 < n
      else (i.val + 2 ≤ q.val.1 ∨ q.val.1 < i.val) ∧ i.val + 2 < n := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff q)]
    unfold secondOpen
    have := i.isLt
    have := q.property.2.2.2
    split_ifs <;> omega
  let f : (unmatchedPositions p) → (unmatchedPositions q) := fun z =>
    ⟨⟨if z.1.val ≤ q.val.1 + 2 then z.1.val - 4 else z.1.val - 2, by
      have hz := (hpu z.1).1 z.2
      have := z.1.isLt
      split_ifs <;> omega⟩, by
      rw [hqu]
      have hz := (hpu z.1).1 z.2
      have := z.1.isLt
      have := q.property.2.2.2
      change (if q.val.1 + 1 = q.val.2 then _ else _)
      dsimp only
      split_ifs <;> omega⟩
  have hf : StrictMono f := by
    intro z w hzw
    change z.1.val < w.1.val at hzw
    change (if z.1.val ≤ q.val.1 + 2 then z.1.val - 4 else z.1.val - 2) <
      (if w.1.val ≤ q.val.1 + 2 then w.1.val - 4 else w.1.val - 2)
    have hz := (hpu z.1).1 z.2
    have hw := (hpu w.1).1 w.2
    split_ifs <;> omega
  have hs : Function.Surjective f := by
    intro y
    have hy := (hqu y.1).1 y.2
    let z : Fin n := ⟨if y.1.val + 2 ≤ q.val.1 then y.1.val + 4
      else y.1.val + 2, by
      have := y.1.isLt
      have := q.property.2.2.2
      have hq := q.property.2.2.1
      have hq2' := hq2
      split_ifs <;> split_ifs at hy <;> omega⟩
    have hz : z ∈ (unmatchedPositions p) := by
      rw [hpu]
      dsimp [z]
      split_ifs <;> split_ifs at hy <;> omega
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    change (if z.val ≤ q.val.1 + 2 then z.val - 4 else z.val - 2) = y.1.val
    dsimp [z]
    have hq := q.property.2.2.1
    have hq2' := hq2
    split_ifs <;> split_ifs at hy <;> omega
  let e := hf.orderIsoOfSurjective f hs
  have he : e = (rankJoin p) q := by
    have hid := StrictMono.eq_id (e.trans ((rankJoin p) q).symm).strictMono
    apply OrderIso.ext
    funext z
    have hz := congrArg ((rankJoin p) q) (congrFun hid z)
    simpa [OrderIso.trans_apply] using hz
  have hfx : (e x).1.val =
      if x.1.val ≤ q.val.1 + 2 then x.1.val - 4 else x.1.val - 2 := rfl
  rwa [he] at hfx

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def cTerminal {n : ℕ} (q : TwoDownPrefix n) (x : ℕ) : ℕ :=
  if x ≤ q.val.1 + 2 then x % 4
  else if (x - (q.val.1 + 3)) % 2 = 0 then (q.val.1 + 1) % 4
  else (q.val.1 + 2) % 4

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem C_terminal_paths {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
    (hc : 2 ≤ q.val.1) (hq2 : q.val.2 = n - 1) :
    (∀ x : (unmatchedPositions p),
      (cTerminal q) ((rankJoin p) q x).1.val = (cTerminal q) x.1.val) ∧
    (∀ x : Fin n, ∃ z : Fin n,
      z.val = (cTerminal q) x.val ∧ z.val < 4 ∧
      Relation.ReflTransGen ((joinedEdge p) q) x z) := by
  have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔ 4 ≤ i.val := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff p)]
    have ho : (secondOpen p) = 0 := by
      simp [secondOpen, hp1, hp2]
    rw [ho, hp1, hp2]
    omega
  have hstep (x : (unmatchedPositions p)) :
      (cTerminal q) ((rankJoin p) q x).1.val = (cTerminal q) x.1.val := by
    rw [(rankJoin_C p) q hp1 hp2 hc hq2 x]
    have hx := (hpu x.1).1 x.2
    have := x.1.isLt
    unfold cTerminal
    split_ifs <;> omega
  refine ⟨hstep, ?_⟩
  have hreach : ∀ k : ℕ, ∀ x : Fin n, x.val = k →
      ∃ z : Fin n, z.val = (cTerminal q) x.val ∧ z.val < 4 ∧
        Relation.ReflTransGen ((joinedEdge p) q) x z := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxk
      by_cases hroot : x.val < 4
      · refine ⟨x, ?_, hroot, Relation.ReflTransGen.refl⟩
        simp [cTerminal,
          show x.val ≤ q.val.1 + 2 by omega, Nat.mod_eq_of_lt hroot]
      · have hx : x ∈ (unmatchedPositions p) := (hpu x).2 (by omega)
        let y : Fin n := ((rankJoin p) q ⟨x, hx⟩).1
        have hlt : y.val < k := by
          dsimp [y]
          rw [(rankJoin_C p) q hp1 hp2 hc hq2 ⟨x, hx⟩]
          change (if x.val ≤ q.val.1 + 2 then x.val - 4 else x.val - 2) < k
          split_ifs <;> omega
        obtain ⟨z, hz, hsmall, hyz⟩ := ih y.val hlt y rfl
        refine ⟨z, hz.trans (hstep ⟨x, hx⟩), hsmall, ?_⟩
        have hxy : (joinedEdge p) q x y := Or.inr (Or.inr (Or.inl ⟨hx, rfl⟩))
        exact (Relation.ReflTransGen.single hxy).trans hyz
  intro x
  exact hreach x.val x rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem joinedEdge_swap {n : ℕ}
    (p q : TwoDownPrefix n) (i j : Fin n)
    (h : (joinedEdge q) p i j) : (joinedEdge p) q i j := by
  rcases h with h | h | ⟨hi, h⟩ | ⟨hj, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · have hj : j ∈ (unmatchedPositions p) := by
      rw [← h]
      exact ((rankJoin q) p ⟨i, hi⟩).2
    right; right; right
    refine ⟨hj, ?_⟩
    have hz : ((rankJoin q) p ⟨i, hi⟩) = ⟨j, hj⟩ := Subtype.ext h
    rw [← (show ((rankJoin q) p).symm = (rankJoin p) q by
      simp [rankJoin, OrderIso.symm_trans]),
      ← hz, OrderIso.symm_apply_apply]
  · have hi : i ∈ (unmatchedPositions p) := by
      rw [← h]
      exact ((rankJoin q) p ⟨j, hj⟩).2
    right; right; left
    refine ⟨hi, ?_⟩
    have hz : ((rankJoin q) p ⟨j, hj⟩) = ⟨i, hi⟩ := Subtype.ext h
    rw [← (show ((rankJoin q) p).symm = (rankJoin p) q by
      simp [rankJoin, OrderIso.symm_trans]),
      ← hz, OrderIso.symm_apply_apply]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem C_color_p_edge {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
    (hc : 2 ≤ q.val.1) (i j : Fin n)
    (hcut : (halfCut p) i = some j) :
    ((cTerminal q) i.val = 0 ∨ (cTerminal q) i.val = 3) ↔
      ((cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3) := by
  unfold halfCut at hcut
  by_cases hfix : (halfMate p) i.val = i.val
  · simp [hfix] at hcut
  · simp only [if_neg hfix] at hcut
    have hv := congrArg Fin.val (Option.some.inj hcut)
    change (halfMate p) i.val = j.val at hv
    have ho : (secondOpen p) = 0 := by
      simp [secondOpen, hp1, hp2]
    unfold halfMate at hv
    rw [hp1, hp2, ho] at hv
    have hroot (x : Fin n) (hx : x.val < 4) : (cTerminal q) x.val = x.val := by
      simp [cTerminal,
        show x.val ≤ q.val.1 + 2 by omega, Nat.mod_eq_of_lt hx]
    have hindex : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
      by_contra h
      have hfixed := ((halfMate_fixed_iff p) i.val).2 (by
        rw [hp1, hp2, ho]
        omega)
      exact hfix hfixed
    have hpair :
        (i.val = 0 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 0) ∨
        (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) := by
      split_ifs at hv <;> omega
    have hi : i.val < 4 := by omega
    have hj : j.val < 4 := by omega
    rw [hroot i hi, hroot j hj]
    rcases hpair with h | h | h | h <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem C_color_q_edge_even {n : ℕ}
    (q : TwoDownPrefix n) (hc : 2 ≤ q.val.1)
    (hq2 : q.val.2 = n - 1) (heven : q.val.1 % 2 = 0)
    (i j : Fin n) (hcut : (halfCut q) i = some j) :
    ((cTerminal q) i.val = 0 ∨ (cTerminal q) i.val = 3) ↔
      ((cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3) := by
  unfold halfCut at hcut
  by_cases hfix : (halfMate q) i.val = i.val
  · simp [hfix] at hcut
  · simp only [if_neg hfix] at hcut
    have hv := congrArg Fin.val (Option.some.inj hcut)
    change (halfMate q) i.val = j.val at hv
    have hindex : i.val = q.val.1 - 1 ∨ i.val = q.val.1 ∨
        i.val = (secondOpen q) ∨ i.val = q.val.2 := by
      by_contra h
      exact hfix (((halfMate_fixed_iff q) i.val).2 (by omega))
    unfold halfMate secondOpen at hv
    unfold secondOpen at hindex
    have hb := q.property.2.2.2
    have ho := q.property.2.2.1
    have hq := hq2
    unfold cTerminal
    split_ifs at hv <;> split_ifs <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_iff_C {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
    (hq2 : q.val.2 = n - 1) :
    (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
      q.val.1 % 2 = 1 := by
  by_cases hc1 : q.val.1 = 1
  · have hB : ∀ i j : Fin n,
        Relation.ReflTransGen ((joinedEdge q) p) i j :=
      (connected_of_B_consecutive q) p hc1 hq2 (by omega) (by omega)
    have hinc : (joinedEdge q) p ≤ (joinedEdge p) q := by
      intro i j h
      exact (joinedEdge_swap p) q i j h
    constructor
    · intro _
      omega
    · intro _ i j
      exact Relation.ReflTransGen.mono hinc i j (hB i j)
  have hc : 2 ≤ q.val.1 := by have := q.property.1; omega
  have ht := (C_terminal_paths p) q hp1 hp2 hc hq2
  have hn : 4 ≤ n := by have := p.property.2.2.2; omega
  let r0 : Fin n := ⟨0, by omega⟩
  let r1 : Fin n := ⟨1, by omega⟩
  let r2 : Fin n := ⟨2, by omega⟩
  let r3 : Fin n := ⟨3, by omega⟩
  have hsym {i j : Fin n}
      (h : Relation.ReflTransGen ((joinedEdge p) q) i j) :
      Relation.ReflTransGen ((joinedEdge p) q) j i := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail mid fin hab hbc ih =>
      have hcb : (joinedEdge p) q fin mid := by
        rcases hbc with hc | hc | hc | hc
        · exact Or.inl ((halfCut_symmetric p) _ _ hc)
        · exact Or.inr (Or.inl ((halfCut_symmetric q) _ _ hc))
        · exact Or.inr (Or.inr (Or.inr hc))
        · exact Or.inr (Or.inr (Or.inl hc))
      exact (Relation.ReflTransGen.single hcb).trans ih
  have h03 : Relation.ReflTransGen ((joinedEdge p) q) r0 r3 := by
    have h : (halfCut p) r0 = some r3 := by
      simpa [r0, r3, secondOpen, hp1, hp2] using
        (halfCut_second_pair p)
    exact Relation.ReflTransGen.single (Or.inl h)
  have h12 : Relation.ReflTransGen ((joinedEdge p) q) r1 r2 := by
    have h : (halfCut p) r1 = some r2 := by
      simpa [r1, r2, hp1] using (halfCut_first_pair p)
    exact Relation.ReflTransGen.single (Or.inl h)
  constructor
  · intro hconn
    by_contra hodd
    have heven : q.val.1 % 2 = 0 := by omega
    let hcolor : Fin n → Prop := fun x =>
      (cTerminal q) x.val = 0 ∨ (cTerminal q) x.val = 3
    have hclosed (i j : Fin n) (hi : hcolor i)
        (hij : (joinedEdge p) q i j) : hcolor j := by
      rcases hij with hcut | hcut | ⟨hiP, hr⟩ | ⟨hjP, hr⟩
      · exact ((C_color_p_edge p) q hp1 hp2 hc i j hcut).mp hi
      · exact ((C_color_q_edge_even q) hc hq2 heven i j hcut).mp hi
      · change (cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3
        rw [← hr, ht.1 ⟨i, hiP⟩]
        exact hi
      · change (cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3
        have hm := ht.1 ⟨j, hjP⟩
        rw [hr] at hm
        change (cTerminal q) i.val = 0 ∨ (cTerminal q) i.val = 3 at hi
        rwa [← hm]
    have hpath := hconn r0 r1
    have hstay : hcolor r0 → hcolor r1 :=
      Relation.ReflTransGen.head_induction_on
        (motive := fun a _ => hcolor a → hcolor r1) hpath
        (fun ha => ha) (fun hab _ ih ha => ih (hclosed _ _ ha hab))
    have hzero : hcolor r0 := by
      change (cTerminal q) 0 = 0 ∨ (cTerminal q) 0 = 3
      left
      simp [cTerminal]
    have hone : ¬ hcolor r1 := by
      change ¬ ((cTerminal q) 1 = 0 ∨ (cTerminal q) 1 = 3)
      simp [cTerminal,
        show 1 ≤ q.val.1 + 2 by omega]
    exact hone (hstay hzero)
  · intro hodd
    let a : Fin n := ⟨q.val.1 - 1, by
      have := q.property.1
      have := q.property.2.2.1
      have := q.property.2.2.2
      omega⟩
    let b : Fin n := ⟨q.val.1, lt_trans q.property.2.2.1 q.property.2.2.2⟩
    have hab : Relation.ReflTransGen ((joinedEdge p) q) a b := by
      have h : (halfCut q) a = some b := by
        simpa [a, b] using (halfCut_first_pair q)
      exact Relation.ReflTransGen.single (Or.inr (Or.inl h))
    obtain ⟨za, hza, _, hpa⟩ := ht.2 a
    obtain ⟨zb, hzb, _, hpb⟩ := ht.2 b
    have hza' : za.val = (q.val.1 - 1) % 4 := by
      rw [hza]
      simp [cTerminal, a,
        show q.val.1 - 1 ≤ q.val.1 + 2 by omega]
    have hzb' : zb.val = q.val.1 % 4 := by
      rw [hzb]
      simp [cTerminal, b]
    have hcross :
        (za.val = 0 ∧ zb.val = 1) ∨
        (za.val = 2 ∧ zb.val = 3) := by
      omega
    have hzab : Relation.ReflTransGen ((joinedEdge p) q) za zb :=
      ((hsym hpa).trans hab).trans hpb
    have h01 : Relation.ReflTransGen ((joinedEdge p) q) r0 r1 := by
      rcases hcross with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have ea : za = r0 := Fin.ext ha
        have eb : zb = r1 := Fin.ext hb
        simpa [ea, eb] using hzab
      · have ea : za = r2 := Fin.ext ha
        have eb : zb = r3 := Fin.ext hb
        have h23 : Relation.ReflTransGen ((joinedEdge p) q) r2 r3 := by
          simpa [ea, eb] using hzab
        exact h03.trans ((hsym h23).trans (hsym h12))
    have hroot0 (z : Fin n) (hz : z.val < 4) :
        Relation.ReflTransGen ((joinedEdge p) q) z r0 := by
      by_cases h0 : z.val = 0
      · have he : z = r0 := Fin.ext h0
        simpa [he] using (Relation.ReflTransGen.refl :
          Relation.ReflTransGen ((joinedEdge p) q) r0 r0)
      by_cases h1 : z.val = 1
      · have he : z = r1 := Fin.ext h1
        simpa [he] using hsym h01
      by_cases h2 : z.val = 2
      · have he : z = r2 := Fin.ext h2
        simpa [he] using (hsym h12).trans (hsym h01)
      · have he : z = r3 := Fin.ext (by dsimp [r3]; omega)
        simpa [he] using hsym h03
    have htozero (x : Fin n) :
        Relation.ReflTransGen ((joinedEdge p) q) x r0 := by
      obtain ⟨z, _, hz, hxz⟩ := ht.2 x
      exact hxz.trans (hroot0 z hz)
    intro i j
    exact (htozero i).trans (hsym (htozero j))


end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
