/- GID: D5/S3/FiniteGroups/HeadleyExtension
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyExtension
   mirror-E: none(waiver:stage-a-extension)
   anchors: []
   utility: none
   digest: The nonsplit kernel-cycle splice for an even R-star quotient. -/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch

/-! The nonsplit extension step for cyclic directed-difference orderings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyExtension

open Function Set

/-! ## The finite cyclic inventories used by the splice -/

/-- A cyclic ordering with its successor and its complete directed-difference inventory.

The successor is allowed to fix zero; its nonzero support is one cycle.  The separate
`difference` equivalence records the closing edge as well as all ordinary edges. -/
structure RCycle (G : Type*) [AddCommGroup G] where
  successor : Equiv.Perm G
  successor_zero : successor 0 = 0
  nonzero_cycle : successor.IsCycleOn {x : G | x ≠ 0}
  difference : Equiv.Perm G
  difference_spec : ∀ x, difference x = successor x - x

/-- An R-cycle with a chosen consecutive additive triple.  The order parity is part of
the quotient hypothesis and is used only to pair the ordinary lift rows. -/
structure RStar (G : Type*) [AddCommGroup G] [Finite G] extends RCycle G where
  even_card : Even (Nat.card G)
  a : G
  b : G
  c : G
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0
  pairwise_distinct : a ≠ b ∧ a ≠ c ∧ b ≠ c
  successor_a : successor a = b
  successor_b : successor b = c
  triple_sum : a + c = b

/-! The permutation surgery below is performed on vertices, with the inverse
three-cycle acting on the old edge-label inventory. -/

private theorem swap_joins {X : Type*} [Finite X] [DecidableEq X]
    (f : Equiv.Perm X) (a b : X) (hab : ¬ f.SameCycle a b) :
    let g : Equiv.Perm X := f * Equiv.swap a b
    g.SameCycle a b ∧
      (∀ x y, f.SameCycle x y → g.SameCycle x y) := by
  dsimp
  let g : Equiv.Perm X := f * Equiv.swap a b
  have hne : a ≠ b := fun h => hab (h.sameCycle f)
  have hex : ∃ n : ℕ, (f ^ n) (f a) = a :=
    (Equiv.Perm.SameCycle.refl f a).apply_left.exists_nat_pow_eq
  let k := Nat.find hex
  have hk : (f ^ k) (f a) = a := Nat.find_spec hex
  have havoid (j : ℕ) (hj : j < k) : (f ^ j) (f a) ≠ a := by
    exact Nat.find_min hex hj
  have havoidb (j : ℕ) : (f ^ j) (f a) ≠ b := by
    intro he
    apply hab
    rw [← he]
    exact (Equiv.Perm.SameCycle.refl f a).apply_right.pow_right
  have hp : ∀ j ≤ k, (g ^ j) (f a) = (f ^ j) (f a) := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
      change f (Equiv.swap a b ((f ^ j) (f a))) = _
      rw [Equiv.swap_apply_of_ne_of_ne (havoid j (by omega)) (havoidb j)]
      rw [pow_succ', Equiv.Perm.mul_apply]
  have hba : g.SameCycle b a := by
    have hga : g b = f a := by simp [g]
    have hpath : g.SameCycle (f a) a :=
      ⟨(k : ℤ), by rw [zpow_natCast, hp k le_rfl, hk]⟩
    exact (hga.sameCycle g).of_apply_left.trans hpath
  refine ⟨hba.symm, ?_⟩
  intro x y hxy
  have hedge (z : X) : g.SameCycle z (f z) := by
    by_cases hza : z = a
    · subst z
      have he : g b = f a := by simp [g]
      rw [← he]
      exact hba.symm.apply_right
    by_cases hzb : z = b
    · subst z
      have he : g a = f b := by simp [g]
      rw [← he]
      exact hba.apply_right
    · have he : g z = f z := by simp [g, Equiv.swap_apply_of_ne_of_ne hza hzb]
      rw [← he]
      exact (Equiv.Perm.SameCycle.refl g z).apply_right
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact Equiv.Perm.SameCycle.refl g x
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (hedge _)


private theorem kernel_return_cycle {N : Type*} [AddCommGroup N] [Fintype N]
    [DecidableEq N] (r : RCycle N) (v : N) (hv : v ≠ 0) :
    (r.successor * Equiv.swap 0 v).IsCycleOn Set.univ := by
  have hn : ¬ r.successor.SameCycle 0 v := by
    intro h
    exact hv (h.eq_of_left r.successor_zero).symm
  obtain ⟨hj, hp⟩ := swap_joins r.successor 0 v hn
  have hc : ∀ h : N, (r.successor * Equiv.swap 0 v).SameCycle 0 h := by
    intro h
    by_cases hh : h = 0
    · subst h
      exact .refl _ _
    · exact hj.trans (hp v h (r.nonzero_cycle.2 hv hh))
  refine ⟨?_, fun x _ y _ => (hc x).symm.trans (hc y)⟩
  exact (r.successor * Equiv.swap 0 v).bijective.bijOn_univ

private structure ColumnChart (Q : Type*) [AddCommGroup Q] [Fintype Q]
    (r : RStar Q) where
  k : ℕ
  even_k : Even k
  vertex : Fin (k + 3) ≃ {q : Q // q ≠ 0}
  first : (vertex 0).val = r.a
  second : (vertex 1).val = r.b
  third : (vertex 2).val = r.c
  step : ∀ i, (vertex (finRotate (k + 3) i)).val = r.successor (vertex i).val

private theorem column_chart {Q : Type*} [AddCommGroup Q] [Fintype Q]
    (r : RStar Q) : Nonempty (ColumnChart Q r) := by
  classical
  let s : Finset Q := Finset.univ.erase 0
  have hs : (s : Set Q) = {q : Q | q ≠ 0} := by ext q; simp [s]
  have hc : r.successor.IsCycleOn (s : Set Q) := hs ▸ r.nonzero_cycle
  have ha : r.a ∈ s := by simp [s, r.a_ne_zero]
  have hsize : 3 ≤ s.card := by
    have hsub : {r.a, r.b, r.c} ⊆ s := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;>
        simp [s, r.a_ne_zero, r.b_ne_zero, r.c_ne_zero]
    have h := Finset.card_le_card hsub
    simpa [r.pairwise_distinct.1, r.pairwise_distinct.2.1,
      r.pairwise_distinct.2.2] using h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hsize
  have hk' : s.card = k + 3 := by omega
  have heven : Even k := by
    have hcard : s.card + 1 = Fintype.card Q := by
      have hpos := Fintype.card_pos (α := Q)
      simp only [s, Finset.card_erase_of_mem (Finset.mem_univ (0 : Q)), Finset.card_univ]
      omega
    obtain ⟨t, ht⟩ := (show Even (Fintype.card Q) by simpa only [Nat.card_eq_fintype_card] using r.even_card)
    exact ⟨t - 2, by omega⟩
  let e : Fin (k + 3) → {q : Q // q ≠ 0} := fun i =>
    ⟨(r.successor ^ i.val) r.a, by
      have h := hc.1.mapsTo.perm_pow i.val ha
      simpa only [hs, Set.mem_ofPred_eq] using h⟩
  have hinj : Injective e := by
    intro i j hij
    apply Fin.ext
    exact hc.injOn_pow_apply ha (by simpa [hk'] using i.isLt)
      (by simpa [hk'] using j.isLt) (congrArg Subtype.val hij)
  have hsurj : Surjective e := by
    intro q
    obtain ⟨i, hi, he⟩ := hc.exists_pow_eq ha (by simpa [s] using q.property)
    exact ⟨⟨i, by simpa [hk'] using hi⟩, Subtype.ext he⟩
  refine ⟨{ k := k, even_k := heven, vertex := Equiv.ofBijective e ⟨hinj, hsurj⟩
            first := ?_, second := ?_, third := ?_, step := ?_ }⟩
  · change (r.successor ^ (0 : Fin (k + 3)).val) r.a = r.a
    simp
  · change (r.successor ^ (1 : Fin (k + 3)).val) r.a = r.b
    simpa using r.successor_a
  · change (r.successor ^ (2 : Fin (k + 3)).val) r.a = r.c
    simpa [Nat.mod_eq_of_lt (show (2 : ℕ) < k + 3 by omega), pow_succ', Equiv.Perm.mul_apply,
      r.successor_a] using r.successor_b
  · intro i
    change (r.successor ^ (finRotate (k + 3) i).val) r.a =
      r.successor ((r.successor ^ i.val) r.a)
    by_cases hi : i = Fin.last (k + 2)
    · subst i
      rw [finRotate_last]
      have hp := hc.pow_card_apply ha
      rw [hk'] at hp
      simpa [pow_succ', Equiv.Perm.mul_apply] using hp.symm
    · rw [coe_finRotate_of_ne_last hi, pow_succ', Equiv.Perm.mul_apply]

private def kernelF {N : Type*} [AddCommGroup N] [Fintype N] (r : RCycle N) :
    Equiv.Perm N := r.difference.trans (Equiv.neg N)

private theorem kernelF_apply {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) (h : N) : kernelF r h = h - r.successor h := by
  change -(r.difference h) = _
  rw [r.difference_spec]
  abel

private theorem kernelF_zero {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) : kernelF r 0 = 0 := by
  simp [kernelF_apply, r.successor_zero]

private theorem inverse_difference_bijective {N : Type*} [AddCommGroup N]
    (f : Equiv.Perm N) (hf : Bijective (fun h => f h - h)) :
    Bijective (fun h => f.symm h - h) := by
  have he : (fun h => f.symm h - h) =
      (fun h => -h) ∘ (fun h => f h - h) ∘ f.symm := by
    funext h
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    abel
  rw [he]
  exact (Equiv.neg N).bijective.comp (hf.comp f.symm.bijective)

private def rowPotential {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) {k : ℕ} (i : Fin (k + 3)) : Equiv.Perm N :=
  if i.val = 0 then 1 else if i.val = 1 then kernelF r
  else if i.val = 2 then 1 else if i.val % 2 = 1 then r.successor
  else r.successor.trans (kernelF r)

private def cylinder {N : Type*} (D : Equiv.Perm N) (k : ℕ) :
    Equiv.Perm (Fin (k + 3) × N) :=
  (Equiv.prodCongrRight (fun i : Fin (k + 3) =>
    if i = Fin.last (k + 2) then D else 1)).trans
      (Equiv.prodCongr (finRotate (k + 3)) (Equiv.refl N))

private def rowLift {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) (k : ℕ) : Equiv.Perm (Fin (k + 3) × N) :=
  let p := Equiv.prodCongrRight (@rowPotential N _ _ r k)
  (p.symm.trans (cylinder r.successor k)).trans p

private theorem cylinder_partial {N : Type*} (D : Equiv.Perm N) (k : ℕ)
    (h : N) (j : ℕ) (hj : j < k + 3) :
    (cylinder D k ^ j) (0, h) = (⟨j, hj⟩, h) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    have hne : (⟨j, by omega⟩ : Fin (k + 3)) ≠ Fin.last (k + 2) := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_mk, Fin.val_last] at this
      omega
    simp [cylinder, hne, finRotate_of_lt (by omega : j < k + 2)]

private theorem cylinder_round {N : Type*} (D : Equiv.Perm N) (k : ℕ) (h : N) :
    (cylinder D k ^ (k + 3)) (0, h) = (0, D h) := by
  rw [pow_succ', Equiv.Perm.mul_apply,
    cylinder_partial D k h (k + 2) (by omega)]
  simp [cylinder, show (⟨k + 2, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) from rfl]


private theorem cylinder_rounds {N : Type*} (D : Equiv.Perm N) (k j : ℕ) (h : N) :
    (cylinder D k ^ ((k + 3) * j)) (0, h) = (0, (D ^ j) h) := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, cylinder_round, ih,
      pow_succ, Equiv.Perm.mul_apply]

private theorem cylinder_connect {N : Type*} [Finite N]
    (D : Equiv.Perm N) (k : ℕ) (i j : Fin (k + 3)) (h t : N)
    (hht : D.SameCycle h t) : (cylinder D k).SameCycle (i, h) (j, t) := by
  have hp (u : N) (l : Fin (k + 3)) :
      (cylinder D k).SameCycle (0, u) (l, u) :=
    ⟨(l.val : ℤ), by rw [zpow_natCast, cylinder_partial]⟩
  obtain ⟨n, hn⟩ := hht.exists_nat_pow_eq
  have hb : (cylinder D k).SameCycle (0, h) (0, t) :=
    ⟨(((k + 3) * n : ℕ) : ℤ), by rw [zpow_natCast, cylinder_rounds, hn]⟩
  exact (hp h i).symm.trans (hb.trans (hp t j))

private def rowEdge {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) {k : ℕ} (i : Fin (k + 3)) : Equiv.Perm N :=
  ((rowPotential r i).symm.trans
    (if i = Fin.last (k + 2) then r.successor else 1)).trans
      (rowPotential r (finRotate (k + 3) i))

private theorem rowLift_apply {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) (k : ℕ) (i : Fin (k + 3)) (h : N) :
    rowLift r k (i, h) = (finRotate (k + 3) i, rowEdge r i h) := rfl

private theorem rowEdge_formula {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) {k : ℕ} (hk : Even k) (i : Fin (k + 3)) :
    rowEdge r i = if i.val = 0 then kernelF r
      else if i.val = 1 then (kernelF r).symm
      else if i.val = 2 then r.successor
      else if i.val % 2 = 1 then kernelF r else (kernelF r).symm := by
  obtain ⟨t, ht⟩ := hk
  have hke : k % 2 = 0 := by omega
  by_cases hl : i = Fin.last (k + 2)
  · have hiv : i.val = k + 2 := congrArg Fin.val hl
    have hir : (finRotate (k + 3) i).val = 0 := by simp [hl]
    by_cases hk0 : k = 0
    · simp only [rowEdge, ite_eq_left hl, rowPotential, hiv, hir, hk0]
      ext x
      simp <;> rfl
    · have hn0 : k + 2 ≠ 0 := by omega
      have hn1 : k + 2 ≠ 1 := by omega
      have hn2 : k + 2 ≠ 2 := by omega
      have hm : (k + 2) % 2 ≠ 1 := by omega
      simp only [rowEdge, ite_eq_left hl, rowPotential, hiv, hir, hn0, hn1, hn2,
        hm, ↓reduceIte]
      ext x
      simp
  · have hn : (finRotate (k + 3) i).val = i.val + 1 :=
      coe_finRotate_of_ne_last hl
    by_cases h0 : i.val = 0
    · simp only [rowEdge, ite_eq_right hl, rowPotential, hn, h0]
      ext x
      simp
    by_cases h1 : i.val = 1
    · simp only [rowEdge, ite_eq_right hl, rowPotential, hn, h1]
      ext x
      simp
    by_cases h2 : i.val = 2
    · simp only [rowEdge, ite_eq_right hl, rowPotential, hn, h2]
      ext x
      simp
    have hn0 : i.val + 1 ≠ 0 := by omega
    have hn1 : i.val + 1 ≠ 1 := by omega
    have hn2 : i.val + 1 ≠ 2 := by omega
    by_cases hm : i.val % 2 = 1
    · have hm' : (i.val + 1) % 2 ≠ 1 := by omega
      simp only [rowEdge, ite_eq_right hl, rowPotential, hn, h0, h1, h2,
        hn0, hn1, hn2, hm, hm', ↓reduceIte]
      ext x
      simp
    · have hm' : (i.val + 1) % 2 = 1 := by omega
      simp only [rowEdge, ite_eq_right hl, rowPotential, hn, h0, h1, h2,
        hn0, hn1, hn2, hm, hm', ↓reduceIte]
      ext x
      simp

private theorem rowEdge_difference {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) {k : ℕ} (hk : Even k) (i : Fin (k + 3)) :
    Bijective (fun h => rowEdge r i h - h) := by
  have hF : Bijective (fun h => kernelF r h - h) := by
    have he : (fun h => kernelF r h - h) = (fun h => -(r.successor h)) := by
      funext h
      rw [kernelF_apply]
      abel
    rw [he]
    exact (Equiv.neg N).bijective.comp r.successor.bijective
  have hJ := inverse_difference_bijective (kernelF r) hF
  rw [rowEdge_formula r hk]
  split_ifs
  · exact hF
  · exact hJ
  · simpa only [← r.difference_spec] using r.difference.bijective
  · exact hF
  · exact hJ

private theorem rowLift_connect {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) (k : ℕ) (i j : Fin (k + 3)) (h t : N)
    (hht : r.successor.SameCycle h t) :
    (rowLift r k).SameCycle (i, rowPotential r i h) (j, rowPotential r j t) := by
  exact (D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.same_cycle_perm_congr
      (Equiv.prodCongrRight (@rowPotential N _ _ r k)) (cylinder r.successor k)
      (i, h) (j, t)).mpr (cylinder_connect r.successor k i j h t hht)

private theorem cycle_invariant {X : Type*} [Finite X] (f : Equiv.Perm X)
    (P : X → Prop) (hP : ∀ x, P (f x) ↔ P x) {x y : X}
    (h : f.SameCycle x y) : P x ↔ P y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hP] using ih


private theorem compatible_section {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Fintype Q] (π : E →+ Q) (hπ : Surjective π) (r : RStar Q) :
    ∃ s : Q → E, (∀ q, π (s q) = q) ∧ s r.a + s r.c = s r.b := by
  classical
  let t : Q → E := fun q => Classical.choose (hπ q)
  have ht : ∀ q, π (t q) = q := fun q => Classical.choose_spec (hπ q)
  let s : Q → E := fun q => if q = r.b then t r.a + t r.c else t q
  refine ⟨s, ?_, ?_⟩
  · intro q
    by_cases hq : q = r.b
    · simp [s, hq, map_add, ht, r.triple_sum]
    · simp [s, hq, ht]
  · simp [s, r.pairwise_distinct.1, Ne.symm r.pairwise_distinct.2.2]

private def vertices {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Fintype Q] (N : AddSubgroup E) (r : RStar Q) (c : ColumnChart Q r)
    (s : Q → E) : N ⊕ (Fin (c.k + 3) × N) → E
  | .inl h => h.val
  | .inr (i, h) => s (c.vertex i).val + h.val

private theorem vertices_bijective {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Fintype Q] (N : AddSubgroup E) (π : E →+ Q)
    (hker : π.ker = N) (r : RStar Q) (c : ColumnChart Q r)
    (s : Q → E) (hs : ∀ q, π (s q) = q) :
    Bijective (vertices N r c s) := by
  have hN (h : N) : π h.val = 0 := by
    exact AddMonoidHom.mem_ker.mp (hker.symm ▸ h.property)
  have hmem (x : E) (hx : π x = 0) : x ∈ N := by
    rw [← hker]
    exact hx
  constructor
  · intro x y hxy
    have hq := congrArg π hxy
    cases x with
    | inl h =>
      cases y with
      | inl t => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y =>
        obtain ⟨j, t⟩ := y
        have he : (c.vertex j).val = 0 := by
          simpa [vertices, map_add, hs, hN] using hq.symm
        exact ((c.vertex j).property he).elim
    | inr x =>
      obtain ⟨i, h⟩ := x
      cases y with
      | inl t =>
        have he : (c.vertex i).val = 0 := by
          simpa [vertices, map_add, hs, hN] using hq
        exact ((c.vertex i).property he).elim
      | inr y =>
        obtain ⟨j, t⟩ := y
        have he : c.vertex i = c.vertex j := Subtype.ext (by
          simpa [vertices, map_add, hs, hN] using hq)
        have hij := c.vertex.injective he
        subst j
        have hht : h = t := Subtype.ext (add_left_cancel hxy)
        rw [hht]
  · intro x
    by_cases hx : π x = 0
    · exact ⟨.inl ⟨x, hmem x hx⟩, rfl⟩
    · let i := c.vertex.symm ⟨π x, hx⟩
      have hi : (c.vertex i).val = π x :=
        congrArg Subtype.val (c.vertex.apply_symm_apply ⟨π x, hx⟩)
      let h : N := ⟨x - s (π x), hmem _ (by simp [map_sub, hs])⟩
      refine ⟨.inr (i, h), ?_⟩
      change s (c.vertex i).val + (x - s (π x)) = x
      rw [hi]
      abel

private def oldSuccessor {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) (k : ℕ) : Equiv.Perm (N ⊕ (Fin (k + 3) × N)) :=
  Equiv.sumCongr r.successor (rowLift r k)

private theorem sum_sameCycle_left {N X : Type*} [Finite N]
    (D : Equiv.Perm N) (f : Equiv.Perm X) {h t : N}
    (hht : D.SameCycle h t) :
    Equiv.Perm.SameCycle (Equiv.sumCongr D f) (.inl h) (.inl t) := by
  obtain ⟨n, hn⟩ := hht.exists_nat_pow_eq
  have hp : ∀ j : ℕ, ((Equiv.sumCongr D f : Equiv.Perm (N ⊕ X)) ^ j) (.inl h) =
      .inl ((D ^ j) h) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rfl
  exact ⟨(n : ℤ), by rw [zpow_natCast, hp n, hn]⟩

private theorem sum_sameCycle_right {N X : Type*} [Finite X]
    (D : Equiv.Perm N) (f : Equiv.Perm X) {x y : X}
    (hxy : f.SameCycle x y) :
    Equiv.Perm.SameCycle (Equiv.sumCongr D f) (.inr x) (.inr y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hp : ∀ j : ℕ, ((Equiv.sumCongr D f : Equiv.Perm (N ⊕ X)) ^ j) (.inr x) =
      .inr ((f ^ j) x) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rfl
  exact ⟨(n : ℤ), by rw [zpow_natCast, hp n, hn]⟩

private def mainNonzero {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) {k : ℕ} : N ⊕ (Fin (k + 3) × N) → Prop
  | .inl _ => False
  | .inr (i, h) => (rowPotential r i).symm h ≠ 0

private theorem mainNonzero_invariant {N : Type*} [AddCommGroup N] [Fintype N]
    (r : RCycle N) (k : ℕ) (x : N ⊕ (Fin (k + 3) × N)) :
    mainNonzero r (oldSuccessor r k x) ↔ mainNonzero r x := by
  cases x with
  | inl h => rfl
  | inr x =>
    rcases x with ⟨i, h⟩
    change (rowPotential r (finRotate (k + 3) i)).symm
      (rowPotential r (finRotate (k + 3) i)
        ((if i = Fin.last (k + 2) then r.successor else 1)
          ((rowPotential r i).symm h))) ≠ 0 ↔ _
    rw [Equiv.symm_apply_apply]
    split_ifs
    · rw [← r.successor_zero, r.successor.injective.ne_iff]
      rfl
    · rfl


private theorem swap_invariant {X : Type*} [DecidableEq X] (P : X → Prop)
    (a b : X) (hab : P a ↔ P b) (x : X) :
    P (Equiv.swap a b x) ↔ P x := by
  by_cases hxa : x = a
  · subst x
    simp only [Equiv.swap_apply_left]
    exact hab.symm
  by_cases hxb : x = b
  · subst x
    simp only [Equiv.swap_apply_right]
    exact hab
  · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

private def spliceSuccessor {N : Type*} [AddCommGroup N] [Fintype N]
    [DecidableEq N] (r : RCycle N) (k : ℕ) (v : N) :
    Equiv.Perm (N ⊕ (Fin (k + 3) × N)) :=
  oldSuccessor r k * Equiv.swap (.inr (0, 0)) (.inl v) *
    Equiv.swap (.inl v) (.inr (1, kernelF r v))

private theorem splice_zero {N : Type*} [AddCommGroup N] [Fintype N]
    [DecidableEq N] (r : RCycle N) (k : ℕ) (v : N) (hv : v ≠ 0) :
    spliceSuccessor r k v (.inl 0) = .inl 0 := by
  simp [spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    hv, Ne.symm hv, oldSuccessor, Equiv.sumCongr, r.successor_zero]

/- A segment which avoids the return section until its endpoint.  In particular,
prepending one edge from the section makes its length a genuine first-return time. -/
private def Until {X : Type*} (f : Equiv.Perm X) (P : X → Prop) (x y : X) : Prop :=
  ∃ n : ℕ, (f ^ n) x = y ∧ ∀ j < n, ¬ P ((f ^ j) x)

private theorem until_prepend {X : Type*} (f : Equiv.Perm X) (P : X → Prop)
    {x y z : X} (hxy : f x = y) (hx : ¬ P x) (hyz : Until f P y z) :
    Until f P x z := by
  obtain ⟨n, hn, ha⟩ := hyz
  refine ⟨n + 1, ?_, ?_⟩
  · rw [pow_succ, Equiv.Perm.mul_apply, hxy, hn]
  · intro j hj
    cases j with
    | zero => exact hx
    | succ j =>
      rw [pow_succ, Equiv.Perm.mul_apply, hxy]
      exact ha j (by omega)

private theorem until_trans {X : Type*} (f : Equiv.Perm X) (P : X → Prop)
    {x y z : X} (hxy : Until f P x y) (hyz : Until f P y z) :
    Until f P x z := by
  obtain ⟨m, hm, ha⟩ := hxy
  obtain ⟨n, hn, hb⟩ := hyz
  refine ⟨n + m, ?_, ?_⟩
  · rw [pow_add, Equiv.Perm.mul_apply, hm, hn]
  · intro j hj
    by_cases hjm : j < m
    · exact ha j hjm
    · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (by omega : m ≤ j)
      rw [Nat.add_comm m l, pow_add, Equiv.Perm.mul_apply, hm]
      exact hb l (by omega)

private def aColumn {N : Type*} {k : ℕ} : N ⊕ (Fin (k + 3) × N) → Prop
  | .inl _ => False
  | .inr (i, _) => i = 0

private theorem splice_tail {N : Type*} [AddCommGroup N] [Fintype N]
    [DecidableEq N] (r : RCycle N) (k : ℕ) (v h : N)
    (i : Fin (k + 3)) (hi : 2 ≤ i.val) :
    Until (spliceSuccessor r k v) aColumn
      (.inr (i, rowPotential r i h)) (.inr (0, r.successor h)) := by
  induction i using Fin.reverseInduction with
  | last =>
    have hl0 : (Fin.last (k + 2) : Fin (k + 3)) ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
    have hl1 : (Fin.last (k + 2) : Fin (k + 3)) ≠ 1 := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_last, Fin.val_one] at this
      omega
    apply until_prepend _ _ (y := .inr (0, r.successor h))
    · simp [spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        oldSuccessor, rowLift, cylinder, Equiv.sumCongr, hl0, hl1, rowPotential]
    · exact hl0
    · exact ⟨0, rfl, by simp⟩
  | @cast i ih =>
    change 2 ≤ i.val at hi
    have hn0 : (i.castSucc : Fin (k + 3)) ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_zero] at this
      omega
    have hn1 : (i.castSucc : Fin (k + 3)) ≠ 1 := by
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_one] at this
      omega
    have hnlast : i.castSucc ≠ Fin.last (k + 2) := Fin.castSucc_ne_last i
    apply until_prepend _ _ (y := .inr (i.succ, rowPotential r i.succ h))
    · simp [spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        oldSuccessor, rowLift, cylinder, Equiv.sumCongr, hn0, hn1, hnlast,
        finRotate_of_lt (show i.val < k + 2 from i.isLt)]
    · exact hn0
    · exact ih (by simpa using Nat.le_succ_of_le hi)

private theorem splice_first_return {N : Type*} [AddCommGroup N] [Fintype N]
    [DecidableEq N] (r : RCycle N) (k : ℕ) (v : N) (hv : v ≠ 0) (h : N) :
    ∃ n : ℕ, 0 < n ∧
      (spliceSuccessor r k v ^ n) (.inr (0, h)) =
        .inr (0, (r.successor * Equiv.swap 0 v) h) ∧
      ∀ j, 0 < j → j < n → ¬ aColumn ((spliceSuccessor r k v ^ j) (.inr (0, h))) := by
  let T := spliceSuccessor r k v
  let P : N ⊕ (Fin (k + 3) × N) → Prop := aColumn
  have h1last : (1 : Fin (k + 3)) ≠ Fin.last (k + 2) := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_one, Fin.val_last] at this
    omega
  have hrot1 : finRotate (k + 3) (1 : Fin (k + 3)) = ⟨2, by omega⟩ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last h1last]
    rfl
  have hmod : 2 % (k + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  have htwo' : (⟨2, by omega⟩ : Fin (k + 3)) = (2 : Fin (k + 3)) := by
    apply Fin.ext
    exact hmod.symm
  have hFv : kernelF r v ≠ 0 := by
    intro he
    exact hv ((kernelF r).injective (he.trans (kernelF_zero r).symm))
  have hA (t : N) (ht : t ≠ 0) : T (.inr (0, t)) = .inr (1, kernelF r t) := by
    simp [T, spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      oldSuccessor, rowLift, cylinder, rowPotential, Equiv.sumCongr, ht]
  have hB (t : N) (ht : t ≠ v) :
      T (.inr (1, kernelF r t)) = .inr (2, t) := by
    have hFt : kernelF r t ≠ kernelF r v := fun he => ht ((kernelF r).injective he)
    simp [T, spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      oldSuccessor, rowLift, cylinder, rowPotential, Equiv.sumCongr, hFt,
      h1last, hrot1, htwo', hmod]
  have htail (t : N) : Until T P (.inr (2, t)) (.inr (0, r.successor t)) := by
    have he : rowPotential r (2 : Fin (k + 3)) = 1 := by simp [rowPotential, hmod]
    simpa only [he, Equiv.Perm.one_apply] using
      splice_tail r k v t (2 : Fin (k + 3)) (by simp [hmod])
  have hpath : Until T P (T (.inr (0, h)))
      (.inr (0, (r.successor * Equiv.swap 0 v) h)) := by
    by_cases hh0 : h = 0
    · subst h
      have hstart : T (.inr (0, 0)) = .inl (r.successor v) := by
        simp [T, spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
          oldSuccessor, Equiv.sumCongr]
      have hend : T (.inl v) = .inr (2, v) := by
        simp [T, spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
          oldSuccessor, rowLift, cylinder, rowPotential, Equiv.sumCongr,
          h1last, hrot1, htwo', hmod]
      have hkernel : Until T P (.inl (r.successor v)) (.inl v) := by
        have hex : ∃ n : ℕ, (r.successor ^ n) (r.successor v) = v :=
          (Equiv.Perm.SameCycle.refl r.successor v).apply_left.exists_nat_pow_eq
        let n := Nat.find hex
        have hn : (r.successor ^ n) (r.successor v) = v := Nat.find_spec hex
        have hp : ∀ j ≤ n, (T ^ j) (.inl (r.successor v)) =
            .inl ((r.successor ^ j) (r.successor v)) := by
          intro j hj
          induction j with
          | zero => rfl
          | succ j ih =>
            rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
            have hne : (r.successor ^ j) (r.successor v) ≠ v :=
              Nat.find_min hex (by omega)
            simp [T, spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
              oldSuccessor, Equiv.sumCongr, hne, pow_succ']
        exact ⟨n, by rw [hp n le_rfl, hn], fun j hj => by
          rw [hp j (by omega)]; simp [P, aColumn]⟩
      rw [hstart]
      have he : (r.successor * Equiv.swap 0 v) 0 = r.successor v := by simp
      rw [he]
      exact until_trans T P hkernel (until_prepend T P hend (by simp [P, aColumn]) (htail v))
    by_cases hhv : h = v
    · subst h
      have hcut : T (.inr (1, kernelF r v)) = .inr (1, 0) := by
        simp [T, spliceSuccessor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
          oldSuccessor, rowLift, cylinder, rowPotential, Equiv.sumCongr, kernelF_zero]
      have he : (r.successor * Equiv.swap 0 v) v = 0 := by simp [r.successor_zero]
      rw [hA v hv, he]
      have hb0 : T (.inr (1, 0)) = .inr (2, 0) := by
        simpa only [kernelF_zero] using hB 0 (Ne.symm hv)
      have ht0 : Until T P (.inr (2, 0)) (.inr (0, 0)) := by
        simpa only [r.successor_zero] using htail 0
      exact until_prepend T P hcut (by simp [P, aColumn])
        (until_prepend T P hb0 (by simp [P, aColumn]) ht0)
    · have he : (r.successor * Equiv.swap 0 v) h = r.successor h := by
        simp [Equiv.swap_apply_of_ne_of_ne hh0 hhv]
      rw [hA h hh0, he]
      exact until_prepend T P (hB h hhv) (by simp [P, aColumn]) (htail h)
  obtain ⟨n, hn, ha⟩ := hpath
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · simpa only [pow_succ, Equiv.Perm.mul_apply] using hn
  · intro j hj hjn
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [pow_succ, Equiv.Perm.mul_apply]
    exact ha l (by omega)

private theorem splice_cycle {N : Type*} [AddCommGroup N] [Fintype N]
    [DecidableEq N] (r : RCycle N) (k : ℕ) (v : N) (hv : v ≠ 0) :
    (spliceSuccessor r k v).IsCycleOn {x | x ≠ .inl 0} := by
  let X := N ⊕ (Fin (k + 3) × N)
  let a : X := .inr (0, 0)
  let b : X := .inl v
  let c : X := .inr (1, kernelF r v)
  let S := oldSuccessor r k
  let g := S * Equiv.swap a b
  let T := g * Equiv.swap b c
  have hab : ¬ S.SameCycle a b := by
    intro h
    let P : X → Prop := Sum.elim (fun _ => True) (fun _ => False)
    have hi : ∀ x, P (S x) ↔ P x := by
      intro x
      cases x <;> rfl
    exact (cycle_invariant S P hi h).mpr trivial
  obtain ⟨hgab, hgs⟩ := swap_joins S a b hab
  have hPa : ¬ mainNonzero r a := by
    change ¬ ((1 : Equiv.Perm N).symm 0 ≠ 0)
    exact fun hn => hn rfl
  have hPb : ¬ mainNonzero r b := by simp [b, mainNonzero]
  have hPc : mainNonzero r c := by
    simpa [c, mainNonzero, rowPotential] using hv
  have hginv : ∀ x, mainNonzero r (g x) ↔ mainNonzero r x := by
    intro x
    change mainNonzero r (S (Equiv.swap a b x)) ↔ _
    rw [mainNonzero_invariant]
    exact swap_invariant (mainNonzero r) a b (by simp [hPa, hPb]) x
  have hgbc : ¬ g.SameCycle b c := by
    intro h
    exact hPb ((cycle_invariant g (mainNonzero r) hginv h).mpr hPc)
  obtain ⟨htbc, htg⟩ := swap_joins g b c hgbc
  let R : Equiv.Perm N := r.successor * Equiv.swap 0 v
  have hreturn := kernel_return_cycle r v hv
  have hrowStep (h : N) : T.SameCycle (.inr (0, h)) (.inr (0, R h)) := by
    obtain ⟨n, _, hn, _⟩ := splice_first_return r k v hv h
    exact ⟨(n : ℤ), by
      simpa only [zpow_natCast, T, g, S, a, b, c, R, spliceSuccessor] using hn⟩
  have hbase (h : N) : T.SameCycle a (.inr (0, h)) := by
    obtain ⟨j, hj⟩ := (hreturn.2 (x := 0) trivial (y := h) trivial).exists_nat_pow_eq
    have hp : ∀ n : ℕ, T.SameCycle a (.inr (0, (R ^ n) 0)) := by
      intro n
      induction n with
      | zero => exact .refl _ _
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.trans (hrowStep _)
    change (R ^ j) 0 = h at hj
    rw [← hj]
    exact hp j
  have hac : T.SameCycle a c := by
    have hr := rowLift_connect r k 0 1 v v (Equiv.Perm.SameCycle.refl _ _)
    have hp1 : rowPotential r (1 : Fin (k + 3)) = kernelF r := by simp [rowPotential]
    rw [hp1] at hr
    change (rowLift r k).SameCycle (0, v) (1, kernelF r v) at hr
    exact (hbase v).trans (htg _ _ (hgs _ _
      (sum_sameCycle_right r.successor (rowLift r k) hr)))
  have hconnect : ∀ x : X, x ≠ .inl 0 → T.SameCycle b x := by
    intro x hx
    cases x with
    | inl h =>
      have hh : h ≠ 0 := fun he => hx (congrArg Sum.inl he)
      exact htg _ _ (hgs _ _ (sum_sameCycle_left r.successor (rowLift r k)
        (r.nonzero_cycle.2 hv hh)))
    | inr x =>
      rcases x with ⟨i, h⟩
      let t := (rowPotential r i).symm h
      have ht : rowPotential r i t = h := (rowPotential r i).apply_symm_apply h
      by_cases ht0 : t = 0
      · have hs : S.SameCycle a (.inr (i, h)) := by
          have hrow := rowLift_connect r k 0 i 0 0 (Equiv.Perm.SameCycle.refl _ _)
          have he : rowPotential r i 0 = h := by simpa [ht0] using ht
          change (rowLift r k).SameCycle (0, 0) (i, rowPotential r i 0) at hrow
          rw [he] at hrow
          exact sum_sameCycle_right r.successor (rowLift r k) hrow
        exact (htg _ _ hgab).symm.trans (htg _ _ (hgs _ _ hs))
      · have hs : S.SameCycle c (.inr (i, h)) := by
          have hrow := rowLift_connect r k 1 i v t (r.nonzero_cycle.2 hv ht0)
          have hp1 : rowPotential r (1 : Fin (k + 3)) = kernelF r := by simp [rowPotential]
          rw [hp1, ht] at hrow
          exact sum_sameCycle_right r.successor (rowLift r k) hrow
        exact (htg _ _ hgab).symm.trans (hac.trans (htg _ _ (hgs _ _ hs)))
  have hT0 : T (.inl 0) = .inl 0 := splice_zero r k v hv
  change T.IsCycleOn {x | x ≠ .inl 0}
  constructor
  · refine ⟨?_, T.injective.injOn, ?_⟩
    · intro x hx he
      exact hx (T.injective (he.trans hT0.symm))
    · intro y hy
      refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
      intro he
      have h := congrArg T he
      rw [T.apply_symm_apply, hT0] at h
      exact hy h
  · intro x hx y hy
    exact (hconnect x hx).symm.trans (hconnect y hy)


private def column {Q N : Type*} [AddCommGroup Q] [Fintype Q]
    (r : RStar Q) (c : ColumnChart Q r) : N ⊕ (Fin (c.k + 3) × N) → Q
  | .inl _ => 0
  | .inr (i, _) => (c.vertex i).val

private theorem old_label_injective {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Fintype E] [Fintype Q] (N : AddSubgroup E) (π : E →+ Q)
    (hker : π.ker = N) [Fintype N] (r : RCycle N) (rQ : RStar Q) (c : ColumnChart Q rQ)
    (s : Q → E) (hs : ∀ q, π (s q) = q) :
    Injective (fun x => vertices N rQ c s (oldSuccessor r c.k x) - vertices N rQ c s x) := by
  have hN (h : N) : π h.val = 0 :=
    AddMonoidHom.mem_ker.mp (hker.symm ▸ h.property)
  have hV : ∀ x, π (vertices N rQ c s x) = column rQ c x := by
    intro x
    cases x with
    | inl h => exact hN h
    | inr x => simp [vertices, column, map_add, hs, hN]
  have hC : ∀ x, column rQ c (oldSuccessor r c.k x) = rQ.successor (column rQ c x) := by
    intro x
    cases x with
    | inl h => exact rQ.successor_zero.symm
    | inr x =>
      rcases x with ⟨i, h⟩
      exact c.step i
  intro x y hxy
  have hcol : column rQ c x = column rQ c y := by
    apply rQ.difference.injective
    have he := congrArg π hxy
    simpa only [map_sub, hV, hC, ← rQ.difference_spec] using he
  cases x with
  | inl h =>
    cases y with
    | inl t =>
      apply congrArg Sum.inl
      apply r.difference.injective
      apply Subtype.ext
      simpa only [oldSuccessor, Equiv.sumCongr_apply, Sum.map_inl, vertices,
        r.difference_spec, AddSubgroup.coe_sub] using hxy
    | inr y =>
      exact ((c.vertex y.1).property hcol.symm).elim
  | inr x =>
    rcases x with ⟨i, h⟩
    cases y with
    | inl t => exact ((c.vertex i).property hcol).elim
    | inr y =>
      rcases y with ⟨j, t⟩
      have hij : i = j := c.vertex.injective (Subtype.ext hcol)
      subst j
      have he : rowEdge r i h - h = rowEdge r i t - t := by
        apply Subtype.ext
        change (rowEdge r i h).val - h.val = (rowEdge r i t).val - t.val
        apply add_left_cancel (a := s (c.vertex (finRotate (c.k + 3) i)).val - s (c.vertex i).val)
        calc
          _ = vertices N rQ c s (oldSuccessor r c.k (.inr (i, h))) -
              vertices N rQ c s (.inr (i, h)) := by
                simp only [oldSuccessor, Equiv.sumCongr_apply, Sum.map_inr,
                  rowLift_apply, vertices]
                abel
          _ = vertices N rQ c s (oldSuccessor r c.k (.inr (i, t))) -
              vertices N rQ c s (.inr (i, t)) := hxy
          _ = _ := by
                simp only [oldSuccessor, Equiv.sumCongr_apply, Sum.map_inr,
                  rowLift_apply, vertices]
                abel
      have hht := (rowEdge_difference r c.even_k i).injective he
      rw [hht]

private theorem three_cut_labels {E X : Type*} [AddCommGroup E] [DecidableEq X]
    (V : X → E) (S : Equiv.Perm X) (a b c : X)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : V (S b) - V a = V (S c) - V c)
    (hb : V (S c) - V b = V (S a) - V a)
    (hc : V (S a) - V c = V (S b) - V b) :
    let T := S * Equiv.swap a b * Equiv.swap b c
    let U := Equiv.swap b c * Equiv.swap a b
    ∀ x, V (T x) - V x = V (S (U x)) - V (U x) := by
  dsimp
  intro x
  by_cases hxa : x = a
  · subst x
    simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hab, hac,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc] using ha
  by_cases hxb : x = b
  · subst x
    simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hab, hac, hbc,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc] using hb
  by_cases hxc : x = c
  · subst x
    simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hab, hac, hbc,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc] using hc
  · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, hxa, hxb, hxc]

private theorem splice_labels {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Fintype E] [Fintype Q] (N : AddSubgroup E) [Fintype N] [DecidableEq N] (r : RCycle N) (rQ : RStar Q)
    (c : ColumnChart Q rQ) (s : Q → E) (hsum : s rQ.a + s rQ.c = s rQ.b)
    (v : N) :
    let V := vertices N rQ c s
    let S := oldSuccessor r c.k
    let U := Equiv.swap (.inl v) (.inr (1, kernelF r v)) *
      Equiv.swap (.inr (0, 0)) (.inl v)
    ∀ x, V (spliceSuccessor r c.k v x) - V x = V (S (U x)) - V (U x) := by
  classical
  dsimp
  let X := N ⊕ (Fin (c.k + 3) × N)
  let a : X := .inr (0, 0)
  let b : X := .inl v
  let d : X := .inr (1, kernelF r v)
  have had : a ≠ d := by
    intro he
    have h := congrArg (fun x : X => match x with | .inl _ => (0 : Fin (c.k + 3)) | .inr y => y.1) he
    simpa [a, d] using h
  have hrot1 : finRotate (c.k + 3) (1 : Fin (c.k + 3)) = 2 := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · simp [Nat.mod_eq_of_lt (show (2 : ℕ) < c.k + 3 by omega)]
    · intro he
      have h := congrArg Fin.val he
      simp at h
  apply three_cut_labels (vertices N rQ c s) (oldSuccessor r c.k)
    a b d (by simp [a, b]) had (by simp [b, d])
  all_goals
    simp only [a, b, d, oldSuccessor, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr, rowLift_apply, vertices]
    simp only [rowEdge_formula r c.even_k, Fin.val_zero, Fin.val_one,
      one_ne_zero, ↓reduceIte, Equiv.symm_apply_apply, kernelF_zero,
      finRotate_apply_zero, hrot1]
    simp only [c.first, c.second, c.third, r.successor_zero, AddSubgroup.coe_zero,
      add_zero, sub_zero]
    have hFv : (kernelF r v).val = v.val - (r.successor v).val := by
      rw [kernelF_apply, AddSubgroup.coe_sub]
    rw [← hsum]
    try rw [hFv]
    abel

private theorem bijOn_complement {X : Type*} (f : Equiv.Perm X) (z : X)
    (hz : f z = z) : Set.BijOn f {x | x ≠ z} {x | x ≠ z} := by
  refine ⟨?_, f.injective.injOn, ?_⟩
  · intro x hx he
    exact hx (f.injective (he.trans hz.symm))
  · intro y hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    intro he
    have h := congrArg f he
    rw [f.apply_symm_apply, hz] at h
    exact hy h

private noncomputable def transportCycle {G H : Type*} [AddCommGroup G]
    [AddCommGroup H] [Fintype G] [Fintype H] (e : G ≃+ H) (r : RCycle G) :
    RCycle H where
  successor := e.toEquiv.permCongr r.successor
  successor_zero := by
    change e (r.successor (e.symm 0)) = 0
    rw [e.symm.map_zero, r.successor_zero, e.map_zero]
  nonzero_cycle := by
    have hz : e.toEquiv.permCongr r.successor 0 = 0 := by
      change e (r.successor (e.symm 0)) = 0
      rw [e.symm.map_zero, r.successor_zero, e.map_zero]
    refine ⟨bijOn_complement _ 0 hz, ?_⟩
    intro x hx y hy
    have hxn : e.symm x ≠ 0 := by simpa using hx
    have hyn : e.symm y ≠ 0 := by simpa using hy
    simpa using
      (D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.same_cycle_perm_congr
        e.toEquiv r.successor (e.symm x) (e.symm y)).mpr
        (r.nonzero_cycle.2 hxn hyn)
  difference := e.toEquiv.permCongr r.difference
  difference_spec := by
    intro x
    change e (r.difference (e.symm x)) = e (r.successor (e.symm x)) - x
    rw [r.difference_spec, map_sub, e.apply_symm_apply]

/-- An R-cycle on the kernel and an even R-star quotient construct an R-cycle on
any finite additive abelian extension. No additive section or R-star kernel is used. -/
theorem nonsplit_extension_r_cycle {E : Type*} [AddCommGroup E] [Fintype E]
    (N : AddSubgroup E) (r : RCycle N) (rQ : RStar (E ⧸ N)) : Nonempty (RCycle E) := by
  classical
  letI : Fintype N := Fintype.ofFinite N
  letI : Fintype (E ⧸ N) := Fintype.ofFinite (E ⧸ N)
  let π := QuotientAddGroup.mk' N
  have hπ : Surjective π := QuotientAddGroup.mk'_surjective N
  have hker : π.ker = N := QuotientAddGroup.ker_mk' N
  by_cases hv : ∃ v : N, v ≠ 0
  · obtain ⟨v, hv⟩ := hv
    obtain ⟨c⟩ := column_chart rQ
    obtain ⟨s, hs, hsum⟩ := compatible_section π hπ rQ
    let X := N ⊕ (Fin (c.k + 3) × N)
    let z : X := .inl 0
    let V : X ≃ E := Equiv.ofBijective (vertices N rQ c s)
      (vertices_bijective N π hker rQ c s hs)
    let T := spliceSuccessor r c.k v
    let L : X → E := fun x => V (oldSuccessor r c.k x) - V x
    have hL : Injective L := old_label_injective N π hker r rQ c s hs
    let oldD : Equiv.Perm X := Equiv.ofBijective (V.symm ∘ L)
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨V.symm.injective.comp hL, rfl⟩)
    let U : Equiv.Perm X := Equiv.swap (.inl v) (.inr (1, kernelF r v)) *
      Equiv.swap (.inr (0, 0)) (.inl v)
    let S : Equiv.Perm E := V.permCongr T
    let D : Equiv.Perm E := V.permCongr (U.trans oldD)
    have hVz : V z = 0 := by simp [V, z, vertices]
    have hS0 : S 0 = 0 := by
      rw [← hVz]
      change V (T (V.symm (V z))) = V z
      rw [V.symm_apply_apply]
      exact congrArg V (splice_zero r c.k v hv)
    have hcycle : S.IsCycleOn {x | x ≠ 0} := by
      refine ⟨bijOn_complement S 0 hS0, ?_⟩
      intro x hx y hy
      have hxn : V.symm x ≠ z := by
        intro he
        have h := congrArg V he
        rw [V.apply_symm_apply, hVz] at h
        exact hx h
      have hyn : V.symm y ≠ z := by
        intro he
        have h := congrArg V he
        rw [V.apply_symm_apply, hVz] at h
        exact hy h
      simpa only [V.apply_symm_apply] using
        (D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.same_cycle_perm_congr
          V T (V.symm x) (V.symm y)).mpr ((splice_cycle r c.k v hv).2 hxn hyn)
    have hD : ∀ x, D x = S x - x := by
      intro x
      change V (oldD (U (V.symm x))) = V (T (V.symm x)) - x
      change V (V.symm (L (U (V.symm x)))) = _
      rw [V.apply_symm_apply]
      have h : V (T (V.symm x)) - V (V.symm x) = L (U (V.symm x)) :=
        splice_labels N r rQ c s hsum v (V.symm x)
      simpa only [V.apply_symm_apply] using h.symm
    exact ⟨{
      successor := S
      successor_zero := hS0
      nonzero_cycle := hcycle
      difference := D
      difference_spec := hD }⟩
  · have hN : ∀ h : N, h = 0 := by simpa using hv
    have hinj : Injective π := by
      intro x y hxy
      have hm : x - y ∈ N := by
        rw [← hker]
        change π (x - y) = 0
        simp [map_sub, hxy]
      have hh := congrArg (fun h : N => h.val) (hN ⟨x - y, hm⟩)
      exact sub_eq_zero.mp hh
    let e : E ≃+ E ⧸ N := AddEquiv.ofBijective π ⟨hinj, hπ⟩
    exact ⟨transportCycle e.symm rQ.toRCycle⟩

end D5.S3.FiniteGroups.HeadleyExtension
