/- GID: D5/S3/Combinatorics/Permutation/Verkama62EarGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62EarGeometry
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Anchored induced two-vertex ears have the precise northeast order geometry. -/

import D5.S3.Combinatorics.Permutation.Verkama62Graph

/-! Connectivity of the old stage after either attachment is deleted fixes the ear's orientation. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

private theorem reachable_invariant {V : Type*} {G : SimpleGraph V} (P : V → Prop)
    (hedge : ∀ a b, G.Adj a b → (P a ↔ P b)) {a b : V} (h : G.Reachable a b) :
    P a ↔ P b := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => rfl
  | cons hadj tail ih => exact (hedge _ _ hadj).trans ih

private theorem uniform_side {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Set (Fin n))
    (u : Fin n) (hu : u ∉ S)
    (hconn : ((valueGraph π).induce (π '' S)).Connected)
    (hnon : ∀ i ∈ S, ¬ (valueGraph π).Adj (π u) (π i)) :
    (∀ i ∈ S, i < u ∧ π i < π u) ∨
      (∀ i ∈ S, u < i ∧ π u < π i) := by
  have hsplit (i : Fin n) (hi : i ∈ S) :
      (i < u ∧ π i < π u) ∨ (u < i ∧ π u < π i) := by
    have hne : i ≠ u := by intro h; exact hu (h ▸ hi)
    have hvne := π.injective.ne hne
    have hn := hnon i hi
    rw [value_adj] at hn
    simp only [Equiv.symm_apply_apply] at hn
    omega
  let H := (valueGraph π).induce (π '' S)
  have hposmem (v : {v // v ∈ π '' S}) : π.symm v.val ∈ S := by
    obtain ⟨i, hi, heq⟩ := v.property
    simpa [← heq] using hi
  have hedge (a b : {v // v ∈ π '' S}) (hadj : H.Adj a b) :
      π.symm a.val < u ↔ π.symm b.val < u := by
    have ha := hsplit _ (hposmem a)
    have hb := hsplit _ (hposmem b)
    simp only [Equiv.apply_symm_apply] at ha hb
    change (valueGraph π).Adj a.val b.val at hadj
    rw [value_adj] at hadj
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
  obtain ⟨root⟩ := hconn.nonempty
  rcases hsplit _ (hposmem root) with hroot | hroot
  · left
    intro i hi
    let v : {v // v ∈ π '' S} := ⟨π i, i, hi, rfl⟩
    have hsame := reachable_invariant (fun a => π.symm a.val < u) hedge (hconn root v)
    have hbelow : i < u := by simpa [v] using hsame.mp hroot.1
    rcases hsplit i hi with h | h
    · exact h
    · omega
  · right
    intro i hi
    let v : {v // v ∈ π '' S} := ⟨π i, i, hi, rfl⟩
    have hsame := reachable_invariant (fun a => π.symm a.val < u) hedge (hconn root v)
    have habove : ¬ i < u := by
      intro h
      have : π.symm v.val < u := by simpa [v] using h
      have := hsame.mpr this
      omega
    rcases hsplit i hi with h | h
    · omega
    · exact h

/-- An induced three-edge ear with distinct old attachments. -/
structure PairEar {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) where
  u : Fin n
  v : Fin n
  x : Fin n
  y : Fin n
  hx : x ∈ S
  hy : y ∈ S
  hu : u ∉ S
  hv : v ∉ S
  hxy : x ≠ y
  huv : u < v
  hvu : π v < π u
  edge_u : (valueGraph π).Adj (π u) (π x)
  edge_v : (valueGraph π).Adj (π v) (π y)
  unique_u : ∀ i ∈ S, i ≠ x → ¬ (valueGraph π).Adj (π u) (π i)
  unique_v : ∀ i ∈ S, i ≠ y → ¬ (valueGraph π).Adj (π v) (π i)

/-- An induced two-vertex ear of an anchored stage has the exact northeast
    geometry. No avoidance or triangle-freeness assumption is used. -/
theorem PairEar.to_double {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (e : PairEar π S) (hsize : 3 ≤ S.card)
    (hdelete : ∀ w ∈ S, ((valueGraph π).induce (π '' ((S.erase w : Finset _) : Set _))).Connected)
    (z : Fin n) (hz : z.val = 0) (hanchor : z ∈ S) :
    ∃ d : Double π S, d.u = e.u ∧ d.v = e.v := by
  have hsides_u := uniform_side π ((S.erase e.x : Finset _) : Set _) e.u
    (by intro hi; exact e.hu (Finset.mem_of_mem_erase hi)) (hdelete e.x e.hx) (by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      exact e.unique_u i hi'.2 hi'.1)
  have hsides_v := uniform_side π ((S.erase e.y : Finset _) : Set _) e.v
    (by intro hi; exact e.hv (Finset.mem_of_mem_erase hi)) (hdelete e.y e.hy) (by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      exact e.unique_v i hi'.2 hi'.1)
  have hpair := Finset.card_le_two (a := e.x) (b := e.y)
  obtain ⟨w, hw, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {e.x, e.y}) (t := S) (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  have hwx : w ∈ S.erase e.x := Finset.mem_erase.mpr ⟨hnot.1, hw⟩
  have hwy : w ∈ S.erase e.y := Finset.mem_erase.mpr ⟨hnot.2, hw⟩
  have hyx : e.y ∈ S.erase e.x := Finset.mem_erase.mpr ⟨e.hxy.symm, e.hy⟩
  have hxy : e.x ∈ S.erase e.y := Finset.mem_erase.mpr ⟨e.hxy, e.hx⟩
  have heu := e.edge_u
  have hev := e.edge_v
  rw [value_adj] at heu hev
  simp only [Equiv.symm_apply_apply] at heu hev
  have huv := e.huv
  have hvu := e.hvu
  rcases hsides_u with hsu | hnu <;> rcases hsides_v with hsv | hnv
  · have hy := hsu e.y hyx
    have hx := hsv e.x hxy
    have hux : e.u < e.x := by rcases heu with heu | heu <;> omega
    have hvy : π e.v < π e.y := by rcases hev with hev | hev <;> omega
    refine ⟨{
      u := e.u, v := e.v, x := e.x, y := e.y,
      hx := e.hx, hy := e.hy, hu := e.hu, hv := e.hv, hxy := e.hxy,
      hux := hux, hxv := hx.1, hvy := hvy, hyu := hy.2,
      old_left := ?_, old_below := ?_ }, rfl, rfl⟩
    · intro i hi hne
      exact (hsu i (Finset.mem_erase.mpr ⟨hne, hi⟩)).1
    · intro i hi hne
      exact (hsv i (Finset.mem_erase.mpr ⟨hne, hi⟩)).2
  · have hwu := hsu w hwx
    have hwv := hnv w hwy
    omega
  · have hwu := hnu w hwx
    have hwv := hsv w hwy
    omega
  · have hx := hnv e.x hxy
    have hzleft : e.u < z := by
      by_cases hzx : z = e.x
      · rw [hzx]; exact huv.trans hx.1
      · exact (hnu z (Finset.mem_erase.mpr ⟨hzx, hanchor⟩)).1
    have : e.u.val < z.val := hzleft
    omega

private theorem boundary_pair {V : Type*} (G : SimpleGraph V) (S : Set V)
    (a b w : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hw : w ∉ S)
    (hc : G.Connected) (hd : ∀ x, (G.induce {x}ᶜ).Connected) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ∃ u ∉ S, ∃ v ∉ S, G.Adj u x ∧ G.Adj v y := by
  classical
  obtain ⟨p⟩ := hc a w
  obtain ⟨d, _, hx, hu⟩ := p.exists_boundary_dart S ha hw
  let r := if a = d.fst then b else a
  have hr : r ∈ S := by dsimp [r]; split <;> assumption
  have hrx : r ≠ d.fst := by
    dsimp [r]
    split_ifs with h
    · exact h ▸ hab.symm
    · exact h
  have hwx : w ≠ d.fst := by intro h; exact hw (h ▸ hx)
  let r' : {v // v ∈ ({d.fst}ᶜ : Set V)} := ⟨r, by simpa using hrx⟩
  let w' : {v // v ∈ ({d.fst}ᶜ : Set V)} := ⟨w, by simpa using hwx⟩
  obtain ⟨q⟩ := hd d.fst r' w'
  obtain ⟨e, _, hy, hv⟩ := q.exists_boundary_dart {v | v.val ∈ S} hr hw
  have hyx : e.fst.val ≠ d.fst := by
    intro h; exact e.fst.property (Set.mem_singleton_iff.mpr h)
  exact ⟨d.fst, hx, e.fst.val, hy, hyx.symm, d.snd, hu, e.snd.val, hv,
    d.adj.symm, e.adj.symm⟩

/-- Every proper anchored stage has either a singleton with two old neighbours
    or a northeast two-vertex ear. -/
theorem anchored_extension {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hsize : 3 ≤ S.card)
    (hdelete : ∀ w ∈ S, ((valueGraph π).induce (π '' ((S.erase w : Finset _) : Set _))).Connected)
    (z b : Fin n) (hz : z.val = 0) (hb : (π b).val = 0)
    (hzb : z ≠ b) (hzS : z ∈ S) (hbS : b ∈ S)
    (hproper : S ≠ Finset.univ)
    (hc : (valueGraph π).Connected)
    (hd : ∀ v, ((valueGraph π).induce {v}ᶜ).Connected) :
    (∃ u ∉ S, 2 ≤ (neighbours π S u).card) ∨ Nonempty (Double π S) := by
  classical
  by_cases hsingle : ∃ u ∉ S, 2 ≤ (neighbours π S u).card
  · exact Or.inl hsingle
  right
  have hsmall (u : Fin n) (hu : u ∉ S) : (neighbours π S u).card ≤ 1 := by
    by_contra h
    exact hsingle ⟨u, hu, by omega⟩
  have hmem (u i : Fin n) : i ∈ neighbours π S u ↔
      i ∈ S ∧ (valueGraph π).Adj (π u) (π i) := by
    simp only [neighbours, Finset.mem_filter, value_adj, Equiv.symm_apply_apply]
    tauto
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ S := by
    by_contra h
    push_neg at h
    exact hproper (Finset.eq_univ_of_forall h)
  have hw' : π w ∉ π '' (S : Set (Fin n)) := by
    rintro ⟨i, hi, heq⟩
    exact hw (π.injective heq ▸ hi)
  obtain ⟨X, hX, Y, hY, hXY, U, hU, V, hV, hUX, hVY⟩ :=
    boundary_pair (valueGraph π) (π '' (S : Set (Fin n))) (π z) (π b) (π w)
      ⟨z, hzS, rfl⟩ ⟨b, hbS, rfl⟩ (π.injective.ne hzb) hw' hc hd
  obtain ⟨x, hx, rfl⟩ := hX
  obtain ⟨y, hy, rfl⟩ := hY
  let u := π.symm U
  let v := π.symm V
  have hu : u ∉ S := by intro h; exact hU ⟨u, h, π.apply_symm_apply U⟩
  have hv : v ∉ S := by intro h; exact hV ⟨v, h, π.apply_symm_apply V⟩
  have hux : (valueGraph π).Adj (π u) (π x) := by simpa [u] using hUX
  have hvy : (valueGraph π).Adj (π v) (π y) := by simpa [v] using hVY
  have hxy : x ≠ y := fun h => hXY (congrArg π h)
  have unique (q a : Fin n) (hq : q ∉ S) (ha : a ∈ S)
      (he : (valueGraph π).Adj (π q) (π a)) :
      ∀ i ∈ S, i ≠ a → ¬ (valueGraph π).Adj (π q) (π i) := by
    intro i hi hia hei
    have hsub := Finset.card_le_one.mp (hsmall q hq)
    exact hia (hsub i ((hmem q i).mpr ⟨hi, hei⟩) a ((hmem q a).mpr ⟨ha, he⟩))
  have side (q a : Fin n) (hq : q ∉ S) (ha : a ∈ S)
      (he : (valueGraph π).Adj (π q) (π a)) :
      ∀ i ∈ S, i ≠ a → i < q ∧ π i < π q := by
    have hs := uniform_side π ((S.erase a : Finset _) : Set _) q
      (by intro hi; exact hq (Finset.mem_of_mem_erase hi)) (hdelete a ha) (by
        intro i hi
        exact unique q a hq ha he i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
    rcases hs with hs | hs
    · intro i hi hia
      exact hs i (Finset.mem_erase.mpr ⟨hia, hi⟩)
    · exfalso
      by_cases hza : z = a
      · have hba : b ≠ a := by intro h; exact hzb (hza.trans h.symm)
        have := (hs b (Finset.mem_erase.mpr ⟨hba, hbS⟩)).2
        change (π q).val < (π b).val at this
        omega
      · have := (hs z (Finset.mem_erase.mpr ⟨hza, hzS⟩)).1
        change q.val < z.val at this
        omega
  have hsy := side u x hu hx hux y hy hxy.symm
  have hsx := side v y hv hy hvy x hx hxy
  have eu := hux
  have ev := hvy
  rw [value_adj] at eu ev
  simp only [Equiv.symm_apply_apply] at eu ev
  have mk (q r a c : Fin n) (hq : q ∉ S) (hr : r ∉ S)
      (ha : a ∈ S) (hc' : c ∈ S) (hac : a ≠ c)
      (hqa : (valueGraph π).Adj (π q) (π a))
      (hrc : (valueGraph π).Adj (π r) (π c))
      (hqr : q < r) (hval : π r < π q) : Nonempty (Double π S) := by
    let e : PairEar π S := {
      u := q, v := r, x := a, y := c, hx := ha, hy := hc', hu := hq, hv := hr,
      hxy := hac, huv := hqr, hvu := hval, edge_u := hqa, edge_v := hrc,
      unique_u := unique q a hq ha hqa, unique_v := unique r c hr hc' hrc }
    obtain ⟨d, _, _⟩ := e.to_double hsize hdelete z hz hzS
    exact ⟨d⟩
  rcases eu with eu | eu <;> rcases ev with ev | ev
  · omega
  · exact mk v u y x hv hu hy hx hxy.symm hvy hux
      (ev.2.trans hsy.1) (eu.1.trans hsx.2)
  · exact mk u v x y hu hv hx hy hxy hux hvy
      (eu.2.trans hsx.1) (ev.1.trans hsy.2)
  · omega

end D5.S3.Combinatorics.Permutation.Verkama62Local
