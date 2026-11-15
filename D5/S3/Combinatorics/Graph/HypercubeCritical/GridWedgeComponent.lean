/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming, mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: A block grid construction of balanced regular induced components of square-dimensional Boolean cubes. -/


import D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSupport

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeComponent

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.Hypercube

private def upperPoint {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd) : support hd :=
  ⟨upperVertex hd p, Or.inl (upperVertex_pattern hd p)⟩

private theorem upper_reachable_one_row {d : ℕ} (hd : 2 ≤ d)
    (side : Bool) (u : {u : Fin d // u ≠ zeroCoord hd})
    (f g : {i : Fin d // i ≠ markedRow hd side} → Fin d)
    (i : {i : Fin d // i ≠ markedRow hd side})
    (hfg : ∀ k, k ≠ i → f k = g k) :
    (componentGraph hd).Reachable (upperPoint hd ⟨side, u, f⟩)
      (upperPoint hd ⟨side, u, g⟩) := by
  let p : UpperData hd := ⟨side, u, f⟩
  let q : UpperData hd := ⟨side, u, g⟩
  have hp : flip (upperVertex hd p) i.val (f i) ∈ support hd :=
    (upper_flip_other_iff hd p i.val i.property (f i)).mpr rfl
  have hq : flip (upperVertex hd q) i.val (g i) ∈ support hd :=
    (upper_flip_other_iff hd q i.val i.property (g i)).mpr rfl
  have he : flip (upperVertex hd p) i.val (f i) =
      flip (upperVertex hd q) i.val (g i) := by
    apply gridRow_ext
    intro k
    by_cases hki : k = i.val
    · subst k
      have hfp : upperVertex hd p (finProdFinEquiv (i.val, f i)) = true := by
        simp [upperVertex, p, i.property]
      have hfq : upperVertex hd q (finProdFinEquiv (i.val, g i)) = true := by
        simp [upperVertex, q, i.property]
      simp [gridRow_flip_same, hfp, hfq, gridRow_upperVertex, p, q, i.property]
    · rw [gridRow_flip_other _ _ _ k hki, gridRow_flip_other _ _ _ k hki]
      by_cases hks : k = markedRow hd side
      · simp [gridRow_upperVertex, p, q, hks]
      · have hne : (⟨k, hks⟩ : {i : Fin d // i ≠ markedRow hd side}) ≠ i := by
          intro h
          exact hki (congrArg Subtype.val h)
        simp [gridRow_upperVertex, p, q, hks, hfg _ hne]
  let y : support hd := ⟨flip (upperVertex hd p) i.val (f i), hp⟩
  have hay : (componentGraph hd).Adj (upperPoint hd p) y := flip_adj _ _ _
  have hby : (componentGraph hd).Adj (upperPoint hd q) y := by
    change (hypercube (d * d)).Adj (upperVertex hd q) (flip (upperVertex hd p) _ _)
    rw [he]
    exact flip_adj _ _ _
  exact hay.reachable.trans hby.reachable.symm

private theorem upper_reachable_same_pair {d : ℕ} (hd : 2 ≤ d)
    (side : Bool) (u : {u : Fin d // u ≠ zeroCoord hd})
    (f g : {i : Fin d // i ≠ markedRow hd side} → Fin d) :
    (componentGraph hd).Reachable (upperPoint hd ⟨side, u, f⟩)
      (upperPoint hd ⟨side, u, g⟩) := by
  have aux (s : Finset {i : Fin d // i ≠ markedRow hd side}) :
      ∀ f g : {i : Fin d // i ≠ markedRow hd side} → Fin d,
        (∀ i ∉ s, f i = g i) →
        (componentGraph hd).Reachable (upperPoint hd ⟨side, u, f⟩)
          (upperPoint hd ⟨side, u, g⟩) := by
    induction s using Finset.induction_on with
    | empty =>
        intro f g h
        have he : f = g := funext fun i => h i (by simp)
        subst g
        exact SimpleGraph.Reachable.rfl
    | @insert i s hi ih =>
        intro f g h
        let f' := Function.update f i (g i)
        have hstep := upper_reachable_one_row hd side u f f' i
          (fun k hk => by simp [f', Function.update_of_ne hk])
        apply hstep.trans (ih f' g ?_)
        intro k hk
        by_cases hki : k = i
        · simp [f', hki]
        · simpa [f', Function.update_of_ne hki] using h k (by simp [hki, hk])
  exact aux Finset.univ f g (by simp)

private def oneColumn {d : ℕ} (hd : 2 ≤ d) :
    {u : Fin d // u ≠ zeroCoord hd} :=
  ⟨⟨1, by omega⟩, by intro h; have := congrArg Fin.val h; simp [zeroCoord] at this⟩

private def canonicalUpper {d : ℕ} (hd : 2 ≤ d) (side : Bool)
    (u : {u : Fin d // u ≠ zeroCoord hd}) : UpperData hd :=
  ⟨side, u, fun _ => (oneColumn hd).val⟩

private theorem upper_delete_ordinary_row {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd)
    (i : Fin d) :
    gridRow (flip (upperVertex hd p) (markedRow hd p.1) p.2.1.val) i =
      if h : i = markedRow hd p.1 then {zeroCoord hd} else {p.2.2 ⟨i, h⟩} := by
  by_cases hi : i = markedRow hd p.1
  · subst i
    have hb : upperVertex hd p (finProdFinEquiv (markedRow hd p.1, p.2.1.val)) =
        true := by simp [upperVertex]
    rw [gridRow_flip_same, if_pos hb]
    simp only [gridRow_upperVertex, dite_eq_left rfl]
    ext k
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    have := p.2.1.property
    aesop
  · rw [gridRow_flip_other _ _ _ i hi]
    simp [gridRow_upperVertex, hi]

private theorem canonical_upper_reachable {d : ℕ} (hd : 2 ≤ d) (side : Bool)
    (u v : {u : Fin d // u ≠ zeroCoord hd}) :
    (componentGraph hd).Reachable (upperPoint hd (canonicalUpper hd side u))
      (upperPoint hd (canonicalUpper hd side v)) := by
  let p := canonicalUpper hd side u
  let q := canonicalUpper hd side v
  have hp : flip (upperVertex hd p) (markedRow hd side) u.val ∈ support hd := by
    apply (upper_flip_ordinary_iff hd p).mpr
    exact bit_false_of_singleton
      (by simp [p, canonicalUpper, gridRow_upperVertex, markedRow_not_ne])
      (Ne.symm (oneColumn hd).property)
  have he : flip (upperVertex hd p) (markedRow hd side) u.val =
      flip (upperVertex hd q) (markedRow hd side) v.val := by
    apply gridRow_ext
    intro i
    have h1 := upper_delete_ordinary_row hd p i
    have h2 := upper_delete_ordinary_row hd q i
    simpa [p, q, canonicalUpper] using h1.trans h2.symm
  let y : support hd := ⟨flip (upperVertex hd p) (markedRow hd side) u.val, hp⟩
  have hay : (componentGraph hd).Adj (upperPoint hd p) y := flip_adj _ _ _
  have hby : (componentGraph hd).Adj (upperPoint hd q) y := by
    change (hypercube (d * d)).Adj (upperVertex hd q)
      (flip (upperVertex hd p) (markedRow hd side) u.val)
    rw [he]
    exact flip_adj _ _ _
  exact hay.reachable.trans hby.reachable.symm

private theorem upper_reachable_same_side {d : ℕ} (hd : 2 ≤ d) (side : Bool)
    (u v : {u : Fin d // u ≠ zeroCoord hd})
    (f g : {i : Fin d // i ≠ markedRow hd side} → Fin d) :
    (componentGraph hd).Reachable (upperPoint hd ⟨side, u, f⟩)
      (upperPoint hd ⟨side, v, g⟩) := by
  exact (upper_reachable_same_pair hd side u f (fun _ => (oneColumn hd).val)).trans
    ((canonical_upper_reachable hd side u v).trans
      (upper_reachable_same_pair hd side v (fun _ => (oneColumn hd).val) g))

private theorem upper_reachable_two_sides {d : ℕ} (hd : 2 ≤ d) :
    (componentGraph hd).Reachable
      (upperPoint hd (canonicalUpper hd false (oneColumn hd)))
      (upperPoint hd (canonicalUpper hd true (oneColumn hd))) := by
  let p := canonicalUpper hd false (oneColumn hd)
  let g : {i : Fin d // i ≠ markedRow hd true} → Fin d :=
    fun i => if i.val = markedRow hd false then zeroCoord hd else (oneColumn hd).val
  let q : UpperData hd := ⟨true, oneColumn hd, g⟩
  have hne : markedRow hd true ≠ markedRow hd false := markedRow_not_ne hd false
  have hp : flip (upperVertex hd p) (markedRow hd false) (oneColumn hd).val ∈
      support hd := by
    apply (upper_flip_ordinary_iff hd p).mpr
    exact bit_false_of_singleton
      (by simp [p, canonicalUpper, gridRow_upperVertex, hne])
      (Ne.symm (oneColumn hd).property)
  have he : flip (upperVertex hd p) (markedRow hd false) (oneColumn hd).val =
      flip (upperVertex hd q) (markedRow hd true) (zeroCoord hd) := by
    apply gridRow_ext
    intro i
    have h1 := upper_delete_ordinary_row hd p i
    change gridRow (flip (upperVertex hd p) (markedRow hd false) (oneColumn hd).val) i =
      (if h : i = markedRow hd false then {zeroCoord hd}
       else {(oneColumn hd).val}) at h1
    rw [h1]
    by_cases hi : i = markedRow hd true
    · subst i
      have hb : upperVertex hd q (finProdFinEquiv (markedRow hd true, zeroCoord hd)) =
          true := by simp [q, upperVertex]
      rw [gridRow_flip_same, if_pos hb]
      simp [p, q, canonicalUpper, gridRow_upperVertex,
        hne, Ne.symm (oneColumn hd).property]
    · rw [gridRow_flip_other _ _ _ i hi]
      by_cases hi' : i = markedRow hd false <;>
        simp [p, q, canonicalUpper, gridRow_upperVertex, hi, hi', g, Ne.symm hne]
  let y : support hd :=
    ⟨flip (upperVertex hd p) (markedRow hd false) (oneColumn hd).val, hp⟩
  have hay : (componentGraph hd).Adj (upperPoint hd p) y := flip_adj _ _ _
  have hby : (componentGraph hd).Adj (upperPoint hd q) y := by
    change (hypercube (d * d)).Adj (upperVertex hd q)
      (flip (upperVertex hd p) (markedRow hd false) (oneColumn hd).val)
    rw [he]
    exact flip_adj _ _ _
  exact (hay.reachable.trans hby.reachable.symm).trans
    (upper_reachable_same_pair hd true (oneColumn hd) g (fun _ => (oneColumn hd).val))

private theorem upper_reachable {d : ℕ} (hd : 2 ≤ d) (p q : UpperData hd) :
    (componentGraph hd).Reachable (upperPoint hd p) (upperPoint hd q) := by
  obtain ⟨a, u, f⟩ := p
  obtain ⟨b, v, g⟩ := q
  have hleft := upper_reachable_same_side hd a u (oneColumn hd) f
    (fun _ => (oneColumn hd).val)
  have hright := upper_reachable_same_side hd b (oneColumn hd) v
    (fun _ => (oneColumn hd).val) g
  apply hleft.trans
  apply SimpleGraph.Reachable.trans (v := upperPoint hd (canonicalUpper hd b (oneColumn hd)))
    (hvw := hright)
  cases a <;> cases b
  · exact SimpleGraph.Reachable.rfl
  · exact upper_reachable_two_sides hd
  · exact (upper_reachable_two_sides hd).symm
  · exact SimpleGraph.Reachable.rfl

private theorem support_reachable_upper {d : ℕ} (hd : 2 ≤ d) (x : support hd) :
    ∃ p : UpperData hd, (componentGraph hd).Reachable x (upperPoint hd p) := by
  rcases x.property with h | h | h
  · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ((upperPattern_iff_mem hd x.val).mp h)
    refine ⟨p, ?_⟩
    have he : upperPoint hd p = x := Subtype.ext hp
    rw [he]
  · obtain ⟨side, missing, u, hm, hu, hr, he, hs⟩ := h
    have hy := (lowerDouble_flip_iff hd x.val side missing u hm hu hr he hs
      missing (zeroCoord hd)).mpr rfl
    have hw : gridWeight x.val = d :=
      lowerDoublePattern_weight hd ⟨side, missing, u, hm, hu, hr, he, hs⟩
    have hup := (support_flip_lower_iff hd hw missing (zeroCoord hd)).mp hy
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ((upperPattern_iff_mem hd _).mp hup)
    refine ⟨p, ?_⟩
    apply SimpleGraph.Adj.reachable
    change (hypercube (d * d)).Adj x.val (upperVertex hd p)
    rw [hp]
    exact flip_adj _ _ _
  · have hw := lowerTransversalPattern_weight hd h
    have hc : 0 < Fintype.card (LegalData hd x.val) := by
      rw [lowerTransversal_card_legal hd h]
      omega
    obtain ⟨p⟩ := Fintype.card_pos_iff.mp hc
    have hup := (support_flip_lower_iff hd hw p.1 p.2.val).mp p.2.property
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp ((upperPattern_iff_mem hd _).mp hup)
    refine ⟨q, ?_⟩
    apply SimpleGraph.Adj.reachable
    change (hypercube (d * d)).Adj x.val (upperVertex hd q)
    rw [hq]
    exact flip_adj _ _ _

private theorem component_connected {d : ℕ} (hd : 2 ≤ d) :
    (componentGraph hd).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  let p := canonicalUpper hd false (oneColumn hd)
  refine ⟨upperPoint hd p, ?_⟩
  intro x
  obtain ⟨q, hq⟩ := support_reachable_upper hd x
  exact (upper_reachable hd p q).trans hq.symm

private def rowPrefix {d : ℕ} (x : Vertex d) (i : Fin d) : ℕ :=
  ∑ k ∈ Finset.Iio i, (gridRow x k).card

/-- Number of occupied coordinates preceding `(i,j)` in row-major order. -/
def gridPrefix {d : ℕ} (x : Vertex d) (i j : Fin d) : ℕ :=
  rowPrefix x i + ((gridRow x i).filter fun k => k < j).card

/-- Explicit TRUE-prefix signing; the sign is unchanged by reversing its edge. -/
def gridEdgeSign {d : ℕ} (x : Vertex d) (i j : Fin d) : ℤ :=
  (-1) ^ gridPrefix x i j

private def switchExponent {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) : ℕ :=
  (∑ i : Fin d, if gridRow x i = ∅ then rowPrefix x i else 0) +
    if lowerTransversalPattern hd x ∧
      x (finProdFinEquiv (markedRow hd false, zeroCoord hd)) = true then 1 else 0

private def switchSign {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) : ℤ :=
  (-1) ^ switchExponent hd x

private theorem switchSign_unit {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) :
    switchSign hd x = 1 ∨ switchSign hd x = -1 := by
  rw [switchSign, neg_one_pow_eq_ite]
  split_ifs <;> simp

private theorem gridPrefix_flip {d : ℕ} (x : Vertex d) (i j : Fin d) :
    gridPrefix (flip x i j) i j = gridPrefix x i j := by
  have hp : rowPrefix (flip x i j) i = rowPrefix x i := by
    unfold rowPrefix
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg Finset.card
      (gridRow_flip_other x i j k (ne_of_lt (Finset.mem_Iio.mp hk)))
  have hf : ((gridRow (flip x i j) i).filter fun k => k < j) =
      ((gridRow x i).filter fun k => k < j) := by
    ext k
    by_cases hk : k < j
    · have hne : k ≠ j := ne_of_lt hk
      by_cases hb : x (finProdFinEquiv (i, j)) = true <;>
        simp [gridRow_flip_same, hb, hk, hne]
    · simp [hk]
  simp only [gridPrefix, hp, hf]

private theorem switchSign_upper {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : upperPattern hd x) : switchSign hd x = 1 := by
  have hn (i : Fin d) : gridRow x i ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp (upperPattern_row_nonempty hd hx i)
  have ht : ¬ lowerTransversalPattern hd x := by
    intro ht
    have hu := upperPattern_weight hd hx
    have hl := lowerTransversalPattern_weight hd ht
    omega
  simp [switchSign, switchExponent, hn, ht]

private theorem switchSign_lowerDouble {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (side : Bool) (missing u : Fin d)
    (hmissing : missing ≠ markedRow hd side) (hu : u ≠ zeroCoord hd)
    (hrow : gridRow x (markedRow hd side) = {zeroCoord hd, u})
    (hempty : gridRow x missing = ∅)
    (hsingle : singletonRowsOutside x {markedRow hd side, missing}) :
    switchSign hd x = (-1 : ℤ) ^ rowPrefix x missing := by
  have he (i : Fin d) : gridRow x i = ∅ ↔ i = missing := by
    constructor
    · intro hi
      by_contra him
      by_cases his : i = markedRow hd side
      · subst i
        simp [hrow] at hi
      · obtain ⟨j, hj⟩ := hsingle i (by simp [his, him])
        simp [hj] at hi
    · rintro rfl
      exact hempty
  have ht : ¬ lowerTransversalPattern hd x := by
    rintro ⟨ht, _⟩
    obtain ⟨j, hj⟩ := ht missing
    simp [hempty] at hj
  simp [switchSign, switchExponent, he, ht]

private theorem sign_lowerDouble_edge {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (side : Bool) (missing u : Fin d)
    (hm : missing ≠ markedRow hd side) (hu : u ≠ zeroCoord hd)
    (hr : gridRow x (markedRow hd side) = {zeroCoord hd, u})
    (he : gridRow x missing = ∅)
    (hs : singletonRowsOutside x {markedRow hd side, missing})
    (i j : Fin d) (hy : flip x i j ∈ support hd) :
    gridEdgeSign x i j = switchSign hd x * switchSign hd (flip x i j) := by
  have hi := (lowerDouble_flip_iff hd x side missing u hm hu hr he hs i j).mp hy
  subst i
  have hl : lowerDoublePattern hd x := ⟨side, missing, u, hm, hu, hr, he, hs⟩
  have hup := (support_flip_lower_iff hd (lowerDoublePattern_weight hd hl) missing j).mp hy
  rw [switchSign_upper hd hup, mul_one,
    switchSign_lowerDouble hd x side missing u hm hu hr he hs]
  simp [gridEdgeSign, gridPrefix, he]

/- For a transversal the exponent is 1 iff it contains alpha.
   Every row has size one, so rowPrefix x i = i.val; within the changed row
   the count is exactly `if f i < j then 1 else 0`. -/
private theorem rowPrefix_transversal {d : ℕ} (x : Vertex d) (f : Fin d → Fin d)
    (hr : ∀ i, gridRow x i = {f i}) (i : Fin d) :
    rowPrefix x i = i.val := by
  simp [rowPrefix, hr]

private theorem gridPrefix_transversal {d : ℕ} (x : Vertex d) (f : Fin d → Fin d)
    (hr : ∀ i, gridRow x i = {f i}) (i j : Fin d) :
    gridPrefix x i j = i.val + if f i < j then 1 else 0 := by
  simp only [gridPrefix, rowPrefix_transversal x f hr, hr, Finset.filter_singleton]
  split_ifs <;> simp

private theorem switchSign_transversal {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (f : Fin d → Fin d) (hr : ∀ i, gridRow x i = {f i}) (side : Bool)
    (hz : f (markedRow hd side) = zeroCoord hd)
    (hn : f (markedRow hd (!side)) ≠ zeroCoord hd) :
    switchSign hd x = if side then 1 else -1 := by
  have ht : x (finProdFinEquiv (markedRow hd side, zeroCoord hd)) = true :=
    (bit_true_iff_of_singleton (hr _) _).mpr hz.symm
  have hf : x (finProdFinEquiv (markedRow hd (!side), zeroCoord hd)) = false :=
    bit_false_of_singleton (hr _) (Ne.symm hn)
  have htr : lowerTransversalPattern hd x := by
    refine ⟨fun i => ⟨f i, hr i⟩, ?_⟩
    cases side <;> simp_all
  have he (i : Fin d) : gridRow x i ≠ ∅ := by simp [hr]
  cases side <;> simp_all [switchSign, switchExponent]

private theorem sign_transversal_edge {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (f : Fin d → Fin d) (hr : ∀ i, gridRow x i = {f i}) (side : Bool)
    (hz : f (markedRow hd side) = zeroCoord hd)
    (hn : f (markedRow hd (!side)) ≠ zeroCoord hd)
    (i j : Fin d) (hy : flip x i j ∈ support hd) :
    gridEdgeSign x i j = switchSign hd x * switchSign hd (flip x i j) := by
  have hw : gridWeight x = d := by simp [gridWeight, hr]
  have hup := (support_flip_lower_iff hd hw i j).mp hy
  rw [switchSign_upper hd hup, mul_one, switchSign_transversal hd x f hr side hz hn]
  have hc := (lowerTransversal_flip_iff hd x f hr side hz hn i j).mp hy
  rcases hc with ⟨rfl, hj⟩ | ⟨rfl, rfl⟩
  · have hjpos : zeroCoord hd < j := by
      change 0 < j.val
      have hjn : j.val ≠ 0 := by
        intro he
        exact hj (Fin.ext he)
      omega
    rw [gridEdgeSign, gridPrefix_transversal x f hr, hz, if_pos hjpos]
    cases side <;> norm_num [markedRow]
  · rw [gridEdgeSign, gridPrefix_transversal x f hr]
    have hlt : ¬ f (markedRow hd (!side)) < zeroCoord hd := by
      change ¬ (f (markedRow hd (!side))).val < 0
      omega
    rw [if_neg hlt]
    cases side <;> norm_num [markedRow]

/- Complete lower cases without choosing a canonical missing row or column.
   Use exactly the same decomposition as lowerTransversal_card_legal. -/
private theorem sign_lower_edge {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (hx : lowerDoublePattern hd x ∨ lowerTransversalPattern hd x)
    (i j : Fin d) (hy : flip x i j ∈ support hd) :
    gridEdgeSign x i j = switchSign hd x * switchSign hd (flip x i j) := by
  rcases hx with h | h
  · obtain ⟨side, missing, u, hm, hu, hr, he, hs⟩ := h
    exact sign_lowerDouble_edge hd x side missing u hm hu hr he hs i j hy
  · choose f hf using h.1
    have hne := h.2
    by_cases hα : x (finProdFinEquiv (markedRow hd false, zeroCoord hd)) = true
    · have hβ : x (finProdFinEquiv (markedRow hd true, zeroCoord hd)) = false := by
        cases hb : x (finProdFinEquiv (markedRow hd true, zeroCoord hd)) <;> simp_all
      have hz := (bit_true_iff_of_singleton (hf (markedRow hd false)) _).mp hα
      have hn : f (markedRow hd true) ≠ zeroCoord hd := by
        intro he
        have ht := (bit_true_iff_of_singleton (hf (markedRow hd true)) _).mpr he.symm
        simp [hβ] at ht
      exact sign_transversal_edge hd x f hf false hz.symm hn i j hy
    · have hα' : x (finProdFinEquiv (markedRow hd false, zeroCoord hd)) = false := by
        cases ha : x (finProdFinEquiv (markedRow hd false, zeroCoord hd)) <;> simp_all
      have hβ : x (finProdFinEquiv (markedRow hd true, zeroCoord hd)) = true := by
        cases hb : x (finProdFinEquiv (markedRow hd true, zeroCoord hd)) <;> simp_all
      have hz := (bit_true_iff_of_singleton (hf (markedRow hd true)) _).mp hβ
      have hn : f (markedRow hd false) ≠ zeroCoord hd := by
        intro he
        have ht := (bit_true_iff_of_singleton (hf (markedRow hd false)) _).mpr he.symm
        simp [hα'] at ht
      exact sign_transversal_edge hd x f hf true hz.symm hn i j hy

/-- Explicit switching balance on every actual coordinate edge of the support. -/
def IsGridBalanced {d : ℕ} (hd : 2 ≤ d) : Prop :=
  ∃ σ : Vertex d → ℤ,
    (∀ x, x ∈ support hd → σ x = 1 ∨ σ x = -1) ∧
    ∀ x, x ∈ support hd → ∀ i j : Fin d,
      flip x i j ∈ support hd → gridEdgeSign x i j = σ x * σ (flip x i j)

private theorem component_balanced {d : ℕ} (hd : 2 ≤ d) : IsGridBalanced hd := by
  refine ⟨switchSign hd, fun x _ => switchSign_unit hd x, ?_⟩
  intro x hx i j hy
  rcases hx with hu | hl | ht
  · have hw := upperPattern_weight hd hu
    have hylower : lowerDoublePattern hd (flip x i j) ∨
        lowerTransversalPattern hd (flip x i j) := by
      rcases hy with hyu | hyl | hyt
      · have hw' := upperPattern_weight hd hyu
        cases hb : x (finProdFinEquiv (i, j))
        · have he := gridWeight_flip_false x i j hb; omega
        · have he := gridWeight_flip_true x i j hb; omega
      · exact Or.inl hyl
      · exact Or.inr hyt
    have hback : flip (flip x i j) i j = x := by
      funext q
      by_cases hq : q = finProdFinEquiv (i, j)
      · subst q
        simp [flip]
      · simp [flip, hq]
    have hs := sign_lower_edge hd (flip x i j) hylower i j
      (by rw [hback]; exact Or.inl hu)
    simpa [gridEdgeSign, gridPrefix_flip, hback, mul_comm] using hs
  · exact sign_lower_edge hd x (Or.inl hl) i j hy
  · exact sign_lower_edge hd x (Or.inr ht) i j hy


/-- A uniform connected, balanced regular induced graph in every square-dimensional cube. -/
theorem grid_wedge_component {d : ℕ} (hd : 2 ≤ d) :
    Fintype.card (support hd) = 4 * (d - 1) * d ^ (d - 1) ∧
      (componentGraph hd).IsRegularOfDegree d ∧
      (componentGraph hd).Connected ∧ IsGridBalanced hd := by
  exact ⟨card_support hd, component_regular hd, component_connected hd, component_balanced hd⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeComponent
