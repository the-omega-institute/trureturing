/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming, mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: The block support, actual coordinate flips, degree and cardinality of square-dimensional Boolean cube components. -/

import D5.S3.Combinatorics.Graph.Hypercube
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeComponent

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.Hypercube

/-- Actual Boolean vertices, with the coordinates arranged in a square grid. -/
abbrev Vertex (d : ℕ) := Fin (d * d) → Bool

def zeroCoord {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

def markedRow {d : ℕ} (hd : 2 ≤ d) (side : Bool) : Fin d :=
  if side then ⟨1, by omega⟩ else ⟨0, by omega⟩

private theorem markedRow_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (markedRow hd) := by
  intro a b h
  cases a <;> cases b <;> simp_all [markedRow, Fin.ext_iff]

/-- The occupied columns in a literal block of a Boolean vertex. -/
def gridRow {d : ℕ} (x : Vertex d) (i : Fin d) : Finset (Fin d) :=
  Finset.univ.filter fun j => x (finProdFinEquiv (i, j)) = true

def singletonRowsOutside {d : ℕ} (x : Vertex d)
    (exceptions : Finset (Fin d)) : Prop :=
  ∀ i ∉ exceptions, ∃ j : Fin d, gridRow x i = {j}

def upperPattern {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) : Prop :=
  ∃ side : Bool, ∃ u : Fin d, u ≠ zeroCoord hd ∧
    gridRow x (markedRow hd side) = {zeroCoord hd, u} ∧
    singletonRowsOutside x {markedRow hd side}

def lowerDoublePattern {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) : Prop :=
  ∃ side : Bool, ∃ missing : Fin d, ∃ u : Fin d,
    missing ≠ markedRow hd side ∧ u ≠ zeroCoord hd ∧
    gridRow x (markedRow hd side) = {zeroCoord hd, u} ∧
    gridRow x missing = ∅ ∧
    singletonRowsOutside x {markedRow hd side, missing}

def lowerTransversalPattern {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) : Prop :=
  (∀ i : Fin d, ∃ j : Fin d, gridRow x i = {j}) ∧
    x (finProdFinEquiv (markedRow hd false, zeroCoord hd)) ≠
      x (finProdFinEquiv (markedRow hd true, zeroCoord hd))

/-- The constructed support in the actual `d²`-dimensional Boolean cube. -/
def support {d : ℕ} (hd : 2 ≤ d) : Set (Vertex d) :=
  {x | upperPattern hd x ∨ lowerDoublePattern hd x ∨ lowerTransversalPattern hd x}

/-- Adjacency is inherited from the Boolean cube, without additional edges. -/
def componentGraph {d : ℕ} (hd : 2 ≤ d) : SimpleGraph (support hd) :=
  (hypercube (d * d)).induce (support hd)

abbrev UpperData {d : ℕ} (hd : 2 ≤ d) :=
  Σ side : Bool, {u : Fin d // u ≠ zeroCoord hd} ×
    ({i : Fin d // i ≠ markedRow hd side} → Fin d)

def upperVertex {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd) : Vertex d :=
  fun q =>
    let ij := finProdFinEquiv.symm q
    decide (if h : ij.1 = markedRow hd p.1 then
      ij.2 = zeroCoord hd ∨ ij.2 = p.2.1.val
    else ij.2 = p.2.2 ⟨ij.1, h⟩)

theorem gridRow_upperVertex {d : ℕ} (hd : 2 ≤ d)
    (p : UpperData hd) (i : Fin d) :
    gridRow (upperVertex hd p) i =
      if h : i = markedRow hd p.1 then {zeroCoord hd, p.2.1.val}
      else {p.2.2 ⟨i, h⟩} := by
  ext j
  by_cases hi : i = markedRow hd p.1 <;>
    simp [gridRow, upperVertex, hi]

private theorem card_gridRow_upperVertex {d : ℕ} (hd : 2 ≤ d)
    (p : UpperData hd) (i : Fin d) :
    (gridRow (upperVertex hd p) i).card = if i = markedRow hd p.1 then 2 else 1 := by
  by_cases hi : i = markedRow hd p.1 <;>
    simp [gridRow_upperVertex, hi, Ne.symm p.2.1.property]

private theorem upperVertex_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (upperVertex hd) := by
  rintro ⟨a, u, f⟩ ⟨b, v, g⟩ h
  have hab : markedRow hd a = markedRow hd b := by
    by_contra hn
    have hc := congrArg (fun x => (gridRow x (markedRow hd a)).card) h
    simpa [card_gridRow_upperVertex, hn] using hc
  have hab' : a = b := markedRow_injective hd hab
  subst b
  have hr := congrArg (fun x => gridRow x (markedRow hd a)) h
  have hp : ({zeroCoord hd, u.val} : Finset (Fin d)) = {zeroCoord hd, v.val} := by
    simpa [gridRow_upperVertex] using hr
  have huv : u.val = v.val := by
    have hm : u.val ∈ ({zeroCoord hd, v.val} : Finset (Fin d)) := by
      rw [← hp]
      simp
    simpa [u.property] using hm
  have huv' : u = v := Subtype.ext huv
  subst v
  have hfg : f = g := by
    funext i
    have hr' := congrArg (fun x => gridRow x i.val) h
    have hs : ({f i} : Finset (Fin d)) = {g i} := by
      simpa [gridRow_upperVertex, i.property] using hr'
    simpa using hs
  subst g
  rfl

private theorem card_upperData {d : ℕ} (hd : 2 ≤ d) :
    Fintype.card (UpperData hd) = 2 * (d - 1) * d ^ (d - 1) := by
  simp [UpperData, Fintype.card_sigma, Fintype.card_prod, Nat.two_mul, Nat.add_mul]

private def upperVertices {d : ℕ} (hd : 2 ≤ d) : Finset (Vertex d) :=
  Finset.univ.image (upperVertex hd)

theorem gridRow_ext {d : ℕ} {x y : Vertex d}
    (h : ∀ i, gridRow x i = gridRow y i) : x = y := by
  funext q
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  have hm := Finset.ext_iff.mp (h i) j
  simp only [gridRow, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  cases hx : x (finProdFinEquiv (i, j)) <;>
    cases hy : y (finProdFinEquiv (i, j)) <;> simp_all

theorem upperVertex_pattern {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd) :
    upperPattern hd (upperVertex hd p) := by
  refine ⟨p.1, p.2.1.val, p.2.1.property, ?_, ?_⟩
  · simp [gridRow_upperVertex]
  · intro i hi
    have hi' : i ≠ markedRow hd p.1 := by simpa using hi
    exact ⟨p.2.2 ⟨i, hi'⟩, by simp [gridRow_upperVertex, hi']⟩

theorem upperPattern_iff_mem {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) :
    upperPattern hd x ↔ x ∈ upperVertices hd := by
  constructor
  · rintro ⟨side, u, hu, hrow, hsingle⟩
    let f : {i : Fin d // i ≠ markedRow hd side} → Fin d :=
      fun i => Classical.choose (hsingle i.val (by simpa using i.property))
    let p : UpperData hd := ⟨side, ⟨u, hu⟩, f⟩
    have hp : upperVertex hd p = x := by
      apply gridRow_ext
      intro i
      by_cases hi : i = markedRow hd side
      · subst i
        simpa [p, gridRow_upperVertex] using hrow.symm
      · have hfi := Classical.choose_spec (hsingle i (by simpa using hi))
        simpa [p, f, gridRow_upperVertex, hi] using hfi.symm
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩
  · intro hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact upperVertex_pattern hd p

/-- The number of occupied Boolean coordinates, summed over the literal blocks. -/
def gridWeight {d : ℕ} (x : Vertex d) : ℕ := ∑ i, (gridRow x i).card

theorem upperPattern_weight {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : upperPattern hd x) : gridWeight x = d + 1 := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ((upperPattern_iff_mem hd x).mp hx)
  have he (i : Fin d) : (gridRow (upperVertex hd p) i).card =
      1 + if i = markedRow hd p.1 then 1 else 0 := by
    by_cases hi : i = markedRow hd p.1 <;> simp [card_gridRow_upperVertex, hi]
  simp [gridWeight, he, Finset.sum_add_distrib]

theorem lowerDoublePattern_weight {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : lowerDoublePattern hd x) : gridWeight x = d := by
  obtain ⟨side, missing, u, hmissing, hu, hrow, hempty, hsingle⟩ := hx
  have he (i : Fin d) : (gridRow x i).card + (if i = missing then 1 else 0) =
      1 + if i = markedRow hd side then 1 else 0 := by
    by_cases hi : i = markedRow hd side
    · subst i
      simp [hrow, Ne.symm hu, Ne.symm hmissing]
    · by_cases him : i = missing
      · subst i
        simp [hempty, hmissing]
      · obtain ⟨j, hj⟩ := hsingle i (by simp [hi, him])
        simp [hj, hi, him]
  have hs := congrArg (fun f : Fin d → ℕ => ∑ i, f i) (funext he)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hs
  change gridWeight x + 1 = d + 1 at hs
  omega

theorem lowerTransversalPattern_weight {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : lowerTransversalPattern hd x) : gridWeight x = d := by
  have he (i : Fin d) : (gridRow x i).card = 1 := by
    obtain ⟨j, hj⟩ := hx.1 i
    simp [hj]
  simp [gridWeight, he]

private theorem support_weight {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : x ∈ support hd) : gridWeight x = d ∨ gridWeight x = d + 1 := by
  rcases hx with h | h | h
  · exact Or.inr (upperPattern_weight hd h)
  · exact Or.inl (lowerDoublePattern_weight hd h)
  · exact Or.inl (lowerTransversalPattern_weight hd h)

def flip {d : ℕ} (x : Vertex d) (i j : Fin d) : Vertex d :=
  Function.update x (finProdFinEquiv (i, j)) (!x (finProdFinEquiv (i, j)))

theorem gridRow_flip_other {d : ℕ} (x : Vertex d) (i j k : Fin d)
    (hk : k ≠ i) : gridRow (flip x i j) k = gridRow x k := by
  ext l
  have hc : finProdFinEquiv (k, l) ≠ finProdFinEquiv (i, j) := by
    intro h
    exact hk (congrArg Prod.fst (finProdFinEquiv.injective h))
  simp only [gridRow, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [flip, Function.update_of_ne hc]

theorem gridRow_flip_same {d : ℕ} (x : Vertex d) (i j : Fin d) :
    gridRow (flip x i j) i = if x (finProdFinEquiv (i, j)) = true then
      (gridRow x i).erase j else insert j (gridRow x i) := by
  ext l
  by_cases hl : l = j
  · subst l
    cases hx : x (finProdFinEquiv (i, j)) <;> simp [gridRow, flip, hx]
  · have hc : finProdFinEquiv (i, l) ≠ finProdFinEquiv (i, j) := by
      intro h
      exact hl (congrArg Prod.snd (finProdFinEquiv.injective h))
    cases hx : x (finProdFinEquiv (i, j)) <;>
      simp only [gridRow, Finset.mem_filter, Finset.mem_univ, true_and,
        hx, Bool.false_eq_true, if_false, if_true, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    all_goals simp [flip, Function.update_of_ne hc, hl]

theorem gridWeight_flip_true {d : ℕ} (x : Vertex d) (i j : Fin d)
    (hx : x (finProdFinEquiv (i, j)) = true) :
    gridWeight (flip x i j) + 1 = gridWeight x := by
  have hj : j ∈ gridRow x i := by simpa [gridRow] using hx
  have hrow := Finset.card_erase_add_one hj
  unfold gridWeight
  rw [← Finset.sum_erase_add Finset.univ (fun k => (gridRow (flip x i j) k).card)
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ (fun k => (gridRow x k).card)
    (Finset.mem_univ i)]
  have he : ∑ k ∈ Finset.univ.erase i, (gridRow (flip x i j) k).card =
      ∑ k ∈ Finset.univ.erase i, (gridRow x k).card := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [gridRow_flip_other x i j k (Finset.mem_erase.mp hk).1]
  rw [he, gridRow_flip_same, if_pos hx]
  omega

theorem gridWeight_flip_false {d : ℕ} (x : Vertex d) (i j : Fin d)
    (hx : x (finProdFinEquiv (i, j)) = false) :
    gridWeight (flip x i j) = gridWeight x + 1 := by
  have hj : j ∉ gridRow x i := by simp [gridRow, hx]
  have hrow := Finset.card_insert_of_notMem hj
  unfold gridWeight
  rw [← Finset.sum_erase_add Finset.univ (fun k => (gridRow (flip x i j) k).card)
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ (fun k => (gridRow x k).card)
    (Finset.mem_univ i)]
  have he : ∑ k ∈ Finset.univ.erase i, (gridRow (flip x i j) k).card =
      ∑ k ∈ Finset.univ.erase i, (gridRow x k).card := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [gridRow_flip_other x i j k (Finset.mem_erase.mp hk).1]
  rw [he, gridRow_flip_same, if_neg (by simp [hx])]
  omega

private theorem gridRow_empty_bit_false {d : ℕ} {x : Vertex d} {i : Fin d}
    (hi : gridRow x i = ∅) (j : Fin d) : x (finProdFinEquiv (i, j)) = false := by
  cases hb : x (finProdFinEquiv (i, j)) with
  | false => rfl
  | true =>
      have hm : j ∈ gridRow x i := by simp [gridRow, hb]
      simpa [hi] using hm

theorem upperPattern_row_nonempty {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : upperPattern hd x) (i : Fin d) : (gridRow x i).Nonempty := by
  obtain ⟨side, u, _, hrow, hsingle⟩ := hx
  by_cases hi : i = markedRow hd side
  · subst i
    exact ⟨zeroCoord hd, by simp [hrow]⟩
  · obtain ⟨j, hj⟩ := hsingle i (by simpa using hi)
    exact ⟨j, by simp [hj]⟩

theorem support_flip_lower_iff {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : gridWeight x = d) (i j : Fin d) :
    flip x i j ∈ support hd ↔ upperPattern hd (flip x i j) := by
  constructor
  · rintro (h | h | h)
    · exact h
    · have hw := lowerDoublePattern_weight hd h
      cases hb : x (finProdFinEquiv (i, j)) with
      | false => have hf := gridWeight_flip_false x i j hb; omega
      | true => have hf := gridWeight_flip_true x i j hb; omega
    · have hw := lowerTransversalPattern_weight hd h
      cases hb : x (finProdFinEquiv (i, j)) with
      | false => have hf := gridWeight_flip_false x i j hb; omega
      | true => have hf := gridWeight_flip_true x i j hb; omega
  · exact fun h => Or.inl h

theorem lowerDouble_flip_iff {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (side : Bool) (missing u : Fin d)
    (hmissing : missing ≠ markedRow hd side) (hu : u ≠ zeroCoord hd)
    (hrow : gridRow x (markedRow hd side) = {zeroCoord hd, u})
    (hempty : gridRow x missing = ∅)
    (hsingle : singletonRowsOutside x {markedRow hd side, missing}) (i j : Fin d) :
    flip x i j ∈ support hd ↔ i = missing := by
  have hx : lowerDoublePattern hd x :=
    ⟨side, missing, u, hmissing, hu, hrow, hempty, hsingle⟩
  rw [support_flip_lower_iff hd (lowerDoublePattern_weight hd hx)]
  constructor
  · intro hy
    by_contra hi
    have hn := upperPattern_row_nonempty hd hy missing
    rw [gridRow_flip_other x i j missing (Ne.symm hi), hempty] at hn
    simpa using hn
  · intro hi
    subst i
    refine ⟨side, u, hu, ?_, ?_⟩
    · rw [gridRow_flip_other x missing j (markedRow hd side) (Ne.symm hmissing)]
      exact hrow
    · intro k hk
      have hks : k ≠ markedRow hd side := by simpa using hk
      by_cases hkm : k = missing
      · subst k
        refine ⟨j, ?_⟩
        rw [gridRow_flip_same, if_neg (by simp [gridRow_empty_bit_false hempty j]), hempty]
        simp
      · obtain ⟨l, hl⟩ := hsingle k (by simp [hks, hkm])
        exact ⟨l, by rw [gridRow_flip_other x missing j k hkm, hl]⟩

theorem bit_true_iff_of_singleton {d : ℕ} {x : Vertex d} {i a : Fin d}
    (hr : gridRow x i = {a}) (j : Fin d) :
    x (finProdFinEquiv (i, j)) = true ↔ j = a := by
  have hm := Finset.ext_iff.mp hr j
  simpa [gridRow] using hm

theorem bit_false_of_singleton {d : ℕ} {x : Vertex d} {i a : Fin d}
    (hr : gridRow x i = {a}) {j : Fin d} (hj : j ≠ a) :
    x (finProdFinEquiv (i, j)) = false := by
  cases hb : x (finProdFinEquiv (i, j)) with
  | false => rfl
  | true => exact False.elim (hj ((bit_true_iff_of_singleton hr j).mp hb))

theorem lowerTransversal_flip_iff {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (f : Fin d → Fin d) (hrows : ∀ i, gridRow x i = {f i}) (side : Bool)
    (hzero : f (markedRow hd side) = zeroCoord hd)
    (hnonzero : f (markedRow hd (!side)) ≠ zeroCoord hd) (i j : Fin d) :
    flip x i j ∈ support hd ↔
      (i = markedRow hd side ∧ j ≠ zeroCoord hd) ∨
        (i = markedRow hd (!side) ∧ j = zeroCoord hd) := by
  have hw : gridWeight x = d := by simp [gridWeight, hrows]
  rw [support_flip_lower_iff hd hw]
  constructor
  · intro hy
    have hfalse : x (finProdFinEquiv (i, j)) = false := by
      cases hb : x (finProdFinEquiv (i, j)) with
      | false => rfl
      | true =>
          have ha := upperPattern_weight hd hy
          have hf := gridWeight_flip_true x i j hb
          omega
    have hjne : j ≠ f i := by
      intro he
      have ht := (bit_true_iff_of_singleton (hrows i) j).mpr he
      simp [hfalse] at ht
    obtain ⟨other, u, hu, hpair, _⟩ := hy
    have hi : i = markedRow hd other := by
      by_contra hne
      have hc := congrArg Finset.card hpair
      rw [gridRow_flip_other x i j (markedRow hd other) (Ne.symm hne), hrows] at hc
      simp [Ne.symm hu] at hc
    have hp : insert j ({f i} : Finset (Fin d)) = {zeroCoord hd, u} := by
      have hpi : gridRow (flip x i j) i = {zeroCoord hd, u} := by simpa [hi] using hpair
      simpa [gridRow_flip_same, hfalse, hrows] using hpi
    have hz : j = zeroCoord hd ∨ f i = zeroCoord hd := by
      have hm : zeroCoord hd ∈ insert j ({f i} : Finset (Fin d)) := by
        rw [hp]
        simp
      simpa [eq_comm] using hm
    have hc : other = side ∨ other = !side := by
      cases other <;> cases side <;> simp
    rcases hc with ho | ho
    · subst other
      left
      refine ⟨hi, ?_⟩
      simpa [hi, hzero] using hjne
    · subst other
      right
      refine ⟨hi, ?_⟩
      exact hz.resolve_right (by simpa [hi] using hnonzero)
  · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
    · subst i
      refine ⟨side, j, hj, ?_, ?_⟩
      · have hf := bit_false_of_singleton (hrows (markedRow hd side))
          (by simpa [hzero] using hj)
        simp [gridRow_flip_same, hf, hrows, hzero, Finset.pair_comm]
      · intro k hk
        have hks : k ≠ markedRow hd side := by simpa using hk
        exact ⟨f k, by rw [gridRow_flip_other x (markedRow hd side) j k hks, hrows]⟩
    · subst i
      subst j
      refine ⟨!side, f (markedRow hd (!side)), hnonzero, ?_, ?_⟩
      · have hf := bit_false_of_singleton (hrows (markedRow hd (!side)))
          (Ne.symm hnonzero)
        simp [gridRow_flip_same, hf, hrows]
      · intro k hk
        have hks : k ≠ markedRow hd (!side) := by simpa using hk
        exact ⟨f k, by rw [gridRow_flip_other x (markedRow hd (!side))
          (zeroCoord hd) k hks, hrows]⟩

theorem markedRow_not_ne {d : ℕ} (hd : 2 ≤ d) (side : Bool) :
    markedRow hd (!side) ≠ markedRow hd side := by
  intro h
  have h' := markedRow_injective hd h
  cases side <;> simp at h'

private theorem flip_bit_other_row {d : ℕ} (x : Vertex d) (i j k l : Fin d)
    (hk : k ≠ i) : flip x i j (finProdFinEquiv (k, l)) =
      x (finProdFinEquiv (k, l)) := by
  have hc : finProdFinEquiv (k, l) ≠ finProdFinEquiv (i, j) := by
    intro h
    exact hk (congrArg Prod.fst (finProdFinEquiv.injective h))
  simp [flip, Function.update_of_ne hc]

private theorem support_singletonRows_iff {d : ℕ} (hd : 2 ≤ d) (x : Vertex d)
    (hs : ∀ i : Fin d, ∃ j : Fin d, gridRow x i = {j}) (side : Bool) :
    x ∈ support hd ↔
      x (finProdFinEquiv (markedRow hd side, zeroCoord hd)) ≠
        x (finProdFinEquiv (markedRow hd (!side), zeroCoord hd)) := by
  have hc (i : Fin d) : (gridRow x i).card = 1 := by
    obtain ⟨j, hj⟩ := hs i
    simp [hj]
  constructor
  · rintro (h | h | h)
    · obtain ⟨s, u, hu, hr, _⟩ := h
      have hh := hc (markedRow hd s)
      simp [hr, Ne.symm hu] at hh
    · obtain ⟨s, missing, u, _, hu, hr, _, _⟩ := h
      have hh := hc (markedRow hd s)
      simp [hr, Ne.symm hu] at hh
    · cases side <;> simpa [ne_comm] using h.2
  · intro h
    refine Or.inr (Or.inr ⟨hs, ?_⟩)
    cases side <;> simpa [ne_comm] using h

private theorem upper_flip_true {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd)
    (i j : Fin d) (h : flip (upperVertex hd p) i j ∈ support hd) :
    upperVertex hd p (finProdFinEquiv (i, j)) = true := by
  cases hb : upperVertex hd p (finProdFinEquiv (i, j)) with
  | true => rfl
  | false =>
      have hw := upperPattern_weight hd (upperVertex_pattern hd p)
      have hf := gridWeight_flip_false (upperVertex hd p) i j hb
      have hs := support_weight hd h
      omega

private theorem upper_flip_zero_iff {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd) :
    flip (upperVertex hd p) (markedRow hd p.1) (zeroCoord hd) ∈ support hd ↔
      upperVertex hd p (finProdFinEquiv (markedRow hd (!p.1), zeroCoord hd)) = true := by
  let x := upperVertex hd p
  have hz : x (finProdFinEquiv (markedRow hd p.1, zeroCoord hd)) = true := by
    simp [x, upperVertex]
  have hs : ∀ i : Fin d, ∃ j : Fin d,
      gridRow (flip x (markedRow hd p.1) (zeroCoord hd)) i = {j} := by
    intro i
    by_cases hi : i = markedRow hd p.1
    · subst i
      refine ⟨p.2.1.val, ?_⟩
      simp [gridRow_flip_same, hz, x, gridRow_upperVertex, Ne.symm p.2.1.property]
    · refine ⟨p.2.2 ⟨i, hi⟩, ?_⟩
      rw [gridRow_flip_other x (markedRow hd p.1) (zeroCoord hd) i hi]
      simp [x, gridRow_upperVertex, hi]
  rw [support_singletonRows_iff hd _ hs p.1]
  rw [flip_bit_other_row x (markedRow hd p.1) (zeroCoord hd)
    (markedRow hd (!p.1)) (zeroCoord hd) (markedRow_not_ne hd p.1)]
  simp [flip, hz, x]

theorem upper_flip_ordinary_iff {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd) :
    flip (upperVertex hd p) (markedRow hd p.1) p.2.1.val ∈ support hd ↔
      upperVertex hd p (finProdFinEquiv (markedRow hd (!p.1), zeroCoord hd)) = false := by
  let x := upperVertex hd p
  have hu : x (finProdFinEquiv (markedRow hd p.1, p.2.1.val)) = true := by
    simp [x, upperVertex]
  have hs : ∀ i : Fin d, ∃ j : Fin d,
      gridRow (flip x (markedRow hd p.1) p.2.1.val) i = {j} := by
    intro i
    by_cases hi : i = markedRow hd p.1
    · subst i
      refine ⟨zeroCoord hd, ?_⟩
      rw [gridRow_flip_same, if_pos hu]
      simp only [x, gridRow_upperVertex, dite_eq_left rfl]
      have hne := p.2.1.property
      ext k
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · refine ⟨p.2.2 ⟨i, hi⟩, ?_⟩
      rw [gridRow_flip_other x (markedRow hd p.1) p.2.1.val i hi]
      simp [x, gridRow_upperVertex, hi]
  rw [support_singletonRows_iff hd _ hs p.1]
  rw [flip_bit_other_row x (markedRow hd p.1) p.2.1.val
    (markedRow hd (!p.1)) (zeroCoord hd) (markedRow_not_ne hd p.1)]
  have hc : finProdFinEquiv (markedRow hd p.1, zeroCoord hd) ≠
      finProdFinEquiv (markedRow hd p.1, p.2.1.val) := by
    intro h
    exact p.2.1.property (congrArg Prod.snd (finProdFinEquiv.injective h)).symm
  have hz : x (finProdFinEquiv (markedRow hd p.1, zeroCoord hd)) = true := by
    simp [x, upperVertex]
  simp [flip, Function.update_of_ne hc, hz, x]

theorem upper_flip_other_iff {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd)
    (i : Fin d) (hi : i ≠ markedRow hd p.1) (j : Fin d) :
    flip (upperVertex hd p) i j ∈ support hd ↔ j = p.2.2 ⟨i, hi⟩ := by
  constructor
  · intro h
    have ht := upper_flip_true hd p i j h
    simpa [upperVertex, hi] using ht
  · intro hj
    subst j
    let x := upperVertex hd p
    have ht : x (finProdFinEquiv (i, p.2.2 ⟨i, hi⟩)) = true := by
      simp [x, upperVertex, hi]
    refine Or.inr (Or.inl ⟨p.1, i, p.2.1.val, hi, p.2.1.property, ?_, ?_, ?_⟩)
    · rw [gridRow_flip_other x i _ (markedRow hd p.1) (Ne.symm hi)]
      simp [x, gridRow_upperVertex]
    · rw [gridRow_flip_same, if_pos ht]
      simp [x, gridRow_upperVertex, hi]
    · intro k hk
      have hkm : k ≠ markedRow hd p.1 := by intro h; exact hk (by simp [h])
      have hki : k ≠ i := by intro h; exact hk (by simp [h])
      refine ⟨p.2.2 ⟨k, hkm⟩, ?_⟩
      rw [gridRow_flip_other x i _ k hki]
      simp [x, gridRow_upperVertex, hkm]

abbrev LegalData {d : ℕ} (hd : 2 ≤ d) (x : Vertex d) :=
  Σ i : Fin d, {j : Fin d // flip x i j ∈ support hd}

theorem flip_adj {d : ℕ} (x : Vertex d) (i j : Fin d) :
    (hypercube (d * d)).Adj x (flip x i j) := by
  change (Finset.univ.filter (fun q => x q ≠ flip x i j q)).card = 1
  have he : Finset.univ.filter (fun q => x q ≠ flip x i j q) =
      {finProdFinEquiv (i, j)} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hq : q = finProdFinEquiv (i, j)
    · subst q
      simp [flip]
    · simp [flip, hq]
  rw [he, Finset.card_singleton]

private theorem degree_eq_card_legal {d : ℕ} (hd : 2 ≤ d) (x : support hd) :
    (componentGraph hd).degree x = Fintype.card (LegalData hd x.val) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let f : LegalData hd x.val → (componentGraph hd).neighborSet x :=
    fun p => ⟨⟨flip x.val p.1 p.2.val, p.2.property⟩, flip_adj x.val p.1 p.2.val⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j, hj⟩ ⟨k, l, hl⟩ he
      have hc : finProdFinEquiv (i, j) = finProdFinEquiv (k, l) := by
        by_contra hn
        have hb := congrArg
          (fun y : (componentGraph hd).neighborSet x =>
            y.val.val (finProdFinEquiv (i, j))) he
        simp [f, flip, Function.update_of_ne hn] at hb
      have hp := finProdFinEquiv.injective hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      rfl
    · intro y
      have hy : (Finset.univ.filter (fun q => x.val q ≠ y.val.val q)).card = 1 :=
        y.property
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hy
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
      have he : flip x.val i j = y.val.val := by
        funext r
        have hm (q : Fin (d * d)) :
            x.val q ≠ y.val.val q ↔ q = finProdFinEquiv (i, j) := by
          have := Finset.ext_iff.mp hq q
          simpa using this
        by_cases hr : r = finProdFinEquiv (i, j)
        · subst r
          have hn := (hm _).mpr rfl
          simp only [flip, Function.update_self]
          cases hx : x.val (finProdFinEquiv (i, j)) <;>
            cases hy : y.val.val (finProdFinEquiv (i, j)) <;> simp_all
        · have hsame : x.val r = y.val.val r := by
            by_contra hn
            exact hr ((hm r).mp hn)
          simpa [flip, Function.update_of_ne hr] using hsame
      refine ⟨⟨i, ⟨j, ?_⟩⟩, ?_⟩
      · rw [he]
        exact y.val.property
      · apply Subtype.ext
        exact Subtype.ext he
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm

private theorem lowerDouble_card_legal {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : lowerDoublePattern hd x) : Fintype.card (LegalData hd x) = d := by
  obtain ⟨side, missing, u, hm, hu, hr, he, hs⟩ := hx
  have hc (i : Fin d) : Fintype.card {j : Fin d // flip x i j ∈ support hd} =
      if i = missing then d else 0 := by
    by_cases hi : i = missing <;>
      simp [Fintype.card_subtype, lowerDouble_flip_iff hd x side missing u hm hu hr he hs,
        hi]
  simp [LegalData, Fintype.card_sigma, hc]

theorem lowerTransversal_card_legal {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : lowerTransversalPattern hd x) : Fintype.card (LegalData hd x) = d := by
  let f : Fin d → Fin d := fun i => Classical.choose (hx.1 i)
  have hr (i : Fin d) : gridRow x i = {f i} := Classical.choose_spec (hx.1 i)
  have hs : ∃ side : Bool, f (markedRow hd side) = zeroCoord hd ∧
      f (markedRow hd (!side)) ≠ zeroCoord hd := by
    have hf := bit_true_iff_of_singleton (hr (markedRow hd false)) (zeroCoord hd)
    have ht := bit_true_iff_of_singleton (hr (markedRow hd true)) (zeroCoord hd)
    by_cases h : f (markedRow hd false) = zeroCoord hd
    · refine ⟨false, h, ?_⟩
      intro he
      exact hx.2 ((hf.mpr h.symm).trans (ht.mpr he.symm).symm)
    · refine ⟨true, ?_, h⟩
      have ha : x (finProdFinEquiv (markedRow hd false, zeroCoord hd)) = false :=
        bit_false_of_singleton (hr _) (Ne.symm h)
      have hb : x (finProdFinEquiv (markedRow hd true, zeroCoord hd)) = true := by
        cases hb : x (finProdFinEquiv (markedRow hd true, zeroCoord hd))
        · exact False.elim (hx.2 (ha.trans hb.symm))
        · rfl
      exact (ht.mp hb).symm
  obtain ⟨side, hz, hn⟩ := hs
  have hcount (i : Fin d) :
      Fintype.card {j : Fin d // flip x i j ∈ support hd} =
        (if i = markedRow hd side then d - 1 else 0) +
          (if i = markedRow hd (!side) then 1 else 0) := by
    by_cases hi : i = markedRow hd side
    · subst i
      simp [Fintype.card_subtype,
        lowerTransversal_flip_iff hd x f hr side hz hn,
        Ne.symm (markedRow_not_ne hd side), Finset.filter_ne']
    · by_cases hi' : i = markedRow hd (!side)
      · subst i
        simp [Fintype.card_subtype,
          lowerTransversal_flip_iff hd x f hr side hz hn, markedRow_not_ne hd side]
      · simp [Fintype.card_subtype,
          lowerTransversal_flip_iff hd x f hr side hz hn, hi, hi']
  simp only [LegalData, Fintype.card_sigma, hcount, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  omega

private def upperDeletionColumn {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd) : Fin d :=
  if upperVertex hd p (finProdFinEquiv (markedRow hd (!p.1), zeroCoord hd))
    then zeroCoord hd else p.2.1.val

private theorem upper_flip_marked_iff {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd)
    (j : Fin d) :
    flip (upperVertex hd p) (markedRow hd p.1) j ∈ support hd ↔
      j = upperDeletionColumn hd p := by
  constructor
  · intro h
    have ht := upper_flip_true hd p (markedRow hd p.1) j h
    have hj : j = zeroCoord hd ∨ j = p.2.1.val := by simpa [upperVertex] using ht
    rcases hj with rfl | rfl
    · have hb := (upper_flip_zero_iff hd p).mp h
      simp [upperDeletionColumn, hb]
    · have hb := (upper_flip_ordinary_iff hd p).mp h
      simp [upperDeletionColumn, hb]
  · intro hj
    rw [hj]
    cases hb : upperVertex hd p
        (finProdFinEquiv (markedRow hd (!p.1), zeroCoord hd))
    · simpa [upperDeletionColumn, hb] using (upper_flip_ordinary_iff hd p).mpr hb
    · simpa [upperDeletionColumn, hb] using (upper_flip_zero_iff hd p).mpr hb

private theorem upper_card_legal {d : ℕ} (hd : 2 ≤ d) (p : UpperData hd) :
    Fintype.card (LegalData hd (upperVertex hd p)) = d := by
  have hc (i : Fin d) :
      Fintype.card {j : Fin d // flip (upperVertex hd p) i j ∈ support hd} = 1 := by
    by_cases hi : i = markedRow hd p.1
    · subst i
      simp [Fintype.card_subtype, upper_flip_marked_iff]
    · simp [Fintype.card_subtype, upper_flip_other_iff hd p i hi]
  simp [LegalData, Fintype.card_sigma, hc]

theorem component_regular {d : ℕ} (hd : 2 ≤ d) :
    (componentGraph hd).IsRegularOfDegree d := by
  intro x
  rw [degree_eq_card_legal]
  rcases x.property with h | h | h
  · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ((upperPattern_iff_mem hd x.val).mp h)
    rw [← hp]
    exact upper_card_legal hd p
  · exact lowerDouble_card_legal hd h
  · exact lowerTransversal_card_legal hd h

private theorem adj_exists_flip {d : ℕ} {x y : Vertex d}
    (h : (hypercube (d * d)).Adj x y) : ∃ i j : Fin d, flip x i j = y := by
  have hh : (Finset.univ.filter (fun q => x q ≠ y q)).card = 1 := h
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hh
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  refine ⟨i, j, ?_⟩
  funext r
  have hm (q : Fin (d * d)) : x q ≠ y q ↔ q = finProdFinEquiv (i, j) := by
    have := Finset.ext_iff.mp hq q
    simpa using this
  by_cases hr : r = finProdFinEquiv (i, j)
  · subst r
    have hn := (hm _).mpr rfl
    simp only [flip, Function.update_self]
    cases hx : x (finProdFinEquiv (i, j)) <;>
      cases hy : y (finProdFinEquiv (i, j)) <;> simp_all
  · have he : x r = y r := by
      by_contra hn
      exact hr ((hm r).mp hn)
    simpa [flip, Function.update_of_ne hr] using he

private theorem support_upper_iff_weight {d : ℕ} (hd : 2 ≤ d) {x : Vertex d}
    (hx : x ∈ support hd) : upperPattern hd x ↔ gridWeight x = d + 1 := by
  constructor
  · exact upperPattern_weight hd
  · intro hw
    rcases hx with h | h | h
    · exact h
    · have := lowerDoublePattern_weight hd h; omega
    · have := lowerTransversalPattern_weight hd h; omega

private def upperPart {d : ℕ} (hd : 2 ≤ d) : Finset (support hd) :=
  Finset.univ.filter fun x => gridWeight x.val = d + 1

private def lowerPart {d : ℕ} (hd : 2 ≤ d) : Finset (support hd) :=
  Finset.univ.filter fun x => gridWeight x.val ≠ d + 1

private theorem component_bipartite {d : ℕ} (hd : 2 ≤ d) :
    (componentGraph hd).IsBipartiteWith (upperPart hd) (lowerPart hd) := by
  constructor
  · exact Finset.disjoint_coe.mpr (Finset.disjoint_filter_filter_not _ _ _)
  · intro x y h
    obtain ⟨i, j, hf⟩ := adj_exists_flip h
    have hx := support_weight hd x.property
    have hy := support_weight hd y.property
    have hw : gridWeight y.val + 1 = gridWeight x.val ∨
        gridWeight y.val = gridWeight x.val + 1 := by
      cases hb : x.val (finProdFinEquiv (i, j))
      · right
        have he := gridWeight_flip_false x.val i j hb
        change flip x.val i j = y.val at hf
        simpa only [hf] using he
      · left
        have he := gridWeight_flip_true x.val i j hb
        change flip x.val i j = y.val at hf
        simpa only [hf] using he
    simp only [upperPart, lowerPart, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega

private theorem card_upperPart {d : ℕ} (hd : 2 ≤ d) :
    (upperPart hd).card = 2 * (d - 1) * d ^ (d - 1) := by
  let f : UpperData hd → {x : support hd // gridWeight x.val = d + 1} :=
    fun p => ⟨⟨upperVertex hd p, Or.inl (upperVertex_pattern hd p)⟩,
      upperPattern_weight hd (upperVertex_pattern hd p)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      exact upperVertex_injective hd (congrArg (fun x => x.val.val) h)
    · intro x
      have hx := (support_upper_iff_weight hd x.val.property).mpr x.property
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ((upperPattern_iff_mem hd _).mp hx)
      refine ⟨p, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hp
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [Fintype.card_subtype] at hc
  change Fintype.card (UpperData hd) = (upperPart hd).card at hc
  rw [← hc, card_upperData]

theorem card_support {d : ℕ} (hd : 2 ≤ d) :
    Fintype.card (support hd) = 4 * (d - 1) * d ^ (d - 1) := by
  have he := SimpleGraph.isBipartiteWith_sum_degrees_eq (component_bipartite hd)
  simp only [(component_regular hd).degree_eq, Finset.sum_const, smul_eq_mul] at he
  have hc : (upperPart hd).card = (lowerPart hd).card :=
    Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) he
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : support hd => gridWeight x.val = d + 1)
  change (upperPart hd).card + (lowerPart hd).card = Fintype.card (support hd) at hs
  rw [← hc, card_upperPart] at hs
  nlinarith

end D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeComponent
