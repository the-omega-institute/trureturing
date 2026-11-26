/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Odd multiplicities and common integer height force one balanced cut in a connected family of transverse boxes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentTransverseFibers
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Tauto

/-! Balanced cuts under the symmetric-difference action give boxes in the
six-coordinate projection. Their shared integer height fixes the center
along overlaps. Odd incidence then determines the unordered cut. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9CutBoxRigidity

open Finset
open scoped symmDiff

abbrev Point := Finset (Fin 6)

/-- A point belongs to the box when its two changed coordinates cross the cut. -/
def Box (A c x : Point) : Prop :=
  ∃ i j : Fin 6, (i ∈ A ↔ j ∉ A) ∧ c ∆ x = {i, j}

/-- On a box, each height coordinate is a fixed offset plus the indicator
of disagreement with the box center. -/
def HasHeight (height : Point → Fin 6 → ℤ) (A c : Point) : Prop :=
  ∃ offset : Fin 6 → ℤ, ∀ x, Box A c x → ∀ i,
    height x i = offset i + if i ∈ c ∆ x then 1 else 0

private theorem cross_swap {A : Point} {i j : Fin 6} (h : i ∈ A ↔ j ∉ A) :
    j ∈ A ↔ i ∉ A := by tauto

private theorem flip_pair {A B : Point} {p q r : Fin 6}
    (hAc : A.card = 3) (hBc : B.card = 3)
    (hA : p ∈ A ↔ r ∉ A) (hB : q ∈ B ↔ r ∉ B) :
    ∃ s, (q ∈ A ↔ s ∉ A) ∧ (p ∈ B ↔ s ∉ B) := by
  let U : Point := univ.filter fun s => decide (s ∈ A) != decide (q ∈ A)
  let V : Point := univ.filter fun s => decide (s ∈ B) != decide (p ∈ B)
  have memU (s : Fin 6) : s ∈ U ↔ (q ∈ A ↔ s ∉ A) := by
    by_cases hq : q ∈ A <;> by_cases hs : s ∈ A <;> simp [U, hq, hs]
  have memV (s : Fin 6) : s ∈ V ↔ (p ∈ B ↔ s ∉ B) := by
    by_cases hp : p ∈ B <;> by_cases hs : s ∈ B <;> simp [V, hp, hs]
  have cardU : U.card = 3 := by
    by_cases hq : q ∈ A
    · have he : U = Aᶜ := by ext s; simp [memU, hq]
      rw [he, card_compl, Fintype.card_fin, hAc]
    · have he : U = A := by ext s; simp [memU, hq]
      rw [he, hAc]
  have cardV : V.card = 3 := by
    by_cases hp : p ∈ B
    · have he : V = Bᶜ := by ext s; simp [memV, hp]
      rw [he, card_compl, Fintype.card_fin, hBc]
    · have he : V = B := by ext s; simp [memV, hp]
      rw [he, hBc]
  by_contra hn
  have hdisj : Disjoint U V := disjoint_left.mpr fun s hs ht =>
    hn ⟨s, (memU s).mp hs, (memV s).mp ht⟩
  have hc : Uᶜ = V := compl_eq_of_disjoint_of_card_add_eq hdisj (by
    rw [cardU, cardV, card_univ, Fintype.card_fin])
  have h (s : Fin 6) : s ∈ U ↔ s ∉ V := by
    rw [← hc]
    simp
  have hp := h p
  have hq := h q
  have hr := h r
  rw [memU, memV] at hp hq hr
  tauto

private theorem alternative_crossing
    (a b s t a' b' s' t' : Bool) (ha : a ≠ b) (ht : s' ≠ t') :
    (s ≠ t ∧ a' ≠ b') ∨
    (a ≠ s ∧ b' ≠ t') ∨ (a ≠ t ∧ b' ≠ s') ∨
    (b ≠ s ∧ a' ≠ t') ∨ (b ≠ t ∧ a' ≠ s') := by
  revert a b s t a' b' s' t' ha ht
  decide +kernel

private theorem cross_bool (A : Point) (i j : Fin 6) :
    decide (i ∈ A) ≠ decide (j ∈ A) ↔ (i ∈ A ↔ j ∉ A) := by
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj]

private theorem repack_disjoint {A B : Point} {a b s t : Fin 6}
    (hA : a ∈ A ↔ b ∉ A) (hB : s ∈ B ↔ t ∉ B)
    (hd : Disjoint ({a, b} : Point) {s, t}) :
    ∃ x, Box A {a, b} x ∧ Box B {s, t} x ∧
      ∃ i, i ∈ ({a, b} : Point) ∆ {s, t} ∧ i ∈ x := by
  have hab : a ≠ b := by intro he; subst b; tauto
  have hst : s ≠ t := by intro he; subst t; tauto
  have has : a ≠ s := fun he => disjoint_left.mp hd
    (show a ∈ ({a,b} : Point) by simp) (by simp [he])
  have hat : a ≠ t := fun he => disjoint_left.mp hd
    (show a ∈ ({a,b} : Point) by simp) (by simp [he])
  have hbs : b ≠ s := fun he => disjoint_left.mp hd
    (show b ∈ ({a,b} : Point) by simp) (by simp [he])
  have hbt : b ≠ t := fun he => disjoint_left.mp hd
    (show b ∈ ({a,b} : Point) by simp) (by simp [he])
  have step (i j k l w : Fin 6) (h₁ : i ∈ A ↔ j ∉ A) (h₂ : k ∈ B ↔ l ∉ B)
      (hu : ({a, b} : Point) ∆ {i, j} = {s, t} ∆ {k, l})
      (hw : w ∈ ({a, b} : Point) ∆ {s, t})
      (hw' : w ∈ ({a, b} : Point) ∆ {i, j}) :
      ∃ x, Box A {a, b} x ∧ Box B {s, t} x ∧
        ∃ i, i ∈ ({a, b} : Point) ∆ {s, t} ∧ i ∈ x := by
    refine ⟨({a,b} : Point) ∆ {i,j}, ⟨i, j, h₁, symmDiff_symmDiff_cancel_left _ _⟩,
      ⟨k, l, h₂, ?_⟩, w, hw, hw'⟩
    rw [hu, symmDiff_symmDiff_cancel_left]
  have h := alternative_crossing (decide (a ∈ A)) (decide (b ∈ A))
    (decide (s ∈ A)) (decide (t ∈ A)) (decide (a ∈ B)) (decide (b ∈ B))
    (decide (s ∈ B)) (decide (t ∈ B)) ((cross_bool A a b).mpr hA) ((cross_bool B s t).mpr hB)
  rcases h with h | h | h | h | h
  · apply step s t a b a ((cross_bool A _ _).mp h.1) ((cross_bool B _ _).mp h.2)
    · exact symmDiff_comm _ _
    · simp [mem_symmDiff, has, hat]
    · simp [mem_symmDiff, has, hat]
  · apply step a s b t b ((cross_bool A _ _).mp h.1) ((cross_bool B _ _).mp h.2)
    · ext i
      simp only [mem_symmDiff, mem_insert, mem_singleton]
      grind
    · simp [mem_symmDiff, hbs, hbt]
    · simp [mem_symmDiff, hab.symm, hbs]
  · apply step a t b s b ((cross_bool A _ _).mp h.1) ((cross_bool B _ _).mp h.2)
    · ext i
      simp only [mem_symmDiff, mem_insert, mem_singleton]
      grind
    · simp [mem_symmDiff, hbs, hbt]
    · simp [mem_symmDiff, hab.symm, hbt]
  · apply step b s a t a ((cross_bool A _ _).mp h.1) ((cross_bool B _ _).mp h.2)
    · ext i
      simp only [mem_symmDiff, mem_insert, mem_singleton]
      grind
    · simp [mem_symmDiff, has, hat]
    · simp [mem_symmDiff, hab, has]
  · apply step b t a s a ((cross_bool A _ _).mp h.1) ((cross_bool B _ _).mp h.2)
    · ext i
      simp only [mem_symmDiff, mem_insert, mem_singleton]
      grind
    · simp [mem_symmDiff, has, hat]
    · simp [mem_symmDiff, hab, hat]

private theorem repack_intersecting {A B : Point} {p q r : Fin 6}
    (hAc : A.card = 3) (hBc : B.card = 3) (hpq : p ≠ q)
    (hA : p ∈ A ↔ r ∉ A) (hB : q ∈ B ↔ r ∉ B) :
    ∃ x, Box A {p, r} x ∧ Box B {q, r} x ∧
      ∃ i, i ∈ ({p, r} : Point) ∆ {q, r} ∧ i ∈ x := by
  obtain ⟨s, hsA, hsB⟩ := flip_pair hAc hBc hA hB
  have hpr : p ≠ r := by intro he; subst r; tauto
  have hqr : q ≠ r := by intro he; subst r; tauto
  have hps : p ≠ s := by intro he; subst s; tauto
  have hqs : q ≠ s := by intro he; subst s; tauto
  let x := ({p, r} : Point) ∆ {q, s}
  have hx : x = ({q, r} : Point) ∆ {p, s} := by
    ext i
    simp only [x, mem_symmDiff, mem_insert, mem_singleton]
    grind
  refine ⟨x, ⟨q, s, hsA, symmDiff_symmDiff_cancel_left _ _⟩, ⟨p, s, hsB, ?_⟩, p, ?_, ?_⟩
  · rw [hx, symmDiff_symmDiff_cancel_left]
  · simp [mem_symmDiff, hpq, hpr]
  · simp [x, mem_symmDiff, hpq, hps]

private theorem box_translate (A c x z : Point) :
    Box A (c ∆ z) (x ∆ z) ↔ Box A c x := by
  unfold Box
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, symmDiff_bot]

private theorem other_axis {A : Point} {a b r : Fin 6} (hc : a ∈ A ↔ b ∉ A)
    (hr : r ∈ ({a,b} : Point)) :
    ∃ p, (p ∈ A ↔ r ∉ A) ∧ ({a,b} : Point) = {p,r} := by
  rcases mem_insert.mp hr with rfl | h
  · exact ⟨b, cross_swap hc, pair_comm _ _⟩
  · obtain rfl := mem_singleton.mp h
    exact ⟨a, hc, rfl⟩

private theorem different_bit_on_overlap {A B c d : Point}
    (hAc : A.card = 3) (hBc : B.card = 3) (hne : c ≠ d)
    (hc : Box A c ∅) (hd : Box B d ∅) :
    ∃ x, Box A c x ∧ Box B d x ∧ ∃ i, i ∈ c ∆ d ∧ i ∈ x := by
  obtain ⟨a,b,hA,hca⟩ := hc
  obtain ⟨s,t,hB,hds⟩ := hd
  rw [show (∅ : Point) = ⊥ from rfl, symmDiff_bot] at hca hds
  subst c
  subst d
  by_cases hdis : Disjoint ({a,b} : Point) {s,t}
  · exact repack_disjoint hA hB hdis
  · obtain ⟨r, hr⟩ := not_disjoint_iff_nonempty_inter.mp hdis
    obtain ⟨p, hp, hpa⟩ := other_axis hA (mem_inter.mp hr).1
    obtain ⟨q, hq, hqa⟩ := other_axis hB (mem_inter.mp hr).2
    rw [hpa, hqa] at hne ⊢
    exact repack_intersecting hAc hBc (fun he => hne (by rw [he])) hp hq

/-- The symmetric-difference action and balance of each cut force two
overlapping boxes with a common height to share their center. -/
theorem center_eq_of_overlap {A B c d z : Point} {height : Point → Fin 6 → ℤ}
    (hAc : A.card = 3) (hBc : B.card = 3)
    (hc : HasHeight height A c) (hd : HasHeight height B d)
    (hzA : Box A c z) (hzB : Box B d z) : c = d := by
  by_contra hne
  have hne' : c ∆ z ≠ d ∆ z := fun h => hne (by
    simpa only [symmDiff_symmDiff_cancel_right] using congrArg (fun x => x ∆ z) h)
  have ha := (box_translate A c z z).mpr hzA
  have hb := (box_translate B d z z).mpr hzB
  rw [symmDiff_self] at ha hb
  obtain ⟨x, hxA, hxB, i, hi, hix⟩ := different_bit_on_overlap hAc hBc hne' ha hb
  let y := x ∆ z
  have hA' : Box A c y := (box_translate A c y z).mp (by
    simpa only [y, symmDiff_symmDiff_cancel_right] using hxA)
  have hB' : Box B d y := (box_translate B d y z).mp (by
    simpa only [y, symmDiff_symmDiff_cancel_right] using hxB)
  obtain ⟨k, hk⟩ := hc
  obtain ⟨l, hl⟩ := hd
  have hz := (hk z hzA i).symm.trans (hl z hzB i)
  have hxC : c ∆ y = (c ∆ z) ∆ x := by
    change c ∆ (x ∆ z) = (c ∆ z) ∆ x
    rw [symmDiff_comm x z, symmDiff_assoc]
  have hxD : d ∆ y = (d ∆ z) ∆ x := by
    change d ∆ (x ∆ z) = (d ∆ z) ∆ x
    rw [symmDiff_comm x z, symmDiff_assoc]
  -- Use the two possible values of the disagreeing coordinate.
  have flipCoord (t : Point) : i ∈ t ∆ x ↔ i ∉ t := by
    simp [mem_symmDiff, hix]
  have hy' := (hk y hA' i).symm.trans (hl y hB' i)
  rw [hxC, hxD] at hy'
  simp only [flipCoord] at hy'
  rcases mem_symmDiff.mp hi with hi | hi
  · simp [hi.1, hi.2] at hz hy'
    omega
  · simp [hi.1, hi.2] at hz hy'
    omega

/-- Crossing pairs characterize boxes with a fixed center. -/
theorem box_pair_iff (A c : Point) (p q : Fin 6) :
    Box A c (c ∆ {p, q}) ↔ (p ∈ A ↔ q ∉ A) := by
  unfold Box
  rw [symmDiff_symmDiff_cancel_left]
  constructor
  · rintro ⟨i, j, hij, he⟩
    have hne : i ≠ j := by intro h; subst j; tauto
    have hi : i ∈ ({p, q} : Point) := by rw [he]; simp
    have hj : j ∈ ({p, q} : Point) := by rw [he]; simp
    simp only [mem_insert, mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hne rfl).elim
    · exact hij
    · exact cross_swap hij
    · exact (hne rfl).elim
  · exact fun h => ⟨p, q, h, rfl⟩

end Q9CutBoxRigidity
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

open Finset
open scoped symmDiff

private theorem card_add_card_eq_card_symmDiff_add_twice_inter {ι : Type*}
    [DecidableEq ι] (A B : Finset ι) :
    A.card + B.card = (A ∆ B).card + 2 * (A ∩ B).card := by
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [Finset.symmDiff_def, card_union_of_disjoint hdis]
  have hA := card_sdiff_add_card_inter A B
  have hB := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at hB
  omega

/-- Pairwise odd symmetric differences separate a finite family of
membership signatures into at most two signatures. The separating map is
cardinality modulo two. -/
theorem card_le_two_of_odd_symmDiff {ι : Type*} [DecidableEq ι] (F : Finset (Finset ι))
    (h : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∆ B).card % 2 = 1) : F.card ≤ 2 := by
  let parity (A : Finset ι) : Fin 2 := ⟨A.card % 2, Nat.mod_lt _ (by decide)⟩
  have hInj : (F : Set (Finset ι)).InjOn parity := by
    intro A hA B hB heq
    by_contra hne
    have hParity := congrArg Fin.val heq
    change A.card % 2 = B.card % 2 at hParity
    have hOdd := h A hA B hB hne
    have hsum := card_add_card_eq_card_symmDiff_add_twice_inter A B
    omega
  have hcard := card_le_card_of_injOn parity
    (t := (univ : Finset (Fin 2))) (fun _ _ => mem_univ _) hInj
  simpa only [card_univ, Fintype.card_fin] using hcard

open scoped Classical in
/-- If every separated pair is cut an odd number of times, all nonconstant
cuts separate the same pairs. Removing constant cuts is unnecessary. -/
theorem same_separation_of_odd_cut_multiplicity {α ι : Type*} [Fintype ι]
    (cut : ι → α → Bool)
    (hodd : ∀ x y : α, (univ.filter fun i => cut i x ≠ cut i y).Nonempty →
      (univ.filter fun i => cut i x ≠ cut i y).card % 2 = 1)
    (i j : ι) (hi : ∃ x y, cut i x ≠ cut i y) (hj : ∃ x y, cut j x ≠ cut j y)
    (x y : α) : cut i x ≠ cut i y ↔ cut j x ≠ cut j y := by
  classical
  let code (z : α) : Finset ι := univ.filter fun k => cut k z = true
  let parity (z : α) : ℕ := (code z).card % 2
  have hparity (z : α) : parity z < 2 := Nat.mod_lt _ (by decide)
  have hcode {u v : α} (hp : parity u = parity v) : code u = code v := by
    by_contra hne
    have hdiff : code u ∆ code v = univ.filter fun k => cut k u ≠ cut k v := by
      ext k
      simp only [Finset.mem_symmDiff, code, mem_filter, mem_univ, true_and]
      cases cut k u <;> cases cut k v <;> decide
    have hmult := hodd u v (hdiff ▸ Finset.symmDiff_nonempty.mpr hne)
    rw [← hdiff] at hmult
    have hsum := card_add_card_eq_card_symmDiff_add_twice_inter (code u) (code v)
    change (code u).card % 2 = (code v).card % 2 at hp
    omega
  have same (k : ι) {u v : α} (h : parity u = parity v) : cut k u = cut k v := by
    have hk : (cut k u = true ↔ cut k v = true) := by
      have hc : k ∈ code u ↔ k ∈ code v := by rw [hcode h]
      simpa only [code, mem_filter, mem_univ, true_and] using hc
    exact Bool.eq_iff_iff.mpr hk
  have separate (k : ι) (h : ∃ u v, cut k u ≠ cut k v) {a z : α}
      (hp : parity a ≠ parity z) : cut k a ≠ cut k z := by
    obtain ⟨u,v,huv⟩ := h
    intro heq
    have matchPair (w : α) : parity w = parity a ∨ parity w = parity z := by
      have ha := hparity a
      have hz := hparity z
      have hw := hparity w
      omega
    have hw (w : α) : cut k w = cut k a :=
      (matchPair w).elim (same k) (fun h => (same k h).trans heq.symm)
    exact huv ((hw u).trans (hw v).symm)
  exact ⟨fun h => separate j hj (fun hp => h (same i hp)),
    fun h => separate i hi (fun hp => h (same j hp))⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CutBoxRigidity

open Finset
open scoped symmDiff

private theorem same_center_along_overlap {ι : Type*} (cut center : ι → Point)
    (hcard : ∀ i, (cut i).card = 3) {height : Point → Fin 6 → ℤ}
    (hheight : ∀ i, HasHeight height (cut i) (center i))
    {i j : ι} (hpath : Relation.ReflTransGen
      (fun u v => ∃ x, Box (cut u) (center u) x ∧ Box (cut v) (center v) x) i j) :
    center i = center j := by
  induction hpath with
  | refl => rfl
  | @tail u v _ hEdge ih =>
    obtain ⟨x, hux, hvx⟩ := hEdge
    exact ih.trans (center_eq_of_overlap (hcard u) (hcard v) (hheight u) (hheight v) hux hvx)

private theorem same_separator_bits (a b c d : Bool)
    (h : (a ≠ c ↔ b ≠ d)) : (a = b ↔ c = d) := by
  revert a b c d h
  decide +kernel

open scoped Classical in
/-- A connected family of balanced cut boxes whose occupied points have
odd multiplicity admits only one center and one unordered cut. -/
theorem same_cut_of_connected_odd_box_fibers {ι : Type*} [Fintype ι]
    (cut center : ι → Point) (hcard : ∀ i, (cut i).card = 3)
    {height : Point → Fin 6 → ℤ}
    (hheight : ∀ i, HasHeight height (cut i) (center i))
    (hconn : ∀ i j, Relation.ReflTransGen
      (fun u v => ∃ x, Box (cut u) (center u) x ∧ Box (cut v) (center v) x) i j)
    (hodd : ∀ x : Point, (univ.filter fun i => Box (cut i) (center i) x).Nonempty →
      (univ.filter fun i => Box (cut i) (center i) x).card % 2 = 1)
    (i j : ι) : center i = center j ∧ (cut i = cut j ∨ cut i = (cut j)ᶜ) := by
  classical
  have hcent (u v : ι) : center u = center v :=
    same_center_along_overlap cut center hcard hheight (hconn u v)
  refine ⟨hcent i j, ?_⟩
  let code (u : ι) (k : Fin 6) : Bool := decide (k ∈ cut u)
  have hsep (u : ι) (p q : Fin 6) :
      code u p ≠ code u q ↔ Box (cut u) (center u) (center i ∆ {p,q}) := by
    rw [hcent u i, box_pair_iff]
    by_cases hp : p ∈ cut u <;> by_cases hq : q ∈ cut u <;> simp [code, hp, hq]
  have hcode (p q : Fin 6) : (univ.filter fun u => code u p ≠ code u q).Nonempty →
      (univ.filter fun u => code u p ≠ code u q).card % 2 = 1 := by
    simpa only [hsep] using hodd (center i ∆ {p,q})
  have nonconstant (u : ι) : ∃ p q, code u p ≠ code u q := by
    obtain ⟨p,hp⟩ := card_pos.mp (show 0 < (cut u).card by rw [hcard]; decide)
    obtain ⟨q,hq⟩ := card_pos.mp (show 0 < (cut u)ᶜ.card by
      rw [card_compl, Fintype.card_fin, hcard]; decide)
    exact ⟨p,q,by simp [code, hp, mem_compl.mp hq]⟩
  have sameSep (p q : Fin 6) : code i p ≠ code i q ↔ code j p ≠ code j q :=
    same_separation_of_odd_cut_multiplicity code hcode i j (nonconstant i) (nonconstant j) p q
  let zero : Fin 6 := 0
  by_cases hbase : code i zero = code j zero
  · left
    ext p
    have he : code i p = code j p := (same_separator_bits _ _ _ _ (sameSep zero p)).mp hbase
    simpa only [code, decide_eq_decide] using he
  · right
    ext p
    have he : code i p ≠ code j p :=
      fun hp => hbase ((same_separator_bits _ _ _ _ (sameSep zero p)).mpr hp)
    rw [mem_compl]
    by_cases h₁ : p ∈ cut i <;> by_cases h₂ : p ∈ cut j <;> simp [code, h₁, h₂] at he ⊢

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CutBoxRigidity

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9LaurentCommonTriple (Axes inside outside commonAxes UniqueCommonNeighbor fiber star)
open Q9LaurentGainPartition (Side)
open private mem_transverseSide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentTransverseFibers
open private star_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentCommonTriple

private theorem eq_of_charts {e : Axes} {x y : Q 9}
    (hi : inside e x = inside e y) (ho : outside e x = outside e y) :
    x = y := by
  funext k
  obtain ⟨i, rfl⟩ := e.surjective k
  cases i with
  | inl j => exact congrFun hi j
  | inr j => exact congrFun ho j

open scoped Classical in
/-- For an actual common-star cover, realize each transverse component by
one balanced cut box. If every two-step move stays in a component or fixes
the projected point, all realized boxes have the same unordered cut. -/
theorem same_cut_of_realized_common_star_boxes
    {C : Finset (Q 9)} {b : Bool} {e : Axes}
    (hconn : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcommon : UniqueCommonNeighbor C b e)
    (encode : Q 6 ≃ Q9CutBoxRigidity.Point)
    (cut center : Quotient (transverseComponents (C := C) (b := b) (commonAxes e)) →
      Q9CutBoxRigidity.Point)
    (hcard : ∀ i, (cut i).card = 3)
    {height : Q9CutBoxRigidity.Point → Fin 6 → ℤ}
    (hheight : ∀ i, Q9CutBoxRigidity.HasHeight height (cut i) (center i))
    (hrealize : ∀ i p, Q9CutBoxRigidity.Box (cut i) (center i) p ↔
      ∃ x : Side C b, Quotient.mk _ x = i ∧ encode (outside e x.val) = p)
    (hstep : ∀ (x y : Side C b) (v : ↥C),
      ((hypercube 9).induce (C : Set (Q 9))).Adj ⟨x.val,x.property.1⟩ v →
      ((hypercube 9).induce (C : Set (Q 9))).Adj v ⟨y.val,y.property.1⟩ →
      (transverseComponents (commonAxes e)).r x y ∨ outside e x.val = outside e y.val)
    (i j : Quotient (transverseComponents (C := C) (b := b) (commonAxes e))) :
    center i = center j ∧ (cut i = cut j ∨ cut i = (cut j)ᶜ) := by
  classical
  let K := Quotient (transverseComponents (C := C) (b := b) (commonAxes e))
  let q : Side C b → K := Quotient.mk _
  have surj : Function.Surjective q := Quotient.mk_surjective
  let _ : Fintype K := Fintype.ofSurjective q surj
  let proj (x : Side C b) := encode (outside e x.val)
  have hbox (x : Side C b) : Q9CutBoxRigidity.Box (cut (q x)) (center (q x)) (proj x) :=
    (hrealize _ _).mpr ⟨x, rfl, rfl⟩
  apply Q9CutBoxRigidity.same_cut_of_connected_odd_box_fibers cut center hcard hheight ?_ ?_ i j
  · intro u v
    obtain ⟨x, rfl⟩ := surj u
    obtain ⟨y, rfl⟩ := surj v
    apply Q9ProjectedWalk.projected_of_connected q hconn ?_ x y
    intro z w v hz hw
    rcases hstep z w v hz hw with h | h
    · have he : q z = q w := Quotient.sound h
      rw [he]
    · apply Relation.ReflTransGen.single
      refine ⟨proj z, hbox z, ?_⟩
      have hep : proj z = proj w := congrArg encode h
      rw [hep]
      exact hbox w
  · intro p hp
    obtain ⟨k,hk⟩ := hp
    obtain ⟨x,_,hx⟩ := (hrealize _ _).mp (mem_filter.mp hk).2
    obtain ⟨c,_,_,hf⟩ := Q9LaurentCommonTriple.exists_star_over_projection hcommon x
    let F := fiber C b e (outside e x.val)
    have hF : F.card = 3 := by rw [show F = star e c from hf, star_card]
    let s (z : ↥F) : Side C b :=
      ⟨z.val, (mem_filter.mp z.property).1, (mem_filter.mp z.property).2.1⟩
    have hout (z : ↥F) : outside e (s z).val = outside e x.val :=
      (mem_filter.mp z.property).2.2
    have injective : Function.Injective (q ∘ s) := by
      intro z w h
      have hrel : (transverseComponents (commonAxes e)).r (s z) (s w) := Quotient.exact h
      have hin := inside_eq_on_transverseSide rfl (mem_transverseSide.mpr hrel)
      exact Subtype.ext (eq_of_charts hin.symm ((hout z).trans (hout w).symm))
    have image_eq : F.attach.image (q ∘ s) =
        (univ : Finset K).filter (fun z => Q9CutBoxRigidity.Box (cut z) (center z) p) := by
      ext w
      constructor
      · intro hw
        obtain ⟨z,_,rfl⟩ := mem_image.mp hw
        exact mem_filter.mpr ⟨mem_univ _, (hrealize _ _).mpr
          ⟨s z, rfl, (congrArg encode (hout z)).trans hx⟩⟩
      · intro hw
        obtain ⟨z,hz,hp'⟩ := (hrealize _ _).mp (mem_filter.mp hw).2
        have ho := encode.injective (hp'.trans hx.symm)
        have hmem : z.val ∈ F := mem_filter.mpr ⟨z.property.1,z.property.2,ho⟩
        exact mem_image.mpr ⟨⟨z.val,hmem⟩,mem_attach _ _,hz⟩
    rw [← image_eq, card_image_of_injective _ injective, card_attach, hF]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions
