/- GID: D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Span.Defs]
   utility: none
   digest: Exact Boolean coverage descends after deleting two private original indices. -/

import D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-! Exact proper Boolean coverage descends under deletion of two private indices. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
open scoped BigOperators
open Finset
universe u
variable {X : Type u} [DecidableEq X]

/-- Coefficient-one Boolean row in the unchanged original coordinate space. -/
def row (A : Finset X) : X → ℤ := fun i => if i ∈ A then 1 else 0

/-- The complete proper Boolean family of an exact integer submodule. -/
def Complete (M : Submodule ℤ (X → ℤ)) (E A : Finset X) : Prop :=
  A ⊆ E ∧ A.Nonempty ∧ A ≠ E ∧ row A ∈ M

/-- Inclusion minimality in the complete family, not cardinality minimality. -/
def Minimal (M : Submodule ℤ (X → ℤ)) (E S : Finset X) : Prop :=
  Complete M E S ∧ ∀ B, Complete M E B → B ⊆ S → B = S

/-- Every literal enumeration is covered by a nonempty proper interval. -/
def Covers (M : Submodule ℤ (X → ℤ)) (E : Finset X) : Prop :=
  ∀ w : List X, w.Nodup → w.toFinset = E →
    ∃ t : List X, t <:+: w ∧ Complete M E t.toFinset

private theorem row_sub {A B : Finset X} (h : B ⊆ A) :
    row (A \ B) = row A - row B := by
  ext i
  by_cases hb : i ∈ B
  · have ha := h hb
    simp [row,hb,ha]
  · by_cases ha : i ∈ A <;> simp [row,hb,ha]

private theorem private_contains (M : Submodule ℤ (X → ℤ)) (E S : Finset X)
    (p : X)
    (hp : ∀ B, Minimal M E B → p ∈ B → B = S) :
    ∀ A, Complete M E A → p ∈ A → S ⊆ A := by
  classical
  intro A
  induction A using Finset.strongInductionOn
  rename_i A ih
  intro hA hpA
  let F := A.powerset.filter (fun B => B.Nonempty ∧ row B ∈ M)
  obtain ⟨B,hBF,hmin⟩ := Finset.exists_min_image F Finset.card
    ⟨A, by simp [F, hA.2.1, hA.2.2.2]⟩
  have hB : B ⊆ A ∧ B.Nonempty ∧ row B ∈ M := by simpa [F] using hBF
  have hBA := hB.1
  have hBC : Complete M E B := ⟨hBA.trans hA.1, hB.2.1,
    fun he => hA.2.2.1 (Finset.Subset.antisymm hA.1 (he ▸ hBA)), hB.2.2⟩
  have hBM : Minimal M E B := by
    refine ⟨hBC, ?_⟩
    intro D hD hDB
    apply Finset.eq_of_subset_of_card_le hDB
    exact hmin D (by simp [F, hDB.trans hBA, hD.2.1, hD.2.2.2])
  by_cases hpB : p ∈ B
  · rw [← hp B hBM hpB]
    exact hBA
  · have hR : Complete M E (A \ B) := by
      refine ⟨Finset.sdiff_subset.trans hA.1,
        ⟨p, mem_sdiff.mpr ⟨hpA, hpB⟩⟩, ?_, ?_⟩
      · intro he
        exact hA.2.2.1 (Finset.Subset.antisymm hA.1 (he ▸ Finset.sdiff_subset))
      · rw [row_sub hBA]
        exact M.sub_mem hA.2.2.2 hB.2.2
    have hlt : A \ B ⊂ A := Finset.sdiff_ssubset hBA hB.2.1
    exact (ih _ hlt hR (mem_sdiff.mpr ⟨hpA,hpB⟩)).trans Finset.sdiff_subset

omit [DecidableEq X] in
private theorem infix_avoid_cons {a : X} {t w : List X}
    (h : t <:+: a :: w) (hn : a ∉ t) : t <:+: w := by
  rcases List.infix_cons_iff.mp h with h | h
  · cases t with
    | nil => exact List.nil_infix
    | cons b t =>
      obtain ⟨q,hq⟩ := h
      have he : b = a := by simpa using congrArg List.head? hq
      exact (hn (by simp [he])).elim
  · exact h

omit [DecidableEq X] in
theorem infix_avoid_separator {a : X} {t l r : List X}
    (h : t <:+: l ++ a :: r) (hn : a ∉ t) : t <:+: l ∨ t <:+: r := by
  rcases List.infix_append_iff_ne_nil.mp h with h | h | ⟨s,q,hs,hq,he,hsl,hqr⟩
  · exact Or.inl h
  · exact Or.inr (infix_avoid_cons h hn)
  · cases q with
    | nil => exact (hq rfl).elim
    | cons b q =>
      obtain ⟨z,hz⟩ := hqr
      have hb : b = a := by simpa using congrArg List.head? hz
      exact (hn (by simp [he, hb])).elim

omit [DecidableEq X] in
private theorem prefix_empty_of_head {a : X} {w p t q : List X}
    (hn : (a :: w).Nodup) (he : p ++ t ++ q = a :: w) (ha : a ∈ t) : p = [] := by
  cases p with
  | nil => rfl
  | cons b p =>
    have hb : b = a := by simpa using congrArg List.head? he
    have hn' : (b :: (p ++ t ++ q)).Nodup := by
      have hnn := hn
      rw [← he] at hnn
      simpa only [List.cons_append] using hnn
    exact ((List.nodup_cons.mp hn').1 (by simp [hb, ha])).elim

omit [DecidableEq X] in
private theorem infix_endpoints {a b : X} {l t : List X}
    (hn : (a :: (l ++ [b])).Nodup) (ht : t <:+: a :: (l ++ [b]))
    (ha : a ∈ t) (hb : b ∈ t) : t = a :: (l ++ [b]) := by
  obtain ⟨p,q,he⟩ := ht
  have hp := prefix_empty_of_head hn he ha
  have hrev : q.reverse ++ t.reverse ++ p.reverse = b :: (l.reverse ++ [a]) := by
    simpa [List.reverse_append, List.append_assoc] using congrArg List.reverse he
  have hnrev : (b :: (l.reverse ++ [a])).Nodup := by
    simpa [List.reverse_append, List.append_assoc] using (List.nodup_reverse.mpr hn)
  have hq := prefix_empty_of_head hnrev hrev (by simpa using hb)
  have hq' : q = [] := by simpa using hq
  simpa [hp,hq'] using he

private theorem order_insert {E : Finset X} {u v : X} (hu : u ∈ E) (hv : v ∈ E)
    (huv : u ≠ v) {b : List X} (hb : b.Nodup)
    (he : b.toFinset = (E.erase u).erase v) :
    (u :: (b ++ [v])).Nodup ∧ (u :: (b ++ [v])).toFinset = E := by
  have hbu : u ∉ b := by
    intro h
    have := he ▸ List.mem_toFinset.mpr h
    simp at this
  have hbv : v ∉ b := by
    intro h
    have := he ▸ List.mem_toFinset.mpr h
    simp at this
  constructor
  · simp only [List.nodup_cons, List.mem_append, List.mem_singleton]
    refine ⟨by simp [hbu,huv], List.nodup_append.mpr ⟨hb,by simp,?_⟩⟩
    intro x hx y hy hxy
    have hyv : y = v := by simpa using hy
    subst y
    subst x
    exact hbv hx
  · ext i
    simp only [List.toFinset_cons, List.toFinset_append, List.toFinset_nil,
      mem_insert, mem_union, Finset.notMem_empty, or_false, he, mem_erase]
    by_cases hiu : i = u <;> by_cases hiv : i = v <;> simp_all

private def mass (w : List X) : X → ℤ := (w.map (fun i => Pi.single i (1 : ℤ))).sum

private theorem mass_row {w : List X} (hn : w.Nodup) : mass w = row w.toFinset := by
  rw [mass, ← List.sum_toFinset _ hn]
  ext i
  simp [row, Pi.single_apply]

private theorem proper_infix {E : Finset X} {w t : List X}
    (hn : w.Nodup) (he : w.toFinset = E) (hi : t <:+: w)
    (ht : t ≠ []) (hl : t.length < w.length) :
    t.toFinset ⊆ E ∧ t.toFinset.Nonempty ∧ t.toFinset ≠ E := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi'
    rw [← he]
    exact List.mem_toFinset.mpr (hi.subset (List.mem_toFinset.mp hi'))
  · simpa using ht
  · intro h
    have hc := List.toFinset_card_of_nodup (hi.nodup hn)
    have hd := List.toFinset_card_of_nodup hn
    rw [h, ← he] at hc
    omega

private theorem circular_extract (M : Submodule ℤ (X → ℤ))
    {Y : Finset X} {b c t : List X} (hb : b.Nodup) (he : b.toFinset = Y)
    (hr : c.IsRotated b) (hi : t <:+: c) (ht : t ≠ [])
    (hl : t.length < c.length) (hy : row Y ∈ M) (hm : row t.toFinset ∈ M) :
    ∃ d : List X, d <:+: b ∧ Complete M Y d.toFinset := by
  obtain ⟨p,q,hpq⟩ := hi
  let k := q ++ p
  have hc : c.Nodup := hr.perm.nodup_iff.mpr hb
  have hperm : (t ++ k).Perm c := by
    rw [← hpq]
    dsimp [k]
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := p) (l₂ := t ++ q)).symm
  have hk : k.Nodup := (List.nodup_append.mp (hperm.nodup_iff.mpr hc)).2.1
  have htn : t.Nodup := (List.nodup_append.mp (hperm.nodup_iff.mpr hc)).1
  have hk0 : k ≠ [] := by
    intro hz
    have hlen := hperm.length_eq
    simp [hz] at hlen
    omega
  have hkl : k.length < b.length := by
    have hlen := hperm.length_eq
    have hlen' := hr.perm.length_eq
    have hpos := List.length_pos_iff.mpr ht
    simp only [List.length_append] at hlen
    omega
  have htl : t.length < b.length := by have := hr.perm.length_eq; omega
  have hsum : mass t + mass k = row Y := by
    have hh := ((hperm.trans hr.perm).map (fun i => Pi.single i (1 : ℤ))).sum_eq
    change mass (t ++ k) = mass b at hh
    rw [mass_row hb,he] at hh
    simpa [mass,List.map_append,List.sum_append] using hh
  have hkm : row k.toFinset ∈ M := by
    have hkEq : row k.toFinset = row Y - row t.toFinset := by
      rw [← mass_row hk, ← mass_row htn, ← hsum]
      abel
    rw [hkEq]
    exact M.sub_mem hy hm
  have hrot : (t ++ k).IsRotated b := by
    apply List.IsRotated.trans _ hr
    rw [← hpq]
    simpa [k,List.append_assoc] using (List.isRotated_append (l := p) (l' := t ++ q)).symm
  rcases ZeroTotalCircleGood.rotated_two_runs hrot with ⟨l,r,hlr⟩ | ⟨l,r,hlr⟩
  · have hi' : t <:+: b := ⟨l,r,hlr.symm⟩
    obtain ⟨hs,hn,hp⟩ := proper_infix hb he hi' ht htl
    exact ⟨t,hi',hs,hn,hp,hm⟩
  · have hi' : k <:+: b := ⟨l,r,hlr.symm⟩
    obtain ⟨hs,hn,hp⟩ := proper_infix hb he hi' hk0 hkl
    exact ⟨k,hi',hs,hn,hp,hkm⟩

private theorem coverage_delete (M : Submodule ℤ (X → ℤ)) {E : Finset X}
    (hcover : Covers M E) {u v x : X} (hu : u ∈ E) (hv : v ∈ E) (huv : u ≠ v)
    (hx : x ∈ (E.erase u).erase v) (hsize : 2 ≤ ((E.erase u).erase v).card)
    (hpair : ∀ A, Complete M E A → (u ∈ A ∨ v ∈ A) → u ∈ A ∧ v ∈ A ∧ x ∈ A) :
    Covers M ((E.erase u).erase v) := by
  classical
  let Y := (E.erase u).erase v
  change 2 ≤ Y.card at hsize
  intro b hb he
  have direct : ∀ {c : List X}, c.Nodup → c.toFinset = Y →
      ∀ t, t <:+: u :: (c ++ [v]) → Complete M E t.toFinset →
      u ∉ t ∧ v ∉ t := by
    intro c hc hce t ht hC
    have hw := order_insert hu hv huv hc hce
    have avoid : ¬ (u ∈ t ∨ v ∈ t) := by
      intro hhit
      have hh := hpair t.toFinset hC (by simpa using hhit)
      have hf := infix_endpoints hw.1 ht (by simpa using hh.1) (by simpa using hh.2.1)
      exact hC.2.2.1 (by rw [hf,hw.2])
    simpa only [not_or] using avoid
  by_cases hy : row Y ∈ M
  · have hxb : x ∈ b := by rw [← List.mem_toFinset,he]; exact hx
    obtain ⟨l,r,hbSplit⟩ := List.mem_iff_append.mp hxb
    let c := r ++ l ++ [x]
    have hr : c.IsRotated b := by
      rw [hbSplit]
      simpa [c,List.append_assoc] using
        (List.isRotated_append (l := r) (l' := l ++ [x]))
    have hc : c.Nodup := hr.perm.nodup_iff.mpr hb
    have hce : c.toFinset = Y := by
      calc
        c.toFinset = b.toFinset := by
          ext i
          simp only [List.mem_toFinset]
          exact hr.perm.mem_iff
        _ = Y := he
    have hclen : 2 ≤ c.length := by
      have hh := List.toFinset_card_of_nodup hc
      rw [hce] at hh
      omega
    have hrl : r ++ l ≠ [] := by
      intro hz
      have hc1 : c = [x] := by
        simpa only [c,List.append_assoc,List.nil_append] using
          congrArg (fun z : List X => z ++ [x]) hz
      rw [hc1] at hclen
      simp at hclen
    obtain ⟨a,d,had⟩ := List.exists_cons_of_ne_nil hrl
    have hcd : c = a :: (d ++ [x]) := by
      simpa only [c,List.append_assoc,List.cons_append] using
        congrArg (fun z : List X => z ++ [x]) had
    let w := u :: a :: v :: (d ++ [x])
    have hwperm : w.Perm (u :: (c ++ [v])) := by
      rw [hcd]
      exact List.Perm.cons u (List.Perm.cons a (by
        simpa [List.append_assoc] using
          (List.perm_middle (a := v) (l₁ := d ++ [x]) (l₂ := [])).symm))
    have hwbase := order_insert hu hv huv hc hce
    have hwn : w.Nodup := hwperm.nodup_iff.mpr hwbase.1
    have hwe : w.toFinset = E := by
      calc
        w.toFinset = (u :: (c ++ [v])).toFinset := by
          ext i
          simp only [List.mem_toFinset]
          exact hwperm.mem_iff
        _ = E := hwbase.2
    obtain ⟨t,ht,hC⟩ := hcover w hwn hwe
    have hav : u ∉ t ∧ v ∉ t := by
      have avoid : ¬ (u ∈ t ∨ v ∈ t) := by
        intro hhit
        have hh := hpair t.toFinset hC (by simpa using hhit)
        have hwend : w = u :: ((a :: v :: d) ++ [x]) := by simp [w]
        have hf := infix_endpoints (hwend ▸ hwn) (hwend ▸ ht)
          (by simpa using hh.1) (by simpa using hh.2.2)
        exact hC.2.2.1 (by rw [hf,← hwend,hwe])
      simpa only [not_or] using avoid
    have hparts : t <:+: [a] ∨ t <:+: d ++ [x] := by
      apply infix_avoid_separator (a := v) _ hav.2
      exact infix_avoid_cons ht hav.1
    have hti : t <:+: c := by
      rw [hcd]
      rcases hparts with h | h
      · exact List.infix_append_of_infix_left (l₃ := d ++ [x]) h
      · exact List.infix_cons h
    have htl : t.length < c.length := by
      rcases hparts with h | h
      · have := h.length_le
        simp only [List.length_singleton] at this
        omega
      · have := h.length_le
        rw [hcd]
        simp only [List.length_cons]
        omega
    have htne : t ≠ [] := by simpa using hC.2.1
    exact circular_extract M hb he hr hti htne htl hy hC.2.2.2
  · have hw := order_insert hu hv huv hb he
    obtain ⟨t,ht,hC⟩ := hcover _ hw.1 hw.2
    have ha := direct hb he t ht hC
    have hti : t <:+: b := by
      have hh := infix_avoid_cons ht ha.1
      rcases infix_avoid_separator hh ha.2 with h | h
      · exact h
      · have ht0 : t = [] := by simpa using h
        have hn := hC.2.1
        simp [ht0] at hn
    refine ⟨t,hti,?_,hC.2.1,?_,hC.2.2.2⟩
    · intro i hi
      rw [← he]
      exact List.mem_toFinset.mpr (hti.subset (List.mem_toFinset.mp hi))
    · intro hf
      exact hy (by simpa only [hf] using hC.2.2.2)

/-- Extension by zero preserves the actual original indices. -/
def embed (Y : Finset X) : (Y → ℤ) →ₗ[ℤ] (X → ℤ) where
  toFun f i := if h : i ∈ Y then f ⟨i,h⟩ else 0
  map_add' f g := by ext i; by_cases h : i ∈ Y <;> simp [h]
  map_smul' a f := by ext i; by_cases h : i ∈ Y <;> simp [h]

/-- Exact integer span of ALL proper reduced Boolean rows whose images lie in M. -/
def reducedSpan (M : Submodule ℤ (X → ℤ)) (Y : Finset X) : Submodule ℤ (Y → ℤ) :=
  Submodule.span ℤ (row '' {B : Finset Y | B.Nonempty ∧ B ≠ univ ∧
    row (B.image Subtype.val) ∈ M})

private theorem embed_row (Y : Finset X) (B : Finset Y) :
    embed Y (row B) = row (B.image Subtype.val) := by
  ext i
  by_cases hi : i ∈ Y
  · simp only [embed,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_left hi,row]
    congr 1
    apply propext
    constructor
    · intro h
      exact mem_image.mpr ⟨⟨i,hi⟩,h,rfl⟩
    · rintro h
      obtain ⟨j,hj,hji⟩ := mem_image.mp h
      have hjEq : j = ⟨i,hi⟩ := Subtype.ext hji
      simpa [hjEq] using hj
  · have hn : i ∉ B.image Subtype.val := by
      rintro h
      obtain ⟨j,_,rfl⟩ := mem_image.mp h
      exact hi j.property
    simp [embed,row,hi,hn]

private theorem reduced_span_embeds (M : Submodule ℤ (X → ℤ)) (Y : Finset X) :
    ∀ z ∈ reducedSpan M Y, embed Y z ∈ M := by
  have hle : reducedSpan M Y ≤ M.comap (embed Y) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨B,hB,rfl⟩
    change embed Y (row B) ∈ M
    rw [embed_row]
    exact hB.2.2
  exact fun z hz => hle hz

/-- A private pair in one minimal support of size at least three gives exact
coverage descent. Other minimal supports can have arbitrary cardinalities.
The reduced full support is excluded even when its row belongs to M. -/
theorem private_pair_exact_boolean_descent (M : Submodule ℤ (X → ℤ))
    (E S : Finset X) (hcover : Covers M E) (hS : Minimal M E S)
    (hsize : 3 ≤ S.card) (u v : X) (huS : u ∈ S) (hvS : v ∈ S) (huv : u ≠ v)
    (hprivate : ∀ B, Minimal M E B → (u ∈ B ∨ v ∈ B) → B = S) :
    let Y := (E.erase u).erase v
    Covers M Y ∧ Y.card + 2 = E.card ∧
    (∀ z ∈ reducedSpan M Y, embed Y z ∈ M) ∧
    (∀ B : Finset Y, B.Nonempty → B ≠ univ →
      (row B ∈ reducedSpan M Y ↔ row (B.image Subtype.val) ∈ M)) ∧
    (∀ i : Y, embed Y (Pi.single i (1 : ℤ)) = Pi.single i.val 1) ∧
    (∀ i j : Y, embed Y ((Pi.single i (1 : ℤ) : Y → ℤ) - Pi.single j (1 : ℤ)) =
      (Pi.single i.val (1 : ℤ) : X → ℤ) - Pi.single j.val (1 : ℤ)) := by
  classical
  let Y := (E.erase u).erase v
  have hu := hS.1.1 huS
  have hv := hS.1.1 hvS
  have hve : v ∈ E.erase u := by simp [huv.symm,hv]
  have hcard : Y.card + 2 = E.card := by
    dsimp [Y]
    rw [card_erase_of_mem hve,card_erase_of_mem hu]
    have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS.1.1,hS.1.2.2.1⟩)
    omega
  have hYsize : 2 ≤ Y.card := by
    have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS.1.1,hS.1.2.2.1⟩)
    omega
  obtain ⟨x,hxS,hxP⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({u,v} : Finset X)) (t := S) (by simp [huv]; omega)
  have hx : x ∈ Y := by
    simp only [mem_insert,mem_singleton,not_or] at hxP
    simp [Y,hxP.1,hxP.2,hS.1.1 hxS]
  have hcontainsU := private_contains M E S u
    (fun B hB hp => hprivate B hB (Or.inl hp))
  have hcontainsV := private_contains M E S v
    (fun B hB hp => hprivate B hB (Or.inr hp))
  have hcov : Covers M Y := by
    apply coverage_delete M hcover hu hv huv hx hYsize
    intro A hA hhit
    have hSA : S ⊆ A := hhit.elim (hcontainsU A hA) (hcontainsV A hA)
    exact ⟨hSA huS,hSA hvS,hSA hxS⟩
  have hunit : ∀ i : Y, embed Y (Pi.single i (1 : ℤ)) = Pi.single i.val 1 := by
    intro i
    ext j
    by_cases hj : j ∈ Y
    · simp [embed,hj,Pi.single_apply,Subtype.ext_iff]
    · have hji : j ≠ i.val := by rintro rfl; exact hj i.property
      simp [embed,hj,hji]
  refine ⟨hcov,hcard,reduced_span_embeds M Y,?_,hunit,?_⟩
  · intro B hn hp
    constructor
    · intro h
      have hh := reduced_span_embeds M Y (row B) h
      rwa [embed_row] at hh
    · intro h
      apply Submodule.subset_span
      exact ⟨B,⟨hn,hp,h⟩,rfl⟩
  · intro i j
    rw [map_sub,hunit i,hunit j]

end D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
