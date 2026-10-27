/- GID: D5/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/ZeroPairGoodOrdering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original zero-pair orderings and exact integral disjoint-support extraction. -/

import D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
import D5.S1.Words.Sequenceability.SeparatedPrefixReflection
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
The full word is exempt, with no restriction on its total. Auxiliary prefix
avoidance is consumed by an ordering of the original indices. The integral
consumer uses the exact integer quotient, never its rational saturation.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering

open Finset
open scoped BigOperators Classical
open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum (Good)
open D5.S1.Words.Sequenceability.SeparatedPrefixReflection (pref)

variable {ι G : Type*} [AddCommGroup G]

private theorem sum_order (a : ι → G) {C : Finset ι} {w : List ι}
    (hw : w.Perm C.toList) : (w.map a).sum = ∑ x ∈ C, a x := by
  simpa using (hw.map a).sum_eq

private theorem next_choice (a : ι → G) (ha : Function.Injective a)
    (C : Finset ι) (f g : G) (hcard : 1 < C.card)
    (hmiss : (∑ x ∈ C, a x) - f ∉ C.image a ∨
      (∑ x ∈ C, a x) - g ∉ C.image a) :
    ∃ x ∈ C, a x ≠ f ∧ a x ≠ g := by
  by_contra hn
  have hall : ∀ x ∈ C, a x = f ∨ a x = g := by
    intro x hx
    by_cases hf : a x = f
    · exact Or.inl hf
    · right
      by_contra hg
      exact hn ⟨x,hx,hf,hg⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  have haxy : a x ≠ a y := fun h => hxy (ha h)
  have hC : C = {x, y} := by
    ext z
    constructor
    · intro hz
      have := hall z hz
      have := hall x hx
      have := hall y hy
      simp only [mem_insert, mem_singleton]
      rcases ‹a z = f ∨ a z = g› with h | h <;>
        rcases ‹a x = f ∨ a x = g› with h' | h' <;>
        rcases ‹a y = f ∨ a y = g› with h'' | h''
      all_goals first | exact False.elim (haxy (h'.trans h''.symm)) |
        exact Or.inl (ha (h.trans h'.symm)) | exact Or.inr (ha (h.trans h''.symm))
    · simpa only [mem_insert, mem_singleton] using
        (show z = x ∨ z = y → z ∈ C from fun h => h.elim (fun h => h ▸ hx) (fun h => h ▸ hy))
  have hsum : ∑ z ∈ C, a z = a x + a y := by simp [hC, hxy]
  rcases hall x hx with hxf | hxg <;> rcases hall y hy with hyf | hyg
  · exact haxy (hxf.trans hyf.symm)
  · rcases hmiss with h | h
    · apply h; exact mem_image.mpr ⟨y, hy, by rw [hsum, ← hxf]; abel⟩
    · apply h; exact mem_image.mpr ⟨x, hx, by rw [hsum, ← hyg]; abel⟩
  · rcases hmiss with h | h
    · apply h; exact mem_image.mpr ⟨x, hx, by rw [hsum, ← hyf]; abel⟩
    · apply h; exact mem_image.mpr ⟨y, hy, by rw [hsum, ← hxg]; abel⟩
  · exact haxy (hxg.trans hyg.symm)

/-- Auxiliary greedy construction; both forbidden values are avoided only at
nonempty proper prefixes. Its two-element obstruction is exact. -/
private theorem two_prefix_order (a : ι → G) (ha : Function.Injective a)
    (C : Finset ι) (f g : G)
    (hmiss : (∑ x ∈ C, a x) - f ∉ C.image a ∨
      (∑ x ∈ C, a x) - g ∉ C.image a) :
    ∃ w : List ι, w.Perm C.toList ∧
      ∀ i, 0 < i → i < w.length →
        ((w.take i).map a).sum ≠ f ∧ ((w.take i).map a).sum ≠ g := by
  classical
  induction C using Finset.strongInductionOn generalizing f g
  rename_i C ih
  by_cases hc : 1 < C.card
  · obtain ⟨x, hx, hxf, hxg⟩ := next_choice a ha C f g hc hmiss
    have hsum : (∑ y ∈ C.erase x, a y) = (∑ y ∈ C, a y) - a x := by
      have := Finset.sum_erase_add C a hx
      exact eq_sub_iff_add_eq.mpr this
    have hm : (∑ y ∈ C.erase x, a y) - (f - a x) ∉ (C.erase x).image a ∨
        (∑ y ∈ C.erase x, a y) - (g - a x) ∉ (C.erase x).image a := by
      have he (v : G) : (∑ y ∈ C.erase x, a y) - (v - a x) =
          (∑ y ∈ C, a y) - v := by rw [hsum]; abel
      simp only [he]
      exact hmiss.imp (fun h hh => h (Finset.image_mono a (erase_subset x C) hh))
        (fun h hh => h (Finset.image_mono a (erase_subset x C) hh))
    obtain ⟨w, hw, hp⟩ := ih (C.erase x) (erase_ssubset hx) (f-a x) (g-a x) hm
    have hwn : w.Nodup := hw.nodup_iff.mpr (C.erase x).nodup_toList
    have hxn : x ∉ w := by
      intro h
      exact notMem_erase x C (mem_toList.mp (hw.mem_iff.mp h))
    have hN : (x :: w).Nodup := List.nodup_cons.mpr ⟨hxn,hwn⟩
    refine ⟨x :: w, (List.perm_ext_iff_of_nodup hN C.nodup_toList).mpr ?_, ?_⟩
    · intro z
      simp only [List.mem_cons, mem_toList]
      rw [hw.mem_iff, mem_toList, mem_erase]
      constructor
      · rintro (rfl | ⟨_, hz⟩) <;> assumption
      · intro hz
        by_cases h : z = x
        · exact Or.inl h
        · exact Or.inr ⟨h, hz⟩
    · intro i hi hil
      cases i with
      | zero => omega
      | succ j =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        by_cases hj : j = 0
        · subst j; simpa using And.intro hxf hxg
        · obtain ⟨hf, hg⟩ := hp j (by omega) (by simpa using hil)
          constructor
          · intro h; apply hf; apply eq_sub_iff_add_eq.mpr; simpa [add_comm] using h
          · intro h; apply hg; apply eq_sub_iff_add_eq.mpr; simpa [add_comm] using h
  · refine ⟨C.toList, List.Perm.refl _, ?_⟩
    intro i hi hil
    simp only [Finset.length_toList] at hil
    omega

private theorem all_prefix_order (a : ι → G) (ha : Function.Injective a)
    (C : Finset ι) (f g : G) (hf : (0 : G) ≠ f) (hg : (0 : G) ≠ g)
    (hTf : (∑ x ∈ C, a x) ≠ f) (hTg : (∑ x ∈ C, a x) ≠ g)
    (hmiss : (∑ x ∈ C, a x) - f ∉ C.image a ∨
      (∑ x ∈ C, a x) - g ∉ C.image a) :
    ∃ w : List ι, w.Perm C.toList ∧
      ∀ i, i ≤ w.length →
        ((w.take i).map a).sum ≠ f ∧ ((w.take i).map a).sum ≠ g := by
  obtain ⟨w, hw, hp⟩ := two_prefix_order a ha C f g hmiss
  refine ⟨w, hw, fun i hi => ?_⟩
  by_cases hi0 : i = 0
  · subst i; simpa using And.intro hf hg
  by_cases hil : i = w.length
  · subst i; simpa [sum_order a hw] using And.intro hTf hTg
  exact hp i (by omega) (by omega)

private def pfx (a : ι → G) (w : List ι) (i : ℕ) : G := ((w.take i).map a).sum

private def Strong (a : ι → G) (w : List ι) : Prop :=
  ∀ i j, i ≤ w.length → j ≤ w.length → pfx a w i = pfx a w j → i = j

private theorem nonzero_list (a : ι → G) (C : Finset ι)
    (hz : ∀ U ⊆ C, U.Nonempty → (∑ x ∈ U, a x) ≠ 0)
    {v : List ι} (hn : v.Nodup) (hv : v ≠ []) (hsub : ∀ x ∈ v, x ∈ C) :
    (v.map a).sum ≠ 0 := by
  have hs : v.toFinset ⊆ C := fun x hx => hsub x (List.mem_toFinset.mp hx)
  have hne : v.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil v hv
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  simpa only [List.sum_toFinset a hn] using hz v.toFinset hs hne

private theorem strong_of_zero_free (a : ι → G) (C : Finset ι)
    (hz : ∀ U ⊆ C, U.Nonempty → (∑ x ∈ U, a x) ≠ 0)
    {w : List ι} (hw : w.Perm C.toList) : Strong a w := by
  have hn : w.Nodup := hw.nodup_iff.mpr C.nodup_toList
  have hneq : ∀ i j, i < j → j ≤ w.length → pfx a w i ≠ pfx a w j := by
    intro i j hij hj he
    let v := (w.drop i).take (j-i)
    have hv : v ≠ [] := by
      apply List.length_pos_iff.mp
      simp only [v, List.length_take, List.length_drop]
      omega
    have hvn : v.Nodup := hn.drop.take
    have hvC : ∀ x ∈ v, x ∈ C := by
      intro x hx
      exact mem_toList.mp (hw.mem_iff.mp (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
    have hs := List.sum_take_add_sum_drop ((w.take j).map a) i
    have hij' : i ≤ j := hij.le
    simp only [← List.map_take, ← List.map_drop, List.take_take,
      Nat.min_eq_left hij', List.drop_take] at hs
    change pfx a w i + (v.map a).sum = pfx a w j at hs
    exact nonzero_list a C hz hvn hv hvC (by rw [he] at hs; simpa using hs)
  intro i j hi hj he
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact hneq i j hij hj he
  · exact hneq j i hji hi he.symm

private theorem strong_cons (a : ι → G) {w : List ι} {x : ι}
    (hw : Strong a w) (hx : ∀ i, i ≤ w.length → pfx a w i ≠ -a x) :
    Strong a (x :: w) := by
  intro i j hi hj he
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ j =>
      have h : pfx a w j = -a x := by
        simp only [pfx, List.take_zero, List.map_nil, List.sum_nil,
          List.take_succ_cons, List.map_cons, List.sum_cons] at he
        exact eq_neg_of_add_eq_zero_right he.symm
      exact False.elim (hx j (by simpa using hj) h)
  | succ i =>
    cases j with
    | zero =>
      have h : pfx a w i = -a x := by
        simp only [pfx, List.take_zero, List.map_nil, List.sum_nil,
          List.take_succ_cons, List.map_cons, List.sum_cons] at he
        exact eq_neg_of_add_eq_zero_right he
      exact False.elim (hx i (by simpa using hi) h)
    | succ j =>
      congr 1
      apply hw i j (by simpa using hi) (by simpa using hj)
      exact add_left_cancel (by simpa only [pfx, List.take_succ_cons, List.map_cons, List.sum_cons] using he)

private theorem strong_append (a : ι → G) {w : List ι} {x : ι}
    (hw : Strong a w)
    (hx : ∀ i, i ≤ w.length → pfx a w i ≠ (w.map a).sum + a x) :
    Strong a (w ++ [x]) := by
  have hleft (i : ℕ) (hi : i ≤ w.length) : pfx a (w ++ [x]) i = pfx a w i := by
    simp only [pfx, List.take_append_of_le_length hi]
  have hfull : pfx a (w ++ [x]) (w ++ [x]).length = (w.map a).sum + a x := by
    simp [pfx]
  intro i j hi hj he
  by_cases hil : i ≤ w.length
  · by_cases hjl : j ≤ w.length
    · exact hw i j hil hjl (by simpa only [hleft i hil, hleft j hjl] using he)
    · have hjf : j = (w ++ [x]).length := by simp only [List.length_append, List.length_singleton] at hj ⊢; omega
      exact False.elim (hx i hil (by simpa only [hjf, hfull, hleft i hil] using he))
  · have hif : i = (w ++ [x]).length := by simp only [List.length_append, List.length_singleton] at hi ⊢; omega
    by_cases hjl : j ≤ w.length
    · exact False.elim (hx j hjl (by simpa only [hif, hfull, hleft j hjl] using he.symm))
    · simp only [List.length_append, List.length_singleton] at hi hj hif
      omega

private theorem good_of_strong (a : ι → G) {w : List ι} (hw : Strong a w) :
    Good (w.map a) := by
  apply (D5.S1.Words.Sequenceability.SeparatedPrefixReflection.good_iff _).mpr
  intro i j hij hj he
  have h : i = j := hw i j (by simpa using (Nat.le_trans hij.le hj))
    (by simpa using hj) (by simpa only [pref, ← List.map_take, pfx] using he)
  omega

private theorem good_sandwich (a : ι → G) {w : List ι} {s t : ι}
    (hw : Strong a w) (hst : a s + a t = 0)
    (hp : ∀ i, i ≤ w.length → pfx a w i ≠ -a s ∧
      pfx a w i ≠ (w.map a).sum - a s) : Good ((s :: w ++ [t]).map a) := by
  let W := s :: (w ++ [t])
  have hlen : W.length = w.length + 2 := by simp [W]
  have hmid (i : ℕ) (hi : i ≤ w.length) : pfx a W (i+1) = a s + pfx a w i := by
    simp only [W, pfx, List.take_succ_cons, List.take_append_of_le_length hi,
      List.map_cons, List.sum_cons]
  have hfull : pfx a W W.length = (w.map a).sum := by
    simp only [pfx, List.take_length, W, List.map_cons, List.map_append,
      List.sum_cons, List.sum_append, List.map_singleton, List.sum_singleton,
      List.map_nil, List.sum_nil, add_zero]
    rw [eq_neg_of_add_eq_zero_right hst]
    abel
  change Good (W.map a)
  apply (D5.S1.Words.Sequenceability.SeparatedPrefixReflection.good_iff _).mpr
  intro i j hij hj he
  have he : pfx a W i = pfx a W j := by simpa only [pref, ← List.map_take, pfx] using he
  have hj : j ≤ W.length := by simpa using hj
  by_cases hi0 : i = 0
  · by_cases hjf : j = W.length
    · exact ⟨hi0, by simpa using hjf⟩
    · cases j with
      | zero => omega
      | succ j =>
        have hjw : j ≤ w.length := by omega
        have hz : pfx a w j = -a s := by
          rw [hi0, hmid j hjw] at he
          simp only [pfx, List.take_zero, List.map_nil, List.sum_nil] at he
          exact eq_neg_of_add_eq_zero_right he.symm
        exact False.elim ((hp j hjw).1 hz)
  · cases i with
    | zero => contradiction
    | succ i =>
      have hiw : i ≤ w.length := by omega
      by_cases hjf : j = W.length
      · have hz : pfx a w i = (w.map a).sum - a s := by
          rw [hmid i hiw, hjf, hfull] at he
          exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he)
        exact False.elim ((hp i hiw).2 hz)
      · cases j with
        | zero => omega
        | succ j =>
          have hjw : j ≤ w.length := by omega
          rw [hmid i hiw, hmid j hjw] at he
          have := hw i j hiw hjw (add_left_cancel he)
          omega

private theorem insert_order {C : Finset ι} {w : List ι} (hw : w.Perm C.toList)
    (x : ι) (hx : x ∉ C) : (x :: w).Perm (insert x C).toList :=
  (hw.cons x).trans (Finset.toList_insert hx).symm

private theorem pair_order {X : Finset ι} {s t : ι} (hs : s ∈ X) (ht : t ∈ X)
    (hst : s ≠ t) {w : List ι} (hw : w.Perm ((X.erase s).erase t).toList) :
    (s :: w ++ [t]).Perm X.toList := by
  have htC : t ∉ (X.erase s).erase t := notMem_erase _ _
  have hsC : s ∉ insert t ((X.erase s).erase t) := by simp [hst]
  have hX : insert s (insert t ((X.erase s).erase t)) = X := by
    ext x
    simp only [mem_insert, mem_erase]
    constructor
    · rintro (rfl | rfl | ⟨_, _, hx⟩) <;> assumption
    · intro hx
      by_cases hxs : x = s
      · exact Or.inl hxs
      by_cases hxt : x = t
      · exact Or.inr (Or.inl hxt)
      exact Or.inr (Or.inr ⟨hxt, hxs, hx⟩)
  have hp := insert_order (insert_order hw t htC) s hsC
  rw [hX] at hp
  exact (List.Perm.cons s (by simpa using (List.perm_append_comm :
    (w ++ [t]).Perm ([t] ++ w)))).trans hp

private theorem exceptional_order (a : ι → G) (ha : Function.Injective a)
    (X : Finset ι) (s t : ι) (hs : s ∈ X) (ht : t ∈ X) (hst : s ≠ t)
    (hnz : ∀ x ∈ X, a x ≠ 0) (hop : a s + a t = 0)
    (hz : ∀ U ⊆ (X.erase s).erase t, U.Nonempty → (∑ x ∈ U, a x) ≠ 0)
    (hT : (∑ x ∈ (X.erase s).erase t, a x) = a s) :
    ∃ W : List ι, W.Perm X.toList ∧ Good (W.map a) := by
  let C := (X.erase s).erase t
  change (∑ x ∈ C, a x) = a s at hT
  have hCsub : C ⊆ X := subset_trans (erase_subset _ _) (erase_subset _ _)
  have hsC : s ∉ C := by simp [C]
  have htC : t ∉ C := notMem_erase _ _
  have hat : a t = -a s := eq_neg_of_add_eq_zero_right hop
  have h2 : a s + a s ≠ 0 := by
    intro h
    have has : a s = -a s := eq_neg_of_add_eq_zero_left h
    exact hst (ha (has.trans hat.symm))
  obtain ⟨c, hc, hca⟩ : ∃ c ∈ C, a c ≠ a s + a s := by
    by_contra hn
    have hall : ∀ c ∈ C, a c = a s + a s := by simpa using hn
    have hsmall : C.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy; exact ha ((hall x hx).trans (hall y hy).symm))
    have hne : C.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      apply hnz s hs
      simpa only [he, sum_empty] using hT.symm
    have hcard : C.card = 1 := by
      have hpos : 0 < C.card := hne.card_pos
      omega
    obtain ⟨c, hsingle⟩ := Finset.card_eq_one.mp hcard
    have hcC : c ∈ C := by simp [hsingle]
    have he : a c = a s := by simpa only [hsingle, sum_singleton] using hT
    exact hsC (ha he ▸ hcC)
  let D := C.erase c
  have hDsub : D ⊆ C := erase_subset _ _
  have hDsum : (∑ x ∈ D, a x) = a s - a c := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [D, hT] using (Finset.sum_erase_add C a hc)
  have hnot (x : ι) (hx : x ∉ D) : a x ∉ D.image a := by
    intro hh
    obtain ⟨y, hy, he⟩ := mem_image.mp hh
    exact hx (ha he ▸ hy)
  have hmiss : (∑ x ∈ D, a x) - (a s + a s - a c) ∉ D.image a := by
    have he : (∑ x ∈ D, a x) - (a s + a s - a c) = a t := by rw [hDsum, hat]; abel
    rw [he]
    exact hnot t (fun h => htC (hDsub h))
  obtain ⟨w, hw, hp⟩ := all_prefix_order a ha D (a s+a s) (a s+a s-a c)
    (Ne.symm h2) (by intro h; apply hca; exact (sub_eq_zero.mp h.symm).symm)
    (by
      intro h
      rw [hDsum] at h
      have he : a c = a t := by
        calc a c = a s - (a s - a c) := by abel
             _ = a s - (a s + a s) := by rw [h]
             _ = a t := by rw [hat]; abel
      exact htC (ha he ▸ hc))
    (by
      intro h
      rw [hDsum] at h
      have he : a s = a s + a s := by
        have hh := congrArg (fun z => z + a c) h
        simpa only [sub_add_cancel] using hh
      have hh : (0 : G) = a s := add_left_cancel (a := a s) (by simpa only [add_zero] using he)
      exact hnz s hs hh.symm)
    (Or.inr hmiss)
  have hwSum : (w.map a).sum = a s-a c := (sum_order a hw).trans hDsum
  have hwStrong : Strong a w := strong_of_zero_free a D
    (fun U hU => hz U (subset_trans hU hDsub)) hw
  have hpa : ∀ i, i ≤ w.length → pfx a w i ≠ a s := by
    intro i hi he
    let B := (w.take i).toFinset
    have hn : (w.take i).Nodup := (hw.nodup_iff.mpr D.nodup_toList).take
    have hBC : B ⊆ C := by
      intro x hx
      exact hDsub (mem_toList.mp (hw.mem_iff.mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))))
    have hcB : c ∉ B := by
      intro h
      have : c ∈ D := mem_toList.mp (hw.mem_iff.mp (List.mem_of_mem_take (List.mem_toFinset.mp h)))
      exact notMem_erase c C this
    have hBsum : (∑ x ∈ B, a x) = a s := by
      simpa only [B, List.sum_toFinset a hn, pfx] using he
    apply hz (C \ B) (sdiff_subset) ⟨c, mem_sdiff.mpr ⟨hc, hcB⟩⟩
    rw [Finset.sum_sdiff_eq_sub hBC, hBsum, hT]
    exact sub_self _
  have htStrong : Strong a (t :: w) := strong_cons a hwStrong (by simpa [hat] using hpa)
  have htwSum : ((t :: w).map a).sum = -a c := by simp only [List.map_cons, List.sum_cons, hwSum, hat]; abel
  have htsStrong : Strong a ((t :: w) ++ [s]) := strong_append a htStrong (by
    intro i hi he
    cases i with
    | zero =>
      have he0 : (0 : G) = -a c + a s := by
        simpa only [pfx, List.take_zero, List.map_nil, List.sum_nil, htwSum] using he
      have he' : a c = a s := by
        have hh := congrArg (fun z => a c + z) he0
        simpa only [add_zero, ← add_assoc, add_neg_cancel, zero_add] using hh
      exact hsC (ha he' ▸ hc)
    | succ i =>
      have hf := (hp i (by simpa using hi)).2
      apply hf
      simp only [pfx, List.take_succ_cons, List.map_cons, List.sum_cons, hat, hwSum] at he
      change pfx a w i = _
      calc pfx a w i = (-a c+a s) - (-a s) := eq_sub_iff_add_eq.mpr (by simpa [pfx, add_comm, sub_eq_add_neg] using he)
           _ = _ := by abel)
  have hfullStrong : Strong a (((t :: w) ++ [s]) ++ [c]) := strong_append a htsStrong (by
    intro i hi he
    have htot : (((t :: w) ++ [s]).map a).sum + a c = a s := by
      simp only [List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, htwSum]
      abel
    rw [htot] at he
    by_cases hil : i ≤ (t :: w).length
    · rw [pfx, List.take_append_of_le_length hil] at he
      cases i with
      | zero => exact hnz s hs (by simpa using he.symm)
      | succ i =>
        apply (hp i (by simpa using hil)).1
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, hat] at he
        change pfx a w i = _
        calc pfx a w i = a s - (-a s) := eq_sub_iff_add_eq.mpr (by simpa [pfx, add_comm] using he)
             _ = _ := by abel
    · have hif : i = ((t :: w) ++ [s]).length := by simp only [List.length_append, List.length_singleton] at hi ⊢; omega
      have he' : a c = 0 := by
        rw [hif] at he
        simp only [pfx, List.take_length, List.map_append, List.sum_append,
          List.map_singleton, List.sum_singleton] at he
        rw [htwSum] at he
        have hh : -a c = 0 := add_right_cancel (show -a c + a s = 0 + a s by simpa using he)
        exact neg_eq_zero.mp hh
      exact hnz c (hCsub hc) he')
  have hwc : (w ++ [c]).Perm C.toList := by
    have h := insert_order hw c (notMem_erase _ _)
    rw [Finset.insert_erase hc] at h
    have h' : (w ++ [c]).Perm (c :: w) := by
      simpa using (List.perm_append_comm : (w ++ [c]).Perm ([c] ++ w))
    exact h'.trans h
  have hpX := pair_order ht hs hst.symm (by simpa only [C, Finset.erase_right_comm] using hwc)
  refine ⟨((t :: w) ++ [s]) ++ [c], ?_, good_of_strong a hfullStrong⟩
  apply List.Perm.trans _ hpX
  have hswap := (List.Perm.refl (t :: w)).append (List.Perm.swap c s [])
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using hswap

/-- A zero original pair with zero-sum-free complement admits a full Good
enumeration. All labels and all exceptional totals stay in the original group. -/
theorem exists_good_order_of_zero_pair (a : ι → G) (ha : Function.Injective a)
    (X : Finset ι) (s t : ι) (hs : s ∈ X) (ht : t ∈ X) (hst : s ≠ t)
    (hnz : ∀ x ∈ X, a x ≠ 0) (hop : a s + a t = 0)
    (hz : ∀ U ⊆ (X.erase s).erase t, U.Nonempty → (∑ x ∈ U, a x) ≠ 0) :
    ∃ W : List ι, W.Perm X.toList ∧ Good (W.map a) := by
  let C := (X.erase s).erase t
  by_cases hTs : (∑ x ∈ C, a x) = a s
  · exact exceptional_order a ha X s t hs ht hst hnz hop hz hTs
  by_cases hTt : (∑ x ∈ C, a x) = a t
  · apply exceptional_order a ha X t s ht hs hst.symm hnz (by simpa [add_comm] using hop)
    · simpa only [Finset.erase_right_comm] using hz
    · simpa only [C, Finset.erase_right_comm] using hTt
  have hnot : a s ∉ C.image a := by
    intro hh
    obtain ⟨x, hx, he⟩ := mem_image.mp hh
    have : s ∈ C := ha he ▸ hx
    simpa [C] using this
  have hmiss : (∑ x ∈ C, a x) - ((∑ x ∈ C, a x) - a s) ∉ C.image a := by
    simpa using hnot
  obtain ⟨w, hw, hp⟩ := all_prefix_order a ha C (-a s) ((∑ x ∈ C, a x)-a s)
    (by simpa using hnz s hs)
    (by intro h; apply hTs; exact sub_eq_zero.mp h.symm)
    (by simpa only [eq_neg_of_add_eq_zero_right hop] using hTt)
    (by
      intro h
      have he : (0 : G) = -a s := add_left_cancel (a := ∑ x ∈ C, a x)
        (by simpa only [sub_eq_add_neg, add_zero] using h)
      exact hnz s hs (neg_eq_zero.mp he.symm))
    (Or.inr hmiss)
  refine ⟨s :: w ++ [t], pair_order hs ht hst hw, ?_⟩
  apply good_sandwich a (strong_of_zero_free a C hz hw) hop
  simpa only [pfx, sum_order a hw] using hp

/-- The original coefficient-one row, in the original integer coordinate module. -/
def row (U : Finset ι) : ι → ℤ := ∑ x ∈ U, Pi.single x 1

/-- Exact integer span of the supplied Boolean rows. -/
def rowSpan (H : Finset (Finset ι)) : Submodule ℤ (ι → ℤ) :=
  Submodule.span ℤ (Set.range fun V : H => row V.1)

/-- Every original permutation has a nonempty proper interval belonging to H. -/
def Covers [Fintype ι] (H : Finset (Finset ι)) : Prop :=
  ∀ w : List ι, w.Perm (univ : Finset ι).toList →
    ∃ i j : ℕ, i < j ∧ j ≤ w.length ∧ (i ≠ 0 ∨ j ≠ w.length) ∧
      ((w.drop i).take (j-i)).toFinset ∈ H

/-- Full coverage plus an exact original pair row gives an original primitive,
or a nonempty disjoint Boolean row with an actual integer coefficient witness.
The extracted row need not belong to H and may be the whole complement. -/
theorem full_blocker_pair_extract [Fintype ι] (H : Finset (Finset ι))
    (hcover : Covers H) (s t : ι) (hst : s ≠ t)
    (hpair : row {s,t} ∈ rowSpan H) :
    (∃ i : ι, Pi.single i (1 : ℤ) ∈ rowSpan H) ∨
    (∃ i j : ι, i ≠ j ∧ Pi.single i (1 : ℤ) - Pi.single j 1 ∈ rowSpan H) ∨
    ∃ U : Finset ι, U.Nonempty ∧ U ⊆ ((univ : Finset ι).erase s).erase t ∧
      ∃ c : H → ℤ, ∑ V : H, c V • row V.1 = row U := by
  classical
  by_cases hu : ∃ i : ι, Pi.single i (1 : ℤ) ∈ rowSpan H
  · exact Or.inl hu
  by_cases hd : ∃ i j : ι, i ≠ j ∧ Pi.single i (1 : ℤ) - Pi.single j 1 ∈ rowSpan H
  · exact Or.inr (Or.inl hd)
  right; right
  let M := rowSpan H
  let a : ι → (ι → ℤ) ⧸ M := fun i => M.mkQ (Pi.single i 1)
  have ha : Function.Injective a := by
    intro i j he
    by_contra hij
    apply hd
    refine ⟨i,j,hij,?_⟩
    apply (Submodule.Quotient.mk_eq_zero M).mp
    change M.mkQ (Pi.single i 1 - Pi.single j 1) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  have hnz : ∀ i ∈ (univ : Finset ι), a i ≠ 0 := by
    intro i _ he
    exact hu ⟨i, (Submodule.Quotient.mk_eq_zero M).mp he⟩
  have hop : a s + a t = 0 := by
    have he : row {s,t} = Pi.single s (1 : ℤ) + Pi.single t 1 := by simp [row, hst]
    have hz := (Submodule.Quotient.mk_eq_zero M).mpr hpair
    simpa only [he, ← Submodule.mkQ_apply, map_add] using hz
  have hsum (U : Finset ι) : (∑ x ∈ U, a x) = M.mkQ (row U) := by
    simp only [row, map_sum, a]
  by_contra hnone
  have hzero : ∀ U ⊆ ((univ : Finset ι).erase s).erase t,
      U.Nonempty → (∑ x ∈ U, a x) ≠ 0 := by
    intro U hU hne hz
    apply hnone
    refine ⟨U,hne,hU,?_⟩
    have hm : row U ∈ rowSpan H := (Submodule.Quotient.mk_eq_zero M).mp (by
      simpa only [← Submodule.mkQ_apply, ← hsum U] using hz)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hm
    exact ⟨c,hc⟩
  obtain ⟨w, hw, hgood⟩ := exists_good_order_of_zero_pair a ha univ s t
    (mem_univ _) (mem_univ _) hst hnz hop hzero
  obtain ⟨i,j,hij,hj,hproper,hH⟩ := hcover w hw
  let v := (w.drop i).take (j-i)
  have hvn : v.Nodup := (hw.nodup_iff.mpr (univ : Finset ι).nodup_toList).drop.take
  have hm : row v.toFinset ∈ rowSpan H := Submodule.subset_span ⟨⟨v.toFinset,hH⟩,rfl⟩
  have hz : (v.map a).sum = 0 := by
    rw [← List.sum_toFinset a hvn, hsum]
    exact (Submodule.Quotient.mk_eq_zero M).mpr hm
  apply hgood i j hij (by simpa using hj) (by simpa using hproper)
  simpa only [← List.map_drop, ← List.map_take] using hz

end D5.S3.Combinatorics.Sequenceability.ZeroPairGoodOrdering
