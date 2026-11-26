/- GID: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiImageBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiImageBound
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Row deletion makes almost symmetric semigroups symmetric of Frobenius number 2(F-g+1)-1, so at most 2^(floor((F+1)/2)-1) outputs occur at source Frobenius number F. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#459)
escape_witness: del_iff (on an almost symmetric semigroup the deleted rows are exactly the gaps x
  with F - x a gap, by the count card_split of such gaps), dl_refl (reflection through F
  exchanges the deleted rows below F - s and above s), no_pair (no two retained relabelled rows
  sum to the relabelled Frobenius number) and out_symmetric (hence the output is symmetric);
  small_targets and image_bound count the outputs.
proof_shape:
  del, dl, out: private definitions; consumers: the lemmas below and result.
  frob_mem, le_frob, gap_pos, mem_retained, mem_del, pf_frob, comp_gap, del_sub, del_lt,
    del_refl, dl_lt, dl_frob, mem_out, ret_gap, ret_not_del, frob_ret, members_out,
    card_le_frob, frob_pos, out_spec: bind-only helpers; consumers: the content lemmas below
    and result.
  count_step, card_split, card_del, del_iff, dl_refl, no_pair, out_strict, frob_out, card_out,
    out_symmetric, small_targets, image_bound: content; consumers along the chain to result.
  result: content.
Direct frozen dependencies: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation
  (NumericalSet, members, frobenius, Semigroup, PseudoFrobenius, AlmostSymmetric, Symmetric,
  retainedRows, deleteRows, phi, phi_omits_one);
  D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiOrdinaryFiber (result);
  D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiSymmetricTargets (result).
Search record (§3.1): the frozen Partitions modules prove the omission of 1, the fixed points,
  the ordinary fiber and the count of symmetric targets; no D5 module or pinned Mathlib
  declaration proves that row deletion of an almost symmetric semigroup is symmetric or bounds
  its image.
-/

import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets
import Mathlib.Tactic

/-! # The image of pseudo-Frobenius row deletion at a fixed source Frobenius number

For an almost symmetric numerical semigroup `S` with genus `g` and Frobenius number `F`, the
deleted rows `PF(S) ∖ {F}` are exactly the gaps `x` with `F - x` a gap, and this set is closed
under `x ↦ F - x`. Consequently no two retained relabelled rows sum to the relabelled Frobenius
number, and the row deletion `Φ(S)` is a symmetric numerical set of genus `F - g + 1` and
Frobenius number `2(F - g + 1) - 1 ≤ F`. Since `Φ(S)` also omits `1`, the outputs at source
Frobenius number `F` number at most `2^(⌊(F+1)/2⌋ - 1)`, and at least one of them,
`ℕ₀ ∖ {1} = Φ(O_{F+1})`, is a semigroup.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound

open D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation (NumericalSet members frobenius
  Semigroup PseudoFrobenius AlmostSymmetric Symmetric retainedRows deleteRows phi phi_omits_one)

private lemma frob_mem (U : NumericalSet) : frobenius U ∈ U.gaps := Finset.max'_mem _ _

private lemma le_frob (U : NumericalSet) {g : ℕ} (hg : g ∈ U.gaps) : g ≤ frobenius U :=
  Finset.le_max' _ _ hg

private lemma gap_pos (U : NumericalSet) {g : ℕ} (hg : g ∈ U.gaps) : 1 ≤ g := by
  rcases Nat.eq_zero_or_pos g with h | h
  · subst h; exact absurd hg U.zero_not_gap
  · exact h

/-- The deleted rows: pseudo-Frobenius gaps other than the Frobenius number. -/
private def del (U : NumericalSet) : Finset ℕ := U.gaps \ retainedRows U

private lemma mem_retained (U : NumericalSet) {x : ℕ} :
    x ∈ retainedRows U ↔ x ∈ U.gaps ∧ (x = frobenius U ∨ ¬ PseudoFrobenius U x) := by
  classical
  unfold retainedRows
  simp only [Finset.mem_filter]

private lemma mem_del (U : NumericalSet) {x : ℕ} :
    x ∈ del U ↔ x ∈ U.gaps ∧ x ≠ frobenius U ∧ PseudoFrobenius U x := by
  unfold del
  rw [Finset.mem_sdiff, mem_retained]
  tauto

/-- Counting a finite set below `b` from below `a`, with the gap `(a, b)` and `a` excluded. -/
private lemma count_step (X : Finset ℕ) {a b : ℕ} (hab : a < b) (ha : a ∉ X) :
    (X.filter (· < b)).card + 1 ≤ (X.filter (· < a)).card + (b - a) := by
  have hsub : X.filter (· < b) ⊆ X.filter (· < a) ∪ Finset.Ioo a b := by
    intro x hx
    obtain ⟨hxX, hxb⟩ := Finset.mem_filter.mp hx
    rcases lt_trichotomy x a with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxX, h⟩)
    · subst h; exact absurd hxX ha
    · exact Finset.mem_union_right _ (Finset.mem_Ioo.mpr ⟨h, hxb⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (X.filter (· < a)) (Finset.Ioo a b)
  rw [Nat.card_Ioo] at h2
  omega


private lemma pf_frob (U : NumericalSet) : PseudoFrobenius U (frobenius U) := by
  refine ⟨frob_mem U, fun s hs _ => ?_⟩
  show frobenius U + s ∉ U.gaps
  intro hg
  have := le_frob U hg
  omega

private lemma comp_gap (U : NumericalSet) (hS : Semigroup U) {y : ℕ} (hy : y ≤ frobenius U)
    (hym : y ∉ U.gaps) : frobenius U - y ∈ U.gaps := by
  by_contra h
  have := hS y (frobenius U - y) hym h
  rw [show y + (frobenius U - y) = frobenius U by omega] at this
  exact this (frob_mem U)

/-- Gaps whose complement in `F` is also a gap number `2g - F - 1`. -/
private lemma card_split (U : NumericalSet) (hS : Semigroup U) :
    (U.gaps.filter (fun x => frobenius U - x ∈ U.gaps)).card + (frobenius U + 1) =
      2 * U.gaps.card := by
  classical
  set F := frobenius U with hF
  have hM : ((Finset.range (F + 1)).filter (· ∉ U.gaps)).card + U.gaps.card = F + 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.range (F + 1))
      (fun x => x ∉ U.gaps)
    rw [Finset.card_range] at h
    have e : (Finset.range (F + 1)).filter (fun x => ¬ (x ∉ U.gaps)) = U.gaps := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, not_not]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by have := le_frob U h; omega, h⟩
    rw [e] at h
    exact h
  have himg : U.gaps.filter (fun x => ¬ (F - x ∈ U.gaps)) =
      ((Finset.range (F + 1)).filter (· ∉ U.gaps)).image (F - ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hx, hc⟩
      exact ⟨F - x, ⟨by omega, hc⟩, by have := le_frob U hx; omega⟩
    · rintro ⟨y, ⟨hy, hym⟩, rfl⟩
      refine ⟨comp_gap U hS (by omega) hym, ?_⟩
      rwa [show F - (F - y) = y by omega]
  have hinj : Set.InjOn (F - ·) (((Finset.range (F + 1)).filter (· ∉ U.gaps) : Finset ℕ) :
      Set ℕ) := by
    intro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    simp only at h
    omega
  have hc := Finset.card_filter_add_card_filter_not (s := U.gaps) (fun x => F - x ∈ U.gaps)
  rw [himg, Finset.card_image_of_injOn hinj] at hc
  omega

private lemma card_del (U : NumericalSet) (hA : AlmostSymmetric U) :
    2 * U.gaps.card = frobenius U + ((del U).card + 1) := by
  classical
  obtain ⟨_, h⟩ := hA
  rw [h]
  congr 1
  have hF : frobenius U ∈ U.gaps.filter (PseudoFrobenius U) :=
    Finset.mem_filter.mpr ⟨frob_mem U, pf_frob U⟩
  have e : del U = (U.gaps.filter (PseudoFrobenius U)).erase (frobenius U) := by
    ext x
    rw [mem_del, Finset.mem_erase, Finset.mem_filter]
    tauto
  rw [e, Finset.card_erase_of_mem hF, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, hF⟩)]

/-- On an almost symmetric semigroup the deleted rows are exactly the gaps `x` with `F - x` a
gap. -/
private lemma del_iff (U : NumericalSet) (hA : AlmostSymmetric U) {x : ℕ} (hx : x ∈ U.gaps) :
    x ∈ del U ↔ frobenius U - x ∈ U.gaps := by
  classical
  have hsub : del U ⊆ U.gaps.filter (fun x => frobenius U - x ∈ U.gaps) := by
    intro x hx
    obtain ⟨hg, hne, hpf⟩ := (mem_del U).mp hx
    refine Finset.mem_filter.mpr ⟨hg, ?_⟩
    by_contra h
    have hlt : x < frobenius U := lt_of_le_of_ne (le_frob U hg) hne
    have := hpf.2 (frobenius U - x) (by omega) h
    rw [show x + (frobenius U - x) = frobenius U by omega] at this
    exact this (frob_mem U)
  have heq : del U = U.gaps.filter (fun x => frobenius U - x ∈ U.gaps) := by
    apply Finset.eq_of_subset_of_card_le hsub
    have h1 := card_split U hA.1
    have h2 := card_del U hA
    omega
  rw [heq, Finset.mem_filter]
  tauto

private lemma del_sub (U : NumericalSet) {d : ℕ} (hd : d ∈ del U) : d ∈ U.gaps :=
  ((mem_del U).mp hd).1

private lemma del_lt (U : NumericalSet) {d : ℕ} (hd : d ∈ del U) : d < frobenius U :=
  lt_of_le_of_ne (le_frob U (del_sub U hd)) ((mem_del U).mp hd).2.1

private lemma del_refl (U : NumericalSet) (hA : AlmostSymmetric U) {d : ℕ} (hd : d ∈ del U) :
    frobenius U - d ∈ del U := by
  have hg := del_sub U hd
  have h1 := (del_iff U hA hg).mp hd
  refine (del_iff U hA h1).mpr ?_
  rwa [show frobenius U - (frobenius U - d) = d by have := del_lt U hd; omega]

/-- The number of deleted rows below `r`. -/
private def dl (U : NumericalSet) (r : ℕ) : ℕ := ((del U).filter (· < r)).card

private lemma dl_lt (U : NumericalSet) {r : ℕ} (hr : 0 < r) : dl U r < r := by
  have h := count_step (del U) hr (fun h0 => U.zero_not_gap (del_sub U h0))
  have h0 : (del U).filter (· < 0) = ∅ := by
    ext x; simp
  unfold dl
  rw [h0, Finset.card_empty] at h
  omega

private lemma dl_frob (U : NumericalSet) : dl U (frobenius U) = (del U).card := by
  unfold dl
  rw [Finset.filter_true_of_mem fun d hd => del_lt U hd]

/-- Reflection through `F` exchanges the deleted rows below `F - s` and above `s`. -/
private lemma dl_refl (U : NumericalSet) (hA : AlmostSymmetric U) {s : ℕ}
    (hs : s ≤ frobenius U) (hsd : s ∉ del U) :
    dl U (frobenius U - s) + dl U s = (del U).card := by
  classical
  set F := frobenius U
  have himg : (del U).filter (· < F - s) = ((del U).filter (fun e => s < e)).image (F - ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hx, hxs⟩
      refine ⟨F - x, ⟨del_refl U hA hx, by omega⟩, ?_⟩
      have := del_lt U hx
      omega
    · rintro ⟨e, ⟨he, hse⟩, rfl⟩
      exact ⟨del_refl U hA he, by have := del_lt U he; omega⟩
  have hinj : Set.InjOn (F - ·) (((del U).filter (fun e => s < e) : Finset ℕ) : Set ℕ) := by
    intro a ha b hb h
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have := del_lt U ha.1
    have := del_lt U hb.1
    simp only at h
    omega
  have hlow : (del U).filter (fun e => ¬ (s < e)) = (del U).filter (· < s) := by
    ext x
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨hx, hxs⟩
      refine ⟨hx, lt_of_le_of_ne hxs ?_⟩
      rintro rfl
      exact hsd hx
    · rintro ⟨hx, hxs⟩
      exact ⟨hx, hxs.le⟩
  have hc := Finset.card_filter_add_card_filter_not (s := del U) (fun e => s < e)
  rw [hlow] at hc
  unfold dl
  rw [himg, Finset.card_image_of_injOn hinj]
  exact hc

/-- No two retained rows have relabelled values summing to the relabelled Frobenius number. -/
private lemma no_pair (U : NumericalSet) (hA : AlmostSymmetric U) {r r' : ℕ}
    (hr : r ∈ retainedRows U) (hr' : r' ∈ retainedRows U) :
    (r - dl U r) + (r' - dl U r') ≠ frobenius U - dl U (frobenius U) := by
  intro heq
  have hrg := ((mem_retained U).mp hr).1
  have hr'g := ((mem_retained U).mp hr').1
  have hrd : r ∉ del U := fun h => by
    rcases ((mem_retained U).mp hr).2 with h1 | h1
    · exact ((mem_del U).mp h).2.1 h1
    · exact h1 ((mem_del U).mp h).2.2
  have hr'd : r' ∉ del U := fun h => by
    rcases ((mem_retained U).mp hr').2 with h1 | h1
    · exact ((mem_del U).mp h).2.1 h1
    · exact h1 ((mem_del U).mp h).2.2
  have hr'F := le_frob U hr'g
  obtain ⟨s, hsdef⟩ : ∃ s, s = frobenius U - r' := ⟨_, rfl⟩
  have hsg : s ∉ U.gaps := fun h => hr'd ((del_iff U hA hr'g).mpr (hsdef ▸ h))
  have hsd : s ∉ del U := fun h => hsg (del_sub U h)
  have hsym := dl_refl U hA (s := s) (by omega) hsd
  have e3 : s + r' = frobenius U := by omega
  rw [show frobenius U - s = r' by omega] at hsym
  have hF := dl_frob U
  have h1 := dl_lt U (gap_pos U hrg)
  have h2 := dl_lt U (gap_pos U hr'g)
  have hds : dl U s ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · unfold dl; rw [h]; simp
    · exact (dl_lt U h).le
  have hcF : (del U).card ≤ frobenius U := by
    rw [← hF]
    exact (dl_lt U (gap_pos U (frob_mem U))).le
  have key : r - dl U r = s - dl U s := by omega
  rcases lt_trichotomy r s with hlt | hreq | hgt
  · have h4 : dl U s + 1 ≤ dl U r + (s - r) := count_step (del U) hlt hrd
    omega
  · exact hsg (hreq ▸ hrg)
  · have h4 : dl U r + 1 ≤ dl U s + (r - s) := count_step (del U) hgt hsd
    omega

private lemma mem_out (U : NumericalSet) {n : ℕ} :
    n ∈ deleteRows U (retainedRows U) ↔ ∃ r ∈ retainedRows U, r - dl U r = n := by
  unfold deleteRows
  exact Finset.mem_image

private lemma ret_gap (U : NumericalSet) {r : ℕ} (hr : r ∈ retainedRows U) : r ∈ U.gaps :=
  ((mem_retained U).mp hr).1

private lemma ret_not_del (U : NumericalSet) {r : ℕ} (hr : r ∈ retainedRows U) :
    r ∉ del U := fun h => by
  rcases ((mem_retained U).mp hr).2 with h1 | h1
  · exact ((mem_del U).mp h).2.1 h1
  · exact h1 ((mem_del U).mp h).2.2

private lemma frob_ret (U : NumericalSet) : frobenius U ∈ retainedRows U :=
  (mem_retained U).mpr ⟨frob_mem U, Or.inl rfl⟩

/-- The relabelling strictly increases along retained rows. -/
private lemma out_strict (U : NumericalSet) {r r' : ℕ} (hr : r ∈ retainedRows U)
    (hr' : r' ∈ retainedRows U) (hlt : r < r') : r - dl U r < r' - dl U r' := by
  have h4 : dl U r' + 1 ≤ dl U r + (r' - r) := count_step (del U) hlt (ret_not_del U hr)
  have h1 := dl_lt U (gap_pos U (ret_gap U hr))
  have h2 := dl_lt U (gap_pos U (ret_gap U hr'))
  omega

/-- The output of the row deletion as a numerical set. -/
private def out (U : NumericalSet) : NumericalSet where
  gaps := deleteRows U (retainedRows U)
  proper := ⟨_, (mem_out U).mpr ⟨_, frob_ret U, rfl⟩⟩
  zero_not_gap := fun h => by
    obtain ⟨r, hr, he⟩ := (mem_out U).mp h
    have := dl_lt U (gap_pos U (ret_gap U hr))
    omega

private lemma members_out (U : NumericalSet) : members (out U) = phi U := rfl

private lemma frob_out (U : NumericalSet) :
    frobenius (out U) = frobenius U - dl U (frobenius U) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro n hn
    obtain ⟨r, hr, rfl⟩ := (mem_out U).mp hn
    rcases lt_or_eq_of_le (le_frob U (ret_gap U hr)) with hlt | heq
    · exact (out_strict U hr (frob_ret U) hlt).le
    · rw [heq]
  · exact Finset.le_max' _ _ ((mem_out U).mpr ⟨_, frob_ret U, rfl⟩)

private lemma card_out (U : NumericalSet) :
    (out U).gaps.card + (del U).card = U.gaps.card := by
  have hinj : Set.InjOn (fun r => r - dl U r) (retainedRows U : Set ℕ) := by
    intro a ha b hb h
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd h (out_strict U ha hb hlt).ne
    · exact heq
    · exact absurd h (out_strict U hb ha hgt).ne'
  have hc : (out U).gaps.card = (retainedRows U).card := Finset.card_image_of_injOn hinj
  have hsub : retainedRows U ⊆ U.gaps := fun r hr => ret_gap U hr
  have := Finset.card_sdiff_add_card_eq_card hsub
  unfold del
  omega

private lemma card_le_frob (U : NumericalSet) : U.gaps.card ≤ frobenius U := by
  have hsub : U.gaps ⊆ Finset.Icc 1 (frobenius U) := fun x hx =>
    Finset.mem_Icc.mpr ⟨gap_pos U hx, le_frob U hx⟩
  have := Finset.card_le_card hsub
  rwa [Nat.card_Icc, Nat.add_sub_cancel] at this

/-- On an almost symmetric semigroup the row-deletion output is symmetric. -/
private lemma out_symmetric (U : NumericalSet) (hA : AlmostSymmetric U) : Symmetric (out U) := by
  classical
  have hF' := frob_out U
  have hc := dl_frob U
  have hcard := card_out U
  have h2g := card_del U hA
  have hcF : dl U (frobenius U) < frobenius U := dl_lt U (gap_pos U (frob_mem U))
  obtain ⟨G, hG⟩ : ∃ G, G = (out U).gaps := ⟨_, rfl⟩
  obtain ⟨F', hF'def⟩ : ∃ F', F' = frobenius (out U) := ⟨_, rfl⟩
  have hle : ∀ x ∈ G, x ≤ F' := fun x hx => by
    rw [hF'def, hG] at *
    exact Finset.le_max' _ _ hx
  have hpair : ∀ x ∈ G, ∀ y ∈ G, x + y ≠ F' := by
    intro x hx y hy
    rw [hG] at hx hy
    obtain ⟨r, hr, rfl⟩ := (mem_out U).mp hx
    obtain ⟨r', hr', rfl⟩ := (mem_out U).mp hy
    rw [hF'def, hF']
    exact no_pair U hA hr hr'
  have hcardG : 2 * G.card = F' + 1 := by
    rw [hG, hF'def, hF']
    omega
  set G2 := G.image (F' - ·) with hG2
  have hdisj : Disjoint G G2 := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx2
    exact hpair _ hx y hy (by have := hle y hy; omega)
  have hinj : Set.InjOn (F' - ·) (G : Set ℕ) := by
    intro a ha b hb h
    have := hle a ha
    have := hle b hb
    simp only at h
    omega
  have hcard2 : G2.card = G.card := Finset.card_image_of_injOn hinj
  have hunion : G ∪ G2 = Finset.range (F' + 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_range.mpr (by have := hle x h; omega)
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_range.mpr (by omega)
    · rw [Finset.card_range, Finset.card_union_of_disjoint hdisj]
      omega
  intro a ha
  rw [← hF'def] at ha ⊢
  change (a ∉ (out U).gaps ↔ ¬ (F' - a ∉ (out U).gaps))
  rw [← hG, not_not]
  constructor
  · intro haG
    have hmem : a ∈ G ∪ G2 := by
      rw [hunion]
      exact Finset.mem_range.mpr (by omega)
    rcases Finset.mem_union.mp hmem with h | h
    · exact absurd h haG
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
      rwa [show F' - (F' - y) = y by have := hle y hy; omega]
  · intro h haG
    exact hpair a haG _ h (by omega)

/-- Row deletion on an almost symmetric semigroup: the output is symmetric, of genus
`F - g + 1` and Frobenius number `2(F - g + 1) - 1 ≤ F`. -/
private lemma out_spec (U : NumericalSet) (hA : AlmostSymmetric U) :
    Symmetric (out U) ∧ (out U).gaps.card = frobenius U - U.gaps.card + 1 ∧
      frobenius (out U) = 2 * (frobenius U - U.gaps.card + 1) - 1 ∧
      frobenius (out U) ≤ frobenius U := by
  have hF' := frob_out U
  have hc := dl_frob U
  have hcard := card_out U
  have h2g := card_del U hA
  have hgF := card_le_frob U
  refine ⟨out_symmetric U hA, by omega, by omega, by omega⟩

private lemma frob_pos (U : NumericalSet) : 1 ≤ frobenius U := gap_pos U (frob_mem U)

/-- Symmetric numerical sets omitting `1` with Frobenius number at most `2H - 1` number at
most `2^(H-1)`. -/
private lemma small_targets (H : ℕ) (hH : 1 ≤ H) :
    {U : NumericalSet | Symmetric U ∧ frobenius U ≤ 2 * H - 1 ∧ 1 ∉ members U}.Finite ∧
    {U : NumericalSet | Symmetric U ∧ frobenius U ≤ 2 * H - 1 ∧ 1 ∉ members U}.ncard ≤
      2 ^ (H - 1) := by
  have hT := DelgadoSuerYesilPhiSymmetricTargets.result
  induction H, hH using Nat.le_induction with
  | base =>
    have hall := hT.2.1 1 le_rfl
    have hfin : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * 1 - 1}.Finite :=
      Set.finite_of_ncard_pos (by rw [hall]; positivity)
    have hsub : {U : NumericalSet | Symmetric U ∧ frobenius U ≤ 2 * 1 - 1 ∧ 1 ∉ members U} ⊆
        {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * 1 - 1} := by
      rintro U ⟨hU, hf, _⟩
      exact ⟨hU, by have := frob_pos U; omega⟩
    refine ⟨hfin.subset hsub, ?_⟩
    calc _ ≤ _ := Set.ncard_le_ncard hsub hfin
      _ = _ := hall
  | succ H hH ih =>
    obtain ⟨hfin, hle⟩ := ih
    have hnew := (hT.2.2.1 (H + 1) (by omega)).2.1
    have hfin2 : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * (H + 1) - 1 ∧
        1 ∉ members U}.Finite :=
      Set.finite_of_ncard_pos (by rw [hnew]; positivity)
    have hsub : {U : NumericalSet | Symmetric U ∧ frobenius U ≤ 2 * (H + 1) - 1 ∧
        1 ∉ members U} ⊆
        {U : NumericalSet | Symmetric U ∧ frobenius U ≤ 2 * H - 1 ∧ 1 ∉ members U} ∪
        {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * (H + 1) - 1 ∧ 1 ∉ members U} := by
      rintro U ⟨hU, hf, h1⟩
      have hodd := hT.1 U H hU
      by_cases hlow : frobenius U ≤ 2 * H - 1
      · exact Or.inl ⟨hU, hlow, h1⟩
      · exact Or.inr ⟨hU, by omega, h1⟩
    have hfinU := hfin.union hfin2
    refine ⟨hfinU.subset hsub, ?_⟩
    calc _ ≤ _ := Set.ncard_le_ncard hsub hfinU
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ 2 ^ (H - 1) + 2 ^ (H + 1 - 2) := by rw [hnew]; omega
      _ = 2 ^ (H + 1 - 1) := by
        rw [show H + 1 - 2 = H - 1 by omega, show H + 1 - 1 = H - 1 + 1 by omega, pow_succ]
        ring

/-- For every `F ≥ 1`, among the row deletions of the almost symmetric numerical semigroups
with Frobenius number `F`, the semigroups number at least one and the outputs at most
`2^(⌊(F+1)/2⌋ - 1)`; the upper bounds also hold at `F = 0`, where there are no sources. -/
private lemma image_bound (F : ℕ) :
    (1 ≤ F → 1 ≤ {X | X ∈ phi '' {S | AlmostSymmetric S ∧ frobenius S = F} ∧
        ∀ a b, a ∈ X → b ∈ X → a + b ∈ X}.ncard) ∧
    {X | X ∈ phi '' {S | AlmostSymmetric S ∧ frobenius S = F} ∧
        ∀ a b, a ∈ X → b ∈ X → a + b ∈ X}.ncard ≤
      (phi '' {S | AlmostSymmetric S ∧ frobenius S = F}).ncard ∧
    (phi '' {S | AlmostSymmetric S ∧ frobenius S = F}).ncard ≤ 2 ^ ((F + 1) / 2 - 1) := by
  rcases Nat.eq_zero_or_pos F with hF0 | hF
  · have he : {S : NumericalSet | AlmostSymmetric S ∧ frobenius S = F} = ∅ := by
      ext S
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h
      have := frob_pos S
      omega
    rw [he, Set.image_empty]
    refine ⟨fun h => absurd h (by omega), ?_, by simp⟩
    simp
  obtain ⟨hfinA, hA⟩ := small_targets ((F + 1) / 2) (by omega)
  have hsub : phi '' {S | AlmostSymmetric S ∧ frobenius S = F} ⊆
      members '' {U : NumericalSet | Symmetric U ∧ frobenius U ≤ 2 * ((F + 1) / 2) - 1 ∧
        1 ∉ members U} := by
    rintro X ⟨S, ⟨hS, hSF⟩, rfl⟩
    obtain ⟨hsym, -, hfo, hle⟩ := out_spec S hS
    refine ⟨out S, ⟨hsym, by omega, ?_⟩, members_out S⟩
    rw [members_out]
    exact phi_omits_one S hS.1
  have hfinI := hfinA.image members
  have hfinS := hfinI.subset hsub
  have hbound : (phi '' {S | AlmostSymmetric S ∧ frobenius S = F}).ncard ≤
      2 ^ ((F + 1) / 2 - 1) :=
    calc _ ≤ _ := Set.ncard_le_ncard hsub hfinI
      _ ≤ _ := Set.ncard_image_le hfinA
      _ ≤ _ := hA
  have hNsub : {X | X ∈ phi '' {S | AlmostSymmetric S ∧ frobenius S = F} ∧
      ∀ a b, a ∈ X → b ∈ X → a + b ∈ X} ⊆ phi '' {S | AlmostSymmetric S ∧ frobenius S = F} :=
    fun X hX => hX.1
  have ho := DelgadoSuerYesilPhiOrdinaryFiber.result.2 (F + 1) (by omega)
  have hmem : {n : ℕ | n ≠ 1} ∈ {X | X ∈ phi '' {S | AlmostSymmetric S ∧ frobenius S = F} ∧
      ∀ a b, a ∈ X → b ∈ X → a + b ∈ X} := by
    refine ⟨⟨_, ⟨ho.2.1, by rw [ho.2.2.1]; omega⟩, ho.2.2.2.2⟩, ?_⟩
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega
  refine ⟨fun _ => ?_, Set.ncard_le_ncard hNsub hfinS, hbound⟩
  exact Nat.one_le_iff_ne_zero.mpr
    (Set.ncard_ne_zero_of_mem hmem (hfinS.subset hNsub))

/-- On every almost symmetric numerical semigroup `S` with genus `g` and Frobenius number `F`,
the row deletion `Φ(S)` is a symmetric numerical set of genus `F - g + 1` and Frobenius number
`2(F - g + 1) - 1 ≤ F`. For every `F ≥ 1`, writing `S_F` for the set of row deletions of the
almost symmetric semigroups with Frobenius number `F` and `NS_F` for those that are additively
closed, `1 ≤ |NS_F| ≤ |S_F| ≤ 2^(⌊(F+1)/2⌋ - 1)`; the two upper bounds hold for every `F`. -/
theorem result :
    (∀ S : NumericalSet, AlmostSymmetric S → ∃ V : NumericalSet, members V = phi S ∧
      Symmetric V ∧ V.gaps.card = frobenius S - S.gaps.card + 1 ∧
      frobenius V = 2 * (frobenius S - S.gaps.card + 1) - 1 ∧ frobenius V ≤ frobenius S) ∧
    (∀ F : ℕ,
      (1 ≤ F → 1 ≤ {X | X ∈ phi '' {S | AlmostSymmetric S ∧ frobenius S = F} ∧
          ∀ a b, a ∈ X → b ∈ X → a + b ∈ X}.ncard) ∧
      {X | X ∈ phi '' {S | AlmostSymmetric S ∧ frobenius S = F} ∧
          ∀ a b, a ∈ X → b ∈ X → a + b ∈ X}.ncard ≤
        (phi '' {S | AlmostSymmetric S ∧ frobenius S = F}).ncard ∧
      (phi '' {S | AlmostSymmetric S ∧ frobenius S = F}).ncard ≤ 2 ^ ((F + 1) / 2 - 1)) :=
  ⟨fun S hS => ⟨out S, members_out S, out_spec S hS⟩, image_bound⟩


end D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiImageBound
