/- GID: D5/S3/Combinatorics/Sequenceability/HalfGirthGoodOrdering
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/HalfGirthGoodOrdering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rank-aware greedy ordering of original labels above half girth. -/


import D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
import D5.S1.Words.Sequenceability.SeparatedPrefixReflection
import Mathlib.Order.Interval.Finset.Nat

/-! All sums and all enumerations use the original indices. No assumption on
the total sum, torsion, or an ordering certificate is made. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering

open scoped BigOperators
open Finset
open PairedZeroSubsetSpectrum (Good)

noncomputable section

universe u v
variable {X : Type u} {G : Type v} [Fintype X] [DecidableEq X] [AddCommGroup G]

private def total (a : X → G) (w : List X) : G := (w.map a).sum

private def ps (a : X → G) (w : List X) (i : ℕ) : G := total a (w.take i)

omit [Fintype X] in
private theorem total_finset (a : X → G) {w : List X} (hw : w.Nodup) :
    total a w = ∑ x ∈ w.toFinset, a x := (List.sum_toFinset a hw).symm

omit [Fintype X] [DecidableEq X] in
private theorem prefix_split (a : X → G) (w : List X) {i j : ℕ} (hij : i ≤ j) :
    ps a w i + total a ((w.drop i).take (j - i)) = ps a w j := by
  have h := List.sum_take_add_sum_drop ((w.map a).take j) i
  simpa only [List.take_take, Nat.min_eq_left hij, List.drop_take,
    ← List.map_take, ← List.map_drop, ps, total] using h

omit [Fintype X] [DecidableEq X] in
private theorem prefix_ne_of_short (a : X → G) {K : ℕ}
    (hshort : ∀ u : List X, u.Nodup → 0 < u.length → u.length < K → total a u ≠ 0)
    {w : List X} (hw : w.Nodup) {i j : ℕ} (hij : i < j)
    (hj : j ≤ w.length) (hK : j - i < K) : ps a w i ≠ ps a w j := by
  intro he
  have hs := prefix_split a w hij.le
  have hlen : ((w.drop i).take (j - i)).length = j - i := by
    simp only [List.length_take, List.length_drop]
    omega
  have hn := hshort ((w.drop i).take (j - i)) hw.drop.take
    (by rw [hlen]; omega) (by rw [hlen]; exact hK)
  exact hn (by rw [← he] at hs; exact add_left_cancel (hs.trans (add_zero _).symm))

omit [DecidableEq X] in
private theorem short_of_minimum (a : X → G) {K : ℕ} (hK : K ≤ Fintype.card X)
    (hmin : ∀ T : Finset X, T.Nonempty → T ≠ univ → (∑ x ∈ T, a x) = 0 → K ≤ T.card) :
    ∀ u : List X, u.Nodup → 0 < u.length → u.length < K → total a u ≠ 0 := by
  classical
  intro u hu hpos hlt hz
  have hc := List.toFinset_card_of_nodup hu
  have hn : u.toFinset.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hp : u.toFinset ≠ univ := by
    intro he
    have : u.length = Fintype.card X := by simpa [he] using hc.symm
    omega
  have hh := hmin u.toFinset hn hp (by rwa [total_finset a hu] at hz)
  omega

/- Equal original sums produce an actual zero replacement, so its rank is
controlled by the minimum of the complete proper-zero family. -/
private theorem replacement_rank (a : X → G) {S A B : Finset X}
    (hS : (∑ x ∈ S, a x) = 0)
    (hmin : ∀ T : Finset X, T.Nonempty → T ≠ univ →
      (∑ x ∈ T, a x) = 0 → S.card ≤ T.card)
    (hA : A ⊂ S) (hAn : A.Nonempty) (hB : B ⊆ Sᶜ)
    (he : (∑ x ∈ A, a x) = ∑ x ∈ B, a x) : A.card ≤ B.card := by
  let T := (S \ A) ∪ B
  have hd : Disjoint (S \ A) B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxb
    exact (Finset.mem_compl.mp (hB hxb)) (Finset.mem_sdiff.mp hx).1
  have hTn : T.Nonempty := by
    obtain ⟨x, hxS, hxA⟩ := Finset.exists_of_ssubset hA
    exact ⟨x, Finset.mem_union_left B (Finset.mem_sdiff.mpr ⟨hxS, hxA⟩)⟩
  have hTp : T ≠ univ := by
    obtain ⟨x, hxA⟩ := hAn
    intro ht
    have hx : x ∈ T := by rw [ht]; exact mem_univ x
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_sdiff.mp hx).2 hxA
    · exact (Finset.mem_compl.mp (hB hx)) (hA.subset hxA)
  have hTz : (∑ x ∈ T, a x) = 0 := by
    dsimp [T]
    rw [Finset.sum_union hd, Finset.sum_sdiff_eq_sub hA.subset, hS, he]
    abel
  have hm := hmin T hTn hTp hTz
  have hc : T.card = S.card - A.card + B.card := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint hd, Finset.card_sdiff_of_subset hA.subset]
  have ha := Finset.card_le_card hA.subset
  omega

/- At stage d, a forbidden suffix has rank at least d+1. Its sum excludes
at most one remaining original label; the strict surplus is S.card-c.length. -/
private theorem greedy_prefixes (a : X → G) (ha : Function.Injective a)
    (S : Finset X) (c : List X) (hc : c.Nodup) (hcS : c.toFinset ⊆ Sᶜ)
    (hgap : c.length < S.card) (hS : (∑ x ∈ S, a x) = 0)
    (hmin : ∀ T : Finset X, T.Nonempty → T ≠ univ →
      (∑ x ∈ T, a x) = 0 → S.card ≤ T.card) :
    ∃ r : List X, r.Nodup ∧ r.toFinset = S ∧
      ∀ d, 0 < d → d < S.card → ∀ j, 0 < j → j ≤ c.length →
        ps a r d ≠ total a (c.drop (c.length - j)) := by
  classical
  have build : ∀ d, d ≤ S.card → ∃ r : List X,
      r.Nodup ∧ r.toFinset ⊆ S ∧ r.length = d ∧
      ∀ e, 0 < e → e ≤ d → e < S.card → ∀ j, 0 < j → j ≤ c.length →
        ps a r e ≠ total a (c.drop (c.length - j)) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨[], by simp, by simp, rfl, ?_⟩
      intro e he hed
      omega
    | succ d ih =>
      intro hd
      obtain ⟨r, hr, hrS, hrd, havoid⟩ := ih (by omega)
      let R := S \ r.toFinset
      have hRcard : R.card = S.card - d := by
        dsimp [R]
        rw [Finset.card_sdiff_of_subset hrS, List.toFinset_card_of_nodup hr, hrd]
      have hRpos : R.Nonempty := Finset.card_pos.mp (by omega)
      have next : ∃ x ∈ R, d + 1 < S.card → ∀ j, 0 < j → j ≤ c.length →
          total a r + a x ≠ total a (c.drop (c.length - j)) := by
        by_cases hlast : d + 1 = S.card
        · obtain ⟨x, hx⟩ := hRpos
          exact ⟨x, hx, by omega⟩
        · have hdK : d + 1 < S.card := by omega
          let values : Finset G := (Finset.Icc (d + 1) c.length).image
            (fun j => total a (c.drop (c.length - j)))
          let images : Finset G := R.image (fun x => total a r + a x)
          have himages : images.card = R.card := by
            apply Finset.card_image_of_injective
            intro x y he
            exact ha (add_left_cancel he)
          have hvalues : values.card ≤ c.length - d := by
            exact (Finset.card_image_le).trans (by simp [Nat.card_Icc])
          have hlt : values.card < images.card := by omega
          obtain ⟨g, hg, hgv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
          obtain ⟨x, hxR, rfl⟩ := Finset.mem_image.mp hg
          refine ⟨x, hxR, fun _ j hj hjc he => hgv ?_⟩
          have hxS : x ∈ S := (Finset.mem_sdiff.mp hxR).1
          have hxr : x ∉ r.toFinset := (Finset.mem_sdiff.mp hxR).2
          have hAcard : (insert x r.toFinset).card = d + 1 := by
            rw [Finset.card_insert_of_notMem hxr, List.toFinset_card_of_nodup hr, hrd]
          have hAS : insert x r.toFinset ⊂ S :=
            Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset hxS hrS, by
              intro heq; have := congrArg Finset.card heq; omega⟩
          have hB : (c.drop (c.length - j)).toFinset ⊆ Sᶜ := by
            intro y hy
            exact hcS (List.mem_toFinset.mpr (List.mem_of_mem_drop (List.mem_toFinset.mp hy)))
          have hrank := replacement_rank a hS hmin hAS (by simp) hB (by
            rw [Finset.sum_insert hxr, ← total_finset a hr,
              ← total_finset a hc.drop]
            simpa [add_comm] using he)
          have hBcard : (c.drop (c.length - j)).toFinset.card = j := by
            rw [List.toFinset_card_of_nodup hc.drop, List.length_drop]
            omega
          apply Finset.mem_image.mpr
          exact ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjc⟩, he.symm⟩
      obtain ⟨x, hxR, hx⟩ := next
      have hxr : x ∉ r := by
        simpa using (Finset.mem_sdiff.mp hxR).2
      refine ⟨r ++ [x], ?_, ?_, by simp [hrd], ?_⟩
      · apply List.nodup_append.mpr
        refine ⟨hr, by simp, ?_⟩
        intro y hyr z hzx hyz
        have hzx' : z = x := by simpa using hzx
        exact hxr (by simpa only [hyz, hzx'] using hyr)
      · simpa using Finset.insert_subset (Finset.mem_sdiff.mp hxR).1 hrS
      · intro e he hed heK j hj hjc
        by_cases her : e ≤ d
        · simpa only [ps, List.take_append, hrd, Nat.sub_eq_zero_of_le her,
            List.take_zero, List.append_nil] using havoid e he her heK j hj hjc
        · have heq : e = d + 1 := by omega
          subst e
          have hlen : (r ++ [x]).length = d + 1 := by simp [hrd]
          simpa [ps, ← hlen, total] using hx heK j hj hjc
  obtain ⟨r, hr, hrS, hrl, havoid⟩ := build S.card (le_refl _)
  have hrEq : r.toFinset = S := Finset.eq_of_subset_of_card_le hrS (by
    rw [List.toFinset_card_of_nodup hr, hrl])
  exact ⟨r, hr, hrEq, fun d hd hdK j hj hjc => havoid d hd hdK.le hdK j hj hjc⟩

omit [Fintype X] [DecidableEq X] in
private theorem prefix_append_left (a : X → G) (c t : List X) {i : ℕ}
    (hi : i ≤ c.length) : ps a (c ++ t) i = ps a c i := by
  simpa only [D5.S1.Words.Sequenceability.SeparatedPrefixReflection.pref,
    ps, total, List.map_take, List.map_append] using
    D5.S1.Words.Sequenceability.SeparatedPrefixReflection.pref_append_left
      (c.map a) (t.map a) (by simpa using hi)

omit [Fintype X] [DecidableEq X] in
private theorem prefix_append_right (a : X → G) (c t : List X) {i : ℕ}
    (hi : c.length ≤ i) :
    ps a (c ++ t) i = total a c + ps a t (i - c.length) := by
  simpa only [D5.S1.Words.Sequenceability.SeparatedPrefixReflection.pref,
    ps, total, List.map_take, List.map_append, List.length_map] using
    D5.S1.Words.Sequenceability.SeparatedPrefixReflection.pref_append_right
      (c.map a) (t.map a) (by simpa using hi)

/- The reversed greedy list makes the whole S block the sole zero interval.
The equivalent ps formulation includes all interval endpoints. -/
omit [Fintype X] [DecidableEq X] in
private theorem sole_collision (a : X → G) {K : ℕ}
    (hshort : ∀ u : List X, u.Nodup → 0 < u.length → u.length < K → total a u ≠ 0)
    (c r : List X) (hw : (c ++ r.reverse).Nodup) (hrK : r.length = K)
    (hgap : c.length < K) (hrzero : total a r = 0)
    (havoid : ∀ d, 0 < d → d < K → ∀ j, 0 < j → j ≤ c.length →
      ps a r d ≠ total a (c.drop (c.length - j))) :
    ∀ i j, i < j → j ≤ (c ++ r.reverse).length →
      ps a (c ++ r.reverse) i = ps a (c ++ r.reverse) j →
      i = c.length ∧ j = (c ++ r.reverse).length := by
  intro i j hij hj he
  have hlen : (c ++ r.reverse).length = c.length + K := by simp [hrK]
  have hc : c.Nodup := (List.nodup_append.mp hw).1
  by_cases hjc : j ≤ c.length
  · exact (prefix_ne_of_short a hshort hw hij hj (by omega) he).elim
  by_cases hci : c.length ≤ i
  · by_cases hdiff : j - i < K
    · exact (prefix_ne_of_short a hshort hw hij hj hdiff he).elim
    · constructor <;> omega
  have hic : i < c.length := by omega
  have hjc' : c.length < j := by omega
  let v := j - c.length
  have hv : 0 < v := by dsimp [v]; omega
  have hvK : v ≤ K := by dsimp [v]; omega
  rw [prefix_append_left a c r.reverse hic.le,
    prefix_append_right a c r.reverse hjc'.le] at he
  have hcs : ps a c i + total a (c.drop i) = total a c := by
    simpa only [← List.map_take, ← List.map_drop, ps, total] using
      List.sum_take_add_sum_drop (c.map a) i
  have htz : total a r.reverse = 0 := by simpa [total] using hrzero
  have hts : ps a r.reverse v + total a (r.reverse.drop v) = 0 := by
    have h : ps a r.reverse v + total a (r.reverse.drop v) = total a r.reverse := by
      simpa only [ps, total, ← List.map_take, ← List.map_drop] using
        List.sum_take_add_sum_drop (r.reverse.map a) v
    rwa [htz] at h
  have hcross : total a (c.drop i) = total a (r.reverse.drop v) := by
    apply add_right_cancel (b := ps a r.reverse v)
    calc
      total a (c.drop i) + ps a r.reverse v = 0 := by
        apply add_left_cancel (a := ps a c i)
        simpa only [add_assoc, add_zero, ← hcs] using he.symm
      _ = total a (r.reverse.drop v) + ps a r.reverse v := by
        simpa only [add_comm] using hts.symm
  have hrev : total a (r.reverse.drop v) = ps a r (K - v) := by
    simp [List.drop_reverse, ps, total, hrK]
  rw [hrev] at hcross
  by_cases hvfull : v = K
  · have hz : total a (c.drop i) = 0 := by simpa [hvfull, ps, total] using hcross
    exact (hshort (c.drop i) hc.drop (by simp; omega) (by simp; omega) hz).elim
  · have hh := havoid (K - v) (by omega) (by omega) (c.length - i)
      (by omega) (by omega)
    exact (hh (by simpa only [show c.length - (c.length - i) = i by omega]
      using hcross.symm)).elim

omit [Fintype X] [DecidableEq X] in
private theorem swap_prefix (a : X → G) (p q : List X) (c s : X) {i : ℕ}
    (hi : i ≠ p.length + 1) :
    ps a (p ++ s :: c :: q) i = ps a (p ++ c :: s :: q) i := by
  by_cases hip : i ≤ p.length
  · rw [prefix_append_left a p _ hip, prefix_append_left a p _ hip]
  · have htwo : 2 ≤ i - p.length := by omega
    rw [prefix_append_right a p _ (by omega), prefix_append_right a p _ (by omega)]
    obtain ⟨n, hn⟩ : ∃ n, i - p.length = n + 2 := ⟨i - p.length - 2, by omega⟩
    simp only [ps, hn, List.take_succ_cons, total, List.map_cons, List.sum_cons]
    abel

omit [Fintype X] [DecidableEq X] in
private theorem swapped_good (a : X → G) (ha : Function.Injective a) {K : ℕ}
    (hshort : ∀ u : List X, u.Nodup → 0 < u.length → u.length < K → total a u ≠ 0)
    (p q : List X) (c s : X) (hw : (p ++ c :: s :: q).Nodup)
    (hK : q.length + 1 = K) (hgap : p.length + 1 < K)
    (hzero : total a (s :: q) = 0)
    (hsole : ∀ i j, i < j → j ≤ (p ++ c :: s :: q).length →
      ps a (p ++ c :: s :: q) i = ps a (p ++ c :: s :: q) j →
      i = p.length + 1 ∧ j = (p ++ c :: s :: q).length) :
    Good ((p ++ s :: c :: q).map a) := by
  have hperm : (p ++ s :: c :: q).Perm (p ++ c :: s :: q) :=
    List.Perm.append_left p (List.Perm.swap _ _ _)
  have hwnd : (p ++ s :: c :: q).Nodup := hperm.nodup_iff.mpr hw
  have hcs : c ≠ s := by
    have h := (List.nodup_append.mp hw).2.1
    exact fun he => (List.nodup_cons.mp h).1 (by simp [he])
  have hlen : (p ++ s :: c :: q).length = p.length + 1 + K := by simp; omega
  have hnew : ∀ j, p.length + 1 < j → j ≤ (p ++ s :: c :: q).length →
      ps a (p ++ s :: c :: q) (p.length + 1) ≠ ps a (p ++ s :: c :: q) j := by
    intro j hj hjw
    by_cases hjend : j = (p ++ s :: c :: q).length
    · subst j
      intro he
      have hpref : ps a (p ++ s :: c :: q) (p.length + 1) = total a p + a s := by
        rw [prefix_append_right a p _ (by omega)]
        simp [ps, total]
      have hend : ps a (p ++ s :: c :: q) (p ++ s :: c :: q).length =
          total a p + a s + a c + total a q := by
        rw [show ps a (p ++ s :: c :: q) (p ++ s :: c :: q).length =
          total a (p ++ s :: c :: q) by unfold ps; rw [List.take_length]]
        simp [total, add_assoc]
      rw [hpref, hend] at he
      have hz : a s + total a q = 0 := by simpa [total] using hzero
      have heq : a c = a s := by
        apply add_right_cancel (b := total a q)
        calc
          a c + total a q = 0 := by
            apply add_left_cancel (a := total a p + a s)
            simpa only [add_assoc, add_zero] using he.symm
          _ = a s + total a q := hz.symm
      exact hcs (ha heq)
    · exact prefix_ne_of_short a hshort hwnd hj hjw (by omega)
  change D5.S1.Words.Sequenceability.SeparatedPrefixReflection.Good _
  apply (D5.S1.Words.Sequenceability.SeparatedPrefixReflection.good_iff _).mpr
  intro i j hij hj he
  have hjw : j ≤ (p ++ s :: c :: q).length := by simpa using hj
  have he' : ps a (p ++ s :: c :: q) i = ps a (p ++ s :: c :: q) j := by
    change (List.take i ((p ++ s :: c :: q).map a)).sum =
      (List.take j ((p ++ s :: c :: q).map a)).sum at he
    simpa only [ps, total, ← List.map_take] using he
  by_cases hi : i = p.length + 1
  · subst i
    exact (hnew j hij hjw he').elim
  by_cases hjcut : j = p.length + 1
  · subst j
    exact (prefix_ne_of_short a hshort hwnd hij hjw (by omega) he').elim
  rw [swap_prefix a p q c s hi, swap_prefix a p q c s hjcut] at he'
  have hh := hsole i j hij (by simpa using hjw) he'
  exact (hi hh.1).elim

omit [DecidableEq X] in
/-- Every half-girth instance has a literal enumeration of all original indices
whose mapped word has no nonempty proper zero interval. -/
theorem exists_good_order (a : X → G) (ha : Function.Injective a)
    (_ha0 : ∀ x, a x ≠ 0) (k : ℕ) (_hk : 2 ≤ k) (_hkm : k ≤ Fintype.card X)
    (hhalf : Fintype.card X < 2 * k)
    (hgirth : ∀ T : Finset X, T.Nonempty → T ≠ univ →
      (∑ x ∈ T, a x) = 0 → k ≤ T.card) :
    ∃ w : List X, w.Perm (univ : Finset X).toList ∧ Good (w.map a) := by
  classical
  let F := (univ : Finset (Finset X)).filter
    (fun T => T.Nonempty ∧ T ≠ univ ∧ (∑ x ∈ T, a x) = 0)
  by_cases hF : F.Nonempty
  · obtain ⟨S, hSF, hminS⟩ := Finset.exists_min_image F Finset.card hF
    have hS : S.Nonempty ∧ S ≠ univ ∧ (∑ x ∈ S, a x) = 0 := by
      simpa [F] using hSF
    have hmin : ∀ T : Finset X, T.Nonempty → T ≠ univ →
        (∑ x ∈ T, a x) = 0 → S.card ≤ T.card := by
      intro T hn hp hz
      exact hminS T (by simp [F, hn, hp, hz])
    have hkS := hgirth S hS.1 hS.2.1 hS.2.2
    have hSm : S.card ≤ Fintype.card X := Finset.card_le_univ S
    have hshort := short_of_minimum a hSm hmin
    let c := Sᶜ.toList
    have hclen : c.length = Fintype.card X - S.card := by simp [c, Finset.card_compl]
    have hgap : c.length < S.card := by omega
    obtain ⟨r, hr, hrS, hav⟩ := greedy_prefixes a ha S c (Finset.nodup_toList _)
      (by simp [c]) hgap hS.2.2 hmin
    have hrlen : r.length = S.card := by
      rw [← List.toFinset_card_of_nodup hr, hrS]
    have hrzero : total a r = 0 := by rw [total_finset a hr, hrS]; exact hS.2.2
    have hw : (c ++ r.reverse).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨Finset.nodup_toList _, List.nodup_reverse.mpr hr, ?_⟩
      intro x hxc y hyr hxy
      subst y
      have hxr := hyr
      have hxS : x ∈ S := by rw [← hrS]; simpa using hxr
      exact (Finset.mem_compl.mp (by simpa [c] using hxc)) hxS
    have hinventory : (c ++ r.reverse).toFinset = univ := by
      have hcS : Sᶜ ∪ S = univ := by
        ext x
        by_cases hx : x ∈ S <;> simp [hx]
      simpa [c, hrS] using hcS
    have hsole := sole_collision a hshort c r hw hrlen hgap hrzero hav
    have hcne : c ≠ [] := by
      intro he
      have hc0 : Sᶜ = ∅ := by simpa [c] using congrArg List.toFinset he
      exact hS.2.1 (compl_eq_bot.mp hc0)
    obtain ⟨x, p', hcx'⟩ := List.exists_cons_of_ne_nil
      (show c.reverse ≠ [] by simpa using hcne)
    let p := p'.reverse
    have hcx : c = p ++ [x] := by
      simpa [p] using congrArg List.reverse hcx'
    have hrne : r.reverse ≠ [] := by
      intro he
      have : r.length = 0 := by simpa using congrArg List.length he
      omega
    obtain ⟨s, q, hsq⟩ := List.exists_cons_of_ne_nil hrne
    let w := p ++ s :: x :: q
    have hperm : w.Perm (c ++ r.reverse) := by
      simpa only [w, hcx, hsq, List.append_assoc, List.singleton_append] using
        (List.Perm.append_left p (List.Perm.swap x s q))
    refine ⟨w, ?_, ?_⟩
    · apply List.perm_ext_iff_of_nodup (hperm.nodup_iff.mpr hw) (Finset.nodup_toList _)|>.mpr
      intro y
      rw [hperm.mem_iff, ← List.mem_toFinset, hinventory]
      simp
    · apply swapped_good a ha hshort p q x s
      · simpa [hcx, hsq, List.append_assoc] using hw
      · have := congrArg List.length hsq
        simp only [List.length_reverse, List.length_cons] at this
        omega
      · simpa [hcx] using hgap
      · have hz : total a r.reverse = 0 := by simpa [total] using hrzero
        simpa only [hsq] using hz
      · simpa [hcx, hsq, List.append_assoc] using hsole
  · have hmin : ∀ T : Finset X, T.Nonempty → T ≠ univ →
        (∑ x ∈ T, a x) = 0 → Fintype.card X ≤ T.card := by
      intro T hn hp hz
      exact (hF ⟨T, by simp [F, hn, hp, hz]⟩).elim
    have hshort := short_of_minimum a (le_refl (Fintype.card X)) hmin
    refine ⟨univ.toList, .refl _, ?_⟩
    change D5.S1.Words.Sequenceability.SeparatedPrefixReflection.Good _
    apply (D5.S1.Words.Sequenceability.SeparatedPrefixReflection.good_iff _).mpr
    intro i j hij hj he
    by_contra hp
    have hlen : ((univ : Finset X).toList.map a).length = Fintype.card X := by simp
    have hd : j - i < Fintype.card X := by omega
    apply prefix_ne_of_short a hshort (Finset.nodup_toList _) hij
      (by simpa only [List.length_map] using hj) hd
    simpa only [D5.S1.Words.Sequenceability.SeparatedPrefixReflection.pref,
      ps, total, ← List.map_take] using he

end
end D5.S3.Combinatorics.Sequenceability.HalfGirthGoodOrdering
