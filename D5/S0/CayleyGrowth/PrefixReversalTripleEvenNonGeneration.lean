/- GID: D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration
   generality: G
   mirror-B: D5/B/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three prefix reversals with even length and small support do not generate the symmetric group. -/

import D5.S0.CayleyGrowth.PrefixReversalTripleOddNonGeneration
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.ZMod.Basic

namespace PrefixReversalTripleEvenNonGeneration

open PrefixReversalTripleOddNonGeneration

/-! The longest-reversal edges are the edges whose endpoint values add to `n - 1`. -/

def longEdge (n : ℕ) (e : Sym2 (Fin n)) : Prop :=
  ∃ i j : Fin n, e = s(i, j) ∧ i.val + j.val = n - 1

noncomputable def edgeWeight (n m k : ℕ) (e : Sym2 (Fin n)) : ZMod 2 := by
  classical
  exact if longEdge n e then 1 else 0

theorem edgeWeight_of_long {n m k : ℕ} {i j : Fin n}
    (h : i.val + j.val = n - 1) : edgeWeight n m k s(i, j) = 1 := by
  have hlong : longEdge n s(i, j) := ⟨i, j, rfl, h⟩
  simp [edgeWeight, hlong]

theorem edgeWeight_of_short {n m k L : ℕ} (hL : L < n) {i j : Fin n}
    (hi : i.val < L) (hs : i.val + j.val = L - 1) :
    edgeWeight n m k s(i, j) = 0 := by
  have hnot : ¬ longEdge n s(i, j) := by
    rintro ⟨a, b, hab, hsum⟩
    rcases (Sym2.eq_iff.mp hab) with hsame | hswap
    · rcases hsame with ⟨rfl, rfl⟩
      omega
    · rcases hswap with ⟨rfl, rfl⟩
      omega
  simp [edgeWeight, hnot]

noncomputable def pathParity {n m k : ℕ} {u v : Fin n}
    (p : (auxiliaryGraph n m k).Walk u v) : ZMod 2 :=
  (p.edges.map (edgeWeight n m k)).sum

noncomputable def rootPath {n m k : ℕ} (hTree : (auxiliaryGraph n m k).IsTree)
    (r v : Fin n) : (auxiliaryGraph n m k).Walk r v :=
  Classical.choose (hTree.existsUnique_path r v)

noncomputable def rootParity {n m k : ℕ} (hTree : (auxiliaryGraph n m k).IsTree)
    (r v : Fin n) : ZMod 2 := pathParity (rootPath hTree r v)

theorem rootParity_root {n m k : ℕ} (hTree : (auxiliaryGraph n m k).IsTree)
    (r : Fin n) : rootParity hTree r r = 0 := by
  have hroot : rootPath hTree r r = .nil := by
    apply (hTree.existsUnique_path r r).unique
    · exact (Classical.choose_spec (hTree.existsUnique_path r r)).1
    · exact SimpleGraph.Walk.IsPath.nil
  rw [rootParity, hroot]
  rfl

theorem rootParity_edge {n m k : ℕ} (hTree : (auxiliaryGraph n m k).IsTree)
    (r x y : Fin n) (hxy : (auxiliaryGraph n m k).Adj x y) :
    rootParity hTree r x + rootParity hTree r y = edgeWeight n m k s(x, y) := by
  let p : (auxiliaryGraph n m k).Walk r x := rootPath hTree r x
  let q : (auxiliaryGraph n m k).Walk r y := rootPath hTree r y
  have hp : p.IsPath := by
    exact (Classical.choose_spec (hTree.existsUnique_path r x)).1
  by_cases hy : y ∉ p.support
  · have hpc : (p.concat hxy).IsPath := hp.concat hy hxy
    have hqeq : q = p.concat hxy :=
      ((Classical.choose_spec (hTree.existsUnique_path r y)).2 _ hpc).symm
    change pathParity p + pathParity q = edgeWeight n m k s(x, y)
    rw [hqeq]
    simp only [pathParity, SimpleGraph.Walk.edges_concat, List.map_concat,
      List.sum_concat]
    rw [← add_assoc, ZModModule.add_self]
    simp
  · have hy : y ∈ p.support := by simpa only [not_not] using hy
    have htake : (p.takeUntil y hy).IsPath := hp.takeUntil hy
    have hqeq : q = p.takeUntil y hy :=
      ((Classical.choose_spec (hTree.existsUnique_path r y)).2 _ htake).symm
    have hdrop : (p.dropUntil y hy).IsPath := hp.dropUntil hy
    have hsingle : hxy.symm.toWalk.IsPath := SimpleGraph.Walk.IsPath.of_adj hxy.symm
    have hdeq : p.dropUntil y hy = hxy.symm.toWalk :=
      (hTree.existsUnique_path y x).unique hdrop hsingle
    -- Splitting the edge list once keeps `take_spec` from folding the append back into `p`.
    have hsplit : p.edges =
        (p.takeUntil y hy).edges ++ (p.dropUntil y hy).edges := by
      conv_lhs => rw [← p.take_spec hy]
      exact SimpleGraph.Walk.edges_append _ _
    have hpq : pathParity p = pathParity (p.takeUntil y hy) +
        edgeWeight n m k s(x, y) := by
      calc
        pathParity p = pathParity (p.takeUntil y hy) + pathParity (p.dropUntil y hy) := by
          simp [pathParity, hsplit]
        _ = pathParity (p.takeUntil y hy) + edgeWeight n m k s(x, y) := by
          rw [hdeq]
          simp [pathParity, SimpleGraph.Adj.edges_toWalk, Sym2.eq_swap]
    change pathParity p + pathParity q = edgeWeight n m k s(x, y)
    rw [hqeq, hpq]
    calc
      (pathParity (p.takeUntil y hy) + edgeWeight n m k s(x, y)) +
          pathParity (p.takeUntil y hy) =
          (pathParity (p.takeUntil y hy) + pathParity (p.takeUntil y hy)) +
            edgeWeight n m k s(x, y) := by ac_rfl
      _ = edgeWeight n m k s(x, y) := by
        rw [ZModModule.add_self, zero_add]

theorem prefix_reversal_adj_of_ne {n m k L : ℕ} (hL : L ≤ n)
    (hmem : L ∈ ({n, m, k} : Set ℕ)) (i : Fin n)
    (hne : prefixReversal L hL i ≠ i) :
    (auxiliaryGraph n m k).Adj i (prefixReversal L hL i) := by
  have hi : i.val < L := by
    by_contra hge
    apply hne
    change reverseIndex L hL i = i
    simp only [reverseIndex, dif_neg hge]
  refine ⟨Ne.symm hne, L, hmem, hi, ?_⟩
  change i.val + (reverseIndex L hL i).val = L - 1
  simp only [reverseIndex, dif_pos hi]
  omega

theorem prefix_reversal_no_fixed_of_even {n : ℕ} (heven : Even n) (i : Fin n) :
    prefixReversal n le_rfl i ≠ i := by
  rintro hfix
  obtain ⟨a, ha⟩ := heven
  have hval : i.val = n - 1 - i.val := by
    change reverseIndex n le_rfl i = i at hfix
    simp only [reverseIndex, dif_pos i.isLt] at hfix
    exact (Fin.ext_iff.mp hfix).symm
  omega

theorem short_reversal_preserves {n m k L : ℕ} (hL : L ≤ n)
    (hmem : L ∈ ({n, m, k} : Set ℕ)) (hshort : L < n)
    (hTree : (auxiliaryGraph n m k).IsTree) (r i : Fin n) :
    rootParity hTree r (prefixReversal L hL i) = rootParity hTree r i := by
  by_cases hfix : prefixReversal L hL i = i
  · simpa [hfix]
  · have hadj := prefix_reversal_adj_of_ne hL hmem i hfix
    have heq := rootParity_edge hTree r i (prefixReversal L hL i) hadj
    have hw : edgeWeight n m k s(i, prefixReversal L hL i) = 0 := by
      apply edgeWeight_of_short hshort
      · have hi : i.val < L := by
          by_contra hge
          apply hfix
          change reverseIndex L hL i = i
          simp only [reverseIndex, dif_neg hge]
        exact hi
      · change i.val + (reverseIndex L hL i).val = L - 1
        have hi : i.val < L := by
          by_contra hge
          apply hfix
          change reverseIndex L hL i = i
          simp only [reverseIndex, dif_neg hge]
        simp only [reverseIndex, dif_pos hi]
        omega
    rw [hw] at heq
    have hneg : rootParity hTree r (prefixReversal L hL i) =
        -rootParity hTree r i := eq_neg_of_add_eq_zero_right heq
    simpa [ZModModule.neg_eq_self] using hneg

theorem longest_reversal_exchanges {n m k : ℕ} (heven : Even n)
    (hTree : (auxiliaryGraph n m k).IsTree) (r i : Fin n) :
    rootParity hTree r (prefixReversal n le_rfl i) =
      rootParity hTree r i + 1 := by
  have hne := prefix_reversal_no_fixed_of_even heven i
  have hadj := prefix_reversal_adj_of_ne (n := n) (m := m) (k := k)
    le_rfl (by simp) i hne
  have heq := rootParity_edge hTree r i (prefixReversal n le_rfl i) hadj
  have hi : i.val < n := i.isLt
  have hw : edgeWeight n m k s(i, prefixReversal n le_rfl i) = 1 := by
    apply edgeWeight_of_long
    change i.val + (reverseIndex n le_rfl i).val = n - 1
    simp only [reverseIndex, dif_pos hi]
    omega
  rw [hw] at heq
  calc
    rootParity hTree r (prefixReversal n le_rfl i) =
        (rootParity hTree r i + rootParity hTree r i) +
          rootParity hTree r (prefixReversal n le_rfl i) := by
            rw [ZModModule.add_self, zero_add]
    _ = rootParity hTree r i +
          (rootParity hTree r i + rootParity hTree r (prefixReversal n le_rfl i)) := by
            ac_rfl
    _ = rootParity hTree r i + 1 := by rw [heq]

def shifts {n : ℕ} (c : Fin n → ZMod 2) (g : Equiv.Perm (Fin n)) : Prop :=
  ∃ b : ZMod 2, ∀ i, c (g i) = c i + b

theorem shifts_one {n : ℕ} (c : Fin n → ZMod 2) : shifts c (1 : Equiv.Perm (Fin n)) := by
  refine ⟨0, ?_⟩
  intro i
  simp [shifts]

theorem shifts_mul {n : ℕ} {c : Fin n → ZMod 2}
    {g h : Equiv.Perm (Fin n)} (hg : shifts c g) (hh : shifts c h) :
    shifts c (g * h) := by
  rcases hg with ⟨b, hb⟩
  rcases hh with ⟨d, hd⟩
  refine ⟨d + b, ?_⟩
  intro i
  change c (g (h i)) = c i + (d + b)
  rw [hb, hd]
  ac_rfl

theorem shifts_inv {n : ℕ} {c : Fin n → ZMod 2}
    {g : Equiv.Perm (Fin n)} (hg : shifts c g) : shifts c g⁻¹ := by
  rcases hg with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro i
  have hgi := hb (g.symm i)
  simp only [Equiv.apply_symm_apply] at hgi
  calc
    c (g.symm i) = c (g.symm i) + (b + b) := by
      rw [ZModModule.add_self, add_zero]
    _ = (c (g.symm i) + b) + b := by rw [add_assoc]
    _ = c i + b := by rw [← hgi]

theorem tripleSubgroup_shifts {n m k : ℕ} (hm : m ≤ n) (hk : k ≤ n)
    (hTree : (auxiliaryGraph n m k).IsTree) (r : Fin n)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ tripleSubgroup n m k hm hk)
    (hsmall : m + k < n) (heven : Even n) (hkm : k < m) :
    shifts (rootParity hTree r) g := by
  change g ∈ Subgroup.closure _ at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨1, longest_reversal_exchanges heven hTree r⟩
      · have hmshort : m < n := by omega
        refine ⟨0, fun i => ?_⟩
        simpa only [add_zero] using short_reversal_preserves hm (by simp) hmshort hTree r i
      · have hks : k < n := by omega
        refine ⟨0, fun i => ?_⟩
        simpa only [add_zero] using short_reversal_preserves hk (by simp) hks hTree r i
  | one => exact shifts_one _
  | mul g h _ _ hg hh => exact shifts_mul hg hh
  | inv g _ hg => exact shifts_inv hg

theorem tripleSubgroup_ne_top_of_tree {n m k : ℕ} (hkmin : 2 ≤ k)
    (hm : m ≤ n) (hk : k ≤ n)
    (hTree : (auxiliaryGraph n m k).IsTree) (heven : Even n) (hsmall : m + k < n)
    (hkm : k < m) (hmn : m < n) :
    tripleSubgroup n m k hm hk ≠ ⊤ := by
  classical
  let r : Fin n := ⟨0, by omega⟩
  let c : Fin n → ZMod 2 := rootParity hTree r
  let z : Fin n := prefixReversal n le_rfl r
  have hz : c z = 1 := by
    dsimp [c, z]
    rw [longest_reversal_exchanges heven hTree r]
    rw [rootParity_root hTree r]
    simp
  have hn4 : 4 ≤ n := by omega
  have hrne : r ≠ z := by
    intro h
    exact prefix_reversal_no_fixed_of_even heven r (by simpa [z] using h.symm)
  let x : Fin n := if z = ⟨2, by omega⟩ then ⟨3, by omega⟩ else ⟨2, by omega⟩
  have hxr : x ≠ r := by
    intro h
    have hv := congrArg Fin.val h
    by_cases hz2 : z = (⟨2, by omega⟩ : Fin n)
    · have hx : x = ⟨3, by omega⟩ := if_pos hz2
      rw [hx] at hv
      change (3 : ℕ) = 0 at hv
      omega
    · have hx : x = ⟨2, by omega⟩ := if_neg hz2
      rw [hx] at hv
      change (2 : ℕ) = 0 at hv
      omega
  have hxz : x ≠ z := by
    intro h
    by_cases hz2 : z = (⟨2, by omega⟩ : Fin n)
    · have hx : x = ⟨3, by omega⟩ := if_pos hz2
      have hv := congrArg Fin.val (hx.symm.trans (h.trans hz2))
      change (3 : ℕ) = 2 at hv
      omega
    · have hx : x = ⟨2, by omega⟩ := if_neg hz2
      exact hz2 (h.symm.trans hx)
  have hzero_pair : ∃ u v : Fin n, u ≠ v ∧ c u = 0 ∧ c v = 0 := by
    by_cases hcx : c x = 0
    · exact ⟨r, x, hxr.symm, rootParity_root hTree r, hcx⟩
    · have hcx1 : c x = 1 := by
        have hvpos : 0 < (c x).val := ZMod.val_pos.mpr hcx
        have hvlt : (c x).val < 2 := ZMod.val_lt _
        have hvone : (c x).val = 1 := by omega
        exact (ZMod.val_eq_one (by decide) _).mp hvone
      let y : Fin n := prefixReversal n le_rfl x
      have hy : c y = 0 := by
        calc
          c y = c x + 1 := longest_reversal_exchanges heven hTree r x
          _ = 0 := by
            rw [hcx1]
            exact ZModModule.add_self 1
      have hyr : y ≠ r := by
        intro hyr
        have : x = z := by
          apply (prefixReversal n le_rfl).injective
          change y = reverseIndex n le_rfl (reverseIndex n le_rfl r)
          exact hyr.trans (reverseIndex_involutive (L := n) le_rfl r).symm
        exact hxz this
      exact ⟨r, y, hyr.symm, rootParity_root hTree r, hy⟩
  obtain ⟨u, v, huv, hcu, hcv⟩ := hzero_pair
  have huvz : u ≠ z := by
    intro huz
    rw [huz, hz] at hcu
    exact (by decide : (1 : ZMod 2) ≠ 0) hcu
  have hvz : v ≠ z := by
    intro hvz
    rw [hvz, hz] at hcv
    exact (by decide : (1 : ZMod 2) ≠ 0) hcv
  let t : Equiv.Perm (Fin n) := Equiv.swap u z
  have ht_not : ¬ shifts c t := by
    rintro ⟨b, hb⟩
    have hb0 := hb v
    rw [Equiv.swap_apply_of_ne_of_ne huv.symm hvz] at hb0
    rw [hcv] at hb0
    have hbzero : b = 0 := by simpa using hb0.symm
    have hbu := hb u
    rw [Equiv.swap_apply_left, hcu, hz, hbzero, add_zero] at hbu
    exact (by decide : (1 : ZMod 2) ≠ 0) hbu
  intro htop
  have hmem : t ∈ tripleSubgroup n m k hm hk := by
    rw [htop]
    trivial
  exact ht_not (tripleSubgroup_shifts hm hk hTree r hmem hsmall heven hkm)

/-- Conjecture 4, second clause: for even `n`, if `2 ≤ k < m < n` and `m + k < n`,
the three prefix reversals generate a proper subgroup of the symmetric group. -/
theorem even_prefix_reversal_triple_ne_top {n m k : ℕ}
    (hk : 2 ≤ k) (hkm : k < m) (hmn : m < n) (heven : Even n)
    (hsmall : m + k < n) :
    tripleSubgroup n m k (Nat.le_of_lt hmn) (Nat.le_of_lt (hkm.trans hmn)) ≠ ⊤ := by
  by_cases hconn : (auxiliaryGraph n m k).Connected
  · have hbound := auxiliaryGraph_edge_bound (Nat.le_of_lt hmn)
      (Nat.le_of_lt (hkm.trans hmn))
    have hlower := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin] at hlower
    have hupper : Nat.card (auxiliaryGraph n m k).edgeSet ≤ n - 1 := by
      obtain ⟨a, ha⟩ := heven
      omega
    have hedge : Nat.card (auxiliaryGraph n m k).edgeSet + 1 = n := by omega
    have hTree : (auxiliaryGraph n m k).IsTree := by
      apply SimpleGraph.isTree_iff_connected_and_card.mpr
      exact ⟨hconn, by simpa only [Nat.card_fin] using hedge⟩
    exact tripleSubgroup_ne_top_of_tree hk (Nat.le_of_lt hmn)
      (Nat.le_of_lt (hkm.trans hmn)) hTree heven hsmall hkm hmn
  · exact tripleSubgroup_ne_top_of_not_connected (by omega)
      (Nat.le_of_lt hmn) (Nat.le_of_lt (hkm.trans hmn)) hconn

#print axioms even_prefix_reversal_triple_ne_top

end PrefixReversalTripleEvenNonGeneration
