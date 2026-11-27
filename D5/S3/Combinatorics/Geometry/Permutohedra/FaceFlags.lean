/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/FaceFlags
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every face extends to a permutation flag and its rank counts the free prefix ranks. -/
import D5.S3.Combinatorics.Geometry.Permutohedra.FaceLattice
import Mathlib.Order.Prod.Lex.Basic

/-! Permutation extensions and unoccupied cut ranks of a face. -/

namespace Rossi
open Finset D5.S3.Combinatorics.Graph.PrefixHamming

def preceding {n : ℕ} (x : CutChain n) (a : Fin n) := x.cuts.filter fun d => a ∉ d

private theorem preceding_ssubset {n : ℕ} {x : CutChain n} {c : Finset (Fin n)}
    (hc : c ∈ x.cuts) {a b : Fin n} (ha : a ∈ c) (hb : b ∉ c) :
    preceding x a ⊂ preceding x b := by
  have hs : preceding x a ⊆ preceding x b := by
    intro d hd
    obtain ⟨hd, hda⟩ := mem_filter.mp hd
    rcases x.comparable c hc d hd with hcd | hdc
    · exact (hda (hcd ha)).elim
    · exact mem_filter.mpr ⟨hd, fun h => hb (hdc h)⟩
  exact (ssubset_iff_of_subset hs).2
    ⟨c, mem_filter.mpr ⟨hc, hb⟩, fun h => (mem_filter.mp h).2 ha⟩

theorem exists_flag_extension {n : ℕ} (x : CutChain n) :
    ∃ p : Equiv.Perm (Fin n), x.cuts ⊆ (flag p).cuts := by
  classical
  let key (a : Fin n) : ℕ ×ₗ Fin n := toLex ((preceding x a).card, a)
  have hk : Function.Injective key := fun a b h => congrArg (fun z => (ofLex z).2) h
  let g := Equiv.ofInjective key hk
  letI : Fintype (Set.range key) := Fintype.ofEquiv (Fin n) g
  let e := Fintype.orderIsoFinOfCardEq (Set.range key)
    ((Fintype.card_congr g).symm.trans (Fintype.card_fin n))
  let p := e.toEquiv.trans g.symm
  refine ⟨p, fun c hc => ?_⟩
  obtain ⟨hpos, hn⟩ := x.proper c hc
  apply (mem_flag p hn hpos).2
  have hpc := prefix_card p hn
  apply eq_of_subset_of_card_le ?_ hpc.ge
  intro a ha
  by_contra hna
  -- Find a missing element of the cut by equal cardinality.
  have hmissing : ¬ c ⊆ prefixSet p c.card := by
    intro hs
    exact hna ((eq_of_subset_of_card_le hs hpc.le) ▸ ha)
  obtain ⟨b, hb, hbp⟩ := not_subset.mp hmissing
  have hkey : key b < key a :=
    Prod.Lex.left _ _ (card_lt_card (preceding_ssubset hc hb hna))
  have hlt : g b < g a := hkey
  have horder := e.symm.strictMono hlt
  change (p.symm b).val < (p.symm a).val at horder
  rw [mem_prefix] at ha hbp
  omega

theorem isAtom_iff_flag {n : ℕ} (a : Face n) :
    IsAtom a ↔ ∃ p : Equiv.Perm (Fin n), a = atom p := by
  refine ⟨?_, fun ⟨p, hp⟩ => hp ▸ atom_isAtom p⟩
  cases a using WithBot.recBotCoe
  · exact fun ha => (ha.1 rfl).elim
  rename_i x
  intro ha
  obtain ⟨p, hp⟩ := exists_flag_extension x
  exact ⟨p, ((ha.le_iff.1 (WithBot.coe_le_coe.2 hp)).resolve_left WithBot.coe_ne_bot).symm⟩

def occupied {n : ℕ} (x : CutChain n) : Finset (Rank n) :=
  x.cuts.attach.image fun c => ⟨⟨c.1.card, (x.proper _ c.2).2⟩, (x.proper _ c.2).1⟩

def free {n : ℕ} (x : CutChain n) : Finset (Rank n) := univ \ occupied x

private theorem card_occupied {n : ℕ} (x : CutChain n) : (occupied x).card = x.cuts.card := by
  unfold occupied
  rw [card_image_of_injective, card_attach]
  intro a b hab
  exact Subtype.ext (x.eq_of_card_eq a.2 b.2 (congrArg (fun d : Rank n => d.1.val) hab))

theorem card_rank_type {n : ℕ} : Fintype.card (Rank n) = n - 1 := by
  rw [Fintype.card_subtype]
  by_cases hn : n = 0
  · subst n
    simp
  · let z : Fin n := ⟨0, by omega⟩
    have h : (univ.filter fun i : Fin n => 0 < i.val) = Ioi z := by
      ext i
      simp [Fin.lt_def, z]
    rw [h, Fin.card_Ioi]
    simp [z]

theorem card_free {n : ℕ} (hn : 1 ≤ n) (x : CutChain n) :
    ((free x).card : ℤ) = rank (x : Face n) := by
  have hs : (occupied x).card ≤ Fintype.card (Rank n) := (occupied x).card_le_univ
  unfold free
  rw [card_sdiff_of_subset (subset_univ _), card_univ, card_occupied, card_rank_type]
  rw [card_occupied, card_rank_type] at hs
  change ((n - 1 - x.cuts.card : ℕ) : ℤ) = (n : ℤ) - 1 - x.cuts.card
  omega

theorem prefix_mem_cuts_iff {n : ℕ} {x : CutChain n} {p : Equiv.Perm (Fin n)}
    (hp : x.cuts ⊆ (flag p).cuts) (d : Rank n) :
    prefixSet p d.1.val ∈ x.cuts ↔ d ∉ free x := by
  classical
  have hd : d ∉ free x ↔ d ∈ occupied x := by simp [free]
  rw [hd]
  change _ ↔ d ∈ x.cuts.attach.image _
  rw [mem_image]
  constructor
  · intro h
    refine ⟨⟨_, h⟩, mem_attach _ _, ?_⟩
    exact Subtype.ext (Fin.ext (prefix_card p d.1.isLt))
  · rintro ⟨c, _, hc⟩
    have he : c.1.card = d.1.val := congrArg (fun r : Rank n => r.1.val) hc
    have eq := (flag p).eq_of_card_eq (hp c.2) (prefix_mem_flag p d)
      (he.trans (prefix_card p d.1.isLt).symm)
    exact eq ▸ c.2

end Rossi
