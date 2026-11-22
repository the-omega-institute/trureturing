/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered partitions correspond to cut chains and adjacent merges. -/
import D5.S3.Combinatorics.Geometry.Permutohedra.FaceFlags

/-! Ordered partitions, cumulative cuts, and adjacent block merges. -/

namespace Rossi
open Finset D5.S3.Combinatorics.Graph.PrefixHamming

/-- The fibers of a surjective labeling are the nonempty blocks in their given order. -/
structure OrderedPartition (n : ℕ) where
  separators : ℕ
  blockOf : Fin n → Fin (separators + 1)
  onto : Function.Surjective blockOf

def OrderedPartition.cut {n : ℕ} (p : OrderedPartition n) (i : Fin p.separators) :
    Finset (Fin n) :=
  univ.filter fun a => (p.blockOf a).val ≤ i.val

private theorem OrderedPartition.mem_cut {n : ℕ} (p : OrderedPartition n)
    (i : Fin p.separators) (a : Fin n) :
    a ∈ p.cut i ↔ (p.blockOf a).val ≤ i.val := by simp [OrderedPartition.cut]

private theorem OrderedPartition.cut_strictMono {n : ℕ} (p : OrderedPartition n) :
    StrictMono p.cut := by
  intro i j hij
  have hj : i.val < j.val := hij
  have hsub : p.cut i ⊆ p.cut j := fun a ha =>
    (p.mem_cut j a).2 ((p.mem_cut i a).1 ha |>.trans hj.le)
  obtain ⟨a, ha⟩ := p.onto ⟨j.val, by omega⟩
  exact (ssubset_iff_of_subset hsub).2
    ⟨a, (p.mem_cut j a).2 (by rw [ha]),
      fun h => (Nat.not_le_of_lt hj) (by simpa only [ha] using (p.mem_cut i a).1 h)⟩

def OrderedPartition.toCuts {n : ℕ} (p : OrderedPartition n) : CutChain n where
  cuts := univ.image p.cut
  proper := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    constructor
    · obtain ⟨a, ha⟩ := p.onto 0
      exact card_pos.2 ⟨a, (p.mem_cut i a).2 (by simp [ha])⟩
    · obtain ⟨a, ha⟩ := p.onto ⟨p.separators, by omega⟩
      have hsub : p.cut i ⊂ univ := (ssubset_iff_of_subset (subset_univ _)).2
        ⟨a, mem_univ _, fun h => (Nat.not_le_of_lt i.isLt) (by
          simpa only [ha] using (p.mem_cut i a).1 h)⟩
      simpa using card_lt_card hsub
  comparable := by
    intro c hc d hd
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    obtain ⟨j, _, rfl⟩ := mem_image.mp hd
    exact (le_total i j).imp (fun h => p.cut_strictMono.monotone h) (fun h => p.cut_strictMono.monotone h)

private theorem OrderedPartition.card_toCuts {n : ℕ} (p : OrderedPartition n) :
    p.toCuts.cuts.card = p.separators := by
  change (univ.image p.cut).card = _
  rw [card_image_of_injective _ p.cut_strictMono.injective, card_univ, Fintype.card_fin]

theorem OrderedPartition.rank_toCuts {n : ℕ} (p : OrderedPartition n) :
    rank (p.toCuts : Face n) = (n : ℤ) - (p.separators + 1 : ℕ) := by
  change (n : ℤ) - 1 - p.toCuts.cuts.card = _
  rw [p.card_toCuts]
  omega

private noncomputable def sortedCuts {n : ℕ} (x : CutChain n) : Fin x.cuts.card ≃ ↥x.cuts :=
  let ord : LinearOrder ↥x.cuts :=
    LinearOrder.lift' (fun c : ↥x.cuts => c.1.card)
      (fun c d h => Subtype.ext (x.eq_of_card_eq c.2 d.2 h))
  (@Fintype.orderIsoFinOfCardEq ↥x.cuts ord _ _ (Fintype.card_coe x.cuts)).toEquiv

private theorem sortedCuts_card_strictMono {n : ℕ} (x : CutChain n) :
    StrictMono (fun i => ((sortedCuts x) i).1.card) := by
  intro i j h
  let ord : LinearOrder ↥x.cuts :=
    LinearOrder.lift' (fun c : ↥x.cuts => c.1.card)
      (fun c d h => Subtype.ext (x.eq_of_card_eq c.2 d.2 h))
  let e := @Fintype.orderIsoFinOfCardEq ↥x.cuts ord _ _ (Fintype.card_coe x.cuts)
  exact @OrderIso.strictMono _ _ (inferInstance : Preorder (Fin x.cuts.card)) ord.toPreorder e i j h

private theorem sortedCuts_subset {n : ℕ} (x : CutChain n) {i j : Fin x.cuts.card} (h : i ≤ j) :
    ((sortedCuts x) i).1 ⊆ ((sortedCuts x) j).1 := by
  rcases h.eq_or_lt with rfl | h
  · exact Subset.rfl
  · rcases x.comparable _ ((sortedCuts x) i).2 _ ((sortedCuts x) j).2 with hj | hj
    · exact hj
    · exact ((sortedCuts_card_strictMono x h).not_ge (card_le_card hj)).elim

private def blockIndex {n : ℕ} (x : CutChain n) (a : Fin n) : Fin (x.cuts.card + 1) :=
  ⟨(preceding x a).card, by
    have h : (preceding x a).card ≤ x.cuts.card :=
      card_le_card (filter_subset (fun c => a ∉ c) x.cuts)
    omega⟩

private theorem in_sortedCut_iff_blockIndex {n : ℕ} (x : CutChain n) (a : Fin n)
    (i : Fin x.cuts.card) :
    a ∈ ((sortedCuts x) i).1 ↔ (blockIndex x a).val ≤ i.val := by
  classical
  let e : Fin x.cuts.card ↪ Finset (Fin n) :=
    (sortedCuts x).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  constructor
  · intro ha
    have hs : preceding x a ⊆ (Iio i).map e := by
      intro c hc
      obtain ⟨hc, hna⟩ := mem_filter.mp hc
      let j := (sortedCuts x).symm ⟨c, hc⟩
      have he : e j = c := congrArg Subtype.val ((sortedCuts x).apply_symm_apply ⟨c, hc⟩)
      have hj : j < i := by
        by_contra! h
        exact hna (he ▸ sortedCuts_subset x h ha)
      exact mem_map.2 ⟨j, mem_Iio.2 hj, he⟩
    have h := card_le_card hs
    rwa [card_map, Fin.card_Iio] at h
  · intro hi
    by_contra ha
    have hs : (Iic i).map e ⊆ preceding x a := by
      intro c hc
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hc
      exact mem_filter.2 ⟨((sortedCuts x) j).2,
        fun h => ha (sortedCuts_subset x (mem_Iic.1 hj) h)⟩
    have h := card_le_card hs
    rw [card_map, Fin.card_Iic] at h
    exact (Nat.not_succ_le_self _ (h.trans hi))

private theorem blockIndex_surjective {n : ℕ} (hn : 1 ≤ n) (x : CutChain n) :
    Function.Surjective (blockIndex x) := by
  intro i
  by_cases hm : x.cuts.card = 0
  · refine ⟨⟨0, by omega⟩, Fin.ext ?_⟩
    have h0 := (blockIndex x ⟨0, by omega⟩).isLt
    have h1 := i.isLt
    omega
  by_cases hi : i.val = 0
  · let j : Fin x.cuts.card := ⟨0, by omega⟩
    have hn := (x.proper _ ((sortedCuts x) j).2).1
    obtain ⟨a, ha⟩ := card_pos.1 hn
    have he := (in_sortedCut_iff_blockIndex x a j).1 ha
    exact ⟨a, Fin.ext (by change _ ≤ 0 at he; omega)⟩
  let l : Fin x.cuts.card := ⟨i.val - 1, by have := i.isLt; omega⟩
  have hl : l.val + 1 = i.val := by dsimp [l]; omega
  by_cases he : i.val = x.cuts.card
  · let c := ((sortedCuts x) l).1
    have hc : c.card < (univ : Finset (Fin n)).card := by
      simpa using (x.proper _ ((sortedCuts x) l).2).2
    obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card hc
    have hbig := not_le.1 (fun h => ha ((in_sortedCut_iff_blockIndex x a l).2 h))
    have hlt := (blockIndex x a).isLt
    exact ⟨a, Fin.ext (by omega)⟩
  · let j : Fin x.cuts.card := ⟨i.val, by have := i.isLt; omega⟩
    have hlj : l < j := by change l.val < i.val; omega
    obtain ⟨a, haj, hal⟩ := exists_mem_notMem_of_card_lt_card (sortedCuts_card_strictMono x hlj)
    have hsmall := (in_sortedCut_iff_blockIndex x a j).1 haj
    have hbig := not_le.1 (fun h => hal ((in_sortedCut_iff_blockIndex x a l).2 h))
    exact ⟨a, Fin.ext (by change _ ≤ i.val at hsmall; omega)⟩

noncomputable def CutChain.toPartition {n : ℕ} (hn : 1 ≤ n) (x : CutChain n) :
    OrderedPartition n :=
  ⟨x.cuts.card, blockIndex x, blockIndex_surjective hn x⟩

private theorem toPartition_toCuts {n : ℕ} (hn : 1 ≤ n) (x : CutChain n) :
    (x.toPartition hn).toCuts = x := by
  apply CutChain.ext_cuts
  change univ.image (x.toPartition hn).cut = x.cuts
  have eq (i : Fin x.cuts.card) : (x.toPartition hn).cut i = ((sortedCuts x) i).1 := by
    ext a
    exact ((x.toPartition hn).mem_cut i a).trans (in_sortedCut_iff_blockIndex x a i).symm
  ext c
  rw [mem_image]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact (eq i).symm ▸ ((sortedCuts x) i).2
  · intro hc
    obtain ⟨i, hi⟩ := (sortedCuts x).surjective ⟨c, hc⟩
    exact ⟨i, mem_univ _, (eq i).trans (congrArg Subtype.val hi)⟩

private theorem OrderedPartition.toCuts_injective {n : ℕ} :
    Function.Injective (OrderedPartition.toCuts (n := n)) := by
  rintro ⟨m, f, hf⟩ ⟨m', g, hg⟩ he
  let u : OrderedPartition n := ⟨m, f, hf⟩
  let v : OrderedPartition n := ⟨m', g, hg⟩
  have hm : m = m' := u.card_toCuts.symm.trans
    ((congrArg (fun x : CutChain n => x.cuts.card) he).trans v.card_toCuts)
  subst m'
  let v : OrderedPartition n := ⟨m, g, hg⟩
  change u.toCuts = v.toCuts at he
  have hcut : u.cut = v.cut := by
    let F (i : Fin m) := (u.cut i).card
    let G (i : Fin m) := (v.cut i).card
    have hF : StrictMono F := fun _ _ h => card_lt_card (u.cut_strictMono h)
    have hG : StrictMono G := fun _ _ h => card_lt_card (v.cut_strictMono h)
    have hEq : Set.range F = Set.range G := by
      have h := congrArg (fun x : CutChain n => x.cuts.image Finset.card) he
      change (univ.image u.cut).image Finset.card = (univ.image v.cut).image Finset.card at h
      rw [image_image, image_image] at h
      simpa [F, G] using congrArg (fun s : Finset ℕ => (s : Set ℕ)) h
    have hfg := (hF.range_inj_of_wellFoundedLT hG).1 hEq
    funext i
    apply u.toCuts.eq_of_card_eq
    · exact mem_image_of_mem _ (mem_univ i)
    · rw [he]
      exact mem_image_of_mem _ (mem_univ i)
    · exact congrFun hfg i
  have hfg : f = g := by
    funext a
    apply Fin.ext
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · let i : Fin m := ⟨(f a).val, by have := (g a).isLt; omega⟩
      have hu : a ∈ u.cut i := (u.mem_cut i a).2 (Nat.le_refl _)
      rw [hcut] at hu
      exact (Nat.not_le_of_lt h) ((v.mem_cut i a).1 hu)
    · let i : Fin m := ⟨(g a).val, by have := (f a).isLt; omega⟩
      have hv : a ∈ v.cut i := (v.mem_cut i a).2 (Nat.le_refl _)
      rw [← hcut] at hv
      exact (Nat.not_le_of_lt h) ((u.mem_cut i a).1 hv)
  subst g
  rfl

noncomputable def orderedPartitionsEquiv {n : ℕ} (hn : 1 ≤ n) :
    OrderedPartition n ≃ CutChain n where
  toFun := OrderedPartition.toCuts
  invFun := CutChain.toPartition hn
  right_inv := toPartition_toCuts hn
  left_inv p := OrderedPartition.toCuts_injective (toPartition_toCuts hn p.toCuts)

def MergesAdjacent {n : ℕ} (p q : OrderedPartition n) : Prop :=
  ∃ f : Fin (p.separators + 1) → Fin (q.separators + 1),
    Monotone f ∧ Function.Surjective f ∧ ∀ a, f (p.blockOf a) = q.blockOf a

theorem mergesAdjacent_iff {n : ℕ} (p q : OrderedPartition n) :
    MergesAdjacent p q ↔ p.toCuts ≤ q.toCuts := by
  classical
  change MergesAdjacent p q ↔ q.toCuts.cuts ⊆ p.toCuts.cuts
  constructor
  · rintro ⟨f, hmono, hsurj, hmap⟩ c hc
    obtain ⟨j, _, rfl⟩ := mem_image.mp hc
    let s : Finset (Fin (p.separators + 1)) := univ.filter fun a => (f a).val ≤ j.val
    obtain ⟨z, hz⟩ := hsurj 0
    have hs : s.Nonempty := ⟨z, mem_filter.2 ⟨mem_univ _, by simp [hz]⟩⟩
    let b := s.max' hs
    have hb := mem_filter.mp (max'_mem s hs : b ∈ s)
    obtain ⟨u, hu⟩ := hsurj ⟨q.separators, by omega⟩
    have hub : b < u := by
      by_contra! h
      have hfu : f u ≤ f b := hmono h
      have he : (f u).val ≤ j.val := (show (f u).val ≤ (f b).val from hfu).trans hb.2
      rw [hu] at he
      exact (Nat.not_le_of_lt j.isLt) he
    have hbl : b.val < p.separators := by have := u.isLt; change b.val < u.val at hub; omega
    refine mem_image.2 ⟨⟨b.val, hbl⟩, mem_univ _, ?_⟩
    ext a
    rw [p.mem_cut, q.mem_cut, ← hmap a]
    change (p.blockOf a).val ≤ b.val ↔ (f (p.blockOf a)).val ≤ j.val
    exact ⟨fun h => (show (f (p.blockOf a)).val ≤ (f b).val from hmono h).trans hb.2,
      fun h => le_max' s (p.blockOf a) (mem_filter.2 ⟨mem_univ _, h⟩)⟩
  · intro hcut
    have hmono {a b : Fin n} (hab : p.blockOf a ≤ p.blockOf b) :
        q.blockOf a ≤ q.blockOf b := by
      by_contra! rev
      let j : Fin q.separators := ⟨(q.blockOf b).val, by
        have := (q.blockOf a).isLt
        change (q.blockOf b).val < (q.blockOf a).val at rev
        omega⟩
      obtain ⟨i, _, he⟩ := mem_image.mp (hcut (mem_image_of_mem q.cut (mem_univ j)))
      have hba : b ∈ p.cut i := he.symm ▸ (q.mem_cut j b).2 (Nat.le_refl _)
      have ha : a ∈ p.cut i := (p.mem_cut i a).2
        ((show (p.blockOf a).val ≤ (p.blockOf b).val from hab).trans ((p.mem_cut i b).1 hba))
      exact (not_le_of_gt rev) ((q.mem_cut j a).1 (he ▸ ha))
    let representative (i : Fin (p.separators + 1)) := (p.onto i).choose
    have hp (i : Fin (p.separators + 1)) : p.blockOf (representative i) = i :=
      (p.onto i).choose_spec
    let f (i : Fin (p.separators + 1)) := q.blockOf (representative i)
    have hmap (a : Fin n) : f (p.blockOf a) = q.blockOf a :=
      le_antisymm (hmono (le_of_eq (hp _))) (hmono (le_of_eq (hp _).symm))
    refine ⟨f, fun i j hij => hmono (by rw [hp, hp]; exact hij), ?_, hmap⟩
    intro j
    obtain ⟨a, rfl⟩ := q.onto j
    exact ⟨p.blockOf a, hmap a⟩

private theorem atom_injective {n : ℕ} : Function.Injective (atom (n := n)) := by
  intro p q h
  have hf : flag p = flag q := WithBot.coe_injective h
  suffices p.symm = q.symm by simpa using congrArg Equiv.symm this
  apply Equiv.ext
  intro a
  apply Fin.ext
  by_contra hr
  have noLt (p q : Equiv.Perm (Fin n)) (hf : flag p = flag q)
      (h : (p.symm a).val < (q.symm a).val) : False := by
    let d : Rank n := ⟨q.symm a, by omega⟩
    have hc : prefixSet p d.1.val ∈ (flag q).cuts := hf ▸ prefix_mem_flag p d
    have hcard := prefix_card p d.1.isLt
    have heq := (mem_flag q (by rw [hcard]; exact d.1.isLt)
      (by rw [hcard]; exact d.2)).1 hc
    rw [hcard] at heq
    have ha : a ∈ prefixSet p d.1.val := (mem_prefix p a).2 h
    have hj := (mem_prefix q a).1 (heq.symm ▸ ha)
    exact (Nat.lt_irrefl _ hj)
  exact (lt_or_gt_of_ne hr).elim (noLt p q hf) (noLt q p hf.symm)

noncomputable def permutationAtomsEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ {a : Face n // IsAtom a} :=
  Equiv.ofBijective (fun p => ⟨atom p, atom_isAtom p⟩)
    ⟨fun _ _ h => atom_injective (congrArg Subtype.val h), fun ⟨a, ha⟩ => by
      obtain ⟨p, hp⟩ := (isAtom_iff_flag a).1 ha
      exact ⟨p, Subtype.ext hp.symm⟩⟩

end Rossi
