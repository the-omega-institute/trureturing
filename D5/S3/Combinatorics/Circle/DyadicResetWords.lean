/- GID: D5/S3/Combinatorics/Circle/DyadicResetWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/DyadicResetWords
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: A physical dyadic allocation assembles exact reset packets and all their prefixes. -/
module
public import D5.S3.Combinatorics.Circle.DyadicResetBlocks
public import D5.S3.Combinatorics.Transportation.DyadicAllocation
import all D5.S3.Combinatorics.Circle.ThreeBitSource
import Mathlib.Data.List.OfFn

/-! Bin labels are concatenated with their actual reset occurrences. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.DyadicResetWords
open List SourceWidth MixedSuffixEnergy DyadicResetBlocks
open D5.S3.Combinatorics.Transportation.DyadicAllocation
open scoped BigOperators

/-- The same allocated physical coins and the same supplied reset occurrences
form a legal word. Every bin is used once, including the zero-capacity tail. -/
theorem word_of_allocation {α : Type*} [DecidableEq α]
    (f : α → ℤ) (S : Finset α) (e : α → ℕ) (Z : List α) (M h : ℕ)
    (hcap : h ≤ M) (hpos : ∀ a ∈ S, f a = (2 : ℤ) ^ e a)
    (hneg : ∀ a ∈ Z, f a = -(M : ℤ))
    (hal : Allocation S e (fun i : Fin Z.length ⊕ Unit =>
      Sum.elim (fun _ => M) (fun _ => h) i)) :
    ∃ V : List α, V.Perm (S.toList ++ Z) ∧ InStrip f M 0 V := by
  classical
  obtain ⟨K, hKS, hKD, hKC, hKb⟩ := hal
  let ids : List (Fin Z.length ⊕ Unit) :=
    (List.finRange Z.length).map Sum.inl ++ [Sum.inr ()]
  have hids : ∀ i, i ∈ ids := by
    intro i
    cases i with
    | inl i => simp [ids]
    | inr i => cases i; simp [ids]
  have hidsN : ids.Nodup := by
    apply List.Nodup.append
    · exact (List.nodup_finRange Z.length).map Sum.inl_injective
    · simp
    · apply List.disjoint_left.mpr
      intro i hi hj
      simp only [List.mem_singleton] at hj
      subst i
      simp at hi
  let F := ids.flatMap (fun i => (K i).toList)
  have hFN : F.Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun i _ => Finset.nodup_toList _, ?_⟩
    apply hidsN.pairwise_of_forall_ne
    intro i _ j _ hij
    apply List.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp (hKD i j hij)
      (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb)
  have hFP : F.Perm S.toList := by
    apply (List.perm_ext_iff_of_nodup hFN (Finset.nodup_toList S)).mpr
    intro a
    simp only [F, List.mem_flatMap, Finset.mem_toList]
    constructor
    · rintro ⟨i, _, ha⟩
      exact hKS i ha
    · intro ha
      obtain ⟨i, hi⟩ := hKC a ha
      exact ⟨i, hids i, hi⟩
  have hmass (i : Fin Z.length ⊕ Unit) :
      mass f (K i).toList =
        (Sum.elim (fun _ : Fin Z.length => M) (fun _ : Unit => h) i : ℕ) := by
    calc
      mass f (K i).toList = ∑ a ∈ K i, f a := by simp [mass]
      _ = ∑ a ∈ K i, (2 : ℤ) ^ e a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hpos a (hKS i ha)
      _ = ((∑ a ∈ K i, (2 : ℕ) ^ e a) : ℕ) := by push_cast; rfl
      _ = _ := by rw [hKb i]
  have hpositive (i : Fin Z.length ⊕ Unit) : Positive f (K i).toList := by
    intro a ha
    rw [hpos a (hKS i (Finset.mem_toList.mp ha))]
    positivity
  let P : List (List α × α) := List.ofFn
    (fun i : Fin Z.length => ((K (Sum.inl i)).toList, Z.get i))
  let T := (K (Sum.inr ())).toList
  have hP : Complete f M P := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨hpositive (Sum.inl i), hmass (Sum.inl i), hneg _ (List.get_mem Z i)⟩
  have hsP := complete_strip (by positivity : (0 : ℤ) ≤ M) hP
  have hsT : InStrip f M 0 T := ThreeBitSource.positive_block_strip
    (fun a ha => le_of_lt (hpositive (Sum.inr ()) a ha)) (le_refl 0)
    (by have ht := hmass (Sum.inr ()); dsimp [T]; simpa [mass] using ht.le.trans (by exact_mod_cast hcap))
  have hzero := complete_mass hP
  have hZ : P.map Prod.snd = Z := by simpa only [P, List.map_ofFn, Function.comp_def] using List.ofFn_get Z
  have hF : P.flatMap Prod.fst ++ T = F := by
    simp [P, T, F, ids, List.flatMap_append, List.flatMap_map,
      List.finRange, List.flatMap, List.map_ofFn, Function.comp_def]
  have hpack : (packets P).Perm (P.flatMap Prod.fst ++ P.map Prod.snd) := by
    simpa [packets, ← List.map_eq_flatMap] using
      (List.flatMap_append_perm P Prod.fst (fun p => [p.2])).symm
  refine ⟨packets P ++ T, ?_, inStrip_append hsP (show InStrip f M (0 + mass f (packets P)) T from by simpa only [hzero, add_zero] using hsT)⟩
  calc
    packets P ++ T ~ (P.flatMap Prod.fst ++ P.map Prod.snd) ++ T := hpack.append_right T
    _ ~ (P.flatMap Prod.fst ++ T) ++ P.map Prod.snd := by
      simpa only [List.append_assoc] using
        (List.Perm.refl (P.flatMap Prod.fst)).append (List.perm_append_comm :
          (P.map Prod.snd ++ T).Perm (T ++ P.map Prod.snd))
    _ ~ S.toList ++ Z := by rw [hF, hZ]; exact hFP.append_right Z

/-- The positive blocks of an actual legal word give an allocation of precisely
its positive labels. No allocation is assumed in the word decomposition. -/
theorem allocation_of_blocks {α : Type*} [DecidableEq α]
    (f : α → ℤ) (e : α → ℕ) (P : List (List α × α)) (T : List α) (M h : ℕ)
    (hW : (packets P ++ T).Nodup) (hP : Complete f M P)
    (hT : Positive f T) (htmass : mass f T = h)
    (hval : ∀ a ∈ P.flatMap Prod.fst ++ T, f a = (2 : ℤ) ^ e a) :
    Allocation (P.flatMap Prod.fst ++ T).toFinset e
      (fun i : Fin P.length ⊕ Unit => Sum.elim (fun _ => M) (fun _ => h) i) := by
  classical
  have hpack : (packets P).Perm (P.flatMap Prod.fst ++ P.map Prod.snd) := by
    simpa [packets, ← List.map_eq_flatMap] using
      (List.flatMap_append_perm P Prod.fst (fun p => [p.2])).symm
  have hperm : (packets P ++ T).Perm ((P.flatMap Prod.fst ++ T) ++ P.map Prod.snd) := by
    exact (hpack.append_right T).trans (by
      simpa only [List.append_assoc] using (List.Perm.refl (P.flatMap Prod.fst)).append
        (List.perm_append_comm : (P.map Prod.snd ++ T).Perm (T ++ P.map Prod.snd)))
  have hN : (P.flatMap Prod.fst ++ T).Nodup :=
    (List.nodup_append.mp (hperm.nodup_iff.mp hW)).1
  obtain ⟨hflatN, hTN, hflatT⟩ := List.nodup_append'.mp hN
  have hmap : List.ofFn (fun i : Fin P.length => (P.get i).1) = P.map Prod.fst := by
    simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map Prod.fst) (List.ofFn_get P)
  have hFN : (List.ofFn (fun i : Fin P.length => (P.get i).1)).flatten.Nodup := by
    rw [hmap]
    simpa only [List.flatMap] using hflatN
  obtain ⟨hbinN, hpair⟩ := List.nodup_flatten.mp hFN
  have hpair' := List.pairwise_ofFn.mp hpair
  let L : Fin P.length ⊕ Unit → List α :=
    Sum.elim (fun i => (P.get i).1) (fun _ => T)
  have hLS : ∀ i, ∀ a ∈ L i, a ∈ P.flatMap Prod.fst ++ T := by
    intro i a ha
    cases i with
    | inl i =>
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨P.get i, List.get_mem P i, ha⟩
    | inr i => exact List.mem_append_right _ ha
  have hLN : ∀ i, (L i).Nodup := by
    intro i
    cases i with
    | inl i => exact hbinN _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    | inr i => exact hTN
  have hLD : ∀ i j, i ≠ j → List.Disjoint (L i) (L j) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hne : i ≠ j := fun he => hij (congrArg Sum.inl he)
        rcases lt_or_gt_of_ne hne with h | h
        · exact hpair' h
        · exact (hpair' h).symm
      | inr j =>
        apply List.disjoint_left.mpr
        intro a ha hb
        exact List.disjoint_left.mp hflatT
          (List.mem_flatMap.mpr ⟨P.get i, List.get_mem P i, ha⟩) hb
    | inr i =>
      cases j with
      | inl j =>
        apply List.disjoint_left.mpr
        intro a ha hb
        exact List.disjoint_left.mp hflatT
          (List.mem_flatMap.mpr ⟨P.get j, List.get_mem P j, hb⟩) ha
      | inr j => exact False.elim (hij (congrArg Sum.inr (Subsingleton.elim i j)))
  refine ⟨fun i => (L i).toFinset, ?_, ?_, ?_, ?_⟩
  · intro i a ha
    exact List.mem_toFinset.mpr (hLS i a (List.mem_toFinset.mp ha))
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact List.disjoint_left.mp (hLD i j hij)
      (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
  · intro a ha
    rcases List.mem_append.mp (List.mem_toFinset.mp ha) with ha | ha
    · obtain ⟨p, hp, hap⟩ := List.mem_flatMap.mp ha
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
      refine ⟨Sum.inl i, List.mem_toFinset.mpr ?_⟩
      change a ∈ (P.get i).1
      rw [hi]
      exact hap
    · exact ⟨Sum.inr (), List.mem_toFinset.mpr ha⟩
  · intro i
    have hm : mass f (L i) =
        (Sum.elim (fun _ : Fin P.length => M) (fun _ : Unit => h) i : ℕ) := by
      cases i with
      | inl i => exact (hP _ (List.get_mem P i)).2.1
      | inr i => exact htmass
    have hs : (∑ a ∈ (L i).toFinset, (2 : ℤ) ^ e a) = mass f (L i) := by
      unfold mass
      rw [← List.sum_toFinset f (hLN i)]
      apply Finset.sum_congr rfl
      intro a ha
      exact (hval a (hLS i a (List.mem_toFinset.mp ha))).symm
    have hs' : ((∑ a ∈ (L i).toFinset, (2 : ℕ) ^ e a) : ℤ) =
        (Sum.elim (fun _ : Fin P.length => M) (fun _ : Unit => h) i : ℕ) := by
      push_cast
      exact hs.trans hm
    exact_mod_cast hs'


/-- Replacing physical coins in one bin by a fresh coin of their exact total
preserves all capacities and all other bins. -/
theorem replace_bin {α β : Type*} [DecidableEq α] [Fintype β]
    (S : Finset α) (e : α → ℕ) (cap : β → ℕ)
    (K : β → Finset α) (hKS : ∀ i, K i ⊆ S)
    (hKD : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hKC : ∀ a ∈ S, ∃ i, a ∈ K i)
    (hKb : ∀ i, ∑ a ∈ K i, 2 ^ e a = cap i)
    (i : β) (a : α) (R : Finset α) (ha : a ∉ S)
    (hR : R ⊆ K i) (hRm : (∑ x ∈ R, 2 ^ e x) = 2 ^ e a) :
    Allocation (insert a (S \ R)) e cap := by
  classical
  let K' : β → Finset α := fun j => if j = i then insert a (K j \ R) else K j
  have hnot (j : β) : a ∉ K j := fun h => ha (hKS j h)
  have hnotR (j : β) (hji : j ≠ i) : Disjoint (K j) R :=
    (hKD j i hji).mono_right hR
  refine ⟨K', ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases hj : j = i
    · simp only [K', if_pos hj, Finset.mem_insert, Finset.mem_sdiff] at hx
      rcases hx with rfl | ⟨hx, hn⟩
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hKS j hx, hn⟩)
    · have hx' : x ∈ K j := by simpa [K', hj] using hx
      exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
        ⟨hKS j hx', fun hr => Finset.disjoint_left.mp (hnotR j hj) hx' hr⟩)
  · intro j l hjl
    apply Finset.disjoint_left.mpr
    intro x hx hy
    by_cases hj : j = i <;> by_cases hl : l = i
    · exact hjl (hj.trans hl.symm)
    · simp only [K', if_pos hj, Finset.mem_insert, Finset.mem_sdiff] at hx
      have hy' : x ∈ K l := by simpa [K', hl] using hy
      rcases hx with rfl | ⟨hx, _⟩
      · exact hnot l hy'
      · exact Finset.disjoint_left.mp (hKD j l hjl) hx hy'
    · have hx' : x ∈ K j := by simpa [K', hj] using hx
      simp only [K', if_pos hl, Finset.mem_insert, Finset.mem_sdiff] at hy
      rcases hy with rfl | ⟨hy, _⟩
      · exact hnot j hx'
      · exact Finset.disjoint_left.mp (hKD j l hjl) hx' hy
    · exact Finset.disjoint_left.mp (hKD j l hjl)
        (by simpa [K', hj] using hx) (by simpa [K', hl] using hy)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨i, by simp [K']⟩
    · obtain ⟨j, hj⟩ := hKC x (Finset.mem_sdiff.mp hx).1
      refine ⟨j, ?_⟩
      by_cases hji : j = i
      · simp only [K', if_pos hji, Finset.mem_insert, Finset.mem_sdiff]
        exact Or.inr ⟨hj, (Finset.mem_sdiff.mp hx).2⟩
      · simpa [K', hji] using hj
  · intro j
    by_cases hj : j = i
    · subst j
      have hz := Finset.sum_sdiff hR (f := fun x => (2 : ℕ) ^ e x)
      have hn : a ∉ K i \ R := fun h => hnot i (Finset.mem_sdiff.mp h).1
      simp only [K', if_pos rfl, Finset.sum_insert hn]
      rw [hRm] at hz
      have hb := hKb i
      omega
    · simpa [K', hj] using hKb j

/-- All-prefix reset legality supplies both the exact positive allocation and
the physical reset list used by its realization. -/
theorem allocation_of_strip {α : Type*} [DecidableEq α]
    (f : α → ℤ) (e : α → ℕ) (M : ℕ) (W : List α)
    (steps : ∀ a, 0 < f a ∨ f a = -(M : ℤ))
    (powers : ∀ a, 0 < f a → f a = (2 : ℤ) ^ e a)
    (hW : W.Nodup) (hs : InStrip f M 0 W) :
    ∃ (S : Finset α) (Z : List α) (h : ℕ),
      h ≤ M ∧ W.Perm (S.toList ++ Z) ∧
      (∀ a ∈ S, 0 < f a) ∧ (∀ a ∈ Z, f a = -(M : ℤ)) ∧
      mass f W = h ∧
      Allocation S e (fun i : Fin Z.length ⊕ Unit =>
        Sum.elim (fun _ => M) (fun _ => h) i) := by
  classical
  obtain ⟨P, T, heq, hP, hT, ht0, htM⟩ := reset_decomposition f M steps W hs
  let L := P.flatMap Prod.fst ++ T
  let Z := P.map Prod.snd
  have hp : W.Perm (L ++ Z) := by
    rw [heq]
    have hpack : (packets P).Perm (P.flatMap Prod.fst ++ Z) := by
      simpa [packets, Z, ← List.map_eq_flatMap] using
        (List.flatMap_append_perm P Prod.fst (fun p => [p.2])).symm
    exact (hpack.append_right T).trans (by
      simpa only [L, List.append_assoc] using
        (List.Perm.refl (P.flatMap Prod.fst)).append
          (List.perm_append_comm : (Z ++ T).Perm (T ++ Z)))
  have hLN := (List.nodup_append.mp (hp.nodup_iff.mp hW)).1
  have hpos : Positive f L := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
      exact (hP p hp).1 a ha
    · exact hT a ha
  have hZ : ∀ a ∈ Z, f a = -(M : ℤ) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact (hP p hp).2.2
  have hmass : mass f W = mass f T := by
    rw [heq]
    simp only [mass, List.map_append, List.sum_append]
    change mass f (packets P) + mass f T = _
    rw [complete_mass hP, zero_add]
    rfl
  have htcast : (mass f T).toNat = mass f T := Int.toNat_of_nonneg ht0
  refine ⟨L.toFinset, Z, (mass f T).toNat, by omega, ?_, ?_, hZ,
    hmass.trans htcast.symm, ?_⟩
  · exact hp.trans ((List.toFinset_toList hLN).symm.append_right Z)
  · intro a ha; exact hpos a (List.mem_toFinset.mp ha)
  · have hal := allocation_of_blocks f e P T M (mass f T).toNat
      (heq ▸ hW) hP hT htcast.symm (fun a ha => powers a (hpos a ha))
    have hlen : P.length = Z.length := by simp [Z]
    exact hlen ▸ hal


/-- An allocated bin below twice the top denomination contains at most one
physical top coin; summing those bin counts counts precisely the original
physical top inventory. -/
theorem top_occupancy {α β : Type*} [DecidableEq α] [Fintype β]
    (S : Finset α) (e : α → ℕ) (b : ℕ) (cap : β → ℕ)
    (K : β → Finset α) (hKS : ∀ i, K i ⊆ S)
    (hKD : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hKC : ∀ a ∈ S, ∃ i, a ∈ K i)
    (hKb : ∀ i, ∑ a ∈ K i, 2 ^ e a = cap i)
    (hcap : ∀ i, cap i < 2 * 2 ^ b) :
    (S.filter (fun a => e a = b)).card =
      ∑ i, ((K i).filter (fun a => e a = b)).card ∧
    ∀ i, ((K i).filter (fun a => e a = b)).card ≤ 1 := by
  classical
  let L : β → Finset α := fun i => (K i).filter (fun a => e a = b)
  have hLD : Set.PairwiseDisjoint (↑(Finset.univ : Finset β)) L := by
    intro i _ j _ hij
    exact (hKD i j hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hL : Finset.univ.biUnion L = S.filter (fun a => e a = b) := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, L, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, he⟩; exact ⟨hKS i hi, he⟩
    · rintro ⟨ha, he⟩; obtain ⟨i, hi⟩ := hKC a ha; exact ⟨i, hi, he⟩
  constructor
  · rw [← hL]
    exact Finset.card_biUnion hLD
  · intro i
    have hsum : (∑ a ∈ L i, (2 : ℕ) ^ e a) = (L i).card * 2 ^ b := by
      calc
        _ = ∑ _a ∈ L i, (2 : ℕ) ^ b := Finset.sum_congr rfl (by
          intro a ha; rw [(Finset.mem_filter.mp ha).2])
        _ = _ := by simp
    have hle := Finset.sum_le_sum_of_subset (f := fun a => (2 : ℕ) ^ e a)
      (Finset.filter_subset (fun a => e a = b) (K i))
    rw [hKb, hsum] at hle
    have hpow : 0 < (2 : ℕ) ^ b := by positivity
    have hi := hcap i
    change (L i).card ≤ 1
    nlinarith

/-- A missing top coin in any of n complete bins and one tail bounds the
whole physical top inventory by n. -/
theorem missing_top_bound (n : ℕ) (c : Fin n ⊕ Unit → ℕ)
    (hc : ∀ i, c i ≤ 1) (i : Fin n ⊕ Unit) (hi : c i = 0) :
    (∑ j, c j) ≤ n := by
  classical
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin n ⊕ Unit)) c (Finset.mem_univ i)
  have hle : (∑ j ∈ Finset.univ.erase i, c j) ≤ (Finset.univ.erase i).card := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, (1 : ℕ) := Finset.sum_le_sum (fun j _ => hc j)
      _ = _ := by simp
  have hcard : (Finset.univ.erase i).card = n := by simp
  omega

end D5.S3.Combinatorics.Circle.DyadicResetWords
