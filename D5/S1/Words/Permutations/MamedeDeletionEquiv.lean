/- GID: D5/S1/Words/Permutations/MamedeDeletionEquiv
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeDeletionEquiv
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Deletion is a length-dropping equivalence of first-orientation singleton fibers. -/

import D5.S1.Words.Permutations.MamedeConditionalConverse
import D5.S1.Words.Permutations.MamedeShapeExtraction

namespace D5.S1.Words.Permutations.MamedeDeletionEquiv

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeSourceAction
open D5.S1.Words.Permutations.MamedeConditionalConverse
open D5.S1.Words.Permutations.MamedeShapeExtraction

/-- Under the exact first-orientation source hypotheses, deleting the excursion
gives an equivalence of actual singleton-word fibers with a fixed length drop. -/
theorem source_deletion_equiv (n m M i j : Nat)
    (σ : Equiv.Perm (Fin (n + 1)))
    (hs : exactSourceHypotheses n m M i j σ) :
    ∃ e : {a : List Nat // singletonWord n σ a} ≃
        {b : List Nat // singletonWord n
          (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b},
      ∀ (a : {a : List Nat // singletonWord n σ a}) (p q : List Nat),
        sourceShape m M i j a.val p q →
          (e a).val = imageWord i j p q ∧
          a.val.length = (e a).val.length + (deletedExcursion m M i).length ∧
          0 < (deletedExcursion m M i).length := by
  rcases hs with ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
  have hs : exactSourceHypotheses n m M i j σ :=
    ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
  have hshape_all (a : List Nat) (ha : singletonWord n σ a) :
      ∃ p q, sourceShape m M i j a p q := by
    apply source_shape_for_every_singleton n m M i j σ a
    · exact ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hfixed⟩
    · exact ha
  have hlength (a p q : List Nat) (hshape : sourceShape m M i j a p q) :
      a.length = (imageWord i j p q).length +
        (deletedExcursion m M i).length := by
    rw [hshape.1]
    simp only [fullExcursion, deletedExcursion, imageWord, descending, ascending,
      List.length_append, List.length_map, List.length_range]
    omega
  have hpos : 0 < (deletedExcursion m M i).length := by
    simp only [deletedExcursion, List.length_append]
    have h : 0 < (ascending (m + 1) M).length := by simp [ascending]
    omega
  let adjacentLetters (a b : Nat) : Prop := a + 1 = b ∨ b + 1 = a
  have consecutive_iff_chain (w : List Nat) :
      consecutive w ↔ w.IsChain adjacentLetters := by
    induction w using List.twoStepInduction with
    | nil => simp [consecutive]
    | singleton a => simp [consecutive]
    | cons_cons a b rest _ ih =>
      simpa [consecutive, adjacentLetters, List.isChain_cons_cons] using
        and_congr Iff.rfl (ih b)
  have descending_chain (lo hi : Nat) (h : lo ≤ hi) :
      (descending hi lo).IsChain adjacentLetters := by
    rw [descending, List.isChain_map, List.isChain_range]
    intro r hr
    right
    dsimp [adjacentLetters]
    omega
  have descending_head (lo hi : Nat) (h : lo ≤ hi) :
      (descending hi lo).head? = some hi := by
    simp [descending, List.head?_range]
  have descending_last (lo hi : Nat) (h : lo ≤ hi) :
      (descending hi lo).getLast? = some lo := by
    simp [descending, List.getLast?_range]
    omega
  have hconsecutive (a p q : List Nat)
      (ha : consecutive a) (hshape : sourceShape m M i j a p q) :
      consecutive (imageWord i j p q) := by
    rw [consecutive_iff_chain] at ha ⊢
    rw [hshape.1] at ha
    have hhead : (fullExcursion m M i j).head? =
        (descending j i).head? := by
      have hn : descending j m ≠ [] := by
        intro he
        have hh := descending_head m j (by omega)
        rw [he] at hh
        simp at hh
      rw [fullExcursion, List.append_assoc,
        List.head?_append_of_ne_nil _ hn]
      rw [descending_head m j (by omega), descending_head i j hij]
    have hlast : (fullExcursion m M i j).getLast? =
        (descending j i).getLast? := by
      have hn : descending (M - 1) i ≠ [] := by
        intro he
        have hh := descending_head i (M - 1) (by omega)
        rw [he] at hh
        simp at hh
      simp [fullExcursion, List.getLast?_append_of_ne_nil _ hn,
        descending_last i (M - 1) (by omega), descending_last i j hij]
    have hFne : fullExcursion m M i j ≠ [] := by
      intro he
      rw [he, descending_head i j hij] at hhead
      simp at hhead
    have hDne : descending j i ≠ [] := by
      intro he
      have hh := descending_head i j hij
      rw [he] at hh
      simp at hh
    have hlast_outer : (p ++ fullExcursion m M i j).getLast? =
        (p ++ descending j i).getLast? := by
      rw [List.getLast?_append_of_ne_nil p hFne,
        List.getLast?_append_of_ne_nil p hDne]
      exact hlast
    simp only [imageWord, List.isChain_append] at ha ⊢
    rcases ha with ⟨⟨hp, _hfull, hleft⟩, hq, hright⟩
    refine ⟨⟨hp, descending_chain i j hij, ?_⟩, hq, ?_⟩
    · simpa only [← hhead] using hleft
    · simpa only [← hlast_outer] using hright
  have hvalid_deleted : validWord n (deletedExcursion m M i) := by
    intro k hk
    simp only [deletedExcursion, List.mem_append] at hk
    rcases hk with (hk | hk) | hk
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      have hr := List.mem_range.mp hr
      constructor <;> dsimp [descending] at * <;> omega
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      have hr := List.mem_range.mp hr
      constructor <;> dsimp [ascending] at * <;> omega
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
      have hr := List.mem_range.mp hr
      constructor <;> dsimp [descending] at * <;> omega
  have hforward (a p q : List Nat)
      (ha : singletonWord n σ a) (hshape : sourceShape m M i j a p q) :
      singletonWord n
        (σ * (wordProduct n (deletedExcursion m M i))⁻¹)
        (imageWord i j p q) := by
    have hprod : wordProduct n (imageWord i j p q) =
        σ * (wordProduct n (deletedExcursion m M i))⁻¹ := by
      have hf := source_full_product n m M i j p q hm hmi hij hjM hMn hshape.2.2
      rw [← hshape.1, ha.2.2] at hf
      calc
        wordProduct n (imageWord i j p q) =
            (wordProduct n (imageWord i j p q) *
              wordProduct n (deletedExcursion m M i)) *
              (wordProduct n (deletedExcursion m M i))⁻¹ := by group
        _ = σ * (wordProduct n (deletedExcursion m M i))⁻¹ := by rw [← hf]
    have hvalid : validWord n (imageWord i j p q) := by
      intro k hk
      simp only [imageWord, List.mem_append] at hk
      rcases hk with (hk | hk) | hk
      · have h := hshape.2.1 k hk
        omega
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
        have hr := List.mem_range.mp hr
        constructor <;> dsimp [descending] at * <;> omega
      · have h := hshape.2.2 k hk
        omega
    refine ⟨⟨hvalid, ?_⟩, hconsecutive a p q ha.2.1 hshape, hprod⟩
    -- A shorter target representative would shorten the original reduced source.
    intro v hv hπ
    have hconcat_valid : validWord n (v ++ deletedExcursion m M i) := by
      intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · exact hv k hk
      · exact hvalid_deleted k hk
    have hconcat_prod : wordProduct n (v ++ deletedExcursion m M i) = σ := by
      calc
        wordProduct n (v ++ deletedExcursion m M i) =
            wordProduct n v * wordProduct n (deletedExcursion m M i) := by
              simp [wordProduct]
        _ = σ := by rw [hπ, hprod]; group
    have hmin := ha.1.2 (v ++ deletedExcursion m M i)
      hconcat_valid (hconcat_prod.trans ha.2.2.symm)
    rw [hlength a p q hshape, List.length_append] at hmin
    omega
  have hmarker (p p' r r' : List Nat) (hjp : j ∉ p) (hjp' : j ∉ p')
      (heq : p ++ (j :: r) = p' ++ (j :: r')) : p = p' ∧ r = r' := by
    -- Only the prefix avoids the marker; the suffix may contain further copies.
    have hprefix (s t : List Nat) (hs : j ∉ s) :
        (s ++ j :: t).takeWhile (· != j) = s := by
      have hmem : ∀ x ∈ s, (x != j) = true := by
        intro x hx
        simp only [bne_iff_ne]
        exact fun he => hs (he ▸ hx)
      simp [List.takeWhile_append_of_pos hmem]
    have hp_eq : p = p' := by
      have hh := congrArg (fun s : List Nat => s.takeWhile (· != j)) heq
      simpa [hprefix p _ hjp, hprefix p' _ hjp'] using hh
    constructor
    · exact hp_eq
    · rw [hp_eq] at heq
      simpa using heq
  have hD : descending j i = j :: (descending j i).tail := by
    have hh := descending_head i j hij
    cases h : descending j i with
    | nil => simp [h] at hh
    | cons x xs =>
      simp [h] at hh
      simp [hh]
  have hF : fullExcursion m M i j = j :: (fullExcursion m M i j).tail := by
    have hh : (fullExcursion m M i j).head? = some j := by
      have hn : descending j m ≠ [] := by
        intro he
        have h := descending_head m j (by omega)
        rw [he] at h
        simp at h
      rw [fullExcursion, List.append_assoc, List.head?_append_of_ne_nil _ hn]
      exact descending_head m j (by omega)
    cases h : fullExcursion m M i j with
    | nil => simp [h] at hh
    | cons x xs =>
      simp [h] at hh
      simp [hh]
  have hsplit (p p' q q' : List Nat)
      (hp : ∀ k ∈ p, m < k ∧ k < j)
      (hp' : ∀ k ∈ p', m < k ∧ k < j)
      (heq : imageWord i j p q = imageWord i j p' q') :
      p = p' ∧ q = q' := by
    have hjp : j ∉ p := by
      intro h; have := hp j h; omega
    have hjp' : j ∉ p' := by
      intro h; have := hp' j h; omega
    rw [imageWord, imageWord, hD] at heq
    have heq' : p ++ (j :: ((descending j i).tail ++ q)) =
        p' ++ (j :: ((descending j i).tail ++ q')) := by
      simpa only [List.append_assoc, List.cons_append] using heq
    obtain ⟨hpre, hsuf⟩ := hmarker p p' _ _ hjp hjp' heq'
    exact ⟨hpre, by simpa using hsuf⟩
  have hshape_unique (a p p' q q' : List Nat)
      (h : sourceShape m M i j a p q)
      (h' : sourceShape m M i j a p' q') : p = p' ∧ q = q' := by
    have hjp : j ∉ p := by
      intro hk; have := h.2.1 j hk; omega
    have hjp' : j ∉ p' := by
      intro hk; have := h'.2.1 j hk; omega
    have heq := h.1.symm.trans h'.1
    rw [hF] at heq
    have heq' : p ++ (j :: ((fullExcursion m M i j).tail ++ q)) =
        p' ++ (j :: ((fullExcursion m M i j).tail ++ q')) := by
      simpa only [List.append_assoc, List.cons_append] using heq
    obtain ⟨hpre, hsuf⟩ := hmarker p p' _ _ hjp hjp' heq'
    exact ⟨hpre, by simpa using hsuf⟩
  let chooseShape (a : {a : List Nat // singletonWord n σ a}) :
      {pq : List Nat × List Nat // sourceShape m M i j a.val pq.1 pq.2} :=
    let h : ∃ pq : List Nat × List Nat,
        sourceShape m M i j a.val pq.1 pq.2 := by
      obtain ⟨p, q, h⟩ := hshape_all a.val a.property
      exact ⟨(p, q), h⟩
    ⟨Classical.choose h, Classical.choose_spec h⟩
  let f (a : {a : List Nat // singletonWord n σ a}) :
      {b : List Nat // singletonWord n
        (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b} :=
    ⟨imageWord i j (chooseShape a).val.1 (chooseShape a).val.2,
      hforward a.val (chooseShape a).val.1 (chooseShape a).val.2
        a.property (chooseShape a).property⟩
  have hf_spec (a : {a : List Nat // singletonWord n σ a}) (p q : List Nat)
      (h : sourceShape m M i j a.val p q) :
      (f a).val = imageWord i j p q := by
    obtain ⟨hp, hq⟩ := hshape_unique a.val (chooseShape a).val.1 p
      (chooseShape a).val.2 q (chooseShape a).property h
    change imageWord i j (chooseShape a).val.1 (chooseShape a).val.2 =
      imageWord i j p q
    rw [hp, hq]
  have hinj : Function.Injective f := by
    intro a a' heq
    have ha := (chooseShape a).property
    have ha' := (chooseShape a').property
    have himg : imageWord i j (chooseShape a).val.1 (chooseShape a).val.2 =
        imageWord i j (chooseShape a').val.1 (chooseShape a').val.2 :=
      congrArg Subtype.val heq
    obtain ⟨hp, hq⟩ := hsplit _ _ _ _ ha.2.1 ha'.2.1 himg
    apply Subtype.ext
    rw [ha.1, ha'.1, hp, hq]
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a₀, ha₀, _⟩ := hex
    obtain ⟨p₀, q₀, hshape₀⟩ := hshape_all a₀ ha₀
    obtain ⟨a, p, q, ha, hshape, hb, _⟩ :=
      source_deletion_surjective n m M i j σ a₀ p₀ q₀ hs hshape₀ ha₀ b.val b.property
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact (hf_spec ⟨a, ha⟩ p q hshape).trans hb
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro a p q hshape
  have he := hf_spec a p q hshape
  refine ⟨he, ?_, hpos⟩
  change a.val.length = (f a).val.length + (deletedExcursion m M i).length
  rw [he]
  exact hlength a.val p q hshape

#print axioms source_deletion_equiv

end D5.S1.Words.Permutations.MamedeDeletionEquiv
