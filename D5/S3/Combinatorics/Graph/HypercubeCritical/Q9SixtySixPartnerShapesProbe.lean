import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDiameterSixProbe

/-! Degree counts for the remaining seven- and eight-partner graphs. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset SimpleGraph

private lemma partner_degree_counts {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 6)
    (hd : ∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 4) :
    let H := univ.filter (fun v => G.degree v = 4)
    let L := univ.filter (fun v => G.degree v = 2)
    let e := G.edgeFinset.card
    (e = 7 → (H.card = 1 ∧ L.card = 5) ∨ (H.card = 2 ∧ L.card = 3)) ∧
      (e = 8 → H.card = 2 ∧ L.card = 4) := by
  classical
  let H := univ.filter (fun v => G.degree v = 4)
  let L := univ.filter (fun v => G.degree v = 2)
  let A := univ.filter (fun v => 0 < G.degree v)
  let e := G.edgeFinset.card
  have hA : H ∪ L = A := by
    ext v
    simp only [H,L,A,mem_union,mem_filter,mem_univ,true_and]
    rcases hd v with h | h | h <;> simp [h]
  have hdis : Disjoint H L := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have h := (mem_filter.mp hv).2
    have h' := (mem_filter.mp hw).2
    omega
  have hcard : H.card + L.card = A.card := by rw [← card_union_of_disjoint hdis,hA]
  have hA6 : A.card ≤ 6 := by simpa [hV] using card_le_card (subset_univ A)
  have hsumH : ∑ v ∈ H, G.degree v = 4 * H.card := by
    rw [sum_congr rfl (fun v hv => (mem_filter.mp hv).2)]
    rw [sum_const,smul_eq_mul,mul_comm]
  have hsumL : ∑ v ∈ L, G.degree v = 2 * L.card := by
    rw [sum_congr rfl (fun v hv => (mem_filter.mp hv).2)]
    rw [sum_const,smul_eq_mul,mul_comm]
  have hsumA : ∑ v ∈ A, G.degree v = ∑ v : V, G.degree v := by
    apply sum_subset (filter_subset _ _)
    simp only [mem_univ,mem_filter,true_and,not_lt,Nat.le_zero]
    exact fun _ _ h => h
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [← hsumA,← hA,sum_union hdis,hsumH,hsumL] at hsum
  change 4 * H.card + 2 * L.card = 2 * e at hsum
  have active (u v : V) (huv : G.Adj u v) : v ∈ A := by
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    exact (G.degree_pos v).mpr (fun hiso => hiso u huv.symm)
  have hNH (u : V) (hu : u ∈ H) : G.neighborFinset u ⊆ A.erase u := by
    intro v hv
    have hadj := (G.mem_neighborFinset u v).mp hv
    exact mem_erase.mpr ⟨hadj.ne.symm,active u v hadj⟩
  have hminA (hH : 0 < H.card) : 5 ≤ A.card := by
    obtain ⟨u,hu⟩ := card_pos.mp hH
    have huA : u ∈ A := by rw [← hA]; exact mem_union_left _ hu
    have his := card_le_card (hNH u hu)
    rw [G.card_neighborFinset_eq_degree,(mem_filter.mp hu).2,card_erase_of_mem huA] at his
    omega
  have hsmall (h5 : A.card = 5) (hL : 0 < L.card) : H.card ≤ 2 := by
    obtain ⟨v,hv⟩ := card_pos.mp hL
    have hsub : H ⊆ G.neighborFinset v := by
      intro u hu
      have huA : u ∈ A := by rw [← hA]; exact mem_union_left _ hu
      have hvA : v ∈ A := by rw [← hA]; exact mem_union_right _ hv
      have hne : v ≠ u := fun h => (Finset.disjoint_left.mp hdis) hu (h ▸ hv)
      have he : G.neighborFinset u = A.erase u := by
        apply eq_of_subset_of_card_le (hNH u hu)
        rw [G.card_neighborFinset_eq_degree,(mem_filter.mp hu).2,card_erase_of_mem huA,h5]
      have hp : v ∈ G.neighborFinset u := he ▸ mem_erase.mpr ⟨hne,hvA⟩
      exact (G.mem_neighborFinset v u).mpr ((G.mem_neighborFinset u v).mp hp).symm
    have h := card_le_card hsub
    rwa [G.card_neighborFinset_eq_degree,(mem_filter.mp hv).2] at h
  change (e = 7 → (H.card = 1 ∧ L.card = 5) ∨ (H.card = 2 ∧ L.card = 3)) ∧
    (e = 8 → H.card = 2 ∧ L.card = 4)
  constructor
  · intro he
    have h := hminA (by omega)
    omega
  · intro he
    have h := hminA (by omega)
    by_cases h5 : A.card = 5
    · have hs := hsmall h5 (by omega)
      omega
    · omega

#print axioms partner_degree_counts

private lemma eight_partner_adjacencies {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 6)
    (hd : ∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 4)
    (he : G.edgeFinset.card = 8) :
    ∃ a b : V, a ≠ b ∧ G.degree a = 4 ∧ G.degree b = 4 ∧
      (∀ v, v ≠ a → v ≠ b → G.degree v = 2) ∧
      ((¬ G.Adj a b ∧ ∀ v, v ≠ a → v ≠ b → G.Adj a v ∧ G.Adj b v) ∨
      (G.Adj a b ∧ ∃ u v : V, u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b ∧ u ≠ v ∧
        (∀ w, w ≠ a → w ≠ b → (G.Adj a w ↔ w ≠ u) ∧ (G.Adj b w ↔ w ≠ v)) ∧
        G.Adj u v ∧ ∀ w, w ≠ a → w ≠ b → w ≠ u → w ≠ v →
          G.neighborFinset w = {a,b})) := by
  let H := univ.filter (fun v => G.degree v = 4)
  let L := univ.filter (fun v => G.degree v = 2)
  have h := (partner_degree_counts G hV hd).2 he
  change H.card = 2 ∧ L.card = 4 at h
  obtain ⟨a,b,hab,hH⟩ := card_eq_two.mp h.1
  have hda : G.degree a = 4 := (mem_filter.mp (show a ∈ H by rw [hH]; simp)).2
  have hdb : G.degree b = 4 := (mem_filter.mp (show b ∈ H by rw [hH]; simp)).2
  have hLsub : L ⊆ (univ.erase a).erase b := by
    intro v hv
    have hvd := (mem_filter.mp hv).2
    have hva : v ≠ a := fun heq => by rw [heq,hda] at hvd; omega
    have hvb : v ≠ b := fun heq => by rw [heq,hdb] at hvd; omega
    exact mem_erase.mpr ⟨hvb,mem_erase.mpr ⟨hva,mem_univ _⟩⟩
  have hL : L = (univ.erase a).erase b := by
    apply eq_of_subset_of_card_le hLsub
    rw [h.2]
    simp [card_erase_of_mem,hab.symm,hV]
  have low (w : V) (hwa : w ≠ a) (hwb : w ≠ b) : w ∈ L := by
    rw [hL]
    exact mem_erase.mpr ⟨hwb,mem_erase.mpr ⟨hwa,mem_univ _⟩⟩
  have hlow_degree (w : V) (hwa : w ≠ a) (hwb : w ≠ b) : G.degree w = 2 :=
    (mem_filter.mp (low w hwa hwb)).2
  have full_low (w : V) (hw : w ∈ L) (haw : G.Adj a w) (hbw : G.Adj b w) :
      G.neighborFinset w = {a,b} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rcases mem_insert.mp hz with he | hz
      · exact (G.mem_neighborFinset w z).mpr (he.symm ▸ haw.symm)
      · have he := mem_singleton.mp hz
        exact (G.mem_neighborFinset w z).mpr (he.symm ▸ hbw.symm)
    · rw [G.card_neighborFinset_eq_degree,(mem_filter.mp hw).2,
        (card_eq_two.mpr ⟨a,b,hab,rfl⟩)]
  refine ⟨a,b,hab,hda,hdb,hlow_degree,?_⟩
  by_cases hAB : G.Adj a b
  · right
    have high_drop (x y : V) (hxy : x ≠ y)
        (hdx : G.degree x = 4) (hdy : G.degree y = 4) (hAdj : G.Adj x y)
        (hPair : ∀ w ∈ L, w ≠ x ∧ w ≠ y)
        (hExcept : ∀ w, w ≠ x → w ≠ y → w ∈ L) :
        ∃ u ∈ L, ∀ w ∈ L, G.Adj x w ↔ w ≠ u := by
      let N := G.neighborFinset x ∩ L
      have hnx : G.neighborFinset x = insert y N := by
        ext w
        constructor
        · intro hw
          by_cases hw' : w = y
          · exact mem_insert.mpr (Or.inl hw')
          · exact mem_insert_of_mem (mem_inter.mpr ⟨hw,
              hExcept w ((G.mem_neighborFinset x w).mp hw).ne.symm hw'⟩)
        · intro hw
          rcases mem_insert.mp hw with he | hw
          · exact (G.mem_neighborFinset x w).mpr (he.symm ▸ hAdj)
          · exact (mem_inter.mp hw).1
      have hny : y ∉ N := fun hp => (hPair y (mem_inter.mp hp).2).2 rfl
      have hN : N.card = 3 := by
        have h := congrArg Finset.card hnx
        rw [G.card_neighborFinset_eq_degree,hdx,card_insert_of_notMem hny] at h
        omega
      have hmiss : (L \ N).card = 1 := by
        rw [card_sdiff_of_subset inter_subset_right,h.2,hN]
      obtain ⟨u,hu⟩ := card_eq_one.mp hmiss
      have huL : u ∈ L := (mem_sdiff.mp (show u ∈ L \ N by rw [hu]; simp)).1
      refine ⟨u,huL,fun w hw => ?_⟩
      have hnot : w ∉ N ↔ w = u := by
        have hs : w ∈ L \ N ↔ w = u := by rw [hu,mem_singleton]
        exact (show w ∉ N ↔ w ∈ L \ N by simp [hw]).trans hs
      have heq : G.Adj x w ↔ w ∈ N := by simp [N,hw]
      exact heq.trans (by
        constructor
        · intro hn he
          exact (hnot.mpr he) hn
        · intro he
          by_contra hn
          exact he (hnot.mp hn))
    have not_high (w : V) (hw : w ∈ L) : w ≠ a ∧ w ≠ b := by
      have hz := mem_erase.mp (hL ▸ hw)
      exact ⟨(mem_erase.mp hz.2).1,hz.1⟩
    obtain ⟨u,hu,ha⟩ := high_drop a b hab hda hdb hAB not_high low
    obtain ⟨v,hv,hb⟩ := high_drop b a hab.symm hdb hda hAB.symm
      (fun w hw => (not_high w hw).symm) (fun w hwb hwa => low w hwa hwb)
    have hue : u ≠ v := by
      intro heq
      have huN : (G.neighborFinset u).card = 2 := by
        rw [G.card_neighborFinset_eq_degree,(mem_filter.mp hu).2]
      obtain ⟨w,hw⟩ := card_pos.mp (by omega : 0 < (G.neighborFinset u).card)
      have huw := (G.mem_neighborFinset u w).mp hw
      have hwa : w ≠ a := fun he => (ha u hu).mp (he ▸ huw.symm) rfl
      have hwb : w ≠ b := fun he => (hb u hu).mp (he ▸ huw.symm) heq
      have hwL := low w hwa hwb
      have hNW := full_low w hwL ((ha w hwL).mpr huw.ne.symm)
        ((hb w hwL).mpr (fun h => huw.ne (heq.trans h.symm)))
      have hum : u ∈ ({a,b} : Finset V) := hNW ▸ (G.mem_neighborFinset w u).mpr huw.symm
      simp [(not_high u hu).1,(not_high u hu).2] at hum
    have hNu : G.neighborFinset u ⊆ {b,v} := by
      intro w hw
      have huw := (G.mem_neighborFinset u w).mp hw
      by_cases hwb : w = b
      · simp [hwb]
      have hwa : w ≠ a := fun he => (ha u hu).mp (he ▸ huw.symm) rfl
      by_cases hwv : w = v
      · simp [hwv]
      have hwL := low w hwa hwb
      have hNW := full_low w hwL ((ha w hwL).mpr huw.ne.symm) ((hb w hwL).mpr hwv)
      have hum : u ∈ ({a,b} : Finset V) := hNW ▸ (G.mem_neighborFinset w u).mpr huw.symm
      simp [(not_high u hu).1,(not_high u hu).2] at hum
    have hNue : G.neighborFinset u = {b,v} := by
      apply eq_of_subset_of_card_le hNu
      rw [G.card_neighborFinset_eq_degree,(mem_filter.mp hu).2,
        (card_eq_two.mpr ⟨b,v,(not_high v hv).2.symm,rfl⟩)]
    refine ⟨hAB,u,v,(not_high u hu).1,(not_high u hu).2,(not_high v hv).1,
      (not_high v hv).2,hue,?_,?_,?_⟩
    · intro w hwa hwb
      exact ⟨ha w (low w hwa hwb),hb w (low w hwa hwb)⟩
    · apply (G.mem_neighborFinset u v).mp
      rw [hNue]
      simp
    · intro w hwa hwb hwu hwv
      have hwL := low w hwa hwb
      exact full_low w hwL ((ha w hwL).mpr hwu) ((hb w hwL).mpr hwv)
  · left
    have neighbors (x y : V) (hxy : x ≠ y) (hdx : G.degree x = 4) (hn : ¬G.Adj x y)
        (hExcept : ∀ w, w ≠ x → w ≠ y → w ∈ L) : G.neighborFinset x = L := by
      apply eq_of_subset_of_card_le
      · intro w hw
        have hxw := (G.mem_neighborFinset x w).mp hw
        exact hExcept w hxw.ne.symm (fun he => hn (he ▸ hxw))
      · rw [G.card_neighborFinset_eq_degree,hdx,h.2]
    have ha := neighbors a b hab hda hAB low
    have hb := neighbors b a hab.symm hdb (fun h => hAB h.symm)
      (fun w hwb hwa => low w hwa hwb)
    refine ⟨hAB,fun w hwa hwb => ?_⟩
    exact ⟨(G.mem_neighborFinset a w).mp (ha.symm ▸ low w hwa hwb),
      (G.mem_neighborFinset b w).mp (hb.symm ▸ low w hwa hwb)⟩

#print axioms eight_partner_adjacencies
