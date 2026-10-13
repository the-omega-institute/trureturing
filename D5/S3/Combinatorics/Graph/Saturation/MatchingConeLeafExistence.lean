/- GID: D5/S3/Combinatorics/Graph/Saturation/MatchingConeLeafExistence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Saturation/MatchingConeLeafExistence
   mirror-E: none(waiver:structural-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Copy, mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: Every maximal matching-cone-free graph of order at least twenty with at most order plus five edges has a leaf. -/
import D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality

namespace D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafExistence

open SimpleGraph Finset
open D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafUniversality

set_option maxHeartbeats 1800000 in
/-- Ordinary, noninduced saturation forces a leaf in every sparse host of
order at least twenty, including disconnected and nonminimal hosts. -/
theorem exists_degree_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : Maximal H.Free G) (hn : 20 ≤ Fintype.card V)
    (hedges : G.edgeFinset.card ≤ Fintype.card V + 5) :
    ∃ v : V, G.degree v = 1 := by
  classical
  let : DecidableRel H.Adj := fun a b => by
    rcases a with a | (a | ⟨i, s⟩) <;>
      rcases b with b | (b | ⟨j, t⟩) <;> dsimp [H] <;> infer_instance
  have hHcenter : H.degree (.inl ()) = 7 := by decide
  have hHpair : ∀ z : Fin 3 × Bool, H.degree (.inr (.inr z)) = 2 := by decide
  have hfree := hmax.prop
  -- Every newly created copy uses the missing edge as a required edge.
  have hnew : ∀ x y : V, x ≠ y → ¬ G.Adj x y →
      ∃ f : H.Copy (G ⊔ edge x y), ∃ a b,
        H.Adj a b ∧ ¬ G.Adj (f a) (f b) := by
    intro x y hxy hmissing
    obtain ⟨f⟩ := not_free.mp (hmax.not_prop_of_gt (G.lt_sup_edge x y hxy hmissing))
    refine ⟨f, ?_⟩
    by_contra h
    push Not at h
    exact hfree ⟨{ toHom := ⟨f, fun hab => h _ _ hab⟩, injective' := f.injective }⟩
  have hdegadd : ∀ x y : V, x ≠ y →
      (G ⊔ edge x y).degree x ≤ G.degree x + 1 := by
    intro x y hxy
    have hsub : (G ⊔ edge x y).neighborFinset x ⊆ insert y (G.neighborFinset x) := by
      intro z hz
      rcases (mem_neighborFinset _ _ _).mp hz with hz | hz
      · exact mem_insert_of_mem (mem_neighborFinset _ _ _ |>.mpr hz)
      · rcases (edge_adj _ _ _ _).mp hz with ⟨hz | hz, _⟩
        · exact mem_insert.mpr (Or.inl hz.2)
        · exact (hxy hz.1).elim
    have hc := card_le_card hsub
    have hi := card_insert_le y (G.neighborFinset x)
    simp only [card_neighborFinset_eq_degree] at hc hi
    omega
  have hcenterold : ∀ x y : V, ∀ f : H.Copy (G ⊔ edge x y),
      f (.inl ()) ≠ x → f (.inl ()) ≠ y →
      7 ≤ G.degree (f (.inl ())) := by
    intro x y f hcx hcy
    have heq : (G ⊔ edge x y).neighborFinset (f (.inl ())) =
        G.neighborFinset (f (.inl ())) := by
      ext z
      simp only [mem_neighborFinset, sup_adj, edge_adj]
      aesop
    have hd := f.degree_le (.inl ())
    rw [hHcenter, ← card_neighborFinset_eq_degree, heq,
      card_neighborFinset_eq_degree] at hd
    exact hd
  -- An isolate can only occupy the pendant role, forcing six old spokes at every other vertex.
  have hpositive : ∀ v : V, 0 < G.degree v := by
    intro v
    by_contra hv
    have hdv : G.degree v = 0 := by omega
    have hiso : ∀ z, ¬ G.Adj v z := by
      intro z hz
      have hp := (G.degree_pos_iff_exists_adj v).mpr ⟨z, hz⟩
      omega
    have hother : ∀ w ∈ univ.erase v, 6 ≤ G.degree w := by
      intro w hw
      have hwv : w ≠ v := (mem_erase.mp hw).1
      obtain ⟨f, a, b, hab, hold⟩ := hnew v w hwv.symm (hiso w)
      have hadd := (edge_adj _ _ _ _).mp ((f.toHom.map_rel hab).resolve_left hold)
      have hrole : ∀ q, f q = v → q = .inr (.inl ()) := by
        intro q hq
        have hbound := hdegadd v w hwv.symm
        have hqdegree := f.degree_le q
        rw [hdv] at hbound
        rw [hq] at hqdegree
        rcases q with ⟨⟩ | (⟨⟩ | q)
        · rw [hHcenter] at hqdegree
          omega
        · rfl
        · rw [hHpair q] at hqdegree
          omega
      have hpend : f (.inr (.inl ())) = v := by
        rcases hadd.1 with h | h
        · exact (hrole a h.1) ▸ h.1
        · exact (hrole b h.2) ▸ h.2
      have hc : f (.inl ()) = w := by
        rcases hadd.1 with h | h
        · have ha := hrole a h.1
          subst a
          rcases b with ⟨⟩ | (⟨⟩ | b)
          · exact h.2
          · exact hab.elim
          · exact hab.elim
        · have hb := hrole b h.2
          subst b
          rcases a with ⟨⟩ | (⟨⟩ | a)
          · exact h.1
          · exact hab.elim
          · exact hab.elim
      let S := univ.image (fun z : Fin 3 × Bool => f (.inr (.inr z)))
      have hScard : S.card = 6 := by
        rw [card_image_of_injective _ (by
          intro a b he
          exact Sum.inr.inj (Sum.inr.inj (f.injective he)))]
        simp
      have hSsub : S ⊆ G.neighborFinset w := by
        intro z hz
        obtain ⟨q, _, rfl⟩ := mem_image.mp hz
        apply (mem_neighborFinset G w _).mpr
        have hh := f.toHom.map_rel (show H.Adj (.inl ()) (.inr (.inr q)) from trivial)
        rcases hh with hh | hh
        · change G.Adj (f (.inl ())) (f (.inr (.inr q))) at hh
          simpa only [hc] using hh
        · rcases (edge_adj _ _ _ _).mp hh with ⟨hh | hh, _⟩
          · exact (hwv (hc.symm.trans hh.1)).elim
          · have he := f.injective (hh.2.trans hpend.symm)
            simp at he
      have hh := card_le_card hSsub
      simpa only [hScard, card_neighborFinset_eq_degree] using hh
    have hsum : 6 * (Fintype.card V - 1) ≤ 2 * G.edgeFinset.card := by
      have hl : ∑ w ∈ univ.erase v, 6 ≤ ∑ w ∈ univ.erase v, G.degree w :=
        sum_le_sum hother
      have hu : ∑ w ∈ univ.erase v, G.degree w ≤ ∑ w : V, G.degree w :=
        sum_le_sum_of_subset (erase_subset v univ)
      simp only [sum_const, smul_eq_mul, card_erase_of_mem (mem_univ v), card_univ] at hl
      rw [G.sum_degrees_eq_twice_card_edges] at hu
      omega
    omega
  by_contra hleaf
  have hmin : ∀ v : V, 2 ≤ G.degree v := by
    intro v
    have hp := hpositive v
    have hne : G.degree v ≠ 1 := fun he => hleaf ⟨v, he⟩
    omega
  let C := univ.filter (fun v : V => 6 ≤ G.degree v)
  let L := univ \ C
  have hpartition : C.card + L.card = Fintype.card V := by
    exact card_add_card_compl C
  have hsum : (∑ c ∈ C, G.degree c) + (∑ x ∈ L, G.degree x) =
      2 * G.edgeFinset.card := by
    have hdisj : Disjoint C L := disjoint_left.mpr (by
      intro c hc hl
      exact (mem_sdiff.mp hl).2 hc)
    have hu : C ∪ L = univ := union_sdiff_of_subset (subset_univ C)
    rw [← sum_union hdisj, hu, G.sum_degrees_eq_twice_card_edges]
  have hCmin : 6 * C.card ≤ ∑ c ∈ C, G.degree c := by
    have hh : (∑ c ∈ C, (6 : ℕ)) ≤ ∑ c ∈ C, G.degree c :=
      sum_le_sum (fun c hc => (mem_filter.mp hc).2)
    simpa [Nat.mul_comm] using hh
  have hLmin : 2 * L.card ≤ ∑ x ∈ L, G.degree x := by
    simpa [Nat.mul_comm] using sum_le_sum (fun x (_hx : x ∈ L) => hmin x)
  have hCcard : C.card ≤ 2 := by omega
  have hCsum : ∑ c ∈ C, G.degree c ≤ 2 * C.card + 10 := by omega
  have hLdegree : ∀ x ∈ L, G.degree x ≤ 5 := by
    intro x hx
    have hh := (mem_sdiff.mp hx).2
    simp only [C, mem_filter, mem_univ, true_and] at hh
    omega
  -- Both low-degree endpoints exclude the center role. Its spokes therefore belong to the old host.
  have hneighbor : ∀ x ∈ L, ∃ c ∈ C, G.Adj c x := by
    intro x hx
    have hsize : 18 ≤ L.card := by omega
    have hdx := hLdegree x hx
    have hex : ∃ y ∈ L, y ≠ x ∧ ¬ G.Adj x y := by
      by_contra h
      push Not at h
      have hsub : L ⊆ insert x (G.neighborFinset x) := by
        intro y hy
        by_cases he : y = x
        · exact mem_insert.mpr (Or.inl he)
        · exact mem_insert_of_mem ((mem_neighborFinset G x y).mpr (h y hy he))
      have hh := card_le_card hsub
      have hi := card_insert_le x (G.neighborFinset x)
      rw [card_neighborFinset_eq_degree] at hi
      omega
    obtain ⟨y, hy, hyx, hmissing⟩ := hex
    have hdy := hLdegree y hy
    obtain ⟨f, a, b, hab, hold⟩ := hnew x y hyx.symm hmissing
    have hadd := (edge_adj _ _ _ _).mp ((f.toHom.map_rel hab).resolve_left hold)
    have hcx : f (.inl ()) ≠ x := by
      intro he
      have hd := f.degree_le (.inl ())
      rw [hHcenter, he] at hd
      have hh := hdegadd x y hyx.symm
      omega
    have hcy : f (.inl ()) ≠ y := by
      intro he
      have hd := f.degree_le (.inl ())
      rw [hHcenter, he] at hd
      have hh := hdegadd y x hyx
      have heq : (G ⊔ edge y x).degree y = (G ⊔ edge x y).degree y := by
        apply congrArg Finset.card
        ext z
        simp only [mem_neighborFinset, sup_adj, edge_adj]
        tauto
      rw [heq] at hh
      omega
    have hcdeg := hcenterold x y f hcx hcy
    have hrole : ∃ q, q ≠ .inl () ∧ f q = x := by
      rcases hadd.1 with h | h
      · exact ⟨a, fun he => hcx (he ▸ h.1), h.1⟩
      · exact ⟨b, fun he => hcx (he ▸ h.2), h.2⟩
    obtain ⟨q, hq, hqx⟩ := hrole
    have hspoke : H.Adj (.inl ()) q := by
      rcases q with ⟨⟩ | q
      · exact (hq rfl).elim
      · trivial
    have hcxadj : G.Adj (f (.inl ())) x := by
      rcases f.toHom.map_rel hspoke with hh | hh
      · change G.Adj (f (.inl ())) (f q) at hh
        simpa only [hqx] using hh
      · rcases (edge_adj _ _ _ _).mp hh with ⟨hh | hh, _⟩
        · exact (hcx hh.1).elim
        · exact (hcy hh.1).elim
    exact ⟨f (.inl ()), mem_filter.mpr ⟨mem_univ _, by omega⟩, hcxadj⟩
  have hcover : L ⊆ C.biUnion (fun c => G.neighborFinset c) := by
    intro x hx
    obtain ⟨c, hc, ha⟩ := hneighbor x hx
    exact mem_biUnion.mpr ⟨c, hc, (mem_neighborFinset G c x).mpr ha⟩
  have hincidence : L.card ≤ ∑ c ∈ C, G.degree c := by
    calc
      L.card ≤ (C.biUnion (fun c => G.neighborFinset c)).card := card_le_card hcover
      _ ≤ ∑ c ∈ C, (G.neighborFinset c).card := card_biUnion_le
      _ = _ := by simp only [card_neighborFinset_eq_degree]
  omega

#print axioms exists_degree_one

end D5.S3.Combinatorics.Graph.Saturation.MatchingConeLeafExistence
