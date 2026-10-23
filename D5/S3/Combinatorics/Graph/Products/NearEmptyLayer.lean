/- GID: D5/S3/Combinatorics/Graph/Products/NearEmptyLayer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/NearEmptyLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Deleting a vertex gives a coloring and a nearly empty layer in the Cartesian square. -/

import D5.S3.Combinatorics.Graph.Products.EmptyLayer
import D5.S3.Combinatorics.Graph.Brooks.Coloring

open SimpleGraph Finset

namespace CayleySquare

variable {V : Type*} [Fintype V]

private theorem colorable_delete (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (r : V) : (G.induce ({r}ᶜ : Set V)).Colorable G.maxDegree := by
  classical
  let N := Fintype.card V
  let e : V → ℕ := fun x => (Fintype.equivFin V x).val
  have he (x : V) : e x < N := (Fintype.equivFin V x).isLt
  let rank : V → ℕ := fun x => N * (N - G.dist r x) + e x
  have hrank : Function.Injective rank := by
    intro a b h
    have hmod (x : V) : rank x % N = e x := by
      simp only [rank, Nat.mul_add_mod, Nat.mod_eq_of_lt (he x)]
    apply (Fintype.equivFin V).injective
    apply Fin.ext
    change e a = e b
    rw [← hmod a, ← hmod b, h]
  have hdist (x : V) : G.dist r x < N := by
    obtain ⟨p, hp, hlen⟩ := (hc r x).exists_path_of_dist
    rw [← hlen]
    exact hp.length_lt
  let H := G.induce ({r}ᶜ : Set V)
  apply BrooksSubcubic.colorable_of_lower_neighbors_lt H G.maxDegree
    (fun x => rank x.val) (fun _ _ h => Subtype.ext (hrank h))
  intro u
  obtain ⟨w, huw, hw⟩ := BrooksSubcubic.exists_closer_neighbor G hc r u.val (by
    intro h
    exact u.property (Set.mem_singleton_iff.mpr h))
  have hblock : N - G.dist r u.val < N - G.dist r w := by have := hdist u.val; omega
  have hr : rank u.val < rank w := by
    have ha : N * (N - G.dist r u.val) + e u.val < N * (N - G.dist r u.val) + N := by
      have := he u.val; omega
    have hb : N * (N - G.dist r u.val) + N ≤ N * (N - G.dist r w) := by
      calc
        _ = N * ((N - G.dist r u.val) + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left N hblock
    dsimp [rank]
    omega
  let L := (H.neighborFinset u).filter (fun x => rank x.val < rank u.val)
  have hsub : L.image Subtype.val ⊆ (G.neighborFinset u.val).erase w := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    obtain ⟨hzu, hzr⟩ := mem_filter.mp hz
    refine mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      rw [heq] at hzr
      omega
    · exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hzu)
  calc
    L.card = (L.image Subtype.val).card := (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((G.neighborFinset u.val).erase w).card := card_le_card hsub
    _ = G.degree u.val - 1 := by
      rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr huw), G.card_neighborFinset_eq_degree]
    _ < G.maxDegree := by
      have := G.degree_le_maxDegree u.val
      have : 0 < G.degree u.val := by
        rw [← G.card_neighborFinset_eq_degree]
        exact card_pos.mpr ⟨w, (G.mem_neighborFinset _ _).mpr huw⟩
      omega

/-- A connected square admits a maximal independent set meeting some row at most once. -/
theorem exists_maximalIndepSet_near_empty_layer (G : SimpleGraph V)
    (hc : G.Connected) :
    ∃ I : Finset (V × V), Maximal (G □ G).IsIndepSet (I : Set (V × V)) ∧
      I.card ≤ (Fintype.card V - 1) * G.indepNum + 1 := by
  classical
  let : Nonempty V := hc.nonempty
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  let r : V := v
  obtain ⟨c⟩ := colorable_delete G hc r
  have hcard : G.maxDegree = Fintype.card (G.neighborSet v) :=
    hv.trans (G.card_neighborSet_eq_degree v).symm
  let e : Fin G.maxDegree ≃ G.neighborSet v :=
    (finCongr hcard).trans (Fintype.equivFin _).symm
  let f : ({r}ᶜ : Set V) → V × V := fun y => (e (c y), y.val)
  let T := univ.image f
  have hT : (G □ G).IsIndepSet (T : Set (V × V)) := by
    intro p hp q hq hpq hadj
    obtain ⟨y, _, rfl⟩ := mem_image.mp hp
    obtain ⟨z, _, rfl⟩ := mem_image.mp hq
    rcases hadj with ⟨h, he⟩ | ⟨h, he⟩
    · have he' : y = z := Subtype.ext he
      subst z
      exact h.ne rfl
    · exact c.valid h (e.injective (Subtype.ext he))
  let F : Finset (Finset (V × V)) := univ.filter fun J => (G □ G).IsIndepSet (J : Set (V × V))
  obtain ⟨I, hTI, hI⟩ := F.exists_le_maximal (mem_filter.mpr ⟨mem_univ T, hT⟩)
  have hi : (G □ G).IsIndepSet (I : Set (V × V)) := (mem_filter.mp hI.1).2
  have hm : Maximal (G □ G).IsIndepSet (I : Set (V × V)) := by
    refine ⟨hi, ?_⟩
    intro U hU hIU
    have hIU' : I ⊆ U.toFinset := by simpa using hIU
    have hUi : U.toFinset ⊆ I := hI.2 (mem_filter.mpr ⟨mem_univ _, by simpa using hU⟩) hIU'
    simpa using hUi
  have hvI : ∀ p ∈ I, p.1 = v → p.2 = r := by
    intro p hp he
    by_contra hpr
    let y : ({r}ᶜ : Set V) := ⟨p.2, by simpa using hpr⟩
    have ht : f y ∈ I := hTI (mem_image.mpr ⟨y, mem_univ _, rfl⟩)
    have ha : (G □ G).Adj p (f y) := by
      refine Or.inl ⟨?_, rfl⟩
      change G.Adj p.1 (e (c y)).val
      rw [he]
      exact (e (c y)).property
    exact hi hp ht ha.ne ha
  let J := I.filter (fun p => p.1 ≠ v)
  let K := I.filter (fun p => p.1 = v)
  have hj : J.card ≤ (Fintype.card V - 1) * G.indepNum := by
    have hb := card_le_layer_bound G G J (univ.erase v) (hi.mono (by
      intro p hp; exact (mem_filter.mp hp).1)) (by
      intro p hp; exact mem_erase.mpr ⟨(mem_filter.mp hp).2, mem_univ _⟩)
    simpa using hb
  have hk : K.card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    obtain ⟨hpI, hpv⟩ := mem_filter.mp hp
    obtain ⟨hqI, hqv⟩ := mem_filter.mp hq
    exact Prod.ext (hpv.trans hqv.symm) ((hvI p hpI hpv).trans (hvI q hqI hqv).symm)
  refine ⟨I, hm, ?_⟩
  have hs : J.card + K.card = I.card := by
    simpa [J, K] using I.card_filter_add_card_filter_not (fun p => p.1 ≠ v)
  omega

end CayleySquare
