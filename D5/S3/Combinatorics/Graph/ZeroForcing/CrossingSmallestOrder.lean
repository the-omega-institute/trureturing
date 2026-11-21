/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/CrossingSmallestOrder
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Star]
   utility: none
   digest: Trees of order n have equal connected forcing coefficients, and the ordered crossing of Mukherjee and Ray holds, exactly when n <= 3. -/

import D5.S3.Combinatorics.Graph.ZeroForcing.StarConnectedForcing
import Mathlib.Combinatorics.SimpleGraph.Star

/-! Problem 5.3 of S. Mukherjee and P. Ray, On the connected zero forcing polynomial of finite
trees (arXiv:2611.10985), asks for a cutoff `l` with the first tree's connected forcing
coefficients below the second's up to `l` and above them afterwards, for every pair of trees of
the same order. `claimAt n` is that assertion at order `n`; the frozen
`ConnectedForcingCrossingRefutation.claim` is its conjunction over all orders.

`result`: all trees of order `n` have the same coefficients exactly when `n ≤ 3`, and `claimAt n`
holds exactly when `n ≤ 3`. Every tree on at most three vertices is
isomorphic to the path on as many vertices, and the coefficients are invariant under graph
isomorphism, so all trees of such an order have the same coefficients and `l = n` works. For
`n ≥ 4` the path followed by the star has no cutoff: the path has two connected forcing sets of
size one and the star none. Hence the smallest order of a counterexample is four.

admission_basis: escape-witness. Escape witnesses: black_map with cf_forward and coefficient_iso
(isomorphism invariance of the coefficients), coefficient_eq_path and tree_le_three (trees on at
most three vertices); the star is a tree by Mathlib's `isTree_starGraph`.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ZeroForcing.CrossingSmallestOrder

open SimpleGraph
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open D5.S3.Combinatorics.Graph.ZeroForcing.ConnectedForcingCrossingRefutation

variable {V W : Type*}

private theorem black_map (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (S : Set V)
    (v : V)    (hv : Black G S v) : Black H (e '' S) (e v) := by
  induction hv with
  | init h => exact .init ⟨_, h, rfl⟩
  | @force u w hu huw hall ihu ihall =>
    refine .force ihu (e.map_adj_iff.mpr huw) fun x hx hxw => ?_
    have := ihall (e.symm x) (by rw [← e.map_adj_iff]; simpa using hx)
      (fun h => hxw (by rw [← h]; simp))
    simpa using this

private theorem cf_forward (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (S : Finset V) (h : connectedForcing G S) :
    connectedForcing H (S.map e.toEquiv.toEmbedding) := by
  obtain ⟨hc, hf⟩ := h
  have hset : ((S.map e.toEquiv.toEmbedding : Finset W) : Set W) = e '' (S : Set V) := by
    ext; simp
  refine ⟨?_, fun w => ?_⟩
  · rw [hset]
    have iso : G.induce (S : Set V) ≃g H.induce (e '' (S : Set V)) :=
      e.induce e.injective.injOn.bijOn_image
    exact (Iso.connected_iff iso).mp hc
  · rw [hset]
    have := black_map G H e S (e.symm w) (hf _)
    simpa using this

/-- The connected forcing coefficients are invariant under graph isomorphism. -/
private theorem coefficient_iso [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) (i : ℕ) : coefficient G i = coefficient H i := by
  classical
  unfold coefficient
  refine Finset.card_bij (fun S _ => S.map e.toEquiv.toEmbedding) ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact ⟨by rw [Finset.card_map, hS.1], cf_forward G H e S hS.2⟩
  · intro S _ T _ h
    exact Finset.map_injective _ h
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    refine ⟨T.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [Finset.card_map, hT.1], cf_forward H G e.symm T hT.2⟩
    · rw [Finset.map_map]
      conv_rhs => rw [← Finset.map_refl (s := T)]
      congr 1
      ext x
      simp

/-- A map into `Fin n` that is injective, preserves and reflects adjacency onto the path, gives
equal coefficients. -/
private theorem coefficient_eq_path [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hV : Fintype.card V = n)    (f : V → Fin n) (hf : Function.Injective f)
    (hadj : ∀ u v, G.Adj u v ↔ (pathGraph n).Adj (f u) (f v)) (i : ℕ) :
    coefficient G i = coefficient (pathGraph n) i := by
  have hb : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp [hV]⟩
  exact coefficient_iso G (pathGraph n)
    { toEquiv := Equiv.ofBijective f hb
      map_rel_iff' := by intro u v; exact (hadj u v).symm } i

/-- A tree on at most three vertices has the coefficients of the path on as many vertices. -/
private theorem tree_le_three [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) (n : ℕ)
    (hV : Fintype.card V = n) (hn : n ≤ 3) (i : ℕ) :
    coefficient G i = coefficient (pathGraph n) i := by
  classical
  have hne : Nonempty V := hG.connected.nonempty
  have hpos : 0 < n := hV ▸ Fintype.card_pos
  have hirr : ∀ u, ¬ G.Adj u u := G.loopless.irrefl
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl
  · refine coefficient_eq_path G 1 hV (fun _ => 0) ?_ ?_ i
    · intro u v _
      exact Fintype.card_le_one_iff.mp (by omega) u v
    · intro u v
      have : u = v := Fintype.card_le_one_iff.mp (by omega) u v
      subst this; simp
  · obtain ⟨x, y, hxy, huniv⟩ := Finset.card_eq_two.mp (show (Finset.univ : Finset V).card = 2 by
      simpa using hV)
    have hmem : ∀ u, u = x ∨ u = y := fun u => by
      have := Finset.mem_univ u; rw [huniv] at this; simpa using this
    have : Nontrivial V := ⟨⟨x, y, hxy⟩⟩
    obtain ⟨u, hu⟩ := hG.connected.preconnected.exists_adj_of_nontrivial x
    have hxy' : G.Adj x y := by
      rcases hmem u with rfl | rfl
      · exact absurd hu (hirr _)
      · exact hu
    refine coefficient_eq_path G 2 hV (fun u => if u = x then 0 else 1) ?_ ?_ i
    · intro u v h
      rcases hmem u with rfl | rfl <;> rcases hmem v with rfl | rfl <;> simp_all [Ne.symm hxy]
    · intro u v
      rcases hmem u with rfl | rfl <;> rcases hmem v with rfl | rfl <;>
        simp [hxy', hxy'.symm, Ne.symm hxy, pathGraph_adj]
  · obtain ⟨x, y, z, hxy, hxz, hyz, huniv⟩ := Finset.card_eq_three.mp
      (show (Finset.univ : Finset V).card = 3 by simpa using hV)
    have hmem : ∀ u, u = x ∨ u = y ∨ u = z := fun u => by
      have := Finset.mem_univ u; rw [huniv] at this; simpa using this
    -- not a triangle
    have hnot3 : ¬ (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) := by
      rintro ⟨h1, h2, h3⟩
      have hsub : ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> simpa
      have hcard : ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 V)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · intro e; rw [Sym2.eq_iff] at e; tauto
        · simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]; tauto
      have h1 := Finset.card_le_card hsub
      have h2 := hG.card_edgeFinset
      omega
    -- each vertex has a neighbour
    have : Nontrivial V := ⟨⟨x, y, hxy⟩⟩
    have nb : ∀ v, ∃ u, G.Adj v u := hG.connected.preconnected.exists_adj_of_nontrivial
    have nbx : G.Adj x y ∨ G.Adj x z := by
      obtain ⟨u, hu⟩ := nb x
      rcases hmem u with rfl | rfl | rfl
      · exact absurd hu (hirr _)
      · exact Or.inl hu
      · exact Or.inr hu
    have nby : G.Adj x y ∨ G.Adj y z := by
      obtain ⟨u, hu⟩ := nb y
      rcases hmem u with rfl | rfl | rfl
      · exact Or.inl hu.symm
      · exact absurd hu (hirr _)
      · exact Or.inr hu
    have nbz : G.Adj x z ∨ G.Adj y z := by
      obtain ⟨u, hu⟩ := nb z
      rcases hmem u with rfl | rfl | rfl
      · exact Or.inl hu.symm
      · exact Or.inr hu.symm
      · exact absurd hu (hirr _)
    -- the centre `c` is adjacent to `a` and `b`, which are not adjacent
    obtain ⟨a, b, c, hab, hac, hbc, hmem', hca, hcb, hnab⟩ : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (∀ u, u = a ∨ u = b ∨ u = c) ∧ G.Adj c a ∧ G.Adj c b ∧ ¬ G.Adj a b := by
      by_cases h1 : G.Adj x y
      · by_cases h2 : G.Adj x z
        · have h3 : ¬ G.Adj y z := fun h3 => hnot3 ⟨h1, h2, h3⟩
          exact ⟨y, z, x, hyz, Ne.symm hxy, Ne.symm hxz,
            fun u => by rcases hmem u with h | h | h <;> simp [h], h1, h2, h3⟩
        · have h3 : G.Adj y z := nbz.resolve_left h2
          exact ⟨x, z, y, hxz, hxy, Ne.symm hyz,
            fun u => by rcases hmem u with h | h | h <;> simp [h], h1.symm, h3, h2⟩
      · have h2 : G.Adj x z := nbx.resolve_left h1
        have h3 : G.Adj y z := nby.resolve_left h1
        exact ⟨x, y, z, hxy, hxz, hyz,
          fun u => by rcases hmem u with h | h | h <;> simp [h], h2.symm, h3.symm, h1⟩
    have hnba : ¬ G.Adj b a := fun h => hnab h.symm
    refine coefficient_eq_path G 3 hV
      (fun u => if u = a then 0 else if u = c then 1 else 2) ?_ ?_ i
    · intro u v h
      rcases hmem' u with rfl | rfl | rfl <;> rcases hmem' v with rfl | rfl | rfl <;>
        simp_all [Ne.symm hab, Ne.symm hac]
    · intro u v
      rcases hmem' u with rfl | rfl | rfl <;> rcases hmem' v with rfl | rfl | rfl <;>
        simp [hca, hcb, hca.symm, hcb.symm, hnab, hnba, hbc, Ne.symm hab, Ne.symm hac,
          pathGraph_adj]

/-- The star `K_{1,n-1}` is Mathlib's star graph centred at `0`, a tree. -/
private theorem star_tree {n : ℕ} (hn : 1 ≤ n) :
    (StarConnectedForcing.starGraph n).IsTree := by
  have : StarConnectedForcing.starGraph n = SimpleGraph.starGraph (⟨0, hn⟩ : Fin n) := by
    ext u v; simp [StarConnectedForcing.starGraph, SimpleGraph.starGraph_adj, Fin.ext_iff]
  rw [this]; exact isTree_starGraph _

/-- The ordered crossing assertion of Problem 5.3 at a fixed order `n`; `claim` is its
conjunction over all `n`. -/
def claimAt (n : ℕ) : Prop :=
  ∀ (p q : ℕ) (V W : Type) [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W),
    G.IsTree → H.IsTree → Fintype.card V = n → Fintype.card W = n →
    leafCount G = p → leafCount H = q →
    ∃ l : ℤ, 1 ≤ l ∧ l ≤ (n : ℤ) ∧
      ∀ i : ℤ, (1 ≤ i ∧ i ≤ l → coefficient G i.toNat ≤ coefficient H i.toNat) ∧
        (l + 1 ≤ i ∧ i ≤ (n : ℤ) → coefficient H i.toNat ≤ coefficient G i.toNat)

/-- Path followed by star at order `n ≥ 4`: two connected forcing sets of size one against none. -/
private theorem path_star_one {n : ℕ} (hn : 4 ≤ n) :
    coefficient (pathGraph n) 1 = 2 ∧ coefficient (StarConnectedForcing.starGraph n) 1 = 0 := by
  have hs := (StarConnectedForcing.result (n := n)).2.1 hn 1
  have h1 : ¬ (1 = n) := by omega
  have h2 : ¬ (1 + 1 = n) := by omega
  simp only [h1, h2, ↓reduceIte] at hs
  exact ⟨(PathConnectedForcing.result (n := n) (by omega)).2.1, hs⟩

/-- All trees of order `n` have the same connected forcing coefficients exactly when `n ≤ 3`. -/
private theorem equal_iff (n : ℕ) :
    (∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      G.IsTree → H.IsTree → Fintype.card V = n → Fintype.card W = n →
      ∀ i, coefficient G i = coefficient H i) ↔ n ≤ 3 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have := h (Fin n) (Fin n) (pathGraph n) (StarConnectedForcing.starGraph n)
      (isTree_pathGraph.mpr (by omega)) (star_tree (by omega)) (Fintype.card_fin n)
      (Fintype.card_fin n) 1
    have := path_star_one hn
    omega
  · intro hn V W _ _ G H hG hH hV hW i
    rw [tree_le_three G hG n hV hn, tree_le_three H hH n hW hn]

/-- The smallest order of a counterexample to the ordered crossing assertion is four. All trees of
order `n` have the same connected forcing coefficients exactly when `n ≤ 3`, and the crossing
assertion holds at order `n` exactly when `n ≤ 3`; at every order `n ≥ 4` the path followed by the
star is a counterexample to both. -/
theorem result (n : ℕ) :
    ((∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      G.IsTree → H.IsTree → Fintype.card V = n → Fintype.card W = n →
      ∀ i, coefficient G i = coefficient H i) ↔ n ≤ 3) ∧
    (claimAt n ↔ n ≤ 3) := by
  refine ⟨equal_iff n, ⟨fun h => ?_, fun hn => ?_⟩⟩
  · by_contra hn
    push Not at hn
    obtain ⟨l, hl, -, hi⟩ := h _ _ (Fin n) (Fin n) (pathGraph n)
      (StarConnectedForcing.starGraph n) (isTree_pathGraph.mpr (by omega))
      (star_tree (by omega)) (Fintype.card_fin n) (Fintype.card_fin n) rfl rfl
    have bad := (hi 1).1 ⟨le_rfl, hl⟩
    obtain ⟨hp, hs⟩ := path_star_one hn
    simp only [Int.toNat_one, hp, hs] at bad
    omega
  · intro p q V W _ _ G H hG hH hV hW _ _
    have hpos : 0 < n := hV ▸ (@Fintype.card_pos _ _ hG.connected.nonempty)
    refine ⟨n, by omega, le_rfl, fun i => ⟨fun _ => ?_, fun hi => by omega⟩⟩
    rw [(equal_iff n).mpr hn V W G H hG hH hV hW]

end D5.S3.Combinatorics.Graph.ZeroForcing.CrossingSmallestOrder
