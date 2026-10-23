/- GID: D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/NoEvenCycleRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching, mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Symmetric zero-diagonal matrices on graphs without even simple cycles have twice the maximum matching rank. -/
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open SimpleGraph Matrix Submodule Finset Equiv
open scoped symmDiff BigOperators Classical
namespace D5.S3.Combinatorics.Graph.Walks.NoEvenCycleRank
universe u v

/-- The witness is a maximum-cardinality matching, with no connectivity or inhabitance restriction. -/
theorem rank_eq_twice_maximum_matching
    {V : Type u} {K : Type v} [Fintype V] [Field K] [CharP K 2]
    (A : Matrix V V K) (hs : A.IsSymm) (hd : ∀ i, A i i = 0)
    (G : SimpleGraph V) (he : ∀ i j, G.Adj i j ↔ A i j ≠ 0)
    (hno : ∀ (x : V) (p : G.Walk x x), p.IsCycle → ¬ Even p.length) :
    ∃ M : G.Subgraph, M.IsMatching ∧
      A.rank = 2 * M.coe.edgeFinset.card ∧
      ∀ N : G.Subgraph, N.IsMatching → N.coe.edgeFinset.card ≤ M.coe.edgeFinset.card := by
  classical
  have unique {V : Type u} [Finite V] (G : SimpleGraph V)
      (hno : ∀ (v : V) (p : G.Walk v v), p.IsCycle → ¬ Even p.length)
      (M N : G.Subgraph) (hM : M.IsPerfectMatching) (hN : N.IsPerfectMatching) :
      M = N := by
    classical
    let _ := Fintype.ofFinite V
    let H : SimpleGraph V := M.spanningCoe ∆ N.spanningCoe
    have hcyc : H.IsCycles := hM.symmDiff_isCycles hN
    have hle : H ≤ G := by
      intro x y h
      simp only [H, symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj] at h
      rcases h with h | h
      · exact M.adj_sub h.1
      · exact N.adj_sub h.1
    have hnone : ∀ x y, ¬ H.Adj x y := by
      intro x y hxy
      obtain ⟨p, hp, hverts⟩ :=
        hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
          (c := H.connectedComponentMk x) (by simp [ConnectedComponent.mem_supp_iff]) ⟨y, hxy⟩
      have hclosed : ∀ a ∈ p.toSubgraph.verts, ∀ b, M.Adj a b → b ∈ p.toSubgraph.verts := by
        intro a ha b hab
        have hncard := hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp ha)
        obtain ⟨z, haz⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hncard]; decide)
        have hHaz : H.Adj a z := p.toSubgraph.adj_sub haz
        have hNnot : ¬ N.Adj a b := by
          intro hNab
          simp only [H, symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj] at hHaz
          rcases hHaz with ⟨hMaz, hNaz⟩ | ⟨hNaz, hMaz⟩
          · have hzb := hM.1.eq_of_adj_left hMaz hab
            exact hNaz (hzb ▸ hNab)
          · have hzb := hN.1.eq_of_adj_left hNaz hNab
            exact hMaz (hzb ▸ hab)
        have hHab : H.Adj a b := by
          simp only [H, symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj]
          exact Or.inl ⟨hab, hNnot⟩
        exact p.toSubgraph.edge_vert
          ((hp.adj_toSubgraph_iff_of_isCycles hcyc ha b).mpr hHab).symm
      let K := M.induce p.toSubgraph.verts
      have hK : K.IsMatching := by
        intro a ha
        have ha' : a ∈ p.toSubgraph.verts := ha
        obtain ⟨b, hab, hb⟩ := hM.1 (hM.2 a)
        refine ⟨b, ⟨ha', hclosed a ha' b hab, hab⟩, ?_⟩
        intro z hz
        exact hb z hz.2.2
      have hKv : K.verts = p.toSubgraph.verts := by
        rfl
      have htail : p.toSubgraph.verts.toFinset = p.support.tail.toFinset := by
        ext a
        simp only [Set.mem_toFinset, p.mem_verts_toSubgraph, List.mem_toFinset]
        rw [← p.cons_tail_support]
        simp only [List.mem_cons]
        exact ⟨fun h => h.elim (fun h => h ▸ p.end_mem_tail_support hp.not_nil) id,
          Or.inr⟩
      have hcard : p.toSubgraph.verts.toFinset.card = p.length := by
        rw [htail, List.toFinset_card_of_nodup hp.support_nodup, List.length_tail,
          p.length_support]
        omega
      have heven : Even p.length := by
        have := hK.even_card
        rwa [hKv, hcard] at this
      exact (hno x (p.mapLe hle) (hp.mapLe hle)) (by simpa using heven)
    apply Subgraph.ext (hM.2.verts_eq_univ.trans hN.2.verts_eq_univ.symm)
    funext a b
    apply propext
    constructor
    · intro h
      by_contra hn
      exact hnone a b (by
        simp only [H, symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj]
        exact Or.inl ⟨h, hn⟩)
    · intro h
      by_contra hm
      exact hnone a b (by
        simp only [H, symmDiff_def, sup_adj, sdiff_adj, Subgraph.spanningCoe_adj]
        exact Or.inr ⟨h, hm⟩)
  have principal
      {n : Type u} [Fintype n] [DecidableEq n] [Field K]
      (A : Matrix n n K) (hsym : A.IsSymm) :
      ∃ S : Finset n,
        S.card = A.rank ∧
        (A.submatrix (fun i : S => (i : n)) (fun i : S => (i : n))).rank = A.rank ∧
        (A.submatrix (fun i : S => (i : n)) (fun i : S => (i : n))).det ≠ 0 := by
    classical
    obtain ⟨s, _, _, hspan, hli⟩ :=
      exists_linearIndepOn_extension (K := K) (v := A.row)
        (linearIndepOn_empty K A.row) (Set.empty_subset Set.univ)
    let S : Finset n := s.toFinset
    have hS : (↑S : Set n) = s := Set.coe_toFinset s
    rw [← hS] at hspan hli
    let B : Matrix S n K := A.submatrix Subtype.val id
    let D : Matrix S S K := A.submatrix Subtype.val Subtype.val
    have hliB : LinearIndependent K B.row := hli
    have himage : A.row '' (↑S : Set n) = Set.range B.row := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.property, rfl⟩
    have hspanEq : span K (Set.range B.row) = span K (Set.range A.row) := by
      apply le_antisymm
      · apply span_mono
        rintro x ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · apply span_le.mpr
        rintro x ⟨i, rfl⟩
        rw [← himage]
        exact hspan ⟨i, Set.mem_univ i, rfl⟩
    have hcoeff : ∀ i : n, ∃ c : S → K, c ᵥ* B = A.row i := by
      intro i
      have hi : A.row i ∈ span K (Set.range B.row) := by
        rw [hspanEq]
        exact subset_span ⟨i, rfl⟩
      rw [← range_vecMulLinear B] at hi
      exact hi
    choose C hC using hcoeff
    let X : Matrix n S K := Matrix.of C
    have hACB : A = X * B := by
      ext i j
      exact (congrFun (hC i) j).symm
    have hcols : A.submatrix id Subtype.val = X * D := by
      ext i j
      exact congrFun (congrFun hACB i) j
    have hBD : B = D * Xᵀ := by
      have ht := congrArg Matrix.transpose hcols
      have hDsym : Dᵀ = D := (hsym.submatrix (Subtype.val : S → n)).eq
      simpa only [Matrix.transpose_submatrix, hsym.eq, Matrix.transpose_mul,
        hDsym] using ht
    have hinjB : Function.Injective B.vecMul := Matrix.vecMul_injective_iff.mpr hliB
    have hinjD : Function.Injective D.vecMul := by
      intro x y hxy
      change x ᵥ* D = y ᵥ* D at hxy
      apply hinjB
      change x ᵥ* B = y ᵥ* B
      rw [hBD]
      rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hxy]
    have hunit : IsUnit D := Matrix.vecMul_injective_iff_isUnit.mp hinjD
    have hdet : D.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det D).mp hunit |>.ne_zero
    have hrB : B.rank = S.card := by
      simpa only [Fintype.card_coe] using hliB.rank_matrix
    have hrA : A.rank = B.rank := by
      rw [A.rank_eq_finrank_span_row, B.rank_eq_finrank_span_row, hspanEq]
    have hrD : D.rank = A.rank := by
      rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_coe, ← hrB, hrA]
    exact ⟨S, hrB.symm.trans hrA.symm, hrD, hdet⟩
  have determinant : ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (A : Matrix V V K), (∀ i j, A i j = A j i) → (∀ i, A i i = 0) →
      ∀ (G : SimpleGraph V), (∀ i j, G.Adj i j ↔ A i j ≠ 0) →
      (∀ M N : G.Subgraph, M.IsPerfectMatching → N.IsPerfectMatching → M = N) →
      (A.det ≠ 0 ↔ ∃ M : G.Subgraph, M.IsPerfectMatching) := by
    intro V _ _
    let term (A : Matrix V V K) (σ : Equiv.Perm V) : K :=
      Equiv.Perm.sign σ • ∏ i, A (σ i) i

    have term_inv (A : Matrix V V K) (hs : ∀ i j, A i j = A j i) (σ : Equiv.Perm V) :
        term A σ⁻¹ = term A σ := by
      unfold term
      rw [Equiv.Perm.sign_inv]
      congr 1
      apply Fintype.prod_equiv σ⁻¹
      intro i
      simpa using hs (σ⁻¹ i) i

    have det_involutions (A : Matrix V V K) (hs : ∀ i j, A i j = A j i) :
        A.det = ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm V => σ⁻¹ = σ), term A σ := by
      classical
      rw [Matrix.det_apply]
      change (∑ σ : Equiv.Perm V, term A σ) = _
      have hz : (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm V => ¬σ⁻¹ = σ), term A σ) = 0 := by
        exact Finset.sum_involution (fun σ _ => σ⁻¹)
          (fun σ _ => by rw [term_inv A hs]; exact CharTwo.add_self_eq_zero _)
          (fun σ hσ _ => (Finset.mem_filter.mp hσ).2)
          (fun σ hσ => by
            have hne := (Finset.mem_filter.mp hσ).2
            simp only [Finset.mem_filter, Finset.mem_univ, inv_inv, true_and]
            exact fun h => hne h.symm)
          (fun σ _ => inv_inv σ)
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun σ : Equiv.Perm V => σ⁻¹ = σ) (term A), hz, add_zero]

    have inv_eq_involutive (σ : Equiv.Perm V) (hi : σ⁻¹ = σ) : Function.Involutive σ := by
      intro i
      have h := congrArg (fun p : Equiv.Perm V => p (σ i)) hi
      simpa using h.symm

    let involutionMatching (G : SimpleGraph V) (σ : Equiv.Perm V)
        (hi : Function.Involutive σ) (he : ∀ v, G.Adj v (σ v)) : G.Subgraph := {
      verts := Set.univ
      Adj v w := σ v = w
      adj_sub := by intro v w h; exact h ▸ he v
      edge_vert := by intro v w h; trivial
      symm := ⟨by intro v w h; rw [← h]; exact hi v⟩ }

    have involutionMatching_perfect (G : SimpleGraph V) (σ : Equiv.Perm V)
        (hi : Function.Involutive σ) (he : ∀ v, G.Adj v (σ v)) :
        (involutionMatching G σ hi he).IsPerfectMatching := by
      rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
      intro v
      exact ⟨σ v, rfl, fun w hw => (show σ v = w from hw).symm⟩

    have perfectMatching_involution (G : SimpleGraph V) (M : G.Subgraph)
        (hm : M.IsPerfectMatching) :
        ∃ σ : Equiv.Perm V, σ⁻¹ = σ ∧ ∀ v, G.Adj v (σ v) := by
      classical
      let f : V → V := fun v => (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hm v).choose
      have hf (v : V) : M.Adj v (f v) :=
        (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hm v).choose_spec.1
      have huniq (v w : V) (h : M.Adj v w) : w = f v :=
        (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hm v).choose_spec.2 w h
      have hi : Function.Involutive f := by
        intro v
        exact (huniq (f v) v (hf v).symm).symm
      refine ⟨hi.toPerm f, ?_, ?_⟩
      · rfl
      · intro v
        exact M.adj_sub (hf v)

    have term_nonzero_iff (A : Matrix V V K) (σ : Equiv.Perm V) :
        term A σ ≠ 0 ↔ ∀ i, A (σ i) i ≠ 0 := by
      classical
      simp [term, smul_ne_zero_iff_ne, Finset.prod_ne_zero_iff]

    let supported (G : SimpleGraph V) : Finset (Equiv.Perm V) := by
      classical
      exact Finset.univ.filter fun σ => σ⁻¹ = σ ∧ (∀ v, σ v ≠ v) ∧ (∀ v, G.Adj v (σ v))

    have mem_supported (G : SimpleGraph V) (σ : Equiv.Perm V) :
        σ ∈ supported G ↔ σ⁻¹ = σ ∧ (∀ v, σ v ≠ v) ∧ (∀ v, G.Adj v (σ v)) := by
      classical
      simp [supported]

    have det_supported (A : Matrix V V K) (hs : ∀ i j, A i j = A j i)
        (hd : ∀ i, A i i = 0) (G : SimpleGraph V)
        (he : ∀ i j, G.Adj i j ↔ A i j ≠ 0) :
        A.det = ∑ σ ∈ supported G, term A σ := by
      classical
      rw [det_involutions A hs]
      symm
      apply Finset.sum_subset
      · intro σ hσ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_supported G σ).mp hσ |>.1⟩
      · intro σ hσ hn
        have hi := (Finset.mem_filter.mp hσ).2
        by_cases hnf : ∀ v, σ v ≠ v
        · have hnedge : ¬∀ v, G.Adj v (σ v) := by
            intro hedge
            exact hn ((mem_supported G σ).mpr ⟨hi, hnf, hedge⟩)
          obtain ⟨v, hv⟩ := not_forall.mp hnedge
          have hvz : A (σ v) v = 0 := by
            by_contra hne
            exact hv ((he (σ v) v).mpr hne).symm
          unfold term
          rw [Finset.prod_eq_zero (f := fun i => A (σ i) i) (Finset.mem_univ v) hvz,
            smul_zero]
        · obtain ⟨v, hv⟩ := not_forall.mp hnf
          have hv' : σ v = v := Classical.not_not.mp hv
          unfold term
          rw [Finset.prod_eq_zero (f := fun i => A (σ i) i) (Finset.mem_univ v)
            (by rw [hv']; exact hd v), smul_zero]

    have supported_perm_unique (G : SimpleGraph V)
        (hu : ∀ M N : G.Subgraph, M.IsPerfectMatching → N.IsPerfectMatching → M = N)
        (σ τ : Equiv.Perm V) (hσ : σ ∈ supported G) (hτ : τ ∈ supported G) : σ = τ := by
      classical
      obtain ⟨hσinv, _, hσedge⟩ := (mem_supported G σ).mp hσ
      obtain ⟨hτinv, _, hτedge⟩ := (mem_supported G τ).mp hτ
      let Mσ := involutionMatching G σ (inv_eq_involutive σ hσinv) hσedge
      let Mτ := involutionMatching G τ (inv_eq_involutive τ hτinv) hτedge
      have hm : Mσ = Mτ := hu Mσ Mτ (involutionMatching_perfect G σ (inv_eq_involutive σ hσinv) hσedge)
        (involutionMatching_perfect G τ (inv_eq_involutive τ hτinv) hτedge)
      ext v
      have h : Mτ.Adj v (σ v) := by rw [← hm]
      exact (show τ v = σ v from h).symm

    have exact_fragment (A : Matrix V V K) (hs : ∀ i j, A i j = A j i)
        (hd : ∀ i, A i i = 0) (G : SimpleGraph V)
        (he : ∀ i j, G.Adj i j ↔ A i j ≠ 0)
        (hu : ∀ M N : G.Subgraph, M.IsPerfectMatching → N.IsPerfectMatching → M = N) :
        A.det ≠ 0 ↔ ∃ M : G.Subgraph, M.IsPerfectMatching := by
      classical
      have hdet := det_supported A hs hd G he
      constructor
      · intro hne
        by_contra hno
        apply hne
        rw [hdet]
        apply Finset.sum_eq_zero
        intro σ hσ
        obtain ⟨hi, _, hedge⟩ := (mem_supported G σ).mp hσ
        exact False.elim (hno ⟨involutionMatching G σ (inv_eq_involutive σ hi) hedge,
          involutionMatching_perfect G σ (inv_eq_involutive σ hi) hedge⟩)
      · rintro ⟨M, hm⟩
        obtain ⟨σ, hi, hedge⟩ := perfectMatching_involution G M hm
        have hσ : σ ∈ supported G := (mem_supported G σ).mpr
          ⟨hi, fun v => (G.ne_of_adj (hedge v)).symm, hedge⟩
        have hsingle : (∑ τ ∈ supported G, term A τ) = term A σ := by
          apply Finset.sum_eq_single σ
          · intro τ hτ hne
            exact False.elim (hne (supported_perm_unique G hu τ σ hτ hσ))
          · intro hn
            exact False.elim (hn hσ)
        rw [hdet, hsingle]
        apply (term_nonzero_iff A σ).mpr
        intro v
        exact (he (σ v) v).mp (hedge v).symm
    exact exact_fragment
  have induced_unique (s : Set V) : ∀ M N : (G.induce s).Subgraph,
      M.IsPerfectMatching → N.IsPerfectMatching → M = N := by
    apply unique (G.induce s)
    intro x p hp heven
    let e : G.induce s ↪g G := SimpleGraph.Embedding.induce s
    exact hno (e.toHom x) (p.map e.toHom) (hp.map e.injective)
      (by rwa [Walk.length_map])
  have nonsingular (s : Set V) [Fintype s] :
      (A.submatrix (Subtype.val : s → V) Subtype.val).det ≠ 0 ↔
      ∃ M : (G.induce s).Subgraph, M.IsPerfectMatching := by
    apply determinant
    · intro i j
      exact congrFun (congrFun hs.eq j) i
    · intro i
      exact hd i
    · intro i j
      exact he i j
    · exact induced_unique s
  have matching_card (N : G.Subgraph) (hN : N.IsMatching) :
      N.verts.toFinset.card = 2 * N.coe.edgeFinset.card := by
    letI : ∀ v : N.verts, Fintype (N.coe.neighborSet v) := fun _ => Subtype.fintype _
    have hh (v : N.verts) : N.coe.degree v = 1 := by
      rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
      obtain ⟨w, hw, hu⟩ := hN v.property
      refine ⟨⟨w, N.edge_vert hw.symm⟩, hw, ?_⟩
      intro z hz
      exact Subtype.ext (hu z hz)
    calc
      N.verts.toFinset.card = Fintype.card N.verts := Set.toFinset_card N.verts
      _ = ∑ v : N.verts, (1 : ℕ) := by simp
      _ = ∑ v : N.verts, N.coe.degree v := by
        apply Finset.sum_congr rfl
        intro v _
        exact (hh v).symm
      _ = 2 * N.coe.edgeFinset.card := N.coe.sum_degrees_eq_twice_card_edges
  have bound (N : G.Subgraph) (hN : N.IsMatching) :
      2 * N.coe.edgeFinset.card ≤ A.rank := by
    let L : (G.induce N.verts).Subgraph := {
      verts := Set.univ
      Adj i j := N.Adj i j
      adj_sub := fun h => N.adj_sub h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun _ _ h => h.symm⟩ }
    have hL : L.IsPerfectMatching := by
      rw [Subgraph.isPerfectMatching_iff]
      intro i
      obtain ⟨j, hj, hu⟩ := hN i.property
      refine ⟨⟨j, N.edge_vert hj.symm⟩, hj, ?_⟩
      intro k hk
      exact Subtype.ext (hu k hk)
    have hdet := (nonsingular N.verts).mpr ⟨L, hL⟩
    have hr := Matrix.rank_submatrix_le A (Subtype.val : N.verts → V) (Subtype.val : N.verts → V)
    rw [Matrix.rank_of_det_ne_zero hdet, ← Set.toFinset_card N.verts] at hr
    rwa [matching_card N hN] at hr
  obtain ⟨S, hS, _, hdet⟩ := principal A hs
  letI : Fintype (↑S : Set V) := Finset.Subtype.fintype S
  obtain ⟨L, hL⟩ := (nonsingular (↑S : Set V)).mp hdet
  let e : G.induce (↑S : Set V) ↪g G := SimpleGraph.Embedding.induce (↑S : Set V)
  let M : G.Subgraph := L.map e.toHom
  have hM : M.IsMatching := hL.1.map e.toHom e.injective
  have hverts : M.verts = (↑S : Set V) := by
    change e.toHom '' L.verts = _
    rw [hL.2.verts_eq_univ, Set.image_univ]
    ext x
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hrank : A.rank = 2 * M.coe.edgeFinset.card := by
    rw [← matching_card M hM, hverts, Finset.toFinset_coe]
    exact hS.symm
  refine ⟨M, hM, hrank, ?_⟩
  intro N hN
  have hh := bound N hN
  rw [hrank] at hh
  omega

#print axioms rank_eq_twice_maximum_matching
end D5.S3.Combinatorics.Graph.Walks.NoEvenCycleRank
