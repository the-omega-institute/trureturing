/- GID: D5/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/FiniteForestCatalan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Actual finite linear forests have nonnegative signed Catalan functionals. -/

import D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-! Signed Catalan positivity from whole-carrier linear-forest path completion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset SimpleGraph
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
namespace D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan

private lemma maximal_path_closed {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hdeg : ∀ a, G.degree a ≤ 2) {u v : α} (p : G.Walk u v) (hp : p.IsPath)
    (hmax : ∀ (a b : α) (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    {a b : α} (ha : a ∈ p.support) (hab : G.Adj a b) : b ∈ p.support := by
  by_contra hb
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  by_cases hi0 : i = 0
  · subst i
    simp only [Walk.getVert_zero] at hab
    have hq := hmax _ _ (p.cons hab.symm) (hp.cons hb)
    simp only [Walk.length_cons] at hq
    omega
  by_cases hil : i = p.length
  · subst i
    simp only [Walk.getVert_length] at hab
    have hq := hmax _ _ (p.concat hab) (hp.concat hb hab)
    simp only [Walk.length_concat] at hq
    omega
  have him : i - 1 < p.length := by omega
  have hip : i < p.length := by omega
  have hadj₀ : G.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have hh := (p.adj_getVert_succ him).symm
    simpa [show i - 1 + 1 = i by omega] using hh
  have hadj₁ := p.adj_getVert_succ hip
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro he
    have := hp.getVert_injOn (by simpa using (show i - 1 ≤ p.length by omega))
      (by simpa using (show i + 1 ≤ p.length by omega)) he
    omega
  have hb₀ : b ≠ p.getVert (i - 1) := by
    intro he
    exact hb (he ▸ p.getVert_mem_support (i - 1))
  have hb₁ : b ≠ p.getVert (i + 1) := by
    intro he
    exact hb (he ▸ p.getVert_mem_support (i + 1))
  have hs : {b, p.getVert (i - 1), p.getVert (i + 1)} ⊆ G.neighborFinset (p.getVert i) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hab
    · exact (G.mem_neighborFinset _ _).mpr hadj₀
    · exact (G.mem_neighborFinset _ _).mpr hadj₁
  have hc := Finset.card_le_card hs
  have hd := hdeg (p.getVert i)
  simp [hb₀, hb₁, hne, G.card_neighborFinset_eq_degree] at hc
  omega

private lemma connected_path_order {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hc : G.Connected)
    (ha : G.IsAcyclic) (hd : ∀ a, G.degree a ≤ 2) :
    ∃ (n : ℕ) (e : α ≃ Fin n), ∀ a b, G.Adj a b → (pathGraph n).Adj (e a) (e b) := by
  letI := hc.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hall : ∀ a, a ∈ p.support := by
    intro a
    by_contra hnot
    obtain ⟨q⟩ := hc u a
    obtain ⟨d, _, hfst, hsnd⟩ := q.exists_boundary_dart {x | x ∈ p.support}
      p.start_mem_support hnot
    exact hsnd (maximal_path_closed G hd p hp hmax hfst d.adj)
  have hh := hp.isHamiltonian_of_mem hall
  let e : Fin (p.length + 1) ≃ α :=
    (finCongr p.length_support.symm).trans hh.getVertEquiv
  have he (i : Fin (p.length + 1)) : e i = p.getVert i.val := by rfl
  let J := G.comap e
  have hsub : pathGraph (p.length + 1) ≤ J := by
    intro i j hij
    change G.Adj (e i) (e j)
    rw [he, he]
    rcases pathGraph_adj.mp hij with hij | hij
    · simpa [hij] using p.adj_getVert_succ (i := i.val) (by omega)
    · exact G.adj_symm (by simpa [hij] using p.adj_getVert_succ (i := j.val) (by omega))
  have hj : J.IsAcyclic := ha.of_comap e.toEmbedding
  have ht : (pathGraph (p.length + 1)).IsTree :=
    ⟨connected_pathGraph_add_one _, isAcyclic_pathGraph _⟩
  have hback : J ≤ pathGraph (p.length + 1) :=
    (maximal_isAcyclic_iff_isTree.mpr ht).le_of_ge hj hsub
  refine ⟨p.length + 1, e.symm, ?_⟩
  intro a b hab
  apply hback
  change G.Adj (e (e.symm a)) (e (e.symm b))
  simpa using hab

universe u

private lemma forest_path_order {α : Type u} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (ha : G.IsAcyclic) (hd : ∀ a, G.degree a ≤ 2) :
    ∃ (n : ℕ) (e : α ≃ Fin n), ∀ a b, G.Adj a b → (pathGraph n).Adj (e a) (e b) := by
  classical
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α with
  | h n ih =>
    by_cases hempty : IsEmpty α
    · letI := hempty
      exact ⟨0, Equiv.equivEmpty α |>.trans (Equiv.equivEmpty (Fin 0)).symm,
        fun a => isEmptyElim a⟩
    haveI : Nonempty α := not_isEmpty_iff.mp hempty
    let a := Classical.choice (inferInstance : Nonempty α)
    let C := G.connectedComponentMk a
    have haC : a ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
    let S : Set α := C.supp
    letI : Fintype S := Fintype.ofFinite S
    letI : Fintype (Sᶜ : Set α) := Fintype.ofFinite (Sᶜ : Set α)
    have hc : (G.induce S).Connected := C.connected_toSimpleGraph
    obtain ⟨k, eC, heC⟩ := connected_path_order (G.induce S) hc
      (ha.induce S) (fun x => ((Copy.induce G S).degree_le x).trans (hd x))
    have hlt : Fintype.card (Sᶜ : Set α) < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := a) (fun h => h haC)
    obtain ⟨l, eB, heB⟩ := ih _ hlt (G.induce Sᶜ) (ha.induce Sᶜ)
      (fun x => ((Copy.induce G Sᶜ).degree_le x).trans (hd x)) rfl
    let e : α ≃ Fin (k + l) := (Equiv.Set.sumCompl S).symm |>.trans
      ((Equiv.sumCongr eC eB).trans finSumFinEquiv)
    refine ⟨k + l, e, ?_⟩
    intro x y hxy
    by_cases hx : x ∈ S
    · have hy : y ∈ S := (C.mem_supp_congr_adj hxy).mp hx
      have hh := heC ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hx,
        Equiv.Set.sumCompl_symm_apply_of_mem hy, pathGraph_adj,
        finSumFinEquiv_apply_left] using hh
    · have hy : y ∉ S := fun hy => hx ((C.mem_supp_congr_adj hxy).mpr hy)
      have hh := heB ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [e, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem hx,
        Equiv.Set.sumCompl_symm_apply_of_notMem hy, Equiv.sumCongr_apply,
        Sum.map_inr, finSumFinEquiv_apply_right, pathGraph_adj, Fin.val_natAdd]
      rcases pathGraph_adj.mp hh with hh | hh
      · left; omega
      · right; omega

private lemma partition_congr {α R : Type*} [DecidableEq α] [CommRing R]
    (G H : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (V : Finset α) (h : ∀ x ∈ V, ∀ y ∈ V, G.Adj x y ↔ H.Adj x y) (w : α → R) :
    partition G V w = partition H V w := by
  have he : configurations G V = configurations H V := by
    ext S
    simp only [configurations, mem_filter, mem_powerset]
    constructor
    · rintro ⟨hs, hi⟩
      exact ⟨hs, fun x hx y hy hne hxy => hi hx hy hne ((h x (hs hx) y (hs hy)).mpr hxy)⟩
    · rintro ⟨hs, hi⟩
      exact ⟨hs, fun x hx y hy hne hxy => hi hx hy hne ((h x (hs hx) y (hs hy)).mp hxy)⟩
  unfold partition
  rw [he]

private lemma partition_edge_absent {α R : Type*} [DecidableEq α] [CommRing R]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (u v : α)
    (hu : u ∉ V) (w : α → R) : partition (G ⊔ edge u v) V w = partition G V w := by
  apply partition_congr
  intro x hx y hy
  have hxu : x ≠ u := fun he => hu (he ▸ hx)
  have hyu : y ≠ u := fun he => hu (he ▸ hy)
  simp [sup_adj, edge_adj, hxu, hyu]

private lemma partition_add_edge {α R : Type*} [DecidableEq α] [CommRing R]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (u v : α)
    (hu : u ∈ V) (hv : v ∈ V) (hne : u ≠ v) (hn : ¬G.Adj u v) (w : α → R) :
    partition G V w = partition (G ⊔ edge u v) V w + w u * w v *
      partition G (closedComplement G V u ∩ closedComplement G V v) w := by
  classical
  let H := G ⊔ edge u v
  let N := closedComplement G V u
  have hvN : v ∈ N := by simp [N, closedComplement, hv, hne.symm, hn]
  have hc : closedComplement H V u = N.erase v := by
    ext x
    by_cases hx : x = u
    · subst x; simp [H, N, closedComplement]
    by_cases hxv : x = v
    · subst x; simp [H, N, closedComplement, sup_adj, edge_adj, hne, hne.symm]
    · simp [H, N, closedComplement, sup_adj, edge_adj, hx, hxv, Ne.symm hx, Ne.symm hxv]
  have hr : closedComplement G N v = closedComplement G V u ∩ closedComplement G V v := by
    ext x
    simp only [N, closedComplement, mem_filter, mem_erase, mem_inter]
    tauto
  have huN : u ∉ N.erase v := by simp [N, closedComplement]
  have he := partition_edge_absent G (V.erase u) u v (by simp) w
  have heN := partition_edge_absent G (N.erase v) u v huN w
  have hG := partition_delete G V u hu w
  have hH := partition_delete H V u hu w
  have hN := partition_delete G N v hvN w
  rw [hc, heN, he] at hH
  rw [hr] at hN
  dsimp only [H, N] at hH hN
  linear_combination hG - hH + w u * hN

private def catalanIntegerSeries : PowerSeries ℤ :=
  PowerSeries.catalanSeries.map (Nat.castRingHom ℤ)

private lemma coeff_partition_phi {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (m : ℕ) (hm : V.card ≤ m) :
    PowerSeries.coeff m (partition G V (fun _ => -PowerSeries.X) * catalanIntegerSeries) =
      phi G V m := by
  open PowerSeries in
    unfold partition phi
    rw [Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hsm : S.card ≤ m := (Finset.card_le_card
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)).trans hm
    have he : (-X : PowerSeries ℤ) ^ S.card = C ((-1 : ℤ) ^ S.card) * X ^ S.card := by
      rw [neg_eq_neg_one_mul, mul_pow]
      simp
    rw [Finset.prod_const, he, mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hsm]
    simp [catalanIntegerSeries]

private lemma residual_card {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (u v : α)
    (hu : u ∈ V) (hv : v ∈ V) (hne : u ≠ v) :
    (closedComplement G V u ∩ closedComplement G V v).card ≤ V.card - 2 ∧ 2 ≤ V.card := by
  have hv' : v ∈ V.erase u := mem_erase.mpr ⟨hne.symm, hv⟩
  have hpos := card_pos.mpr ⟨v, hv'⟩
  have hc₀ := card_erase_of_mem hu
  have hc₁ := card_erase_of_mem hv'
  have hs : closedComplement G V u ∩ closedComplement G V v ⊆ (V.erase u).erase v := by
    intro x hx
    obtain ⟨hx₀, hx₁⟩ := mem_inter.mp hx
    exact mem_erase.mpr ⟨(mem_erase.mp (mem_filter.mp hx₁).1).1, (mem_filter.mp hx₀).1⟩
  have hh := card_le_card hs
  constructor <;> omega

private lemma phi_add_edge {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (u v : α)
    (hu : u ∈ V) (hv : v ∈ V) (hne : u ≠ v) (hn : ¬G.Adj u v)
    (m : ℕ) (hm : V.card ≤ m) :
    phi G V m = phi (G ⊔ edge u v) V m +
      phi G (closedComplement G V u ∩ closedComplement G V v) (m - 2) := by
  open PowerSeries in
    let R := closedComplement G V u ∩ closedComplement G V v
    have hR := residual_card G V u v hu hv hne
    have hRm : R.card ≤ m - 2 := by dsimp [R]; omega
    have hm₂ : 2 ≤ m := hR.2.trans hm
    have hh := congrArg (fun F : PowerSeries ℤ => coeff m (F * catalanIntegerSeries))
      (partition_add_edge G V u v hu hv hne hn (fun _ => (-X : PowerSeries ℤ)))
    rw [add_mul, map_add, coeff_partition_phi G V m hm,
      coeff_partition_phi (G ⊔ edge u v) V m hm] at hh
    have hs : (-X : PowerSeries ℤ) * -X * partition G R (fun _ => -X) *
        catalanIntegerSeries = X ^ 2 * (partition G R (fun _ => -X) * catalanIntegerSeries) := by ring
    change phi G V m = phi (G ⊔ edge u v) V m +
      coeff m ((-X) * (-X) * partition G R (fun _ => -X) * catalanIntegerSeries) at hh
    rw [hs, coeff_X_pow_mul', ite_eq_left hm₂, coeff_partition_phi G R (m - 2) hRm] at hh
    exact hh

private lemma phi_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : α ↪ β) (hf : ∀ x y, G.Adj x y ↔ H.Adj (f x) (f y)) (V : Finset α) (m : ℕ) :
    phi H (V.map f) m = phi G V m := by
  classical
  have hi (S : Finset α) : H.IsIndepSet (S.map f : Set β) ↔ G.IsIndepSet (S : Set α) := by
    constructor
    · intro h x hx y hy hne hxy
      exact h (mem_map.mpr ⟨x, hx, rfl⟩) (mem_map.mpr ⟨y, hy, rfl⟩)
        (fun he => hne (f.injective he)) ((hf x y).mp hxy)
    · intro h x hx y hy hne hxy
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
      exact h ha hb (fun he => hne (congrArg f he)) ((hf a b).mpr hxy)
  have he : configurations H (V.map f) =
      (configurations G V).map (Finset.mapEmbedding f).toEmbedding := by
    ext T
    simp only [configurations, mem_filter, mem_powerset, mem_map, Function.Embedding.coeFn_mk,
      Finset.mapEmbedding_apply]
    constructor
    · rintro ⟨hsub, hind⟩
      obtain ⟨S, hS, rfl⟩ := subset_map_iff.mp hsub
      exact ⟨S, ⟨hS, (hi S).mp hind⟩, rfl⟩
    · rintro ⟨S, ⟨hs, hiS⟩, rfl⟩
      exact ⟨map_subset_map.mpr hs, (hi S).mpr hiS⟩
  unfold phi
  rw [he, Finset.sum_map]
  simp

private lemma phi_subtype {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (m : ℕ) :
    phi (G.induce (V : Set α)) univ m = phi G V m := by
  classical
  have he : (univ : Finset (V : Set α)).map (Function.Embedding.subtype _) = V := by
    ext x
    simp
  simpa only [he] using (phi_map (G.induce (V : Set α)) G
    (Function.Embedding.subtype _) (fun _ _ => Iff.rfl) univ m).symm

private lemma path_comap_degree {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (e : α ≃ Fin n) (a : α) : ((pathGraph n).comap e).degree a ≤ 2 := by
  classical
  let K := (pathGraph n).comap e
  let f : α → ℕ := fun x => (e x).val
  have hf : Function.Injective f := Fin.val_injective.comp e.injective
  have hs : (K.neighborFinset a).image f ⊆ {f a - 1, f a + 1} := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
    have hh := pathGraph_adj.mp ((K.mem_neighborFinset a b).mp hb)
    simp only [mem_insert, mem_singleton]
    dsimp [f]
    omega
  have hc := card_le_card hs
  rw [card_image_of_injective _ hf, K.card_neighborFinset_eq_degree] at hc
  exact hc.trans Finset.card_le_two

set_option maxHeartbeats 1000000 in
/-- The signed Catalan sum over all actual vertices of every finite linear forest. -/
theorem finite_forest_phi_nonnegative {α : Type u} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (ha : G.IsAcyclic) (hd : ∀ a, G.degree a ≤ 2) (m : ℕ)
    (hm : Fintype.card α ≤ m) : 0 ≤ phi G univ m := by
  classical
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α m with
  | h n ih =>
    obtain ⟨k, e, he⟩ := forest_path_order G ha hd
    let K := (pathGraph k).comap e
    let decK : DecidableRel K.Adj := inferInstance
    have hGK : G ≤ K := fun a b hab => he a b hab
    have hKa : K.IsAcyclic := (isAcyclic_pathGraph k).of_comap e.toEmbedding
    have hKd : ∀ a, K.degree a ≤ 2 := path_comap_degree k e
    have hKpos : 0 ≤ phi K univ m := by
      let f : α ↪ ℕ := e.toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩
      have hf : ∀ x y, K.Adj x y ↔ (SimpleGraph.hasse ℕ).Adj (f x) (f y) := by
        intro x y
        simp [K, f, pathGraph_adj, SimpleGraph.hasse_adj, ← Order.succ_eq_iff_covBy]
      have hmap : (univ : Finset α).map f = range k := by
        ext x
        simp only [mem_map, mem_univ, true_and, mem_range]
        constructor
        · rintro ⟨a, rfl⟩
          exact (e a).isLt
        · intro hx
          exact ⟨e.symm ⟨x, hx⟩, by simp [f]⟩
      have hcard := Fintype.card_congr e
      simp only [Fintype.card_fin] at hcard
      rw [← phi_map K (SimpleGraph.hasse ℕ) f hf univ m, hmap]
      exact path_phi_nonnegative k m (by omega)
    have hfill : ∀ d (H : SimpleGraph α) [DecidableRel H.Adj], H ≤ K →
        Nat.card K.edgeSet - Nat.card H.edgeSet = d → 0 ≤ phi H univ m := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d jh =>
        intro H instH hHK hdiff
        by_cases hEq : H = K
        · subst H
          have hi : instH = decK := Subsingleton.elim _ _
          rw [hi]
          exact hKpos
        have hnot : ¬K ≤ H := fun hKH => hEq (le_antisymm hHK hKH)
        change ¬(∀ ⦃a b : α⦄, K.Adj a b → H.Adj a b) at hnot
        push_neg at hnot
        obtain ⟨a, b, hab, hnab⟩ := hnot
        have hne := K.ne_of_adj hab
        let J := H ⊔ edge a b
        have hJK : J ≤ K := sup_le hHK ((edge_le_iff K).mpr (Or.inr hab))
        have hJcard : Nat.card J.edgeSet = Nat.card H.edgeSet + 1 := by
          simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using
            H.card_edgeFinset_sup_edge hnab hne
        have hbound : Nat.card J.edgeSet ≤ Nat.card K.edgeSet := by
          simpa only [edgeFinset_card, ← Nat.card_eq_fintype_card] using
            card_le_card (edgeFinset_mono hJK)
        have hless : Nat.card K.edgeSet - Nat.card J.edgeSet < d := by omega
        have hJpos := jh _ hless J hJK rfl
        let R := closedComplement H univ a ∩ closedComplement H univ b
        have hR := residual_card H univ a b (mem_univ a) (mem_univ b) hne
        simp only [card_univ] at hR
        have hRlt : R.card < n := by dsimp [R]; omega
        have hRm : R.card ≤ m - 2 := by dsimp [R]; omega
        have hRa : (H.induce (R : Set α)).IsAcyclic := (hKa.anti hHK).induce _
        have hRd : ∀ x : (R : Set α), (H.induce (R : Set α)).degree x ≤ 2 := by
          intro x
          exact ((Copy.induce H (R : Set α)).degree_le x).trans
            ((degree_le_of_le hHK).trans (hKd x))
        have hRcard : Fintype.card (R : Set α) = R.card :=
          Fintype.card_of_finset' R (fun _ => Iff.rfl)
        have hRpos : 0 ≤ phi H R (m - 2) := by
          rw [← phi_subtype H R (m - 2)]
          apply ih _ hRlt (H.induce (R : Set α)) hRa hRd (m - 2)
          · simpa only [hRcard] using hRm
          · exact hRcard
        rw [phi_add_edge H univ a b (mem_univ a) (mem_univ b) hne hnab m (by simpa using hm)]
        exact add_nonneg hJpos hRpos
    exact hfill _ G hGK rfl

#print axioms finite_forest_phi_nonnegative

end D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan
