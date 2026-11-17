/- GID: D5/S3/Topology/StoneCech/DeletedSquareChromatic
   generality: G
   mirror-B: D5/B/S3/Topology/StoneCech/DeletedSquareChromatic
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The deleted square of beta Nat separates bounded cliques from finite open chromatic number. -/

import D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation
import D5.S3.Combinatorics.GroupWords.NathansonProblem9
import D5.S3.Topology.StoneCech.CountableAvoidance
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Compactness.CountablyCompact
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

/-!
# Feldman–Wilce Question 2

The topology on the deleted square is the subspace topology. Every relation
below is closed in the whole product, and finite open covers may overlap.
The countable-power implication is the standard argument of Feldman–Wilce,
Theorem 1. Its implementation here is independent of the unlicensed author
repository. The deleted-square construction follows the supplied mathematical
manuscript; the clopen separation argument is reused from PointPairSeparation.
-/

open Set Filter Topology Function
open D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation

set_option autoImplicit false

noncomputable section

namespace D5.S3.Topology.StoneCech.DeletedSquareChromatic

universe u

/-- Ordered pairs of different points, with the induced product topology. -/
def DeletedSquare (K : Type u) := {z : K × K // z.1 ≠ z.2}

instance {K : Type u} [TopologicalSpace K] : TopologicalSpace (DeletedSquare K) :=
  inferInstanceAs (TopologicalSpace {z : K × K // z.1 ≠ z.2})

instance {K : Type u} [TopologicalSpace K] [T2Space K] : T2Space (DeletedSquare K) :=
  inferInstanceAs (T2Space {z : K × K // z.1 ≠ z.2})

private theorem finite_eventually_avoid {S : Set ℕ} (hS : S.Finite) :
    ∀ᶠ n in atTop, n ∉ S := by
  obtain ⟨N, hN⟩ := hS.bddAbove
  exact eventually_atTop.mpr ⟨N + 1, fun n hn hmem => by
    have := hN hmem
    omega⟩

private theorem oriented_pool {K : Type u} [TopologicalSpace K] [T2Space K]
    [ExtremallyDisconnected K] (p q : ℕ → K) (hne : ∀ n, p n ≠ q n) :
    ∃ C : Set K, IsClopen C ∧ {n | p n ∈ C ∧ q n ∉ C}.Infinite := by
  classical
  by_contra! h
  have hagree : ∀ C : Set K, IsClopen C →
      ∀ᶠ n in atTop, (p n ∈ C ↔ q n ∈ C) := by
    intro C hC
    have h₁ := finite_eventually_avoid (h C hC)
    have h₂ := finite_eventually_avoid (h Cᶜ hC.compl)
    filter_upwards [h₁, h₂] with n hn₁ hn₂
    change ¬ (p n ∈ C ∧ q n ∉ C) at hn₁
    change ¬ (p n ∉ C ∧ ¬ q n ∉ C) at hn₂
    tauto
  obtain ⟨n, hn⟩ := (eventually_eq_of_eventually_mem_isClopen_iff p q hagree).exists
  exact hne n hn

private theorem separate_on_pool {K : Type u} [TopologicalSpace K] [T2Space K]
    [ExtremallyDisconnected K] (z : ℕ → DeletedSquare K) {I : Set ℕ} (hI : I.Infinite) :
    ∃ C : Set K, IsClopen C ∧ ∃ J : Set ℕ, J ⊆ I ∧ J.Infinite ∧
      ∀ n ∈ J, (z n).val.1 ∈ C ∧ (z n).val.2 ∉ C := by
  obtain ⟨a, ha, hIa⟩ := enumerate_pool hI
  obtain ⟨C, hC, hsep⟩ := oriented_pool
    (fun n => (z (a n)).val.1) (fun n => (z (a n)).val.2)
    (fun n => (z (a n)).property)
  refine ⟨C, hC, a '' {n | (z (a n)).val.1 ∈ C ∧ (z (a n)).val.2 ∉ C},
    ?_, hsep.image ha.injective.injOn, ?_⟩
  · rintro _ ⟨n, _, rfl⟩; exact hIa n
  · rintro _ ⟨n, hn, rfl⟩; exact hn

/-- The countable power of the deleted square of any compact Hausdorff
extremally disconnected space is countably compact. -/
theorem countablyCompactSpace_deletedSquare_power (K : Type u) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [ExtremallyDisconnected K] :
    CountablyCompactSpace (ℕ → DeletedSquare K) := by
  classical
  constructor
  apply IsCountablyCompact.of_seq_clusterPt
  intro z _
  let step (n : ℕ) (I : {I : Set ℕ // I.Infinite}) :=
    separate_on_pool (fun m => z m n) I.property
  let pools : ℕ → {I : Set ℕ // I.Infinite} :=
    fun n => Nat.rec ⟨univ, Set.infinite_univ⟩
      (fun n I => ⟨(step n I).choose_spec.2.choose,
        (step n I).choose_spec.2.choose_spec.2.1⟩) n
  let C : ℕ → Set K := fun n => (step n (pools n)).choose
  have hC : ∀ n, IsClopen (C n) := fun n => (step n (pools n)).choose_spec.1
  have hdec : ∀ n, (pools (n + 1)).val ⊆ (pools n).val :=
    fun n => (step n (pools n)).choose_spec.2.choose_spec.1
  have hsep : ∀ n m, m ∈ (pools (n + 1)).val →
      (z m n).val.1 ∈ C n ∧ (z m n).val.2 ∉ C n :=
    fun n => (step n (pools n)).choose_spec.2.choose_spec.2.2
  obtain ⟨S, hS, _, hfin⟩ := diagonal_pool (fun n => (pools n).val)
    (fun n => (pools n).property) hdec
  obtain ⟨a, ha, hSa⟩ := enumerate_pool hS
  let ambient : (ℕ → DeletedSquare K) → (ℕ → K × K) :=
    fun w j => (w j).val
  have hemb : IsEmbedding ambient := IsEmbedding.piMap (fun _ => IsEmbedding.subtypeVal)
  obtain ⟨w, _, hw⟩ := isCompact_univ.exists_mapClusterPt (f := atTop)
    (u := fun n => ambient (z (a n))) (by simp)
  have hrect (j : ℕ) : w j ∈ (C j) ×ˢ (C j)ᶜ := by
    have htail : ∀ᶠ n in atTop, a n ∈ (pools (j + 1)).val := by
      have hfinite : {n | a n ∈ S \ (pools (j + 1)).val}.Finite :=
        (hfin (j + 1)).preimage ha.injective.injOn
      filter_upwards [finite_eventually_avoid hfinite] with n hn
      exact Classical.byContradiction (fun h => hn ⟨hSa n, h⟩)
    have hwj : MapClusterPt (w j) atTop (fun n => (z (a n) j).val) :=
      MapClusterPt.continuousAt_comp
        (show ContinuousAt (fun v : ℕ → K × K => v j) w from
          (continuous_apply j).continuousAt) hw
    exact ((hC j).isClosed.prod (hC j).compl.isClosed).mem_of_mapClusterPt
      hwj (htail.mono fun n hn => hsep j (a n) hn)
  let v : ℕ → DeletedSquare K := fun j =>
    ⟨w j, fun heq => (hrect j).2 (heq ▸ (hrect j).1)⟩
  refine ⟨v, mem_univ _, ?_⟩
  apply MapClusterPt.of_comp ha.tendsto_atTop
  have hv : MapClusterPt (ambient v) atTop (ambient ∘ (z ∘ a)) := hw
  have hv' : MapClusterPt (ambient v) (map (z ∘ a) atTop) ambient := by
    simpa only [MapClusterPt, map_map] using hv
  exact hemb.isInducing.mapClusterPt_iff.mp hv'

/-- Every clique, including infinite candidate subsets, has a common finite
size bound depending on the given whole-product closed graph. -/
def BoundedCliqueProperty (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ G : SimpleGraph X, IsClosed {p : X × X | G.Adj p.1 p.2} →
    ∃ N : ℕ, ∀ S : Set X, G.IsClique S → S.Finite ∧ S.ncard ≤ N

/-- Finite open independent covers are indexed by arbitrary finite `Fin m`;
there is no disjointness condition on the cover. -/
def FiniteOpenChromaticProperty (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ G : SimpleGraph X, IsClosed {p : X × X | G.Adj p.1 p.2} →
    ∃ m : ℕ, ∃ U : Fin m → Set X, (∀ i, IsOpen (U i)) ∧
      (∀ x, ∃ i, x ∈ U i) ∧
      ∀ i x, x ∈ U i → ∀ y, y ∈ U i → ¬ G.Adj x y

private theorem cluster_sequence {X : Type u} [TopologicalSpace X]
    [CountablyCompactSpace X] (s : ℕ → X) : ∃ x, MapClusterPt x atTop s := by
  obtain ⟨x, _, hx⟩ := CountablyCompactSpace.isCountablyCompact_univ.seq_clusterPt s
    (by simp)
  exact ⟨x, hx⟩

private theorem no_infinite_clique_sequence {X : Type u} [TopologicalSpace X]
    (hc : ∀ s : ℕ → X, ∃ x, MapClusterPt x atTop s)
    (G : SimpleGraph X) (hG : IsClosed {p : X × X | G.Adj p.1 p.2})
    (s : ℕ → X) (hs : ∀ i j, i ≠ j → G.Adj (s i) (s j)) : False := by
  obtain ⟨x, hx⟩ := hc s
  have hxx : (x, x) ∈ closure {p : X × X | G.Adj p.1 p.2} := by
    apply mem_closure_iff_nhds.mpr
    intro W hW
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
    have hfreq := hx.frequently (inter_mem hU hV)
    obtain ⟨i, hi⟩ := hfreq.exists
    obtain ⟨j, hij, hj⟩ := (frequently_atTop.mp hfreq) (i + 1)
    exact ⟨(s i, s j), hUV ⟨hi.1, hj.2⟩, hs i j (by omega)⟩
  exact G.irrefl (hG.closure_eq ▸ hxx)

/-- Feldman–Wilce's countable-power criterion, for every symmetric
irreflexive relation closed in the entire product. -/
theorem boundedCliqueProperty_of_countablyCompact_power (X : Type u) [TopologicalSpace X]
    [CountablyCompactSpace (ℕ → X)] : BoundedCliqueProperty X := by
  classical
  have hc : ∀ s : ℕ → X, ∃ x, MapClusterPt x atTop s := by
    intro s
    obtain ⟨q, hq⟩ := cluster_sequence (fun n (_ : ℕ) => s n)
    exact ⟨q 0, hq.continuousAt_comp (continuous_apply 0).continuousAt⟩
  intro G hG
  have hfinite : ∀ S : Set X, G.IsClique S → S.Finite := by
    intro S hS
    by_contra hinf
    haveI : Infinite S := Set.infinite_coe_iff.mpr hinf
    let e : ℕ ↪ S := Infinite.natEmbedding S
    exact no_infinite_clique_sequence hc G hG (fun n => (e n).val)
      (fun i j hij => hS (e i).property (e j).property
        (fun h => hij (e.injective (Subtype.ext h))))
  by_contra hnone
  have hbound (n : ℕ) : ∃ S : Set X, G.IsClique S ∧ ¬ (S.Finite ∧ S.ncard ≤ n) := by
    have hn : ¬ ∀ S : Set X, G.IsClique S → S.Finite ∧ S.ncard ≤ n :=
      fun hn => hnone ⟨n, hn⟩
    by_contra hs
    apply hn
    intro S hS
    by_contra hb
    exact hs ⟨S, hS, hb⟩
  have hsupply : ∀ n : ℕ, ∃ f : Fin (n + 1) → X,
      ∀ i j, i ≠ j → G.Adj (f i) (f j) := by
    intro n
    obtain ⟨S, hS, hbad⟩ := hbound n
    have hfin := hfinite S hS
    have hlarge : n < S.ncard := by
      by_contra hn
      exact hbad ⟨hfin, by omega⟩
    letI := hfin.fintype
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Fin (n + 1)) ≤ Fintype.card S by
        simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using
          (Nat.succ_le_iff.mpr hlarge))
    exact ⟨fun i => (e i).val, fun i j hij =>
      hS (e i).property (e j).property (fun h => hij (e.injective (Subtype.ext h)))⟩
  choose f hf using hsupply
  let y : ℕ → ℕ → X := fun n j => f n ⟨min j n, by omega⟩
  obtain ⟨q, hq⟩ := cluster_sequence y
  have hqclique : ∀ i j, i ≠ j → G.Adj (q i) (q j) := by
    intro i j hij
    have hcont : Continuous (fun w : ℕ → X => (w i, w j)) :=
      (continuous_apply i).prodMk (continuous_apply j)
    apply hG.mem_of_mapClusterPt (hq.continuousAt_comp hcont.continuousAt)
    filter_upwards [eventually_ge_atTop (max i j)] with n hn
    apply hf n
    intro heq
    have := congrArg Fin.val heq
    simp only [min_eq_left (le_trans (le_max_left _ _) hn),
      min_eq_left (le_trans (le_max_right _ _) hn)] at this
    exact hij this
  exact no_infinite_clique_sequence hc G hG q hqclique

/-- The graph of the coordinate swap, expressed by two ambient equalities. -/
def swapGraph (K : Type u) : SimpleGraph (DeletedSquare K) where
  Adj x y := x.val.1 = y.val.2 ∧ x.val.2 = y.val.1
  symm.symm := fun _ _ h => ⟨h.2.symm, h.1.symm⟩
  loopless.irrefl := fun x h => x.property h.1

private theorem isClosed_swapGraph (K : Type u) [TopologicalSpace K] [T2Space K] :
    IsClosed {p : DeletedSquare K × DeletedSquare K | (swapGraph K).Adj p.1 p.2} :=
  (isClosed_eq (continuous_subtype_val.fst.comp continuous_fst)
    (continuous_subtype_val.snd.comp continuous_snd)).inter
  (isClosed_eq (continuous_subtype_val.snd.comp continuous_fst)
    (continuous_subtype_val.fst.comp continuous_snd))

private def principalPair (a b : ℕ) (hab : a ≠ b) : DeletedSquare (Ultrafilter ℕ) :=
  ⟨(pure a, pure b), fun h => hab (Ultrafilter.pure_injective h)⟩

private def membershipPattern {m : ℕ} (U : Fin m → Set (DeletedSquare (Ultrafilter ℕ)))
    (a b : ℕ) : Set (Fin m) := {i | ∃ h : a ≠ b, principalPair a b h ∈ U i}

private theorem mem_pattern_iff {m : ℕ} (U : Fin m → Set (DeletedSquare (Ultrafilter ℕ)))
    (a b : ℕ) (hab : a ≠ b) (i : Fin m) :
    i ∈ membershipPattern U a b ↔ principalPair a b hab ∈ U i := by
  constructor
  · rintro ⟨h, hi⟩; exact hi
  · intro hi; exact ⟨hab, hi⟩

private theorem homogeneous_patterns {m : ℕ}
    (U : Fin m → Set (DeletedSquare (Ultrafilter ℕ))) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ P Q : Set (Fin m),
      ∀ a ∈ A, ∀ b ∈ A, a < b →
        membershipPattern U a b = P ∧ membershipPattern U b a = Q := by
  classical
  let color (s : Finset ℕ) : Set (Fin m) × Set (Fin m) :=
    if hs : s.Nonempty then
      (membershipPattern U (s.min' hs) (s.max' hs),
        membershipPattern U (s.max' hs) (s.min' hs)) else (∅, ∅)
  obtain ⟨A, _, hA, col, hcol⟩ := infinite_ramsey 2 color Set.infinite_univ
  refine ⟨A, hA, col.1, col.2, ?_⟩
  intro a ha b hb hab
  have hsub : (↑({a, b} : Finset ℕ) : Set ℕ) ⊆ A := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl <;> assumption
  have hcard : ({a, b} : Finset ℕ).card = 2 := by simp [hab.ne]
  have heq := hcol {a, b} hsub hcard
  have heq' : (membershipPattern U a b, membershipPattern U b a) = col := by
    simpa [color, Finset.min'_pair, Finset.max'_pair, min_eq_left hab.le,
      max_eq_right hab.le] using heq
  exact ⟨congrArg Prod.fst heq', congrArg Prod.snd heq'⟩

private theorem free_on_support {A : Set ℕ} (hA : A.Infinite) :
    ∃ p : Ultrafilter ℕ, (p : Filter ℕ) ≤ cofinite ∧ A ∈ p := by
  haveI : (cofinite ⊓ 𝓟 A : Filter ℕ).NeBot := cofinite_inf_principal_neBot_iff.mpr hA
  let p := Ultrafilter.of (cofinite ⊓ 𝓟 A)
  have hp : (p : Filter ℕ) ≤ cofinite ⊓ 𝓟 A := Ultrafilter.of_le _
  exact ⟨p, hp.trans inf_le_left, (hp.trans inf_le_right) (by simp)⟩

private theorem infinite_of_free_mem {p : Ultrafilter ℕ} (hp : (p : Filter ℕ) ≤ cofinite)
    {B : Set ℕ} (hB : B ∈ p) : B.Infinite := by
  intro hfin
  exact p.neBot.ne (empty_mem_iff_bot.mp (by
    simpa using inter_mem hB (hp hfin.compl_mem_cofinite)))

private theorem basic_rectangle {p q : Ultrafilter ℕ} (hne : p ≠ q)
    {U : Set (DeletedSquare (Ultrafilter ℕ))} (hU : IsOpen U)
    (hpq : (⟨(p, q), hne⟩ : DeletedSquare (Ultrafilter ℕ)) ∈ U) :
    ∃ B C : Set ℕ, B ∈ p ∧ C ∈ q ∧
      ∀ (r s : Ultrafilter ℕ) (hrs : r ≠ s), B ∈ r → C ∈ s →
        (⟨(r, s), hrs⟩ : DeletedSquare (Ultrafilter ℕ)) ∈ U := by
  obtain ⟨O, hO, hOU⟩ := (IsInducing.subtypeVal.isOpen_iff).mp hU
  have hpqO : (p, q) ∈ O := by
    exact (Set.ext_iff.mp hOU ⟨(p, q), hne⟩).mpr hpq
  obtain ⟨V, W, hV, hW, hpV, hqW, hVW⟩ := isOpen_prod_iff.mp hO p q hpqO
  obtain ⟨VB, ⟨B, rfl⟩, hpB, hBV⟩ := ultrafilterBasis_is_basis.isOpen_iff.mp hV p hpV
  obtain ⟨WC, ⟨C, rfl⟩, hqC, hCW⟩ := ultrafilterBasis_is_basis.isOpen_iff.mp hW q hqW
  refine ⟨B, C, hpB, hqC, ?_⟩
  intro r s hrs hBr hCs
  exact (Set.ext_iff.mp hOU ⟨(r, s), hrs⟩).mp (hVW ⟨hBV hBr, hCW hCs⟩)

/-- No finite open independent cover of the deleted square exists for its
swap graph, even when the proposed cover is allowed to overlap. -/
theorem no_finite_open_independent_cover (m : ℕ)
    (U : Fin m → Set (DeletedSquare (Ultrafilter ℕ)))
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hind : ∀ i x, x ∈ U i → ∀ y, y ∈ U i → ¬ (swapGraph (Ultrafilter ℕ)).Adj x y) :
    False := by
  classical
  obtain ⟨A, hA, P, Q, hhom⟩ := homogeneous_patterns U
  have hPQ : Disjoint P Q := by
    obtain ⟨a, ha⟩ := hA.nonempty
    obtain ⟨b, hb, hab⟩ := hA.exists_gt a
    obtain ⟨hP, hQ⟩ := hhom a ha b hb hab
    apply disjoint_left.mpr
    intro i hiP hiQ
    have hiab : principalPair a b hab.ne ∈ U i :=
      (mem_pattern_iff U a b hab.ne i).mp (hP ▸ hiP)
    have hiba : principalPair b a hab.ne.symm ∈ U i :=
      (mem_pattern_iff U b a hab.ne.symm i).mp (hQ ▸ hiQ)
    exact hind i _ hiab _ hiba ⟨rfl, rfl⟩
  obtain ⟨A₀, A₁, hA₀A, hA₁A, hA₀, hA₁, hdis⟩ := split_pool hA
  obtain ⟨p, hp, hA₀p⟩ := free_on_support hA₀
  obtain ⟨q, hq, hA₁q⟩ := free_on_support hA₁
  have hpq : p ≠ q := by
    intro heq
    have hA₁p : A₁ ∈ p := heq ▸ hA₁q
    have hempty : (∅ : Set ℕ) ∈ p := by
      simpa [Set.disjoint_iff_inter_eq_empty.mp hdis] using inter_mem hA₀p hA₁p
    exact p.neBot.ne (empty_mem_iff_bot.mp hempty)
  obtain ⟨i, hi⟩ := hcover ⟨(p, q), hpq⟩
  obtain ⟨B₀, C₀, hB₀, hC₀, hrect⟩ := basic_rectangle hpq (hopen i) hi
  let B := B₀ ∩ A₀
  let C := C₀ ∩ A₁
  have hB : B.Infinite := infinite_of_free_mem hp (inter_mem hB₀ hA₀p)
  have hC : C.Infinite := infinite_of_free_mem hq (inter_mem hC₀ hA₁q)
  have hBA : B ⊆ A := fun _ h => hA₀A h.2
  have hCA : C ⊆ A := fun _ h => hA₁A h.2
  have hinside : ∀ b ∈ B, ∀ c ∈ C, ∀ hbc : b ≠ c,
      principalPair b c hbc ∈ U i := by
    intro b hb c hc hbc
    exact hrect (pure b) (pure c)
      (fun h => hbc (Ultrafilter.pure_injective h))
      (Ultrafilter.mem_pure.mpr hb.1) (Ultrafilter.mem_pure.mpr hc.1)
  obtain ⟨b, hb⟩ := hB.nonempty
  obtain ⟨c, hc, hbc⟩ := hC.exists_gt b
  have hiP : i ∈ P := by
    rw [← (hhom b (hBA hb) c (hCA hc) hbc).1]
    exact (mem_pattern_iff U b c hbc.ne i).mpr (hinside b hb c hc hbc.ne)
  obtain ⟨c', hc'⟩ := hC.nonempty
  obtain ⟨b', hb', hcb'⟩ := hB.exists_gt c'
  have hiQ : i ∈ Q := by
    rw [← (hhom c' (hCA hc') b' (hBA hb') hcb').2]
    exact (mem_pattern_iff U b' c' hcb'.ne.symm i).mpr
      (hinside b' hb' c' hc' hcb'.ne.symm)
  exact disjoint_left.mp hPQ hiP hiQ

/-- The concrete ZFC witness for the strictness in Feldman–Wilce Question 2.
Hausdorffness and the universal bounded-clique property coexist with failure
of the finite-open-chromatic property. -/
theorem result :
    T2Space (DeletedSquare (Ultrafilter ℕ)) ∧
    BoundedCliqueProperty (DeletedSquare (Ultrafilter ℕ)) ∧
    ¬ FiniteOpenChromaticProperty (DeletedSquare (Ultrafilter ℕ)) := by
  letI : ExtremallyDisconnected (StoneCech ℕ) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  letI : ExtremallyDisconnected (Ultrafilter ℕ) :=
    extremallyDisconnected_of_homeo (CountableAvoidance.ultrafilterHomeomorph (α := ℕ)).symm
  letI := countablyCompactSpace_deletedSquare_power (Ultrafilter ℕ)
  refine ⟨inferInstance, boundedCliqueProperty_of_countablyCompact_power _, ?_⟩
  intro h
  obtain ⟨m, U, hopen, hcover, hind⟩ := h (swapGraph (Ultrafilter ℕ))
    (isClosed_swapGraph (Ultrafilter ℕ))
  exact no_finite_open_independent_cover m U hopen hcover hind

#print axioms countablyCompactSpace_deletedSquare_power
#print axioms boundedCliqueProperty_of_countablyCompact_power
#print axioms no_finite_open_independent_cover
#print axioms result

end D5.S3.Topology.StoneCech.DeletedSquareChromatic
