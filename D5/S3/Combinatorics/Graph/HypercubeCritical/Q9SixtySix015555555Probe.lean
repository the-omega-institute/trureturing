import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixAgreementCapacityProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixProfilesAfterAgreementProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixTopTripleCutProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TopTripleCountProbe

/-! The top triples in a deficit-one true slice of the nine-cube. -/

set_option autoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
local notation "flip_flip" => BalancedCriticalSpectrum.flip_flip
attribute [local instance] Classical.propDecidable
open private directions mem_directions regular_directions exterior_even from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private sum_cube_membership_property from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe

private def heavySupport (x : Q 9) : Finset (Fin 7) :=
  univ.filter fun i => x i.succ.succ = true

private def sliceVertex (b : Bool × Bool) (s : Finset (Fin 7)) : Q 9 :=
  Fin.cases b.1 (Fin.cases b.2 (fun i => decide (i ∈ s)))

private lemma heavySupport_sliceVertex (b : Bool × Bool) (s : Finset (Fin 7)) :
    heavySupport (sliceVertex b s) = s := by
  ext i
  simp [heavySupport, sliceVertex]

private lemma sliceVertex_heavySupport (x : Q 9) (hx : x 1 = true) :
    sliceVertex (x 0, true) (heavySupport x) = x := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases hx.symm (fun k => ?_) j
  change decide (k ∈ heavySupport x) = x k.succ.succ
  cases h : x k.succ.succ <;> simp [heavySupport, h]

private lemma sliceVertex_injective (b : Bool × Bool) : Function.Injective (sliceVertex b) := by
  intro s t h
  simpa only [heavySupport_sliceVertex] using congrArg heavySupport h

private lemma flip_heavy_erase (b : Bool × Bool) {s : Finset (Fin 7)} {i : Fin 7}
    (hi : i ∈ s) :
    flip (sliceVertex b s) i.succ.succ = sliceVertex b (s.erase i) := by
  funext j
  refine Fin.cases (by
    rw [BalancedCriticalSpectrum.flip, Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rfl) (fun k => ?_) j
  refine Fin.cases (by
    have hn : (0 : Fin 8).succ ≠ i.succ.succ := fun e =>
      (Fin.succ_ne_zero i).symm (Fin.succ_inj.mp e)
    rw [BalancedCriticalSpectrum.flip, Function.update_of_ne hn]
    rfl) (fun k => ?_) k
  by_cases h : k = i
  · subst k
    simp [BalancedCriticalSpectrum.flip, sliceVertex, hi]
  · simp [BalancedCriticalSpectrum.flip, sliceVertex, h]

private lemma flip_heavy_insert (b : Bool × Bool) {s : Finset (Fin 7)} {i : Fin 7}
    (hi : i ∉ s) :
    flip (sliceVertex b s) i.succ.succ = sliceVertex b (insert i s) := by
  have h := congrArg (fun x => flip x i.succ.succ) (flip_heavy_erase b (mem_insert_self i s))
  simpa only [flip_flip, erase_insert hi] using h.symm

private def heavyDirection : Fin 7 ↪ Fin 9 :=
  ⟨fun i => i.succ.succ, fun _ _ h => Fin.succ_inj.mp (Fin.succ_inj.mp h)⟩

@[simp] private lemma heavyDirection_apply (i : Fin 7) :
    heavyDirection i = i.succ.succ := rfl

private lemma slice_top_directions {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (b : Bool × Bool) {s : Finset (Fin 7)} (h3 : s.card = 3) (hs : sliceVertex b s ∈ C)
    (hforced : ∀ i ∈ s, flip (sliceVertex b s) i.succ.succ ∈ C) :
    directions C (sliceVertex b s) = s.map heavyDirection := by
  classical
  symm
  apply eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hj
    exact (mem_directions C _ _).mpr (hforced i hi)
  · rw [card_map, h3, regular_directions C hr hs]

private lemma four_directions {C : Finset (Q 9)}
    (hCap : ∀ x ∈ C, lastSevenWeight x ≤ 3)
    (b : Bool × Bool) {s : Finset (Fin 7)} (h4 : s.card = 4) :
    directions C (sliceVertex b s) =
      ((s.filter fun i => sliceVertex b (s.erase i) ∈ C).map heavyDirection) := by
  classical
  have exclude {y : Q 9} (he : heavySupport y = s) : y ∉ C := by
    intro hy
    have hw := hCap y hy
    change (heavySupport y).card ≤ 3 at hw
    rw [he, h4] at hw
    omega
  have unchanged (j : Fin 9) (hj : ∀ i : Fin 7, i.succ.succ ≠ j) :
      heavySupport (flip (sliceVertex b s) j) = s := by
    calc
      _ = heavySupport (sliceVertex b s) := by
        unfold heavySupport
        apply filter_congr
        intro i _
        rw [BalancedCriticalSpectrum.flip, Function.update_of_ne (hj i)]
      _ = s := heavySupport_sliceVertex b s
  have hzero : flip (sliceVertex b s) 0 ∉ C :=
    exclude (unchanged 0 fun i => Fin.succ_ne_zero i.succ)
  have hone : flip (sliceVertex b s) 1 ∉ C :=
    exclude (unchanged 1 Fin.succ_succ_ne_one)
  ext j
  refine Fin.cases (by simp [mem_directions, hzero]) (fun k => ?_) j
  refine Fin.cases (by simp [mem_directions, hone, Fin.succ_succ_ne_one]) (fun i => ?_) k
  by_cases hi : i ∈ s
  · simp [mem_directions, hi, flip_heavy_erase b hi]
  · have hnot : flip (sliceVertex b s) i.succ.succ ∉ C := by
      rw [flip_heavy_insert b hi]
      intro h
      have hc := hCap _ h
      change (heavySupport (sliceVertex b (insert i s))).card ≤ 3 at hc
      rw [heavySupport_sliceVertex, card_insert_of_notMem hi, h4] at hc
      omega
    simp [mem_directions, hi, hnot]

private lemma no_three_top_in_four {C : Finset (Q 9)} (hb : IsBalanced C)
    (b : Bool × Bool) {s : Finset (Fin 7)} {i j k : Fin 7}
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsel : ∀ d ∈ s, sliceVertex b (s.erase d) ∈ C →
      ∀ e ∈ s.erase d, flip (sliceVertex b (s.erase d)) e.succ.succ ∈ C)
    (hI : sliceVertex b (s.erase i) ∈ C) (hJ : sliceVertex b (s.erase j) ∈ C)
    (hK : sliceVertex b (s.erase k) ∈ C) : False := by
  let x := sliceVertex b s
  let I := i.succ.succ
  let J := j.succ.succ
  let K := k.succ.succ
  have hIJ : I ≠ J := fun h => hij (heavyDirection.injective h)
  have hIK : I ≠ K := fun h => hik (heavyDirection.injective h)
  have hJK : J ≠ K := fun h => hjk (heavyDirection.injective h)
  have hxi : flip x I ∈ C := (flip_heavy_erase b hi).symm ▸ hI
  have hxj : flip x J ∈ C := (flip_heavy_erase b hj).symm ▸ hJ
  have hxk : flip x K ∈ C := (flip_heavy_erase b hk).symm ▸ hK
  have hxij : flip (flip x I) J ∈ C := by
    rw [show flip x I = sliceVertex b (s.erase i) from flip_heavy_erase b hi]
    exact hsel i hi hI j (mem_erase.mpr ⟨hij.symm, hj⟩)
  have hxik : flip (flip x I) K ∈ C := by
    rw [show flip x I = sliceVertex b (s.erase i) from flip_heavy_erase b hi]
    exact hsel i hi hI k (mem_erase.mpr ⟨hik.symm, hk⟩)
  have ej : flip (flip (flip x I) J) I = flip x J := by
    rw [flip_comm x I J, flip_flip]
  have ek : flip (flip (flip x I) K) I = flip x K := by
    rw [flip_comm x I K, flip_flip]
  have hxjk : flip (flip x J) K ∈ C := by
    rw [show flip x J = sliceVertex b (s.erase j) from flip_heavy_erase b hj]
    exact hsel j hj hJ k (mem_erase.mpr ⟨hjk.symm, hk⟩)
  apply hJK
  exact BalancedCubeGirth.three_step_first_direction_eq hb hIJ.symm hIK hIK.symm hIJ
    hxi hxij (ej.symm ▸ hxj) (by rw [ej]; exact hxjk)
    hxik (ek.symm ▸ hxk) (by rw [ek, flip_comm x K J]; exact hxjk)
    (by rw [ej, ek, flip_comm x J K])

private lemma one_more_coordinate {p t : Finset (Fin 7)}
    (hpt : p ⊆ t) (hc : t.card = p.card + 1) :
    ∃ i ∈ t, i ∉ p ∧ t.erase i = p := by
  have hd : (t \ p).card = 1 := by rw [card_sdiff_of_subset hpt, hc]; omega
  obtain ⟨i, hi⟩ := card_eq_one.mp hd
  have hmem : i ∈ t \ p := by rw [hi]; simp
  obtain ⟨hit, hip⟩ := mem_sdiff.mp hmem
  refine ⟨i, hit, hip, eq_of_subset_of_card_le ?_ ?_⟩
  · intro z hz
    by_contra hzp
    have hzs : z ∈ t \ p := mem_sdiff.mpr ⟨(mem_erase.mp hz).2, hzp⟩
    rw [hi, mem_singleton] at hzs
    exact (mem_erase.mp hz).1 hzs
  · rw [card_erase_of_mem hit, hc, Nat.add_sub_cancel]

open Classical in
private noncomputable def topFamily (C : Finset (Q 9)) (b : Bool × Bool)
    (H : Finset (Fin 7)) :
    Finset (Finset (Fin 7)) :=
  (H.powersetCard 3).filter fun s => sliceVertex b s ∈ C

private lemma mem_topFamily {C : Finset (Q 9)} {b : Bool × Bool} {H s : Finset (Fin 7)} :
    s ∈ topFamily C b H ↔ s ⊆ H ∧ s.card = 3 ∧ sliceVertex b s ∈ C := by
  classical
  simp [topFamily, mem_powersetCard, and_assoc]

private lemma topFamily_four {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hCap : ∀ x ∈ C, lastSevenWeight x ≤ 3)
    (b : Bool × Bool) (H : Finset (Fin 7))
    (hforced : ∀ s ∈ topFamily C b H, ∀ i ∈ s, flip (sliceVertex b s) i.succ.succ ∈ C)
    (s : Finset (Fin 7)) (h4 : s.card = 4) (hsH : s ⊆ H) :
    Even ((topFamily C b H).filter (· ⊆ s)).card ∧
      ((topFamily C b H).filter (· ⊆ s)).card ≤ 2 := by
  classical
  let D := s.filter fun i => sliceVertex b (s.erase i) ∈ C
  have hcard : D.card = ((topFamily C b H).filter (· ⊆ s)).card := by
    apply card_bij (fun i _ => s.erase i)
    · intro i hi
      obtain ⟨his, hiC⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨mem_topFamily.mpr ⟨(erase_subset _ _).trans hsH,
        by rw [card_erase_of_mem his, h4], hiC⟩, erase_subset _ _⟩
    · intro i hi j hj he
      by_contra hne
      have hm := mem_erase.mpr ⟨hne, (mem_filter.mp hi).1⟩
      rw [← he] at hm
      exact (notMem_erase i s) hm
    · intro t ht
      obtain ⟨htT, hts⟩ := mem_filter.mp ht
      obtain ⟨_, ht3, htC⟩ := mem_topFamily.mp htT
      obtain ⟨i, his, _, he⟩ := one_more_coordinate hts (by rw [h4, ht3])
      exact ⟨i, mem_filter.mpr ⟨his, he.symm ▸ htC⟩, he⟩
  rw [← hcard]
  constructor
  · have hnot : sliceVertex b s ∉ C := by
      intro h
      have hc := hCap _ h
      change (heavySupport (sliceVertex b s)).card ≤ 3 at hc
      rw [heavySupport_sliceVertex, h4] at hc
      omega
    have he := exterior_even C hr hb _ hnot
    rw [four_directions hCap b h4, card_map] at he
    exact he
  · by_contra! h
    obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := two_lt_card.mp h
    obtain ⟨his, hiC⟩ := mem_filter.mp hi
    obtain ⟨hjs, hjC⟩ := mem_filter.mp hj
    obtain ⟨hks, hkC⟩ := mem_filter.mp hk
    refine no_three_top_in_four hb b his hjs hks hij hik hjk (fun d hd hC => ?_) hiC hjC hkC
    exact hforced _ (mem_topFamily.mpr
      ⟨(erase_subset _ _).trans hsH, by rw [card_erase_of_mem hd, h4], hC⟩)

private lemma topFamily_pair {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (b : Bool × Bool) (H : Finset (Fin 7))
    (hforced : ∀ s ∈ topFamily C b H, ∀ i ∈ s, flip (sliceVertex b s) i.succ.succ ∈ C)
    (p : Finset (Fin 7)) (h2 : p.card = 2) :
    ((topFamily C b H).filter (p ⊆ ·)).card ≤ 3 := by
  classical
  let U := (topFamily C b H).filter (p ⊆ ·)
  change U.card ≤ 3
  by_cases hU : U.Nonempty
  · have hcoord (t : Finset (Fin 7)) (ht : t ∈ U) :
        ∃ i ∈ t, i ∉ p ∧ t.erase i = p := by
      obtain ⟨htT, hpt⟩ := mem_filter.mp ht
      exact one_more_coordinate hpt (by rw [(mem_topFamily.mp htT).2.1, h2])
    obtain ⟨t, ht⟩ := hU
    obtain ⟨i, hi, _, he⟩ := hcoord t ht
    have hp : sliceVertex b p ∈ C := by
      have hf := hforced _ (mem_filter.mp ht).1 i hi
      rwa [flip_heavy_erase b hi, he] at hf
    choose f hfmem hfout hferase using hcoord
    have hins (u : Finset (Fin 7)) (hu : u ∈ U) : insert (f u hu) p = u := by
      rw [← hferase u hu, insert_erase (hfmem u hu)]
    calc
      U.card ≤ (directions C (sliceVertex b p)).card := by
        rw [← card_attach (s := U)]
        apply card_le_card_of_injOn (fun a : U => heavyDirection (f a.val a.property))
        · intro a _
          apply (mem_directions C _ _).mpr
          change flip (sliceVertex b p) (f a.val a.property).succ.succ ∈ C
          rw [flip_heavy_insert b (hfout a.val a.property), hins _ _]
          exact (mem_topFamily.mp (mem_filter.mp a.property).1).2.2
        · intro a _ a' _ h
          apply Subtype.ext
          rw [← hins a.val a.property, ← hins a'.val a'.property, heavyDirection.injective h]
      _ = 3 := regular_directions C hr hp
  · rw [not_nonempty_iff_eq_empty.mp hU, card_empty]
    decide

private lemma slice_count {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hCap : ∀ x ∈ C, lastSevenWeight x ≤ 3)
    (b : Bool) (hT : (topFamily C (b, true) univ).Nonempty)
    (hforced : ∀ s ∈ topFamily C (b, true) univ, ∀ i ∈ s, flip (sliceVertex (b, true) s) i.succ.succ ∈ C) :
    18 ≤ (C.filter fun x => x 0 = b ∧ x 1 = true).card := by
  classical
  let T := topFamily C (b, true) univ
  let P := (univ.powersetCard 2 : Finset (Finset (Fin 7))).filter
    fun p => sliceVertex (b, true) p ∈ C
  have hP (p : Finset (Fin 7)) : p ∈ P ↔ p.card = 2 ∧ sliceVertex (b, true) p ∈ C := by
    simp [P, mem_powersetCard]
  have ht : 9 ≤ T.card := nine_le_top_triple_family (by decide) T
    (fun t ht => (mem_topFamily.mp ht).2.1) hT
    (fun s hs => topFamily_four hr hb hCap (b, true) univ hforced s hs (subset_univ _))
    (topFamily_pair hr (b, true) univ hforced)
  have hp (p : Finset (Fin 7)) (h : p ∈ P) : (T.filter (p ⊆ ·)).card ≤ 3 :=
    topFamily_pair hr (b, true) univ hforced p ((hP p).mp h).1
  have hcount (t : Finset (Fin 7)) (ht : t ∈ T) : (P.filter (· ⊆ t)).card = 3 := by
    have h3 := (mem_topFamily.mp ht).2.1
    have he : P.filter (· ⊆ t) = t.powersetCard 2 := by
      ext p
      rw [mem_filter, hP, mem_powersetCard]
      refine ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, ?_⟩, h.1⟩⟩
      obtain ⟨i, hi, _, he⟩ := one_more_coordinate h.1 (by rw [h3, h.2])
      simpa only [flip_heavy_erase (b, true) hi, he] using hforced t ht i hi
    rw [he, card_powersetCard, h3]
    decide
  have hdouble : (∑ t ∈ T, (P.filter (· ⊆ t)).card) = ∑ p ∈ P, (T.filter (p ⊆ ·)).card := by
    simp only [card_filter]
    exact sum_comm
  have hu : (∑ p ∈ P, (T.filter (p ⊆ ·)).card) ≤ ∑ _ ∈ P, (3 : ℕ) := sum_le_sum hp
  rw [← hdouble, sum_const_nat hcount, sum_const_nat (fun _ _ => rfl)] at hu
  have hdisjoint : Disjoint T P := by
    apply disjoint_left.mpr
    intro s hs hp
    have h3 := (mem_topFamily.mp hs).2.1
    have h2 := ((hP s).mp hp).1
    omega
  have hinj : (T ∪ P).card ≤ (C.filter fun x => x 0 = b ∧ x 1 = true).card := by
    apply card_le_card_of_injOn (sliceVertex (b, true)) _ (sliceVertex_injective (b, true)).injOn
    intro t h
    have hmem : sliceVertex (b, true) t ∈ C := (mem_union.mp h).elim
      (fun h => (mem_topFamily.mp h).2.2) (fun h => ((hP t).mp h).2)
    exact mem_filter.mpr ⟨hmem, rfl, rfl⟩
  rw [card_union_of_disjoint hdisjoint] at hinj
  omega

private def deficit : Fin 9 → ℤ := Fin.cases 0 (Fin.cases 1 (fun _ : Fin 7 => 5))

private lemma weight_formula (x : Q 9) :
    (∑ i, if x i = true then deficit i else 0) =
      (if x 1 = true then 1 else 0) + 5 * (lastSevenWeight x : ℤ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, mul_comm]
  have he (i : Fin 7) : (if x i.succ.succ = true then deficit i.succ.succ else 0) =
      (if x i.succ.succ = true then (1 : ℤ) else 0) * 5 := by
    cases x i.succ.succ <;> simp [deficit]
  simp only [he, ← sum_mul, lastSevenWeight, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  have hzero : (if x (0 : Fin 9) = true then deficit 0 else 0) = 0 := by simp [deficit]
  rw [hzero, zero_add]
  change (if x 1 = true then 1 else 0) + _ = _
  rfl

private lemma heavy_distance_le_weights (x y : Q 9) :
    (univ.filter fun i : Fin 7 => x i.succ.succ ≠ y i.succ.succ).card ≤
      lastSevenWeight x + lastSevenWeight y := by
  classical
  simp only [lastSevenWeight, card_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  cases x i.succ.succ <;> cases y i.succ.succ <;> decide

private lemma partner_opposite_slice {x y : Q 9} (hx1 : x 1 = true) (hy1 : y 1 = true)
    (hdist : hammingDist x y = 7) (hx3 : lastSevenWeight x = 3)
    (hy3 : lastSevenWeight y ≤ 3) : x 0 ≠ y 0 ∧ lastSevenWeight y = 3 := by
  have h := heavy_distance_le_weights x y
  simp only [hammingDist, card_filter] at hdist
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hdist
  change (if x 0 ≠ y 0 then 1 else 0) + ((if x 1 ≠ y 1 then 1 else 0) + _) = 7 at hdist
  rw [hx1, hy1] at hdist
  have hd : (if x 0 ≠ y 0 then 1 else 0) +
      (univ.filter fun i : Fin 7 => x i.succ.succ ≠ y i.succ.succ).card = 7 := by
    simpa [card_filter] using hdist
  by_cases he : x 0 = y 0
  · rw [ite_eq_right (not_not.mpr he), zero_add] at hd
    omega
  · rw [ite_eq_left he] at hd
    exact ⟨he, by omega⟩

/-- A Huang-balanced induced cubic support of size 66 cannot have the
normalized coordinate deficits 015555555. -/
theorem q9_sixty_six_excludes_015555555 {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) +
      2 * (![0, 1, 5, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) i = 33) : False := by
  classical
  have hr_eq : deficit = ![0, 1, 5, 5, 5, 5, 5, 5, 5] := by decide +kernel
  rw [← hr_eq] at hhalf
  have hr_sum : (∑ i, deficit i) = 36 := by decide +kernel
  have hr_nonneg : ∀ i, 0 ≤ deficit i := by decide +kernel
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hr hb
  have hweight (x : Q 9) (hx : x ∈ C) :=
    coordinate_profile_weight_bound hC hr hb (fun _ => true) deficit hhalf hx
  simp only [weight_formula, hr_sum] at hweight
  have hcap (x : Q 9) (hx : x ∈ C) : lastSevenWeight x ≤ 3 := by
    have hw := hweight x hx
    have hs := sixty_six_distance_seven_le_eight hC hr hb hd hx
    split at hw <;> omega
  have h8 (x : Q 9) (hx : x ∈ C) (hx1 : x 1 = true) (hx3 : lastSevenWeight x = 3) :
      (shell C x 7).card = 8 := by
    have hw := hweight x hx
    rw [hx3, ite_eq_left hx1] at hw
    have hs := sixty_six_distance_seven_le_eight hC hr hb hd hx
    omega
  have hlow : (C.filter fun x => x 1 = true).card = 31 := by
    have h := hhalf 1
    change _ + 2 * (1 : ℤ) = 33 at h
    omega
  have hheavy (i : Fin 7) : (C.filter fun x => x i.succ.succ = true).card = 23 := by
    have h := hhalf i.succ.succ
    change _ + 2 * (5 : ℤ) = 33 at h
    omega
  have hforced (b : Bool) (s : Finset (Fin 7)) (hs : s ∈ topFamily C (b, true) univ)
      (i : Fin 7) (hi : i ∈ s) : flip (sliceVertex (b, true) s) i.succ.succ ∈ C := by
    obtain ⟨_, hs3, hsel⟩ := mem_topFamily.mp hs
    have hw : lastSevenWeight (sliceVertex (b, true) s) = 3 := by
      change (heavySupport (sliceVertex (b, true) s)).card = 3
      rw [heavySupport_sliceVertex, hs3]
    have htrue : sliceVertex (b, true) s i.succ.succ = true := by simpa [sliceVertex] using hi
    exact eight_partners_force_minority_directions_used hC hr hb hd
      (fun _ => true) deficit hhalf hr_nonneg hsel (h8 _ hsel rfl hw) htrue
      (show (2 : ℤ) ≤ 5 by decide)
  obtain ⟨x, hx, hx1, hx3⟩ := q9_top_triple_on_deficit_one_true_side hC hr hb hheavy hlow hcap
  have hxSlice := sliceVertex_heavySupport x hx1
  have htx : heavySupport x ∈ topFamily C (x 0, true) univ := mem_topFamily.mpr ⟨subset_univ _, hx3, by rwa [hxSlice]⟩
  have hno : flip x 1 ∉ C := by
    intro hf
    have hm := (mem_directions C _ _).mpr hf
    have h3 : (heavySupport x).card = 3 := hx3
    have he := slice_top_directions hr (x 0, true) h3 (mem_topFamily.mp htx).2.2
      (hforced (x 0) _ htx)
    rw [hxSlice] at he
    rw [he] at hm
    obtain ⟨i, _, hi⟩ := mem_map.mp hm
    exact (Fin.succ_ne_zero i) (Fin.succ_inj.mp hi)
  have hag := (cube_lifted_agreement_capacity hr hb hd x 1).2 (h8 x hx hx1 hx3)
  simp only [cubePairMembership, show cubeMembership C x = 1 by simp [cubeMembership, hx],
    show cubeMembership C (flip x 1) = 0 by simp [cubeMembership, hno], mul_zero, sub_zero,
    mul_one, one_mul, sum_cube_membership_property] at hag
  have hpos : 0 < (C.filter fun y => hammingDist x y = 7 ∧ x 1 = y 1).card := by omega
  obtain ⟨y, hy⟩ := card_pos.mp hpos
  obtain ⟨hyC, hyDist, hy1⟩ := mem_filter.mp hy
  have hy1' := hy1.symm.trans hx1
  obtain ⟨hopp, hy3⟩ := partner_opposite_slice hx1 hy1' hyDist hx3 (hcap y hyC)
  have hty : heavySupport y ∈ topFamily C (y 0, true) univ :=
    mem_topFamily.mpr ⟨subset_univ _, hy3, by rwa [sliceVertex_heavySupport y hy1']⟩
  have hleft := slice_count hr hb hcap (x 0) ⟨_, htx⟩ (hforced (x 0))
  have hright := slice_count hr hb hcap (y 0) ⟨_, hty⟩ (hforced (y 0))
  have hdj : Disjoint (C.filter fun v => v 0 = x 0 ∧ v 1 = true)
      (C.filter fun v => v 0 = y 0 ∧ v 1 = true) := by
    apply disjoint_left.mpr
    intro v hv hw
    exact hopp ((mem_filter.mp hv).2.1.symm.trans (mem_filter.mp hw).2.1)
  have hu : (C.filter fun v => v 0 = x 0 ∧ v 1 = true) ∪
      (C.filter fun v => v 0 = y 0 ∧ v 1 = true) ⊆ C.filter (fun v => v 1 = true) := by
    intro v hv
    rcases mem_union.mp hv with h | h
    all_goals exact mem_filter.mpr ⟨(mem_filter.mp h).1, (mem_filter.mp h).2.2⟩
  have hk := card_le_card hu
  rw [card_union_of_disjoint hdj, hlow] at hk
  omega

#print axioms q9_sixty_six_excludes_015555555

def sixtySixProfilesAfterTopTriples : List (List ℤ) :=
  sixtySixProfilesAfterAgreement.filter (· != [0, 1, 5, 5, 5, 5, 5, 5, 5])

-- Reduction evaluates the preceding profile filters as well as this deletion.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
theorem sixtySixProfilesAfterTopTriples_length : sixtySixProfilesAfterTopTriples.length = 37 := by
  decide +kernel

open Classical in
theorem q9_sixty_six_mem_profiles_after_top_triples
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterTopTriples := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hp⟩ := q9_sixty_six_mem_profiles_after_agreement hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterTopTriples, List.mem_filter]
  refine ⟨hp, bne_iff_ne.mpr ?_⟩
  intro he
  have hv : List.ofFn (![0, 1, 5, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) =
      [0, 1, 5, 5, 5, 5, 5, 5, 5] := by decide +kernel
  have hr := List.ofFn_inj.mp (he.trans hv.symm)
  subst r
  exact q9_sixty_six_excludes_015555555 hS hregS hbS hhalf

#print axioms q9_sixty_six_mem_profiles_after_top_triples

end D5.S3.Combinatorics.Graph.HypercubeCritical
