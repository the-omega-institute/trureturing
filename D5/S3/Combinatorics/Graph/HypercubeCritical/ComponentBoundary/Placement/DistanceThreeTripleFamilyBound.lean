/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: A triple family with the specified face degrees and four-axis exclusions has at least eighteen members. -/

module

public import Mathlib.Data.Finset.Powerset

import all D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
import all D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.TripleContactFamilyBound
import Batteries.Tactic.OpenPrivate

/-! The finite triple-family bound for the all-unshared distance-three chart. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.DistanceThreeTripleFamilyBound

open Finset
open scoped BigOperators
open private axes extensions link mem_axes mem_extensions mem_link extensions_link from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
open private sum_triple_link_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.TripleContactFamilyBound

variable {α : Type*} [DecidableEq α]

/-- The number of members containing the face `R`. -/
@[expose] public def codegree (H : Finset (Finset α)) (R : Finset α) : ℕ :=
  (H.filter fun U => R ⊆ U).card

private theorem exists_erase_eq {R T : Finset α} (hRT : R ⊆ T)
    (hcard : T.card = R.card + 1) : ∃ i ∈ T, T.erase i = R := by
  obtain ⟨i, hi, hiR⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (show R.card < T.card by omega)
  refine ⟨i, hi, (Finset.eq_of_subset_of_card_le (s := R) (t := T.erase i) ?_ ?_).symm⟩
  · intro j hj
    exact Finset.mem_erase.mpr ⟨fun e => hiR (e ▸ hj), hRT hj⟩
  · have := Finset.card_erase_add_one hi
    omega

private theorem card_extensions_eq_codegree {H : Finset (Finset α)} {R : Finset α}
    (hsize : ∀ U ∈ H, U.card = R.card + 1) :
    (extensions H R).card = codegree H R := by
  have himage : (extensions H R).image (fun i => insert i R) =
      H.filter (fun U => R ⊆ U) := by
    ext U
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(mem_extensions.mp hi).2, Finset.subset_insert _ _⟩
    · rintro ⟨hU, hRU⟩
      obtain ⟨i, hiU, he⟩ := exists_erase_eq hRU (hsize U hU)
      have hins : insert i R = U := by rw [← he, Finset.insert_erase hiU]
      have hiR : i ∉ R := by
        rw [← he]
        exact Finset.notMem_erase _ _
      exact ⟨i, mem_extensions.mpr ⟨hiR, hins.symm ▸ hU⟩, hins⟩
  unfold codegree
  rw [← himage]
  symm
  apply Finset.card_image_of_injOn
  intro i hi j _ he
  change insert i R = insert j R at he
  have hm : i ∈ insert j R := he ▸ Finset.mem_insert_self i R
  exact (Finset.mem_insert.mp hm).resolve_right (mem_extensions.mp hi).1

private def freshExtensions (H : Finset (Finset α)) (T : Finset α) (i : α) : Finset α :=
  (extensions H (T.erase i)).erase i

private theorem mem_freshExtensions {H : Finset (Finset α)} {T : Finset α} {i x : α}
    (hx : x ∈ freshExtensions H T i) : x ∉ T ∧ insert x (T.erase i) ∈ H := by
  obtain ⟨hxi, hx⟩ := Finset.mem_erase.mp hx
  obtain ⟨hx', hxH⟩ := mem_extensions.mp hx
  exact ⟨fun hxT => hx' (Finset.mem_erase.mpr ⟨hxi, hxT⟩), hxH⟩

private theorem fresh_disjoint {H : Finset (Finset α)} {T : Finset α}
    (hT : T ∈ H) (hcT : T.card = 3)
    (hfour : ∀ S : Finset α, S.card = 4 → (H.filter fun U => U ⊆ S).card ≤ 2) :
    (T : Set α).PairwiseDisjoint (freshExtensions H T) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨hxT, hPi⟩ := mem_freshExtensions hxi
  obtain ⟨_, hPj⟩ := mem_freshExtensions hxj
  -- Two extensions by the same fresh axis would put three members in insert x T.
  let P := insert x (T.erase i)
  let Q := insert x (T.erase j)
  have hTP : T ≠ P := Finset.ne_insert_of_notMem _ _ hxT
  have hTQ : T ≠ Q := Finset.ne_insert_of_notMem _ _ hxT
  have hPQ : P ≠ Q := by
    have hiQ : i ∈ Q := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hij, hi⟩)
    have hiP : i ∉ P := by
      simp [P, show i ≠ x from fun e => hxT (e ▸ hi)]
    exact fun e => hiP (e.symm ▸ hiQ)
  have hsub : ({T, P, Q} : Finset (Finset α)) ⊆ H.filter (fun U => U ⊆ insert x T) := by
    refine Finset.insert_subset_iff.mpr ⟨Finset.mem_filter.mpr ⟨hT, Finset.subset_insert _ _⟩, ?_⟩
    refine Finset.insert_subset_iff.mpr ⟨Finset.mem_filter.mpr ⟨hPi, ?_⟩, ?_⟩
    · exact Finset.insert_subset_insert _ (Finset.erase_subset _ _)
    · exact Finset.singleton_subset_iff.mpr
        (Finset.mem_filter.mpr ⟨hPj, Finset.insert_subset_insert _ (Finset.erase_subset _ _)⟩)
  have hthree : ({T, P, Q} : Finset (Finset α)).card = 3 :=
    Finset.card_eq_three.mpr ⟨T, P, Q, hTP, hTQ, hPQ, rfl⟩
  have hle := Finset.card_le_card hsub
  have hfour' := hfour (insert x T) (by rw [Finset.card_insert_of_notMem hxT, hcT])
  omega

private theorem fresh_count {H : Finset (Finset α)} {T : Finset α}
    (hT : T ∈ H) (hsize : ∀ U ∈ H, U.card = 3)
    (hdeg : ∀ i ∈ T, 2 ≤ codegree H (T.erase i) ∧ codegree H (T.erase i) ≤ 3)
    (hfour : ∀ S : Finset α, S.card = 4 → (H.filter fun U => U ⊆ S).card ≤ 2) :
    6 ≤ (axes H).card - 3 + (T.filter fun i => codegree H (T.erase i) = 2).card := by
  have hcT := hsize T hT
  have hTA : T ⊆ axes H := fun _ hi => mem_axes.mpr ⟨T, hT, hi⟩
  have hsub : T.biUnion (freshExtensions H T) ⊆ axes H \ T := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxT, hxH⟩ := mem_freshExtensions hxi
    exact Finset.mem_sdiff.mpr ⟨mem_axes.mpr ⟨_, hxH, Finset.mem_insert_self _ _⟩, hxT⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_biUnion (fresh_disjoint hT hcT hfour), Finset.card_sdiff_of_subset hTA, hcT] at hle
  have hsum : (∑ i ∈ T, (freshExtensions H T i).card) +
      (T.filter fun i => codegree H (T.erase i) = 2).card = 6 := by
    have hcount (i : α) (hi : i ∈ T) :
        (freshExtensions H T i).card + (if codegree H (T.erase i) = 2 then 1 else 0) = 2 := by
      have hiE : i ∈ extensions H (T.erase i) :=
        mem_extensions.mpr ⟨Finset.notMem_erase _ _, by rwa [Finset.insert_erase hi]⟩
      have hc := Finset.card_erase_add_one hiE
      change (freshExtensions H T i).card + 1 = (extensions H (T.erase i)).card at hc
      rw [card_extensions_eq_codegree (H := H) (R := T.erase i) (fun U hU => by
        have := Finset.card_erase_add_one hi
        have := hsize U hU
        omega)] at hc
      obtain ⟨hlo, hhi⟩ := hdeg i hi
      split <;> omega
    calc
      _ = ∑ i ∈ T, ((freshExtensions H T i).card +
          (if codegree H (T.erase i) = 2 then 1 else 0)) := by
        simp [Finset.sum_add_distrib, ← Finset.sum_filter]
      _ = _ := by rw [Finset.sum_const_nat hcount, hcT]
  omega

private theorem erase_middle {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) :
    (insert a ({b, c} : Finset α)).erase b = {a, c} := by
  rw [Finset.erase_insert_of_ne hab,
    Finset.erase_insert (show b ∉ ({c} : Finset α) by simpa using hbc)]

private theorem link_card_ge_six {H : Finset (Finset α)}
    (hsize : ∀ T ∈ H, T.card = 3)
    (hdeg : ∀ T ∈ H, ∀ i ∈ T, 2 ≤ codegree H (T.erase i) ∧ codegree H (T.erase i) ≤ 3)
    (hlow : ∀ T ∈ H, (T.filter fun i => codegree H (T.erase i) = 2).card ≤ 1)
    (hfour : ∀ S : Finset α, S.card = 4 → (H.filter fun U => U ⊆ S).card ≤ 2)
    {a : α} (ha : a ∈ axes H) : 6 ≤ (link H a).card := by
  let L := link H a
  let nbr (b : α) := extensions L ({b} : Finset α)
  let incident (b : α) := L.filter fun S => b ∈ S
  have hL (S : Finset α) (hS : S ∈ L) : S.card = 2 := by
    obtain ⟨haS, hT⟩ := mem_link.mp hS
    have hc := hsize _ hT
    rw [Finset.card_insert_of_notMem haS] at hc
    omega
  have hnbr {b : α} (hab : a ≠ b) : (nbr b).card = codegree H {a, b} := by
    change (extensions (link H a) {b}).card = codegree H {a, b}
    rw [extensions_link (show a ∉ ({b} : Finset α) by simpa using hab)]
    exact card_extensions_eq_codegree (fun T hT => by rw [hsize T hT, Finset.card_pair hab])
  have hpair {b c : α} (hS : ({b, c} : Finset α) ∈ L) :
      2 ≤ (nbr b).card ∧ 2 ≤ (nbr c).card ∧ ((nbr b).card = 3 ∨ (nbr c).card = 3) := by
    obtain ⟨haS, hT⟩ := mem_link.mp hS
    have hab : a ≠ b := fun e => haS (by simp [e])
    have hac : a ≠ c := fun e => haS (by simp [e])
    have hbc : b ≠ c := by
      intro e
      subst c
      simpa using hL _ hS
    let T : Finset α := insert a {b, c}
    have hbT : b ∈ T := by simp [T]
    have hcT : c ∈ T := by simp [T]
    have hEb : codegree H (T.erase c) = (nbr b).card := by
      change codegree H ((insert a ({b,c} : Finset α)).erase c) = (nbr b).card
      rw [Finset.pair_comm b c, erase_middle hac hbc.symm, hnbr hab]
    have hEc : codegree H (T.erase b) = (nbr c).card := by
      change codegree H ((insert a ({b,c} : Finset α)).erase b) = (nbr c).card
      rw [erase_middle hab hbc, hnbr hac]
    obtain ⟨hblo, hbhi⟩ := hdeg T hT c hcT
    obtain ⟨hclo, hchi⟩ := hdeg T hT b hbT
    rw [hEb] at hblo hbhi
    rw [hEc] at hclo hchi
    refine ⟨hblo, hclo, ?_⟩
    by_contra h
    obtain ⟨hb3, hc3⟩ := not_or.mp h
    have hb2 : codegree H (T.erase c) = 2 := by
      rw [hEb]
      omega
    have hc2 : codegree H (T.erase b) = 2 := by
      rw [hEc]
      omega
    exact hbc (Finset.card_le_one.mp (hlow T hT) b (Finset.mem_filter.mpr ⟨hbT, hc2⟩)
      c (Finset.mem_filter.mpr ⟨hcT, hb2⟩))
  obtain ⟨T, hT, haT⟩ := mem_axes.mp ha
  have hS : T.erase a ∈ L :=
    mem_link.mpr ⟨Finset.notMem_erase _ _, by rwa [Finset.insert_erase haT]⟩
  obtain ⟨u, v, _, huv⟩ := Finset.card_eq_two.mp (hL _ hS)
  rw [huv] at hS
  obtain ⟨b, hb⟩ : ∃ b, (nbr b).card = 3 := by
    rcases (hpair hS).2.2 with h | h
    · exact ⟨u, h⟩
    · exact ⟨v, h⟩
  -- An edge between two neighbors of b would admit b across two of its triple's faces.
  have hdisj : (nbr b : Set α).PairwiseDisjoint incident := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro S hcS hdS
    obtain ⟨hSL, hcS⟩ := Finset.mem_filter.mp hcS
    have hdS := (Finset.mem_filter.mp hdS).2
    have he : ({c, d} : Finset α) = S := by
      apply Finset.eq_of_subset_of_card_le
        (Finset.insert_subset_iff.mpr ⟨hcS, Finset.singleton_subset_iff.mpr hdS⟩)
      rw [hL S hSL, Finset.card_pair hcd]
    rw [← he] at hSL
    obtain ⟨haS, hU⟩ := mem_link.mp hSL
    have hac : a ≠ c := fun e => haS (by simp [e])
    have had : a ≠ d := fun e => haS (by simp [e])
    have hcb : c ≠ b := by simpa using (mem_extensions.mp hc).1
    have hdb : d ≠ b := by simpa using (mem_extensions.mp hd).1
    let U : Finset α := insert a {c, d}
    have hfresh {x y : α} (hx : x ∈ nbr b) (hy : y ≠ b) (herase : U.erase y = {a, x}) :
        b ∈ freshExtensions H U y := by
      obtain ⟨hxb, hxL⟩ := mem_extensions.mp hx
      obtain ⟨ha', hxH⟩ := mem_link.mp hxL
      have hba : b ≠ a := fun e => ha' (by simp [← e])
      have hbx : b ≠ x := fun e => hxb (by simp [e])
      refine Finset.mem_erase.mpr ⟨hy.symm, mem_extensions.mpr ⟨?_, ?_⟩⟩
      · rw [herase]
        simp [hba, hbx]
      · rw [herase, Finset.insert_comm b a, Finset.pair_comm b x]
        exact hxH
    have hec : U.erase c = {a, d} := erase_middle hac hcd
    have hed : U.erase d = {a, c} := by
      change (insert a ({c, d} : Finset α)).erase d = {a, c}
      rw [Finset.pair_comm c d, erase_middle had hcd.symm]
    exact Finset.disjoint_left.mp
      (fresh_disjoint hU (hsize U hU) hfour (by simp) (by simp) hcd)
      (hfresh hd hcb hec) (hfresh hc hdb hed)
  have hinc (c : α) (hc : c ∈ nbr b) : 2 ≤ (incident c).card := by
    have hdegc := (hpair (mem_extensions.mp hc).2).1
    have heq : (nbr c).card = (incident c).card := by
      simpa [nbr, incident, codegree, Finset.singleton_subset_iff] using
        (card_extensions_eq_codegree (H := L) (R := {c}) (fun S hS => by
          rw [hL S hS, Finset.card_singleton]))
    exact heq ▸ hdegc
  have hsub : (nbr b).biUnion incident ⊆ L := by
    intro S hS
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hS
    exact (Finset.mem_filter.mp hc).1
  calc
    6 = ∑ _c ∈ nbr b, (2 : ℕ) := by simp [hb, Nat.mul_comm]
    _ ≤ ∑ c ∈ nbr b, (incident c).card := Finset.sum_le_sum hinc
    _ = _ := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

private theorem count_pair_incidences {H : Finset (Finset α)}
    (hsize : ∀ T ∈ H, T.card = 3) (k : ℕ) :
    (∑ T ∈ H, (T.filter fun i => codegree H (T.erase i) = k).card) =
      k * ((H.biUnion fun T => T.powersetCard 2).filter fun R => codegree H R = k).card := by
  let P := (H.biUnion fun T => T.powersetCard 2).filter fun R => codegree H R = k
  -- Erasing an axis indexes each incident pair once in a given triple.
  have hfiber (T : Finset α) (hT : T ∈ H) :
      ((T.filter fun i => codegree H (T.erase i) = k).image T.erase) =
        P.filter (fun R => R ⊆ T) := by
    ext R
    simp only [P, Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_powersetCard]
    constructor
    · rintro ⟨i, ⟨hi, hk⟩, rfl⟩
      have hcard := Finset.card_erase_add_one hi
      have hTcard := hsize T hT
      exact ⟨⟨⟨T, hT, Finset.erase_subset _ _, by omega⟩, hk⟩, Finset.erase_subset _ _⟩
    · rintro ⟨⟨⟨_, _, _, hR⟩, hk⟩, hRT⟩
      obtain ⟨i, hi, he⟩ := exists_erase_eq hRT (by rw [hsize T hT, hR])
      exact ⟨i, ⟨hi, he.symm ▸ hk⟩, he⟩
  have hp (R : Finset α) (hR : R ∈ P) : codegree H R = k :=
    (Finset.mem_filter.mp hR).2
  calc
    _ = ∑ T ∈ H, (P.filter fun R => R ⊆ T).card := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [← hfiber T hT]
      symm
      apply Finset.card_image_of_injOn
      intro i hi j _ he
      change T.erase i = T.erase j at he
      by_contra hij
      have hm : i ∈ T.erase j := Finset.mem_erase.mpr ⟨hij, (Finset.mem_filter.mp hi).1⟩
      exact Finset.notMem_erase _ _ (he.symm ▸ hm)
    _ = ∑ T ∈ H, ∑ R ∈ P, if R ⊆ T then (1 : ℕ) else 0 := by
      simp [← Finset.sum_filter]
    _ = ∑ R ∈ P, ∑ T ∈ H, if R ⊆ T then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ R ∈ P, codegree H R := by simp [← Finset.sum_filter, codegree]
    _ = _ := by rw [Finset.sum_const_nat hp, Nat.mul_comm]

/-- A nonempty triple family has at least eighteen members if its occurring pairs have
codegree two or three, each triple has at most one pair of codegree two, and each four-set
contains at most two members. -/
public theorem card_ge_eighteen
    (H : Finset (Finset α)) (hne : H.Nonempty) (hsize : ∀ T ∈ H, T.card = 3)
    (hdeg : ∀ T ∈ H, ∀ i ∈ T, 2 ≤ codegree H (T.erase i) ∧ codegree H (T.erase i) ≤ 3)
    (hlow : ∀ T ∈ H, (T.filter fun i => codegree H (T.erase i) = 2).card ≤ 1)
    (hfour : ∀ S : Finset α, S.card = 4 → (H.filter fun U => U ⊆ S).card ≤ 2) :
    18 ≤ H.card := by
  have hfresh (T : Finset α) (hT : T ∈ H) :
      6 ≤ (axes H).card - 3 + (T.filter fun i => codegree H (T.erase i) = 2).card :=
    fresh_count hT hsize (hdeg T hT) hfour
  have haxes : 8 ≤ (axes H).card := by
    obtain ⟨T, hT⟩ := hne
    have := hfresh T hT
    have := hlow T hT
    omega
  have hsum : 6 * (axes H).card ≤ 3 * H.card := by
    calc
      _ = ∑ _a ∈ axes H, (6 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ axes H, (link H a).card := by
        apply Finset.sum_le_sum
        intro a ha
        exact link_card_ge_six hsize hdeg hlow hfour ha
      _ = _ := sum_triple_link_card hsize
  by_contra h18
  have h8 : (axes H).card = 8 := by omega
  have htwo (T : Finset α) (hT : T ∈ H) :
      (T.filter fun i => codegree H (T.erase i) = 2).card = 1 := by
    have := hfresh T hT
    have := hlow T hT
    omega
  have hthree (T : Finset α) (hT : T ∈ H) :
      (T.filter fun i => codegree H (T.erase i) = 3).card = 2 := by
    have heq : (T.filter fun i => ¬ codegree H (T.erase i) = 2) =
        T.filter (fun i => codegree H (T.erase i) = 3) := by
      apply Finset.filter_congr
      intro i hi
      obtain ⟨hlo, hhi⟩ := hdeg T hT i hi
      omega
    have h := Finset.card_filter_add_card_filter_not (s := T)
      (fun i => codegree H (T.erase i) = 2)
    rw [htwo T hT, heq, hsize T hT] at h
    omega
  have h2 := count_pair_incidences hsize 2
  have h3 := count_pair_incidences hsize 3
  rw [Finset.sum_const_nat htwo, Nat.mul_one] at h2
  rw [Finset.sum_const_nat hthree] at h3
  have h16or17 : H.card = 16 ∨ H.card = 17 := by omega
  rcases h16or17 with h16 | h17 <;> omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.DistanceThreeTripleFamilyBound
