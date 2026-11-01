/- GID: D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionMatchingDecoder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recovery of actual noncrossing partners from cut endpoint data. -/

import D5.S3.Combinatorics.PerfectMatchings.OrderedMatchingIntervals
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport

/-! Recovery of the pairing from its opening predicate at a fixed cut. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder

open CupCapBridgeProposal

/-- The smaller endpoint of a pair after cutting the circle. -/
def IsOpening {m : ℕ} (M : NCMatching m) (k : Fin m) : Prop := k < M.partner k

/-- Recovery retains the actual pairs, not merely the support of the matching. -/
theorem partner_eq_of_openings {m : ℕ} (M Q : NCMatching m)
    (h : ∀ k, IsOpening M k ↔ IsOpening Q k) : M.partner = Q.partner := by
  have close_eq : ∀ k : Fin m, M.partner k < k → M.partner k = Q.partner k := by
    intro k
    induction hk : k.val using Nat.strong_induction_on generalizing k with
    | h v ih =>
      intro hclose
      have hcloseQ : Q.partner k < k := by
        have hn : ¬ IsOpening Q k := fun hh => (not_lt_of_gt hclose) ((h k).mpr hh)
        have hne := Q.noFixed k
        dsimp [IsOpening] at hn
        exact lt_of_le_of_ne (le_of_not_gt hn) hne
      have same (A B : NCMatching m)
          (hab : ∀ t, IsOpening A t ↔ IsOpening B t)
          (hind : ∀ t : Fin m, t.val < v → A.partner t < t → A.partner t = B.partner t)
          (ha : A.partner k < k) (hb : B.partner k < k) :
          ¬ A.partner k < B.partner k := by
        intro hlt
        have ins := A.interior_closed (A.partner k) (B.partner k) hlt
          (by simpa only [A.involutive k] using hb)
        have hopB : IsOpening B (B.partner k) := by
          dsimp [IsOpening]
          simpa only [B.involutive k] using hb
        have hopA : B.partner k < A.partner (B.partner k) := (hab _).mpr hopB
        have hprev : A.partner (B.partner k) < k := by
          simpa only [A.involutive k] using ins.2
        have heq := hind (A.partner (B.partner k)) (by change (A.partner (B.partner k)).val < k.val at hprev; omega)
          (by simpa only [A.involutive (B.partner k)] using hopA)
        have heq' : B.partner k = B.partner (A.partner (B.partner k)) := by
          simpa only [A.involutive (B.partner k)] using heq
        have heq'' := B.partner.injective heq'
        exact (ne_of_lt hprev) heq''.symm
      have hMN : ¬ M.partner k < Q.partner k :=
        same M Q h (fun t ht hc => ih t.val ht t rfl hc) hclose hcloseQ
      have hNM : ¬ Q.partner k < M.partner k :=
        same Q M (fun t => (h t).symm)
          (fun t ht hc => by
            have hm : M.partner t < t := by
              have hn : ¬ IsOpening M t := fun hh => (not_lt_of_gt hc) ((h t).mp hh)
              dsimp [IsOpening] at hn
              exact lt_of_le_of_ne (le_of_not_gt hn) (M.noFixed t)
            exact (ih t.val ht t rfl hm).symm)
          hcloseQ hclose
      exact le_antisymm (le_of_not_gt hNM) (le_of_not_gt hMN)
  apply Equiv.ext
  intro k
  rcases lt_or_gt_of_ne (M.noFixed k) with hc | ho
  · exact close_eq k hc
  · have hc : M.partner (M.partner k) < M.partner k := by
      simpa only [M.involutive k] using ho
    have heq := close_eq (M.partner k) hc
    have heq' : k = Q.partner (M.partner k) := by simpa only [M.involutive k] using heq
    have heq'' := congrArg Q.partner heq'
    simpa only [Q.involutive (M.partner k)] using heq''.symm

private theorem opening_card (M : NCMatching 6) :
    (Finset.univ.filter (IsOpening M)).card = 3 := by
  classical
  let a := Finset.univ.filter (IsOpening M)
  let b := Finset.univ.filter (fun k => ¬ IsOpening M k)
  have himage : a.image M.partner = b := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, a, b]
    constructor
    · rintro ⟨j, hj, rfl⟩ hh
      exact (not_lt_of_gt hj) (by simpa only [IsOpening, M.involutive j] using hh)
    · intro hk
      have hc : M.partner k < k :=
        lt_of_le_of_ne (le_of_not_gt hk) (M.noFixed k)
      exact ⟨M.partner k, by simpa only [IsOpening, M.involutive k] using hc,
        M.involutive k⟩
  have hc : a.card = b.card := by
    rw [← himage, Finset.card_image_of_injective _ M.partner.injective]
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := IsOpening M)
  change a.card + b.card = _ at hs
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  change a.card = 3
  omega

private theorem closing_card (M : NCMatching 6) :
    (Finset.univ.filter (fun k => ¬ IsOpening M k)).card = 3 := by
  classical
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := IsOpening M)
  rw [opening_card M] at hs
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  omega

/-- Increasing opening ranks at the ordinary cut. -/
noncomputable def openingRanks (M : NCMatching 6) : Fin 3 ↪o Fin 6 := by
  classical
  exact (Finset.univ.filter (IsOpening M)).orderEmbOfFin (opening_card M)

/-- Increasing closing ranks at the same cut, independently sorted. -/
noncomputable def closingRanks (M : NCMatching 6) : Fin 3 ↪o Fin 6 := by
  classical
  exact (Finset.univ.filter (fun k => ¬ IsOpening M k)).orderEmbOfFin (closing_card M)

private theorem opening_is_open (M : NCMatching 6) (j : Fin 3) :
    IsOpening M (openingRanks M j) := by
  classical
  exact (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ (opening_card M) j)).2

private theorem closing_is_closed (M : NCMatching 6) (j : Fin 3) :
    M.partner (closingRanks M j) < closingRanks M j := by
  classical
  have hn : ¬ IsOpening M (closingRanks M j) :=
    (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ (closing_card M) j)).2
  exact lt_of_le_of_ne (le_of_not_gt hn) (M.noFixed _)

private theorem opening_surjective (M : NCMatching 6) (k : Fin 6)
    (hk : IsOpening M k) : ∃ j, openingRanks M j = k := by
  classical
  let x : {k // k ∈ Finset.univ.filter (IsOpening M)} := ⟨k, by simpa⟩
  let j : Fin 3 := ((Finset.univ.filter (IsOpening M)).orderIsoOfFin (opening_card M)).symm x
  refine ⟨j, ?_⟩
  exact congrArg Subtype.val ((Finset.orderIsoOfFin _ (opening_card M)).apply_symm_apply x)

private theorem closing_surjective (M : NCMatching 6) (k : Fin 6)
    (hk : ¬ IsOpening M k) : ∃ j, closingRanks M j = k := by
  classical
  let x : {k // k ∈ Finset.univ.filter (fun k => ¬ IsOpening M k)} := ⟨k, by simpa⟩
  let j : Fin 3 := ((Finset.univ.filter (fun k => ¬ IsOpening M k)).orderIsoOfFin (closing_card M)).symm x
  refine ⟨j, ?_⟩
  exact congrArg Subtype.val ((Finset.orderIsoOfFin _ (closing_card M)).apply_symm_apply x)

private theorem opening_lt_closing (M : NCMatching 6) (j : Fin 3) :
    openingRanks M j < closingRanks M j := by
  classical
  have hk (i : Fin 3) : IsOpening M (M.partner (closingRanks M i)) := by
    dsimp [IsOpening]
    simpa only [M.involutive (closingRanks M i)] using closing_is_closed M i
  let g : Fin 3 → Fin 3 := fun i =>
    Classical.choose (opening_surjective M _ (hk i))
  have hg (i : Fin 3) : openingRanks M (g i) = M.partner (closingRanks M i) :=
    Classical.choose_spec (opening_surjective M _ (hk i))
  by_contra hn
  have hle : closingRanks M j ≤ openingRanks M j := le_of_not_gt hn
  let f : Fin (j.val + 1) → Fin j.val := fun i => by
    let ci : Fin 3 := ⟨i.val, by omega⟩
    refine ⟨(g ci).val, ?_⟩
    have hqj : g ci < j := by
      by_contra h
      have hjo : openingRanks M j ≤ openingRanks M (g ci) :=
        (openingRanks M).monotone (le_of_not_gt h)
      have hic : closingRanks M ci ≤ closingRanks M j :=
        (closingRanks M).monotone (by change i.val ≤ j.val; omega)
      have hkc := closing_is_closed M ci
      rw [hg ci] at hjo
      exact (not_lt_of_ge (le_trans (le_trans hic hle) hjo)) hkc
    exact hqj
  have hf : Function.Injective f := by
    intro i l hil
    have hval := congrArg Fin.val hil
    dsimp [f] at hval
    have hp := congrArg (fun q : Fin 3 => openingRanks M q) (Fin.ext hval)
    rw [hg, hg] at hp
    have hi := M.partner.injective hp
    have hc := (closingRanks M).injective hi
    apply Fin.ext
    exact congrArg (Fin.val : Fin 3 → ℕ) hc
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

/-- Six actual selected sites, with their noncrossing pairing and indexed separation. -/
structure CircularMatching (n : ℕ) where
  sites : Fin 6 ↪o Fin (n + 4)
  pairs : NCMatching 6
  separated : ∀ r s : Fin 6, r < s →
    8 ≤ min ((sites s).val - (sites r).val)
      ((n + 4) - ((sites s).val - (sites r).val))

/-- The two distinguished sites, numbered n+3 and n+4 in the source, are absent. -/
def Ordinary {n : ℕ} (M : CircularMatching n) : Prop :=
  ∀ k, (M.sites k).val < n + 2

abbrev OrdinaryMatching (n : ℕ) := {M : CircularMatching n // Ordinary M}

/-- Starts and ends are ranked separately; these ranks are not partner assignments. -/
def start {n : ℕ} (M : OrdinaryMatching n) (j : Fin 3) : Fin (n + 4) :=
  M.val.sites (openingRanks M.val.pairs j)

def finish {n : ℕ} (M : OrdinaryMatching n) (j : Fin 3) : Fin (n + 4) :=
  M.val.sites (closingRanks M.val.pairs j)

/-- The literal ordinary decoder on the native zero-based rectangle carrier.
The source's row 4-j is j.rev, and t_j-2 becomes the bound column+2 ≤ finish_j. -/
def decode {n : ℕ} (M : OrdinaryMatching n) : Set (Fin 3 × Fin n) :=
  {p | (start M p.1.rev).val ≤ p.2.val ∧ p.2.val + 2 ≤ (finish M p.1.rev).val}

private theorem endpoint_gap {n : ℕ} (M : OrdinaryMatching n) (j : Fin 3) :
    (start M j).val + 8 ≤ (finish M j).val := by
  have hlt := opening_lt_closing M.val.pairs j
  have hs := (le_min_iff.mp (M.val.separated _ _ hlt)).1
  have ho := M.val.sites.strictMono hlt
  change (start M j).val < (finish M j).val at ho
  change 8 ≤ (finish M j).val - (start M j).val at hs
  omega

private def leftPoint {n : ℕ} (M : OrdinaryMatching n) (j : Fin 3) : Fin 3 × Fin n :=
  ⟨j.rev, ⟨(start M j).val, by
    have hg := endpoint_gap M j
    have hb := M.property (closingRanks M.val.pairs j)
    change (finish M j).val < n + 2 at hb
    omega⟩⟩

private def rightPoint {n : ℕ} (M : OrdinaryMatching n) (j : Fin 3) : Fin 3 × Fin n :=
  ⟨j.rev, ⟨(finish M j).val - 2, by
    have hg := endpoint_gap M j
    have hb := M.property (closingRanks M.val.pairs j)
    change (finish M j).val < n + 2 at hb
    omega⟩⟩

private theorem left_mem {n : ℕ} (M : OrdinaryMatching n) (j : Fin 3) :
    leftPoint M j ∈ decode M := by
  have hg := endpoint_gap M j
  simpa only [decode, leftPoint, Set.mem_ofPred_eq, Fin.rev_rev] using
    (show (start M j).val ≤ (start M j).val ∧
      (start M j).val + 2 ≤ (finish M j).val from ⟨le_rfl, by omega⟩)

private theorem right_mem {n : ℕ} (M : OrdinaryMatching n) (j : Fin 3) :
    rightPoint M j ∈ decode M := by
  have hg := endpoint_gap M j
  simpa only [decode, rightPoint, Set.mem_ofPred_eq, Fin.rev_rev] using
    (show (start M j).val ≤ (finish M j).val - 2 ∧
      (finish M j).val - 2 + 2 ≤ (finish M j).val from ⟨by omega, by omega⟩)

private theorem decode_injective {n : ℕ} :
    Function.Injective (decode : OrdinaryMatching n → Set (Fin 3 × Fin n)) := by
  intro M Q hd
  have hs : ∀ j, start M j = start Q j := by
    intro j
    have hm := left_mem M j
    rw [hd] at hm
    have hq := left_mem Q j
    rw [← hd] at hq
    have hml : (start Q j).val ≤ (start M j).val := by
      simpa only [decode, leftPoint, Set.mem_ofPred_eq, Fin.rev_rev] using hm.1
    have hql : (start M j).val ≤ (start Q j).val := by
      simpa only [decode, leftPoint, Set.mem_ofPred_eq, Fin.rev_rev] using hq.1
    exact Fin.ext (le_antisymm hql hml)
  have ht : ∀ j, finish M j = finish Q j := by
    intro j
    have hm := right_mem M j
    rw [hd] at hm
    have hq := right_mem Q j
    rw [← hd] at hq
    have hml : (finish M j).val - 2 + 2 ≤ (finish Q j).val := by
      simpa only [decode, rightPoint, Set.mem_ofPred_eq, Fin.rev_rev] using hm.2
    have hql : (finish Q j).val - 2 + 2 ≤ (finish M j).val := by
      simpa only [decode, rightPoint, Set.mem_ofPred_eq, Fin.rev_rev] using hq.2
    have hgm := endpoint_gap M j
    have hgq := endpoint_gap Q j
    apply Fin.ext
    omega
  have support (A B : OrdinaryMatching n)
      (hs : ∀ j, start A j = start B j) (ht : ∀ j, finish A j = finish B j) :
      Set.range A.val.sites ⊆ Set.range B.val.sites := by
    rintro x ⟨k, rfl⟩
    by_cases hk : IsOpening A.val.pairs k
    · obtain ⟨j, hj⟩ := opening_surjective A.val.pairs k hk
      refine ⟨openingRanks B.val.pairs j, ?_⟩
      rw [← hj]
      exact (hs j).symm
    · obtain ⟨j, hj⟩ := closing_surjective A.val.pairs k hk
      refine ⟨closingRanks B.val.pairs j, ?_⟩
      rw [← hj]
      exact (ht j).symm
  have hsites : M.val.sites = Q.val.sites := by
    apply DFunLike.coe_injective
    apply (M.val.sites.strictMono.range_inj_of_wellFoundedLT Q.val.sites.strictMono).mp
    exact Set.Subset.antisymm (support M Q hs ht)
      (support Q M (fun j => (hs j).symm) (fun j => (ht j).symm))
  have hopen : ∀ k, IsOpening M.val.pairs k ↔ IsOpening Q.val.pairs k := by
    intro k
    constructor
    · intro hk
      obtain ⟨j, hj⟩ := opening_surjective M.val.pairs k hk
      have he : Q.val.sites (openingRanks M.val.pairs j) =
          Q.val.sites (openingRanks Q.val.pairs j) := by
        simpa only [start, hsites] using hs j
      have hh := Q.val.sites.injective he
      rw [← hj, hh]
      exact opening_is_open Q.val.pairs j
    · intro hk
      obtain ⟨j, hj⟩ := opening_surjective Q.val.pairs k hk
      have he : M.val.sites (openingRanks M.val.pairs j) =
          M.val.sites (openingRanks Q.val.pairs j) := by
        simpa only [start, ← hsites] using hs j
      have hh := M.val.sites.injective he
      rw [← hj, ← hh]
      exact opening_is_open M.val.pairs j
  have hp := partner_eq_of_openings M.val.pairs Q.val.pairs hopen
  have hpairs : M.val.pairs = Q.val.pairs := by
    cases hm : M.val.pairs
    cases hq : Q.val.pairs
    simp only [hm, hq] at hp
    cases hp
    rfl
  apply Subtype.ext
  cases M with
  | mk M hM =>
    cases Q with
    | mk Q hQ =>
      cases M
      cases Q
      cases hsites
      cases hpairs
      rfl

/-- The six indexed source coordinates, in native zero-based site coordinates. -/
def endpointSites {n : ℕ} (a b : Fin 3 → Fin n) (k : Fin 6) : Fin (n + 4) :=
  if h : k.val < 3 then ⟨(a ⟨k.val, h⟩).val, by have := (a ⟨k.val, h⟩).isLt; omega⟩
  else ⟨(b ⟨k.val - 3, by omega⟩).val + 2, by
    have := (b ⟨k.val - 3, by omega⟩).isLt
    omega⟩

/-- Endpoint data for the whole separated source family, without a nonempty-family premise. -/
structure SeparatedEndpoints (n : ℕ) where
  a : Fin 3 → Fin n
  b : Fin 3 → Fin n
  left_strict : StrictAnti a
  right_strict : StrictAnti b
  nonempty : ∀ r, a r ≤ b r
  separated : ∀ r s : Fin 6, r < s →
    8 ≤ min (Nat.dist (endpointSites a b r).val (endpointSites a b s).val)
      ((n + 4) - Nat.dist (endpointSites a b r).val (endpointSites a b s).val)

/-- The actual union of its three native row intervals. -/
def endpointState {n : ℕ} (E : SeparatedEndpoints n) : Set (Fin 3 × Fin n) :=
  {p | E.a p.1 ≤ p.2 ∧ p.2 ≤ E.b p.1}

/-- Membership of an actual state in the original separated family. -/
def Separated {n : ℕ} (I : Set (Fin 3 × Fin n)) : Prop :=
  ∃ E : SeparatedEndpoints n, endpointState E = I

private theorem separated_full {n : ℕ} (E : SeparatedEndpoints n) (r s : Fin 6)
    (hrs : r ≠ s) :
    8 ≤ min (Nat.dist (endpointSites E.a E.b r).val (endpointSites E.a E.b s).val)
      ((n + 4) - Nat.dist (endpointSites E.a E.b r).val (endpointSites E.a E.b s).val) := by
  rcases lt_or_gt_of_ne hrs with h | h
  · exact E.separated r s h
  · simpa only [Nat.dist_comm] using E.separated s r h

private theorem endpointSites_injective {n : ℕ} (E : SeparatedEndpoints n) :
    Function.Injective (endpointSites E.a E.b) := by
  intro r s he
  by_contra hn
  have hh := separated_full E r s hn
  rw [he, Nat.dist_self] at hh
  simp at hh

private theorem endpointState_convex {n : ℕ} (E : SeparatedEndpoints n) :
    (endpointState E).OrdConnected := by
  constructor
  intro x hx y hy z hz
  refine ⟨?_, ?_⟩
  · exact le_trans (E.left_strict.antitone hz.1.1) (le_trans hx.1 hz.1.2)
  · exact le_trans (le_trans hz.2.2 hy.2) (E.right_strict.antitone hz.2.1)

private def endpointRank (M : NCMatching 6) (k : Fin 6) : Fin 6 :=
  if h : k.val < 3 then openingRanks M (⟨k.val, h⟩ : Fin 3).rev
  else closingRanks M (⟨k.val - 3, by omega⟩ : Fin 3).rev

private theorem endpointRank_injective (M : NCMatching 6) :
    Function.Injective (endpointRank M) := by
  intro r s he
  by_cases hr : r.val < 3 <;> by_cases hs : s.val < 3
  · simp only [endpointRank, dite_eq_left hr, dite_eq_left hs] at he
    have hh := congrArg Fin.rev ((openingRanks M).injective he)
    simp only [Fin.rev_rev] at hh
    exact Fin.ext (congrArg (Fin.val : Fin 3 → ℕ) hh)
  · simp only [endpointRank, dite_eq_left hr, dite_eq_right hs] at he
    have ho := opening_is_open M (⟨r.val, hr⟩ : Fin 3).rev
    rw [he] at ho
    exact False.elim (lt_asymm ho (closing_is_closed M _))
  · simp only [endpointRank, dite_eq_right hr, dite_eq_left hs] at he
    have ho := opening_is_open M (⟨s.val, hs⟩ : Fin 3).rev
    rw [← he] at ho
    exact False.elim (lt_asymm ho (closing_is_closed M _))
  · simp only [endpointRank, dite_eq_right hr, dite_eq_right hs] at he
    have hh := congrArg Fin.rev ((closingRanks M).injective he)
    simp only [Fin.rev_rev] at hh
    have hv := congrArg (Fin.val : Fin 3 → ℕ) hh
    change r.val - 3 = s.val - 3 at hv
    apply Fin.ext
    have := r.isLt
    have := s.isLt
    omega

private theorem sites_separated_full {n : ℕ} (M : CircularMatching n) (r s : Fin 6)
    (hrs : r ≠ s) :
    8 ≤ min (Nat.dist (M.sites r).val (M.sites s).val)
      ((n + 4) - Nat.dist (M.sites r).val (M.sites s).val) := by
  rcases lt_or_gt_of_ne hrs with h | h
  · rw [Nat.dist_eq_sub_of_le (le_of_lt (M.sites.strictMono h))]
    exact M.separated r s h
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (le_of_lt (M.sites.strictMono h))]
    exact M.separated s r h

private theorem decode_landing {n : ℕ} (M : OrdinaryMatching n) :
    Separated (decode M) := by
  let a : Fin 3 → Fin n := fun r => (leftPoint M r.rev).2
  let b : Fin 3 → Fin n := fun r => (rightPoint M r.rev).2
  have hcoord (k : Fin 6) : endpointSites a b k = M.val.sites (endpointRank M.val.pairs k) := by
    apply Fin.ext
    by_cases hk : k.val < 3
    · simp only [endpointSites, dite_eq_left hk, a, leftPoint, endpointRank]
      rfl
    · simp only [endpointSites, dite_eq_right hk, b, rightPoint, endpointRank]
      change (finish M (⟨k.val - 3, by omega⟩ : Fin 3).rev).val - 2 + 2 =
        (finish M (⟨k.val - 3, by omega⟩ : Fin 3).rev).val
      have hh := endpoint_gap M (⟨k.val - 3, by omega⟩ : Fin 3).rev
      omega
  let E : SeparatedEndpoints n := {
    a := a
    b := b
    left_strict := by
      intro r s hrs
      exact M.val.sites.strictMono ((openingRanks M.val.pairs).strictMono
        (Fin.rev_lt_rev.mpr hrs))
    right_strict := by
      intro r s hrs
      have ht := M.val.sites.strictMono ((closingRanks M.val.pairs).strictMono
        (Fin.rev_lt_rev.mpr hrs))
      change (finish M s.rev).val < (finish M r.rev).val at ht
      have hgs := endpoint_gap M s.rev
      have hgr := endpoint_gap M r.rev
      change (finish M s.rev).val - 2 < (finish M r.rev).val - 2
      omega
    nonempty := by
      intro r
      have hg := endpoint_gap M r.rev
      change (start M r.rev).val ≤ (finish M r.rev).val - 2
      omega
    separated := by
      intro r s hrs
      rw [hcoord r, hcoord s]
      exact sites_separated_full M.val _ _
        (fun he => (ne_of_lt hrs) (endpointRank_injective M.val.pairs he)) }
  refine ⟨E, ?_⟩
  ext p
  change ((start M p.1.rev).val ≤ p.2.val ∧
    p.2.val ≤ (finish M p.1.rev).val - 2) ↔
    ((start M p.1.rev).val ≤ p.2.val ∧ p.2.val + 2 ≤ (finish M p.1.rev).val)
  have hg := endpoint_gap M p.1.rev
  omega

private def patternPartner : Fin 5 → Fin 6 → Fin 6 :=
  ![![5, 4, 3, 2, 1, 0], ![5, 2, 1, 4, 3, 0], ![3, 2, 1, 0, 5, 4],
    ![1, 0, 5, 4, 3, 2], ![1, 0, 3, 2, 5, 4]]

/-- The five noncrossing pairings, in the five possible opening/closing orders. -/
def patternMatching (w : Fin 5) : NCMatching 6 where
  partner := {
    toFun := patternPartner w
    invFun := patternPartner w
    left_inv := by intro i; fin_cases w <;> fin_cases i <;> rfl
    right_inv := by intro i; fin_cases w <;> fin_cases i <;> rfl }
  involutive := by intro i; fin_cases w <;> fin_cases i <;> rfl
  noFixed := by intro i; fin_cases w <;> fin_cases i <;> decide
  noncrossing := by intro a b; fin_cases w <;> fin_cases a <;> fin_cases b <;> decide

private def patternLabel : Fin 5 → Fin 6 → Fin 6 :=
  ![![2, 1, 0, 5, 4, 3], ![2, 1, 5, 0, 4, 3], ![2, 1, 5, 4, 0, 3],
    ![2, 5, 1, 0, 4, 3], ![2, 5, 1, 4, 0, 3]]

private def patternOpenPosition : Fin 5 → Fin 3 → Fin 6 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 1, 4], ![0, 2, 3], ![0, 2, 4]]

private def patternClosePosition : Fin 5 → Fin 3 → Fin 6 :=
  ![![3, 4, 5], ![2, 4, 5], ![2, 3, 5], ![1, 4, 5], ![1, 3, 5]]

private def patternOpens (w : Fin 5) : Fin 3 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono (patternOpenPosition w) (by
    intro a b hab
    fin_cases w <;> fin_cases a <;> fin_cases b <;>
      norm_num [patternOpenPosition, patternClosePosition] at *)

private def patternCloses (w : Fin 5) : Fin 3 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono (patternClosePosition w) (by
    intro a b hab
    fin_cases w <;> fin_cases a <;> fin_cases b <;>
      norm_num [patternOpenPosition, patternClosePosition] at *)

private theorem encode_sorted {n : ℕ} (E : SeparatedEndpoints n) (w : Fin 5)
    (hmono : StrictMono (fun k => endpointSites E.a E.b (patternLabel w k))) :
    ∃ M : OrdinaryMatching n, decode M = endpointState E := by
  have hlabel : Function.Injective (patternLabel w) := by
    intro a b hab
    fin_cases w <;> fin_cases a <;> fin_cases b <;>
      simp_all [patternLabel]
  let C : CircularMatching n := {
    sites := OrderEmbedding.ofStrictMono _ hmono
    pairs := patternMatching w
    separated := by
      intro r s hrs
      have hh := separated_full E (patternLabel w r) (patternLabel w s)
        (fun he => (ne_of_lt hrs) (hlabel he))
      have hlt := hmono hrs
      rw [Nat.dist_eq_sub_of_le (le_of_lt hlt)] at hh
      exact hh }
  have hordinary : Ordinary C := by
    intro k
    change (endpointSites E.a E.b (patternLabel w k)).val < n + 2
    by_cases hk : (patternLabel w k).val < 3
    · simp only [endpointSites, dite_eq_left hk]
      have := (E.a ⟨(patternLabel w k).val, hk⟩).isLt
      omega
    · simp only [endpointSites, dite_eq_right hk]
      have := (E.b ⟨(patternLabel w k).val - 3, by omega⟩).isLt
      omega
  let M : OrdinaryMatching n := ⟨C, hordinary⟩
  have ho : openingRanks (patternMatching w) = patternOpens w := by
    unfold openingRanks
    symm
    apply Finset.orderEmbOfFin_unique'
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases w <;> fin_cases j <;> unfold IsOpening <;> decide
  have hc : closingRanks (patternMatching w) = patternCloses w := by
    unfold closingRanks
    symm
    apply Finset.orderEmbOfFin_unique'
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases w <;> fin_cases j <;> unfold IsOpening <;> decide
  have hlo (j : Fin 3) : patternLabel w (patternOpens w j) =
      (⟨j.rev.val, by omega⟩ : Fin 6) := by
    fin_cases w <;> fin_cases j <;> rfl
  have hlc (j : Fin 3) : patternLabel w (patternCloses w j) =
      (⟨j.rev.val + 3, by omega⟩ : Fin 6) := by
    fin_cases w <;> fin_cases j <;> rfl
  have hs (j : Fin 3) : (start M j).val = (E.a j.rev).val := by
    change (endpointSites E.a E.b (patternLabel w (openingRanks (patternMatching w) j))).val = _
    rw [ho, hlo]
    simp only [endpointSites, dite_eq_left j.rev.isLt]
  have ht (j : Fin 3) : (finish M j).val = (E.b j.rev).val + 2 := by
    change (endpointSites E.a E.b (patternLabel w (closingRanks (patternMatching w) j))).val = _
    rw [hc, hlc]
    have hn : ¬ j.rev.val + 3 < 3 := by omega
    simp only [endpointSites, dite_eq_right hn]
    congr 2
  refine ⟨M, ?_⟩
  ext p
  change ((start M p.1.rev).val ≤ p.2.val ∧ p.2.val + 2 ≤ (finish M p.1.rev).val) ↔
    ((E.a p.1).val ≤ p.2.val ∧ p.2.val ≤ (E.b p.1).val)
  rw [hs, ht]
  simp only [Fin.rev_rev]
  omega

private theorem decode_surjective {n : ℕ} (E : SeparatedEndpoints n) :
    ∃ M : OrdinaryMatching n, decode M = endpointState E := by
  let f := endpointSites E.a E.b
  have hs01 : f 2 < f 1 := E.left_strict (by decide : (1 : Fin 3) < 2)
  have hs12 : f 1 < f 0 := E.left_strict (by decide : (0 : Fin 3) < 1)
  have ht01 : f 5 < f 4 := by
    have hh := E.right_strict (by decide : (1 : Fin 3) < 2)
    change (E.b 2).val + 2 < (E.b 1).val + 2
    exact Nat.add_lt_add_right hh 2
  have ht12 : f 4 < f 3 := by
    have hh := E.right_strict (by decide : (0 : Fin 3) < 1)
    change (E.b 1).val + 2 < (E.b 0).val + 2
    exact Nat.add_lt_add_right hh 2
  have hown0 : f 2 < f 5 := by
    have hh := E.nonempty 2
    change (E.a 2).val < (E.b 2).val + 2
    omega
  have hown1 : f 1 < f 4 := by
    have hh := E.nonempty 1
    change (E.a 1).val < (E.b 1).val + 2
    omega
  have hown2 : f 0 < f 3 := by
    have hh := E.nonempty 0
    change (E.a 0).val < (E.b 0).val + 2
    omega
  have hn05 : f 0 ≠ f 5 := fun he => (by decide : (0 : Fin 6) ≠ 5)
    (endpointSites_injective E he)
  have hn15 : f 1 ≠ f 5 := fun he => (by decide : (1 : Fin 6) ≠ 5)
    (endpointSites_injective E he)
  have hn04 : f 0 ≠ f 4 := fun he => (by decide : (0 : Fin 6) ≠ 4)
    (endpointSites_injective E he)
  by_cases hwx : f 0 < f 5
  · apply encode_sorted E 0
    change StrictMono (fun k => f (patternLabel 0 k))
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [patternLabel] at * <;> omega
  · have hxw : f 5 < f 0 := lt_of_le_of_ne (le_of_not_gt hwx) hn05.symm
    by_cases hvx : f 1 < f 5
    · by_cases hwy : f 0 < f 4
      · apply encode_sorted E 1
        change StrictMono (fun k => f (patternLabel 1 k))
        intro i j hij
        fin_cases i <;> fin_cases j <;> norm_num [patternLabel] at * <;> omega
      · have hyw : f 4 < f 0 := lt_of_le_of_ne (le_of_not_gt hwy) hn04.symm
        apply encode_sorted E 2
        change StrictMono (fun k => f (patternLabel 2 k))
        intro i j hij
        fin_cases i <;> fin_cases j <;> norm_num [patternLabel] at * <;> omega
    · have hxv : f 5 < f 1 := lt_of_le_of_ne (le_of_not_gt hvx) hn15.symm
      by_cases hwy : f 0 < f 4
      · apply encode_sorted E 3
        change StrictMono (fun k => f (patternLabel 3 k))
        intro i j hij
        fin_cases i <;> fin_cases j <;> norm_num [patternLabel] at * <;> omega
      · have hyw : f 4 < f 0 := lt_of_le_of_ne (le_of_not_gt hwy) hn04.symm
        apply encode_sorted E 4
        change StrictMono (fun k => f (patternLabel 4 k))
        intro i j hij
        fin_cases i <;> fin_cases j <;> norm_num [patternLabel] at * <;> omega

/-- The source ordinary decoder is a bijection onto the actual separated state family.
Equality of decoded states recovers both selected sites and the actual partner permutation. -/
theorem ordinary_decoder {n : ℕ} :
    Function.Injective (decode : OrdinaryMatching n → Set (Fin 3 × Fin n)) ∧
    (∀ M : OrdinaryMatching n, Separated (decode M) ∧ (decode M).OrdConnected) ∧
    (∀ I : Set (Fin 3 × Fin n), Separated I → ∃ M : OrdinaryMatching n, decode M = I) := by
  refine ⟨decode_injective, ?_, ?_⟩
  · intro M
    obtain ⟨E, he⟩ := decode_landing M
    refine ⟨⟨E, he⟩, ?_⟩
    rw [← he]
    exact endpointState_convex E
  · rintro I ⟨E, rfl⟩
    exact decode_surjective E

#print axioms partner_eq_of_openings
#print axioms ordinary_decoder

end D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
