/- GID: D5/S3/Combinatorics/Graph/HyperedgeCutDensity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HyperedgeCutDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: A double-edge and triangle lift strengthens hereditary hyperedge cut density. -/

import D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity

namespace D5.S3.Combinatorics.Graph.HyperedgeCutDensity
variable {α β : Type*} [DecidableEq α]

/-- Every induced cut contains at most twice its vertex count. -/
def TwoCutCap (V : Finset α) (E : Finset β) (l r : β → α) : Prop :=
  ∀ S ⊆ V, ∀ L ⊆ S,
    CutAverage.ownerCount (inside E l r S) (fun e => {l e, r e}) L ≤ 2 * S.card

theorem sparse_of_two_cut_cap (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e) (hcap : TwoCutCap V E l r)
    (S : Finset α) (hSV : S ⊆ V) (hS : S.Nonempty) :
    (inside E l r S).card < 4 * S.card := by
  let J := inside E l r S
  have hsub : ∀ e ∈ J, ({l e, r e} : Finset α) ⊆ S := by
    intro e he
    simpa only [insert_subset_iff, singleton_subset_iff] using (mem_filter.mp he).2
  have hpair : ∀ e ∈ J, ({l e, r e} : Finset α).card = 2 := by
    intro e he
    simp [hne e (mem_filter.mp he).1]
  by_cases hJ : J.Nonempty
  · obtain ⟨e, he⟩ := hJ
    have hs2 : 2 ≤ S.card := by simpa only [hpair e he] using card_le_card (hsub e he)
    have hpow : 2 ^ S.card = 2 * 2 ^ (S.card - 1) := by
      have hexp : S.card = S.card - 1 + 1 := by omega
      conv_lhs => rw [hexp]
      rw [pow_succ, Nat.mul_comm]
    have hc : ∀ e ∈ J, CutAverage.crossCount S {l e, r e} = 2 ^ (S.card - 1) := by
      intro e he
      rw [CutAverage.cross_count_nonempty S _ (hsub e he) (by simp), hpair e he]
      have hexp : S.card - 2 + 1 = S.card - 1 := by omega
      rw [hexp, hpow]
      omega
    have htotal := CutAverage.double_count S J (fun e => {l e, r e})
    have hsum : (∑ e ∈ J, CutAverage.crossCount S {l e, r e}) = J.card * 2 ^ (S.card - 1) := by
      rw [sum_congr rfl hc]
      simp
    have hstrict : (∑ L ∈ S.powerset, CutAverage.ownerCount J (fun e => {l e, r e}) L) <
        ∑ _L ∈ S.powerset, 2 * S.card := by
      apply sum_lt_sum
      · intro L hL
        exact hcap S hSV L (mem_powerset.mp hL)
      · refine ⟨∅, empty_mem_powerset S, ?_⟩
        rw [CutAverage.empty_cut_count]
        have := card_pos.mpr hS
        omega
    rw [← htotal, hsum] at hstrict
    simp only [sum_const, card_powerset, smul_eq_mul, hpow] at hstrict
    have ht : 0 < 2 ^ (S.card - 1) := pow_pos (by decide) _
    change J.card < 4 * S.card
    nlinarith
  · have hz : J.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hJ)
    change J.card < 4 * S.card
    have := card_pos.mpr hS
    omega

theorem low_degree_of_sparse (n : Nat) (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e)
    (hends : ∀ e ∈ E, l e ∈ V ∧ r e ∈ V)
    (hsparse : 2 * E.card < n * V.card) :
    ∃ v ∈ V, (incident E l r v).card < n := by
  by_contra h
  have hdeg : ∀ v ∈ V, n ≤ (incident E l r v).card := by
    intro v hv
    by_contra hh
    exact h ⟨v, hv, by omega⟩
  have hh := sum_le_sum hdeg
  have hs := sum_incident V E l r hne hends
  simp only [sum_const, smul_eq_mul] at hh
  rw [hs] at hh
  nlinarith

/-- Indexed-edge degeneracy gives a proper coloring on the finite vertex set. -/
theorem coloring_of_sparse (n : Nat) (hn : 0 < n) (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e)
    (hsparse : ∀ S ⊆ V, S.Nonempty → 2 * (inside E l r S).card < n * S.card) :
    ∃ c : α → Fin n, ∀ e ∈ E, l e ∈ V → r e ∈ V → c (l e) ≠ c (r e) := by
  induction V using Finset.strongInductionOn with
  | _ V ih =>
    by_cases hV : V.Nonempty
    · let J := inside E l r V
      have hJsub : J ⊆ E := filter_subset _ _
      have hJends : ∀ e ∈ J, l e ∈ V ∧ r e ∈ V := by
        intro e he
        exact (mem_filter.mp he).2
      obtain ⟨v, hv, hdeg⟩ := low_degree_of_sparse n V J l r
        (fun e he => hne e (hJsub he)) hJends (hsparse V (Subset.refl _) hV)
      obtain ⟨c, hc⟩ := ih (V.erase v) (erase_ssubset hv) (by
        intro S hS hneS
        exact hsparse S (hS.trans (erase_subset v V)) hneS)
      let T := incident J l r v
      let other (e : β) : α := if l e = v then r e else l e
      let used : Finset (Fin n) := T.image (fun e => c (other e))
      have hused : used.card < (univ : Finset (Fin n)).card := by
        have hh : used.card ≤ T.card := card_image_le
        have ht : T.card < n := hdeg
        simpa using (show used.card < n by omega)
      obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card hused
      let c' := Function.update c v a
      refine ⟨c', ?_⟩
      intro e he hel her
      have heJ : e ∈ J := mem_filter.mpr ⟨he, hel, her⟩
      by_cases hl : l e = v
      · have hr : r e ≠ v := by intro hr; exact hne e he (hl.trans hr.symm)
        have heT : e ∈ T := mem_filter.mpr ⟨heJ, Or.inl hl⟩
        have hm : c (r e) ∈ used := by
          apply mem_image.mpr
          exact ⟨e, heT, by simp [other, hl]⟩
        have hca : a ≠ c (r e) := by intro ha'; exact ha (ha' ▸ hm)
        simpa [c', hl, hr] using hca
      · by_cases hr : r e = v
        · have heT : e ∈ T := mem_filter.mpr ⟨heJ, Or.inr hr⟩
          have hm : c (l e) ∈ used := by
            apply mem_image.mpr
            exact ⟨e, heT, by simp [other, hl]⟩
          have hca : c (l e) ≠ a := by intro ha'; exact ha (ha' ▸ hm)
          simpa [c', hl, hr] using hca
        · have hh := hc e he (mem_erase.mpr ⟨hl, hel⟩) (mem_erase.mpr ⟨hr, her⟩)
          simpa [c', hl, hr] using hh
    · refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
      intro e he hel _
      exact (hV ⟨l e, hel⟩).elim

/-- The seven nonzero binary linear forms on three-bit colors. -/
def split8 (k : Fin 7) (a : Fin 8) : Bool :=
  decide ((a.val % 2 * ((k.val + 1) % 2) +
    (a.val / 2 % 2) * ((k.val + 1) / 2 % 2) +
    (a.val / 4 % 2) * ((k.val + 1) / 4 % 2)) % 2 = 0)

theorem split8_count (a b : Fin 8) (hne : a ≠ b) :
    ((univ : Finset (Fin 7)).filter fun k => split8 k a ≠ split8 k b).card = 4 := by
  fin_cases a <;> fin_cases b <;> first | exact (hne rfl).elim | decide

theorem density_of_eight_coloring (V : Finset α) (E : Finset β) (l r : β → α)
    (hends : ∀ e ∈ E, l e ∈ V ∧ r e ∈ V)
    (hcut : ∀ L ⊆ V,
      CutAverage.ownerCount E (fun e => {l e, r e}) L ≤ 2 * V.card)
    (c : α → Fin 8) (hc : ∀ e ∈ E, c (l e) ≠ c (r e)) :
    4 * E.card ≤ 14 * V.card := by
  let cuts (k : Fin 7) := V.filter fun v => split8 k (c v) = true
  have hcap (k : Fin 7) :
      (E.filter fun e => split8 k (c (l e)) ≠ split8 k (c (r e))).card ≤ 2 * V.card := by
    have h := hcut (cuts k) (filter_subset _ _)
    convert h using 1
    congr 1
    ext e
    by_cases he : e ∈ E
    · have hh := hends e he
      have hp := pair_cross_iff (l e) (r e) (cuts k)
      simp only [mem_filter, he, true_and]
      rw [hp]
      simp only [cuts, mem_filter, hh.1, hh.2, true_and]
      cases split8 k (c (l e)) <;> cases split8 k (c (r e)) <;> decide
    · simp [he]
  have hd := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset (Fin 7))) (t := E)
    (fun k e => split8 k (c (l e)) ≠ split8 k (c (r e)))
  change (∑ k : Fin 7, (E.filter fun e =>
      split8 k (c (l e)) ≠ split8 k (c (r e))).card) =
    ∑ e ∈ E, ((univ : Finset (Fin 7)).filter fun k =>
      split8 k (c (l e)) ≠ split8 k (c (r e))).card at hd
  have heq : (∑ k : Fin 7, (E.filter fun e =>
      split8 k (c (l e)) ≠ split8 k (c (r e))).card) = 4 * E.card := by
    rw [hd]
    calc
      _ = ∑ _e ∈ E, 4 := sum_congr rfl fun e he => split8_count _ _ (hc e he)
      _ = 4 * E.card := by simp [Nat.mul_comm]
  have hh := sum_le_sum (fun (k : Fin 7) (_ : k ∈ univ) => hcap k)
  rw [heq] at hh
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hh
  omega

/-- Hereditary cut capacity two bounds multigraph density by seven halves. -/
theorem two_cut_density (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e)
    (hends : ∀ e ∈ E, l e ∈ V ∧ r e ∈ V)
    (hcap : TwoCutCap V E l r) : 2 * E.card ≤ 7 * V.card := by
  have hsparse : ∀ S ⊆ V, S.Nonempty → 2 * (inside E l r S).card < 8 * S.card := by
    intro S hS hneS
    have := sparse_of_two_cut_cap V E l r hne hcap S hS hneS
    omega
  obtain ⟨c, hc⟩ := coloring_of_sparse 8 (by decide) V E l r hne hsparse
  have hcut : ∀ L ⊆ V, CutAverage.ownerCount E (fun e => {l e, r e}) L ≤ 2 * V.card := by
    have heq : inside E l r V = E := filter_eq_self.mpr hends
    simpa only [heq] using hcap V (Subset.refl V)
  have h := density_of_eight_coloring V E l r hends hcut c
    (fun e he => hc e he (hends e he).1 (hends e he).2)
  omega


namespace OwnerLift

variable {ι α : Type*} [DecidableEq α]

/-- An ordinary owner contributes two parallel edges; a flagged owner contributes a triangle. -/
def slots (large : Bool) : Finset (Fin 3) := if large then univ else {0, 1}

def left (large : Bool) (a b c : α) (j : Fin 3) : α :=
  if large then (if j = 0 then a else if j = 1 then b else c) else a

def right (large : Bool) (a b c : α) (j : Fin 3) : α :=
  if large then (if j = 0 then b else if j = 1 then c else a) else b

theorem ends_mem (large : Bool) (a b c : α) (j : Fin 3) :
    left large a b c j ∈ ({a,b,c} : Finset α) ∧
    right large a b c j ∈ ({a,b,c} : Finset α) := by
  cases large <;> fin_cases j <;> simp [left, right]

theorem local_cross_le_two (large : Bool) (a b c : α) (L : Finset α) :
    ((slots large).filter fun j =>
      CutAverage.Cross {left large a b c j, right large a b c j} L).card ≤ 2 := by
  cases large
  · calc
      _ ≤ (slots false).card := card_filter_le _ _
      _ = 2 := by decide
  · rw [slots, if_pos rfl, show (univ : Finset (Fin 3)) = {0,1,2} by decide]
    by_cases ha : a ∈ L <;> by_cases hb : b ∈ L <;> by_cases hc : c ∈ L <;>
      simp [filter_insert, filter_singleton, left, right, pair_cross_iff, ha, hb, hc]

def edges (I : Finset ι) (large : ι → Bool) : Finset (Σ _i : ι, Fin 3) :=
  I.sigma fun i => slots (large i)

def Left (large : ι → Bool) (a b c : ι → α) (e : Σ _i : ι, Fin 3) : α :=
  left (large e.1) (a e.1) (b e.1) (c e.1) e.2

def Right (large : ι → Bool) (a b c : ι → α) (e : Σ _i : ι, Fin 3) : α :=
  right (large e.1) (a e.1) (b e.1) (c e.1) e.2

/-- A representative set meets both sides of the cut inside the selected vertex set. -/
def Hits (a b c : α) (S L : Finset α) : Prop :=
  CutAverage.Cross (({a,b,c} : Finset α) ∩ S) L

instance hitsDecidable (a b c : α) (S L : Finset α) : Decidable (Hits a b c S L) :=
  inferInstanceAs (Decidable (CutAverage.Cross (({a,b,c} : Finset α) ∩ S) L))

theorem local_cut_le (large : Bool) (a b c : α) (S L : Finset α) :
    ((slots large).filter fun j =>
      (left large a b c j ∈ S ∧ right large a b c j ∈ S) ∧
      CutAverage.Cross {left large a b c j, right large a b c j} L).card ≤
        if Hits a b c S L then 2 else 0 := by
  by_cases hhit : Hits a b c S L
  · rw [if_pos hhit]
    apply le_trans (card_le_card ?_) (local_cross_le_two large a b c L)
    intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2.2⟩
  · rw [if_neg hhit]
    apply Nat.le_zero.mpr
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro j hj hcross
    have hm := ends_mem large a b c j
    have hp := (pair_cross_iff _ _ L).mp hcross.2
    apply hhit
    rcases hp with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨⟨_, mem_inter.mpr ⟨mem_inter.mpr ⟨hm.1, hcross.1.1⟩, hl⟩⟩,
        ⟨_, mem_sdiff.mpr ⟨mem_inter.mpr ⟨hm.2, hcross.1.2⟩, hr⟩⟩⟩
    · exact ⟨⟨_, mem_inter.mpr ⟨mem_inter.mpr ⟨hm.2, hcross.1.2⟩, hr⟩⟩,
        ⟨_, mem_sdiff.mpr ⟨mem_inter.mpr ⟨hm.1, hcross.1.1⟩, hl⟩⟩⟩

theorem lift_cut_cap (V : Finset α) (I : Finset ι) (large : ι → Bool)
    (a b c : ι → α)
    (hcap : ∀ S ⊆ V, ∀ L ⊆ S, (I.filter fun i => Hits (a i) (b i) (c i) S L).card ≤ S.card) :
    TwoCutCap V (edges I large) (Left large a b c) (Right large a b c) := by
  intro S hSV L hLS
  unfold CutAverage.ownerCount inside edges
  rw [filter_filter, filter_sigma, card_sigma]
  change (∑ i ∈ I, ((slots (large i)).filter fun j =>
      (left (large i) (a i) (b i) (c i) j ∈ S ∧ right (large i) (a i) (b i) (c i) j ∈ S) ∧
      CutAverage.Cross {left (large i) (a i) (b i) (c i) j,
        right (large i) (a i) (b i) (c i) j} L).card) ≤ 2 * S.card
  calc
    _ ≤ ∑ i ∈ I, if Hits (a i) (b i) (c i) S L then 2 else 0 :=
      sum_le_sum fun i _ => local_cut_le _ _ _ _ _ _
    _ = 2 * (I.filter fun i => Hits (a i) (b i) (c i) S L).card := by
      rw [← sum_filter]
      simp [Nat.mul_comm]
    _ ≤ 2 * S.card := Nat.mul_le_mul_left _ (hcap S hSV L hLS)

theorem slots_card (large : Bool) : (slots large).card = 2 + if large then 1 else 0 := by
  cases large <;> decide

theorem edges_card (I : Finset ι) (large : ι → Bool) :
    (edges I large).card = 2 * I.card + (I.filter fun i => large i = true).card := by
  rw [edges, card_sigma]
  simp_rw [slots_card]
  rw [sum_add_distrib]
  simp [Nat.mul_comm]

end OwnerLift

open OwnerLift

variable {ι : Type*}

/-- The hereditary owner-cut bound charges flagged owners an additional two units. -/
theorem mixed_owner_density (V : Finset α) (I : Finset ι) (large : ι → Bool)
    (a b c : ι → α)
    (hab : ∀ i ∈ I, a i ≠ b i)
    (hthird : ∀ i ∈ I, large i = true → a i ≠ c i ∧ b i ≠ c i)
    (hends : ∀ i ∈ I, a i ∈ V ∧ b i ∈ V ∧ c i ∈ V)
    (hcap : ∀ S ⊆ V, ∀ L ⊆ S, (I.filter fun i => Hits (a i) (b i) (c i) S L).card ≤ S.card) :
    4 * I.card + 2 * (I.filter fun i => large i = true).card ≤ 7 * V.card := by
  have hne : ∀ e ∈ edges I large, Left large a b c e ≠ Right large a b c e := by
    intro ⟨i,j⟩ he
    have hi := (mem_sigma.mp he).1
    have hab' := hab i hi
    by_cases hlarge : large i = true
    · obtain ⟨hac, hbc⟩ := hthird i hi hlarge
      fin_cases j <;> simp [Left, Right, left, right, hlarge, hab', hbc, hac.symm]
    · simp [Left, Right, left, right, hlarge, hab']
  have he : ∀ e ∈ edges I large, Left large a b c e ∈ V ∧ Right large a b c e ∈ V := by
    intro ⟨i,j⟩ he
    have hi := (mem_sigma.mp he).1
    obtain ⟨ha,hb,hc⟩ := hends i hi
    by_cases hlarge : large i = true <;> fin_cases j <;>
      simp [Left, Right, left, right, hlarge, ha, hb, hc]
  have h := two_cut_density V (edges I large) (Left large a b c) (Right large a b c)
    hne he (lift_cut_cap V I large a b c hcap)
  rw [edges_card] at h
  omega



end D5.S3.Combinatorics.Graph.HyperedgeCutDensity
