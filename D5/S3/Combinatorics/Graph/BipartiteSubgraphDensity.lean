/- GID: D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/BipartiteSubgraphDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Hereditary cut bounds force multigraph edge density at most three halves. -/

import Mathlib.Data.Finset.Interval
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity

namespace CutAverage

variable {α β : Type*} [DecidableEq α]

def Cross (A L : Finset α) : Prop :=
  (A ∩ L).Nonempty ∧ (A \ L).Nonempty

instance crossDecidable (A L : Finset α) : Decidable (Cross A L) :=
  inferInstanceAs (Decidable ((A ∩ L).Nonempty ∧ (A \ L).Nonempty))

def crossCount (P A : Finset α) : Nat :=
  (P.powerset.filter (Cross A)).card

def ownerCount (I : Finset β) (A : β → Finset α) (L : Finset α) : Nat :=
  (I.filter (fun i => Cross (A i) L)).card

theorem cross_count_nonempty (P A : Finset α) (hAP : A ⊆ P)
    (hA : A.Nonempty) :
    crossCount P A = 2 ^ P.card - 2 ^ (P.card - A.card + 1) := by
  have hsets : P.powerset.filter (Cross A) =
      P.powerset \ ((P \ A).powerset ∪ Icc A P) := by
    ext L
    simp only [mem_filter, mem_powerset, Cross, mem_sdiff, mem_union, mem_Icc,
      sdiff_nonempty, ← not_disjoint_iff_nonempty_inter, subset_sdiff]
    rw [disjoint_comm (a := A)]
    tauto
  have hsub : (P \ A).powerset ∪ Icc A P ⊆ P.powerset := by
    intro L hL
    rcases mem_union.mp hL with hL | hL
    · exact mem_powerset.mpr ((mem_powerset.mp hL).trans sdiff_subset)
    · exact mem_powerset.mpr (mem_Icc.mp hL).2
  have hd : Disjoint (P \ A).powerset (Icc A P) := by
    apply disjoint_left.mpr
    intro L hL hLA
    obtain ⟨a, ha⟩ := hA
    have hal : a ∈ L := (mem_Icc.mp hLA).1 ha
    exact (mem_sdiff.mp ((mem_powerset.mp hL) hal)).2 ha
  rw [crossCount, hsets, card_sdiff_of_subset hsub, card_union_of_disjoint hd,
    card_powerset, card_powerset, card_sdiff_of_subset hAP, card_Icc_finset hAP,
    pow_succ]
  omega

theorem double_count (P : Finset α) (I : Finset β) (A : β → Finset α) :
    (∑ i ∈ I, crossCount P (A i)) = ∑ L ∈ P.powerset, ownerCount I A L := by
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun i L => Cross (A i) L)

theorem empty_cut_count (I : Finset β) (A : β → Finset α) :
    ownerCount I A ∅ = 0 := by
  simp [ownerCount, Cross]

theorem full_cut_count (P : Finset α) (I : Finset β) (A : β → Finset α)
    (hAP : ∀ i ∈ I, A i ⊆ P) : ownerCount I A P = 0 := by
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro i hi
  simp only [Cross, sdiff_nonempty, not_and]
  exact fun _ => not_not.mpr (hAP i hi)

theorem total_cross_bound (P : Finset α) (I : Finset β) (A : β → Finset α)
    (hP : P.Nonempty) (hAP : ∀ i ∈ I, A i ⊆ P)
    (hcut : ∀ L ⊆ P, ownerCount I A L ≤ P.card) :
    (∑ i ∈ I, crossCount P (A i)) ≤ P.card * (2 ^ P.card - 2) := by
  let proper := P.powerset \ {∅, P}
  have hpair : ({∅, P} : Finset (Finset α)) ⊆ P.powerset := by
    intro L hL
    have hLeq : L = ∅ ∨ L = P := by simpa only [mem_insert, mem_singleton] using hL
    rcases hLeq with hL | hL
    · rw [hL]
      exact empty_mem_powerset P
    · rw [hL]
      exact mem_powerset_self P
  have hproper : proper ⊆ P.powerset := sdiff_subset
  have hcard : proper.card = 2 ^ P.card - 2 := by
    rw [show proper = P.powerset \ {∅, P} from rfl,
      card_sdiff_of_subset hpair, card_powerset]
    simp [Ne.symm hP.ne_empty]
  have hsum : (∑ L ∈ proper, ownerCount I A L) =
      ∑ L ∈ P.powerset, ownerCount I A L := by
    apply sum_subset hproper
    intro L hLP hLn
    have hL : L = ∅ ∨ L = P := by
      simpa only [proper, mem_sdiff, mem_insert, mem_singleton, hLP, true_and,
        not_not] using hLn
    rcases hL with hL | hL
    · rw [hL]
      exact empty_cut_count I A
    · rw [hL]
      exact full_cut_count P I A hAP
  rw [double_count, ← hsum]
  calc
    _ ≤ ∑ _L ∈ proper, P.card := sum_le_sum fun L hL =>
      hcut L (mem_powerset.mp (hproper hL))
    _ = _ := by simp [hcard, Nat.mul_comm]

theorem cross_count_ge (P A : Finset α) (hAP : A ⊆ P)
    (s : Nat) (hs : 1 ≤ s) (hsA : s ≤ A.card) :
    2 ^ P.card - 2 ^ (P.card - s + 1) ≤ crossCount P A := by
  rw [cross_count_nonempty P A hAP (card_pos.mp (by omega))]
  have he : P.card - A.card + 1 ≤ P.card - s + 1 := by omega
  exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide) he) _

theorem large_support_integer_bound
    (P : Finset α) (I : Finset β) (A : β → Finset α)
    (hP : P.Nonempty) (hAP : ∀ i ∈ I, A i ⊆ P)
    (hcut : ∀ L ⊆ P, ownerCount I A L ≤ P.card)
    (s : Nat) (hs : 1 ≤ s) :
    (I.filter (fun i => s ≤ (A i).card)).card *
        (2 ^ P.card - 2 ^ (P.card - s + 1)) ≤
      P.card * (2 ^ P.card - 2) := by
  let J := I.filter (fun i => s ≤ (A i).card)
  calc
    _ = ∑ _i ∈ J, (2 ^ P.card - 2 ^ (P.card - s + 1)) := by
      simp [J]
    _ ≤ ∑ i ∈ J, crossCount P (A i) := sum_le_sum fun i hi =>
      cross_count_ge P (A i) (hAP i (mem_filter.mp hi).1) s hs (mem_filter.mp hi).2
    _ ≤ ∑ i ∈ I, crossCount P (A i) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
    _ ≤ _ := total_cross_bound P I A hP hAP hcut

end CutAverage

variable {α β : Type*} [DecidableEq α]

def inside (E : Finset β) (l r : β → α) (V : Finset α) : Finset β :=
  E.filter fun e => l e ∈ V ∧ r e ∈ V

def incident (E : Finset β) (l r : β → α) (v : α) : Finset β :=
  E.filter fun e => l e = v ∨ r e = v

def CutCap (V : Finset α) (E : Finset β) (l r : β → α) : Prop :=
  ∀ S ⊆ V, ∀ L ⊆ S,
    CutAverage.ownerCount (inside E l r S) (fun e => {l e, r e}) L ≤ S.card

theorem pair_cross_iff (a b : α) (L : Finset α) :
    CutAverage.Cross {a, b} L ↔
      (a ∈ L ∧ b ∉ L) ∨ (a ∉ L ∧ b ∈ L) := by
  simp only [CutAverage.Cross, Finset.Nonempty,
    mem_inter, mem_sdiff, mem_insert, mem_singleton]
  aesop

theorem sparse_of_cut_cap (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e) (hcap : CutCap V E l r)
    (S : Finset α) (hSV : S ⊆ V) (hS : S.Nonempty) :
    (inside E l r S).card < 2 * S.card := by
  let J := inside E l r S
  have hp : ∀ e ∈ J, ({l e, r e} : Finset α).card = 2 := by
    intro e he
    have h := hne e (mem_filter.mp he).1
    simp [h]
  have hsub : ∀ e ∈ J, ({l e, r e} : Finset α) ⊆ S := by
    intro e he
    have hh := (mem_filter.mp he).2
    simpa only [insert_subset_iff, singleton_subset_iff] using hh
  have hcut : ∀ L ⊆ S, CutAverage.ownerCount J
      (fun e => {l e, r e}) L ≤ S.card := hcap S hSV
  by_cases hJ : J.Nonempty
  · obtain ⟨e, he⟩ := hJ
    have hs2 : 2 ≤ S.card := by simpa only [hp e he] using card_le_card (hsub e he)
    have hb := CutAverage.large_support_integer_bound
      S J (fun e => {l e, r e}) hS hsub hcut 2 (by omega)
    have hf : J.filter (fun e => 2 ≤ ({l e, r e} : Finset α).card) = J := by
      apply filter_eq_self.mpr
      intro e he
      rw [hp e he]
    rw [hf] at hb
    have hexp : S.card - 2 + 1 = S.card - 1 := by omega
    have hpow : 2 ^ S.card = 2 * 2 ^ (S.card - 1) := by
      have hexp' : S.card = S.card - 1 + 1 := by omega
      conv_lhs => rw [hexp']
      rw [pow_succ, Nat.mul_comm]
    rw [hexp, hpow] at hb
    have ht : 0 < 2 ^ (S.card - 1) := pow_pos (by decide) _
    have ha : 2 * 2 ^ (S.card - 1) - 2 + 2 = 2 * 2 ^ (S.card - 1) := by omega
    have hb' : 2 * 2 ^ (S.card - 1) - 2 ^ (S.card - 1) = 2 ^ (S.card - 1) := by omega
    rw [hb'] at hb
    change J.card < 2 * S.card
    nlinarith
  · have hz : J.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hJ)
    change J.card < 2 * S.card
    have := card_pos.mpr hS
    omega

theorem sum_incident (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e)
    (hends : ∀ e ∈ E, l e ∈ V ∧ r e ∈ V) :
    (∑ v ∈ V, (incident E l r v).card) = 2 * E.card := by
  have hd := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := V) (t := E) (fun v e => l e = v ∨ r e = v)
  change (∑ v ∈ V, (incident E l r v).card) =
    ∑ e ∈ E, (V.filter (fun v => l e = v ∨ r e = v)).card at hd
  rw [hd]
  have hp : ∀ e ∈ E, (V.filter (fun v => l e = v ∨ r e = v)).card = 2 := by
    intro e he
    have heq : V.filter (fun v => l e = v ∨ r e = v) = {l e, r e} := by
      ext v
      have hh := hends e he
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · intro h
        exact h.2.imp Eq.symm Eq.symm
      · intro h
        rcases h with h | h <;> subst v <;> simp_all
    rw [heq]
    simp [hne e he]
  calc
    _ = ∑ _e ∈ E, 2 := sum_congr rfl hp
    _ = 2 * E.card := by simp [Nat.mul_comm]

theorem exists_low_degree (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e)
    (hends : ∀ e ∈ E, l e ∈ V ∧ r e ∈ V)
    (hsparse : E.card < 2 * V.card) :
    ∃ v ∈ V, (incident E l r v).card ≤ 3 := by
  by_contra h
  have hdeg : ∀ v ∈ V, 4 ≤ (incident E l r v).card := by
    intro v hv
    by_contra hh
    exact h ⟨v, hv, by omega⟩
  have hh := sum_le_sum hdeg
  have hs := sum_incident V E l r hne hends
  simp only [sum_const, smul_eq_mul] at hh
  rw [hs] at hh
  omega

theorem four_coloring_of_sparse (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e)
    (hsparse : ∀ S ⊆ V, S.Nonempty → (inside E l r S).card < 2 * S.card) :
    ∃ c : α → Fin 4, ∀ e ∈ E, l e ∈ V → r e ∈ V → c (l e) ≠ c (r e) := by
  induction V using Finset.strongInductionOn with
  | _ V ih =>
    by_cases hV : V.Nonempty
    · let J := inside E l r V
      have hJsub : J ⊆ E := filter_subset _ _
      have hJends : ∀ e ∈ J, l e ∈ V ∧ r e ∈ V := by
        intro e he
        exact (mem_filter.mp he).2
      obtain ⟨v, hv, hdeg⟩ := exists_low_degree V J l r
        (fun e he => hne e (hJsub he)) hJends (hsparse V (Subset.refl _) hV)
      obtain ⟨c, hc⟩ := ih (V.erase v) (erase_ssubset hv) (by
        intro S hS hneS
        exact hsparse S (hS.trans (erase_subset v V)) hneS)
      let T := incident J l r v
      let other (e : β) : α := if l e = v then r e else l e
      let used : Finset (Fin 4) := T.image (fun e => c (other e))
      have hused : used.card < (univ : Finset (Fin 4)).card := by
        have hh : used.card ≤ T.card := card_image_le
        have ht : T.card ≤ 3 := hdeg
        simpa using (show used.card < 4 by omega)
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
    · refine ⟨fun _ => 0, ?_⟩
      intro e he hel _
      exact (hV ⟨l e, hel⟩).elim

def balancedSplit (k : Fin 3) (a : Fin 4) : Bool :=
  if k = 0 then decide (a.val < 2)
  else if k = 1 then decide (a.val % 2 = 0)
  else decide (a.val = 0 ∨ a.val = 3)

theorem balancedSplit_count (a b : Fin 4) (hne : a ≠ b) :
    ((univ : Finset (Fin 3)).filter fun k => balancedSplit k a ≠ balancedSplit k b).card = 2 := by
  fin_cases a <;> fin_cases b <;> first | exact (hne rfl).elim | decide

theorem density_of_four_coloring (V : Finset α) (E : Finset β) (l r : β → α)
    (hends : ∀ e ∈ E, l e ∈ V ∧ r e ∈ V)
    (hcut : ∀ L ⊆ V,
      CutAverage.ownerCount E (fun e => {l e, r e}) L ≤ V.card)
    (c : α → Fin 4) (hc : ∀ e ∈ E, c (l e) ≠ c (r e)) :
    2 * E.card ≤ 3 * V.card := by
  let cuts (k : Fin 3) := V.filter fun v => balancedSplit k (c v) = true
  have hcap (k : Fin 3) :
      (E.filter fun e => balancedSplit k (c (l e)) ≠ balancedSplit k (c (r e))).card ≤ V.card := by
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
      cases balancedSplit k (c (l e)) <;> cases balancedSplit k (c (r e)) <;> decide
    · simp [he]
  have hd := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset (Fin 3))) (t := E)
    (fun k e => balancedSplit k (c (l e)) ≠ balancedSplit k (c (r e)))
  change (∑ k : Fin 3, (E.filter fun e =>
      balancedSplit k (c (l e)) ≠ balancedSplit k (c (r e))).card) =
    ∑ e ∈ E, ((univ : Finset (Fin 3)).filter fun k =>
      balancedSplit k (c (l e)) ≠ balancedSplit k (c (r e))).card at hd
  have heq : (∑ k : Fin 3, (E.filter fun e =>
      balancedSplit k (c (l e)) ≠ balancedSplit k (c (r e))).card) = 2 * E.card := by
    rw [hd]
    calc
      _ = ∑ _e ∈ E, 2 := sum_congr rfl fun e he => balancedSplit_count _ _ (hc e he)
      _ = 2 * E.card := by simp [Nat.mul_comm]
  have hh := sum_le_sum (fun (k : Fin 3) (_ : k ∈ univ) => hcap k)
  rw [heq] at hh
  simpa using hh

theorem bipartite_pseudoforest_density (V : Finset α) (E : Finset β) (l r : β → α)
    (hne : ∀ e ∈ E, l e ≠ r e)
    (hends : ∀ e ∈ E, l e ∈ V ∧ r e ∈ V)
    (hcap : CutCap V E l r) : 2 * E.card ≤ 3 * V.card := by
  obtain ⟨c, hc⟩ := four_coloring_of_sparse V E l r hne
    (sparse_of_cut_cap V E l r hne hcap)
  apply density_of_four_coloring V E l r hends _ c
    (fun e he => hc e he (hends e he).1 (hends e he).2)
  have heq : inside E l r V = E := filter_eq_self.mpr hends
  simpa only [heq] using hcap V (Subset.refl V)

end D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity
