/- GID: D5/S3/Combinatorics/Interpolation/AbrCoordinateBoxStraightening
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrCoordinateBoxStraightening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: ABR descent straightening preserves a coordinate box in multivariate polynomials. -/

import D5.S3.Combinatorics.Interpolation.AbrCoordinateExchange
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
This module formalizes the descent-monomial straightening argument of
Adin--Brenti--Roichman, Sections 3.1--3.4.  The filtration used here is the
coordinate box: every variable exponent is bounded independently.  In
particular, the maximum descent exponent is the number of descents; its total
degree is the major index and is not used as the box bound.

Source: R. M. Adin, F. Brenti, Y. Roichman, Trans. Amer. Math. Soc. 357
(2005), DOI 10.1090/S0002-9947-04-03494-4, Claim 3.1 through Lemma 3.5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening

open scoped BigOperators
theorem sum_le_prefixWeight {n : Nat} (a : Fin n →₀ Nat)
    (s : Finset (Fin n)) :
    (∑ x ∈ s, a x) ≤ prefixWeight a s.card := by
  classical
  have hanti : Antitone (fun i => a (indexPerm a i)) :=
    fun i j hij =>
      Tuple.monotone_sort (fun x : Fin n => OrderDual.toDual (a x)) hij
  let pi := indexPerm a
  let positions := s.image pi.symm
  have hcard : positions.card = s.card := by
    exact Finset.card_image_of_injective s pi.symm.injective
  let e : Fin s.card ↪o Fin n := positions.orderEmbOfFin hcard
  have hrewrite : (∑ x ∈ s, a x) = ∑ j ∈ positions, a (pi j) := by
    calc
      (∑ x ∈ s, a x) = ∑ x ∈ s, a (pi (pi.symm x)) := by simp [pi]
      _ = ∑ j ∈ positions, a (pi j) := by
        symm
        simpa [positions] using
          (Finset.sum_image (s := s) (f := fun j => a (pi j)) pi.symm.injective)
  have henum : (∑ j ∈ positions, a (pi j)) =
      ∑ i : Fin s.card, a (pi (e i)) := by
    calc
      (∑ j ∈ positions, a (pi j)) =
          ∑ j : positions, a (pi j.1) :=
        (Finset.sum_attach positions (fun j => a (pi j))).symm
      _ = ∑ i : Fin s.card, a (pi (e i)) := by
        simpa [e] using
          ((positions.orderIsoOfFin hcard).toEquiv.sum_comp
            (fun j : positions => a (pi j.1))).symm
  have hsle : s.card ≤ n := by simpa using Finset.card_le_univ s
  have hprefix : prefixWeight a s.card =
      ∑ i : Fin s.card, a (indexPerm a (Fin.castLE hsle i)) := by
    have hset : (Finset.univ.filter fun i : Fin n => i.val < s.card) =
        Finset.univ.image (Fin.castLE hsle) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hx
        exact ⟨⟨x.val, hx⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact i.isLt
    rw [prefixWeight, hset, Finset.sum_image]
    exact (Fin.castLE_injective hsle).injOn
  rw [hrewrite, henum, hprefix]
  apply Finset.sum_le_sum
  intro i _
  apply hanti
  exact Fin.mk_le_mk.mpr (fin_val_le_orderEmbedding e i)

theorem prefixWeight_leadExponent {n : Nat} (a : Fin n →₀ Nat) (h k : Nat) :
    prefixWeight (leadExponent a h) k =
      prefixWeight a k + min (min n k) h := by
  classical
  have hindicator (i : Fin n) :
      subsetExponent (initialSet a h) (indexPerm a i) =
        if i.val < h then 1 else 0 := by
    simp [subsetExponent, Finsupp.indicator_apply, initialSet]
  unfold prefixWeight
  rw [indexPerm_leadExponent]
  simp_rw [leadExponent, Finsupp.add_apply, hindicator]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show min (min n k) h = min n (min k h) by omega,
    ← Fin.card_filter_val_lt]
  rw [← Finset.card_filter]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- Every squarefree summand in the one-factor expansion is dominated by the
stable initial-segment leader. -/
theorem oneFactor_dominatedBy {n h : Nat} (a : Fin n →₀ Nat)
    (t : Finset (Fin n)) (ht : t.card = h) :
    DominatedBy (a + subsetExponent t) (leadExponent a h) := by
  classical
  have hsumSubset (s u : Finset (Fin n)) :
      (∑ x ∈ s, subsetExponent u x) = (s ∩ u).card := by
    simp [subsetExponent, Finsupp.indicator_apply, Finset.card_inter]
  have hcardInitial (u : Fin n →₀ Nat) {m : Nat} (hm : m ≤ n) :
      (initialSet u m).card = m := by
    let e := indexPerm u
    have himage : initialSet u m =
        (Finset.univ.filter fun i : Fin n => i.val < m).image e := by
      ext x
      simp only [initialSet, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, e]
      constructor
      · intro hx
        exact ⟨(indexPerm u).symm x, hx, by simp⟩
      · rintro ⟨i, hi, rfl⟩
        simpa using hi
    rw [himage, Finset.card_image_of_injective _ e.injective]
    simpa [Nat.min_eq_right hm] using (Fin.card_filter_val_lt (n := n) (m := m))
  have hcardInitialGeneral (u : Fin n →₀ Nat) (m : Nat) :
      (initialSet u m).card = min n m := by
    let e := indexPerm u
    have himage : initialSet u m =
        (Finset.univ.filter fun i : Fin n => i.val < m).image e := by
      ext x
      simp only [initialSet, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, e]
      constructor
      · intro hx
        exact ⟨(indexPerm u).symm x, hx, by simp⟩
      · rintro ⟨i, hi, rfl⟩
        simpa using hi
    rw [himage, Finset.card_image_of_injective _ e.injective]
    exact Fin.card_filter_val_lt
  have hprefixInitial (u : Fin n →₀ Nat) (m : Nat) :
      prefixWeight u m = ∑ x ∈ initialSet u m, u x := by
    have hset : initialSet u m =
        (Finset.univ.filter fun i : Fin n => i.val < m).image (indexPerm u) := by
      ext x
      simp only [initialSet, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact ⟨(indexPerm u).symm x, hx, by simp⟩
      · rintro ⟨i, hi, rfl⟩
        simpa using hi
    rw [prefixWeight, hset, Finset.sum_image]
    exact (indexPerm u).injective.injOn
  have hprefixMin (u : Fin n →₀ Nat) (m : Nat) :
      prefixWeight u (min n m) = prefixWeight u m := by
    unfold prefixWeight
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  constructor
  · have hh : h ≤ n := by
      rw [← ht]
      simpa using Finset.card_le_univ t
    change (Finset.univ.sum fun x : Fin n =>
        a x + subsetExponent t x) =
      (Finset.univ.sum fun x : Fin n =>
        a x + subsetExponent (initialSet a h) x)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hsumSubset, hsumSubset]
    simp [ht, hcardInitial a hh]
  · intro k
    let s := initialSet (a + subsetExponent t) k
    have hscard : s.card = min n k := hcardInitialGeneral _ _
    have ha : (∑ x ∈ s, a x) ≤ prefixWeight a s.card :=
      sum_le_prefixWeight a s
    have hinter : (s ∩ t).card ≤ min s.card t.card := by
      exact le_min
        (Finset.card_le_card Finset.inter_subset_left)
        (Finset.card_le_card Finset.inter_subset_right)
    rw [hprefixInitial, prefixWeight_leadExponent]
    change (s.sum fun i => a i + subsetExponent t i) ≤ _
    rw [Finset.sum_add_distrib, hsumSubset]
    rw [ht, hscard] at hinter
    rw [hscard, hprefixMin] at ha
    omega

/-- If a squarefree summand has the leader's sorted exponent partition but
uses a different subset, its stable index permutation has strictly more
inversions.  This is the equal-partition clause of ABR Lemma 3.2. -/
theorem inversionCount_indexPerm_lt_of_sorted_eq {n h : Nat}
    (a : Fin n →₀ Nat) (t : Finset (Fin n))
    (hsorted :
      (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
        fun i => leadExponent a h (indexPerm (leadExponent a h) i))
    (hne : t ≠ initialSet a h) :
    inversionCount (indexPerm (leadExponent a h)) <
      inversionCount (indexPerm (a + subsetExponent t)) := by
  classical
  rw [inversionCount_indexPerm, inversionCount_indexPerm]
  let leaderPairs := (Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ leadExponent a h p.1 < leadExponent a h p.2)
  let termPairs := (Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (a + subsetExponent t) p.1 < (a + subsetExponent t) p.2)
  change leaderPairs.card < termPairs.card
  have hbase {x y : Fin n} (hxy : x < y)
      (hlt : leadExponent a h x < leadExponent a h y) : a x < a y := by
    by_contra hnot
    have hayx : a y ≤ a x := le_of_not_gt hnot
    by_cases heq : a x = a y
    · by_cases hxi : x ∈ initialSet a h
      · by_cases hyi : y ∈ initialSet a h <;>
          simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hxi, hyi, heq] at hlt
      · have hyi : y ∉ initialSet a h := by
          intro hyi
          exact hxi (mem_initialSet_of_tie_lt a h hxy heq hyi)
        simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hxi, hyi, heq] at hlt
    · have hayx' : a y < a x := lt_of_le_of_ne hayx (Ne.symm heq)
      by_cases hxi : x ∈ initialSet a h <;>
        by_cases hyi : y ∈ initialSet a h <;>
          simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hxi, hyi] at hlt <;> omega
  have hsubset : leaderPairs ⊆ termPairs := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hpuniv, hxy, hleader⟩
    refine ⟨hpuniv, hxy, ?_⟩
    have hab : a p.1 < a p.2 := hbase hxy hleader
    by_cases hxt : p.1 ∈ t
    · by_cases hyt : p.2 ∈ t
      · simp [subsetExponent, Finsupp.indicator_apply, hxt, hyt]
        exact hab
      · simp [subsetExponent, Finsupp.indicator_apply, hxt, hyt]
        by_contra hnot
        have hsucc : a p.2 = a p.1 + 1 := by omega
        by_cases hxi : p.1 ∈ initialSet a h
        · have hyi : p.2 ∈ initialSet a h :=
            mem_initialSet_of_exponent_lt a h hab hxi
          obtain ⟨q, hqa, hqt, hqi⟩ :=
            exists_selected_mismatch_of_initial_mismatch a t hsorted hyi hyt
          exact hqi (mem_initialSet_of_exponent_lt a h
            (hab.trans_eq hqa.symm) hxi)
        · have hxmis : (p.1 ∈ t) ≠ (p.1 ∈ initialSet a h) := by
            simp [hxt, hxi]
          obtain ⟨q, hqa, hqi, hqt⟩ :=
            exists_initial_mismatch_of_selected_mismatch a t hsorted hxt hxi
          have hyi : p.2 ∈ initialSet a h :=
            mem_initialSet_of_exponent_lt a h (hqa.trans_lt hab) hqi
          have hymis : (p.2 ∈ t) ≠ (p.2 ∈ initialSet a h) := by
            simp [hyt, hyi]
          have heq := exponent_eq_of_membership_mismatch a t hsorted hxmis hymis
          omega
    · by_cases hyt : p.2 ∈ t <;>
        simp [subsetExponent, Finsupp.indicator_apply, hxt, hyt] <;> omega
  have hmismatch : ∃ x : Fin n,
      ¬ (x ∈ t ↔ x ∈ initialSet a h) := by
    by_contra hnone
    push_neg at hnone
    apply hne
    ext x
    exact hnone x
  obtain ⟨x, hx⟩ := hmismatch
  have hxne : (x ∈ t) ≠ (x ∈ initialSet a h) := by
    intro heq
    apply hx
    rw [heq]
  have exchange :
      ∃ p m, a p = a x ∧ a m = a x ∧
        p ∈ t ∧ p ∉ initialSet a h ∧
        m ∈ initialSet a h ∧ m ∉ t := by
    by_cases hxt : x ∈ t
    · have hxi : x ∉ initialSet a h := by
        intro hmem
        exact hxne (propext ⟨fun _ => hmem, fun _ => hxt⟩)
      obtain ⟨m, hma, hmi, hmt⟩ :=
        exists_initial_mismatch_of_selected_mismatch a t hsorted hxt hxi
      exact ⟨x, m, rfl, hma, hxt, hxi, hmi, hmt⟩
    · have hxi : x ∈ initialSet a h := by
        by_contra hni
        exact hxne (propext ⟨fun hmem => (hxt hmem).elim,
          fun hmem => (hni hmem).elim⟩)
      obtain ⟨p, hpa, hpt, hpi⟩ :=
        exists_selected_mismatch_of_initial_mismatch a t hsorted hxi hxt
      exact ⟨p, x, hpa, rfl, hpt, hpi, hxi, hxt⟩
  obtain ⟨p, m, hpa, hma, hpt, hpi, hmi, hmt⟩ := exchange
  have hmp : m < p := by
    by_contra hnot
    have hnepm : p ≠ m := by
      intro heq
      exact hmt (heq ▸ hpt)
    have hpm : p < m := lt_of_le_of_ne (le_of_not_gt hnot) hnepm
    exact hpi (mem_initialSet_of_tie_lt a h hpm (hpa.trans hma.symm) hmi)
  have hwitnessTerm : (m, p) ∈ termPairs := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      hmp, ?_⟩
    simp [subsetExponent, Finsupp.indicator_apply, hpt, hmt, hpa, hma]
  have hwitnessLeader : (m, p) ∉ leaderPairs := by
    rw [Finset.mem_filter]
    simp only [Finset.mem_product, Finset.mem_univ, and_self, not_and]
    intro _
    simp [leadExponent, subsetExponent, Finsupp.indicator_apply, hpi, hmi, hpa, hma]
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset hsubset).mpr
      ⟨(m, p), hwitnessTerm, hwitnessLeader⟩)

/-- Every nonleader squarefree summand is strictly below the stable leader in
the ABR dominance/reverse-inversion order. -/
theorem oneFactor_abrLower {n h : Nat} (a : Fin n →₀ Nat)
    (t : Finset (Fin n)) (ht : t.card = h)
    (hne : t ≠ initialSet a h) :
    AbrLower (a + subsetExponent t) (leadExponent a h) := by
  have hprefixStep (u : Fin n →₀ Nat) (i : Fin n) :
      prefixWeight u (i.val + 1) =
        prefixWeight u i.val + u (indexPerm u i) := by
    have hsucc : i.val + 1 ≤ n := i.isLt
    have hval : i.val ≤ n := le_trans (Nat.le_succ _) hsucc
    have hsumFin (m : Nat) (hm : m ≤ n) :
        prefixWeight u m =
          ∑ j : Fin m, u (indexPerm u (Fin.castLE hm j)) := by
      have hset : (Finset.univ.filter fun j : Fin n => j.val < m) =
          Finset.univ.image (Fin.castLE hm) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hx
          exact ⟨⟨x.val, hx⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          exact j.isLt
      rw [prefixWeight, hset, Finset.sum_image]
      exact (Fin.castLE_injective hm).injOn
    rw [hsumFin (i.val + 1) hsucc, hsumFin i.val hval, Fin.sum_univ_castSucc]
    congr
  have hdom := oneFactor_dominatedBy a t ht
  by_cases hreverse : DominatedBy (leadExponent a h) (a + subsetExponent t)
  · right
    have hsorted :
        (fun i => (a + subsetExponent t) (indexPerm (a + subsetExponent t) i)) =
          fun i => leadExponent a h (indexPerm (leadExponent a h) i) := by
      funext i
      have hprefix :
          prefixWeight (a + subsetExponent t) i.val =
            prefixWeight (leadExponent a h) i.val :=
        le_antisymm (hdom.2 i.val) (hreverse.2 i.val)
      have hprefixSucc :
          prefixWeight (a + subsetExponent t) (i.val + 1) =
            prefixWeight (leadExponent a h) (i.val + 1) :=
        le_antisymm (hdom.2 (i.val + 1)) (hreverse.2 (i.val + 1))
      rw [hprefixStep, hprefixStep, hprefix] at hprefixSucc
      omega
    exact ⟨hsorted, inversionCount_indexPerm_lt_of_sorted_eq a t hsorted hne⟩
  · exact Or.inl ⟨hdom, hreverse⟩

end D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
