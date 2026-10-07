/- GID: D5/S3/Combinatorics/Probability/FiniteCliqueAvoidance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/FiniteCliqueAvoidance
   mirror-E: none(waiver:symbolic-finite-event-inequality)
   anchors: []
   utility: none
   digest: Coordinate-deletion positivity controls actual avoidance and conditional queries. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime.Probability

/-!
The finite rational form of the coordinate-clique induction in Hough and
Nielsen, Covering systems with restricted divisibility, Appendix C, Theorem 16.
The comparison function is supplied with its exact deletion recurrence;
identifying it with a particular independent-set polynomial is a separate input.
All events and all conditional queries use one actual finite probability law.
-/

namespace D5.S3.Combinatorics.Probability.FiniteCliqueAvoidance

open Erdos7
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

/-- Avoid all nonempty event supports contained in the coordinate set. -/
def Avoids (A : Finset ι → Ω → Prop) (R : Finset ι) (ω : Ω) : Prop :=
  ∀ S : Finset ι, S ⊆ R → S.Nonempty → ¬ A S ω

/-- The avoidance mass is computed under the original finite law. -/
noncomputable abbrev avoidance (μ : FiniteLaw Ω) (A : Finset ι → Ω → Prop)
    (R : Finset ι) : ℚ := by
  classical
  exact μ.prob (Avoids A R)

omit [Fintype Ω] [DecidableEq ι] in
private theorem avoids_mono (A : Finset ι → Ω → Prop) {R T : Finset ι}
    (hRT : R ⊆ T) {ω : Ω} (h : Avoids A T ω) : Avoids A R ω :=
  fun S hS hne => h S (hS.trans hRT) hne

omit [DecidableEq ι] in
private theorem avoidance_empty (μ : FiniteLaw Ω) (A : Finset ι → Ω → Prop) :
    avoidance μ A ∅ = 1 := by
  classical
  unfold avoidance
  have h : Avoids A ∅ = fun _ => True := by
    funext ω
    apply propext
    simp [Avoids, Finset.subset_empty]
  rw [h]
  simpa only [FiniteLaw.prob, FiniteLaw.expect, if_true, mul_one] using μ.weight_sum

/-- Removing the new-coordinate events loses at most their actual union mass,
and disjoint-support independence bounds that loss using smaller avoidances. -/
private theorem avoidance_insert_lower (μ : FiniteLaw Ω)
    (A : Finset ι → Ω → Prop) (P : Finset ι) (t : Finset ι → ℚ)
    (hcap : ∀ S ⊆ P, S.Nonempty → μ.prob (A S) ≤ t S)
    (hind : ∀ S R, S ⊆ P → S.Nonempty → R ⊆ P → Disjoint S R →
      μ.prob (fun ω => A S ω ∧ Avoids A R ω) =
        μ.prob (A S) * avoidance μ A R)
    (R : Finset ι) (p : ι) (hp : p ∉ R) (hR : insert p R ⊆ P) :
    avoidance μ A R -
      ∑ U ∈ R.powerset, t (insert p U) * avoidance μ A (R \ U) ≤
        avoidance μ A (insert p R) := by
  classical
  have hRP : R ⊆ P := (Finset.subset_insert p R).trans hR
  have hsplit : avoidance μ A R = avoidance μ A (insert p R) +
      μ.prob (fun ω => Avoids A R ω ∧ ¬ Avoids A (insert p R) ω) := by
    unfold avoidance FiniteLaw.prob
    rw [← μ.expect_add]
    apply μ.expect_congr
    intro ω
    by_cases hT : Avoids A (insert p R) ω
    · have hRω := avoids_mono A (Finset.subset_insert p R) hT
      simp [hT, hRω]
    · by_cases hRω : Avoids A R ω <;> simp [hT, hRω]
  have hcovered : ∀ ω, (Avoids A R ω ∧ ¬ Avoids A (insert p R) ω) →
      ∃ U ∈ R.powerset, A (insert p U) ω ∧ Avoids A R ω := by
    intro ω ⟨hgood, hbad⟩
    simp only [Avoids, not_forall] at hbad
    obtain ⟨S, hbad⟩ := hbad
    push Not at hbad
    obtain ⟨hS, hne, hAS⟩ := hbad
    have hpS : p ∈ S := by
      by_contra hn
      have hSR : S ⊆ R := by
        intro x hx
        rcases Finset.mem_insert.mp (hS hx) with he | hxR
        · subst x
          exact False.elim (hn hx)
        · exact hxR
      exact hgood S hSR hne hAS
    refine ⟨S.erase p, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp (hS (Finset.mem_of_mem_erase hx)) with he | hxR
      · exact False.elim ((Finset.mem_erase.mp hx).1 he)
      · exact hxR
    · simpa only [Finset.insert_erase hpS] using And.intro hAS hgood
  have hsum : μ.prob (fun ω => Avoids A R ω ∧ ¬ Avoids A (insert p R) ω) ≤
      ∑ U ∈ R.powerset, t (insert p U) * avoidance μ A (R \ U) := by
    calc
      _ ≤ μ.prob (fun ω => ∃ U ∈ R.powerset,
          A (insert p U) ω ∧ Avoids A R ω) := μ.prob_mono _ _ hcovered
      _ ≤ ∑ U ∈ R.powerset, μ.prob (fun ω =>
          A (insert p U) ω ∧ Avoids A R ω) :=
        μ.prob_exists_finset_le_sum R.powerset _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro U hU
        have hUR := Finset.mem_powerset.mp hU
        have hSP : insert p U ⊆ P := (Finset.insert_subset_insert p hUR).trans hR
        have hd : Disjoint (insert p U) (R \ U) := by
          apply Finset.disjoint_left.mpr
          intro x hx hxR
          rcases Finset.mem_insert.mp hx with rfl | hxU
          · exact hp (Finset.mem_sdiff.mp hxR).1
          · exact (Finset.mem_sdiff.mp hxR).2 hxU
        calc
          _ ≤ μ.prob (fun ω => A (insert p U) ω ∧ Avoids A (R \ U) ω) :=
            μ.prob_mono _ _ (fun _ h =>
              ⟨h.1, avoids_mono A Finset.sdiff_subset h.2⟩)
          _ = μ.prob (A (insert p U)) * avoidance μ A (R \ U) :=
            hind _ _ hSP (Finset.insert_nonempty _ _) (Finset.sdiff_subset.trans hRP) hd
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (hcap _ hSP (Finset.insert_nonempty _ _)) (μ.prob_nonneg _)
  linarith

/-- The coordinate deletion induction compares every pair of nested actual
avoidance events. Strict positivity is established rather than assumed. -/
private theorem avoidance_comparison (μ : FiniteLaw Ω)
    (A : Finset ι → Ω → Prop) (P : Finset ι) (t ρ : Finset ι → ℚ)
    (hcap : ∀ S ⊆ P, S.Nonempty → μ.prob (A S) ≤ t S)
    (hind : ∀ S R, S ⊆ P → S.Nonempty → R ⊆ P → Disjoint S R →
      μ.prob (fun ω => A S ω ∧ Avoids A R ω) =
        μ.prob (A S) * avoidance μ A R)
    (hρpos : ∀ R ⊆ P, 0 < ρ R)
    (hrec : ∀ R p, p ∉ R → insert p R ⊆ P →
      ρ (insert p R) = ρ R - ∑ U ∈ R.powerset, t (insert p U) * ρ (R \ U)) :
    ∀ T ⊆ P, 0 < avoidance μ A T ∧
      ∀ S ⊆ T, ρ T / ρ S ≤ avoidance μ A T / avoidance μ A S := by
  classical
  intro T
  refine Finset.strongInductionOn T ?_
  intro T ih hTP
  have hρT := hρpos T hTP
  have hstep : ∀ p ∈ T, ρ T / ρ (T.erase p) ≤
      avoidance μ A T / avoidance μ A (T.erase p) := by
    intro p hpT
    let R := T.erase p
    have hRp : p ∉ R := Finset.notMem_erase p T
    have hRT : R ⊂ T := Finset.erase_ssubset hpT
    have hRP : R ⊆ P := hRT.subset.trans hTP
    have hinsert : insert p R = T := Finset.insert_erase hpT
    obtain ⟨hZR, hratios⟩ := ih R hRT hRP
    have hρR := hρpos R hRP
    have hsum :
        (∑ U ∈ R.powerset, t (insert p U) * avoidance μ A (R \ U)) * ρ R ≤
          (∑ U ∈ R.powerset, t (insert p U) * ρ (R \ U)) * avoidance μ A R := by
      simp only [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro U hU
      have hUR := Finset.mem_powerset.mp hU
      have hρD := hρpos (R \ U) (Finset.sdiff_subset.trans hRP)
      have hZD : 0 < avoidance μ A (R \ U) :=
        (ih (R \ U) (Finset.ssubset_of_subset_of_ssubset Finset.sdiff_subset hRT)
          (Finset.sdiff_subset.trans hRP)).1
      have hratio := hratios (R \ U) Finset.sdiff_subset
      have hcross : avoidance μ A (R \ U) * ρ R ≤
          ρ (R \ U) * avoidance μ A R := by
        simpa only [mul_comm] using (div_le_div_iff₀ hρD hZD).mp hratio
      have htU : 0 ≤ t (insert p U) := (μ.prob_nonneg _).trans
        (hcap _ ((Finset.insert_subset_insert p hUR).trans (hinsert ▸ hTP))
          (Finset.insert_nonempty _ _))
      nlinarith [mul_le_mul_of_nonneg_left hcross htU]
    have hlower := avoidance_insert_lower μ A P t hcap hind R p hRp (hinsert ▸ hTP)
    rw [hinsert] at hlower
    have hrecR := hrec R p hRp (hinsert ▸ hTP)
    rw [hinsert] at hrecR
    apply (div_le_div_iff₀ hρR hZR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlower hρR.le]
  have hZT : 0 < avoidance μ A T := by
    rcases T.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · rw [avoidance_empty]
      norm_num
    · have hRT := Finset.erase_ssubset hp
      have hRP := hRT.subset.trans hTP
      have hZR := (ih (T.erase p) hRT hRP).1
      have h := hstep p hp
      have hpos : 0 < avoidance μ A T / avoidance μ A (T.erase p) :=
        lt_of_lt_of_le (div_pos hρT (hρpos _ hRP)) h
      exact (div_pos_iff_of_pos_right hZR).mp hpos
  refine ⟨hZT, ?_⟩
  intro S hST
  by_cases heq : S = T
  · subst S
    simp [ne_of_gt hρT, ne_of_gt hZT]
  · have hproper : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, heq⟩
    obtain ⟨p, hpT, hpS⟩ := Finset.exists_of_ssubset hproper
    have hRT := Finset.erase_ssubset hpT
    have hRP := hRT.subset.trans hTP
    have hSR : S ⊆ T.erase p := Finset.subset_erase.mpr ⟨hST, hpS⟩
    obtain ⟨hZR, hratioR⟩ := ih (T.erase p) hRT hRP
    have hρR := hρpos _ hRP
    have hρS := hρpos S (hST.trans hTP)
    have hZS := (ih S hproper (hST.trans hTP)).1
    have hc1 := (div_le_div_iff₀ hρR hZR).mp (hstep p hpT)
    have hc2 := (div_le_div_iff₀ hρS hZS).mp (hratioR S hSR)
    apply (div_le_div_iff₀ hρS hZS).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc1 hρS.le,
      mul_le_mul_of_nonneg_right hc2 hρT.le]

/-- Finite clique-Shearer comparison and its same-law conditional-query bound.
The activities majorize actual events; the comparison function has a positive
coordinate-deletion recurrence. Query independence concerns the entire
complementary avoidance event, not merely each bad event separately. -/
theorem finite_clique_avoidance (μ : FiniteLaw Ω)
    (A : Finset ι → Ω → Prop) (P : Finset ι) (t ρ : Finset ι → ℚ)
    (hcap : ∀ S ⊆ P, S.Nonempty → μ.prob (A S) ≤ t S)
    (hind : ∀ S R, S ⊆ P → S.Nonempty → R ⊆ P → Disjoint S R →
      μ.prob (fun ω => A S ω ∧ Avoids A R ω) =
        μ.prob (A S) * avoidance μ A R)
    (hρ0 : ρ ∅ = 1) (hρpos : ∀ R ⊆ P, 0 < ρ R)
    (hrec : ∀ R p, p ∉ R → insert p R ⊆ P →
      ρ (insert p R) = ρ R - ∑ U ∈ R.powerset, t (insert p U) * ρ (R \ U)) :
    (∀ T ⊆ P, ρ T ≤ avoidance μ A T ∧ 0 < avoidance μ A T ∧
      ∀ S ⊆ T, ρ T / ρ S ≤ avoidance μ A T / avoidance μ A S) ∧
    ∃ hP : 0 < avoidance μ A P,
      ∀ (Q : Finset ι) (E : Ω → Prop) [DecidablePred E], Q ⊆ P →
        μ.prob (fun ω => E ω ∧ Avoids A (P \ Q) ω) =
          μ.prob E * avoidance μ A (P \ Q) →
        (μ.condition (Avoids A P) hP).prob E ≤
          μ.prob E * ρ (P \ Q) / ρ P := by
  classical
  have hcomp := avoidance_comparison μ A P t ρ hcap hind hρpos hrec
  have hP := (hcomp P (Finset.Subset.refl P)).1
  refine ⟨?_, hP, ?_⟩
  · intro T hTP
    obtain ⟨hpos, hrat⟩ := hcomp T hTP
    have habs := hrat ∅ (Finset.empty_subset T)
    rw [hρ0, avoidance_empty, div_one, div_one] at habs
    exact ⟨habs, hpos, hrat⟩
  · intro Q E _ hQP hE
    rw [μ.condition_prob]
    have hsmall := (hcomp (P \ Q) Finset.sdiff_subset).1
    have hρP := hρpos P (Finset.Subset.refl P)
    have hρsmall := hρpos (P \ Q) Finset.sdiff_subset
    have hratio := (hcomp P (Finset.Subset.refl P)).2 (P \ Q) Finset.sdiff_subset
    have hcross := (div_le_div_iff₀ hρsmall hsmall).mp hratio
    have hnum : μ.prob (fun ω => Avoids A P ω ∧ E ω) ≤
        μ.prob E * avoidance μ A (P \ Q) := by
      calc
        _ ≤ μ.prob (fun ω => E ω ∧ Avoids A (P \ Q) ω) :=
          μ.prob_mono _ _ (fun _ h => ⟨h.2, avoids_mono A Finset.sdiff_subset h.1⟩)
        _ = _ := hE
    apply (div_le_div_iff₀ hP hρP).mpr
    nlinarith [mul_le_mul_of_nonneg_right hnum hρP.le,
      mul_le_mul_of_nonneg_left hcross (μ.prob_nonneg E)]

#print axioms finite_clique_avoidance

end D5.S3.Combinatorics.Probability.FiniteCliqueAvoidance
