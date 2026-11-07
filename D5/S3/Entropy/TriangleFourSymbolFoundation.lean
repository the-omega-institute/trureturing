/- GID: D5/S3/Entropy/TriangleFourSymbolFoundation
   generality: G
   mirror-B: D5/B/S3/Entropy/TriangleFourSymbolFoundation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite entropy and cross-support foundations for common-record recovery on original stochastic triangle laws. -/

import Mathlib.Tactic
import D5.S3.Divergence.ClassicalDPI
import D5.S3.Entropy.MaxEntropy
import D5.S3.Entropy.ConditionalEntropy
import D5.S3.Entropy.Submodularity.StrongSubadditivity
import D5.S3.Entropy.MutualInformationIndependence
import D5.S3.Entropy.Relabeling.InjectiveInvariance

/-! Finite incident laws retain structural zeros and all original source symbols. -/

namespace D5.S3.Entropy.TriangleFourSymbolNecessity

open scoped BigOperators
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.MutualInformationIndependence
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Relabeling.InjectiveInvariance

/-- The original finite source law and the three incident stochastic kernels.
No source independence, source-cardinality bound, or strict positivity is imposed. -/
structure IncidentLaw (S₁ S₂ S₃ O : Type*)
    [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype O] where
  nu : S₁ × S₂ × S₃ → ℝ
  nu_nonneg : ∀ s, 0 ≤ nu s
  nu_sum : ∑ s, nu s = 1
  KA : S₂ → S₃ → O → ℝ
  KB : S₃ → S₁ → O → ℝ
  KC : S₁ → S₂ → O → ℝ
  KA_nonneg : ∀ s₂ s₃ x, 0 ≤ KA s₂ s₃ x
  KB_nonneg : ∀ s₃ s₁ x, 0 ≤ KB s₃ s₁ x
  KC_nonneg : ∀ s₁ s₂ x, 0 ≤ KC s₁ s₂ x
  KA_sum : ∀ s₂ s₃, ∑ x, KA s₂ s₃ x = 1
  KB_sum : ∀ s₃ s₁, ∑ x, KB s₃ s₁ x = 1
  KC_sum : ∀ s₁ s₂, ∑ x, KC s₁ s₂ x = 1

variable {S₁ S₂ S₃ O : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype O]

namespace FiniteEntropy

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

noncomputable def yz (p : A × B × C → ℝ) : B × C → ℝ :=
  marginal (fun q : (B × C) × A => p (q.2, q.1))

noncomputable def dual (p : A × B × C → ℝ) : ℝ :=
  shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) +
    shannonEntropy (yz p) - 2 * shannonEntropy p

theorem dual_nonneg (p : A × B × C → ℝ)
    (hp : (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1) : 0 ≤ dual p := by
  have h1 := entropy_submodular p hp
  have h2 := entropy_subadditive p hp
  change 0 ≤ shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) +
    shannonEntropy (yz p) - 2 * shannonEntropy p
  change shannonEntropy p ≤ shannonEntropy (marginal p) + shannonEntropy (yz p) at h2
  linarith

theorem dual_zero_product (p : A × B × C → ℝ)
    (hp : (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1) (hz : dual p = 0) :
    ∀ a b c, p (a, b, c) = marginal p a * marginal (yz p) b *
      marginal (fun q : C × B => yz p (q.2, q.1)) c := by
  classical
  have hs := entropy_submodular p hp
  have hm := mutual_information_nonneg p hp
  rw [mutual_information_eq_entropy_sub p hp.1] at hm
  change 0 ≤ shannonEntropy (marginal p) + shannonEntropy (yz p) -
    shannonEntropy p at hm
  change shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) +
    shannonEntropy (yz p) - 2 * shannonEntropy p = 0 at hz
  have he : shannonEntropy p + shannonEntropy (marginal p) =
      shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) := by linarith
  have hmi : mutualInformation p = 0 := by
    rw [mutual_information_eq_entropy_sub p hp.1]
    change shannonEntropy (marginal p) + shannonEntropy (yz p) - shannonEntropy p = 0
    linarith
  have hprod := (mutual_information_eq_zero_iff_product p hp).mp hmi
  have hcond := (entropy_submodular_eq_iff_conditional_product p hp).mp he
  have hsum : ∑ a, marginal p a = 1 := by
    simpa only [marginal, ← Fintype.sum_prod_type] using hp.2
  obtain ⟨a, _, ha⟩ : ∃ a ∈ Finset.univ, 0 < marginal p a := by
    apply (Finset.sum_pos_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (fun bc _ => hp.1 (a, bc)))).mp
    change 0 < ∑ a, marginal p a
    rw [hsum]; norm_num
  have hslice : conditional p a = yz p := by
    funext bc
    simp only [conditional, congrFun hprod (a, bc)]
    change marginal p a * yz p bc / marginal p a = yz p bc
    exact mul_div_cancel_left₀ _ (ne_of_gt ha)
  have hyz := hcond a (ne_of_gt ha)
  rw [hslice] at hyz
  intro a' b c
  change p (a', (b, c)) = _
  rw [congrFun hprod (a', (b, c))]
  change marginal p a' * yz p (b, c) = _
  rw [congrFun hyz (b, c)]
  ring

noncomputable def totalCorrelation (p : A × B × C → ℝ) : ℝ :=
  D5.S3.Divergence.ClassicalDPI.klDivergence p (fun s =>
    marginal p s.1 * marginal (yz p) s.2.1 *
      marginal (fun q : C × B => yz p (q.2, q.1)) s.2.2)

private theorem totalCorrelation_entropy (p : A × B × C → ℝ)
    (hp : ∀ s, 0 ≤ p s) :
    totalCorrelation p = shannonEntropy (marginal p) + shannonEntropy (marginal (yz p)) +
      shannonEntropy (marginal (fun q : C × B => yz p (q.2, q.1))) - shannonEntropy p := by
  classical
  let m₁ := marginal p
  let m₂ := marginal (yz p)
  let m₃ := marginal (fun q : C × B => yz p (q.2, q.1))
  have hterm (a : A) (b : B) (c : C) :
      p (a, b, c) * Real.log (p (a, b, c) / (m₁ a * m₂ b * m₃ c)) =
        -Real.negMulLog (p (a, b, c)) - p (a, b, c) * Real.log (m₁ a) -
          p (a, b, c) * Real.log (m₂ b) - p (a, b, c) * Real.log (m₃ c) := by
    by_cases hz : p (a, b, c) = 0
    · simp [hz]
    have hpos : 0 < p (a, b, c) := lt_of_le_of_ne (hp _) (Ne.symm hz)
    have h₁ : 0 < m₁ a := lt_of_lt_of_le hpos
      (Finset.single_le_sum (fun bc _ => hp (a, bc)) (Finset.mem_univ (b, c)))
    have h₂ : 0 < m₂ b := by
      apply lt_of_lt_of_le hpos
      calc
        p (a, b, c) ≤ ∑ a', p (a', b, c) :=
          Finset.single_le_sum (fun a' _ => hp (a', b, c)) (Finset.mem_univ a)
        _ ≤ ∑ c', ∑ a', p (a', b, c') :=
          Finset.single_le_sum (fun c' _ => Finset.sum_nonneg fun a' _ => hp (a', b, c'))
            (Finset.mem_univ c)
    have h₃ : 0 < m₃ c := by
      apply lt_of_lt_of_le hpos
      calc
        p (a, b, c) ≤ ∑ a', p (a', b, c) :=
          Finset.single_le_sum (fun a' _ => hp (a', b, c)) (Finset.mem_univ a)
        _ ≤ ∑ b', ∑ a', p (a', b', c) :=
          Finset.single_le_sum (fun b' _ => Finset.sum_nonneg fun a' _ => hp (a', b', c))
            (Finset.mem_univ b)
    rw [Real.log_div hz (mul_ne_zero (mul_ne_zero (ne_of_gt h₁) (ne_of_gt h₂))
      (ne_of_gt h₃)), Real.log_mul (mul_ne_zero (ne_of_gt h₁) (ne_of_gt h₂))
      (ne_of_gt h₃), Real.log_mul (ne_of_gt h₁) (ne_of_gt h₂)]
    simp only [Real.negMulLog]
    ring
  have hs₁ : (∑ a, ∑ b, ∑ c, p (a, b, c) * Real.log (m₁ a)) =
      ∑ a, m₁ a * Real.log (m₁ a) := by
    simp only [m₁, marginal, Fintype.sum_prod_type, Finset.sum_mul]
  have hs₂ : (∑ a, ∑ b, ∑ c, p (a, b, c) * Real.log (m₂ b)) =
      ∑ b, m₂ b * Real.log (m₂ b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    simp only [m₂, marginal, yz, Finset.sum_mul]
  have hs₃ : (∑ a, ∑ b, ∑ c, p (a, b, c) * Real.log (m₃ c)) =
      ∑ c, m₃ c * Real.log (m₃ c) := by
    calc
      _ = ∑ b, ∑ a, ∑ c, p (a, b, c) * Real.log (m₃ c) := Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ a, p (a, b, c) * Real.log (m₃ c) := by
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ a, p (a, b, c) * Real.log (m₃ c) := Finset.sum_comm
      _ = ∑ c, m₃ c * Real.log (m₃ c) := by
        simp only [m₃, marginal, yz, Finset.sum_mul]
  unfold totalCorrelation D5.S3.Divergence.ClassicalDPI.klDivergence
  simp only [Fintype.sum_prod_type]
  change (∑ a, ∑ b, ∑ c, p (a, b, c) *
    Real.log (p (a, b, c) / (m₁ a * m₂ b * m₃ c))) = _
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hs₁, hs₂, hs₃]
  simp only [shannonEntropy, Real.negMulLog, Fintype.sum_prod_type,
    m₁, m₂, m₃]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem totalCorrelation_dual_balance (p : A × B × C → ℝ)
    (hp : ∀ s, 0 ≤ p s) :
    2 * totalCorrelation p = mutualInformation (xyProjection p) +
      mutualInformation (xzProjection p) + mutualInformation (yz p) + dual p := by
  classical
  have hm₁₂ : marginal (xyProjection p) = marginal p := by
    funext a
    simp only [marginal, xyProjection, Fintype.sum_prod_type]
  have hm₁₃ : marginal (xzProjection p) = marginal p := by
    funext a
    simp only [marginal, xzProjection, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hm₂ : marginal (fun z : B × A => xyProjection p (z.2, z.1)) =
      marginal (yz p) := by
    funext b
    simp only [marginal, xyProjection, yz]
    exact Finset.sum_comm
  have hm₃ : marginal (fun z : C × A => xzProjection p (z.2, z.1)) =
      marginal (fun z : C × B => yz p (z.2, z.1)) := by
    funext c
    simp only [marginal, xzProjection, yz]
    exact Finset.sum_comm
  have h₁₂ := mutual_information_eq_entropy_sub (xyProjection p)
    (fun z => Finset.sum_nonneg fun c _ => hp (z.1, z.2, c))
  have h₁₃ := mutual_information_eq_entropy_sub (xzProjection p)
    (fun z => Finset.sum_nonneg fun b _ => hp (z.1, b, z.2))
  have h₂₃ := mutual_information_eq_entropy_sub (yz p)
    (fun z => Finset.sum_nonneg fun a _ => hp (a, z))
  rw [hm₁₂, hm₂] at h₁₂
  rw [hm₁₃, hm₃] at h₁₃
  rw [totalCorrelation_entropy p hp, h₁₂, h₁₃, h₂₃, dual]
  ring

end FiniteEntropy

namespace CrossSupport

variable {X A B C : Type*} [Fintype X] [DecidableEq X]

private theorem no_common_coordinate (F : A → Finset X) (G : B → Finset X)
    (coverF : ∀ x, ∃ a, x ∈ F a) (coverG : ∀ x, ∃ b, x ∈ G b)
    (cross : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (hm : 2 ≤ Fintype.card X) (x : X) :
    ¬ ((∀ a, x ∈ F a) ∧ (∀ b, x ∈ G b)) := by
  rintro ⟨hxF, hxG⟩
  haveI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨y, hy⟩ := exists_ne x
  obtain ⟨a, ha⟩ := coverF y
  obtain ⟨b, hb⟩ := coverG y
  obtain ⟨z, hz, hu⟩ := cross a b
  exact hy ((hu y ⟨ha, hb⟩).trans (hu x ⟨hxF a, hxG b⟩).symm)

private theorem row_card_two (F : A → Finset X) (G : B → Finset X)
    (H : C → Finset X)
    (coverG : ∀ x, ∃ b, x ∈ G b) (coverH : ∀ x, ∃ c, x ∈ H c)
    (crossFG : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (crossFH : ∀ a c, ∃! x, x ∈ F a ∧ x ∈ H c)
    (crossGH : ∀ b c, ∃! x, x ∈ G b ∧ x ∈ H c)
    (hm : 2 ≤ Fintype.card X) (a : A) : 2 ≤ (F a).card := by
  by_contra hn
  have hsmall : (F a).card ≤ 1 := by omega
  haveI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b, _⟩ := coverG (Classical.choice inferInstance)
  obtain ⟨x, hx, _⟩ := crossFG a b
  apply no_common_coordinate G H coverG coverH crossGH hm x
  constructor
  · intro b'
    obtain ⟨y, hy, _⟩ := crossFG a b'
    have he := Finset.card_le_one.mp hsmall y hy.1 x hx.1
    exact he ▸ hy.2
  · intro c
    obtain ⟨y, hy, _⟩ := crossFH a c
    have he := Finset.card_le_one.mp hsmall y hy.1 x hx.1
    exact he ▸ hy.2

private theorem has_outside (u v : Finset X) (hv : 2 ≤ v.card)
    (cross : ∃! x, x ∈ u ∧ x ∈ v) : ∃ x, x ∈ v ∧ x ∉ u := by
  by_contra! hn
  obtain ⟨z, hz, hu⟩ := cross
  have hs : v.card ≤ 1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    exact (hu x ⟨hn x hx, hx⟩).trans (hu y ⟨hn y hy, hy⟩).symm)
  omega

private theorem row_complement_card_two (F : A → Finset X) (G : B → Finset X)
    (H : C → Finset X)
    (coverF : ∀ x, ∃ a, x ∈ F a)
    (coverG : ∀ x, ∃ b, x ∈ G b) (coverH : ∀ x, ∃ c, x ∈ H c)
    (crossFG : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (crossFH : ∀ a c, ∃! x, x ∈ F a ∧ x ∈ H c)
    (crossGH : ∀ b c, ∃! x, x ∈ G b ∧ x ∈ H c)
    (hm : 2 ≤ Fintype.card X) (a : A) :
    2 ≤ (Finset.univ \ F a).card := by
  classical
  have crossGF : ∀ b a, ∃! x, x ∈ G b ∧ x ∈ F a := by
    intro b a
    simpa only [and_comm] using crossFG a b
  have crossHF : ∀ c a, ∃! x, x ∈ H c ∧ x ∈ F a := by
    intro c a
    simpa only [and_comm] using crossFH a c
  have crossHG : ∀ c b, ∃! x, x ∈ H c ∧ x ∈ G b := by
    intro c b
    simpa only [and_comm] using crossGH b c
  have hG := row_card_two G F H coverF coverH crossGF crossGH crossFH hm
  have hH := row_card_two H F G coverF coverG crossHF crossHG crossFG hm
  by_contra hn
  have hsmall : (Finset.univ \ F a).card ≤ 1 := by omega
  haveI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b, _⟩ := coverG (Classical.choice inferInstance)
  obtain ⟨x, hx, hxu⟩ := has_outside (F a) (G b) (hG b) (crossFG a b)
  have hxc : x ∈ Finset.univ \ F a := by simp [hxu]
  apply no_common_coordinate G H coverG coverH crossGH hm x
  constructor
  · intro b'
    obtain ⟨y, hy, hyu⟩ := has_outside (F a) (G b') (hG b') (crossFG a b')
    have hyc : y ∈ Finset.univ \ F a := by simp [hyu]
    have he := Finset.card_le_one.mp hsmall y hyc x hxc
    exact he ▸ hy
  · intro c
    obtain ⟨y, hy, hyu⟩ := has_outside (F a) (H c) (hH c) (crossFH a c)
    have hyc : y ∈ Finset.univ \ F a := by simp [hyu]
    have he := Finset.card_le_one.mp hsmall y hyc x hxc
    exact he ▸ hy

theorem cardinal_lower_bound (F : A → Finset X) (G : B → Finset X)
    (H : C → Finset X)
    (coverF : ∀ x, ∃ a, x ∈ F a)
    (coverG : ∀ x, ∃ b, x ∈ G b) (coverH : ∀ x, ∃ c, x ∈ H c)
    (crossFG : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (crossFH : ∀ a c, ∃! x, x ∈ F a ∧ x ∈ H c)
    (crossGH : ∀ b c, ∃! x, x ∈ G b ∧ x ∈ H c)
    (hm : 2 ≤ Fintype.card X) : 4 ≤ Fintype.card X := by
  haveI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a, _⟩ := coverF (Classical.choice inferInstance)
  have h₁ := row_card_two F G H coverG coverH crossFG crossFH crossGH hm a
  have h₂ := row_complement_card_two F G H coverF coverG coverH
    crossFG crossFH crossGH hm a
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F a))
  rw [Finset.card_univ] at hsum
  omega

private theorem row_card_eq_two (F : A → Finset X) (G : B → Finset X)
    (H : C → Finset X)
    (coverF : ∀ x, ∃ a, x ∈ F a)
    (coverG : ∀ x, ∃ b, x ∈ G b) (coverH : ∀ x, ∃ c, x ∈ H c)
    (crossFG : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (crossFH : ∀ a c, ∃! x, x ∈ F a ∧ x ∈ H c)
    (crossGH : ∀ b c, ∃! x, x ∈ G b ∧ x ∈ H c)
    (hm : 2 ≤ Fintype.card X) (hmax : Fintype.card X ≤ 4) (a : A) :
    (F a).card = 2 := by
  have h₁ := row_card_two F G H coverG coverH crossFG crossFH crossGH hm a
  have h₂ := row_complement_card_two F G H coverF coverG coverH
    crossFG crossFH crossGH hm a
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F a))
  rw [Finset.card_univ] at hsum
  omega

private theorem equal_or_disjoint (F : A → Finset X) (G : B → Finset X)
    (H : C → Finset X)
    (coverG : ∀ x, ∃ b, x ∈ G b) (coverH : ∀ x, ∃ c, x ∈ H c)
    (crossFG : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (crossFH : ∀ a c, ∃! x, x ∈ F a ∧ x ∈ H c)
    (crossGH : ∀ b c, ∃! x, x ∈ G b ∧ x ∈ H c)
    (hF : ∀ a, (F a).card = 2) (hG : ∀ b, (G b).card = 2)
    (hH : ∀ c, (H c).card = 2) (hmax : Fintype.card X ≤ 4)
    (a a' : A) : F a = F a' ∨ Disjoint (F a) (F a') := by
  classical
  by_cases he : F a = F a'
  · exact Or.inl he
  right
  by_contra hn
  obtain ⟨x, hx, hx'⟩ := Finset.not_disjoint_iff.mp hn
  have hd₁ : ∃ y, y ∈ F a ∧ y ∉ F a' := by
    by_contra! hsub
    exact he (Finset.eq_of_subset_of_card_le hsub (by rw [hF, hF]))
  have hd₂ : ∃ z, z ∈ F a' ∧ z ∉ F a := by
    by_contra! hsub
    exact he (Finset.eq_of_subset_of_card_le hsub (by rw [hF, hF])).symm
  obtain ⟨y, hy, hy'⟩ := hd₁
  obtain ⟨z, hz', hz⟩ := hd₂
  have hxy : x ≠ y := by rintro rfl; exact hy' hx'
  have hxz : x ≠ z := by rintro rfl; exact hz hx
  have hyz : y ≠ z := by rintro rfl; exact hy' hz'
  have hthree : 3 ≤ (F a ∪ F a').card := by
    have hsub : ({x, y, z} : Finset X) ⊆ F a ∪ F a' := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_left _ hy
      · exact Finset.mem_union_right _ hz'
    have hc : ({x, y, z} : Finset X).card = 3 := by simp [hxy, hxz, hyz]
    simpa only [hc] using Finset.card_le_card hsub
  have hsmall : (Finset.univ \ (F a ∪ F a')).card ≤ 1 := by
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F a ∪ F a'))
    rw [Finset.card_univ] at hs
    omega
  obtain ⟨b, hb⟩ := coverG x
  obtain ⟨c, hc⟩ := coverH x
  obtain ⟨v, hv, hvx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({x} : Finset X).card < (G b).card by rw [Finset.card_singleton, hG]; omega)
  obtain ⟨w, hw, hwx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({x} : Finset X).card < (H c).card by rw [Finset.card_singleton, hH]; omega)
  have hvne : v ≠ x := by simpa only [Finset.mem_singleton] using hvx
  have hwne : w ≠ x := by simpa only [Finset.mem_singleton] using hwx
  have hvout : v ∈ Finset.univ \ (F a ∪ F a') := by
    have h₁ : v ∉ F a := by
      intro hv'
      obtain ⟨q, hq, hu⟩ := crossFG a b
      exact hvne ((hu v ⟨hv', hv⟩).trans (hu x ⟨hx, hb⟩).symm)
    have h₂ : v ∉ F a' := by
      intro hv'
      obtain ⟨q, hq, hu⟩ := crossFG a' b
      exact hvne ((hu v ⟨hv', hv⟩).trans (hu x ⟨hx', hb⟩).symm)
    simp [h₁, h₂]
  have hwout : w ∈ Finset.univ \ (F a ∪ F a') := by
    have h₁ : w ∉ F a := by
      intro hw'
      obtain ⟨q, hq, hu⟩ := crossFH a c
      exact hwne ((hu w ⟨hw', hw⟩).trans (hu x ⟨hx, hc⟩).symm)
    have h₂ : w ∉ F a' := by
      intro hw'
      obtain ⟨q, hq, hu⟩ := crossFH a' c
      exact hwne ((hu w ⟨hw', hw⟩).trans (hu x ⟨hx', hc⟩).symm)
    simp [h₁, h₂]
  have hvw := Finset.card_le_one.mp hsmall v hvout w hwout
  obtain ⟨q, hq, hu⟩ := crossGH b c
  exact hvne ((hu v ⟨hv, hvw ▸ hw⟩).trans (hu x ⟨hb, hc⟩).symm)

private theorem two_blocks (F : A → Finset X) (G : B → Finset X)
    (H : C → Finset X)
    (coverF : ∀ x, ∃ a, x ∈ F a)
    (coverG : ∀ x, ∃ b, x ∈ G b) (coverH : ∀ x, ∃ c, x ∈ H c)
    (crossFG : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (crossFH : ∀ a c, ∃! x, x ∈ F a ∧ x ∈ H c)
    (crossGH : ∀ b c, ∃! x, x ∈ G b ∧ x ∈ H c)
    (hm : 2 ≤ Fintype.card X) (hmax : Fintype.card X ≤ 4) :
    ∃ u : Finset X, u.card = 2 ∧ (Finset.univ \ u).card = 2 ∧
      (∀ a, F a = u ∨ F a = Finset.univ \ u) ∧
      (∃ a, F a = u) ∧ (∃ a, F a = Finset.univ \ u) := by
  classical
  have swapFG : ∀ b a, ∃! x, x ∈ G b ∧ x ∈ F a := by
    intro b a; simpa only [and_comm] using crossFG a b
  have swapFH : ∀ c a, ∃! x, x ∈ H c ∧ x ∈ F a := by
    intro c a; simpa only [and_comm] using crossFH a c
  have swapGH : ∀ c b, ∃! x, x ∈ H c ∧ x ∈ G b := by
    intro c b; simpa only [and_comm] using crossGH b c
  have hF := row_card_eq_two F G H coverF coverG coverH crossFG crossFH crossGH hm hmax
  have hG := row_card_eq_two G F H coverG coverF coverH swapFG crossGH crossFH hm hmax
  have hH := row_card_eq_two H F G coverH coverF coverG swapFH swapGH crossFG hm hmax
  haveI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a₀, _⟩ := coverF (Classical.choice inferInstance)
  have hcomp : (Finset.univ \ F a₀).card = 2 := by
    have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F a₀))
    rw [Finset.card_univ, hF] at hs
    have hl := row_complement_card_two F G H coverF coverG coverH
      crossFG crossFH crossGH hm a₀
    omega
  have hcases (a : A) : F a = F a₀ ∨ F a = Finset.univ \ F a₀ := by
    rcases equal_or_disjoint F G H coverG coverH crossFG crossFH crossGH
      hF hG hH hmax a a₀ with he | hd
    · exact Or.inl he
    · right
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hd hx⟩
      · rw [hcomp, hF]
  refine ⟨F a₀, hF a₀, hcomp, hcases, ⟨a₀, rfl⟩, ?_⟩
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (Finset.univ \ F a₀).card by omega)
  obtain ⟨a₁, ha₁⟩ := coverF x
  rcases hcases a₁ with he | he
  · exact False.elim ((Finset.mem_sdiff.mp hx).2 (he ▸ ha₁))
  · exact ⟨a₁, he⟩

private theorem binary_codes (F : A → Finset X)
    (hblocks : ∃ u : Finset X, u.card = 2 ∧ (Finset.univ \ u).card = 2 ∧
      (∀ a, F a = u ∨ F a = Finset.univ \ u) ∧
      (∃ a, F a = u) ∧ (∃ a, F a = Finset.univ \ u)) :
    ∃ b : A → Bool, ∃ d : X → Bool,
      Function.Surjective b ∧ (∀ a x, x ∈ F a ↔ d x = b a) := by
  classical
  obtain ⟨u, hu, huc, hcases, ⟨a₀, ha₀⟩, ⟨a₁, ha₁⟩⟩ := hblocks
  let b : A → Bool := fun a => if F a = u then false else true
  let d : X → Bool := fun x => if x ∈ u then false else true
  have hne : Finset.univ \ u ≠ u := by
    intro he
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < u.card by omega)
    have hx' : x ∈ Finset.univ \ u := he.symm ▸ hx
    exact (Finset.mem_sdiff.mp hx').2 hx
  refine ⟨b, d, ?_, ?_⟩
  · intro t
    cases t
    · exact ⟨a₀, by simp [b, ha₀]⟩
    · exact ⟨a₁, by simp [b, ha₁, hne]⟩
  · intro a x
    rcases hcases a with ha | ha
    · simp [d, b, ha]
    · simp [d, b, ha, hne]

private theorem pair_codes_bijective (F : A → Finset X) (G : B → Finset X)
    (cross : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (bF : A → Bool) (bG : B → Bool) (dF dG : X → Bool)
    (surjF : Function.Surjective bF) (surjG : Function.Surjective bG)
    (codeF : ∀ a x, x ∈ F a ↔ dF x = bF a)
    (codeG : ∀ b x, x ∈ G b ↔ dG x = bG b) :
    Function.Bijective (fun x => (dF x, dG x)) := by
  constructor
  · intro x y he
    obtain ⟨a, ha⟩ := surjF (dF x)
    obtain ⟨b, hb⟩ := surjG (dG x)
    obtain ⟨z, hz, hu⟩ := cross a b
    have hyF : dF y = bF a := (congrArg Prod.fst he).symm.trans ha.symm
    have hyG : dG y = bG b := (congrArg Prod.snd he).symm.trans hb.symm
    exact (hu x ⟨(codeF a x).mpr ha.symm, (codeG b x).mpr hb.symm⟩).trans
      (hu y ⟨(codeF a y).mpr hyF, (codeG b y).mpr hyG⟩).symm
  · rintro ⟨u, v⟩
    obtain ⟨a, ha⟩ := surjF u
    obtain ⟨b, hb⟩ := surjG v
    obtain ⟨x, hx, _⟩ := cross a b
    exact ⟨x, Prod.ext ((codeF a x).mp hx.1 |>.trans ha)
      ((codeG b x).mp hx.2 |>.trans hb)⟩

private theorem latin_bool_parity (g : Bool × Bool → Bool)
    (rows : ∀ u, g (u, false) ≠ g (u, true))
    (cols : ∀ v, g (false, v) ≠ g (true, v)) :
    ∀ u v, (g (u, v) ^^ g (false, false)) = (u ^^ v) := by
  have r₀ := rows false
  have r₁ := rows true
  have c₀ := cols false
  have c₁ := cols true
  intro u v
  cases u <;> cases v <;>
    cases h₀ : g (false, false) <;> cases h₁ : g (false, true) <;>
    cases h₂ : g (true, false) <;> cases h₃ : g (true, true) <;>
    simp_all

theorem three_codes (F : A → Finset X) (G : B → Finset X)
    (H : C → Finset X)
    (coverF : ∀ x, ∃ a, x ∈ F a)
    (coverG : ∀ x, ∃ b, x ∈ G b) (coverH : ∀ x, ∃ c, x ∈ H c)
    (crossFG : ∀ a b, ∃! x, x ∈ F a ∧ x ∈ G b)
    (crossFH : ∀ a c, ∃! x, x ∈ F a ∧ x ∈ H c)
    (crossGH : ∀ b c, ∃! x, x ∈ G b ∧ x ∈ H c)
    (hm : 2 ≤ Fintype.card X) (hmax : Fintype.card X ≤ 4) :
    ∃ bF : A → Bool, ∃ bG : B → Bool, ∃ bH : C → Bool,
    ∃ h : (Bool × Bool) ≃ X,
      Function.Surjective bF ∧ Function.Surjective bG ∧ Function.Surjective bH ∧
      (∀ a u v, h (u, v) ∈ F a ↔ u = bF a) ∧
      (∀ b u v, h (u, v) ∈ G b ↔ v = bG b) ∧
      (∀ c u v, h (u, v) ∈ H c ↔ (u ^^ v) = bH c) := by
  classical
  have swapFG : ∀ b a, ∃! x, x ∈ G b ∧ x ∈ F a := by
    intro b a; simpa only [and_comm] using crossFG a b
  have swapFH : ∀ c a, ∃! x, x ∈ H c ∧ x ∈ F a := by
    intro c a; simpa only [and_comm] using crossFH a c
  have swapGH : ∀ c b, ∃! x, x ∈ H c ∧ x ∈ G b := by
    intro c b; simpa only [and_comm] using crossGH b c
  obtain ⟨bF, dF, sF, cF⟩ := binary_codes F
    (two_blocks F G H coverF coverG coverH crossFG crossFH crossGH hm hmax)
  obtain ⟨bG, dG, sG, cG⟩ := binary_codes G
    (two_blocks G F H coverG coverF coverH swapFG crossGH crossFH hm hmax)
  obtain ⟨bH, dH, sH, cH⟩ := binary_codes H
    (two_blocks H F G coverH coverF coverG swapFH swapGH crossFG hm hmax)
  have bijFG := pair_codes_bijective F G crossFG bF bG dF dG sF sG cF cG
  have bijFH := pair_codes_bijective F H crossFH bF bH dF dH sF sH cF cH
  have bijGH := pair_codes_bijective G H crossGH bG bH dG dH sG sH cG cH
  let h : (Bool × Bool) ≃ X := (Equiv.ofBijective (fun x => (dF x, dG x)) bijFG).symm
  have hF (u v : Bool) : dF (h (u, v)) = u :=
    congrArg Prod.fst ((Equiv.ofBijective (fun x => (dF x, dG x)) bijFG).apply_symm_apply (u, v))
  have hG (u v : Bool) : dG (h (u, v)) = v :=
    congrArg Prod.snd ((Equiv.ofBijective (fun x => (dF x, dG x)) bijFG).apply_symm_apply (u, v))
  let g : Bool × Bool → Bool := fun z => dH (h z)
  have rows (u : Bool) : g (u, false) ≠ g (u, true) := by
    intro he
    have hh := bijFH.1 (show (dF (h (u, false)), dH (h (u, false))) =
        (dF (h (u, true)), dH (h (u, true))) from Prod.ext (by rw [hF, hF]) he)
    have hn : false = true := congrArg Prod.snd (h.injective hh)
    cases hn
  have cols (v : Bool) : g (false, v) ≠ g (true, v) := by
    intro he
    have hh := bijGH.1 (show (dG (h (false, v)), dH (h (false, v))) =
        (dG (h (true, v)), dH (h (true, v))) from Prod.ext (by rw [hG, hG]) he)
    have hn : false = true := congrArg Prod.fst (h.injective hh)
    cases hn
  let k := g (false, false)
  have parity := latin_bool_parity g rows cols
  refine ⟨bF, bG, (fun c => bH c ^^ k), h, sF, sG, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨c, hc⟩ := sH (t ^^ k)
    refine ⟨c, ?_⟩
    simp only [hc]
    cases t <;> cases k <;> rfl
  · intro a u v
    rw [cF, hF]
  · intro b u v
    rw [cG, hG]
  · intro c u v
    rw [cH]
    change g (u, v) = bH c ↔ _
    rw [← Bool.xor_left_inj (z := k), parity]

end CrossSupport

namespace BlockAlgebra

variable {A : Type*} [Fintype A]

noncomputable def extendLabel (mu : A → ℝ) (b : {a // 0 < mu a} → Bool) (a : A) : Bool :=
  if h : 0 < mu a then b ⟨a, h⟩ else false

noncomputable def mass (mu : A → ℝ) (b : A → Bool) (u : Bool) : ℝ :=
  ∑ a, if b a = u then mu a else 0

theorem mass_pos (mu : A → ℝ) (b : {a // 0 < mu a} → Bool)
    (hmu : ∀ a, 0 ≤ mu a) (hb : Function.Surjective b) (u : Bool) :
    0 < mass mu (extendLabel mu b) u := by
  classical
  obtain ⟨a, ha⟩ := hb u
  apply lt_of_lt_of_le a.property
  have hterm : (if extendLabel mu b a.val = u then mu a.val else 0) = mu a.val := by
    simp [extendLabel, a.property, ha]
  rw [← hterm]
  unfold mass
  exact Finset.single_le_sum
    (f := fun a => if extendLabel mu b a = u then mu a else 0)
    (fun a _ => by split_ifs <;> simp_all [hmu a]) (Finset.mem_univ a.val)

theorem mass_sum (mu : A → ℝ) (b : A → Bool) (hnorm : ∑ a, mu a = 1) :
    mass mu b false + mass mu b true = 1 := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ a, mu a := by
      apply Finset.sum_congr rfl
      intro a _
      cases b a <;> simp
    _ = 1 := hnorm

theorem cell_from_support (mu nu p r s t : ℝ) (u v a b : Bool)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hp : 0 < p) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : t = p * r * s) (hselector : t = 0 ∨ t = mu * nu)
    (activeR : 0 < r → 0 < mu) (activeS : 0 < s → 0 < nu)
    (codeR : 0 < mu → (0 < r ↔ u = a))
    (codeS : 0 < nu → (0 < s ↔ v = b)) :
    t = (if a = u then mu else 0) * (if b = v then nu else 0) := by
  classical
  by_cases hmass : mu * nu = 0
  · have htz : t = 0 := hselector.elim id (fun h => h.trans hmass)
    rw [htz]
    split_ifs <;> simp_all
  have hmupos : 0 < mu := lt_of_le_of_ne hmu
    (Ne.symm fun he => hmass (by rw [he, zero_mul]))
  have hnupos : 0 < nu := lt_of_le_of_ne hnu
    (Ne.symm fun he => hmass (by rw [he, mul_zero]))
  by_cases hcodes : a = u ∧ b = v
  · have hpos : 0 < t := by
      rw [ht]
      exact mul_pos (mul_pos hp ((codeR hmupos).mpr hcodes.1.symm))
        ((codeS hnupos).mpr hcodes.2.symm)
    have htv : t = mu * nu := hselector.resolve_left (ne_of_gt hpos)
    simp [hcodes.1, hcodes.2, htv]
  · have htz : t = 0 := by
      by_contra hn
      have htpos : 0 < t := lt_of_le_of_ne
        (by rw [ht]; positivity) (Ne.symm hn)
      have hrs : 0 < r ∧ 0 < s := by
        constructor
        · by_contra! hn; have hz : r = 0 := le_antisymm hn hr
          simp [ht, hz] at htpos
        · by_contra! hn; have hz : s = 0 := le_antisymm hn hs
          simp [ht, hz] at htpos
      exact hcodes ⟨((codeR (activeR hrs.1)).mp hrs.1).symm,
        ((codeS (activeS hrs.2)).mp hrs.2).symm⟩
    rw [htz]
    split_ifs <;> simp_all

theorem fair_weights (f g k : Bool → ℝ)
    (hf : ∀ u, 0 < f u) (hg : ∀ v, 0 < g v)
    (hnf : f false + f true = 1) (hng : g false + g true = 1)
    (hnk : k false + k true = 1)
    (hfgk : ∀ u v, f u * g v = f u * k (u ^^ v))
    (hgkf : ∀ u v, f u * g v = g v * k (u ^^ v)) :
    (∀ b, f b = 1 / 2) ∧ (∀ b, g b = 1 / 2) ∧ (∀ b, k b = 1 / 2) := by
  have h₀ : g false = k false := by
    simpa using (mul_left_cancel₀ (ne_of_gt (hf false)) (hfgk false false))
  have h₁ : g false = k true := by
    simpa using (mul_left_cancel₀ (ne_of_gt (hf true)) (hfgk true false))
  have hk₀ : k false = 1 / 2 := by linarith
  have hk₁ : k true = 1 / 2 := by linarith
  have hg₀ : g false = 1 / 2 := h₀.trans hk₀
  have hg₁ : g true = 1 / 2 := by linarith
  have hf₀ : f false = 1 / 2 := by
    have hh := hgkf false false
    simp only [Bool.false_xor, hg₀, hk₀] at hh
    linarith
  have hf₁ : f true = 1 / 2 := by linarith
  exact ⟨(fun b => by cases b <;> assumption),
    (fun b => by cases b <;> assumption), (fun b => by cases b <;> assumption)⟩

theorem posterior_from_pair {A B : Type*} [Fintype A] [Fintype B]
    (p : ℝ) (r : A → ℝ) (s : B → ℝ) (f : A → ℝ) (g : B → ℝ)
    (hp : p = 1 / 4) (hs : ∑ b, s b = 1) (hg : ∑ b, g b = 1 / 2)
    (htable : ∀ a b, p * r a * s b = f a * g b) : ∀ a, r a = 2 * f a := by
  classical
  intro a
  have hsum : (∑ b, p * r a * s b) = ∑ b, f a * g b :=
    Finset.sum_congr rfl (fun b _ => htable a b)
  simp only [← Finset.mul_sum, hs, mul_one] at hsum
  rw [hg, hp] at hsum
  linarith

end BlockAlgebra

namespace IncidentLaw

open Classical

/-- The six-variable law, with the original three source slots retained. -/
noncomputable def responseLaw (L : IncidentLaw S₁ S₂ S₃ O)
    (s : S₁ × S₂ × S₃) (a b c : O) : ℝ :=
  L.nu s * L.KA s.2.1 s.2.2 a * L.KB s.2.2 s.1 b * L.KC s.1 s.2.1 c

/-- Finite almost-sure agreement: every off-diagonal cell of the response law is zero. -/
def Agreement (L : IncidentLaw S₁ S₂ S₃ O) : Prop :=
  ∀ s a b c, (a ≠ b ∨ b ≠ c) → L.responseLaw s a b c = 0

/-- The actual joint law of the first output and all original sources. -/
noncomputable def recordLaw (L : IncidentLaw S₁ S₂ S₃ O)
    (x : O) (s : S₁ × S₂ × S₃) : ℝ :=
  L.nu s * L.KA s.2.1 s.2.2 x

noncomputable def outputLaw (L : IncidentLaw S₁ S₂ S₃ O) (x : O) : ℝ :=
  ∑ s, L.recordLaw x s

noncomputable def marginal₁ (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) : ℝ :=
  ∑ s₂, ∑ s₃, L.nu (s₁, s₂, s₃)
noncomputable def marginal₂ (L : IncidentLaw S₁ S₂ S₃ O) (s₂ : S₂) : ℝ :=
  ∑ s₁, ∑ s₃, L.nu (s₁, s₂, s₃)
noncomputable def marginal₃ (L : IncidentLaw S₁ S₂ S₃ O) (s₃ : S₃) : ℝ :=
  ∑ s₁, ∑ s₂, L.nu (s₁, s₂, s₃)
noncomputable def pair₁₂ (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) (s₂ : S₂) : ℝ :=
  ∑ s₃, L.nu (s₁, s₂, s₃)
noncomputable def pair₁₃ (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) (s₃ : S₃) : ℝ :=
  ∑ s₂, L.nu (s₁, s₂, s₃)
noncomputable def pair₂₃ (L : IncidentLaw S₁ S₂ S₃ O) (s₂ : S₂) (s₃ : S₃) : ℝ :=
  ∑ s₁, L.nu (s₁, s₂, s₃)

/-- The KL defect uses the product of the marginals of this very source law. -/
noncomputable def sourceCost (L : IncidentLaw S₁ S₂ S₃ O) : ℝ :=
  D5.S3.Divergence.ClassicalDPI.klDivergence L.nu
    (fun s => L.marginal₁ s.1 * L.marginal₂ s.2.1 * L.marginal₃ s.2.2)

/-- Positive output symbols; unused symbols of the original output type remain present in `L`. -/
abbrev PositiveOutput (L : IncidentLaw S₁ S₂ S₃ O) := {x : O // 0 < L.outputLaw x}

/-- A probability vector on an original source alphabet. -/
def IsProbability {S : Type*} [Fintype S] (q : S → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1

open Classical in
/-- The complete necessity conclusion, including exact active response rows.
Its existence is not assumed by `IncidentLaw`. -/
noncomputable def BinaryBlockConclusion (L : IncidentLaw S₁ S₂ S₃ O) : Prop :=
  Nonempty (L.PositiveOutput ≃ Bool × Bool) ∧
  ∃ h : (Bool × Bool) ≃ L.PositiveOutput,
    ∃ q₁ : Bool → S₁ → ℝ, ∃ q₂ : Bool → S₂ → ℝ, ∃ q₃ : Bool → S₃ → ℝ,
      (∀ b, IsProbability (q₁ b) ∧ IsProbability (q₂ b) ∧ IsProbability (q₃ b)) ∧
      (∀ s, q₁ false s * q₁ true s = 0) ∧
      (∀ s, q₂ false s * q₂ true s = 0) ∧
      (∀ s, q₃ false s * q₃ true s = 0) ∧
      (∀ u v s, L.recordLaw (h (u, v)).val s =
        (1 / 4 : ℝ) * q₁ u s.1 * q₂ v s.2.1 * q₃ (u ^^ v) s.2.2) ∧
      (∀ s₂ s₃, 0 < L.pair₂₃ s₂ s₃ →
        ∃ v w, 0 < q₂ v s₂ ∧ 0 < q₃ w s₃ ∧
          ∀ x, L.KA s₂ s₃ x = if x = (h (v ^^ w, v)).val then 1 else 0) ∧
      (∀ s₃ s₁, 0 < L.pair₁₃ s₁ s₃ →
        ∃ u w, 0 < q₁ u s₁ ∧ 0 < q₃ w s₃ ∧
          ∀ x, L.KB s₃ s₁ x = if x = (h (u, u ^^ w)).val then 1 else 0) ∧
      (∀ s₁ s₂, 0 < L.pair₁₂ s₁ s₂ →
        ∃ u v, 0 < q₁ u s₁ ∧ 0 < q₂ v s₂ ∧
          ∀ x, L.KC s₁ s₂ x = if x = (h (u, v)).val then 1 else 0)

theorem positive_entry {I : Type*} [Fintype I] (p : I → ℝ)
    (hsum : 0 < ∑ i, p i) : ∃ i, 0 < p i := by
  by_contra! h
  exact (not_lt_of_ge (Finset.sum_nonpos fun i _ => h i)) hsum

open Classical in
/-- A positive source cell admits one common output and forces every coordinate
of each of its three original stochastic rows. -/
private theorem rows_at_positive_source (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (s : S₁ × S₂ × S₃) (hs : 0 < L.nu s) :
    ∃ x : O,
      (∀ y, L.KA s.2.1 s.2.2 y = if y = x then 1 else 0) ∧
      (∀ y, L.KB s.2.2 s.1 y = if y = x then 1 else 0) ∧
      (∀ y, L.KC s.1 s.2.1 y = if y = x then 1 else 0) := by
  classical
  obtain ⟨a, ha⟩ := positive_entry (L.KA s.2.1 s.2.2) (by rw [L.KA_sum]; norm_num)
  obtain ⟨b, hb⟩ := positive_entry (L.KB s.2.2 s.1) (by rw [L.KB_sum]; norm_num)
  obtain ⟨c, hc⟩ := positive_entry (L.KC s.1 s.2.1) (by rw [L.KC_sum]; norm_num)
  have common {a' b' c' : O}
      (ha' : 0 < L.KA s.2.1 s.2.2 a')
      (hb' : 0 < L.KB s.2.2 s.1 b')
      (hc' : 0 < L.KC s.1 s.2.1 c') : a' = b' ∧ b' = c' := by
    by_contra hn
    have hoff : a' ≠ b' ∨ b' ≠ c' := by tauto
    have hz := hagree s a' b' c' hoff
    have hp : 0 < L.responseLaw s a' b' c' :=
      mul_pos (mul_pos (mul_pos hs ha') hb') hc'
    linarith
  obtain ⟨hab, hbc⟩ := common ha hb hc
  subst b; subst c
  have hAz (y : O) (hy : y ≠ a) : L.KA s.2.1 s.2.2 y = 0 := by
    apply le_antisymm _ (L.KA_nonneg _ _ _)
    by_contra! hp
    exact hy (common hp hb hc).1
  have hBz (y : O) (hy : y ≠ a) : L.KB s.2.2 s.1 y = 0 := by
    apply le_antisymm _ (L.KB_nonneg _ _ _)
    by_contra! hp
    exact hy (common ha hp hc).1.symm
  have hCz (y : O) (hy : y ≠ a) : L.KC s.1 s.2.1 y = 0 := by
    apply le_antisymm _ (L.KC_nonneg _ _ _)
    by_contra! hp
    exact hy (common ha hb hp).2.symm
  have hAa : L.KA s.2.1 s.2.2 a = 1 := by
    calc
      _ = ∑ y, L.KA s.2.1 s.2.2 y := (Finset.sum_eq_single a (fun y _ hy => hAz y hy) (by simp)).symm
      _ = 1 := L.KA_sum _ _
  have hBa : L.KB s.2.2 s.1 a = 1 := by
    calc
      _ = ∑ y, L.KB s.2.2 s.1 y := (Finset.sum_eq_single a (fun y _ hy => hBz y hy) (by simp)).symm
      _ = 1 := L.KB_sum _ _
  have hCa : L.KC s.1 s.2.1 a = 1 := by
    calc
      _ = ∑ y, L.KC s.1 s.2.1 y := (Finset.sum_eq_single a (fun y _ hy => hCz y hy) (by simp)).symm
      _ = 1 := L.KC_sum _ _
  refine ⟨a, ?_, ?_, ?_⟩
  · intro y; split_ifs with hy
    · subst y; exact hAa
    · exact hAz y hy
  · intro y; split_ifs with hy
    · subst y; exact hBa
    · exact hBz y hy
  · intro y; split_ifs with hy
    · subst y; exact hCa
    · exact hCz y hy

/-- Incident maps selected directly from normalized original kernel rows. -/
noncomputable def readoutA (L : IncidentLaw S₁ S₂ S₃ O) (s₂ : S₂) (s₃ : S₃) : O :=
  Classical.choose (positive_entry (L.KA s₂ s₃) (by rw [L.KA_sum]; norm_num))
noncomputable def readoutB (L : IncidentLaw S₁ S₂ S₃ O) (s₃ : S₃) (s₁ : S₁) : O :=
  Classical.choose (positive_entry (L.KB s₃ s₁) (by rw [L.KB_sum]; norm_num))
noncomputable def readoutC (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) (s₂ : S₂) : O :=
  Classical.choose (positive_entry (L.KC s₁ s₂) (by rw [L.KC_sum]; norm_num))

private theorem readoutA_pos (L : IncidentLaw S₁ S₂ S₃ O) (s₂ : S₂) (s₃ : S₃) :
    0 < L.KA s₂ s₃ (L.readoutA s₂ s₃) :=
  Classical.choose_spec (positive_entry (L.KA s₂ s₃) (by rw [L.KA_sum]; norm_num))
private theorem readoutB_pos (L : IncidentLaw S₁ S₂ S₃ O) (s₃ : S₃) (s₁ : S₁) :
    0 < L.KB s₃ s₁ (L.readoutB s₃ s₁) :=
  Classical.choose_spec (positive_entry (L.KB s₃ s₁) (by rw [L.KB_sum]; norm_num))
private theorem readoutC_pos (L : IncidentLaw S₁ S₂ S₃ O) (s₁ : S₁) (s₂ : S₂) :
    0 < L.KC s₁ s₂ (L.readoutC s₁ s₂) :=
  Classical.choose_spec (positive_entry (L.KC s₁ s₂) (by rw [L.KC_sum]; norm_num))

open Classical in
private theorem point_at_readout (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (s : S₁ × S₂ × S₃) (hs : 0 < L.nu s) :
    (∀ y, L.KA s.2.1 s.2.2 y = if y = L.readoutA s.2.1 s.2.2 then 1 else 0) ∧
    (∀ y, L.KB s.2.2 s.1 y = if y = L.readoutB s.2.2 s.1 then 1 else 0) ∧
    (∀ y, L.KC s.1 s.2.1 y = if y = L.readoutC s.1 s.2.1 then 1 else 0) ∧
    L.readoutA s.2.1 s.2.2 = L.readoutB s.2.2 s.1 ∧
    L.readoutB s.2.2 s.1 = L.readoutC s.1 s.2.1 := by
  obtain ⟨x, ha, hb, hc⟩ := L.rows_at_positive_source hagree s hs
  have ea : L.readoutA s.2.1 s.2.2 = x := by
    have hp := L.readoutA_pos s.2.1 s.2.2
    rw [ha] at hp
    split_ifs at hp with h
    · exact h
    · linarith
  have eb : L.readoutB s.2.2 s.1 = x := by
    have hp := L.readoutB_pos s.2.2 s.1
    rw [hb] at hp
    split_ifs at hp with h
    · exact h
    · linarith
  have ec : L.readoutC s.1 s.2.1 = x := by
    have hp := L.readoutC_pos s.1 s.2.1
    rw [hc] at hp
    split_ifs at hp with h
    · exact h
    · linarith
  exact ⟨by simpa only [ea] using ha, by simpa only [eb] using hb,
    by simpa only [ec] using hc, ea.trans eb.symm, eb.trans ec.symm⟩

open Classical in
/-- Agreement forces exactly the active incident rows and yields incident
readouts of the same record on every positive original source cell.
No conclusion about an inactive row is included. -/
theorem original_law_recoverability (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) :
    (∀ s₂ s₃, 0 < L.pair₂₃ s₂ s₃ →
      ∀ y, L.KA s₂ s₃ y = if y = L.readoutA s₂ s₃ then 1 else 0) ∧
    (∀ s₃ s₁, 0 < L.pair₁₃ s₁ s₃ →
      ∀ y, L.KB s₃ s₁ y = if y = L.readoutB s₃ s₁ then 1 else 0) ∧
    (∀ s₁ s₂, 0 < L.pair₁₂ s₁ s₂ →
      ∀ y, L.KC s₁ s₂ y = if y = L.readoutC s₁ s₂ then 1 else 0) ∧
    (∀ s, 0 < L.nu s →
      L.readoutA s.2.1 s.2.2 = L.readoutB s.2.2 s.1 ∧
      L.readoutB s.2.2 s.1 = L.readoutC s.1 s.2.1) ∧
    (∀ x s, L.recordLaw x s =
      if x = L.readoutA s.2.1 s.2.2 then L.nu s else 0) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s₂ s₃ hpair
    obtain ⟨s₁, hs⟩ := positive_entry (fun s₁ => L.nu (s₁, s₂, s₃)) hpair
    exact (L.point_at_readout hagree (s₁, s₂, s₃) hs).1
  · intro s₃ s₁ hpair
    obtain ⟨s₂, hs⟩ := positive_entry (fun s₂ => L.nu (s₁, s₂, s₃)) hpair
    exact (L.point_at_readout hagree (s₁, s₂, s₃) hs).2.1
  · intro s₁ s₂ hpair
    obtain ⟨s₃, hs⟩ := positive_entry (fun s₃ => L.nu (s₁, s₂, s₃)) hpair
    exact (L.point_at_readout hagree (s₁, s₂, s₃) hs).2.2.1
  · intro s hs
    exact (L.point_at_readout hagree s hs).2.2.2
  · intro x s
    by_cases hs : L.nu s = 0
    · simp [recordLaw, hs]
    · have hp := (L.point_at_readout hagree s (lt_of_le_of_ne (L.nu_nonneg s) (Ne.symm hs))).1 x
      simp only [recordLaw, hp, mul_ite, mul_one, mul_zero]

/-- Summing over the two unobserved outputs gives exactly `recordLaw`. -/
private theorem response_marginal_is_record (L : IncidentLaw S₁ S₂ S₃ O)
    (s : S₁ × S₂ × S₃) (x : O) :
    (∑ b, ∑ c, L.responseLaw s x b c) = L.recordLaw x s := by
  classical
  simp only [responseLaw, recordLaw, ← Finset.mul_sum, L.KC_sum, mul_one,
    L.KB_sum]

theorem record_nonneg (L : IncidentLaw S₁ S₂ S₃ O) (x : O)
    (s : S₁ × S₂ × S₃) : 0 ≤ L.recordLaw x s :=
  mul_nonneg (L.nu_nonneg s) (L.KA_nonneg _ _ _)

theorem output_is_probability (L : IncidentLaw S₁ S₂ S₃ O) :
    IsProbability L.outputLaw := by
  classical
  constructor
  · intro x
    exact Finset.sum_nonneg fun s _ => L.record_nonneg x s
  · simp only [outputLaw, recordLaw]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, L.KA_sum, mul_one, L.nu_sum]

theorem record_eq_other_responses (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (x : O) (s : S₁ × S₂ × S₃) :
    L.recordLaw x s = L.nu s * L.KB s.2.2 s.1 x ∧
      L.recordLaw x s = L.nu s * L.KC s.1 s.2.1 x := by
  classical
  by_cases hs : L.nu s = 0
  · simp [recordLaw, hs]
  · obtain ⟨ha, hb, hc, hab, hbc⟩ :=
      L.point_at_readout hagree s (lt_of_le_of_ne (L.nu_nonneg s) (Ne.symm hs))
    simp only [recordLaw, ha, hb, hc, hab, hbc, and_self]

open Classical in
/-- The same original law, including its six-variable response law and all
incident conditional rows, has deterministic common-record support. -/
theorem original_law_common_record (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) :
    IsProbability L.outputLaw ∧
    (∀ s x, (∑ b, ∑ c, L.responseLaw s x b c) = L.recordLaw x s) ∧
    (∀ x s, L.recordLaw x s = L.nu s * L.KB s.2.2 s.1 x ∧
      L.recordLaw x s = L.nu s * L.KC s.1 s.2.1 x) ∧
    (∀ x s, L.recordLaw x s =
      if x = L.readoutA s.2.1 s.2.2 then L.nu s else 0) ∧
    (∀ s, 0 < L.nu s →
      L.readoutA s.2.1 s.2.2 = L.readoutB s.2.2 s.1 ∧
      L.readoutB s.2.2 s.1 = L.readoutC s.1 s.2.1) := by
  refine ⟨L.output_is_probability, L.response_marginal_is_record,
    L.record_eq_other_responses hagree, ?_, ?_⟩
  · exact (L.original_law_recoverability hagree).2.2.2.2
  · exact (L.original_law_recoverability hagree).2.2.2.1

end IncidentLaw
end D5.S3.Entropy.TriangleFourSymbolNecessity
