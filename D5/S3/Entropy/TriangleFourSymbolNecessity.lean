/- GID: D5/S3/Entropy/TriangleFourSymbolNecessity
   generality: G
   mirror-B: D5/B/S3/Entropy/TriangleFourSymbolNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite incident stochastic laws and support-exact common-record recovery on the original sources. -/

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

private theorem dual_nonneg (p : A × B × C → ℝ)
    (hp : (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1) : 0 ≤ dual p := by
  have h1 := entropy_submodular p hp
  have h2 := entropy_subadditive p hp
  change 0 ≤ shannonEntropy (xyProjection p) + shannonEntropy (xzProjection p) +
    shannonEntropy (yz p) - 2 * shannonEntropy p
  change shannonEntropy p ≤ shannonEntropy (marginal p) + shannonEntropy (yz p) at h2
  linarith

private theorem dual_zero_product (p : A × B × C → ℝ)
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

private theorem totalCorrelation_dual_balance (p : A × B × C → ℝ)
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

private theorem cardinal_lower_bound (F : A → Finset X) (G : B → Finset X)
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

private theorem three_codes (F : A → Finset X) (G : B → Finset X)
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

private theorem mass_pos (mu : A → ℝ) (b : {a // 0 < mu a} → Bool)
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

private theorem mass_sum (mu : A → ℝ) (b : A → Bool) (hnorm : ∑ a, mu a = 1) :
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

private theorem cell_from_support (mu nu p r s t : ℝ) (u v a b : Bool)
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

private theorem fair_weights (f g k : Bool → ℝ)
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

private theorem posterior_from_pair {A B : Type*} [Fintype A] [Fintype B]
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

private theorem positive_entry {I : Type*} [Fintype I] (p : I → ℝ)
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

private theorem record_nonneg (L : IncidentLaw S₁ S₂ S₃ O) (x : O)
    (s : S₁ × S₂ × S₃) : 0 ≤ L.recordLaw x s :=
  mul_nonneg (L.nu_nonneg s) (L.KA_nonneg _ _ _)

private theorem output_is_probability (L : IncidentLaw S₁ S₂ S₃ O) :
    IsProbability L.outputLaw := by
  classical
  constructor
  · intro x
    exact Finset.sum_nonneg fun s _ => L.record_nonneg x s
  · simp only [outputLaw, recordLaw]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, L.KA_sum, mul_one, L.nu_sum]

private theorem record_eq_other_responses (L : IncidentLaw S₁ S₂ S₃ O)
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

/-- The record/source joint table in the repository's finite entropy carrier. -/
noncomputable def recordJoint (L : IncidentLaw S₁ S₂ S₃ O)
    (z : O × (S₁ × S₂ × S₃)) : ℝ := L.recordLaw z.1 z.2
noncomputable def recordPair₁₂ (L : IncidentLaw S₁ S₂ S₃ O)
    (z : O × (S₁ × S₂)) : ℝ := ∑ s₃, L.recordLaw z.1 (z.2.1, z.2.2, s₃)
noncomputable def recordPair₁₃ (L : IncidentLaw S₁ S₂ S₃ O)
    (z : O × (S₁ × S₃)) : ℝ := ∑ s₂, L.recordLaw z.1 (z.2.1, s₂, z.2.2)
noncomputable def recordPair₂₃ (L : IncidentLaw S₁ S₂ S₃ O)
    (z : O × (S₂ × S₃)) : ℝ := ∑ s₁, L.recordLaw z.1 (s₁, z.2.1, z.2.2)

private theorem entropy_deterministic_extension {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y → ℝ) (f : Y → X) :
    shannonEntropy (fun z : X × Y => if z.1 = f z.2 then p z.2 else 0) =
      shannonEntropy p := by
  classical
  let e : Y → X × Y := fun y => (f y, y)
  have he : Function.Injective e := fun a b h => congrArg Prod.snd h
  have htable : (fun z : X × Y => if z.1 = f z.2 then p z.2 else 0) =
      Function.extend e p (fun _ => 0) := by
    funext z
    by_cases hz : z.1 = f z.2
    · have ze : z = e z.2 := by ext <;> simp_all [e]
      rw [ze, he.extend_apply]
      simp [e]
    · have hn : ¬ ∃ y, e y = z := by
        rintro ⟨y, hy⟩
        have hy₂ := congrArg Prod.snd hy
        have hy₁ := congrArg Prod.fst hy
        exact hz (by simpa [e, ← hy₂] using hy₁.symm)
      rw [if_neg hz, Function.extend_apply' _ _ _ hn]
  rw [htable]
  exact shannonEntropy_extend_injective he p

private theorem record_pair_tables (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) :
    (∀ z, L.recordPair₁₂ z =
      if z.1 = L.readoutC z.2.1 z.2.2 then L.pair₁₂ z.2.1 z.2.2 else 0) ∧
    (∀ z, L.recordPair₁₃ z =
      if z.1 = L.readoutB z.2.2 z.2.1 then L.pair₁₃ z.2.1 z.2.2 else 0) ∧
    (∀ z, L.recordPair₂₃ z =
      if z.1 = L.readoutA z.2.1 z.2.2 then L.pair₂₃ z.2.1 z.2.2 else 0) := by
  classical
  have hr := L.original_law_recoverability hagree
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have he : L.recordPair₁₂ z = L.pair₁₂ z.2.1 z.2.2 * L.KC z.2.1 z.2.2 z.1 := by
      simp only [recordPair₁₂, pair₁₂, Finset.sum_mul,
        (L.record_eq_other_responses hagree _ _).2]
    rw [he]
    by_cases hz : L.pair₁₂ z.2.1 z.2.2 = 0
    · simp [hz]
    · have hp : 0 < L.pair₁₂ z.2.1 z.2.2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun s₃ _ => L.nu_nonneg _) (Ne.symm hz)
      rw [hr.2.2.1 _ _ hp z.1]
      split_ifs <;> simp
  · intro z
    have he : L.recordPair₁₃ z = L.pair₁₃ z.2.1 z.2.2 * L.KB z.2.2 z.2.1 z.1 := by
      simp only [recordPair₁₃, pair₁₃, Finset.sum_mul,
        (L.record_eq_other_responses hagree _ _).1]
    rw [he]
    by_cases hz : L.pair₁₃ z.2.1 z.2.2 = 0
    · simp [hz]
    · have hp : 0 < L.pair₁₃ z.2.1 z.2.2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun s₂ _ => L.nu_nonneg _) (Ne.symm hz)
      rw [hr.2.1 _ _ hp z.1]
      split_ifs <;> simp
  · intro z
    have he : L.recordPair₂₃ z = L.pair₂₃ z.2.1 z.2.2 * L.KA z.2.1 z.2.2 z.1 := by
      simp only [recordPair₂₃, pair₂₃, recordLaw, Finset.sum_mul]
    rw [he]
    by_cases hz : L.pair₂₃ z.2.1 z.2.2 = 0
    · simp [hz]
    · have hp : 0 < L.pair₂₃ z.2.1 z.2.2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun s₁ _ => L.nu_nonneg _) (Ne.symm hz)
      rw [hr.1 _ _ hp z.1]
      split_ifs <;> simp

private theorem record_joint_entropy (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) :
    shannonEntropy L.recordJoint = shannonEntropy L.nu := by
  have he := (L.original_law_common_record hagree).2.2.2.1
  have ht : L.recordJoint = fun z : O × (S₁ × S₂ × S₃) =>
      if z.1 = L.readoutA z.2.2.1 z.2.2.2 then L.nu z.2 else 0 := by
    funext z
    exact he _ _
  rw [ht]
  exact entropy_deterministic_extension L.nu (fun s => L.readoutA s.2.1 s.2.2)

private theorem record_pair_entropies (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) :
    shannonEntropy L.recordPair₁₂ = shannonEntropy (fun z : S₁ × S₂ => L.pair₁₂ z.1 z.2) ∧
    shannonEntropy L.recordPair₁₃ = shannonEntropy (fun z : S₁ × S₃ => L.pair₁₃ z.1 z.2) ∧
    shannonEntropy L.recordPair₂₃ = shannonEntropy (fun z : S₂ × S₃ => L.pair₂₃ z.1 z.2) := by
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := L.record_pair_tables hagree
  refine ⟨?_, ?_, ?_⟩
  · rw [show L.recordPair₁₂ = _ from funext h₁₂]
    exact entropy_deterministic_extension (fun z : S₁ × S₂ => L.pair₁₂ z.1 z.2)
      (fun z => L.readoutC z.1 z.2)
  · rw [show L.recordPair₁₃ = _ from funext h₁₃]
    exact entropy_deterministic_extension (fun z : S₁ × S₃ => L.pair₁₃ z.1 z.2)
      (fun z => L.readoutB z.2 z.1)
  · rw [show L.recordPair₂₃ = _ from funext h₂₃]
    exact entropy_deterministic_extension (fun z : S₂ × S₃ => L.pair₂₃ z.1 z.2)
      (fun z => L.readoutA z.1 z.2)

private theorem record_marginals (L : IncidentLaw S₁ S₂ S₃ O) :
    marginal L.recordJoint = L.outputLaw ∧
    marginal L.recordPair₁₂ = L.outputLaw ∧
    marginal L.recordPair₁₃ = L.outputLaw ∧
    marginal L.recordPair₂₃ = L.outputLaw := by
  classical
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext x
    simp only [marginal, recordPair₁₂, outputLaw, Fintype.sum_prod_type]
  · funext x
    simp only [marginal, recordPair₁₃, outputLaw, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s₁ _
    exact Finset.sum_comm
  · funext x
    change (∑ z : S₂ × S₃, ∑ s₁, L.recordLaw x (s₁, z)) =
      ∑ s, L.recordLaw x s
    rw [Finset.sum_comm]
    exact (Fintype.sum_prod_type _).symm

private theorem record_conditionals (L : IncidentLaw S₁ S₂ S₃ O) (x : O) :
    conditional L.recordPair₁₂ x = xyProjection (conditional L.recordJoint x) ∧
    conditional L.recordPair₁₃ x = xzProjection (conditional L.recordJoint x) ∧
    conditional L.recordPair₂₃ x = FiniteEntropy.yz (conditional L.recordJoint x) := by
  obtain ⟨h₀, h₁₂, h₁₃, h₂₃⟩ := L.record_marginals
  constructor
  · funext z
    simp only [conditional, h₁₂, h₀, recordPair₁₂, recordJoint, xyProjection,
      Finset.sum_div]
  constructor
  · funext z
    simp only [conditional, h₁₃, h₀, recordPair₁₃, recordJoint, xzProjection,
      Finset.sum_div]
  · funext z
    simp only [FiniteEntropy.yz, marginal]
    simp only [conditional, h₂₃, h₀]
    simp only [recordPair₂₃, recordJoint, Finset.sum_div]

private theorem record_dual_balance (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) :
    FiniteEntropy.dual L.nu - shannonEntropy L.outputLaw =
      ∑ x, L.outputLaw x * FiniteEntropy.dual (conditional L.recordJoint x) := by
  classical
  obtain ⟨hm₀, hm₁₂, hm₁₃, hm₂₃⟩ := L.record_marginals
  have hc₀ := entropy_chain_rule L.recordJoint (fun z => L.record_nonneg _ _)
  have hc₁₂ := entropy_chain_rule L.recordPair₁₂
    (fun z => Finset.sum_nonneg fun s₃ _ => L.record_nonneg _ _)
  have hc₁₃ := entropy_chain_rule L.recordPair₁₃
    (fun z => Finset.sum_nonneg fun s₂ _ => L.record_nonneg _ _)
  have hc₂₃ := entropy_chain_rule L.recordPair₂₃
    (fun z => Finset.sum_nonneg fun s₁ _ => L.record_nonneg _ _)
  obtain ⟨he₁₂, he₁₃, he₂₃⟩ := L.record_pair_entropies hagree
  rw [L.record_joint_entropy hagree, hm₀] at hc₀
  rw [he₁₂, hm₁₂] at hc₁₂
  rw [he₁₃, hm₁₃] at hc₁₃
  rw [he₂₃, hm₂₃] at hc₂₃
  simp only [conditionalEntropy, hm₀] at hc₀
  simp only [conditionalEntropy, hm₁₂] at hc₁₂
  simp only [conditionalEntropy, hm₁₃] at hc₁₃
  simp only [conditionalEntropy, hm₂₃] at hc₂₃
  simp_rw [(L.record_conditionals _).1] at hc₁₂
  simp_rw [(L.record_conditionals _).2.1] at hc₁₃
  simp_rw [(L.record_conditionals _).2.2] at hc₂₃
  change shannonEntropy (fun z : S₁ × S₂ => L.pair₁₂ z.1 z.2) +
    shannonEntropy (fun z : S₁ × S₃ => L.pair₁₃ z.1 z.2) +
    shannonEntropy (fun z : S₂ × S₃ => L.pair₂₃ z.1 z.2) -
      2 * shannonEntropy L.nu - shannonEntropy L.outputLaw = _
  simp only [FiniteEntropy.dual, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  simp_rw [← mul_assoc, mul_comm (L.outputLaw _) (2 : ℝ), mul_assoc]
  rw [← Finset.mul_sum]
  linarith

private theorem source_gap_balance (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) :
    2 * L.sourceCost - shannonEntropy L.outputLaw =
      mutualInformation (xyProjection L.nu) + mutualInformation (xzProjection L.nu) +
        mutualInformation (FiniteEntropy.yz L.nu) +
          ∑ x, L.outputLaw x * FiniteEntropy.dual (conditional L.recordJoint x) := by
  classical
  have hm₂ (s₂ : S₂) : marginal (FiniteEntropy.yz L.nu) s₂ = L.marginal₂ s₂ := by
    simp only [marginal, FiniteEntropy.yz, marginal₂]
    exact Finset.sum_comm
  have hm₃ (s₃ : S₃) :
      marginal (fun z : S₃ × S₂ => FiniteEntropy.yz L.nu (z.2, z.1)) s₃ =
        L.marginal₃ s₃ := by
    simp only [marginal, FiniteEntropy.yz, marginal₃]
    exact Finset.sum_comm
  have hcost : L.sourceCost = FiniteEntropy.totalCorrelation L.nu := by
    unfold sourceCost FiniteEntropy.totalCorrelation
    congr 1
    funext s
    rw [hm₂, hm₃]
    simp only [marginal₁, marginal, Fintype.sum_prod_type]
  calc
    _ = mutualInformation (xyProjection L.nu) + mutualInformation (xzProjection L.nu) +
        mutualInformation (FiniteEntropy.yz L.nu) +
          (FiniteEntropy.dual L.nu - shannonEntropy L.outputLaw) := by
      rw [hcost, FiniteEntropy.totalCorrelation_dual_balance L.nu L.nu_nonneg]
      ring
    _ = _ := by rw [L.record_dual_balance hagree]

/-- Equality of the original KL source cost forces unconditional source-pair
products and a threefold product on every positive original output fiber. -/
theorem original_equality_fibers (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement)
    (heq : L.sourceCost = shannonEntropy L.outputLaw / 2) :
    (∀ s₁ s₂, L.pair₁₂ s₁ s₂ = L.marginal₁ s₁ * L.marginal₂ s₂) ∧
    (∀ s₁ s₃, L.pair₁₃ s₁ s₃ = L.marginal₁ s₁ * L.marginal₃ s₃) ∧
    (∀ s₂ s₃, L.pair₂₃ s₂ s₃ = L.marginal₂ s₂ * L.marginal₃ s₃) ∧
    (∀ x, 0 < L.outputLaw x →
      ∀ s₁ s₂ s₃, conditional L.recordJoint x (s₁, s₂, s₃) =
        marginal (conditional L.recordJoint x) s₁ *
          marginal (FiniteEntropy.yz (conditional L.recordJoint x)) s₂ *
          marginal (fun z : S₃ × S₂ =>
            FiniteEntropy.yz (conditional L.recordJoint x) (z.2, z.1)) s₃) := by
  classical
  have hp₁₂ : (∀ z, 0 ≤ xyProjection L.nu z) ∧ ∑ z, xyProjection L.nu z = 1 := by
    refine ⟨fun z => Finset.sum_nonneg fun s₃ _ => L.nu_nonneg _, ?_⟩
    simpa only [xyProjection, Fintype.sum_prod_type] using L.nu_sum
  have hp₁₃ : (∀ z, 0 ≤ xzProjection L.nu z) ∧ ∑ z, xzProjection L.nu z = 1 := by
    refine ⟨fun z => Finset.sum_nonneg fun s₂ _ => L.nu_nonneg _, ?_⟩
    simp only [xzProjection, Fintype.sum_prod_type]
    have he : (∑ s₁, ∑ s₃, ∑ s₂, L.nu (s₁, s₂, s₃)) =
        ∑ s₁, ∑ s₂, ∑ s₃, L.nu (s₁, s₂, s₃) := by
      apply Finset.sum_congr rfl
      intro s₁ _
      exact Finset.sum_comm
    rw [he]
    simpa only [Fintype.sum_prod_type] using L.nu_sum
  have hp₂₃ : (∀ z, 0 ≤ FiniteEntropy.yz L.nu z) ∧
      ∑ z, FiniteEntropy.yz L.nu z = 1 := by
    refine ⟨fun z => Finset.sum_nonneg fun s₁ _ => L.nu_nonneg _, ?_⟩
    simp only [FiniteEntropy.yz, marginal]
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using L.nu_sum
  have hout := L.output_is_probability
  have hmarg := L.record_marginals
  have hfiber (x : O) (hx : L.outputLaw x ≠ 0) :
      (∀ s, 0 ≤ conditional L.recordJoint x s) ∧
        ∑ s, conditional L.recordJoint x s = 1 := by
    constructor
    · intro s
      exact div_nonneg (L.record_nonneg x s) (by simpa only [hmarg.1] using hout.1 x)
    · simp only [conditional, ← Finset.sum_div]
      change marginal L.recordJoint x / marginal L.recordJoint x = 1
      rw [hmarg.1]
      exact div_self hx
  have hweighted (x : O) :
      0 ≤ L.outputLaw x * FiniteEntropy.dual (conditional L.recordJoint x) := by
    by_cases hx : L.outputLaw x = 0
    · simp only [hx, zero_mul, le_refl]
    · exact mul_nonneg (hout.1 x) (FiniteEntropy.dual_nonneg _ (hfiber x hx))
  have h₁₂ := mutual_information_nonneg _ hp₁₂
  have h₁₃ := mutual_information_nonneg _ hp₁₃
  have h₂₃ := mutual_information_nonneg _ hp₂₃
  have hsum : 0 ≤ ∑ x, L.outputLaw x *
      FiniteEntropy.dual (conditional L.recordJoint x) :=
    Finset.sum_nonneg (fun x _ => hweighted x)
  have hz : mutualInformation (xyProjection L.nu) + mutualInformation (xzProjection L.nu) +
      mutualInformation (FiniteEntropy.yz L.nu) +
        ∑ x, L.outputLaw x * FiniteEntropy.dual (conditional L.recordJoint x) = 0 := by
    rw [← L.source_gap_balance hagree, heq]
    ring
  have hz₁₂ : mutualInformation (xyProjection L.nu) = 0 := by linarith
  have hz₁₃ : mutualInformation (xzProjection L.nu) = 0 := by linarith
  have hz₂₃ : mutualInformation (FiniteEntropy.yz L.nu) = 0 := by linarith
  have hzw : ∑ x, L.outputLaw x * FiniteEntropy.dual (conditional L.recordJoint x) = 0 := by
    linarith
  have prod₁₂ := (mutual_information_eq_zero_iff_product _ hp₁₂).mp hz₁₂
  have prod₁₃ := (mutual_information_eq_zero_iff_product _ hp₁₃).mp hz₁₃
  have prod₂₃ := (mutual_information_eq_zero_iff_product _ hp₂₃).mp hz₂₃
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s₁ s₂
    have hh := congrFun prod₁₂ (s₁, s₂)
    simpa only [xyProjection, marginal, Fintype.sum_prod_type, pair₁₂, marginal₁,
      marginal₂] using hh
  · intro s₁ s₃
    have hh := congrFun prod₁₃ (s₁, s₃)
    have hm : marginal (xzProjection L.nu) s₁ = L.marginal₁ s₁ := by
      simp only [marginal, xzProjection, marginal₁]
      exact Finset.sum_comm
    rw [hm] at hh
    exact hh
  · intro s₂ s₃
    have hh := congrFun prod₂₃ (s₂, s₃)
    have hm₂ : marginal (FiniteEntropy.yz L.nu) s₂ = L.marginal₂ s₂ := by
      simp only [marginal, FiniteEntropy.yz, marginal₂]
      exact Finset.sum_comm
    have hm₃ : marginal (fun z : S₃ × S₂ => FiniteEntropy.yz L.nu (z.2, z.1)) s₃ =
        L.marginal₃ s₃ := by
      simp only [marginal, FiniteEntropy.yz, marginal₃]
      exact Finset.sum_comm
    rw [hm₂, hm₃] at hh
    exact hh
  · intro x hx
    have hwzero := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hweighted x)).mp hzw
    have hd : FiniteEntropy.dual (conditional L.recordJoint x) = 0 :=
      (mul_eq_zero.mp (hwzero x (Finset.mem_univ x))).resolve_left (ne_of_gt hx)
    exact FiniteEntropy.dual_zero_product _ (hfiber x (ne_of_gt hx)) hd

/-- Conditional source laws on the original source alphabets. -/
noncomputable def posterior₁ (L : IncidentLaw S₁ S₂ S₃ O) (x : O) : S₁ → ℝ :=
  marginal (conditional L.recordJoint x)
noncomputable def posterior₂ (L : IncidentLaw S₁ S₂ S₃ O) (x : O) : S₂ → ℝ :=
  marginal (FiniteEntropy.yz (conditional L.recordJoint x))
noncomputable def posterior₃ (L : IncidentLaw S₁ S₂ S₃ O) (x : O) : S₃ → ℝ :=
  marginal (fun z : S₃ × S₂ => FiniteEntropy.yz (conditional L.recordJoint x) (z.2, z.1))

private theorem conditional_is_probability (L : IncidentLaw S₁ S₂ S₃ O)
    (x : O) (hx : 0 < L.outputLaw x) : IsProbability (conditional L.recordJoint x) := by
  classical
  have hm := L.record_marginals
  constructor
  · intro s
    exact div_nonneg (L.record_nonneg x s) (by simpa only [hm.1] using le_of_lt hx)
  · simp only [conditional, ← Finset.sum_div]
    change marginal L.recordJoint x / marginal L.recordJoint x = 1
    rw [hm.1]
    exact div_self (ne_of_gt hx)

private theorem posterior_probabilities (L : IncidentLaw S₁ S₂ S₃ O)
    (x : O) (hx : 0 < L.outputLaw x) :
    IsProbability (L.posterior₁ x) ∧ IsProbability (L.posterior₂ x) ∧
      IsProbability (L.posterior₃ x) := by
  classical
  have hp := L.conditional_is_probability x hx
  have hyz : IsProbability (FiniteEntropy.yz (conditional L.recordJoint x)) := by
    constructor
    · intro z
      exact Finset.sum_nonneg fun a _ => hp.1 (a, z)
    · simp only [FiniteEntropy.yz, marginal]
      rw [Finset.sum_comm]
      simpa only [Fintype.sum_prod_type] using hp.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro s₁
    exact Finset.sum_nonneg fun z _ => hp.1 (s₁, z)
  · simpa only [posterior₁, marginal, ← Fintype.sum_prod_type] using hp.2
  · intro s₂
    exact Finset.sum_nonneg fun s₃ _ => hyz.1 (s₂, s₃)
  · simpa only [posterior₂, marginal, ← Fintype.sum_prod_type] using hyz.2
  · intro s₃
    exact Finset.sum_nonneg fun s₂ _ => hyz.1 (s₂, s₃)
  · simp only [posterior₃, marginal]
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using hyz.2

private theorem original_product_cells (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (heq : L.sourceCost = shannonEntropy L.outputLaw / 2)
    (x : O) (hx : 0 < L.outputLaw x) (s : S₁ × S₂ × S₃) :
    L.recordLaw x s = L.outputLaw x * L.posterior₁ x s.1 *
      L.posterior₂ x s.2.1 * L.posterior₃ x s.2.2 := by
  have hh := (L.original_equality_fibers hagree heq).2.2.2 x hx s.1 s.2.1 s.2.2
  change conditional L.recordJoint x s =
    L.posterior₁ x s.1 * L.posterior₂ x s.2.1 * L.posterior₃ x s.2.2 at hh
  have hm := (L.record_marginals).1
  simp only [conditional, hm, recordJoint] at hh
  calc
    _ = L.outputLaw x * (L.recordLaw x s / L.outputLaw x) :=
      (mul_div_cancel₀ _ (ne_of_gt hx)).symm
    _ = _ := by rw [hh]; ring

private theorem original_product_pairs (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (heq : L.sourceCost = shannonEntropy L.outputLaw / 2)
    (x : O) (hx : 0 < L.outputLaw x) :
    (∀ a b, L.recordPair₁₂ (x, a, b) =
      L.outputLaw x * L.posterior₁ x a * L.posterior₂ x b) ∧
    (∀ a c, L.recordPair₁₃ (x, a, c) =
      L.outputLaw x * L.posterior₁ x a * L.posterior₃ x c) ∧
    (∀ b c, L.recordPair₂₃ (x, b, c) =
      L.outputLaw x * L.posterior₂ x b * L.posterior₃ x c) := by
  classical
  obtain ⟨hp₁, hp₂, hp₃⟩ := L.posterior_probabilities x hx
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    simp only [recordPair₁₂, L.original_product_cells hagree heq x hx,
      ← Finset.mul_sum, hp₃.2, mul_one]
  · intro a c
    simp only [recordPair₁₃, L.original_product_cells hagree heq x hx]
    calc
      _ = (L.outputLaw x * L.posterior₁ x a) * (∑ b, L.posterior₂ x b) *
          L.posterior₃ x c := by simp only [Finset.sum_mul, Finset.mul_sum]
      _ = _ := by rw [hp₂.2, mul_one]
  · intro b c
    simp only [recordPair₂₃, L.original_product_cells hagree heq x hx]
    calc
      _ = L.outputLaw x * (∑ a, L.posterior₁ x a) *
          L.posterior₂ x b * L.posterior₃ x c := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = _ := by rw [hp₁.2, mul_one]

private theorem positive_factors_of_cell {x : O} (L : IncidentLaw S₁ S₂ S₃ O)
    (hx : 0 < L.outputLaw x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : 0 < L.outputLaw x * a * b) : 0 < a ∧ 0 < b := by
  constructor
  · by_contra! hn
    have hz : a = 0 := le_antisymm hn ha
    simp [hz] at hpos
  · by_contra! hn
    have hz : b = 0 := le_antisymm hn hb
    simp [hz] at hpos

/-- Positive source symbols are retained as subtypes of the original alphabets. -/
abbrev Active₁ (L : IncidentLaw S₁ S₂ S₃ O) := {s : S₁ // 0 < L.marginal₁ s}
abbrev Active₂ (L : IncidentLaw S₁ S₂ S₃ O) := {s : S₂ // 0 < L.marginal₂ s}
abbrev Active₃ (L : IncidentLaw S₁ S₂ S₃ O) := {s : S₃ // 0 < L.marginal₃ s}

noncomputable def support₁ (L : IncidentLaw S₁ S₂ S₃ O) (s : L.Active₁) :
    Finset L.PositiveOutput := Finset.univ.filter (fun x => 0 < L.posterior₁ x.val s.val)
noncomputable def support₂ (L : IncidentLaw S₁ S₂ S₃ O) (s : L.Active₂) :
    Finset L.PositiveOutput := Finset.univ.filter (fun x => 0 < L.posterior₂ x.val s.val)
noncomputable def support₃ (L : IncidentLaw S₁ S₂ S₃ O) (s : L.Active₃) :
    Finset L.PositiveOutput := Finset.univ.filter (fun x => 0 < L.posterior₃ x.val s.val)

private theorem posterior_active₁ (L : IncidentLaw S₁ S₂ S₃ O) (x : O)
    (hx : 0 < L.outputLaw x) (s : S₁) (hs : 0 < L.posterior₁ x s) :
    0 < L.marginal₁ s := by
  classical
  have hm := (L.record_marginals).1
  change 0 < ∑ z, conditional L.recordJoint x (s, z) at hs
  obtain ⟨z, hz⟩ := positive_entry _ hs
  have hr : 0 < L.recordLaw x (s, z) := by
    simpa only [conditional, hm, recordJoint] using
      (div_pos_iff_of_pos_right hx).mp hz
  have hnu : 0 < L.nu (s, z) := by
    by_contra! hn
    have hnz : L.nu (s, z) = 0 := le_antisymm hn (L.nu_nonneg _)
    simp [recordLaw, hnz] at hr
  apply lt_of_lt_of_le hnu
  exact (Finset.single_le_sum
    (fun bc _ => L.nu_nonneg (s, bc)) (Finset.mem_univ z)).trans_eq
      (by simp only [marginal₁, Fintype.sum_prod_type])

private theorem posterior_active₂ (L : IncidentLaw S₁ S₂ S₃ O) (x : O)
    (hx : 0 < L.outputLaw x) (s : S₂) (hs : 0 < L.posterior₂ x s) :
    0 < L.marginal₂ s := by
  classical
  have hm := (L.record_marginals).1
  change 0 < ∑ c, ∑ a, conditional L.recordJoint x (a, s, c) at hs
  obtain ⟨c, hc⟩ := positive_entry _ hs
  obtain ⟨a, ha⟩ := positive_entry _ hc
  have hr : 0 < L.recordLaw x (a, s, c) := by
    simpa only [conditional, hm, recordJoint] using
      (div_pos_iff_of_pos_right hx).mp ha
  have hnu : 0 < L.nu (a, s, c) := by
    by_contra! hn
    have hnz : L.nu (a, s, c) = 0 := le_antisymm hn (L.nu_nonneg _)
    simp [recordLaw, hnz] at hr
  apply lt_of_lt_of_le hnu
  calc
    _ ≤ ∑ c', L.nu (a, s, c') :=
      Finset.single_le_sum (fun c' _ => L.nu_nonneg _) (Finset.mem_univ c)
    _ ≤ L.marginal₂ s :=
      Finset.single_le_sum (fun a' _ => Finset.sum_nonneg fun c' _ =>
        L.nu_nonneg (a', s, c')) (Finset.mem_univ a)

private theorem posterior_active₃ (L : IncidentLaw S₁ S₂ S₃ O) (x : O)
    (hx : 0 < L.outputLaw x) (s : S₃) (hs : 0 < L.posterior₃ x s) :
    0 < L.marginal₃ s := by
  classical
  have hm := (L.record_marginals).1
  change 0 < ∑ b, ∑ a, conditional L.recordJoint x (a, b, s) at hs
  obtain ⟨b, hb⟩ := positive_entry _ hs
  obtain ⟨a, ha⟩ := positive_entry _ hb
  have hr : 0 < L.recordLaw x (a, b, s) := by
    simpa only [conditional, hm, recordJoint] using
      (div_pos_iff_of_pos_right hx).mp ha
  have hnu : 0 < L.nu (a, b, s) := by
    by_contra! hn
    have hnz : L.nu (a, b, s) = 0 := le_antisymm hn (L.nu_nonneg _)
    simp [recordLaw, hnz] at hr
  apply lt_of_lt_of_le hnu
  calc
    _ ≤ ∑ b', L.nu (a, b', s) :=
      Finset.single_le_sum (fun b' _ => L.nu_nonneg _) (Finset.mem_univ b)
    _ ≤ L.marginal₃ s :=
      Finset.single_le_sum (fun a' _ => Finset.sum_nonneg fun b' _ =>
        L.nu_nonneg (a', b', s)) (Finset.mem_univ a)

private theorem support_cover (L : IncidentLaw S₁ S₂ S₃ O) :
    (∀ x, ∃ s, x ∈ L.support₁ s) ∧
    (∀ x, ∃ s, x ∈ L.support₂ s) ∧
    (∀ x, ∃ s, x ∈ L.support₃ s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hp := (L.posterior_probabilities x.val x.property).1
    obtain ⟨s, hs⟩ := positive_entry _ (show 0 < ∑ s, L.posterior₁ x.val s by
      rw [hp.2]; norm_num)
    exact ⟨⟨s, L.posterior_active₁ _ x.property s hs⟩, by simp [support₁, hs]⟩
  · intro x
    have hp := (L.posterior_probabilities x.val x.property).2.1
    obtain ⟨s, hs⟩ := positive_entry _ (show 0 < ∑ s, L.posterior₂ x.val s by
      rw [hp.2]; norm_num)
    exact ⟨⟨s, L.posterior_active₂ _ x.property s hs⟩, by simp [support₂, hs]⟩
  · intro x
    have hp := (L.posterior_probabilities x.val x.property).2.2
    obtain ⟨s, hs⟩ := positive_entry _ (show 0 < ∑ s, L.posterior₃ x.val s by
      rw [hp.2]; norm_num)
    exact ⟨⟨s, L.posterior_active₃ _ x.property s hs⟩, by simp [support₃, hs]⟩

private theorem unique_factor_support (L : IncidentLaw S₁ S₂ S₃ O)
    (f g : L.PositiveOutput → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (t : O → ℝ) (m : ℝ) (a : O) (hm : 0 < m)
    (ht : ∀ x, t x = if x = a then m else 0)
    (hle : ∀ x, t x ≤ L.outputLaw x)
    (hfactor : ∀ x : L.PositiveOutput, t x.val = L.outputLaw x.val * f x * g x) :
    ∃! x : L.PositiveOutput, 0 < f x ∧ 0 < g x := by
  classical
  have hta : t a = m := by simp [ht]
  have ha : 0 < L.outputLaw a := lt_of_lt_of_le (by rwa [hta]) (hle a)
  let x : L.PositiveOutput := ⟨a, ha⟩
  have hx : 0 < f x ∧ 0 < g x := by
    apply L.positive_factors_of_cell ha (hf x) (hg x)
    rw [← hfactor x]
    simpa only [x, hta] using hm
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hpos : 0 < t y.val := by
    rw [hfactor]
    exact mul_pos (mul_pos y.property hy.1) hy.2
  have he : y.val = a := by
    by_contra hn
    simp [ht, hn] at hpos
  exact Subtype.ext he

private theorem support_cross (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (heq : L.sourceCost = shannonEntropy L.outputLaw / 2) :
    (∀ a b, ∃! x, x ∈ L.support₁ a ∧ x ∈ L.support₂ b) ∧
    (∀ a c, ∃! x, x ∈ L.support₁ a ∧ x ∈ L.support₃ c) ∧
    (∀ b c, ∃! x, x ∈ L.support₂ b ∧ x ∈ L.support₃ c) := by
  classical
  obtain ⟨ind₁₂, ind₁₃, ind₂₃, _⟩ := L.original_equality_fibers hagree heq
  obtain ⟨tab₁₂, tab₁₃, tab₂₃⟩ := L.record_pair_tables hagree
  obtain ⟨m₀, m₁₂, m₁₃, m₂₃⟩ := L.record_marginals
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have hm : 0 < L.pair₁₂ a.val b.val := by
      rw [ind₁₂]; exact mul_pos a.property b.property
    have hh := L.unique_factor_support
      (fun x => L.posterior₁ x.val a.val) (fun x => L.posterior₂ x.val b.val)
      (fun x => (L.posterior_probabilities x.val x.property).1.1 a.val)
      (fun x => (L.posterior_probabilities x.val x.property).2.1.1 b.val)
      (fun x => L.recordPair₁₂ (x, a.val, b.val)) (L.pair₁₂ a.val b.val)
      (L.readoutC a.val b.val) hm (fun x => tab₁₂ (x, a.val, b.val))
      (fun x => (Finset.single_le_sum
        (fun z _ => Finset.sum_nonneg fun c _ => L.record_nonneg x (z.1, z.2, c))
        (Finset.mem_univ (a.val, b.val))).trans_eq (congrFun m₁₂ x))
      (fun x => (L.original_product_pairs hagree heq x.val x.property).1 a.val b.val)
    simpa only [support₁, support₂, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  · intro a c
    have hm : 0 < L.pair₁₃ a.val c.val := by
      rw [ind₁₃]; exact mul_pos a.property c.property
    have hh := L.unique_factor_support
      (fun x => L.posterior₁ x.val a.val) (fun x => L.posterior₃ x.val c.val)
      (fun x => (L.posterior_probabilities x.val x.property).1.1 a.val)
      (fun x => (L.posterior_probabilities x.val x.property).2.2.1 c.val)
      (fun x => L.recordPair₁₃ (x, a.val, c.val)) (L.pair₁₃ a.val c.val)
      (L.readoutB c.val a.val) hm (fun x => tab₁₃ (x, a.val, c.val))
      (fun x => (Finset.single_le_sum
        (fun z _ => Finset.sum_nonneg fun b _ => L.record_nonneg x (z.1, b, z.2))
        (Finset.mem_univ (a.val, c.val))).trans_eq (congrFun m₁₃ x))
      (fun x => (L.original_product_pairs hagree heq x.val x.property).2.1 a.val c.val)
    simpa only [support₁, support₃, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  · intro b c
    have hm : 0 < L.pair₂₃ b.val c.val := by
      rw [ind₂₃]; exact mul_pos b.property c.property
    have hh := L.unique_factor_support
      (fun x => L.posterior₂ x.val b.val) (fun x => L.posterior₃ x.val c.val)
      (fun x => (L.posterior_probabilities x.val x.property).2.1.1 b.val)
      (fun x => (L.posterior_probabilities x.val x.property).2.2.1 c.val)
      (fun x => L.recordPair₂₃ (x, b.val, c.val)) (L.pair₂₃ b.val c.val)
      (L.readoutA b.val c.val) hm (fun x => tab₂₃ (x, b.val, c.val))
      (fun x => (Finset.single_le_sum
        (fun z _ => Finset.sum_nonneg fun a _ => L.record_nonneg x (a, z))
        (Finset.mem_univ (b.val, c.val))).trans_eq (congrFun m₂₃ x))
      (fun x => (L.original_product_pairs hagree heq x.val x.property).2.2 b.val c.val)
    simpa only [support₂, support₃, Finset.mem_filter, Finset.mem_univ, true_and] using hh

/-- The original equality law has at least four positive outputs. -/
theorem original_output_cardinality (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (heq : L.sourceCost = shannonEntropy L.outputLaw / 2)
    (hmin : 2 ≤ Fintype.card L.PositiveOutput) : 4 ≤ Fintype.card L.PositiveOutput := by
  classical
  obtain ⟨cover₁, cover₂, cover₃⟩ := L.support_cover
  obtain ⟨cross₁₂, cross₁₃, cross₂₃⟩ := L.support_cross hagree heq
  exact CrossSupport.cardinal_lower_bound L.support₁ L.support₂ L.support₃
    cover₁ cover₂ cover₃ cross₁₂ cross₁₃ cross₂₃ hmin

/-- The binary source blocks and the parity-labelled output bijection are
constructed from the actual conditional supports, with no replacement law. -/
theorem original_binary_supports (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (heq : L.sourceCost = shannonEntropy L.outputLaw / 2)
    (hmin : 2 ≤ Fintype.card L.PositiveOutput)
    (hmax : Fintype.card L.PositiveOutput ≤ 4) :
    Fintype.card L.PositiveOutput = 4 ∧
    ∃ b₁ : L.Active₁ → Bool, ∃ b₂ : L.Active₂ → Bool, ∃ b₃ : L.Active₃ → Bool,
    ∃ h : (Bool × Bool) ≃ L.PositiveOutput,
      Function.Surjective b₁ ∧ Function.Surjective b₂ ∧ Function.Surjective b₃ ∧
      (∀ s u v, 0 < L.posterior₁ (h (u, v)).val s.val ↔ u = b₁ s) ∧
      (∀ s u v, 0 < L.posterior₂ (h (u, v)).val s.val ↔ v = b₂ s) ∧
      (∀ s u v, 0 < L.posterior₃ (h (u, v)).val s.val ↔ (u ^^ v) = b₃ s) := by
  classical
  have hcard : Fintype.card L.PositiveOutput = 4 :=
    le_antisymm hmax (L.original_output_cardinality hagree heq hmin)
  refine ⟨hcard, ?_⟩
  obtain ⟨cover₁, cover₂, cover₃⟩ := L.support_cover
  obtain ⟨cross₁₂, cross₁₃, cross₂₃⟩ := L.support_cross hagree heq
  have hh := CrossSupport.three_codes L.support₁ L.support₂ L.support₃
    cover₁ cover₂ cover₃ cross₁₂ cross₁₃ cross₂₃ hmin hmax
  simpa only [support₁, support₂, support₃, Finset.mem_filter,
    Finset.mem_univ, true_and] using hh

private theorem original_block_pair_tables (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (heq : L.sourceCost = shannonEntropy L.outputLaw / 2)
    (b₁ : L.Active₁ → Bool) (b₂ : L.Active₂ → Bool) (b₃ : L.Active₃ → Bool)
    (h : (Bool × Bool) ≃ L.PositiveOutput)
    (code₁ : ∀ s u v, 0 < L.posterior₁ (h (u, v)).val s.val ↔ u = b₁ s)
    (code₂ : ∀ s u v, 0 < L.posterior₂ (h (u, v)).val s.val ↔ v = b₂ s)
    (code₃ : ∀ s u v, 0 < L.posterior₃ (h (u, v)).val s.val ↔ (u ^^ v) = b₃ s) :
    let l₁ := BlockAlgebra.extendLabel L.marginal₁ b₁
    let l₂ := BlockAlgebra.extendLabel L.marginal₂ b₂
    let l₃ := BlockAlgebra.extendLabel L.marginal₃ b₃
    ∀ u v,
      (∀ a b, L.recordPair₁₂ ((h (u, v)).val, a, b) =
        (if l₁ a = u then L.marginal₁ a else 0) *
        (if l₂ b = v then L.marginal₂ b else 0)) ∧
      (∀ a c, L.recordPair₁₃ ((h (u, v)).val, a, c) =
        (if l₁ a = u then L.marginal₁ a else 0) *
        (if l₃ c = (u ^^ v) then L.marginal₃ c else 0)) ∧
      (∀ b c, L.recordPair₂₃ ((h (u, v)).val, b, c) =
        (if l₂ b = v then L.marginal₂ b else 0) *
        (if l₃ c = (u ^^ v) then L.marginal₃ c else 0)) := by
  classical
  intro l₁ l₂ l₃ u v
  obtain ⟨ind₁₂, ind₁₃, ind₂₃, _⟩ := L.original_equality_fibers hagree heq
  obtain ⟨tab₁₂, tab₁₃, tab₂₃⟩ := L.record_pair_tables hagree
  obtain ⟨prod₁₂, prod₁₃, prod₂₃⟩ :=
    L.original_product_pairs hagree heq (h (u, v)).val (h (u, v)).property
  obtain ⟨hp₁, hp₂, hp₃⟩ := L.posterior_probabilities (h (u, v)).val (h (u, v)).property
  have hc₁ (a : S₁) (ha : 0 < L.marginal₁ a) :
      0 < L.posterior₁ (h (u, v)).val a ↔ u = l₁ a := by
    simpa only [l₁, BlockAlgebra.extendLabel, dif_pos ha] using code₁ ⟨a, ha⟩ u v
  have hc₂ (b : S₂) (hb : 0 < L.marginal₂ b) :
      0 < L.posterior₂ (h (u, v)).val b ↔ v = l₂ b := by
    simpa only [l₂, BlockAlgebra.extendLabel, dif_pos hb] using code₂ ⟨b, hb⟩ u v
  have hc₃ (c : S₃) (hc : 0 < L.marginal₃ c) :
      0 < L.posterior₃ (h (u, v)).val c ↔ (u ^^ v) = l₃ c := by
    simpa only [l₃, BlockAlgebra.extendLabel, dif_pos hc] using code₃ ⟨c, hc⟩ u v
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    apply BlockAlgebra.cell_from_support (L.marginal₁ a) (L.marginal₂ b)
      (L.outputLaw (h (u, v)).val) (L.posterior₁ (h (u, v)).val a)
      (L.posterior₂ (h (u, v)).val b) _ u v (l₁ a) (l₂ b)
      (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => L.nu_nonneg (a, b, c))
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => L.nu_nonneg (a, b, c))
      (h (u, v)).property (hp₁.1 a) (hp₂.1 b) (prod₁₂ a b)
    · rw [tab₁₂]
      split_ifs
      · exact Or.inr (ind₁₂ a b)
      · exact Or.inl rfl
    · exact L.posterior_active₁ _ (h (u, v)).property a
    · exact L.posterior_active₂ _ (h (u, v)).property b
    · exact hc₁ a
    · exact hc₂ b
  · intro a c
    apply BlockAlgebra.cell_from_support (L.marginal₁ a) (L.marginal₃ c)
      (L.outputLaw (h (u, v)).val) (L.posterior₁ (h (u, v)).val a)
      (L.posterior₃ (h (u, v)).val c) _ u (u ^^ v) (l₁ a) (l₃ c)
      (Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => L.nu_nonneg (a, b, c))
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => L.nu_nonneg (a, b, c))
      (h (u, v)).property (hp₁.1 a) (hp₃.1 c) (prod₁₃ a c)
    · rw [tab₁₃]
      split_ifs
      · exact Or.inr (ind₁₃ a c)
      · exact Or.inl rfl
    · exact L.posterior_active₁ _ (h (u, v)).property a
    · exact L.posterior_active₃ _ (h (u, v)).property c
    · exact hc₁ a
    · exact hc₃ c
  · intro b c
    apply BlockAlgebra.cell_from_support (L.marginal₂ b) (L.marginal₃ c)
      (L.outputLaw (h (u, v)).val) (L.posterior₂ (h (u, v)).val b)
      (L.posterior₃ (h (u, v)).val c) _ v (u ^^ v) (l₂ b) (l₃ c)
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => L.nu_nonneg (a, b, c))
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => L.nu_nonneg (a, b, c))
      (h (u, v)).property (hp₂.1 b) (hp₃.1 c) (prod₂₃ b c)
    · rw [tab₂₃]
      split_ifs
      · exact Or.inr (ind₂₃ b c)
      · exact Or.inl rfl
    · exact L.posterior_active₂ _ (h (u, v)).property b
    · exact L.posterior_active₃ _ (h (u, v)).property c
    · exact hc₂ b
    · exact hc₃ c

/-- On arbitrary original finite alphabets, equality with two to four positive
outputs has the complete binary block form and exactly the forced active rows. -/
theorem original_law_necessity (L : IncidentLaw S₁ S₂ S₃ O)
    (hagree : L.Agreement) (heq : L.sourceCost = shannonEntropy L.outputLaw / 2)
    (hmin : 2 ≤ Fintype.card L.PositiveOutput)
    (hmax : Fintype.card L.PositiveOutput ≤ 4) :
    Fintype.card L.PositiveOutput = 4 ∧ L.BinaryBlockConclusion := by
  classical
  obtain ⟨hcard, b₁, b₂, b₃, h, surj₁, surj₂, surj₃, code₁, code₂, code₃⟩ :=
    L.original_binary_supports hagree heq hmin hmax
  let l₁ := BlockAlgebra.extendLabel L.marginal₁ b₁
  let l₂ := BlockAlgebra.extendLabel L.marginal₂ b₂
  let l₃ := BlockAlgebra.extendLabel L.marginal₃ b₃
  let M₁ (u : Bool) (a : S₁) := if l₁ a = u then L.marginal₁ a else 0
  let M₂ (v : Bool) (b : S₂) := if l₂ b = v then L.marginal₂ b else 0
  let M₃ (w : Bool) (c : S₃) := if l₃ c = w then L.marginal₃ c else 0
  let rho₁ := BlockAlgebra.mass L.marginal₁ l₁
  let rho₂ := BlockAlgebra.mass L.marginal₂ l₂
  let rho₃ := BlockAlgebra.mass L.marginal₃ l₃
  have mu₁ : IsProbability L.marginal₁ := by
    constructor
    · intro a
      exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => L.nu_nonneg (a, b, c)
    · simpa only [marginal₁, Fintype.sum_prod_type] using L.nu_sum
  have mu₂ : IsProbability L.marginal₂ := by
    constructor
    · intro b
      exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => L.nu_nonneg (a, b, c)
    · simp only [marginal₂]
      rw [Finset.sum_comm]
      simpa only [Fintype.sum_prod_type] using L.nu_sum
  have mu₃ : IsProbability L.marginal₃ := by
    constructor
    · intro c
      exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => L.nu_nonneg (a, b, c)
    · simp only [marginal₃]
      rw [Finset.sum_comm]
      calc
        _ = ∑ a, ∑ b, ∑ c, L.nu (a, b, c) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = 1 := by simpa only [Fintype.sum_prod_type] using L.nu_sum
  have table := L.original_block_pair_tables hagree heq b₁ b₂ b₃ h code₁ code₂ code₃
  change ∀ u v,
    (∀ a b, L.recordPair₁₂ ((h (u, v)).val, a, b) = M₁ u a * M₂ v b) ∧
    (∀ a c, L.recordPair₁₃ ((h (u, v)).val, a, c) = M₁ u a * M₃ (u ^^ v) c) ∧
    (∀ b c, L.recordPair₂₃ ((h (u, v)).val, b, c) = M₂ v b * M₃ (u ^^ v) c) at table
  have weights (u v : Bool) :
      L.outputLaw (h (u, v)).val = rho₁ u * rho₂ v ∧
      L.outputLaw (h (u, v)).val = rho₁ u * rho₃ (u ^^ v) ∧
      L.outputLaw (h (u, v)).val = rho₂ v * rho₃ (u ^^ v) := by
    obtain ⟨m₀, m₁₂, m₁₃, m₂₃⟩ := L.record_marginals
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ = ∑ a, ∑ b, L.recordPair₁₂ ((h (u, v)).val, a, b) := by
          simpa only [marginal, Fintype.sum_prod_type] using (congrFun m₁₂ (h (u, v)).val).symm
        _ = (∑ a, M₁ u a) * ∑ b, M₂ v b := by
          simp_rw [(table u v).1]
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_comm
        _ = _ := rfl
    · calc
        _ = ∑ a, ∑ c, L.recordPair₁₃ ((h (u, v)).val, a, c) := by
          simpa only [marginal, Fintype.sum_prod_type] using (congrFun m₁₃ (h (u, v)).val).symm
        _ = (∑ a, M₁ u a) * ∑ c, M₃ (u ^^ v) c := by
          simp_rw [(table u v).2.1]
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_comm
        _ = _ := rfl
    · calc
        _ = ∑ b, ∑ c, L.recordPair₂₃ ((h (u, v)).val, b, c) := by
          simpa only [marginal, Fintype.sum_prod_type] using (congrFun m₂₃ (h (u, v)).val).symm
        _ = (∑ b, M₂ v b) * ∑ c, M₃ (u ^^ v) c := by
          simp_rw [(table u v).2.2]
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_comm
        _ = _ := rfl
  have pos₁ : ∀ u, 0 < rho₁ u := BlockAlgebra.mass_pos _ _ mu₁.1 surj₁
  have pos₂ : ∀ v, 0 < rho₂ v := BlockAlgebra.mass_pos _ _ mu₂.1 surj₂
  have sum₁ : rho₁ false + rho₁ true = 1 := BlockAlgebra.mass_sum _ _ mu₁.2
  have sum₂ : rho₂ false + rho₂ true = 1 := BlockAlgebra.mass_sum _ _ mu₂.2
  have sum₃ : rho₃ false + rho₃ true = 1 := BlockAlgebra.mass_sum _ _ mu₃.2
  obtain ⟨fair₁, fair₂, fair₃⟩ := BlockAlgebra.fair_weights rho₁ rho₂ rho₃ pos₁ pos₂
    sum₁ sum₂ sum₃ (fun u v => (weights u v).1.symm.trans (weights u v).2.1)
    (fun u v => (weights u v).1.symm.trans (weights u v).2.2)
  have quarter (u v : Bool) : L.outputLaw (h (u, v)).val = 1 / 4 := by
    rw [(weights u v).1, fair₁, fair₂]; norm_num
  let q₁ (u : Bool) (a : S₁) := 2 * M₁ u a
  let q₂ (v : Bool) (b : S₂) := 2 * M₂ v b
  let q₃ (w : Bool) (c : S₃) := 2 * M₃ w c
  have posteriors (u v : Bool) :
      (∀ a, L.posterior₁ (h (u, v)).val a = q₁ u a) ∧
      (∀ b, L.posterior₂ (h (u, v)).val b = q₂ v b) ∧
      (∀ c, L.posterior₃ (h (u, v)).val c = q₃ (u ^^ v) c) := by
    obtain ⟨hp₁, hp₂, hp₃⟩ := L.posterior_probabilities (h (u, v)).val (h (u, v)).property
    obtain ⟨pr₁₂, pr₁₃, pr₂₃⟩ :=
      L.original_product_pairs hagree heq (h (u, v)).val (h (u, v)).property
    have tt₁₂ (a b) : L.outputLaw (h (u, v)).val *
        L.posterior₁ (h (u, v)).val a * L.posterior₂ (h (u, v)).val b =
        M₁ u a * M₂ v b := (pr₁₂ a b).symm.trans ((table u v).1 a b)
    have tt₁₃ (a c) : L.outputLaw (h (u, v)).val *
        L.posterior₁ (h (u, v)).val a * L.posterior₃ (h (u, v)).val c =
        M₁ u a * M₃ (u ^^ v) c := (pr₁₃ a c).symm.trans ((table u v).2.1 a c)
    refine ⟨?_, ?_, ?_⟩
    · exact BlockAlgebra.posterior_from_pair _ _ _ (M₁ u) (M₂ v)
        (quarter u v) hp₂.2 (fair₂ v) tt₁₂
    · apply BlockAlgebra.posterior_from_pair _ _ _ (M₂ v) (M₁ u)
        (quarter u v) hp₁.2 (fair₁ u)
      intro b a
      nlinarith only [tt₁₂ a b]
    · apply BlockAlgebra.posterior_from_pair _ _ _ (M₃ (u ^^ v)) (M₁ u)
        (quarter u v) hp₁.2 (fair₁ u)
      intro c a
      nlinarith only [tt₁₃ a c]
  have prob (b : Bool) : IsProbability (q₁ b) ∧ IsProbability (q₂ b) ∧ IsProbability (q₃ b) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro a
      apply mul_nonneg (by norm_num)
      dsimp [M₁]
      split_ifs
      · exact mu₁.1 a
      · norm_num
    · change ∑ a, 2 * M₁ b a = 1
      rw [← Finset.mul_sum]
      change 2 * rho₁ b = 1
      rw [fair₁]; norm_num
    · intro a
      apply mul_nonneg (by norm_num)
      dsimp [M₂]
      split_ifs
      · exact mu₂.1 a
      · norm_num
    · change ∑ a, 2 * M₂ b a = 1
      rw [← Finset.mul_sum]
      change 2 * rho₂ b = 1
      rw [fair₂]; norm_num
    · intro a
      apply mul_nonneg (by norm_num)
      dsimp [M₃]
      split_ifs
      · exact mu₃.1 a
      · norm_num
    · change ∑ a, 2 * M₃ b a = 1
      rw [← Finset.mul_sum]
      change 2 * rho₃ b = 1
      rw [fair₃]; norm_num
  have dis₁ (a : S₁) : q₁ false a * q₁ true a = 0 := by
    dsimp [q₁, M₁]; cases l₁ a <;> simp
  have dis₂ (a : S₂) : q₂ false a * q₂ true a = 0 := by
    dsimp [q₂, M₂]; cases l₂ a <;> simp
  have dis₃ (a : S₃) : q₃ false a * q₃ true a = 0 := by
    dsimp [q₃, M₃]; cases l₃ a <;> simp
  have cells (u v : Bool) (s : S₁ × S₂ × S₃) :
      L.recordLaw (h (u, v)).val s = (1 / 4 : ℝ) *
        q₁ u s.1 * q₂ v s.2.1 * q₃ (u ^^ v) s.2.2 := by
    rw [L.original_product_cells hagree heq _ (h (u, v)).property,
      (posteriors u v).1, (posteriors u v).2.1, (posteriors u v).2.2, quarter]
  obtain ⟨ind₁₂, ind₁₃, ind₂₃, _⟩ := L.original_equality_fibers hagree heq
  obtain ⟨tab₁₂, tab₁₃, tab₂₃⟩ := L.record_pair_tables hagree
  obtain ⟨rowA, rowB, rowC, _, _⟩ := L.original_law_recoverability hagree
  refine ⟨hcard, ⟨h.symm⟩, h, q₁, q₂, q₃, prob, dis₁, dis₂, dis₃, cells, ?_, ?_, ?_⟩
  · intro b c hp
    have hm : 0 < L.marginal₂ b * L.marginal₃ c := by rwa [← ind₂₃]
    have hb : 0 < L.marginal₂ b := by
      by_contra! hn
      have hz : L.marginal₂ b = 0 := le_antisymm hn (mu₂.1 b)
      simp [hz] at hm
    have hc : 0 < L.marginal₃ c := by
      by_contra! hn
      have hz : L.marginal₃ c = 0 := le_antisymm hn (mu₃.1 c)
      simp [hz] at hm
    let v := l₂ b
    let w := l₃ c
    have hx : ((v ^^ w) ^^ v) = w := by cases v <;> cases w <;> rfl
    have hpos : 0 < L.recordPair₂₃ ((h (v ^^ w, v)).val, b, c) := by
      rw [(table (v ^^ w) v).2.2]
      simpa only [M₂, M₃, v, w, hx, if_pos rfl] using hm
    have he : (h (v ^^ w, v)).val = L.readoutA b c := by
      rw [tab₂₃] at hpos
      split_ifs at hpos with he
      · exact he
      · linarith
    refine ⟨v, w, ?_, ?_, ?_⟩
    · simpa only [q₂, M₂, v, if_pos rfl, ite_true] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) hb
    · simpa only [q₃, M₃, w, if_pos rfl, ite_true] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) hc
    · intro x
      simpa only [he] using rowA b c hp x
  · intro c a hp
    have hm : 0 < L.marginal₁ a * L.marginal₃ c := by rwa [← ind₁₃]
    have ha : 0 < L.marginal₁ a := by
      by_contra! hn
      have hz : L.marginal₁ a = 0 := le_antisymm hn (mu₁.1 a)
      simp [hz] at hm
    have hc : 0 < L.marginal₃ c := by
      by_contra! hn
      have hz : L.marginal₃ c = 0 := le_antisymm hn (mu₃.1 c)
      simp [hz] at hm
    let u := l₁ a
    let w := l₃ c
    have hx : (u ^^ (u ^^ w)) = w := by cases u <;> cases w <;> rfl
    have hpos : 0 < L.recordPair₁₃ ((h (u, u ^^ w)).val, a, c) := by
      rw [(table u (u ^^ w)).2.1]
      simpa only [M₁, M₃, u, w, hx, if_pos rfl] using hm
    have he : (h (u, u ^^ w)).val = L.readoutB c a := by
      rw [tab₁₃] at hpos
      split_ifs at hpos with he
      · exact he
      · linarith
    refine ⟨u, w, ?_, ?_, ?_⟩
    · simpa only [q₁, M₁, u, if_pos rfl, ite_true] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) ha
    · simpa only [q₃, M₃, w, if_pos rfl, ite_true] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) hc
    · intro x
      simpa only [he] using rowB c a hp x
  · intro a b hp
    have hm : 0 < L.marginal₁ a * L.marginal₂ b := by rwa [← ind₁₂]
    have ha : 0 < L.marginal₁ a := by
      by_contra! hn
      have hz : L.marginal₁ a = 0 := le_antisymm hn (mu₁.1 a)
      simp [hz] at hm
    have hb : 0 < L.marginal₂ b := by
      by_contra! hn
      have hz : L.marginal₂ b = 0 := le_antisymm hn (mu₂.1 b)
      simp [hz] at hm
    let u := l₁ a
    let v := l₂ b
    have hpos : 0 < L.recordPair₁₂ ((h (u, v)).val, a, b) := by
      rw [(table u v).1]
      simpa only [M₁, M₂, u, v, if_pos rfl] using hm
    have he : (h (u, v)).val = L.readoutC a b := by
      rw [tab₁₂] at hpos
      split_ifs at hpos with he
      · exact he
      · linarith
    refine ⟨u, v, ?_, ?_, ?_⟩
    · simpa only [q₁, M₁, u, if_pos rfl, ite_true] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) ha
    · simpa only [q₂, M₂, v, if_pos rfl, ite_true] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) hb
    · intro x
      simpa only [he] using rowC a b hp x

end IncidentLaw
end D5.S3.Entropy.TriangleFourSymbolNecessity
