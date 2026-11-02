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
def PositiveOutput (L : IncidentLaw S₁ S₂ S₃ O) := {x : O // 0 < L.outputLaw x}

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
  have he := (L.original_law_recoverability hagree).2.2.2.2
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
  have hsum := Finset.sum_nonneg (fun x _ => hweighted x)
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
    simpa only [hm, xzProjection, marginal, pair₁₃, marginal₃] using hh
  · intro s₂ s₃
    have hh := congrFun prod₂₃ (s₂, s₃)
    have hm₂ : marginal (FiniteEntropy.yz L.nu) s₂ = L.marginal₂ s₂ := by
      simp only [marginal, FiniteEntropy.yz, marginal₂]
      exact Finset.sum_comm
    have hm₃ : marginal (fun z : S₃ × S₂ => FiniteEntropy.yz L.nu (z.2, z.1)) s₃ =
        L.marginal₃ s₃ := by
      simp only [marginal, FiniteEntropy.yz, marginal₃]
      exact Finset.sum_comm
    simpa only [hm₂, hm₃, FiniteEntropy.yz, marginal, pair₂₃] using hh
  · intro x hx
    have hwzero := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hweighted x)).mp hzw
    have hd : FiniteEntropy.dual (conditional L.recordJoint x) = 0 :=
      (mul_eq_zero.mp (hwzero x (Finset.mem_univ x))).resolve_left (ne_of_gt hx)
    exact FiniteEntropy.dual_zero_product _ (hfiber x (ne_of_gt hx)) hd

end IncidentLaw
end D5.S3.Entropy.TriangleFourSymbolNecessity
