/- GID: D5/S3/Entropy/TriangleFourSymbolNecessity
   generality: G
   mirror-B: D5/B/S3/Entropy/TriangleFourSymbolNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite incident stochastic laws and support-exact common-record recovery on the original sources. -/

import D5.S3.Entropy.TriangleFourSymbolFoundation

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

variable {S₁ S₂ S₃ O : Type*}
  [Fintype S₁] [Fintype S₂] [Fintype S₃] [Fintype O]

namespace IncidentLaw

open Classical

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
