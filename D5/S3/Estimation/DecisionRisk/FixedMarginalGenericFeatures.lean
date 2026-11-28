/- GID: D5/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/FixedMarginalGenericFeatures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-marginal signed decision quality is equivalent to randomized reconstruction with half the quality bound. -/

module

public import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
public import Mathlib.Data.Fintype.EquivFin

/-! Finite generic features and reconstruction. The real risk retains signed
losses. The reconstruction indicator is inequality; the factor two agrees with
full l1 distance. Source: van Rooyen and Williamson, Le Cam meets LeCun,
arXiv:1402.4884v2, Definition 3 and Theorem 3. -/

@[expose] public section

noncomputable section
open scoped BigOperators
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.DecisionRisk.BoundedRiskSimulatorTransport
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures

universe u v w t

/-- Finite Bayes cost expanded by observations and actions. -/
theorem finite_bayes_cost_expansion
    {State Observation Action : Type*}
    [Fintype State] [Fintype Observation] [Fintype Action]
    (p : State → ℝ) (l : State → Action → ℝ) (X : State → Observation → ℝ)
    (d : Observation → Action → ℝ) :
    finiteBayesCost p l X d = ∑ a, ∑ b, d a b * ∑ i, p i * X i a * l i b := by
  classical
  simp only [finiteBayesCost, channelOutput, Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i, ∑ b, ∑ a, p i * (X i a * d a b * l i b)) =
        ∑ i, ∑ a, ∑ b, p i * (X i a * d a b * l i b) := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ b, p i * (X i a * d a b * l i b) := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, p i * (X i a * d a b * l i b) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro i _; ring

/-- Finite real expected loss attains its minimum, including signed losses.
The decision is chosen separately at each observation by minimizing its finite
unnormalized posterior loss. No positive-mass assumption is needed. -/
theorem finite_bayes_cost_minimizer
    {State Observation Action : Type*}
    [Fintype State] [Fintype Observation] [Fintype Action] [Nonempty Action]
    (p : State → ℝ) (l : State → Action → ℝ) (X : State → Observation → ℝ) :
    ∃ d : FiniteMarkovKernel Observation Action,
      ∀ k : FiniteMarkovKernel Observation Action,
        finiteBayesCost p l X d.1 ≤ finiteBayesCost p l X k.1 := by
  classical
  have hm (a : Observation) := Finset.exists_min_image Finset.univ
    (fun b : Action => ∑ i, p i * X i a * l i b) Finset.univ_nonempty
  choose m hm using hm
  let d : FiniteMarkovKernel Observation Action :=
    ⟨fun a b => if m a = b then 1 else 0,
      ⟨by intro a b; dsimp only; split_ifs <;> norm_num,
        by intro a; simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]⟩⟩
  have hd : finiteBayesCost p l X d.1 = ∑ a, ∑ i, p i * X i a * l i (m a) := by
    rw [finite_bayes_cost_expansion]
    simp [d]
  refine ⟨d, fun k => ?_⟩
  rw [hd, finite_bayes_cost_expansion]
  apply Finset.sum_le_sum
  intro a _
  calc
    (∑ i, p i * X i a * l i (m a)) =
        (∑ b, k.1 a b) * ∑ i, p i * X i a * l i (m a) := by rw [k.2.2, one_mul]
    _ = ∑ b, k.1 a b * ∑ i, p i * X i a * l i (m a) := Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_left ((hm a).2 b (Finset.mem_univ b)) (k.2.1 a b)

/-- Infimum of real expected losses over every stochastic decision. -/
def realBayesRisk {Θ O A : Type*} [Fintype Θ] [Fintype O] [Fintype A]
    (π : Θ → ℝ) (L : Θ → A → ℝ) (T : Θ → O → ℝ) : ℝ :=
  sInf (Set.range fun D : FiniteMarkovKernel O A => finiteBayesCost π L T D.1)

/-- The maximum absolute loss on a genuine finite decision problem. -/
def lossNorm {Θ A : Type*} [Fintype Θ] [Fintype A] (L : Θ → A → ℝ) : ℝ :=
  sSup (Set.range fun p : Θ × A => |L p.1 p.2|)

/-- Fixed-marginal probability of a reconstruction mismatch. -/
def reconstructionError {X Z : Type*} [Fintype X] [Fintype Z]
    (q : X → ℝ) (φ : X → Z → ℝ) (d : Z → X → ℝ) : ℝ := by
  classical
  exact ∑ x, q x * ∑ z, φ x z * ∑ y, d z y * (if y ≠ x then 1 else 0)

/-- Universal quality at fixed data marginal; all losses are real and signed.
The hypothesis and action types range independently of the data and features. -/
def GenericQuality {X : Type u} {Z : Type v} [Fintype X] [Fintype Z]
    (q : X → ℝ) (φ : X → Z → ℝ) (ε : ℝ) : Prop :=
  ∀ (Θ : Type w) (A : Type t) [Fintype Θ] [Fintype A] [Nonempty A]
    (π : Θ → ℝ) (T : Θ → X → ℝ) (L : Θ → A → ℝ),
    (∀ θ, 0 ≤ π θ) → (∑ θ, π θ) = 1 → IsRowStochastic T →
    (∀ x, ∑ θ, π θ * T θ x = q x) →
    realBayesRisk π L (fun θ => channelOutput φ (T θ)) - realBayesRisk π L T ≤
      ε * lossNorm L

private theorem mass_nonempty {I : Type*} [Fintype I]
    (p : I → ℝ) (hp : (∑ i, p i) = 1) : Nonempty I := by
  by_contra h
  letI : IsEmpty I := not_nonempty_iff.mp h
  simpa using hp

private theorem risk_min {Θ O A : Type*}
    [Fintype Θ] [Fintype O] [Fintype A] [Nonempty A]
    (π : Θ → ℝ) (L : Θ → A → ℝ) (T : Θ → O → ℝ) :
    ∃ d : FiniteMarkovKernel O A,
      realBayesRisk π L T = finiteBayesCost π L T d.1 ∧
      ∀ k : FiniteMarkovKernel O A, realBayesRisk π L T ≤ finiteBayesCost π L T k.1 := by
  obtain ⟨d, hd⟩ := finite_bayes_cost_minimizer π L T
  have hb : BddBelow (Set.range fun k : FiniteMarkovKernel O A =>
      finiteBayesCost π L T k.1) := ⟨finiteBayesCost π L T d.1, by
        rintro _ ⟨k, rfl⟩; exact hd k⟩
  have he : realBayesRisk π L T = finiteBayesCost π L T d.1 := by
    apply le_antisymm
    · exact csInf_le hb ⟨d, rfl⟩
    · exact le_csInf ⟨_, ⟨d, rfl⟩⟩ (by rintro _ ⟨k, rfl⟩; exact hd k)
  exact ⟨d, he, fun k => he.trans_le (hd k)⟩

private theorem loss_bounds {Θ A : Type*} [Fintype Θ] [Fintype A]
    [Nonempty Θ] [Nonempty A] (L : Θ → A → ℝ) :
    0 ≤ lossNorm L ∧ ∀ θ a, |L θ a| ≤ lossNorm L := by
  have hb : BddAbove (Set.range fun p : Θ × A => |L p.1 p.2|) :=
    (Set.finite_range _).bddAbove
  have hh (θ : Θ) (a : A) : |L θ a| ≤ lossNorm L :=
    le_csSup hb ⟨(θ, a), rfl⟩
  exact ⟨(abs_nonneg _).trans (hh (Classical.choice inferInstance)
    (Classical.choice inferInstance)), hh⟩

private theorem expectation_bounds {A : Type*} [Fintype A]
    (p f : A → ℝ) (M : ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : (∑ a, p a) = 1) (hf : ∀ a, |f a| ≤ M) :
    -M ≤ ∑ a, p a * f a ∧ (∑ a, p a * f a) ≤ M := by
  constructor
  · calc
      -M = ∑ a, p a * (-M) := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (abs_le.mp (hf a)).1 (hp a)
  · calc
      (∑ a, p a * f a) ≤ ∑ a, p a * M := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (abs_le.mp (hf a)).2 (hp a)
      _ = M := by rw [← Finset.sum_mul, hs, one_mul]

private theorem cost_expectation {Θ O A : Type*}
    [Fintype Θ] [Fintype O] [Fintype A]
    (π : Θ → ℝ) (L : Θ → A → ℝ) (T : Θ → O → ℝ) (D : O → A → ℝ) :
    finiteBayesCost π L T D = ∑ θ, π θ * ∑ x, T θ x * ∑ a, D x a * L θ a := by
  rw [finite_bayes_cost_expansion]
  simp only [Finset.mul_sum]
  calc
    (∑ x, ∑ a, ∑ θ, D x a * (π θ * T θ x * L θ a)) =
        ∑ x, ∑ θ, ∑ a, D x a * (π θ * T θ x * L θ a) := by
      apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]
    _ = ∑ θ, ∑ x, ∑ a, D x a * (π θ * T θ x * L θ a) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro θ _
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro a _
      ring

private theorem transported_cost_bound
    {X Z Θ A : Type*} [Fintype X] [Fintype Z] [Fintype Θ] [Fintype A]
    [Nonempty Θ] [Nonempty A]
    (q : X → ℝ) (φ : X → Z → ℝ) (d : FiniteMarkovKernel Z X)
    (π : Θ → ℝ) (T : Θ → X → ℝ) (L : Θ → A → ℝ)
    (D : FiniteMarkovKernel X A)
    (hπ : ∀ θ, 0 ≤ π θ) (hT : IsRowStochastic T)
    (hφ : IsRowStochastic φ)
    (hq : ∀ x, ∑ θ, π θ * T θ x = q x) :
    finiteBayesCost π L (fun θ => channelOutput φ (T θ))
        (fun z => channelOutput D.1 (d.1 z)) ≤
      finiteBayesCost π L T D.1 + 2 * lossNorm L * reconstructionError q φ d.1 := by
  classical
  let R : X → X → ℝ := fun x => channelOutput d.1 (φ x)
  have hR : IsRowStochastic R := row_stochastic_channel_comp φ d.1 hφ d.2
  let g : Θ → X → ℝ := fun θ x => ∑ a, D.1 x a * L θ a
  have hg (θ : Θ) (x : X) : -lossNorm L ≤ g θ x ∧ g θ x ≤ lossNorm L :=
    expectation_bounds (D.1 x) (L θ) (lossNorm L) (D.2.1 x) (D.2.2 x)
      ((loss_bounds L).2 θ)
  have hdiff (θ : Θ) (x y : X) :
      g θ y - g θ x ≤ 2 * lossNorm L * (if y ≠ x then 1 else 0) := by
    by_cases h : y = x
    · simp [h]
    · simp only [Ne, h, not_false_eq_true, ite_true, mul_one]
      linarith [(hg θ y).2, (hg θ x).1]
  have expansion :
      finiteBayesCost π L (fun θ => channelOutput φ (T θ))
          (fun z => channelOutput D.1 (d.1 z)) - finiteBayesCost π L T D.1 =
        ∑ θ, π θ * ∑ x, T θ x * ∑ y, R x y * (g θ y - g θ x) := by
    have hc (θ : Θ) :
        channelOutput (fun z => channelOutput D.1 (d.1 z)) (channelOutput φ (T θ)) =
          channelOutput D.1 (channelOutput R (T θ)) := by
      calc
        _ = channelOutput D.1 (channelOutput d.1 (channelOutput φ (T θ))) :=
          channel_output_comp d.1 D.1 _
        _ = _ := congrArg (channelOutput D.1) (channel_output_comp φ d.1 (T θ)).symm
    have he : finiteBayesCost π L (fun θ => channelOutput φ (T θ))
        (fun z => channelOutput D.1 (d.1 z)) =
        finiteBayesCost π L (fun θ => channelOutput R (T θ)) D.1 := by
      unfold finiteBayesCost
      simp_rw [hc]
    rw [he, cost_expectation, cost_expectation]
    change (∑ θ, π θ * ∑ y, channelOutput R (T θ) y * g θ y) -
        (∑ θ, π θ * ∑ x, T θ x * g θ x) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro θ _
    rw [← mul_sub]
    congr 1
    have hfirst : (∑ y, channelOutput R (T θ) y * g θ y) =
        ∑ x, T θ x * ∑ y, R x y * g θ y := by
      simp only [channelOutput, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      ring
    rw [hfirst, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [show T θ x * (∑ y, R x y * g θ y) - T θ x * g θ x =
        T θ x * ((∑ y, R x y * g θ y) - g θ x) by ring]
    congr 1
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hR.2 x, one_mul]
  have weight :
      (∑ θ, π θ * ∑ x, T θ x * ∑ y, R x y * (if y ≠ x then 1 else 0)) =
        reconstructionError q φ d.1 := by
    have marginal (f : X → ℝ) :
        (∑ θ, π θ * ∑ x, T θ x * f x) = ∑ x, q x * f x := by
      simp only [Finset.mul_sum]
      simp_rw [← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hq]
    rw [marginal]
    unfold reconstructionError
    apply Finset.sum_congr rfl; intro x _
    congr 1
    simp only [R, channelOutput, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro z _
    apply Finset.sum_congr rfl; intro y _
    ring
  have bound :
      (∑ θ, π θ * ∑ x, T θ x * ∑ y, R x y * (g θ y - g θ x)) ≤
        2 * lossNorm L * reconstructionError q φ d.1 := by
    calc
      _ ≤ ∑ θ, π θ * ∑ x, T θ x *
          ∑ y, R x y * (2 * lossNorm L * (if y ≠ x then 1 else 0)) := by
        apply Finset.sum_le_sum; intro θ _
        apply mul_le_mul_of_nonneg_left _ (hπ θ)
        apply Finset.sum_le_sum; intro x _
        apply mul_le_mul_of_nonneg_left _ (hT.1 θ x)
        apply Finset.sum_le_sum; intro y _
        exact mul_le_mul_of_nonneg_left (hdiff θ x y) (hR.1 x y)
      _ = _ := by
        rw [← weight]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro θ _
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        ring
  linarith

private theorem reconstruction_implies_quality
    {X : Type u} {Z : Type v} [Fintype X] [Fintype Z]
    (q : X → ℝ) (φ : X → Z → ℝ) (ε : ℝ)
    (hφ : IsRowStochastic φ)
    (hd : ∃ d : FiniteMarkovKernel Z X, reconstructionError q φ d.1 ≤ ε / 2) :
    GenericQuality.{u,v,w,t} q φ ε := by
  classical
  obtain ⟨d, hd⟩ := hd
  intro Θ A _ _ _ π T L hπ hπsum hT hq
  letI : Nonempty Θ := mass_nonempty π hπsum
  obtain ⟨D, hD, _⟩ := risk_min π L T
  obtain ⟨_, _, hmin⟩ := risk_min π L (fun θ => channelOutput φ (T θ))
  let E : FiniteMarkovKernel Z A :=
    ⟨fun z => channelOutput D.1 (d.1 z),
      row_stochastic_channel_comp d.1 D.1 d.2 D.2⟩
  have ht := transported_cost_bound q φ d π T L D hπ hT hφ hq
  have hn := (loss_bounds L).1
  have he : 2 * lossNorm L * reconstructionError q φ d.1 ≤ ε * lossNorm L := by
    nlinarith [mul_le_mul_of_nonneg_left hd hn]
  have hm := hmin E
  change realBayesRisk π L (fun θ => channelOutput φ (T θ)) ≤
    finiteBayesCost π L (fun θ => channelOutput φ (T θ)) E.1 at hm
  change finiteBayesCost π L (fun θ => channelOutput φ (T θ)) E.1 ≤ _ at ht
  linarith

private theorem cost_lower_bound {Θ O A : Type*}
    [Fintype Θ] [Fintype O] [Fintype A]
    (π : Θ → ℝ) (L : Θ → A → ℝ) (T : Θ → O → ℝ)
    (D : FiniteMarkovKernel O A)
    (hπ : ∀ θ, 0 ≤ π θ) (hπsum : (∑ θ, π θ) = 1)
    (hT : IsRowStochastic T) (hL : ∀ θ a, -1 ≤ L θ a) :
    -1 ≤ finiteBayesCost π L T D.1 := by
  have hs := row_stochastic_channel_comp T D.1 hT D.2
  calc
    -1 = ∑ θ, π θ * (-1) := by rw [← Finset.sum_mul, hπsum, one_mul]
    _ ≤ _ := by
      unfold finiteBayesCost
      apply Finset.sum_le_sum; intro θ _
      apply mul_le_mul_of_nonneg_left _ (hπ θ)
      calc
        -1 = ∑ a, channelOutput D.1 (T θ) a * (-1) := by
          rw [← Finset.sum_mul, hs.2 θ, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hL θ a) (hs.1 θ a)

/-- For a fixed normalized finite data marginal and a stochastic encoder,
universal real signed-loss quality is equivalent to one stochastic decoder
whose marginal-weighted mismatch probability is at most half the quality.
The four type universes are independent; zero weights are permitted. -/
theorem generic_quality_iff_reconstruction
    {X : Type u} {Z : Type v} [Fintype X] [Fintype Z]
    (q : X → ℝ) (φ : X → Z → ℝ) (ε : ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : (∑ x, q x) = 1)
    (hφ : IsRowStochastic φ) (hε : 0 < ε) :
    GenericQuality.{u,v,w,t} q φ ε ↔
      ∃ d : FiniteMarkovKernel Z X, reconstructionError q φ d.1 ≤ ε / 2 := by
  classical
  constructor
  · intro h
    letI : Nonempty X := mass_nonempty q hqsum
    let H := ULift.{w} (Fin (Fintype.card X))
    let A := ULift.{t} (Fin (Fintype.card X))
    let eH : H ≃ X := Equiv.ulift.trans (Fintype.equivFin X).symm
    let eA : A ≃ X := Equiv.ulift.trans (Fintype.equivFin X).symm
    letI : Nonempty H := eH.nonempty
    letI : Nonempty A := eA.nonempty
    let p : H → ℝ := fun θ => q (eH θ)
    let T : H → X → ℝ := fun θ x => if eH θ = x then 1 else 0
    let L : H → A → ℝ := fun θ a => if eA a = eH θ then -1 else 1
    have hp : ∀ θ, 0 ≤ p θ := fun θ => hq (eH θ)
    have hpsum : (∑ θ, p θ) = 1 := (eH.sum_comp q).trans hqsum
    have hT : IsRowStochastic T := by
      constructor
      · intro θ x; dsimp [T]; split_ifs <;> norm_num
      · intro θ; simp [T]
    have hmarg (x : X) : (∑ θ, p θ * T θ x) = q x := by
      change (∑ θ, q (eH θ) * (if eH θ = x then 1 else 0)) = q x
      rw [eH.sum_comp (fun y => q y * (if y = x then 1 else 0))]
      simp
    have hc (θ : H) : channelOutput φ (T θ) = φ (eH θ) := by
      funext z
      simp [channelOutput, T]
    let I : FiniteMarkovKernel X A :=
      ⟨fun x a => if eA.symm x = a then 1 else 0,
        ⟨by intro x a; dsimp only; split_ifs <;> norm_num,
          by
            intro x
            exact Finset.sum_ite_eq_of_mem Finset.univ (eA.symm x)
              (fun _ : A => (1 : ℝ)) (Finset.mem_univ _)⟩⟩
    have hI : finiteBayesCost p L T I.1 = -1 := by
      rw [cost_expectation]
      have hi (θ : H) : (∑ x, T θ x * ∑ a, I.1 x a * L θ a) = -1 := by
        simp only [T, I, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq_of_mem Finset.univ (eH θ) _ (Finset.mem_univ _)]
        rw [Finset.sum_ite_eq_of_mem Finset.univ (eA.symm (eH θ)) _ (Finset.mem_univ _)]
        simp [L]
      simp_rw [hi]
      rw [← Finset.sum_mul, hpsum, one_mul]
    have hbase : realBayesRisk p L T = -1 := by
      obtain ⟨k, hk, hkle⟩ := risk_min p L T
      apply le_antisymm
      · exact (hkle I).trans_eq hI
      · rw [hk]
        exact cost_lower_bound p L T k hp hpsum hT (by
          intro θ a; dsimp [L]; split_ifs <;> norm_num)
    obtain ⟨k, hk, _⟩ := risk_min p L (fun θ => channelOutput φ (T θ))
    let d : FiniteMarkovKernel Z X :=
      ⟨fun z x => k.1 z (eA.symm x),
        ⟨fun z x => k.2.1 z (eA.symm x), fun z =>
          (eA.symm.sum_comp (k.1 z)).trans (k.2.2 z)⟩⟩
    have herr : finiteBayesCost p L (fun θ => channelOutput φ (T θ)) k.1 =
        2 * reconstructionError q φ d.1 - 1 := by
      rw [cost_expectation]
      simp_rw [hc]
      rw [← eH.symm.sum_comp (fun θ => p θ * ∑ z, φ (eH θ) z * ∑ a, k.1 z a * L θ a)]
      simp only [p, eH.apply_symm_apply]
      have inner (x : X) (z : Z) :
          (∑ a, k.1 z a * L (eH.symm x) a) =
            2 * (∑ y, d.1 z y * (if y ≠ x then 1 else 0)) - 1 := by
        rw [← eA.symm.sum_comp (fun a => k.1 z a * L (eH.symm x) a)]
        simp only [L, eA.apply_symm_apply, eH.apply_symm_apply]
        have signed (y : X) : (if y = x then (-1 : ℝ) else 1) =
            2 * (if y ≠ x then 1 else 0) - 1 := by
          by_cases hy : y = x <;> norm_num [hy]
        simp_rw [signed]
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
        rw [show (∑ y, k.1 z (eA.symm y)) = 1 from d.2.2 z]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _
        change k.1 z (eA.symm y) * (2 * _) = 2 * (k.1 z (eA.symm y) * _)
        ring
      have scale (x : X) :
          (∑ z, φ x z * (2 * (∑ y, d.1 z y * (if y ≠ x then 1 else 0)) - 1)) =
            2 * (∑ z, φ x z * ∑ y, d.1 z y * (if y ≠ x then 1 else 0)) - 1 := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hφ.2 x]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z _
        ring
      simp_rw [inner, scale]
      unfold reconstructionError
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hqsum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      ring
    have hnorm : lossNorm L ≤ 1 := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨⟨θ, a⟩, rfl⟩
      dsimp [L]
      split_ifs <;> norm_num
    have hquality := h H A p T L hp hpsum hT hmarg
    rw [hbase, hk, herr] at hquality
    refine ⟨d, ?_⟩
    have hn := mul_le_mul_of_nonneg_left hnorm (le_of_lt hε)
    nlinarith
  · exact reconstruction_implies_quality q φ ε hφ

end D5.S3.Estimation.DecisionRisk.FixedMarginalGenericFeatures
