/- GID: D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The compensated pair and path laws yield positive ordered posteriors and exact uniform-cutoff Bayes rules. -/

import Mathlib
import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

open scoped BigOperators
open Finset
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
noncomputable section

inductive Experiment where | pair | path
abbrev Vertex (M : ℕ) := Fin M ⊕ Fin M
abbrev Support (M q : ℕ) := {S : Finset (Fin M) // S.card = q}
def Obs (M s : ℕ) : Experiment → Type
  | .pair => Fin s → Vertex M × Vertex M
  | .path => Fin (s+1) → Vertex M
instance (M s : ℕ) (e : Experiment) : Fintype (Obs M s e) := by
  cases e <;> dsimp [Obs] <;> infer_instance
instance (M s : ℕ) (e : Experiment) : MeasurableSpace (Obs M s e) := ⊤
def edges {M s : ℕ} (e : Experiment) (o : Obs M s e) : Fin s → Vertex M × Vertex M :=
  match e with
  | .pair => o
  | .path => fun k => (o k.castSucc, o k.succ)
def chi {M : ℕ} : Vertex M → ℝ | .inl _ => 1 | .inr _ => -1
def compensation (M q : ℕ) (r : ℝ) : ℝ := r * q / (M-q : ℕ)
def b {M q : ℕ} (r : ℝ) (S : Support M q) : Vertex M → ℝ
  | .inl i => if i ∈ S.val then r else -compensation M q r
  | .inr _ => 0
def transition {M q : ℕ} (r : ℝ) (S : Support M q) (x y : Vertex M) : ℝ :=
  (1 + b r S x * chi y) / (2 * M)
def probability {M q s : ℕ} (r : ℝ) (e : Experiment)
    (S : Support M q) (o : Obs M s e) : ℝ :=
  match e with
  | .pair => ∏ k : Fin s, (2 * (M : ℝ))⁻¹ * transition r S (o k).1 (o k).2
  | .path => (2 * (M : ℝ))⁻¹ * ∏ k : Fin s, transition r S (o k.castSucc) (o k.succ)
def uniformMass (M s : ℕ) (e : Experiment) : ℝ :=
  (2 * (M : ℝ))⁻¹ ^ (match e with | .pair => 2*s | .path => s+1)
def count {M s : ℕ} (e : Experiment) (o : Obs M s e) (i : Fin M) (z : ℝ) : ℕ :=
  (Finset.univ.filter fun k => (edges e o k).1 = Sum.inl i ∧ chi (edges e o k).2 = z).card
def score {M s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment) (o : Obs M s e) (i : Fin M) : ℝ :=
  count e o i 1 * Real.log ((1+r)/(1-compensation M q r)) +
  count e o i (-1) * Real.log ((1-r)/(1+compensation M q r))
def weight {M s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment) (o : Obs M s e) (i : Fin M) : ℝ :=
  ((1+r)/(1-compensation M q r)) ^ count e o i 1 *
  ((1-r)/(1+compensation M q r)) ^ count e o i (-1)
def background {M s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment) (o : Obs M s e) : ℝ :=
  ∏ k : Fin s, match (edges e o k).1 with
    | .inl _ => 1 - compensation M q r * chi (edges e o k).2
    | .inr _ => 1
def partition {M q s : ℕ} (r : ℝ) (e : Experiment) (o : Obs M s e) : ℝ :=
  ∑ S : Support M q, ∏ i ∈ S.val, weight q r e o i
def posterior {M q s : ℕ} (r : ℝ) (e : Experiment) (o : Obs M s e) (S : Support M q) : ℝ :=
  probability r e S o / ∑ T : Support M q, probability r e T o
def inclusion {M s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment) (o : Obs M s e) (i : Fin M) : ℝ :=
  ∑ S : Support M q, if i ∈ S.val then posterior r e o S else 0
def topFamily {M s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment) (o : Obs M s e) : Finset (Support M q) :=
  Finset.univ.filter fun T => ∀ i ∈ T.val, ∀ j ∉ T.val, weight q r e o j ≤ weight q r e o i
def decision {M s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment) (o : Obs M s e) (T : Support M q) : ℝ :=
  if T ∈ topFamily q r e o then ((topFamily q r e o).card : ℝ)⁻¹ else 0
def allDecision {M s : ℕ} (q : ℕ) (r : ℝ) (e : Experiment) (o : Obs M s e) (T : Finset (Fin M)) : ℝ :=
  if h : T.card = q then decision q r e o ⟨T,h⟩ else 0
def exactLoss {M q : ℕ} (S : Support M q) (T : Finset (Fin M)) : ℝ :=
  if T = S.val then 0 else 1
def hammingLoss {M q : ℕ} (S T : Support M q) : ℝ :=
  ((symmDiff T.val S.val).card : ℝ) / (2*q)
def risk {M q s : ℕ} {A : Type*} [Fintype A] (r : ℝ) (e : Experiment)
    (loss : Support M q → A → ℝ) (D : Obs M s e → A → ℝ) (S : Support M q) : ℝ :=
  ∑ o, probability r e S o * ∑ T, D o T * loss S T
def prior (M q : ℕ) (_ : Support M q) : ℝ := (Fintype.card (Support M q) : ℝ)⁻¹
def Optimal {M q s : ℕ} {A : Type*} [Fintype A] (r : ℝ) (e : Experiment)
    (loss : Support M q → A → ℝ) (D : FiniteMarkovKernel (Obs M s e) A) : Prop :=
  (∀ D' : FiniteMarkovKernel (Obs M s e) A,
    finiteBayesCost (prior M q) loss (probability r e) D.val ≤
      finiteBayesCost (prior M q) loss (probability r e) D'.val) ∧
  (∀ S T : Support M q, risk r e loss D.val S = risk r e loss D.val T) ∧
  (∀ D' : FiniteMarkovKernel (Obs M s e) A, ∀ S : Support M q,
    risk r e loss D.val S ≤ sSup (Set.range (risk r e loss D'.val))) ∧
  sSup (Set.range (risk r e loss D.val)) =
    sInf (Set.range fun D' : FiniteMarkovKernel (Obs M s e) A =>
      sSup (Set.range (risk r e loss D'.val)))
def permVertex {M : ℕ} (σ : Equiv.Perm (Fin M)) : Vertex M ≃ Vertex M :=
  Equiv.sumCongr σ (Equiv.refl (Fin M))
def permSupport {M q : ℕ} (σ : Equiv.Perm (Fin M)) (S : Support M q) : Support M q :=
  ⟨S.val.map σ.toEmbedding, by simpa using S.property⟩
def permObs {M s : ℕ} (σ : Equiv.Perm (Fin M)) (e : Experiment) (o : Obs M s e) : Obs M s e :=
  match e with
  | .pair => fun k => (permVertex σ (o k).1, permVertex σ (o k).2)
  | .path => fun k => permVertex σ (o k)

def BayesCertificate (M q s : ℕ) (r : ℝ) (e : Experiment) : Prop :=
  (∀ S : Support M q, IsRowStochastic (transition r S) ∧
    (∀ y : Vertex M, (∑ x : Vertex M, transition r S x y) = 1)) ∧
  IsRowStochastic (probability (M := M) (q := q) (s := s) r e) ∧
  (∀ (S : Support M q) (o : Obs M s e),
    0 < probability r e S o ∧
    probability r e S o = uniformMass M s e *
      ∏ k : Fin s, (1 + b r S (edges e o k).1 * chi (edges e o k).2) ∧
    probability r e S o = uniformMass M s e * background q r e o *
      ∏ i ∈ S.val, weight q r e o i) ∧
  (∀ o : Obs M s e,
    0 < partition (q := q) r e o ∧
    (∀ i : Fin M, 0 < weight q r e o i ∧ weight q r e o i = Real.exp (score q r e o i)) ∧
    (∀ S : Support M q, posterior r e o S =
      (∏ i ∈ S.val, weight q r e o i) / partition (q := q) r e o) ∧
    (∀ i j : Fin M, i ≠ j →
      inclusion q r e o i - inclusion q r e o j =
        (weight q r e o i - weight q r e o j) *
          (∑ U ∈ ((Finset.univ.erase i).erase j).powersetCard (q-1),
            ∏ k ∈ U, weight q r e o k) / partition (q := q) r e o) ∧
    (∀ i j : Fin M, inclusion q r e o i ≤ inclusion q r e o j ↔
      weight q r e o i ≤ weight q r e o j)) ∧
  IsRowStochastic (decision (M := M) (s := s) q r e) ∧
    (∀ o : Obs M s e, ∃ t : ℝ,
      let H := univ.filter (fun i => t < weight q r e o i)
      let E := univ.filter (fun i => weight q r e o i = t)
      H.card < q ∧ q ≤ H.card + E.card ∧
      (∀ T : Support M q, decision q r e o T =
        if H ⊆ T.val ∧ T.val ⊆ H ∪ E then ((E.card.choose (q-H.card) : ℕ) : ℝ)⁻¹ else 0)) ∧
  IsRowStochastic (allDecision (M := M) (s := s) q r e) ∧
    (∀ D' : FiniteMarkovKernel (Obs M s e) (Support M q),
      finiteBayesCost (prior M q) hammingLoss (probability r e) (decision (s := s) q r e) ≤
        finiteBayesCost (prior M q) hammingLoss (probability r e) D'.val) ∧
    (∀ D' : FiniteMarkovKernel (Obs M s e) (Finset (Fin M)),
      finiteBayesCost (prior M q) exactLoss (probability r e) (allDecision (s := s) q r e) ≤
        finiteBayesCost (prior M q) exactLoss (probability r e) D'.val)

/-- For either complete finite observation experiment, the uniform cutoff rule is Bayes
optimal for exactly-q Hamming loss and for exact recovery with arbitrary-subset actions. -/
theorem finite_support_bayes {M q s : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (e : Experiment) : BayesCertificate M q s r e := by
  have actual_laws {M q : ℕ} {r : ℝ}
      (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
      (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1) :
      (∀ S : Support M q, IsRowStochastic (transition r S) ∧
        (∀ y : Vertex M, (∑ x : Vertex M, transition r S x y) = 1)) ∧
      (∀ (s : ℕ) (e : Experiment),
        IsRowStochastic (probability (M := M) (q := q) (s := s) r e) ∧
        ∀ (S : Support M q) (o : Obs M s e),
          0 < probability r e S o ∧
          probability r e S o = uniformMass M s e *
            ∏ k : Fin s, (1 + b r S (edges e o k).1 * chi (edges e o k).2)) := by
    classical
    have hM : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    have hden : 0 < 2 * (M : ℝ) := by positivity
    have hfac (S : Support M q) (x y : Vertex M) : 0 < 1 + b r S x * chi y := by
      rcases x with i | i <;> rcases y with j | j
      · dsimp [b, chi]; split_ifs <;> linarith
      · dsimp [b, chi]; split_ifs <;> linarith
      · norm_num [b, chi]
      · norm_num [b, chi]
    have hpos (S : Support M q) (x y : Vertex M) : 0 < transition r S x y :=
      div_pos (hfac S x y) hden
    have hrow (S : Support M q) (x : Vertex M) : ∑ y, transition r S x y = 1 := by
      simp only [transition, Fintype.sum_sum_type, chi, mul_one, mul_neg_one,
        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      <;> ring
    have hcol (S : Support M q) (y : Vertex M) : ∑ x, transition r S x y = 1 := by
      have hsum : ∑ i : Fin M, (if i ∈ S.val then r else -compensation M q r) = 0 := by
        rw [sum_ite]
        simp only [filter_mem_eq_inter, filter_notMem_eq_sdiff]
        simp only [univ_inter, sum_const, nsmul_eq_mul, S.property,
          card_sdiff_of_subset (subset_univ S.val), card_univ, Fintype.card_fin]
        have hn : (M - q : ℕ) ≠ 0 := by omega
        simp only [compensation]
        field_simp
        <;> ring
      simp only [transition, sum_div, Fintype.sum_sum_type, b, zero_mul, add_zero]
      rw [← sum_div, sum_add_distrib, ← sum_mul, hsum]
      simp only [zero_mul, add_zero, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      field_simp
      <;> ring
    refine ⟨fun S => ⟨⟨fun x y => (hpos S x y).le, hrow S⟩, hcol S⟩, ?_⟩
    intro s e
    have hp (S : Support M q) (o : Obs M s e) : 0 < probability r e S o := by
      cases e with
      | pair => exact prod_pos (fun k _ => mul_pos (inv_pos.mpr hden) (hpos S _ _))
      | path => exact mul_pos (inv_pos.mpr hden) (prod_pos (fun k _ => hpos S _ _))
    have hn (S : Support M q) : ∑ o : Obs M s e, probability r e S o = 1 := by
      cases e with
      | pair =>
        change (∑ o : Fin s → Vertex M × Vertex M, ∏ k,
          (2 * (M : ℝ))⁻¹ * transition r S (o k).1 (o k).2) = 1
        rw [← Fintype.prod_sum (fun (_ : Fin s) (p : Vertex M × Vertex M) =>
          (2 * (M : ℝ))⁻¹ * transition r S p.1 p.2)]
        simp only [Fintype.sum_prod_type, ← mul_sum, hrow, mul_one,
          sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
        have : (2 * (M : ℝ))⁻¹ * ((M + M : ℕ) : ℝ) = 1 := by
          push_cast
          field_simp
          <;> ring
        simpa only [this, prod_const_one]
      | path =>
        dsimp [Obs, probability]
        have hpaths : ∀ n : ℕ, ∑ o : Fin (n+1) → Vertex M,
            ∏ k : Fin n, transition r S (o k.castSucc) (o k.succ) = (2 * (M : ℝ)) := by
          intro n
          induction n with
          | zero => simp [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]; ring
          | succ n ih =>
            rw [← (Fin.snocEquiv (fun _ : Fin (n+2) => Vertex M)).sum_comp]
            simp only [Fintype.sum_prod_type, Fin.snocEquiv, Equiv.coe_fn_mk]
            rw [sum_comm]
            simp only [Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
              ← Fin.castSucc_succ]
            simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, ← mul_sum, hrow, mul_one]
            exact ih
        rw [← mul_sum, hpaths, inv_mul_cancel₀ (ne_of_gt hden)]
    refine ⟨⟨fun S o => (hp S o).le, hn⟩, ?_⟩
    intro S o
    refine ⟨hp S o, ?_⟩
    cases e with
    | pair =>
      have heq (k : Fin s) :
          (2 * (M : ℝ))⁻¹ * transition r S (o k).1 (o k).2 =
          ((2 * (M : ℝ))⁻¹)^2 * (1 + b r S (o k).1 * chi (o k).2) := by
        simp only [transition, div_eq_mul_inv]; ring
      simp only [probability, uniformMass, edges, heq, prod_mul_distrib,
        prod_const, card_univ, Fintype.card_fin, ← pow_mul]

    | path =>
      simp only [probability, uniformMass, edges, transition, div_eq_mul_inv,
        prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, pow_succ]
      ring

  have likelihood_posterior {M q s : ℕ} {r : ℝ}
      (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
      (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
      (e : Experiment) (o : Obs M s e) :
      (∀ S : Support M q, probability r e S o = uniformMass M s e *
        background q r e o * ∏ i ∈ S.val, weight q r e o i) ∧
      (∀ i : Fin M, 0 < weight q r e o i ∧ weight q r e o i = Real.exp (score q r e o i)) ∧
      0 < partition (q := q) r e o ∧
      (∀ S : Support M q, posterior r e o S =
        (∏ i ∈ S.val, weight q r e o i) / partition (q := q) r e o) := by
    classical
    let a := compensation M q r
    let A := (1+r)/(1-a)
    let B := (1-r)/(1+a)
    have hA : 0 < A := div_pos (by linarith) (by dsimp [a]; linarith)
    have hB : 0 < B := div_pos (by linarith) (by dsimp [a]; linarith)
    let g (i : Fin M) (k : Fin s) : ℝ :=
      (if (edges e o k).1 = Sum.inl i ∧ chi (edges e o k).2 = 1 then A else 1) *
      (if (edges e o k).1 = Sum.inl i ∧ chi (edges e o k).2 = -1 then B else 1)
    have hw (i : Fin M) : weight q r e o i = ∏ k, g i k := by
      dsimp [g]
      rw [prod_mul_distrib]
      simp only [prod_ite, prod_const, one_pow, mul_one, count, weight, A, B, a]
    have hedge (S : Support M q) (k : Fin s) :
        1 + b r S (edges e o k).1 * chi (edges e o k).2 =
          (match (edges e o k).1 with
          | .inl _ => 1 - a * chi (edges e o k).2 | .inr _ => 1) * ∏ i ∈ S.val, g i k := by
      have hdA : 1 - a ≠ 0 := by dsimp [a]; linarith
      have hdB : 1 + a ≠ 0 := by dsimp [a]; linarith
      rcases he : edges e o k with ⟨x,y⟩
      rcases x with j | j <;> rcases y with l | l
      · simp only [he, b, chi, mul_one, g, Sum.inl.injEq, and_true, show (1 : ℝ) ≠ -1 by norm_num,
          and_false, if_false, mul_one]
        simp only [prod_ite_eq, A, a]
        split_ifs <;> field_simp [show 1 - compensation M q r ≠ 0 from hdA,
          show 1 + compensation M q r ≠ 0 from hdB] <;> ring
      · simp only [he, b, chi, mul_neg_one, g, Sum.inl.injEq, and_true, show (-1 : ℝ) ≠ 1 by norm_num,
          and_false, if_false, one_mul]
        simp only [prod_ite_eq, B, a]
        split_ifs <;> field_simp [show 1 - compensation M q r ≠ 0 from hdA,
          show 1 + compensation M q r ≠ 0 from hdB] <;> ring
      · simp [he, b, chi, g]
      · simp [he, b, chi, g]
    have hlike (S : Support M q) : probability r e S o = uniformMass M s e *
        background q r e o * ∏ i ∈ S.val, weight q r e o i := by
      rw [(actual_laws hq hqm hr hr1 ha ha1).2 s e |>.2 S o |>.2]
      simp_rw [hedge, prod_mul_distrib, hw]
      rw [prod_comm]
      exact (mul_assoc _ _ _).symm
    have hwpos (i : Fin M) : 0 < weight q r e o i :=
      mul_pos (pow_pos hA _) (pow_pos hB _)
    have hcard : (univ.powersetCard q : Finset (Finset (Fin M))).Nonempty :=
      powersetCard_nonempty.mpr (by simpa using hqm.le)
    obtain ⟨S₀, hS₀⟩ := hcard
    let T₀ : Support M q := ⟨S₀, (mem_powersetCard.mp hS₀).2⟩
    letI : Nonempty (Support M q) := ⟨T₀⟩
    have hZ : 0 < partition (q := q) r e o := sum_pos
      (fun S _ => prod_pos (fun i _ => hwpos i)) univ_nonempty
    refine ⟨hlike, ?_, hZ, ?_⟩
    · intro i
      refine ⟨hwpos i, ?_⟩
      change A ^ count e o i 1 * B ^ count e o i (-1) =
        Real.exp (count e o i 1 * Real.log A + count e o i (-1) * Real.log B)
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hA, Real.exp_log hB]
    · intro S
      have hc : uniformMass M s e * background q r e o ≠ 0 := by
        have hp := ((actual_laws hq hqm hr hr1 ha ha1).2 s e).2 T₀ o |>.1
        rw [hlike T₀] at hp
        exact left_ne_zero_of_mul (ne_of_gt hp)
      simp only [posterior, hlike, ← mul_sum]
      rw [mul_div_mul_left _ _ hc]
      rfl

  have inclusion_order {M q s : ℕ} {r : ℝ}
      (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
      (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
      (e : Experiment) (o : Obs M s e) :
      (∀ i j : Fin M, i ≠ j →
        inclusion q r e o i - inclusion q r e o j =
          (weight q r e o i - weight q r e o j) *
            (∑ U ∈ ((univ.erase i).erase j).powersetCard (q-1),
              ∏ k ∈ U, weight q r e o k) / partition (q := q) r e o) ∧
      (∀ i j : Fin M, inclusion q r e o i ≤ inclusion q r e o j ↔
        weight q r e o i ≤ weight q r e o j) := by
    classical
    let w := weight q r e o
    have hp := likelihood_posterior hq hqm hr hr1 ha ha1 e o
    have hsum (f : Finset (Fin M) → ℝ) :
        (∑ S : Support M q, f S.val) = ∑ S ∈ univ.powersetCard q, f S := by
      exact (sum_subtype _ (fun S => by simp) f).symm
    have hone (i j : Fin M) (hij : i ≠ j) :
        (∑ S : Support M q, if i ∈ S.val ∧ j ∉ S.val then ∏ k ∈ S.val, w k else 0) =
          w i * ∑ U ∈ ((univ.erase i).erase j).powersetCard (q-1), ∏ k ∈ U, w k := by
      rw [hsum (fun S => if i ∈ S ∧ j ∉ S then ∏ k ∈ S, w k else 0), ← sum_filter, mul_sum]
      symm
      apply sum_bij (fun U _ => insert i U)
      · intro U hU
        obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hU
        have hi : i ∉ U := fun h => (mem_erase.mp (mem_erase.mp (hsub h)).2).1 rfl
        have hj : j ∉ U := fun h => (mem_erase.mp (hsub h)).1 rfl
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
        refine ⟨?_, mem_insert_self _ _, ?_⟩
        · rw [card_insert_of_notMem hi,hcard]; omega
        · simp [(Ne.symm hij), hj]
      · intro U hU V hV heq
        have hiU : i ∉ U := fun h =>
          (mem_erase.mp (mem_erase.mp ((mem_powersetCard.mp hU).1 h)).2).1 rfl
        have hiV : i ∉ V := fun h =>
          (mem_erase.mp (mem_erase.mp ((mem_powersetCard.mp hV).1 h)).2).1 rfl
        have := congrArg (fun T : Finset (Fin M) => T.erase i) heq
        simpa [hiU,hiV] using this
      · intro S hS
        obtain ⟨hS,hi,hj⟩ := mem_filter.mp hS
        refine ⟨S.erase i, mem_powersetCard.mpr ⟨?_, ?_⟩, insert_erase hi⟩
        · intro k hk
          simp only [mem_erase, mem_univ, and_true]
          exact ⟨fun heq => hj (heq ▸ mem_of_mem_erase hk), (mem_erase.mp hk).1⟩
        · rw [card_erase_of_mem hi, (mem_powersetCard.mp hS).2]
      · intro U hU
        have hi : i ∉ U := fun h =>
          (mem_erase.mp (mem_erase.mp ((mem_powersetCard.mp hU).1 h)).2).1 rfl
        rw [prod_insert hi]
    have hdiff (i j : Fin M) (hij : i ≠ j) :
        inclusion q r e o i - inclusion q r e o j =
          (w i-w j) * (∑ U ∈ ((univ.erase i).erase j).powersetCard (q-1), ∏ k ∈ U, w k) /
            partition (q := q) r e o := by
      have hrow (S : Support M q) :
          (if i ∈ S.val then ∏ k ∈ S.val, w k else 0) -
            (if j ∈ S.val then ∏ k ∈ S.val, w k else 0) =
          (if i ∈ S.val ∧ j ∉ S.val then ∏ k ∈ S.val, w k else 0) -
            (if j ∈ S.val ∧ i ∉ S.val then ∏ k ∈ S.val, w k else 0) := by
        by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;> simp [hi,hj]
      have hinc (i : Fin M) : inclusion q r e o i =
          (∑ S : Support M q, if i ∈ S.val then ∏ k ∈ S.val, w k else 0) /
            partition (q := q) r e o := by
        unfold inclusion
        rw [sum_div]
        apply sum_congr rfl
        intro S _
        rw [hp.2.2.2]
        split_ifs <;> simp [w]
      rw [hinc, hinc, ← sub_div, ← sum_sub_distrib]
      simp_rw [hrow]
      rw [sum_sub_distrib, hone i j hij, hone j i (Ne.symm hij), erase_right_comm]
      ring
    refine ⟨hdiff, ?_⟩
    intro i j
    by_cases hij : i = j
    · subst j; simp
    have hcard : q-1 ≤ ((univ.erase i).erase j : Finset (Fin M)).card := by
      rw [card_erase_of_mem (by simp [(Ne.symm hij)]), card_erase_of_mem (mem_univ i),
        card_univ, Fintype.card_fin]
      omega
    have hc : 0 < ∑ U ∈ ((univ.erase i).erase j).powersetCard (q-1), ∏ k ∈ U, w k :=
      sum_pos (fun U _ => prod_pos (fun k _ => (hp.2.1 k).1))
        (powersetCard_nonempty.mpr hcard)
    rw [← sub_nonpos, hdiff i j hij, div_le_iff₀ hp.2.2.1, zero_mul,
      ← zero_mul (∑ U ∈ ((univ.erase i).erase j).powersetCard (q-1), ∏ k ∈ U, w k),
      mul_le_mul_iff_left₀ hc, sub_nonpos]

  have cutoff_kernel {M q s : ℕ} (hq : 1 ≤ q) (hqm : q < M)
      (r : ℝ) (e : Experiment) :
      IsRowStochastic (decision (M := M) (s := s) q r e) ∧
      (∀ o : Obs M s e, ∃ t : ℝ,
        let H := univ.filter (fun i => t < weight q r e o i)
        let E := univ.filter (fun i => weight q r e o i = t)
        H.card < q ∧ q ≤ H.card + E.card ∧
        (∀ T : Support M q, decision q r e o T =
          if H ⊆ T.val ∧ T.val ⊆ H ∪ E then ((E.card.choose (q-H.card) : ℕ) : ℝ)⁻¹ else 0)) := by
    classical
    have hobs (o : Obs M s e) :
        (topFamily q r e o).Nonempty ∧ ∃ t : ℝ,
          let H := univ.filter (fun i => t < weight q r e o i)
          let E := univ.filter (fun i => weight q r e o i = t)
          H.card < q ∧ q ≤ H.card + E.card ∧
          (∀ T : Support M q, decision q r e o T =
            if H ⊆ T.val ∧ T.val ⊆ H ∪ E then ((E.card.choose (q-H.card) : ℕ) : ℝ)⁻¹ else 0) := by
      let w := weight q r e o
      let Top (w : Fin M → ℝ) (q : ℕ) (T : Finset (Fin M)) :=
        T.card = q ∧ ∀ i ∈ T, ∀ j ∉ T, w j ≤ w i
      have hcut : ∃ t : ℝ,
        let H := univ.filter (fun i => t < w i)
        let E := univ.filter (fun i => w i = t)
        H.card < q ∧ q ≤ H.card + E.card ∧
        (∀ T : Finset (Fin M), Top w q T ↔
          ∃ U ∈ E.powersetCard (q - H.card), T = H ∪ U) ∧
        Set.InjOn (fun U : Finset (Fin M) => H ∪ U)
          (↑(E.powersetCard (q - H.card)) : Set (Finset (Fin M))) := by
        let σ := Tuple.sort (fun i => OrderDual.toDual (w i))
        let f := w ∘ σ
        have hf : Antitone f := Tuple.monotone_sort (fun i => OrderDual.toDual (w i))
        let j : Fin M := ⟨q-1, by omega⟩
        let t := f j
        let H := univ.filter (fun i => t < w i)
        let E := univ.filter (fun i => w i = t)
        have hH : ∀ i, i ∈ H ↔ t < w i := fun i => by simp [H]
        have hE : ∀ i, i ∈ E ↔ w i = t := fun i => by simp [E]
        have hperm (p : ℝ → Prop) [DecidablePred p] :
            (univ.filter (fun i => p (f i))).card = (univ.filter (fun i => p (w i))).card :=
          card_equiv σ (fun i => by simp [f])
        have hHlt : H.card < q := by
          have hn := (Tuple.lt_card_gt_iff_apply_gt_of_antitone (j := j) (a := t) hf).not
          have hn' : ¬ (j.val < (univ.filter (fun i => t < f i)).card) := hn.mpr (lt_irrefl t)
          rw [hperm] at hn'
          dsimp [j] at hn'
          change (univ.filter (fun i => t < w i)).card < q
          omega
        have hdisj : Disjoint H E := by
          apply disjoint_left.mpr
          intro i hi hei
          have hgt := (hH i).mp hi
          have heq := (hE i).mp hei
          linarith
        have hHE : H ∪ E = univ.filter (fun i => t ≤ w i) := by
          ext i
          simp only [mem_union, hH, hE, mem_filter, mem_univ, true_and]
          constructor
          · rintro (h | h); exact h.le; exact h.ge
          · intro h; rcases lt_or_eq_of_le h with h | h
            · exact Or.inl h
            · exact Or.inr h.symm
        have hqHE : q ≤ H.card + E.card := by
          have hn := (Tuple.lt_card_ge_iff_apply_ge_of_antitone (j := j) (a := t) hf).mpr le_rfl
          rw [hperm, ← hHE, card_union_of_disjoint hdisj] at hn
          dsimp [j] at hn
          omega
        refine ⟨t, hHlt, hqHE, ?_, ?_⟩
        · intro A
          change Top w q A ↔ ∃ U ∈ E.powersetCard (q - H.card), A = H ∪ U
          constructor
          · intro hA
            have hHA : H ⊆ A := by
              intro i hi
              by_contra hnot
              obtain ⟨j, hj, hjnot⟩ := exists_mem_notMem_of_card_lt_card
                (show H.card < A.card by rw [hA.1]; exact hHlt)
              have hgt := (hH i).mp hi
              have hjle : w j ≤ t := le_of_not_gt (fun h => hjnot ((hH j).mpr h))
              have hij := hA.2 j hj i hnot
              linarith
            have hAU : A ⊆ H ∪ E := by
              intro i hi
              by_contra hinot
              have hiH : i ∉ H := fun h => hinot (mem_union_left E h)
              have hiE : i ∉ E := fun h => hinot (mem_union_right H h)
              have hilt : w i < t := lt_of_le_of_ne
                (le_of_not_gt (fun h => hiH ((hH i).mpr h)))
                (fun h => hiE ((hE i).mpr h))
              have hex : ∃ j ∈ H ∪ E, j ∉ A := by
                by_contra hn
                push Not at hn
                have heq : H ∪ E = A := eq_of_subset_of_card_le hn (by
                  rw [hA.1, card_union_of_disjoint hdisj]
                  exact hqHE)
                exact hinot (heq.symm ▸ hi)
              obtain ⟨j, hj, hjnot⟩ := hex
              have hjge : t ≤ w j := by
                rcases mem_union.mp hj with hj | hj
                · exact ((hH j).mp hj).le
                · exact ((hE j).mp hj).ge
              have hij := hA.2 i hi j hjnot
              linarith
            refine ⟨A \ H, mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
            · intro i hi
              have hh := mem_sdiff.mp hi
              exact (mem_union.mp (hAU hh.1)).resolve_left hh.2
            · rw [card_sdiff_of_subset hHA, hA.1]
            · exact (union_sdiff_of_subset hHA).symm
          · rintro ⟨U, hU, rfl⟩
            obtain ⟨hUE, hUcard⟩ := mem_powersetCard.mp hU
            have hd : Disjoint H U := hdisj.mono_right hUE
            refine ⟨?_, ?_⟩
            · rw [card_union_of_disjoint hd, hUcard]
              omega
            · intro i hi j hj
              have hjH : j ∉ H := fun h => hj (mem_union_left U h)
              have hjle : w j ≤ t := le_of_not_gt (fun h => hjH ((hH j).mpr h))
              rcases mem_union.mp hi with hi | hi
              · exact hjle.trans ((hH i).mp hi).le
              · exact hjle.trans ((hE i).mp (hUE hi)).ge
        · intro U hU V hV heq
          change H ∪ U = H ∪ V at heq
          have hUE := (mem_powersetCard.mp hU).1
          have hVE := (mem_powersetCard.mp hV).1
          have hUd : Disjoint H U := hdisj.mono_right hUE
          have hVd : Disjoint H V := hdisj.mono_right hVE
          have hleft : (H ∪ U) \ H = U := by
            ext i
            simp only [mem_sdiff, mem_union]
            constructor
            · rintro ⟨hi | hi, hn⟩
              · exact False.elim (hn hi)
              · exact hi
            · intro hi
              exact ⟨Or.inr hi, fun h => disjoint_left.mp hUd h hi⟩
          have hright : (H ∪ V) \ H = V := by
            ext i
            simp only [mem_sdiff, mem_union]
            constructor
            · rintro ⟨hi | hi, hn⟩
              · exact False.elim (hn hi)
              · exact hi
            · intro hi
              exact ⟨Or.inr hi, fun h => disjoint_left.mp hVd h hi⟩
          rw [← hleft, ← hright, heq]
      obtain ⟨t, hHlt, hqHE, hfiber, hinj⟩ := hcut
      let H := univ.filter (fun i => t < w i)
      let E := univ.filter (fun i => w i = t)
      let R := E.powersetCard (q-H.card)
      have himage : (topFamily q r e o).image Subtype.val = R.image (fun U => H ∪ U) := by
        ext T
        constructor
        · rintro hT
          obtain ⟨A,hA,rfl⟩ := mem_image.mp hT
          have htop : Top w q A.val := ⟨A.property, (mem_filter.mp hA).2⟩
          obtain ⟨U,hU,hAU⟩ := (hfiber A.val).mp htop
          exact mem_image.mpr ⟨U,hU,hAU.symm⟩
        · intro hT
          obtain ⟨U,hU,rfl⟩ := mem_image.mp hT
          have htop := (hfiber (H ∪ U)).mpr ⟨U,hU,rfl⟩
          exact mem_image.mpr ⟨⟨H ∪ U, htop.1⟩, mem_filter.mpr ⟨mem_univ _, htop.2⟩, rfl⟩
      have hcard : (topFamily q r e o).card = E.card.choose (q-H.card) := by
        rw [← card_image_of_injective (topFamily q r e o) Subtype.val_injective,
          himage, card_image_iff.mpr hinj, card_powersetCard]
      have hn : (topFamily q r e o).Nonempty := card_pos.mp (by
        rw [hcard]
        exact Nat.choose_pos (by change q-H.card ≤ E.card; change q ≤ H.card + E.card at hqHE; omega))
      refine ⟨hn, t, hHlt, hqHE, ?_⟩
      intro T
      have hevent : T ∈ topFamily q r e o ↔ H ⊆ T.val ∧ T.val ⊆ H ∪ E := by
        constructor
        · intro hT
          obtain ⟨U,hU,hT⟩ := (hfiber T.val).mp ⟨T.property, (mem_filter.mp hT).2⟩
          rw [hT]
          exact ⟨subset_union_left, union_subset_union_right (mem_powersetCard.mp hU).1⟩
        · rintro ⟨hHT,hTH⟩
          have hU : T.val \ H ∈ E.powersetCard (q-H.card) := mem_powersetCard.mpr ⟨by
            intro i hi
            exact (mem_union.mp (hTH (mem_sdiff.mp hi).1)).resolve_left (mem_sdiff.mp hi).2,
            by rw [card_sdiff_of_subset hHT, T.property]⟩
          have ht := (hfiber T.val).mpr ⟨T.val \ H, hU, (union_sdiff_of_subset hHT).symm⟩
          exact mem_filter.mpr ⟨mem_univ _,ht.2⟩
      simp only [decision, hevent, hcard]
      rfl
    refine ⟨⟨?_, ?_⟩, fun o => (hobs o).2⟩
    · intro o T
      dsimp [decision]
      split_ifs <;> positivity
    · intro o
      have hn : ((topFamily q r e o).card : ℝ) ≠ 0 := by
        exact_mod_cast (card_pos.mpr (hobs o).1).ne'
      simp [decision, ← sum_filter, nsmul_eq_mul, hn]

  have posterior_optimal_actions {M q s : ℕ} {r : ℝ}
      (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
      (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
      (e : Experiment) (o : Obs M s e) (T : Support M q)
      (hT : T ∈ topFamily q r e o) :
      (∀ A : Support M q,
        (∑ S, posterior r e o S * hammingLoss S T) ≤
          ∑ S, posterior r e o S * hammingLoss S A) ∧
      (∀ A : Finset (Fin M),
        (∑ S : Support M q, posterior r e o S * exactLoss S T.val) ≤
          ∑ S : Support M q, posterior r e o S * exactLoss S A) := by
    classical
    let w := weight q r e o
    let p : Support M q → ℝ := posterior r e o
    have hp := likelihood_posterior hq hqm hr hr1 ha ha1 e o
    have horder := (inclusion_order hq hqm hr hr1 ha ha1 e o).2
    have htop := (mem_filter.mp hT).2
    letI : Nonempty (Support M q) := ⟨T⟩
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hpn (S : Support M q) : 0 ≤ p S := by
      rw [show p S = (∏ i ∈ S.val,w i) / partition (q := q) r e o from hp.2.2.2 S]
      exact div_nonneg (prod_nonneg (fun i _ => (hp.2.1 i).1.le)) hp.2.2.1.le
    have hpnorm : ∑ S, p S = 1 := by
      dsimp [p,posterior]
      rw [← sum_div]
      apply div_self
      exact ne_of_gt (sum_pos
        (fun S _ => ((actual_laws hq hqm hr hr1 ha ha1).2 s e).2 S o |>.1) univ_nonempty)
    have hbest (A : Support M q) :
        (∏ i ∈ A.val, w i) ≤ (∏ i ∈ T.val, w i) ∧
        (∑ i ∈ A.val, inclusion q r e o i) ≤ ∑ i ∈ T.val, inclusion q r e o i := by
      have hc : (A.val \ T.val).card = (T.val \ A.val).card :=
        card_sdiff_comm (A.property.trans T.property.symm)
      let bij : ↥(A.val \ T.val) ≃ ↥(T.val \ A.val) :=
        Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; exact hc)
      have hwi (i : ↥(A.val \ T.val)) : w i ≤ w (bij i) :=
        htop (bij i) (mem_sdiff.mp (bij i).property).1 i (mem_sdiff.mp i.property).2
      have hprod : (∏ i ∈ A.val \ T.val, w i) ≤ ∏ i ∈ T.val \ A.val, w i := by
        rw [← prod_coe_sort (A.val \ T.val) w, ← prod_coe_sort (T.val \ A.val) w,
          ← bij.prod_comp (fun i => w i)]
        exact prod_le_prod (fun i _ => (hp.2.1 i).1.le) (fun i _ => hwi i)
      have hsum : (∑ i ∈ A.val \ T.val, inclusion q r e o i) ≤
          ∑ i ∈ T.val \ A.val, inclusion q r e o i := by
        rw [← sum_coe_sort (A.val \ T.val) (inclusion q r e o),
          ← sum_coe_sort (T.val \ A.val) (inclusion q r e o),
          ← bij.sum_comp (fun i => inclusion q r e o i)]
        exact sum_le_sum (fun i _ => (horder i (bij i)).mpr (hwi i))
      have hprodA : (∏ i ∈ A.val \ T.val, w i) * (∏ i ∈ A.val ∩ T.val, w i) = ∏ i ∈ A.val, w i := by
        rw [← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter]
      have hprodT : (∏ i ∈ T.val \ A.val, w i) * (∏ i ∈ A.val ∩ T.val, w i) = ∏ i ∈ T.val, w i := by
        rw [inter_comm A.val T.val, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter]
      have hsumA := sum_union (f := inclusion q r e o) (disjoint_sdiff_inter A.val T.val)
      have hsumT := sum_union (f := inclusion q r e o) (disjoint_sdiff_inter T.val A.val)
      rw [sdiff_union_inter] at hsumA hsumT
      rw [inter_comm T.val A.val] at hsumT
      refine ⟨?_, by linarith⟩
      rw [← hprodA, ← hprodT]
      exact mul_le_mul_of_nonneg_right hprod (prod_nonneg (fun i _ => (hp.2.1 i).1.le))
    have hh (S A : Support M q) : hammingLoss S A = 1 - ((A.val ∩ S.val).card : ℝ) / q := by
      have hdis : Disjoint (A.val \ S.val) (S.val \ A.val) := by
        apply disjoint_left.mpr
        intro i hi hj
        exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
      have hn : (symmDiff A.val S.val).card + 2*(A.val ∩ S.val).card = 2*q := by
        rw [Finset.symmDiff_def, card_union_of_disjoint hdis]
        have h₁ := card_sdiff_add_card_inter A.val S.val
        have h₂ := card_sdiff_add_card_inter S.val A.val
        rw [inter_comm S.val A.val, S.property] at h₂
        rw [A.property] at h₁
        omega
      have hnR : ((symmDiff A.val S.val).card : ℝ) + 2*(A.val ∩ S.val).card = 2*q := by exact_mod_cast hn
      unfold hammingLoss
      field_simp
      linarith
    have hhc (A : Support M q) : (∑ S, p S * hammingLoss S A) =
        1 - (∑ i ∈ A.val, inclusion q r e o i) / q := by
      have hm : (∑ i ∈ A.val, inclusion q r e o i) =
          ∑ S, p S * (A.val ∩ S.val).card := by
        simp only [inclusion]
        rw [sum_comm]
        apply sum_congr rfl
        intro S _
        rw [← sum_filter]
        simp [filter_mem_eq_inter, p, nsmul_eq_mul, mul_comm]
      simp only [hh, mul_sub, mul_one, ← mul_div_assoc]
      rw [sum_sub_distrib, hpnorm, ← sum_div, ← hm]
    have hec (A : Support M q) : (∑ S, p S * exactLoss S A.val) = 1-p A := by
      have he (S : Support M q) : exactLoss S A.val = 1 - if S = A then (1 : ℝ) else 0 := by
        simp only [exactLoss, Subtype.ext_iff]
        by_cases h : S.val = A.val
        · simp [h]
        · simp [h, Ne.symm h]
      simp_rw [he, mul_sub, mul_one, mul_ite, mul_one, mul_zero]
      rw [sum_sub_distrib, hpnorm]
      simp
    refine ⟨?_, ?_⟩
    · intro A
      change (∑ S, p S * hammingLoss S T) ≤ ∑ S, p S * hammingLoss S A
      rw [hhc,hhc]
      exact sub_le_sub_left (div_le_div_of_nonneg_right (hbest A).2 (by positivity)) 1
    · intro A
      change (∑ S, p S * exactLoss S T.val) ≤ ∑ S, p S * exactLoss S A
      rw [hec T]
      by_cases hA : A.card = q
      · let A' : Support M q := ⟨A,hA⟩
        change 1-p T ≤ ∑ S, p S * exactLoss S A'.val
        rw [hec A']
        apply sub_le_sub_left
        dsimp [p]
        rw [hp.2.2.2, hp.2.2.2]
        exact div_le_div_of_nonneg_right (hbest A').1 hp.2.2.1.le
      · have he (S : Support M q) : exactLoss S A = 1 := by
          apply if_neg
          intro h
          exact hA (h ▸ S.property)
        simp only [he,mul_one,hpnorm]
        linarith [hpn T]

  have bayes_rules {M q s : ℕ} {r : ℝ}
      (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
      (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
      (e : Experiment) :
      IsRowStochastic (allDecision (M := M) (s := s) q r e) ∧
      (∀ D' : FiniteMarkovKernel (Obs M s e) (Support M q),
        finiteBayesCost (prior M q) hammingLoss (probability r e) (decision (s := s) q r e) ≤
          finiteBayesCost (prior M q) hammingLoss (probability r e) D'.val) ∧
      (∀ D' : FiniteMarkovKernel (Obs M s e) (Finset (Fin M)),
        finiteBayesCost (prior M q) exactLoss (probability r e) (allDecision (s := s) q r e) ≤
          finiteBayesCost (prior M q) exactLoss (probability r e) D'.val) := by
    classical
    have hqD := (cutoff_kernel (s := s) hq hqm r e).1
    have hext (f : Support M q → ℝ) :
        (∑ T : Finset (Fin M), if h : T.card = q then f ⟨T,h⟩ else 0) = ∑ T, f T := by
      symm
      apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
      · intro A hA
        split_ifs with h
        · exact False.elim (hA ⟨⟨A,h⟩,rfl⟩)
        · rfl
      · intro T
        simp [T.property]
    have haD : IsRowStochastic (allDecision (M := M) (s := s) q r e) := by
      refine ⟨?_, ?_⟩
      · intro o A; unfold allDecision; split_ifs; exact hqD.1 o _; exact le_rfl
      · intro o; unfold allDecision; rw [hext]; exact hqD.2 o
    have hbayes {A : Type} [Fintype A] (loss : Support M q → A → ℝ)
        (D : Obs M s e → A → ℝ) (hD : IsRowStochastic D)
        (hopt : ∀ o a, D o a ≠ 0 → ∀ b,
          (∑ S, posterior r e o S * loss S a) ≤ ∑ S, posterior r e o S * loss S b)
        (D' : FiniteMarkovKernel (Obs M s e) A) :
        finiteBayesCost (prior M q) loss (probability r e) D ≤
          finiteBayesCost (prior M q) loss (probability r e) D'.val := by
      let c (o : Obs M s e) (a : A) := ∑ S, probability r e S o * loss S a
      have hc (o : Obs M s e) (a : A) : c o a =
          (∑ S : Support M q, probability r e S o) *
            ∑ S, posterior r e o S * loss S a := by
        have hne : (∑ S : Support M q, probability r e S o) ≠ 0 := by
          obtain ⟨S,hS⟩ := powersetCard_nonempty.mpr (show q ≤ (univ : Finset (Fin M)).card by simpa using hqm.le)
          letI : Nonempty (Support M q) := ⟨⟨S,(mem_powersetCard.mp hS).2⟩⟩
          exact ne_of_gt (sum_pos
            (fun S _ => ((actual_laws hq hqm hr hr1 ha ha1).2 s e).2 S o |>.1) univ_nonempty)
        dsimp [c]
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        dsimp [posterior]
        field_simp
      have hb (o : Obs M s e) (a b : A) (h : D o a ≠ 0) : c o a ≤ c o b := by
        rw [hc,hc]
        exact mul_le_mul_of_nonneg_left (hopt o a h b)
          (sum_nonneg (fun S _ => ((actual_laws hq hqm hr hr1 ha ha1).2 s e).1.1 S o))
      have hpoint (o : Obs M s e) : (∑ a, D o a * c o a) ≤ ∑ b, D'.val o b * c o b := by
        calc
          (∑ a, D o a * c o a) = ∑ b, D'.val o b * ∑ a, D o a * c o a := by
            rw [← sum_mul,D'.property.2,one_mul]
          _ ≤ ∑ b, D'.val o b * c o b := by
            apply sum_le_sum
            intro b _
            apply mul_le_mul_of_nonneg_left _ (D'.property.1 o b)
            calc
              (∑ a, D o a * c o a) ≤ ∑ a, D o a * c o b := by
                apply sum_le_sum
                intro a _
                by_cases h : D o a = 0
                · simp [h]
                · exact mul_le_mul_of_nonneg_left (hb o a b h) (hD.1 o a)
              _ = c o b := by rw [← sum_mul,hD.2,one_mul]
      have hexpand (d : Obs M s e → A → ℝ) :
          finiteBayesCost (prior M q) loss (probability r e) d =
            (Fintype.card (Support M q) : ℝ)⁻¹ * ∑ o, ∑ a, d o a * c o a := by
        unfold finiteBayesCost prior D5.S3.Divergence.ClassicalDPI.channelOutput
        rw [← mul_sum]
        congr 1
        simp only [sum_mul]
        rw [sum_comm]
        simp_rw [sum_comm (s := (univ : Finset (Support M q))) (t := (univ : Finset (Obs M s e)))]
        rw [sum_comm]
        apply sum_congr rfl
        intro o _
        apply sum_congr rfl
        intro a _
        dsimp [c]
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        ring
      rw [hexpand,hexpand]
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun o _ => hpoint o)) (by positivity)
    refine ⟨haD, ?_, ?_⟩
    · intro D'
      apply hbayes hammingLoss (decision (s := s) q r e) hqD _ D'
      intro o T h A
      have hT : T ∈ topFamily q r e o := by
        by_contra hn
        exact h (if_neg hn)
      exact (posterior_optimal_actions hq hqm hr hr1 ha ha1 e o T hT).1 A
    · intro D'
      apply hbayes exactLoss (allDecision (s := s) q r e) haD _ D'
      intro o T h A
      have hcard : T.card = q := by
        by_contra hn
        exact h (dif_neg hn)
      have hT : (⟨T,hcard⟩ : Support M q) ∈ topFamily q r e o := by
        by_contra hn
        exact h (by simp [allDecision,hcard,decision,hn])
      exact (posterior_optimal_actions hq hqm hr hr1 ha ha1 e o ⟨T,hcard⟩ hT).2 A

  have hl := actual_laws hq hqm hr hr1 ha ha1
  have hp := likelihood_posterior (s := s) hq hqm hr hr1 ha ha1 e
  have hi := inclusion_order (s := s) hq hqm hr hr1 ha ha1 e
  have hc := cutoff_kernel (s := s) hq hqm r e
  have hb := bayes_rules (s := s) hq hqm hr hr1 ha ha1 e
  refine ⟨hl.1, (hl.2 s e).1, ?_, ?_, hc.1, hc.2, hb.1, hb.2.1, hb.2.2⟩
  · intro S o
    exact ⟨((hl.2 s e).2 S o).1, ((hl.2 s e).2 S o).2, (hp o).1 S⟩
  · intro o
    exact ⟨(hp o).2.2.1, (hp o).2.1, (hp o).2.2.2, (hi o).1, (hi o).2⟩

#print axioms finite_support_bayes
end
end D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
