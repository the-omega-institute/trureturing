/- GID: D5/S1/Words/Patterns/Separable/OccupiedComparison
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedComparison
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Topology.Algebra.InfiniteSum.Real]
   utility: none
   digest: The actual occupied-diagonal fixed point and strict nonlinear maximum comparison. -/

import D5.S1.Words.Patterns.Separable.ActualCardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Set.Finite.Lemmas

namespace D5.S1.Words.Patterns.Separable.OccupiedComparison

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open scoped BigOperators

noncomputable def b : ℝ := Real.sqrt 2 - 1
noncomputable def rho : ℝ := b ^ 2
noncomputable def a : ℝ := 1 - b
noncomputable def h : ℝ := (1 + b) / 2
noncomputable def ceiling : ℝ := a / 2
/-- Each actual sum-indecomposable shape contributes once if its diagonal is occupied. -/
noncomputable def occupiedCount (n : ℕ) (e : ℤ) : ℕ := Nat.card {π : Indecomposable false n //
    ∃ j : Fin n, (j.val : ℤ) - ((π.val.val j).val : ℤ) = e}
/-- At-least-one diagonal occupation for an actual permutation. -/
def hitsDiagonal {n : ℕ} (π : Equiv.Perm (Fin n)) (e : ℤ) : Prop :=
  ∃ j : Fin n, (j.val : ℤ) - ((π j).val : ℤ) = e
noncomputable def allOccupiedCount (n : ℕ) (e : ℤ) : ℕ :=
  Nat.card {π : Avoider n // hitsDiagonal π.val e}
noncomputable def signedOccupiedCount (sign : Bool) (n : ℕ) (e : ℤ) : ℕ :=
  Nat.card {π : Indecomposable sign n // hitsDiagonal π.val.val e}
noncomputable def decomposableOccupiedCount (sign : Bool) (n : ℕ) (e : ℤ) : ℕ :=
  Nat.card {π : D5.S1.Words.Patterns.Separable.ActualCardinality.ProperSigned sign n //
    hitsDiagonal π.val.val e}
/-- The length index is shifted to exclude the empty permutation. -/
noncomputable def rawOccupation (e : ℤ) : ℝ :=
  ∑' n : ℕ, rho ^ (n + 1) * (occupiedCount (n + 1) e : ℝ)
noncomputable def occupation (e : ℤ) : ℝ := (2 / a) * rawOccupation e
noncomputable def shapeWeight (n : ℕ) : ℝ := rho ^ (n + 1) * (Nat.card (Avoider (n + 1)) : ℝ)
/-- The correction at index zero is the genuine length-one correction. -/
noncomputable def kernelWeight (n : ℕ) : ℝ := shapeWeight n + if n = 0 then rho / 2 else 0
noncomputable def lossWeight (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) * shapeWeight n + if n = 0 then rho / 2 else 0
noncomputable def loss (x : ℝ) : ℝ := x ^ 2 / (h + x)
noncomputable def neighborTerm (n : ℕ) (x : ℝ) : ℝ := kernelWeight n * x - lossWeight n * loss x
noncomputable def forcing (e : ℤ) : ℝ :=
  if e = 0 then rho else (rho / 2) * shapeWeight (e.natAbs - 1)
noncomputable def occupationMap (u : ℤ → ℝ) (e : ℤ) : ℝ := forcing e + ∑' n : ℕ,
    (neighborTerm n (u (e + (n + 1 : ℕ))) + neighborTerm n (u (e - (n + 1 : ℕ))))
set_option maxHeartbeats 4000000 in
-- Actual convergence, event transport and strict comparison share one proof.
/-- The literal actual occupation mass is a fixed point of its nonlinear map,
and bounds every vanishing subsolution in the actual mass box. Critical
convergence, event transport and reflection retain the singleton correction. -/
theorem actual_occupation_subsolution_comparison : Summable shapeWeight ∧
    (∑' n, shapeWeight n) = b ∧
    (∑' n, kernelWeight n) = (1 / 2 : ℝ) ∧
    (∀ e, Summable (fun n : ℕ =>
      rho ^ (n + 1) * (occupiedCount (n + 1) e : ℝ))) ∧
    (∀ e, 0 ≤ rawOccupation e ∧ rawOccupation e ≤ ceiling) ∧
    (∀ sign n e, decomposableOccupiedCount sign n e = ∑ cut ∈ Finset.Ioo 0 n,
        if sign then
          signedOccupiedCount sign cut (e + (n - cut : ℕ)) * Nat.card (Avoider (n - cut)) +
            Nat.card (Indecomposable sign cut) * allOccupiedCount (n - cut) (e - cut)
        else
          signedOccupiedCount sign cut e *
              (Nat.card (Avoider (n - cut)) - allOccupiedCount (n - cut) e) +
            Nat.card (Indecomposable sign cut) * allOccupiedCount (n - cut) e) ∧
    (∀ sign n e, allOccupiedCount n e =
      signedOccupiedCount sign n e + decomposableOccupiedCount sign n e) ∧
    (∀ sign n e, 2 ≤ n → decomposableOccupiedCount sign n e = signedOccupiedCount (!sign) n e) ∧
    (∀ sign e, signedOccupiedCount sign 1 e = if e = 0 then 1 else 0) ∧
    (∀ sign n e, signedOccupiedCount sign n e = signedOccupiedCount sign n (-e)) ∧
    (∀ e, rawOccupation e = occupationMap rawOccupation e) ∧
    (∀ w : ℤ → ℝ, (∀ e, 0 ≤ w e ∧ w e ≤ ceiling) →
      (∀ ε : ℝ, 0 < ε → Set.Finite {e : ℤ | ε ≤ w e}) →
      (∀ e, w e ≤ occupationMap w e) → ∀ e, w e ≤ rawOccupation e) := by
  classical
  have sqrtSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have sqrtBounds : 1 < Real.sqrt (2 : ℝ) ∧ Real.sqrt (2 : ℝ) < 2 := by
    constructor <;> nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hp : 0 < h := by dsimp [h, b]; linarith
  have hc : 0 < ceiling := by dsimp [ceiling, a, b]; linarith [sqrtBounds.2]
  have hsumc : h + ceiling = 1 := by dsimp [h, ceiling, a, b]; ring
  have hsq : h ^ 2 = (1 / 2 : ℝ) := by dsimp [h, b]; nlinarith
  have rhop : 0 < rho := by exact pow_pos (sub_pos.mpr sqrtBounds.1) 2
  have tn (n : ℕ) : 0 ≤ shapeWeight n := by
    unfold shapeWeight
    positivity
  obtain ⟨_, actualCounts, _, _, _, _, _, _, _, _⟩ :=
    D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
  have weightCount (n : ℕ) : shapeWeight n = rho ^ (n + 1) * (Nat.largeSchroder n : ℝ) := by
    simp only [shapeWeight, actualCounts (n + 1) (by omega), Nat.add_sub_cancel]
  have weightZero : shapeWeight 0 = rho := by simp [weightCount]
  have recurrence (n : ℕ) : shapeWeight (n + 1) = rho * shapeWeight n +
      ∑ pair ∈ Finset.antidiagonal n, shapeWeight pair.1 * shapeWeight pair.2 := by
    have counts : (Nat.largeSchroder (n + 1) : ℝ) = (Nat.largeSchroder n : ℝ) +
        ∑ pair ∈ Finset.antidiagonal n,
          (Nat.largeSchroder pair.1 : ℝ) * (Nat.largeSchroder pair.2 : ℝ) := by
      have natural := Nat.largeSchroder_succ n
      rw [← Nat.range_succ_eq_Iic] at natural
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Nat.largeSchroder i * Nat.largeSchroder j)] at natural
      exact_mod_cast natural
    rw [weightCount, counts, mul_add, Finset.mul_sum, weightCount]
    congr 1
    · rw [pow_succ]
      ring
    · apply Finset.sum_congr rfl
      intro pair member
      rw [weightCount, weightCount]
      have indices := Finset.mem_antidiagonal.mp member
      have exponents : n + 1 + 1 = (pair.1 + 1) + (pair.2 + 1) := by omega
      rw [exponents, pow_add]
      ring
  have bp : 0 < b := sub_pos.mpr sqrtBounds.1
  have bquadratic : b ^ 2 + 2 * b = 1 := by dsimp [b]; nlinarith
  have rhoValue : rho = 1 - 2 * b := by dsimp [rho]; nlinarith
  have critical : rho + rho * b + b ^ 2 = b := by rw [rhoValue]; nlinarith
  have triangleBound (n : ℕ) : (∑ k ∈ Finset.range n,
        ∑ pair ∈ Finset.antidiagonal k, shapeWeight pair.1 * shapeWeight pair.2) ≤
      (∑ k ∈ Finset.range n, shapeWeight k) ^ 2 := by
    have disjoint : Set.PairwiseDisjoint (Finset.range n : Set ℕ) Finset.antidiagonal := by
      intro i _ j _ different
      apply Finset.disjoint_left.mpr
      intro pair hi hj
      exact different ((Finset.mem_antidiagonal.mp hi).symm.trans (Finset.mem_antidiagonal.mp hj))
    rw [← Finset.sum_biUnion disjoint]
    calc
      (∑ pair ∈ (Finset.range n).biUnion Finset.antidiagonal,
          shapeWeight pair.1 * shapeWeight pair.2) ≤
          ∑ pair ∈ (Finset.range n) ×ˢ (Finset.range n),
            shapeWeight pair.1 * shapeWeight pair.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro pair member
          obtain ⟨k, hk, hpair⟩ := Finset.mem_biUnion.mp member
          have indices := Finset.mem_antidiagonal.mp hpair
          simp only [Finset.mem_product, Finset.mem_range]
          have := Finset.mem_range.mp hk
          omega
        · intro pair _ _
          exact mul_nonneg (tn _) (tn _)
      _ = (∑ k ∈ Finset.range n, shapeWeight k) ^ 2 := by
        rw [Finset.sum_product, ← Finset.sum_mul_sum, pow_two]
  have partialBound (n : ℕ) : (∑ k ∈ Finset.range n, shapeWeight k) ≤ b := by
    induction n with
    | zero => simpa using bp.le
    | succ n ih =>
      rw [Finset.sum_range_succ', weightZero]
      simp_rw [recurrence]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have nonneg : 0 ≤ ∑ k ∈ Finset.range n, shapeWeight k := Finset.sum_nonneg (fun k _ => tn k)
      have squareBound : (∑ k ∈ Finset.range n, shapeWeight k) ^ 2 ≤ b ^ 2 := by nlinarith
      have linearBound := mul_le_mul_of_nonneg_left ih rhop.le
      have quadraticBound := triangleBound n
      linarith [critical]
  have hsum : Summable shapeWeight := summable_of_sum_range_le tn partialBound
  have productSum : Summable (fun pair : ℕ × ℕ =>
      shapeWeight pair.1 * shapeWeight pair.2) := hsum.mul_of_nonneg hsum tn tn
  have convolutionSum := summable_sum_mul_antidiagonal_of_summable_mul productSum
  have cauchy := hsum.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsum productSum
  have totalEquation : (∑' n, shapeWeight n) = rho + rho * (∑' n, shapeWeight n) +
      (∑' n, shapeWeight n) ^ 2 := by
    calc
      (∑' n, shapeWeight n) = rho + ∑' n, shapeWeight (n + 1) := by
        rw [hsum.tsum_eq_zero_add, weightZero]
      _ = rho + ∑' n, (rho * shapeWeight n +
          ∑ pair ∈ Finset.antidiagonal n, shapeWeight pair.1 * shapeWeight pair.2) := by
        congr 1
        exact tsum_congr recurrence
      _ = rho + rho * (∑' n, shapeWeight n) + (∑' n, shapeWeight n) ^ 2 := by
        rw [((hsum.mul_left rho).tsum_add convolutionSum), tsum_mul_left, ← cauchy]
        ring
  have shapeTotal : (∑' n, shapeWeight n) = b := by
    rw [rhoValue] at totalEquation
    have zero : ((∑' n, shapeWeight n) - b) ^ 2 = 0 := by nlinarith [bquadratic]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp zero)
  have kn (n : ℕ) : 0 ≤ kernelWeight n := by
    unfold kernelWeight
    have := tn n
    split_ifs <;> positivity
  have rn (n : ℕ) : 0 ≤ lossWeight n := by
    unfold lossWeight
    have := tn n
    split_ifs <;> positivity
  have kr (n : ℕ) : lossWeight n / 2 ≤ kernelWeight n := by
    unfold kernelWeight lossWeight
    split_ifs <;> nlinarith [tn n]
  have kzero : 0 < kernelWeight 0 := by
    simp only [kernelWeight, ite_true]
    linarith [tn 0]
  have rzero : 0 < lossWeight 0 := by
    simp only [lossWeight, ite_true]
    nlinarith [tn 0]
  have deltaSum : Summable (fun n : ℕ => if n = 0 then rho / 2 else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      simp only [Finset.mem_singleton] at hn
      exact if_neg hn)
  have ksum : Summable kernelWeight := hsum.add deltaSum
  have hmass : ∑' n : ℕ, kernelWeight n = (1 / 2 : ℝ) := by
    change tsum (fun n : ℕ => shapeWeight n + if n = 0 then rho / 2 else 0) = _
    rw [hsum.tsum_add deltaSum, shapeTotal]
    simp only [tsum_ite_eq]
    rw [rhoValue]
    ring
  obtain ⟨_, _, _, halfCounts, _, _, singletonCount, tinyCounts, _, _⟩ :=
    D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
  let indecomposableWeight (n : ℕ) : ℝ :=
    rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ)
  have indecomposableIdentity (n : ℕ) : indecomposableWeight n =
      (kernelWeight n + (if n = 0 then rho / 2 else 0)) / 2 := by
    by_cases nz : n = 0
    · subst n
      have singletonIndecomposable := (tinyCounts false).2
      simp only [indecomposableWeight, kernelWeight, shapeWeight,
        singletonIndecomposable, singletonCount, Nat.cast_one, zero_add,
        pow_one, ite_true]
      ring
    · have large : 2 ≤ n + 1 := by omega
      have halfReal : (2 : ℝ) * (Nat.card (Indecomposable false (n + 1)) : ℝ) =
          (Nat.card (Avoider (n + 1)) : ℝ) := by
        exact_mod_cast halfCounts false (n + 1) large
      dsimp [indecomposableWeight, kernelWeight, shapeWeight]
      simp only [nz, ite_false, add_zero]
      rw [← halfReal]
      ring
  have indecomposableSummable : Summable indecomposableWeight := by
    apply Summable.congr ((ksum.add deltaSum).div_const 2)
    intro n
    exact (indecomposableIdentity n).symm
  have indecomposableTotal : (∑' n, indecomposableWeight n) = ceiling := by
    calc
      (∑' n, indecomposableWeight n) =
          (∑' n, (kernelWeight n + (if n = 0 then rho / 2 else 0)) / 2) :=
        tsum_congr indecomposableIdentity
      _ = ((∑' n, kernelWeight n) + rho / 2) / 2 := by
        rw [tsum_div_const, ksum.tsum_add deltaSum]
        simp
      _ = ceiling := by
        rw [hmass]
        dsimp [ceiling, a, rho, b]
        nlinarith
  have occupiedBound (n : ℕ) (e : ℤ) :
      rho ^ (n + 1) * (occupiedCount (n + 1) e : ℝ) ≤ indecomposableWeight n := by
    have cardinal : occupiedCount (n + 1) e ≤ Nat.card (Indecomposable false (n + 1)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast cardinal) (by positivity)
  have actualSummable (e : ℤ) : Summable (fun n : ℕ =>
      rho ^ (n + 1) * (occupiedCount (n + 1) e : ℝ)) := by
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => occupiedBound n e) indecomposableSummable
  have hactual (e : ℤ) : 0 ≤ rawOccupation e ∧ rawOccupation e ≤ ceiling := by
    refine ⟨tsum_nonneg (fun n => by positivity), ?_⟩
    rw [← indecomposableTotal]
    exact (actualSummable e).tsum_le_tsum (fun n => occupiedBound n e)
      indecomposableSummable
  have blockHit {m k : ℕ} (sign : Bool) (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin k)) (e : ℤ) :
      hitsDiagonal (blockSum sign α β) e ↔
        hitsDiagonal α (e + (if sign then (k : ℤ) else 0)) ∨
        hitsDiagonal β (e - (if sign then (m : ℤ) else 0)) := by
    have leftval (i : Fin m) : (blockSum sign α β (Fin.castAdd k i)).val =
          (if sign then k else 0) + (α i).val := by
      cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
    have rightval (i : Fin k) : (blockSum sign α β (Fin.natAdd m i)).val =
          (if sign then 0 else m) + (β i).val := by
      cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
    constructor
    · rintro ⟨j, hj⟩
      by_cases left : j.val < m
      · left
        refine ⟨⟨j.val, left⟩, ?_⟩
        have jj : j = Fin.castAdd k ⟨j.val, left⟩ := Fin.ext rfl
        rw [jj, leftval] at hj
        cases sign <;> simp only [Bool.false_eq_true,
          ↓reduceIte, Fin.val_castAdd, Nat.cast_add, zero_add] at hj ⊢ <;> omega
      · right
        let i : Fin k := ⟨j.val - m, by omega⟩
        have jj : j = Fin.natAdd m i := Fin.ext (by simp [i]; omega)
        refine ⟨i, ?_⟩
        rw [jj, rightval] at hj
        cases sign <;> simp only [Bool.false_eq_true,
          ↓reduceIte, Fin.val_natAdd, Nat.cast_add, zero_add] at hj ⊢ <;> omega
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · refine ⟨Fin.castAdd k j, ?_⟩
        rw [leftval]
        cases sign <;> simp only [Bool.false_eq_true,
          ↓reduceIte, Fin.val_castAdd, Nat.cast_add, zero_add] at hj ⊢ <;> omega
      · refine ⟨Fin.natAdd m j, ?_⟩
        rw [rightval]
        cases sign <;> simp only [Bool.false_eq_true,
          ↓reduceIte, Fin.val_natAdd, Nat.cast_add, zero_add] at hj ⊢ <;> omega
  have skewDisjoint {m k : ℕ} (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin k)) (e : ℤ) :
      ¬(hitsDiagonal α (e + k) ∧ hitsDiagonal β (e - m)) := by
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have := i.isLt
    have := j.isLt
    have := (α i).isLt
    have := (β j).isLt
    omega
  have productUnion {A B : Type} [Finite A] [Finite B] (P : A → Prop) (Q : B → Prop) :
      Nat.card {pair : A × B // P pair.1 ∨ Q pair.2} =
        Nat.card {x : A // P x} * (Nat.card B - Nat.card {y : B // Q y}) +
          Nat.card A * Nat.card {y : B // Q y} := by
    let _ := Fintype.ofFinite A
    let _ := Fintype.ofFinite B
    let left : A × B → Prop := fun pair => P pair.1 ∧ ¬Q pair.2
    let right : A × B → Prop := fun pair => Q pair.2
    have alternate (pair : A × B) : (P pair.1 ∨ Q pair.2) ↔ (left pair ∨ right pair) := by
      dsimp [left, right]
      tauto
    have disjoint : Disjoint left right := by
      apply disjoint_iff_inf_le.mpr
      intro pair both
      exact both.1.2 both.2
    let leftEquiv : {pair : A × B // left pair} ≃
        {x : A // P x} × {y : B // ¬Q y} :=
      Equiv.subtypeProdEquivProd (p := P) (q := fun y => ¬Q y)
    let rightEquiv : {pair : A × B // right pair} ≃ A × {y : B // Q y} :=
      { toFun := fun pair => ⟨pair.val.1, pair.val.2, pair.property⟩
        invFun := fun pair => ⟨⟨pair.1, pair.2.val⟩, pair.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr (Equiv.subtypeEquivRight alternate),
      Nat.card_congr (subtypeOrEquiv left right disjoint), Nat.card_sum,
      Nat.card_congr leftEquiv, Nat.card_congr rightEquiv, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have productDisjoint {A B : Type} [Finite A] [Finite B] (P : A → Prop) (Q : B → Prop)
      (disjoint : ∀ pair : A × B, ¬(P pair.1 ∧ Q pair.2)) :
      Nat.card {pair : A × B // P pair.1 ∨ Q pair.2} =
        Nat.card {x : A // P x} * Nat.card B + Nat.card A * Nat.card {y : B // Q y} := by
    have separated : Disjoint (fun pair : A × B => P pair.1) (fun pair : A × B => Q pair.2) := by
      apply disjoint_iff_inf_le.mpr
      intro pair both
      exact disjoint pair both
    let leftEquiv : {pair : A × B // P pair.1} ≃ {x : A // P x} × B :=
      { toFun := fun pair => ⟨⟨pair.val.1, pair.property⟩, pair.val.2⟩
        invFun := fun pair => ⟨⟨pair.1.val, pair.2⟩, pair.1.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let rightEquiv : {pair : A × B // Q pair.2} ≃ A × {y : B // Q y} :=
      { toFun := fun pair => ⟨pair.val.1, pair.val.2, pair.property⟩
        invFun := fun pair => ⟨⟨pair.1, pair.2.val⟩, pair.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr (subtypeOrEquiv _ _ separated), Nat.card_sum,
      Nat.card_congr leftEquiv, Nat.card_congr rightEquiv, Nat.card_prod, Nat.card_prod]
  have finiteEvents (sign : Bool) (n : ℕ) (e : ℤ) : decomposableOccupiedCount sign n e =
      ∑ cut ∈ Finset.Ioo 0 n, if sign then
          signedOccupiedCount sign cut (e + (n - cut : ℕ)) * Nat.card (Avoider (n - cut)) +
            Nat.card (Indecomposable sign cut) * allOccupiedCount (n - cut) (e - cut)
        else
          signedOccupiedCount sign cut e *
              (Nat.card (Avoider (n - cut)) - allOccupiedCount (n - cut) e) +
            Nat.card (Indecomposable sign cut) * allOccupiedCount (n - cut) e := by
    obtain ⟨_, _, _, _, _, _, _, _, enumeration, _⟩ :=
      D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
    obtain ⟨equiv, reconstruction⟩ := enumeration sign n
    let Factors (cut : ↥(Finset.Ioo 0 n)) := Indecomposable sign cut.val × Avoider (n - cut.val)
    let event (cut : ↥(Finset.Ioo 0 n)) (pair : Factors cut) :=
      hitsDiagonal pair.1.val.val (e + (if sign then ((n - cut.val : ℕ) : ℤ) else 0)) ∨
      hitsDiagonal pair.2.val (e - (if sign then (cut.val : ℤ) else 0))
    have transported {m k : ℕ} (eq : m = k) (π : Equiv.Perm (Fin m)) :
        hitsDiagonal (eq ▸ π : Equiv.Perm (Fin k)) e ↔ hitsDiagonal π e := by
      cases eq
      rfl
    have exactEvent (π : D5.S1.Words.Patterns.Separable.ActualCardinality.ProperSigned sign n) :
        hitsDiagonal π.val.val e ↔ event (equiv π).1 (equiv π).2 := by
      have preserved := congrArg (fun π => hitsDiagonal π e) (reconstruction π).2
      rw [← preserved]
      exact (transported _ _).trans (blockHit sign _ _ e)
    let restricted : {π : D5.S1.Words.Patterns.Separable.ActualCardinality.ProperSigned sign n //
        hitsDiagonal π.val.val e} ≃ {item : Σ cut, Factors cut // event item.1 item.2} :=
      Equiv.subtypeEquiv equiv exactEvent
    let split : {item : Σ cut, Factors cut // event item.1 item.2} ≃
        Σ cut, {pair : Factors cut // event cut pair} :=
      { toFun := fun item => ⟨item.val.1, item.val.2, item.property⟩
        invFun := fun item => ⟨⟨item.1, item.2.val⟩, item.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    unfold decomposableOccupiedCount
    rw [Nat.card_congr restricted, Nat.card_congr split, Nat.card_sigma]
    rw [← Finset.sum_coe_sort (Finset.Ioo 0 n)]
    apply Finset.sum_congr rfl
    intro cut _
    cases sign with
    | false =>
      simpa only [event, Bool.false_eq_true, ↓reduceIte, add_zero, sub_zero,
        signedOccupiedCount, allOccupiedCount, Factors] using
        productUnion (fun π : Indecomposable false cut.val => hitsDiagonal π.val.val e)
          (fun π : Avoider (n - cut.val) => hitsDiagonal π.val e)
    | true =>
      simpa only [event, ↓reduceIte, signedOccupiedCount, allOccupiedCount, Factors] using
        productDisjoint
          (fun π : Indecomposable true cut.val => hitsDiagonal π.val.val (e + (n - cut.val : ℕ)))
          (fun π : Avoider (n - cut.val) => hitsDiagonal π.val (e - cut.val))
          (fun pair => skewDisjoint pair.1.val.val pair.2.val e)
  have eventPartition (sign : Bool) (n : ℕ) (e : ℤ) : allOccupiedCount n e =
      signedOccupiedCount sign n e + decomposableOccupiedCount sign n e := by
    let Event := {π : Avoider n // hitsDiagonal π.val e}
    let P (π : Event) := ¬HasProperCut sign π.val.val
    let leftEquiv : {π : Event // P π} ≃
        {π : Indecomposable sign n // hitsDiagonal π.val.val e} :=
      { toFun := fun π => ⟨⟨π.val.val, π.property⟩, π.val.property⟩
        invFun := fun π => ⟨⟨π.val.val, π.property⟩, π.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let rightEquiv : {π : Event // ¬P π} ≃
        {π : D5.S1.Words.Patterns.Separable.ActualCardinality.ProperSigned sign n //
          hitsDiagonal π.val.val e} :=
      { toFun := fun π => ⟨⟨π.val.val, Classical.not_not.mp π.property⟩, π.val.property⟩
        invFun := fun π => ⟨⟨π.val.val, π.property⟩, Classical.not_not.mpr π.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change Nat.card Event = _
    rw [← Nat.card_congr (Equiv.sumCompl P), Nat.card_sum,
      Nat.card_congr leftEquiv, Nat.card_congr rightEquiv]
    rfl
  have oppositeEvents (sign : Bool) (n : ℕ) (e : ℤ) (large : 2 ≤ n) :
      decomposableOccupiedCount sign n e = signedOccupiedCount (!sign) n e := by
    obtain ⟨_, _, _, _, _, _, _, _, signLaw⟩ :=
      D5.S1.Words.Patterns.Separable.EndpointHistoryKernel.endpoint_history_count_kernel
        (D5.S1.Words.Patterns.Separable.EndpointHistoryKernel.EndpointHistory.stop none n)
    let equiv : {π : D5.S1.Words.Patterns.Separable.ActualCardinality.ProperSigned sign n //
        hitsDiagonal π.val.val e} ≃
        {π : Indecomposable (!sign) n // hitsDiagonal π.val.val e} :=
      { toFun := fun π => ⟨⟨π.val.val, (signLaw sign large π.val.val).mpr π.val.property⟩,
          π.property⟩
        invFun := fun π => ⟨⟨π.val.val, (signLaw sign large π.val.val).mp π.val.property⟩,
          π.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Nat.card_congr equiv
  have singletonEvents (sign : Bool) (e : ℤ) :
      signedOccupiedCount sign 1 e = if e = 0 then 1 else 0 := by
    have displacement (π : Equiv.Perm (Fin 1)) : hitsDiagonal π e ↔ e = 0 := by
      constructor
      · rintro ⟨j, hj⟩
        have := j.isLt
        have := (π j).isLt
        omega
      · intro zero
        subst e
        exact ⟨0, by have := (π 0).isLt; simp only [Fin.val_zero]; omega⟩
    by_cases zero : e = 0
    · subst e
      simp only [signedOccupiedCount, ite_true]
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv
        (fun π : Indecomposable sign 1 => (displacement π.val.val).mpr rfl))]
      exact (tinyCounts sign).2
    · have empty : IsEmpty {π : Indecomposable sign 1 // hitsDiagonal π.val.val e} :=
        ⟨fun π => zero ((displacement π.val.val.val).mp π.property)⟩
      simp only [signedOccupiedCount, zero, ite_false]
      exact Nat.card_eq_zero.mpr (Or.inl empty)
  have inverseAvoids {n : ℕ} (π : Avoider n) : Avoids π.val.symm := by
    have inverseOccurrence (σ : Equiv.Perm (Fin 4))
        (occ : D5.S1.Words.Patterns.DerangementRatioNonconvergence.Contains σ π.val.symm) :
        D5.S1.Words.Patterns.DerangementRatioNonconvergence.Contains σ.symm π.val := by
      obtain ⟨f, hf⟩ := occ
      let g : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono (fun i => π.val.symm (f (σ.symm i))) (by
          intro i j hij
          apply (hf (σ.symm i) (σ.symm j)).mp
          simpa only [Equiv.apply_symm_apply] using hij)
      refine ⟨g, fun i j => ?_⟩
      change σ.symm i < σ.symm j ↔
        π.val (π.val.symm (f (σ.symm i))) < π.val (π.val.symm (f (σ.symm j)))
      simp only [Equiv.apply_symm_apply, f.lt_iff_lt]
    have patterns : D5.S1.Words.Patterns.Separable.ProperCut.pattern2413.symm =
          D5.S1.Words.Patterns.Separable.ProperCut.pattern3142 ∧
        D5.S1.Words.Patterns.Separable.ProperCut.pattern3142.symm =
          D5.S1.Words.Patterns.Separable.ProperCut.pattern2413 := by decide
    constructor
    · intro occ
      exact π.property.2 (patterns.1 ▸ inverseOccurrence _ occ)
    · intro occ
      exact π.property.1 (patterns.2 ▸ inverseOccurrence _ occ)
  have inverseProperForward {n : ℕ} (sign : Bool) (π : Avoider n) :
      HasProperCut sign π.val → HasProperCut sign π.val.symm := by
    rintro ⟨m, hm, hmn, cut⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn.le
    have hk : 0 < k := by omega
    obtain ⟨factors, reconstruction, _⟩ := (fixed_cut_factorization hm hk sign π).mp cut
    have leftval (i : Fin m) : (π.val (Fin.castAdd k i)).val =
        (if sign then k else 0) + (factors.1.val i).val := by
      rw [← reconstruction]
      cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
    have rightval (i : Fin k) : (π.val (Fin.natAdd m i)).val =
        (if sign then 0 else m) + (factors.2.val i).val := by
      rw [← reconstruction]
      cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
    have ranges (i : Fin (m+k)) : ((π.val i).val < (if sign then k else m)) ↔
          (if sign then m ≤ i.val else i.val < m) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [leftval]
        cases sign <;> simp
      · rw [rightval]
        cases sign <;> simp
    refine ⟨if sign then k else m, ?_, ?_, ?_⟩
    · cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    intro i j hi hj
    have ir := ranges (π.val.symm i)
    have jr := ranges (π.val.symm j)
    rw [Equiv.apply_symm_apply] at ir jr
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hj ir jr ⊢
    · have ip := ir.mp hi
      have jp : m ≤ (π.val.symm j).val := by
        by_contra bad
        have := jr.mpr (by omega)
        omega
      exact (show (π.val.symm i).val < (π.val.symm j).val by omega)
    · have ip := ir.mp hi
      have jp : (π.val.symm j).val < m := by
        by_contra bad
        have := jr.mpr (by omega)
        omega
      exact (show (π.val.symm j).val < (π.val.symm i).val by omega)
  let inversion {n : ℕ} (π : Avoider n) : Avoider n := ⟨π.val.symm, inverseAvoids π⟩
  have inverseProper {n : ℕ} (sign : Bool) (π : Avoider n) :
      HasProperCut sign (inversion π).val ↔ HasProperCut sign π.val := by
    constructor
    · exact inverseProperForward sign (inversion π)
    · exact inverseProperForward sign π
  have inversionInvolution {n : ℕ} : Function.Involutive (@inversion n) := by
    intro π
    apply Subtype.ext
    exact Equiv.symm_symm _
  have inverseHit {n : ℕ} (π : Equiv.Perm (Fin n)) (e : ℤ) :
      hitsDiagonal π.symm (-e) ↔ hitsDiagonal π e := by
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨π.symm j, ?_⟩
      rw [Equiv.apply_symm_apply]
      omega
    · rintro ⟨j, hj⟩
      refine ⟨π j, ?_⟩
      rw [Equiv.symm_apply_apply]
      omega
  have reflectedEvents (sign : Bool) (n : ℕ) (e : ℤ) :
      signedOccupiedCount sign n e = signedOccupiedCount sign n (-e) := by
    let inv : Avoider n ≃ Avoider n :=
      ⟨inversion, inversion, inversionInvolution, inversionInvolution⟩
    let restricted : Indecomposable sign n ≃ Indecomposable sign n :=
      Equiv.subtypeEquiv inv (fun π => (inverseProper sign π).not.symm)
    exact Nat.card_congr (Equiv.subtypeEquiv restricted (fun π => (inverseHit π.val.val e).symm))
  have actualEven (e : ℤ) : rawOccupation (-e) = rawOccupation e := by
    apply tsum_congr
    intro n
    rw [show occupiedCount (n+1) (-e) = occupiedCount (n+1) e from
      (reflectedEvents false (n+1) e).symm]
  let J (sign : Bool) (n : ℕ) (e : ℤ) : ℝ := rho ^ (n+1) * (signedOccupiedCount sign (n+1) e : ℝ)
  let A (n : ℕ) (e : ℤ) : ℝ := rho ^ (n+1) * (allOccupiedCount (n+1) e : ℝ)
  let D (sign : Bool) (n : ℕ) (e : ℤ) : ℝ :=
    rho ^ (n+1) * (decomposableOccupiedCount sign (n+1) e : ℝ)
  have allCountBound (n : ℕ) (e : ℤ) : allOccupiedCount n e ≤ Nat.card (Avoider n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have signedCountBound (sign : Bool) (n : ℕ) (e : ℤ) :
      signedOccupiedCount sign n e ≤ Nat.card (Indecomposable sign n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have sameCounts (sign : Bool) (n : ℕ) :
      Nat.card (Indecomposable sign n) = Nat.card (Indecomposable false n) := by
    obtain ⟨_, _, counts, _⟩ :=
      D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
    rw [counts, counts]
  have Ibound (n : ℕ) : 0 ≤ indecomposableWeight n ∧ indecomposableWeight n ≤ shapeWeight n := by
    constructor
    · dsimp [indecomposableWeight]; positivity
    · apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact_mod_cast (Nat.card_le_card_of_injective
        (fun π : Indecomposable false (n+1) => π.val) Subtype.val_injective)
  have Abound (n : ℕ) (e : ℤ) : 0 ≤ A n e ∧ A n e ≤ shapeWeight n := by
    constructor
    · dsimp [A]; positivity
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast allCountBound (n+1) e) (by positivity)
  have Jbound (sign : Bool) (n : ℕ) (e : ℤ) :
      0 ≤ J sign n e ∧ J sign n e ≤ indecomposableWeight n := by
    constructor
    · dsimp [J]; positivity
    · dsimp [J, indecomposableWeight]
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact_mod_cast ((signedCountBound sign (n+1) e).trans_eq (sameCounts sign (n+1)))
  have Asum (e : ℤ) : Summable (fun n => A n e) :=
    Summable.of_nonneg_of_le (fun n => (Abound n e).1) (fun n => (Abound n e).2) hsum
  have Jsum (sign : Bool) (e : ℤ) : Summable (fun n => J sign n e) :=
    Summable.of_nonneg_of_le (fun n => (Jbound sign n e).1)
      (fun n => (Jbound sign n e).2) indecomposableSummable
  have partitionW (sign : Bool) (n : ℕ) (e : ℤ) : A n e = J sign n e + D sign n e := by
    dsimp only [A, J, D]
    rw [eventPartition, Nat.cast_add, mul_add]
  have Dsum (sign : Bool) (e : ℤ) : Summable (fun n => D sign n e) := by
    apply Summable.congr ((Asum e).sub (Jsum sign e))
    intro n
    linarith [partitionW sign n e]
  have Dzero (sign : Bool) (e : ℤ) : D sign 0 e = 0 := by
    have empty : IsEmpty {π :
        D5.S1.Words.Patterns.Separable.ActualCardinality.ProperSigned sign 1 //
          hitsDiagonal π.val.val e} := ⟨fun π => by
            obtain ⟨c, hc, hb, _⟩ := π.val.property
            omega⟩
    simp [D, decomposableOccupiedCount]
  let F (sign : Bool) (e : ℤ) (i k : ℕ) : ℝ := if sign then J sign i (e+(k+1 : ℕ)) * shapeWeight k +
      indecomposableWeight i * A k (e-(i+1 : ℕ))
    else J sign i e * (shapeWeight k - A k e) + indecomposableWeight i * A k e
  have Fbound (sign : Bool) (e : ℤ) (i k : ℕ) :
      0 ≤ F sign e i k ∧ F sign e i k ≤ 2 * (shapeWeight i * shapeWeight k) := by
    have ji (x : ℤ) := (Jbound sign i x).2.trans (Ibound i).2
    have term (x : ℤ) : 0 ≤ J sign i x * shapeWeight k ∧
        J sign i x * shapeWeight k ≤ shapeWeight i * shapeWeight k :=
      ⟨mul_nonneg (Jbound sign i x).1 (tn k), mul_le_mul_of_nonneg_right (ji x) (tn k)⟩
    have termA (x : ℤ) : 0 ≤ indecomposableWeight i * A k x ∧
        indecomposableWeight i * A k x ≤ shapeWeight i * shapeWeight k :=
      ⟨mul_nonneg (Ibound i).1 (Abound k x).1,
        mul_le_mul (Ibound i).2 (Abound k x).2 (Abound k x).1 (tn i)⟩
    dsimp [F]
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · have first0 := mul_nonneg (Jbound false i e).1 (sub_nonneg.mpr (Abound k e).2)
      have firstLe := mul_le_mul_of_nonneg_left
        (show shapeWeight k - A k e ≤ shapeWeight k by linarith [(Abound k e).1])
        (Jbound false i e).1
      exact ⟨add_nonneg first0 (termA e).1, by linarith [(term e).2, (termA e).2]⟩
    · have t1 := term (e+(k+1 : ℕ))
      have t2 := termA (e-(i+1 : ℕ))
      simp only [Nat.cast_add, Nat.cast_one] at t1 t2
      exact ⟨add_nonneg t1.1 t2.1, by linarith [t1.2,t2.2]⟩
  have Fsum (sign : Bool) (e : ℤ) : Summable (fun p : ℕ × ℕ => F sign e p.1 p.2) :=
    Summable.of_nonneg_of_le (fun p => (Fbound sign e p.1 p.2).1)
      (fun p => (Fbound sign e p.1 p.2).2) (productSum.mul_left 2)
  have recurrenceW (sign : Bool) (e : ℤ) (n : ℕ) :
      D sign (n+1) e = ∑ p ∈ Finset.antidiagonal n, F sign e p.1 p.2 := by
    dsimp only [D]
    rw [finiteEvents]
    simp only [Nat.cast_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun cut _ => (cut-1, n+1-cut)) ?_ ?_ ?_ ?_
    · intro cut member
      have bounds := Finset.mem_Ioo.mp member
      apply Finset.mem_antidiagonal.mpr
      omega
    · intro c hc d hd eq
      have := congrArg Prod.fst eq
      have := Finset.mem_Ioo.mp hc
      have := Finset.mem_Ioo.mp hd
      omega
    · intro p hp
      have indices := Finset.mem_antidiagonal.mp hp
      refine ⟨p.1+1, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, ?_⟩
      apply Prod.ext <;> dsimp <;> omega
    · intro cut member
      have bounds := Finset.mem_Ioo.mp member
      have ei : cut-1+1 = cut := by omega
      have ek : n+1-cut+1 = n+1+1-cut := by omega
      have exponent : n+1+1 = cut+(n+1+1-cut) := by omega
      dsimp only [F,J,A,indecomposableWeight,shapeWeight]
      rw [ei,ek,exponent,pow_add,sameCounts]
      simp only [Nat.add_sub_cancel_left]
      cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_mul]
      · rw [Nat.cast_sub (allCountBound _ e)]
        ring
      · ring
  have weightedTransport (sign : Bool) (e : ℤ) :
      (∑' n, D sign n e) = ∑' p : ℕ × ℕ, F sign e p.1 p.2 := by
    rw [(Dsum sign e).tsum_eq_zero_add, Dzero, zero_add]
    simp_rw [recurrenceW]
    let E := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
    have sigmaSum : Summable (fun p : Σ n : ℕ, ↥(Finset.antidiagonal n) =>
        F sign e p.2.val.1 p.2.val.2) := E.summable_iff.mpr (Fsum sign e)
    rw [← E.tsum_eq (fun p : ℕ × ℕ => F sign e p.1 p.2)]
    change _ = ∑' p : Σ n : ℕ, ↥(Finset.antidiagonal n), F sign e p.2.val.1 p.2.val.2
    rw [sigmaSum.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
    congr 1
    funext n
    rw [tsum_fintype]
    exact (Finset.sum_coe_sort (Finset.antidiagonal n) (fun p => F sign e p.1 p.2)).symm
  let T (e : ℤ) := ∑' n, A n e
  let P (e : ℤ) := ∑' n, D false n e
  let B (e : ℤ) := ∑' n, J true n e
  let delta (e : ℤ) : ℝ := if e = 0 then rho else 0
  have Ctotal (e : ℤ) : (∑' n, J false n e) = rawOccupation e := rfl
  have fullPartition (e : ℤ) : T e = rawOccupation e + P e := by
    dsimp only [T,P]
    rw [← Ctotal, ← (Jsum false e).tsum_add (Dsum false e)]
    exact tsum_congr (partitionW false · e)
  have oppositeTotal (sign : Bool) (e : ℤ) :
      (∑' n, J sign n e) = delta e + ∑' n, D (!sign) n e := by
    rw [(Jsum sign e).tsum_eq_zero_add, (Dsum (!sign) e).tsum_eq_zero_add, Dzero, zero_add]
    have singleton : J sign 0 e = delta e := by
      dsimp only [J,delta]
      rw [singletonEvents]
      by_cases zero : e = 0 <;>
        simp only [zero,ite_true,ite_false,zero_add,pow_one,Nat.cast_one,Nat.cast_zero,
          mul_one,mul_zero]
    rw [singleton]
    congr 1
    apply tsum_congr
    intro n
    dsimp [J,D]
    rw [oppositeEvents (!sign) (n+1+1) e (by omega), Bool.not_not]
  have directEquation (e : ℤ) : P e = rawOccupation e * (b - T e) + ceiling * T e := by
    rw [show P e = ∑' p : ℕ × ℕ, F false e p.1 p.2 from weightedTransport false e]
    rw [(Fsum false e).tsum_prod]
    have fiber (i : ℕ) : (∑' k, F false e i k) =
        J false i e * (b - T e) + indecomposableWeight i * T e := by
      dsimp only [F]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [((hsum.sub (Asum e)).mul_left _).tsum_add ((Asum e).mul_left _),
        tsum_mul_left, tsum_mul_left, hsum.tsum_sub (Asum e),shapeTotal]
    simp_rw [fiber]
    rw [((Jsum false e).mul_right _).tsum_add (indecomposableSummable.mul_right _),
      tsum_mul_right,tsum_mul_right, Ctotal,indecomposableTotal]
  have eliminateFull (e : ℤ) : T e = 2 * rawOccupation e - 2 * loss (rawOccupation e) := by
    have equation := directEquation e
    have partition := fullPartition e
    have pos : 0 < h + rawOccupation e := by linarith only [hp,(hactual e).1]
    have constants : 1-ceiling = h ∧ 1+b = 2*h := by dsimp [ceiling,a,h]; constructor <;> ring
    have product : (h+rawOccupation e)*T e = 2*h*rawOccupation e := by
      rw [← constants.2, ← constants.1]
      nlinarith only [equation,partition]
    unfold loss
    have quotient : T e = (2*h*rawOccupation e)/(h+rawOccupation e) :=
      (eq_div_iff (ne_of_gt pos)).mpr (by nlinarith only [product])
    rw [quotient]
    field_simp
    ring
  have eliminateDirect (e : ℤ) : P e = rawOccupation e - 2 * loss (rawOccupation e) := by
    linarith only [fullPartition e, eliminateFull e]
  have eliminateSkewIndecomposable (e : ℤ) :
      B e = delta e + rawOccupation e - 2 * loss (rawOccupation e) := by
    change (∑' n, J true n e) = _
    rw [oppositeTotal]
    change delta e + P e = _
    rw [eliminateDirect]
    ring
  have skewLeftSum (e : ℤ) : Summable (fun p : ℕ × ℕ =>
      J true p.1 (e+(p.2+1 : ℕ)) * shapeWeight p.2) := by
    apply Summable.of_nonneg_of_le (fun p => mul_nonneg (Jbound true _ _).1 (tn _))
      (fun p => ?_) productSum
    exact mul_le_mul_of_nonneg_right ((Jbound true _ _).2.trans (Ibound _).2) (tn _)
  have skewRightSum (e : ℤ) : Summable (fun p : ℕ × ℕ =>
      indecomposableWeight p.1 * A p.2 (e-(p.1+1 : ℕ))) := by
    apply Summable.of_nonneg_of_le (fun p => mul_nonneg (Ibound _).1 (Abound _ _).1)
      (fun p => ?_) productSum
    exact mul_le_mul (Ibound _).2 (Abound _ _).2 (Abound _ _).1 (tn _)
  have skewEquation (e : ℤ) : rawOccupation e = delta e + (∑' n, shapeWeight n * B (e+(n+1 : ℕ))) +
      (∑' n, indecomposableWeight n * T (e-(n+1 : ℕ))) := by
    rw [← Ctotal, oppositeTotal]
    simp only [Bool.not_false]
    rw [weightedTransport]
    dsimp only [F]
    simp only [↓reduceIte]
    rw [(skewLeftSum e).tsum_add (skewRightSum e), (skewLeftSum e).tsum_prod,
      (Summable.tsum_comm (f := fun i k => J true i (e+(k+1 : ℕ)) * shapeWeight k)
        (skewLeftSum e)).symm,
      (skewRightSum e).tsum_prod]
    simp_rw [tsum_mul_right,tsum_mul_left]
    simp only [B,T,mul_comm,add_assoc]
  have leftConvolutionSum (e : ℤ) : Summable (fun n => shapeWeight n * B (e+(n+1 : ℕ))) := by
    have sum := (skewLeftSum e).prod_symm.prod
    change Summable (fun n => ∑' i, J true i (e+(n+1 : ℕ)) * shapeWeight n) at sum
    simp only [tsum_mul_right] at sum
    simpa only [B,mul_comm] using sum
  have rightConvolutionSum (e : ℤ) :
      Summable (fun n => indecomposableWeight n * T (e-(n+1 : ℕ))) := by
    simpa only [tsum_mul_left] using (skewRightSum e).prod
  let G (e : ℤ) (n : ℕ) : ℝ := shapeWeight n * B (e+(n+1 : ℕ)) +
      indecomposableWeight n * T (e-(n+1 : ℕ))
  have Gsum (e : ℤ) : Summable (G e) := (leftConvolutionSum e).add (rightConvolutionSum e)
  have skewCombined (e : ℤ) : rawOccupation e = delta e + ∑' n, G e n := by
    change rawOccupation e = delta e + ∑' n, (shapeWeight n * B (e+(n+1 : ℕ)) +
        indecomposableWeight n * T (e-(n+1 : ℕ)))
    rw [(leftConvolutionSum e).tsum_add (rightConvolutionSum e)]
    simpa only [add_assoc] using skewEquation e
  let Q (e : ℤ) (n : ℕ) : ℝ := (shapeWeight n / 2) * (delta (e+(n+1 : ℕ)) + delta (e-(n+1 : ℕ)))
  have deltaBound (e : ℤ) : 0 ≤ delta e ∧ delta e ≤ rho := by
    dsimp [delta]
    split_ifs <;> exact ⟨by positivity, by linarith only [rhop]⟩
  have deltaEven (e : ℤ) : delta (-e) = delta e := by simp [delta]
  have Qsum (e : ℤ) : Summable (Q e) := by
    apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hsum.mul_right rho)
    · dsimp [Q]
      exact mul_nonneg (div_nonneg (tn n) (by norm_num))
        (add_nonneg (deltaBound _).1 (deltaBound _).1)
    · have bound : delta (e+(n+1 : ℕ)) + delta (e-(n+1 : ℕ)) ≤ 2*rho := by
        linarith only [(deltaBound (e+(n+1 : ℕ))).2, (deltaBound (e-(n+1 : ℕ))).2]
      calc
        Q e n ≤ (shapeWeight n / 2) * (2*rho) :=
          mul_le_mul_of_nonneg_left bound (div_nonneg (tn n) (by norm_num))
        _ = shapeWeight n * rho := by ring
  have averageTerm (e : ℤ) (n : ℕ) : (G e n + G (-e) n) / 2 =
        neighborTerm n (rawOccupation (e+(n+1 : ℕ))) +
        neighborTerm n (rawOccupation (e-(n+1 : ℕ))) + Q e n := by
    have plus : -e+(n+1 : ℕ) = -(e-(n+1 : ℕ)) := by omega
    have minus : -e-(n+1 : ℕ) = -(e+(n+1 : ℕ)) := by omega
    dsimp only [G]
    rw [eliminateSkewIndecomposable,eliminateSkewIndecomposable,
      eliminateFull,eliminateFull,plus,minus,deltaEven,actualEven,actualEven]
    rw [indecomposableIdentity]
    dsimp only [neighborTerm,kernelWeight,lossWeight,Q]
    split_ifs <;> ring
  have Qtotal (e : ℤ) : (∑' n, Q e n) = forcing e - delta e := by
    by_cases zero : e = 0
    · subst e
      have terms (n : ℕ) : Q 0 n = 0 := by
        have hplus : (0 : ℤ)+(n+1 : ℕ) ≠ 0 := by omega
        have hminus : (0 : ℤ)-(n+1 : ℕ) ≠ 0 := by omega
        simp only [Q,delta,if_neg hplus,if_neg hminus,add_zero,mul_zero]
      rw [tsum_congr terms]
      simp [forcing,delta]
    · have ea : (e.natAbs : ℤ) = |e| := Int.natCast_natAbs e
      have positive : 0 < e.natAbs := Int.natAbs_pos.mpr zero
      rw [tsum_eq_single (e.natAbs-1)]
      · dsimp [Q,forcing,delta]
        rw [if_neg zero]
        have cases : e+(e.natAbs-1+1 : ℕ) = 0 ∧ e-(e.natAbs-1+1 : ℕ) ≠ 0 ∨
            e+(e.natAbs-1+1 : ℕ) ≠ 0 ∧ e-(e.natAbs-1+1 : ℕ) = 0 := by
          rcases le_total e 0 with neg | pos
          · rw [abs_of_nonpos neg] at ea
            left; constructor <;> omega
          · rw [abs_of_nonneg pos] at ea
            right; constructor <;> omega
        rcases cases with ⟨yes,no⟩ | ⟨no,yes⟩ <;>
          simp only [Nat.cast_add,Nat.cast_one] at yes no <;>
          rw [if_pos yes,if_neg no,if_neg zero] <;> ring
      · intro n different
        have hplus : e+(n+1 : ℕ) ≠ 0 := by
          intro eq
          have neg : e ≤ 0 := by omega
          rw [abs_of_nonpos neg] at ea
          apply different
          omega
        have hminus : e-(n+1 : ℕ) ≠ 0 := by
          intro eq
          have pos : 0 ≤ e := by omega
          rw [abs_of_nonneg pos] at ea
          apply different
          omega
        simp only [Q,delta,if_neg hplus,if_neg hminus,add_zero,mul_zero]
  have hequation (e : ℤ) : rawOccupation e = occupationMap rawOccupation e := by
    have reflected := skewCombined (-e)
    rw [actualEven,deltaEven] at reflected
    have original := skewCombined e
    have avgSum : Summable (fun n => (G e n + G (-e) n)/2) := ((Gsum e).add (Gsum (-e))).div_const 2
    have avgValue : (∑' n, (G e n + G (-e) n)/2) = rawOccupation e - delta e := by
      rw [tsum_div_const,(Gsum e).tsum_add (Gsum (-e))]
      linarith only [original,reflected]
    have neighborSum : Summable (fun n =>
        neighborTerm n (rawOccupation (e+(n+1 : ℕ))) +
        neighborTerm n (rawOccupation (e-(n+1 : ℕ)))) := by
      apply Summable.congr (avgSum.sub (Qsum e))
      intro n
      linarith only [averageTerm e n]
    have averageValue : (∑' n, (G e n+G (-e) n)/2) =
        ∑' n, (neighborTerm n (rawOccupation (e+(n+1 : ℕ))) +
          neighborTerm n (rawOccupation (e-(n+1 : ℕ))) + Q e n) :=
      tsum_congr (averageTerm e)
    rw [neighborSum.tsum_add (Qsum e),Qtotal,avgValue] at averageValue
    unfold occupationMap
    linarith only [averageValue]
  refine ⟨hsum, shapeTotal, hmass, actualSummable, hactual, finiteEvents,
    eventPartition, oppositeEvents, singletonEvents, reflectedEvents, hequation, ?_⟩
  intro w hw hvanish hsubsolution
  clear inverseAvoids inverseProperForward inversion inverseProper inversionInvolution inverseHit
    reflectedEvents actualEven J A D allCountBound signedCountBound sameCounts Ibound Abound Jbound
    Asum Jsum partitionW Dsum Dzero F Fbound Fsum recurrenceW weightedTransport T P B delta Ctotal
    fullPartition oppositeTotal directEquation eliminateFull eliminateDirect eliminateSkewIndecomposable
    skewLeftSum skewRightSum skewEquation leftConvolutionSum rightConvolutionSum G Gsum skewCombined
    Q deltaBound deltaEven Qsum averageTerm Qtotal
  have slopes (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ ceiling) (hy : 0 ≤ y ∧ y ≤ ceiling) (hxy : x ≤ y) :
      0 ≤ loss y - loss x ∧ loss y - loss x ≤ (y - x) / 2 ∧ (x < y → 0 < loss y - loss x) := by
    have dx : 0 < h + x := by linarith
    have dy : 0 < h + y := by linarith
    have dp : 0 < (h + x) * (h + y) := mul_pos dx dy
    have upper : (h + x) * (h + y) ≤ 1 := by
      have x1 : h + x ≤ 1 := by linarith
      have y1 : h + y ≤ 1 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr x1) (sub_nonneg.mpr y1)]
    have lower : h ^ 2 ≤ (h + x) * (h + y) := by nlinarith [mul_nonneg hx.1 hy.1]
    have coef0 : 0 ≤ 1 - h ^ 2 / ((h + x) * (h + y)) := by
      have := (div_le_one dp).2 lower
      linarith
    have coefHalf : 1 - h ^ 2 / ((h + x) * (h + y)) ≤ 1 / 2 := by
      have bound : (1 / 2 : ℝ) ≤ h ^ 2 / ((h + x) * (h + y)) := by
        apply (le_div_iff₀ dp).2
        rw [hsq]
        linarith
      linarith
    have identity : loss y - loss x = (y - x) * (1 - h ^ 2 / ((h + x) * (h + y))) := by
      unfold loss
      field_simp
      ring
    rw [identity]
    refine ⟨mul_nonneg (sub_nonneg.mpr hxy) coef0, ?_, ?_⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr coefHalf)]
    · intro strict
      have strictLower : h ^ 2 < (h + x) * (h + y) := by
        have yp : 0 < y := lt_of_le_of_lt hx.1 strict
        nlinarith [mul_pos hp yp, mul_nonneg hx.1 hy.1]
      have strictCoef : 0 < 1 - h ^ 2 / ((h + x) * (h + y)) := by
        have := (div_lt_one dp).2 strictLower
        linarith
      exact mul_pos (sub_pos.mpr strict) strictCoef
  have termMono (n : ℕ) (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ ceiling)
      (hy : 0 ≤ y ∧ y ≤ ceiling) (hxy : x ≤ y) :
      neighborTerm n x ≤ neighborTerm n y := by
    obtain ⟨_, bound, _⟩ := slopes x y hx hy hxy
    unfold neighborTerm
    nlinarith [mul_nonneg (rn n) (by linarith : 0 ≤ (y - x) / 2 - (loss y - loss x)),
      mul_nonneg (by linarith [kr n] : 0 ≤ kernelWeight n - lossWeight n / 2) (sub_nonneg.mpr hxy)]
  have termBound (n : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ ceiling) :
      0 ≤ neighborTerm n x ∧ neighborTerm n x ≤ kernelWeight n * ceiling := by
    have zero : neighborTerm n 0 = 0 := by simp [neighborTerm, loss]
    have positive := zero ▸ termMono n 0 x ⟨le_rfl, hc.le⟩ hx hx.1
    have lx : 0 ≤ loss x := by exact div_nonneg (sq_nonneg x) (by linarith)
    constructor
    · exact positive
    · unfold neighborTerm
      nlinarith [mul_nonneg (rn n) lx, mul_nonneg (kn n) (sub_nonneg.mpr hx.2)]
  have mapSum (u : ℤ → ℝ) (hu : ∀ e, 0 ≤ u e ∧ u e ≤ ceiling) (e : ℤ) :
      Summable (fun n : ℕ => neighborTerm n (u (e + (n + 1 : ℕ))) +
        neighborTerm n (u (e - (n + 1 : ℕ)))) := by
    apply Summable.of_nonneg_of_le
      (fun n => add_nonneg (termBound n _ (hu _)).1 (termBound n _ (hu _)).1)
      (fun n => ?_) (ksum.mul_right (2 * ceiling))
    nlinarith [(termBound n _ (hu (e + (n + 1 : ℕ)))).2, (termBound n _ (hu (e - (n + 1 : ℕ)))).2]
  by_contra fails
  push Not at fails
  obtain ⟨start, hstart⟩ := fails
  let threshold := w start - rawOccupation start
  have thpos : 0 < threshold := sub_pos.mpr hstart
  let core : Set ℤ := {e | threshold ≤ w e}
  have coreFinite : core.Finite := hvanish threshold thpos
  have startCore : start ∈ core := by
    change w start - rawOccupation start ≤ w start
    linarith [(hactual start).1]
  obtain ⟨peak, hpeakCore, hpeak⟩ := Set.exists_max_image core
    (fun e => w e - rawOccupation e) coreFinite ⟨start, startCore⟩
  let maximum := w peak - rawOccupation peak
  have maxPos : 0 < maximum := lt_of_lt_of_le thpos (hpeak start startCore)
  have maxBound (e : ℤ) : w e - rawOccupation e ≤ maximum := by
    by_cases he : e ∈ core
    · exact hpeak e he
    · have below : w e < threshold := lt_of_not_ge he
      linarith [(hactual e).1, hpeak start startCore]
  have step (n : ℕ) (e : ℤ) : neighborTerm n (w e) - neighborTerm n (rawOccupation e) ≤
        kernelWeight n * maximum ∧
      (n = 0 → neighborTerm n (w e) - neighborTerm n (rawOccupation e) <
        kernelWeight n * maximum) := by
    by_cases order : w e ≤ rawOccupation e
    · have mono := termMono n _ _ (hw e) (hactual e) order
      have bound : 0 ≤ kernelWeight n * maximum := mul_nonneg (kn n) maxPos.le
      refine ⟨by linarith, ?_⟩
      intro nz
      subst n
      have strict := mul_pos kzero maxPos
      linarith
    · have strict : rawOccupation e < w e := lt_of_not_ge order
      obtain ⟨nonneg, _, positive⟩ := slopes _ _ (hactual e) (hw e) strict.le
      have prod : 0 ≤ lossWeight n * (loss (w e) - loss (rawOccupation e)) :=
        mul_nonneg (rn n) nonneg
      have bound := mul_le_mul_of_nonneg_left (maxBound e) (kn n)
      constructor
      · unfold neighborTerm
        nlinarith
      · intro nz
        subst n
        have lossPos := mul_pos rzero (positive strict)
        unfold neighborTerm
        nlinarith
  let difference (n : ℕ) := (neighborTerm n (w (peak + (n + 1 : ℕ))) +
      neighborTerm n (w (peak - (n + 1 : ℕ)))) -
    (neighborTerm n (rawOccupation (peak + (n + 1 : ℕ))) +
      neighborTerm n (rawOccupation (peak - (n + 1 : ℕ))))
  have differences : Summable difference := (mapSum w hw peak).sub
    (mapSum rawOccupation hactual peak)
  have totalStrict : (∑' n, difference n) < ∑' n, kernelWeight n * (2 * maximum) := by
    refine Summable.tsum_lt_tsum (i := 0) ?_ ?_ differences (ksum.mul_right (2 * maximum))
    · intro n
      dsimp only [difference]
      linarith [(step n (peak + (n + 1 : ℕ))).1, (step n (peak - (n + 1 : ℕ))).1]
    · dsimp only [difference]
      linarith [(step 0 (peak + (0 + 1 : ℕ))).2 rfl, (step 0 (peak - (0 + 1 : ℕ))).1]
  have totalValue : (∑' n, kernelWeight n * (2 * maximum)) = maximum := by
    rw [tsum_mul_right, hmass]
    ring
  have contradictionBound : maximum ≤ ∑' n, difference n := by
    have sub := hsubsolution peak
    have eq := hequation peak
    unfold occupationMap at sub eq
    simp only [Nat.cast_add, Nat.cast_one] at sub eq
    rw [Summable.tsum_sub (mapSum w hw peak) (mapSum rawOccupation hactual peak)]
    dsimp [maximum]
    linarith
  linarith
#print axioms actual_occupation_subsolution_comparison
end D5.S1.Words.Patterns.Separable.OccupiedComparison
