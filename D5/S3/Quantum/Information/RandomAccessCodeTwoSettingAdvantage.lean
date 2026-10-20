/- GID: D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two settings give a strict quantum advantage in every random access code. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Norm
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.UnitaryGroup

open scoped BigOperators Matrix

noncomputable section

namespace D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage

def deterministicValue (n d : ℕ) (E : (Fin n → Fin d) → Fin d)
    (D : Fin d → Fin n → Fin d) : ℝ :=
  (1 / ((n : ℝ) * (d : ℝ) ^ n)) *
    ∑ x, ∑ j, if D (E x) j = x j then 1 else 0

structure ClassicalStrategy (n d : ℕ) where
  Λ : Type
  finite : Fintype Λ
  weight : Λ → ℝ
  nonneg : ∀ l, 0 ≤ weight l
  total : @Finset.sum Λ ℝ _ (@Finset.univ Λ finite) weight = 1
  encode : Λ → (Fin n → Fin d) → Fin d
  decode : Λ → Fin d → Fin n → Fin d

attribute [instance] ClassicalStrategy.finite

def classicalValue {n d : ℕ} (S : ClassicalStrategy n d) : ℝ :=
  ∑ l, S.weight l * deterministicValue n d (S.encode l) (S.decode l)

def quantumValue (n d : ℕ) (ψ : (Fin n → Fin d) → Fin d → ℂ)
    (U : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (s : Fin n → Fin 2) : ℝ :=
  (1 / ((n : ℝ) * (d : ℝ) ^ n)) *
    ∑ x, ∑ j, ‖star (fun k => U (s j) k (x j)) ⬝ᵥ ψ x‖ ^ 2

def claim : Prop :=
  ∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
    ∃ (ψ : (Fin n → Fin d) → Fin d → ℂ)
      (U : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (s : Fin n → Fin 2),
      (∀ x, star (ψ x) ⬝ᵥ ψ x = 1) ∧
      (∀ i, U i ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
      ∀ S : ClassicalStrategy n d, classicalValue S < quantumValue n d ψ U s

private def columnScore {d : ℕ} (v : Fin d → ℕ) (c : Fin d → Fin d)
    (b : Fin d) : ℕ := Finset.univ.sup (fun r => v r + if c r = b then 1 else 0)

private theorem column_exchange {d : ℕ} (v : Fin d → ℕ) (c : Fin d → Fin d)
    (r b : Fin d) (hb : ∀ i, c i ≠ b) :
    ∑ t, columnScore v c t ≤ ∑ t, columnScore v (Function.update c r b) t := by
  classical
  let a := c r
  have hab : a ≠ b := hb r
  let c' := Function.update c r b
  have same (t : Fin d) (hta : t ≠ a) (htb : t ≠ b) :
      columnScore v c t = columnScore v c' t := by
    unfold columnScore
    apply congrArg Finset.univ.sup
    funext i
    by_cases hi : i = r
    · subst i; simp [c', a, Ne.symm hta, Ne.symm htb]
    · simp [c', Function.update_of_ne hi]
  have b0 : columnScore v c b = Finset.univ.sup v := by
    simp only [columnScore, if_neg (hb _), add_zero]
  have bmono : columnScore v c b ≤ columnScore v c' b := by
    rw [b0]
    exact Finset.sup_mono_fun (fun i _ => Nat.le_add_right _ _)
  have apair : columnScore v c a + columnScore v c b ≤
      columnScore v c' a + columnScore v c' b := by
    by_cases ha : columnScore v c a ≤ columnScore v c' a
    · omega
    · have vr : v r ≤ columnScore v c' a := by
        simpa [c', columnScore, hab.symm] using
          (Finset.le_sup (f := fun i => v i + if c' i = a then 1 else 0) (Finset.mem_univ r))
      have aupper : columnScore v c a ≤ v r + 1 := by
        letI : Nonempty (Fin d) := ⟨r⟩
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
          (fun i => v i + if c i = a then 1 else 0)
        change columnScore v c a = _ at hi
        by_cases hir : i = r
        · subst i; simpa [a] using hi.le
        · have h := Finset.le_sup (f := fun i => v i + if c' i = a then 1 else 0)
            (Finset.mem_univ i)
          change v i + (if c' i = a then 1 else 0) ≤ columnScore v c' a at h
          rw [show c' i = c i from Function.update_of_ne hir _ _] at h
          omega
      have base : Finset.univ.sup v ≤ v r := by
        apply Finset.sup_le
        intro i _
        have h : v i ≤ columnScore v c' a :=
          (Nat.le_add_right _ _).trans
            (Finset.le_sup (f := fun i => v i + if c' i = a then 1 else 0) (Finset.mem_univ i))
        omega
      have gain : v r + 1 ≤ columnScore v c' b := by
        simpa [c', columnScore] using
          (Finset.le_sup (f := fun i => v i + if c' i = b then 1 else 0) (Finset.mem_univ r))
      rw [b0] at *
      omega
  have decomp (f : Fin d → ℕ) :
      ∑ t, f t = f a + f b + ∑ t ∈ (Finset.univ.erase a).erase b, f t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
    omega
  rw [decomp, decomp]
  apply Nat.add_le_add apair
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro t ht
  exact same t (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    (Finset.mem_erase.mp ht).1

private def matchCount {n d : ℕ} (D : Fin d → Fin n → Fin d)
    (x : Fin n → Fin d) (r : Fin d) : ℕ :=
  ∑ j, if D r j = x j then 1 else 0

private def optimum {n d : ℕ} (D : Fin d → Fin n → Fin d) : ℕ :=
  ∑ x, Finset.univ.sup (matchCount D x)

private def missing {n d : ℕ} (D : Fin d → Fin n → Fin d) : ℕ :=
  ∑ j : Fin n, (d - (Finset.univ.image (fun r => D r j)).card)

private def exchange {n d : ℕ} (D : Fin d → Fin n → Fin d)
    (j : Fin n) (r b : Fin d) : Fin d → Fin n → Fin d :=
  fun i k => if k = j then Function.update (fun i => D i j) r b i else D i k

private theorem exchange_optimum {n d : ℕ} (D : Fin d → Fin n → Fin d)
    (j : Fin n) (r b : Fin d) (hb : ∀ i, D i j ≠ b) :
    optimum D ≤ optimum (exchange D j r b) := by
  classical
  let e := Equiv.funSplitAt j (Fin d)
  have split (A : Fin d → Fin n → Fin d) : optimum A =
      ∑ z : {k : Fin n // k ≠ j} → Fin d,
        ∑ t, columnScore (fun i => ∑ k : {k : Fin n // k ≠ j},
          if A i k = z k then 1 else 0) (fun i => A i j) t := by
    unfold optimum
    rw [← Equiv.sum_comp e.symm]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    funext i
    change matchCount A (e.symm (t, z)) i = _
    rw [matchCount, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have hrest : (∑ k ∈ Finset.univ.erase j,
        if A i k = e.symm (t,z) k then 1 else 0) =
        ∑ k : {k : Fin n // k ≠ j}, if A i k = z k then 1 else 0 := by
      rw [Finset.sum_subtype (p := fun k : Fin n => k ≠ j)
        (Finset.univ.erase j) (by intro k; simp)]
      apply Finset.sum_congr rfl
      intro k _
      have he : e.symm (t,z) k = z k :=
        congrFun (congrArg Prod.snd (e.apply_symm_apply (t,z))) k
      rw [he]
    rw [hrest]
    have he : e.symm (t,z) j = t :=
      congrArg Prod.fst (e.apply_symm_apply (t,z))
    rw [he]
  rw [split, split]
  apply Finset.sum_le_sum
  intro z _
  have h := column_exchange (fun i => ∑ k : {k : Fin n // k ≠ j},
    if D i k = z k then 1 else 0) (fun i => D i j) r b hb
  convert h using 1
  congr 1
  funext t
  congr 1
  · funext i
    apply Finset.sum_congr rfl
    intro k _
    rw [exchange, if_neg k.property]
  · funext i
    simp [exchange]

private theorem exchange_missing {n d : ℕ} (D : Fin d → Fin n → Fin d)
    (j : Fin n) (r r' b : Fin d) (hrr : r ≠ r') (heq : D r j = D r' j)
    (hb : ∀ i, D i j ≠ b) :
    missing (exchange D j r b) < missing D := by
  classical
  let S := Finset.univ.image (fun i => D i j)
  have hS : b ∉ S := by simpa [S] using hb
  have him : Finset.univ.image (fun i => exchange D j r b i j) = insert b S := by
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, S]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hir : i = r
      · subst i; left; simpa [exchange] using hi.symm
      · right; exact ⟨i, by simpa [exchange, Function.update_of_ne hir] using hi⟩
    · rintro (rfl | ⟨i, hi⟩)
      · exact ⟨r, by simp [exchange]⟩
      · by_cases hir : i = r
        · subst i
          exact ⟨r', by simpa [exchange, Function.update_of_ne hrr.symm, ← heq] using hi⟩
        · exact ⟨i, by simpa [exchange, Function.update_of_ne hir] using hi⟩
  have hc : S.card < d := by
    have hsub : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, by intro h; have := hS; simp [h] at this⟩
    simpa using Finset.card_lt_card hsub
  unfold missing
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hother : (∑ k ∈ Finset.univ.erase j,
      (d - (Finset.univ.image (fun i => exchange D j r b i k)).card)) =
      ∑ k ∈ Finset.univ.erase j, (d - (Finset.univ.image (fun i => D i k)).card) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [exchange, if_neg (Finset.mem_erase.mp hk).1]
  rw [hother, him, Finset.card_insert_of_notMem hS]
  change _ + (d - (S.card + 1)) < _ + (d - S.card)
  omega

private theorem permute_decoder {n d : ℕ} (D : Fin d → Fin n → Fin d) :
    ∃ A : Fin d → Fin n → Fin d, (∀ j, Function.Bijective (fun r => A r j)) ∧
      optimum D ≤ optimum A := by
  classical
  suffices ∀ m, ∀ D : Fin d → Fin n → Fin d, missing D = m →
      ∃ A : Fin d → Fin n → Fin d, (∀ j, Function.Bijective (fun r => A r j)) ∧
        optimum D ≤ optimum A from this _ D rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro D hm
    by_cases h : ∀ j, Function.Injective (fun r => D r j)
    · exact ⟨D, fun j => ⟨h j, (Finite.injective_iff_surjective).mp (h j)⟩, le_rfl⟩
    · push_neg at h
      obtain ⟨j, hj⟩ := h
      obtain ⟨r, r', heq, hrr⟩ : ∃ r r', D r j = D r' j ∧ r ≠ r' := by
        simpa [Function.Injective] using hj
      have hn : ¬ Function.Surjective (fun r => D r j) := by
        exact fun hs => hj ((Finite.injective_iff_surjective).mpr hs)
      obtain ⟨b, hb⟩ : ∃ b, ∀ i, D i j ≠ b := by simpa [Function.Surjective] using hn
      obtain ⟨A, hA, hle⟩ := ih (missing (exchange D j r b))
        (by simpa [← hm] using exchange_missing D j r r' b hrr heq hb)
        (exchange D j r b) rfl
      exact ⟨A, hA, (exchange_optimum D j r b hb).trans hle⟩

private def counts {n d : ℕ} (x : Fin n → Fin d) (r : Fin d) : ℕ :=
  (Finset.univ.filter (fun j => x j = r)).card

private def C (n d : ℕ) : ℝ :=
  (1 / ((n : ℝ) * (d : ℝ) ^ n)) * ∑ x : Fin n → Fin d, ((Finset.univ.sup (counts x) : ℕ) : ℝ)

private theorem permutation_optimum {n d : ℕ} (D : Fin d → Fin n → Fin d)
    (h : ∀ j, Function.Bijective (fun r => D r j)) :
    optimum D = ∑ x : Fin n → Fin d, Finset.univ.sup (counts x) := by
  classical
  let e := Equiv.piCongrRight (fun j => Equiv.ofBijective (fun r => D r j) (h j))
  unfold optimum
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg Finset.univ.sup
  funext r
  simp only [matchCount, counts, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  change (if D r j = D (x j) j then 1 else 0) = if x j = r then 1 else 0
  simp only [(h j).injective.eq_iff, eq_comm]

private theorem deterministic_bound {n d : ℕ}
    (E : (Fin n → Fin d) → Fin d) (D : Fin d → Fin n → Fin d) :
    deterministicValue n d E D ≤ C n d := by
  classical
  obtain ⟨A, hA, hle⟩ := permute_decoder D
  rw [permutation_optimum A hA] at hle
  have hpoint : (∑ x, ∑ j, if D (E x) j = x j then (1 : ℕ) else 0) ≤
      ∑ x : Fin n → Fin d, Finset.univ.sup (counts x) :=
    (Finset.sum_le_sum (fun x _ =>
      Finset.le_sup (f := matchCount D x) (Finset.mem_univ (E x)))).trans hle
  unfold deterministicValue C
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast hpoint

private theorem classical_bound {n d : ℕ} (S : ClassicalStrategy n d) :
    classicalValue S ≤ C n d := by
  calc
    classicalValue S ≤ ∑ l, S.weight l * C n d :=
      Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left
        (deterministic_bound (S.encode l) (S.decode l)) (S.nonneg l))
    _ = C n d := by rw [← Finset.sum_mul, S.total, one_mul]

private def payoff {d : ℕ} (N : Fin d → ℕ) (f v : Fin d → ℝ) : ℝ :=
  (∑ i, (N i : ℝ) * v i ^ 2) + (∑ i, f i * v i) ^ 2

private def mass {d : ℕ} (N : Fin d → ℕ) (f : Fin d → ℝ) : ℝ :=
  ∑ i, if N i = Finset.univ.sup N then f i ^ 2 else 0

private theorem baseline_vector {d : ℕ} [Nonempty (Fin d)]
    (N : Fin d → ℕ) (f : Fin d → ℝ) :
    ∃ v : Fin d → ℝ, (∑ i, v i ^ 2) = 1 ∧
      payoff N f v = ((Finset.univ.sup N : ℕ) : ℝ) + mass N f := by
  classical
  have hn (i : Fin d) : 0 ≤ if N i = Finset.univ.sup N then f i ^ 2 else 0 := by
    split_ifs <;> positivity
  have hmass : 0 ≤ mass N f := Finset.sum_nonneg (fun i _ => hn i)
  by_cases hz : mass N f = 0
  · obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty N
    have hfa : f a = 0 := by
      have h := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ a)
      rw [← ha, if_pos rfl] at h
      change f a ^ 2 ≤ mass N f at h
      rw [hz] at h
      nlinarith [sq_nonneg (f a)]
    refine ⟨fun i => if i = a then 1 else 0, by simp, ?_⟩
    simp [payoff, ha, hz, hfa, mul_ite]
  · have hp : 0 < mass N f := lt_of_le_of_ne hmass (Ne.symm hz)
    let v : Fin d → ℝ := fun i =>
      (if N i = Finset.univ.sup N then f i else 0) / Real.sqrt (mass N f)
    have hs : Real.sqrt (mass N f) ^ 2 = mass N f := Real.sq_sqrt hmass
    have hv : (∑ i, v i ^ 2) = 1 := by
      calc
        (∑ i, v i ^ 2) = mass N f / mass N f := by
          simp only [v, div_pow, ← Finset.sum_div, hs]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp
        _ = 1 := div_self hp.ne'
    have hw : (∑ i, (N i : ℝ) * v i ^ 2) = ((Finset.univ.sup N : ℕ) : ℝ) * ∑ i, v i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : N i = Finset.univ.sup N
      · rw [hi]
      · simp [v, hi]
    have hf : (∑ i, f i * v i) = mass N f / Real.sqrt (mass N f) := by
      simp only [v, ← mul_div_assoc, ← Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp [pow_two]
    refine ⟨v, hv, ?_⟩
    rw [payoff, hw, hv, hf, div_pow, hs, mul_one]
    field_simp

private theorem increment_peak {d : ℕ} [Nonempty (Fin d)]
    (N : Fin d → ℕ) (b : Fin d) :
    Finset.univ.sup (fun i => N i + if i = b then 1 else 0) =
      Finset.univ.sup N + if N b = Finset.univ.sup N then 1 else 0 := by
  classical
  have hle (i : Fin d) := Finset.le_sup (f := N) (Finset.mem_univ i)
  by_cases hb : N b = Finset.univ.sup N
  · rw [if_pos hb]
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      have := hle i
      split_ifs <;> omega
    · have h := Finset.le_sup (f := fun i => N i + if i = b then 1 else 0) (Finset.mem_univ b)
      simpa [hb] using h
  · rw [if_neg hb, add_zero]
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      by_cases hi : i = b
      · subst i; simp only [ite_true]; have := hle b; omega
      · simp only [if_neg hi, add_zero]; exact hle i
    · obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty N
      have h := Finset.le_sup (f := fun i => N i + if i = b then 1 else 0) (Finset.mem_univ a)
      omega

private def block {d : ℕ} (a b : Fin d) (i j : Fin d) : ℝ :=
  if j = a then (if i = a then 3 / 5 else 0) + (if i = b then 4 / 5 else 0)
  else if j = b then (if i = a then 4 / 5 else 0) + (if i = b then -(3 / 5) else 0)
  else if i = j then 1 else 0

private theorem block_dot {d : ℕ} (a b : Fin d) (v : Fin d → ℝ) (j : Fin d) :
    (∑ i, block a b i j * v i) =
      if j = a then 3 / 5 * v a + 4 / 5 * v b
      else if j = b then 4 / 5 * v a - 3 / 5 * v b else v j := by
  classical
  by_cases hja : j = a
  · simp [block, hja, add_mul, ite_mul, Finset.sum_add_distrib]
  · by_cases hjb : j = b
    · simp [block, hja, hjb, add_mul, ite_mul, Finset.sum_add_distrib, sub_eq_add_neg]
    · simp [block, hja, hjb, ite_mul]

private theorem block_symm {d : ℕ} (a b : Fin d) (hab : a ≠ b) (i j : Fin d) :
    block a b i j = block a b j i := by
  classical
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp only [block, hia, hib, hja, hjb, ite_true, ite_false, eq_comm] <;>
    grind

private theorem block_orthogonal {d : ℕ} (a b : Fin d) (hab : a ≠ b) (i j : Fin d) :
    (∑ k, block a b k i * block a b k j) = if i = j then 1 else 0 := by
  rw [block_dot]
  classical
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp_all [block, eq_comm] <;> norm_num

private theorem baseline_sum {d : ℕ} [Nonempty (Fin d)] (N : Fin d → ℕ)
    (a b : Fin d) (hab : a ≠ b) :
    (∑ t, (((Finset.univ.sup N : ℕ) : ℝ) + mass N (fun i => block a b i t))) =
      ∑ t, ((Finset.univ.sup (fun i => N i + if i = t then 1 else 0) : ℕ) : ℝ) := by
  classical
  simp only [increment_peak, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_add_distrib]
  congr 1
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : N i = Finset.univ.sup N
  · simp only [hi, if_pos, ← pow_two, Finset.sum_ite_irrel]
    simpa only [block_symm a b hab, pow_two, ite_true] using block_orthogonal a b hab i i
  · simp [hi]

private def prefixCounts {n d : ℕ} (j : Fin n) (x : Fin n → Fin d) (i : Fin d) : ℕ :=
  ∑ k ∈ Finset.univ.erase j, if x k = i then 1 else 0

private theorem counts_prefix {n d : ℕ} (j : Fin n) (x : Fin n → Fin d) :
    counts x = fun i => prefixCounts j x i + if i = x j then 1 else 0 := by
  classical
  funext i
  rw [counts, Finset.card_filter, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  simp only [prefixCounts, eq_comm]

private theorem split_sum {n d : ℕ} {R : Type*} [AddCommMonoid R]
    (j : Fin n) (f : (Fin n → Fin d) → R) :
    (∑ x, f x) = ∑ z : {k : Fin n // k ≠ j} → Fin d,
      ∑ t, f ((Equiv.funSplitAt j (Fin d)).symm (t,z)) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt j (Fin d)).symm, Fintype.sum_prod_type,
    Finset.sum_comm]

private theorem prefix_fiber {n d : ℕ} (j : Fin n)
    (z : {k : Fin n // k ≠ j} → Fin d) (a t : Fin d) :
    prefixCounts j ((Equiv.funSplitAt j (Fin d)).symm (t,z)) =
      prefixCounts j ((Equiv.funSplitAt j (Fin d)).symm (a,z)) := by
  classical
  let e := Equiv.funSplitAt j (Fin d)
  funext i
  apply Finset.sum_congr rfl
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  have ht : e.symm (t,z) k = z ⟨k,hkj⟩ :=
    congrFun (congrArg Prod.snd (e.apply_symm_apply (t,z))) ⟨k,hkj⟩
  have ha : e.symm (a,z) k = z ⟨k,hkj⟩ :=
    congrFun (congrArg Prod.snd (e.apply_symm_apply (a,z))) ⟨k,hkj⟩
  rw [ht, ha]

private def measurements {d : ℕ} (a b : Fin d) :
    Fin 2 → Matrix (Fin d) (Fin d) ℂ :=
  fun t => if t = 0 then 1 else fun i j => (block a b i j : ℂ)

private theorem measurements_unitary {d : ℕ} (a b : Fin d) (hab : a ≠ b) (t : Fin 2) :
    measurements a b t ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  classical
  by_cases ht : t = 0
  · simp [measurements, ht]
  · apply Matrix.mem_unitaryGroup_iff'.mpr
    ext i j
    change (∑ k, star (measurements a b t k i) * measurements a b t k j) =
      if i = j then (1 : ℂ) else 0
    have hm (k l : Fin d) : measurements a b t k l = (block a b k l : ℂ) := by
      simp [measurements, ht]
    simp only [hm, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum]
    rw [block_orthogonal a b hab]
    split_ifs <;> simp

private theorem real_born {d : ℕ} (f v : Fin d → ℝ) :
    ‖star (fun i => (f i : ℂ)) ⬝ᵥ (fun i => (v i : ℂ))‖ ^ 2 =
      (∑ i, f i * v i) ^ 2 := by
  have hdot : star (fun i => (f i : ℂ)) ⬝ᵥ (fun i => (v i : ℂ)) =
      ((f ⬝ᵥ v : ℝ) : ℂ) := by
    simpa only [Function.comp_def, Complex.ofRealHom_eq_coe, Pi.star_def,
      Complex.star_def, Complex.conj_ofReal] using (Complex.ofRealHom.map_dotProduct f v).symm
  rw [hdot]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, dotProduct]

private theorem real_unit {d : ℕ} (v : Fin d → ℝ) (hv : (∑ i, v i ^ 2) = 1) :
    star (fun i => (v i : ℂ)) ⬝ᵥ (fun i => (v i : ℂ)) = 1 := by
  calc
    _ = ((v ⬝ᵥ v : ℝ) : ℂ) := by
      simpa only [Function.comp_def, Complex.ofRealHom_eq_coe, Pi.star_def,
        Complex.star_def, Complex.conj_ofReal] using (Complex.ofRealHom.map_dotProduct v v).symm
    _ = 1 := by simp only [dotProduct, ← pow_two, hv, Complex.ofReal_one]

private theorem quantum_payoff {n d : ℕ} (j : Fin n) (a b : Fin d)
    (x : Fin n → Fin d) (v : Fin d → ℝ) :
    (∑ k, ‖star (fun i => measurements a b (if k = j then 1 else 0) i (x k)) ⬝ᵥ
      (fun i => (v i : ℂ))‖ ^ 2) = payoff (prefixCounts j x) (fun i => block a b i (x j)) v := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hlast : ‖star (fun i => measurements a b (if j = j then 1 else 0) i (x j)) ⬝ᵥ
      (fun i => (v i : ℂ))‖ ^ 2 = (∑ i, block a b i (x j) * v i) ^ 2 := by
    simpa [measurements] using real_born (fun i => block a b i (x j)) v
  rw [hlast, payoff]
  congr 1
  have hrest : (∑ k ∈ Finset.univ.erase j,
      ‖star (fun i => measurements a b (if k = j then 1 else 0) i (x k)) ⬝ᵥ
        (fun i => (v i : ℂ))‖ ^ 2) = ∑ k ∈ Finset.univ.erase j, v (x k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    simp [hkj, measurements, dotProduct, Matrix.one_apply, Pi.star_apply, ite_mul,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hrest]
  simp only [prefixCounts, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

private theorem baseline_total {n d : ℕ} [Nonempty (Fin d)] (j : Fin n)
    (a b : Fin d) (hab : a ≠ b) :
    (∑ x : Fin n → Fin d, (((Finset.univ.sup (prefixCounts j x) : ℕ) : ℝ) +
      mass (prefixCounts j x) (fun i => block a b i (x j)))) =
      ∑ x : Fin n → Fin d, ((Finset.univ.sup (counts x) : ℕ) : ℝ) := by
  classical
  rw [split_sum j, split_sum j]
  apply Finset.sum_congr rfl
  intro z _
  let e := Equiv.funSplitAt j (Fin d)
  let N := prefixCounts j (e.symm (a,z))
  have hp (t : Fin d) : prefixCounts j (e.symm (t,z)) = N := prefix_fiber j z a t
  have ht (t : Fin d) : e.symm (t,z) j = t :=
    congrArg Prod.fst (e.apply_symm_apply (t,z))
  calc
    _ = ∑ t, (((Finset.univ.sup N : ℕ) : ℝ) + mass N (fun i => block a b i t)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hp, ht]
    _ = ∑ t, ((Finset.univ.sup (fun i => N i + if i = t then 1 else 0) : ℕ) : ℝ) :=
      baseline_sum N a b hab
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [counts_prefix j, hp, ht]

private theorem constant_improvement {n d : ℕ} (hn : 2 ≤ n) (j : Fin n)
    (a b : Fin d) (hab : a ≠ b) :
    ∃ v : Fin d → ℝ, (∑ i, v i ^ 2) = 1 ∧
      ((Finset.univ.sup (prefixCounts j (fun _ => a)) : ℕ) : ℝ) +
        mass (prefixCounts j (fun _ => a)) (fun i => block a b i a) <
        payoff (prefixCounts j (fun _ => a)) (fun i => block a b i a) v := by
  classical
  let N := prefixCounts j (fun _ => a)
  have hN (i : Fin d) : N i = if i = a then n - 1 else 0 := by
    simp [N, prefixCounts, eq_comm, Finset.card_erase_of_mem (Finset.mem_univ j)]
  have hn0 : 1 ≤ n := by omega
  have hnp : 0 < n - 1 := by omega
  have hm : Finset.univ.sup N = n - 1 := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      rw [hN]
      split_ifs <;> omega
    · simpa [hN] using Finset.le_sup (f := N) (Finset.mem_univ a)
  have hmass : mass N (fun i => block a b i a) = (3 / 5 : ℝ) ^ 2 := by
    unfold mass
    rw [hm]
    have he (i : Fin d) : (N i = n - 1) ↔ i = a := by
      rw [hN]; split_ifs <;> omega
    simp only [he]
    simp [block, hab, hab.symm]
  let q : ℝ := 4 * (n : ℝ) ^ 2 + 1
  have hq : 0 < q := by dsimp [q]; positivity
  let u : Fin d → ℝ := fun i => if i = a then 2 * n else if i = b then 1 else 0
  have hu : (∑ i, u i ^ 2) = q := by
    have he (i : Fin d) : u i ^ 2 =
        (if i = a then 4 * (n : ℝ) ^ 2 else 0) + (if i = b then 1 else 0) := by
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        simp_all [u] <;> ring
    simp only [he, Finset.sum_add_distrib]
    simp [q]
  let v : Fin d → ℝ := fun i => u i / Real.sqrt q
  refine ⟨v, ?_, ?_⟩
  · simp only [v, div_pow, ← Finset.sum_div, Real.sq_sqrt hq.le, hu, div_self hq.ne']
  have hscore : payoff N (fun i => block a b i a) v =
      ((n : ℝ) - 1) * (2 * n / Real.sqrt q) ^ 2 +
        (3 / 5 * (2 * n / Real.sqrt q) + 4 / 5 * (1 / Real.sqrt q)) ^ 2 := by
    rw [payoff, block_dot]
    simp only [ite_true, hN, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
    simp [v, u, hab, hab.symm, Nat.cast_sub hn0]
  change ((Finset.univ.sup N : ℕ) : ℝ) + mass N (fun i => block a b i a) < _
  rw [hm, hmass, hscore, Nat.cast_sub hn0, Nat.cast_one]
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hr : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hid : ((n : ℝ) - 1) * (2 * n / Real.sqrt q) ^ 2 +
      (3 / 5 * (2 * n / Real.sqrt q) + 4 / 5 * (1 / Real.sqrt q)) ^ 2 -
      ((n : ℝ) - 1 + (3 / 5) ^ 2) = (23 * n + 32) / (25 * q) := by
    field_simp
    rw [hs]
    dsimp [q]
    ring
  have hg : 0 < (23 * (n : ℝ) + 32) / (25 * q) := by positivity
  linarith

theorem result : claim := by
  classical
  intro n d hn hd
  let a : Fin d := ⟨0, by omega⟩
  let b : Fin d := ⟨1, by omega⟩
  let j : Fin n := ⟨n - 1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  letI : Nonempty (Fin d) := ⟨a⟩
  choose v hv hscore using fun x : Fin n → Fin d =>
    baseline_vector (prefixCounts j x) (fun i => block a b i (x j))
  obtain ⟨w, hw, hgain⟩ := constant_improvement hn j a b hab
  let x₀ : Fin n → Fin d := fun _ => a
  let v' := Function.update v x₀ w
  have hunit (x : Fin n → Fin d) : (∑ i, v' x i ^ 2) = 1 := by
    by_cases hx : x = x₀
    · subst x; simpa [v'] using hw
    · simpa [v', Function.update_of_ne hx] using hv x
  have htotal : (∑ x : Fin n → Fin d, (((Finset.univ.sup (prefixCounts j x) : ℕ) : ℝ) +
      mass (prefixCounts j x) (fun i => block a b i (x j)))) <
      ∑ x : Fin n → Fin d, payoff (prefixCounts j x) (fun i => block a b i (x j)) (v' x) := by
    apply Finset.sum_lt_sum
    · intro x _
      by_cases hx : x = x₀
      · subst x; simpa [v', x₀] using hgain.le
      · simpa [v', Function.update_of_ne hx] using (hscore x).ge
    · exact ⟨x₀, Finset.mem_univ _, by simpa [v', x₀] using hgain⟩
  rw [baseline_total j a b hab] at htotal
  refine ⟨fun x i => (v' x i : ℂ), measurements a b,
    (fun k => if k = j then 1 else 0), ?_, measurements_unitary a b hab, ?_⟩
  · intro x; exact real_unit (v' x) (hunit x)
  · intro S
    apply lt_of_le_of_lt (classical_bound S)
    unfold C quantumValue
    apply mul_lt_mul_of_pos_left _ (by positivity)
    convert htotal using 1
    apply Finset.sum_congr rfl
    intro x _
    exact quantum_payoff j a b x (v' x)

end D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage
