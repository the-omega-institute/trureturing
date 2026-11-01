/- GID: D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact transition weights of legal binary blocks with both exterior bits. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import D5.S3.Quantum.Entanglement.PhaseHistoryBound
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight

open scoped BigOperators Matrix
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.Entanglement.PhaseHistoryBound (transition)

/-- The ordered product from the left bit, through the block, to the right bit. -/
def pathMass (p : ℝ) : (n : ℕ) → Bool → (Fin n → Bool) → Bool → ℝ
  | 0, l, _, r => transition p l r
  | n + 1, l, w, r => transition p l (w 0) * pathMass p n (w 0) (Fin.tail w) r

private theorem pathMass_integer (p : ℝ) (hp : p ≠ 1) (n : ℕ)
    (l r : Bool) (w : Fin n → Bool)
    (hw : Adm (n + 2) (Fin.cons l (Fin.snoc w r))) :
    pathMass p n l w r =
      p ^ r.toNat * (1 - p) ^ ((n + 1 : ℤ) - l.toNat - r.toNat) *
        (p / (1 - p) ^ 2) ^ (∑ i, (w i).toNat) := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  induction n generalizing l r with
  | zero =>
      cases l <;> cases r <;> simp [Adm, pathMass, transition, Fin.snoc] at hw ⊢
  | succ n ih =>
      have hh : ¬(l ∧ w 0) ∧
          Adm (n + 2) (Fin.cons (w 0) (Fin.snoc (Fin.tail w) r)) := by
        have he : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
        rw [he, ← Fin.cons_snoc_eq_snoc_cons] at hw
        simpa [Adm, Fin.cons_zero, Fin.cons_one, Fin.tail_cons] using hw
      rw [pathMass, ih (w 0) r (Fin.tail w) hh.2, Fin.sum_univ_succ]
      change transition p l (w 0) *
          (p ^ r.toNat * (1 - p) ^ ((n + 1 : ℤ) - (w 0).toNat - r.toNat) *
            (p / (1 - p) ^ 2) ^ (∑ i, ((Fin.tail w) i).toNat)) =
        p ^ r.toNat * (1 - p) ^ ((n + 2 : ℤ) - l.toNat - r.toNat) *
          (p / (1 - p) ^ 2) ^ ((w 0).toNat + ∑ i, ((Fin.tail w) i).toNat)
      cases l <;> cases hc : w 0 <;> simp only [transition, Bool.false_eq_true, if_false, if_true]
      · simp only [ Bool.toNat_false, Nat.cast_zero, sub_zero, zero_add]
        rw [show (n + 2 : ℤ) - r.toNat = ((n + 1 : ℤ) - r.toNat) + 1 by omega,
          zpow_add₀ hq]
        simp only [zpow_one]
        ring
      · simp only [ Bool.toNat_true, Bool.toNat_false, Nat.cast_zero,
          Nat.cast_one, sub_zero, pow_add, pow_one]
        rw [show (n + 2 : ℤ) - r.toNat = ((n + 1 : ℤ) - 1 - r.toNat) + 2 by omega,
          zpow_add₀ hq]
        simp only [zpow_ofNat]
        field_simp
      · simp only [ Bool.toNat_true, Bool.toNat_false, Nat.cast_zero,
          Nat.cast_one, sub_zero, zero_add, one_mul]
        rw [show (n + 2 : ℤ) - 1 - r.toNat = (n + 1 : ℤ) - r.toNat by omega]
      · simp [hc] at hh

/-- Every positive-length legal block has exactly the hard-core activity weight. -/
theorem path_weight_formula (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℕ) (hn : 1 ≤ n) (l r : Bool) (w : Fin n → Bool)
    (hw : Adm (n + 2) (Fin.cons l (Fin.snoc w r))) :
    pathMass p n l w r =
      p ^ r.toNat * (1 - p) ^ (n + 1 - l.toNat - r.toNat) *
        (p / (1 - p) ^ 2) ^ (∑ i, (w i).toNat) ∧
      0 < pathMass p n l w r := by
  have he : (n + 1 : ℤ) - l.toNat - r.toNat =
      ((n + 1 - l.toNat - r.toNat : ℕ) : ℤ) := by
    cases l <;> cases r <;> simp <;> omega
  have hf := pathMass_integer p (ne_of_lt hp1) n l r w hw
  rw [he, zpow_natCast] at hf
  refine ⟨hf, ?_⟩
  rw [hf]
  exact mul_pos (mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _))
    (pow_pos (div_pos hp (sq_pos_of_pos (sub_pos.mpr hp1))) _)


/-- The row 0(10)^j followed by 2(N-j) zeros, in zero-based coordinates. -/
def halfWord (N : ℕ) (j : Fin (N + 1)) (i : Fin (2 * N + 1)) : Bool :=
  decide (i.val % 2 = 1 ∧ i.val < 2 * j.val)

private theorem halfWord_count (N : ℕ) (j : Fin (N + 1)) :
    (∑ i, (halfWord N j i).toNat) = j.val := by
  classical
  have hs : (∑ i, (halfWord N j i).toNat) =
      (Finset.univ.filter (fun i : Fin (2 * N + 1) =>
        i.val % 2 = 1 ∧ i.val < 2 * j.val)).card := by
    trans ∑ i : Fin (2 * N + 1),
      if i.val % 2 = 1 ∧ i.val < 2 * j.val then 1 else 0
    · apply Finset.sum_congr rfl
      intro i _
      by_cases h : i.val % 2 = 1 ∧ i.val < 2 * j.val <;> simp [halfWord, h]
    · exact Finset.sum_boole _ _
  rw [hs]
  have hc : (Finset.univ.filter (fun i : Fin (2 * N + 1) =>
      i.val % 2 = 1 ∧ i.val < 2 * j.val)).card =
      (Finset.univ : Finset (Fin j.val)).card := by
    apply Finset.card_bij (fun i hi =>
      (⟨i.val / 2, by have := (Finset.mem_filter.mp hi).2; omega⟩ : Fin j.val))
    · simp
    · intro i hi k hk he
      have hi' := (Finset.mem_filter.mp hi).2
      have hk' := (Finset.mem_filter.mp hk).2
      have hval : i.val / 2 = k.val / 2 := congrArg Fin.val he
      apply Fin.ext
      omega
    · intro k _
      refine ⟨⟨2 * k.val + 1, by have := k.isLt; have := j.isLt; omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := k.isLt
        constructor <;> omega
      · apply Fin.ext
        change (2 * k.val + 1) / 2 = k.val
        omega
  simpa using hc

/-- Concatenated selected row and column, with the cut after 2N+1 bits. -/
def selectedWord (N : ℕ) (i j : Fin (N + 1)) :
    Fin ((2 * N + 1) + (2 * N + 1)) → Bool :=
  Fin.append (halfWord N i) (halfWord N j)

private theorem selectedWord_count (N : ℕ) (i j : Fin (N + 1)) :
    (∑ k, (selectedWord N i j k).toNat) = i.val + j.val := by
  rw [Fin.sum_univ_add]
  simp only [selectedWord, Fin.append_left, Fin.append_right]
  rw [halfWord_count, halfWord_count]


private theorem selectedWord_no_adjacent (N : ℕ) (i j : Fin (N + 1))
    (u v : Fin ((2 * N + 1) + (2 * N + 1))) (h : u.val + 1 = v.val) :
    selectedWord N i j u = false ∨ selectedWord N i j v = false := by
  simp only [selectedWord, Fin.append, Fin.addCases, halfWord]
  split_ifs <;> simp_all <;> omega

private theorem selectedWord_zero (N : ℕ) (i j : Fin (N + 1))
    (k : Fin ((2 * N + 1) + (2 * N + 1))) (hk : k.val = 0) :
    selectedWord N i j k = false := by
  simp [selectedWord, Fin.append, Fin.addCases, halfWord, hk]

private theorem selectedWord_last (N : ℕ) (i j : Fin (N + 1))
    (k : Fin ((2 * N + 1) + (2 * N + 1)))
    (hk : k.val + 1 = (2 * N + 1) + (2 * N + 1)) :
    selectedWord N i j k = false := by
  simp only [selectedWord, Fin.append, Fin.addCases, halfWord]
  split_ifs <;> simp_all <;> omega

private theorem padded_legal {m : ℕ} (hm : 1 ≤ m) (w : Fin m → Bool)
    (hf : ∀ k, k.val = 0 → w k = false)
    (hl : ∀ k, k.val + 1 = m → w k = false)
    (ha : ∀ u v, u.val + 1 = v.val → w u = false ∨ w v = false)
    (l r : Bool) : Adm (m + 2) (Fin.cons l (Fin.snoc w r)) := by
  apply (adm_iff_no_adjacent_true _ _).mpr
  intro u v huv
  by_cases hu : u.val = 0
  · let k : Fin m := ⟨0, by omega⟩
    have ev : v = k.castSucc.succ := Fin.ext (by simp [k]; omega)
    right
    simpa [ev] using hf k rfl
  · by_cases hv : v.val = m + 1
    · let k : Fin m := ⟨m - 1, by omega⟩
      have eu : u = k.castSucc.succ := Fin.ext (by simp [k]; omega)
      left
      simpa [eu] using hl k (by simp [k]; omega)
    · let u' : Fin m := ⟨u.val - 1, by omega⟩
      let v' : Fin m := ⟨v.val - 1, by omega⟩
      have eu : u = u'.castSucc.succ := Fin.ext (by simp [u']; omega)
      have ev : v = v'.castSucc.succ := Fin.ext (by simp [v']; omega)
      simpa [eu, ev] using ha u' v' (by simp [u', v']; omega)

private theorem selectedWord_legal (N : ℕ) (i j : Fin (N + 1)) (l r : Bool) :
    Adm (((2 * N + 1) + (2 * N + 1)) + 2)
      (Fin.cons l (Fin.snoc (selectedWord N i j) r)) := by
  exact padded_legal (by omega) _ (selectedWord_zero N i j) (selectedWord_last N i j)
    (selectedWord_no_adjacent N i j) l r


noncomputable section

/-- Sum of actual transition products over all legal completions with fixed exterior bits. -/
def pathNormalizer (p : ℝ) (m : ℕ) (l r : Bool) : ℝ :=
  ∑ w : Fin m → Bool, if Adm (m + 2) (Fin.cons l (Fin.snoc w r))
    then pathMass p m l w r else 0

/-- The activity partition function over the same completion set. -/
def activityPartition (p : ℝ) (m : ℕ) (l r : Bool) : ℝ :=
  ∑ w : Fin m → Bool, if Adm (m + 2) (Fin.cons l (Fin.snoc w r))
    then (p / (1 - p) ^ 2) ^ (∑ k, (w k).toNat) else 0

/-- Mixture of normalized actual component path products, with fixed exterior bits. -/
def conditionalMixture {K : ℕ} (p θ : Fin K → ℝ) (m : ℕ)
    (l r : Bool) (w : Fin m → Bool) : ℝ :=
  ∑ k, θ k * (pathMass (p k) m l w r / pathNormalizer (p k) m l r)

/-- The selected square submatrix at the middle cut of the length 4N+2 block. -/
def cutMinor (N : ℕ) (p θ : Fin (N + 1) → ℝ) (l r : Bool) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => conditionalMixture p θ ((2 * N + 1) + (2 * N + 1))
    l r (selectedWord N i j)

private theorem normalizer_factor (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) :
    pathNormalizer p m l r =
      (p ^ r.toNat * (1 - p) ^ (m + 1 - l.toNat - r.toNat)) *
        activityPartition p m l r := by
  rw [pathNormalizer, activityPartition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : Adm (m + 2) (Fin.cons l (Fin.snoc w r))
  · simp only [hw, ite_true]
    exact (path_weight_formula p hp hp1 m hm l r w hw).1
  · simp [hw]

private theorem partition_pos (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (l r : Bool) :
    0 < activityPartition p ((2 * N + 1) + (2 * N + 1)) l r := by
  unfold activityPartition
  apply Finset.sum_pos'
  · intro w _
    split_ifs
    · exact (pow_pos (div_pos hp (sq_pos_of_pos (sub_pos.mpr hp1))) _).le
    · rfl
  · refine ⟨selectedWord N 0 0, Finset.mem_univ _, ?_⟩
    rw [if_pos (selectedWord_legal N 0 0 l r)]
    exact pow_pos (div_pos hp (sq_pos_of_pos (sub_pos.mpr hp1))) _

private theorem normalized_path (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ) (hm : 1 ≤ m) (l r : Bool) (w : Fin m → Bool)
    (hw : Adm (m + 2) (Fin.cons l (Fin.snoc w r))) :
    pathMass p m l w r / pathNormalizer p m l r =
      (p / (1 - p) ^ 2) ^ (∑ k, (w k).toNat) / activityPartition p m l r := by
  rw [(path_weight_formula p hp hp1 m hm l r w hw).1,
    normalizer_factor p hp hp1 m hm l r]
  exact mul_div_mul_left _ _ (ne_of_gt
    (mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _)))

private theorem activity_strictMono :
    StrictMonoOn (fun p : ℝ => p / (1 - p) ^ 2) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  apply (div_lt_div_iff₀ (sq_pos_of_pos (sub_pos.mpr ha.2))
    (sq_pos_of_pos (sub_pos.mpr hb.2))).mpr
  have hprod : 0 < 1 - a * b := sub_pos.mpr
    (lt_trans (by simpa using mul_lt_mul_of_pos_right ha.2 hb.1) hb.2)
  have h : 0 < (b - a) * (1 - a * b) := mul_pos (sub_pos.mpr hab) hprod
  nlinarith

/-- The explicit legal-word minor of a persistent positive mixture has a positive determinant. -/
theorem persistent_mixture_minor (N : ℕ) (p θ : Fin (N + 1) → ℝ)
    (hp : ∀ k, 0 < p k ∧ p k < 1) (hmono : StrictMono p)
    (hθ : ∀ k, 0 < θ k) (l r : Bool) :
    Function.Injective (halfWord N) ∧
    (cutMinor N p θ l r).det =
      (∏ k, θ k / activityPartition (p k) ((2 * N + 1) + (2 * N + 1)) l r) *
        (∏ i : Fin (N + 1), ∏ j ∈ Finset.Ioi i,
          (p j / (1 - p j) ^ 2 - p i / (1 - p i) ^ 2)) ^ 2 ∧
      0 < (cutMinor N p θ l r).det := by
  let z : Fin (N + 1) → ℝ := fun k => p k / (1 - p k) ^ 2
  let c : Fin (N + 1) → ℝ := fun k =>
    θ k / activityPartition (p k) ((2 * N + 1) + (2 * N + 1)) l r
  have hc : ∀ k, 0 < c k := fun k => div_pos (hθ k)
    (partition_pos N (p k) (hp k).1 (hp k).2 l r)
  have hz : StrictMono z := fun i j hij =>
    activity_strictMono (hp i) (hp j) (hmono hij)
  have he : cutMinor N p θ l r =
      (Matrix.vandermonde z)ᵀ * Matrix.diagonal c * Matrix.vandermonde z := by
    rw [Matrix.mul_assoc]
    ext i j
    change conditionalMixture p θ ((2 * N + 1) + (2 * N + 1))
      l r (selectedWord N i j) = _
    rw [Matrix.mul_apply]
    simp only [conditionalMixture, Matrix.transpose_apply, Matrix.diagonal_mul,
      Matrix.vandermonde_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [normalized_path (p k) (hp k).1 (hp k).2 _ (by omega) l r _
      (selectedWord_legal N i j l r), selectedWord_count, pow_add]
    dsimp [z, c]
    ring
  have hd : (cutMinor N p θ l r).det =
      (∏ k, c k) * (Matrix.vandermonde z).det ^ 2 := by
    rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    rw [← halfWord_count N i, ← halfWord_count N j, hij]
  · rw [hd, Matrix.det_vandermonde]
  · rw [hd]
    exact mul_pos (Finset.prod_pos (fun k _ => hc k))
      (sq_pos_of_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hz.injective))

#print axioms path_weight_formula
#print axioms persistent_mixture_minor

end

end D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight
