/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct normalized finite unifilar future laws give a common strict killed-pair contraction. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
import D5.S3.TotalVariation.Hellinger
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance 100000] Classical.propDecidable
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival
open D5.S3.TotalVariation.Bhattacharyya

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarAffinityContraction
variable {S : Type*} [Fintype S]

omit [Fintype S] in
theorem word_nonneg (p : S → Bool → ℝ) (δ : S → Bool → S)
    (hp : ∀ a x, 0 ≤ p a x) (n : ℕ) (a : S) (w : Fin n → Bool) :
    0 ≤ wordMass p δ n a w := by
  induction n generalizing a with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hp _ _) (ih _ _)

theorem word_total (p : S → Bool → ℝ) (δ : S → Bool → S)
    (hs : ∀ a, ∑ x, p a x = 1) (n : ℕ) (a : S) :
    ∑ w : Fin n → Bool, wordMass p δ n a w = 1 := by
  induction n generalizing a with
  | zero => simp [wordMass]
  | succ n ih =>
    rw [sum_words]
    simp only [wordMass,Fin.cons_zero,Fin.tail_cons,← Finset.mul_sum,ih,mul_one]
    exact hs a

private theorem word_append (p : S → Bool → ℝ) (δ : S → Bool → S)
    (m n : ℕ) (a : S) (w : Fin m → Bool) (v : Fin n → Bool) :
    wordMass p δ (m+n) a (Fin.append w v) =
      wordMass p δ m a w * wordMass p δ n (endpoint δ m a w) v := by
  induction m generalizing a with
  | zero =>
    have hv : Fin.append w v = v ∘ Fin.cast (Nat.zero_add n) := by
      ext k
      simp [Fin.append,Fin.addCases]
    simp only [hv,wordMass,endpoint,one_mul]
    have hcast (k l : ℕ) (e : k = l) (u : Fin l → Bool) :
        wordMass p δ k a (u ∘ Fin.cast e) = wordMass p δ l a u := by
      subst k
      rfl
    exact hcast _ _ _ _
  | succ m ih =>
    have e : m+1+n = (m+n)+1 := by omega
    have hw : Fin.append w v = (Fin.cons (w 0) (Fin.append (Fin.tail w) v)) ∘ Fin.cast e := by
      rw [← Fin.cons_self_tail w]
      exact Fin.append_cons _ _ _
    have hcast : ∀ (k : ℕ) (e : k = (m+n)+1) (u : Fin ((m+n)+1) → Bool),
        wordMass p δ k a (u ∘ Fin.cast e) = wordMass p δ ((m+n)+1) a u := by
      intro k e u
      subst k
      rfl
    rw [hw,hcast]
    simp only [wordMass,Fin.cons_zero,Fin.tail_cons,endpoint]
    rw [ih,mul_assoc]

private theorem word_marginal (p : S → Bool → ℝ) (δ : S → Bool → S)
    (hs : ∀ a, ∑ x, p a x = 1) (m n : ℕ) (a : S) (w : Fin m → Bool) :
    ∑ v : Fin n → Bool, wordMass p δ (m+n) a (Fin.append w v) = wordMass p δ m a w := by
  simp_rw [word_append]
  rw [← Finset.mul_sum,word_total p δ hs,mul_one]

private theorem common_length (p : S → Bool → ℝ) (δ : S → Bool → S)
    (hs : ∀ a, ∑ x, p a x = 1)
    (hd : ∀ a b : S, a ≠ b → ∃ n, wordMass p δ n a ≠ wordMass p δ n b) :
    ∃ ell : ℕ, 0 < ell ∧ ∀ a b : S, a ≠ b →
      wordMass p δ ell a ≠ wordMass p δ ell b := by
  classical
  let f : Pair S → ℕ := fun s => Classical.choose (hd s.val.1 s.val.2 s.property)
  let ell := max 1 (Finset.univ.sup f)
  refine ⟨ell,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _),?_⟩
  intro a b hab he
  let s : Pair S := ⟨(a,b),hab⟩
  have hf : f s ≤ ell := (Finset.le_sup (f := f) (Finset.mem_univ s)).trans (le_max_right _ _)
  have hbad := Classical.choose_spec (hd a b hab)
  change wordMass p δ (f s) a ≠ wordMass p δ (f s) b at hbad
  apply hbad
  funext w
  have ha := word_marginal p δ hs (f s) (ell-f s) a w
  have hb := word_marginal p δ hs (f s) (ell-f s) b w
  rw [← ha,← hb]
  apply Finset.sum_congr rfl
  intro v _
  have he' : wordMass p δ (f s+(ell-f s)) a = wordMass p δ (f s+(ell-f s)) b := by
    have heq : f s+(ell-f s) = ell := by omega
    exact (congrArg (fun n => wordMass p δ n a = wordMass p δ n b) heq).mpr he
  exact congrFun he' (Fin.append w v)

private theorem affinity_strict {W : Type*} [Fintype W] (p q : W → ℝ)
    (hp : (∀ w, 0 ≤ p w) ∧ ∑ w, p w = 1)
    (hq : (∀ w, 0 ≤ q w) ∧ ∑ w, q w = 1) (hne : p ≠ q) :
    bhattacharyya p q < 1 := by
  have hle := bhattacharyya_le_one p q hp hq
  have hsq := total_variation_sq_le_one_sub_bhattacharyya_sq p q hp hq
  have hn := D5.S3.TotalVariation.Metric.total_variation_nonneg p q
  have hz := D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff p q
  by_contra hnot
  have he : bhattacharyya p q = 1 := le_antisymm hle (le_of_not_gt hnot)
  rw [he] at hsq
  have ht : D5.S3.TotalVariation.Pinsker.totalVariation p q = 0 := by nlinarith
  exact hne (hz.mp ht)

theorem matrix_block {A : Type*} [Fintype A]
    [DecidableEq A] (B : Matrix A A ℝ) (hn : ∀ i j, 0 ≤ B i j)
    (hs : ∀ i, ∑ j, B i j ≤ 1) (ell : ℕ) (he : 0 < ell)
    (rho : ℝ) (hr : 0 ≤ rho) (hb : ∀ i, ∑ j, (B^ell) i j ≤ rho) :
    ∀ n i, ∑ j, (B^n) i j ≤ rho^(n/ell) := by
  classical
  have hbase : ∀ n i, ∑ j, (B^n) i j ≤ 1 := by
    intro n
    induction n with
    | zero => intro i; simp [Matrix.one_apply]
    | succ n ih =>
      intro i
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      exact (Finset.sum_le_sum (fun j _ => mul_le_of_le_one_right (hn i j) (ih j))).trans (hs i)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i
    by_cases hsmall : n < ell
    · rw [Nat.div_eq_of_lt hsmall,pow_zero]
      exact hbase n i
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show ell ≤ n by omega)
      have hik := ih k (by omega)
      have hpow : (ell+k)/ell = k/ell+1 := by
        rw [Nat.add_div_left _ he]
      rw [hpow,pow_succ]
      calc
        _ = ∑ j, (B^ell) i j * (∑ t, (B^k) j t) := by
          rw [pow_add]
          simp only [Matrix.mul_apply]
          rw [Finset.sum_comm]
          simp only [← Finset.mul_sum]
        _ ≤ ∑ j, (B^ell) i j * rho^(k/ell) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hik j)
            (Matrix.pow_apply_nonneg hn ell i j))
        _ ≤ rho * rho^(k/ell) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hb i) (pow_nonneg hr _)
        _ = _ := mul_comm _ _

/-- A single finite length distinguishes all pairs; its normalized affinities are
strictly below one and control every original-time killed-pair power. -/
theorem finite_distinguishing_contraction (p : S → Bool → ℝ) (δ : S → Bool → S)
    (hp : ∀ a x, 0 ≤ p a x) (hs : ∀ a, ∑ x, p a x = 1)
    (hd : ∀ a b : S, a ≠ b → ∃ n, wordMass p δ n a ≠ wordMass p δ n b) :
    ∃ (ell : ℕ) (rho : ℝ), 0 < ell ∧ 0 ≤ rho ∧ rho < 1 ∧
      (∀ a b : S, a ≠ b → wordMass p δ ell a ≠ wordMass p δ ell b) ∧
      (∀ a b : S, a ≠ b → bhattacharyya (wordMass p δ ell a) (wordMass p δ ell b) ≤ rho) ∧
      (∀ n (s : Pair S), ∑ t, (pairMatrix p δ ^ n) s t ≤ rho^(n/ell)) := by
  classical
  obtain ⟨ell,he,hdell⟩ := common_length p δ hs hd
  let aff : Pair S → ℝ := fun s => bhattacharyya
    (wordMass p δ ell s.val.1) (wordMass p δ ell s.val.2)
  have ha (s : Pair S) : aff s < 1 := affinity_strict _ _
    ⟨word_nonneg p δ hp _ _,word_total p δ hs _ _⟩
    ⟨word_nonneg p δ hp _ _,word_total p δ hs _ _⟩ (hdell _ _ s.property)
  obtain ⟨smax,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Option (Pair S)))
    (fun s => s.elim 0 aff) (by simp)
  let rho := max 0 (smax.elim 0 aff)
  have hr0 : 0 ≤ rho := le_max_left _ _
  have hr1 : rho < 1 := by
    apply max_lt zero_lt_one
    cases smax with
    | none => exact zero_lt_one
    | some s => exact ha s
  have har (s : Pair S) : aff s ≤ rho :=
    (hmax (some s) (Finset.mem_univ _)).trans (le_max_right _ _)
  have hn (s t : Pair S) : 0 ≤ pairMatrix p δ s t := by
    unfold pairMatrix
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> positivity
  have hrow (s : Pair S) : ∑ t, pairMatrix p δ s t ≤ 1 := by
    have haff := bhattacharyya_le_one (p s.val.1) (p s.val.2)
      ⟨hp _,hs _⟩ ⟨hp _,hs _⟩
    have hh := pairMatrix_action p δ s (fun _ => 1)
    simp only [mul_one] at hh
    rw [hh]
    apply le_trans _ haff
    apply Finset.sum_le_sum
    intro x _
    split_ifs <;> first | exact le_rfl | exact Real.sqrt_nonneg _
  have hb (s : Pair S) : ∑ t, (pairMatrix p δ ^ ell) s t ≤ rho := by
    rw [pair_survival_word_affinity p δ hp]
    apply le_trans _ (har s)
    unfold survivingAffinity aff bhattacharyya
    apply Finset.sum_le_sum
    intro w _
    dsimp only
    split_ifs <;> simp [Real.sqrt_nonneg]
  exact ⟨ell,rho,he,hr0,hr1,hdell,fun a b hab => har ⟨(a,b),hab⟩,
    matrix_block _ hn hrow ell he rho hr0 hb⟩

#print axioms finite_distinguishing_contraction
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarAffinityContraction
