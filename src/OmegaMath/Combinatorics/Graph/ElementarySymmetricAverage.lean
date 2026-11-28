import OmegaBuild.Commands
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

/-! # Elementary symmetric sums and pair averaging

The scalar estimates used to average a finite clique invariant. All symmetric
sums are unscaled; the variance correction has coefficient one half of the
uniform upper bound for a pair complement.
-/

compile_only_with_mathlib

open scoped BigOperators

namespace ElementarySymmetricAverage

variable {ι : Type*}

/-- The unscaled elementary symmetric sum on a specified set of coordinates. -/
noncomputable def elementary (S : Finset ι) (s : ℕ) (p : ι → ℝ) : ℝ :=
  ∑ A ∈ S.powersetCard s, ∏ i ∈ A, p i

@[simp] theorem elementary_zero (S : Finset ι) (p : ι → ℝ) :
    elementary S 0 p = 1 := by
  classical
  simp [elementary]

/-- Evaluation on a constant vector, including degrees exceeding the cardinality. -/
theorem elementary_const (S : Finset ι) (s : ℕ) (u : ℝ) :
    elementary S s (fun _ => u) = (S.card.choose s : ℝ) * u ^ s := by
  classical
  unfold elementary
  have h : ∀ A ∈ S.powersetCard s, (∏ _i ∈ A, u) = u ^ s := by
    intro A hA
    simp [(Finset.mem_powersetCard.mp hA).2]
  simp_rw [Finset.sum_congr rfl h]
  simp

/-- Restricting to a set only uses coordinates in that set. -/
theorem elementary_congr (S : Finset ι) (s : ℕ) {p q : ι → ℝ}
    (h : ∀ i ∈ S, p i = q i) : elementary S s p = elementary S s q := by
  classical
  apply Finset.sum_congr rfl
  intro A hA
  exact Finset.prod_congr rfl fun i hi => h i ((Finset.mem_powersetCard.mp hA).1 hi)

theorem elementary_nonneg (S : Finset ι) (s : ℕ) (p : ι → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) : 0 ≤ elementary S s p := by
  classical
  exact Finset.sum_nonneg fun A hA => Finset.prod_nonneg fun i hi =>
    hp i ((Finset.mem_powersetCard.mp hA).1 hi)

/-- The insertion recurrence is the decomposition of subsets according to
whether they contain the inserted coordinate. -/
theorem elementary_insert [DecidableEq ι] (S : Finset ι) (i : ι) (hi : i ∉ S)
    (s : ℕ) (p : ι → ℝ) :
    elementary (insert i S) (s + 1) p =
      elementary S (s + 1) p + p i * elementary S s p := by
  unfold elementary
  rw [Finset.powersetCard_succ_insert hi]
  have hd : Disjoint (S.powersetCard (s + 1)) ((S.powersetCard s).image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro A hA hB
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB
    exact hi ((Finset.mem_powersetCard.mp hA).1 (Finset.mem_insert_self i B))
  rw [Finset.sum_union hd, Finset.sum_image]
  · congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    exact Finset.prod_insert (fun h => hi ((Finset.mem_powersetCard.mp hA).1 h))
  · intro A hA B hB hab
    have ha : i ∉ A := fun h => hi ((Finset.mem_powersetCard.mp hA).1 h)
    have hb : i ∉ B := fun h => hi ((Finset.mem_powersetCard.mp hB).1 h)
    simpa [ha, hb] using congrArg (fun T : Finset ι => T.erase i) hab

@[simp] theorem elementary_one (S : Finset ι) (p : ι → ℝ) :
    elementary S 1 p = ∑ i ∈ S, p i  := by
  classical
  simp [elementary, Finset.powersetCard_one]


/-- Averaging two coordinates. -/
noncomputable def average [DecidableEq ι] (p : ι → ℝ) (i j : ι) : ι → ℝ :=
  fun k => if k = i ∨ k = j then (p i + p j) / 2 else p k

section Finite
variable [Fintype ι] [DecidableEq ι]

/-- Sum over the complement of two different coordinates. -/
theorem sum_pair (f : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have h := Finset.sum_erase_add (Finset.univ : Finset ι) f (Finset.mem_univ i)
  have h' := Finset.sum_erase_add (Finset.univ.erase i) f
    (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  linarith

theorem sum_average (p : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    (∑ k, average p i j k) = ∑ k, p k := by
  rw [sum_pair _ i j hij, sum_pair p i j hij]
  have h : (∑ k ∈ (Finset.univ.erase i).erase j, average p i j k) =
      ∑ k ∈ (Finset.univ.erase i).erase j, p k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    simp [average, hk.1, hk.2.1]
  rw [h]
  simp only [average, or_true, ite_true, true_or, eq_self]
  ring

/-- Squared deviations from any fixed center. -/
noncomputable def variance (u : ℝ) (p : ι → ℝ) : ℝ := ∑ i, (p i - u) ^ 2

theorem variance_average (u : ℝ) (p : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    variance u (average p i j) = variance u p - (p i - p j) ^ 2 / 2 := by
  unfold variance
  rw [sum_pair _ i j hij, sum_pair _ i j hij]
  have h : (∑ k ∈ (Finset.univ.erase i).erase j, (average p i j k - u) ^ 2) =
      ∑ k ∈ (Finset.univ.erase i).erase j, (p k - u) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    simp [average, hk.1, hk.2.1]
  rw [h]
  simp only [average, or_true, ite_true, true_or, eq_self]
  ring

/-- Two insertions isolate the only term quadratic in the selected coordinates. -/
theorem elementary_pair (p : ι → ℝ) (i j : ι) (hij : i ≠ j) (s : ℕ) :
    elementary Finset.univ (s + 2) p =
      elementary ((Finset.univ.erase i).erase j) (s + 2) p +
      (p i + p j) * elementary ((Finset.univ.erase i).erase j) (s + 1) p +
      p i * p j * elementary ((Finset.univ.erase i).erase j) s p := by
  let S := (Finset.univ.erase i).erase j
  have hi : i ∉ S := by simp [S]
  have hj : j ∉ S := by simp [S]
  have hi' : i ∉ insert j S := by simp [hi, hij]
  have hU : (Finset.univ : Finset ι) = insert i (insert j S) := by
    ext k
    simp [S]
    tauto
  conv_lhs => rw [hU]
  rw [elementary_insert _ _ hi', elementary_insert _ _ hj, elementary_insert _ _ hj]
  ring

/-- Exact gain in the elementary symmetric sum under pair averaging. -/
theorem elementary_average (p : ι → ℝ) (i j : ι) (hij : i ≠ j) (s : ℕ) :
    elementary Finset.univ (s + 2) (average p i j) =
      elementary Finset.univ (s + 2) p + (p i - p j) ^ 2 / 4 *
        elementary ((Finset.univ.erase i).erase j) s p := by
  rw [elementary_pair _ i j hij, elementary_pair p i j hij]
  have hc (n : ℕ) : elementary ((Finset.univ.erase i).erase j) n (average p i j) =
      elementary ((Finset.univ.erase i).erase j) n p := by
    apply elementary_congr
    intro k hk
    simp only [Finset.mem_erase] at hk
    simp [average, hk.1, hk.2.1]
  rw [hc, hc, hc]
  simp only [average, or_true, ite_true, true_or, eq_self]
  ring


/-- The closed simplex with a prescribed total mass. -/
def simplex (t : ℝ) : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = t}

omit [Fintype ι] [DecidableEq ι] in
private theorem continuous_elementary (S : Finset ι) (s : ℕ) :
    Continuous (elementary S s) := by
  classical
  unfold elementary
  fun_prop

omit [DecidableEq ι] in
private theorem continuous_variance (u : ℝ) : Continuous (variance (ι := ι) u) := by
  unfold variance
  fun_prop

omit [DecidableEq ι] in
private theorem compact_simplex (t : ℝ) : IsCompact (simplex (ι := ι) t) := by
  have hc : IsClosed (simplex (ι := ι) t) := by
    change IsClosed ({p : ι → ℝ | ∀ i, 0 ≤ p i} ∩ {p : ι → ℝ | (∑ i, p i) = t})
    apply IsClosed.inter
    · have hh : {p : ι → ℝ | ∀ i, 0 ≤ p i} = ⋂ i, {p : ι → ℝ | 0 ≤ p i} := by
        ext p
        simp
      rw [hh]
      exact isClosed_iInter fun i => isClosed_le
        (continuous_const : Continuous (fun _ : ι → ℝ => (0 : ℝ))) (continuous_apply i)
    · exact isClosed_eq (by fun_prop) continuous_const
  apply IsCompact.of_isClosed_subset (s := Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => t))
    isCompact_Icc hc
  intro p hp
  refine ⟨hp.1, fun i => ?_⟩
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

private theorem average_mem_simplex {t : ℝ} {p : ι → ℝ}
    (hp : p ∈ simplex t) (i j : ι) (hij : i ≠ j) :
    average p i j ∈ simplex t := by
  refine ⟨fun k => ?_, (sum_average p i j hij).trans hp.2⟩
  dsimp [average]
  split_ifs
  · exact div_nonneg (add_nonneg (hp.1 i) (hp.1 j)) (by norm_num)
  · exact hp.1 k

/-- A continuous objective which cannot increase under pair averaging is
minimized at the uniform vector. A second minimization of variance forces all
coordinates of an objective minimizer to coincide. -/
private theorem uniform_minimum (t : ℝ) (f : (ι → ℝ) → ℝ) (hf : Continuous f)
    (hav : ∀ p ∈ simplex t, ∀ i j, i ≠ j → f (average p i j) ≤ f p)
    (p : ι → ℝ) (hp : p ∈ simplex t) :
    f (fun _ => t / Fintype.card ι) ≤ f p := by
  obtain ⟨a, ha, hamin⟩ := (compact_simplex t).exists_isMinOn ⟨p, hp⟩ hf.continuousOn
  let M : Set (ι → ℝ) := simplex t ∩ {x | f x = f a}
  have hM : IsCompact M := (compact_simplex t).inter_right
    (isClosed_eq hf continuous_const)
  obtain ⟨x, hx, hxmin⟩ := hM.exists_isMinOn ⟨a, ha, rfl⟩
    (continuous_variance (t / Fintype.card ι)).continuousOn
  have heq (i j : ι) : x i = x j := by
    by_cases hij : i = j
    · simp [hij]
    have hy := average_mem_simplex hx.1 i j hij
    have hfxy : f (average x i j) = f a := le_antisymm
      ((hav x hx.1 i j hij).trans hx.2.le) (hamin hy)
    have hv := hxmin (show average x i j ∈ M from ⟨hy, hfxy⟩)
    change variance (t / Fintype.card ι) x ≤
      variance (t / Fintype.card ι) (average x i j) at hv
    rw [variance_average _ _ _ _ hij] at hv
    nlinarith [sq_nonneg (x i - x j)]
  have hxu : x = fun _ => t / Fintype.card ι := by
    funext i
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      have : Nonempty ι := ⟨i⟩
      exact_mod_cast (ne_of_gt (Fintype.card_pos (α := ι)))
    have hs : (∑ j, x j) = (Fintype.card ι : ℝ) * x i := by
      calc
        _ = ∑ _j : ι, x i := Finset.sum_congr rfl fun j _ => heq j i
        _ = _ := by simp
    apply (eq_div_iff hn).2
    nlinarith [hx.1.2]
  rw [← hxu]
  exact hx.2.le.trans (hamin hp)



end Finite

/-- Every elementary symmetric polynomial on nonnegative weights is maximized
at the uniform vector with the same total mass. The empty type is included. -/
theorem elementary_le_uniform [Fintype ι] (s : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    elementary Finset.univ s p ≤
      ((Fintype.card ι).choose s : ℝ) * ((∑ i, p i) / Fintype.card ι) ^ s := by
  classical
  let t := ∑ i, p i
  have hav : ∀ (q : ι → ℝ), q ∈ simplex t → ∀ i j, i ≠ j →
      -(elementary Finset.univ s (average q i j)) ≤ -(elementary Finset.univ s q) := by
    intro q hq i j hij
    rcases s with _ | s
    · simp
    rcases s with _ | s
    · simp [elementary_one, sum_average q i j hij]
    · rw [elementary_average q i j hij s]
      have hE := elementary_nonneg ((Finset.univ.erase i).erase j) s q
        (fun k _ => hq.1 k)
      have := mul_nonneg (div_nonneg (sq_nonneg (q i - q j)) (by norm_num : (0 : ℝ) ≤ 4)) hE
      linarith
  have h := uniform_minimum t (fun q => -(elementary Finset.univ s q))
    (continuous_elementary _ s).neg hav p ⟨hp, rfl⟩
  rw [elementary_const] at h
  simpa only [Finset.card_univ, neg_le_neg_iff] using h

/-- Changing the coordinate type by an embedding preserves symmetric sums. -/
theorem elementary_map {κ : Type*} (f : ι ↪ κ) (S : Finset ι) (s : ℕ) (p : κ → ℝ) :
    elementary (S.map f) s p = elementary S s (p ∘ f) := by
  classical
  simp only [elementary, Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro A _
  change (∏ i ∈ A.map f, p i) = ∏ i ∈ A, p (f i)
  exact Finset.prod_map A f p

/-- The same uniform upper bound on any finite set of coordinates. -/
theorem elementary_le_uniform_finset (S : Finset ι) (s : ℕ) (p : ι → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) :
    elementary S s p ≤ (S.card.choose s : ℝ) * ((∑ i ∈ S, p i) / S.card) ^ s := by
  classical
  have hS : (Finset.univ : Finset S).map (Function.Embedding.subtype _) = S := by
    ext i
    simp
  have h := elementary_le_uniform (ι := S) s (fun i => p i) (fun i => hp i i.2)
  have he := elementary_map (Function.Embedding.subtype (fun i => i ∈ S)) Finset.univ s p
  change elementary ((Finset.univ : Finset S).map (Function.Embedding.subtype _)) s p =
    elementary Finset.univ s (fun i : S => p i) at he
  have he' : elementary S s p = elementary Finset.univ s (fun i : S => p i) :=
    (congrArg (fun T => elementary T s p) hS.symm).trans he
  rw [← he'] at h
  simpa only [Fintype.card_coe, Finset.sum_coe_sort] using h

section Finite
variable [Fintype ι] [DecidableEq ι]

/-- A complement upper bound gives the sharp coefficient `U / 2` in the
unscaled variance correction. The bound must hold throughout the simplex. -/
theorem elementary_lower_of_complement_bound (s : ℕ) (t U : ℝ)
    (hU : ∀ q ∈ simplex (ι := ι) t, ∀ i j, i ≠ j →
      elementary ((Finset.univ.erase i).erase j) s q ≤ U)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = t) :
    ((Fintype.card ι).choose (s + 2) : ℝ) * (t / Fintype.card ι) ^ (s + 2) -
      U / 2 * variance (t / Fintype.card ι) p ≤ elementary Finset.univ (s + 2) p := by
  let f := fun (q : ι → ℝ) => elementary Finset.univ (s + 2) q + U / 2 * variance (t / Fintype.card ι) q
  have hf : Continuous f := (continuous_elementary _ _).add
    (continuous_const.mul (continuous_variance _))
  have hav : ∀ (q : ι → ℝ), q ∈ simplex t → ∀ i j, i ≠ j → f (average q i j) ≤ f q := by
    intro q hq i j hij
    dsimp [f]
    rw [elementary_average q i j hij s, variance_average _ q i j hij]
    have h := mul_le_mul_of_nonneg_left (hU q hq i j hij)
      (sq_nonneg (q i - q j))
    nlinarith
  have h := uniform_minimum t f hf hav p ⟨hp, hsum⟩
  dsimp [f] at h
  rw [elementary_const] at h
  have hv : variance (t / Fintype.card ι) (fun _ : ι => t / Fintype.card ι) = 0 := by
    simp [variance]
  rw [hv] at h
  simp only [Finset.card_univ] at h
  linarith

end Finite

/-- A mass upper bound suffices; no positivity of the set cardinality is needed. -/
theorem elementary_le_of_sum_le (S : Finset ι) (s : ℕ) (p : ι → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) (t : ℝ) (ht : (∑ i ∈ S, p i) ≤ t) :
    elementary S s p ≤ (S.card.choose s : ℝ) * (t / S.card) ^ s := by
  have hsum : 0 ≤ ∑ i ∈ S, p i := Finset.sum_nonneg hp
  apply (elementary_le_uniform_finset S s p hp).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (div_nonneg hsum (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right ht (Nat.cast_nonneg _)) s

/-- Explicit unscaled variance bound. The complement coefficient is the maximum
for `s` coordinates chosen from the other `card ι - 2` coordinates, with total
mass bounded by the full mass. -/
theorem elementary_lower_uniform [Fintype ι] (s : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    ((Fintype.card ι).choose (s + 2) : ℝ) *
        ((∑ i, p i) / Fintype.card ι) ^ (s + 2) -
      (((Fintype.card ι - 2).choose s : ℝ) *
        ((∑ i, p i) / (Fintype.card ι - 2 : ℕ)) ^ s) / 2 *
          variance ((∑ i, p i) / Fintype.card ι) p ≤
      elementary Finset.univ (s + 2) p := by
  classical
  apply elementary_lower_of_complement_bound s (∑ i, p i) _ _ p hp rfl
  intro q hq i j hij
  have hc : ((Finset.univ.erase i).erase j).card = Fintype.card ι - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  have hm : (∑ k ∈ (Finset.univ.erase i).erase j, q k) ≤ ∑ k, p k := by
    rw [← hq.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hq.1 k)
  simpa only [hc] using elementary_le_of_sum_le ((Finset.univ.erase i).erase j) s q
    (fun k _ => hq.1 k) (∑ i, p i) hm

/-- The normalization used in finite clique estimates. Degree zero is one,
including when the ambient cardinality is zero. -/
noncomputable def factor (N s : ℕ) : ℝ :=
  (s.factorial : ℝ) * (N.choose s : ℝ) * (1 / (N : ℝ)) ^ s

/-- The normalized upper bound used for edge and triangle complements in
C39 (20). Coordinates outside `S` need no hypotheses. -/
theorem factorial_elementary_le (S : Finset ι) (s : ℕ) (p : ι → ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) (hsum : (∑ i ∈ S, p i) ≤ 1) :
    (s.factorial : ℝ) * elementary S s p ≤ factor S.card s := by
  have h := mul_le_mul_of_nonneg_left (elementary_le_of_sum_le S s p hp 1 hsum)
    (Nat.cast_nonneg s.factorial : (0 : ℝ) ≤ (s.factorial : ℝ))
  simpa only [factor, mul_assoc] using h

/-- C39 (21), in factorial normalization. The estimate allows zero weights and
does not require the support to contain `s + 2` elements. -/
theorem factorial_elementary_lower [Fintype ι] (s : ℕ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : (∑ i, p i) = 1) :
    factor (Fintype.card ι) (s + 2) -
      ((s + 2).choose 2 : ℝ) * factor (Fintype.card ι - 2) s *
        variance (1 / Fintype.card ι) p ≤
      ((s + 2).factorial : ℝ) * elementary Finset.univ (s + 2) p := by
  have h := elementary_lower_uniform s p hp
  rw [hsum] at h
  have hmul := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (s + 2).factorial :
    (0 : ℝ) ≤ ((s + 2).factorial : ℝ))
  have hfact : ((s + 2).choose 2 : ℝ) * 2 * (s.factorial : ℝ) =
      ((s + 2).factorial : ℝ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial (n := s + 2) (k := 2) (by omega)
    have hn' : (s + 2 - 2) = s := by omega
    rw [hn'] at hn
    exact_mod_cast hn
  convert hmul using 1
  dsimp [factor]
  rw [← hfact]
  ring

end ElementarySymmetricAverage
