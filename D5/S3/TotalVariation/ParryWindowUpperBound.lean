/- GID: D5/S3/TotalVariation/ParryWindowUpperBound
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryWindowUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed minimizer tables attain finite-window bounds under the actual Parry source. -/

import D5.S3.TotalVariation.ParryWordCollision
import D5.S3.TotalVariation.ParryTwistedComparison
import D5.S3.Combinatorics.FairWindowMinimizer

open scoped BigOperators
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryTwistedComparison
open D5.S3.TotalVariation.ParryWordCollision
open D5.S3.Combinatorics.FairWindowDefect
open D5.S3.Combinatorics.FairWindowMinimizer
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
open private prod_paritySign_cases from D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
namespace D5.S3.TotalVariation.ParryWindowUpperBound

/-- The rightmost occurrence of the minimum word rank. -/
noncomputable def rightmostSelect {n : ℕ} (q : Fin (n+1) → ℕ) : Fin (n+1) :=
  (Finset.univ.filter (fun i => q i = Finset.univ.inf' Finset.univ_nonempty q)).max'
    (by
      obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty q
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩)

/-- The same word-rank and transported-label construction with rightmost tie breaking. -/
noncomputable def rightmostTable (m q : ℕ) (ρ : Equiv.Perm (Fin m → Fin 2))
    (β : (Fin m → Fin 2) → Fin 2) (v : Fin (m+q) → Fin 2) : Fin 2 :=
  let a := rightmostSelect (fun i => rank ρ (word v i))
  let s := paritySign (β (word v a)) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin (m+q) => a.val+m ≤ j.val), paritySign (v j)
  if s = 1 then 1 else 0

/-- Bool encoding of the fixed minimizer construction. False selects the existing
leftmost table; true selects its rightmost variant. The chosen convention, word
ordering and label table are fixed for all successive windows. -/
noncomputable def windowTable (R m : ℕ) (hmR : m ≤ R)
    (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2)
    (rightmost : Bool) (v : Fin R → Bool) : Bool :=
  finTwoEquiv ((if rightmost then rightmostTable m (R-m) ρ β else table m (R-m) ρ β)
    (fun i => finTwoEquiv.symm (v ⟨i.val, by omega⟩)))

set_option maxHeartbeats 1200000 in
-- The two finite table averages and their transport encodings elaborate together.
/-- Actual stationary Parry windows admit fixed tables with the reciprocal bound
and the overlapping-word collision correction. Requiring the label table to be
identically zero doubles only the reciprocal term. -/
theorem parry_window_upper_bound (k : ℕ) (hk : 2 ≤ k)
    (R m : ℕ) (hm : 1 ≤ m) (hmR : m ≤ R) (rightmost : Bool) :
    (∃ (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2),
      stationaryDefect k R (windowTable R m hmR ρ β rightmost) ≤
        1 / (R-m+2 : ℕ) + ((R-m+2).choose 2 : ℝ) * parryParameter k^(m-1)) ∧
    (∃ ρ : Equiv.Perm (Fin m → Fin 2),
      stationaryDefect k R (windowTable R m hmR ρ (fun _ => 0) rightmost) ≤
        2 / (R-m+2 : ℕ) + ((R-m+2).choose 2 : ℝ) * parryParameter k^(m-1)) := by
  classical
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hmR
  let P : Prefix k (m+q+1) → ℝ := referenceLaw k (parryParameter k) (m+q+1) (parryLaw k)
  let V (v : Prefix k (m+q+1)) : Fin (m+q+1) → Fin 2 :=
    fun i => finTwoEquiv.symm (prefixRelation v i)
  let D (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2)
      (v : Prefix k (m+q+1)) : ℝ :=
    if prefixRuleDefect (windowTable (m+q) m hmR ρ β rightmost) v then 1 else 0
  let bad (v : Prefix k (m+q+1)) :=
    ¬ Function.Injective (word (m := m) (k := q+1) (V v))
  obtain ⟨_, _, _, hQ, hrow, hπ, hπsum, _, _⟩ := parry_stationary_law k hk
  have hw : ∀ (l : ℕ) (s : State k) (v : Fin l → State k),
      0 ≤ pathWeight k (parryParameter k) l s v := by
    intro l
    induction l with
    | zero => intro s v; exact zero_le_one
    | succ l ih => intro s v; exact mul_nonneg (hQ _ _) (ih _ _)
  have hP (v) : 0 ≤ P v := mul_nonneg (hπ v.1) (hw _ _ _)
  have hrows : ∀ (l : ℕ) (s : State k),
      (∑ v : Fin l → State k, pathWeight k (parryParameter k) l s v) = 1 := by
    intro l
    induction l with
    | zero => intro s; simp [pathWeight]
    | succ l ih =>
      intro s
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (l+1) => State k)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      exact hrow s
  have htotal : ∑ v, P v = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [P, referenceLaw]
    simp_rw [← Finset.mul_sum, hrows, mul_one]
    exact hπsum
  have hcollision (a b : Fin (q+2)) (hab : a < b) :
      (∑ v : Prefix k (m+q+1),
        if word (m := m) (k := q+1) (V v) a = word (m := m) (k := q+1) (V v) b
        then P v else 0) ≤ parryParameter k^(m-1) := by
    have he (v : Prefix k (m+q+1)) :
        word (m := m) (k := q+1) (V v) a = word (m := m) (k := q+1) (V v) b ↔
          Collision m a.val b.val (by omega) (by omega) v.1 v.2 := by
      simp only [funext_iff, word, V, Equiv.apply_eq_iff_eq, Collision]
      rfl
    simp_rw [he]
    rw [← Finset.sum_filter]
    exact parry_overlapping_collision k hk (m+q+1) m a.val b.val hm hab (by omega)
  have hpoint (v : Prefix k (m+q+1)) :
      (if bad v then (1:ℝ) else 0) ≤
        ∑ b : Fin (q+2), ∑ a ∈ Finset.Iio b,
          if word (m := m) (k := q+1) (V v) a = word (m := m) (k := q+1) (V v) b
          then (1:ℝ) else 0 := by
    by_cases hv : bad v
    · have hn : ¬ Function.Injective (word (m := m) (k := q+1) (V v)) := hv
      simp only [Function.Injective, not_forall] at hn
      obtain ⟨a,b,hab⟩ := hn
      have he : word (m := m) (k := q+1) (V v) a =
          word (m := m) (k := q+1) (V v) b ∧ a ≠ b := by tauto
      have hex : ∃ a b : Fin (q+2), a < b ∧ word (m := m) (k := q+1) (V v) a =
          word (m := m) (k := q+1) (V v) b := by
        rcases lt_or_gt_of_ne he.2 with h | h
        · exact ⟨a,b,h,he.1⟩
        · exact ⟨b,a,h,he.1.symm⟩
      obtain ⟨a,b,hab,he⟩ := hex
      rw [if_pos hv]
      calc
        1 = if word (m := m) (k := q+1) (V v) a =
            word (m := m) (k := q+1) (V v) b then (1:ℝ) else 0 := by simp [he]
        _ ≤ ∑ a ∈ Finset.Iio b,
            if word (m := m) (k := q+1) (V v) a = word (m := m) (k := q+1) (V v) b
            then (1:ℝ) else 0 := by
          apply Finset.single_le_sum (s := Finset.Iio b)
            (f := fun i : Fin (q+2) => if word (m := m) (k := q+1) (V v) i =
              word (m := m) (k := q+1) (V v) b then (1:ℝ) else 0)
          · intro i _; split_ifs <;> norm_num
          · exact Finset.mem_Iio.mpr hab
        _ ≤ _ := by
          apply Finset.single_le_sum (s := Finset.univ)
            (f := fun b : Fin (q+2) => ∑ a ∈ Finset.Iio b,
              if word (m := m) (k := q+1) (V v) a =
                word (m := m) (k := q+1) (V v) b then (1:ℝ) else 0)
          · intro b _; apply Finset.sum_nonneg; intro a _; split_ifs <;> norm_num
          · exact Finset.mem_univ b
    · rw [if_neg hv]
      apply Finset.sum_nonneg
      intro b _
      apply Finset.sum_nonneg
      intro a _
      split_ifs <;> norm_num
  have hcount : (∑ b : Fin (q+2), (Finset.Iio b).card) = (q+2).choose 2 := by
    simp only [Fin.card_Iio]
    rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id, Nat.choose_two_right]
  have hbad : (∑ v, P v * if bad v then 1 else 0) ≤
      ((q+2).choose 2 : ℝ) * parryParameter k^(m-1) := by
    calc
      _ ≤ ∑ v : Prefix k (m+q+1), P v *
          ∑ b : Fin (q+2), ∑ a ∈ Finset.Iio b,
            if word (m := m) (k := q+1) (V v) a = word (m := m) (k := q+1) (V v) b
            then (1:ℝ) else 0 :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hpoint v) (hP v)
      _ = ∑ b : Fin (q+2), ∑ a ∈ Finset.Iio b,
          ∑ v : Prefix k (m+q+1),
            if word (m := m) (k := q+1) (V v) a = word (m := m) (k := q+1) (V v) b
            then P v else 0 := by
        simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_comm
      _ ≤ ∑ b : Fin (q+2), ∑ _a ∈ Finset.Iio b, parryParameter k^(m-1) := by
        apply Finset.sum_le_sum
        intro b _
        apply Finset.sum_le_sum
        intro a ha
        exact hcollision a b (Finset.mem_Iio.mp ha)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast hcount
  have hright (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2)
      (w : Fin (m+q) → Fin 2) (hw : Function.Injective (word (m := m) (k := q) w)) :
      rightmostTable m q ρ β w = table m q ρ β w := by
    have hq : Function.Injective (fun i : Fin (q+1) => rank ρ (word w i)) := by
      intro i j h
      apply hw
      exact ρ.injective ((Fintype.equivFin _).injective (Fin.ext h))
    have hs : rightmostSelect (fun i => rank ρ (word w i)) =
        select (fun i => rank ρ (word w i)) := by
      apply hq
      have hmax := Finset.max'_mem
        (Finset.univ.filter (fun i : Fin (q+1) => rank ρ (word w i) =
          Finset.univ.inf' Finset.univ_nonempty (fun i => rank ρ (word w i))))
        (by obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
              (fun i : Fin (q+1) => rank ρ (word w i))
            exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩)
      have hmin := Finset.min'_mem
        (Finset.univ.filter (fun i : Fin (q+1) => rank ρ (word w i) =
          Finset.univ.inf' Finset.univ_nonempty (fun i => rank ρ (word w i))))
        (by obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
              (fun i : Fin (q+1) => rank ρ (word w i))
            exact ⟨i, Finset.mem_filter.mpr ⟨hi, he.symm⟩⟩)
      exact (Finset.mem_filter.mp hmax).2.trans (Finset.mem_filter.mp hmin).2.symm
    simp only [rightmostTable, table, hs]
  have htable (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2)
      (v : Fin (m+q) → Bool)
      (hv : Function.Injective (word (m := m) (k := q) (fun i => finTwoEquiv.symm (v i)))) :
      windowTable (m+q) m hmR ρ β rightmost v =
        finTwoEquiv (table m q ρ β (fun i => finTwoEquiv.symm (v i))) := by
    have aux (t : ℕ) (ht : t = q) :
        finTwoEquiv ((if rightmost then rightmostTable m t ρ β else table m t ρ β)
          (fun i => finTwoEquiv.symm (v ⟨i.val, by omega⟩))) =
          finTwoEquiv (table m q ρ β (fun i => finTwoEquiv.symm (v i))) := by
      subst t
      cases rightmost
      · rfl
      · simp only [↓reduceIte, hright ρ β _ hv]
    exact aux (m+q-m) (by omega)
  have hdefect (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2)
      (v : Prefix k (m+q+1)) (hv : ¬ bad v) :
      D ρ β v = (defect (table m q ρ β) (V v) : ℝ) := by
    have hvinj : Function.Injective (word (m := m) (k := q+1) (V v)) := by
      simpa only [bad, not_not] using hv
    have hlword (i : Fin (q+1)) :
        word (m := m) (k := q) (fun i => V v i.castSucc) i =
          word (m := m) (k := q+1) (V v) i.castSucc := rfl
    have hrword (i : Fin (q+1)) :
        word (m := m) (k := q) (fun i => V v i.succ) i =
          word (m := m) (k := q+1) (V v) i.succ := by
      funext j
      apply congrArg (V v)
      apply Fin.ext
      simp
      omega
    have hl : Function.Injective (word (m := m) (k := q) (fun i => V v i.castSucc)) := by
      intro a b he
      apply Fin.castSucc_injective
      apply hvinj
      simpa only [hlword] using he
    have hr : Function.Injective (word (m := m) (k := q) (fun i => V v i.succ)) := by
      intro a b he
      apply Fin.succ_injective
      apply hvinj
      simpa only [hrword] using he
    have hb (x y : Fin 2) (z : Bool) :
        (if xor (xor (finTwoEquiv x) (finTwoEquiv y)) (!z) then (1:ℝ) else 0) =
        ((if paritySign x = paritySign (finTwoEquiv.symm z) * paritySign y
          then 0 else 1 : ℚ) : ℝ) := by
      fin_cases x <;> fin_cases y <;> cases z <;> norm_num [finTwoEquiv, paritySign]
    simp only [D, prefixRuleDefect, htable ρ β _ hr, htable ρ β _ hl, defect, V]
    exact hb _ _ _
  have hstation (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2) :
      stationaryDefect k (m+q) (windowTable (m+q) m hmR ρ β rightmost) =
        ∑ v, P v * D ρ β v := by
    unfold stationaryDefect
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [D]
    split_ifs <;> simp [P]
  have hlabel (v : Fin (m+q+1) → Fin 2) (ρ : Equiv.Perm (Fin m → Fin 2)) :
      defect (table m q ρ (fun _ => 0)) v ≤
        2 * (𝔼 β : (Fin m → Fin 2) → Fin 2, defect (table m q ρ β) v) := by
    let v₀ : Fin (m+q) → Fin 2 := fun i => v i.castSucc
    let v₁ : Fin (m+q) → Fin 2 := fun i => v i.succ
    let a := select (fun i => rank ρ (word v₀ i))
    let b := select (fun i => rank ρ (word v₁ i))
    let A := word v₀ a
    let B := word v₁ b
    let T₀ : ℤ := ∏ j ∈ Finset.univ.filter
      (fun j : Fin (m+q) => a.val+m ≤ j.val), paritySign (v₀ j)
    let T₁ : ℤ := ∏ j ∈ Finset.univ.filter
      (fun j : Fin (m+q) => b.val+m ≤ j.val), paritySign (v₁ j)
    have hsign (β : (Fin m → Fin 2) → Fin 2) (w : Fin (m+q) → Fin 2) :
        paritySign (table m q ρ β w) =
          paritySign (β (word w (select (fun i => rank ρ (word w i))))) *
          ∏ j ∈ Finset.univ.filter (fun j : Fin (m+q) =>
            (select (fun i => rank ρ (word w i))).val+m ≤ j.val), paritySign (w j) := by
      let c := select (fun i => rank ρ (word w i))
      have hp := prod_paritySign_cases
        (Finset.univ.filter (fun j : Fin (m+q) => c.val+m ≤ j.val)) w
      have hbval : β (word w c) = 0 ∨ β (word w c) = 1 := by omega
      dsimp [c] at hp hbval
      rcases hp with hp | hp <;> rcases hbval with hbval | hbval <;>
        simp only [table, hp, hbval] <;> norm_num [paritySign]
    have hD (β : (Fin m → Fin 2) → Fin 2) :
        defect (table m q ρ β) v =
          if paritySign (β B) * T₁ =
            paritySign (v (Fin.last (m+q))) * (paritySign (β A) * T₀)
          then 0 else 1 := by
      unfold defect
      rw [hsign β v₁, hsign β v₀]
    have ht₀ : T₀ = -1 ∨ T₀ = 1 := prod_paritySign_cases _ _
    have ht₁ : T₁ = -1 ∨ T₁ = 1 := prod_paritySign_cases _ _
    have hlast : v (Fin.last (m+q)) = 0 ∨ v (Fin.last (m+q)) = 1 := by omega
    by_cases hAB : A = B
    · have he (β : (Fin m → Fin 2) → Fin 2) :
          defect (table m q ρ β) v = defect (table m q ρ (fun _ => 0)) v := by
        rw [hD, hD, hAB]
        have hb : β B = 0 ∨ β B = 1 := by omega
        rcases ht₀ with ht₀ | ht₀ <;> rcases ht₁ with ht₁ | ht₁ <;>
          rcases hlast with hlast | hlast <;> rcases hb with hb | hb <;>
          norm_num [ht₀, ht₁, hlast, hb, paritySign]
      simp_rw [he, Fintype.expect_const]
      have hn : 0 ≤ defect (table m q ρ (fun _ => 0)) v := by
        unfold defect; split_ifs <;> norm_num
      linarith
    · let flip (β : (Fin m → Fin 2) → Fin 2) :=
        Function.update β B (Equiv.swap (0 : Fin 2) 1 (β B))
      have hflipflip (β : (Fin m → Fin 2) → Fin 2) : flip (flip β) = β := by
        funext w
        by_cases hw : w = B
        · subst w; simp [flip]
        · simp [flip, hw]
      have hpair (β : (Fin m → Fin 2) → Fin 2) :
          defect (table m q ρ β) v + defect (table m q ρ (flip β)) v = 1 := by
        rw [hD, hD]
        have hfa : flip β A = β A := by simp [flip, hAB]
        have hfb : flip β B = Equiv.swap (0 : Fin 2) 1 (β B) := by simp [flip]
        rw [hfa, hfb]
        have hba : β A = 0 ∨ β A = 1 := by omega
        have hbb : β B = 0 ∨ β B = 1 := by omega
        rcases ht₀ with ht₀ | ht₀ <;> rcases ht₁ with ht₁ | ht₁ <;>
          rcases hba with hba | hba <;> rcases hbb with hbb | hbb <;>
          rcases hlast with hlast | hlast <;>
          norm_num [ht₀, ht₁, hba, hbb, hlast, paritySign]
      have heq : (𝔼 β, defect (table m q ρ (flip β)) v) =
          𝔼 β, defect (table m q ρ β) v :=
        Fintype.expect_bijective flip (Function.Involutive.bijective hflipflip) _ _ (fun _ => rfl)
      have hsum : 2 * (𝔼 β, defect (table m q ρ β) v) = 1 := by
        calc
          _ = (𝔼 β, defect (table m q ρ β) v) +
              (𝔼 β, defect (table m q ρ (flip β)) v) := by rw [heq]; ring
          _ = 𝔼 β, (defect (table m q ρ β) v + defect (table m q ρ (flip β)) v) :=
            (Finset.expect_add_distrib ..).symm
          _ = 1 := by simp_rw [hpair]; exact Fintype.expect_const _
      rw [hsum]
      unfold defect
      split_ifs <;> norm_num
  have hgood (v : Prefix k (m+q+1)) (hv : ¬ bad v) :
      (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), 𝔼 β : (Fin m → Fin 2) → Fin 2,
        (defect (table m q ρ β) (V v) : ℝ)) = 1 / (q+2 : ℝ) := by
    have h := good_context_average m q hm (V v) (by simpa [bad] using hv)
    simp only [Finset.expect_eq_sum_div_card] at h ⊢
    have hc := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at hc
    exact hc
  have hcontext (v : Prefix k (m+q+1)) :
      (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), 𝔼 β : (Fin m → Fin 2) → Fin 2,
        D ρ β v) ≤
          1 / (q+2 : ℝ) + if bad v then 1 else 0 := by
    by_cases hv : bad v
    · rw [if_pos hv]
      have ht : (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), 𝔼 β : (Fin m → Fin 2) → Fin 2,
          D ρ β v) ≤ 1 := by
        apply Finset.expect_le Finset.univ_nonempty
        intro ρ _
        apply Finset.expect_le Finset.univ_nonempty
        intro β _
        dsimp [D]
        split_ifs <;> norm_num
      exact ht.trans (le_add_of_nonneg_left (by positivity))
    · simp_rw [hdefect _ _ v hv]
      rw [hgood v hv, if_neg hv, add_zero]
  have havg : (𝔼 ρ : Equiv.Perm (Fin m → Fin 2), 𝔼 β : (Fin m → Fin 2) → Fin 2,
      stationaryDefect k (m+q) (windowTable (m+q) m hmR ρ β rightmost)) ≤
        1 / (q+2 : ℝ) + ((q+2).choose 2 : ℝ) * parryParameter k^(m-1) := by
    simp_rw [hstation, Finset.expect_sum_comm, ← Finset.mul_expect]
    calc
      _ ≤ ∑ v, P v * (1 / (q+2 : ℝ) + if bad v then 1 else 0) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hcontext v) (hP v)
      _ = 1 / (q+2 : ℝ) + ∑ v, P v * if bad v then 1 else 0 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, htotal, one_mul]
      _ ≤ _ := add_le_add le_rfl hbad
  have hfirst : ∃ (ρ : Equiv.Perm (Fin m → Fin 2)) (β : (Fin m → Fin 2) → Fin 2),
      stationaryDefect k (m+q) (windowTable (m+q) m hmR ρ β rightmost) ≤
        1 / (q+2 : ℝ) + ((q+2).choose 2 : ℝ) * parryParameter k^(m-1) := by
    obtain ⟨ρ,_,hρ⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty havg
    obtain ⟨β,_,hβ⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty hρ
    exact ⟨ρ,β,hβ⟩
  have hcontext0 (v : Prefix k (m+q+1)) :
      (𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
        D ρ (fun _ => 0) v) ≤
          2 / (q+2 : ℝ) + if bad v then 1 else 0 := by
    by_cases hv : bad v
    · rw [if_pos hv]
      have ht : (𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
          D ρ (fun _ => 0) v) ≤ 1 := by
        apply Finset.expect_le Finset.univ_nonempty
        intro ρ _
        dsimp [D]
        split_ifs <;> norm_num
      exact ht.trans (le_add_of_nonneg_left (by positivity))
    · rw [if_neg hv, add_zero]
      simp_rw [hdefect _ _ v hv]
      calc
        _ ≤ 𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
            2 * (𝔼 β : (Fin m → Fin 2) → Fin 2,
              (defect (table m q ρ β) (V v) : ℝ)) := by
          apply Finset.expect_le_expect
          intro ρ _
          have h := hlabel (V v) ρ
          simp only [Finset.expect_eq_sum_div_card] at h ⊢
          exact_mod_cast h
        _ = _ := by rw [← Finset.mul_expect, hgood v hv]; ring
  have havg0 : (𝔼 ρ : Equiv.Perm (Fin m → Fin 2),
      stationaryDefect k (m+q) (windowTable (m+q) m hmR ρ (fun _ => 0) rightmost)) ≤
        2 / (q+2 : ℝ) + ((q+2).choose 2 : ℝ) * parryParameter k^(m-1) := by
    simp_rw [hstation, Finset.expect_sum_comm, ← Finset.mul_expect]
    calc
      _ ≤ ∑ v, P v * (2 / (q+2 : ℝ) + if bad v then 1 else 0) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hcontext0 v) (hP v)
      _ = 2 / (q+2 : ℝ) + ∑ v, P v * if bad v then 1 else 0 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, htotal, one_mul]
      _ ≤ _ := add_le_add le_rfl hbad
  refine ⟨?_, ?_⟩
  · simpa only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_ofNat] using hfirst
  · obtain ⟨ρ,_,hρ⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty havg0
    refine ⟨ρ, ?_⟩
    simpa only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_ofNat] using hρ

#print axioms parry_window_upper_bound
end D5.S3.TotalVariation.ParryWindowUpperBound
