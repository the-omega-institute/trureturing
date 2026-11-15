/- GID: D5/S1/Words/AdmissibleWords/KBonacciEmittedTail
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciEmittedTail
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Geometric emitted-event tail for the original conditional zero-reset coupling. -/

import D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling

/-! The full-output event is estimated in both reset and recursive branches. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.TerminalSampling
open D5.S1.Words.ClosedRunStarts
open scoped BigOperators ENNReal NNReal Classical

private theorem completion_all_true_card {k n : ℕ} (hk : 0 < k)
    (sites : List (Fin n)) (hn : sites.Nodup)
    (fixed : Finset (Fin n)) (x : Fin n → Bool)
    (hfree : ∀ i ∈ sites, i ∉ fixed) :
    2 ^ sites.length * ((completions k n fixed x).filter
      (fun w => ∀ i ∈ sites, w i = true)).card ≤
      (completions k n fixed x).card := by
  classical
  induction sites generalizing fixed x with
  | nil => simp
  | cons i rest ih =>
    have hi : i ∉ fixed := hfree i (by simp)
    have hn' := List.nodup_cons.mp hn
    have hfree' : ∀ j ∈ rest, j ∉ insert i fixed := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun he => hn'.1 (he ▸ hj), hfree j (by simp [hj])⟩
    have hrec := ih hn'.2 (insert i fixed) (Function.update x i true) hfree'
    have hzero := zero_completion_injection hk fixed x i hi
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := completions k n fixed x) (fun w => w i = false)
    have hnot : ((completions k n fixed x).filter (fun w => ¬ w i = false)) =
        ((completions k n fixed x).filter (fun w => w i = true)) := by
      ext w
      simp
    rw [hnot] at hsplit
    have hhalf : 2 * ((completions k n fixed x).filter (fun w => w i = true)).card ≤
        (completions k n fixed x).card := by omega
    have he : ((completions k n fixed x).filter
          (fun w => ∀ j ∈ i :: rest, w j = true)) =
        ((completions k n (insert i fixed) (Function.update x i true)).filter
          (fun w => ∀ j ∈ rest, w j = true)) := by
      rw [refined_completions fixed x i hi, Finset.filter_filter]
      ext w
      simp
    rw [List.length_cons, he]
    calc
      2 ^ (rest.length + 1) * _ =
          2 * (2 ^ rest.length * ((completions k n (insert i fixed)
            (Function.update x i true)).filter (fun w => ∀ j ∈ rest, w j = true)).card) := by
        ring
      _ ≤ 2 * (completions k n (insert i fixed) (Function.update x i true)).card :=
        Nat.mul_le_mul_left 2 hrec
      _ ≤ (completions k n fixed x).card := by
        rw [refined_completions fixed x i hi]
        exact hhalf

private theorem completion_all_true_probability {k n : ℕ} (hk : 0 < k)
    (sites : List (Fin n)) (hn : sites.Nodup)
    (fixed : Finset (Fin n)) (x : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty)
    (hfree : ∀ i ∈ sites, i ∉ fixed) :
    mean (completionLaw fixed x hx)
      (fun w => if ∀ i ∈ sites, w i = true then 1 else 0) ≤
        (1 / 2 : ℝ≥0∞) ^ sites.length := by
  classical
  have he : mean (completionLaw fixed x hx)
      (fun w => if ∀ i ∈ sites, w i = true then 1 else 0) =
      (((completions k n fixed x).filter (fun w => ∀ i ∈ sites, w i = true)).card : ℝ≥0∞) /
        (completions k n fixed x).card := by
    rw [mean, tsum_fintype]
    simp_rw [completionLaw_apply]
    have hterm : ∀ w : Fin n → Bool,
        (if w ∈ completions k n fixed x then
          ((completions k n fixed x).card : ℝ≥0∞)⁻¹ else 0) *
          (if ∀ i ∈ sites, w i = true then 1 else 0) =
        if w ∈ (completions k n fixed x).filter (fun w => ∀ i ∈ sites, w i = true)
          then ((completions k n fixed x).card : ℝ≥0∞)⁻¹ else 0 := by
      intro w
      by_cases hw : w ∈ completions k n fixed x <;>
        by_cases ht : ∀ i ∈ sites, w i = true <;> simp [hw, ht]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun w => w ∈ (completions k n fixed x).filter
        (fun w => ∀ i ∈ sites, w i = true)) =
        (completions k n fixed x).filter (fun w => ∀ i ∈ sites, w i = true) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hf]
    simp [div_eq_mul_inv]
  rw [he]
  have hc : (2 : ℝ≥0∞)^sites.length *
      (((completions k n fixed x).filter (fun w => ∀ i ∈ sites, w i = true)).card : ℝ≥0∞) ≤
      (completions k n fixed x).card := by
    exact_mod_cast completion_all_true_card hk sites hn fixed x hfree
  have hp : ((completions k n fixed x).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hx.card_pos
  apply (ENNReal.div_le_iff hp (ENNReal.natCast_ne_top _)).mpr
  have hm : (1 / 2 : ℝ≥0∞)^sites.length *
      ((2 : ℝ≥0∞)^sites.length *
        (((completions k n fixed x).filter (fun w => ∀ i ∈ sites, w i = true)).card : ℝ≥0∞)) ≤
      (1 / 2 : ℝ≥0∞)^sites.length * (completions k n fixed x).card := by
    gcongr
  have ht : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    simpa only [one_div] using ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  simpa only [← mul_assoc, ← mul_pow, ht, one_pow, one_mul] using hm

private theorem reset_no_common_false {k n : ℕ} (hk : 0 < k)
    (sites : List (Fin n)) (hn : sites.Nodup)
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty) (z : Fin n)
    (leftFixed : ∀ i : Fin n, i.val ≤ z.val → i ∈ fixed)
    (hfree : ∀ i ∈ sites, i ∉ fixed) :
    mean (resetCoupling fixed x y hx z)
      (fun w => if ∀ i ∈ sites, ¬ (w.1 i = false ∧ w.2 i = false) then 1 else 0) ≤
        (1 / 2 : ℝ≥0∞) ^ sites.length := by
  classical
  rw [resetCoupling, mean_map]
  have he : (fun w : Fin n → Bool =>
      if ∀ i ∈ sites, ¬ (w i = false ∧ resetMap z y w i = false) then (1 : ℝ≥0∞) else 0) =
      (fun w => if ∀ i ∈ sites, w i = true then 1 else 0) := by
    funext w
    have hh : (∀ i ∈ sites, ¬ (w i = false ∧ resetMap z y w i = false)) ↔
        (∀ i ∈ sites, w i = true) := by
      have hd : ∀ i ∈ sites, resetMap z y w i = w i := by
        intro i hi
        have hz : ¬ i.val ≤ z.val := fun h => hfree i hi (leftFixed i h)
        simp [resetMap, hz]
      constructor
      · intro h i hi
        have hp := h i hi
        rw [hd i hi] at hp
        simpa using hp
      · intro h i hi
        simp [hd i hi, h i hi]
    simp only [hh]
  rw [he]
  exact completion_all_true_probability hk sites hn fixed x hx hfree

/-- The emitted no-common-false event of the original joint has a geometric tail. -/
theorem prefix_coupling_emitted_tail {k n : ℕ} (hk : 0 < k)
    (sites : List (Fin n)) (hn : sites.Nodup)
    (fixed : Finset (Fin n)) (hfree : ∀ i ∈ sites, i ∉ fixed)
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty) (j : ℕ) (hj : j ≤ sites.length) :
    mean (prefixCoupling sites fixed x y hx hy)
      (fun w => if ∀ i ∈ sites.take j, ¬ (w.1 i = false ∧ w.2 i = false) then 1 else 0) ≤
        (1 / 2 : ℝ≥0∞)^j := by
  classical
  induction sites generalizing fixed x y j with
  | nil =>
    have hj0 : j = 0 := by simpa using hj
    subst j
    simp [mean_const]
  | cons i rest ih =>
    cases j with
    | zero => simp [mean_const]
    | succ j =>
      by_cases hr : resetReady fixed x y
      · rw [prefixCoupling, dif_pos hr]
        simpa only [List.length_take, Nat.min_eq_left hj] using reset_no_common_false hk ((i :: rest).take (j+1)) hn.take
          fixed x hy.choose hx hr.choose hr.choose_spec.2.2.1
          (fun t ht => hfree t (List.mem_of_mem_take ht))
      have hi := hfree i (by simp)
      have hrn := (List.nodup_cons.mp hn).2
      have hrf : ∀ t ∈ rest, t ∉ insert i fixed := by
        intro t ht hm
        rcases Finset.mem_insert.mp hm with hti | htf
        · exact (List.nodup_cons.mp hn).1 (hti ▸ ht)
        · exact hfree t (by simp [ht]) htf
      let event := fun (s : List (Fin n)) (w : (Fin n → Bool) × (Fin n → Bool)) =>
        if ∀ t ∈ s, ¬ (w.1 t = false ∧ w.2 t = false) then (1 : ℝ≥0∞) else 0
      let joint := bitCoupling ((completionLaw fixed x hx).map (fun w => w i))
        ((completionLaw fixed y hy).map (fun w => w i))
      let child := fun bits : Bool × Bool =>
        if hx' : (completions k n (insert i fixed) (Function.update x i bits.1)).Nonempty then
          if hy' : (completions k n (insert i fixed) (Function.update y i bits.2)).Nonempty then
            prefixCoupling rest (insert i fixed) (Function.update x i bits.1)
              (Function.update y i bits.2) hx' hy'
          else independentCompletions fixed x y hx hy
        else independentCompletions fixed x y hx hy
      have hb : ∀ bits, joint bits ≠ 0 → mean (child bits) (event ((i :: rest).take (j+1))) ≤
          if bits = (false, false) then 0 else (1/2 : ℝ≥0∞)^j := by
        intro bits hs
        have hf := bitCoupling_supported_fibers fixed x y hx hy i hi bits hs
        have hm := prefix_coupling_marginals hk rest hrn (insert i fixed) hrf
          (Function.update x i bits.1) (Function.update y i bits.2) hf.1 hf.2
        have hc : child bits = prefixCoupling rest (insert i fixed)
            (Function.update x i bits.1) (Function.update y i bits.2) hf.1 hf.2 := by
          simp only [child, dif_pos hf.1, dif_pos hf.2]
        have hbits : ∀ w, (child bits) w ≠ 0 → w.1 i = bits.1 ∧ w.2 i = bits.2 := by
          intro w hw
          rw [hc] at hw
          have h := coupled_fixed _ _ _ hf.1 hf.2 _ hm w hw i (by simp)
          simpa only [Function.update_self] using h
        have he : mean (child bits) (event ((i :: rest).take (j+1))) =
            mean (child bits) (fun w => if bits = (false,false) then 0 else event (rest.take j) w) := by
          apply mean_congr_support
          intro w hw
          have hh := hbits w hw
          rcases bits with ⟨a,b⟩
          cases a <;> cases b <;> simp [event, hh.1, hh.2]
        rw [he]
        by_cases hz : bits = (false,false)
        · simp [hz, mean_const]
        · simp only [hz, ite_false]
          rw [hc]
          exact ih hrn (insert i fixed) hrf _ _ hf.1 hf.2 j (by simpa using hj)
      rw [prefixCoupling, dif_neg hr]
      change mean (joint.bind child) (event ((i :: rest).take (j+1))) ≤ _
      rw [mean_bind]
      have hm : mean joint (fun bits => mean (child bits) (event ((i :: rest).take (j+1)))) ≤
          mean joint (fun bits => if bits = (false,false) then 0 else (1/2 : ℝ≥0∞)^j) := by
        apply ENNReal.tsum_le_tsum
        intro bits
        by_cases hs : joint bits = 0
        · simp [hs]
        · exact mul_le_mul_right (hb bits hs) _
      apply hm.trans
      have he : mean joint (fun bits => if bits = (false,false) then 0 else (1/2 : ℝ≥0∞)^j) =
          mean joint (fun bits => if bits = (false,false) then 0 else 2) * (1/2 : ℝ≥0∞)^(j+1) := by
        rw [mean, mean, ← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro bits
        by_cases hz : bits = (false,false)
        · simp [hz]
        · simp only [hz, ite_false, pow_succ]
          have ht : (2 : ℝ≥0∞) * (1/2) = 1 := by
            simpa only [one_div] using ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
          symm
          calc
            _ = joint bits * (1/2 : ℝ≥0∞)^j * (2 * (1/2)) := by ac_rfl
            _ = _ := by rw [ht]; simp
      rw [he]
      have hh := half_failure_budget joint (conditional_step_coupling hk fixed x y hx hy i hi).2.2
      simpa using mul_le_mul_left hh ((1/2 : ℝ≥0∞)^(j+1))

#print axioms prefix_coupling_emitted_tail

end D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
