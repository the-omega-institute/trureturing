/- GID: D5/S1/Words/AdmissibleWords/KBonacciRightScanHamming
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciRightScanHamming
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Right-scan Hamming estimate and its common-false reset criterion. -/

import D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling

open scoped BigOperators ENNReal NNReal Classical

/-- A common false at the head of an increasing complete free-site scan makes
both updated histories ready for the native reset test. -/
theorem reset_ready_after_false {n : ℕ} (i : Fin n) (rest : List (Fin n))
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hlt : ∀ j ∈ rest, i.val < j.val)
    (hcover : ∀ j : Fin n, j ∉ insert i fixed → j ∈ rest)
    (hfar : ∀ j ∈ fixed, i.val < j.val → x j = y j) :
    resetReady (insert i fixed) (Function.update x i false)
      (Function.update y i false) := by
  refine ⟨i, by simp, by simp, ?_, ?_⟩
  · intro j hji
    by_contra hj
    have := hlt j (hcover j hj)
    omega
  · intro j hj hij
    have hji : j ≠ i := by intro he; subst j; omega
    have hjf : j ∈ fixed := (Finset.mem_insert.mp hj).resolve_left hji
    simpa [Function.update_of_ne hji] using hfar j hjf hij

/-- Increasing scans of the entire unfixed region have expected internal Hamming
cost at most one when the two fixed exteriors agree beyond every scanned site.
The joint law is the supported conditional recursion, stopped by zero screening. -/
theorem right_scan_hamming {k n : ℕ} (hk : 0 < k) (sites : List (Fin n))
    (hn : sites.Nodup) (horder : sites.Pairwise (fun i j => i.val < j.val))
    (fixed : Finset (Fin n)) (hfree : ∀ i ∈ sites, i ∉ fixed)
    (hcover : ∀ i : Fin n, i ∉ fixed → i ∈ sites)
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty)
    (hfar : ∀ i ∈ sites, ∀ j ∈ fixed, i.val < j.val → x j = y j) :
    (∑' w, prefixCoupling sites fixed x y hx hy w * scanHamming sites w) ≤ 1 := by
  change mean (prefixCoupling sites fixed x y hx hy) (scanHamming sites) ≤ 1
  induction sites generalizing fixed x y with
  | nil => simpa only [scanHamming, mean_const] using (zero_le : (0 : ℝ≥0∞) ≤ 1)
  | cons i rest ih =>
    by_cases hr : resetReady fixed x y
    · rw [prefixCoupling, dif_pos hr]
      rw [reset_mean_zero _ _ _ _ _ _ hr.choose_spec.2.2.1 hfree]
      exact zero_le
    have hi := hfree i (by simp)
    have hrn := (List.nodup_cons.mp hn).2
    have hro := (List.pairwise_cons.mp horder).2
    have hlt : ∀ j ∈ rest, i.val < j.val := (List.pairwise_cons.mp horder).1
    have hrf : ∀ j ∈ rest, j ∉ insert i fixed := by
      intro j hj hm
      rcases Finset.mem_insert.mp hm with hji | hjf
      · exact (List.nodup_cons.mp hn).1 (hji ▸ hj)
      · exact hfree j (by simp [hj]) hjf
    have hrc : ∀ j : Fin n, j ∉ insert i fixed → j ∈ rest := by
      intro j hj
      have hjf : j ∉ fixed := fun h => hj (Finset.mem_insert_of_mem h)
      rcases List.mem_cons.mp (hcover j hjf) with hji | hjr
      · exact False.elim (hj (by simp [hji]))
      · exact hjr
    have hsame (a b : Bool) : ∀ j ∈ rest, ∀ t ∈ insert i fixed, j.val < t.val →
        Function.update x i a t = Function.update y i b t := by
      intro j hj t ht hjt
      have hit : t ≠ i := by intro he; subst t; have := hlt j hj; omega
      have htf : t ∈ fixed := (Finset.mem_insert.mp ht).resolve_left hit
      simpa [Function.update_of_ne hit] using hfar j (by simp [hj]) t htf hjt
    let joint := bitCoupling ((completionLaw fixed x hx).map (fun w => w i))
      ((completionLaw fixed y hy).map (fun w => w i))
    let child := fun bits : Bool × Bool =>
      if hx' : (completions k n (insert i fixed) (Function.update x i bits.1)).Nonempty then
        if hy' : (completions k n (insert i fixed) (Function.update y i bits.2)).Nonempty then
          prefixCoupling rest (insert i fixed) (Function.update x i bits.1)
            (Function.update y i bits.2) hx' hy'
        else independentCompletions fixed x y hx hy
      else independentCompletions fixed x y hx hy
    have hb : ∀ bits, joint bits ≠ 0 → mean (child bits) (scanHamming (i :: rest)) ≤
        if bits = (false, false) then 0 else 2 := by
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
      rw [mean_head _ i rest bits.1 bits.2 hbits]
      by_cases hzero : bits = (false, false)
      · have hz : resetReady (insert i fixed) (Function.update x i bits.1)
            (Function.update y i bits.2) := by
          simpa only [hzero] using reset_ready_after_false i rest fixed x y hlt hrc
            (hfar i (by simp))
        have hzmean : mean (child bits) (scanHamming rest) = 0 := by
          rw [hc, prefixCoupling.eq_def, dif_pos hz]
          exact reset_mean_zero rest _ _ _ _ _ hz.choose_spec.2.2.1 hrf
        rw [hzmean]
        simp [hzero]
      · rw [if_neg hzero, hc]
        have hrec := ih hrn hro (insert i fixed) hrf hrc
          (Function.update x i bits.1) (Function.update y i bits.2) hf.1 hf.2
          (hsame bits.1 bits.2)
        calc
          _ ≤ 1 + 1 := add_le_add (by split_ifs <;> norm_num) hrec
          _ = 2 := by norm_num
    rw [prefixCoupling, dif_neg hr]
    change mean (joint.bind child) (scanHamming (i :: rest)) ≤ 1
    rw [mean_bind]
    apply le_trans _ (half_failure_budget joint
      (conditional_step_coupling hk fixed x y hx hy i hi).2.2)
    apply ENNReal.tsum_le_tsum
    intro bits
    by_cases hs : joint bits = 0
    · simp [hs]
    · exact mul_le_mul_right (hb bits hs) _

#print axioms right_scan_hamming
#print axioms reset_ready_after_false

end D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
