/- GID: D5/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciSupportedCoalescence
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Supported common-false coalescence of the native conditional prefix coupling. -/

import D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming

/-! Coalescence concerns complete outputs of the original stopped recursion. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling

private theorem reset_supported_agreement {k n : ℕ} (sites : List (Fin n))
    (fixed : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty)
    (hfree : ∀ i ∈ sites, i ∉ fixed) (hr : resetReady fixed x y)
    (w : (Fin n → Bool) × (Fin n → Bool))
    (hw : prefixCoupling sites fixed x y hx hy w ≠ 0) :
    ∀ i ∈ sites, w.1 i = w.2 i := by
  rw [prefixCoupling.eq_def, dite_eq_left hr, resetCoupling] at hw
  obtain ⟨u, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp
    hw
  rw [← he]
  intro i hi
  have hcut : ¬ i.val ≤ hr.choose.val :=
    fun h => hfree i hi (hr.choose_spec.2.2.1 i h)
  simp [resetMap, hcut]

/-- Every supported full output of the unchanged native coupling coalesces at
all scanned positions at or after an emitted common false. -/
theorem prefix_coupling_supported_coalescence {k n : ℕ} (hk : 0 < k)
    (sites : List (Fin n)) (hn : sites.Nodup)
    (horder : sites.Pairwise (fun i j => i.val < j.val))
    (fixed : Finset (Fin n)) (hfree : ∀ i ∈ sites, i ∉ fixed)
    (hcover : ∀ i : Fin n, i ∉ fixed → i ∈ sites)
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty)
    (hfar : ∀ i ∈ sites, ∀ j ∈ fixed, i.val < j.val → x j = y j) :
    ∀ w : (Fin n → Bool) × (Fin n → Bool),
      prefixCoupling sites fixed x y hx hy w ≠ 0 →
      ∀ r q : Fin sites.length, r ≤ q →
        w.1 (sites.get r) = false → w.2 (sites.get r) = false →
        w.1 (sites.get q) = w.2 (sites.get q) := by
  classical
  induction sites generalizing fixed x y with
  | nil =>
    intro w hw r
    exact Fin.elim0 r
  | cons i rest ih =>
    intro w hw r q hrq hx0 hy0
    by_cases hr : resetReady fixed x y
    · exact reset_supported_agreement (i :: rest) fixed x y hx hy hfree hr w hw
        _ (List.get_mem _ _)
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
    rw [prefixCoupling.eq_def, dite_eq_right hr] at hw
    obtain ⟨bits, hs, hc⟩ := (PMF.mem_support_bind_iff _ _ _).mp
      hw
    have hf := bitCoupling_supported_fibers fixed x y hx hy i hi bits
      hs
    simp only [dite_eq_left hf.1, dite_eq_left hf.2] at hc
    have hw' := hc
    by_cases hq : q.val = 0
    · have he : r = q := Fin.ext (by have := r.isLt; omega)
      subst r
      exact hx0.trans hy0.symm
    let qt : Fin rest.length := ⟨q.val - 1, by have := q.isLt; simp only [List.length_cons] at *; omega⟩
    have hqe : q = qt.succ := Fin.ext (by simp [qt]; omega)
    by_cases hr0 : r.val = 0
    · have hre : r = 0 := Fin.ext hr0
      have hxhead : w.1 i = false := by simpa [hre] using hx0
      have hyhead : w.2 i = false := by simpa [hre] using hy0
      have hm := prefix_coupling_marginals hk rest hrn (insert i fixed) hrf
        (Function.update x i bits.1) (Function.update y i bits.2) hf.1 hf.2
      have hbits := coupled_fixed _ _ _ hf.1 hf.2 _ hm w hw' i (by simp)
      have hb1 : bits.1 = false := by simpa only [Function.update_self] using hbits.1.symm.trans hxhead
      have hb2 : bits.2 = false := by simpa only [Function.update_self] using hbits.2.symm.trans hyhead
      have hz : resetReady (insert i fixed) (Function.update x i bits.1)
          (Function.update y i bits.2) := by
        rw [hb1, hb2]
        exact reset_ready_after_false i rest fixed x y hlt hrc (hfar i (by simp))
      have he := reset_supported_agreement rest (insert i fixed)
        (Function.update x i bits.1) (Function.update y i bits.2) hf.1 hf.2 hrf hz w hw'
        (rest.get qt) (List.get_mem _ _)
      simpa only [hqe, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] using he
    · let rt : Fin rest.length := ⟨r.val - 1, by have := r.isLt; simp only [List.length_cons] at *; omega⟩
      have hre : r = rt.succ := Fin.ext (by simp [rt]; omega)
      have hrt : rt ≤ qt := by change r.val - 1 ≤ q.val - 1; exact Nat.sub_le_sub_right hrq 1
      have hxrest : w.1 (rest.get rt) = false := by simpa only [hre, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] using hx0
      have hyrest : w.2 (rest.get rt) = false := by simpa only [hre, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] using hy0
      have he := ih hrn hro (insert i fixed) hrf hrc
        (Function.update x i bits.1) (Function.update y i bits.2) hf.1 hf.2
        (hsame bits.1 bits.2) w hw' rt qt hrt hxrest hyrest
      simpa only [hqe, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] using he

#print axioms prefix_coupling_supported_coalescence
#print axioms reset_ready_after_false

end D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
