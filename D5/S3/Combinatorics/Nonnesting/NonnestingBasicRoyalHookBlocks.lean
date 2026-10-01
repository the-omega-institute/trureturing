/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks
   mirror-E: none(waiver:royal-hook-block-classification)
   anchors: []
   utility: none
   digest: Classifies triple-avoiding permutations by recursive hook blocks. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHooks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHookBlocks

open D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHooks

def hookBlocks : ℕ → List ℕ → List ℕ
  | _, [] => []
  | n, k :: ks =>
      List.ofFn (fun i : Fin (k - 1) => n - i.val - 1) ++ [n] ++
        hookBlocks (n - k) ks
theorem avoids_has_hook_blocks (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n))
    (h123 : ¬ NonnestingDefs.Occurs [1, 2, 3] p)
    (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p) :
    ∃ ks : List ℕ, (∀ k ∈ ks, 0 < k) ∧ ks.sum = n ∧ p = hookBlocks n ks := by
  classical
  have maximum_prefix_values (n : ℕ) (p : List ℕ)
      (hp : p.Perm (List.range' 1 n))
      (h123 : ¬ NonnestingDefs.Occurs [1, 2, 3] p)
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (m : ℕ) (hm : m < p.length)
      (hmax : ∀ k (hk : k < p.length), k ≠ m → p[k] < p[m]) :
      ∀ i (hi : i < m), p[i]'(by omega) + i + 1 = n := by
    have hnodup : p.Nodup := (hp.nodup_iff).mpr List.nodup_range'
    obtain ⟨hprefix, hdom⟩ :=
      maximum_hook_structure p hnodup h123 h132 m hm hmax
    have hnpos : 0 < n := by
      have hlen := hp.length_eq; simp only [List.length_range'] at hlen; omega
    have hnmem : n ∈ p := hp.symm.subset
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    let rmax := p.idxOf n; have hrmax : rmax < p.length := List.idxOf_lt_length_of_mem hnmem
    have hrmaxv : p[rmax] = n :=
      (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hnmem)).2
    have hmupper : p[m] < 1 + n :=
      (List.mem_range'_1.mp (hp.subset (List.getElem_mem hm))).2
    have hrmaxeq : rmax = m := by
      by_contra hne
      have hlt := hmax rmax hrmax hne; omega
    have hmval : p[m] = n := by simpa [hrmaxeq] using hrmaxv
    have hbase (h0 : 0 < m) : p[0] + 1 = n := by
      have hzero : 0 < p.length := by omega
      have hbelow : p[0] < n := by
        simpa [hmval] using hmax 0 hzero (by omega)
      by_contra hne
      have hgap : p[0] + 1 < n := by omega
      have hzrange : p[0] + 1 ∈ List.range' 1 n :=
        List.mem_range'_1.mpr ⟨by omega, by omega⟩
      have hzmem : p[0] + 1 ∈ p := hp.symm.subset hzrange; let r := p.idxOf (p[0] + 1)
      have hr : r < p.length := List.idxOf_lt_length_of_mem hzmem; have hrv : p[r] = p[0] + 1 :=
        (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hzmem)).2
      by_cases hrm : r < m
      · by_cases hr0 : r = 0
        · have heq : p[0] = p[0] + 1 := by simpa [hr0] using hrv
          omega
        · have hlt := hprefix 0 r hzero hr (by omega) hrm
          omega
      · by_cases hrmeq : r = m
        · have heq : p[m] = p[0] + 1 := by simpa [hrmeq] using hrv
          omega
        · have hlt := hdom 0 r hzero hr h0 (by omega)
          omega
    have hstep (i : ℕ) (hi : i + 1 < m) :
        p[i + 1] + 1 = p[i] := by
      have hil : i < p.length := by omega
      have his : i + 1 < p.length := by omega
      have hdesc := hprefix i (i + 1) hil his (by omega) hi
      by_contra hne
      have hgap : p[i + 1] + 1 < p[i] := by omega
      have hiupper : p[i] < 1 + n :=
        (List.mem_range'_1.mp (hp.subset (List.getElem_mem hil))).2
      have hzrange : p[i + 1] + 1 ∈ List.range' 1 n :=
        List.mem_range'_1.mpr ⟨by omega, by omega⟩
      have hzmem : p[i + 1] + 1 ∈ p := hp.symm.subset hzrange; let r := p.idxOf (p[i + 1] + 1)
      have hr : r < p.length := List.idxOf_lt_length_of_mem hzmem; have hrv : p[r] = p[i + 1] + 1 :=
        (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hzmem)).2
      by_cases hrm : r < m
      · by_cases hri : r ≤ i
        · by_cases heq : r = i
          · have hv : p[i] = p[i + 1] + 1 := by simpa [heq] using hrv
            omega
          · have hlt := hprefix r i hr hil (by omega) (by omega)
            omega
        · by_cases heq : r = i + 1
          · have hv : p[i + 1] = p[i + 1] + 1 := by simpa [heq] using hrv
            omega
          · have hlt := hprefix (i + 1) r his hr (by omega) hrm
            omega
      · by_cases heq : r = m
        · have hv : p[m] = p[i + 1] + 1 := by simpa [heq] using hrv
          have himax : p[i] < p[m] := hmax i hil (by omega); omega
        · have hlt := hdom (i + 1) r his hr hi (by omega)
          omega
    intro i
    induction i with
    | zero =>
      intro hi
      simpa using hbase hi
    | succ i ih =>
      intro hi
      have him : i < m := by omega
      have hprev := ih him; have hnext := hstep i hi; omega
  have maximum_suffix_perm (n : ℕ) (p : List ℕ)
      (hp : p.Perm (List.range' 1 n))
      (h123 : ¬ NonnestingDefs.Occurs [1, 2, 3] p)
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (m : ℕ) (hm : m < p.length)
      (hmax : ∀ k (hk : k < p.length), k ≠ m → p[k] < p[m]) :
      (p.drop (m + 1)).Perm (List.range' 1 (n - m - 1)) := by
    have hlen : p.length = n := by simpa using hp.length_eq
    have hmn : m < n := by omega
    have hnmem : n ∈ p := hp.symm.subset
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    let rmax := p.idxOf n; have hrmax : rmax < p.length := List.idxOf_lt_length_of_mem hnmem
    have hrmaxv : p[rmax] = n :=
      (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hnmem)).2
    have hmupper : p[m] < n + 1 :=
      by simpa [Nat.add_comm] using
        (List.mem_range'_1.mp (hp.subset (List.getElem_mem hm))).2
    have hrmaxeq : rmax = m := by
      by_contra hne
      have hlt := hmax rmax hrmax hne; omega
    have hmval : p[m] = n := by simpa [hrmaxeq] using hrmaxv
    have hprefix := maximum_prefix_values n p hp h123 h132 m hm hmax
    have hsubset : List.range' 1 (n - m - 1) ⊆ p.drop (m + 1) := by
      intro a ha
      have harange : 1 ≤ a ∧ a < n - m := by
        have h := List.mem_range'_1.mp ha; omega
      have hap : a ∈ p := hp.symm.subset
        (List.mem_range'_1.mpr ⟨harange.1, by omega⟩)
      let r := p.idxOf a; have hr : r < p.length := List.idxOf_lt_length_of_mem hap
      have hrv : p[r] = a :=
        (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hap)).2
      have hmr : m < r := by
        by_contra hnot
        by_cases hrm : r = m
        · have heq : a = n := by simpa [hrm, hmval] using hrv.symm
          omega
        · have hpre := hprefix r (by omega : r < m)
          rw [hrv] at hpre; omega
      apply List.mem_iff_getElem.mpr
      have hindex : r - (m + 1) < (p.drop (m + 1)).length := by
        simp only [List.length_drop]; omega
      refine ⟨r - (m + 1), hindex, ?_⟩
      rw [List.getElem_drop]
      have heq : m + 1 + (r - (m + 1)) = r := by omega
      simpa only [heq] using hrv
    have hsubperm := List.subperm_of_subset List.nodup_range' hsubset
    obtain ⟨q, hqperm, hqsub⟩ := List.subperm_iff.mp hsubperm
    have hqlen : q.length = (List.range' 1 (n - m - 1)).length := by
      have hqdrop := hqperm.length_eq
      simp only [List.length_drop, List.length_range'] at hqdrop ⊢; omega
    have hq : List.range' 1 (n - m - 1) = q := hqsub.eq_of_length hqlen.symm
    simpa only [hq] using hqperm.symm
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hpnil : p = [] := List.eq_nil_of_length_eq_zero (by
        simpa using hp.length_eq)
      exact ⟨[], by simp, by simp, by simp [hpnil, hookBlocks]⟩
    · have hnpos : 0 < n := by omega
      have hnmem : n ∈ p := hp.symm.subset
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      let m := p.idxOf n; have hm : m < p.length := List.idxOf_lt_length_of_mem hnmem
      have hmval : p[m] = n :=
        (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hnmem)).2
      have hnodup : p.Nodup := (hp.nodup_iff).mpr List.nodup_range'
      have hmax : ∀ k (hk : k < p.length), k ≠ m → p[k] < p[m] := by
        intro k hk hkm
        have hupper : p[k] < n + 1 := by
          simpa [Nat.add_comm] using
            (List.mem_range'_1.mp (hp.subset (List.getElem_mem hk))).2
        have hne : p[k] ≠ p[m] := by
          intro heq; exact hkm ((hnodup.getElem_inj_iff (hi := hk) (hj := hm)).mp heq)
        omega
      let q := p.drop (m + 1); have hqperm : q.Perm (List.range' 1 (n - m - 1)) :=
        maximum_suffix_perm n p hp h123 h132 m hm hmax
      have hqavoid (σ : List ℕ) (hσ : ¬ NonnestingDefs.Occurs σ p) :
          ¬ NonnestingDefs.Occurs σ q := by
        intro hocc
        obtain ⟨x, hxlt, hxmem, hxsub, _⟩ := hocc
        apply hσ
        refine ⟨x, hxlt, ?_, ?_, by simp⟩
        · intro i hi hik
          exact List.mem_of_mem_drop (hxmem i hi hik)
        · exact hxsub.trans (List.drop_sublist _ _)
      have hq123 := hqavoid [1, 2, 3] h123; have hq132 := hqavoid [1, 3, 2] h132
      have hsmall : n - m - 1 < n := by omega
      obtain ⟨ks, hpos, hsum, hform⟩ := ih (n - m - 1) hsmall q hqperm hq123 hq132
      have hprefix := maximum_prefix_values n p hp h123 h132 m hm hmax
      have hlen : p.length = n := by simpa using hp.length_eq
      have hprefixList : p.take m =
          List.ofFn (fun i : Fin m => n - i.val - 1) := by
        apply List.ext_getElem
        · simp [List.length_take, hlen, Nat.min_eq_left (by omega : m ≤ n)]
        · intro i hi1 hi2
          have hpi := hprefix i (by
            simp only [List.length_take] at hi1
            omega)
          simp only [List.getElem_take, List.getElem_ofFn]; omega
      have hsplit : p = p.take m ++ [n] ++ q := by
        calc
          p = p.take m ++ p.drop m := (List.take_append_drop m p).symm
          _ = p.take m ++ (p[m] :: p.drop (m + 1)) := by
            rw [← List.cons_getElem_drop_succ]
          _ = p.take m ++ [n] ++ q := by simp [hmval, q]
      refine ⟨(m + 1) :: ks, ?_, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · omega
        · exact hpos k hk
      · simp only [List.sum_cons]
        omega
      · rw [hsplit, hprefixList, hform]
        have hrem : n - m - 1 = n - (m + 1) := by omega
        simp [hookBlocks, hrem]
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHookBlocks

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalHookBlocks.avoids_has_hook_blocks
