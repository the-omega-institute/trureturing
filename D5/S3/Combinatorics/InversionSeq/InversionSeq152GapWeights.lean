/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152GapWeights
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152GapWeights
   mirror-E: none(waiver:top-gap-isolation)
   anchors: []
   utility: none
   digest: Reverse induction isolates the top nonzero jump of a nondecreasing word. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152GapCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152GapWeights

theorem gap_weight_isolation (internal top : ℕ → ℕ)
    (hint0 : internal 0 = 0) (htop0 : top 0 = 0) :
    ∀ word : List ℕ, ∀ previous : ℕ, word.Pairwise (· ≤ ·) →
      (∀ value ∈ word, previous ≤ value) →
      let maximum := word.getLastD previous
      let jumps := (word.zipWith (· - ·) (previous :: word)).filter (· != 0)
      (word.zipWith (fun value prior => if value = maximum then top (value - prior)
        else internal (value - prior)) (previous :: word)).sum =
      ((jumps.dropLast.map internal).sum) + top (jumps.getLastD 0) := by
  have hzip (function : ℕ → ℕ → ℕ) : ∀ word : List ℕ, ∀ previous value : ℕ,
      (word ++ [value]).zipWith function (previous :: (word ++ [value])) =
      word.zipWith function (previous :: word) ++ [function value (word.getLastD previous)] := by
    intro word
    induction word with
    | nil => intro previous value; simp
    | cons first rest ih =>
      intro previous value
      simpa only [List.cons_append, List.zipWith_cons_cons, List.getLastD_cons]
        using congrArg (List.cons (function first previous)) (ih first value)
  have hlast (word : List ℕ) (previous : ℕ) (hsorted : word.Pairwise (· ≤ ·)) :
      ∀ value ∈ word, value ≤ word.getLastD previous := by
    induction word using List.reverseRecOn with
    | nil => simp
    | append_singleton word last _ =>
      intro value hv
      simp only [List.getLastD_concat]
      rcases List.mem_append.mp hv with hv | hv
      · exact (List.pairwise_append.mp hsorted).2.2 value hv last (by simp)
      · simp only [List.mem_singleton] at hv
        subst value
        exact le_rfl
  have hfilterSum : ∀ word : List ℕ,
      ((word.filter (· != 0)).map internal).sum = (word.map internal).sum := by
    intro word
    induction word with
    | nil => rfl
    | cons value rest ih =>
      by_cases hz : value = 0
      · subst value; simp [hint0, ih]
      · simp [hz, ih]
  have hplain : ∀ word : List ℕ, ∀ previous maximum : ℕ,
      (∀ value ∈ word, value ≠ maximum) →
      (word.zipWith (fun value prior => if value = maximum then top (value - prior)
        else internal (value - prior)) (previous :: word)).sum =
      ((word.zipWith (· - ·) (previous :: word)).map internal).sum := by
    intro word
    induction word with
    | nil => simp
    | cons value rest ih =>
      intro previous maximum hall
      have hv := hall value (by simp)
      have ht := ih value maximum (fun entry he => hall entry (by simp [he]))
      simpa [hv] using congrArg (internal (value - previous) + ·) ht
  intro word
  induction word using List.reverseRecOn with
  | nil => intro previous _ _; simp [htop0]
  | append_singleton word value ih =>
    intro previous hsorted hall
    have hp := (List.pairwise_append.mp hsorted).1
    have hprev : ∀ entry ∈ word, previous ≤ entry :=
      fun entry he => hall entry (List.mem_append_left _ he)
    have hvalue : previous ≤ value := hall value (by simp)
    have hlastLe : word.getLastD previous ≤ value := by
      induction word using List.reverseRecOn with
      | nil => simpa using hvalue
      | append_singleton rest last _ =>
        simp only [List.getLastD_concat]
        exact (List.pairwise_append.mp hsorted).2.2 last (by simp) value (by simp)
    dsimp only
    rw [List.getLastD_concat, hzip, hzip, List.filter_append]
    by_cases heq : word.getLastD previous = value
    · simp only [heq, Nat.sub_self, List.filter_cons, List.filter_nil,
        bne_self_eq_false, Bool.false_eq_true, ite_false, List.append_nil,
        ite_true, List.sum_append, List.sum_singleton, htop0, Nat.add_zero]
      simpa only [heq] using ih previous hp hprev
    · have hdelta : value - word.getLastD previous ≠ 0 := by omega
      have hn : ∀ entry ∈ word, entry ≠ value := by
        intro entry he
        have hh := hlast word previous hp entry he
        omega
      have hh := (hplain word previous value hn).trans
        (hfilterSum (word.zipWith (· - ·) (previous :: word))).symm
      have hb : (value - word.getLastD previous != 0) = true := by
        simp only [bne_iff_ne]; exact hdelta
      simp only [List.filter_cons, List.filter_nil, hb, ite_true,
        List.dropLast_concat, List.getLastD_concat, List.sum_append, List.sum_singleton]
      exact congrArg (· + top (value - word.getLastD previous)) hh
end D5.S3.Combinatorics.InversionSeq.InversionSeq152GapWeights
