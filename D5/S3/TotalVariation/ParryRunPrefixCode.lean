/- GID: D5/S3/TotalVariation/ParryRunPrefixCode
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryRunPrefixCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Parry run words are prefix-free at each fixed run count. -/

import D5.S3.TotalVariation.ParrySharedZeroRule

namespace D5.S3.TotalVariation.ParryRunPrefixCode

open D5.S3.TotalVariation.ParrySharedZeroRule

set_option autoImplicit false

/-- For a fixed number of complete zero/one cycles, the actual run words are
prefix-free. All run lengths are positive, with no upper bound. The initial
zero in the boundary belongs to the first run, and each cycle contributes
the first zero of the next run. -/
theorem run_word_prefix_iff (cs ds : List (ℕ × ℕ))
    (hlen : cs.length = ds.length)
    (hcs : ∀ c ∈ cs, 1 ≤ c.1 ∧ 1 ≤ c.2)
    (hds : ∀ d ∈ ds, 1 ≤ d.1 ∧ 1 ≤ d.2) :
    ([true, false] ++ runContinuation cs).IsPrefix
      ([true, false] ++ runContinuation ds) ↔ cs = ds := by
  constructor
  · intro hp
    induction cs generalizing ds with
    | nil =>
      have hd : ds = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      exact hd.symm
    | cons c cs ih =>
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
        obtain ⟨hc0, hc1⟩ := hcs c (by simp)
        obtain ⟨hd0, hd1⟩ := hds d (by simp)
        have htail_len : cs.length = ds.length := by simpa using hlen
        have htail_cs : ∀ a ∈ cs, 1 ≤ a.1 ∧ 1 ≤ a.2 :=
          fun a ha => hcs a (by simp [ha])
        have htail_ds : ∀ a ∈ ds, 1 ≤ a.1 ∧ 1 ≤ a.2 :=
          fun a ha => hds a (by simp [ha])
        have hpre : (runContinuation (c :: cs)).IsPrefix
            (runContinuation (d :: ds)) :=
          (List.prefix_append_right_inj [true, false]).mp hp
        -- The first forced switch recovers the unobserved zeros of this run.
        have hfirst (a : ℕ × ℕ) (as : List (ℕ × ℕ)) (ha : 1 ≤ a.2) :
            (runContinuation (a :: as)).idxOf true = a.1 - 1 := by
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a.2 ≠ 0)
          simp [runContinuation, List.append_assoc, hm, List.replicate_succ,
            List.idxOf_append_of_notMem]
        have hmem : true ∈ runContinuation (c :: cs) := by
          simp [runContinuation, List.mem_replicate]
          exact Or.inl (by omega)
        have hzsub := hpre.idxOf_eq_of_mem hmem
        rw [hfirst c cs hc1, hfirst d ds hd1] at hzsub
        have hz : c.1 = d.1 := by omega
        have hone : (List.replicate c.2 true ++ false :: runContinuation cs).IsPrefix
            (List.replicate d.2 true ++ false :: runContinuation ds) := by
          simpa only [runContinuation, List.flatMap_cons, List.append_assoc,
            List.singleton_append, hz, List.prefix_append_right_inj] using hpre
        -- The closing zero fixes the full one run, even when word lengths differ.
        have hsecond (m : ℕ) (w : List Bool) :
            (List.replicate m true ++ false :: w).idxOf false = m := by
          simp [List.idxOf_append_of_notMem]
        have hm : false ∈ List.replicate c.2 true ++ false :: runContinuation cs := by
          simp
        have ho := hone.idxOf_eq_of_mem hm
        rw [hsecond, hsecond] at ho
        have hrest : (runContinuation cs).IsPrefix (runContinuation ds) := by
          simpa only [ho, List.prefix_append_right_inj, List.prefix_cons_inj] using hone
        have htail : cs = ds := ih ds htail_len htail_cs htail_ds
          ((List.prefix_append_right_inj [true, false]).mpr hrest)
        exact congrArg₂ List.cons (Prod.ext hz ho) htail
  · rintro rfl
    exact List.prefix_refl _

#print axioms run_word_prefix_iff

end D5.S3.TotalVariation.ParryRunPrefixCode
