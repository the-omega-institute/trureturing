/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicInitialValues
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicInitialValues
   mirror-E: none(waiver:iterated-maximum-deletion)
   anchors: []
   utility: none
   digest: Restricting a Fishburn avoider to its initial value interval preserves its class. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicParents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicInitialValues

open D5.S3.Combinatorics.Fishburn FishburnDefs FishburnBasicParents

theorem initial_values_avoider (patterns : List (List ℕ)) (n : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n patterns) (cut : ℕ) (hcut : cut ≤ n) :
    p.filter (fun value => value ≤ cut) ∈ avoiders cut patterns := by
  have hfilter_insert (bound : ℕ) (word : List ℕ) (site value : ℕ)
      (hsite : site ≤ word.length) (hvalue : bound < value) :
      (word.insertIdx site value).filter (fun entry => entry ≤ bound) =
        word.filter (fun entry => entry ≤ bound) := by
    induction word generalizing site with
    | nil =>
      have hs : site = 0 := by simpa using hsite
      subst site
      simp [show ¬ value ≤ bound by omega]
    | cons head tail ih =>
      cases site with
      | zero => simp [show ¬ value ≤ bound by omega]
      | succ site =>
        simp only [List.insertIdx_succ_cons, List.filter_cons]
        rw [ih site (by simp only [List.length_cons] at hsite; omega)]
  induction n generalizing cut p with
  | zero =>
    have hc : cut = 0 := by omega
    subst cut
    have hp : p = [] := List.perm_nil.mp hparent.1
    simpa only [hp, List.filter_nil] using hparent
  | succ n ih =>
    by_cases heq : cut = n + 1
    · subst cut
      have hf : p.filter (fun value => value ≤ n + 1) = p := by
        apply List.filter_eq_self.mpr
        intro value hm
        have hr := hparent.1.mem_iff.mp hm
        simp only [List.mem_range', Nat.one_mul] at hr
        obtain ⟨offset, hb, heq⟩ := hr
        simpa only [decide_eq_true_eq] using (show value ≤ n + 1 by omega)
      simpa only [hf] using hparent
    · obtain ⟨entry, heq⟩ := (maximum_insertion_bijection n patterns).2 ⟨p, hparent⟩
      have hp : entry.val.1.insertIdx entry.val.2 (n + 1) = p :=
        congrArg Subtype.val heq
      rw [← hp, hfilter_insert cut entry.val.1 entry.val.2 (n + 1)
        entry.property.2.1 (by omega)]
      exact ih entry.val.1 entry.property.1 cut (by omega)

end D5.S3.Combinatorics.Fishburn.FishburnBasicInitialValues
