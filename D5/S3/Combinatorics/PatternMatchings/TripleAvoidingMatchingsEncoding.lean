/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding
   mirror-E: none(waiver:ordered-queue-encoding)
   anchors: []
   utility: none
   digest: The scan action word uniquely determines an avoiding matching. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs

/-- Distinct labels retain the two different closures available at height two. -/
inductive Action
  | opening
  | oldest
  | second
  deriving DecidableEq

/-- Record an opening or the rank of the closed arc. For an avoider, the scan
characterization guarantees that any closure with an older open arc is second-oldest. -/
noncomputable def encode {n : ℕ} (m : Matching n) : Fin (2 * n) → Action :=
  fun v => if v < m.1 v then .opening else
    if ∃ x, x < m.1 v ∧ v ≤ m.1 x then .second else .oldest

/-- Completed pairs determine the open queue at the next cut. Strong induction
then reconstructs each closing partner from its oldest/second-oldest label. -/
theorem encode_injective {n : ℕ} (m m' : Matching n)
    (hm : AvoidsP1 m) (hm' : AvoidsP1 m') (he : encode m = encode m') : m = m' := by
  classical
  have inv : ∀ v, m.1 (m.1 v) = v := fun v => (m.2 v).1
  have inv' : ∀ v, m'.1 (m'.1 v) = v := fun v => (m'.2 v).1
  have neq : ∀ v, m.1 v ≠ v := fun v => (m.2 v).2
  have neq' : ∀ v, m'.1 v ≠ v := fun v => (m'.2 v).2
  have ranks := (scan_characterization m).mp hm |>.1
  have ranks' := (scan_characterization m').mp hm' |>.1
  have orientation (v : Fin (2 * n)) : v < m.1 v ↔ v < m'.1 v := by
    have h := congrFun he v
    by_cases h1 : v < m.1 v <;> by_cases h2 : v < m'.1 v
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · simp only [encode, if_pos h1, if_neg h2] at h
      split_ifs at h
    · simp only [encode, if_neg h1, if_pos h2] at h
      split_ifs at h
    · exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
  have closing : ∀ t : ℕ, ∀ v : Fin (2 * n), v.val = t →
      m.1 v < v → m.1 v = m'.1 v := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro v hv hc
      have hc' : m'.1 v < v := by
        have hn := neq' v
        have ho := orientation v
        omega
      have prior (x : Fin (2 * n)) (hxv : x < v) (hcx : m.1 x < v) :
          m.1 x = m'.1 x := by
        by_cases h : m.1 x < x
        · exact ih x.val (by omega) x rfl h
        · have hn := neq x
          have hxm : x < m.1 x := by omega
          have h := ih (m.1 x).val (by omega) (m.1 x) rfl
            (by rw [inv]; exact hxm)
          have hi := congrArg m'.1 h
          rw [inv, inv'] at hi
          exact hi.symm
      have prior' (x : Fin (2 * n)) (hxv : x < v) (hcx : m'.1 x < v) :
          m.1 x = m'.1 x := by
        by_cases h : m'.1 x < x
        · have hmx : m.1 x < x := by
            have hn := neq x
            have ho := orientation x
            omega
          exact ih x.val (by omega) x rfl hmx
        · have hn := neq' x
          have hxm : x < m'.1 x := by omega
          have hcm : m.1 (m'.1 x) < m'.1 x := by
            have hn := neq (m'.1 x)
            have ho := orientation (m'.1 x)
            rw [inv'] at ho
            omega
          have h := ih (m'.1 x).val (by omega) (m'.1 x) rfl hcm
          rw [inv'] at h
          have hi := congrArg m.1 h
          rw [inv] at hi
          exact hi.symm
      have queue (x : Fin (2 * n)) (hx : x < v) : v ≤ m.1 x ↔ v ≤ m'.1 x := by
        constructor
        · intro h
          by_contra h'
          have hp := prior' x hx (by omega)
          omega
        · intro h
          by_contra h'
          have hp := prior x hx (by omega)
          omega
      have qc : v ≤ m'.1 (m.1 v) :=
        (queue (m.1 v) hc).mp (by rw [inv])
      have qd : v ≤ m.1 (m'.1 v) :=
        (queue (m'.1 v) hc').mpr (by rw [inv'])
      have older : (∃ x, x < m.1 v ∧ v ≤ m.1 x) ↔
          (∃ x, x < m'.1 v ∧ v ≤ m'.1 x) := by
        have h := congrFun he v
        simp only [encode, if_neg (not_lt_of_ge hc.le),
          if_neg (not_lt_of_ge hc'.le)] at h
        split_ifs at h with h1 h2 h2
        · exact iff_of_true h1 h2
        · exact iff_of_false h1 h2
      by_cases hcd : m.1 v < m'.1 v
      · by_cases hold : ∃ x, x < m.1 v ∧ v ≤ m.1 x
        · obtain ⟨x, hxc, hxq⟩ := hold
          exact (ranks' v x (m.1 v) hc' hxc hcd
            ((queue x (by omega)).mp hxq) qc).elim
        · exact (hold (older.mpr ⟨m.1 v, hcd, qc⟩)).elim
      · by_cases hdc : m'.1 v < m.1 v
        · by_cases hold : ∃ x, x < m'.1 v ∧ v ≤ m'.1 x
          · obtain ⟨x, hxd, hxq⟩ := hold
            exact (ranks v x (m'.1 v) hc hxd hdc
              ((queue x (by omega)).mpr hxq) qd).elim
          · exact (hold (older.mp ⟨m'.1 v, hdc, qd⟩)).elim
        · omega
  apply Subtype.ext
  funext v
  by_cases h : m.1 v < v
  · exact closing v.val v rfl h
  · have hn := neq v
    have hvm : v < m.1 v := by omega
    have hi := closing (m.1 v).val (m.1 v) rfl (by rw [inv]; exact hvm)
    have hh := congrArg m'.1 hi
    rw [inv, inv'] at hh
    exact hh.symm

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings
