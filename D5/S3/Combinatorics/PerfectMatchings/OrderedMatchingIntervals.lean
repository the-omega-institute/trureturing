/- GID: D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/OrderedMatchingIntervals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Basic]
   utility: none
   digest: Label transport across closed matching intervals. -/
import D5.S3.Combinatorics.PerfectMatchings.OrderedMatchingCore

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CupCapBridgeProposal
namespace NCMatching

variable {n : ℕ} (M : NCMatching n)

/-- Every strict matched interval is partner-closed. -/
theorem interior_closed (a t : Fin n) (hat : a < t) (htp : t < M.partner a) :
    a < M.partner t ∧ M.partner t < M.partner a := by
  have hhi : ¬ M.partner a < M.partner t :=
    fun h => M.noncrossing a t hat htp h
  have hlo : ¬ M.partner t < a := by
    intro h
    exact M.noncrossing (M.partner t) a h
      (by simpa only [M.involutive t] using hat)
      (by simpa only [M.involutive t] using htp)
  have hnhi : M.partner t ≠ M.partner a := by
    intro h
    have := M.partner.injective h
    omega
  have hnlo : M.partner t ≠ a := by
    intro h
    have h' := congrArg M.partner h
    rw [M.involutive t] at h'
    omega
  constructor <;> omega

/-- Closure of a half-open interval of endpoint indices; its ends are gaps. -/
def IntervalClosed (l r : Fin (n + 1)) : Prop :=
  ∀ t : Fin n, l.val ≤ t.val → t.val < r.val →
    l.val ≤ (M.partner t).val ∧ (M.partner t).val < r.val

/-- A suffix left after removing the first matched block is still closed. -/
theorem interval_suffix_closed {l r : Fin (n + 1)}
    (hlr : l < r) (hc : M.IntervalClosed l r) :
    let k : Fin n := ⟨l.val, by have := r.isLt; omega⟩
    M.IntervalClosed (M.partner k).succ r := by
  dsimp only
  let k : Fin n := ⟨l.val, by have := r.isLt; omega⟩
  change M.IntervalClosed (M.partner k).succ r
  have hk := hc k (by simp [k]) (by simpa [k] using hlr)
  intro t hlt htr
  change (M.partner k).val + 1 ≤ t.val at hlt
  change t.val < r.val at htr
  change l.val ≤ (M.partner k).val ∧ (M.partner k).val < r.val at hk
  have ht := hc t (by omega) htr
  refine ⟨?_, ht.2⟩
  by_contra hh
  change l.val ≤ (M.partner t).val ∧ (M.partner t).val < r.val at ht
  change ¬ ((M.partner k).val + 1 ≤ (M.partner t).val) at hh
  have hkp : k.val < (M.partner k).val := by
    have hne : (M.partner k).val ≠ k.val := by
      intro he
      exact M.noFixed k (Fin.ext he)
    have hne' : (M.partner k).val ≠ l.val := by simpa [k] using hne
    have hkl : k.val = l.val := rfl
    omega
  have htp : (M.partner t).val ≤ (M.partner k).val := by omega
  have hne₁ : (M.partner t).val ≠ k.val := by
    intro he
    have he' : M.partner t = k := Fin.ext he
    have hp := congrArg M.partner he'
    rw [M.involutive t] at hp
    have hp' := congrArg Fin.val hp
    omega
  have hne₂ : (M.partner t).val ≠ (M.partner k).val := by
    intro he
    have he' : M.partner t = M.partner k := Fin.ext he
    have hp := M.partner.injective he'
    have hp' := congrArg Fin.val hp
    omega
  have hlow : k < M.partner t := by
    change k.val < (M.partner t).val
    have hne₁' : (M.partner t).val ≠ l.val := by simpa [k] using hne₁
    have hkl : k.val = l.val := rfl
    omega
  have hhigh : M.partner t < M.partner k := by
    change (M.partner t).val < (M.partner k).val
    omega
  have hi := M.interior_closed k (M.partner t) hlow hhigh
  rw [M.involutive t] at hi
  exact (by omega : False)

/-- The actual boundary-label transport through any closed noncrossing interval.
The induction removes the *first matched block*, not a scalar or a face premise.
In particular it applies to intervals containing arbitrarily many other arcs. -/
theorem closed_interval_gap {L : Type*} (x : Fin (n + 1) → L)
    (hx : Compatible M x) (l r : Fin (n + 1)) (hlr : l ≤ r)
    (hc : M.IntervalClosed l r) : x l = x r := by
  suffices haux : ∀ d : ℕ, ∀ l r : Fin (n + 1), l ≤ r →
      r.val - l.val = d → M.IntervalClosed l r → x l = x r by
    exact haux (r.val - l.val) l r hlr rfl hc
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro l r hlr hlen hc
    by_cases he : l = r
    · exact congrArg x he
    have hlt : l < r := by omega
    let k : Fin n := ⟨l.val, by have := r.isLt; omega⟩
    have hkl : k.castSucc = l := Fin.ext rfl
    have hk := hc k (by simp [k]) (by simpa [k] using hlt)
    have hneq := M.noFixed k
    have hkp : k.val < (M.partner k).val := by
      have : k.val = l.val := rfl
      omega
    have hcut : (M.partner k).succ ≤ r := by
      change (M.partner k).val + 1 ≤ r.val
      omega
    have hsmaller : r.val - (M.partner k).succ.val < d := by
      have : k.val = l.val := rfl
      simp only [Fin.val_succ]
      omega
    have hs : M.IntervalClosed (M.partner k).succ r := by
      simpa only [k] using M.interval_suffix_closed hlt hc
    calc
      x l = x (M.partner k).succ := by
        rw [← hkl]
        exact (hx k).1
      _ = x r := ih (r.val - (M.partner k).succ.val) hsmaller
        (M.partner k).succ r hcut rfl hs

end NCMatching
end CupCapBridgeProposal
