/- GID: D5/S1/Digit/Infinite/LegalDigitCoveringNumber
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/LegalDigitCoveringNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The least number of closed digit-distance balls covering legal infinite digits is the Fibonacci prefix count. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.LegalDigitCoveringNumber

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Words.AdmissibleWords.AdmissibleCount

noncomputable def digitDist (theta : ℝ) (x y : LegalDigits) : ℝ :=
  if x = y then 0 else theta ^ PiNat.firstDiff x.val y.val

def covers (theta : ℝ) (L m : ℕ) : Prop :=
  ∃ centers : Fin m → LegalDigits, ∀ x : LegalDigits,
    ∃ i : Fin m, digitDist theta x (centers i) ≤ theta ^ L

/-- The exact minimum cardinality of closed prefix balls in the legal digit space. -/
theorem least_covering_number (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < 1) (L : ℕ) :
    IsLeast {m : ℕ | covers theta L m} (Nat.fib (L + 2)) := by
  have adm_no_adj : ∀ (m : ℕ) (w : Fin m → Bool), Adm m w →
      ∀ i : ℕ, i + 1 < m → ¬ (w ⟨i, by omega⟩ = true ∧ w ⟨i + 1, by omega⟩ = true) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro w hw i hi
        cases m with
        | zero => omega
        | succ m =>
            cases m with
            | zero => omega
            | succ k =>
                rw [adm_two_iff] at hw
                by_cases hi0 : i = 0
                · subst i
                  exact hw.1
                · have hi' : i - 1 + 1 < k + 1 := by omega
                  have ht := ih (k + 1) (by omega) (Fin.tail w) hw.2 (i - 1) hi'
                  simpa [Fin.tail, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)] using ht
  have prefix_adm : ∀ (m : ℕ) (x : LegalDigits),
      Adm m (fun i : Fin m => x.val i.1) := by
    intro m x
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        cases m with
        | zero => simp [Adm]
        | succ m =>
            cases m with
            | zero => simp [Adm]
            | succ k =>
                rw [adm_two_iff]
                constructor
                · intro h
                  exact x.property 0 ⟨h.1, by simpa using h.2⟩
                · apply ih (k + 1) (by omega)
                  intro i
                  exact x.val (i.succ)
  let extend : ∀ (w : Fin L → Bool), Adm L w → LegalDigits := fun w hw =>
    ⟨fun n => if h : n < L then w ⟨n, h⟩ else false, by
      intro n hn
      by_cases hL : n + 1 < L
      · have hna := adm_no_adj L w hw n (by omega)
        exact hna (by simpa [hL] using hn)
      · simp [hL]
    ⟩
  have extend_prefix : ∀ (w : Fin L → Bool) (hw : Adm L w),
      (fun i : Fin L => (extend w hw).val i.1) = w := by
    intro w hw
    funext i
    simp [extend]
  have dist_prefix : ∀ (x y : LegalDigits),
      digitDist theta x y ≤ theta ^ L →
      (fun i : Fin L => x.val i.1) = (fun i : Fin L => y.val i.1) := by
    intro x y hxy
    by_cases hEq : x = y
    · simp [hEq]
    · unfold digitDist at hxy
      rw [dif_neg hEq] at hxy
      by_contra hne
      have hfd : PiNat.firstDiff x.val y.val < L := by
        by_contra hnot
        exact hne (funext fun i => PiNat.apply_eq_of_lt_firstDiff (by omega))
      have hpow : theta ^ L < theta ^ PiNat.firstDiff x.val y.val :=
        pow_lt_pow_right_of_lt_one₀ hθ0 hθ1 hfd
      linarith
  constructor
  · let words := {w : Fin L → Bool // Adm L w}
    let e : words ≃ Fin (Nat.fib (L + 2)) :=
      (Fintype.equivFin words)
    refine ⟨fun i => extend (e.symm i).val (e.symm i).property, ?_⟩
    intro x
    let w : words := ⟨fun i => x.val i.1, prefix_adm L x⟩
    let i : Fin (Nat.fib (L + 2)) := e ⟨w, w.property⟩
    refine ⟨i, ?_⟩
    have hp : (fun j : Fin L => x.val j.1) =
        (fun j : Fin L => (extend (e.symm i).val (e.symm i).property).val j.1) := by
      rw [show e.symm i = ⟨w, w.property⟩ by simp [i, e]]
      exact (extend_prefix w.val w.property).symm
    have hfirst : ∀ j < L, x.val j =
        (extend (e.symm i).val (e.symm i).property).val j := by
      intro j hj
      have := congrFun hp ⟨j, hj⟩
      simpa using this
    by_cases hEq : x = extend (e.symm i).val (e.symm i).property
    · simp [digitDist, hEq]
    · unfold digitDist
      rw [dif_neg hEq]
      have hfd : L ≤ PiNat.firstDiff x.val
          (extend (e.symm i).val (e.symm i).property).val := by
        by_contra hlt
        have := PiNat.apply_firstDiff_ne hEq hlt
        exact this (hfirst _ hlt)
      exact pow_le_pow_right_of_le_one₀ hθ0.le hfd
  · intro hcover
    rcases hcover with ⟨centers, hcenters⟩
    intro m hm
    by_contra hlt
    have hcard : Fintype.card {w : Fin L → Bool // Adm L w} ≤ m := by
      let f : {w : Fin L → Bool // Adm L w} → Fin m := fun w =>
        Classical.choose (hcenters (extend w.val w.property))
      have hf : Function.Injective f := by
        intro w v hfv
        have hw := Classical.choose_spec (hcenters (extend w.val w.property))
        have hv := Classical.choose_spec (hcenters (extend v.val v.property))
        have hpw := dist_prefix _ _ hw
        have hpv := dist_prefix _ _ hv
        apply Subtype.ext
        have : w.val = v.val := by
          calc
            w.val = (fun i : Fin L => (extend w.val w.property).val i.1) := (extend_prefix w.val w.property).symm
            _ = (fun i : Fin L => (centers (f w)).val i.1) := hpw.trans (by rfl)
            _ = (fun i : Fin L => (extend v.val v.property).val i.1) := by rw [hfv]; exact hpv.symm
            _ = v.val := extend_prefix v.val v.property
        exact this
      exact Fintype.card_le_of_injective f hf
    rw [admissibleWord_card_eq_fib] at hcard
    omega

end D5.S1.Digit.Infinite.LegalDigitCoveringNumber
