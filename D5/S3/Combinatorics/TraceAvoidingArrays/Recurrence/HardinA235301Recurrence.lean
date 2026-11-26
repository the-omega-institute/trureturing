/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Recurrence.hardin_a235301; premises=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Certificate.initial_certificate
   digest: Hardin A235301 common order-ten recurrence on both axes. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate

/-! Hardin A235301 common order-ten recurrence on both axes. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Encoding
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Transfer
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Certificate
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet (C)
open scoped BigOperators

set_option warningAsError true

private lemma residual_relation (h : ℕ) (f : State → ℤ) :
    evalHist (residualHist (h+2)) f =
      -3 * evalHist (residualHist (h+1)) f - 2 * evalHist (residualHist h) f := by
  induction h generalizing f with
  | zero =>
    change evalHist (residualHist 2) f =
      -3 * evalHist (residualHist 1) f - 2 * evalHist (residualHist 0) f
    rw [initial_certificate.1]
    simp only [eval_normalize, eval_append, eval_scale]
    ring
  | succ h ih =>
    change evalHist (residualHist ((h+2)+1)) f =
      -3 * evalHist (residualHist ((h+1)+1)) f - 2 * evalHist (residualHist (h+1)) f
    simpa only [eval_residual_succ] using ih (action f)

private lemma residual_zero_for_mask (h : ℕ) (f : ℕ → ℤ) :
    evalHist (residualHist h) (fun s => f s.mask) = 0 := by
  let e (h : ℕ) := evalHist (residualHist h) (fun s => f s.mask)
  have bases : e 0 = 0 ∧ e 1 = 0 := by
    constructor
    · simp only [e, ← eval_group, initial_certificate.2.1, eval_nil]
    · simp only [e, ← eval_group, initial_certificate.2.2, eval_nil]
  have main (h : ℕ) : e h = 0 ∧ e (h+1) = 0 := by
    induction h with
    | zero => exact bases
    | succ h ih =>
      refine ⟨ih.2, ?_⟩
      change e (h+2) = 0
      have hr : e (h+2) = -3 * e (h+1) - 2 * e h :=
        residual_relation h (fun s => f s.mask)
      rw [hr, ih.1, ih.2]
      simp
  exact (main h).1

/-- The signed recurrence from the pinned A235292 record, at index n. -/
private def RecursAt (a : ℕ → ℤ) (n : ℕ) : Prop :=
  a n = 3*a (n-1) + 17*a (n-2) - 57*a (n-3) - 86*a (n-4) +
    372*a (n-5) + 76*a (n-6) - 972*a (n-7) + 360*a (n-8) +
    864*a (n-9) - 576*a (n-10)

private theorem row_recurrence_shifted (h w : ℕ) (hw : 0 < w) :
    (C 3 3 (h+11) w : ℤ) = 3*(C 3 3 (h+10) w : ℤ) + 17*(C 3 3 (h+9) w : ℤ) - 57*(C 3 3 (h+8) w : ℤ) - 86*(C 3 3 (h+7) w : ℤ) +
    372*(C 3 3 (h+6) w : ℤ) + 76*(C 3 3 (h+5) w : ℤ) - 972*(C 3 3 (h+4) w : ℤ) + 360*(C 3 3 (h+3) w : ℤ) +
    864*(C 3 3 (h+2) w : ℤ) - 576*(C 3 3 (h+1) w : ℤ) := by
  have hz := residual_zero_for_mask h (value w)
  simp only [residualHist, eval_normalize, coefficients, eval_append, eval_scale] at hz
  have he (i : ℕ) :
      evalHist (path (h+i+1)) (fun s => value w s.mask) = (C 3 3 (h+i+1) w : ℤ) :=
    (count_transfer (h+i+1) w (by omega) hw).symm
  simp only [he 0, he 1, he 2, he 3, he 4, he 5, he 6, he 7, he 8, he 9, he 10] at hz
  change 1*(C 3 3 (h+11) w : ℤ) + -3*(C 3 3 (h+10) w : ℤ) + -17*(C 3 3 (h+9) w : ℤ) + 57*(C 3 3 (h+8) w : ℤ) +
    86*(C 3 3 (h+7) w : ℤ) + -372*(C 3 3 (h+6) w : ℤ) + -76*(C 3 3 (h+5) w : ℤ) + 972*(C 3 3 (h+4) w : ℤ) +
    -360*(C 3 3 (h+3) w : ℤ) + -864*(C 3 3 (h+2) w : ℤ) + 576*(C 3 3 (h+1) w : ℤ) = 0 at hz
  linear_combination hz

/-- Hardin's published A235301 common order-ten recurrence, for every positive
fixed side parameter and at every index at least eleven, in both coordinates. -/
theorem hardin_a235301 (k n : ℕ) (hk : 1 ≤ k) (hn : 11 ≤ n) :
    (C 3 3 n k : ℤ) = 3 * (C 3 3 (n-1) k : ℤ) + 17 * (C 3 3 (n-2) k : ℤ) -
      57 * (C 3 3 (n-3) k : ℤ) - 86 * (C 3 3 (n-4) k : ℤ) +
      372 * (C 3 3 (n-5) k : ℤ) + 76 * (C 3 3 (n-6) k : ℤ) -
      972 * (C 3 3 (n-7) k : ℤ) + 360 * (C 3 3 (n-8) k : ℤ) +
      864 * (C 3 3 (n-9) k : ℤ) - 576 * (C 3 3 (n-10) k : ℤ) ∧
    (C 3 3 k n : ℤ) = 3 * (C 3 3 k (n-1) : ℤ) + 17 * (C 3 3 k (n-2) : ℤ) -
      57 * (C 3 3 k (n-3) : ℤ) - 86 * (C 3 3 k (n-4) : ℤ) +
      372 * (C 3 3 k (n-5) : ℤ) + 76 * (C 3 3 k (n-6) : ℤ) -
      972 * (C 3 3 k (n-7) : ℤ) + 360 * (C 3 3 k (n-8) : ℤ) +
      864 * (C 3 3 k (n-9) : ℤ) - 576 * (C 3 3 k (n-10) : ℤ) := by
  have hrow : RecursAt (fun i => (C 3 3 i k : ℤ)) n := by
    let h := n - 11
    unfold RecursAt
    dsimp only
    have hindex : n = h+11 := by
      dsimp [h]
      omega
    rw [hindex]
    simp only [show (h+11)-1 = h+10 by omega, show (h+11)-2 = h+9 by omega,
      show (h+11)-3 = h+8 by omega, show (h+11)-4 = h+7 by omega,
      show (h+11)-5 = h+6 by omega, show (h+11)-6 = h+5 by omega,
      show (h+11)-7 = h+4 by omega, show (h+11)-8 = h+3 by omega,
      show (h+11)-9 = h+2 by omega, show (h+11)-10 = h+1 by omega]
    exact row_recurrence_shifted h k hk
  refine ⟨hrow, ?_⟩
  have he (i : ℕ) : (C 3 3 k i : ℤ) = (C 3 3 i k : ℤ) := by rw [count_symm k i]
  simpa only [RecursAt, he] using hrow

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235301Recurrence
