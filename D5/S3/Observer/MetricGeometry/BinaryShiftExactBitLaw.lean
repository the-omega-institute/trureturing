/- GID: D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw
   generality: I
   mirror-B: D5/B/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: At error in [0,1), binary shift prediction through time H requires exactly H plus one bits. -/

import D5.S3.Observer.MetricGeometry.ContractingDigitMemory
import D5.S3.ObserverMemory.Trajectories.DominanceMemoryUpdate
import Mathlib.Data.Nat.Log

namespace D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.Observer.MetricGeometry.ContractingDigitMemory (prefixStream)
open D5.S3.ObserverMemory.Trajectories.DominanceMemoryUpdate (shiftWindow)

/-- Finite prediction with the same state accounting as full-future prediction,
but with accuracy required only on words of length at most `H`. -/
def HasFiniteHorizonPredictor {X A Y : Type*} [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (H : ℕ) (ε : ℝ) (s : ℕ) : Prop :=
  ∃ (S : Type) (finiteS : Fintype S),
    Nonempty S ∧ @Fintype.card S finiteS ≤ s ∧
      ∃ (e : X → S) (G : A → S → S) (h : S → Y),
        ∀ x w, w.length ≤ H →
          dist (h (runWord G w (e x))) (o (runWord F w x)) ≤ ε

/-- The sign of the leading bit, with false representing zero. -/
def binaryObservation (x : ℕ → Bool) : ℝ := (-1 : ℝ) ^ (x 0).toNat

/-- For every horizon, including zero, and every error in `[0,1)`, the least
autonomous state budget is the number of binary prefixes of length `H+1`.
Its ceiling base-two logarithm is exactly `H+1`. -/
theorem binary_shift_exact_bit_law (H : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    IsLeast {s : ℕ | HasFiniteHorizonPredictor
      (fun (_ : Unit) (x : ℕ → Bool) j => x (j + 1)) binaryObservation H ε s}
      (2 ^ (H + 1)) ∧
    Nat.clog 2 (2 ^ (H + 1)) = H + 1 := by
  classical
  let F : Unit → (ℕ → Bool) → (ℕ → Bool) := fun _ x j => x (j + 1)
  have orbit (w : List Unit) (x : ℕ → Bool) (j : ℕ) :
      runWord F w x j = x (j + w.length) := by
    induction w generalizing x with
    | nil => rfl
    | cons a w ih =>
        simpa [runWord, F, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (F a x)
  let Q := Fin (H + 1) → Bool
  let G : Unit → Q → Q := fun _ q => shiftWindow q false
  have register (w : List Unit) (q : Q) (i : Fin (H + 1))
      (hi : i.val + w.length < H + 1) :
      runWord G w q i = q ⟨i.val + w.length, hi⟩ := by
    induction w generalizing q i with
    | nil => rfl
    | cons a w ih =>
        change runWord G w (G a q) i = _
        rw [ih (G a q) i (by simp only [List.length_cons] at hi; omega)]
        dsimp [G, shiftWindow]
        rw [dif_pos (by simp only [List.length_cons] at hi; omega)]
        congr 1
  have upper : HasFiniteHorizonPredictor F binaryObservation H ε (2 ^ (H + 1)) := by
    refine ⟨Q, inferInstance, inferInstance, ?_,
      (fun x i => x i.val), G, (fun q => (-1 : ℝ) ^ (q 0).toNat), ?_⟩
    · simp [Q]
    · intro x w hw
      have hi : (0 : Fin (H + 1)).val + w.length < H + 1 := by
        simp only [Fin.val_zero]; omega
      dsimp only
      rw [register w (fun i => x i.val) 0 hi]
      simp only [binaryObservation, orbit, Fin.val_zero, Nat.zero_add, dist_self]
      exact hε
  have lower (s : ℕ) (hs : HasFiniteHorizonPredictor F binaryObservation H ε s) :
      2 ^ (H + 1) ≤ s := by
    rcases hs with ⟨S, finiteS, _nonemptyS, hcard, e, δ, h, herr⟩
    let : Fintype S := finiteS
    let initialMap : Q → S := fun q => e (prefixStream (H + 1) q)
    have inj : Function.Injective initialMap := by
      intro u v huv
      funext i
      by_contra hbit
      let w : List Unit := List.replicate i.val ()
      have hw : w.length ≤ H := by simp only [w, List.length_replicate]; omega
      have common : runWord δ w (e (prefixStream (H + 1) u)) =
          runWord δ w (e (prefixStream (H + 1) v)) :=
        congrArg (runWord δ w) huv
      have hu := herr (prefixStream (H + 1) u) w hw
      have hv := herr (prefixStream (H + 1) v) w hw
      have gap : dist
          (binaryObservation (runWord F w (prefixStream (H + 1) u)))
          (binaryObservation (runWord F w (prefixStream (H + 1) v))) ≤ ε + ε := by
        calc
          _ ≤ dist (binaryObservation (runWord F w (prefixStream (H + 1) u)))
                (h (runWord δ w (e (prefixStream (H + 1) u)))) +
              dist (h (runWord δ w (e (prefixStream (H + 1) u))))
                (binaryObservation (runWord F w (prefixStream (H + 1) v))) :=
            dist_triangle _ _ _
          _ ≤ ε + ε := by
            rw [dist_comm (binaryObservation _) _, common]
            exact add_le_add (by simpa [common] using hu) hv
      have read (q : Q) : binaryObservation (runWord F w (prefixStream (H + 1) q)) =
          (-1 : ℝ) ^ (q i).toNat := by
        simp [binaryObservation, orbit, w, prefixStream, i.isLt]
      rw [read u, read v] at gap
      cases hu : u i <;> cases hv : v i <;>
        simp_all [Real.dist_eq] <;> norm_num at gap <;> linarith
    have hcount := Fintype.card_le_of_injective initialMap inj
    have : 2 ^ (H + 1) ≤ Fintype.card S := by simpa [Q] using hcount
    exact this.trans hcard
  exact ⟨⟨upper, lower⟩, Nat.clog_pow 2 (H + 1) (by decide)⟩

#print axioms binary_shift_exact_bit_law

end D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw
