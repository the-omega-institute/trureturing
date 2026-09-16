/- GID: D5/S3/Observer/Monodromy/TransvectionHistoryObservability
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TransvectionHistoryObservability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual bounded pulse histories have exactly the observation kernel of a directed pairing ball. -/

import D5.S3.Observer.Monodromy.TransvectionLieFiltration
import Mathlib.Tactic

/-!
# Exact observation kernels of controlled rank-one histories

Reuse the actual increment, Walk and Within objects. The observer reads a row
of H; a pulse is multiplication by I + increment H i. All pulse labels are
available. The theorem compares actual output equalities on all bounded words
with coordinate equalities on the independently defined directed graph ball.
It does not follow by applying the Lie-layer theorem: finite products act on
states here, whereas that theorem concerns spans of matrix commutators.

The general statement needs neither invertibility nor skew symmetry. Its
Hamiltonian interpretation requires a real nonsingular alternating H. Quantum
interpretations additionally require a CCR representation and unitary covariance;
the theorem does not assert quantum-state tomography or noninvasive measurement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TransvectionHistoryObservability

open D5.S3.Observer.Monodromy.TransvectionLieFiltration

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- A concrete linear readout of the phase state. -/
def readout (H : Matrix I I K) (a : I) (x : I → K) : K :=
  ∑ j, H a j * x j

/-- The actual rank-one pulse, not an abstract graph transition. -/
def pulse (H : Matrix I I K) (i : I) (x : I → K) : I → K :=
  (1 + increment H i).mulVec x

/-- Composition order: the head pulse is applied after the tail. -/
def history (H : Matrix I I K) : List I → (I → K) → (I → K)
  | [], x => x
  | i :: w, x => pulse H i (history H w x)

/-- Equality for every available control word of length at most k, including empty. -/
def SameHistory (H : Matrix I I K) (a : I) (k : ℕ) (x y : I → K) : Prop :=
  ∀ w : List I, w.length ≤ k →
    readout H a (history H w x) = readout H a (history H w y)

/-- Exact bounded-history indistinguishability, with both directions proved from
actual pulse products. The pairing graph may be directed, singular or disconnected. -/
theorem history_kernel_eq_pairing_ball (H : Matrix I I K) (a : I)
    (k : ℕ) (x y : I → K) :
    SameHistory H a k x y ↔
      ∀ j, Within H k a j → readout H j x = readout H j y := by
  classical
  have pulse_entry (i r : I) (z : I → K) :
      pulse H i z r = z r + if r = i then readout H i z else 0 := by
    change (∑ c, ((1 : Matrix I I K) r c + increment H i r c) * z c) = _
    simp only [add_mul, Finset.sum_add_distrib]
    have hid : (∑ c, (1 : Matrix I I K) r c * z c) = z r := by
      simp [Matrix.one_apply]
    rw [hid]
    by_cases hr : r = i
    · subst r
      simp [increment, readout]
    · simp [increment, hr]
  have read_pulse (b i : I) (z : I → K) :
      readout H b (pulse H i z) =
        readout H b z + H b i * readout H i z := by
    unfold readout
    simp_rw [pulse_entry]
    simp [mul_add, Finset.sum_add_distrib, mul_ite, readout]
  have one_edge (b i : I) (n : ℕ) (he : H b i ≠ 0)
      (h : SameHistory H b (n+1) x y) : SameHistory H i n x y := by
    intro w hw
    have htail := h w (hw.trans (Nat.le_succ n))
    have hhead := h (i :: w) (by simpa using Nat.add_le_add_right hw 1)
    change readout H b (pulse H i (history H w x)) =
      readout H b (pulse H i (history H w y)) at hhead
    rw [read_pulse, read_pulse, htail] at hhead
    exact mul_left_cancel₀ he (add_left_cancel hhead)
  have walk_transfer : ∀ {d : ℕ} {b j : I}, Walk H d b j →
      ∀ n, SameHistory H b (d+n) x y → SameHistory H j n x y := by
    intro d b j p
    induction p with
    | nil b =>
        intro n h
        simpa using h
    | @snoc d b u j p he ih =>
        intro n h
        apply one_edge u j n he
        apply ih (n+1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have prepend : ∀ {d : ℕ} {b j : I}, Walk H d b j →
      ∀ v, H v b ≠ 0 → Walk H (d+1) v j := by
    intro d b j p
    induction p with
    | nil b =>
        intro v hv
        exact Walk.snoc (Walk.nil v) hv
    | snoc p he ih =>
        intro v hv
        simpa [Nat.add_assoc] using Walk.snoc (ih v hv) he
  have output_agree : ∀ (w : List I) (b : I),
      (∀ j, Within H w.length b j → readout H j x = readout H j y) →
      readout H b (history H w x) = readout H b (history H w y) := by
    intro w
    induction w with
    | nil =>
        intro b h
        exact h b ⟨0, by simp, Walk.nil b⟩
    | cons i w ih =>
        intro b h
        simp only [List.length_cons] at h
        change readout H b (pulse H i (history H w x)) =
          readout H b (pulse H i (history H w y))
        rw [read_pulse, read_pulse]
        have hb : readout H b (history H w x) = readout H b (history H w y) := by
          apply ih b
          intro j hj
          rcases hj with ⟨d, hd, p⟩
          exact h j ⟨d, by omega, p⟩
        rw [hb]
        by_cases he : H b i = 0
        · simp [he]
        · have hi : readout H i (history H w x) = readout H i (history H w y) := by
            apply ih i
            intro j hj
            rcases hj with ⟨d, hd, p⟩
            exact h j ⟨d+1, by omega, prepend p b he⟩
          rw [hi]
  constructor
  · intro h j hj
    rcases hj with ⟨d, hd, p⟩
    have hsmall : SameHistory H a (d+0) x y := by
      intro w hw
      exact h w (by omega)
    have hout := walk_transfer p 0 hsmall
    simpa [history] using hout [] (by simp)
  · intro h w hw
    apply output_agree w a
    intro j hj
    rcases hj with ⟨d, hd, p⟩
    exact h j ⟨d, hd.trans hw, p⟩

#print axioms history_kernel_eq_pairing_ball

end D5.S3.Observer.Monodromy.TransvectionHistoryObservability
