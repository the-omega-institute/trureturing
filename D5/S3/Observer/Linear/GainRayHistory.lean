/- GID: D5/S3/Observer/Linear/GainRayHistory
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayHistory
   mirror-E: none(waiver:literal-real-history-and-fixed-palettes)
   anchors: []
   utility: none
   digest: Literal initial-inclusive M and J histories transfer through unrestricted deterministic decisions. -/

import D5.S3.Observer.Linear.GainRayEvaluation
import D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

abbrev Raw := D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word

def action (a : Bool) : Mat :=
  (D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic a).map (Int.castRingHom ℝ)

/-- False is M, true is J, in chronological list order. -/
def acquisition (w : List Bool) : Mat := (Raw w).map (Int.castRingHom ℝ)

/-- Appending one atom applies that one matrix on the left. -/
theorem acquisition_append (w : List Bool) (a : Bool) :
    acquisition (w ++ [a]) = action a * acquisition w := by
  have h := (D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound w).2.2.2.1 [a]
  simp only [acquisition, h, Matrix.map_mul]
  congr 1
  simp [Raw, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word, action]

/-- A read at its original natural clock; the initial read uses the identity. -/
def readAt {d : ℕ} (W : World d) (w : List Bool) (i : ℕ) : ℝ :=
  (gain d W.coeff).eval (i : ℝ) * Matrix.trace (acquisition (w.take i) * W.source) + W.drift

abbrev History (w : List Bool) := Fin (w.length + 1) → ℝ
abbrev Readout (d : ℕ) (w : List Bool) := Matrix (Fin (d + 1)) (Fin (w.length + 1)) ℝ

def readings {d : ℕ} (W : World d) (w : List Bool) : History w :=
  fun i => readAt W w i.val

/-- Zero is allowed for collinearity, but never for gain-ray success. -/
def Collinear {d : ℕ} (β v : Coeff d) : Prop := ∃ s : ℝ, v = s • β

def Succeeds {d : ℕ} (W : World d) (w : List Bool) (C : Readout d w) : Prop :=
  ∃ s : ℝ, s ≠ 0 ∧ C.mulVec (readings W w) = s • W.coeff

/-- Each palette is fixed before observations; only its selection is adaptive.
The set may be empty, finite or countably infinite. -/
structure Protocol (d : ℕ) where
  palette : ∀ w : List Bool, Set (Readout d w)
  countable : ∀ w, (palette w).Countable
  decide : ∀ w : List Bool, History w → Bool ⊕ {C : Readout d w // C ∈ palette w}

/-- Reaching a word entails every preceding actual decision and its immediate read.
There is no initial action and no action without its read. -/
inductive Reaches {d : ℕ} (P : Protocol d) (W : World d) : List Bool → Prop
  | initial : Reaches P W []
  | step {w : List Bool} {a : Bool} : Reaches P W w →
      P.decide w (readings W w) = Sum.inl a → Reaches P W (w ++ [a])

def Terminates {d : ℕ} (P : Protocol d) (W : World d) (w : List Bool)
    (C : {C : Readout d w // C ∈ P.palette w}) : Prop :=
  Reaches P W w ∧ P.decide w (readings W w) = Sum.inr C

/-- A total-read bound counts the initial read and every executed atom's read. -/
def UniformlySuccessful {d : ℕ} (P : Protocol d) (N : ℕ) : Prop :=
  ∀ W : World d, ∃ w C, Terminates P W w C ∧ w.length + 1 ≤ N ∧ Succeeds W w C.1

private theorem readings_before_append {d : ℕ} (W W' : World d) (w : List Bool) (a : Bool)
    (h : readings W (w ++ [a]) = readings W' (w ++ [a])) :
    readings W w = readings W' w := by
  ext i
  have hi : i.val ≤ w.length := by omega
  have he := congrFun h ⟨i.val, by simp <;> omega⟩
  simpa [readings, readAt, List.take_append_of_le_length hi] using he

/-- The identical values are actual for both worlds, through all prior decisions. -/
theorem identical_prefix_transfer {d : ℕ} (P : Protocol d) (W W' : World d)
    (w : List Bool) (hr : Reaches P W w)
    (he : readings W w = readings W' w) :
    Reaches P W' w ∧ P.decide w (readings W w) = P.decide w (readings W' w) := by
  have replay : ∀ v, Reaches P W v → readings W v = readings W' v → Reaches P W' v := by
    intro v hv
    induction hv with
    | initial => intro _; exact .initial
    | @step v a hv hd ih =>
        intro h
        have hpre := readings_before_append W W' v a h
        exact .step (ih hpre) (by rw [← hpre]; exact hd)
  exact ⟨replay w hr he, congrArg (P.decide w) he⟩

/-- The transferred next M is forced even if later observations and decisions differ. -/
theorem identical_prefix_firstM {d : ℕ} (P : Protocol d) (W W' : World d)
    (n : ℕ) (hr : Reaches P W (List.replicate n true))
    (he : readings W (List.replicate n true) = readings W' (List.replicate n true))
    (hd : P.decide (List.replicate n true) (readings W (List.replicate n true)) =
      Sum.inl false) :
    Reaches P W' (List.replicate n true ++ [false]) := by
  obtain ⟨hr', hdecision⟩ := identical_prefix_transfer P W W' _ hr he
  exact .step hr' (hdecision.symm.trans hd)

/-- A terminal history transfers its very same fixed matrix selection. -/
theorem identical_terminal_transfer {d : ℕ} (P : Protocol d) (W W' : World d)
    (w : List Bool) (C : {C : Readout d w // C ∈ P.palette w})
    (ht : Terminates P W w C) (he : readings W w = readings W' w) :
    Terminates P W' w C := by
  obtain ⟨hr, hd⟩ := identical_prefix_transfer P W W' w ht.1 he
  exact ⟨hr, hd.symm.trans ht.2⟩

#print axioms identical_prefix_firstM
end D5.S3.Observer.Linear.GainRay
