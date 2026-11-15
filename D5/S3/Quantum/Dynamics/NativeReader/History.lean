/- GID: D5/S3/Quantum/Dynamics/NativeReader/History
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/History
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fifteen-call zero-trigger histories on the full native carrier. -/

import D5.S3.Quantum.Dynamics.NativeReader.Global

/-! The auxiliary event law uses actual amplitudes and carries the configuration across seams. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.Dynamics.NativeReader

/-- A legal two-point edge flips only the actual physical center of the current call. -/
def legalAuxiliaryEdge (i : Bool) (j : Fin 5) (z w : Tail i) : Prop :=
  z ≠ w ∧ ∀ r : Fin 7, r.val ≠ j.val + 1 → z.1 r = w.1 r

abbrev AuxiliaryEvents (q : Source) := List (ℝ × Tail (q.1 9))

/-- The current global complex amplitude is read without a projected update. -/
def currentAmplitude (chi : Source → ℂ) (q : Source) (lam : ℝ)
    (k : Fin 15) (s : ℝ) (z : Tail (q.1 9)) : ℂ :=
  fullDuring chi lam k s (joinPath (q.1 9) ⟨q, rfl⟩ z)

/-- Events occur at the first exact zero. A right endpoint event is processed in this call;
    the new current coordinate must be nonzero and is reused across the seam. -/
def auxiliaryCallLaw (chi : Source → ℂ) (q : Source) (lam : ℝ) (k : Fin 15) :
    ℝ → Tail (q.1 9) → AuxiliaryEvents q → Prop
  | t, z, [] => ∀ s ∈ Set.Icc t 1, currentAmplitude chi q lam k s z ≠ 0
  | t, z, (s, w) :: rest =>
      t ≤ s ∧ s ≤ 1 ∧
      (∀ r ∈ Set.Ico t s, currentAmplitude chi q lam k r z ≠ 0) ∧
      currentAmplitude chi q lam k s z = 0 ∧
      legalAuxiliaryEdge (q.1 9) (address k) z w ∧
      currentAmplitude chi q lam k s w ≠ 0 ∧
      auxiliaryCallLaw chi q lam k s w rest

def afterEvents {q : Source} (z : Tail (q.1 9)) (es : AuxiliaryEvents q) : Tail (q.1 9) :=
  es.foldl (fun _ e => e.2) z

/-- Exactly fifteen event tables exist; after them the configuration waits unchanged. -/
def readerConfiguration {q : Source} (es : Fin 15 → AuxiliaryEvents q) : ℕ → Tail (q.1 9)
  | 0 => readyTail (q.1 9)
  | n + 1 => if h : n < 15 then afterEvents (readerConfiguration es n) (es ⟨n, h⟩)
      else readerConfiguration es n

structure NativeReaderHistory (chi : Source → ℂ) (q : Source) (lam : ℝ) where
  events : Fin 15 → AuxiliaryEvents q
  obeys : ∀ k : Fin 15,
    auxiliaryCallLaw chi q lam k 0 (readerConfiguration events k) (events k)

private theorem no_events (chi : Source → ℂ) (q : Source) (lam : ℝ)
    (hn : ∀ (k : Fin 15) (s : ℝ),
      currentAmplitude chi q lam k s (readyTail (q.1 9)) ≠ 0)
    (h : NativeReaderHistory chi q lam) :
    (∀ k, h.events k = []) ∧ readerConfiguration h.events 15 = readyTail (q.1 9) := by
  have ih (n : ℕ) (hb : n ≤ 15) :
      readerConfiguration h.events n = readyTail (q.1 9) ∧
        ∀ k : Fin 15, k.val < n → h.events k = [] := by
    induction n with
    | zero => exact ⟨rfl, by intro k hk; omega⟩
    | succ n ih =>
      obtain ⟨hc, he⟩ := ih (by omega)
      have hl := h.obeys ⟨n, by omega⟩
      rw [hc] at hl
      have hz : h.events ⟨n, by omega⟩ = [] := by
        cases hh : h.events ⟨n, by omega⟩ with
        | nil => rfl
        | cons e rest =>
          rw [hh, auxiliaryCallLaw] at hl
          exact False.elim (hn ⟨n, by omega⟩ e.1 hl.2.2.2.1)
      refine ⟨?_, ?_⟩
      · simp [readerConfiguration, show n < 15 by omega, hz, afterEvents, hc]
      · intro k hk
        by_cases hkn : k.val < n
        · exact he k hkn
        · have hke : k = ⟨n, by omega⟩ := Fin.ext (by change k.val = n; omega)
          simpa [hke] using hz
  obtain ⟨hc, he⟩ := ih 15 le_rfl
  exact ⟨fun k => he k k.isLt, hc⟩

/-- For every positive source entrance, the stipulated native event law has one auxiliary
    history: all fifteen actual calls, no jumps, unchanged ready configuration and report zero. -/
theorem native_reader_no_jumps :
    Fintype.card Source = 89 ∧ Fintype.card Extended = 610 ∧
    ∃ eta : ℝ, 0 < eta ∧ eta < min alpha (2 * Real.pi - alpha) ∧
      ∀ lam : ℝ, 0 < |lam - alpha| → |lam - alpha| < eta →
        ∀ (chi : Source → ℂ) (q : Source), chi q ≠ 0 →
          Nonempty (NativeReaderHistory chi q lam) ∧
          ∀ h : NativeReaderHistory chi q lam,
            (∀ k, h.events k = []) ∧
              readerConfiguration h.events 15 = readyTail (q.1 9) ∧
              report (readerConfiguration h.events 15) = false := by
  refine ⟨source_card, extended_card, ?_⟩
  obtain ⟨eta, he, ha, hn⟩ := full_reader_uniform_nonvanishing
  refine ⟨eta, he, ha, ?_⟩
  intro lam hl hd chi q hq
  have hnon (k : Fin 15) (s : ℝ) :
      currentAmplitude chi q lam k s (readyTail (q.1 9)) ≠ 0 :=
    hn lam hl hd chi q hq k s
  have hc (n : ℕ) : readerConfiguration (q := q) (fun _ => []) n = readyTail (q.1 9) := by
    induction n with
    | zero => rfl
    | succ n ih => simp [readerConfiguration, afterEvents, ih]
  constructor
  · exact ⟨⟨fun _ => [], by intro k; simp only [hc, auxiliaryCallLaw]; exact fun s _ => hnon k s⟩⟩
  · intro h
    obtain ⟨hevents, hconfig⟩ := no_events chi q lam hnon h
    exact ⟨hevents, hconfig, by rw [hconfig]; exact ready_report _⟩

end D5.S3.Quantum.Dynamics.NativeReader
