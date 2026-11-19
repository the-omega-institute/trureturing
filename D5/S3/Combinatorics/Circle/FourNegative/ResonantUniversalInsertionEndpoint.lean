/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionEndpoint
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Repetition and natural-take closure of the strict resonant target lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionNatural

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport

private theorem resonant_strip_of_prefix {α : Type*} (f : α → ℤ) (B h : ℤ)
    (l : List α)
    (hl : ∀ n, 0 ≤ h + ((l.take n).map f).sum ∧
      h + ((l.take n).map f).sum ≤ B) :
    InStrip f B h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using hl 0
  | cons x xs ih =>
    have hh := hl 0
    refine ⟨by simpa using hh.1, by simpa using hh.2, ih (h + f x) ?_⟩
    intro n
    simpa [List.take_succ_cons, add_assoc] using hl (n + 1)

private theorem resonant_zero_period_transport {α : Type*} (f : α → ℤ) (B : ℤ)
    (l : List α) (hz : (l.map f).sum = 0)
    (hp : ∀ n, 0 ≤ ((l.take n).map f).sum ∧
      ((l.take n).map f).sum ≤ B) (m : ℕ) :
    (((List.replicate m l).flatten).map f).sum = 0 ∧
      (∀ n, 0 ≤ ((((List.replicate m l).flatten).take n).map f).sum ∧
        ((((List.replicate m l).flatten).take n).map f).sum ≤ B) := by
  have hB : 0 ≤ B := by simpa using (hp 0).2
  have hs : InStrip f B 0 l := by
    apply resonant_strip_of_prefix f B 0 l
    intro n
    simpa using hp n
  have hr (r : ℕ) :
      (((List.replicate r l).flatten).map f).sum = 0 ∧
        InStrip f B 0 (List.replicate r l).flatten := by
    induction r with
    | zero => simp [InStrip, hB]
    | succ r ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      constructor
      · simp only [List.map_append, List.sum_append, hz, ih.1, add_zero]
      · exact inStrip_append hs (by simpa only [hz, zero_add] using ih.2)
  refine ⟨(hr m).1, ?_⟩
  intro n
  simpa only [zero_add] using inStrip_prefix (hr m).2 n

/-- Every finite repetition of the strict adaptive lift has both target strips
    on every natural take, and both repeated totals remain zero. -/
theorem resonant_target_word_repeated_strict {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell < k)
    (word : List (Fin (k + 1))) (hsource : resonantSourceWord k w word) :
    let orientation :=
      resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
    (∀ r n : ℕ,
      0 ≤ ((((List.replicate r (resonantLiftWord word orientation)).flatten).take n).map
        (resonantTargetFirst k ell w)).sum ∧
      ((((List.replicate r (resonantLiftWord word orientation)).flatten).take n).map
        (resonantTargetFirst k ell w)).sum ≤ resonantTargetH k ell ∧
      0 ≤ ((((List.replicate r (resonantLiftWord word orientation)).flatten).take n).map
        (resonantTargetSecond k ell w)).sum ∧
      ((((List.replicate r (resonantLiftWord word orientation)).flatten).take n).map
        (resonantTargetSecond k ell w)).sum ≤ resonantTargetN k ell) ∧
    (∀ r : ℕ,
      (((List.replicate r (resonantLiftWord word orientation)).flatten).map
        (resonantTargetFirst k ell w)).sum = 0 ∧
      (((List.replicate r (resonantLiftWord word orientation)).flatten).map
        (resonantTargetSecond k ell w)).sum = 0) := by
  dsimp only
  let orientation :=
    resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
  have htarget := resonant_target_word_of_source_strict hw hell hm hdiv hlarge hkl
    word hsource
  dsimp only at htarget
  have htarget' :
      ((resonantLiftWord word orientation).map
          (resonantTargetFirst k ell w)).sum = 0 ∧
      ((resonantLiftWord word orientation).map
          (resonantTargetSecond k ell w)).sum = 0 ∧
      ∀ n : ℕ,
        0 ≤ (((resonantLiftWord word orientation).take n).map
          (resonantTargetFirst k ell w)).sum ∧
        (((resonantLiftWord word orientation).take n).map
          (resonantTargetFirst k ell w)).sum ≤ resonantTargetH k ell ∧
        0 ≤ (((resonantLiftWord word orientation).take n).map
          (resonantTargetSecond k ell w)).sum ∧
        (((resonantLiftWord word orientation).take n).map
          (resonantTargetSecond k ell w)).sum ≤ resonantTargetN k ell := by
    simpa [orientation] using htarget.2
  have hfirst : ∀ n : ℕ,
      0 ≤ (((resonantLiftWord word orientation).take n).map
        (resonantTargetFirst k ell w)).sum ∧
      (((resonantLiftWord word orientation).take n).map
        (resonantTargetFirst k ell w)).sum ≤ resonantTargetH k ell := by
    intro n
    exact ⟨(htarget'.2.2 n).1, (htarget'.2.2 n).2.1⟩
  have hsecond : ∀ n : ℕ,
      0 ≤ (((resonantLiftWord word orientation).take n).map
        (resonantTargetSecond k ell w)).sum ∧
      (((resonantLiftWord word orientation).take n).map
        (resonantTargetSecond k ell w)).sum ≤ resonantTargetN k ell := by
    intro n
    exact ⟨(htarget'.2.2 n).2.2.1, (htarget'.2.2 n).2.2.2⟩
  have hfirstRep := resonant_zero_period_transport
    (resonantTargetFirst k ell w) (resonantTargetH k ell)
    (resonantLiftWord word orientation) htarget'.1 hfirst
  have hsecondRep := resonant_zero_period_transport
    (resonantTargetSecond k ell w) (resonantTargetN k ell)
    (resonantLiftWord word orientation) htarget'.2.1 hsecond
  refine ⟨?_, ?_⟩
  · intro r n
    exact ⟨((hfirstRep r).2 n).1, ((hfirstRep r).2 n).2,
      ((hsecondRep r).2 n).1, ((hsecondRep r).2 n).2⟩
  · intro r
    exact ⟨(hfirstRep r).1, (hsecondRep r).1⟩

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
