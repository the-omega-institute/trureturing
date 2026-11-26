/- GID: D5/S3/Combinatorics/Golomb/NotikMinimizers
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Golomb/NotikMinimizers
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Combinatorics/Golomb/NotikMinimizers.result; instance=D5/S3/Combinatorics/Golomb/NotikCheck8.archivedCertificate8
   digest: All normalized real Golomb minimizers at eight, nine, and ten marks are integral. -/

import D5.S3.Combinatorics.Golomb.NotikSmallerBounds
import D5.S3.Combinatorics.Golomb.NotikCheck8
import D5.S3.Combinatorics.Golomb.NotikCheck9
import D5.S3.Combinatorics.Golomb.NotikCheck10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Golomb.NotikMinimizers

open D5.S3.Combinatorics.Golomb.Replay
open scoped BigOperators

private theorem lower8 : LowerBound 7 34 :=
  replay_marks smaller7 archivedCertificate8.1 archivedCertificate8.2.1

private theorem integral8 (x : Marks 7) (hx : RealGolomb x) (hzero : x 0 = 0)
    (hlen : endLength x = 34) : ∀ i, ∃ z : ℤ, x i = (z : ℝ) :=
  replay_marks_integral smaller7 archivedCertificate8.1 archivedCertificate8.2.1
    archivedCertificate8.2.2 hx hzero hlen

private theorem smaller8 : SmallerBounds 8 archiveBounds :=
  smaller_extend smaller7 lower8

private theorem lower9 : LowerBound 8 44 :=
  replay_marks smaller8 archivedCertificate9.1 archivedCertificate9.2.1

private theorem integral9 (x : Marks 8) (hx : RealGolomb x) (hzero : x 0 = 0)
    (hlen : endLength x = 44) : ∀ i, ∃ z : ℤ, x i = (z : ℝ) :=
  replay_marks_integral smaller8 archivedCertificate9.1 archivedCertificate9.2.1
    archivedCertificate9.2.2 hx hzero hlen

private theorem smaller9 : SmallerBounds 9 archiveBounds :=
  smaller_extend smaller8 lower9

private theorem lower10 : LowerBound 9 55 :=
  replay_marks smaller9 archivedCertificate10.1 archivedCertificate10.2.1

private theorem integral10 (x : Marks 9) (hx : RealGolomb x) (hzero : x 0 = 0)
    (hlen : endLength x = 55) : ∀ i, ∃ z : ℤ, x i = (z : ℝ) :=
  replay_marks_integral smaller9 archivedCertificate10.1 archivedCertificate10.2.1
    archivedCertificate10.2.2 hx hzero hlen

/-- Check an integer witness before interpreting its distances over the reals. -/
private def validEndpoint {n : ℕ} (z : Fin (n + 1) → ℤ) (target : ℤ) : Bool :=
  decide (z 0 = 0 ∧ z (Fin.last n) = target ∧
    (∀ i j, i < j → 1 ≤ z j - z i) ∧
    (∀ i j k l, i < j → k < l → (i, j) ≠ (k, l) →
      1 ≤ |(z j - z i) - (z l - z k)|))

private theorem integer_endpoint {n : ℕ} {z : Fin (n + 1) → ℤ} {target : ℤ}
    (h : validEndpoint z target = true) :
    z 0 = 0 ∧ z (Fin.last n) = target ∧ RealGolomb (fun i => (z i : ℝ)) := by
  obtain ⟨h0, ht, hmin, hsep⟩ := of_decide_eq_true h
  refine ⟨h0, ht, ⟨?_, ?_⟩⟩
  · intro i j hij
    exact_mod_cast hmin i j hij
  · intro i j k l hij hkl hne
    exact_mod_cast hsep i j k l hij hkl hne

/-- The three clauses for a specific ruler size and target. The universal clauses are
stated for the ordered marks themselves, independent of their orientation. -/
def MinimumAt (n : ℕ) (target : ℤ) : Prop :=
  (∃ z : Fin (n + 1) → ℤ,
    z 0 = 0 ∧ z (Fin.last n) = target ∧ RealGolomb (fun i => (z i : ℝ))) ∧
  LowerBound n target ∧
  (∀ x : Marks n, RealGolomb x → x 0 = 0 → endLength x = (target : ℝ) →
    ∀ i, ∃ z : ℤ, x i = (z : ℝ))

/-- Notik's §10 question, with the attained minimum specified for each size. -/
def claim : Prop := MinimumAt 7 34 ∧ MinimumAt 8 44 ∧ MinimumAt 9 55

/-- At 8, 9, and 10 marks every normalized shortest real Golomb ruler is integral. -/
theorem result : claim := by
  refine ⟨⟨?_, lower8, integral8⟩, ⟨?_, lower9, integral9⟩, ⟨?_, lower10, integral10⟩⟩
  · exact ⟨![0, 1, 4, 9, 15, 22, 32, 34], integer_endpoint (by decide +kernel)⟩
  · exact ⟨![0, 1, 5, 12, 25, 27, 35, 41, 44], integer_endpoint (by decide +kernel)⟩
  · exact ⟨![0, 1, 6, 10, 23, 26, 34, 41, 53, 55], integer_endpoint (by decide +kernel)⟩

end D5.S3.Combinatorics.Golomb.NotikMinimizers
