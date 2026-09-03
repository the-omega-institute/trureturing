/- GID: D5/S3/Arith/Congruence/EvenDenseConstellationMirrorCode
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/EvenDenseConstellationMirrorCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An even admissible two-four-gap constellation has a reversal-fixed gap code. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.EvenDenseConstellationMirrorCode

private theorem alternating_bool_reverse_eq_self
    (bits : List Bool)
    (halt : bits.IsChain (fun left right => left ≠ right))
    (hodd : Odd bits.length) :
    bits.reverse = bits := by
  obtain ⟨k, hk⟩ := hodd
  have hchain : bits.IsChain (fun left right => (!left) = right) := by
    simpa only [Bool.not_eq_iff] using halt
  have hpos : 0 < bits.length := by omega
  apply List.ext_getElem
  · simp
  intro i hirev hibits
  have hi : i < bits.length := by simpa using hibits
  have hmirror : bits.length - 1 - i < bits.length := by omega
  rw [List.getElem_reverse]
  have hforward := hchain.iterate_eq_of_apply_eq i hi
  have hbackward := hchain.iterate_eq_of_apply_eq (bits.length - 1 - i) hmirror
  rw [← hforward, ← hbackward]
  have hparity : Even (bits.length - 1 - i) ↔ Even i := by
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨k - j, ?_⟩
      omega
    · rintro ⟨j, hj⟩
      refine ⟨k - j, ?_⟩
      omega
  have hnot : Function.Involutive (fun b : Bool => !b) := by
    intro b
    cases b <;> rfl
  by_cases hi_even : Even i
  · rw [hnot.iterate_even hi_even]
    rw [hnot.iterate_even (hparity.mpr hi_even)]
  · have hi_odd : Odd i := Nat.not_even_iff_odd.mp hi_even
    have hmirror_odd : Odd (bits.length - 1 - i) :=
      Nat.not_even_iff_odd.mp (fun he => hi_even (hparity.mp he))
    rw [hnot.iterate_odd hi_odd]
    rw [hnot.iterate_odd hmirror_odd]

/-- The gap code constructed from an even dense constellation is fixed by reversal when the
constellation omits one residue modulo three. Equal neighboring gaps would visit all three
residues, so admissibility forces the two gap symbols to alternate. -/
theorem even_dense_constellation_gap_code_self
    (points : List ℤ)
    (hdense : ∀ (i : ℕ) (hi : i + 1 < points.length),
      points[i + 1] - points[i] = 2 ∨ points[i + 1] - points[i] = 4)
    (hadmissible : ∃ omitted : ZMod 3, ∀ (i : ℕ) (hi : i < points.length),
      (points[i] : ZMod 3) ≠ omitted)
    (heven : Even points.length) :
    (points.zipWith (fun left right => decide (right - left = 4)) points.tail).reverse =
      points.zipWith (fun left right => decide (right - left = 4)) points.tail := by
  by_cases hempty : points = []
  · simp [hempty]
  let bits := points.zipWith (fun left right => decide (right - left = 4)) points.tail
  apply alternating_bool_reverse_eq_self bits
  · rw [List.isChain_iff_getElem]
    intro i hi
    have hlength : bits.length = points.length - 1 := by simp [bits]
    have hi2 : i + 2 < points.length := by
      rw [hlength] at hi
      omega
    have hfirst := hdense i (by omega)
    have hsecond : points[i + 2] - points[i + 1] = 2 ∨
        points[i + 2] - points[i + 1] = 4 := by
      simpa [Nat.add_assoc] using hdense (i + 1) (by omega)
    have hbit_first : bits[i] = decide (points[i + 1] - points[i] = 4) := by
      simp [bits]
    have hbit_second : bits[i + 1] = decide (points[i + 2] - points[i + 1] = 4) := by
      simp [bits]
    rw [hbit_first, hbit_second]
    intro heq
    obtain ⟨omitted, homitted⟩ := hadmissible
    have hnot0 := homitted i (by omega)
    have hnot1 := homitted (i + 1) (by omega)
    have hnot2 := homitted (i + 2) (by omega)
    rcases hfirst with hgap | hgap <;> rcases hsecond with hgap' | hgap'
    · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hgap
      have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hgap'
      push_cast at hcast hcast'
      have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 2 := by
        linear_combination hcast
      have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 2 := by
        linear_combination hcast'
      have hcover : ∀ x r : ZMod 3, x = r ∨ x + 2 = r ∨ x + 2 + 2 = r := by
        decide
      rcases hcover (points[i] : ZMod 3) omitted with hcover | hcover | hcover
      · exact hnot0 hcover
      · exact hnot1 (hp1.trans hcover)
      · apply hnot2
        rw [hp2, hp1]
        exact hcover
    · simp [hgap, hgap'] at heq
    · simp [hgap, hgap'] at heq
    · have hcast := congrArg (fun z : ℤ => (z : ZMod 3)) hgap
      have hcast' := congrArg (fun z : ℤ => (z : ZMod 3)) hgap'
      push_cast at hcast hcast'
      have hp1 : (points[i + 1] : ZMod 3) = (points[i] : ZMod 3) + 4 := by
        linear_combination hcast
      have hp2 : (points[i + 2] : ZMod 3) = (points[i + 1] : ZMod 3) + 4 := by
        linear_combination hcast'
      have hcover : ∀ x r : ZMod 3, x = r ∨ x + 4 = r ∨ x + 4 + 4 = r := by
        decide
      rcases hcover (points[i] : ZMod 3) omitted with hcover | hcover | hcover
      · exact hnot0 hcover
      · exact hnot1 (hp1.trans hcover)
      · apply hnot2
        rw [hp2, hp1]
        exact hcover
  · obtain ⟨k, hk⟩ := heven
    refine ⟨k - 1, ?_⟩
    simp [bits]
    have hpos : 0 < points.length := List.length_pos_of_ne_nil hempty
    omega

#print axioms even_dense_constellation_gap_code_self

end D5.S3.Arith.Congruence.EvenDenseConstellationMirrorCode
