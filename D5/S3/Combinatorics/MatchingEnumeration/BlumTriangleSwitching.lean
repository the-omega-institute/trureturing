/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleSwitching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleSwitching
   mirror-E: none(waiver:axis-pairing-combinatorics)
   anchors: [mathlib/module/Mathlib.Order.RelIso.Basic]
   utility: none
   digest: Noncrossing boundary pairings join opposite index parities. -/

import Mathlib.Order.RelIso.Basic
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleDefs
import D5.S3.Combinatorics.SemiMeanderSecondDiagonal.Model
import D5.S3.PrimeForms.Crossing.GlideCrossingParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleSwitching

open D5.S3.Combinatorics.SemiMeanderSecondDiagonal
open D5.S3.PrimeForms.Crossing.GlideCrossingParity

/-- Reflection in `x = n - 1`, constructed on the fixed coordinate graph. -/
def reflection (n : ℕ) : @BlumTriangleDefs.Adj n ≃r @BlumTriangleDefs.Adj n := by
  let flip : BlumTriangleDefs.Vertex n → BlumTriangleDefs.Vertex n := fun v =>
    ⟨(v.1.1, ⟨2 * (n - 1) - v.1.2.val, by
      have hv := v.2
      have hr := v.1.1.isLt
      omega⟩), by
      have hv := v.2
      dsimp
      omega⟩
  have hinvol : Function.Involutive flip := by
    intro v
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have hv := v.2
      dsimp [flip]
      omega
  have step (v w : BlumTriangleDefs.Vertex n) (h : BlumTriangleDefs.Step v w) :
      BlumTriangleDefs.Adj (flip v) (flip w) := by
    have hv := v.2
    have hw := w.2
    rcases h with ⟨hr, hx⟩ | ⟨heven, ⟨hr, hx⟩ | ⟨hr, hx⟩⟩
    · left
      left
      refine ⟨hr, ?_⟩
      dsimp [flip]
      rcases hx with hx | hx
      · right
        omega
      · left
        omega
    · right
      right
      refine ⟨?_, Or.inl ⟨hr.symm, ?_⟩⟩
      · dsimp [flip]
        omega
      · dsimp [flip]
        omega
    · left
      right
      refine ⟨heven, Or.inr ⟨hr, ?_⟩⟩
      dsimp [flip]
      omega
  have preserves (v w : BlumTriangleDefs.Vertex n) (h : BlumTriangleDefs.Adj v w) :
      BlumTriangleDefs.Adj (flip v) (flip w) := by
    rcases h with h | h
    · exact step v w h
    · exact (step w v h).elim Or.inr Or.inl
  refine
    { toFun := flip
      invFun := flip
      left_inv := hinvol
      right_inv := hinvol
      map_rel_iff' := ?_ }
  intro v w
  change BlumTriangleDefs.Adj (flip v) (flip w) ↔ BlumTriangleDefs.Adj v w
  constructor
  · intro h
    simpa only [hinvol v, hinvol w] using preserves (flip v) (flip w) h
  · exact preserves v w

/-- Restricting the pairing to the open interval inside an arch gives a fixed-point-free
involution. Its even cardinality forces the two boundary indices to have opposite parity. -/
theorem noncrossing_mates_opposite_parity {n : ℕ} (P : UpperMatching n)
    (a : Fin (2 * n)) : (P.mate a).val % 2 ≠ a.val % 2 := by
  classical
  have forward (s t : Fin (2 * n)) (hlt : s.val < t.val) (hpair : P.mate s = t) :
      s.val % 2 ≠ t.val % 2 := by
    let Interior := {x : Fin (2 * n) // s.val < x.val ∧ x.val < t.val}
    have closed (x : Interior) : s.val < (P.mate x.1).val ∧
        (P.mate x.1).val < t.val := by
      have hx := x.2
      have hts : P.mate t = s := by rw [← hpair, P.mate_mate]
      have hneS : P.mate x.1 ≠ s := by
        intro h
        have hx' := P.mate_mate x.1
        rw [h, hpair] at hx'
        have hv := congrArg Fin.val hx'
        omega
      have hneT : P.mate x.1 ≠ t := by
        intro h
        have hx' := P.mate_mate x.1
        rw [h, hts] at hx'
        have hv := congrArg Fin.val hx'
        omega
      have hneSv : (P.mate x.1).val ≠ s.val := by
        intro h
        exact hneS (Fin.ext h)
      have hneTv : (P.mate x.1).val ≠ t.val := by
        intro h
        exact hneT (Fin.ext h)
      constructor
      · by_contra h
        have hleft : (P.mate x.1).val < s.val := by omega
        have hn := P.noncrossing (P.mate x.1) s hleft
        rw [P.mate_mate, hpair] at hn
        exact hn hx.1 hx.2
      · by_contra h
        have hright : t.val < (P.mate x.1).val := by omega
        have hn := P.noncrossing s x.1 hx.1
        rw [hpair] at hn
        exact hn hx.2 hright
    let inside : Interior → Interior := fun x => ⟨P.mate x.1, closed x⟩
    have hinvol : Function.Involutive inside := by
      intro x
      apply Subtype.ext
      exact P.mate_mate x.1
    have hfree (x : Interior) : inside x ≠ x := by
      intro h
      exact P.mate_ne x.1 (congrArg Subtype.val h)
    have heven := glide_crossing_count_even inside hinvol hfree
    let e : Interior ≃ Fin (t.val - s.val - 1) :=
      { toFun := fun x => ⟨x.1.val - s.val - 1, by
          have := x.2
          omega⟩
        invFun := fun i => ⟨⟨s.val + 1 + i.val, by
          have := i.isLt
          have := t.isLt
          omega⟩, by
          change s.val < s.val + 1 + i.val ∧ s.val + 1 + i.val < t.val
          have := i.isLt
          omega⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Fin.ext
          have := x.2
          dsimp
          omega
        right_inv := fun i => by
          apply Fin.ext
          dsimp
          omega }
    rw [Fintype.card_congr e, Fintype.card_fin] at heven
    obtain ⟨d, hd⟩ := heven
    omega
  rcases lt_trichotomy a.val (P.mate a).val with hlt | heq | hgt
  · exact (forward a (P.mate a) hlt rfl).symm
  · exact False.elim (P.mate_ne a (Fin.ext heq.symm))
  · exact forward (P.mate a) a hgt (P.mate_mate a)

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleSwitching
