/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A last label singles out exactly one native b edge within its complete circle. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleTerminalEdge

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement

/-- In one actual complete native circle, a fixed last label has exactly
the two orientations at the ends of its unique terminal b edge. -/
theorem native_circle_same_last_iff {m : ℕ} (hm : 3 ≤ m)
    (z x : Configuration m) (hx : Circle z x) :
    x (Fin.last m) = z (Fin.last m) ↔ x = z ∨ x = z * b m := by
  constructor
  · intro hlast
    let p := (circleEquiv hm z).symm ⟨x, hx⟩
    have hp : circleCoordinate z p = x :=
      congrArg Subtype.val ((circleEquiv hm z).apply_symm_apply ⟨x, hx⟩)
    obtain ⟨r, t⟩ := p
    cases t with
    | false =>
      rw [← hp] at hlast
      simp only [circleCoordinate, Bool.false_eq_true, if_false, mul_one,
        Equiv.Perm.mul_apply, finCycle_apply] at hlast
      have hr : r = 0 := add_left_cancel (by
        simpa only [add_zero] using z.injective hlast)
      subst r
      exact Or.inl (by simpa only [circleCoordinate, Bool.false_eq_true, if_false,
        mul_one, cycle_zero] using hp.symm)
    | true =>
      rw [← hp] at hlast
      simp only [circleCoordinate, if_true, Equiv.Perm.mul_apply, a_apply,
        Fin.rev_last, finCycle_apply, zero_add] at hlast
      have hr : r = Fin.last m := z.injective hlast
      have hn : (Fin.last m : Fin (m + 1)) = -1 := by
        rw [← Fin.neg_last m, neg_neg]
      exact Or.inr (by
        rw [← hp]
        change z * finCycle r * a m = z * b m
        rw [hr, hn, b_eq_cycle_a, mul_assoc])
  · rintro (rfl | rfl)
    · rfl
    · rw [Equiv.Perm.mul_apply, b_last]

/-- Every actual native b edge with the anchor's last label equals the
anchor's own undirected b edge, independently of orientation. -/
theorem native_circle_terminal_b_edge {m : ℕ} (hm : 3 ≤ m)
    (z x : Configuration m) (hx : Circle z x)
    (hlast : x (Fin.last m) = z (Fin.last m)) :
    s(x, x * b m) = s(z, z * b m) := by
  rcases (native_circle_same_last_iff hm z x hx).mp hlast with rfl | rfl
  · rfl
  · apply Sym2.eq_iff.mpr
    refine Or.inr ⟨rfl, ?_⟩
    apply Equiv.ext
    intro i
    change z (b m (b m i)) = z i
    rw [show b m (b m i) = i from
      PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
        (L := m) (by omega) i]

#print axioms native_circle_same_last_iff
#print axioms native_circle_terminal_b_edge

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleTerminalEdge
