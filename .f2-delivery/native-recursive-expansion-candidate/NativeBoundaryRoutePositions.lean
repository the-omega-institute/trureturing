/- UNCOMPILED native E/O route positions used by the Q ordered split.
   The B path finishing at actual L0 is strictly later than the B path
   starting at actual R0. These are consequences of the verified explicit
   E/O enumerations and native port injectivity, not new state assumptions. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialBoundaryInstances

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open private code_injective from
  D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open private frame_k_lt_m from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialChildAssembly

private theorem even_left_zero_route_position (s i : ℕ) (hi : i < 2 * s + 3) :
    evenRoute s (2 * i + 1) = (0, 1) ↔ i = s + 1 := by
  have hm := Nat.mod_lt (2 * i + 1) (by decide : 0 < 2)
  unfold evenRoute
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

private theorem odd_left_zero_route_position (s i : ℕ) (hi : i < 2 * s + 4) :
    oddRoute s (2 * i + 1) = (0, 1) ↔ i = s + 1 := by
  have hm := Nat.mod_lt (2 * i + 1) (by decide : 0 < 2)
  unfold oddRoute
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- Actual even-route pieces have precisely one path finishing at L0,
at position s+1. Thus it is later than the first rooted B path. -/
theorem native_even_left_zero_piece_position {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 2)) (hB : 3 ≤ F.base.length)
    (ordered : Fin (2 * s + 3) → Piece (domainGraph (SpecialDomain F hB)))
    (hend : ∀ i, (ordered i).finish = specialVertex hm F hB
      (evenPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) :
    ∀ i, (ordered i).finish = specialVertex hm F hB (0, 1) ↔ i.val = s + 1 := by
  intro i
  rw [hend i]
  have hport : Function.Injective (specialVertex hm F hB) := by
    intro p q he
    exact native_special_port_injective hm F (frame_k_lt_m F hB)
      (congrArg Subtype.val he)
  rw [hport.eq_iff, ← (code_injective (2 * s + 2)).eq_iff]
  change evenRoute s (2 * i.val + 1) = (0, 1) ↔ i.val = s + 1
  exact even_left_zero_route_position s i.val i.isLt

/-- The odd route has the same actual L0 B-piece position. The empty
ladder at k=3 is included, with the distinguished path still at index 1. -/
theorem native_odd_left_zero_piece_position {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 3)) (hB : 3 ≤ F.base.length)
    (ordered : Fin (2 * s + 4) → Piece (domainGraph (SpecialDomain F hB)))
    (hend : ∀ i, (ordered i).finish = specialVertex hm F hB
      (oddPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) :
    ∀ i, (ordered i).finish = specialVertex hm F hB (0, 1) ↔ i.val = s + 1 := by
  intro i
  rw [hend i]
  have hport : Function.Injective (specialVertex hm F hB) := by
    intro p q he
    exact native_special_port_injective hm F (frame_k_lt_m F hB)
      (congrArg Subtype.val he)
  rw [hport.eq_iff, ← (code_injective (2 * s + 3)).eq_iff]
  change oddRoute s (2 * i.val + 1) = (0, 1) ↔ i.val = s + 1
  exact odd_left_zero_route_position s i.val i.isLt

#print axioms native_even_left_zero_piece_position
#print axioms native_odd_left_zero_piece_position

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
