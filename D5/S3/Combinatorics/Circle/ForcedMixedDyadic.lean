/- GID: D5/S3/Combinatorics/Circle/ForcedMixedDyadic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ForcedMixedDyadic
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Every two-fresh strict competitor in an unbounded native family requires a mixed packet. -/
module
public import D5.S3.Combinatorics.Circle.MixedDyadicAugmentation
import Mathlib.Tactic

/-! Necessary physical count and prefix constraints allow arbitrary returns and reorderings. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.ForcedMixedDyadic
open SourceWidth ExpandingSourcePath MixedSuffixEnergy TwoOppositeLargeExchange
open DyadicResetSource DyadicResetBlocks

private theorem forced_counts (a b c x y z₁ z₂ A B H₀ Gt Ht Ut : ℕ)
    (hAB : A < B) (ha : a ≤ 1) (budget : a + b + c ≤ 2) (h : ℤ)
    (hend : 0 ≤ h ∧ h ≤ 7)
    (hmass : h = 6 + 4 * ((a : ℤ) - x) - 7 * ((b : ℤ) - y) +
      2 * c - z₁ - 2 * z₂)
    (block : (1 : ℤ) + a + y ≤ b + x + if 4 ≤ h then 1 else 0)
    (gbal : Gt + a + b = 3 + x + y)
    (hbal : Ht + x * A + y * B = H₀ + a * A + b * B)
    (ubal : Ut + a + b + c = 5 + x + y + z₁ + z₂)
    (strict : Gt < 3 ∨ Gt = 3 ∧ (Ht < H₀ ∨ Ht = H₀ ∧ Ut < 5)) :
    a = 0 ∧ b = 1 ∧ c = 1 := by
  rcases strict with hg | ⟨hg, hs⟩
  · split_ifs at block <;> omega
  · have hcounts : a + b = x + y := by omega
    have hax : a ≤ x := by split_ifs at block <;> omega
    obtain ⟨d, hd, hBd⟩ : ∃ d : ℕ, 0 < d ∧ B = A + d :=
      ⟨B - A, by omega, by omega⟩
    obtain ⟨v, hxv⟩ : ∃ v : ℕ, x = a + v := ⟨x - a, by omega⟩
    have hbv : b = y + v := by omega
    subst B; subst x; subst b
    have hbal' : Ht = H₀ + v * d := by nlinarith [hbal]
    rcases hs with hh | ⟨hh, hu⟩
    · omega
    · have hv : v = 0 := by nlinarith
      subst v
      omega

end D5.S3.Combinatorics.Circle.ForcedMixedDyadic
