/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/GaussSumSign
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/GaussSumSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.GaussSumSign. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/GaussSumSign.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Unitary.SpaceGram
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Sign of a Gauss sum fixed modulo 4 by orbits of order four. -/

/-- Let X be a finite abelian group without 2-torsion, f(f(x)) = −x, F an f-invariant function
with values roots of unity, F(0) = 1, ∑F real, r ≡ 1 mod 4 an integer. If |c| = 1 and c·r^a
= (∑F)·r^b, then c = 1. -/
lemma eq_one_of_orbits {X} [AddCommGroup X] [Fintype X] (f : X → X) (F : X → ℂ) r {a b c}
    (hr : r ≡ 1 [ZMOD 4]) (h₀ : F 0 = 1) (h : ∀ x, IsOfFinOrder (F x) ∧ F (f x) = F x ∧ f (f x) = -x
    ∧ (-x = x ↔ x = 0)) (hc : ‖c‖ = 1) (re : IsSelfAdjoint (Finset.univ.sum F))
    (e : c * r ^ a = Finset.univ.sum F * r ^ b) : c = 1 := by
  by_contra; let s x : Finset X := {x, f x, -x, -f x}
  have E : r ^ b • ((Finset.univ.erase 0).sum F / 4) = ((r ^ a + r ^ b) / -4 : ℚ) := by
    have := congr(star $e); simp_all [IsSelfAdjoint, ↓star_mul', ← c.inv_eq_conj]; grind [norm_zero]
  have ⟨k, _⟩ := (IsIntegral.smul _ ?_).exists_int_iff_exists_rat.1 ⟨_, E.symm⟩
  simp_all [field]; norm_cast at *
  grind [(hr.pow · |>.eq)]
  rw [Finset.sum_div, ← Finset.sum_fiberwise_of_maps_to fun _ ↦ Finset.mem_image_of_mem s]
  refine .sum _ (Finset.forall_mem_image.2 fun y _ ↦ ?_)
  convert IsPrimitiveRoot.isIntegral (.orderOf _) (h y).1.orderOf_pos
  rw [(_ : Finset.filter .. = s y), Finset.sum_insert] <;> grind (splits := 20)
