/- GID: D5/S3/Weil/ZetaLinear/CompactCharacterMellinObstruction
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/CompactCharacterMellinObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact complex characters are unitary, excluding nonzero Mellin drift. -/

import D5.S3.Weil.ZetaLinear.OfflineZeroCharacter
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.PontryaginDual

/- Library-search audit trail (2026-09-02):
   * D5 searches for compact-character modulus, continuous complex
     characters, Pontryagin characters, and compact Mellin descent found no
     theorem with both source clauses. `OfflineZeroCharacter` supplies the
     canonical Mellin character and its exact unitarity criterion, but it has
     no compact-domain result or no-factorization theorem.
   * Pinned Mathlib searches for compact character norm, compact subgroups of
     the positive reals, bounded character powers, and Mellin/Pontryagin
     descent found no exact theorem. The proof applies compact-range
     boundedness, `pow_unbounded_of_one_lt`, and the circle norm identity.
   * Searches of the installed non-Mathlib Lean packages for compact-character
     modulus and Mellin/Pontryagin descent returned no hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.CompactCharacterMellinObstruction

open D5.S3.Weil.ZetaLinear.OfflineZeroCharacter

universe u

/-- Every continuous character from a compact topological group to the
nonzero complex numbers has unit modulus. Consequently a Mellin character
with nonzero real drift cannot factor through any Pontryagin character of
that compact group. -/
theorem compact_character_modulus_and_mellin_obstruction
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] :
    (∀ (chi : ContinuousMonoidHom G (Units ℂ)) (g : G),
      ‖(chi g : ℂ)‖ = 1) ∧
    (∀ (delta gamma : ℝ), delta ≠ 0 →
      ∀ (descent : ContinuousMonoidHom (Multiplicative ℝ) G)
        (phase : PontryaginDual G),
        ¬∀ time : ℝ,
          mellinCharacter ((delta : ℂ) + Complex.I * (gamma : ℂ))
              (Multiplicative.ofAdd time) =
            ((phase (descent (Multiplicative.ofAdd time)) : Circle) : ℂ)) := by
  constructor
  · intro chi
    have hcompact :
        IsCompact (Set.range fun g : G => ‖(chi g : ℂ)‖) := by
      apply isCompact_range
      exact continuous_norm.comp (Units.continuous_val.comp chi.continuous)
    have hbounded : BddAbove (Set.range fun g : G => ‖(chi g : ℂ)‖) :=
      hcompact.bddAbove
    obtain ⟨bound, hbound⟩ := hbounded
    have hle (g : G) : ‖(chi g : ℂ)‖ ≤ 1 := by
      by_contra hnot
      have hone : 1 < ‖(chi g : ℂ)‖ := lt_of_not_ge hnot
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt bound hone
      have hpowers : ‖(chi g : ℂ)‖ ^ n ≤ bound := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow]
        exact hbound ⟨g ^ n, rfl⟩
      exact (not_lt_of_ge hpowers) hn
    intro g
    apply le_antisymm (hle g)
    have hinverse := hle g⁻¹
    calc
      1 = ‖(chi g : ℂ)‖ * ‖(chi g⁻¹ : ℂ)‖ := by
        symm
        rw [← norm_mul, ← Units.val_mul, ← map_mul]
        simp
      _ ≤ ‖(chi g : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hinverse (norm_nonneg _)
      _ = ‖(chi g : ℂ)‖ := mul_one _
  · intro delta gamma hdelta descent phase hfactor
    have hunitary :
        IsUnitary (mellinCharacter ((delta : ℂ) + Complex.I * (gamma : ℂ))) := by
      intro time
      rw [hfactor time]
      exact Circle.norm_coe _
    have hreal : (((delta : ℂ) + Complex.I * (gamma : ℂ))).re = 0 :=
      (mellin_character_unitary_iff _).mp hunitary
    exact hdelta (by simpa using hreal)

#print axioms compact_character_modulus_and_mellin_obstruction

end D5.S3.Weil.ZetaLinear.CompactCharacterMellinObstruction
