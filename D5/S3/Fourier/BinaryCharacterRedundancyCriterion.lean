/- GID: D5/S3/Fourier/BinaryCharacterRedundancyCriterion
   generality: G
   mirror-B: D5/B/S3/Fourier/BinaryCharacterRedundancyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A binary character is redundant exactly when it lies in the existing span. -/

import D5.S3.Fourier.BinaryCharacterBasisMinimality
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-25):
   * Repository searches for binary-character redundancy, unchanged joint
     kernels, span membership, and product recovery found no exact D5 theorem.
     The frozen `binary_character_basis_minimality` theorem uses the same
     canonical character carrier but proves minimum-cardinality consequences,
     not this three-clause redundancy criterion, so it is imported as the
     family predecessor rather than wrapped.
   * Body-shape searches for intersections of character kernels, membership in
     the span of a character range, and finite products of recovered outputs
     found no D5 predicate or construction to reuse. This module introduces no
     new `def` or `abbrev`.
   * Exact pinned-Mathlib hit `mem_span_of_iInf_ker_le_ker` converts preservation
     of the existing joint kernel into character-span membership.
   * Exact pinned-Mathlib hits
     `Finsupp.mem_span_range_iff_exists_finsupp` and
     `ofAdd_sum` expose finite coefficients and turn their
     additive binary combination into the public product recovery formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Module Set

namespace D5.S3.Fourier.BinaryCharacterRedundancyCriterion

set_option maxHeartbeats 2000000 in
-- The two span/coefficient equivalences require extended elaboration time.
/-- For binary characters evaluated on the original group through its canonical
quotient by doubles, the following are equivalent: the new character vanishes
on the existing joint kernel, it belongs to the span of the existing roles,
and its multiplicative binary output is a finite product recovered from the
existing outputs. -/
theorem binary_character_redundancy_criterion
    {G : Type*} [AddCommGroup G]
    {roleIndex : Type*} [Finite roleIndex]
    (characters : roleIndex → Module.Dual (ZMod 2) (ModN G 2))
    (newCharacter : Module.Dual (ZMod 2) (ModN G 2)) :
    List.TFAE [
      ∀ g : G,
        (∀ i, characters i (ModN.mkQ 2 g) = 0) →
          newCharacter (ModN.mkQ 2 g) = 0,
      newCharacter ∈ Submodule.span (ZMod 2) (Set.range characters),
      ∃ coefficients : roleIndex →₀ ZMod 2, ∀ g : G,
        Multiplicative.ofAdd (newCharacter (ModN.mkQ 2 g)) =
          ∏ i ∈ coefficients.support,
            Multiplicative.ofAdd
              (coefficients i * characters i (ModN.mkQ 2 g))] := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hKernel
      apply mem_span_of_iInf_ker_le_ker
      intro x hx
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
      revert hx
      refine QuotientAddGroup.induction_on x ?_
      intro g hx
      exact hKernel g hx
    · intro hSpan g hKernel
      have spanLe :
          Submodule.span (ZMod 2) (Set.range characters) ≤
            LinearMap.ker
              (Module.Dual.eval (ZMod 2) (ModN G 2) (ModN.mkQ 2 g)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        apply LinearMap.mem_ker.mpr
        simpa only [Module.Dual.eval_apply] using hKernel i
      simpa only [LinearMap.mem_ker, Module.Dual.eval_apply] using spanLe hSpan
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hSpan
      obtain ⟨coefficients, hcoefficients⟩ :=
        Finsupp.mem_span_range_iff_exists_finsupp.mp hSpan
      refine ⟨coefficients, ?_⟩
      intro g
      have hvalue :
          (∑ i ∈ coefficients.support,
              coefficients i * characters i (ModN.mkQ 2 g)) =
            newCharacter (ModN.mkQ 2 g) := by
        have evaluated := congrArg
          (fun character => character (ModN.mkQ 2 g)) hcoefficients
        simpa only [Finsupp.sum, smul_eq_mul, LinearMap.coe_sum,
          Finset.sum_apply, LinearMap.smul_apply] using evaluated
      rw [← hvalue]
      exact ofAdd_sum _ _
    · rintro ⟨coefficients, hrecover⟩
      apply Finsupp.mem_span_range_iff_exists_finsupp.mpr
      refine ⟨coefficients, ?_⟩
      have mkQ_surjective : Function.Surjective (ModN.mkQ (G := G) 2) := by
        change Function.Surjective
          (LinearMap.range
            (LinearMap.lsmul ℤ G (↑(2 : Nat) : ℤ))).mkQ
        exact (LinearMap.range
          (LinearMap.lsmul ℤ G (↑(2 : Nat) : ℤ))).mkQ_surjective
      ext x
      obtain ⟨g, rfl⟩ := mkQ_surjective x
      have recoveredAdd := congrArg Multiplicative.toAdd (hrecover g)
      simpa only [Finsupp.sum, smul_eq_mul, LinearMap.coe_sum,
        Finset.sum_apply, LinearMap.smul_apply, toAdd_ofAdd,
        toAdd_prod] using recoveredAdd.symm
  tfae_finish

#print axioms binary_character_redundancy_criterion

end D5.S3.Fourier.BinaryCharacterRedundancyCriterion
