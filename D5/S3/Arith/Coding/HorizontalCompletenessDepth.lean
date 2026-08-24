/- GID: D5/S3/Arith/Coding/HorizontalCompletenessDepth
   generality: G
   mirror-B: D5/B/S3/Arith/Coding/HorizontalCompletenessDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: On the natural interval [0,N], joint reduction modulo the first r primes is injective exactly when their product exceeds N, so the least faithful horizontal depth is the first such r. -/

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PrimeCounting

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'horizontal_completeness_depth' D5 Golden/Frozen/accepted` and the
     corresponding search for `residue_reading_injOn_iff_primorial_gt` returned no matches.
   * Repository searches for `Nat.nth`, `primorial`, `InjOn.*ZMod`, and `residueReading`
     found `PrimeSequenceCode`, which reuses `Nat.nth Nat.Prime`, but no finite-window
     injectivity threshold. The public `ResidueSeparation` is a one-modulus bound, while
     `FiniteWindowEscape` proves noninjectivity on all integers; neither covers this result.
   * The corresponding `private theorem|lemma` search found unrelated injectivity results,
     but no private result about first-prime residue products or a finite-window threshold.
     The target `Coding` directory contained only the unrelated Hamming-code module
     `ResidueCodeErrorDetection`.
   * Pinned Mathlib has no theorem with this bounded `InjOn` equivalence. The proof reuses
     `Nat.modEq_list_map_prod_iff`, `ZMod.natCast_eq_natCast_iff`, `Nat.coprime_primes`,
     `Nat.nth_strictMono`, `Nat.add_two_le_nth_prime`, and `Nat.lt_two_pow_self`, then supplies
     the finite-window argument and the explicit collision at zero and the prefix product.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Function

noncomputable section

namespace D5.S3.Arith.Coding.HorizontalCompletenessDepth

/-- The product of the first `r` primes, with the empty product equal to one. -/
def primePrefixProduct (r : Nat) : Nat :=
  ∏ i ∈ Finset.range r, Nat.nth Nat.Prime i

/-- The joint single-power residue reading modulo the first `r` primes. -/
def residueReading (r x : Nat) : (i : Fin r) → ZMod (Nat.nth Nat.Prime i) :=
  fun _ => x

/-- On `[0, N]`, the first `r` prime residues are jointly injective exactly when their
modulus product is greater than `N`. -/
theorem residue_reading_injOn_iff_primorial_gt (N r : Nat) :
    Set.InjOn (residueReading r) (Set.Icc 0 N) ↔ N < primePrefixProduct r := by
  have hcoprime :
      (List.range r).Pairwise (Nat.Coprime on fun i => Nat.nth Nat.Prime i) := by
    refine List.pairwise_lt_range.imp ?_
    intro i j hij
    exact (Nat.coprime_primes (Nat.prime_nth_prime i) (Nat.prime_nth_prime j)).2
      (Nat.nth_strictMono Nat.infinite_setOf_prime hij).ne
  constructor
  · intro hinjective
    by_contra hnotGreater
    have hproduct_le : primePrefixProduct r ≤ N := Nat.le_of_not_gt hnotGreater
    have hzero_mem : 0 ∈ Set.Icc 0 N := ⟨Nat.zero_le _, Nat.zero_le _⟩
    have hproduct_mem : primePrefixProduct r ∈ Set.Icc 0 N :=
      ⟨Nat.zero_le _, hproduct_le⟩
    have hsame : residueReading r 0 = residueReading r (primePrefixProduct r) := by
      funext i
      simp only [residueReading]
      rw [eq_comm]
      simpa only [Nat.cast_zero] using
        (ZMod.natCast_eq_zero_iff (primePrefixProduct r) (Nat.nth Nat.Prime i)).2
          (Finset.dvd_prod_of_mem (fun j => Nat.nth Nat.Prime j)
            (Finset.mem_range.mpr i.isLt))
    have hproduct_zero : 0 = primePrefixProduct r :=
      hinjective hzero_mem hproduct_mem hsame
    have hproduct_pos : 0 < primePrefixProduct r := by
      apply Nat.pos_of_ne_zero
      rw [primePrefixProduct, Finset.prod_ne_zero_iff]
      intro i hi
      exact (Nat.prime_nth_prime i).ne_zero
    exact (Nat.ne_of_gt hproduct_pos) hproduct_zero.symm
  · intro hgreater x hx y hy hsame
    have hmod : x ≡ y [MOD primePrefixProduct r] := by
      rw [← show ((List.range r).map (fun i => Nat.nth Nat.Prime i)).prod =
          primePrefixProduct r by
        rw [primePrefixProduct, ← List.prod_toFinset _ List.nodup_range,
          List.toFinset_range]]
      apply (Nat.modEq_list_map_prod_iff hcoprime).2
      intro i hi
      apply (ZMod.natCast_eq_natCast_iff x y _).mp
      simpa [residueReading] using congrFun hsame ⟨i, List.mem_range.mp hi⟩
    exact hmod.eq_of_lt_of_lt (hx.2.trans_lt hgreater) (hy.2.trans_lt hgreater)

/-- Some finite prefix of the primes has product greater than any prescribed bound. -/
theorem exists_primePrefixProduct_gt (N : Nat) :
    ∃ r, N < primePrefixProduct r := by
  refine ⟨N, ?_⟩
  calc
    N < 2 ^ N := N.lt_two_pow_self
    _ = ∏ _i ∈ Finset.range N, 2 := by simp
    _ ≤ primePrefixProduct N := by
      rw [primePrefixProduct]
      apply Finset.prod_le_prod'
      intro i hi
      exact (Nat.le_add_left 2 i).trans (Nat.add_two_le_nth_prime i)

/-- The least number of initial prime residues whose modulus product exceeds `N`. -/
def horizontalDepth (N : Nat) : Nat :=
  Nat.find (exists_primePrefixProduct_gt N)

/-- `horizontalDepth N` is exactly the least jointly faithful prime-residue depth on
the natural interval `[0, N]`. -/
theorem horizontal_completeness_depth (N : Nat) :
    IsLeast {r : Nat | Set.InjOn (residueReading r) (Set.Icc 0 N)}
      (horizontalDepth N) := by
  constructor
  · apply (residue_reading_injOn_iff_primorial_gt N (horizontalDepth N)).2
    exact Nat.find_spec (exists_primePrefixProduct_gt N)
  · intro r hr
    apply Nat.find_min' (exists_primePrefixProduct_gt N)
    exact (residue_reading_injOn_iff_primorial_gt N r).1 hr

example :
    IsLeast {r : Nat | Set.InjOn (residueReading r) (Set.Icc 0 10)}
      (horizontalDepth 10) := by
  exact horizontal_completeness_depth 10

#print axioms horizontal_completeness_depth

end D5.S3.Arith.Coding.HorizontalCompletenessDepth
