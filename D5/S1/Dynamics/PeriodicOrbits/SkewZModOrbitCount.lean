/- GID: D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Möbius inversion preserves the cyclic-fiber holonomy factor in exact orbit counts. -/

import D5.S1.Dynamics.PeriodicOrbits.SkewZModFixedCount

/-! # Möbius orbit counts for cyclic additive skew products -/

set_option autoImplicit false

namespace D5.S1.Dynamics.PeriodicOrbits.SkewZModOrbitCount

open Function
open D5.S1.Descent.FiniteSelfMapConjugacy (cycleLengthMultiplicity)
open D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
open D5.S1.Dynamics.PeriodicOrbits.SkewAdditiveReturn
open D5.S1.Dynamics.PeriodicOrbits.SkewZModFixedCount

variable {X : Type*} {q : ℕ}

open scoped Classical in
/-- The base return table seen by a cyclic skew product after imposing zero holonomy. -/
noncomputable def zeroHolonomyCount (f : X → X) (c : X → ZMod q) [Fintype X] (n : ℕ) : ℕ :=
  Fintype.card {x : X // f^[n] x = x ∧ birkhoffSum f c n x = 0}

/-- Möbius inversion commutes with the q-fold phase multiplicity of a cyclic skew product.

Thus the exact orbit-count transform of the lifted system is already visible in the
zero-holonomy return table on the base. -/
theorem delta_fixed_count_skew_zmod (f : X → X) (c : X → ZMod q) [Fintype X]
    [NeZero q] (n : ℕ) :
    delta (fixedCount (skewStep f c)) n =
      (q : ℤ) * delta (zeroHolonomyCount f c) n := by
  unfold delta
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [fixed_count_skew_zmod f c p.2]
  simp only [zeroHolonomyCount, Nat.cast_mul]
  ring_nf

/-- The weighted number of exact lifted cycles factors through the fiber cardinality.

For positive time, the left side is the usual `n`-weighted primitive cycle count;
the right side is q times the Möbius transform of zero-holonomy returns. -/
theorem weighted_cycle_count_factorization (f : X → X) (c : X → ZMod q) [Fintype X]
    [NeZero q] {n : ℕ} (hn : 0 < n) :
    (n : ℤ) * cycleLengthMultiplicity (skewStep f c) n =
      (q : ℤ) * delta (zeroHolonomyCount f c) n := by
  calc
    (n : ℤ) * cycleLengthMultiplicity (skewStep f c) n =
        delta (fixedCount (skewStep f c)) n :=
      (delta_fixed_count (skewStep f c) hn).symm
    _ = (q : ℤ) * delta (zeroHolonomyCount f c) n :=
      delta_fixed_count_skew_zmod f c n

/-- Every positive-time weighted cycle count of a ZMod-q skew product is divisible by q. -/
theorem zmod_dvd_weighted_cycle_count (f : X → X) (c : X → ZMod q) [Fintype X]
    [NeZero q] {n : ℕ} (hn : 0 < n) :
    (q : ℤ) ∣ (n : ℤ) * cycleLengthMultiplicity (skewStep f c) n := by
  rw [weighted_cycle_count_factorization f c hn]
  exact dvd_mul_right _ _

#print axioms delta_fixed_count_skew_zmod
#print axioms weighted_cycle_count_factorization
#print axioms zmod_dvd_weighted_cycle_count

end D5.S1.Dynamics.PeriodicOrbits.SkewZModOrbitCount
