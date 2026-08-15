/- GID: D5/S0/Diagonal/Extrema/MaximumDistanceDistribution
   generality: G
   mirror-B: D5/B/S0/Diagonal/Extrema/MaximumDistanceDistribution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact finite distribution function for the maximum diagonal row distance. -/

import D5.S0.Diagonal.DistanceProfile

open scoped BigOperators

universe u v

namespace D5.S0.Diagonal.Extrema.MaximumDistanceDistribution

open DistanceProfile

variable {A : Type u} {Y : Type v}

/- Provenance: the pinned repository search found no maximum-distance distribution theorem.
   The proof applies `distance_profile_card` and pinned mathlib's finite sigma/product APIs. -/

/-- The distribution function of the maximum row distance is the power of the single-row
lower prefix. -/
theorem maximum_distance_cdf [Fintype A] [Fintype Y] (f : Y → Y) (r : ℕ) :
    Nat.card {g : A → A → Y // ∀ a, hammingDistance f g a ≤ r} =
      (∑ j ∈ Finset.Icc 0 r, rowDistanceCount (A := A) f j) ^ Fintype.card A := by
  classical
  letI : Fintype {j : ℕ // j ≤ r} := Fintype.ofFinite _
  let distanceVector : (A → A → Y) → A → ℕ :=
    fun g a => hammingDistance f g a
  let profileEquiv :
      {profile : A → ℕ // ∀ a, profile a ≤ r} ≃
        ((a : A) → {j : ℕ // j ≤ r}) :=
    Equiv.subtypePiEquivPi (p := fun (_a : A) (j : ℕ) => j ≤ r)
  letI : Fintype {profile : A → ℕ // ∀ a, profile a ≤ r} :=
    Fintype.ofEquiv _ profileEquiv.symm
  let e :
      (Σ profile : {profile : A → ℕ // ∀ a, profile a ≤ r},
        {g : A → A → Y // distanceVector g = profile.1}) ≃
          {g : A → A → Y // ∀ a, hammingDistance f g a ≤ r} :=
    Equiv.sigmaSubtypeFiberEquivSubtype distanceVector (fun _g => Iff.rfl)
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e.symm, Fintype.card_sigma]
  calc
    (∑ profile : {profile : A → ℕ // ∀ a, profile a ≤ r},
        Fintype.card
          {g : A → A → Y // distanceVector g = profile.1}) =
        ∑ profile : {profile : A → ℕ // ∀ a, profile a ≤ r},
          ∏ a, rowDistanceCount (A := A) f (profile.1 a) := by
      apply Finset.sum_congr rfl
      intro profile _
      have hFiber :
          Fintype.card {g : A → A → Y // distanceVector g = profile.1} =
            Fintype.card
              {g : A → A → Y //
                ∀ a, hammingDistance f g a = profile.1 a} := by
        apply Fintype.card_congr
        exact (Equiv.refl (A → A → Y)).subtypeEquiv fun g => by
          change distanceVector g = profile.1 ↔
            ∀ a, hammingDistance f g a = profile.1 a
          exact funext_iff
      rw [hFiber]
      simpa only [Nat.card_eq_fintype_card] using
        distance_profile_card (A := A) f profile.1
    _ = ∑ profile : (a : A) → {j : ℕ // j ≤ r},
          ∏ a, rowDistanceCount (A := A) f (profile a).1 := by
      exact profileEquiv.sum_comp fun profile =>
        ∏ a, rowDistanceCount (A := A) f (profile a).1
    _ = ∏ _a : A, ∑ j : {j : ℕ // j ≤ r}, rowDistanceCount (A := A) f j.1 := by
      symm
      exact Fintype.prod_sum fun (_a : A) (j : {j : ℕ // j ≤ r}) =>
        rowDistanceCount (A := A) f j.1
    _ = ∏ _a : A, ∑ j ∈ Finset.Icc 0 r, rowDistanceCount (A := A) f j := by
      apply Finset.prod_congr rfl
      intro _a _
      rw [← Finset.sum_subtype (p := fun j : ℕ => j ≤ r) (Finset.Icc 0 r) (by simp)]
    _ = _ := Finset.prod_const _

#print axioms maximum_distance_cdf

end D5.S0.Diagonal.Extrema.MaximumDistanceDistribution
