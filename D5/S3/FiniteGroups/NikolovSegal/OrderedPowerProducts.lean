/- GID: D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact ordered power products lift factor by factor through surjective homomorphisms. -/

import D5.S3.Factorization.Galois.ProfinitePowerTransfer

set_option autoImplicit false

/-!
Ordered products, without a commutativity assumption. The number of factors
is exactly `m`, with identity factors allowed; `m = 0` is the empty product.
-/

open D5.S3.Factorization.Galois.PowerCompactness
  D5.S3.Factorization.Galois.ProfinitePowerTransfer

namespace NikolovSegal

universe u

/-- The paper's `G_q^{*m}`, as an ordered list of `m` qth powers. -/
def orderedPowerProducts (G : Type u) [Group G] (q m : ℕ) : Set G :=
  Set.range (powerProduct (G := G) q m)

variable {G Q : Type u} [Group G] [Group Q]

theorem one_mem_orderedPowerProducts (q m : ℕ) :
    (1 : G) ∈ orderedPowerProducts G q m := by
  refine ⟨fun _ => 1, ?_⟩
  simp [powerProduct]

/-- An exact-length power product in a quotient lifts factor by factor. -/
theorem lift_orderedPowerProducts (f : G →* Q) (hf : Function.Surjective f)
    {q m : ℕ} {x : Q} (hx : x ∈ orderedPowerProducts Q q m) :
    ∃ y ∈ orderedPowerProducts G q m, f y = x := by
  classical
  obtain ⟨t, ht⟩ := hx
  choose s hs using fun i => hf (t i)
  refine ⟨powerProduct q m s, ⟨s, rfl⟩, ?_⟩
  rw [map_powerProduct]
  simpa only [hs] using ht

end NikolovSegal
