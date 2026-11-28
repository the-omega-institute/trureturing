/- GID: D5/S3/Combinatorics/ExtremalDensity/RootedTwinHomCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/RootedTwinHomCount
   mirror-E: none(waiver:formal-unit-only)
   anchors: [lake/module/OmegaMath.Combinatorics.RootedTwinHomCount]
   utility: none
   digest: The fixed-centre homomorphism count of two rooted copies is at most a quarter square. -/

import D5.S3.Combinatorics.RootedTwinHomCount

/-! The isomorphic-pair bound of Proposition 5.2, for every asymmetric host relation. -/

namespace D5.S3.Combinatorics.ExtremalDensity.RootedTwinHomCount

universe u v

/-- Book citation of the general rooted-twin counting theorem. -/
theorem quarter_bound {A : Type u} {B : Type v} [Finite A] [Finite B]
    (H : Digraph A) (w : A) (R : B → B → Prop)
    (hR : ∀ x y, R x y → ¬ R y x) (t : B) :
    4 * Nat.card {f : RelHom (Omega.RootedTwinHomCount.rootedTwin H w).Adj R // f none = t} ≤
      (Nat.card (RelHom H.Adj R)) ^ 2 :=
  Omega.RootedTwinHomCount.quarter_bound H w R hR t

end D5.S3.Combinatorics.ExtremalDensity.RootedTwinHomCount
