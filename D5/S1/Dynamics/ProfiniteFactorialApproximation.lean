/- GID: D5/S1/Dynamics/ProfiniteFactorialApproximation
   generality: I
   mirror-B: D5/B/S1/Dynamics/ProfiniteFactorialApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical factorial-stage natural representatives converge to every profinite integer. -/

import D5.S1.Dynamics.ProfiniteIntegers

namespace D5.S1.Dynamics.ProfiniteIntegers

/-- The least natural representative of `x` at the modulus `n!`. -/
def factorialRepresentative (x : ProfiniteIntegers) (n : Nat) : Nat :=
  (x.1 (n.factorial - 1)).val

/-- The natural embeddings of the factorial-stage representatives converge to
the original compatible residue family. -/
theorem natEmbedding_factorialRepresentative_tendsto (x : ProfiniteIntegers) :
    Filter.Tendsto (fun n : Nat => natEmbedding (factorialRepresentative x n))
      Filter.atTop (nhds x) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro m
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [Filter.eventually_ge_atTop (m + 1)] with n hn
  change ((x.1 (n.factorial - 1)).val : ZMod (m + 1)) = x.1 m
  have hfactorial : n.factorial - 1 + 1 = n.factorial :=
    Nat.sub_add_cancel (Nat.factorial_pos n)
  have hdiv : m + 1 ∣ n.factorial - 1 + 1 := by
    rw [hfactorial]
    exact Nat.dvd_factorial (Nat.succ_pos m) hn
  simpa [ZMod.castHom_apply] using x.2 hdiv

end D5.S1.Dynamics.ProfiniteIntegers
