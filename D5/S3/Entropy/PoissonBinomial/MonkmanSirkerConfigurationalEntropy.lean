/- GID: D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define the Poisson-binomial configurational entropy and the Monkman--Sirker majorization claim.
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Tuple.Sort

namespace D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy

open scoped BigOperators

private noncomputable def descendingPerm {M : ℕ} (c : Fin M → ℝ) : Equiv.Perm (Fin M) :=
  Fin.revPerm.trans (Tuple.sort c)

private noncomputable def descending {M : ℕ} (c : Fin M → ℝ) : Fin M → ℝ :=
  c ∘ descendingPerm c

private noncomputable def prefixSum {M : ℕ} (k : ℕ) (c : Fin M → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin M => (i : ℕ) < k), descending c i

noncomputable def pb {M : ℕ} (c : Fin M → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ.powerset.filter (fun A => A.card = k)),
    (∏ i ∈ A, c i) * ∏ i ∈ Aᶜ, (1 - c i)

noncomputable def F {M : ℕ} (c : Fin M → ℝ) : ℝ :=
  (∑ i, Real.binEntropy (c i)) -
    ∑ k ∈ Finset.range (M + 1), Real.negMulLog (pb c k)

def Majorizes {M : ℕ} (c d : Fin M → ℝ) : Prop :=
  (∑ i, c i = ∑ i, d i) ∧ ∀ k ≤ M, prefixSum k d ≤ prefixSum k c

def claim : Prop :=
  ∀ (M : ℕ) (c d : Fin M → ℝ),
    (∀ i, c i ∈ Set.Icc 0 1) →
    (∀ i, d i ∈ Set.Icc 0 1) →
    Majorizes c d → F c ≤ F d

end D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
