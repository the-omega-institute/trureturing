/- GID: D5/S3/Combinatorics/Matroids/SpeyerUniformNormality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SpeyerUniformNormality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Growing uniform-matroid ranks satisfy the central and local normal limit theorems. -/

/- admission_basis: open-problem-resolution (#15111; Proved)
   Direct frozen dependencies (declaration GID and declaration statement_id):
   F0: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance sha256:acf3515171050627eccee903208eb3f1d603d5d3ff4cc74a94c0c95259871d6f
   F1: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_le_quarter sha256:d26843918e966727ef778f8c78682791d54fdc06c6a8b7c77e5a9601dd05c43e
   Module escape_witness: bernoulli_array_uniform_lattice_limit (same-delivery content)
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15743
   Template gap: No divergent-rank-sequence realization or conjunction-of-limits readout is supplied.
   Four-slot evidence missing: source-specific arenas and observation/readout maps,
     exact reconstruction and realization bridges, E1–E8, variation and sensitivity.
   DTR reading: 1 DTR-Unregistered findings (Observe); no Reg mirror is supplied.
   claim: proof_shape: bind-only; escape_witness: none;
     consumers: statement/type consumers.
   result: proof_shape: content; escape_witness: splits_reverse;
     frozen_dependencies: F0, F1.
     consumers: statement/type consumers.
-/

import D5.S3.Combinatorics.Matroids.SpeyerUniformVariance

noncomputable section
open Polynomial Finset Filter Real Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval Interval
namespace D5.S3.Combinatorics.Matroids.SpeyerUniformNormality

open D5.S3.Analytic.Probability.BernoulliFourierControl D5.S3.Analytic.Probability.BernoulliTriangularLimits D5.S3.Combinatorics.Matroids.SpeyerUniformVariance
def claim : Prop := ∀ d : ℕ → ℕ,
  (∀ᶠ n in atTop, 1 ≤ d n ∧ d n ≤ n / 2) → Tendsto d atTop atTop →
  CLT (fun n => g n (d n)) ∧ LLT (fun n => g n (d n))


open Polynomial Finset Filter Real
open scoped BigOperators unitInterval Topology

theorem result : claim := by
  intro d hadm hd
  have hpair : ∀ᶠ n in atTop, 2≤d n ∧ 2*d n≤n := by
    filter_upwards [hadm,hd.eventually_ge_atTop 2] with n hn hdn
    exact ⟨hdn,by omega⟩
  have hex : ∀ n, ∃ m : ℕ, ∃ p : Fin m → unitInterval,
      (2≤d n ∧ 2*d n≤n) → normalized (g n (d n)) = X*∏ i, bernoulliPGF (p i:ℝ) := by
    intro n
    by_cases hn : 2≤d n ∧ 2*d n≤n
    · obtain ⟨m,p,hp,hpgf⟩ := g_bernoulli_factorization n (d n) hn.1 hn.2
      exact ⟨m,p,fun _ => hpgf⟩
    · exact ⟨0,(fun i => Fin.elim0 i),fun h => False.elim (hn h)⟩
  choose m p hp using hex
  have hfac : ∀ᶠ n in atTop, normalized (g n (d n)) = X*∏ i, bernoulliPGF (p n i:ℝ) :=
    hpair.mono (fun n hn => hp n hn)
  have hV : Tendsto (fun n => rowVariance (p n)) atTop atTop := by
    apply (speyer_variance_tendsto d hadm hd).congr'
    filter_upwards [hfac] with n hpgf
    exact (factorization_moments (p n) hpgf).2.2
  exact bernoulli_polynomial_uniform_limits (fun n => g n (d n)) p hfac hV

end D5.S3.Combinatorics.Matroids.SpeyerUniformNormality
