/- GID: D5/S3/Analytic/EntropyRelabellingInvariance/CountableFunctionalsMapInvariance
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Countable Shannon, Renyi, and min-entropy are invariant under injective relabelling. -/

import D5.S3.Analytic.Zeta.ZetaMinEntropy

/-!
# Countable entropy functionals depend only on masses, not labels

The three countable entropy functionals are invariant under every injective relabelling of
`Nat`. Injectivity is the exact common hypothesis: on the image, `PMF.map` preserves each mass;
off the image, it adds only zero masses. Shannon atoms and nonzero-order Renyi atoms vanish at
zero. Two Renyi orders are degenerate rather than substantive: at order zero every atom is
`x ^ (0 : Real) = 1`, including the added zero masses, so the constant-one series over the
infinite carrier `Nat` is not summable, its totalized `tsum` is `0`, and `Real.log 0 = 0`; at
order one the totalized coefficient `1 / (1 - alpha)` is `0`. At those two orders both sides are
the same totalized constant for every `PMF Nat`, so the identity carries no relabelling content.
The supremum defining min-entropy is unchanged because the added masses are zero.

The mathematical content is general for arbitrary `PMF Nat`, with no zeta-specific hypothesis.
Nevertheless this artifact must have `generality: I`: the three existing definitions live in
`generality: I` modules, and H10 forbids a `G` artifact from importing those instance-tier facts.
Restating the definitions here would create a forbidden second source of truth.

Search receipt (2026-08-23): recursive repository searches for the three definition names paired
with `map`, `equiv`, `inject`, `relabel`, and `congr` found no invariance theorem. In pinned
mathlib, `PMF.map_apply` evaluates the defining pushforward sum, `tsum_eq_single` evaluates it at
an image point under injectivity, and `Function.Injective.tsum_eq` reindexes a `tsum` whose support
lies in the image. For the conditional supremum, `PMF.coe_le_one`, `ENNReal.toReal_mono`,
`ciSup_le`, and `le_ciSup` provide the required boundedness and comparison. No third-party search
was needed after these exact pinned APIs resolved.
-/

namespace D5.S3.Analytic.EntropyRelabellingInvariance.CountableFunctionalsMapInvariance

open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy
open D5.S3.Analytic.Zeta.ZetaMinEntropy

noncomputable section

private lemma pmfReal_map_apply_of_injective (f : Nat → Nat) (hf : Function.Injective f)
    (p : PMF Nat) (n : Nat) :
    pmfReal (p.map f) (f n) = pmfReal p n := by
  unfold pmfReal
  congr 1
  rw [PMF.map_apply]
  rw [tsum_eq_single n]
  · simp
  · intro m hmn
    rw [if_neg]
    exact fun h ↦ hmn (hf h).symm

private lemma pmfReal_map_eq_zero_of_not_mem_range (f : Nat → Nat) (p : PMF Nat)
    (k : Nat) (hk : k ∉ Set.range f) :
    pmfReal (p.map f) k = 0 := by
  have hmass : (p.map f) k = 0 := ((p.map f).apply_eq_zero_iff k).mpr (by
    intro hsupport
    rw [PMF.mem_support_map_iff] at hsupport
    rcases hsupport with ⟨n, _, hn⟩
    exact hk ⟨n, hn⟩)
  simp [pmfReal, hmass]

private lemma tsum_atom_map_of_injective (phi : Real → Real) (hphi_zero : phi 0 = 0)
    (f : Nat → Nat) (hf : Function.Injective f) (p : PMF Nat) :
    ∑' k, phi (pmfReal (p.map f) k) = ∑' n, phi (pmfReal p n) := by
  have hsupport :
      Function.support (fun k ↦ phi (pmfReal (p.map f) k)) ⊆ Set.range f := by
    intro k hk
    by_contra hkrange
    apply hk
    change phi (pmfReal (p.map f) k) = 0
    rw [pmfReal_map_eq_zero_of_not_mem_range f p k hkrange, hphi_zero]
  symm
  calc
    ∑' n, phi (pmfReal p n) = ∑' n, phi (pmfReal (p.map f) (f n)) := by
      apply tsum_congr
      intro n
      rw [pmfReal_map_apply_of_injective f hf p n]
    _ = ∑' k, phi (pmfReal (p.map f) k) := hf.tsum_eq hsupport

private lemma pmfReal_nonneg (p : PMF Nat) (n : Nat) : 0 ≤ pmfReal p n :=
  ENNReal.toReal_nonneg

private lemma pmfReal_le_one (p : PMF Nat) (n : Nat) : pmfReal p n ≤ 1 := by
  simpa [pmfReal] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one n)

private lemma pmfReal_bddAbove (p : PMF Nat) : BddAbove (Set.range (pmfReal p)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact pmfReal_le_one p n

private lemma iSup_pmfReal_map_of_injective (f : Nat → Nat) (hf : Function.Injective f)
    (p : PMF Nat) :
    (⨆ k, pmfReal (p.map f) k) = ⨆ n, pmfReal p n := by
  apply le_antisymm
  · apply ciSup_le
    intro k
    by_cases hk : k ∈ Set.range f
    · rcases hk with ⟨n, rfl⟩
      rw [pmfReal_map_apply_of_injective f hf p n]
      exact le_ciSup (pmfReal_bddAbove p) n
    · rw [pmfReal_map_eq_zero_of_not_mem_range f p k hk]
      exact (pmfReal_nonneg p 0).trans (le_ciSup (pmfReal_bddAbove p) 0)
  · apply ciSup_le
    intro n
    rw [← pmfReal_map_apply_of_injective f hf p n]
    exact le_ciSup (pmfReal_bddAbove (p.map f)) (f n)

/-- Countable Shannon entropy is invariant under every injective relabelling of `Nat`. -/
theorem countableEntropy_map_of_injective (f : Nat → Nat) (hf : Function.Injective f)
    (p : PMF Nat) :
    countableEntropy (p.map f) = countableEntropy p := by
  exact tsum_atom_map_of_injective Real.negMulLog (by simp) f hf p

/-- Countable Renyi entropy is invariant under every injective relabelling, at every real order.

Orders zero and one are degenerate rather than substantive: at order zero the atoms are constantly
`1`, so the series over the infinite carrier `Nat` is not summable and totalizes to `0` before the
logarithm; at order one the totalized coefficient `1 / (1 - alpha)` is `0`. At both, the two sides
are the same totalized constant for every `PMF Nat`. Every other real order carries genuine
relabelling content. -/
theorem countableRenyiEntropy_map_of_injective (alpha : Real) (f : Nat → Nat)
    (hf : Function.Injective f) (p : PMF Nat) :
    countableRenyiEntropy alpha (p.map f) = countableRenyiEntropy alpha p := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp [countableRenyiEntropy]
  · rw [countableRenyiEntropy, countableRenyiEntropy,
      tsum_atom_map_of_injective (fun x ↦ x ^ alpha) (Real.zero_rpow halpha) f hf p]

/-- Countable min-entropy is invariant under every injective relabelling of `Nat`. -/
theorem countableMinEntropy_map_of_injective (f : Nat → Nat) (hf : Function.Injective f)
    (p : PMF Nat) :
    countableMinEntropy (p.map f) = countableMinEntropy p := by
  rw [countableMinEntropy, countableMinEntropy, iSup_pmfReal_map_of_injective f hf p]

end

end D5.S3.Analytic.EntropyRelabellingInvariance.CountableFunctionalsMapInvariance
