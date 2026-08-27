# OACTC theorem 13.1 formalization receipt

Date: 2026-08-28
Atom: `generic-residual-bb0d9ca298be3f69a754bf262836596105ad49dc6ae99793bdc4ff1992690fd1`
CAS: `sha256:bb0d9ca298be3f69a754bf262836596105ad49dc6ae99793bdc4ff1992690fd1`

## Repository declarations and duplicate coverage

- Searched `D5/**/*.lean` and `Blueprint/**/*.scribe.cs` with `rg` for `heat trace`,
  `heatTrace`, `linear density`, `Stieltjes`, `Laplace`, `Mellin`, `IsBigO`, and the atom id.
- The atom id occurs only in its open digestion ticket under
  `Meta/Digestion/backfill/observer-adelic-completion-constant-theory/residual-open/`.
- `D5/S3/Midline/UniversalHeatTrace.lean` defines a general heat trace as an exponential
  `tsum` and proves summability and Hilbert-space threshold results. It has no counting-density
  asymptotic theorem.
- `D5/S3/Midline/HeatTraceConvergence.lean`,
  `D5/S3/Midline/ZetaHeatTraceBridge.lean`, and the other heat-trace modules are specialized
  convergence or identity results. None proves that `N(u) = c*u + O(1)` implies
  `Theta(t) = c/t + O(1)`.
- Reverse-coverage result: no other repository module covers theorem 13.1 or an equivalent
  generic counting-density-to-heat-trace bridge.
- Capacity receipt: `ls D5/S3/Analytic/ | wc -l` returned `31`, above the SL-003 threshold
  `12`. `ls D5/S3/Analytic/Asymptotics/ | wc -l` returned `1`, so the module routes through
  the `Asymptotics` subdomain.

## Pinned mathlib

- Searched `.lake/packages/mathlib/Mathlib/**/*.lean` with `rg` for Stieltjes integration,
  Laplace and Mellin transforms, Abel summation, layer-cake formulas, exponential improper
  integrals, nonnegative sum-integral interchange, and asymptotic boundedness.
- No exact theorem matching the requested heat-trace asymptotic was found.
- Exact declarations reused:
  - `Real.integral_rpow_mul_exp_neg_mul_Ioi` computes the linear exponential moment.
  - `integrableOn_exp_mul_Ioi` supplies integrability of the exponential kernel.
  - `MeasureTheory.lintegral_tsum` supplies the nonnegative Tonelli interchange used to prove
    the spectral-sum/counting-integral bridge.
  - `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` converts the finite nonnegative
    integrals back to real integrals.
  - `Asymptotics.IsBigO.of_bound` packages the uniform residual estimate as `O(1)`.
- `StieltjesFunction.measure`, layer-cake formulas, and
  `Mathlib.NumberTheory.AbelSummation` exist, but none directly states the arbitrary-real-spectrum
  bridge required here.
- Difficulty isolated by the search: mathlib provides the exponential moments, Tonelli, and
  asymptotic packaging. The local proof must identify the pointwise indicator sum with the
  finite counting function, prove heat-trace summability, and derive the Laplace bridge without
  assuming it.

## Third-party Lean ecosystem

- Loogle queries for `integral_rpow_mul_exp_neg_mul_Ioi`, Stieltjes integrals, and exponential
  transforms returned the pinned mathlib Gamma-integral declaration but no heat-trace
  asymptotic theorem.
- A LeanSearch natural-language query for `linear counting density implies heat trace c/t plus
  bounded error` returned unrelated approximation, counting-measure, and finite-dimensional
  trace results.
- GitHub Lean-code searches for `heatTrace IsBigO`, `linear density heat trace`, and
  `StieltjesFunction laplace` found no matching theorem. Gamma-integral hits were mathlib or
  downstream uses of the same mathlib declaration.
- Reservoir was checked as the package index; the corresponding package and GitHub searches
  identified no exact third-party result.

## Formalization decision and provenance

The public declaration is
`D5/S3/Analytic/Asymptotics/LinearDensityHeatTrace.linear_density_heat_trace`.
Its premises have the following source provenance:

- `hpos : forall n, 0 < lambda n` is the source clause `0 < lambda_1` together with the displayed
  positive increasing spectrum `0 < lambda_1 < lambda_2 < ...`.
- `hstrict : StrictMono lambda` is exactly the strict inequalities in
  `0 < lambda_1 < lambda_2 < ...`.
- `hfinite : forall u, Set.Finite {n | lambda n <= u}` records the finiteness already asserted by
  writing `N(u) = #{n : lambda_n <= u}` as a real-valued counting function. This is not an
  analytic strengthening: it prevents `Set.ncard` from taking its documented junk value on an
  infinite set.
- `hdensity : (spectralCounting lambda u - c*u) =O[atTop] 1` is exactly
  `N(u) = c*u + O(1)`.
- `spectralHeatTrace lambda t` is definitionally the source sum
  `sum_n exp(-t*lambda_n)`; indexing by Lean naturals is the zero-based reindexing of `n >= 1`.
- The conclusion is the residual form
  `spectralHeatTrace lambda t - c/t =O[nhdsWithin 0 (Ioi 0)] 1`, exactly
  `Theta(t) = c/t + O(1)` for `t` decreasing to zero through positive values.

There are no RH assumptions, conjectural premises, or hypotheses asserting the
Stieltjes/Laplace bridge. That bridge and summability of the exponential series are proved in
the module using nonnegative Tonelli.

## Fidelity probes

### Reverse probe

The `example` following the public theorem applies only the theorem's public type and derives

```lean
exists K, forall eventually t in nhdsWithin 0 (Set.Ioi 0),
  norm (spectralHeatTrace lambda t - c / t) <= K
```

This is a nontrivial consequence: the actual spectral `tsum` residual, not an auxiliary integral,
is eventually uniformly bounded on the positive side of zero.

### Trivialization probe

Set the key spectrum parameter to the trivial sequence `lambda n = 0`. The public type cannot be
instantiated: `hpos` becomes `0 < 0`, `hstrict` becomes strict monotonicity of a constant function,
and for every `u >= 0` the counting set is all of `Nat`, contradicting `hfinite`. Thus a zero or
constant spectrum cannot make the theorem vacuous. The nondegeneracy conditions are present in
the proposition itself, not hidden in the proof.
