---
bibkey: schroeder2026noncoverage
authors: Michael Schroeder
year: 2026
title: "Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors"
doi: 10.5281/zenodo.22760638
url: https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_complete.zip
claim: "The author claims noncoverage for finite families of distinct odd moduli greater than one when each modulus has at most three distinct prime factors, with arbitrary exponents and arbitrary total prime support."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
  - D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison
  - D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/DistortionChain
  - D5/S3/Arith/Congruence/ConditionalComparison/ArithmeticCoordinates
  - D5/S3/Arith/Congruence/ActualCylinderChain
  - D5/S3/Arith/Congruence/ConditionalComparison/CappedGainTypes
license: "Paper and prose: CC BY 4.0; original Lean/Python code and certificate inputs: MIT; third-party licenses retained."
triage: anchor
---

# Three prime factors per modulus

## Verified locator

Locator: https://doi.org/10.5281/zenodo.22760638, version 1.0, manuscript dated
9 September and revised 15 September 2026. Metadata and supplied source read
16 September 2026. Archive:
https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_complete.zip.
SHA-256: `5956327277ac47dd6e98a0a38f2a785cd61e647560c7f6ab5c73a63cf49faa51`.
The archive root is `three-prime-factors-complete/`; its `LICENSE.md` assigns
copyright © 2026 Michael Schroeder and the component licenses above. No source
Git revision is supplied.

The source declaration `Erdos7.noncoverage_at_most_three_prime_factors` in
`formal/Erdos7/ThreePrime/Arithmetic.lean` takes `residue : Fin L → ℤ`,
`modulus : Fin L → ℕ`, nontriviality, oddness, injectivity, and explicitly
`hThree : ∀ k, (modulus k).primeFactors.card ≤ 3`. It concludes the existence
of an integer avoiding every class. Dropping `hThree` changes the theorem.
The paper's separate largest-prime-cutoff extension is not in this Lean result.

Pins: Lean `4.32.0-rc1`; mathlib
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, as recorded in
`formal/lean-toolchain` and `formal/lake-manifest.json`.
The official Lean release is commit `b4812ae53eea93439ad5dce5a5c26591c31cb697`;
its macOS ARM archive SHA-256 is
`181f967f61bbaf4864102d69c7a2167a7e3d1939df70e3ff3b8def8202fc768e`.

Completed local verification on 16 September 2026 rebuilt the author's source
with `python3 build_three_prime.py --jobs 4`: all 90 driver steps exited zero.
Both `lake env lean AuditThreePrime.lean` and its `--trust=0` variant exited
zero, reporting the target's axiom closure
`[propext, Classical.choice, Quot.sound]`. Importing with `--trust=0` alone does
not recheck all imported `.olean` bodies. Separately,
`lake env leanchecker --fresh --verbose Erdos7.ThreePrime.Arithmetic` exited zero:
the official checker replayed the imported and target constant environment
from an empty environment through `Environment.replay`. This uses the same
official Lean kernel; it is not a second verifier implementation.

The postbuild archive check rehashed all 491 manifest entries with zero
mismatches. A token scan of the 413 Lean files under `formal/Erdos7`, with
comments and strings removed, found no proof bypass; its only options were
`maxHeartbeats` and `maxRecDepth`, and its two ordinary tactic macros were read.
The supplied `verify.py`, `crosscheck.py`, and `verify_formal_appendix.py` also
exited zero. These checks rely on the pinned official toolchain and dependencies
and preserve `hThree`. The source transplant below does not include that
arithmetic noncoverage endpoint.

The [bridge program](../../docs/reports/erdos7-odd-covering/bridge_checks.py)
is an original repository experiment that binds selected formulas to this
exact archive and calculates two finite
counterexamples to proposed extensions. Substring checks are evidence binding
only; the program neither elaborates Lean nor verifies the author's theorem.

## Conditional comparison and the unrestricted positive-part bound

The same pinned archive contains
`publication/three_factors/paper/main.tex`, SHA-256
`291020863f5fbb4f2d98aa0a1d5ac63349bd8c565d4ab07422aee83d23825451`.
Section 3, **A conditional convex
comparison**, states Proposition **Conditional comparison** with source label
`prop:comparison`. Its hypotheses do not bound the number of coordinates
in one label. Precisely, let `X=(X_1,...,X_d)` have any law on a finite
product, let `c` range over finitely many labels, and let `A_(c,i)` depend
only on coordinate `i`. Suppose deterministic `r_(c,i) in [0,1]` satisfy

\[
 \Pr(X_i\in A_{c,i}\mid X_1,\ldots,X_{i-1})\le r_{c,i}
 \quad\text{almost surely}.
\]

For `w_c>=0` and nonnegative increasing convex `h`, the proposition gives

\[
 \mathbb E h\!\left(\sum_c w_c\prod_i
                  \mathbf1_{A_{c,i}}(X_i)\right)
 \le
 \mathbb E h\!\left(\sum_c w_c\prod_i
                  \mathbf1_{\{U_i\le r_{c,i}\}}\right),
\]

where the `U_i` are independent uniforms on `[0,1]`. The same `U_i` is
used for every label in coordinate `i`. The actual sets for different
labels need not be nested, and each residue can depend on the entire
modulus label. The preceding Lemma **Nested marginals**, `lem:nested`,
compares an increasing supermodular function of a random subset with the
nested subset having the prescribed upper marginal probabilities. The
proposition applies it to the last coordinate conditional on the whole
past, then repeats backwards. Independence is introduced only for the
auxiliary uniforms. Its final paragraph permits subsequent countable
nonnegative completion by monotone convergence when the upper expectation
is finite.

Section 8, **Unrestricted moduli after a fixed largest prime**,
`sec:extension`, defines

\[
 D_q=\prod_{3\le p<q}(1+K_p),\qquad
 S(x)=\prod_{3\le p\le x}
       \left(1+C_p\frac{3p-1}{(p-1)^2}\right),
\]

with prime products and the auxiliary height tails from the paper's fixed
schedule. In the proof of Lemma **Unrestricted second-moment charge**,
`lem:unrestricted-charge`, it applies `prop:comparison` to the original
labels and completes the nonempty old cofactor types. There are `D_q-1`
completed types, each with total weight at most one. Before any quadratic
relaxation, the proof explicitly bounds the assigned mixed-union probability
by

\[
 \frac{\mathbb E(D_q-1-t_q)_+}{d_q-t_q},\qquad
 d_q=q-2,\quad t_q=d_q\delta_q.
\]

It then uses `(u-t)_+<=u^2/(4t)` and its choice `delta_q=1/2` to obtain
`E D_q^2/(q-2)^2`. The preceding positive-part expression retains more
information. The proof also derives
`E(1+K_p)^2=1+C_p(3p-1)/(p-1)^2`. Both the cofactor completion and this
moment identity permit arbitrary support per original modulus. The
coordinate heights still resolve the entire original family, including
classes ending after the cutoff. None of these observations removes the
three-prime hypothesis from the audited Lean theorem quoted above.

The [complete-star extension](../../Problems/erdos-7-odd-covering-systems.md)
uses this ordinary conditional comparison with a different, actual star
head law and `delta=2/5` through prime 2039. Its finite-height ternary
convex-order step, original-label completion, exact positive-part sum and
same-law survivor conditioning are stated in (US1)--(US12) there. They
supply a supported `Gamma<4331` seed for BBMST continuation and exclude
arbitrary tails above 73 for that specific head assignment. This is a
new application of the paper's ordinary propositions, not a claim that
the upstream Lean development formalizes the changed head law or the
unrestricted-tail star theorem.


## MIT source transplant for conditional comparison

The repository imports the original proofs of
`Erdos7.ThreePrime.convex_load_comparison` and
`Erdos7.CappedGain.saturation_bound`, together with
`Erdos7.ThreePrime.PhysicalChain.covered_probability_le` and
`Erdos7.ThreePrime.PhysicalChain.kernels_have_caps`. These declarations and
their support modules are Michael Schroeder's results, not new repository mathematics.
The convex comparison permits arbitrary coordinate and label support; saturation
bounds the total geometric weight of labels with injective nonzero index-depth
pairs. The physical chain constructs normalized full-history distortion kernels,
bounds the final covered-event probability by accumulated charge, and derives
conditional caps from its explicit base-law cap hypotheses. None of these
theorems assumes at most three prime divisors per modulus.

The source-module mapping replaces the prefix `formal/Erdos7/` by
`D5/S3/Arith/Congruence/ConditionalComparison/`. It retains these 25 files:
`FiniteProbability`, `Distortion`, `CappedGainProbability`, `Supermodular`,
`Causal`, `CappedGain`, `CappedGainScalar`, `CappedGainLattice`,
`CappedGainLift`, `Runs`, `CappedGainDepth`, `Hybrid`, `RankedRearrangement`,
`CappedGainRearrangement`, `CappedGainDistortion`, `CappedGainBlock`,
`CappedGainFunctional`, `CappedGainGeometric`, `Cylinders`, `TreeSelection`,
`CappedGainTrees`, `ThreePrime/Probability`, `ThreePrime/Comparison`,
`CappedGainTypes`, and `ThreePrime/DistortionChain`, each with its original
`.lean` extension.
This is the complete source import closure of Comparison, CappedGainTypes,
and DistortionChain, not a claim that every supporting declaration is a
separate mathematical contribution.
The original `Erdos7` namespaces and declaration names are retained.

The repository pins Lean `v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, so the upstream package's different
pins exclude the direct Lake dependency form under spec A17.2. Besides the
canonical headers, attribution and mapped imports, the only source-proof
adaptations separate simplification steps: `CausalLaw.activeWithin_snoc`
expands finite-set membership before `reqInit` and `reqLast`, and
`rankSet_downward` in `RankedRearrangement` expands finite-set membership
before `rankNat`. DistortionChain requires no proof adaptation. Statements
and proof arguments are unchanged. No wrapper or specialized covering-system
theorem is introduced.

The archive's `LICENSE.md` assigns the original Lean sources to MIT;
`LICENSES/MIT.txt` is reproduced verbatim below. The pinned archive contains
no NOTICE file. Dependencies retain their own licenses and are not copied.
Retirement condition: when this repository's own pinned Mathlib provides an
equivalent eligible declaration, route its consumers directly to that
Mathlib result and retire the corresponding transplant under the applicable
frozen-source rules. Acceptance into a future, unpinned Mathlib version is
not the retirement trigger.

## Arithmetic coordinate excerpts

The additional module
`D5/S3/Arith/Congruence/ConditionalComparison/ArithmeticCoordinates.lean`
retains the following general source excerpts, with their original declaration
names and proof bodies. They are reusable arithmetic interfaces, not new
repository mathematical contributions:

- `formal/Erdos7/ArithmeticReduction.lean`: `embeddedWordValue` and
  `embeddedWordValue_prefix_eq`; the `PrimePowerCover` structure;
  `PrimePowerCover.crtModulus`, its nonzero and pairwise-coprime proofs,
  `modulus`, `primePowDepth_dvd_modulus`, and `covers_modulus`;
  `finset_prod_odd_nat`; the `OddDistinctCoveringSystem` structure and its
  namespace from `commonModulus` through `toPrimePowerCover` inclusive.
- `formal/Erdos7/Rank8Arithmetic.lean`: the `PrimePowerCover` namespace from
  `actualCRT` through `actualCylinder_covers` inclusive.
- `formal/Erdos7/Rank8Cylinders.lean`: the complete `PurePrefixes` section,
  from `purePrefixAt` through `forbidden_eq_digits` inclusive.
- `formal/Erdos7/ThreePrime/CylinderModel.lean`: the complete
  `Erdos7.FiniteLaw` namespace containing `piLaw_prob_coordinate`.

Imports are narrowed to the existing `CappedGainTrees` transplant and the
original Mathlib arithmetic imports. Namespace delimiters are reconstructed
around these excerpts; unused six-block, seven-block and sparse-support
applications are excluded. No arithmetic conclusion is generalized.

`ActualCylinderChain` directly consumes the retained ordinary-cover arithmetic
and pure-prefix interfaces. Its ending-coordinate construction is adapted
from `formal/Erdos7/ThreePrime/Model.lean` (`bad`, `build`) and the induction
in `ModelSemantics.lean` (`covered_build_iff`). It accepts arbitrary admissible
thresholds and has no `PrefixModel` or `sparse` field. These construction ideas
are attributed to the source.

The repository interface permits an arbitrary rational law `mu` on the
complete prime-power words of the first `b` coordinates. Correlations within
this head are unrestricted. The required `headSafe` probability is one:
every original cylinder supported entirely in the head, including a mixed
cylinder, must fail `headMatch`. Tail stage `i` processes coordinate `b+i`,
retaining every original label, its head match and all preceding tail
requirements. Distinctness of the original moduli does not imply distinctness
of their tail cofactors.

The additional live argument propagates probability-one pure-prefix avoidance
through the full-word tail distortion laws and glues the head and tail into
an actual CRT point. Ordinary coverage forces the final covered event under
`mu.joint` with those same tail kernels. The imported covered-event bound
then gives `1 <= mu.expect (fun head => totalCharge head)`.
Its per-cylinder base-cap expressions directly use `PurePrefixResidualLaw`
and supply `BaseCaps` for every head when the residual-probability inequalities
hold. A law specified only modulo 315 needs a distribution on the complete
selected prime-power words satisfying `headSafe`; this theorem does not
construct a lift preserving an arbitrary truncated marginal.
The unrestricted noncoverage conclusion still requires an average charge
budget below one; the source excerpt and interface theorem do not provide
that budget.

## Source license

```text
MIT License

Copyright (c) 2026 Michael Schroeder

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

```
