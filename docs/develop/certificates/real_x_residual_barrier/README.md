# Ambient order-six Hadamard exclusion from a residual barrier

This is a concrete certificate instance for the unified
`docs/develop/theory/MUB_SIX_FOURTH_BASIS_THEORY.md` research lane.
It is a computational proof subject to the analytic interpretation below.
The interval implementation and the complete cover transfer are not Lean-kernel
verified. The global dimension-six four-MUB conjecture remains open here.

## Exact centre and statement

Put `b=(-3+4i)/5`, `e=(-2+i sqrt(21))/5`, and let J and I be the three by three
all-ones and identity matrices. Define

```
H0 = [[J+(b-1)I,       J+(e-1)I],
      [J+(conj(e)-1)I, -J-(conj(b)-1)I]].
```

The existing exact Q(i,sqrt(21)) audit verifies entrywise modulus one and
`H0 H0* = 6I`. The present conclusion applies to **every** order-six complex
Hadamard matrix H with

```
max_ij |H_ij-H0_ij| <= 2^-24.
```

The fixed pair `(I,H/sqrt(6))` has at most one completion up to vector phases
and permutation, and cannot extend to a quartet. H need not be two-circulant,
commute with the old symmetry, or lie in the X parameterization. No claim of
mode affinity exactly two is made on this ambient neighborhood.

## The missing global barrier, now computed

For a dephased phase vector u with `u0=1`, use all 32 signed compact Cayley
charts and the five-component residual

```
f_H0(t)_a = |(H0* u(t))_a|^2 - 6,    a=0,...,4.
```

The base traversal proves

```
||f_H0(t)||_infinity <= eta  =>  t lies in one of the 60 chart guards,
eta = 2^-18, guard halfwidth = 2^-12.
```

All 32 charts terminate, with 5,990,945 visited boxes and no unresolved or
pending box. Guards can extend beyond a compact chart's boundary. Membership
in a differently signed chart uses the exact transition `t -> -1/t`, only
where the interval denominator excludes zero. Thus chart seams are covered.

The crucial sublevel image is

```
K_eta(X) = m-C f(m) + (I-C J(X))(X-m) + C[-eta,eta]^5.
```

If f(x)=r, the affine mean-value identity expresses x by the right-hand side
with r in the final cube. The last summand must not be omitted. The root-only
Krawczyk image is unsound for nonzero residuals. Componentwise mean-value
points or an average Jacobian suffice; a single shared vector mean-value
point is neither assumed nor required.

The traversal only uses: full-coverage splits, intersections with a sound
sublevel image, interval residual exclusion, and containment in a guard.
Floating-point matrix inversion only proposes dyadic preconditioners. Every
acceptance step then uses exact outward interval arithmetic. Budgets result
in INCOMPLETE, never in success. No precomputed verdict is consumed.

## Matrix perturbation sends every new root into the base sublevel

Suppose u is any actual common-unbiased phase root for H. For each output a,

```
|(H0* u)_a-(H* u)_a| <= 6 delta,
|(H* u)_a|^2 = 6,          sqrt(6) < 5/2.
```

The reverse triangle inequality and the difference of squared norms give

```
||f_H0(u)||_infinity <= 30 delta + 36 delta^2.
```

For `delta=2^-24`, the exact bound and remaining margin are

```
30 delta + 36 delta^2 = 125829129/70368744177664,
eta - (30 delta + 36 delta^2) = 142606327/70368744177664 > 0.
```

Consequently every new root enters a base guard. This is an actual exterior
residual barrier, not an assumption that known roots are all the roots.

One public Lean theorem supplies this concrete estimate:

```
HadamardResidualBarrier.common_unbiased_root_has_small_base_residual
```

It reuses Matrix.mulVec, conjugate transpose, complex norm-square, and finite
sum bounds. Generic residual transport already belongs to CayleyCoverAnalysis.
The new Lean source has not been elaborated in this runtime.

## Guard uniqueness and graph certificate over the whole matrix envelope

Each real and imaginary entry of H is independently enclosed by a rectangle
of radius delta about H0. This rectangle includes the complex-norm ball in
the statement. On this entire envelope the checker proves, for each guard:

* a small box has strict Krawczyk inclusion and a root;
* the larger base guard has contraction less than one, hence at most one root;
* the small box is contained in the larger guard.

The maximum certified guard contraction is
`384555794353/1099511627776`, strictly less than one. Thus any root that enters
a guard is the root already enclosed in its associated small box.

The first five residuals form a square system even for matrices in the
rectangular envelope that are not Hadamard. Only for actual Hadamard H does
Parseval imply the sixth residual from the first five. We use that fact only
when passing to actual common-unbiased vectors.

Fraction arithmetic independently checks all 1770 ray pairs on the envelope.
The 1656 pairs outside the prescribed supergraph have squared inner product
strictly greater than `1/100000000`. The 60 rays are distinct. The supergraph
has a designated six-vertex block, a disjoint bipartite remainder, and no
cross edges. Only graph containment is used. Allowed zero edges may disappear
under perturbation, including when the old symmetry disappears.

Every orthogonal six-tuple must use the designated six labels. Any two actual
completions therefore share all six projectors and cannot be mutually unbiased.
This is exactly the mathematical hypothesis boundary of the existing
CompleteRootSupergraphExclusion consumer. Root existence is stronger than what
this exclusion needs: exhaustive coverage and at-most-one occupancy suffice.

## Reproduction

Run from the repository root:

```bash
python3 scripts/research/check_real_x_residual_barrier.py \
  docs/develop/certificates/real_x_supergraph_patch/input.json \
  --output /tmp/mub-residual-barrier --jobs 4
python3 scripts/research/test_real_x_residual_barrier.py \
  docs/develop/certificates/real_x_supergraph_patch/input.json \
  /tmp/mub-residual-barrier \
  --report /tmp/mub-residual-barrier/negative_tests.json
```

The old JSON supplies root proposals and the proposed graph only. Its old
claim flags and success reports have no admission role. The compact checked-in
verification.json is a report of the executed run, not an input to acceptance.
The replay emits full per-chart reports and rational matrix/root enclosures.

Nine tests cover resource exhaustion, invalid chart, truncated or duplicate
root catalogues, a false centre, truncated matrix bounds, a true edge falsely
listed as a nonedge, the exact affine sublevel-inflation witness, and a radius
that exceeds the certified transfer margin. Tests are not a universal proof
of the interval implementation.

## Literature bridge and research boundary

Ponleitner and Schichl (2021), *Exclusion regions for parameter-dependent
systems of equations*, Journal of Global Optimization 81, 621-644,
DOI `10.1007/s10898-021-01082-3`, distinguish tight solution enclosures from
larger exclusion neighborhoods and develop parameter-dependent interval
bounds. This distinction motivates our small root boxes versus larger guards.

Duff and Lee (2024), *Certified homotopy tracking using the Krawczyk method*,
arXiv `2402.07053v2`, gives correctness and termination results for a parametric
Krawczyk path tracker. Tracking known paths does not, by itself, supply our
missing global exterior barrier.

Lee (2025), *A priori bounds for certified Krawczyk homotopy tracking*, arXiv
`2512.01355`, supplies a priori step bounds and a weighted-path-length
complexity estimate. It is a source for future continuation scheduling, not a
certificate for the present MUB matrices.

These methods are established validated numerics. Our concrete contribution
is the computed base sublevel barrier and the explicitly checked ambient
Hadamard neighborhood joined to the MUB supergraph obstruction. No priority
claim is made for interval Newton methods or for abstract openness.

## Next mathematical use

For anisotropic matrix perturbations, the same proof uses the column budget
`r_a=sum_i |H0_ia-H_ia|` and gives `5 r_a+r_a^2` in that output coordinate.
The explicit base barrier can therefore be reused across several parameter
families or a correlated matrix enclosure, instead of rerunning global root
coverage for each family. Local uniqueness and nonedges must still be checked
on each proposed envelope. Legal simultaneous fixed-edge monomial gauges can
transport the neighborhood; independent incompatible gauges cannot.

Missing kernel obligations remain: interval expression enclosure, analytic
mean-value/Krawczyk soundness, complete split/contract/exclude tree soundness,
and the transfer to actual rank-one contexts. No intrinsic-information gain,
finite sampled Arena, AnalysisDisposition, or successful seal is asserted.
