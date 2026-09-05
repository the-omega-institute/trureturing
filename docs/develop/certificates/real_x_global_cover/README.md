# Global common-unbiased root coverage on a two-real-parameter X patch

This certificate instance belongs to the single theory volume
`docs/develop/theory/MUB_SIX_FOURTH_BASIS_THEORY.md`. It supplies the previously
missing global coverage calculation for the patch in section 36. It does not
assert the full dimension-six MUB conjecture, full-X exclusion, or Lean admission.

## Result, scope, and verification level

For the exact X-construction branch already fixed by
`real_x_supergraph_patch/input.json`, set

```
|Re(alpha) + 1/5| <= 2^-32,  |Im(alpha)| <= 2^-32.
```

The replay checks every point of every one of 32 compact signed-Cayley charts
covering the dephased five-dimensional phase torus. All possible solutions are
contained in the 60 strictly validated uniqueness neighborhoods. An independent
Fraction graph replay proves these roots distinct and all 1656 forbidden pairs
nonorthogonal. The one-sided orthogonality supergraph consists of a canonical
six-block and a disjoint bipartite remainder.

Consequently, in the computational proof described below, **every actual
completion uses the canonical six rays**. There is at most one completion up
to column phases and permutations. Two such completions cannot be mutually
unbiased. The fixed edge therefore cannot extend to four MUBs anywhere on this
small closed parameter rectangle. Every actual completion also has exact
mode-affinity 2, since its rays are certified shift eigenrays.

The last statement does not assert existence of a completion: at-most-one is
already enough for quartet exclusion. The rectangle is very small; this is
not a large continuous-family classification. Literature priority has not been
established. Independent verification is appropriate before treating this as
a publication-ready exclusion result.

**Verification level:** exact computational interval proof, with an explicit
analytic interpretation. The C++ interval engine and contraction/cover adapter
have not been proved sound in Lean. The conditional Lean consumer is submitted
as source only until admission succeeds. External JSON `PASS` is not a kernel
proof or an intrinsic-information verdict.

## Compactness without an omitted phase

Write an unnormalized dephased vector as u_0=1. Each remaining unit complex
coordinate has a representation

```
u_j = s_j (1+i t_j)/(1-i t_j),  s_j in {-1,1}, t_j in [-1,1].
```

Indeed choose s_j so Re(s_j u_j)>=0 and set
`t_j=Im(s_j u_j)/(1+Re(s_j u_j))`. The unit-circle identity proves |t_j|<=1
and the displayed reconstruction formula. Thus all 2^5=32 signed charts must
be covered, including their boundaries. No omitted point at infinity remains.
Opposite signs are related by `t -> -1/t` wherever t is nonzero. The verifier
uses this exact transition to map boundary boxes into existing uniqueness boxes.

The equations are the first five components of

```
f_a(t) = |(H(alpha)^* u(t))_a|^2 - 6.
```

The sixth follows from HH*=6I and sum |u_j|^2=6. The old Fraction parameter
generator verifies the exact Cayley cubic identity, three disjoint root
intervals for each cubic, and the resulting Hadamard construction. It also
checks all 30 squared-minor Fourier-separation witnesses across the patch.

## Exact interval arithmetic and the covering proof

The cover core uses signed 64-bit interval endpoints divided by 2^40. Products
use signed 128-bit integers with directed exact floor/ceiling division. Endpoint
overflow fails closed. The graph and parameter stages reuse the existing
`fractions.Fraction` implementation, so their arithmetic is independently coded.

A floating-point inverse is permitted solely as a **proposal** for a dyadic
preconditioner C. It is never trusted as an inverse. All subsequent function,
Jacobian, contraction, exclusion, and inclusion bounds are integer intervals.

For a box X with centre m, the computed enclosure is

```
K = m-C f(m)+(I-C J(X))(X-m).
```

For any actual zero x in X, the mean-value integral Jacobian gives x in K.
This containment does not require C to be nonsingular. Therefore:

* an interval component of f excluding zero rejects the entire box;
* K disjoint from X rejects the entire box;
* every possible zero in X is retained in X intersect K;
* if that intersection lies in a known uniqueness box, no unknown root remains;
* otherwise the box is bisected into two closed children whose union is X.

The initial root neighborhoods additionally satisfy strict K containment and
`||I-C J||_infinity < 1`. The preconditioned Newton map is then a contraction
from the complete box into itself. The same norm bound implies C is invertible,
so its unique fixed point is a zero of f. These statements hold uniformly for
every exact parameter in the input rectangle. Root enclosures are sharpened
by three further valid K intersections before the graph replay.

The traversal may report `COVERED` only when both pending and unresolved counts
are zero. A resource cap cannot turn an incomplete traversal into success. The
driver deletes stale reports, runs all 32 charts, checks every exit code, and
reconstructs all parameter bounds. Stored success reports are never inputs.

## Why a supergraph closes the completion problem

Let K be the six canonical labels and color all other labels with two colors.
The verified forbidden pairs imply every actual orthogonality edge lies either
inside K, or outside K between opposite colors. There are no cross-block edges.
An orthogonal triple containing a noncanonical vertex would therefore be a
triangle in a bipartite graph, which is impossible. In particular every
six-element orthogonal context uses only K, and cardinality forces it to use
all of K. Two such contexts share a rank-one projector; its overlap is one,
not one-sixth.

`CompleteRootSupergraphExclusion.lean` expresses this argument directly using
`RankOneContext`, `overlap`, and finite cardinality. Its coverage hypotheses
refer to all projectors of the actual contexts, not merely an observed sample.
The proof neither needs nor claims that the 114 allowed edges persist.

## Replay

From the repository root:

```
python3 scripts/research/check_real_x_global_cover.py \
  docs/develop/certificates/real_x_supergraph_patch/input.json \
  --output /tmp/real_x_global_cover --jobs 4
```

Requirements: Python standard library, g++ with C++17 and __int128 support,
and the two existing research modules imported by the driver. No NumPy, SciPy,
SDP solver, internet connection, or precomputed success verdict is required.
The default one-million-node cap is per chart and is a safety limit only.
An exhausted cap rejects the calculation as incomplete.

The audited run explored 5,990,624 nodes across all charts, with no pending
or unresolved boxes. This count and elapsed time are diagnostics, never
mathematical novelty scores or admission criteria. The arithmetic tests compare
12,000 interval operations with exact Fraction endpoint calculations and include
overflow/zero-denominator rejection. Corrupted centres, duplicate labels,
truncated catalogues, and insufficient budgets are rejected.

## Relation to the single-compilation intrinsic-information specification

The referenced normative draft is version 4.3, blob
`bba1875f68c733b925582ffc81f1344cfce96931`. This computation does not replace
its Lean-internal admission rule. No sampled finite Arena, user-adjusted gain,
external novelty judge, or hand-written AnalysisDisposition is introduced.
The actual object is the complete common-unbiased ray space for the fixed
parameter. Its proposed finite catalogue requires the global analytic transfer
before it can serve as a kernel-checked finite presentation.

All code, input, and output hashes are provenance diagnostics. A future
single-compilation Lean root must verify the interval soundness/cover transfer,
then consume the public context theorem and use the project's actual registry.
Until then the intrinsic-information status is **not executed**, with no claim
of positive exclusive capture or successful catalog sealing.
