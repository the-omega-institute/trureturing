# Four-point rows lower the global binary-support upper bound

For the fixed six-anchor chart and common threshold theta=1/3696, every
binary upward bad-profile support satisfying the declared pair, triple and
four-point constraints has auxiliary mass at most

    U=0.016386655453077197... <0.016386656.                 (G1)

The exact rational certificate combines the genuine triples of reports499
and501 and the four-point rows of
[report505](505-joint-four-point-budgets-exclude-what-no-fixed-weight-can.md)
with the binary pair-clique cuts and signed order rows of
[report496](496-integer-triangle-cuts-give-a-strict-relaxation-gap.md).
It improves that earlier certified upper bound by

    U496-U=0.00003617247882224525...>0.                    (G2)

The bound applies to all supports in this declared model, including ones
that add points outside report501's example. It is not restricted to
repairing a previously supplied support by deletion. It is also not the
exact optimum of the full constraint system: a valid subset of its rows
already proves G1. Additional valid rows can only restrict that system.

The required source threshold is still

    m7=7235955529/450000000000
       =0.01607990117555555...,
    U-m7=0.0003067542775216409...>0.                       (G3)

Thus this improvement does not meet the same-source noncoverage criterion.
All decimals here are derived from exact fractions. The consumer uses
integer arithmetic and rational arithmetic, with no new Lean verification.

## Domain, source and constraint types

Keep references(2,7,3,4), split coordinates3,5,7, common coordinates
11,13,17,19, and new coordinates23,29. There are20076 middle profiles
with20<=Q<=38. The support value is zero on Q<=19. The complete Q>=39
comparison mass is charged on the upper side, including its infinite tails.
Each middle profile retains its literal eta shell weight. The conditional
caps and original full-label selector convention are those of reports495–501.
No comparison mass is asserted to be occupied by the actual source.

Here bad means strictly s<theta; a pair bound attained at s_i+s_j=2theta still excludes two strict-bad fibres. The upward support is generated from actual strict-bad profiles under the declared labelled-box inclusion.

For a binary support vector z, pair exclusions have right side1; genuine
three-point exclusions have right side2; the new four-point exclusions have
right side3. Three mutually excluded pairs also give the integer clique
cut z_i+z_j+z_k<=1. An upward row is z_i-z_j<=0 with3/5 fixed and one
allowed enlargement in a later coordinate.

The new upper certificate uses the following positive-price rows:

| Kind | Count | Right side |
| --- | ---: | ---: |
| Pair exclusion | 9307 | 1 |
| Genuine triple | 57 | 2 |
| Binary triangle clique | 620 | 1 |
| Genuine four-point edge | 6 | 3 |
| Upward order | 922 | 0 |

The six four-point edges are

    (68,70,1101,12707), (68,72,1105,12713),
    (68,74,1110,12722), (70,72,1106,12715),
    (70,74,1111,12724), (72,74,1112,12726).

They belong to the48-edge orbit in report505. Only the used rows need
certification; G1 assumes no completeness claim for a proposed graph.
The improvement in G2 uses the whole newer certificate and is not attributed
to four-point rows alone while ignoring its additional genuine triples.

## Exact rational dual with signed residuals

Write the selected rows as A z<=b and let w_i=eta(i). The certificate
supplies nonnegative integer numerators u_r with denominator D=10^13.
With y_r=u_r/D, every0<=z<=1 satisfying the selected rows obeys

    sum_i w_i z_i
      <=sum_r y_r b_r + sum_i max(w_i-(A^T y)_i,0).       (G4)

This follows by writing w=A^T y+(w-A^T y), using nonnegative row prices,
and bounding each remaining coordinate with0<=z_i<=1. The negative
coefficient of every order row is retained in A^T y before taking the
positive part. Omitting that signed contribution would invalidate G4.

The exact row-price numerator is86515302785. The consumer reconstructs all
20076 signed loads and exact positive residuals, then adds the full overflow
mass. The result is the rational value

    219220376045461843233719456511184899540100317956779193203442521592521859656673824667
    /13377981655450939865669018596957704255849689143005894395280837668089031250000000000000.

The chosen numerators were rounded upward when preparing the certificate.
Validity does not depend on that preparation: any nonnegative numerators
with the residual term in G4 give a sound upper bound. No solver flag or
floating objective is an input to the consumer.

There are no positive-price qualitative zero-only pair rows. All nine such
rows in the auxiliary proposal had coefficient zero. Consequently G1 already
holds at the uniform positive threshold1/3696; it does not borrow a
finite-height positive gap that can tend to zero as heights increase.

## Independent provenance of each used relation

The9307 pair rows and constituent pairs of the620 cliques use10840 distinct
pairs, with215 unordered capacity types. Their A/B divisor boxes are rebuilt
from the profile coordinates. The independent two-variable epigraph check
evaluates the exact rectangle-edge minima of the four residual pieces from
report481. Every used pair has K2>=1/3, including equality. This establishes
the common-threshold exclusion rather than only a qualitative positive value.
The clique row then follows from the three pair exclusions and integrality.

For each active genuine triple, the consumer checks its actual coordinate
transformation and full literal selector-mask pattern against the declared
seed. It regenerates the applicable exact axis vertices: seven-subset
constraints for the report499 seeds and all ten directions for the report501
seed. The weighted residual minimum is at least the sum of point weights
divided by6, which is the required common-threshold test.

For the four-point rows it reads the canonical
`four_point_joint_budget_certificate.json` and rechecks its179-node rational
branch proof. All direction capacities are independently reconstructed from
the literal seed masks. The90 leaf contradictions have nonnegative rational
multipliers, exact row cancellation, and strictly negative right sides;
both children cover every branch and all removed coordinate ranges violate
an axis bound. Each active edge is then checked against its actual orbit
transformation and literal masks. It does not rely on an optimizer to
recognize or validate these four-point rows.

Every used order row is checked directly as an allowed coordinate enlargement
and inclusion of both labelled boxes. The same source and arithmetic inputs,
including the canonical500,501 and505 results, are bound by their file hashes.
The comparison value in G2 comes from canonical report496 data.

## Remaining gap and reproduction

G1 is an ordinary exact upper bound for this entire binary-support model.
It is neither a feasible support with mass U nor an assertion of LP or binary
optimality. In particular it does not show that further joint constraints
cannot lower the bound through m7. Conversely, disproving the old explicit
support by new four-point edges did not by itself establish G1; the universal
certificate G4 is the additional step.

The existing same-source bridge would give original survivor Haar mass at
least(m7-U)/49896 if U<m7. G3 leaves this obligation unresolved. Other chart
configurations and unrestricted Erdős#7 are outside the conclusion.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_split_four_point_bound.py

The default run compares the complete derived result with the adjacent JSON;
`--output PATH` writes that result. It uses only the standard library, the
pure rational certificate and pinned canonical inputs. It reads no transient
pair graph, LP solution, optimizer executable or temporary research file.
