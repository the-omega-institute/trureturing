# Exact prefix reduction for the actual joint query load

This is an ordinary finite proof and exact computation, not Lean verification.
The probability source is fixed throughout. The statement concerns the query
layout in the second moment, not a rephasing of the actual forbidden originals.

## 1. Simultaneous higher-digit saturation

Let `p` be any probability on residues modulo `315`. For integers `E,F>=1`,
let `mu` on `Q=9*5^E*7^F` have law `p` on the first `315` digits and independent
uniform higher `5`-adic and `7`-adic digits. There is one query cylinder for each
NUMERICAL divisor `d=3^j*5^e*7^f` of `Q`, including `d=1`. Its residue may be
chosen independently of the other query residues. Define

    Gamma_Q(p) = max_(a_d mod d) E_mu (sum_(d|Q) 1_[a_d mod d])^2.

Put `flat(d)=3^j*5^[e>0]*7^[f>0]`. A first-phase layout consists of one
`alpha_d mod flat(d)` for EVERY numerical divisor `d`, including distinct
exponent slots with the same `flat(d)`. Write

    P_(d,d')(alpha,beta)
      = sum_(u mod315) p(u) 1_[u=alpha mod flat(d)]
                              1_[u=beta mod flat(d')],
    c_(d,d') = 5^(-(max(e,e')-1)_+)
               7^(-(max(f,f')-1)_+).

Then the exact identity is

    Gamma_Q(p) = max_alpha sum_(d,d'|Q) c_(d,d') P_(d,d')(alpha_d,alpha_d'). (R)

The sum is ordered and includes diagonal pairs. No independent optimization
of a pair or a cylinder is being inserted on the right.

**Upper bound.** Fix an actual residue layout. Project each residue to its
first phase. If its two cylinders are incompatible, their intersection has
mass zero. If compatible, fixing the first-phase intersection leaves exactly
`max(e,e')-1` higher `5` digits and `max(f,f')-1` higher `7` digits to specify
when those maxima are positive. Independent conditional Haar digits give
precisely the displayed coefficient times `P`. Thus each intersection is at
most its summand in (R). Expand the square and add these inequalities.

**One layout achieves all pair bounds simultaneously.** Given ALL the first
phases, lift the `5`-root of each query as its representative in `{0,...,4}`
modulo `5^e`, and its `7`-root as its representative in `{0,...,6}` modulo
`7^f`. Keep the full ternary residue modulo `3^j`. CRT determines one residue
modulo the original numerical divisor. On either nonternary axis, two such
lifts are compatible exactly when their first roots agree; compatibility of
different ternary heights is already included in `P`. Therefore every pair
having nonzero `P` is compatible after this SINGLE simultaneous assignment.
The upper bound is attained for every pair, proving (R).

The same proof works for arbitrary fixed prime-power prefix heights and
independent Haar continuations. It does not allow changing phases of the
forbidden family, assume independence of prefix coordinates under `p`, or
combine different maximizers for separate pair terms.

## 2. A complete geometric remainder

For first-mode caps

    C_(j,D) = max_a p[u=a mod (3^j prod_(q in D)q)],

put

    w_q(h) = sum_(t=1..h) (2t+1) q^(1-t),
    w_q(infinity) = q(3q-1)/(q-1)^2.

For finite heights `E,F` and arbitrary larger heights, their additional
ordered-pair terms are bounded, on the SAME source, by

    Tail_(E,F)(p)
      = sum_(j=0..2,D subset{5,7}) (2j+1) C_(j,D)
          [prod_(q in D) w_q(infinity)
            - prod_(q in D) w_q(h_q)],

where `h_5=E,h_7=F`. In particular

    sup_(E',F'>=1) Gamma_(9*5^E'*7^F')(p)
      <= Gamma_(9*5^E*7^F)(p) + Tail_(E,F)(p).

For smaller heights use monotonicity: extend a layout by adding query slots;
the nonnegative load can only increase. For larger heights, separate the old
rectangle from pairs with at least one new exponent slot. A pair whose
maximum ternary height is `j` has `2j+1` possible ordered ternary indices.
On a `q` axis there are `2t+1` ordered exponent pairs with maximum `t`;
the Haar multiplier is `q^(1-t)`. The product coefficient counts precisely
the new pairs and bounds each projected intersection by its common-source
cap. This proves the stated remainder without truncating actual heights.

The tail on one axis is explicitly

    w_q(infinity)-w_q(h)
      = q^(-h) [(2h+3)q/(q-1) + 2q/(q-1)^2].

## 3. One coherent anchor is NOT without loss, even on the actual heads

The actual opposite head has originals

    (3,0),(9,1),(5,0),(7,0),(15,11),(45,2),
    (21,1),(63,58),(35,3),(105,74),(315,187),

with entries `(modulus,residue)`. Its four live rows
`23,128,233,268` have common `(mod 5,mod 7)=(3,2)` and ternary leaves
`5,2,8,7`. Give the first three mass `21/100` each and the last mass `37/100`.

For the actual same head replace the seven mixed residues by
`1,22,1,16,3,74,47`. The rows `17,52,122,227` are all live with common
`(mod 5,mod 7)=(2,3)` and leaves `8,7,5,2`. Give leaf `7` mass `37/100` and
the other three mass `21/100`.

Take `Q=315`. There are four numerical divisors for each ternary height
`j=0,1,2`. In every query choose the fixed `5` and `7` roots of this source
when those axes occur. For `j=1` choose ternary root `2 mod 3`, and for `j=2`
choose `7 mod 9`. The four `j=0` queries all hit. At every supported point
exactly one of the four-query `j=1` or `j=2` groups hits. The total load is
therefore identically `8`, giving second moment `64`.

This is the exact optimum, not merely a lower bound. Moving a query's `5/7`
roots to the source's fixed roots cannot reduce its indicator on any point
of the source. The four remaining choices within each ternary height are
interchangeable. Holding the other heights fixed, the square expectation is
a convex function of the empirical distribution of these four choices.
Jensen's inequality bounds its value by the maximum value when all four use
one choice. First apply this to height `1`, then to height `2`. Consequently
one only needs to check the `3*9=27` pairs of ternary roots. Their exact
maximum is `64`, attained at `(2 mod 3,7 mod 9)`.

If ALL twelve queries must instead use one coherent anchor `a mod 315`,
the optimum is

    16 * max(1+8*(37/100), 1+3*(63/100)+5*(21/100))
      = 1584/25 = 63.36 < 64.

An anchor with the wrong fixed `5/7` roots cannot help, because matching
these roots increases every affected indicator pointwise. Among matching
anchors, the two expressions cover leaf `7` and the three positive leaves
of ternary group `2`; empty leaves give still smaller values. The precise
gap is `16/25`.

Thus simultaneous zero lifting is valid, whereas replacing the first-phase
layout by one global coherent anchor loses the true optimum. The example
uses one actual source supported inside each declared legal head and
retains all twelve numerical query labels. It does not itself prove or
disprove a covering statement or the desired distortion positivity gate.

## 4. Exact checks

[exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_load.py) verifies the two four-row source
supports against their eleven actual forbidden originals, the exact optimum
by the convexity reduction's 27 choices, all 315 coherent anchors, and the
full twelve-query witness layout. It also compares direct finite-period
second moments against the pair formula for deterministic first-phase
layouts at `E=F=2` on a non-product probability supported on each full legal
head, and checks arbitrary higher-digit layouts against their simultaneous
zero lifts. Exact results are in [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_load.json).


The invariant and the obstruction to its separate-cylinder envelope are in
[Report 720](720-weighted-distortion-bridge-and-all-parameter-cylinder-envelope-obstruction.md).
The identity here preserves the common query layout, supplying a different
finite optimization target with a proved complete-height remainder. It does
not yet provide a source passing the unrestricted head-extension gate.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_load.py
```
