# Nine- and ten-prime heads with a missing small prime admit an unrestricted tail

Let `C={a_m mod m}` be a finite family of pairwise distinct odd numerical
moduli greater than one, and let `N` be their LCM. Assume at least one of
`3,5,7,11` is absent from the complete prime support of `N`. Each row below
is a sufficient noncoverage condition:

| Maximum number of prime divisors at most B | B | Final distorted survivor mass |
| --- | --- | --- |
| 8 | 1400 | greater than 1/256, report763 |
| 9 | 3000 | greater than 1/200 |
| 10 | 10000 | greater than 1/1100 |

Original residues, finite prime-power exponents and support arities are
unrestricted. There is no bound on the finite number of prime divisors
larger than the corresponding B. These mass bounds refer to the
constructed distorted submeasure, not uniform final Haar-density bounds.

In particular, any such original family supported on at most ten primes
and missing one of `3,5,7,11` is noncovering. Equivalently, a putative odd
distinct cover with at most ten prime divisors must contain all four of
these primes. This is a restricted deduction, not a resolution of Erdős #7
or a literature-priority claim.

The new step is to expose one or two actual head primes using [Chapter08's](../../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md)
half-clipped kernel, delete each actual new bad set without normalization,
and retain [report763's](763-a-joint-query-head-admits-an-unrestricted-prime-tail-above-1400.md) mass and joint-query estimates on that same live
law. Then report763's quarter-clipped tail continuation applies unchanged.
The proof below and exact arithmetic are ordinary mathematics, not new
Lean verification.

## The paired eight-prime source

At full finite coordinate heights, including every old-coordinate exponent
in original classes that also touch future primes, report763 constructs
one submeasure on every ordered eight-prime tuple `r_i >= (P0)_i`, where

\[
 P_0=(3,5,7,13,17,19,23,29).
\]

The same measure is supported outside all original classes involving only
these eight coordinates and satisfies

\[
 \mu_8(X)\ge m_8:=\frac{10237584019}{168750000000},\qquad
 \Gamma(\mu_8)\le G_8:=\frac{26010182627}{1040449536}.
 \tag{NH1}
\]

Here Gamma is the maximum second moment of the complete query load, with
one query for every numerical divisor of the full current period,
including the unit divisor. Every residue layout is allowed. This is a
homogeneous invariant of a positive measure, not a ratio divided by its
mass. Report763's original source construction and averaged finite prefix
injections transport both bounds together. No new source geometry or
reweighting search is needed here.

## An actual head extension followed by restriction

Suppose mu is supported on the current original survivor set, has mass at
least m and has Gamma at most G. Expose a new actual prime q, resolving its
complete finite height. Assign to this stage exactly those original
classes whose largest exposed head prime is q. Write B for their actual
forbidden union. At a fixed earlier word x let alpha(x) be the Haar
fraction of the complete q-coordinate covered by B.

Use Chapter08's normalized full-coordinate kernel with delta=1/2. It has
pointwise density at most 2 relative to current Haar, including histories
with alpha=1. If nu=mu K, the chapter's homogeneous query transfer and
actual-bad-mass estimate give

\[
 \nu(X)=\mu(X),\qquad
 \Gamma(\nu)\le G(1+2a(q)),\qquad
 \nu(B)\le\frac{G}{(q-1)^2},\qquad
 a(q)=\frac{3q-1}{(q-1)^2}.
 \tag{NH2}
\]

The bad-mass estimate retains all original numerical labels. At each
positive q-exponent, distinct numerical moduli give a partial earlier
query layout; its unit cofactor includes the pure q-power class. Complete
the partial layout and use the existing joint-load second-moment bound.
Finite height sums are at most their convergent infinite sums. No support
radical or independently optimized residue choice replaces the originals.

Now define the next **unnormalized** law by actual restriction:

\[
 \mu'=\nu\mathbin{|}_{B^c}.
\]

For every full query load L its square is nonnegative, so

\[
 \int L^2\,d\mu'\le\int L^2\,d\nu.
\]

Thus on this single supported law

\[
 \mu'(X)\ge m-\frac{G}{(q-1)^2},\qquad
 \Gamma(\mu')\le G(1+2a(q)).
 \tag{NH3}
\]

Restriction may change the old marginal; no marginal preservation is
claimed after it. The intermediate normalized kernel preserves the old
law, while the subsequent restriction is paid for by its actual bad mass.
No positivity in each old fibre is assumed. An entirely forbidden fibre
can lose all its mass and is included in the same estimate. Later Gamma
bounds are all taken on this restricted measure, never on an independently
chosen replacement law.

The two coefficients `1/(q-1)^2` and `a(q)` decrease with q>1; indeed
`a'(q)=-(3q+1)/(q-1)^3<0`. Hence uniform lower bounds on newly exposed
primes give uniform lower mass and upper moment recurrences.

Starting with (NH1), use q>=31 and then q>=37. The exact paired bounds are

\[
 \begin{aligned}
 m_9&=m_8-G_8/30^2
 =\frac{60153961455906929}{1828915200000000000}>0,\\
 G_9&=G_8(1+2a(31))
 =\frac{7048759491917}{234101145600},\\
 m_{10}&=m_9-G_9/36^2
 =\frac{817539304151922053}{84652646400000000000}>0,\\
 G_{10}&=G_9(1+2a(37))
 =\frac{2671479847436543}{75848771174400}.
 \end{aligned}
 \tag{NH4}
\]

Both positive masses and their corresponding Gamma bounds belong to the
same sequence of original-family live laws.

## Why the support conditions supply these head primes

For a row with head size k and cutoff B, put **every** actual prime divisor
at most B into the head. Choose one absent prime q* in `{3,5,7,11}`. Pad the
head to exactly k with unused odd primes at most B, always excluding q*;
already the first k+1 odd primes supply enough choices. Give artificial
coordinates arbitrary positive finite heights and add no forbidden class.

Sort the padded head as `r_1<...<r_k`. Because it misses one of the first
four odd primes, it satisfies `r_4>=13`, so its first eight entries dominate
P0 coordinatewise. Its ninth is at least31 and its tenth at least37.
Applying (NH1) to the first eight and (NH3) to any additional head
coordinates yields a law supported outside the complete original head-only
family with the corresponding `(m_k,G_k)` from (NH4).

The prime11 may be present when q* is3,5 or7. It then belongs to the head;
it is never treated as a large-prime tail coordinate. All original
nonhead primes are strictly greater than B. Original classes are assigned
once by their largest head coordinate, or later by their largest tail
coordinate. A survivor on padded coordinates projects to an original
survivor, so padding places no added condition on the original family.

## Continue the same head law through all larger primes

Start from the supported k-head law just constructed. Expose all actual
outside primes in increasing order and apply report763's normalized
quarter-clipped kernels. Their density cap and bad-mass factor are both
4/3. The same query transfer gives the growth bound

\[
 1+\frac43a(q)\le\left(\frac q{q-1}\right)^4.
\]

Report763's prime-product ratio and decreasing-sum integral bound give a
total all-prime tail charge at most

\[
 \frac43G_k\tau_4(B,\ell),\qquad
 \tau_4(B,\ell)=\frac1B
 \left(\frac{2\ell^2+1}{2\ell^2-1}\right)^4
 \left(\frac B{B-1}\right)^2
 \sum_{h=0}^4\frac{4!}{(4-h)!\ell^h}.
 \tag{NH5}
\]

Here `B>=286`, `ell>=4` and `3^ell<=B`; the latter gives `log B>ell>2`,
as required for the decreasing integral comparison. This uses exactly the
analytic premise and the full-coordinate denominator B-1 of report763.
No new analytic estimate is assumed.

For these tail stages, retain all bad sets in the physical law until one
final union deletion. Each later normalized kernel preserves the entire
earlier joint law, hence every earlier tail bad-set mass. This global
accounting starts from the already restricted head law, so its mass and
query bound remain paired. It does not mix a high-mass head source with a
separately favorable tail-query source.

For the new rows the exact final lower bounds are

\[
 \begin{aligned}
 m_9-\tfrac43G_9\tau_4(3000,7)
 &=\frac{18660801896253107429046442075711649}
        {3496436119104322625689651200000000000}
 >\frac1{200},\\
 m_{10}-\tfrac43G_{10}\tau_4(10000,8)
 &=\frac{3007744035678694606230772099147}
        {3145040240553014165913600000000000}
 >\frac1{1100}.
 \end{aligned}
 \tag{NH6}
\]

These quantities are approximately0.00533709218775 and0.000956345167510.
The positive final law is supported outside every original class. Any
point of its finite CRT carrier yields an avoiding integer.

## Relation to existing ranges and exact checking

[Report467](../450-499/467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) allows a nine-prime head at cutoff5000000 when at most seven
support primes are below43; equivalently its ordered last two head primes
are at least43 and47. [Report464](../450-499/464-smaller-common-law-cores-give-ten-prime-noncoverage.md) allows a ten-prime head at cutoff1000000
when at most five support primes are below43 or at most six are below53.
Those theorems do not require a missing prime from `{3,5,7,11}`. Conversely,
they do not cover the minimal nine- and ten-head tuples here, obtained by
appending31 and37 to P0. The statements have different hypotheses and all
remain valid. The subcase missing3 already has stronger bare noncoverage
results in the literature; no first noncoverage claim is made for it.

The exact consumer pins and invokes report763's existing paired-source
consumer. That invocation re-evaluates its32 ordinary source formulas and
checks its retained result and source identities. The new consumer computes
(NH3)--(NH6) with exact fractions and independently evaluates the degree-four
integral polynomial by its integration-by-parts recurrence. It does not
regenerate the source geometry, prove the arbitrary-height source
construction or analytic prime-product theorem, or rerun Lean.

At the next reference prime41 the same crude head ledger gives

\[
 m_{10}-G_{10}/40^2
 =-\frac{117144961015964651939}{9481096396800000000000}<0.
\]

This only limits the stated sufficient scalar continuation. It is not a
covering example, a proof that an eleventh-prime extension is impossible,
or an obstruction to a sharper source or estimate. The present result
claims only the8/9/10 table above.


The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_nine_ten_head_tail.py)
and [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_nine_ten_head_tail.json)
reproduce all paired bounds and positive margins:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_nine_ten_head_tail.py
```

Optimization mode is rejected before importing the pinned source evaluator,
because that inherited evaluator uses assertions. The default invocation
compares a fresh exact recomputation with the retained result. A separate
rational calculation and an independent review confirm the two head steps,
their unnormalized restriction, the missing-prime padding and complete-tail
quantifiers; this does not replace the stated ordinary source premises.
