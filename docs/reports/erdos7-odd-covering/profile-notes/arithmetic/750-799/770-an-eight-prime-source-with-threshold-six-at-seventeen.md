# An eight-prime source with threshold six at17

For every finite family of pairwise distinct odd numerical moduli supported on

\[
 P=(3,5,7,13,17,19,23,29),
\]

the ordinary source construction supplies one avoiding submeasure `mu`, at arbitrary original finite heights and fixed residues, with

\[
 \mu(X)\ge m_*:=\frac{89120862071}{1350000000000},\qquad
 \mu\le D_*H_P,\qquad D_*:=\frac{891}{50}.
 \tag{SS1}
\]

The source has the same conditional-kernel representation as [Report763](763-a-joint-query-head-admits-an-unrestricted-prime-tail-above-1400.md), with later-coordinate caps

\[
 (C_7,C_{13},C_{17},C_{19},C_{23},C_{29})
 =(3/2,3/2,8/5,9/5,11/7,7/4).
 \tag{SS2}
\]

These properties belong to the same law. The construction also has the complete query bound

\[
 \Gamma(\mu)\le G_*:=\frac{214960187}{8257536}.
 \tag{SS3}
\]

Here `Gamma` is Report763's homogeneous second moment of the complete query load, including the unit divisor and a separate globally fixed phase for every full numerical divisor. The result transports to ordered eight-prime supports dominating `P` coordinatewise.

The mass in (SS1) is distorted mass. It is not itself a claimed Haar survivor density. The source comparison and completion are inherited ordinary mathematics; the new finite calculation is exact rational arithmetic, not new Lean verification.

## 1. One changed source threshold

Use the ordinary basic3/5 anchor and the later thresholds

\[
 (t_7,t_{13},t_{17},t_{19},t_{23},t_{29})=(2,4,6,8,8,12).
 \tag{SS4}
\]

The only change from the Chapter68 source row is the threshold at17. The cap there is now

\[
 C_{17}=\frac{17-1}{17-1-6}=\frac85,
\]

and its source-loss denominator is10. Every subsequent comparison multiplier is recomputed with this new cap. This changes the joint density cap from the old value to `891/50`; one cannot retain the old density cap after changing the threshold.

The underlying source hypotheses are unchanged. [Schroeder, *Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1](../../../../../../Library/Arith/schroeder2026nine.md), DOI `10.5281/zenodo.22759614`, provides countable completion of the pure prime powers and15, the capped normalized kernels, ordered increments, weighted aggregation, and the ordinary first-hit deletion ledger. Completion preserves the original covered subset. The proper-divisor reciprocal sums for a pure power and15 satisfy the required strict bounds.

For all six later primes,

\[
 1\le t_q\le q-2,\qquad
 C_q=\frac{q-1}{q-1-t_q}<q,\qquad
 C_q\left(1-\frac1{q-1}\right)\ge1.
\]

Thus the same full-coordinate source construction is feasible with (SS4). It keeps full numerical exponent labels and actual residues. It neither replaces them by support-only labels nor assumes independence of the later conditioned coordinates.

## 2. The32 common anchor vertices and unchanged finite geometry

After the source's Haar-preserving tree normalization, write

\[
 a\in\{1,2\},\quad b\in\{2,4\},\quad c\in\{a,3-a\},\quad j\in\{1,2,3,4\}.
\]

The selected pure3,9,5 classes are `0 mod3`, `1 mod9`, `0 mod5`; the15 and27 classes are represented by `a` and `b`. The first5 digit of25 is `c`. The pure5 tail simplex is evaluated at `t_h=(1/20)1_(h=j)`.

In135-cell units the old reserve is

\[
 R_i=\frac{135}{4}+\gamma_i+(9-\gamma_i)
       \left(\frac{\mathbf1_{c=a}}5+\frac{\mathbf1_{j=a}}{20}\right),
 \quad
 \gamma_i=3\mathbf1_{a=1}+\mathbf1_{b\bmod3=a\bmod3}.
 \tag{SS5}
\]

The coarse cells and four anchor-region weights do not depend on the later primes or thresholds. Use the same inherited72 geometry batches, with51,840 requested integer hinge entries. Their threshold set contains

\[
 \{t/m:t\in\{2,4,8,12\},\ 1\le m<t\}.
\]

For the changed17 threshold, only

\[
 6/m\quad(1\le m\le5)
 =6,3,2,3/2,6/5
\]

are required. Each equals `12/(2m)` and is already in the inherited table. No interpolation and no new hinge search is needed.

## 3. Recompute all later multiplier distributions

Let `A_i`, `W_i`, and `H_i(r)` be, respectively, the total comparison mass, linear-load upper bound, and hinge upper envelope supplied by one basic anchor vertex, in135-cell units. They include the inherited exact infinite-height remainders.

The earlier later-coordinate multiplier is

\[
 M_q=\prod_{5<p<q}(1+J_p),\qquad
 \Pr(J_p=0)=1-C_p/p,\quad
 \Pr(J_p=n)=C_p(p-1)/p^{n+1}\ (n\ge1).
\]

These are auxiliary comparison runs. Their independence is a property of the comparison, not an asserted property of the physical source. Their full first moment is

\[
 \overline M_q=\prod_{5<p<q}\left(1+\frac{C_p}{p-1}\right).
\]

For `w_q(m)=Pr(M_q=m)`, the loss numerator at threshold `t=t_q` is bounded by

\[
 \sum_{m<t}m w_q(m)H_i(t/m)
 +\left(\overline M_q-\sum_{m<t}mw_q(m)\right)W_i
 -t\left(1-\sum_{m<t}w_q(m)\right)A_i.
 \tag{SS6}
\]

Divide this by `q-1-t`. The cases `m>=t` are linear because the anchor load is at least one. Only multipliers below12 need to be stored for the six thresholds; their omitted probability and first moment are accounted for by (SS6). The full first moment is not truncated.

The inherited anchor envelope retains positive extra3 runs below12 and positive extra5 runs below9. Its omitted terms use the explicit geometric mass and first-moment remainders. Thus this source calculation does not impose a bound on original heights. All infinite inventories are justified by nonnegative finite truncation and the finite first moments used in the ordinary source theorem.

Round each computed loss upward to a multiple of `10^-10` in135-cell units, writing it as `L_(i,q)`. The certified mass is

\[
 m_i=\frac{R_i-\sum_qL_{i,q}}{135}.
 \tag{SS7}
\]

The exact minimum is `m_*` in (SS1), attained by `(a,b,c,j)=(2,4,1,1),(2,4,1,3),(2,4,1,4)`. For the first of these vertices the reserve is `135/4` and the six rounded losses are

\[
 \left(
 \frac{105625469639}{10^{10}},
 \frac{43069336959}{10^{10}},
 \frac{14720206577}{5\cdot10^9},
 \frac{84487061}{31250000},
 \frac{26260017057}{10^{10}},
 \frac{5296263}{3125000}
 \right).
\]

The actual pure5 budget is a convex combination of its four vertices. The reserve is affine and the upper loss envelopes are convex. Using the same vertex weights for every source loss proves the uniform mass lower bound for the actual source. The calculation does not combine separately optimized source laws.

## 4. Joint density, queries, and physical-prime transport

The initial law is Haar restricted to one actual3/5 avoiding set `A`, contained in the product of the completed pure survivors, whose masses are `1/2` and `3/4`. The normalized later kernels have the caps in (SS2), and restrictions only decrease density. Hence the product of those caps gives `D_*` pointwise on this one joint law.

The same representation supports Report763's query-pair proof. A constrained later coordinate costs its cap once per pair intersection, not twice. With

\[
 a(q)=\sum_{n\ge1}(2n+1)q^{-n}=\frac{3q-1}{(q-1)^2},
\]

the later factors and product are

\[
 (11/6,67/48,21/16,59/45,94/77,267/224),\qquad
 \prod_q(1+C_qa(q))=\frac{16535399}{2580480}.
\]

The pure-anchor factor remains `(1/2+a(3))(3/4+a(5))=65/16`. Their product is `G_*` in (SS3).

For larger physical primes, use the averaged prefix injections of Report763. For each injection construct this source on the pulled-back head family and then push the same measure forward. Every target query pulls back to an empty query or one source prefix cylinder per numerical exponent vector. Filling empty entries and nonnegativity give the uniform query bound. Averaging preserves the mass bound and the joint density cap. The source may depend on the injection; no independence between the law and the injection is required.

## 5. Exact verification and limits

The [standalone standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_source_schedule_six.py) reads only the [inherited geometry JSON](../../../frontier/cover-geometry/finite-prefix-sources/six_prime_prefix_geometry.json), checks its SHA256

`0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1`,

checks the internal batch identities, and recomputes every source envelope and all32 new ledgers. It checks the kernel conditions, the17 query identities, density cap and full query-pair product with exact fractions. Every check remains active under Python optimization mode. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_source_schedule_six.json) records all32 reserves, six rounded costs and mass bounds. A normal invocation must reproduce that result; writing a new result requires the explicit `--write-result` option. The default geometry location is relative to the consumer, with an optional explicit `--geometry` path.

An independent implementation enumerated the multiplier factor tuples directly and reproduced all32 new source ledgers and the same minimum. Neither arithmetic implementation regenerates the inherited geometry maxima or replaces the ordinary completion, all-height comparison, kernel representation or prime-injection proof. The source archive is edition1.0.1, SHA256 `9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`.

This result is a reusable stronger source for subsequent continuation arguments. It makes no optimality claim for (SS4), no refined query-ratio claim, and no unrestricted Erdős #7 claim.
