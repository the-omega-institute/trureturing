[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Four earlier prime neighbours: one closing deterministic schedule

Let a finite family have pairwise distinct odd numerical moduli greater
than one. Form its actual prime-interaction graph and process primes in
natural increasing order. Assume that every prime has at most four
smaller neighbours in this graph. There are no height, residue, total
prime-count, or additional spacing restrictions.

The single deterministic threshold schedule
\[
 \delta_7=\frac15,\qquad \delta_{11}=\frac13,\qquad
 \delta_p=\frac12\quad(p\ge13)
 \tag{FS1}
\]
closes the actual-law charge budget. If \(U\) is the original avoiding
set and \(M\) is its number of actual primes at least 7, then
\[
 H(U)>\frac3{800}
 \prod_{p\ge7\text{ actual}}\frac{(1-\delta_p)(p-2)}{p-1}
 \ge\frac3{800}\left(\frac{11}{24}\right)^M>0.
 \tag{FS2}
\]
This is an ordinary proof with an exact rational certificate, not a Lean
theorem or a resolution of unrestricted Erdős #7. It establishes one
valid schedule; no global optimality assertion is made.

## 1. One actual law, with arbitrary original heights and labels

Use the original finite CRT coordinates at heights resolving the entire
family. Write \(H_p\) for uniform Haar measure. Remove all original
pure \(p\)-power classes to obtain \(V_p\), then put
\[
 \nu_p=H_p(\cdot\mid V_p),\qquad c_p=\frac{p-1}{p-2}.
\]
Distinct full numerical moduli give
\(H_p(V_p)\ge(p-2)/(p-1)>0\), hence \(\nu_p\le c_pH_p\).
Start from the fixed product \(\nu_3\nu_5\). If either anchor is
absent, it can be inserted as a free coordinate and removed at the end.
Do not condition this root law on avoiding mixed \(3^a5^b\) classes.
Their once-only union fee is bounded by
\[
 \frac83\sum_{a,b\ge1}3^{-a}5^{-b}=\frac13.
 \tag{FS3}
\]

Assign each remaining nonpure original class to its largest prime \(p\).
Given the complete preceding word, let \(B_p\) be the actual forbidden
union on that coordinate and \(\alpha_p=\nu_p(B_p)\). Relative to
\(\nu_p\), use the normalized kernel with density
\[
 k_p=
 \begin{cases}
 0,&\alpha_p\le\delta_p,\ y\in B_p,\\
 (1-\alpha_p)^{-1},&\alpha_p\le\delta_p,\ y\notin B_p,\\
 (\alpha_p-\delta_p)/(\alpha_p(1-\delta_p)),
   &\alpha_p>\delta_p,\ y\in B_p,\\
 (1-\delta_p)^{-1},&\alpha_p>\delta_p,\ y\notin B_p.
 \end{cases}
\]
Thus at every history
\[
 K_p(X_p)=1,\quad K_p\le\frac{\nu_p}{1-\delta_p},\quad
 K_p(B_p)=\frac{(\alpha_p-\delta_p)_+}{1-\delta_p}.
 \tag{FS4}
\]
In particular, at \(\alpha_p=1\) the kernel is \(\nu_p\), retains
that history, and charges it by one. Appending the kernels gives one
normalized global probability law \(\mathbb P\); later kernels
preserve all earlier prefix marginals and assigned violation probabilities.

At positive depth \(e\), the deterministic conditional cylinder caps
given the entire earlier history are
\[
 3:\ 2\,3^{-e},\quad 5:\ \frac43 5^{-e},\quad
 7:\ \frac32 7^{-e},\quad 11:\ \frac53 11^{-e},
\]
\[
 q\ge13:\ 2c_qq^{-e}.
 \tag{FS5}
\]
Every cap here is less than one at positive depth; depth zero has cap one.
The caps at 7 and 11 follow from their actual thresholds in (FS1).

## 2. Comparison on the actual earlier-neighbour set

For a stage \(p\), let \(S_p\) contain all its actual smaller graph
neighbours. By hypothesis \(|S_p|\le4\). Every assigned nonpure
original numerical label has the unique form
\[
 p^e\prod_{q\in S_p}q^{f_q},\qquad
 e\ge1,\ f_q\ge0,\ \sum_q f_q>0.
\]
There is at most one original class for each complete exponent vector.
No uniqueness of projected numerical labels or of pair products is used.

The selected coordinates retain their caps after unqueried coordinates
are integrated out. Explicitly, if \(\mathcal H_q\) is the complete
history before \(q\) and \(\mathcal G_q\subseteq\mathcal H_q\) the
history of previously selected coordinates, then for each original
labelled cylinder event \(E\) on \(q\)
\[
 \Pr(E\mid\mathcal G_q)
 =\mathbb E[\Pr(E\mid\mathcal H_q)\mid\mathcal G_q]
 \le b_E,
 \tag{FS6}
\]
where \(b_E\) is its deterministic cap in (FS5). This is the tower
argument from Chapter 39. No private-coordinate independence is assumed.

First bound the actual \(\alpha_p\) by the sum of its original
labelled predecessor indicators with weights \(c_pp^{-e}\). Apply
Schroeder's pinned Proposition 3.2, Conditional comparison, using the
increasing convex function \(h(x)=(x-\delta_p)_+/(1-\delta_p)\).
The replacement introduces independent auxiliary uniforms, one per
selected coordinate and shared by all labels on that coordinate.
Only after this valid comparison complete the nonnegative exponent
tuples. Since \(\sum_{e\ge1}c_pp^{-e}=1/(p-2)\), if the auxiliary
product on the selected coordinates is \(Z\), the stage fee is at most
\[
 \frac{\mathbb E(Z-1-(p-2)\delta_p)_+}
      {(p-2)(1-\delta_p)}.
 \tag{FS7}
\]
The subtraction of one removes the pure current-prime cofactor. All
residues may depend on their complete original label. Countable
nonnegative completion follows by monotone convergence and the finite
moments stated below.

## 3. Four slots cover every earlier-neighbour pattern

Let \(N(q,C)=1+K\) have positive-depth tails
\(\Pr(K\ge e)=Cq^{-e}\). Introduce independent variables
\[
 N_3=N(3,2),\quad N_5=N(5,4/3),\quad
 N_7^*=N(7,3/2),\quad N_{11}^*=N(11,24/13).
 \tag{FS8}
\]
The last cap is deliberately larger than the actual 11-cap \(5/3\).
It must cover a possible second private predecessor 13 when actual 11
is missing. This is essential for arbitrary neighbour sets.

Put the actual root parents 3 and 5 in their own slots. Sort the actual
private parents \(q_1<q_2<q_3<q_4\), retaining only those present.
Use the following assignment, omitting unused entries:

| Actual root parents | Private parents allowed | Assigned slots |
|---|---:|---|
| 3 and 5 | at most 2 | \(q_1\to N_7^*,q_2\to N_{11}^*\) |
| 3 only | at most 3 | \(q_1\to N_7^*,q_2\to N_{11}^*,q_3\to N_5\) |
| 5 only | at most 3 | \(q_1\to N_7^*,q_2\to N_{11}^*,q_3\to N_3\) |
| neither | at most 4 | \(q_1\to N_7^*,q_2\to N_{11}^*,q_3\to N_5,q_4\to N_3\) |

For all \(e\ge1\), the first private slot dominates 7 exactly,
11 because
\[
 \frac53 11^{-e}\le\frac{35}{33}7^{-e}\le\frac32 7^{-e},
\]
and every \(q\ge13\) because
\[
 2c_qq^{-e}\le\frac{24}{11}13^{-e}
 \le\frac{168}{143}7^{-e}\le\frac32 7^{-e}.
 \tag{FS9}
\]
For the second private slot \(q_2\ge11\). If it is 11, its cap
\(5/3\) is below \(24/13\). If it is at least 13,
\[
 2c_{q_2}q_2^{-e}\le\frac{24}{11}13^{-e}
 \le\frac{24}{13}11^{-e}.
 \tag{FS10}
\]
For a third private slot \(q_3\ge13\),
\[
 2c_{q_3}q_3^{-e}\le\frac{24}{11}13^{-e}
 \le\frac43 5^{-e}\le2\,3^{-e}.
 \tag{FS11}
\]
Indeed the first comparison to the 5-slot at \(e=1\) is
\(24/143<4/15\), and its ratio decreases by \(5/13\) at each
additional depth. The 3-slot inequality is looser. A fourth private
prime is at least 17 and also fits the 3-slot. These comparisons use
distinct actual primes and distinct auxiliary slots.

Unused slots may be inserted since \(N\ge1\). Common-uniform
coupling therefore bounds every selected product by
\[
 Z_*=N_3N_5N_7^*N_{11}^*.
 \tag{FS12}
\]
Three early stages admit sharper products solely from natural order:

* At 7, the product is bounded by \(Z_7=N_3N_5\).
* At 11, it is bounded by \(Z_{11}=N_3N_5N_7^*\).
* At 13, it is bounded by
  \(Z_{13}=N_3N_5N_7^*N(11,5/3)\).

At 13 there is no earlier prime at least 13, so the actual 11-cap
is valid. No early stage uses a private prime not yet processed.
For every \(p\ge17\), use (FS12). If one of the small primes is
absent, completing its comparison factor and charging its fee merely
weakens the bound. No actual modulus or coordinate is duplicated.

## 4. Twenty-two finite fees and the analytic remainder

For \(N=N(q,C)\), the exact masses are
\[
 \Pr(N=1)=1-C/q,\qquad
 \Pr(N=n)=C(q-1)q^{-n}\quad(n\ge2).
\]
The complete first three moments follow from geometric tail sums.
For any positive threshold \(t\), integer-valued product \(Z\)
satisfies
\[
 \mathbb E(Z-t)_+=\mathbb EZ-t+
 \sum_{1\le j\le\lfloor t\rfloor}(t-j)\Pr(Z=j).
 \tag{FS13}
\]
Every probability in this finite complement is obtained by enumerating
the positive integer tuples whose product is \(j\). There is no
truncation of the geometric upper tails: they remain in the complete
mean \(\mathbb EZ\).

Let \(b_p\) denote the right-hand side of (FS7) using the indicated
actual/common comparison product; it bounds that stage's actual
violation probability. Evaluate these quantities for every prime from
7 through 97. There are 22 such primes. In particular, the 7-stage has
product threshold 2, denominator 4, and fee \(41/180\); the 11-stage
has product threshold 4 and denominator 6. The accompanying exact
certificate proves
\[
 \sum_{7\le p\le97\text{ prime}} b_p
 =0.6376571314242491\ldots<\frac{16}{25}.
 \tag{FS14}
\]
The decimal here displays the rational sum, while the strict comparison
uses fractions throughout.

For \(Y=Z_*-1\), the complete moment is
\[
 \mathbb EY^3=\frac{918032029}{1872000}.
 \tag{FS15}
\]
For every later prime, \(\delta_p=1/2\). The inequality
\((u-t)_+\le4u^3/(27t^2)\) gives
\[
 b_p\le\frac{32}{27}\frac{\mathbb EY^3}{(p-2)^3}.
\]
Overcount the primes greater than 97 by all odd integers starting at
99. A decreasing-integrand comparison proves
\[
 \sum_{p>97\text{ prime}}b_p
 \le\frac{32}{27}\frac{918032029}{1872000}
 \left(\frac1{97^3}+\frac1{4\,97^2}\right)
 =0.0160799384808130\ldots<\frac1{60}.
 \tag{FS16}
\]
Every actual stage is charged once, whether or not stages share earlier
neighbours. Consequently the total actual private fee is strictly below
\[
 \frac{16}{25}+\frac1{60}=\frac{197}{300}.
\]
Pure classes have zero probability, and mixed-root classes cost at most
\(1/3\). The union bound in the one actual law therefore yields
\[
 \mathbb P(U)>1-\frac13-\frac{197}{300}=\frac1{100}.
 \tag{FS17}
\]

## 5. Full Haar density and scope

The full conditional density bounds in (FS4) multiply along the actual
sequential law, giving
\[
 \mathbb P\le\frac83
 \prod_{p\ge7\text{ actual}}\frac{c_p}{1-\delta_p}\,H.
\]
Combining this full joint bound with (FS17) proves (FS2). This step does
not multiply marginal density caps. The reciprocal factors are
\(2/3\) for actual 7, \(3/5\) for actual 11, and
\((p-2)/(2(p-1))\ge11/24\) for actual \(p\ge13\).
Free missing anchor coordinates do not alter the original Haar volume.
Finite CRT then supplies an uncovered integer.

In particular, common-\(\{3,5\}\) books with disjoint private pages
of at most three primes satisfy the natural-order hypothesis: a private
prime has at most two earlier private neighbours in its page and the
two possible root neighbours. Pages may have arbitrary original powers,
labels and residues. This is a consequence of the graph theorem, not a
separate law or a fresh budget per page.

## 6. A graph beyond the three-predecessor theorem

Take the first ten odd primes
\[
 (p_1,\ldots,p_{10})=(3,5,7,11,13,17,19,23,29,31),
\]
and allow every original modulus supported in a five-prime sliding window
\[
 W_i=\{p_i,p_{i+1},p_{i+2},p_{i+3},p_{i+4}\},
 \qquad 1\le i\le6.
 \tag{FS18}
\]
Every finite distinct-modulus family with these supports satisfies the
theorem, for arbitrary original heights and residues. Its actual graph
is a subgraph of the fourth power of the ten-vertex path: in the full
graph, two indices are adjacent precisely when their distance is at
most four. Hence each prime has at most its previous four primes as
smaller neighbours.

If a full-support label on each \(W_i\) is included, the actual graph
is precisely this path power, with 30 edges. It is a single biconnected
block on ten vertices: deleting any vertex leaves a connected path
using an edge of length two across the deleted vertex. The graph
contains \(K_5\) on each \(W_i\). In **every** vertex order, the last
vertex of such a clique has its other four clique vertices as earlier
neighbours. Thus no order can satisfy Chapter 39's three-predecessor
hypothesis, including any alternative order anchored at 3 and 5.
This gives a structural class outside Chapter 39's order hypothesis,
and also outside the class with all blocks of size at most seven.
Chapter 39 allows anchored orders that need not be increasing, whereas the
present theorem requires natural order; no general inclusion of its
entire graph class is asserted.

The example describes an entire allowed-support family with unbounded
original exponent heights and arbitrarily many distinct labels. Its
noncoverage is not inferred from the reciprocal sum of just six chosen
illustrative classes. Longer sliding-window lists give arbitrarily
large blocks with the same natural-order bound.

## 7. Reuse and verification boundary

The proof reuses the actual ordered kernels of
[Chapter 07](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md),
the deterministic-schedule discipline of
[Chapter 03](03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md),
[Chapter 39's selected-coordinate tower interface](39-anchored-three-predecessor-orders-are-noncovering.md),
and [Chapter 37's original-label comparison](37-full-density-and-large-prime-continuation-for-spine-books.md)
and complete geometric moment formulas. The ordinary comparison theorem
is attributed to
[Schroeder's pinned Proposition 3.2](../../../../Library/Arith/schroeder2026noncoverage.md#conditional-comparison-and-the-unrestricted-positive-part-bound).

The program
[`four_predecessor_schedule_certificate.py`](../frontier/cover-geometry/four_predecessor_schedule_certificate.py)
produces the adjacent
[`exact output`](../frontier/cover-geometry/four_predecessor_schedule_certificate.json).
Its `--helper` argument points to the existing
[`spine_book_density_certificate.py`](../frontier/cover-geometry/spine_book_density_certificate.py),
whose SHA-256 is checked before importing its mass and moment functions.
It evaluates all 22 finite fees, the complete third moment and the
infinite-tail bound, the endpoint inequalities sufficient for all-depth
slot domination, and the density factors. Python 3.10 or later is
required, with assertions enabled. The only thresholds used throughout
are (FS1); fees and subsequent comparison laws are never taken from
incompatible schedules.

The result is restricted to the declared increasing order and
four-earlier-neighbour hypothesis. It does not prove that arbitrary
4-degenerate graphs admit this order, bound arbitrary predecessor
counts, or assert that every root word extends through every page.
The retained rational program verifies these numerical premises; the
kernel, comparison, and graph arguments above remain ordinary proofs.
