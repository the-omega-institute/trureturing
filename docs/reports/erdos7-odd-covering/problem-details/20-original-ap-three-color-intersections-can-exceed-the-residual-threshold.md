[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](19-five-prime-parent-envelopes-and-the-cofactor-allocation-barrier.md)

<a id="original-ap-three-color-intersection-countercontrol"></a>
# Original AP three-color intersections can exceed the residual threshold

Preserving each original cofactor's unique parent-prefix assignment does
not imply that three child-event unions have conditional intersection at
most \(14/79\). The finite family below has parent prime 3 at exponent 1,
child primes \(5,7,11,13\) at height 3, and 510 distinct original odd
moduli. Under its one actual complete child-survivor law,
\[
 \mu(E_0\cap E_1\cap E_2)
 =\frac{9255389299}{52156725189}
 >\frac{14}{79},\qquad
 \mu(E_0\cap E_1\cap E_2)-\frac{14}{79}
 =\frac{981601975}{4120381289931}.
 \tag{TC1}
\]

This refutes only that uniform intersection bound. The family does not
cover the integers. It neither realizes the previous chapter's abstract
comb nor refutes the proposed \(23/48\) parent fee. The statements here are
ordinary finite arithmetic results, without new Lean certification.

## 1. Literal original labels

For every nonempty support \(I\subseteq\{5,7,11,13\}\) and every exponent
tuple \(e_q\in\{1,2,3\}\), put \(d=\prod_{q\in I}q^{e_q}\).
A digit pattern \((r_q)_{q\in I}\) specifies the actual congruences
\[
 x\equiv r_q q^{e_q-1}\pmod {q^{e_q}}\quad(q\in I).
 \tag{TC2}
\]
For the old label, CRT combines the old pattern into one residue modulo
\(d\). For the new label, CRT combines the new pattern and the parent
condition \(x\equiv c\pmod3\) into one residue modulo \(3d\).
Patterns list their coordinates in increasing prime order.

| Support | Old digit pattern | Parent color \(c\) | New digit pattern |
|---|---|---:|---|
| 5 | 1 | 0 | 2 |
| 7 | 1 | 1 | 2 |
| 11 | 1 | 2 | 2 |
| 13 | 1 | 2 | 2 |
| 5,7 | 3,3 | 2 | 2,2 |
| 5,11 | 4,3 | 1 | 2,2 |
| 5,13 | 4,3 | 1 | 2,2 |
| 7,11 | 4,4 | 0 | 2,2 |
| 7,13 | 5,4 | 0 | 2,2 |
| 11,13 | 5,5 | 0 | 2,2 |
| 5,7,11 | 3,6,6 | 2 | 2,2,2 |
| 5,7,13 | 3,6,6 | 2 | 2,2,2 |
| 5,11,13 | 4,6,6 | 1 | 4,2,2 |
| 7,11,13 | 6,7,7 | 1 | 4,2,2 |
| 5,7,11,13 | 3,6,8,8 | 1 | 3,5,2,2 |

There are \(4^4-1=255\) old labels and 255 new labels. All 510 numerical
moduli are distinct and odd, and exceed 1. The old moduli and new child
cofactors are exactly the same set. Each child cofactor receives one
parent color; no original modulus is duplicated to supply another color.
Every nonempty child support, including the original five-prime new
labels, and every exponent tuple within the stated height is retained.

## 2. One survivor law and an exact finite quotient

The child period is
\[
 Q=5^3 7^3 11^3 13^3=125375375125.
\]
Let \(S\subseteq\mathbb Z/Q\mathbb Z\) avoid all old labels and set
\(\mu(A)=|A\cap S|/|S|\). For color \(c\), let \(E_c\) be the union of
the child projections of its new labels. Every intersection and weight
uses this same \(S\).

For a child prime \(q\), group nonzero residues modulo \(q^3\) by their
first nonzero base-\(q\) digit \(r\). The group for \(r\) is the disjoint
union of the three classes
\[
 x\equiv r q^{e-1}\pmod {q^e},\qquad e=1,2,3.
\]
Its cardinality is \(w_q=q^2+q+1\); the zero residue has cardinality 1.
Thus \((w_5,w_7,w_{11},w_{13})=(31,57,133,183)\).
Old pure labels remove exactly digit 1. Each remaining coordinate
alphabet is \(\{0,2,\ldots,q-1\}\).

Because every exponent tuple is present for each support pattern, the
union of those labels is exactly the corresponding product of digit
groups. All old and colored new events factor through this one finite
quotient, together with its original counting weights. This is an exact
partition for this particular family, not an assertion about arbitrary
AP residues or an infinite-height approximation.

There are \(4\cdot6\cdot10\cdot12=2880\) pure-allowed quotient cells.
Each has weight equal to the product of \(w_q\) over its nonzero
coordinates. Filtering by every old pattern and accumulating the new
color membership gives the following counts. Bit \(c\) in a mask
indicates membership in \(E_c\).

| Color mask | Complete old-survivor count |
|---:|---:|
| 0 | 18916297811 |
| 1 | 12852682305 |
| 2 | 6140417910 |
| 3 | 0 |
| 4 | 4943990034 |
| 5 | 47947830 |
| 6 | 0 |
| 7 | 9255389299 |

The total is \(|S|=52156725189\). The old pure constraints alone leave
64864962448 residues, so the actual mixed-survivor fraction in that
pure-domain product law is \(52156725189/64864962448\). Equation (TC1)
uses the complete-survivor denominator, not the pure-domain denominator.
The integer check is \(79\cdot9255389299-14\cdot52156725189=981601975>0\).

## 3. Reproduction from the original labels

The [program](../frontier/cover-geometry/k5_three_color_ap_control.py)
and [exact data](../frontier/cover-geometry/k5_three_color_ap_control.json)
retain all 510 literal modulus/residue pairs. The program factors those
labels anew, reads their local residues and parent colors, and checks
uniqueness and complete exponent coverage. Its second count retains each
valuation-digit state \((e,r)\) separately, with weight \(q^{3-e}\), plus
zero with weight 1. After the old pure exclusions it examines
\(10\cdot16\cdot28\cdot34=152320\) cells and recovers the same eight
counts. At height 1, a direct modular sieve of all 5005 child integers
also agrees: 2493 old survivors and 291 triple-intersection residues.

An independent check of the literal 510 labels grouped all 3996 individual
prime-power residues by their complete modular membership signatures,
without using the pattern table or the first-nonzero-digit quotient.
Its \(13\cdot19\cdot25\cdot25=154375\) signature cells give the same
histogram and strict inequality. A separate full height-1 original-period
sieve finds 5589 uncovered residues among 15015.

The full original height-3 period is \(3Q=376126125375\). If \(n_b\)
denotes a row of the table, its uncovered count is
\[
 \sum_{b=0}^7(3-\operatorname{popcount}(b))n_b=104671021761>0.
 \tag{TC3}
\]
Zero is also an explicit uncovered residue. Thus this finite family is
not a covering counterexample.

From the repository root, using only Python's standard library:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/k5_three_color_ap_control.py --output /tmp/k5-three-color-ap.json
```

## 4. What remains necessary for a blocked parent fibre

A large triple intersection alone does not supply the required residual
shape. If an ancestor event \(A\) is followed by three child events and
each branch is to block the whole old survivor set, one needs
\[
 S\setminus A\subseteq E_0\cap E_1\cap E_2.
 \tag{TC4}
\]
The ancestor and child events must all arise from their actual original
labels on the same \(S\). Across depths, these inclusions must hold for
one common allocation: a cofactor may recur at different parent
exponents, but a fixed pair \((a,d)\) can have only one parent prefix.
The example proves no such ancestor inclusion or cross-depth allocation.
It rules out the scalar threshold in (TC1) as a universal shortcut. The
[coupled first-root theorem](21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md)
instead uses shared support allocations to bound the parent fee for this
specified five-prime block with established four-vertex-block descendants;
it does not require the false triple-intersection bound. General block
recursion remains open.
