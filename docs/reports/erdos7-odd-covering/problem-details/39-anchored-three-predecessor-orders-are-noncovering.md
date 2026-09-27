[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Anchored three-predecessor orders are noncovering

The integrated-fee method of [Chapter 37](37-full-density-and-large-prime-continuation-for-spine-books.md)
extends to any actual prime-interaction graph with the anchored order
specified below. There is no page partition or disjoint-support
requirement: a single normalized sequential law handles arbitrary
overlap of the earlier-neighbour sets. This is an ordinary mathematical
deduction using the existing conditional comparison and rational fee
certificate, not an end-to-end Lean theorem or a solution of unrestricted
Erdős #7. No literature-priority claim is made.

## 1. Statement and the order certificate

Let the original congruence family be finite, with pairwise distinct odd
numerical moduli greater than one. Use its actual prime-interaction graph:
two primes are adjacent if one original modulus contains both. Choose an
order with 3 and 5 first; absent anchors may be added as unconstrained
coordinates. If 7 occurs, require it to be the first prime after those
anchors. Every later actual prime must have at most three earlier
neighbours, **counting the anchors as well as all earlier private primes**.
The order need not otherwise be numerical.

Writing \(P_*\) for the actual primes at least 7, \(M=|P_*|\), and \(U\)
for the original complete avoiding set, the conclusion is
\[
 H(U)>\frac{67}{4000}
       \prod_{p\in P_*}\frac{p-2}{2(p-1)}
 \ge\frac{67}{4000}\left(\frac5{12}\right)^M>0.
 \tag{OT1}
\]
There are no restrictions on original residues, exponent heights, number
of primes, overlap between successive neighbour sets, or components.
In particular, increasing prime order suffices whenever every prime
has at most three smaller neighbours.
If 7 is absent, no artificial 7-factor enters the product or \(M\).

This order hypothesis does not follow merely from 3-degeneracy. For
example, on primes \(3,5,7,11,13\), let the graph be \(K_5\) minus edge
\(\{3,5\}\). It is 3-degenerate: remove 3, then the remainder is \(K_4\).
But after starting with 3 and 5, every remaining vertex has the two
anchors as neighbours and the remaining three vertices form a triangle;
the last of those three has four earlier neighbours. Thus no required
anchored order exists. This is an obstruction to the proposed order
certificate, not a covering-system counterexample. These graph edges can
be realized by the distinct pair-product numerical labels.

## 2. One global law and once-only ownership

Resolve every original modulus on the full finite CRT coordinates
\(X_p\). Let \(H_p\) be uniform. Remove all original pure \(p\)-power
classes to form \(V_p\), and set
\[
 \nu_p=H_p(\cdot\mid V_p),\qquad c_p=\frac{p-1}{p-2}.
\]
Distinct original numerical moduli give
\(H_p(V_p)\ge(p-2)/(p-1)>0\), hence \(\nu_p\le c_pH_p\).
Start with the fixed product \(\nu_3\otimes\nu_5\), without
conditioning on mixed-anchor survival. The union of all original
\(3^a5^b\) classes, \(a,b\ge1\), has probability at most
\[
 c_3c_5\sum_{a,b\ge1}3^{-a}5^{-b}=1/3.
 \tag{OT2}
\]

Assign each remaining nonpure original class to its latest prime in the
chosen order. At stage \(p\), let \(B_p(x)\) be its actual forbidden
coordinate union at the complete preceding word, and put
\(\alpha_p(x)=\nu_p(B_p(x))\). Use the normalized capped kernel with
threshold \(1/2\). Its density relative to \(\nu_p\) is zero on
\(B_p\) and \((1-\alpha_p)^{-1}\) off it when \(\alpha_p\le1/2\);
otherwise it is \(2-1/\alpha_p\) on \(B_p\) and 2 off it. Thus at
every complete history
\[
 K_p(X_p)=1,\quad K_p\le2\nu_p,\quad
 K_p(B_p)=2(\alpha_p-1/2)_+.
 \tag{OT3}
\]
At \(\alpha_p=1\) this is \(K_p=\nu_p\), so completely forbidden
fibres are retained and charged. At zero it is also normalized.

Append all these kernels in the certified order to obtain one probability
law \(\mathbb P\). Later normalized kernels preserve every earlier
prefix marginal and every earlier assigned-violation probability. At
positive depth \(e\), a selected earlier coordinate has the following
cap conditional on its *entire* earlier history:
\[
 3:\ 2\,3^{-e},\qquad
 5:\ \tfrac43 5^{-e},\qquad
 q\ge7:\ 2c_qq^{-e}.
 \tag{OT4}
\]
Depth zero has cap one. No conditioning on all previous avoidance is
performed, and no independence of the actual private coordinates is used.

## 3. Every three-neighbour set fits the same comparison polynomial

For stage \(p\), let \(S_p\) be its actual earlier-neighbour set. Every
other prime in an assigned original modulus lies in \(S_p\). Its complete
label is
\(p^e\prod_{q\in S_p}q^{f_q}\), where \(e\ge1\), \(f_q\ge0\),
and at least one \(f_q>0\); pure classes were already removed.

First bound the actual forbidden union by the sum over its original
labelled cylinders with weights \(c_pp^{-e}\). The relevant predecessor
law is the actual global prefix marginal, which also includes coordinates
outside \(S_p\). To restrict the comparison to selected coordinates,
list \(S_p=\{s_1,\ldots,s_k\}\) in processing order. Let
\(\mathcal H_i\) be the complete history immediately before \(s_i\),
and let \(\mathcal G_i=\sigma(X_{s_1},\ldots,X_{s_{i-1}})\).
Since \(\mathcal G_i\subseteq\mathcal H_i\), every original cylinder
event \(E\) on coordinate \(s_i\) with deterministic cap \(b_E\)
satisfies the tower bound
\[
 \Pr(E\mid\mathcal G_i)
 =\mathbb E[\Pr(E\mid\mathcal H_i)\mid\mathcal G_i]
 \le b_E.
 \tag{OT4a}
\]
The full-history bound (OT4) remains valid in this prefix marginal
because all later kernels are normalized. Thus the selected-coordinate
law meets the hypotheses of
[Schroeder's pinned Proposition 3.2, Conditional comparison](../../../../Library/Arith/schroeder2026noncoverage.md#conditional-comparison-and-the-unrestricted-positive-part-bound).
Apply it to the finite original labelled sum and the hinge
\(h(u)=2(u-1/2)_+\). It introduces one independent auxiliary uniform
per selected coordinate, shared by all labels at that coordinate. No
extra factor comes from intervening unselected coordinates. Equivalently,
one can use the entire prefix with whole-space events and cap one on
those coordinates. The actual coordinates need not be independent.

Only after this comparison, complete the nonnegative exponent tuples.
There is at most one label for each full numerical exponent vector, and
\(\sum_{e\ge1}c_pp^{-e}=1/(p-2)\). If \(N_q=1+K_q^*\), where
\(\Pr(K_q^*\ge e)\) is the corresponding cap in (OT4), the completed
load is at most
\[
 \frac{\prod_{q\in S_p}N_q-1}{p-2}.
 \tag{OT5}
\]
This includes original residues depending on the entire numerical label.
Completion does not assert alignment or compatibility of those residues.
Unbounded auxiliary depths follow by monotone convergence; the variables
have finite third moments.

Take independent comparison variables
\[
 \Pr(N_3\ge e+1)=2\,3^{-e},\quad
 \Pr(N_5\ge e+1)=\tfrac43 5^{-e},\quad
 \Pr(N_*\ge e+1)=\tfrac{12}{5}7^{-e}\quad(e\ge1).
 \tag{OT6}
\]
An actual root 3 or 5 occupies its own slot. Sort the actual private
parents as \(q_1<q_2<q_3\), taking only those present. Their slot
assignment is:

| Actual root parents | Private parents allowed | Assigned slots |
|---|---:|---|
| 3 and 5 | at most 1 | \(q_1\mapsto N_*\) |
| 3 only | at most 2 | \(q_1\mapsto N_*,q_2\mapsto N_5\) |
| 5 only | at most 2 | \(q_1\mapsto N_*,q_2\mapsto N_3\) |
| neither | at most 3 | \(q_1\mapsto N_*,q_2\mapsto N_5,q_3\mapsto N_3\) |

Unused slots can be inserted since each \(N\ge1\). Distinct actual
primes give \(q_1\ge7,q_2\ge11,q_3\ge13\). The positive-depth
caps satisfy
\[
 2c_qq^{-e}\le\tfrac{12}{5}7^{-e}\quad(q\ge7),
 \tag{OT7}
\]
\[
 2c_qq^{-e}\le 2c_{11}11^{-e}
 \le\tfrac43 5^{-e}\quad(q\ge11),
 \tag{OT8}
\]
\[
 2c_qq^{-e}\le2\,3^{-e}\quad(q\ge11).
 \tag{OT9}
\]
For (OT8), the ratio of its middle quantity to the right-hand side is
\(\frac{25}{33}(\frac5{11})^{e-1}\le25/33<1\).
For (OT9), the ratio is \(c_q(3/q)^e\le10/33<1\).
Equation (OT7) follows because both \(c_q\) and \(q^{-e}\) decrease.
Common-uniform coupling on the three distinct slots now proves
\[
 \prod_{q\in S_p}N_q-1\ \le_{\rm st}\ Y:=N_3N_5N_*-1.
 \tag{OT10}
\]

If actual prime 7 occurs, it was placed first after the anchors; it has
no private predecessor and uses \(Y_0=N_3N_5-1\) instead. All other
actual stages have \(p\ge11\), irrespective of their processing order.
Writing
\[
 F_0(p)=\frac2{p-2}\mathbb E(Y_0-(p-2)/2)_+,\qquad
 F(p)=\frac2{p-2}\mathbb E(Y-(p-2)/2)_+,
 \tag{OT11}
\]
we therefore charge 7 by \(F_0(7)\) and every actual \(p\ge11\) by
\(F(p)\). This is the same numerical fee table as for books, but its
validity now uses only the three-neighbour order certificate.

## 4. Global reserve and full Haar density

Each actual prime is processed and charged once. The six early fees
obey the strict rational bounds
\[
 (F_0(7),F(11),F(13),F(17),F(19),F(23))
 <(174,148,92,42,30,16)/1000.
\]
Their sum is less than \(251/500\). The complete moment is
\(\mathbb EY^3=92467/360\). Using
\((u-t)_+\le4u^3/(27t^2)\) and overcounting primes at least 29 by
all odd integers yields
\[
 \sum_{\substack{p\ge29\\p\text{ prime}}}F(p)
 \le\frac{32}{27}\frac{92467}{360}
     \left(\frac1{27^3}+\frac1{4\,27^2}\right)
 =\frac{2866477}{23914845}<\frac3{25}.
 \tag{OT12}
\]
Thus the sum over actual stages is less than \(311/500\). Missing
actual primes only remove nonnegative fees from this bound. Together
with (OT2), the union bound in the single law gives
\[
 \mathbb P(U)>1-\frac13-\frac{311}{500}
 =\frac{67}{1500}.
 \tag{OT13}
\]

The actual conditional density bounds multiply along this same law:
\[
 \mathbb P\le D H,\qquad
 D=\frac83\prod_{p\in P_*}2c_p.
 \tag{OT14}
\]
This is a bound on the full joint density, not a product of marginal
caps. Combining (OT13) and (OT14) proves (OT1). Every factor in (OT1)
is at least \(5/12\). Free missing anchor coordinates can be projected
away without changing the original avoiding Haar proportion.

## 5. A ten-prime block beyond the book structure

Let
\[
 (p_1,\ldots,p_{10})=(3,5,7,11,13,17,19,23,29,31).
\]
Permit every original numerical modulus whose support is contained in
one of the seven sliding windows
\[
 W_i=\{p_i,p_{i+1},p_{i+2},p_{i+3}\},\qquad 1\le i\le7.
 \tag{OT15}
\]
Any finite distinct-modulus family with these supports, arbitrary
exponent heights and arbitrary original residues satisfies (OT1).
Indeed, its actual interaction graph is a subgraph of the third power
of the ten-vertex path: two indices are adjacent exactly when their
distance is at most three in the full graph. Each prime has at most
the previous three primes as earlier neighbours.

If the family includes at least one label with full support \(W_i\)
for each \(i\), the actual graph is precisely this path power. It has
one biconnected block containing all ten vertices: removing any vertex
leaves the path connected using steps of length at most two across the
removed location. Thus the graph lies outside the class whose blocks
all have at most seven vertices. It is also outside the common
\(\{3,5\}\)-book class. For example, the full window
\(W_3=\{7,11,13,17\}\) contains four private primes, whereas a
book page permits at most two. Equivalently, removing 3 and 5 leaves
a connected graph on eight vertices, instead of disjoint components
of size at most two.

This example specifies an entire allowed-support class, including
arbitrarily many distinct original labels and arbitrarily high powers.
The conclusion is not inferred from the small reciprocal sum of seven
chosen illustrative classes. The same sliding-window argument works
on arbitrarily long increasing odd-prime lists.

## 6. Fixed-head continuation to unrestricted large primes

Fix a finite actual head prime set \(P\) and one anchored order
certificate for its head-only family. Let
\[
 M=|P\setminus\{3,5\}|,\qquad
 \varepsilon_M=\frac{67}{4000}\left(\frac5{12}\right)^M.
 \tag{OT16}
\]
The order condition applies to the graph generated by original
**head-only** labels. It need not hold for the head-induced graph after
arbitrary tail-touching labels are added. Unused head coordinates and
absent pure or mixed classes are allowed.

At heights resolving the entire larger original family, let \(U_H\)
be the set avoiding all head-only classes and take the unnormalized
Haar restriction \(\mu_H=H_P|_{U_H}\). Uniform lifting from the
head-only heights preserves its density, so (OT1) gives
\[
 \mu_H(X)>\varepsilon_M,\qquad \mu_H\le H_P.
 \tag{OT17}
\]
As in Chapter 37, use the existing homogeneous joint-load continuation
from [Chapter 33](33-seven-small-primes-with-an-unrestricted-large-prime-tail.md)
with joint density cap one and
\[
 M_2(P)=\prod_{p\in P}\left(1+\frac{3p-1}{(p-1)^2}\right).
\]
For integers \(\ell\ge6\), set
\[
 B=3^\ell,\qquad c_\ell=\frac{2\ell^2+1}{2\ell^2-1},
\]
\[
 \tau_7(B,\ell)=\frac{c_\ell^7}{B}
 \left(\frac B{B-3}\right)^2
 \sum_{h=0}^7\frac{7!}{(7-h)!\ell^h}.
 \tag{OT18}
\]
Increase \(\ell\) until
\[
 B\ge\max(\{286\}\cup P),\qquad
 M_2(P)\tau_7(B,\ell)<\varepsilon_M/2.
 \tag{OT19}
\]
This is an exact-rational search and terminates: the factor \(3^{-\ell}\)
tends to zero and the remaining factors stay bounded. The inherited
analytic hypotheses \(B\ge286,\ell\ge4,3^\ell\le B\) all hold.

If every actual prime outside \(P\) exceeds the resulting cutoff,
Chapter 33's one sequence of normalized kernels loses less than
\(\varepsilon_M/2\) of weighted mass. It retains every original
tail-touching label, including its complete head exponents and residue,
and charges each actual tail prime once. There is no restriction on
how many head or tail coordinates one such modulus joins. Positive
remaining mass gives an original avoiding CRT tuple.

The head is fixed before selecting the cutoff. This is a sufficient
prime-gap condition, not a claim that an arbitrary family already has
such a gap. The final weighted reserve is not the same numerical lower
bound for the final full Haar density. This continuation inherits
Chapter 33's explicitly stated analytic premise and verification boundary.

## 7. Reuse and verification boundary

[Chapter 07](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md)
already supplies the actual latest-prime ownership and
normalized global sequential-kernel architecture, including arbitrary
overlap of earlier-neighbour sets. Its displayed theorems instead start
with an already surviving head law and use quadratic estimates with
additional prime cutoffs. The present deduction starts from unconditioned
product pure-anchor survivors, pays the mixed-anchor loss once, and uses
the integrated hinge and the three-slot cap assignment. It closes all
actual primes under the stated order assumption, with an explicit full
Haar reserve. The root law here is not head-safe; a head-safe endpoint
cannot be invoked without this separate root-loss accounting.

Every common-\(\{3,5\}\) book with private pages of size at most two has
the required increasing-prime order, so the proof subsumes its
noncoverage conclusion. Section 5 gives a class beyond that fixed
two-prime-spine structure. The book-specific pairing also supplies its
per-page density simplification \((67/4000)(3/16)^N\).

An extension to unrestricted ordered predecessor sets or every
3-degenerate graph is not proved. The existing Chapter 37
[`spine_book_density_certificate.py`](../frontier/cover-geometry/spine_book_density_certificate.py)
and its
[`exact output`](../frontier/cover-geometry/spine_book_density_certificate.json)
check precisely the same six early fees, complete third moment, cubic
tail, and reserve used in Section 4. No duplicate numerical producer is
needed here. The all-depth slot inequalities (OT7)--(OT9), selected
tower passage, original-label completion, and graph interface are the
ordinary proof steps supplied above. Existing source
comparison theorems are reused, not re-proved or packaged as new Lean.
