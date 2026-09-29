# Owner-independent depth-two certificates reduce the remaining star restriction to 5,7

The six-coordinate depth-two source/query construction admits a common
five-leaf certificate with no specified star owners. In particular, if
on every retained ternary leaf the actual star deletion masses satisfy

$$
 \beta_{q\ell}^{\rm act}\le\frac{2}{3(q-2)}
 \qquad(q=5,7),                                      \tag{SP1}
$$

then the four larger coordinates q=11,13,17,19 may each use their full
possible star budget 2/(q-2). The same-source query upper is <113/10,
strictly below the pure-conditioned23/29 continuation threshold566/49.
This is a uniform sufficient condition for actual masks satisfying SP1,
not a proof that every actual family satisfies SP1. The full prime support here is contained in
{3,5,7,11,13,17,19,23,29}; the last two coordinates use the stated
outside continuation. The whole original family must have ternary exponent at most2. Arbitrary finite
nonternary exponents and original phases remain allowed.

The statements below are ordinary mathematical consequences of the
six-coordinate signed-support and same-carrier query interfaces, with
exact rational verification. They are not new Lean verification.

## 1. A conditional theorem for arbitrary common target masses

Set Q=(5,7,11,13,17,19), b_q=1/(q-2), C_q=(q-1)/(q-2), and retain the
five actual ternary leaves with roots R0={0,1}, R1={2,3,4}. Use fixed
weights

$$
 w=(1/4,1/4,1/6,1/6,1/6).                              \tag{SP2}
$$

Choose rational target masses m_q, common across all leaves, with
C_q/q<=m_q<=1. Assume the actual star-survivor mass a_ql is at least m_q
on every leaf and coordinate. Here the actual star mask is the union
of all source-live original3q^e and9q^e blockers, with their original
exponents and phases. For its actual survivor submeasure eta_ql,
perform the uniform thinning

$$
 \xi_{q\ell}=\frac{m_q}{a_{q\ell}}\eta_{q\ell}.          \tag{SP3}
$$

Thus xi has mass m_q, is supported on actual star avoidance, and remains
dominated by the actual pure-q source law. This construction works on
finite carriers and does not invent a compatible corner source. Start
from the one actual supported submeasure

$$
 \nu=\sum_\ell w_\ell\delta_\ell\otimes\bigotimes_q\xi_{q\ell},
$$

then restrict to avoidance of every remaining actual mixed original.
Only this common submeasure and its final normalization are used for
source mass, query and continuation.

For S subset Q define the signed coordinate residual

$$
 Z(S)=\sum_{\mathcal P}(-1)^{|\mathcal P|}
       \prod_{D\in\mathcal P}\left(3\prod_{q\in D}\frac{b_q}{m_q}\right),
                                                               \tag{SP4}
$$

where P ranges over pairwise disjoint subsets D of S with |D|>=2,
including the empty collection. Require

$$
 Z(S)>0\quad (|S|\le4).                                \tag{SP5}
$$

Let e_j be the j-th elementary symmetric function of (b_q/m_q) and
write

$$
 G=\prod_qm_q\left[
 1-\frac74\sum_{j=2}^6 e_j
 +\frac{29}{12}(3e_4+10e_5+25e_6)
 -\frac{37}{4}\,15e_6\right].                         \tag{SP6}
$$

Define an unnormalized independent product law of integer factors V_q
by

$$
 u_q(1)=m_q-C_q/q,
 \qquad u_q(v)=\frac{C_q(q-1)}{q^v}\quad(v\ge2).
$$

Its mass is m_q and first moment is m_q+b_q. Let p_n be the unnormalized
mass of N=product V_q at n. Define

$$
 H=\frac74\prod_q(m_q+b_q)-6\prod_qm_q
   +\frac{17}{4}p_1+\frac52p_2+\frac32p_3+p_4+\frac12p_5. \tag{SP7}
$$

If SP5 holds, G>0 and

$$
 (615/49-6)G-H>0,                                      \tag{SP8}
$$

then the actual mixed-surviving supported mass is at least G, and its
normalized query response satisfies

$$
 R_{v_3\le2}\le5+H/G<566/49.                           \tag{SP9}
$$

This is the desired general conditional certificate, not merely a
collection of isolated numerical weights.

## 2. Why the signed source bound remains a probability bound

At one leaf, actual normalized support-group weights are bounded by
3 product_{q in D}(b_q/m_q), |D|>=2. SP5 is checked at these maximal
caps. Decreasing any support weight preserves positivity on coordinate
subsets of size at most4: its derivative is minus a complementary
residual of size at most2, and induction supplies positivity along the
whole decreasing box.

For any allowed support weights, a nonpositive full signed response is
a trivial probability lower bound. If its full response is positive,
for any five-coordinate set A use the coordinate recurrence at its
missing coordinate q:

$$
 Z(Q)=Z(A)-\sum_{D\ni q}c_D Z(Q\setminus D).
$$

Every complementary residual has size at most4 and is positive. Hence
Z(A)>=Z(Q)>0. All coordinate residuals are now positive. Deleting any
set of event groups decreases their weights toward zero; the same
complementary-residual induction keeps the full and lower residuals
positive. The signed-support probability interface therefore applies.
The signed full polynomial is a valid lower bound whether or not its
maximal-cap value is positive. In fact both concrete certificates below
have negative maximal-cap six-coordinate residuals; this is consistent
with the argument and is not a missed positivity assumption.

For every support D, the d,3d,9d inventories retain their distinct full
numerical labels and share one root and one leaf allocation across all
five leaves. Their ten corner multiplicity vectors are

$$
 v_\ell^{r,s}=1+\mathbf1_{\ell\in R_r}+\mathbf1_{\ell=s}.
$$

For k pairwise disjoint supports the signed coefficient can be bounded
using the maximum weighted product for odd k and the minimum for even
k. The common masses factor out. The exact three constants are

$$
 \kappa_1=7/4,\qquad\kappa_2=29/12,\qquad\kappa_3=37/4.
$$

For k=1 the maximum uses the short root and one of its own leaves.
For k=2, opposite roots with one own leaf apiece attain29/12. To see the
lower bound, expand the weighted product: the baseline and the two
root masses total2; the remaining terms are the two leaf weights,
the cross-incidences, root intersection, and any coincident-leaf term.
If the roots differ, the independent minima of leaf-plus-cross terms
are1/4 and1/6. If the roots agree, their intersection alone adds1/2,
and the two leaf weights add at least1/3. Thus29/12 is the minimum.
For k=3, weighted Holder bounds the product by the largest weighted
cube of a single corner; its maximum37/4 is attained by repeating the
short-root/own-leaf corner three times. The checker also enumerates all
10,100,1000 ordered corner tuples exactly.

A six-set has3 partitions into two nonsingleton blocks on four elements,
10 on five,25 on six, and15 into three pairs on six. Bounding each
signed partition term in the safe direction gives SP6. This does not
require these separately extremal coefficients to be attained together
by any actual family.

## 3. Why a fixed query corner is now sufficient

For fixed product load N and any allocation corner, the leaf-weighted
hinge is sum_l w_l[v_l N-6]_+. A short root and one of its own leaves
has multiplier law

$$
 \Pr(V=1)=1/2,\quad\Pr(V=2)=1/4,\quad\Pr(V=3)=1/4.
$$

This law dominates every other corner for increasing convex functions.
A long root and own leaf has masses(1/2,1/3,1/6) and is dominated by a
simple shift of mass from2 to3. A long root and short leaf has masses
(1/4,3/4,0); the difference of expectations is
(\phi(1)-2\phi(2)+\phi(3))/4>=0. A short root and long leaf has masses
(1/3,2/3,0); the difference is
(\phi(1)-2\phi(2)+\phi(3))/6+(\phi(3)-\phi(2))/12>=0.

All leaves have identical auxiliary product laws because their target
masses are common. Consequently the same corner wins pointwise at
every exponent tuple, before integration. No generally invalid
exchange of a varying maximum with integration is used. The exact
query upper is

$$
 H=\int\left(\tfrac12[N-6]_+
          +\tfrac14[2N-6]_++\tfrac14[3N-6]_+\right)\,du.
$$

For N>=6 the integrand is(7/4)N-6. Its difference from this affine
expression at N=1,2,3,4,5 is17/4,5/2,3/2,1,1/2 respectively. The full
product mass and first moment therefore give exactly SP7. Every
prime-power height is included; only the finitely many small product
atoms need enumeration. The unit nonternary cofactor is included.

## 4. Two concrete uniform certificates

The first certificate is owner-independent throughout the box

$$
 \beta_{q\ell}^{\rm act}\le(9/10)b_q
 \quad(q\in Q,\ \ell=0,\ldots,4).
$$

Use m=(7/10,41/50,9/10,101/110,47/50,161/170). Its exact outputs are

$$
 \min_{|S|\le4}Z(S)=7207/111807,\qquad
 \min_q(m_q-C_q/q)=13/30,
$$

$$
 G=1963520017/25818750000,\quad
 (615/49-6)G-H>1/50,\quad R<113/10<566/49.
$$

In particular this covers the balanced budget parameters with root
shares b_q/2 and leaf shares b_q/5, which lie outside the former
DT+.01 target boxes. This statement is about a legal budget vector;
it does not assert an exact finite family realizes that vector.

The second certificate assumes only SP1. For q=11,13,17,19 the universal
root-plus-leaf budget already supplies beta_ql<=2b_q, without a further
owner condition. Use

$$
 m=(7/9,13/15,7/9,9/11,13/15,15/17).
$$

Then

$$
 \min_{|S|\le4}Z(S)=23/273,\qquad
 \min_q(m_q-C_q/q)=23/45,
$$

$$
 G=401209/6816150,
$$

$$
 H=318796013142906561738218675031086501
     /860130022681537511729619735529087500,
$$

$$
 (615/49-6)G-H
 =12872761849864573554575016887810749
    /860130022681537511729619735529087500
 >7/500,
$$

$$
 R<113/10<566/49.
$$

All five leaves carry positive weight. The residual minimum for both
certificates occurs at the four-coordinate set{5,7,11,13}. The first
certificate handles a wider small-prime budget than the second; the
second frees all four larger budgets. Neither logically subsumes the
other, and neither covers every admissible profile.

## 5. Exact scope of the remaining global problem

Any profile outside the second sufficient region has some retained
leaf and q in{5,7} with beta_ql>2b_q/3. Thus, after applying this
certificate, only profiles with a concentrated small-prime star mask
remain. This is a necessary description of the uncovered region, not
a claim that those profiles fail to have survivors or that they form a
single jointly realizable extremizer. The remaining work is to exploit
the original shared root/leaf allocations and phases at those small
primes while transporting every resulting certificate to one actual
source. No condition on the four larger star budgets needs to be
added in the region already proved here.

The [standalone verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_small_primes.py)
and [retained exact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_small_primes.json)
check all low-dimensional residuals, ordered inventory products, pointwise
query corners at every hinge breakpoint and the final slope, and complete-tail
source/query bounds. It uses no optimization package, actual-phase scan,
or tail cutoff. Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_small_primes.py
```

The source and query interfaces are developed in
[Report710](710-shared-support-and-query-carriers-pass-the-fixed-depth-two-profile.md).
Independent explicit support partitions and an alternative full-moment query
calculation reproduce the second certificate's exact source, hinge and score.

## 6. The uncovered region forces one of four original first-level labels

Keep exactly the actual source, retained ternary leaves, whole-family
v3<=2 scope and outside23/29 continuation of the owner-independent
certificate. Let beta_ql be the actual pure-q source mass of the union
of all source-live original3q^e and9q^e blockers on one retained leaf.
Write A_ql for the union supplied by the two possible original labels
3q and9q alone, retaining their original q residues and ternary owners.
There is at most one original for each numerical label.

The remaining star labels have e>=2. Their source mass is at most

$$
 \lambda_q\!\left(\bigcup_{e\ge2}\{
     \text{live }3q^e\text{ or }9q^e\text{ blocker}\}\right)
 \le 2\sum_{e\ge2}\frac{C_q}{q^e}
 =\frac{2b_q}{q}.
$$

This bound allows every height in both inventories; it does not truncate
or identify original phases. Hence

$$
 \beta_{q\ell}>\frac23b_q
 \quad\Longrightarrow\quad
 \lambda_q(A_{q\ell})>
       \left(\frac23-\frac2q\right)b_q.                \tag{FS1}
$$

For q=5 the right side is4/45, and for q=7 it is8/105. A missing original
or a forbidden cylinder outside the actual source contributes zero.
Thus every profile outside the two-small-prime sufficient region has
one retained leaf on which at least one of the actual numerical labels
15,45,21,63 supplies a positive source-live first-level blocker.

Equivalently, if the first-level live union masses are at most4/45 for
q5 and8/105 forq7 on every leaf, the two-small-prime certificate applies,
regardless of all higher star exponents and all larger-q star budgets.
In particular, a family with none of15,45,21,63 has no remaining star
profile obstruction in this declared scope.

This is a necessary description of the uncovered region, not a claim
that the four labels are sufficient for a cover. Their root/leaf
allocations and q residues must still arise in one actual original
family. The point is to isolate a finite set of original first-level
relations for the next forcing argument; no independent phase optimum
or numerical corner source is substituted.
