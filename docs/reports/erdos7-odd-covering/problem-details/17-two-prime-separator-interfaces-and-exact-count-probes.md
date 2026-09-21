# Two-prime separator interfaces and an original-AP countercontrol

This note establishes an exact interface and a sufficient quantitative
recursion for clique trees, and identifies a missing observation in a concrete
original-AP example. It does not prove a new noncoverage theorem for arbitrary
two-prime clique sums. In particular, the displayed two-K4 example has six
total primes; bare noncoverage is not claimed as new beyond the reported
at-most-eight-total-primes result.

The self-contained Python 3 standard-library [control program](../frontier/cover-geometry/two_prime_separator_controls.py)
and its [exact data](../frontier/cover-geometry/two_prime_separator_controls.json)
retain every original label and boundary table. Direct CRT enumeration and
four full-period sieves agree. The results below are ordinary mathematical
proofs and exact experimental checks, without new Lean certification.

## 1. Existing mathematical interfaces and the new obligation

The existing repository declaration
`D5/S3/Arith/Congruence/ExactForestMessages.exact_forest_message_feasibility`
already handles exact feasibility on a finite tree with arbitrary finite
vertex domains and arbitrary parent-child incompatibility relations. It can
be applied here by taking a tree vertex's state to be an entire bag assignment
and declaring two neighboring bag assignments incompatible when they disagree
on either separator coordinate. Thus Boolean junction-tree feasibility is a
direct reuse; it should not be represented as new Lean content.

The current edge/cycle/four-vertex-block proof uses scalar feasible domains
at articulation primes. A separator containing two primes instead has an
actual relation on two complete prime-power coordinates. Its two projections
do not determine that relation. The useful additional interface is the joint
extension-count kernel and its actual conditional budgets. The common-source
discipline is the same one emphasized in RRO Recovery Geometry §17.8; the AP
identities and countercontrol below establish its concrete application here.

## 2. A clique tree with original labels assigned once

Let \(D\) be a finite set of distinct odd moduli greater than one, with one
chosen residue \(a_d\pmod d\) per modulus. Put
\[
 Q=\operatorname{lcm}D,\qquad X_p=\mathbb Z/p^{h_p}\mathbb Z,
 \qquad h_p=v_p(Q),
\]
and use the original product Haar law \(H=\bigotimes_p H_p\).

Assume a finite tree of prime bags \(B_t\), each of size at most four, with
the running-intersection property: the bags containing any one prime form a
connected subtree. Every original support is contained in a bag. The
intersection of a child bag with its parent is a two-prime separator
\(S_t\); singleton separators can also be allowed without changing the
formulas. This describes the intended tree of clique sums along edges. It is
an explicit structural assumption, not a property of every general prime
graph.

Root the bag tree. Assign each original class to exactly one bag containing
its support, for example the highest such bag. The bags containing a fixed
support form a connected subtree, so this convention is unambiguous. Let
\(L_t(x_{B_t})\) be the indicator that the full bag assignment avoids all
original labels assigned to \(t\). Separator-supported labels and pure
powers are also assigned once; they are not copied into both branches.

Write \(I_t\) for the primes occurring strictly on the child side of the
edge above \(t\), excluding \(S_t\). At a fixed bag, the private interiors
of different child subtrees are disjoint by running intersection. All
prime-power heights and residues in this construction are the original ones.

## 3. The exact joint kernel

For a nonroot bag define
\[
 W_t(s)=H_{I_t}\{x_{I_t}:\text{all labels owned at or below }t
                  \text{ are avoided at }(s,x_{I_t})\},
 \qquad s\in X_{S_t}.
 \tag{1}
\]
This is a function on the full two-coordinate boundary, not a pair of
one-coordinate marginals. Its positive support
\(R_t=\{s:W_t(s)>0\}\) is the exact joint extendability relation.

If the child bags of \(t\) are \(c\), then
\[
 W_t(s)=
 \int_{X_{B_t\setminus S_t}}
       L_t(x_{B_t})\prod_c W_c(x_{S_c})\,
       dH_{B_t\setminus S_t},
 \qquad x_{S_t}=s.
 \tag{2}
\]
At the root \(o\), the original uncovered Haar mass is exactly
\[
 U=\int_{X_{B_o}}L_o(x_{B_o})\prod_cW_c(x_{S_c})\,dH_{B_o}.
 \tag{3}
\]
Equations (2)--(3) follow by finite Fubini. Conditioned on one actual bag
assignment, the private child interiors are disjoint and have product Haar
law; this is where the product of kernels is justified. If child separators
overlap, their factors still read the very same bag coordinates. One must
multiply them at those coordinates before integrating.

Let \(N_t(s)\) be the number of avoiding private assignments. Then
\[
 W_t(s)=\frac{N_t(s)}{\prod_{p\in I_t}p^{h_p}}.
 \tag{4}
\]
For two subfamilies meeting exactly in \(S\), with all shared labels assigned
once, the total number of avoiding assignments is consequently
\[
 \sum_{s\in X_S}N_A(s)N_B(s).
 \tag{5}
\]
Multiplying total counts, multiplying marginal supports, or coupling sorted
entry lists instead does not preserve (5).

## 4. A sufficient quantitative invariant for arbitrary finite clique trees

One exact form of a quantitative induction invariant is a family of
nonnegative separator functions \(\underline W_t\) satisfying
\[
 \underline W_t(s)\le
 \int L_t(x_{B_t})\prod_c\underline W_c(x_{S_c})\,
                 dH_{B_t\setminus S_t}
 \tag{6}
\]
for every boundary word. Monotonicity of (2) proves inductively that
\(W_t\ge\underline W_t\). If the root expression in (3) with these lower
kernels is positive, then the original family is noncovering. No equality of
different probability laws is assumed.

A more concrete sufficient condition supplies (6) by a common conditional
budget. For each edge choose a joint relation \(A_t\subseteq X_{S_t}\) and
a constant \(m_t>0\). For a fixed \(s\in A_t\), set
\[
 g_t(s)=H_{B_t\setminus S_t}(L_t=1\mid x_{S_t}=s)>0,
\]
and let \(\nu_{t,s}\) be that one conditional local law, normalized on
\(L_t=1\). Suppose
\[
 \sum_{c}\nu_{t,s}\{x_{S_c}\notin A_c\}
       \le1-\eta_t(s),\qquad \eta_t(s)>0,
 \tag{7}
\]
and choose
\[
 m_t\le\inf_{s\in A_t}
             g_t(s)\eta_t(s)\prod_c m_c.
 \tag{8}
\]
For nonempty finite \(A_t\), a positive right side is enough; empty
relations may be discarded as unusable in this certificate.

Then \(W_t(s)\ge m_t\) on \(A_t\). To prove it, the union bound under the
same \(\nu_{t,s}\) leaves at least \(\eta_t(s)\) local mass where every child
separator belongs to its \(A_c\). At each such common bag assignment, the
inductive bounds give \(\prod_cW_c\ge\prod_cm_c\). Integrating proves
(8). The same condition at the root, with no incoming separator, gives
positive uncovered Haar mass for any finite depth and any number of bags.

This does not assume independence of the child bad events in (7). Nor does
it multiply existential survival fractions obtained at incompatible boundary
values: each \(m_c\) is a pointwise bound on its entire certified relation,
and all factors are evaluated at one actual bag assignment.

For several branches attached to one fixed separator, the simpler condition
is useful: under one common boundary law \(\nu\), if
\(\nu(A_i^c)\le\epsilon_i\) and \(\sum_i\epsilon_i<1\), then
\[
 \nu\left(\bigcap_iA_i\right)\ge1-\sum_i\epsilon_i>0.
 \tag{9}
\]
For \(\nu=H_S\), pointwise bounds \(W_i\ge m_i>0\) on the \(A_i\)
give original uncovered Haar mass at least
\((1-\sum_i\epsilon_i)\prod_i m_i\). If instead a different boundary
law is used, a bound \(\nu(E)\le C H_S(E)\) for every event \(E\),
with a specified finite \(C>0\), gives the same lower bound divided by
\(C\). Without such a conversion, (9) supplies an intersection statement
under \(\nu\), not that numerical bound under the original Haar law.
Multiplying a proved Haar bound by the full period gives the corresponding
count bound in (5). Two separate one-coordinate projection bounds do not
provide the joint costs \(\epsilon_i\).

The unresolved arithmetic obligation is to construct such joint relations,
conditional bad-event budgets or lower-kernel profiles with summable costs
uniformly over the permitted original labels and heights. Equations
(6)--(9) are sufficient interfaces; their hypotheses have not been proved for
arbitrary edge-glued K4 families by the existing articulation fees.

## 5. An actual-AP nonproduct boundary relation

Start with these original classes, as in the earlier Nyx four-cycle proposal:

| modulus | residue |
|---:|---:|
| 3 | 0 |
| 5 | 0 |
| 7 | 0 |
| 9 | 2 |
| 11 | 0 |
| 15 | 1 |
| 33 | 1 |
| 35 | 8 |
| 45 | 37 |
| 49 | 2 |
| 77 | 1 |
| 245 | 99 |

The complete separator coordinates are \(x\bmod9\) and \(y\bmod49\).
Their pure survivor domains are
\[
 V_3=\{1,4,5,7,8\},\qquad
 V_7=\{y\bmod49:7\nmid y,\ y\ne2\},\quad |V_7|=41.
 \tag{10}
\]
For \(x\in V_3,y\in V_7\), put
\[
 a=\mathbf1_{x\equiv1\pmod3},\quad b=\mathbf1_{x=1\pmod9},
 \quad c=\mathbf1_{y\equiv1\pmod7},\quad d=\mathbf1_{y=1\pmod{49}}.
\]
The exact number of private \((5,11)\)-coordinate extensions is
\[
 N_A(x,y)=(4-a-b-c-d)(10-\mathbf1_{a\lor c}),
 \tag{11}
\]
and is zero outside \(V_3\times V_7\).

For (11), the four possible mixed exclusions at prime five have distinct
roots \(1,2,3,4\), activated respectively by \(a,b,c,d\). The pure class
excludes root zero. At prime eleven the two mixed classes, when active,
exclude the same root one; the pure class excludes root zero. Also
\(b\Rightarrow a\) and \(d\Rightarrow c\). Hence
\[
 R_A=V_3\times V_7\setminus\{(1,1)\}.
 \tag{12}
\]
Both coordinate projections of \(R_A\) are full, but their product is not
the actual relation.

To make the original graph a K4 on \(\{3,5,7,11\}\), add original labels
\(21,55,1155\), all at residue zero. They do not change (11), since their
classes are already removed by the original pure-prime classes. The
four-prime label 1155 is retained as an original class.

These redundant padding labels deliberately establish the stated prime-graph
geometry. The padded family is not claimed to be irredundant, to have a
private point for every class, or to satisfy the stronger extremal-family
hypotheses. No such property is used in this countercontrol.

## 6. Same domains and scalar summaries, different result after the same gluing

Let \(A'\) change only the residue of modulus 45 from 37 to 22. Both residues
are two modulo five, but their residues modulo nine are respectively one and
four. Consequently \(N_{A'}\) is exactly \(N_A\) with the rows \(x=1\)
and \(x=4\) interchanged. In particular
\[
 R_{A'}=V_3\times V_7\setminus\{(4,1)\},\qquad
 N_A(1,1)=0,\qquad N_{A'}(1,1)=9.
 \tag{13}
\]
The two families have the same original moduli, heights, individual feasible
domains, 204 positive boundary pairs, total private extension count 5816,
and complete entry histogram:
\[
 \#(N=0,9,18,27,40)=(237,8,48,80,68).
 \tag{14}
\]
The count includes all 441 full separator words. Their **weighted**
one-coordinate marginals are not all equal: the first weighted marginal
changes under the row swap. The comparison only claims equality of the
listed Boolean projections and scalar/histogram observations.

Now attach a second K4 on \(\{3,7,13,17\}\). Its initial original labels
are
\[
 13,17,39,51,91,119,221,4641,
\]
all at residue zero. They have exactly 192 private extensions at every
separator pair: the 13- and 17-coordinates have respectively 12 and 16
nonzero choices, and the other zero classes are redundant there. Add the
same new original label to both families:
\[
 M=97461=9\cdot49\cdot13\cdot17,
 \qquad a_M=1.
 \tag{15}
\]
Its full separator condition is precisely \((x,y)=(1,1)\); it excludes
exactly the private pair \((1,1)\) at primes 13 and 17. Thus the second
bag's extension-count kernel becomes
\[
 N_B(x,y)=192-\mathbf1_{(x,y)=(1,1)}.
 \tag{16}
\]

All original moduli are distinct, and the full prime graph is exactly the
union of the two K4 graphs along edge \(\{3,7\}\). After (15) there are
24 labels, including all three displayed four-prime labels
\(1155,4641,97461\). The original common period is
\[
 Q=9\cdot49\cdot5\cdot11\cdot13\cdot17=5360355.
\]
Equation (5) gives the following exact counts:

| Left family | Before the same new label | After the same new label | Deleted |
|---|---:|---:|---:|
| \(A\) | 1116672 | 1116672 | 0 |
| \(A'\) | 1116672 | 1116663 | 9 |

The 441-entry kernels computed directly from the original CRT cylinders
agree with an independent univariate sieve over the full original period,
both before and after adding the label, for both families. These finite
checks certify this countercontrol, not a universal noncoverage theorem.

The result disproves sufficiency of individual feasible domains, total
extension mass, support cardinality and an unlabeled kernel histogram for
this exact future update. It is not a covering example, does not separate
cover from noncover, and does not refute every possible scalar sufficient
criterion for noncoverage.

## 7. General exact-count probes recover the entire joint kernel

The distinction in Section 6 has a general task-relative form. Let an old
family have original period \(Q\), boundary primes \(p,q\) at their full
old heights \(h_p,h_q\), and extension-count kernel \(N(\sigma)\) on
\(S=X_p\times X_q\). Put
\(T=\sum_{\sigma\in S}N(\sigma)\).

Choose distinct fresh odd primes \(r,t\nmid Q\). Add their pure-prime
classes at zero. The new common period is \(Qrt\), and the number of
survivors before any new mixed class is
\(cT\), where \(c=(r-1)(t-1)>1\).

For any chosen \(\sigma\in S\), CRT provides one new original residue
class of modulus
\[
 p^{h_p}q^{h_q}rt
\]
whose boundary is \(\sigma\), with roots one at \(r,t\). Its addition
deletes exactly one private \((r,t)\)-choice for each old extension of
\(\sigma\). Therefore the exact new count is
\[
 T_\sigma^{\rm new}=cT-N(\sigma).
 \tag{17}
\]
The new modulus is distinct from every old one because it contains fresh
primes. If \(pq\) was an old graph edge, this adds a K4 along that edge.
The old heights and the common interface remain fixed across the compared
families and probes.
Different choices of \(\sigma\) are separate alternative continuations of
the same old family. They are not inserted simultaneously as repeated
residue classes of one numerical modulus.

Any representation sufficient for the baseline count and every exact-count
response (17) must determine every \(N(\sigma)\). Even the collection of
all new counts alone determines the table, since
\[
 \sum_{\sigma\in S}T_\sigma^{\rm new}
       =(c|S|-1)T.
 \tag{18}
\]
This is a recoverability statement, not a claim that a program must literally
store a dense table. A lossless compressed description could determine it.
Nor is a memory-size lower bound asserted: not every arbitrary table has
been shown realizable by original AP families.

The task restriction is essential. If \(T>0\), then
\[
 cT-N(\sigma)\ge(c-1)T>0.
\]
Thus every one of these single-label probes preserves positivity. The probe
family establishes necessity of the joint information for **exact-count
responses only**. It supplies no necessity of the full kernel for a
positivity-only proof. A coarser invariant could prove noncoverage, provided
its stability and joint budget under all required continuations are actually
established, for example through a proved instance of Section 4.

## 8. Precise remaining mathematical question

The articulation proof keeps one-coordinate domains and a summable fee. On
an edge separator, the exact continuation instead reads a joint relation or
weighted joint kernel at the same pair of full original coordinates. The
countercontrol proves that replacing this joint object by the product of its
projections is invalid, even when the listed scalar summaries match.

The next useful target is a tractable class of nonnegative two-coordinate
lower kernels, or joint relation-defect budgets, that is closed under (2)
with original-label costs summable across the actual disjoint interiors.
Such a closure would imply noncoverage by (6)--(9). It has not been proved
here. The exact interface, the common-law sufficient criterion and the
original-AP distinguishability test specify that missing obligation without
claiming a new bare two-K4 existence result.
