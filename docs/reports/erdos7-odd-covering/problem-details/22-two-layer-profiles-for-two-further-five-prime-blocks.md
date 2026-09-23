[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="two-layer-profiles-for-two-further-five-prime-blocks"></a>
# Two parent layers give fees for two further five-prime blocks

With parent prime 3, each of the child tuples
\[
 J_5=\{5,11,13,17\},\qquad J_7=\{7,11,13,17\}
\]
has whole-parent-fibre blocker measure strictly less than the sum of its
established child fees:
\[
 H_3(B)<M_5=\frac{275}{768},\qquad
 H_3(B)<M_7=\frac{49}{256},
 \tag{TL1}
\]
respectively. The bounds allow every strict descendant expense permitted
by the [four-vertex-block induction](06c-four-vertex-blocks-and-cycle-breaking-vertices.md#four-vertex-blocks-with-a-common-descendant-budget).
They retain arbitrary finite prime-power heights, all original residues,
and every original support, including four-child and five-prime labels.

Consequently, a finite distinct odd AP family is noncovering if every
nontrivial block of its original prime-interaction graph is an edge, a
simple cycle, or a four-vertex block, except possibly for one block on
exactly \(\{3\}\cup J_5\) or \(\{3\}\cup J_7\). That component is rooted
at 3. Its root-coordinate extension proportion is greater than \(5/384\).
Arbitrarily many of the established blocks are allowed as descendants and
elsewhere; repeated exceptional five-prime blocks are not covered.

These are ordinary mathematical results with an exact rational
certificate, not Lean-certified results. The new estimate uses a
conditional union bound after the first parent layer. It requires
positivity throughout \(w\le v\le w+b\), but does not require positivity
at \(w+2b\). It does not establish unrestricted Erdős #7.

## 1. Actual child laws and the two descendant rectangles

Use the original full prime-power coordinates
\(X_p=\mathbb Z/p^{h_p}\mathbb Z\), with uniform Haar law \(H_p\).
If \(h_3<2\), replace its coordinate by
\(\mathbb Z/3^{\max(h_3,2)}\mathbb Z\) and pull back every original class
under the reduction map. This changes no original label and preserves
all Haar proportions. Thus each two-digit parent prefix has Haar measure
\(1/9\), without a lower-height exception.

For each \(q\in J\), let \(V_q\) be the actual domain of words admitting
an avoiding extension through its strict descendant subtree, including
avoidance of all original pure \(q\)-power classes. The established fees
and descendant estimates are
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad
 f(11)=\frac1{24},\quad f(13)=\frac1{48},\quad f(17)=\frac1{256},
 \qquad F=\frac{187}{384},
\]
\[
 H_q(V_q)\ge1-\frac1{q-1}-c_qe_q,
 \qquad c_5=\frac3{10},\quad c_q=\frac2{q-1}\quad(q\ge7).
 \tag{TL2}
\]
Here \(e_q\) is the sum of the established fees of the actual strict
descendant primes. These descendant sets are disjoint and avoid the
exceptional block, so \(\sum_qe_q\le E:=F-M\), where \(M=\sum_{q\in J}f(q)\).
Enlarge this shared simplex to the rectangle \(0\le e_q\le E\), and set
\[
 d_q=1-\frac1{q-1}-c_qE,\qquad b_q=\frac1{(q-1)d_q},
 \qquad b_S=\prod_{q\in S}b_q.
\]
In increasing child-prime order the constants are:

| Child tuple | \(E\) | \((b_q)\) |
| --- | ---: | --- |
| \(5,11,13,17\) | \(33/256\) | \((640/1821,128/1119,128/1375,128/1887)\) |
| \(7,11,13,17\) | \(227/768\) | \((384/1693,384/3229,384/3997,384/5533)\) |

This is an outer domain for a uniform inequality. It does not assert
simultaneous realization of four independent copies of the descendant
expense. All four \(d_q\) in each row are positive.

Put \(\nu=\bigotimes_{q\in J}H_q(\cdot\mid V_q)\). Let \(R\) be the
event avoiding every original internal mixed child class, and put
\(\mu=\nu(\cdot\mid R)\) after verifying positivity below. As in
[the first-layer construction](21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md),
this is one actual complete child-survivor law. It is not the marginal
obtained by weighting child words by their numbers of global extensions.

For every nonempty support set \(S\subseteq J\), define
\[
 w_S=\begin{cases}0,&|S|=1,\\b_S,&|S|\ge2,\end{cases}
 \qquad
 Z_A(v)=\sum_{\substack{\mathcal F\text{ pairwise-disjoint}\\
                        \text{nonempty supports in }A}}
             (-1)^{|\mathcal F|}\prod_{S\in\mathcal F}v_S.
 \tag{TL3}
\]
The empty family contributes one. Set
\[
 Z_0=Z_J(w),\qquad L=\sum_{S\ne\varnothing}b_SZ_{J\setminus S}(w).
\]
The exact certificate checks all fifteen nonempty residuals at \(w+b\).
Their minima are positive:
\[
 \min_{A\ne\varnothing} Z_A(w+b)=
 \begin{cases}
 1489693258883/5287064767875,&J=J_5,\\
 50716879766737/120898196300497,&J=J_7.
 \end{cases}
 \tag{TL4}
\]
The support-polynomial argument (KR7)–(KR8) then gives positivity of all
induced Shearer polynomials, and coordinatewise decrease, throughout
\(0\le v\le w+b\). In particular \(\nu(R)\ge Z_0>0\).
The probability input is Scott–Sokal,
[Theorem 4.1 and conditional inequality (4.3)](https://arxiv.org/html/cond-mat/0309352v2),
applied under the actual product law \(\nu\).

## 2. A shared second-layer inequality

For a first parent digit \(j\in\{0,1,2\}\), let \(A_j\) be the union
of the original child cylinders whose parent exponent is one and parent
residue is \(j\). On each nonempty support \(S\), let \(y_{j,S}\) be
the sum of their literal cylinder caps under \(\nu\). Distinctness of the
original moduli gives
\[
 y_{j,S}\ge0,\qquad \sum_jy_{j,S}\le b_S.
 \tag{TL5}
\]
Write
\[
 R_j=R\setminus A_j,\qquad
 \Phi_j=Z_J(w+y_j),\qquad
 \Phi_{j,S}=Z_{J\setminus S}(w+y_j).
\]
First-layer conditional Shearer gives
\[
 \mu(R_j)\ge\frac{\Phi_j}{Z_0}>0,
 \qquad
 \nu(C\mid R_j)\le\nu(C)\frac{\Phi_{j,S}}{\Phi_j}
 \tag{TL6}
\]
for every actual cylinder \(C\) with support \(S\). The latter inequality
follows by separating the groups disjoint from \(S\) under \(\nu\) and
using the conditional Shearer ratio, exactly as in (KR10).

For a second digit \(k\in\{0,1,2\}\), let \(E_{jk}\) be the union of
the original exponent-two crossing cylinders assigned to the prefix
\((j,k)\). Let their literal support caps be \(z_{jk,S}\). The original
labels give another shared budget:
\[
 z_{jk,S}\ge0,\qquad \sum_{j,k}z_{jk,S}\le b_S.
 \tag{TL7}
\]
The two budget systems are separate. A cofactor may recur at different
parent exponents, since the original moduli are then different; within
one fixed parent exponent each original cofactor occurs at most once.
No support is allocated afresh to each sibling.

A union bound under the correctly matched law \(\nu(\cdot\mid R_j)\)
gives
\[
 \nu(E_{jk}\mid R_j)
 \le \frac{\sum_Sz_{jk,S}\Phi_{j,S}}{\Phi_j}.
\]
When the resulting survival bracket is nonnegative, multiply this bound
by the lower bound in (TL6). When it is negative, use nonnegativity of
probability instead. Together these cases give
\[
 \mu(R_j\setminus E_{jk})
 \ge\frac{[\Phi_j-\sum_Sz_{jk,S}\Phi_{j,S}]_+}{Z_0}.
 \tag{TL8}
\]
This argument does not condition on a presumed positive second-layer
survivor set, and makes no assumption about \(Z(w+y_j+z_{jk})\).

Let \(B\) be the set of fully blocked parent words for this block alone,
before imposing any parent-pure classes. Put
\(\beta_{jk}=H_3(B\cap\text{prefix}(j,k))\), so
\(0\le\beta_{jk}\le1/9\). For a blocked word, every child survivor of
its first two layers must be covered by an original label with parent
exponent \(a\ge3\). Each such exponent has total child cylinder load at
most \(L/Z_0\) under the same old law \(\mu\). Integrating over the one
product law \(H_3\times\mu\) therefore yields
\[
 \sum_{j,k}\beta_{jk}
       [\Phi_j-\sum_Sz_{jk,S}\Phi_{j,S}]_+
 \le L\sum_{a\ge3}3^{-a}=\frac L{18}.
 \tag{TL9}
\]
The actual finite set of depths is bounded by this infinite geometric
sum. All original depths and supports remain present.

Dropping positive parts gives a weaker necessary inequality. Define
\[
 \alpha_j=\sum_k\beta_{jk},\qquad m_j=\max_k\beta_{jk},
\]
and spend each second-layer support budget at its largest possible cost.
Then (TL7)–(TL9) imply
\[
 G(y,\beta):=\sum_j\alpha_j\Phi_j
      -\sum_Sb_S\max_j(m_j\Phi_{j,S})\le\frac L{18}.
 \tag{TL10}
\]
The following sections prove the opposite strict inequality whenever
\(\sum_{j,k}\beta_{jk}=M\). If the actual blocker has mass at least
\(M\), its nine weights may be scaled down to this total; (TL9) still
holds. No realizable parent subset with exactly that rational mass is
needed.

For fixed \(y\), \(G\) is concave in the nine \(\beta\)'s: its first
term is linear and each subtracted maximum is a maximum of linear forms.
Its minimum on
\(0\le\beta_{jk}\le1/9,\ \sum\beta_{jk}=M\)
is therefore attained at an extreme point. Such a point has full slots
of mass \(1/9\), at most one partial slot, and zero elsewhere.
This reduction retains the exact shared allocations in (TL5), including
unused support budgets.

## 3. A tangent lower bound for most occupancy types

Throughout the certified box,
\[
 \frac{\partial Z_J}{\partial v_S}=-Z_{J\setminus S},
 \qquad
 \frac{\partial^2 Z_J}{\partial v_S\partial v_T}=
 \begin{cases}Z_{J\setminus(S\cup T)},&S\cap T=\varnothing,\\
 0,&S\cap T\ne\varnothing.
 \end{cases}
\]
All displayed residuals are positive. Integrating the first derivatives
from \(w\) along a nonnegative direction gives
\[
 Z_J(w+y)\ge Z_0-\sum_Sy_SZ_{J\setminus S}(w),
 \qquad \Phi_{j,S}\le Z_{J\setminus S}(w).
\]
Consequently, using the actual common budget (TL5),
\[
 G(y,\beta)-\frac L{18}
 \ge MZ_0-
       \left(\max_j\alpha_j+\max_jm_j+\frac1{18}\right)L.
 \tag{TL11}
\]
The original unsaturated budget inequality is sufficient here.

## 4. The tuple \(5,11,13,17\)

Here \(M=275/768=3/9+19/768\). Up to permutation of the three first
roots, the extreme weights have the following five forms. The full-slot
count at any root is at most three.

| Full-slot counts | Partial-slot root | Certified margin \(G-L/18\) |
| --- | --- | ---: |
| \((3,0,0)\) | Second | \(19521746462501/812093148345600\) |
| \((2,1,0)\) | First | \(129355064916523/12181397225184000\) |
| \((2,1,0)\) | Second | \(348488383335211/12181397225184000\) |
| \((2,1,0)\) | Third | \(348488383335211/12181397225184000\) |
| \((1,1,1)\) | First | \(1113532775709227/12181397225184000\) |

The last four rows are lower bounds from (TL11). For the first row the
listed margin is the exact minimum of the relaxed expression (TL10),
proved next. Every margin is strictly positive.

For this remaining row, use roots \(A,B\), with the third root inactive.
After scaling by 2304,
\[
 2304\alpha=(768,57,0),\qquad2304m=(256,57,0).
\]
For every nonempty support \(S\), the certificate verifies
\[
 256Z_{J\setminus S}(w+b)-57Z_{J\setminus S}(w)>0.
 \tag{TL12}
\]
The smallest margin is \(118714918987/2801836125\). Monotonicity shows
that the first root realizes the maximum in every term of (TL10), for
all permitted allocations. Thus
\[
 2304(G-L/18)=768Z_J(w+y_A)+57Z_J(w+y_B)
       -256\sum_Sb_SZ_{J\setminus S}(w+y_A)-128L.
 \tag{TL13}
\]
Unused budget, including allocations to the inactive third root, can be
assigned to root \(B\). This only decreases (TL13), because it changes
only its positive \(57Z_J\) term and the maximum remains at root \(A\).
Hence it suffices to minimize with \(y_B=b-y_A\).

The derivative of (TL13) with respect to \(y_{A,S}\) is at most
\[
 -768Z_{J\setminus S}(w+b)+57Z_{J\setminus S}(w)
 +256\sum_{T\cap S=\varnothing}b_T
                 Z_{J\setminus(S\cup T)}(w).
 \tag{TL14}
\]
All fifteen bounds are strictly negative; their maximum is
\(-64062535193/933945375\). Therefore the minimum occurs at
\(y_A=b,\ y_B=0\). Exact evaluation gives the first row of the table,
contradicting (TL10) at total blocker mass \(M\). This proves the first
bound in (TL1).

## 5. The tuple \(7,11,13,17\)

Here \(M=49/256=1/9+185/2304\). An extreme point has one full slot and
one partial slot. If they have different first roots, (TL11) gives
\[
 G-L/18\ge MZ_0-\frac5{18}L
 =\frac{906202683555331}{92849814758781696}>0.
 \tag{TL15}
\]
If they share a first root, only that root is active and
\[
 G=MZ_J(w+y)-\frac19\sum_Sb_SZ_{J\setminus S}(w+y).
\]
Every support derivative is at most
\[
 -MZ_{J\setminus S}(w+b)
 +\frac19\sum_{T\cap S=\varnothing}b_T
                  Z_{J\setminus(S\cup T)}(w)<0.
 \tag{TL16}
\]
The largest upper bound is \(-232733960757/5593699304704\).
Thus the minimum on \(0\le y\le b\), retaining unused budget, occurs at
\(y=b\). Its exact margin is
\[
 G-L/18\ge\frac{13175440576419}{2813630750266112}>0.
 \tag{TL17}
\]
Both occupancy types contradict (TL10). This proves the second bound in
(TL1).

## 6. One exceptional block and original-Haar transport

The strict descendants in this result are all from the established
edge/cycle/four-vertex class. No five-prime fee is assumed in deriving
(TL2). Root the exceptional component at 3. All other child blocks at 3
have total assigned fees at most \(F-M\), while the original pure
3-power classes have Haar measure at most \(1/2\). The exact block-cut
extension recursion gives
\[
 H_3(V_3)>1-\frac12-M-(F-M)
         =\frac12-F=\frac5{384}>0.
 \tag{TL18}
\]
At one fixed parent word, witnesses on the disjoint private sides of the
blocks combine. This argument does not multiply marginal extension
proportions. With \(Q_{\mathrm{off}}=\prod_{p\ne3}p^{h_p}\) over this
component, each extendable root word has at least one original avoiding
extension, so its full uncovered Haar proportion is
\[
 U>\frac5{384Q_{\mathrm{off}}}>0.
 \tag{TL19}
\]
The reserve \(5/384\) concerns the root coordinate, not the full uncovered
density. Other connected components combine by CRT.

## 7. Reproducible certificate and remaining scope

The standard-library program
[k5_two_layer_profile_certificate.py](../frontier/cover-geometry/k5_two_layer_profile_certificate.py)
and its [exact data](../frontier/cover-geometry/k5_two_layer_profile_certificate.json)
record both descendant rectangles, all old and upper-box residuals, every
support dominance and derivative bound, and all occupancy margins.
Support polynomials are evaluated both by the coordinate recurrence and
by directly summing the 52 pairwise-disjoint support families; the two
methods agree on every residual used in the certificate.

Run with Python 3.10 or later and assertions enabled:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/k5_two_layer_profile_certificate.py
```

The default JSON destination is beside the program; `--output PATH`
selects another destination. Optimized `-O` execution is rejected. The
program checks exact arithmetic, not the measure-theoretic source theorem
or a Lean proof. Independently, an exact integer check of all
\(3^{15}=14,348,907\) allocations for the first occupancy type of
\(J_5\), including unused support budgets, found the same minimum at
\(y_A=b,y_B=0\). That enumeration is not needed by the retained analytic
certificate.

The reusable addition is (TL8)–(TL10): the first-layer conditional law
bounds a second-layer union while the final charging remains under the
same old law. Suitable uniform fees are still missing for other child
tuples, parent orientations, arbitrary repeated exceptional blocks and
larger blocks. The two explicit successes do not settle those obligations
or unrestricted odd covering.
