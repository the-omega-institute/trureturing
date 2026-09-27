[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="coupled-first-root-profiles-and-an-exceptional-five-prime-block"></a>
# A coupled first-root fee for the exceptional five-prime block

A block with parent prime 3 and child primes \(J=\{5,7,11,13\}\) has
whole-parent-fibre blocker measure strictly below \(15/32\), even after
allowing every strict descendant expense permitted by the
[four-vertex-block induction](06c-four-vertex-blocks-and-cycle-breaking-vertices.md#four-vertex-blocks-with-a-common-descendant-budget).
The fee is smaller than
\[
 f(5)+f(7)+f(11)+f(13)=\frac{23}{48}.
 \tag{KR1}
\]
All original residue classes and arbitrary finite prime-power heights are
retained, including the original five-factor classes. The result uses a
shared allocation of the original exponent-one labels among the three
parent roots, and a conditional Shearer bound under one actual child law.
It does not require a small triple intersection of three arbitrary colored
child unions.

Consequently, a finite distinct odd AP family is noncovering whenever every
nontrivial block of its original prime-interaction graph is an edge, a simple
cycle, or a four-vertex block, except possibly for one block on exactly
\(\{3,5,7,11,13\}\). Arbitrarily many of the established blocks may occur
below the exceptional block or elsewhere. For the exceptional component,
more than \(3/128\) of the original full root-3 coordinate admits an avoiding
extension.

These are ordinary mathematical statements with an exact rational
certificate, not Lean-certified results. They do not prove unrestricted
Erdős #7, a fee for every five-prime block, or recursive closure under
arbitrary repeated five-prime blocks.

## 1. Actual domains and the descendant budget

Use the original full prime-power coordinates
\(X_p=\mathbb Z/p^{h_p}\mathbb Z\), with uniform law \(H_p\). Root the
exceptional component at prime 3. For each child \(q\in J\), let
\(V_q\subseteq X_q\) be the actual domain admitting an extension through its
strict descendant subtree, including avoidance of all original pure
\(q\)-power classes. Descendant witnesses are not assigned additional
probability weights. Put \(\delta_q=H_q(V_q)\).

The established induction (FB5)–(FB7) uses
\[
 f(5)=\frac7{24},\quad f(7)=\frac18,\quad
 f(11)=\frac1{24},\quad f(13)=\frac1{48},\quad
 F=\frac{187}{384},
\]
\[
 \delta_q\ge1-\frac1{q-1}-c_qe_q,\qquad
 c_5=\frac3{10},\quad c_q=\frac2{q-1}\ (q\ge7),
 \tag{KR2}
\]
where \(e_q\) is the sum of the established prime fees over the actual
strict descendant set of \(q\). Those sets are disjoint and avoid the
entire exceptional block. Thus
\[
 \sum_{q\in J}e_q\le F-\frac{23}{48}=\frac1{128}.
 \tag{KR3}
\]
For the certificate it suffices to enlarge this simplex to the rectangle
\(0\le e_q\le1/128\). This gives
\[
 (\delta_5,\delta_7,\delta_{11},\delta_{13})
 \ge(d_5,d_7,d_{11},d_{13})
 :=\left(\frac{957}{1280},\frac{319}{384},
          \frac{115}{128},\frac{703}{768}\right).
 \tag{KR4}
\]
This is an outer domain for a uniform inequality, not an assertion that
four independent copies of the outside expense can occur together.

Define
\[
 b_q=\frac1{(q-1)d_q},\qquad
 (b_5,b_7,b_{11},b_{13})
 =\left(\frac{320}{957},\frac{64}{319},
         \frac{64}{575},\frac{64}{703}\right),
 \qquad b_S=\prod_{q\in S}b_q.
 \tag{KR5}
\]
Let \(\nu=\bigotimes_{q\in J}H_q(\cdot\mid V_q)\), and let \(R\) avoid
every original internal mixed class supported entirely on \(J\). Once its
positivity is established below, set \(\mu=\nu(\cdot\mid R)\).
This is uniform on the actual complete child-survivor set. It is used to
test existence of a child extension, and is not identified with the
extension-count-weighted marginal of full global Haar survivors.

## 2. A support polynomial and its complete positivity certificate

For every nonempty \(S\subseteq J\), set
\[
 w_S=\begin{cases}0,&|S|=1,\\ b_S,&|S|\ge2.\end{cases}
\]
For \(A\subseteq J\), define
\[
 Z_A(v)=
 \sum_{\substack{\mathcal F\text{ a family of pairwise-disjoint}\\
                 \text{nonempty subsets of }A}}
       (-1)^{|\mathcal F|}\prod_{S\in\mathcal F}v_S,
 \qquad Z_\varnothing=1.
 \tag{KR6}
\]
The empty family contributes one. This is the independence polynomial of
the support-intersection graph, whose vertices are the nonempty supports.
It does not replace an original composite modulus by its prime divisors.
Each vertex will represent the union of actual classes on its complete
support. For \(i\in A\), the recurrence is
\[
 Z_A(v)=Z_{A\setminus\{i\}}(v)
       -\sum_{\substack{S\subseteq A\\i\in S}}
          v_SZ_{A\setminus S}(v).
 \tag{KR7}
\]

For the coefficients (KR5), every nonempty residual coordinate set has
\(Z_A(w+b)>1/8\). Here are all fifteen exact values:

| \(A\) | \(Z_A(w+b)\) |
| --- | ---: |
| \(5\) | \(637/957\) |
| \(7\) | \(255/319\) |
| \(5,7\) | \(121475/305283\) |
| \(11\) | \(511/575\) |
| \(5,11\) | \(94849/183425\) |
| \(7,11\) | \(122113/183425\) |
| \(5,7,11\) | \(43789181/175537725\) |
| \(13\) | \(639/703\) |
| \(5,13\) | \(366083/672771\) |
| \(7,13\) | \(154753/224257\) |
| \(5,7,13\) | \(19779327/71537983\) |
| \(11,13\) | \(318337/404225\) |
| \(5,11,13\) | \(153055229/386843325\) |
| \(7,11,13\) | \(71230847/128947775\) |
| \(5,7,11,13\) | \(5714546433/41134340225\) |

These checks give the whole strict Shearer region needed here, not merely
positivity of its top polynomial. For an independent support family
\(\mathcal I\), deleting its closed neighborhood leaves precisely the
support graph on \(J\setminus\bigcup\mathcal I\). Its Shearer atom is
\[
 \left(\prod_{S\in\mathcal I}v_S\right)
 Z_{J\setminus\bigcup\mathcal I}(v).
 \tag{KR8}
\]
At \(v=w+b\), all these atoms are nonnegative and the empty atom is
positive. Their sum over the independent families disjoint from any
specified vertex set is the avoidance polynomial for that induced set;
in particular every induced avoidance polynomial is strictly positive.

The same conclusion holds when any event weights decrease. Equivalently,
\(\partial Z_A/\partial v_S=-Z_{A\setminus S}\); induction on \(|A|\)
shows positivity and coordinatewise decrease throughout
\(0\le v\le w+b\). The certificate therefore covers \(w+y\) for every
\(0\le y_S\le b_S\). Separate old and new vertices with the same support
are adjacent twins: an independent family can select at most one of them,
so their weights add in every relevant polynomial. Zero old singleton
weights may be omitted.

The external probability theorem is Scott–Sokal,
[arXiv:cond-mat/0309352v2, Theorem 4.1 and conditional inequality (4.3)](https://arxiv.org/html/cond-mat/0309352v2).
Under \(\nu\), groups with disjoint supports depend on disjoint full prime
coordinates. Thus an event has its stated probability bound even after
conditioning on avoidance of any family of nonneighbors, as required by
that theorem. Its strict-region hypothesis is supplied by (KR8).

Write
\[
 Z_0=Z_J(w),\qquad
 L=\sum_{\varnothing\ne S\subseteq J}b_SZ_{J\setminus S}(w),
 \qquad D_0=123403020675.
\]
Exact evaluation gives
\[
 Z_0=\frac{98338810243}{D_0},\qquad
 L=\frac{108435700864}{D_0}.
 \tag{KR9}
\]
The old internal group on support \(S\) has probability at most \(w_S\):
sum its literal cylinder caps over all its original exponent vectors.
Hence \(\nu(R)\ge Z_0>0\), establishing the actual law \(\mu\).

## 3. Cylinder costs and three first-root profiles under the same law

Let \(C\) be a literal child cylinder with support \(S\), and let
\(R_{J\setminus S}\) avoid only the old groups supported outside \(S\).
Independence under \(\nu\) gives
\[
 \mu(C)\le\nu(C)
             \frac{\nu(R_{J\setminus S})}{\nu(R)}
 \le\nu(C)\frac{Z_{J\setminus S}(w)}{Z_0}.
 \tag{KR10}
\]
The second inequality is the conditional Shearer ratio; it is not obtained
by dividing two unrelated lower bounds. For
\(m=\prod_{q\in S}q^{e_q}\), the literal cap is
\[
 \nu(C_m)\le\prod_{q\in S}\frac{q^{-e_q}}{d_q}.
\]
At each fixed original parent exponent \(a\), every child modulus \(m>1\)
occurs at most once among labels \(3^am\), regardless of its parent
residue. Completing the nonnegative finite sums by all positive exponents
in (KR10) therefore yields
\[
 \sum_{\text{original labels }3^am,\ m>1}
       \mu(C_{3^am,\mathrm{child}})\le\frac L{Z_0}.
 \tag{KR11}
\]
Labels at different parent exponents remain separate.

For \(j=0,1,2\), let
\[
 y_{j,S}=
 \sum_{\substack{\text{original labels }3m,\ \operatorname{supp}(m)=S\\
                  \text{parent residue }j\pmod3}}
       \prod_{q\in S}\frac{q^{-v_q(m)}}{d_q}.
\]
Original numerical distinctness implies the shared constraint
\[
 y_{j,S}\ge0,\qquad\sum_{j=0}^2y_{j,S}\le b_S.
 \tag{KR12}
\]
In particular the same label \(3m\) cannot spend its weight in two roots.
Let \(s_j\) be the \(\mu\)-probability that the child point avoids all
original parent-exponent-one classes assigned to root \(j\). Treat these
new support groups and the old internal groups as separate vertices under
the same product law \(\nu\). The conditional Shearer inequality, followed
by the adjacent-twin sum, gives
\[
 s_j\ge\frac{Z_J(w+y_j)}{Z_0}>0.
 \tag{KR13}
\]
All three inequalities concern the same old survivor law \(\mu\).
Neither the events nor their overlaps are replaced by independently
optimized sets or probability laws.

## 4. Charging the actual blocked parent words

Let \(B\subseteq X_3\) consist of the parent words for which this block
has no avoiding child extension within \(\prod_qV_q\). Original pure
3-power classes are excluded from this definition and paid separately.
Set
\[
 \beta_j=H_3(B\cap\{x:x\equiv j\pmod3\}),\qquad
 0\le\beta_j\le\frac13.
\]
If \(x\in B\) is in root \(j\), every child point counted by \(s_j\)
must hit a crossing label with parent exponent at least two: internal
classes and first-exponent crossing classes have already been avoided.
Integrating this pointwise required load over \(H_3\times\mu\), then
using (KR11), proves
\[
 \sum_j\beta_js_j\le\frac L{Z_0}\sum_{a\ge2}3^{-a}
                  =\frac L{6Z_0}.
\]
Consequently
\[
 \boxed{\sum_{j=0}^2\beta_j Z_J(w+y_j)\le\frac L6,
 \quad0\le\beta_j\le\frac13,
 \quad\sum_jy_{j,S}\le b_S.}
 \tag{KR14}
\]
The finite original parent heights were enlarged only in a convergent
upper-bound sum. All crossing supports, including all four-child supports,
are included in (KR11) and (KR14).

## 5. Exact two-root optimization

Suppose \(\sum_j\beta_j\ge15/32\). For fixed positive root costs, the
cheapest allocation fills a cheapest root to \(1/3\), then puts
\(15/32-1/3=13/96\) in a second cheapest root. Therefore the left side
of (KR14) is at least
\[
 \frac1{96}\left(32Z_J(w+y_j)+13Z_J(w+y_k)\right)
\]
for an ordered pair of roots. Their allocations satisfy
\(y_j+y_k\le b\). Since every residual polynomial is positive, \(Z_J\)
decreases in each coordinate. Completing the two allocations until their
sum equals \(b\) can only lower this cost. Thus (KR14) would require
\[
 \min_{0\le y_S\le b_S}
 G(y)\le16L,\qquad
 G(y)=32Z_J(w+y)+13Z_J(w+b-y).
 \tag{KR15}
\]

The function \(G\) is affine in each individual coordinate. Its partial
derivative is
\[
 \frac{\partial G}{\partial y_S}
 =-32Z_{J\setminus S}(w+y)
    +13Z_{J\setminus S}(w+b-y).
 \tag{KR16}
\]
For any residual set \(A\), monotonicity gives the uniform
upper bound \(-[32Z_A(w+b)-13Z_A(w)]\). For a two-coordinate residual,
the bracket is
\[
 19-32(b_i+b_j)-19b_ib_j
 \ge19-32(b_5+b_7)-19b_5b_7
 =\frac{61587}{101761}>0.
\]
For a one-coordinate residual it is at least
\(19-32b_5=7943/957>0\), and for the empty residual it is 19. Hence
all mixed supports must be assigned entirely to the first root in a
minimum. The singleton supports 5 and 7 have respective positive brackets
\[
 \frac{691510957}{128947775},\qquad
 \frac{92352173}{128947775},
\]
so they are forced there as well. Only singleton supports 11 and 13
remain. Separate affinity puts each of these two coordinates at an
endpoint. The four exact cases are:

| Extra singleton supports assigned to the first root | \(D_0[G-16L]\) |
| --- | ---: |
| None | \(51066292103\) |
| \(11\) | \(55247672775\) |
| \(13\) | \(56761234887\) |
| \(11,13\) | \(92029776903\) |

In particular
\[
 \min G=\frac{1786037505927}{D_0}
        >\frac{1734971213824}{D_0}=16L.
 \tag{KR17}
\]
This contradicts (KR15) and proves
\[
 \boxed{H_3(B)<\frac{15}{32}<\frac{23}{48}.}
 \tag{KR18}
\]
The same polynomial inequality is also checked at all \(2^{15}=32768\)
box vertices. Each vertex is evaluated both by the integer version of
(KR7) and by direct enumeration of the 52 pairwise-disjoint support
families in (KR6); both methods give (KR17). The finite calculation
certifies a multiaffine inequality for all allocations in the continuous
box, and places no bound on the AP heights.

## 6. The exceptional-block recursion and original-Haar transport

All strict descendants of the exceptional block belong to the already
established edge/cycle/four-vertex class, so (KR2) applies without assuming
a five-prime descendant theorem. Other child blocks attached to the root 3
cannot reuse its four exceptional child primes. Their assigned fees total
at most \(1/128\). The original pure 3-power classes have total Haar
measure at most \(1/2\). The exact block-cut extension recursion therefore
gives
\[
 H_3(V_3)>1-\frac12-\frac{15}{32}-\frac1{128}
          =\frac3{128}>0.
 \tag{KR19}
\]
The recursion chooses simultaneous witnesses on the disjoint private sides
of the blocks at one fixed original root word. It does not multiply
marginal extension proportions.

For the exceptional connected component, let
\(Q_{\mathrm{off}}=\prod_{p\ne3}p^{h_p}\). Every root word in \(V_3\)
has at least one avoiding full extension, so its conditional original-Haar
extension probability is at least \(1/Q_{\mathrm{off}}\). Thus the full
uncovered Haar proportion \(U\) in that component satisfies
\[
 U\ge\frac{H_3(V_3)}{Q_{\mathrm{off}}}
   >\frac3{128Q_{\mathrm{off}}}>0.
 \tag{KR20}
\]
Other components are noncovering by the established theorem and combine by
CRT. This proves the stated exceptional-block noncoverage result. The
quantity \(3/128\) is a root-coordinate extension reserve, not the full
uncovered density.

## 7. Certificate and remaining scope

The standard-library Python program
[k5_coupled_first_root_certificate.py](../frontier/cover-geometry/k5_coupled_first_root_certificate.py)
and its
[exact rational data](../frontier/cover-geometry/k5_coupled_first_root_certificate.json)
contain the domain calculation, all fifteen residual checks, both support
polynomial algorithms, the derivative margins, and the four-case and
32768-vertex inequalities. Run from the repository root with assertions
enabled:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/k5_coupled_first_root_certificate.py
```

The default output is the JSON file beside the program; `--output PATH`
selects another destination. Running with `-O` is rejected. The program
checks rational arithmetic and the finite polynomial certificate; it does
not verify the external measure-theoretic theorem or elaborate Lean.

### Finite controls on complete original parent fibres

The [actual-AP control program](../frontier/cover-geometry/k5_coupled_first_root_ap_controls.py)
and its [full data](../frontier/cover-geometry/k5_coupled_first_root_ap_controls.json)
check two complete families at \(Q_H=3^H\cdot5005\), for \(H=2,4\).
Every nonunit divisor occurs once. Old child labels use \(0\bmod d\);
parent-pure labels use \(1\bmod3^a\). The label \(3^a5\) has the CRT
conditions \(x\equiv0\pmod{3^a}\), \(x\equiv a\pmod5\), while all
other crossing labels use residue zero. These prescriptions retain all
original four-child and five-prime supports.

The complete old child-survivor set \(S\) has 2880 points modulo 5005,
and every crossing event uses its same uniform law. For a complete parent
word \(r\), put
\[
 j_H(r)=\max\{a\in\{0,\ldots,H\}:r\equiv0\pmod{3^a}\}.
\]
The block-only child fibre, excluding parent-pure labels, has exactly
\(720(4-j_H(r))\) points for every parent word. The full-family fibre
multiplies this count by \(\mathbf1_{r\not\equiv1\pmod3}\). Thus the
block blocker is defined on the entire original parent coordinate before
any conditioning on the parent-pure allowed domain.

| Quantity | \(H=2\) | \(H=4\) |
| --- | ---: | ---: |
| Original labels | 47 | 79 |
| Original period | 45045 | 405405 |
| Block-only blocked parent words | None | \(0\bmod81\) |
| Original-parent-Haar blocker mass | 0 | \(1/81\) |
| Full-family uncovered residues | 14400 | 126720 |
| Sum of crossing-row masses under \(H_3\times\mu\) | \(1/9\) | \(10/81\) |

The last row equals \(\tfrac14\sum_{a=1}^H3^{-a}\), and is distinct
from the measure of completely blocked parent words. A direct congruence
sieve over every original integer and a separate original-label child
sieve for every complete parent word agree pointwise, for both the full
family and the block-only family. The data retain each literal label,
residue, parent-fibre count and Haar normalization. Reproduce with

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/k5_coupled_first_root_ap_controls.py --output /tmp/k5-coupled-first-root-ap-controls.json
```

These finite controls verify the fibre and weighting interfaces; the
all-height fee follows from (KR10)–(KR18). The retained five-prime labels
have zero mass on this old child-survivor set, so the controls do not assert
effective high-support interaction or supply a covering counterexample.

### Remaining uniform obligation

The reusable information is the common first-root budget (KR12) together
with the coupled saturation inequality (KR14). Its proof also works for a
parent prime \(p\) once the corresponding support region and cylinder
bounds are established: the deeper geometric factor becomes
\(1/[p(p-1)]\). Closing unrestricted recursion still requires suitable
fees for the other child tuples, parent orientations and larger blocks,
with their actual descendant domains. Those uniform estimates are not
proved here.

The [aggregate prefix countermodel](19-five-prime-parent-envelopes-and-the-cofactor-allocation-barrier.md)
and [original-AP three-color control](20-original-ap-three-color-intersections-can-exceed-the-residual-threshold.md)
show why two weaker summaries do not supply this conclusion. Neither
contradicts (KR14), which retains the nonlinear first-root profiles and
their shared allocation of the same original labels.
