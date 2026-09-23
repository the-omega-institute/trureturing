[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](18-five-prime-cores-with-tree-and-cactus-attachments.md)

<a id="five-prime-parent-envelopes-and-the-cofactor-allocation-barrier"></a>
# Five-prime parent envelopes and the cofactor-allocation barrier

For parent prime 3 and child primes \(P=\{5,7,11,13\}\), **with no
descendant attachments**, the actual complete child-survivor law admits a
coupled bound for every fixed-parent-prefix union. This improves the
available estimates, but the resulting scalar information still permits a
common-law countermodel whose blocked-parent mass exceeds the proposed fee
\(23/48\).

These are ordinary mathematical results with exact rational certificates.
The countermodel refutes the stated aggregate inference; it is not an
original AP family, an AP counterexample, or a proof that the actual K5 fee
is impossible. No Lean certification or extension of the
[five-core noncoverage theorem](18-five-prime-cores-with-tree-and-cactus-attachments.md)
is asserted.

## 1. One original child system and law

Retain every original finite prime-power coordinate
\[
 X_q=\mathbb Z/q^{h_q}\mathbb Z\qquad(q\in P)
\]
with uniform Haar law \(H_q\). Let \(V_q\subseteq X_q\) avoid all original
pure \(q\)-power classes, and put
\[
 \delta_q=H_q(V_q)\ge d_q:=\frac{q-2}{q-1},\qquad
 \nu=\bigotimes_{q\in P}H_q(\cdot\mid V_q).
\]
Let \(S\subseteq\prod_qV_q\) also avoid every original mixed class supported
entirely on \(P\), and define
\[
 s=\nu(S),\qquad \mu=\nu(\cdot\mid S).
\]
The [P3–P5 cylinder-profile induction](10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md#a-four-prime-head-and-a-restricted-noncoverage-theorem)
gives
\[
 s\ge s_0:=\frac{79}{99},\qquad R_0=\frac{1301}{1185}.
 \tag{KE1}
\]
Here \(R_0\) is the exact value of the numerical profile envelope. It
upper-bounds the sum of maximal cylinder probabilities over all original
nonunit child divisors, uniformly in the original finite heights. It is
not asserted to equal that sum for every actual family. All profile caps
and survivor bounds concern this same complete child system and law.

Fix an original parent exponent \(a\ge1\) and one prefix modulo \(3^a\).
Let \(N\) be the union of the child projections of original classes with
modulus \(3^a d\), \(d>1\), whose parent prefix matches. At this exponent
each child modulus \(d\) contributes at most one original class. Child
supports of sizes one through four are retained; the four-child support
includes the original five-prime labels. The parent-pure label \(d=1\)
is treated separately.

## 2. Coupled bounds for a single parent layer

Let \(W_q\subseteq V_q\) additionally avoid the newly projected pure
\(q\)-power classes. Their total full-coordinate Haar mass is at most
\(1/(q-1)\), so
\[
 \frac{H_q(W_q)}{H_q(V_q)}
 \ge1-\frac{1}{(q-1)\delta_q}
 \ge\frac{q-3}{q-2},\qquad
 H_q(W_q)\ge\frac{q-3}{q-1}.
 \tag{KE2}
\]
The old and newly projected mixed classes together have multiplicity at
most two for each child modulus. The same P3–P5 induction, with unary
lower bounds \((q-3)/(q-1)\) and mixed deletion factor two, gives a
survivor-fraction lower bound \(21/64\) on \(\prod_qW_q\). Its numerical
envelope is \(3359/1050\). Consequently, in the **same old product law**,
\[
 \nu(S\setminus N)
 \ge\frac{21}{64}\prod_{q\in P}\frac{H_q(W_q)}{H_q(V_q)}
 \ge\frac{21}{64}\frac{128}{297}
 =:C=\frac{14}{99}.
 \tag{KE3}
\]
The ratios in (KE2) retain their common source; they are not ratios of
independently optimized domain bounds.

There is also a raw union bound in that same \(\nu\)-law. Put
\(b_q=1/(q-2)\). The new pure-coordinate unions have probabilities at
most \(b_q\) and are independent under \(\nu\). The mixed classes have
total probability at most \(e_2(b)+e_3(b)+e_4(b)\), by original distinctness
and complete geometric sums over the exponents. Thus
\[
 \nu(N)\le U:=1-\prod_q(1-b_q)+e_2(b)+e_3(b)+e_4(b)
          =e_1(b)+2e_3(b)=\frac{1148}{1485}.
 \tag{KE4}
\]
No fourth-order label is omitted: its cancellation in the final algebraic
expression combines the pure-coordinate union formula with the mixed-class
bound.

Since \(\mu(N)=\nu(S\cap N)/s\), equations (KE3)–(KE4) imply
\[
 \boxed{\mu(N)\le\beta(s):=
       \min\left(\frac{U}{s},1-\frac{C}{s}\right),
       \qquad s\in[79/99,1].}
 \tag{KE5}
\]
The branches meet at \(s=U+C=1358/1485\), so
\[
 \beta(s)\le\frac{U}{U+C}=\frac{82}{97},\qquad
 \beta(79/99)=\frac{65}{79}.
 \tag{KE6}
\]

## 3. Retaining the same survivor fraction in the whole envelope

Let \(c(T)\) be the P3–P5 profile coefficients for the same \(\mu\), with
\(c(\varnothing)=1\). For nonempty \(T\subseteq P\), put
\[
 r_T:=\prod_{q\in T}\frac{q-1}{q-2},\qquad
 c_s(T):=\min\left(c(T),\frac{r_T}{s}\right),
 \qquad c_s(\varnothing)=1.
\]
Indeed, conditioning the original product law bounds any specified original
positive prefix exponents on \(T\) by
\[
 \mu(\text{prefixes on }T)
 \le\frac1s\prod_{q\in T}\frac{1}{\delta_q q^{e_q}}
 \le\frac{r_T/s}{\prod_{q\in T}q^{e_q}}.
\]
Taking the minimum with the existing profile is valid because both bounds
apply to the same measure.

The original child profile has zero tail cutoffs:
\(c(T\cup\{q\})\le q c(T)\). The raw coefficients satisfy the same
extension inequality, since \(r_{T\cup\{q\}}=((q-1)/(q-2))r_T\).
Taking minima preserves it for nonempty \(T\). For the empty support,
\(c_s(\{q\})\le c(\{q\})\le q\). Therefore every positive exponent
coordinate can be included in a minimizing support, giving the exact
infinite profile envelope
\[
 \boxed{R(s)=\sum_{\varnothing\ne T\subseteq P}
      \left(\prod_{q\in T}\frac1{q-1}\right)
      \min\left(c(T),\frac{r_T}{s}\right)
      \le\frac{1301}{1185}.}
 \tag{KE7}
\]
This fifteen-term expression is an all-height geometric sum. It is not a
finite-height AP test. The
[envelope certificate](../frontier/cover-geometry/k5_parent_same_law_envelope.py)
and its [exact data](../frontier/cover-geometry/k5_parent_same_law_envelope.json)
contain both profile inductions, all fifteen support coefficients, their
switch points, and the formula \(A+B/s\) on every resulting interval.

For a fixed parent exponent \(a\), write \(N_{a,w}\) for its child union
at prefix \(w\). Each original child cofactor appears at most once across
those prefixes. Summing the union bounds therefore gives
\[
 \sum_{w\bmod3^a}\mu(N_{a,w})
 \le\sum_{\text{original }d>1}\mu(\text{its child cylinder})
 \le R(s).
\]
Together with (KE5), this supplies the aggregate budgets used below while
forgetting which cofactor supplies each individual event.

## 4. A common-law countermodel at the coupled endpoint

The proposed charge for these four children under the
[four-vertex-block fee schedule](06c-four-vertex-blocks-and-cycle-breaking-vertices.md#four-vertex-blocks-with-a-common-descendant-budget)
is
\[
 F=f(5)+f(7)+f(11)+f(13)
   =\frac7{24}+\frac18+\frac1{24}+\frac1{48}
   =\frac{23}{48}.
 \tag{KE8}
\]
This is the four-vertex-block schedule, not the older cactus fees. The
following countermodel concerns the proposed inference from \(R(s)\) and
\(\beta(s)\) to this charge; it does not have an asserted original AP
realization.

Take the allowed scalar endpoint
\[
 s=\frac{79}{99},\qquad R=\frac{1301}{1185},\qquad
 \beta=\frac{65}{79}=\frac{975}{1185},\qquad
 u=R-\beta=\frac{326}{1185}.
\]
Use one uniformly weighted child set \(Y\) of size 1185 and nested actual
events \(U_0\subset A\subset Y\), with atom counts
\[
 |U_0|=326,\qquad |A\setminus U_0|=649,\qquad
 |Y\setminus A|=210.
 \tag{KE9}
\]
Thus \(\mu(A)=\beta\) and \(\mu(U_0)=u\). Every parent prefix below
uses this same finite probability law.

Fix parent height \(H\ge2\), and use \(\mathbb Z/3^H\mathbb Z\) with
uniform probability. Write ternary words with the least significant digit
first. For each depth \(a\), define
\[
 p_a=1^{a-1}0,\qquad b_a=1^{a-1}2.
\]
Use \(p_a\) as the one pure-parent forbidden prefix at depth \(a\).
The \(p_a\)-cylinders are pairwise disjoint, the \(b_a\)-cylinders are
pairwise disjoint, and the two collections do not intersect.

Let \(E_{a,w}\) be the child event at parent prefix \(w\) of length \(a\).
At depth one set
\[
 E_{1,2}=A,\qquad E_{1,1}=U_0.
\]
At every later depth set
\[
 E_{a,b_a}=A\setminus U_0,\qquad
 E_{a,b_{a-1}j}=Y\setminus A\quad(j\in\{0,1,2\}),
 \tag{KE10}
\]
and set all other events empty. The four prefixes in (KE10) are distinct.

Every individual event has mass at most \(\beta\). The total event mass
at depth one is \(\beta+u=R\), and at every subsequent depth it is
\[
 (\beta-u)+3(1-\beta)=3-\beta-R
       =\frac{1279}{1185}<R,
 \tag{KE11}
\]
with slack \(22/1185\). Hence all aggregate constraints hold:
\[
 \mu(E_{a,w})\le\beta,\qquad
 \sum_{|w|=a}\mu(E_{a,w})\le R.
 \tag{KE12}
\]
They are also consistent with the additional scalar couplings:
\(s(1-\beta)=14/99=C\) and \(s\beta=65/99\le U\).

A parent word is fully blocked when the union of its active child events
is \(Y\). A word with prefix \(b_1\) sees \(A\) and then its complement.
For \(j\ge2\), a word with prefix \(b_j\) sees \(U_0\) at depth one,
\(A\setminus U_0\) at depth \(j\), and \(Y\setminus A\) at depth
\(j+1\). Every other parent word sees a proper subset of \(Y\): a word
in a pure cylinder sees at most \(U_0\), a word with prefix \(b_H\) sees
only \(A\), and the all-ones word sees only \(U_0\). Consequently the
fully blocked set is exactly
\[
 B_H=\bigsqcup_{j=1}^{H-1}\operatorname{cyl}(b_j),\qquad
 H_3(B_H)=\frac{1-3^{-(H-1)}}2.
 \tag{KE13}
\]
It is disjoint from every specified pure-parent exclusion.

At height four, the literal pure classes are
\[
 0\bmod3,\quad1\bmod9,\quad4\bmod27,\quad13\bmod81,
\]
and the blocked classes are
\[
 2\bmod3,\quad7\bmod9,\quad22\bmod27.
\]
Thus 39 of the 81 parent words are blocked outside all pure classes, and
\[
 H_3(B_4)=\frac{13}{27}
        =\frac{23}{48}+\frac1{432}>F.
 \tag{KE14}
\]
The [finite prefix verifier](../frontier/cover-geometry/k5_common_law_prefix_barrier.py)
and its [exact data](../frontier/cover-geometry/k5_common_law_prefix_barrier.json)
check all child-event unions, depth budgets, prefix caps, and literal
congruence counts at heights 2, 3, 4, and 8. At height eight the blocked
mass is \(1093/2187\). These finite checks verify the construction; the
general-height identity is (KE13).

The same construction, on three weighted child atoms, works for
\[
 0<\beta<1,\qquad
 \max(R/2,1/2)\le\beta\le R,\qquad \beta\ge3-2R,
 \tag{KE15}
\]
with positive atoms in the strict interior case. The final inequality is
exactly the depth-budget requirement \(3-\beta-R\le R\). For the
present \(R\), its threshold is \(3-2R=953/1185<65/79\).
Since (KE13) tends to \(1/2\), this aggregate information cannot imply
any uniform fee strictly below \(1/2\), even with a common child law and
the stated pure-parent compatibility. The verifier also retains the weaker
cap \(85/99\) as a second exact parameter instance.

## 5. What the coupled envelope excludes

For the construction above put
\[
 g(s)=3-2R(s)-\beta(s).
\]
A positive \(g(s)\) rules out its particular full comb-budget allocation.
It is not asserted to give a general K5 dead-fibre estimate or an AP
noncoverage criterion. The exact piecewise envelope gives
\[
 g(79/99)=-\frac{22}{1185},\qquad
 \min_{s\in[79/99,1]}g(s)=g(79/98)=-\frac{466}{23463},
\]
and its unique zero is \(s_*=8927/10494\). The interval containing this
zero is
\[
 \frac{395}{469}\le s\le\frac{395}{462};
\]
**on this interval** the formulas are
\[
 R(s)=\frac{183}{395}+\frac{29}{55s},\qquad
 g(s)=\frac{424}{395}-\frac{452}{495s}.
 \tag{KE16}
\]
At the smaller minimizer \(79/98\), the values instead are
\(R=326/297\) and \(\beta=6449/7821\); (KE16) does not apply there.
The envelope data give all thirteen breakpoints and the intervening
affine-in-\(1/s\) formulas, including their derivative signs, so the
minimum and unique-zero claims cover the complete interval.

## 6. The missing original-cofactor allocation

Let \(Q_{\rm child}\) be the complete original child period. For an actual
parent exponent \(a\), retain the set of original nonunit child cofactors
\(D_a\subseteq\operatorname{Div}(Q_{\rm child})\setminus\{1\}\),
and maps
\[
 w_a:D_a\longrightarrow\mathbb Z/3^a\mathbb Z,
 \qquad b_{a,d}\in\mathbb Z/d\mathbb Z.
\]
Let \(W\) be the same complete feasible child set obtained from the
original child labels and actual descendant domains, with its uniform law.
The actual prefix events have the form
\[
 E_{a,w}=\{y\in W:\ y\equiv b_{a,d}\pmod d
           \text{ for some }d\in D_a\text{ with }w_a(d)=w\}.
 \tag{KE17}
\]
At a fixed \(a\), each \(d\) is assigned to only one parent prefix because
the original modulus \(3^a d\) appears at most once. Different parent
exponents may reuse \(d\), since they give different original moduli.
All these child cylinders also retain their actual CRT intersections and
their actual masses under the same \(W\)-law.

The countermodel repeatedly places \(Y\setminus A\) in three parent
prefixes at the same exponent without supplying three original cofactor
allocations realizing those events. Neither a common probability law nor
matching total masses supplies those allocations. No original arithmetic
attainability of its scalar endpoint or event configuration is asserted;
no impossibility of such attainability is asserted either.

The arithmetic obligation beyond these aggregate bounds is an upper bound on the parent words
whose union of the actual sets (KE17) is \(W\), retaining the unique
\((a,d)\) assignment and jointly established descendant-expense restrictions.
The estimates in Sections 1–3 have only the stated **no-descendant** scope;
they do not discharge these further restrictions. For the first four child
primes the proposed fee is \(23/48\). The aggregate countermodel identifies
information missing from that inference. The
[coupled first-root theorem](21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md)
retains richer shared support allocations and proves a fee strictly below
\(15/32\) for the specified \(\{3,5,7,11,13\}\) block with the established
four-vertex-block descendants. That result does not infer a fee from the
scalar constraints refuted here; arbitrary block recursion remains open.

Both programs require Python 3.9+ and only the standard library. Their
compact JSON defaults beside the corresponding script, and `--output PATH`
selects another destination. From the repository root:

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/k5_parent_same_law_envelope.py
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/k5_common_law_prefix_barrier.py
```
