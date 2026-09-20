[Problem index](../../../../Problems/erdos-7-odd-covering-systems.md) ·
[Two-level example](42-two-level-fixed-colors-and-first-hit-moment-obstruction.md) ·
[Actual-chain risk certificates](../profile-notes/321-384/334-same-chain-overlap-and-future-risk-certificates.md)

# Complete event laws can hide a sharp first-hit interval in arbitrarily many coordinates

For every integer \(r\ge4\), there is one containment-reduced family of
distinct odd original moduli and a class of incoming source laws with the
following properties. Every proper marginal of the \(r\) old prime
coordinates is fixed. The complete joint distribution of all original AP
indicators, under the source times current-coordinate Haar, is also fixed.
Every source obeys the stated full-history cylinder caps. Nevertheless, at
the next prime, the half-threshold first-hit cost ranges over a nondegenerate
closed interval whose two endpoints are attained explicitly.

The prime order is increasing and every original prime-power height is one.
This is an ordinary proof for arbitrary \(r\), not an inference from a finite
experiment. It does not rule out useful bounds from these summaries: the
proof gives their sharp bounds in this family. On these complete coordinates,
the two displayed sources have positive distance from the single-step
clipped construction specified in Section 6. The observed
event law does not include the old coordinates or their joint association
with the event vector. No unrestricted noncoverage or new Lean result is
claimed.

Section 7 supplies a separate, reachable ambiguity pair on deeper complete
coordinates. Its two earlier families share numerical moduli but differ
in two residues. All next-stage labels are fixed, and their complete
incoming event-vector law agrees. Equality of the entire original-family
event law is not claimed for that pair and is explicitly disproved below.

## 1. One original family in natural prime order

Let \(p_1<\cdots<p_r\) be the first \(r\) odd primes and put

\[
 N=2^r-2,\qquad P=\prod_{i=1}^r(p_i-1),\qquad
 \epsilon=\frac1{p_r(p_r-2)}.
 \tag{FA1}
\]

Choose a prime \(q\) with \(N<q<2N\). Bertrand's postulate supplies it;
the endpoint \(2N>2\) is even and is not prime. The same postulate gives
\(p_{r+1}<2p_r\). Starting from \(p_4=11<14\), induction yields
\(p_r<2^r-2=N\). Thus \(q\) is larger than every old prime.

The old coordinate space and its pure survivors are

\[
 G=\prod_{i=1}^r\mathbb Z/p_i\mathbb Z,\qquad
 X=\prod_{i=1}^r\{1,\ldots,p_i-1\}.
 \tag{FA2}
\]

Include the old pure classes \(0\pmod {p_i}\). For each nonempty proper
subset \(S\subsetneq\{1,\ldots,r\}\), include exactly one further class,
with original numerical modulus

\[
 m_S=q\prod_{i\in S}p_i.
 \tag{FA3}
\]

There are \(N\) such subsets. Give them pairwise distinct fixed residues
\(t_S\pmod q\), and impose residue one modulo each \(p_i\), \(i\in S\).
CRT gives the corresponding original residue \(a_S\pmod {m_S}\).
For an explicit assignment, order subsets by their nonzero binary codes
\(1,\ldots,2^r-2\) and use one less than the code for \(t_S\).

All numerical moduli are distinct, odd and greater than one. If an old
prime divides \(m_S\), the two classes are disjoint because their residues
at that prime are zero and one. Two comparable new moduli are disjoint
because their \(q\)-residues differ. Hence no containment reduction removes
any original class. The complete original period is
\(q\prod_i p_i\); no numerical modulus is replaced by a projected label.
The \(q-N\) unused current residues already give avoiding integers after
choosing old nonzero residues. These families test the information interface;
they are not odd distinct covering systems.

## 2. Feasible sources with fixed proper marginals

Let \(\nu\) be uniform on \(X\), with atom mass \(1/P\), and write
\(c_p=(p-1)/(p-2)\). Define \(\mathcal M\) to consist of probability
measures \(\mu\) on \(X\) whose marginal on every proper coordinate subset
is the corresponding marginal of \(\nu\), and for which

\[
 \Pr_\mu(X_r=a\mid X_1,\ldots,X_{r-1})
 \le \frac{c_{p_r}}{p_r}
 \quad(a=1,\ldots,p_r-1).
 \tag{FA4}
\]

All conditioning prefixes have positive uniform marginal mass. Before the
last old coordinate, the conditional laws are uniform pure-survivor laws,
because the entire first \(j<r\) coordinate marginal is fixed to a product.
Their atom masses satisfy
\(1/(p_i-1)\le c_{p_i}/p_i\). Thus every member of \(\mathcal M\) has an
actual normalized sequential realization obeying these full-history caps
at every old prime. The last cap is equivalently the linear atom constraint

\[
 \mu(x)\le\frac{1+\epsilon}{P}\quad(x\in X),
 \tag{FA5}
\]

since the first \(r-1\) coordinates have uniform joint mass and
\((1+\epsilon)/(p_r-1)=c_{p_r}/p_r\).

Let \(h_i\) equal one at residue one, minus one at residue two, and zero
at the remaining survivor residues. Each has mean zero. The two laws

\[
 \mu_\pm(x)=\frac1P
 \left(1\pm\epsilon\prod_{i=1}^r h_i(x_i)\right)
 \tag{FA6}
\]

are strictly positive and normalized. Summing over any omitted coordinate
kills the perturbation, so all proper marginals agree with \(\nu\).
Their atom masses obey (FA5). In their sequential realizations the only
nonproduct step is the last old kernel, whose atom mass is
\((1\pm\epsilon\prod_i h_i(x_i))/(p_r-1)\).
In particular \(\mu_\pm\in\mathcal M\), and all old pure classes have
probability zero under every \(\mu\in\mathcal M\).

## 3. The entire single-sample AP event law is fixed

Draw the old word from any \(\mu\in\mathcal M\) and the current coordinate
from uniform \(H_q\), independently. Observe the Boolean membership vector
of **all** original classes at this single CRT point. The old pure
indicators vanish. At most one new-class indicator can be one, because
the \(t_S\) are distinct. Its singleton probability is

\[
 (\mu\otimes H_q)(A_{m_S})
 =\frac1q\Pr_\mu(X_i=1\text{ for all }i\in S)
 =\frac1q\prod_{i\in S}\frac1{p_i-1}.
 \tag{FA7}
\]

The last equality uses that \(S\) is proper. All other nonempty patterns
have probability zero, and normalization determines the empty pattern.
Consequently the complete event-vector law is identical for **every**
\(\mu\in\mathcal M\), not merely for the two displayed sources. Adding
moments of any order of that same single-sample event vector supplies no
additional distinction within this class of sources.

This assertion is about the incoming Haar extension. It does not assert
equality after applying the nonlinear kernel, or equality of the stronger
joint law that retains the old word beside the event vector.

## 4. Half-threshold first-hit cost and its exact range

For an old word \(x\), put \(J(x)=\{i:x_i=1\}\) and \(s=|J(x)|\).
The active new labels are exactly the nonempty proper subsets contained
in \(J(x)\), each occupying its own fixed current residue. The literal
forbidden-fibre Haar load is therefore

\[
 \alpha(x)=
 \begin{cases}
 (2^s-1)/q,&s<r,\\
 N/q,&s=r.
 \end{cases}
 \tag{FA8}
\]

Use the normalized clipped kernel at threshold \(\delta=1/2\). If
\(\alpha\le1/2\), its density is zero on the forbidden set and
\((1-\alpha)^{-1}\) on its complement. If \(\alpha>1/2\), the densities
are \(2-1/\alpha\) on the forbidden set and two on its complement.
The kernel is normalized for each complete old word and is bounded by
\(2H_q\). Its forbidden probability is \((2\alpha-1)_+\).

For \(s<r\), the forbidden count is at most
\(2^{r-1}-1=N/2<q/2\). For \(s=r\), it is \(N>q/2\). Hence, with
\(b=2N/q-1>0\),

\[
 \beta(x)=(2\alpha(x)-1)_+
 =b\,\mathbf1_{\{x=(1,\ldots,1)\}}.
 \tag{FA9}
\]

All sources avoid the earlier pure classes, so \(\mathbb E_\mu\beta\)
is the actual first-hit mass at the current prime. Its exact feasible range
is

\[
 \boxed{\left\{\mathbb E_\mu\beta:\mu\in\mathcal M\right\}
 =\left[\frac{b(1-\epsilon)}P,\frac{b(1+\epsilon)}P\right].}
 \tag{FA10}
\]

To prove the upper bound, apply (FA5) to \(a=(1,\ldots,1)\). For the
lower bound use \(p_1=3\), whose surviving coordinate has exactly two
values. Put \(a'=(2,1,\ldots,1)\). The fixed proper marginal omitting the
first coordinate gives

\[
 \mu(a)+\mu(a')=2/P.
\]

By (FA5), \(\mu(a')\le(1+\epsilon)/P\), so
\(\mu(a)\ge(1-\epsilon)/P\). Multiplication by \(b\) proves both
bounds. The laws \(\mu_-\) and \(\mu_+\) attain the lower and upper
endpoints, respectively. All proper-marginal constraints and (FA5) are
linear, so their convex mixtures remain feasible and attain every value
between those endpoints. The ambiguity is precisely

\[
 \mathbb E_{\mu_+}\beta-\mathbb E_{\mu_-}\beta
 =\frac{2\epsilon b}P>0.
 \tag{FA11}
\]

Thus the loss of exact determination comes with a sharp quantitative bound.
The example supplies no lower bound on the error of an arbitrary compressed
method for different families, and no impossibility theorem for useful
approximate or worst-case estimates.

## 5. Concrete reading and the remaining interface

For \(r=4\), take old primes \((3,5,7,11)\), \(N=14\), \(q=17\).
There are 18 original labels, full period 19635 and 480 old survivor atoms.
The incoming AP vector has only 15 possible patterns: the empty pattern
and fourteen singletons. Formula (FA10) is exactly

\[
 \left[\frac{49}{36720},\frac5{3672}\right],
 \qquad\text{with width }\frac1{36720}.
\]

Independent literal CRT verification of this case matches the proper
marginals, complete event laws, normalized current kernels and both costs.
The proof for arbitrary \(r\) is the construction and inequalities above;
it does not rely on a cutoff experiment or a new Lean check.

For any fixed coordinate-marginal order \(k\), choose \(r>k\) with
\(r\ge4\). Even all proper marginals then fail to determine this cost.
Moreover, even the **complete** single-sample AP event law fails in the
same family. What it discards is the joint incidence of different current
colors over the same old word. Shared-old-word replicas or explicit
conditional fibre information can reveal this relation; more moments of
the unchanged single-sample event vector cannot.

[Profile 334](../profile-notes/321-384/334-same-chain-overlap-and-future-risk-certificates.md)
already provides sufficient finite state using the matching status of every
remaining original label. The present result does not replace its actual
history states or its risk recursion. It gives an explicit family and sharp
interval testing a weaker proposed summary. A useful unrestricted bridge
still needs a quantitative actual-prefix or killed-law estimate that can be
transported across all original labels, depths and future stages.

## 6. The displayed sources are separated from a prescribed clipped step

The normalized sequential realization in Section 2 permits any conditional
kernel satisfying (FA4). A prescribed clipped step imposes an additional
restriction. Fix the complete last old coordinate, its uniform
pure-survivor base \(\nu_r\), and the preceding joint marginal
\(\nu_{<r}\). For each complete preceding word \(x\), choose a forbidden
set \(B_x\) and a threshold \(0<\delta_x<1\). Put
\(\alpha_x=\nu_r(B_x)\) and use density

\[
 k_x(y)=
 \begin{cases}
 [1-\min(\alpha_x,\delta_x)]^{-1},&y\notin B_x,\\
 (\alpha_x-\delta_x)_+/[\alpha_x(1-\delta_x)],
       &y\in B_x,\ \alpha_x>0.
 \end{cases}
 \tag{FA12}
\]

The empty forbidden set gives density one. The full forbidden set also
gives density one. Otherwise (FA12) has at most two values on the entire
resolved coordinate. Allowing arbitrary sets and history-dependent
thresholds enlarges the family of kernels supplied by a fixed original
congruence family; a lower distance bound for this enlarged class remains
valid for such an actual step.

Here is the exact elementary distance calculation. On a uniform space of
\(n\ge3\) atoms, let the target density be
\(r_a=(1+a,1-a,1,\ldots,1)\), where \(0<a<1\). Among all nonnegative
normalized densities \(k\) with at most two values,

\[
 \inf_k\operatorname{TV}(r_a\nu,k\nu)
 =\frac{a(n-2)}{n(n-1)},
 \qquad
 \operatorname{TV}(\rho,\eta)
 :=\frac12\sum_z|\rho(z)-\eta(z)|.
 \tag{FA13}
\]

To prove the lower bound, the constant density has distance \(a/n\).
For a nonconstant candidate, write its high and low values as \(1+u\)
on \(j\) atoms and \(1-v\) on \(n-j\) atoms. Normalization says
\(ju=(n-j)v\), with \(u,v>0\). Exchanging two assigned values cannot
increase absolute error when their order is aligned with the target;
thus a minimizing assignment puts the positive exceptional atom in the
high group and the negative exceptional atom in the low group. The sum
of absolute density errors is

\[
 E=|u-a|+(j-1)u+|v-a|+(n-j-1)v.
\]

For \(2\le j\le n-2\),
\(E\ge2a+(j-2)u+(n-j-2)v\ge2a\). If \(j=1\), substitute
\(u=(n-1)v\). The resulting piecewise linear function has its minimum
\(2a(n-2)/(n-1)\) at \(v=a/(n-1)\); the breakpoints are
\(a/(n-1)\) and \(a\). The case \(j=n-1\) is the same with
\(u,v\) exchanged. Division by \(2n\) proves the lower bound.

For attainment, give the negative exceptional atom density \(1-a\)
and every other atom density \(1+a/(n-1)\). This is also a kernel
of form (FA12): take the forbidden set to be that single atom and
\(\delta=a/(n-1+a)<1/n=\alpha\). Thus (FA13) is sharp even within
the enlarged class of clipped rows. This does not assert that this
particular row is obtainable using the original arithmetic labels.

For (FA6), put \(n=p_r-1\). On the event
\(A=\{\prod_{i<r}h_i(X_i)\ne0\}\), the conditional target density
relative to \(\nu_r\) is a permutation of \(r_\epsilon\). Its
preceding marginal is \(\nu_{<r}\), and
\(\nu_{<r}(A)=\prod_{i<r}2/(p_i-1)\). Total variation of joint laws
with a common preceding marginal is the average conditional total
variation. Consequently every law
\(\widetilde\mu=\nu_{<r}K_r\) of the specified form satisfies

\[
 \operatorname{TV}(\mu_\pm,\widetilde\mu)
 \ge
 \left(\prod_{i<r}\frac2{p_i-1}\right)
 \frac{\epsilon(p_r-3)}{(p_r-1)(p_r-2)}>0.
 \tag{FA14}
\]

For the four-coordinate example this lower bound is \(2/13365\).
The same calculation applies to Chapter 42's displayed sources: their
complete last old coordinate has six pure-survivor atoms, the nonzero
perturbation has amplitude \(1/35\), and the active preceding rows have
mass \(1/2\). Every single clipped step from that fixed preceding
\(\nu_3\otimes\nu_5\) and fixed \(\nu_7\) has joint distance at least
\(1/525\) from either displayed source.

There is a stronger arithmetic conclusion on these two small carriers.
Suppose a fixed set \(T\) has positive reference mass and is disjoint
from every \(B_x\). Formula (FA12) then gives

\[
 \widetilde\mu(T)=\nu_r(T)\,
 \mathbb E_{\nu_{<r}}
 \frac1{1-\min(\alpha_x,\delta_x)}.
 \tag{FA15}
\]

Every integrand is at least one. If the last-coordinate marginal remains
\(\nu_r\), equality forces \(\min(\alpha_x,\delta_x)=0\) almost
surely. Since every \(\delta_x>0\), this means \(\alpha_x=0\) almost
surely, so \(K_r(x,\cdot)=\nu_r\). The resulting joint source is
exactly \(\nu_{<r}\otimes\nu_r\). The same conclusion holds when only
the mass of this fixed \(T\) is preserved.

In Chapter 42's complete carrier \(\mathbb Z/9\times\mathbb Z/5
\times\mathbb Z/7\), keep the stated pure exclusions and bases. Every
possible original mixed class owned by seven has modulus in
\(\{21,35,63,105,315\}\). Numerical distinctness allows at most five
such labels, each using one fixed seven-residue. The six surviving
seven-residues therefore include a residue unused by all these classes;
it supplies \(T\), regardless of their old residues or which classes
are present. Consequently any arithmetic clipped step of this form that
preserves the stated full seven-coordinate marginal produces only the
product source \(\nu\). With the next eleven-stage labels and threshold
kept as in Chapter 42, its cost is exactly \(133/7920\).

For the four-coordinate case of this chapter, the last old prime is
eleven. There are only \(2^3-1=7\) possible nonunit old squarefree
cofactors on \(\{3,5,7\}\), hence at most seven mixed eleven-ending
labels on the complete declared carrier. The ten pure-survivor
eleven-residues again supply an unused \(T\). Preserving their uniform
marginal forces the product source, whose subsequent seventeen-stage
cost is \(b/P=11/8160\). Both conclusions allow history-dependent
positive thresholds; neither permits additional coordinate heights or
duplicate original moduli. The counting argument is not asserted for
\(r\ge5\), where these counts no longer supply an unused residue.

These bounds concern the declared complete carriers and base laws.
Marginalizing additional hidden prime-power digits, mixing different
operations, changing the base, or changing the preceding joint marginal
does not satisfy this comparison contract. The result does not exclude
other ambiguity pairs within a prescribed arithmetic process. It leaves
the cap-class interval (FA10) unchanged, while showing why that interval
cannot by itself disprove a stronger estimate using the actual source
construction.

## 7. A reachable pair with the same incoming next-stage event law

Arithmetic reachability does not make all proper old marginals and the
complete incoming **next-stage** AP vector sufficient. The following two
families use the same numerical moduli, pure-survivor root source, prime
order and threshold schedule. Only two earlier residues differ. Their
actual prescribed outputs have the same indicated summaries, but different
next physical charges and different genuine first-hit masses.

### Literal families and the prescribed kernels

Use prime order \((3,5,7,11)\), complete coordinates
\(\mathbb Z/27\times\mathbb Z/5\times\mathbb Z/49\times\mathbb Z/11\),
and thresholds \(\delta_7=1/96\) and \(\delta_p=1/2\) at the other
primes. Pure-power classes are removed in the stated bases before mixed
clipping, as in (FA12). There are no mixed stages at three and five.

| Original modulus | Family 1 residue | Family 2 residue |
|---:|---:|---:|
| 5 | 0 | 0 |
| 9 | 1 | 1 |
| 49 | 1 | 1 |
| 21 | 1 | 1 |
| 1323 | 2 | 2 |
| 735 | 541 | 247 |
| 945 | 596 | 407 |
| 33 | 1 | 1 |
| 55 | 46 | 46 |
| 539 | 443 | 443 |
| 165 | 136 | 136 |
| 1617 | 247 | 247 |
| 2695 | 1766 | 1766 |

The last six rows are the fixed eleven-ending labels. All thirteen
numerical moduli are distinct odd integers greater than one, with full
period \(72765\). No class contains another, and the integer 14553
avoids every class in both families. These are noncovering information
examples, not counterexamples to Erdős #7.

Write the old coordinates as \((x,z,y)\). The common pure-survivor bases
are uniform on

\[
 V_3=\{x\pmod{27}:x\not\equiv1\pmod9\},\quad
 V_5=\{1,2,3,4\},\quad V_7=(\mathbb Z/49)\setminus\{1\},
 \qquad (|V_3|,|V_5|,|V_7|)=(24,4,48).
 \tag{FA16}
\]

Let \(\nu=\nu_3\otimes\nu_5\otimes\nu_7\), and define disjoint
regions on the indicated coordinates:

\[
 \begin{aligned}
 A&=\{x\in V_3:x\equiv1\pmod3\},& B&=\{2\pmod{27}\},\\
 C&=\{y\in V_7:y\equiv1\pmod7\},& D&=\{2\pmod{49}\}.
 \end{aligned}
 \qquad
 \nu_3(A):\nu_3(B)=6:1=\nu_7(C):\nu_7(D).
 \tag{FA17}
\]

Their probabilities are \(1/4,1/24,1/8,1/48\), respectively. The
literal moduli 21 and 1323 forbid \(C\) on \(A\) and \(D\) on \(B\).
In family \(j\in\{1,2\}\), the moduli 735 and 945 additionally forbid
\(D\) on \(A\) and \(C\) on \(B\), exactly when \(z=j\). Thus the
actual seven-stage forbidden set is

\[
 E_j(x,z)=
 \begin{cases}
 C\cup D,&x\in A\cup B,\ z=j,\\
 C,&x\in A,\ z\ne j,\\
 D,&x\in B,\ z\ne j,\\
 \varnothing,&x\notin A\cup B.
 \end{cases}
 \tag{FA18}
\]

This is a statement about the literal congruences, not a reassignment of
colours after observing a word. For instance, 541 has residues
\((1,1,2)\) modulo \((3,5,49)\), whereas 247 changes only its
five-residue to two. Similarly 596 and 407 have residues \((2,1,1)\)
and \((2,2,1)\) modulo \((27,5,7)\).

For any probability base \(\rho\), its clipped kernel with forbidden
set \(E\) and threshold \(0<d<1\), \(d\le\rho(E)\), obeys the
measure identity

\[
 K_E=\frac{\rho-d\rho(\,\cdot\mid E)}{1-d}.
 \qquad
 K_{C\cup D}=\frac67K_C+\frac17K_D
 \quad(\rho=\nu_7,\ d=1/96).
 \tag{FA19}
\]

The first equality follows directly from (FA12), inside and outside
\(E\). The second uses disjointness and the 6:1 mass ratio. All three
nonempty loads \(1/8,1/48,7/48\) exceed \(d\). This is an identity
among prescribed kernels, not a claim that arbitrary mixtures of
arithmetic operations are permitted. Each actual row uses its own single
set from (FA18).

### What the summaries preserve and omit

Let
\(\mu_j(dx,dz,dy)=\nu_3(dx)\nu_5(dz)K_{E_j(x,z)}(dy)\).
Both are strictly positive on all 4608 old survivor atoms. Their full
\((3,5)\) marginals agree because each row is normalized. For the
\((3,7)\) marginal, each family merges at one of the four equal-mass
five-atoms. For the \((5,7)\) marginal, (FA19) gives
\((7/24)K_{C\cup D}=(1/4)K_C+(1/24)K_D\). Hence all proper
marginals of the **complete** old coordinates agree.

More explicitly, their nonzero difference is

\[
 \frac{d(\mu_1-\mu_2)}{d\nu}(x,z,y)
 =\frac8{665}
   (\mathbf1_A(x)-6\mathbf1_B(x))
   (\mathbf1_{\{1\}}(z)-\mathbf1_{\{2\}}(z))
   (\mathbf1_C(y)-6\mathbf1_D(y)).
 \tag{FA20}
\]

Each factor has mean zero. This also verifies the marginal equalities,
without asserting that those common marginals equal the product base.
In particular the common seven-marginal is not \(\nu_7\): at the unused
residue zero, both laws give mass \(2287/109440\), exceeding the base
mass \(1/48=2280/109440\). Thus the unused-residue rigidity in Section 6
does not apply to this pair.

Set \(Q_3=\mathbf1_A\), \(Q_5=\mathbf1_{\{z=1\}}\), and
\(Q_7=\mathbf1_D\). The six eleven-ending labels correspond to the
nonempty proper subsets of these three conditions, with distinct
eleven-colours \(1,2,3,4,5,6\) in the table's order. Read their AP
indicators under \(\mu_j\otimes H_{11}\), using an independent Haar
current coordinate **before** applying the eleven kernel. At most one
indicator is one. The probability of its singleton pattern is
\(\mu_j(\prod_{i\in S}Q_i=1)/11\), equal between the two families
because \(S\) is proper. Every multiple-one pattern has zero probability,
and normalization fixes the all-zero pattern. Thus the entire incoming
six-dimensional AP event law agrees. It does not retain the joint law
of \((Q_3,Q_5,Q_7)\) or the old word alongside that vector.

If \(s=Q_3+Q_5+Q_7\), the next forbidden count is respectively
\(0,1,3,6\) for \(s=0,1,2,3\). At threshold one half,
\(\beta_{11}=\mathbf1_T/11\), where \(T=A\times\{1\}\times D\).
Here \(\nu(T)=1/768\). Family 1 uses the merged row on \(T\), with
density \(624/665\); family 2 uses \(K_C\), with density \(96/95\).
Consequently

\[
 \begin{aligned}
 \mu_1(T)&=\frac{13}{10640},&\mu_2(T)&=\frac1{760},\\
 \mu_1(\beta_{11})&=\frac{13}{117040},&
 \mu_2(\beta_{11})&=\frac1{8360},&
 \mu_2(\beta_{11})-\mu_1(\beta_{11})&=\frac1{117040}.
 \end{aligned}
 \tag{FA21}
\]

For genuine first-hit mass, use the same-chain killed sources
\(\eta_j=\mathbf1_{\{y\notin E_j(x,z)\}}\mu_j\).
Every point of \(T\) was already killed in family 1; every such point
survived stage seven in family 2. Thus

\[
 \eta_1(\beta_{11})=0,\qquad
 \eta_2(\beta_{11})=\frac1{8360}.
 \qquad
 \eta_1(1)=\eta_2(1)=\frac{2207}{2280}.
 \tag{FA22}
\]

The common earlier loss is \(73/2280\). The equality of proper
marginals concerns \(\mu_1,\mu_2\), not \(\eta_1,\eta_2\).
Keeping just the total earlier loss does not repair the missing joint
relation between survival and the next matching conditions.

The entire thirteen-label original-family event law is **not** equal.
Under \(\mu_1\otimes H_{11}\), the intersection of its 735-class and
the common 55-class has mass \(13/117040\). In family 2 that intersection
is empty: the classes require five-residues two and one. Likewise the
earlier residues themselves are different known inputs. With a fully
fixed family, root law, order and schedule, the prescribed construction
determines one law; this example concerns compression across legal families.

### A range of thresholds and exact verification

The same construction works whenever
\(0<d=\delta_7<1/48\) and \(3/11\le e=\delta_{11}<6/11\).
Equation (FA19) and all marginal/event-law equalities remain valid.
Writing \(\gamma(e)=(6/11-e)/(1-e)>0\), direct evaluation on \(T\)
gives

\[
 \begin{aligned}
 \mu_2(\beta_{11})-\mu_1(\beta_{11})
   &=\gamma(e)\frac{d}{112(1-d)},\\
 \eta_1(\beta_{11})&=0,&
 \eta_2(\beta_{11})&=\frac{\gamma(e)}{768(1-d)}.
 \end{aligned}
 \tag{FA23}
\]

This parameter interval concerns these two fixed finite families. It is
not an all-height ambiguity theorem. A single-number prediction based
only on the shared summaries at \((d,e)=(1/96,1/2)\) has worst-case
absolute error at least \(1/234080\) for the physical fee or \(1/16720\)
for genuine first-hit mass. This is a two-point lower bound; no assertion
is made that an interval of intermediate source laws is reachable.

The [literal-congruence producer](../frontier/cover-geometry/reachable_clipped_ambiguity.py)
and its [exact output](../frontier/cover-geometry/reachable_clipped_ambiguity.json)
reconstruct all 4608 old atoms and 50688 incoming extended atoms per
family. They check normalization, strict positivity, all full proper
marginals, the entire next-stage vector law, (FA20), both kinds of cost,
the distinguishing earlier/current event, numerical distinctness,
noncontainment and the avoiding integer. Nine threshold pairs
check the stated formulas using the same literal row unions. The proof
of the whole interval is (FA19) and the displayed evaluation, not those
finite checks. All executable checks remain active under Python \(-O\).

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/reachable_clipped_ambiguity.py --output /tmp/reachable-clipped-ambiguity.json
```

The new arithmetic ingredient is that literal pure-power exclusions make
the two disjoint mass ratios in (FA17) agree, enabling a legal kernel
identity to move a highest-order interaction between contexts. The generic
kernel formula is already available. This removes an exact-sufficiency
claim for the stated summaries even within actual arithmetic outputs;
it does not rule out useful quantitative bounds that retain additional
original-label or cover-completion information.

## 8. A balanced prefix class has one all-height extra-loss budget

The next estimate uses original numerical-label uniqueness beyond a
conditional density cap. Its source class is restricted: a complete Latin
grid of disjoint old prefixes, one forbidden current prefix per active
cell, and full product two-coordinate marginals. Positive thresholds may
depend on the complete old history. In fact, the fixed-leaf policy
obstruction below shows why that dependence is essential in this class.
The estimate supplies a single budget for the additional first-hit loss
over any fixed continuation; it does not bound the reference continuation
loss or close unrestricted Erdős #7.

### The actual source and its fixed-prefix optimum

Let \(r<s<p\) be odd primes. On complete prime-power coordinates, retain
the pure exclusions \(0\pmod r,0\pmod s,0\pmod p\), and let
\(\nu_r,\nu_s,\nu_p\) be their uniform pure-survivor bases. Choose
pairwise disjoint \(r\)-prefixes \(C_i\) of depths \(e_i\ge1\), and
pairwise disjoint \(s\)-prefixes \(D_j\) of depths \(f_j\ge1\), for
\(1\le i,j\le n\), all contained in the respective pure survivors.
Their masses are
\[
 s_i=\frac{r^{1-e_i}}{r-1},\qquad
 t_j=\frac{s^{1-f_j}}{s-1}.
\]
Let \(J_1,\ldots,J_n\) be a prefix partition of the *entire*
pure-survivor \(p\)-coordinate, with depths \(a_\ell\ge1\) and masses
\(v_\ell=p^{1-a_\ell}/(p-1)\). Choose a Latin square \(L\) of order
\(n\). The head consists exactly of the three pure classes and one
mixed original class per cell, with conditions
\[
 C_i\times D_j\times J_{L_{ij}},\qquad
 m_{ij}=r^{e_i}s^{f_j}p^{a_{L_{ij}}}.
 \tag{FA24}
\]
Require all these numerical moduli to be distinct. No mixed old
\(r,s\) class is added. Thus the incoming old law is
\(\nu_r\otimes\nu_s\), and the actual forbidden union on
\(C_i\times D_j\) is exactly \(J_{L_{ij}}\); elsewhere it is empty.

Use (FA12) with positive history-dependent thresholds, and assume
\[
 K_p\le(1+\zeta)\nu_p,\quad \zeta>0,\qquad
 \mu_{r,p}=\nu_r\otimes\nu_p,\quad
 \mu_{s,p}=\nu_s\otimes\nu_p,
 \quad \mu=(\nu_r\otimes\nu_s)K_p.
 \tag{FA25}
\]
These are full-coordinate marginals, including every declared digit.
For a cell whose forbidden prefix has mass \(v\), put
\(u=\min(v,\delta)/(1-\min(v,\delta))\). Its actual density is
\(1+u\) off the prefix and \(1-(1-v)u/v\) on it. Hence
\(0<u\le\min\{\zeta,v/(1-v)\}\).

Let \(b_{ij}=\int_{C_i\times D_j}u\,d(\nu_r\otimes\nu_s)\).
For a fixed \(x\in C_i\), preservation of the full \((r,p)\)
marginal means that the total increase over the \(s\)-coordinate
equals the subtraction on each \(J_\ell\). Each leaf occurs in
exactly one cell of that row. Integrating in \(x\) gives
\(b_{ij}=v_{L_{ij}}\tau_i\). The other marginal gives
\(b_{ij}=v_{L_{ij}}\kappa_j\). All cells are present and every
\(v_\ell>0\), so \(\tau_i=\kappa_j=\tau\) for one common positive
number, and
\[
 b_{ij}=\tau v_{L_{ij}},\qquad
 \tau\le T_*:=\min_{i,j}s_it_j
       \min\left\{\frac{\zeta}{v_{L_{ij}}},
                    \frac1{1-v_{L_{ij}}}\right\}.
 \tag{FA26}
\]

Let \(R\) be the actual head avoiding set, and define two measures on
that same set:
\(\eta=\mathbf1_R\mu\) and
\(\sigma=\mathbf1_R(\nu_r\otimes\nu_s\otimes\nu_p)\).
The latter is an unnormalized reference measure, not a freshly
conditioned product process. The good-set density formula implies
\(\eta-\sigma\ge0\), and
\[
 (\eta-\sigma)(1)
 =\sum_{i,j}(1-v_{L_{ij}})b_{ij}
 =n\left(1-\sum_\ell v_\ell^2\right)\tau
 \le n\left(1-\sum_\ell v_\ell^2\right)T_*.
 \tag{FA27}
\]
For these fixed prefixes and Latin incidences this upper bound is
attained: take \(u_{ij}=T_*v_{L_{ij}}/(s_it_j)\), constant on each
cell, and \(\delta_{ij}=u_{ij}/(1+u_{ij})\). The definition of
\(T_*\) gives \(0<\delta_{ij}\le v_{L_{ij}}<1\), so these are
actual clipped rows. The Latin row and column sums verify (FA25)
pointwise on the old coordinate, not only after taking its prefix label.
On inactive old cells any positive threshold below one is allowed.

### Numerical uniqueness supplies an all-height bound

Let \(M_r\) be the largest multiplicity of one depth among the
\(e_i\), and \(M_s\) the corresponding multiplicity among the
\(f_j\). The \(M_rM_s\) cells formed by such two depth groups
have the same old numerical cofactor. By (FA24), all their current
depths must differ. If \(d\) is the number of different current depths,
then \(M_rM_s\le d\).

The complete prefix partition is a full \(p\)-ary forest rooted at
the \(p-1\) surviving first digits. With \(I\) internal nodes, it has
\(n=(p-1)(I+1)\) leaves, and its maximum leaf depth is at most
\(I+1\). Consequently, writing \(E=\max_i e_i\) and
\(F=\max_j f_j\),
\[
 M_rM_s\le d\le\frac n{p-1},\qquad
 E\ge\frac n{M_r},\quad F\ge\frac n{M_s},\qquad
 EF\ge n(p-1).
 \tag{FA28}
\]
The leaf-count step uses completeness of the current partition;
it is not asserted for an arbitrary list of prefixes.

Summing (FA26) along a row or column and using disjointness gives
\(\tau\le\zeta\min\{\min_i s_i,\min_j t_j\}\).
Put \(k=\lceil\sqrt{n(p-1)}\rceil\). Equation (FA28) implies
\(\max(E,F)\ge k\), and \(r<s\) gives
\(\tau\le\zeta r^{1-k}/(r-1)\).
Since \(n\ge p-1\ge6\), we have \(k\ge p-1\) and
\(n\le k^2/(p-1)\). The sequence \(k^2r^{-k}\) decreases in
this range. Dropping the factor \(1-\sum v_\ell^2\) in (FA27)
therefore gives the height-independent estimate
\[
 0\le(\eta-\sigma)(1)
 \le\zeta\frac r{r-1}(p-1)r^{-(p-1)}.
 \tag{FA29}
\]
The uniform constant in (FA29) is not claimed optimal.

For any fixed continuation by actual original classes and prescribed
history-dependent kernels, let \(L(\rho)\) be total future first-hit
mass from \(\rho\). Use exactly the same future kernels for both
measures, including when \(\sigma\) is unnormalized. The probability
of a future first hit, conditional on the complete head state, lies in
\([0,1]\). Positivity of \(\eta-\sigma\) gives
\[
 0\le L(\eta)-L(\sigma)
 \le(\eta-\sigma)(1)
 \le\zeta\frac r{r-1}(p-1)r^{-(p-1)}.
 \tag{FA30}
\]
This uses the existing same-killed-law continuation mechanism in
[profile 334](../profile-notes/321-384/334-same-chain-overlap-and-future-risk-certificates.md).
Its new input is (FA28), derived from actual numerical labels and the
prefix forest. There is one budget for all later events together;
neither small \(L(\sigma)\) nor a net global gain is supplied by (FA30).

### A fixed current-leaf policy is impossible in this class

Suppose instead that the positive threshold on an active cell depends
only on its current leaf \(\ell=L_{ij}\). Then \(u=u_\ell>0\)
is constant on that cell, and (FA26) becomes
\(s_it_ju_{L_{ij}}=\tau v_{L_{ij}}\). Multiply over all columns
of row \(i\):
\[
 s_i^n\prod_jt_j
 =\tau^n\prod_{\ell=1}^n\frac{v_\ell}{u_\ell}.
 \tag{FA31}
\]
The right-hand side is independent of \(i\). Thus all \(s_i\),
and hence all \(e_i\), are equal. The column argument makes all
\(f_j\) equal. Each current leaf occurs \(n\) times in the Latin
square, so its numerical modulus in (FA24) is repeated \(n>1\)
times, a contradiction. This includes every single fixed positive
\(\delta_p\). It is an impossibility for the stated Latin source
class, not for all clipped arithmetic sources or for fixed-threshold
methods in general.

### A sharp source-restricted fee and overlapping future events

Take \((r,s,p)=(3,5,7)\), \(n=6\), and \(\zeta=1/35\).
For \(1\le i,j\le6\), use the original class with modulus
\(7\cdot3^i5^j\) and literal conditions
\[
 x_3\equiv\frac{3^{i-1}+1}{2}\pmod{3^i},\qquad
 x_5\equiv\frac{5^{j-1}+1}{2}\pmod{5^j},\qquad
 x_7\equiv1+((i+j-2)\bmod6)\pmod7.
 \tag{FA32}
\]
Together with the three pure classes these are 39 distinct odd moduli.
The old prefix lists are disjoint: the difference between the depth
\(i\) and depth \(j>i\) residues has valuation exactly \(i-1\).
The complete head carrier is \(3^6\times5^6\times7\).
Set
\[
 \epsilon=\zeta s_6t_6=\frac1{212625000},\qquad
 u_{ij}=\frac\epsilon{s_it_j},\qquad
 \delta_{ij}=\frac{u_{ij}}{1+u_{ij}}.
 \tag{FA33}
\]
Then \(T_*=6\epsilon\), every full pair marginal is product, and
the exact head surplus is \(30\epsilon=1/7087500\), attaining
(FA27). The looser all-height bound (FA29) is \(1/2835\).

Append the three literal classes \(22\pmod{33}\),
\(1\pmod{55}\), \(24\pmod{77}\), with \(\delta_{11}=2/11\).
Their three different eleven-colors make
\(\beta_{11}=\mathbf1_{C_1D_1\{x_7=3\}}/9\).
This trigger avoids the head's forbidden seven-color 1 on that cell.
Every source satisfying (FA25) on these fixed head prefixes therefore has
\[
 \eta(\beta_{11})\le\frac1{432}+\frac\epsilon{54}
 =\frac{13289063}{5740875000},
 \tag{FA34}
\]
and (FA33) attains equality. This is strictly below the cap-only value
\(1/420\), achieved by the density
\(1+\zeta h_3h_5h_7\), where \(h_3\) is 1 on \(C_1\) and
\(-1\) elsewhere, \(h_5\) is 1 on \(D_1\) and \(-1/3\)
elsewhere, and \(h_7=\mathbf1_{\{3\}}-\mathbf1_{\{4\}}\).
This comparison density has the same full product pair marginals and
row cap but is not claimed reachable by the head's clipping operations.
The exact improvement is \(54241/820125000\).

A separate continuation of the same head has overlapping triggers.
Write \(A=\{x_3=1\pmod9\}\), \(A_2=\{x_3=4\pmod{27}\}\),
\(B=\{x_5=1\pmod{25}\}\), \(B_2=\{x_5=6\pmod{125}\}\),
and \(C=\{x_7=3\}\). All lie in their stated \(C_1,D_1\)
prefixes. At eleven use old conditions \(A,A_2,B,C\), with current
colors \(0,0,1,2\); at thirteen use \(A,B,B_2,C\), with colors
\(0,1,1,2\). Each old condition and its stated current color defines
one original CRT class. All 47 head-plus-continuation moduli are distinct.
For thresholds \(2/11,2/13\), the triggers are
\(G_1=(A\cup A_2)BC\), \(G_2=A(B\cup B_2)C\), with fees
\(\beta_{11}=\mathbf1_{G_1}/9\),
\(\beta_{13}=\mathbf1_{G_2}/11\). Their actual head-good masses are
\[
 \eta(G_1)=\frac1{540}+\frac{2\epsilon}{135},\quad
 \eta(G_2)=\frac1{600}+\frac\epsilon{75},\quad
 \eta(G_1\cap G_2)=\frac1{720}+\frac\epsilon{90}.
 \tag{FA35}
\]
The thirteen-step does not depend on the eleven-coordinate. Thus
the same-chain first-hit calculation gives
\[
 L_{11,13}(\eta)
 =\frac{\eta(G_1)}9+\frac{\eta(G_2)}{11}
   -\frac{\eta(G_1\cap G_2)}{99}
 =\frac{4877086121}{14208665625000}.
 \tag{FA36}
\]
The generic overlap formula is already available in profile 334; the
literal classes and common-law masses are the inputs verified here.
Integer 2 avoids this whole family. No covering counterexample is claimed.

The [exact producer](../frontier/cover-geometry/balanced_prefix_budget.py)
and [output](../frontier/cover-geometry/balanced_prefix_budget.json) check
the literal congruences, actual rows, complete pair marginals, both
continuations and the cap comparator using rational arithmetic. A
disjoint radix-cell partition carries the exact mass of every complete
coordinate point; 3072 constant-test cells suffice for the sharp head and
the displayed future tests. It is not full-period point enumeration.
The producer also verifies a 147-label head with 12 prefixes per old
coordinate, five depth-one and seven depth-two current leaves, and
\(\zeta=1/100\). On \(3^{12}\times5^{12}\times7^2\), its head
surplus is \(1/16018066406250\). The all-height justification is
(FA28)--(FA29), not this additional finite experiment.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/balanced_prefix_budget.py --output /tmp/balanced-prefix-budget.json
```

All checks remain active under \(-O\). Arbitrary forbidden unions,
nonproduct pair marginals, extra head classes, and an accounting bound
for the reference future loss remain outside (FA29). In particular, the
\(1/2835\) allowance cannot be inserted into a different fixed full-Haar
policy's deficit as a proved gain.

### At current height one, fixed thresholds have a quantitative defect

A different bound drops both pair-product assumptions and the density
cap in (FA25). Retain (FA24), the pure-product incoming old law and the
complete Latin grid, but require every current leaf to have depth one,
so \(n=p-1\) and \(v_\ell=1/n\). Use one fixed
\(0<\delta_p<1\) across all old histories. Write
\[
 S=\sum_i s_i,\quad T=\sum_jt_j,\qquad
 u=\frac{\min(1/n,\delta_p)}{1-\min(1/n,\delta_p)},\qquad
 h=(\eta-\sigma)(1)=\frac{n-1}{n}uST.
\]
In a fixed active old row, the Latin square permutes the current
colors, and its current-coordinate density after integrating out the
other old coordinate is \(1+uT-nut_j\). Off the active old prefixes
it is one. Therefore, with
\(\operatorname{TV}(a,b)=\tfrac12\sum|a-b|\), direct integration gives
\[
 \begin{aligned}
 \operatorname{TV}(\mu_{r,p},\nu_r\otimes\nu_p)
   &=uST\operatorname{TV}((t_j/T)_j,\operatorname{Unif}_n),\\
 \operatorname{TV}(\mu_{s,p},\nu_s\otimes\nu_p)
   &=uST\operatorname{TV}((s_i/S)_i,\operatorname{Unif}_n).
 \end{aligned}
 \tag{FA37}
\]
Here both marginals are allowed to differ from their product bases.

Numerical uniqueness now forces the \(e_i\) to be pairwise distinct:
two equal depths in any fixed column would give the same numerical
modulus, whatever the current colors. Similarly all \(f_j\) are
distinct. If \(d_1<\cdots<d_n\) are positive integer depths and
\(w_i=q^{-d_i}\), then for \(1\le k<n\),
\[
 \sum_{i\le k}w_i\ge w_k\sum_{j=0}^{k-1}q^j,\qquad
 \sum_{i>k}w_i\le w_k\sum_{j=1}^{n-k}q^{-j}.
\]
Thus the normalized first \(k\) weights sum to at least
\((1-q^{-k})/(1-q^{-n})\). Define the positive constant
\[
 \kappa(q,n)=\max_{0\le k\le n}
 \left\{\frac{1-q^{-k}}{1-q^{-n}}-\frac{k}{n}\right\}.
\]
Total variation from the uniform distribution is the maximum such
prefix excess for decreasing weights. Equations (FA37) therefore imply
\[
 \begin{aligned}
 \operatorname{TV}(\mu_{r,p},\nu_r\otimes\nu_p)
   &\ge\frac n{n-1}\kappa(s,n)h,\\
 \operatorname{TV}(\mu_{s,p},\nu_s\otimes\nu_p)
   &\ge\frac n{n-1}\kappa(r,n)h.
 \end{aligned}
 \tag{FA38}
\]
The two constants are sharp: consecutive depths in both coordinates
give exactly the normalized geometric weights, and the disjoint prefix
construction in (FA32), with the corresponding odd primes, realizes
those depths and distinct original moduli for any \(n=p-1\).

For \((r,s,p)=(3,5,7)\), the two factors are
\(2474/3255\) and \(304/455\). The same-kernel positivity argument
used for (FA30) yields, for any fixed actual continuation,
\[
 0\le L(\eta)-L(\sigma)\le h
 \le\min\left\{
  \frac{3255}{2474}\operatorname{TV}(\mu_{3,7},\nu_3\otimes\nu_7),
  \frac{455}{304}\operatorname{TV}(\mu_{5,7},\nu_5\otimes\nu_7)
 \right\}.
 \tag{FA39}
\]
Consequently near-product marginals force small additional loss in this
fixed-threshold class. This is a bound from measured marginal errors,
not a claim that those errors are small in an unrestricted family.
It allows arbitrary old heights, but still requires one current digit,
a complete Latin grid and the stated product incoming law.

The exact producer reuses the same 39 original head labels with fixed
thresholds \(1/96\) and \(1/5\), explicitly dropping (FA25).
The head surpluses are respectively \(19747/9618750\) and
\(19747/506250\); both full-coordinate marginal-TV ratios equal
the sharp constants in (FA38). It does not reuse the balanced source's
probability law for these different policies.

The zero-mean product perturbation, finite conditional-kernel construction
and convexity argument are standard methods. The elementary prime-choice
input is Bertrand's postulate; the repository's pinned Mathlib records it
as `Nat.exists_prime_lt_and_le_two_mul` in
[`Mathlib/NumberTheory/Bertrand.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/Bertrand.lean#L222).
The sharp interval in Sections 1--5, reachable pair in Section 7 and
source-restricted budget in Section 8 are repository-derived;
no literature-priority assertion is made.

## 9. A fixed policy can preserve the current marginal without preserving either full pair

The fixed-leaf obstruction in Section 8 uses a complete Latin grid and
full pair-product marginals. Current-marginal stationarity alone does
not have that rigidity. The following source has 31 distinct original
odd moduli and preserves the current marginal for every fixed
\(0<\delta_7<1\).

### An original-congruence stationary source

Use the carrier \(3^{12}\times5^6\times7\), with pure classes
\(0\pmod3,0\pmod5,0\pmod7\). The incoming old law is the product
of the two uniform pure-survivor laws; the current base is uniform on
\(\{1,\ldots,6\}\). Partition the following 28 distinct
\(3,5\)-monomials into six groups:

| Current color | Monomials |
| --- | --- |
| 1 | \(1,5,375,405,625,2025,3125\) |
| 2 | \(3,15,225,243,6075\) |
| 3 | \(9,25,27,125,1125,1875,3375\) |
| 4 | \(45,81,135,675,5625\) |
| 5 | \(729,2187,3645\) |
| 6 | \(6561\) |

Each group sums to \(6561\). Enumerate the entries in table order by
\(h=0,\ldots,27\). For an entry \(3^i5^j\) in color \(c\), set
\[
 a_h=12-i,\qquad b_h=6-j,\qquad
 \rho_h=1+h+\lfloor h/2\rfloor.
\]
The associated original mixed class is the unique CRT class satisfying
\[
 x\equiv\rho_h\pmod{3^{a_h}},\qquad
 x\equiv1\pmod{5^{b_h}},\qquad x\equiv c\pmod7.
 \tag{FA40}
\]
All \(a_h\ge4\), all \(b_h\ge1\), and the 28 values
\(\rho_h\in\{1,2,4,5,\ldots,40,41\}\) are distinct nonzero
residues modulo \(81\). Consequently the old trigger rectangles are
pairwise disjoint. Unique monomials give unique pairs \((a_h,b_h)\),
hence all 28 mixed numerical moduli are distinct. Together with the
three pure classes these are 31 distinct odd moduli greater than one.

The old mass of a rectangle is
\[
 \frac{3^{1-a_h}}2\frac{5^{1-b_h}}4
 =\frac{15\,3^i5^j}{8\,3^{12}5^6}.
\]
Thus each color has trigger mass \(m=1/675000\), and the union of
all triggers has mass \(6m=1/112500\). Every active old row forbids
exactly one current color. Put
\[
 u=\frac{\min(1/6,\delta_7)}{1-\min(1/6,\delta_7)}.
\]
On a row forbidding \(c\), the actual current density is
\(1+u(1-6\mathbf1_{\{c\}})\); on inactive rows it is one.
Integrating any current color \(c\) therefore gives density
\[
 1+u(6m)-6um=1.
 \quad\text{Hence}\quad \mu_7=\nu_7
 \quad\text{for every }0<\delta_7<1.
 \tag{FA41}
\]
The actual source differs from the product law on its active rows.
On the head-avoiding set, its surplus above the unnormalized product
reference is
\[
 h=\frac56u\frac1{112500}>0.
 \tag{FA42}
\]
This is a stationarity counterexample, not an odd covering: the integer
\(2\) avoids all 31 classes.

### Disjoint original rectangles cannot preserve a full old-current pair

Let \(r<s<p\) be odd primes, \(n=p-1\), and take uniform old
pure-survivor bases at arbitrary finite heights \(E,F\). Consider a
nonempty family of original classes with moduli
\(r^{a_i}s^{b_i}p\), where \(1\le a_i\le E\),
\(1\le b_i\le F\), the pairs \((a_i,b_i)\) are distinct, and
the old rectangles \(C_i\times D_i\) are nonempty and pairwise
disjoint. Assign any current color \(c_i\in\{1,\ldots,n\}\) to
each class, and use one fixed \(0<\delta_p<1\). Then
\[
 \mu_{r,p}\ne\nu_r\otimes\nu_p,
 \qquad
 \mu_{s,p}\ne\nu_s\otimes\nu_p.
 \tag{FA43}
\]
This does not require a Latin grid or a density cap.

To prove the first inequality, set
\(u=\min(1/n,\delta_p)/(1-\min(1/n,\delta_p))>0\) and
\(v_i=\mathbf1-n e_{c_i}\in\mathbb R^n\). Disjointness gives
the current density \(\mathbf1+u v_i\) on rectangle \(i\).
The alleged full pair-product law would therefore imply, at every
complete old \(r\)-word \(x\),
\[
 F(x):=\sum_{i:x\in C_i}\frac{s^{1-b_i}}{s-1}v_i=0.
 \tag{FA44}
\]
Choose the largest occurring \(r\)-depth \(A\), and among labels
at that depth choose the unique largest \(s\)-depth \(B\).
Choose \(x\) in that label's \(r\)-cylinder and \(x'\) in a
different child of the same depth-\((A-1)\) parent. Such an old
survivor child exists: there are \(r\) children when \(A>1\),
and \(r-1\ge2\) at the first pure-survivor level.

All labels of depth less than \(A\) agree at \(x,x'\). Multiply
\(F(x)-F(x')=0\) by \((s-1)s^{B-1}\). Each remaining term of
\(s\)-depth \(b<B\) has integer coefficient divisible by \(s\).
The chosen label is the only term of depth \(B\), and has coefficient
one. In any current coordinate other than its color its vector entry
is one. That coordinate of the alleged equality reduces modulo \(s\)
to \(1=0\), a contradiction. Exchanging \(r,s\) proves the
second inequality. All complete digits are retained throughout.

The same first inequality holds under a weaker assumption than
disjointness: no old word triggers two labels of the same color, and
for each fixed \(x\), the positive values of
\(k(x,y)=\#B(x,y)\) are constant as \(y\) varies. The constant
may depend on \(x\). Indeed the density perturbation on that row is
\[
 \frac{u_k}{k}\sum_{i:(x,y)\in C_i\times D_i}v_i,
 \qquad
 u_k=\frac{\min(k/n,\delta_p)}{1-\min(k/n,\delta_p)}.
 \tag{FA45}
\]
The positive scalar \(u_k/k\) is constant on its active part.
Pair-product would again force (FA44), including rows with no active
point, and the same contradiction applies. The analogous columnwise
condition gives the second inequality. Arbitrary multicolor unions
with varying \(k\), or overlapping triggers of the same color,
are not covered by this argument; simultaneous full pair products
in that unrestricted source class remain unresolved here.

### Exact finite witness

The standard-library producer
[`fixed_stationary_boundary.py`](../frontier/cover-geometry/fixed_stationary_boundary.py)
and its [exact output](../frontier/cover-geometry/fixed_stationary_boundary.json)
give every literal modulus and residue in (FA40). The producer uses
the adjacent `balanced_prefix_budget.py` only for CRT, prefix
partitions and clipping, and rebuilds this source's probability law.
It partitions the complete old coordinates into \(352\times24\)
constant-test cylinders, representing \(4428675000\) old survivor
words. For the default thresholds it verifies:

| \(\delta_7\) | Head surplus \(h\) | \(\operatorname{TV}(\mu_{3,7},\nu_3\otimes\nu_7)\) | \(\operatorname{TV}(\mu_{5,7},\nu_5\otimes\nu_7)\) |
| --- | --- | --- | --- |
| \(1/96\) | \(1/12825000\) | \(1/12825000\) | \(341/6643012500\) |
| \(1/6\) | \(1/675000\) | \(1/675000\) | \(6479/6643012500\) |
| \(1/5\) | \(1/675000\) | \(1/675000\) | \(6479/6643012500\) |

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_stationary_boundary.py --output /tmp/fixed-stationary-boundary.json
```

Repeating `--delta` selects other exact rational thresholds. The
all-threshold assertion is proved by (FA41), not by the three sampled
policies. Section 9 is a repository-derived ordinary mathematical
argument with an exact computational witness, not a Lean-certified
result or a resolution of unrestricted Erdős #7; no literature-priority
assertion is made.
