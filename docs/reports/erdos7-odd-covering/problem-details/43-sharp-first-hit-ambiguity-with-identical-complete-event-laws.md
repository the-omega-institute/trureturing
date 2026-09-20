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

These bounds concern the declared complete carriers and base laws.
Marginalizing additional hidden prime-power digits, mixing different
operations, changing the base, or changing the preceding joint marginal
does not satisfy this comparison contract. The result does not exclude
other ambiguity pairs within a prescribed arithmetic process. It leaves
the cap-class interval (FA10) unchanged, while showing why that interval
cannot by itself disprove a stronger estimate using the actual source
construction.

The zero-mean product perturbation, finite conditional-kernel construction
and convexity argument are standard methods. The elementary prime-choice
input is Bertrand's postulate; the repository's pinned Mathlib records it
as `Nat.exists_prime_lt_and_le_two_mul` in
[`Mathlib/NumberTheory/Bertrand.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/Bertrand.lean#L222).
This ordinary arithmetic construction and its sharp first-hit interval
are repository-derived; no literature-priority assertion is made.
