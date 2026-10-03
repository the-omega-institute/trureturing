# Whole-cover surplus decomposition for endpoint capacity

[Index](../../../marked_head_profile.md) · [Endpoint capacity](845-endpoint-capacity-forces-singleton-charges.md) · [Collision cofactor packing](../600-649/844-collision-moment-needs-cofactor-packing.md)

Report 845 reduces one explicit BBMST-style adapter to the scalar condition
\[
 N(\omega)\le C_*W(\omega),
 \qquad
 C_*=\frac1{\sqrt2-2^{1/4}},
\]
where \(N\) is the complete labelled collision-pair count and \(W\) is the
sum of reciprocal output moduli. This report uses the fact, specific to the
actual common-source pullback, that the output classes cover their complete
quotient. It gives an exact decomposition of the missing capacity into two
source-preserving quantities: overlap among collision columns and excess
singleton mass. The unrestricted Erdős #7 problem remains open; the new
statement is a target for this full-pair endpoint adapter. It is not a
necessary condition for every possible noncoverage argument; see
[report 847](847-selector-charge-is-weaker-than-pair-demand.md).

## 1. The complete output cover and the first threshold

Fix one actual source outcome \(\omega\). Keep every surviving original label,
its literal output modulus \(n_h\), and its literal output phase
\(a'_h\). Let
\[
 L=\operatorname{lcm}_{h\text{ surviving}}n_h,\qquad
 B_h=\{a'_h+n_h\mathbb Z\}\pmod L.
\]
The common-source pullback in report 844 preserves complete coverage, so its
finite output quotient satisfies
\[
 T(V):=\sum_h\mathbf1_{B_h}(V)\ge1
 \qquad\text{for every }V\in\mathbb Z/L\mathbb Z. \tag{1}
\]
This use of whole coverage is essential; an arbitrary endpoint adapter would
not supply (1) merely from the original cover.

Put
\[
 W=\sum_h\frac1{n_h}=\mathbb E_VT(V).
\]
By (1), \(W\ge1\). Writing \(C=C_*\) and
\[
 \theta=\frac1C=\sqrt2-2^{1/4},
\]
the scalar inequality \(N\le CW\) is automatic whenever \(N\le4\), because
\[
 N\le4< C\le CW. \tag{2}
\]
Every scalar violation therefore has
\[
 N\ge5,\qquad 1\le W<\theta N. \tag{3}
\]
The first possible violation is \(N=5\) with
\[
 1\le W<5\theta=1.125032236851869\ldots.
\]

## 2. Exact collision/singleton surplus identity

Let \(H_{\mathrm c}\) be the surviving originals in output columns containing
at least two labels, and \(H_{\mathrm s}\) those in singleton columns. Define
\[
 \begin{aligned}
 W_{\mathrm c}&=\sum_{h\in H_{\mathrm c}}\frac1{n_h},&
 W_{\mathrm s}&=\sum_{h\in H_{\mathrm s}}\frac1{n_h},\\
 T_{\mathrm c}(V)&=\sum_{h\in H_{\mathrm c}}\mathbf1_{B_h}(V),&
 U_{\mathrm c}&=\bigcup_{h\in H_{\mathrm c}}B_h,\\
 R&=(\mathbb Z/L\mathbb Z)\setminus U_{\mathrm c}.&&
 \end{aligned}
\]
The singleton classes cover all of \(R\): every point in \(R\) is covered by
the complete output family, and no collision class covers it. Set
\[
 e_{\mathrm c}:=W_{\mathrm c}-\mu(U_{\mathrm c})
 =\mathbb E_V(T_{\mathrm c}(V)-1)_+,
\]
\[
 s_{\mathrm{extra}}:=W_{\mathrm s}-\mu(R)\ge0.
\]
Since \(\mu(U_{\mathrm c})+\mu(R)=1\), the reciprocal mass has the exact
decomposition
\[
 \boxed{W=1+e_{\mathrm c}+s_{\mathrm{extra}}.} \tag{4}
\]
Thus the desired pointwise scalar capacity is equivalent to
\[
 \boxed{
 e_{\mathrm c}(\omega)+s_{\mathrm{extra}}(\omega)
 \ge\theta N(\omega)-1.
 } \tag{5}
\]
This retains all output phases and the one common Haar coordinate. Merely
showing that singleton classes cover \(R\) proves \(s_{\mathrm{extra}}\ge0\);
it does not prove (5).

Two labels counted by \(N\) can have the same numerical output modulus but
different phases. Their output classes are then disjoint, so numerical
collision does not automatically contribute to \(e_{\mathrm c}\). For two
literal output classes,
\[
 \mu(B_h\cap B_g)=
 \begin{cases}
 1/\operatorname{lcm}(n_h,n_g),
 &a'_h\equiv a'_g\pmod{\gcd(n_h,n_g)},\\
 0,&\text{otherwise}.
 \end{cases} \tag{6}
\]
The missing proof must therefore force actual phase overlap or actual
singleton excess.

## 3. What report 845 forces

Let
\[
 A=\{\omega:N(\omega)>C W_{\mathrm c}(\omega)\}.
\]
On the event \(F\) of report 845, every collision column has modulus at least
\(9\), and report 845 gives
\[
 \mu(F)>\frac27,\qquad
 W_{\mathrm c}\le\frac{2}{9}N.
\]
Since \(C W_{\mathrm c}\le(2C/9)N<N\), we still have \(F\subseteq A\), so
\[
 \boxed{\mu(A)>\frac27.} \tag{7}
\]
Define the singleton mass required by the scalar inequality:
\[
 D(\omega)=\bigl(\theta N(\omega)-W_{\mathrm c}(\omega)\bigr)_+.
\]
Then, exactly,
\[
 N\le CW\quad\Longleftrightarrow\quad W_{\mathrm s}\ge D. \tag{8}
\]
On \(A\), the gap between this required singleton mass and the amount
forced just by covering \(R\) is
\[
 D-\mu(R)=\theta N-1-e_{\mathrm c}. \tag{9}
\]
Hence a proof on \(A\) must establish positive singleton excess whenever the
right-hand side of (9) is positive. Whole coverage alone only gives the
nonnegative lower bound \(s_{\mathrm{extra}}\ge0\).

## 4. An exact integer certificate for a violating outcome

The threshold \(\theta\) is algebraic. It is the unique zero in
\([0,1/4]\) of
\[
 f(x)=x^4-4x^2-8x+2,\qquad f(\theta)=0,
\]
and \(f\) is strictly decreasing on that interval. At a finite output
outcome write \(W=a/L\) with \(a\in\mathbb Z_{>0}\), and put \(z=LN\).
If \(4a\ge z\), then \(W/N\ge1/4>\theta\), so no violation is possible.
If \(4a<z\), define
\[
 P(a,z)=a^4-4a^2z^2-8az^3+2z^4.
\]
Then
\[
 \boxed{
 N>CW\quad\Longleftrightarrow\quad P(a,LN)>0
 \qquad(4a<LN).
 } \tag{10}
\]
This is an exact positive-integer test using the full labelled pair count and
the full reciprocal mass.

It also gives a quantitative gap. On \(A\), put
\(y=W_{\mathrm c}/N=b/(LN)<\theta\). Since
\[
 f(y)=\frac{P(b,LN)}{(LN)^4}>0
\]
has a positive integer numerator and \(\lvert f'(x)\rvert<10\) on
\([0,\theta]\),
\[
 \boxed{
 D(\omega)>
 \frac1{10\,L(\omega)^4N(\omega)^3}.
 } \tag{11}
\]
Therefore pointwise scalar feasibility requires
\[
 \mathbb E[\mathbf1_AW_{\mathrm s}]
 >
 \frac1{10}\,
 \mathbb E\!\left[
 \frac{\mathbf1_A}{L^4N^3}\right]. \tag{12}
\]
If the actual source supplies \(L\le L_0\) on \(A\), and the original family
has \(K\) labels so that \(N\le\binom K2=:G\), then (7) yields the explicit
necessary lower bound
\[
 \mathbb E[\mathbf1_AW_{\mathrm s}]
 >\frac1{35L_0^4G^3}. \tag{13}
\]
No uniform \(L_0\) is currently available for the unrestricted problem, so
(12) is the general form.

## 5. A conditional obstruction usable on any source event

Let \(E\) be an actual source event on which every collision column has
modulus at least \(M>2C\). Since
\(k\le2\binom{k}{2}\) for \(k\ge2\),
\[
 W_{\mathrm c}\le\frac2M N
\quad\text{on }E.
\]
Thus
\[
 N-CW
 \ge C\left[\left(\theta-\frac2M\right)N-W_{\mathrm s}\right].
 \tag{14}
\]
Consequently,
\[
 \boxed{
 \mathbb E[\mathbf1_EW_{\mathrm s}]
 <
 \left(\theta-\frac2M\right)
 \mathbb E[\mathbf1_EN]
 }
 \tag{15}
\]
implies \(\mathbb P(E\cap\{N>CW\})>0\). This is a source-preserving
obstruction theorem; the unresolved task is to establish its singleton
upper bound for an event generated by an EB1 whole cover.

## 6. Why one global mean is insufficient

For the fixed actual source law, the pointwise inequality \(N\le CW\)
almost surely is equivalent to
\[
 \mathbb E[\mathbf1_EN]\le C\,\mathbb E[\mathbf1_EW]
 \quad\text{for every measurable source event }E. \tag{16}
\]
The single signed mean inequality \(\mathbb EN\le C\mathbb EW\) only tests
\(E=\Omega\) and permits surplus in one source region to offset a deficit in
another. A useful averaged target is
\[
 \mathbb E[(N-CW)_+]=0, \tag{17}
\]
together with an argument covering every relevant source outcome.

Writing \(I_{h,c}\) for the indicator that original \(h\) survives in column
\(c\), the exact joint quantities are
\[
 p_{h,c}=\mathbb E I_{h,c},\qquad
 q_{hg,c}=\mathbb E(I_{h,c}I_{g,c}),
\]
\[
 \mathbb EN=\sum_c\sum_{h<g}q_{hg,c},\qquad
 \mathbb EW=\sum_c\frac1{n_c}\sum_hp_{h,c}. \tag{18}
\]
Any source-averaged proof must control the actual phase-dependent correlations
\(q_{hg,c}\) by the reciprocal capacities in the same law; separately
optimizing conditional laws would destroy the required joint source.

## 7. Exact status of the bridge

A scalar violation \(N>CW\) would exclude the literal-endpoint adapter class
of report 845, but it would not by itself give an Erdős #7 counterexample:
an EB1 descent must repair
\[
 \mathbb Z\setminus\bigcup_{d\notin J}A_d
\]
with unused distinct odd nonunit moduli and preserve the original phases.
Conversely, numerical collisions do not prove that any original class is
redundant.

For this full-pair adapter, the remaining target is the source-preserving
surplus inequality (5). A different charge construction need not satisfy this
capacity requirement. No proof of (5), no admissible violating whole cover,
and no unrestricted Erdős #7 settlement is claimed here.
