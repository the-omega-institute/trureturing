[Index](../marked_head_profile.md) · [Previous](16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md) · [Next](18-actual-bb-kernels-with-fixed-old-second-moment-need-not-be-uniformly-continuous.md)

<a id="higher-moments-retain-the-full-old-inventory-in-a-law-changing-perturbation"></a>
### Higher moments retain the full old inventory in a law-changing perturbation

A bounded second moment does not justify replacing the pointwise bound12
in (GC5) by its square root. To see this on actual original labels, let
\(M_N=315\cdot3^N\), retain the PG1 low family, and put every additional
old forbidden class at0. Each new modulus contains27, so these new classes
lie in the already forbidden class0 modulo3. Lift PG1 uniformly to this
period, and condition only for this comparison on the slice
\(E=\{x:x\equiv314\pmod{315}\}\). Its probability \(\eta_N\) is
uniform on \(3^N\) points. For every old divisor choose test residue314.
The resulting load is \(A_N=4(3+Z_N)\), where
\(\Pr(Z_N\ge j)=3^{-j}\) for \(1\le j\le N\). Nested prefix
intersections simultaneously attain every pair cap, so the exact maximum
second moment over all complete old tests is

\[
 \Gamma(\eta_N)=208-16(N+4)3^{-N}\le208.
 \quad
 \frac{\mathbb E_{\eta_N}[A_N\mathbf1_{C_N}]}{\eta_N(C_N)}
 =4(N+3),\qquad C_N=\{x:x\equiv314\pmod{3^{N+2}}\}.
                                                               \tag{FI1}
\]

Here \(\eta_N(C_N)=3^{-N}>0\). Thus no constant depending only on
that second-moment bound controls all these conditional loads. The
indicator of \(C_N\) is itself an original old label, and multiplying
it by a current prefix uses the original label \(3^{N+2}17^e\).
This obstruction concerns the proposed moment substitution, not (GC6).

A third-moment tail supplies a different estimate. Define a full old period

\[
 M=3^{N_3+2}5^{N_5+1}7^{N_7+1}11^{A_{11}}13^{A_{13}},\qquad
 N_3,N_5,N_7\ge0,\quad A_{11},A_{13}\ge1.
                                                               \tag{FI2}
\]

Keep the eleven PG1 forbidden classes and add0 modulo11 and13.
Complete the forbidden old inventory to one class for every \(d\mid M\),
\(d>1\), as follows. For any remaining \(d\) divisible by11 or13,
use residue0; its class lies in a corresponding pure forbidden root.
For any remaining divisor using only3,5,7, put
\(d_0=\gcd(d,315)\) and use the PG1 forbidden residue \(a_{d_0}\)
also modulo\(d\). It lies in the old forbidden class modulo\(d_0\).
The old survivor set is therefore exactly the PG1 survivors, arbitrary
extra3/5/7 digits, and nonzero first11/13 digits with arbitrary suffixes.
Let \(\nu\) be PG1 times those uniform independent coordinates.
This is one actual supported probability; in particular
\(\nu(E)=\mu_*=16622259/1000000007\).

At17, for every \(1\le e\le H\), keep the pure and eleven low-cofactor
CS2 classes from (GC1). Every other original label \(d17^e\),
\(d\mid M\), is forbidden at residue0, hence already lies in the pure
forbidden root0 modulo17. This completes the actual forbidden inventory
to all divisors greater than one of \(M17^H\), without changing the
current bad masks from the low comb. All original complete-test labels
remain independent, including the higher old powers and11/13 cofactors.
The specified extra forbidden residues are part of this construction;
they are not arbitrary-residue hypotheses.

Use the same clipping parameter \(\delta=7/15\). Its actual current
BBMST kernel \(q_0\) depends only on the low point. On every row in
\(E\), transfer mass \(t=2^{-24}\) from the designated clean roots
\(R_H\), equally, to the whole root2 as in (GC1). Call the kernel
\(q_t\). The cap and support checks of (GC1) apply on each such row;
old marginals, bad masses and survivor normalizers remain unchanged.

For completeness, the higher-moment bound keeps every original label.
Let \(G_p\) be independent nonnegative geometric variables with
\(\Pr(G_p\ge j)=p^{-j}\). For11 and13 also use independent
\(B_p\) of probability \(1/(p-1)\). Conditional on any fixed low315
point, and with the current coordinate uniform in a specified first root,
the complete-test moments of orders \(k=2,3\) are bounded by

\[
 Y_{\rm root}=(3+G_3)(2+G_5)(2+G_7)
 \bigl(1+B_{11}(1+G_{11})\bigr)
 \bigl(1+B_{13}(1+G_{13})\bigr)(2+G_{17}),\qquad
 K_k=\mathbb E[Y_{\rm root}^k],
\]

where the expectation is of the kth power of the displayed random
product. To prove the bound, expand the kth power as ordered original-label
tuples. Compatible prefixes intersect at their greatest depth; incompatible
ones have zero mass. Conditional on the low point, every tuple is bounded
by the corresponding product of prefix caps. Nested test residues attain
all those caps in the enlarged infinite suffix model. Summing gives the
stated geometric product. Completing finite heights adds only nonnegative
terms. This comparison is for test moments; the actual forbidden masks
and law have not been centered or changed. Exact values are

\[
 K_2=\frac{638455140323}{248832000},\qquad
 K_3=\frac{104829447952912991}{402653184000},\qquad
 17tK_3<\frac3{10}.
                                                               \tag{FI3}
\]

Fix an arbitrary complete test \(T\), let \(z\) be the root of its
original pure17 label, and keep all its old layouts. Their pair-cap upper
value \(U(T)\), as in (GC2), is still attained by a single nested clean
path. The size of the old inventory is irrelevant to this attainment,
since all its additional forbidden classes were placed in the pure root.
For the killed law use the same baseline replacement
\((1-\beta)A_0^2\) as after (GC2).

If \(z\notin R_H\), the spoke, pure-root or spine gaps from (GC4)
remain \(3\mu(2)14/187\), \(3/17\) or \(3/289\).
The increase under the transfer is at most \(\mu_*tK_2\). Each gap
exceeds that quantity plus \(3\mu_*t/10\).

If \(z\in R_H\), the donor decrease after canceling the old-only
baseline is at least \(3\mu_*t/r_H\): use just the original pure17
label and its two ordered cross terms with the unit label. At the recipient
write its complete load as \(X=A_0+Z\), where \(Z\) includes all
positive17-depth labels that hit there. Their first root is2, so each
is disjoint from the pure17 test on root\(z\). Their missing ordered
pairs supply a cap deficit at least \((2/p)\mu_*\mathbb E Z\),
where \(p=17\) and this expectation uses \(\nu(\cdot\mid E)\)
and the uniform recipient root. The recipient square increment is
\(\mu_*t\mathbb E(2A_0Z+Z^2)\). Pointwise,

\[
 t(2A_0Z+Z^2)-\frac2pZ
 \le tX^2\mathbf1_{X>1/(pt)}\le pt^2X^3.
                                                               \tag{FI4}
\]

Indeed the left side is \(Z[t(2A_0+Z)-2/p]\), nonpositive when
\(X\le1/(pt)\); otherwise it is at most \(tX^2\).
The final inequality is the elementary third-moment tail estimate.
Thus the missing pairs pay for the recipient gain except at a cost
at most \(\mu_*pt^2K_3\). By (FI3), the net decrease is at least
\(3\mu_*t/5-3\mu_*t/10\). No conditional pointwise old-load bound,
depth-one alignment assumption, or omission of a high label is needed.

Taking maxima, both the physical and killed complete-test suprema decrease
by at least

\[
 \varepsilon_0=\frac{3\mu_*t}{10}
 =\frac{49866777}{167772161174405120}>0.
                                                               \tag{FI5}
\]

This bound is uniform over every finite exponent vector in (FI2) and every
finite \(H\ge1\). The conditioned maximum decreases by at least
\(\varepsilon_0/\rho\), with the common \(\rho\ge4/17\).
The conclusion concerns all original test labels on this explicitly
constructed family, not a restriction to its low315 tests.

<a id="rare-old-cylinders-remove-every-globally-clean-root-without-losing-the-improvement"></a>
### Rare old cylinders remove every globally clean root without losing the improvement

The full-inventory improvement is stable when the actual current forbidden
masks change on a sufficiently small old event. Keep \(\nu\), the original
inventory, and all pure17 classes fixed. Change any of the mixed forbidden
residues, subject to the requirement that the resulting bad mask on the fixed
pure-survivor base equals the base mask for every old row outside \(F\). Write \(q=\nu(F)\).
Let \(\widetilde q_0\) be the new family's actual BBMST kernel and let
\(\widetilde q_t\) apply the same transfer on \(E\setminus F\),
with no transfer on \(F\). This is feasible: outside \(F\) the original
support and capacity checks apply; on \(F\) the new normalized BBMST
kernel is retained. The pair have equal old marginals, actual bad charge
and survivor mass, with
\(\widetilde\rho\ge4(1-q)/17>0\) when \(q<1\).

All four physical kernels have density at most2 relative to the uniform
current Haar coordinate: the pure survivor mass is at least15/16 and
the global pure-base cap is15/8. Their killed restrictions also have
this cap. Each new-versus-base comparison is supported on old rows\(F\),
and its pointwise density difference has absolute value at most2.

Under \(\nu\) times current Haar measure, the same ordered-tuple
argument bounds every complete-test fourth moment by

\[
 \begin{aligned}
 Y_{\rm Haar}&=(3+G_3)(2+G_5)(2+G_7)
 (1+B_{11}(1+G_{11}))(1+B_{13}(1+G_{13}))(1+G_{17}),\\
 K_4^{\rm Haar}&=\mathbb E[Y_{\rm Haar}^4]
 =\frac{3528039728534972593}{637009920000}.
 \end{aligned}
                                                               \tag{FI6}
\]

As in (FI3), the power is inside the expectation. The current Haar factor
is \(1+G_{17}\), whose fourth moment is17595/8192; it differs from
the conditioned-root factor in (FI3). Cauchy--Schwarz gives, uniformly over
all complete tests, the following bound for each physical or killed
new-versus-base comparison:

\[
 |J_{\rm new}(T)-J_{\rm base}(T)|
 \le2\int\mathbf1_F L_T^2\,d(\nu\otimes\lambda)
 \le2\sqrt{qK_4^{\rm Haar}}=:\eta.
                                                               \tag{FI7}
\]

Apply (FI7) once to the perturbed kernels and once to the BBMST kernels,
using the same full test domain throughout. Combining with (FI5), the
new-family physical and killed suprema improve by at least
\(\varepsilon_0-2\eta\). In particular,

\[
 q\le3^{-64},\qquad
 64K_4^{\rm Haar}<3^{64}\varepsilon_0^2
 \quad\Longrightarrow\quad
 \widetilde\Gamma_t
 \le\widetilde\Gamma_0-\frac{\varepsilon_0}{2\widetilde\rho}.
                                                               \tag{FI8}
\]

The same positive \(\varepsilon_0/2\) saving holds before conditioning.
This estimate uses comparisons with a fully evaluated geometric moment,
not an assumption that a pair-cap upper bound for the new masks is attained.

There are actual families satisfying (FI8) with no globally clean current
root. Take \(N_3\ge64\), set \(Q=3^{66}\), and let
\(F=\{x:x\equiv314\pmod Q\}\). Under \(\nu\), its probability
is \(\mu\{x\equiv314\pmod9\}3^{-64}\le3^{-64}\), independently
of the higher physical heights. At current depth one, replace just the
five previously redundant mixed classes with old cofactors

\[
 (Q,5Q,7Q,35Q,11Q)
\]

by the CRT classes with old residues314 and respective17 roots
\((12,13,14,15,16)\). Every new old cylinder lies in \(F\); the
removed residue-zero current classes were contained in the pure forbidden
root, so the masks are unchanged outside \(F\). The five moduli are
pairwise distinct and present in the full inventory for every allowed
height. Their old cylinders have positive \(\nu\)-mass, witnessed by
old point314, whose first11 and13 digits are6 and2, both nonzero.
Root0 is already pure forbidden; every spoke1 through11 is bad on the
positive-mass low row2; these five additional classes put forbidden mass
in each other root. Thus no first-level cylinder is globally clean,
including at height one, and this remains so for every finite height.
All original moduli and all their test labels are retained.

This gives a uniform actual-law improvement for a full-inventory,
arbitrary-height family with no globally clean root. Its extra residues
and its small old-event budget are specified hypotheses. No improvement
uniform over arbitrary old/current residues, no improved unrestricted
continuation constant, and no unrestricted noncoverage theorem follow.
The arguments are ordinary moment and CRT proofs; no Lean declaration or
literature-priority claim is made.

The moment estimates reuse the original-label saturated-prefix expansion
(SH19) and the common clean-path comparison (GC2); (FI7) is the finite
Cauchy--Schwarz inequality, also supplied by pinned Mathlib's
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`. BBMST's normalized
clipping kernel and actual-measure optimization remain the public inputs
([1811.03547](https://arxiv.org/abs/1811.03547), section2;
[1901.11465](https://arxiv.org/abs/1901.11465), section5.3). The cubic
absorption and its full-inventory arithmetic construction are the ordinary
proof above; no generic moment or conditioning wrapper is added to Lean.

The [exact moment and family verifier](../verify_pg1_lifted_global_cap.py)
reconstructs the [certificate](../certificates/pg1_lifted_global_cap_certificate.json).
It checks the PG1 source, rational second/third/fourth moment factors,
finite original-label tuple sums with their explicit tails, capacity and
strict-gain constants, and the rare-cylinder CRT witnesses. The symbolic
proofs (FI1)--(FI8) establish the full height and test quantifiers; the
finite arithmetic fixtures do not enumerate that domain. Reproduce from
any directory with:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_pg1_lifted_global_cap.py
```

<a id="joint-mask-stability-permits-arbitrary-high-old-and-current-residues"></a>
### Joint mask stability permits arbitrary high old and current residues

The old-event hypothesis in (FI8) can be replaced by an averaged joint
mask budget. This also permits arbitrary high old forbidden residues,
using one explicitly conditioned old law. The fixed finite core remains
a hypothesis; this is not a uniform improvement over arbitrary cores.

Retain the finite original inventory, reference old probability \(\nu_0=\nu\)
and pure17 comb of (FI2). Let \(\ell_H\) be uniform current Haar measure,
\(\lambda_H=\ell_H(P_H)\ge15/16\) the pure-survivor mass, and
\(m_H=\ell_H(\cdot\mid P_H)\). For the reference and new mixed masks
\(B_x,B'_x\subseteq P_H\), set

\[
 h(x)=\ell_H(B_x\mathbin\triangle B'_x),\qquad
 d(x)=m_H(B_x\mathbin\triangle B'_x)=h(x)/\lambda_H,\qquad
 \epsilon=\mathbb E_{\nu_0}h(x).
                                                               \tag{AM1}
\]

The old projection of this symmetric difference can have full mass.
Neither (AM1) nor the estimates below require that projection to be small.
All budgets are measured using \(\nu_0\), before any old conditioning.

First the BBMST kernel is Lipschitz in its actual bad mask. On any finite
probability space \((P,m)\), fix \(\delta=7/15\), \(C=15/8\),
and write its physical and killed densities as

\[
 k_B=a(\alpha)\mathbf1_{B^c}+b(\alpha)\mathbf1_B,\quad
 k_B^-=a(\alpha)\mathbf1_{B^c},\quad \alpha=m(B),\qquad
 a(u)=\frac1{1-\min(u,\delta)},\quad
 b(u)=\begin{cases}C(u-\delta)_+/u,&u>0,\\0,&u=0.\end{cases}
\]

Both coefficients are increasing, \(a\le C\), \(b\le1\), and
\(\int k_B\,dm=1\). If \(B\subseteq B'\), the negative part of
\(k_{B'}-k_B\) is supported on \(B'\setminus B\), where its absolute
value is at most \(C\). Equal total masses therefore give the physical
bound below. For the killed densities, the negative part has mass at most
\(C(\alpha'-\alpha)\), and the positive part has mass
\((1-\alpha')[a(\alpha')-a(\alpha)]\le C(\alpha'-\alpha)\),
as follows directly in the three cases separated by \(\delta\).
For arbitrary masks, apply the nested bounds through \(B\cup B'\):

\[
 \|k_{B'}-k_B\|_{L^1(m)},\quad
 \|k_{B'}^--k_B^-\|_{L^1(m)}
 \le2C\,m(B\mathbin\triangle B').
                                                               \tag{AM2}
\]

In the original current Haar coordinate, integrating (AM2) over old rows
bounds each physical or killed reference/new BBMST difference by
\((2C/\lambda_H)\epsilon\le4\epsilon\).

The improving transfer itself can be repaired. Keep \(t=2^{-24}\),
\(E=\{x\equiv314\pmod{315}\}\) and the roots \(R_H\) from (FI3).
On a row in \(E\) with \(d(x)\le1/68\), replace each uniform root
probability \(U_{j,H}\), for \(j\in\{2\}\cup R_H\), by its
conditioning \(U'_{j,x,H}\) on the new good set. Define

\[
 q'_{t,x}=q'_{0,x}+tU'_{2,x,H}
                  -\frac{t}{r_H}\sum_{j\in R_H}U'_{j,x,H}.
                                                               \tag{AM3}
\]

Here \(q'_0\) is the new mask's actual BBMST kernel. On all other rows
use \(q'_t=q'_0\). This rule is fixed before selecting any test.
Every indicated root was wholly good in the reference row. Its new good
Haar mass is at least \(1/17-h(x)\ge3/68\). The reference good Haar
mass on \(E\) is at least \(7/8\), so the new mass is at least
\(117/136\). Also \(\alpha'\le1/15+1/68<\delta\), and the
new BBMST row is uncharged. Its good Haar density \(c'\) satisfies
\(1\le c'\le136/117\). The following strict margins prove feasibility:

\[
 \frac{136}{117}+\frac{68}{3}t<C,\qquad
 1-\frac{17}{3}t>0.
\]

The first bounds the recipient density below the allowed Haar cap
\(C/\lambda_H\); the second bounds the remaining donor density, using
\(r_H\ge4\). The transfer has zero total mass and is entirely good.
Thus it preserves each old marginal, the new family's actual bad charge,
and its survivor mass. It does not posit a separate test-dependent law.
All physical and killed kernels still have Haar density at most2.

Here is the quantitative repair error. If \(h_j\) is the new bad Haar
mass removed from root \(j\), then
\(\|U'_{j,x,H}-U_{j,H}\|_1=34h_j\). The roots are disjoint, so on
retained rows the change in the signed transfer is at most \(34t h(x)\).
On skipped rows in \(E\) it is \(2t\le136t d(x)\). Combining these
disjoint row cases gives at most \(136t\mathbb E_{\nu_0}d\).
The signed transfers are supported on the respective good sets, so this
same comparison applies to physical and killed kernels. With (AM2),

\[
 \|q'_t-q_t\|_1,\quad\|(q'_t)^--q_t^-\|_1
 \le A\epsilon,\qquad
 A=4+\frac{2176}{15}t=\frac{7864337}{1966080}<5.
                                                               \tag{AM4}
\]

These are joint-law norms under the unchanged \(\nu_0\).
For every complete original test \(T\), (FI6) supplies
\(\mathbb E_{\nu_0\otimes\ell_H}L_T^4\le K_4^{\rm Haar}\).
If a density difference has absolute value at most2 and \(L^1\) norm
at most \(D\), Cauchy--Schwarz bounds its test-square integral by
\(\sqrt{2D K_4^{\rm Haar}}\). Consequently the two comparisons needed
to transfer (FI5) cost at most
\((\sqrt8+\sqrt{10})\sqrt{K_4^{\rm Haar}\epsilon}
\le6\sqrt{K_4^{\rm Haar}\epsilon}\). This bound is uniform over all
test residues and all finite heights, with no truncated test domain.
The new common survivor mass is at least \(4/17-\epsilon\): every
reference row has good Haar mass at least \(4/17\), the new mask removes
at most \(h(x)\) of it, and BBMST good Haar density is at least one.

Old high residues may also change. Let \(S\) be the event that the old
point avoids all new old forbidden classes, set
\(q=\nu_0(S^c)\), and use the single supported probability
\(\nu_S=\nu_0(\cdot\mid S)\). Assume \(q\le1/2\).
For either fixed new row kernel in (AM3), the joint density change caused
by \(\nu_0\to\nu_S\) has \(L^1\) norm at most \(2q\).
Its absolute value relative to \(\nu_0\otimes\ell_H\) is at most2:
on \(S^c\) it is the old density, and on \(S\) it is that density
times \(q/(1-q)\). This bounds the difference, although the conditioned
joint density itself can exceed2. Each physical or killed test-square
comparison costs at most \(2\sqrt{qK_4^{\rm Haar}}\).
The two maxima therefore lose at most \(4\sqrt{qK_4^{\rm Haar}}\).

Let \(V_{S,0},V_{S,t}\) be the new family's physical maxima under
\(\nu_S q'_0,\nu_S q'_t\), and let \(V^-\) denote their killed
maxima. Combining the comparisons gives both inequalities

\[
 \begin{aligned}
 V_{S,t}&\le V_{S,0}-\varepsilon_0
       +6\sqrt{K_4^{\rm Haar}\epsilon}+4\sqrt{K_4^{\rm Haar}q},\\
 V^-_{S,t}&\le V^-_{S,0}-\varepsilon_0
       +6\sqrt{K_4^{\rm Haar}\epsilon}+4\sqrt{K_4^{\rm Haar}q}.
 \end{aligned}
                                                               \tag{AM5}
\]

Their actual bad charges agree pointwise, and their common survivor mass
satisfies
\(\rho_S\ge(4/17-\epsilon-q)/(1-q)\).
In particular, the exact constants in (FI5)--(FI6) satisfy

\[
 \theta=2^{-100},\qquad
 400K_4^{\rm Haar}\theta<\varepsilon_0^2.
 \quad
 q,\epsilon\le\theta
 \ \Longrightarrow\quad
 \Gamma_{S,t}\le\Gamma_{S,0}
              -\frac{\varepsilon_0}{2\rho_S},\qquad \rho_S>0.
                                                               \tag{AM6}
\]

The physical and killed maxima each improve by at least
\(\varepsilon_0/2\). The conditioning is on actual new old survivors;
the two laws being compared have the same old marginal \(\nu_S\).

The pure17 residues need not remain fixed above the finite core either.
For a new pure-survivor set \(P'_H\), its mass is still at least
\(15/16\): there is only one pure forbidden class at each positive
17-depth. In this paragraph let \(D_x,D'_x\) be the raw mixed unions
before restriction to a pure-survivor set, and define

\[
 \kappa=\ell_H(P_H\mathbin\triangle P'_H),\quad
 \eta=\mathbb E_{\nu_0}\ell_H(D_x\mathbin\triangle D'_x),\quad
 \zeta=\kappa+\eta.
\]

The symmetric difference of the full good sets
\(P_H\setminus D_x\) and \(P'_H\setminus D'_x\) has Haar mass
\(h_G(x)\le\kappa+\ell_H(D_x\mathbin\triangle D'_x)\).
To compare the two actual BBMST kernels, first change the pure probability
while holding the raw mixed set fixed, then change that mixed set.
The pure probabilities have \(L^1\) distance
\(r\le(32/15)\kappa\). For a fixed bad set their bad probabilities
therefore differ by at most \(r/2\). The coefficients \(a,b\) in
(AM2) have Lipschitz constants at most \(225/64,225/56\), respectively,
including the break at \(\delta\). Decomposing the kernel difference
into a change of probability and a change of coefficients gives, for both
physical and killed kernels,

\[
 \|q_{m',D}-q_{m,D}\|_1
 \le\left(C+\frac{225}{112}\right)r
 =\frac{435}{112}r\le4r.
\]

Here \(435/112<4\), and when \(r=0\) the norm is zero.
Together with (AM2), the joint new/reference BBMST difference is at most
\((128/15)\kappa+4\eta\le9\zeta\).
Now apply (AM3) on rows in \(E\) for which \(h_G(x)\le1/68\),
conditioning each selected root on the full new good set. The same
\(117/136\) good-mass bound makes the row uncharged, since
\(\alpha'\le1-117/136<\delta\). The same capacity margins apply.
The repair difference is at most \(136t\mathbb E h_G\), so the
candidate physical and killed differences are at most
\((9+136t)\zeta\le10\zeta\), since \(9+136t<10\).
Every current row kernel again has Haar density at most2.
The two current square comparisons cost at most
\((\sqrt{18}+\sqrt{20})\sqrt{K_4^{\rm Haar}\zeta}
\le9\sqrt{K_4^{\rm Haar}\zeta}\).
Combining with the same old conditioning gives

\[
 \begin{gathered}
 V_{S,t}\le V_{S,0}-\varepsilon_0
       +9\sqrt{K_4^{\rm Haar}\zeta}+4\sqrt{K_4^{\rm Haar}q},\\
 V^-_{S,t}\le V^-_{S,0}-\varepsilon_0
       +9\sqrt{K_4^{\rm Haar}\zeta}+4\sqrt{K_4^{\rm Haar}q},\\
 676K_4^{\rm Haar}2^{-100}<\varepsilon_0^2,\qquad
 q,\zeta\le2^{-100} \Longrightarrow\quad
 \Gamma_{S,t}\le\Gamma_{S,0}-\frac{\varepsilon_0}{2\rho_S},\qquad
 \rho_S\ge\frac{4/17-\zeta-q}{1-q}>0.
 \end{gathered}
                                                               \tag{AM7}
\]

Here both compared kernels use the new full pure-survivor base and the
same actual old probability \(\nu_S\). This extension changes the
pure normalization explicitly; it does not silently count pure holes as
mixed holes on the old base.

This budget holds for arbitrary forbidden residues beyond an explicit
finite exponent box. For every period in (FI2) and current height \(H\),
keep the reference forbidden residue on each original label whose six
prime exponents are all at most65. On every other original label allow an
arbitrary residue, including old labels, pure17 labels and mixed labels.
Keep every original test label and its independent test residue.

The reference old probability has density, relative to uniform old Haar,
at most

\[
 C_{\rm old}=315\max_x\mu(x)\frac{11}{10}\frac{13}{12}
 =\frac{49916643777}{8000000056}.
\]

For a common box depth \(b\), define the complete geometric sums

\[
 \begin{aligned}
 S_\infty&=\prod_{p\in\{3,5,7,11,13\}}\frac p{p-1}
          =\frac{1001}{384},\\
 S_b&=\prod_{p\in\{3,5,7,11,13\}}
             \frac p{p-1}(1-p^{-(b+1)}),\\
 T_{\rm old}(b)&=S_\infty-S_b,\qquad
 T_{\rm pure}(b)=\frac{17^{-b}}{16},\\
 T_{\rm mixed}(b)&=\frac{S_\infty-1}{16}
                    -\frac{(S_b-1)(1-17^{-b})}{16}.
 \end{aligned}
\]

These are sums over all original labels outside the box, with old depth
starting at zero and current depth starting at one; \(d=1\) is excluded
only from the mixed sum, because its pure labels have their own sum.
They majorize every finite physical exponent vector by adding nonnegative
terms. For old labels only the new classes can delete reference mass.
For current labels, the symmetric difference of the unions lies in the
union of all removed and added classes. The actual cylinder cap
\(\nu_0(a\bmod d)\le C_{\rm old}/d\) and CRT therefore give

\[
 q\le C_{\rm old}T_{\rm old}(b),\qquad
 \zeta\le2T_{\rm pure}(b)+2C_{\rm old}T_{\rm mixed}(b).
                                                               \tag{AM8}
\]

At \(b=65\), exact rational arithmetic gives both right sides less
than \(2^{-100}\). Their ratios to \(2^{-100}\) are respectively
less than0.668 and0.084. Thus (AM7) applies to **every assignment outside
this fixed core**, uniformly over all finite heights, with gain at least
\(\varepsilon_0/(2\rho_S)\) in the actual conditioned supremum.
The full tails have been evaluated, not discarded; no enumeration of a
large but finite height substitutes for this argument.

The stronger joint-mask condition has examples beyond the small-old-event
condition. For \(H\ge67\), change the two original classes with labels
\(3\cdot17^{66}\) and \(3\cdot17^{67}\) to old residues1 and2
modulo3, respectively, and current residue12 at their respective depths.
Every reference old survivor has residue1 or2 modulo3. Root12 was globally
clean, so every old row gains a forbidden current point. The old projection
of the changed mask is therefore the entire old support. Both labels lie
outside the exponent65 core, so (AM8) still bounds their small joint mass.
This construction is an illustration of the strict extension, not an
extra assumption in the arbitrary-tail conclusion.

The remaining restrictions matter. The six allowed primes are fixed and
the original finite core residues are specified by (FI2); arbitrary cores
and additional prime support remain outside this result. The supported old
law is the explicitly constructed \(\nu_S\), not an unspecified prior
BBMST output. Its quantitative reference cylinder cap is used in (AM8),
and its reference fourth moment is used in (AM5)--(AM7). No better bound
for the unrestricted17/19 continuation follows merely from this local
strict improvement.

The proof reuses the original-label moment expansion (FI6), the actual
BBMST clipping coefficients, finite conditioning and Cauchy--Schwarz.
Pinned Mathlib provides `ProbabilityTheory.cond_apply` and
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`; these standard
primitives are not presented as new Lean declarations. The repaired
probability and its full original-label comparison above are ordinary
mathematical proofs. They have not been formalized in Lean.

<a id="the-same-complete-second-moment-can-hide-an-unbounded-fourth-moment"></a>
### The same complete second moment can hide an unbounded fourth moment

The fourth-moment hypothesis in (AM5)--(AM7) cannot be replaced by a
bound on the complete original-test second moment alone, even with an
unchanged exact value. For \(N\ge2\), take every original old modulus
\(3^j\), \(1\le j\le N\), with forbidden residue1. These distinct
odd classes have union exactly1 modulo3. Let \(\beta_N\) be uniform on
the actual survivors \(x\not\equiv1\pmod3\), and define

\[
 \nu_{N,u}=(1-u)\beta_N+u\delta_0,\qquad 0\le u\le1.
\]

Every original divisor, including the unit divisor, retains an independent
test residue. A cylinder at depth \(j\ge1\) has \(\nu_{N,u}\)-mass
at most \((1-u)/(2\cdot3^{j-1})+u\), attained by the zero cylinder.
Expanding the kth power of the complete load into ordered original-label
tuples, an intersection is empty or a cylinder at the maximum depth.
The coherent zero tests attain all those caps simultaneously. Thus

\[
 \Gamma_k(\nu_{N,u})=(1-u)B_{k,N}+u(N+1)^k,\qquad
 B_{k,N}=1+\sum_{j=1}^N
                 \frac{(j+1)^k-j^k}{2\cdot3^{j-1}}.
\]

In particular \(B_{2,N}=4-(N+2)/(2\cdot3^{N-1})<4\). Put

\[
 u_N=\frac{5-B_{2,N}}{(N+1)^2-B_{2,N}}.
 \qquad
 \Gamma_2(\nu_{N,u_N})=5,\qquad
 \Gamma_4(\nu_{N,u_N})>(N+1)^2\longrightarrow\infty.
                                                               \tag{AM9}
\]

Indeed \(0<u_N<1\) and \(u_N>1/(N+1)^2\); the atom at zero alone
supplies the displayed fourth-moment lower bound. These laws give positive
weight to every actual old survivor. This excludes any height-uniform
fourth-moment bound depending only on \(\Gamma_2\) for arbitrary
supported old probabilities. It does not assert that these spike laws are
produced by the prior BBMST kernels. Their Haar density cap is at least
\(3^Nu_N>3^N/(N+1)^2\), so they violate the extra uniform domination
used in (AM8). The original-label base moment formula is the same geometric
prefix calculation as (FI3); the added spike keeps the second maximum
exactly fixed while forcing the higher maximum to diverge.

The [joint-mask and complete-tail verifier](../verify_average_mask_tails.py)
reconstructs its [exact certificate](../certificates/average_mask_tails_certificate.json)
from the pinned FI inputs. It checks the rational margins and full tail
sums, all65536 ordered masks on an eight-point space through165 intersection
types, literal current repair and pure-base comparisons, and the original-label
full-projection example. For (AM9), it enumerates all27 and729 independent
test layouts at heights2 and3; the unbounded conclusion follows from the
ordered-tuple proof above. Reproduce from any directory with:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_average_mask_tails.py
```
