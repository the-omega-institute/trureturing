[Index](../marked_head_profile.md) · [Previous](14-joint-observation-guidance-from-the-polynomial-closed-graphs.md) · [Next](16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md)

<a id="a-clean-cylinder-makes-all-current-prime-pair-caps-exact"></a>
### A clean cylinder makes all current-prime pair caps exact

The fixed-test distinction (PO3) need not survive maximization over
all tests. At height one, suppose a root avoids both the pure forbidden
root and every actual mixed bad class. Fix arbitrary independent old
complete test loads \(A_0,A_1\). Placing every positive-depth test
label on that root simultaneously attains all current-prefix caps,
so the maximal new square for these old loads is

\[
 \mathbb E_\mu\left[A_0^2+
       \frac{g_x}{p-1}(2A_0A_1+A_1^2)\right].          \tag{CS1}
\]

The exponent-zero term follows from preserved old marginals; the
other terms are supported in the clean root. The same expression is
an upper bound for every current-root assignment, since the actual
kernel density is at most \(g_x\). Both families in (PO3) have a
common clean root and the same \(g_x\). Maximizing (CS1) over their
identical old test domain therefore gives identical complete-test
suprema, although their common fixed test has different values.

A common clean path does not suffice for this argument: every shallow
test cylinder on that path must itself be clean to attain its cap.
For example, at17 delete pure root0 and, for \(2\le e\le17\),
use the original mixed modulus \(3\cdot17^e\), old class1 modulo3,
and current residue \(e-1\) modulo \(17^e\). Each surviving root
contains some bad mass on that old row, although their total Haar
mass is less than \(\sum_{e\ge2}17^{-e}\) and a positive-measure
common clean set remains. This does not assert that every complete
test has positive overlap: a test can instead sacrifice shallow
energy on deleted cylinders.

Here is an exact arbitrary-height construction that also allows the
old layouts to vary independently with depth. Let \(M\) be odd,
\(p\nmid M\) prime, and

\[
 D=\{d>1:d\mid M\},\qquad K=|D|\le p-3.
\]

Fix one old probability \(\mu\). At each \(1\le e\le H\),
fix arbitrary old forbidden cylinders \(C_{d,e}\) for every
\(d\in D\). Independently, at every \(0\le e\le H\), fix
a complete old test layout with load \(A_e\). No old residues need
agree across depths or between forbidden and test layouts. The new
forbidden inventory contains exactly one class of each modulus
\(p^e\) and \(dp^e\), \(d\in D\), \(1\le e\le H\).
If an input omits some of these moduli, this is an enlarged admissible
inventory, not an assertion of equality within that smaller inventory.

Assign distinct spokes \(j_d\in\{1,\ldots,K\}\), reserve the
spine digit \(s=p-2\) and the test root \(r=p-1\). Digits below
are least significant first. Choose forbidden prefixes

\[
 p^e:\ s^{e-1}0,\qquad
 dp^e:\ (C_{d,e},s^{e-1}j_d).                         \tag{CS2}
\]

CRT realizes each pair as a residue modulo the stated original
modulus. No moduli are identified: \(p\nmid d\) separates current
exponents, and the old divisors are distinct. All current forbidden
prefixes are disjoint. At different depths they differ where the
shorter prefix leaves the spine; at the same depth their final digits
differ. The whole first-level cylinder \([r]\) is clean. Put

\[
 \begin{aligned}
 s_H&=\sum_{e=1}^H p^{-e},&\lambda_H&=1-s_H,\\
 R_e(x)&=\sum_{d\in D}\mathbf1_{C_{d,e}}(x),&
 b_H(x)&=\sum_{e=1}^H p^{-e}R_e(x),&
 \alpha_H(x)&=b_H(x)/\lambda_H.
 \end{aligned}                                       \tag{CS3}
\]

These are actual pure-survivor and mixed-union masses, not union
relaxations. In particular \(\lambda_H>(p-2)/(p-1)>0\) and
\(\alpha_H<K/(p-2)<1\) when \(K>0\); for \(K=0\) it is zero.
Fix \(0\le\delta<1\). For the normalized kernel (PO1), let

\[
 c_H=\frac1{\max\{\lambda_H-b_H,\lambda_H(1-\delta)\}},
 \qquad \beta_H=\frac{(\alpha_H-\delta)_+}{1-\delta}.
                                                               \tag{CS4}
\]

Thus \(c_H=g_H/\lambda_H\), and \(\beta_H\) is its actual
assigned bad mass. Place every depth-\(e\) test prefix at
\(r00\cdots0\), independently of its old label. Define

\[
 Q_H(x)=\sum_{\substack{0\le e,f\le H\\(e,f)\ne(0,0)}}
                  p^{-\max(e,f)}A_e(x)A_f(x).
\]

Every positive-depth pair intersection is then a nested clean prefix
of Haar mass \(p^{-\max(e,f)}\). The entire new square increment
vanishes on the actual bad union, while the old baseline is preserved.
Consequently

\[
 \mathbb E_{\rm new}[L_H^2\mid x]=A_0(x)^2+c_H(x)Q_H(x).
                                                               \tag{CS5}
\]

This is also the maximum over all current-prime forbidden residues
and all current-prime test prefixes with the specified old layouts.
Indeed, for any alternative, its pure-survivor Haar mass \(\lambda\)
and conditional mixed density \(\alpha\) obey
\(\lambda\ge\lambda_H\) and \(\lambda\alpha\le b_H\).
Its kernel cap therefore satisfies

\[
 \frac g\lambda=
 \frac1{\max\{\lambda(1-\alpha),\lambda(1-\delta)\}}
 \le c_H,
\]

and its charge is at most \(\beta_H\). Expanding every original
test-label pair gives the upper bound in (CS5). Construction (CS2)
attains it and the charge simultaneously, at every old point. For
any \(f,W\ge0\), the exact joint maximum is thus

\[
 \mathbb E_\mu\left[f(A_0^2+c_HQ_H)+W\beta_H\right]. \tag{CS6}
\]

The current-prime optimization has been eliminated in this specified
domain; the old forbidden and test layouts still have to be optimized
together. The count \(K\) is the number of actual original old
cofactors, not their number after projection to315 and not the number
active at one old point. Higher old prime powers, and previously
introduced11/13 labels, cannot be discarded to meet this hypothesis.

For the specialization \(R_e=R\) and \(A_e=A\) at every depth,
write \(C=1+R\), \(\delta=(T-1)/(p-2)\),
\(1\le T<p-1\), and \(d_p=p-1-T\). Then

\[
 \begin{aligned}
 Q_H&=a_H A^2,&a_H&=\sum_{j=1}^H(2j+1)p^{-j},\\
 a_H&\uparrow a_p=\frac{3p-1}{(p-1)^2},&
 a_p-a_H&=p^{-H}\left(\frac{2H}{p-1}+a_p\right),\\
 c_H&\uparrow\kappa(C)=\frac{p-1}{p-1-\min(C,T)},&
 \beta_H&\uparrow\frac{(C-T)_+}{d_p}.
 \end{aligned}                                       \tag{CS7}
\]

Hence the supremum over legitimate finite heights, with these old
layouts repeated, is exactly

\[
 \mathbb E_\mu\left[f(1+a_p\kappa(C))A^2+
                         \frac W{d_p}(C-T)_+\right]. \tag{CS8}
\]

This is a limit of finite actual families, not an infinite covering
system. Repeated old layouts are only a specialization of (CS6);
no claim that they optimize its full old-layout domain is made.

For PG1 at \(M=315\), \(K=11\), so both17 and19 admit the
construction. Including its eleven original old forbidden classes
gives exactly \(11+12H\) distinct odd moduli. Center both old
layouts at2, so \(R(2)=11\) and \(A=1+R\). At \(T=8\),
already at \(H=1\),

\[
 \beta_{17}(2)=53/128,\qquad \beta_{19}(2)=61/180.
\]

The global charge is at least these constants times
\(\mu(2)=13119398/1000000007>0\), yet new-square bad overlap is
exactly zero for every height. This rules out a universal positive
extra-overlap rebate under the local hypotheses alone. It does not
saturate the later (SH26) unit-floor relaxation, Jensen comparisons,
the scalar certificate or the final17/19 criterion, and it imposes
no eventual-cover assumption. The useful remaining target is the
joint old-layout energy and charge in (CS6), and control when the
actual cofactor inventory exceeds this construction's range.

`verify_pg1_comb_sharpness.py` and its adjacent certificate retain
exact finite realizations and kernel checks for this obstruction.
The all-height and optimization statements above have ordinary
proofs; no new Lean declaration or unrestricted resolution is claimed.

<a id="effective-truncation-of-both-forbidden-and-test-layouts"></a>
### Effective truncation of both forbidden and test layouts

In the precise small-inventory domain of (CS2)--(CS6), let \(M_H\)
be the maximum of (CS6) over every old forbidden and complete test
layout through height \(H\). Keep the same old law, cofactor inventory,
\(\delta,f,W\) at all heights. Suppose
\(\mathbb E_\mu A^2\le J\) for every complete old layout; the
elementary choice \(J=(K+1)^2\) always works here. Define

\[
 \begin{aligned}
 \lambda_*&=\frac{p-2}{p-1},& c_*&=\frac1{\lambda_*(1-\delta)},\\
 t_k&=\frac{p^{-k}}{p-1},&
 \varepsilon_k&=p^{-k}\left(\frac{2k+3}{p-1}
                                      +\frac2{(p-1)^2}\right).
 \end{aligned}
\]

For every extension from \(k\) to \(H\ge k\),
\(\lambda_k-\lambda_H\le t_k\) and
\(b_H-b_k\le Kt_k\). Both arguments of the maximum in the
denominator of (CS4) decrease, and its decrease is at most
\((K+1)t_k\). Its reciprocal never exceeds \(c_*\). Therefore

\[
 0\le c_H-c_k\le c_*^2(K+1)t_k,\qquad
 0\le\beta_H-\beta_k\le
                  \frac{Kt_k}{\lambda_*^2(1-\delta)}. \tag{CS9}
\]

For the second inequality, first bound
\(b_H/\lambda_H-b_k/\lambda_k\) by
\(Kt_k/\lambda_*+Kt_k/((p-1)\lambda_*^2)
=Kt_k/\lambda_*^2\), and then use the Lipschitz constant
\((1-\delta)^{-1}\) of the positive-part charge function.
For arbitrary independent old test loads, Cauchy--Schwarz gives
\(\mathbb E A_eA_f\le J\). Counting the \(2n+1\) ordered
exponent pairs with maximum \(n\) yields

\[
 \mathbb E Q_k\le a_pJ,\qquad
 0\le\mathbb E(Q_H-Q_k)\le J\varepsilon_k.
\]

Use the positive decomposition
\(c_HQ_H-c_kQ_k=c_H(Q_H-Q_k)+(c_H-c_k)Q_k\). Taking maxima gives
the effective enclosure

\[
 \boxed{M_k\le\sup_{H<\infty}M_H\le M_k+E_k},\qquad
 E_k=fJ\left[c_*\varepsilon_k+c_*^2(K+1)a_pt_k\right]
             +\frac{WKt_k}{\lambda_*^2(1-\delta)}.     \tag{CS10}
\]

The lower side follows by extending any maximizing old layouts;
all added terms and changes in (CS9) are nonnegative. The upper side
holds for each such extension before maximizing. For finite old period
and rational source data, \(M_k\) is a finite rational optimization,
and \(E_k\to0\). This is an algorithm for an arbitrary prescribed
precision, not a claim that a finite height attains the supremum or
that the finite optimization has been evaluated on PG1. Unlike a test
tail estimate, (CS10) also truncates the varying actual forbidden
families. The hypothesis \(K\le p-3\) and fixed old probability
are essential to the exact reduction used here. No bound on the
unrestricted old inventories or resulting \(\Gamma_{19}\) follows.

<a id="complete-test-tails-for-one-arbitrary-actual-forbidden-family"></a>
### Complete test tails for one arbitrary actual forbidden family

A separate estimate applies without the small-inventory hypothesis,
provided the actual forbidden family is fixed. Let \(P\) be its
minimal pure-prefix antichain, \(B_x\) its actual mixed union, and
\(\lambda\) Haar prefix mass. Put \(s=\lambda(P^c)>0\),
\(m=\lambda|_{P^c}/s\), and take the row coefficients \(g_x,h_x\)
from (PO1). For any prefix \(C\), write
\(R_F(C)=\lambda(C\setminus F)\). The exact kernel table is

\[
 K_x(C)=\frac{(g_x-h_x)R_P(C)+h_xR_{P\cup B_x}(C)}s.   \tag{KT1}
\]

Both coefficients are nonnegative. Reducing each actual union to
its minimal forbidden-prefix antichain makes (KT1) a finite residual
calculation as in (P13.2); forbidden descendants deeper than the query
remain in the calculation. This computes actual nonnegative pair
masses directly rather than assigning separate signed tail bounds.

Let \(D_0\) be the maximum actual forbidden depth. Above it extend
the actual law by uniform independent suffixes; below it use its
marginals. These consistent finite laws define every expectation
below. A complete test through \(H\) retains one independently chosen
CRT class per original label \(dp^e\), \(d\mid M\),
\(0\le e\le H\). If \(H>D_0\), these are auxiliary tests on
the extended period. Their supremum is an upper domain for the
original finite-period tests; a lower bound for the extended supremum
is not a lower bound for the original finite-period maximum.

Suppose \(K_x(C_e)\le c(x)p^{-e}\) for every positive-depth
prefix, and \(\mathbb E_\mu[cA^2]\le G_c\) for every complete
old layout. One may always use \(c=g/s\). For any test through
\(H\ge k\), retain its original labels through \(k\), with load
\(U=L_{\le k}\). Expanding the actual nonnegative pair masses gives

\[
 0\le\mathbb E L_H^2-\mathbb E U^2\le G_c\varepsilon_k.
                                                               \tag{KT2}
\]

Indeed, a pair of exponents \(e,f\) has mass at most
\(p^{-\max(e,f)}\mathbb E[cA_eA_f]\), bounded by
\(p^{-\max(e,f)}G_c\) by weighted Cauchy--Schwarz. Sum precisely
the pairs with maximum above \(k\). This is the complete-tail
application of the existing
`PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le`
pair estimate; no new Lean wrapper is needed. Consequently the exact
finite maximum \(\Gamma_k\), computed with the entire actual
forbidden family, satisfies

\[
 \Gamma_k\le\sup_{H<\infty}\Gamma_H
                  \le\Gamma_k+G_c\varepsilon_k.       \tag{KT3}
\]

Here only tests are truncated. Dropping deeper forbidden prefixes
would change the actual kernel and is not justified by (KT2).

A correlated finite support function can sharpen this tail. Take
\(k\ge D_0\), fix one truncated test \(U\), and let \(V\)
range over the finite set of loads

\[
 V(x,a)=\sum_{d\mid M}\mathbf1_{x=u_d\bmod d}
                        \mathbf1_{a=v_d\bmod p^k}.
\]

Each pair \((u_d,v_d)\) is chosen globally for its original label,
before sampling \((x,a)\); these are not pointwise choices in each
old row. For the actual joint law \(\nu_k\), define

\[
 b(V)=\mathbb E_{\nu_k}UV,\quad s(V)=\mathbb E_{\nu_k}V^2,
 \qquad h_U(t)=\max_V\{2b(V)+ts(V)\}.
\]

Uniformity after \(k\) implies that, for any independent projected
layers \(V_1,\ldots,V_n\), the largest extra energy equals

\[
 2\sum_{j=1}^np^{-j}\langle U,V_j\rangle+
 \sum_{j,l=1}^np^{-\max(j,l)}\langle V_j,V_l\rangle.  \tag{KT4}
\]

The intersection cap supplies the upper bound. It is simultaneously
attained by setting every additional test suffix to zero, leaving its
old residue and first \(k\) digits unchanged. Equal first prefixes
then have compatible suffixes, while unequal first prefixes still
have empty intersection. This alignment applies only beyond the
complete actual forbidden depth; it does not identify the independent
\(V_j\)'s or their old layouts.

Let \(T(U)\) be the supremum of (KT4) over all finite lengths and
allowed layers. Repeating one layer gives the lower bound below;
\(2\langle V_j,V_l\rangle\le s(V_j)+s(V_l)\) gives the upper:

\[
 \frac{h_U((p+1)/(p-1))}{p-1}\le T(U)
 \le\sum_{j\ge1}p^{-j}h_U\left(j+\frac1{p-1}\right)
 \le G_c\varepsilon_k.                              \tag{KT5}
\]

For the last step use
\(\max_V b(V)\le(k+1)p^{-k}G_c\) and
\(\max_V s(V)\le p^{-k}G_c\), proved by the same original-pair
expansion as (KT2). Maximizing \(\mathbb E U^2\) plus a chosen
side of (KT5) must keep the same \(U\) in both terms. Repeating
one \(V\) is a lower construction, not a proved optimizer.

For rational source data, \(h_U\) is a finite upper envelope of
rational lines. If \(S=\max s(V)\) and
\(b_* =\max\{b(V):s(V)=S\}\), choose an integer \(N\ge1\)
at least every
\(2(b(V)-b_*)/(S-s(V))-1/(p-1)\) with \(s(V)<S\).
For \(j\ge N\), the line \((b_*,S)\) dominates, so the remaining
sum in (KT5) is exactly geometric. With \(r=1/p\) and
\(a=2b_*+S/(p-1)\), it is

\[
 \sum_{j=N}^{\infty}r^j(a+Sj)
 =r^N\left[\frac a{1-r}
       +S\left(\frac N{1-r}+\frac r{(1-r)^2}\right)\right].
\]

The finite support enumeration or a valid dominance certificate must
cover every realizable \(V\); a sampled support function gives no
upper certificate. These formulas give a complete-tail optimization
framework for a fixed actual family. Uniform maximization over all
forbidden families with unrestricted old inventories remains unresolved.

<a id="original-label-coloring-extends-the-exact-comb-reduction"></a>
### Original-label coloring extends the exact comb reduction

The small total inventory condition in (CS2) has a useful sufficient
replacement. At each depth \(e\), form the graph on the original
nonunit old cofactors, joining \(d,d'\) when
\(\mu(C_{d,e}\cap C_{d',e})>0\). Suppose it has a proper coloring
with at most \(q\le p-3\) colors. Each coloring is chosen globally
before sampling the old point; it may vary with depth. Assign its colors
to the spokes of (CS2), retaining every original modulus \(dp^e\).
Same-color old cylinders are disjoint almost everywhere, and different
depths leave the spine at different digits. Thus

\[
 R_e\le q\quad\mu\text{-a.e.},\qquad
 b_H=\sum_{e=1}^Hp^{-e}R_e,\qquad
 \max\mathbb E[fL_H^2+W\beta]
 =\mathbb E_\mu[f(A_0^2+c_HQ_H)+W\beta_H].             \tag{CC1}
\]

The coefficients are exactly (CS4). The same union and pair-cap proof
gives the upper bound for arbitrary alternative current residues;
the colored comb attains it. The complete test layouts remain independent
of the forbidden layouts. The construction is a sufficient condition,
not a characterization of every exact arrangement.

This permits arbitrarily many original labels. On the uniform higher-3
lift of PG1, the cylinders \(2+3^{a-1}\bmod3^a\),
\(3\le a\le A\), are positive and pairwise disjoint: for \(a<b\),
the latter cylinder reduces to \(2\bmod3^a\). They use one color
for every \(A\). Other old divisors can take cylinders disjoint from
the old support. Their labels still occur in the complete test domain.
If \(J\) bounds every complete old test square for that full period,
(CS9)--(CS10) hold with \(q\) replacing \(K\):

\[
 E_k=fJ[c_*\varepsilon_k+c_*^2(q+1)a_pt_k]
       +\frac{Wqt_k}{\lambda_*^2(1-\delta)}.           \tag{CC2}
\]

This follows from \(R_e\le q\) in each tail estimate. It does not
replace \(J\) by a bound for only the colored or low-power labels.
For a supremum over colorable families and \(k\ge1\), repeating any
already admissible properly colored old forbidden layout preserves
the domain and supplies the lower truncation bound.

For a palette assignment that is not proper, put
\(N_{e,j}=\sum_{d:\,\mathrm{color}_e(d)=j}\mathbf1_{C_{d,e}}\),
\(U_e=\sum_j\mathbf1_{N_{e,j}>0}\), and
\(D_e=R_e-U_e=\sum_j(N_{e,j}-1)_+\). Its legal comb has actual
mixed mass \(b_1=\sum_ep^{-e}U_e\), while the counting relaxation
has \(b_0=\sum_ep^{-e}R_e\). For fixed \(\lambda=\lambda_H\),
write

\[
 \ell_< =\min(b_0,\delta\lambda)-\min(b_1,\delta\lambda),\qquad
 \ell_> =(b_0-\delta\lambda)_+-(b_1-\delta\lambda)_+.
\]

Their sum is \(b_0-b_1\). Subtracting the actual cost from the
counting-relaxation cost gives exactly

\[
 \mathbb E_\mu\left[
 \frac{fQ_H\ell_<}
 {(\lambda-\min(b_0,\delta\lambda))
  (\lambda-\min(b_1,\delta\lambda))}
 +\frac{W\ell_>}{\lambda(1-\delta)}\right].          \tag{CC3}
\]

This is an identity for that assigned comb, not an assertion that it
maximizes the unrestricted current-prefix problem. It locates losses
below and above the clipping threshold on the same actual old rows.

<a id="a-genuine-seventeen-step-collision-with-an-exact-charge-correction"></a>
### A genuine seventeen-step collision with an exact charge correction

Use PG1 with denominator \(D=1000000007\), and independently uniform
coordinates modulo \(121\) and \(169\) conditional on nonzero
roots modulo \(11\) and \(13\). This is an actual old law for the
eleven PG1 classes and the four pure zero classes modulo
\(11,121,13,169\); its old period is \(6441435\).
The old cylinders
\(C_3=(2\bmod3),C_5=(4\bmod5),C_7=(4\bmod7)\)
have empty triple intersection on this support and pair masses

\[
 \mu_0(C_3\cap C_5)=\frac{106787589}{D},\qquad
 \mu_0(C_3\cap C_7)=\frac{81877150}{D},\qquad
 \mu_0(C_5\cap C_7)=\frac{28161457}{D}.                \tag{CC4}
\]

For each \(d\in\{3,5,7\}\) and
\(t\in\{1,11,13,121,143,169\}\), retain the original
cofactor \(dt\), with old condition \(C_d\) and residue \(1\)
modulo \(t\). These eighteen old events form \(K_{18}\), although
no old point activates more than twelve of them. Add pure zero modulo
\(17\) and one class of each original modulus \(17dt\), with
arbitrary current roots. This is a family of thirty-four distinct odd
moduli, with period \(109504395\). The sixteen surviving current
roots cannot make all eighteen labels pairwise disjoint on old support.

Let \(E_{ij}\) require \(C_i\cap C_j\) and the common deep slice
\(z_{11}=1\bmod121,z_{13}=1\bmod169\). These three events are
disjoint and each has mass at least
\(m=28161457/(17160D)\). If \(S_i\) is the set of nonpure
roots assigned to the six labels in group \(i\), set
\(d_{ij}=12-|S_i\cup S_j|\). With
\(D_i=6-|S_i|\), inclusion-exclusion gives

\[
 \sum_{i<j}d_{ij}=2\sum_iD_i+\sum_{i<j}|S_i\cap S_j|
 \ge18-\left|\bigcup_i S_i\right|\ge2.
\]

This also permits repeated roots within a group or assignments to the
deleted pure root. At \(\delta=7/15\), the ideal row charge on
\(E_{ij}\) is \(17/32\), and losing \(d_{ij}\) roots reduces
it by \(\min(15d_{ij},68)/128\). These are nonnegative integer
deficits whose sum is at least two; consequently their three charge
reductions sum to at least \(30/128\). Every current-root assignment
therefore satisfies

\[
 \mathbb E\beta_{\rm actual}
 \le\mathbb E\beta_{\rm count}-\Delta,\qquad
 \Delta=\frac{15m}{64}
       =\frac{28161457}{73216000512512}.              \tag{CC5}
\]

The bound is attained. Give one shared root to the pair
\((5\cdot121,7\cdot169)\), another to
\((5\cdot169,7\cdot121)\), and distinct roots to the other
fourteen labels. Only \(E_{57}\) loses roots, exactly two there.
The resulting exact maximum charge is
\(201659592817/1098240007687680\), compared with the counting
upper value \(12630125917/68640000480480\).

The minimum mean union-count loss is exactly \(2m\). To see the
lower bound, move pure-root labels to surviving roots and split groups
until sixteen roots are occupied; neither operation decreases any
row's union. A partition of eighteen labels into sixteen nonempty
groups has one triple or two disjoint pairs. Each pair intersection
has mass at least \(m\); a triple contributes its three pair masses
minus its triple mass, hence at least \(2m\). The displayed two
pairs attain that loss. There are precisely \(816+9180=9996\)
such partitions, all included in the exact verifier.

For this fixed inventory and these fixed old cylinders, \(W\Delta\)
may be subtracted from the union/cap joint upper functional for every
test and every \(f,W\ge0\). Optimal charge does not assert optimal
test square. Every row has density at most \(3/4\), so a pointwise
near-full-union overlap correction requiring density greater than
\(15/16\) detects none of this gain.

The graph alone supplies no positive height-uniform gap. For
\(N\ge0\), replace every multiplier \(t\) by \(11^Nt\),
preserving its compatible residue \(1\). Keep the fifteen old
forbidden classes and lift the old law uniformly through height
\(N+2\) at \(11\). The actual full period is now
\(315\cdot11^{N+2}\cdot13^2\cdot17\). The graph is still
\(K_{18}\), the maximum row activity is still twelve, and the
same two pairs attain

\[
 \min\mathbb E(R-U)=2m\,11^{-N},\qquad
 \min\mathbb E(\beta_{\rm count}-\beta_{\rm actual})
       =\Delta\,11^{-N}.                            \tag{CC6}
\]

Indeed the three common deep pair events now require
\(z_{11}=1\bmod11^{N+2}\); their masses scale by \(11^{-N}\).
Every pair intersection still has mass at least \(m11^{-N}\),
and the two chosen pairs intersect only on the smallest deep event.
The preceding lower and upper constructions apply unchanged. This
does not say that all other intersection masses scale equally.
Thus class count, row activity and unweighted overlap graph leave a
genuine quantitative gap: the intersection masses must be retained.

`verify_pg1_color_collision.py` checks the adjacent certificate with
exact arithmetic: all9996 partitions,55 reduced source states,
675 weighted old CRT representatives and10800 literal current-point
checks. It reconstructs the same actual probability, original residues
and normalized kernels. The coloring extension and (CC6) are ordinary
arguments above; the certificate covers the \(N=0\) instance.

<a id="repeating-one-diagonal-old-layout-does-not-maximize-the-joint-cost"></a>
### Repeating one diagonal old layout does not maximize the joint cost

Even within the low315 comb domain, identifying the forbidden and
test layouts loses possibilities. Fix \(p=17,T=8,f=59/45,W=483\),
and let \(A,C\) be independent complete old twelve-label loads,
each repeated at every current depth; \(C\) includes the unit term.
The limit of (CS6) is

\[
 \Phi(A,C)=\mathbb E_\mu\left[
 \frac{59}{45}\left(1+\frac{25}{128}
             \frac{16}{16-\min(C,8)}\right)A^2
 +\frac{483}{8}(C-8)_+\right].                      \tag{JL1}
\]

The existing complete twelve-label oracle enumerates every independent
old residue choice for a common load \(B\), not only coherent centers.
Round each whole weighted point cost upward at scale32768 and apply
that oracle. It gives the rigorous bound

\[
 \max_B\Phi(B,B)\le
 \frac{746858239119517}{32768000229376}
 =22.792304501083659\ldots.                           \tag{JL2}
\]

The maximum's rounding gap is less than
\(75/32768000229376\). This also bounds every finite-height
family with one such repeated common old layout and arbitrary current
prefixes. In fact \(s_H\le1/16\) and
\(a_H=\sum_{e=1}^H(2e+1)17^{-e}\le25/128\).
Both denominator branches of
\(c_H(B)=1/\max\{1-Bs_H,(1-s_H)8/15\}\) decrease with
\(s_H\), while \((B-1)s_H/(1-s_H)\) increases. They are
positive for \(1\le B\le12\). Thus the finite joint cost is
at most (JL1) with \(A=C=B\), and (CS6) covers arbitrary current
prefix choices for those old layouts.

Now choose the forbidden old center257 and test old center47:
\(C(x)=\sum_{d\mid315}\mathbf1_{x=257\bmod d}\) and
\(A(x)=\sum_{d\mid315}\mathbf1_{x=47\bmod d}\).
The actual height-three comb has47 distinct forbidden moduli,
48 complete test labels and period1547595. Its exact joint cost is

\[
 \frac{3843229007141107789887039465169}
      {168205257902111866972725489300}
 =22.848447516294048\ldots>\max_B\Phi(B,B).           \tag{JL3}
\]

Its limit is \(74868660065651/3276000022932\); the full
omitted tail difference is
\(440164771212699691855269553/84102628951055933486362744650\).
`verify_pg1_joint_layout_gap.py` reconstructs the directed full-domain
upper bound and all345450 supported CRT/kernel point evaluations for
the finite witness. Both the forbidden and test tails are retained.

This refutes domination by a single repeated diagonal old layout.
It does not compare against the larger class of common layouts
\(A_e=C_e\) varying independently with depth, nor optimize arbitrary
higher old powers or the later-prime continuation. Together with
(CC5)--(CC6), it identifies actual joint information required by the
next bound; no new global \(\Gamma\) improvement or unrestricted
noncoverage theorem follows. These are ordinary mathematical arguments
and exact experimental certificates, not new Lean conclusions.
