# Shared old coordinates give a phase-filtered collision bound

[Source](../350-399/388-source-global-substitution-collision-moment.md) · [Column bound](../600-649/844-collision-moment-needs-cofactor-packing.md) · [Charge scope](847-selector-charge-is-weaker-than-pair-demand.md)

In the common \(r<s\) substitution source, only equal old-cofactor phases
contribute to a same-column conditional replica moment. Comparable-class
disjointness then forces different original \(s\)-prefixes. This improves
the column coefficient by \((r-1)/(s-1)\). For \(r=5,s=7\), the resulting
ordered same-column contribution under old Haar measure is
\[
 R_{\mathrm{same}}
 <\frac5{306}\sum_{m\in\mathcal M}\frac1m.
 \tag{1}
\]
If all those cofactors are powers of \(3\), it is less than \(5/204\),
with no exponent cutoff. This bounds one part of the labelled second-moment
majorant. Diagonal terms, cross-column terms, the actual distorted old law,
and a strict total noncoverage budget remain separate obligations.

[Report 849](849-actual-unions-admit-sharp-common-tree-moment-transport.md)
gives a direct comparison for the complete actual union under any fixed old
law independent of the common tree. It avoids a separate cofactor-pair
majorant, while retaining the original union moments as required inputs.

## 1. Reuse the conditional moment with its actual common coordinate

The published input is
[BBMST, *The density of the uncovered set*, Theorem 3.2 and Lemma 3.6](https://arxiv.org/pdf/1811.03547v1).
Its tuple estimate uses the least common multiple of old cofactors. The
following phase-retaining form is an application of that estimate and finite
conditioning, not a new general probability theorem.

Fix a prime block \(p^B\), an old coordinate \(X\) on a period \(M\) coprime
to \(p\), and one law \(\nu\) of \(X\). A labelled original has old modulus
\(m_h\mid M\), old phase \(a_h\), new depth \(1\le b_h\le B\), and new
prefix \(t_h\bmod p^{b_h}\). Write \(C_h=\{X\equiv a_h\pmod{m_h}\}\) and
let \(D_h\) be that new prefix cylinder. For
\[
 B_{\mathrm{bad}}=\bigcup_h(C_h\times D_h),\qquad
 \alpha(x)=H_p\!\left(\bigcup_{h:x\in C_h}D_h\right),
\]
two conditionally independent Haar new words \(Y,Y'\), sharing the same
\(X\), give exactly
\[
 \mathbb E_\nu\alpha(X)^2
 =\Pr\bigl((X,Y)\in B_{\mathrm{bad}},(X,Y')\in B_{\mathrm{bad}}\bigr).
 \tag{2}
\]
The labelled load \(L(x)=\sum_h p^{-b_h}\mathbf1_{C_h}(x)\) majorizes
\(\alpha(x)\). Consequently
\[
 \mathbb E_\nu\alpha^2\le\mathbb E_\nu L^2
 =\sum_{h,g}p^{-b_h-b_g}\nu(C_h\cap C_g). \tag{3}
\]
Under old Haar, the last probability is zero if the old phases disagree
modulo \(\gcd(m_h,m_g)\), and is \(1/\operatorname{lcm}(m_h,m_g)\)
otherwise. No independence of these old events is asserted.

For a single output column \(mp^b\) with distinct full phases, let \(k_t\)
count the distinct new prefixes associated with old residue \(t\bmod m\).
Then its union moment is exactly
\[
 M_{\mathrm{col}}^{(2)}
 =p^{-2b}\sum_{t\bmod m}\nu(X\equiv t\bmod m)\,k_t^2.
 \tag{4}
\]
In particular, old Haar gives \(\sum_tk_t^2/(mp^{2b})\), not
\((\sum_tk_t)^2/(m^2p^{2b})\). The latter redraws the old coordinate
independently for each complete endpoint.

Across different columns, (3) is generally an inequality for the actual
union: identical or nested new prefixes can overcount. It is an exact
identity only for the labelled load. Also this is a whole prime-power block
exposure, as in the cited BBMST interface. If the history already includes
the first \(b-1\) digits of \(p\), the replicas share those digits as well.
Conditional on a fixed exposed prefix \(v\), two depth-\(b\) labels have
factor \(p^{-2}\mathbf1_{\{v\equiv t_h\equiv t_g\pmod{p^{b-1}}\}}\).
After averaging that shared prefix under Haar, this becomes
\(p^{-(b+1)}\mathbf1_{\{t_h\equiv t_g\pmod{p^{b-1}}\}}\).

## 2. Comparable disjointness improves the relevant collision moment

Use report 388's one source
\(\omega=(u,\theta)\), where \(u\) is uniform on the safe \(r\)-coordinate
set of density \(\eta_r>(r-2)/(r-1)\), and \(\theta\) is the independent
common compatible rooted-tree embedding. Write original labels as
\[
 d=r^a s^b m,\qquad \gcd(m,rs)=1.
\]
Assume numerical distinctness and comparable-class disjointness, as supplied
by the stated EB1 hypotheses. Let \(N^{=}_{b,m}(\omega)\) count the unordered
surviving pairs in this column whose original phases modulo \(m\) agree.
This is a subcount of report 844's \(N_{b,m}\).

Take a pair with \(a<a'=k\) and agreeing \(m\)-phases. If its safe-coordinate
constraints are compatible and its original \(s^b\)-prefixes were equal, the
phases would agree modulo \(r^as^bm\). The deeper original class would be
contained in the shallower one. Comparable disjointness therefore forces
different \(s^b\)-prefixes whenever such a pair can survive. In particular
\[
 N^{=}_{0,m}=0. \tag{5}
\]
For \(b\ge1\), if the two prefixes have \(\ell<b\) common initial digits,
report 388's exact common-tree kernel is
\[
 \kappa_\ell=
 \left(\frac rs\right)^\ell
 \frac{r(r-1)}{s(s-1)}
 \left(\frac rs\right)^{2(b-\ell-1)}
 \le \frac{r-1}{s-1}\left(\frac rs\right)^b. \tag{6}
\]
The bound is attained at \(\ell=b-1\), so its factor cannot be improved
solely by knowing that the prefixes differ.

For each larger exponent \(k\), at most \(k\) earlier exponents can pair
with its unique original label in the column. Their safe-coordinate
probabilities are at most \(r^{-k}/\eta_r\). Summing (6) on this same law,
and reusing \(\sum_{k\ge1}kr^{-k}=r/(r-1)^2\), proves
\[
 \boxed{\mathbb E_\omega N^{=}_{b,m}
 <\frac{r}{(r-2)(s-1)}\left(\frac rs\right)^b
 \quad(b\ge1).} \tag{7}
\]
For \(5<7\), the coefficient is \(5/18\), in place of the unfiltered
\(5/12\) in report 844. Pairs with different old \(m\)-phases contribute
zero to the corresponding same-column term of (3); they need not have zero
probability as numerical collision events on \(\omega\).

## 3. Complete heights and one actual old law

Let \(\mathcal M\) be the finite set of distinct cofactors that occur.
For each fixed source outcome use old Haar on the common cofactor period.
The ordered same-column off-diagonal part of the labelled majorant (3) is
\[
 R_{\mathrm{same}}
 :=2\sum_{m\in\mathcal M}\sum_{b\ge1}
 \frac{\mathbb E_\omega N^{=}_{b,m}}{m r^{2b}}.
 \tag{8}
\]
The actual family has finite heights; completing the nonnegative sum with
(7) gives
\[
 \boxed{R_{\mathrm{same}}
 <\frac{2r}{(r-2)(s-1)(rs-1)}
     \sum_{m\in\mathcal M}\frac1m.} \tag{9}
\]
If \(\mathcal M\) is empty the contribution is zero instead; the strict
inequality is stated for a nonempty palette. For \(r=5,s=7\), (9) is (1).
For \(\mathcal M\subseteq\{3^c:c\ge0\}\), geometric completion gives
\(\sum_{m\in\mathcal M}1/m<3/2\), and hence
\[
 R_{\mathrm{same}}<5/204. \tag{10}
\]

A distorted old law must be retained as one joint kernel
\(\mu(d\omega)\nu_\omega(dx)\). The exact same-column expression then is
\[
 2\sum_{b,m}r^{-2b}\!
 \sum_{\substack{h<g\text{ in }(b,m)\\a_h\equiv a_g\pmod m}}
 \mathbb E_\omega\!\left[
 \mathbf1_{\{h,g\text{ survive}\}}
 \nu_\omega(X\equiv a_h\bmod m)\right]. \tag{11}
\]
If this one kernel satisfies a uniform cylinder cap
\(\nu_\omega(X\equiv t\bmod m)\le\beta_m\) for every relevant
\(\omega,t,m\), the proof of (9) applies with \(\sum_m\beta_m\) in place of
\(\sum_m1/m\). Marginal old Haar, without conditional independence or these
caps, does not justify replacing the factor inside (11) by \(1/m\).

## 4. No uniform conversion from independently redrawn endpoints

The cofactor discrepancy can be arbitrarily large within literal finite
odd, distinct, divisor-closed, comparable-disjoint families. For a prime
\(m>7\), use
\[
 D=\{3,5,7,m,35,5m,7m,35m\}.
\]
Give every prime singleton phase zero. Specify the other classes by their
CRT coordinates:
\[
\begin{array}{c|ccc}
 d&\bmod5&\bmod7&\bmod m\\ \hline
35&2&3&-\\
5m&1&-&2\\
7m&-&1&1\\
35m&1&2&1
\end{array}
\]
All comparable pairs disagree on a common constrained coordinate. The safe
\(5\)-coordinate is uniform on \(\{1,2,3,4\}\).
The pair \(7m,35m\) survives exactly when \(u=1\) and the common five-child
subset of seven contains both children \(1,2\). Thus
\[
 \Pr(\text{pair survives})=\frac14\frac{5\cdot4}{7\cdot6}
 =\frac5{42}. \tag{12}
\]
It has equal old \(m\)-phase and distinct new output \(5\)-phases. Its
ordered contribution to (8) is \(1/(105m)\), whereas the corresponding
ordered term from independently redrawing full endpoints is
\(1/(105m^2)\). Their ratio is exactly \(m\).

Thus no universal constant converts the latter pair contribution to the
former under these local structural conditions. At \(m=11\), the literal
residues in the displayed modulus order are
\(0,0,0,0,17,46,1,331\). The families are not whole covers: a point avoiding
the four prime singletons and with \(m\)-residue outside \(\{0,1,2\}\)
and \(5\)-residue \(1\) avoids every listed class. They supply no EB1
counterexample and do not refute an additional whole-cover theorem.

## 5. Scope and reusable verification

The source expectation in (7)--(11) is never optimized separately by pair
or cofactor. Nevertheless, the fact that numerical collision events cover
\(\Omega\) does not make \(N^{=}\) positive everywhere: equal numerical
moduli can have incompatible old phases. Nor does a bound on (8) bound the
full (3). Its cross-column terms retain both actual old-phase compatibility
and their least-common-multiple weights.

Using these estimates in BBMST still requires a legal prime-block order,
the corresponding full-history old law, all remaining tuple contributions,
and a strict total budget. In particular, a cofactor containing primes later
than \(r\) is not automatically an old coordinate at the \(r\)-stage.
No unrestricted noncoverage conclusion follows from (10).

The [exact checker](../../../frontier/cover-geometry/source-global-collision-moment/conditional_replica.py)
and [data](../../../frontier/cover-geometry/source-global-collision-moment/conditional_replica.json)
compare literal finite two-replica counts, CRT tuple majorants, and the common
source pullbacks, including nonuniform old laws and nested new cylinders.
They test the finite interfaces; (7)--(11) are ordinary deductions from the
source hypotheses and published moment machinery, without a new Lean check.

The saved fixtures include 7 generic models, 420 common source maps,
418,380 literal pullback checks, and 281,274 conditional replica states.
Replay from the repository root with
`python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/source-global-collision-moment/conditional_replica.py --check`.

## 6. Cross-column tree bounds retain the original divisibility order

Write \(t=r/s\) and \(\gamma=(r-1)/(s-1)\). For two original tree
prefixes of depths \(b\le c\), the common-tree calculation in report 388
has the following unequal-depth form. If the short prefix is an initial
segment of the long one, including equality, their simultaneous survival
probability is \(t^c\).
Otherwise, if they split after \(\ell<b\) common digits, it is
\[
 K=\gamma t^{b+c-\ell-1}\le\gamma t^c. \tag{13}
\]
This follows by multiplying the common-prefix factor, the one shared
two-child selection factor, and the two remaining branch factors. Equality
in the bound occurs at \(\ell=b-1\).

If two distinct originals have comparable numerical moduli, and their safe
\(r\)-constraints and old cofactor phases are compatible, comparable-class
disjointness excludes the ancestor case. Thus (13) applies whenever
\(b\ge1\); at \(b=0\) no such compatible pair survives. For incomparable
original moduli the ancestor case can remain, so the factor \(\gamma\)
cannot be imposed on all cross-column terms.

Nor is (13) a negative-correlation bound relative to the two marginal
survival probabilities. For split prefixes the exact ratio is
\[
 \frac K{t^bt^c}=\gamma(s/r)^{\ell+1}. \tag{14}
\]
For \(r=5,s=7,\ell=1\), it is \(98/75>1\). Sharing a long selected
prefix can outweigh the negative dependence of two children at the split.
Each old-phase contribution still carries its actual joint cylinder
probability, with the LCM weight only under conditional old Haar.

## 7. A bounded actual union can have an unbounded labelled majorant

The general warning about excessive raw pair demand is already present in
the [original-owner budget construction](../../../../../../Library/Arith/lettlsun2008cosets.md#distinct-prime-lower-indices-can-carry-arbitrarily-large-raw-pair-capacity).
Here the same distinction can be computed exactly inside the common-tree,
divisor-closed model of Section 4. This is a source-specific application of
union and load moments, not a new general probability theorem.

Let \(\mathcal Q\) be any finite set of primes greater than seven. Take
the union of Section 4's original families over \(m=q\in\mathcal Q\),
sharing the four labels \(3,5,7,35\). Thus
\[
 D_{\mathcal Q}=\{3,5,7,35\}
  \cup\bigcup_{q\in\mathcal Q}\{q,5q,7q,35q\}. \tag{15}
\]
Every phase is exactly the one specified there. The \(4+4|\mathcal Q|\)
moduli are odd, distinct and divisor closed. Across different \(q\)'s,
no additional nonshared moduli are comparable, so comparable-class
disjointness is preserved as well.

Use the same independent safe \(u\in\{1,2,3,4\}\), common five-child
subset of seven, and old Haar law on \(3\prod_{q\in\mathcal Q}q\).
Put
\[
 S=\sum_{q\in\mathcal Q}\frac1q,\qquad
 T=\sum_{q\in\mathcal Q}\frac1{q^2},\qquad
 z=1-\prod_{q\in\mathcal Q}(1-1/q).
\]
For the old word \(x\), let \(N(x)=\sum_q\mathbf1_{\{x\equiv1\pmod q\}}\)
and \(Z(x)=\mathbf1_{\{N(x)>0\}}\). CRT independence under this one old
Haar law gives
\[
 \mathbb EN=S,\qquad \mathbb EN^2=S^2+S-T,\qquad \mathbb EZ=z.
 \tag{16}
\]
Write \(B_j\) for the indicator that child \(j\) belongs to the common
selected subset. Then \(\mathbb EB_j=5/7\) and
\(\mathbb EB_jB_k=10/21\) for \(j\ne k\).

First consider only the \(7q\) labels. Every one has the same original
seven-child prefix \(1\), hence the same new prefix when that child is
selected. Its full subfamily has
\[
 L(x)=B_1N(x)/5,\qquad \alpha(x)=B_1Z(x)/5.
\]
Consequently, averaging on that one joint source,
\[
 \mathbb EL^2=\frac{S^2+S-T}{35},\qquad
 \mathbb E\alpha^2=\frac z{35}<\frac1{35}. \tag{17}
\]
The ordered cross-cofactor part alone is \((S^2-T)/35\).

The entire depth-one output block, including the pure \(7\) label, has
the exact union and load
\[
 \alpha_u(x)=\frac{B_0+B_1Z(x)
       +\mathbf1_{\{u=1\}}B_2Z(x)+\mathbf1_{\{u=2\}}B_3}{5},
 \qquad
 L_u(x)=\frac{B_0+B_1N(x)
       +\mathbf1_{\{u=1\}}B_2N(x)+\mathbf1_{\{u=2\}}B_3}{5}.
 \tag{18}
\]
Distinct selected children have disjoint new cylinders, which justifies
the union expression. Expanding on this common source gives
\[
 \boxed{\mathbb E\alpha_u^2=\frac{19+43z}{420}<\frac{31}{210},
 \qquad
 \mathbb EL_u^2=\frac{19(1+S^2-T)+43S}{420}.} \tag{19}
\]
Euler's divergence of the sum of prime reciprocals makes the load moment
unbounded as \(\mathcal Q\) grows, while the union bound in (19) remains
fixed. The classical divergence is reused, not reproved; the pinned
Mathlib also supplies `Nat.Primes.not_summable_one_div` in
`Mathlib/NumberTheory/SumPrimeReciprocals.lean`.

These are local noncovers. CRT coordinates \(1\bmod3\), \(1\bmod5\),
\(4\bmod7\), and \(3\bmod q\) for every \(q\in\mathcal Q\) avoid all
listed classes. Neither EB1 minimality nor a legal increasing-prime BBMST
exposure is supplied. The conclusion is precisely that the local
conditions do not give a uniform finite bound on the labelled majorant,
or a uniform comparison of that majorant with the actual union moment.
Its divergence does not rule out controlling the actual union. A useful
continuation must preserve shared-prefix unions or use an additional
whole-cover restriction that excludes this local obstruction.

For \(\mathcal Q=\{11,13\}\), the same checker gives
\(\mathbb EL_u^2=541/8580\) and
\(\mathbb E\alpha_u^2=1853/30030\). The \(7q\) subfamily gives
\(2/385\) and \(23/5005\), respectively. It checks all 84 common source
maps and 2,162,160 literal original-to-output membership comparisons;
the whole block and subfamily replica counts are kept separately in its
data. An independent direct enumeration of 300,300 shared-old replica
states agrees with these four values. These finite checks and the ordinary
deductions above are not new Lean verification.
