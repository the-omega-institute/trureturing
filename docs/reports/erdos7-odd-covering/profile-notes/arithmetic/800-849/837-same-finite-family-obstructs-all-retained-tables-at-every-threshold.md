# The same finite 53-original family obstructs every retained table at every threshold

For the explicit finite family of [Report 826](826-one-finite-pure-family-obstructs-every-kernel-in-the-h16-comparison.md), the capacity-aware complete-head comparison is negative for every nonzero first-colour K8 table and every admissible real threshold, even with zero tail debit. The quantitative statement is

$$
\frac{H_{A,4}(h;u)+H_{C,4}(h;u)}2
\ge (28-h)L_4(u)
 +\frac{500}{501}\left(\frac{28-h}{2000}
             +\frac{2}{401397328829}\right)M_4(u),
\qquad 0\le h\le28.
$$

Here $L_4$ is [Report 820](820-queried-colour-capacities-sharpen-complete-head-and-moment-bounds.md)'s capacity-aware bound evaluated at this one finite source, with the same selected phases and inherited complete inventory; it is not the infinite-source cap matrix evaluated without change. The hinges use complete query heights under the actual retained finite-source law. This is an ordinary proof using the exact certificate in Report 835. No new optimizer, integration or Lean verification is used.

The result is a method obstruction for one finite actual family, not a covering example or an Erdős #7 resolution. The integer 4 avoids that family, as already established in Report 826. Sharper actual-family loss inventories, deeper retained states and different source or survivor comparisons remain outside the conclusion.

## Existing ingredients and the new bridge

[Report 809, section 5](809-two-colour-core-obstructs-every-fixed-weight-full-box-certificate.md) gives finite combs approaching the source C and a compactness argument for a fixed-weight comparison. [Report 812, FS21](812-fractional-categorical-kernels-admit-explicit-finite-pure-families.md) supplies total-variation transport of common-colour envelopes. [Report 816, section 3](816-actual-pure-source-cells-and-a-finite-three-kernel-gap.md) proves actual finite realization of the combs. Report 826 adds the shallow-capacity factors and one uniform depth-four comparison for every legal table, but only for its specified h16 full-source-hinge criterion.

[Report 831, sections 1–3](831-clean-root-query-phases-admit-exact-incidence-states-but-small-prefix-tails-remain-too-large.md) identifies the finite and infinite combs on one source space, their common clean roots and complete-height query laws. [Report 835](835-one-scaled-common-centre-dual-excludes-every-threshold-for-all-retained-tables.md) proves the following inequality on the infinite-comb source, uniformly for every nonnegative table $u$ on the 249 allowed K8 cells:

$$
\frac{H_{A,\infty}(h;u)+H_{C,\infty}(h;u)}2
\ge (28-h)\left(L_\infty(u)+\frac{M_\infty(u)}{400}\right)
       +\delta M_\infty(u),
\quad
\delta=\frac{2}{401397328829},\quad 0\le h\le28.
$$

The bridge below uses one-sided measure domination and the proportional $1/400$ reserve. It transfers the complete-height inequality to the already specified depth-four family without estimating an unbounded hinge by total variation and without choosing a depth after seeing the table.

## The actual family and its source laws

Keep $Q=(5,7,11,13,17,19,23)$ and the 25 literal originals from Report 826, written as $(\text{modulus},\text{residue})$:

```
(3,0), (9,1), (15,10), (21,7), (45,31),
(33,22), (35,0), (39,13), (63,49), (51,34),
(57,19), (55,0), (105,70), (75,25), (69,46),
(65,0), (99,22), (77,0), (85,0), (117,13),
(95,0), (165,55), (91,0), (147,49), (225,175).
```

At 5 add $2\bmod5$ and $3+5^{j-1}\bmod5^j$ for $j=2,3,4$. At every other $q\in Q$ add $1\bmod q$ and $2+q^{j-1}\bmod q^j$ for $j=2,3,4$. Report 826 establishes the disjoint local pure cylinders, all 53 globally distinct odd nonunit numerical moduli, and the survivor 4. These facts are reused without another carrier enumeration.

Let $S_{q,4}$ be the pure survivor in the $q$-adic coordinate, and let $S_{q,\infty}$ be obtained by extending the same disjoint comb to every higher depth. Their Haar masses are

$$
s_{q,4}=\frac{q-2+q^{-4}}{q-1},
\qquad s_{q,\infty}=\frac{q-2}{q-1}.
$$

Their normalized laws are denoted $\lambda_{q,4}$ and $\lambda_{q,\infty}$. Define

$$
r_q=\frac{s_{q,\infty}}{s_{q,4}}
=\frac{q-2}{q-2+q^{-4}},\qquad r=\prod_{q\in Q}r_q>0.
$$

Both sources use the same five ternary leaves $(4,7,2,5,8)\bmod9$, the same Haar suffix above depth two, and the same nonnegative table $u$. The ternary weights are absorbed into $u$; every legal weighted retained kernel lies in this cone. The fixed phase-31 K8 mask is unchanged. The three mixed labels involving deeper nonternary digits are already contained in their selected shallower originals, as shown in Report 831, so no new selected-null constraint is created by the finite comb.

The two actual query centres use ternary leaf 5 for A and leaf 2 for C, root 0 at 5, root 3 at the other six primes, and zero higher digits. These roots are untouched by every finite or infinite pure comb in this construction. Their phases are fixed globally per numerical label; they do not depend on the source cell or on $u$.

## Complete-height hinge domination requires no truncation

Since $S_{q,\infty}\subseteq S_{q,4}$, their densities with respect to the same Haar measure give

$$
\lambda_{q,4}\ge r_q\lambda_{q,\infty}
$$

as measures. Taking products, keeping the same ternary law and multiplying by the same nonnegative table yields

$$
\nu_{u,4}\ge r\nu_{u,\infty}.
$$

Consequently, for each of the two globally fixed query loads and all $h\in[0,28]$,

$$
H_{X,4}(h;u)\ge r H_{X,\infty}(h;u),\qquad X\in\{A,C\}.
$$

This holds first for finite numerical query inventories and then for complete heights by monotone convergence. The inherited all-height cylinder bounds $C_q/q^e$, with $C_q=(q-1)/(q-2)$, bound the complete first moments by convergent geometric products at both sources. No finite original height is substituted for a query-height cutoff, and no total-variation bound is applied to an unbounded load.

## Capacity envelopes change, but their losses have the needed sign

Write $c_q=C_q/q$. At the infinite source the protected singleton colours have probability $c_q$; at depth four they have probability $r_qc_q$. The remaining colour has probability $1-n_qc_q$ at infinity and $1-n_qr_qc_q$ at depth four, where $n_5=2$ and $n_q=1$ otherwise. Thus, for every observed colour $c$,

$$
\pi_{q,4}(c)\ge r_q\pi_{q,\infty}(c).
$$

All colours are live at both sources. Report 826 UF8–UF9, equivalently Report 820's actual-source bounds, gives unchanged deep capacities and shallow factors

$$
\rho_{q,\infty}(c)=1,\qquad
\rho_{q,4}(c)=
\begin{cases}
r_q,&c\text{ is a protected singleton},\\
1,&c\text{ is the remaining colour}.
\end{cases}
$$

For a full depth type $(D,S,t)$ of Report 820 CC4, coordinates outside $D$ enter a branch through $\pi_q$, coordinates in $S\subseteq D$ through $\rho_q$, and deep coordinates in $D\setminus S$ through a factor one. Therefore, for every identical colour/leaf branch and every $u\ge0$,

$$
\operatorname{branch}_4
\ge\left(\prod_{q\notin D}r_q\right)
     \left(\prod_{q\in S}r_q\right)
       \operatorname{branch}_\infty
\ge r\operatorname{branch}_\infty.
$$

The last inequality uses $0<r_q\le1$. Taking maxima over the same live branch menu gives

$$
F_{4,D,S,t}(u)\ge rF_{\infty,D,S,t}(u).
$$

Keep the complete depth-type coefficients of CC5–CC6, including the subtraction of each selected numerical label exactly once in its own type and the complete higher-ternary term, including empty nonternary support. Every resulting loss coefficient is nonnegative. If $D_E(u)$ denotes their complete envelope sum, then

$$
D_4(u)\ge rD_\infty(u),\qquad
L_4(u)=M_4(u)-D_4(u)
\le rL_\infty(u)+M_4(u)-rM_\infty(u).
$$

At the infinite C source the shallow factors all equal one, so summing over $S$ recovers precisely the 384 inherited loss blocks used by Report 835; this aggregation is established in Report 826 section 5. At the finite source the different $S$ envelopes generally differ. Thus the old 9,902 epigraph rows are not asserted to remain the finite-source matrix. The displayed one-sided comparison accounts for the actual capacity change over the full depth-type inventory.

## A table-independent relative mass estimate at depth four

For a protected singleton,

$$
\frac{\pi_{q,4}(c)}{r_q\pi_{q,\infty}(c)}=1.
$$

For the remaining colour the ratio is $1+x_q$, where

$$
x_q=\frac{q^{-4}}{(q-2)\pi_{q,\infty}(\mathrm{remaining})}.
$$

In particular,

$$
x_5=\frac1{875},\qquad
x_q=\frac{q^{-3}}{q^2-3q+1}\le\frac1{8575}\quad(q\ge7).
$$

The latter uses $q^2-3q+1\ge(q-2)^2\ge25$ and $q^3\ge343$. Hence

$$
s:=\sum_{q\in Q}x_q
\le\frac1{875}+\frac6{8575}
=\frac{79}{42875}<\frac1{501}.
$$

For nonnegative $x_q$ with sum below one, $\prod_q(1+x_q)\le1/(1-\sum_qx_q)$. Indeed, $1+x_q\le(1-x_q)^{-1}$ and $\prod_q(1-x_q)\ge1-\sum_qx_q$. It follows that

$$
\prod_q(1+x_q)<\frac{501}{500}.
$$

Every categorical cell, with the same ternary leaf at both sources, therefore satisfies

$$
rm_{\infty,i}\le m_{4,i}\le\frac{501}{500}rm_{\infty,i}.
$$

Multiplying by any common nonnegative table and summing gives

$$
0\le M_4(u)-rM_\infty(u)
\le\frac{r}{500}M_\infty(u),\qquad
rM_\infty(u)\ge\frac{500}{501}M_4(u).
$$

No compactness or lower bound on a chosen table's mass is required. The comparison is homogeneous and simultaneous for every table; it is not a limit followed by a table-dependent choice of depth.

## Combining the three one-sided inequalities

Put $t=28-h\ge0$ and $\overline H_E=(H_{A,E}+H_{C,E})/2$. Hinge domination, Report 835 and loss domination give

$$
\begin{aligned}
\overline H_4-tL_4
&\ge r\overline H_\infty
      -t\bigl(rL_\infty+M_4-rM_\infty\bigr)\\
&\ge r\left(\frac{t}{400}+\delta\right)M_\infty
      -t(M_4-rM_\infty)\\
&\ge r\left(\frac{t}{2000}+\delta\right)M_\infty\\
&\ge\frac{500}{501}\left(\frac{t}{2000}+\delta\right)M_4.
\end{aligned}
$$

This proves the leading inequality, including $h=28$. If $H_{*,4}$ is the supremum over all globally fixed, independently assigned per-numerical-label phases, A and C are two admissible witnesses and $H_{*,4}\ge\overline H_4$. Therefore

$$
(28-h)L_4-H_{*,4}
\le-\frac{500}{501}\left(\frac{28-h}{2000}+\delta\right)M_4<0
$$

for every nonzero admissible table. Any further nonnegative tail penalty preserves this negative sign.

This excludes the stipulated inherited raw-retained comparison for one actual finite 53-original family, uniformly over its admitted first-colour kernels and every real threshold in the continuation domain. It does not exclude replacing $L_4$ with a sharper actual-survivor lower bound, changing the query law after additional original deletions, sharpening the actual finite inventory, or allowing retained tables to depend on deeper source digits. Those changes alter a premise of the transported comparison.

## A finer actual survivor source passes the complete query gate

The same 53 originals admit a single product probability whose complete
query norm, including the unit and every height, is less than28. This is
an explicit application of [794's actual-prefix source representation](../750-799/794-actual-prefix-orbits-make-all-height-source-search-sparse.md),
not a uniform theorem for arbitrary eight-prime families.

Write $Q_*=(7,11,13,17,19,23)$. Use normalized Haar on the product region

$$
R=\{x_3=4\bmod9\}\times\{x_5=4\bmod5\}
  \times\prod_{q\in Q_*}\{x_q\bmod q\in\{3,\ldots,q-1\}\}.
$$

All higher digits remain Haar. The ternary condition avoids the originals
at3 and9. Each of the other23 displayed base originals $(m,a)$ has a
nonternary prime divisor $q$ with $a\bmod q<3$, so it misses this region.
At5 the added pure comb uses first roots2 and3; at every $q\in Q_*$ it
uses first roots1 and2. These also miss $R$. The same statement holds
for every further depth of these particular pure combs. No original
residue is changed or independently reassigned.

Let $\nu$ be this one normalized product law. For each positive
$P$-smooth integer $d$, where $P=(3,5,7,11,13,17,19,23)$, put
$q_d=\max_a\nu([a]_d)$. Independence of this explicitly chosen law
gives $q_d=\prod_p c_p(v_p(d))$, where

$$
\begin{aligned}
c_3(0)&=c_3(1)=1,& c_3(e)&=3^{2-e}\quad(e\ge2),\\
c_5(0)&=1,& c_5(e)&=5^{1-e}\quad(e\ge1),\\
c_q(0)&=1,& c_q(e)&=\frac1{(q-3)q^{e-1}}\quad(q\in Q_*,\ e\ge1).
\end{aligned}
$$

Each coordinate maximum is attained by a cylinder inside its allowed
prefixes. Summing these nonnegative geometric series retains every
numerical query label, including labels absent from the original family:

$$
B_P(\nu)=\sum_{\substack{d\ge1\\d\ P\text{-smooth}}}q_d
=\frac72\frac94\prod_{q\in Q_*}
  \left(1+\frac{q}{(q-3)(q-1)}\right)
=\frac{12852604279333}{830472192000}<28.
$$

The region has Haar mass $40960/9561123$, so this is a probability with
finite Haar density $9561123/40960$. In794's named-prefix representation
it is one surviving joint orbit. The local coefficient and phase-menu
interfaces give the same exact query value using215 local rows, followed
by the complete Euler tails; no joint-orbit grid or optimizer is needed.

In particular, adjoining any finite set of distinct29-ending originals
of modulus $29^e d$, with $e\ge1$ and $d\ge1$ supported on $P$, preserves
noncoverage for this fixed old family. Keep their globally fixed phases
and arbitrary full numerical old cofactors. At each positive
29-exponent there is at most one query per old numerical cofactor, so
the union bound under $\nu\times\mathrm{Haar}_{29}$ is at most
$B_P(\nu)\sum_{e\ge1}29^{-e}=B_P(\nu)/28$. The remaining mass is at least

$$
1-B_P(\nu)/28
=\frac{1485802442381}{3321888768000}>0.
$$

This source separates first-root values that the old K8 table combined:
it keeps only root4 at5 and excludes root2 at the other nonternary primes.
It also uses the actual53-label inventory rather than the inherited
complete loss envelope. Thus it changes both the admitted source family
and the loss comparison; it does not attribute the improvement to either
change alone, nor contradict the earlier all-table inequality.
The literal support exclusions and exact rational query value have scoped
transient Lean checks. The probability-product identification, geometric
tails and one-step continuation are ordinary reuse of794 and the existing
query extension argument, not a newly kernel-verified measure theorem.
