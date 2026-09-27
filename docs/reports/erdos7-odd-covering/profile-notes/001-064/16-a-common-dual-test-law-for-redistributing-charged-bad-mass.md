[Index](../../marked_head_profile.md) · [Previous](15-a-clean-cylinder-makes-all-current-prime-pair-caps-exact.md) · [Next](17-higher-moments-retain-the-full-old-inventory-in-a-law-changing-perturbation.md)

<a id="a-common-dual-test-law-for-redistributing-charged-bad-mass"></a>
### A common dual test law for redistributing charged bad mass

For one fixed actual forbidden family and one fixed old law \(\nu\),
the density in (PO1) has an additional admissible degree of freedom.
Write \(m_x\) for the normalized pure-survivor law on a finite
current fibre, \(B_x\) for its entire actual mixed bad union, and
\(\alpha_x=m_x(B_x)\). On rows with \(\alpha_x>\delta\), put

\[
 C=(1-\delta)^{-1},\quad
 \beta_x=\frac{\alpha_x-\delta}{1-\delta},\quad
 r_x=\frac{\beta_x}{\alpha_x},\qquad
 \frac{dq_{v,x}}{dm_x}=C\mathbf1_{B_x^c}+v_x\mathbf1_{B_x},
 \quad 0\le v_x\le1,\quad\int_{B_x}v_x\,dm_x=\beta_x.
                                                               \tag{KR1}
\]

The constant choice \(v_x=r_x\) is the existing kernel. Every
choice in (KR1) has total mass \(C(1-\alpha_x)+\beta_x=1\),
the same charge \(q_{v,x}(B_x)=\beta_x\), the same density cap
\(C\), and \(q_{v,x}(S)\le m_x(S)\) for \(S\subseteq B_x\).
Normalization preserves all old marginals. These are precisely the
pointwise cap and bad-subset properties used here from
[BBMST, section2, Lemma2.2](https://arxiv.org/html/1811.03547#S2.Thmtheorem2).
The existing `ConditionalComparison/Distortion` module fixes the
constant inside multiplier; it is reused as that special choice.

Keep uncharged and degenerate rows at their existing kernels by
definition. Nonconstant choices within this specified class require
\(0<\delta<\alpha_x<1\) and at least two positive-mass bad atoms.
No optimum over every possible physical law is asserted: the exterior
density and uncharged rows have deliberately been fixed.

Let \(\mathcal T\) be the finite set of all globally legal complete
tests at the chosen finite height, preserving every original modulus.
Let \(L_T\) be the actual load, \(Q_{\rm BB}(T)\) its square
expectation for the constant-inside kernel, and
\(V_{\rm BB}=\max_TQ_{\rm BB}(T)\). Choose one kernel before
the test is selected, and define
\(V_* =\min_v\max_T\mathbb E_{\nu q_v}L_T^2\).
For a single common distribution \(\pi\) on \(\mathcal T\), put
\(F_{\pi,x}(y)=\sum_T\pi_TL_T(x,y)^2\). On a flexible row,
the exact minimum bad contribution and its saving are

\[
 \begin{aligned}
 \ell_x(F)&=\min_{0\le v\le1,\,\int_Bv\,dm=\beta_x}
                     \int_BvF\,dm\\
 &=\max_{\tau\in\mathbb R}
       \left[\beta_x\tau-\int_B(\tau-F)_+\,dm\right],\\
 D_x(F)&=r_x\int_BF\,dm-\ell_x(F)\ge0.
 \end{aligned}                                                 \tag{KR2}
\]

This directly reuses `FractionalKnapsackDual.fractional_knapsack_strong_duality`
and `greedy_attains_duality`: on positive-mass bad atoms take item
weights \(m_x(y)\), values \(m_x(y)F(y)\), budget
\(\alpha_x-\beta_x\), and item variables \(1-v(y)\).
Since \(F\ge0\), unused budget can be filled without decreasing
the objective. Subtracting the resulting maximum from \(\int_BF\,dm\)
gives (KR2); negative prices cannot improve its right side. Thus fill
the lowest \(F\) levels with density one, the highest with zero,
and split at a boundary level to give exactly \(\beta_x\).
Set \(D_x=0\) on unchanged rows. No duplicate duality theorem is needed.

Finite minimax (the compact convex affine case of Mathlib's
`Sion.minimax'`), followed by this separate row minimization, gives

\[
 \begin{aligned}
 V_*&=\max_{\pi\in\Delta(\mathcal T)}
       \left[\sum_T\pi_TQ_{\rm BB}(T)
                         -\mathbb E_\nu D_x(F_{\pi,x})\right],\\
 V_{\rm BB}-V_*&=\min_{\pi\in\Delta(\mathcal T)}
       \left[V_{\rm BB}-\sum_T\pi_TQ_{\rm BB}(T)
                         +\mathbb E_\nu D_x(F_{\pi,x})\right].
 \end{aligned}                                                 \tag{KR3}
\]

Both terms on the second line are nonnegative. On a flexible row,
\(D_x(F)=0\) exactly when \(F\) is constant on the positive-mass
part of \(B_x\). One direct quantitative proof is to let
\(a=\mathbb E[F\mid B_x]\),
\(\omega=\max_{B_x}F-\min_{B_x}F>0\), taking extrema only on
positive-mass atoms, and choose
\(v=r_x-\min(r_x,1-r_x)(F-a)/\omega\). Its density lies in
\([0,1]\), its mass is \(\beta_x\), and hence

\[
 D_x(F)\ge
 \frac{\alpha_x\min(r_x,1-r_x)}{\omega}
                 \operatorname{Var}_{m_x(\cdot\mid B_x)}(F).
                                                               \tag{KR4}
\]

For constant \(F\) set this lower bound to zero. For nonconstant
\(F\) its right side is positive. Compactness of the finite simplex
in (KR3) now gives an exact strict-improvement criterion: \(V_*<V_{\rm BB}\)
if and only if there is no common mixture supported on
BBMST-maximizing tests for which \(F_{\pi,x}\) is constant on
every flexible bad fibre of positive \(\nu\)-mass. For rational
data, absence of such a mixture is a finite rational feasibility
question, using equations
\(\sum_T\pi_T(L_T(x,y)^2-L_T(x,z)^2)=0\) for positive-mass
bad atoms \(y,z\). The optimal values are rational.
Replacing each \(D_x\) in (KR3) by (KR4) also gives a sufficient
lower bound for the improvement, but it still requires minimizing
over that single common \(\pi\). Separate row mixtures or gains
against only one test do not supply it.

The threshold formula in (KR2) solves the inner problem for a
fixed \(\pi\). Arbitrary choices at tied threshold levels of a
dual optimum need not give a primal minimax kernel. A realizing law
must come from a saddle-compatible primal solution or be checked
against every legal test. The strict criterion above is finite;
an infinite test domain need not have a maximizing face.

The clean comb passes this test with equality. It has a maximizing
complete test whose positive-depth labels are all on the clean root.
On every actual bad fibre its load equals the old load \(A_0(x)\),
independent of the current point. The point mass on this test makes
every \(D_x\) zero, so (KR3) gives \(V_*=V_{\rm BB}\).
The coloring extension has the same property. Thus the new kernel
class does not contradict the sharpness obstruction.

Complete test tails remain controlled for an arbitrary fixed family.
Let \(D_0\) be its actual forbidden depth and \(k\ge D_0\).
Allow uniform independent suffix coordinates as in (KT2)--(KT3).
Project any feasible density to its conditional expectation on the
first \(k\) digits; since \(B_x\) is already measurable there,
this preserves all row constraints and every depth-at-most-\(k\)
test. Conversely, extend a finite feasible kernel uniformly in the
suffix. Let \(V_k^*\) be its finite minimax value and \(V_\infty^*\)
the infimum, over these full feasible densities, of the supremum
over all finite complete test heights. If
\(\mathbb E_\nu[cA^2]\le G_c\) for every complete old layout,
where \(c=g_x/s\) is the unchanged cap relative to Haar measure,
the same original-pair proof gives

\[
 V_k^*\le V_\infty^*\le V_k^*+
 G_cp^{-k}\left[\frac{2k+3}{p-1}+\frac2{(p-1)^2}\right].
                                                               \tag{KR5}
\]

For the upper bound, uniformly extend a finite minimizer and use
(KT2); the lower bound follows from projection. The old law and
complete forbidden antichain are fixed throughout. Tests beyond the
family's own period are auxiliary, so their supremum is an upper
domain, not a lower bound for the original finite-period problem.
This truncates tests only and gives no uniform family truncation.

At the final prime of a continuation, the new kernel can be consumed
without changing any earlier observation. Write \(B_{<p}\) for
accumulated earlier assigned charge and \(b_p=\mathbb E_\nu\beta_x\).
Here \(V_p^*\) denotes the attained finite minimax on the actual
family's full period; an upper certificate from an explicitly feasible
kernel with its complete tail may be substituted for it.
For \(W>0\), if a common history domain satisfies
\(V_p^*-1+W(B_{<p}+b_p)\le C_0<W\), then the same final
conditioning proof as (SH28) gives positive survivor mass and
\(\Gamma\le1+C_0\). Indeed \(V_p^*\ge1\) forces \(C_0\ge0\),
the total charge is at most \(C_0/W<1\), and
\(V_p^*-1\le C_0(1-B_{<p}-b_p)\). An earlier-prime change
requires recomputing any later statistics tied to the old law.

The optimized value concerns the physical law before final conditioning.
All admissible kernels agree on \(B_x^c\); therefore they agree on
the final survivor event, which is contained in that complement.
Its mass and its conditioned law, when that mass is positive, are
unchanged. At the last prime this procedure can sharpen the physical
moment/charge certificate, but cannot change the actual final supported
law or its true complete-test \(\Gamma\).
No bound \(C_0<483\) through19, uniform improvement over all
forbidden families, or unrestricted noncoverage conclusion is established here. These
are ordinary finite optimization and tail arguments, not new Lean
declarations or a claim of literature priority.

<a id="the-constant-bad-multiplier-need-not-minimize-the-physical-test-square"></a>
### The constant bad multiplier need not minimize the physical test square

There is an exact finite counterexample to universal optimality of the
constant inside multiplier. Use old period9, old forbidden classes
\(0\bmod3,0\bmod9\), and old probability concentrated at1.
This is a supplied supported old law, as permitted in (KR1); it is
not asserted to arise from an earlier standard distortion of Haar law.
At prime5 through height2 take the additional original classes

\[
 0\bmod5,\quad0\bmod25,\quad1\bmod15,\quad
 37\bmod45,\quad28\bmod75,\quad154\bmod225.          \tag{KR6}
\]

All eight moduli are distinct odd integers greater than one. On the
old row1, let \(y\) be the current residue modulo25. The pure law
is uniform on the twenty \(y\not\equiv0\pmod5\). The mixed bad
set consists of the ten leaves on roots1 and2, together with the
leaves3 and4 on the other two surviving roots. Thus
\(\alpha=3/5\). At \(\delta=2/5\) its assigned charge is
\(\beta=1/3\). The constant kernel gives each good leaf mass
\(1/12\) and each bad leaf mass \(1/36\).

An admissible alternative keeps each good leaf at \(1/12\), assigns
\(1/30\) to each of the ten leaves on roots1 and2, and assigns zero
to bad leaves3 and4. Its bad density relative to the pure law is
\(2/3\) or zero, so (KR1) holds with unchanged charge and cap.

The complete test domain has all nine original divisor labels
\(d5^e\), \(d\in\{1,3,9\},0\le e\le2\).
On the old atom, every inactive old residue can be made active without
reducing the load. Its zero layer can therefore be set to3.
For the three remaining root choices \(r_i\) and three leaf choices
\(s_j\), the full load divided by3 is the average of
\(1+\mathbf1_{y=r_i\bmod5}+\mathbf1_{y=s_j\bmod25}\)
over all nine pairs \((i,j)\). Convexity of the square and taking
all roots equal and all leaves equal consequently prove the exact
full-domain reduction

\[
 V(q)=9\max_{0\le r<5,\,0\le s<25}
     \mathbb E_q(1+\mathbf1_{y=r\bmod5}
                    +\mathbf1_{y=s\bmod25})^2.       \tag{KR7}
\]

All125 choices give

\[
 V_{\rm BB}=\frac{45}{2},\qquad
 V(q_*)=V_* =\frac{87}{4},\qquad
 V_{\rm BB}-V_* =\frac34.                            \tag{KR8}
\]

For the matching minimax lower bound, choose root3 and a good leaf
above it. Under every admissible kernel, its four good leaves retain
total mass \(1/3\), and that leaf retains mass \(1/12\).
The nested aligned test therefore has square at least
\(9[1+3/3+5/12]=87/4\); other bad contributions are nonnegative.
Thus the alternative attains the exact optimum of (KR1), with no
unexamined complete tests or sampled maximum.

Both laws condition on the same eight final good leaves to the same
uniform law. Its complete-test value, again by (KR7), is
\(9[1+3/2+5/8]=225/8\). The strict improvement in (KR8) is a
physical moment improvement before conditioning, not an improvement
in this final supported value. It occurs for a fixed small-inventory
family without a common clean root; the separate clean-comb worst
family obstruction remains intact.

`verify_bad_mass_rearrangement.py` reconstructs the actual eight-class
family and checks its adjacent exact certificate, including all125
aligned tests under both physical laws and the common final survivor
law. The full-domain reduction is (KR7); the minimax lower bound is
the fixed good-root test above. This refutes universal optimality of
the constant inside multiplier for the physical complete-test objective,
without asserting any full-family or later-prime improvement.

<a id="survivor-invariance-along-a-finite-chain-and-density-cap-saturation"></a>
### Survivor invariance along a finite chain and density-cap saturation

Fix an initial law \(\nu_0\), an actual forbidden family, and any finite
sequence of prime-coordinate extensions. Let \(S_i\) be the event of
avoiding every forbidden class through stage\(i\). At an old prefix
\(h\), write \(m_i(h,y)\) for the fixed pure-survivor base and
\(B_i(h)\) for the entire current mixed bad set. Consider two normalized
kernel chains \(q_i^a\), \(a\in\{0,1\}\), with these same bases.
Suppose that whenever \(h\in S_{i-1}\) and \(y\notin B_i(h)\),
both kernels have the same good transition
\(q_i^a(h,y)=m_i(h,y)g_i(h,y)\). The common multiplier may depend on
the whole prefix and current point. For every \(z=(x_0,\ldots,x_i)\in S_i\),
successive multiplication of conditional probabilities gives

\[
 P_i^a(z)=\nu_0(x_0)\prod_{j=1}^i q_j^a(z_{<j},x_j)
        =\nu_0(x_0)\prod_{j=1}^i m_j(z_{<j},x_j)g_j(z_{<j},x_j).
                                                               \tag{SI1}
\]

Thus the restrictions \(P_i^0|_{S_i}\) and \(P_i^1|_{S_i}\) agree
pointwise at every stage. No agreement is required on bad transitions
or on any transition after an already bad prefix. In particular, arbitrary
rearrangements confined to bad sets throughout a finite continuation
preserve the final survivor mass and, when that mass is positive, its
entire conditioned law and true complete-test \(\Gamma\). Later physical
moments and expected assigned charges can change on already bad prefixes;
such changes can tighten certificates without changing this final law.

More generally, keep the same initial law, bases and final event \(S=S_n\),
but allow different good multipliers \(g_i^a\). Assume the baseline
\(g_i^0\) is strictly positive on positive-base good transitions, the
comparison \(g_i^1\) is finite and nonnegative, and both survivor masses
\(\rho_a=P_n^a(S)\) are positive. On the positive baseline survivor
support define

\[
 \begin{aligned}
 R(z)=\prod_{i=1}^n\frac{g_i^1(z_{<i},x_i)}{g_i^0(z_{<i},x_i)},
 &\qquad P_n^1(z)=R(z)P_n^0(z),\\
 P_n^1(\cdot\mid S)=P_n^0(\cdot\mid S)
 &\ \Longleftrightarrow\ R(z)\equiv\frac{\rho_1}{\rho_0}.
 \end{aligned}
                                                               \tag{SI2}
\]

This follows by dividing each survivor weight by its total mass. A common
factor can change survival probability while leaving the conditional law
unchanged. For the standard distortion, \(0\le\delta_i(h)<1\) and
\(\alpha_i(h)=m_i(h,B_i(h))\) give good multiplier
\((1-\min(\alpha_i(h),\delta_i(h)))^{-1}\). A common threshold rule
depending on the actual observed prefix therefore preserves (SI1).
A rule depending on the whole current physical law can change the
effective threshold at the same good prefix; it changes the final
conditional law only when the product ratio in (SI2) is nonconstant.
Changing between threshold values both at least \(\alpha_i(h)\) has
no good-side effect.

For the local obstruction, let \(m\) be a fixed finite probability,
\(B\) a bad set of mass \(\alpha\), and \(q=fm\) a normalized law
with density \(0\le f\le g\), where \(1\le g<\infty\). Define
the available good capacity \(A=g(1-\alpha)\) and its unused mass
\(\Delta=\int_{B^c}(g-f)\,dm\). Then

\[
 \begin{gathered}
 \min_f q(B)=\beta:=\max(0,1-A),\qquad
 q(B)=1-A+\Delta,\\
 A\le1\ \Longrightarrow
 \left[q(B)=\beta+\Delta,\quad
 q(B)=\beta\ \Longleftrightarrow\ f=g\quad m\text{-a.e. on }B^c\right].
 \end{gathered}
                                                               \tag{SI3}
\]

Indeed \(q(B)=1-q(B^c)\) and \(q(B^c)\le A\). If \(A<1\),
the minimum is attained by density \(g\) on the good set and
\(\beta/\alpha\) on the bad set; if \(A\ge1\), use density
\((1-\alpha)^{-1}\) on the good set and zero on the bad set.
Both constructions also obey \(f\le1\) on the bad set, if that
additional constraint is imposed. Equality for \(A\le1\) forces the
nonnegative good deficit to vanish at every positive-mass good atom.
Consequently any reduction of good mass in a saturated row increases
its actual bad charge by exactly the same amount. If \(A_x\le1\) in
every compared row, at fixed old law \(\nu\) the one-step charge increment is
\(\mathbb E_\nu\Delta_x\); this is not a telescoping comparison
between chains whose intermediate physical laws differ.

The strict branch \(A>1\) has \(\beta=0\) and
\(q(B)=\Delta-(A-1)\). Zero bad charge then leaves unused capacity
\(A-1\) and does not force good-side saturation. With at least two
positive-mass good atoms, nonconstant zero-charge perturbations are
possible. The distinction between the global cap and the natural cap
is therefore essential.
For \(0\le\delta<1\),

\[
 \begin{aligned}
 g_{\rm global}&=(1-\delta)^{-1},
 &A_{\rm global}>1&\ \Longleftrightarrow\ \alpha<\delta,\\
 g_{\rm natural}&=(1-\min(\alpha,\delta))^{-1},
 &A_{\rm natural}&\le1,\qquad
 \beta=\frac{(\alpha-\delta)_+}{1-\delta}.
 \end{aligned}                                                 \tag{SI4}
\]

Under the natural cap, minimum bad charge fixes the good side in every
row, including uncharged rows. Under only the global cap, strictly
uncharged rows with at least two positive-mass good atoms can retain
zero bad charge while changing their good density; (KR1) deliberately
kept those rows fixed. In a saturated row,
changing the good transition requires increasing bad charge as in (SI3),
or relaxing the prior cap to allow compensating density increases.
Together with (SI2), these identify ways to change the supported law;
they do not establish a better numerical \(\Gamma\), a uniform family
bound, or unrestricted noncoverage.

The product and conditioning identities reuse `Erdos7.FiniteLaw.joint`,
`condition_prob`, and `Erdos7.ThreePrime.KernelChain.law` in the existing
`ConditionalComparison/ThreePrime` modules. The natural multiplier is
`Erdos7.outsideMultiplier_eq_natural` in `CappedGainDistortion`;
saturation is the finite instance of Mathlib's
`MeasureTheory.integral_eq_iff_of_ae_le`. These are ordinary consequences
of existing APIs, with no new Lean declarations.

<a id="a-common-clean-path-test-blocks-the-natural-cap-charge-tradeoff"></a>
### A common clean-path test blocks the natural-cap charge tradeoff

Fix one finite CS2 comb of height \(H\ge1\), its old probability
\(\mu\), and its complete original old inventory of \(K\le p-3\)
nonunit labels. Old forbidden cylinders may vary independently at every
depth. Besides the pure root0, the \(K\) spoke roots and spine root
\(p-2\), designate the remaining \(r=p-K-2\ge1\) roots. Their
union \(R\) is disjoint from every forbidden prefix, on every old row.
There can be additional clean roots; only this fixed subset is used.
Write \(\lambda_H=1-\sum_{e=1}^Hp^{-e}\), let \(m_x\) be the
normalized pure-survivor law, and put
\(\alpha_x=m_x(B_x)\), \(g_x=(1-\min(\alpha_x,\delta))^{-1}\),
\(\beta_x=(\alpha_x-\delta)_+/(1-\delta)\), with
\(0\le\delta<1\). Thus \(m_x(R)=r/(p\lambda_H)\),
\(\alpha_x<1\), and the BBMST law saturates all good points.

Allow the larger honest row domain
\(0\le\rho_x\le g_x\) on \(B_x^c\),
\(0\le\rho_x\le1\) on \(B_x\), and
\(\int\rho_x\,dm_x=1\). In particular its actual charge
\(b_x=\int_{B_x}\rho_x\,dm_x\) may exceed \(\beta_x\).
For fixed \(f\ge0,W>0\), minimize over this one kernel the maximum
of \(f\mathbb E L_T^2+W\mathbb E_\mu b_x\) over all complete tests.

Fix any old complete-test sequence \(A_0,\ldots,A_H\), independently
of the forbidden layouts. Choose a root uniformly among the designated
\(r\) roots, then an independent uniform suffix of length \(H-1\).
Put every depth-\(e\) original test label on the corresponding prefix
of this one path. This is one common finite mixture \(\pi\) of legal
tests, shared across all old rows. For a point in \(R\), its depth-\(j\)
prefix is selected with probability \(1/(rp^{j-1})\); outside \(R\)
no positive-depth test hits. Hence, using \(Q_H\) defined before (CS5),

\[
 F_{\pi,x}(y):=\mathbb E_{T\sim\pi}L_T(x,y)^2
 =A_0(x)^2+\frac p r Q_H(x)\mathbf1_R(y),\qquad
 Q_H=\sum_{\substack{0\le e,j\le H\\(e,j)\ne(0,0)}}
                      p^{-\max(e,j)}A_eA_j.
                                                               \tag{HC1}
\]

Set \(c_H=g_x/\lambda_H\),
\(d_x=fpQ_H(x)/r\), \(h_x=g_xr/(p\lambda_H)\), and
\(\tau_x=\min(h_x,\alpha_x-\beta_x)\). There is an exact row identity
for this fixed common mixture:

\[
 \min_{\rho_x}\left[f\int F_{\pi,x}\rho_x\,dm_x+Wb_x\right]
 =f\bigl(A_0(x)^2+c_HQ_H(x)\bigr)+W\beta_x
                     -\tau_x(d_x-W)_+.
                                                               \tag{HC2}
\]

To prove it, let \(u\) be the lost mass from \(R\) relative to
the saturated BBMST law, and \(v\) the lost mass from \(B_x^c\setminus R\).
The cap makes \(u,v\ge0\), and (SI3) gives
\(b_x=\beta_x+u+v\). Also \(u\le h_x\) and
\(u+v\le\alpha_x-\beta_x\), because bad density is at most1.
The objective change is exactly
\((W-d_x)u+Wv\). Its minimum is
\(-\tau_x(d_x-W)_+\), attained with \(v=0\), by moving either
zero mass or \(\tau_x\) from \(R\) to unused bad capacity.
Fractional atom densities permit that transfer even on a finite fibre.
If the unused bad capacity is zero, \(\tau_x=0\) and no transfer is
needed. If \(d_x<W\), equality with the BBMST value forces
\(u=v=0\), so every positive-mass good atom remains saturated.
Strict improvement against this fixed mixture occurs precisely when
\(\tau_x>0\) and \(d_x>W\).

At fixed \(H\) the old layout set is finite. Choose a sequence maximizing
the BBMST complete-test objective. By (CS5), each of its nested designated
clean-path tests attains the pair caps, so the mixture in (HC1) is
supported on BBMST-maximizing tests. If \(d_x\le W\) on every
positive-\(\mu\) row, (HC2) supplies a lower bound against every honest
kernel equal to the BBMST maximum. BBMST itself is feasible. Therefore

\[
 V_{\rm honest}(H)=V_{\rm BB}(H).
                                                               \tag{HC3}
\]

If all those row inequalities are strict, every honest minimizer agrees
with BBMST on all positive-mass good transitions. It has the same current
survivor subprobability and, when its mass is positive, conditioned law. Bad-side choices can still
differ; later policies that read them must be assessed under (SI1)--(SI2).
The common maximizing mixture is essential: improving one deterministic
test is insufficient to improve this maximum.

For a pointwise old-load bound \(A_e(x)\le R_0\), the full geometric
sum, without identifying layouts across depths, gives

\[
 Q_H(x)\le R_0^2\sum_{j=1}^H(2j+1)p^{-j}
 \le R_0^2\frac{3p-1}{(p-1)^2}.
 \quad
 W\ge\frac{fpR_0^2}{p-K-2}\frac{3p-1}{(p-1)^2}
 \ \Longrightarrow\ \text{(HC3) for every finite }H.
                                                               \tag{HC4}
\]

In the PG1 low315 comb at17, \(K=11\), \(R_0=12\), \(r=4\),
\(f=59/45\), and \(W=483\). All original \(11+12H\) forbidden
moduli and \(12(H+1)\) test labels are retained. Exactly,

\[
 d_x\le\frac{59}{45}\frac{17}{4}\,144\frac{25}{128}
       =\frac{5015}{32}<483,
 \qquad 483-\frac{5015}{32}=\frac{10441}{32}.
                                                               \tag{HC5}
\]

Thus allowing good-side mass reductions with their actual charge cost
cannot improve this family's complete-test objective at any finite
height, even with independent old layouts at every depth. This includes
the off-diagonal layouts left essential by (JL1)--(JL3). It does not
evaluate the remaining old-layout maximum or improve a global bound.
The cap here is the natural row cap: replacing it on uncharged rows by
the larger global cap invalidates \(u,v\ge0\) relative to BBMST and is
outside this obstruction. General original inventories with higher
3/5/7 powers and earlier11/13 labels need not admit these designated
clean roots. Changing the reference thresholds or the old law is also
outside this fixed-cap comparison. This is an ordinary finite saddle argument with a complete
geometric bound, not a new Lean theorem or a literature-priority claim.


<a id="a-global-cap-perturbation-improves-the-actual-survivor-law-at-every-finite-height"></a>
### A global-cap perturbation improves the actual survivor law at every finite height

The natural-cap obstruction (HC3) does not persist when strictly uncharged
rows may use the global cap. There is an explicit actual-family construction
whose physical complete-test square and final supported \(\Gamma\) both
strictly decrease, with a lower bound on the gain independent of height.
This is a fixed low315 family, not a bound over unrestricted old inventories.

Use the canonical PG1 probability \(\mu\) on its75 actual old survivors,
with denominator \(D=1000000007\). In particular,
\(\mu(2)=13119398/D\) and \(\mu(314)=16622259/D=:\mu_*\).
For each finite \(H\ge1\), keep its11 original old forbidden classes and
add the CS2 comb at \(p=17\), with all old forbidden cylinders centered
at2. The ordered nonunit old divisors
\((3,5,7,9,15,21,35,45,63,105,315)\) have respective spokes1 through11;
the spine is15. Thus all \(11+12H\) forbidden moduli are distinct odd
integers, the period is \(315\cdot17^H\), and all \(12(H+1)\) original
test labels retain independent residues. Fix \(\delta=7/15\).

Write \(s_H=\sum_{e=1}^H17^{-e}\), \(\lambda_H=1-s_H\),
\(n(x)=\sum_{d>1,\,d\mid315}\mathbf1_{x\equiv2\bmod d}\), and
\(c_H(x)=[\max(1-(n(x)+1)s_H,\lambda_H(1-\delta))]^{-1}\).
This is the BBMST good density relative to current-coordinate Haar measure.
At \(x_*=314\), only the old divisor3 matches2, so \(n(x_*)=1\).
The entire current root2, assigned to old divisor5, is good there.
This row is strictly uncharged for every \(H\), and
\(c_H(x_*)=(1-2s_H)^{-1}\le8/7\).

Let \(R_H=\{12,13,14,15,16\}\) when \(H=1\), and
\(R_H=\{12,13,14,16\}\) when \(H\ge2\); put \(r_H=|R_H|\).
These whole roots are globally clean. Let \(U_{j,H}\) denote the uniform
probability on current points congruent to \(j\bmod17\). Change only
row \(x_*\), with \(t=1/8192\):

\[
 q'_H(x_*,\cdot)=q_H(x_*,\cdot)+tU_{2,H}
                   -\frac{t}{r_H}\sum_{j\in R_H}U_{j,H}.
                                                               \tag{GC1}
\]

Every donor root has mass \(c_H(x_*)/17\ge1/17>t/r_H\).
The global density cap relative to Haar is
\(C/\lambda_H\), where \(C=15/8\). The recipient's unused root
capacity is at least
\((15/8-8/7)/17=41/952>t\). Thus (GC1) is nonnegative, preserves
normalization and the old marginal, obeys the global cap, and changes
no bad mass or bad-subset bound. The final survivor mass is unchanged
and satisfies \(\rho_H\ge r_H/17\ge4/17>0\), using the globally
clean roots and \(c_H\ge1\). The two conditioned survivor laws differ on root2 above
\(x_*\). Keeping the natural cap on this row would forbid this change.

Here is a bound against every complete test, without enumerating its
residues or identifying its layouts across depths. For a test \(T\),
let \(A_e(x)\le12\) be its complete old load at depth\(e\), and let
\(z\) be the first digit of its original pure17 test. Denote by \(U_H(T)\)
the BBMST pair-cap value with these old layouts, attained by aligning all
current prefixes along one nested globally clean path:

\[
 U_H(T)=\mathbb E_\mu[A_0^2+c_HQ_H],\qquad
 U_H(T)\le V_{{\rm BB},H}:=\max_T\mathbb E_{\mu q_H}L_T^2.
                                                               \tag{GC2}
\]

For the restriction to actual survivors, the corresponding value is
\(U_H^S(T)=\mathbb E_\mu[(1-\beta_H)A_0^2+c_HQ_H]
\le\rho_H\Gamma_{{\rm BB},H}\). The same aligned test attains that cap value;
the positive-depth pair caps are unchanged. Every gap used below holds
for both physical and survivor-restricted square integrals.

First suppose \(z\notin R_H\). A spoke root is entirely bad on the
positive-mass old row2. On that row the Haar-density difference between
the good cap and the physical bad density is
\(\delta/[(1-\delta)11s_H]\ge14/11\). Its pure17 test and its
cross terms with the old baseline, whose load is at least1, lose at least
\(G_{\rm spoke}=3\mu(2)14/187\) from (GC2). Root0 is pure forbidden,
giving \(G_0=3/17\). If \(H\ge2\), the spine root contains the whole
pure forbidden depth-two cylinder, giving \(G_{\rm spine}=3/289\).
For the survivor restriction the spoke loses still more, so the same
lower bounds remain valid. These cases exhaust roots outside \(R_H\).

Next suppose \(z\in R_H\), but some depth-one test label active at
\(x_*\) has another root. Its intersection with the original pure17
label is empty, while the two ordered cap terms in (GC2) total at least
\(G_{\rm split}=2\mu_*/17\).

For either of these cases, a uniform probability inside any one current
root gives, for every test and every height,

\[
 \mathbb E_{U_{j,H}}L_T(x_*,\cdot)^2
 \le12^2\left(1+17\sum_{e\ge1}(2e+1)17^{-e}\right)
 =\frac{4977}{8}=:M.
                                                               \tag{GC3}
\]

Indeed each intersection with maximal positive depth\(e\) has conditional
mass at most \(17^{1-e}\). Discarding the removed nonnegative square
cost, (GC1) can increase the integral by at most \(\mu_*tM\).
Exact rational arithmetic gives, for all four gaps above,

\[
 G-\mu_*tM>\varepsilon,
 \qquad \varepsilon:=\frac{3\mu_*t}{5}
   =\frac{49866777}{40960000286720}>0.
                                                               \tag{GC4}
\]

It remains to handle \(z\in R_H\) when every depth-one label active
at \(x_*\) has root\(z\). Removing donor mass loses a shallow square
increment of at least
\(\mu_*t(2A_0A_1+A_1^2)/r_H\ge3\mu_*t/r_H\), since both old
loads include their unit label. The baseline square cancels because the transferred masses total zero.
The recipient has only the baseline and possible deeper test hits. Let \(a_e\le12\) count the labels
active at \(x_*\) whose current prefix starts with2, for \(e\ge2\),
and put \(S=\sum_{e=2}^H17^{-e}a_e\). All these are original labels.
For any such nonnegative sequence, grouping pairs by their earlier depth
and bounding later coefficients by12 gives

\[
 \sum_{e,j=2}^H17^{-\max(e,j)}a_ea_j
 \le12\left(1+\frac2{16}\right)S.
                                                               \tag{GC5}
\]

Consequently the recipient's extra square cost is at most
\(\mu_*t\,17[2A_0+12(18/16)]S\le\mu_*t(1275/2)S\).
But every one of these deeper labels is disjoint from the original
pure17 test on row \(x_*\). Their missing cross terms already give
\(U_H(T)-\mathbb E L_T^2\ge2\mu_*c_H(x_*)S\ge2\mu_*S\).
Since \(t(1275/2)<2\), this gap absorbs the entire recipient gain.
The remaining donor decrease is at least \(\varepsilon\), as \(r_H\le5\).
This also covers \(H=1\), when \(S=0\). No infinite-family minimax
exchange or finite-height truncation is used.

Taking maxima over the original complete test domain in all three cases
therefore proves, for every finite \(H\ge1\),

\[
 V'_H\le V_{{\rm BB},H}-\varepsilon,
 \qquad
 \Gamma'_H\le\Gamma_{{\rm BB},H}-\frac{\varepsilon}{\rho_H}.
                                                               \tag{GC6}
\]

The second statement follows by applying the same argument to the killed
subprobabilities and dividing by their common positive mass. In particular
this is an improvement of the true supported test supremum, not merely
of a bound before final conditioning. Any objective \(fV+Wb\), with
\(f>0\), improves by at least \(f\varepsilon\), since charge is fixed.
The entire proof uses one explicitly defined probability before any test
is chosen. It refutes optimality of the BBMST law in this larger global-cap
class at every finite height. It does not give a gain uniform over all
forbidden families, treat unrestricted old3/5/7 and11/13 inventories, or
prove unrestricted noncoverage. These are ordinary probability and
original-label pair estimates, not new Lean declarations.

The [exact verifier](../../verify_pg1_global_cap_improvement.py) binds the canonical
PG1 source and reconstructs the [certificate](../../certificates/pg1_global_cap_improvement_certificate.json).
It checks the rational constants, cap slack and gap margins, five exact
height fixtures, and 22,950 literal supported CRT points across heights1
and2 under both laws, including unchanged charge and an actual change in
the conditioned survivor law. Run from any directory:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_pg1_global_cap_improvement.py
```

These finite arithmetic checks do not enumerate the complete test domain
or establish the universal height quantifier; those are proved in
(GC2)--(GC6), including the full geometric tail.
