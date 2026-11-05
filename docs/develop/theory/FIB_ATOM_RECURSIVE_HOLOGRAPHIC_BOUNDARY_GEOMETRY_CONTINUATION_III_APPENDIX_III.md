# FIB-ATOM recursive holographic boundary geometry · Continuation III Appendix III: an actual positive joint coefficient

## 134. A positive coefficient on the exact common-readout linear kernel

**Definition 134.1 (the original model and a fixed equal-gap readout).** Retain the complete original hypotheses, definitions and suppliers of [Appendix II §115](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#115-positivity-and-the-full-ground-state-form-of-the-actual-endpoint), [§117](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#117-deterministic-time-entrance-from-the-original-source-and-a-forbidden-passive-record), [§123](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#123-the-three-time-coefficient-image-and-its-compact-fibers), [§124](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#124-obstructions-to-common-factorization), [§125](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#125-the-common-readout-coefficient-boundary) and [§133](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#133-global-boundedness-of-the-original-source-density-and-the-equal-gap-marginal-pencil), including their inherited original endpoint and source assumptions. More explicitly, fix arbitrary original finite $a,\eta,d>0$. Write the central coordinate as $\zeta$, so that the unchanged group, raw Haar measure, source and differential operators are

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad
(x,y,z,\zeta)(x',y',z',\zeta')
=(x+x',y+y',z+z',\zeta+\zeta'+xy'),\\
e=(0,0,0,0),\qquad d\mu=dx\,dy\,dz\,d\zeta,\\
X_1=\partial_x,\qquad X_2=\partial_y+x\partial_\zeta,
\qquad X_3=\partial_z,\qquad L=-\sum_{r=1}^3X_r^2,\\
L\Gamma=\delta_e,\qquad g_c=16\sqrt{a\eta},\qquad
S=(aL+\eta D_\zeta^2-g_c\Gamma)|_{\mathcal D_0},\qquad
\mathcal D_0=C_c^\infty(G\setminus\{e\};\mathbb C).
\end{gathered}
\tag{134.1}
$$

Here $\Gamma$ is the original positive homogeneous degree-$-3$ unit-source Green field, and the central derivative and units are those of §115. Let $w_*$ be the original coefficient-one zero vector, and retain the actual endpoint selector and its coefficient-positive normalized state:

$$
\begin{gathered}
C_{\rm src}(w_*)=1,\qquad h=w_*/\|w_*\|_{L^2(\mu)},
\qquad C_{\rm src}(h)>0,\\
\rho=A_{\rm src}(h)/C_{\rm src}(h),\qquad
H=H_{\rm end},\\
D(H)=\{u\in D(S^*):A_{\rm src}(u)=\rho C_{\rm src}(u)\},
\qquad Hu=S^*u,\\
m=h^2\mu,\qquad m(G)=1,\qquad U_hv=hv,\qquad
K=U_h^{-1}HU_h\ge0,\qquad T_s=e^{-sK}.
\end{gathered}
\tag{134.2}
$$

The source coefficients $A_{\rm src},C_{\rm src}$ are precisely those of (112.2)–(112.5), as retained in §§115 and 133. The state $h$ is real and strictly positive off the source, and $m$ is a nonatomic Borel probability with $m(\{e\})=0$. The operator $K$ is the full conservative self-adjoint operator on $L^2(G,m)$. Its entire form domain and energy remain

$$
\begin{gathered}
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\qquad
\mathscr V_0=\overline{C_c^\infty(G\setminus\{e\})}^{\,(115.14)},\\
\mathscr E[v]=\int_{G\setminus\{e\}}
\left(a\sum_{r=1}^3|X_rv|^2+\eta|\partial_\zeta v|^2\right)dm,
\qquad v\in\mathscr V.
\end{gathered}
\tag{134.3}
$$

Thus the source coordinate is retained. No punctured or killed domain, alternate selector, clock rescaling or invariant initial law is introduced. The conservative diffusion $Z$ starts at the actual source $e$ at time zero. For every $s>0$, its density is the original $g_s$ of Theorem 117.2:

$$
\mathbb P_e(Z_s\in dx)=g_s(x)m(dx),\qquad
 g_s>0\quad m\text{-a.e.},\qquad
 g_s\in L^2(m),\qquad \int_Gg_s\,dm=1,
\qquad g_{s+r}=T_rg_s\quad(r\ge0).
\tag{134.4}
$$

Use the original time $t=2d$ and both gaps $\Delta_1=\Delta_2=d$. In particular, the observation epochs are $2d,3d,4d$. Put

$$
P=T_d,\qquad g=g_{2d},\qquad
M=1+\|g_d\|_{L^\infty(m)},\qquad c=\frac1{4M}.
\tag{134.5}
$$

Theorem 133.2 makes $M$ finite. Since $m(G)=1$ and $g_d$ has mass one, $M\ge2$. Choose a real Borel representative of $g_d$ and replace its values by $1$ on the Borel $m$-null set where it is not in $(0,M]$. Denote the repaired function by $b$. Then

$$
0<b(x)\le M\quad(x\in G),\qquad [b]=g_d.
\tag{134.6}
$$

With label set $\mathcal L=\{0,1,3,B\}$, define the single pointwise Borel readout used at all three epochs by

$$
f_3=cb,\qquad f_B=\frac14,\qquad
f_0=f_1=\frac{3/4-f_3}{2}.
\tag{134.7}
$$

These four functions sum to $1$ everywhere and satisfy

$$
0<f_3\le\frac14,\qquad f_B=\frac14,\qquad
\frac14\le f_0=f_1<\frac38.
\tag{134.8}
$$

For the two-label perturbation of Definition 125.1, choose $i=0$, $j=1$ and $\kappa=1/4$. Its prescribed overlap and signs are exactly

$$
E=\{f_0\ge\kappa,\ f_1\ge\kappa\}=G,\qquad
\sigma_0=1,\quad \sigma_1=-1,\quad \sigma_3=\sigma_B=0.
\tag{134.9}
$$

For real bounded classes use the original trilinear form, now with the equal gaps,

$$
\mathcal C(u,v,w)=\int_Gg\,u\,P(vPw)\,dm.
\tag{134.10}
$$

The fresh reads are conditionally independent given the three states, so the common-readout law is $\nu_f^{(3)}(y,z,w)=\mathcal C(f_y,f_z,f_w)$. Keep all the actual linear and quadratic coefficients of (125.2):

$$
\begin{aligned}
\ell_{yzw}(v)={}&\sigma_y\mathcal C(v,f_z,f_w)
+\sigma_z\mathcal C(f_y,v,f_w)
+\sigma_w\mathcal C(f_y,f_z,v),\\
q_{yzw}(v)={}&\sigma_y\sigma_z\mathcal C(v,v,f_w)
+\sigma_y\sigma_w\mathcal C(v,f_z,v)
+\sigma_z\sigma_w\mathcal C(f_y,v,v),
\qquad (y,z,w)\in\mathcal L^3.
\end{aligned}
\tag{134.11}
$$

Define the full linear constraint map, its exact kernel and the restricted quadratic span by

$$
\begin{gathered}
\Lambda:L^\infty(G,m;\mathbb R)\longrightarrow\mathbb R^{64},
\qquad \Lambda(v)=(\ell_{yzw}(v))_{(y,z,w)\in\mathcal L^3},\\
V=\ker\Lambda,\qquad
\mathcal Q_E=\operatorname{span}_{\mathbb R}
\{q_{yzw}|_V:(y,z,w)\in\mathcal L^3\}.
\end{gathered}
\tag{134.12}
$$

Here $E=G$, so support in $E$ imposes no additional restriction. All spaces and coefficients are real in (134.10)–(134.12), and functions are identified modulo $m$-null sets.

**Proposition 134.2 (an actual positive joint coefficient after every exact first-order constraint).** For every original finite $a,\eta,d>0$, the readout of Definition 134.1 has an infinite-dimensional exact linear kernel $V$, and its actual coefficient $q_{003}$ satisfies

$$
q_{003}(v)=c\langle gv,P(gv)\rangle_m
=c\|T_{d/2}(gv)\|_{L^2(m)}^2>0
\qquad\bigl(0\ne v\in L^\infty(G,m;\mathbb R)\bigr).
\tag{134.13}
$$

In particular,

$$
0\ne q_{003}|_V\in\mathcal Q_E,\qquad
n_-(q_{003}|_V)=0.
\tag{134.14}
$$

The negative index is the supremum of the dimensions of subspaces on which the form is negative definite. Consequently, the requirement that every nonzero member of the actual restricted span $\mathcal Q_E$ have negative-definite subspaces of arbitrarily large dimension fails for this readout and its prescribed overlap. No coercive or parameter-uniform lower bound is asserted.

**Proof.** First propagate the actual source density, without changing the first observation law. Equations (134.4) and (134.6) give, as $m$-classes,

$$
Pf_3=cT_dg_d=cg_{2d}=cg.
\tag{134.15}
$$

This is the original source propagation identity (117.3). The function $g_d$ defines only the fixed terminal readout component $f_3$; the first observation density in every coefficient is still $g=g_{2d}$.

For the ordered triple $(0,0,3)$, both terms of (134.11) containing $\sigma_3$ vanish and $\sigma_0^2=1$. Hence this is the actual coefficient

$$
\begin{aligned}
q_{003}(v)
&=\mathcal C(v,v,f_3)\\
&=\int_Gg\,v\,P(vPf_3)\,dm\\
&=c\int_Gg\,v\,P(gv)\,dm
=c\langle gv,P(gv)\rangle_m.
\end{aligned}
\tag{134.16}
$$

Every expression is finite: $g\in L^2(m)$ and $v\in L^\infty(m)$ imply $gv\in L^2(m)$, and $P$ is an $L^2$ contraction. Since the original semigroup is self-adjoint,

$$
\langle u,Pu\rangle_m
=\langle T_{d/2}u,T_{d/2}u\rangle_m
=\|T_{d/2}u\|_2^2
\qquad(u\in L^2(m;\mathbb R)).
\tag{134.17}
$$

Strict positivity uses the same spectral-calculus mechanism as Proposition 124.1. If $E_K$ denotes the spectral resolution of the full nonnegative self-adjoint $K$, then

$$
\|T_{d/2}u\|_2^2
=\int_{[0,\infty)}e^{-d\lambda}
\,d\langle u,E_K(\lambda)u\rangle_m.
\tag{134.18}
$$

The spectral measure has total mass $\|u\|_2^2$, and its multiplier $e^{-d\lambda}$ is strictly positive at every finite $\lambda\ge0$. Therefore the integral is strictly positive for every nonzero $u$. For a nonzero bounded $m$-class $v$, strict positivity of $g$ almost everywhere implies $gv\ne0$ in $L^2(m)$. Together with $c>0$, (134.16)–(134.18) prove (134.13) on the entire real $L^\infty$ space. The symmetric polar form is explicitly

$$
B_{003}(u,v)
=c\langle T_{d/2}(gu),T_{d/2}(gv)\rangle_m.
\tag{134.19}
$$

Next retain every first-order equation exactly. The Markov contractions and $\int g\,dm=1$ give, for all real bounded inputs,

$$
|\mathcal C(u,v,w)|
\le\|u\|_\infty\|v\|_\infty\|w\|_\infty.
\tag{134.20}
$$

Thus each of the 64 components of $\Lambda$ is a finite real linear functional on $L^\infty(m)$. In particular, (134.12) is an exact system of at most 64 independent linear constraints; no rank optimization is needed.

Fix any integer $N\ge1$. Nonatomicity of the Borel probability $m$ supplies $N+64$ pairwise disjoint positive-measure Borel subsets $A_1,\ldots,A_{N+64}$ of $E=G$. Their indicators are linearly independent as $m$-classes. On their span

$$
F_N=\operatorname{span}_{\mathbb R}
\{\mathbf1_{A_1},\ldots,\mathbf1_{A_{N+64}}\},
\qquad \dim F_N=N+64,
$$

apply finite-dimensional rank-nullity to the full map $\Lambda|_{F_N}:F_N\to\mathbb R^{64}$. It gives

$$
\dim(F_N\cap V)
=N+64-\operatorname{rank}(\Lambda|_{F_N})\ge N.
\tag{134.21}
$$

All 64 equations are imposed in this intersection, not merely a selection of slotwise or marginal constraints. Since $N$ was arbitrary, $V$ is infinite-dimensional. These finite-dimensional subspaces consist of bounded real Borel classes; in particular $V$ contains a nonzero such class. More generally a bounded class can be represented by a bounded Borel function after repairing its exceptional null set. Such repairs leave all coefficients unchanged, since the positive-time source laws are absolutely continuous with respect to $m$ and the semigroup acts on $m$-classes.

Finally, strict positivity in (134.13) survives restriction to $V$. Choosing any nonzero $v\in V$ shows that $q_{003}|_V$ is not the zero form, so it is a nonzero actual member of $\mathcal Q_E$. No nonzero vector in $V$ has negative value under this form. There is therefore no positive-dimensional negative-definite subspace, and its negative index is exactly zero. This proves (134.14) and contradicts the stated all-nonzero-pencil requirement for this actual readout. $\square$

**Remark 134.3 (scope and mathematical attribution).** The source-specific coefficient deduction (134.15)–(134.16), combined with the exact constrained span (134.12), is `repo-derived` relative to the cited suppliers. Source propagation is supplied by (117.3); spectral positivity and injectivity are the mature spectral-calculus mechanism already used in Proposition 124.1; the finite-codimension argument is ordinary finite-dimensional rank-nullity. These are intermediates within Proposition 134.2, not separate new theorems. The source-specific deduction carries no exhaustive-search or worldwide-novelty claim.

The obstruction concerns the universal all-nonzero-pencil hypothesis for the actual joint coefficients, at $t=2d$ and both gaps $d$, on the prescribed overlap $E=G$ of this fixed common readout. The constants $M,c$ may depend on the fixed original $a,\eta,d$; the argument uses no parameter-uniform estimate. It does not replace the original model by another density, another source or another semigroup.

Lemma 125.3 remains valid as a conditional statement. Its positive-dimensional restricted-span branch requires every nonzero pencil to have infinite negative index, a premise that Proposition 134.2 shows is unavailable here. Its zero-span branch also remains valid: when all restricted quadratic forms vanish, one may choose a plane in the infinite-dimensional linear kernel and use oddness of the homogeneous cubic, exactly as in §125. For the present readout, (134.14) shows that the restricted span is nonzero, so that branch does not apply to this example.

The scalar marginal result of Corollary 133.3, with its complete hypotheses and parameter range, remains valid. Infinite negative index for its marginal combinations does not imply the all-pencil hypothesis for the individual joint coefficients, and Proposition 134.2 supplies no reversal of that implication. The compact-fiber and deterministic-approximation conclusions of Proposition 123.2 and the factorization obstructions of §124 retain their stated scopes.

The existence of deterministic representatives in every full 64-coordinate common-readout fiber, the general joint quadratic and cubic requirements for such a construction, and any native or physical realization remain unresolved here. Proposition 134.2 refutes the specified universal negative-index premise for the joint-coefficient route; it is not a counterexample to purification itself.

## 追加锚（本行以下为增补区）

## 135. The prescribed rank-two slice and the actual terminal correction

**Definition 135.1 (the unchanged source and the full marginal partition class).** Retain the entire telescope of Definition 134.1, including (134.1)–(134.12), all its original hypotheses and the complete inherited suppliers of Appendix II §§115–117, 123–125 and 133. Thus $a,\eta,d>0$ are arbitrary original finite parameters, $G=H^1\times\mathbb R$ has the product in (134.1), $e=(0,0,0,0)$, and the raw Haar measure is $d\mu=dx\,dy\,dz\,d\zeta$. The original unit-source field satisfies $L\Gamma=\delta_e$, with $X_1=\partial_x$, $X_2=\partial_y+x\partial_\zeta$, $X_3=\partial_z$, $L=-\sum_{r=1}^3X_r^2$, $D_\zeta=-i\partial_\zeta$ and $g_c=16\sqrt{a\eta}$. Keep the coefficient-one vector $w_*$, the coefficient-positive normalization $h=w_*/\|w_*\|_{L^2(\mu)}$, and precisely the actual selector

$$
\begin{gathered}
S=(aL+\eta D_\zeta^2-g_c\Gamma)|_{C_c^\infty(G\setminus\{e\};\mathbb C)},\qquad
\rho=\frac{A_{\rm src}(h)}{C_{\rm src}(h)},\qquad C_{\rm src}(h)>0,\\
D(H_{\rm end})=\{u\in D(S^*):A_{\rm src}(u)=\rho C_{\rm src}(u)\},\qquad H_{\rm end}u=S^*u,\\
m=h^2\mu,\qquad m(G)=1,\qquad U_hv=hv,\qquad
K=U_h^{-1}H_{\rm end}U_h\ge0,\qquad T_s=e^{-sK}.
\end{gathered}
$$

The source coefficients and central units are those already fixed in Definition 134.1. The full form domain is still $\mathscr V=\mathscr V_0\dotplus\mathbb C1$ with the closure and energy in (134.3); it is not its killed part. The measure $m$ is the same nonatomic Borel probability, absolutely continuous with respect to the raw Haar measure, with $m(\{e\})=0$. The actual conservative diffusion starts at $e$ at original time zero, and the three observation epochs remain $2d,3d,4d$. Its supplied real densities satisfy

$$
g_s>0\quad m\text{-a.e.},\qquad
g_s\in L^2(m),\qquad \int_Gg_s\,dm=1,\qquad
g_{s+r}=T_rg_s\quad(s>0,\ r\ge0).
$$

Conservation, self-adjointness, positivity improvement at every positive time, and $\ker K=\mathbb C1$ are the original endpoint and source suppliers. In particular $T_s1=1$ and the real $L^2(m)$ subspace is preserved. The finite bound needed below is exactly Theorem 133.2 for this fixed tuple; no parameter-uniform estimate is assumed. Set, as before,

$$
P=T_d,\qquad g=g_{2d},\qquad
M=1+\|g_d\|_{L^\infty(m)}<\infty,\qquad c=\frac1{4M},
$$

and allow any real Borel representative $b$ with $[b]=g_d$ and $0<b\le M$ at every point of the whole $G$. With $\mathcal L=\{0,1,3,B\}$ keep

$$
f_3=cb,\qquad f_B=\frac14,\qquad
f_0=f_1=\frac{3/4-cb}{2},\qquad
\mathcal C(u,v,w)=\int_Gg\,u\,P(vPw)\,dm.
$$

Define $\mathscr D_{12}(a,\eta,d,b)$ to consist of single pointwise Borel partitions $D=(D_y)_{y\in\mathcal L}$ of the whole $G$, pairwise disjoint with union $G$, satisfying all twelve equalities

$$
\int_Gg_{rd}\mathbf1_{D_y}\,dm
=\int_Gg_{rd}f_y\,dm
\qquad(r\in\{2,3,4\},\ y\in\mathcal L).
$$

In the fixed order $(0,1,3,B)$, distinguish the prescribed stochastic slice and the actual partition slice:

$$
\begin{aligned}
A^f_{yz}&=\mathcal C(f_y,f_z,f_3),\\
q_D&=P\mathbf1_{D_3},\\
A^D_{yz}&=\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_3})
=\int_Gg\mathbf1_{D_y}P(\mathbf1_{D_z}q_D)\,dm.
\end{aligned}
$$

All pairings and matrix ranks below are real. In particular $q_D$ is the actual terminal factor in $A^D$; the propagation identity $Pf_3=cg$ describes the prescribed readout and does not identify $q_D$ with $cg$.

**Proposition 135.2 (rank target, unavoidable terminal discrepancy and exact cancellation criterion).** Under Definition 135.1, for every allowed tuple the class $\mathscr D_{12}(a,\eta,d,b)$ is nonempty, every $D$ in that class satisfies $m(D_y)>0$ for each $y\in\mathcal L$, and

$$
\operatorname{rank}A^f=2.
$$

For every $D\in\mathscr D_{12}(a,\eta,d,b)$, write $q=q_D$ and $\delta=q-cg$. Then

$$
\begin{gathered}
0<q<1\quad m\text{-a.e.},\qquad \delta\ne0\text{ in }L^2(m),\\
\langle b,\delta\rangle_m
=\langle g_{2d},\delta\rangle_m
=\langle g_{3d},\delta\rangle_m=0,\\
m(\{\delta>0\})>0,\qquad m(\{\delta<0\})>0,
\qquad q/g\text{ is not constant }m\text{-a.e.}
\end{gathered}
$$

Define the separate comparison and correction matrices by

$$
\begin{aligned}
(B_D)_{yz}&=c\langle g\mathbf1_{D_y},P(g\mathbf1_{D_z})\rangle_m,\\
(E_D)_{yz}&=\langle g\mathbf1_{D_y},P(\delta\mathbf1_{D_z})\rangle_m.
\end{aligned}
$$

The matrix $B_D$ is symmetric positive definite, of rank four, while

$$
A^D=B_D+E_D.
$$

With the positive definite square root of $B_D$, put

$$
F_D=B_D^{-1/2}E_DB_D^{-1/2}.
$$

The actual matrix $A^D$ and $F_D$ need not be symmetric. The exact finite-dimensional criterion is

$$
\begin{gathered}
\operatorname{rank}A^D=4-\dim_{\mathbb R}\ker(I_4+F_D),\\
\operatorname{rank}A^D\le2
\quad\Longleftrightarrow\quad
\dim_{\mathbb R}\ker(I_4+F_D)\ge2,\\
\operatorname{rank}A^D\le2\quad\Longrightarrow\quad
\operatorname{rank}E_D\ge2.
\end{gathered}
$$

Thus the requirement at $-1$ is a geometric eigenspace dimension of at least two, not merely an algebraic multiplicity. The prescribed terminal marginal masses also satisfy

$$
t_r:=\int_Gg_{rd}f_3\,dm
=c\langle b,P^{r-1}b\rangle_m\quad(r\in\{2,3,4\}),
\qquad 0<t_4<t_3<t_2\le\frac14.
$$

These source-specific deductions are `repo-derived` relative to Definition 134.1 and its inherited suppliers. The finite linear vector-measure theorem, spectral calculus and finite-rank algebra used in the proof are attributed intermediates, rather than separate new general theorems.

*Proof.* First obtain the common partition for the fixed linear marginals. On the Borel sigma-algebra of the original whole $G$, let

$$
\nu_r(A)=\int_Ag_{rd}\,dm,\qquad r=2,3,4.
$$

These are three finite probability measures, each absolutely continuous with respect to coordinate Lebesgue measure. For any Borel $A$, the function $t\mapsto\nu_r(A\cap\{x\le t\})$ is continuous: coordinate hyperplanes have Lebesgue measure zero, so dominated convergence gives continuity at every $t$. Its limits at the two ends of the real line are $0$ and $\nu_r(A)$. If $\nu_r(A)>0$, it therefore attains $\nu_r(A)/2$, proving atomlessness on this very Borel space. The pointwise Borel vector $(f_y)_{y\in\mathcal L}$ has nonnegative entries summing to one. Apply Dvoretzky–Wald–Wolfowitz, [*Relations among certain ranges of vector measures*, Pacific J. Math. 1 (1951), 59–74, §3 Theorem 4 and Lemma 2](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), with these three measures and four labels. Its equality of probability-vector and decomposition-vector ranges, with the definitions on pp. 59–60 and Lemma 2 on pp. 66–67, gives one Borel partition preserving all twelve entries simultaneously. Since $g_{rd}>0$ almost everywhere and every $f_y>0$ everywhere, each prescribed entry is strictly positive. Hence each cell of every marginal-feasible partition has positive $m$-measure. This use of the theorem preserves fixed linear integrals only; it does not prescribe the partition-dependent terminal factor or the joint coefficients.

For the rank computation, the spectral-calculus identity already used in §134 gives, for real $u\in L^2(m)$ and $s>0$,

$$
\|T_su\|_2^2
=\int_{[0,\infty)}e^{-2s\lambda}\,d\langle u,E_K(\lambda)u\rangle_m.
$$

The multiplier is strictly positive at every finite $\lambda\ge0$. Thus $T_s$ is injective, and $\langle u,Pu\rangle_m=\|T_{d/2}u\|_2^2>0$ when $u\ne0$.

The class $b$ is nonconstant. Indeed, if it were constant, mass one would force $g_d=1$. For every $0<u<d$, propagation and conservation would then give $T_{d-u}(g_u-1)=0$, hence $g_u=1$ by injectivity. Choose a nonzero nonnegative continuous compactly supported function $\psi$ away from $e$. Strict positivity of $h$ off $e$ gives $\int_G\psi\,dm>0$. On the other hand the continuous source start implies $\mathbb E_e[\psi(Z_u)]\to\psi(e)=0$ as $u\downarrow0$, by bounded convergence. The supplied density formula with $g_u=1$ would make all these expectations equal to the fixed positive integral. This contradiction proves nonconstancy without replacing the source law by a stationary initial law.

Let $b^0=1$ and define a real $2$-by-$2$ matrix and a real $4$-by-$2$ matrix by

$$
H_{ij}=\langle gb^i,P(gb^j)\rangle_m\quad(i,j\in\{0,1\}),\qquad
R=\begin{pmatrix}
3/8&-c/2\\
3/8&-c/2\\
0&c\\
1/4&0
\end{pmatrix}.
$$

All entries are finite because $g\in L^2(m)$, $b$ is bounded and $P$ is an $L^2$ contraction. The classes $g,gb$ are linearly independent: $g>0$ almost everywhere would otherwise make $b$ constant. For $\xi=(\xi_0,\xi_1)\ne0$,

$$
\xi^{\mathsf T}H\xi
=\|T_{d/2}(g(\xi_0+\xi_1b))\|_2^2>0.
$$

Thus $H$ is positive definite. The rows of $R$ express the four $f_y$ in the basis $(1,b)$. Propagation gives $Pf_3=cPb=cg$ as an $m$-class, and consequently

$$
A^f=cRHR^{\mathsf T}.
$$

The minor of $R$ formed by rows $3,B$ has determinant $-c/4\ne0$. Hence $\operatorname{rank}R=2$, and positive definiteness of $H$ gives $\ker A^f=\ker R^{\mathsf T}$; rank-nullity proves $\operatorname{rank}A^f=2$. This argument concerns the prescribed stochastic slice alone.

Now fix any $D\in\mathscr D_{12}(a,\eta,d,b)$. Both $\mathbf1_{D_3}$ and $1-\mathbf1_{D_3}$ are nonzero nonnegative $L^2(m)$ classes. Positivity improvement of the original semigroup, as supplied in Theorem 117.2 using the irreducibility equivalence of Lenz–Stollmann–Veselić, [*The Allegretto–Piepenbrink Theorem for Strongly local forms*, Theorem 1.1](https://arxiv.org/html/0811.2135v1#S1.Thmtheorem1), gives $P\mathbf1_{D_3}>0$ and $P(1-\mathbf1_{D_3})>0$ almost everywhere. Conservation therefore proves $0<q<1$ almost everywhere.

Put $v=\mathbf1_{D_3}-cb$. It is a bounded real class, and $\delta=Pv\in L^2(m)$. If $\delta=0$, injectivity of $P$ would give $\mathbf1_{D_3}=cb$ almost everywhere, impossible because $0<cb\le1/4$ everywhere. For the three moment identities, the label-$3$ marginal constraints say

$$
\langle g_{2d},v\rangle_m
=\langle g_{3d},v\rangle_m
=\langle g_{4d},v\rangle_m=0.
$$

Since $Pb=g_{2d}$, $Pg_{2d}=g_{3d}$ and $Pg_{3d}=g_{4d}$, self-adjointness gives exactly

$$
\langle b,\delta\rangle_m=\langle Pb,v\rangle_m=0,\qquad
\langle g_{2d},\delta\rangle_m=\langle Pg_{2d},v\rangle_m=0,\qquad
\langle g_{3d},\delta\rangle_m=\langle Pg_{3d},v\rangle_m=0.
$$

All pairings are finite by boundedness of $b$, the $L^2$ density bounds and the contraction property. Nonzero $\delta$, strict positivity of $b$ and $\langle b,\delta\rangle_m=0$ force both sign sets of $\delta$ to have positive measure. If $q/g$ were a constant $k$ almost everywhere, this same moment equation would give $(k-c)\langle b,g\rangle_m=0$. The last inner product is finite and strictly positive, so $k=c$, contradicting $\delta\ne0$. No identity $\int_G\delta\,dm=0$ is used or asserted.

The comparison matrices are well defined: $g\mathbf1_{D_y}$ and $\delta\mathbf1_{D_z}$ are in real $L^2(m)$. For $x=(x_y)_{y\in\mathcal L}\in\mathbb R^4$,

$$
x^{\mathsf T}B_Dx
=c\left\|T_{d/2}\left(g\sum_{y\in\mathcal L}x_y\mathbf1_{D_y}\right)\right\|_2^2.
$$

If $x\ne0$, disjointness and positive measure of every cell, together with $g>0$ almost everywhere, make the vector inside $T_{d/2}$ nonzero. Injectivity proves positive definiteness of the symmetric $B_D$. Substitute the exact equality $q=cg+\delta$ in the actual coefficient, retaining its actual terminal factor:

$$
\begin{aligned}
A^D_{yz}
&=\langle g\mathbf1_{D_y},P(\mathbf1_{D_z}q)\rangle_m\\
&=c\langle g\mathbf1_{D_y},P(g\mathbf1_{D_z})\rangle_m
+\langle g\mathbf1_{D_y},P(\delta\mathbf1_{D_z})\rangle_m.
\end{aligned}
$$

This proves $A^D=B_D+E_D$. Ordinary finite-dimensional square-root algebra gives

$$
A^D=B_D^{1/2}(I_4+F_D)B_D^{1/2}.
$$

Multiplication by the invertible square roots preserves rank. Rank-nullity for $I_4+F_D$ proves the displayed rank formula and its equivalent geometric-eigenspace condition, without a symmetry assumption on $F_D$. Finally,

$$
4=\operatorname{rank}B_D
=\operatorname{rank}(A^D-E_D)
\le\operatorname{rank}A^D+\operatorname{rank}E_D
$$

proves the correction-rank requirement when $\operatorname{rank}A^D\le2$. Positive definiteness of the comparison matrix has not been transferred to the actual matrix.

For the marginal masses, propagation gives $g_{rd}=P^{r-1}b$, so self-adjointness proves the stated formula for $t_r$. Let $\sigma_b$ be the spectral measure of $b$ for $K$. Since $\ker K=\mathbb C1$ and $b$ is nonconstant, $\sigma_b((0,\infty))>0$. For $r=2,3$,

$$
t_r-t_{r+1}
=c\int_{[0,\infty)}e^{-(r-1)d\lambda}(1-e^{-d\lambda})\,d\sigma_b(\lambda)>0.
$$

The integrand is strictly positive on $(0,\infty)$. Also $t_4>0$ follows from $g_{4d}>0$ almost everywhere and $f_3>0$, and $t_2\le1/4$ follows from $f_3\le1/4$ and the mass-one density. No spectral gap or numerical rank approximation enters any of these conclusions. $\square$

**Proposition 135.3 (the necessary parent consequence and the remaining quantifiers).** Under Definition 135.1, if a full pointwise Borel partition $D$ attains all $64$ prescribed coordinates,

$$
\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
=\mathcal C(f_y,f_z,f_w)
\qquad(y,z,w\in\mathcal L),
$$

then $D\in\mathscr D_{12}(a,\eta,d,b)$, $A^D=A^f$, and $\operatorname{rank}A^D=2$. For fixed $a,\eta,d$, changing only the allowed null-set representative $b$ leaves this marginal-feasible class, every actual matrix $A^D$, and the prescribed $64$ coordinates unchanged.

Let $\Theta$ denote all tuples $(a,\eta,d,b)$ allowed by Definition 135.1. The all-partition rank obstruction is precisely the following unresolved statement, equivalently written using Proposition 135.2:

$$
\begin{aligned}
&\exists\theta\in\Theta\ \forall D\in\mathscr D_{12}(\theta),
&&\operatorname{rank}A^D\ge3,\\
\Longleftrightarrow\quad
&\exists\theta\in\Theta\ \forall D\in\mathscr D_{12}(\theta),
&&\dim_{\mathbb R}\ker(I_4+F_D)\le1.
\end{aligned}
$$

Its negation requires the fully quantified alternative

$$
\begin{aligned}
&\forall\theta\in\Theta\ \exists D\in\mathscr D_{12}(\theta),
&&\operatorname{rank}A^D\le2,\\
\Longleftrightarrow\quad
&\forall\theta\in\Theta\ \exists D\in\mathscr D_{12}(\theta),
&&\dim_{\mathbb R}\ker(I_4+F_D)\ge2.
\end{aligned}
$$

The obstruction, if established, excludes full $64$-coordinate attainment for its tuple. Neither quantified alternative, nor full $64$-coordinate attainment, is established by Proposition 135.2. Its marginal feasibility, terminal sign and moment identities, nonconstant ratio and positive comparison matrix supply no bound excluding the required cancellation for all feasible partitions. The forward necessary condition above supplies no converse from rank two to equality with $A^f$ or to attainment of the full law; a low-rank construction would still have to satisfy those additional equalities.

*Proof.* For either common simplex tuple $u=f$ or $u_y=\mathbf1_{D_y}$, summation over the other two labels, conservation and self-adjoint propagation give the three slot marginals:

$$
\begin{aligned}
\sum_{z,w\in\mathcal L}\mathcal C(u_y,u_z,u_w)
&=\mathcal C(u_y,1,1)=\langle g_{2d},u_y\rangle_m,\\
\sum_{y,w\in\mathcal L}\mathcal C(u_y,u_z,u_w)
&=\mathcal C(1,u_z,1)=\langle Pg_{2d},u_z\rangle_m
=\langle g_{3d},u_z\rangle_m,\\
\sum_{y,z\in\mathcal L}\mathcal C(u_y,u_z,u_w)
&=\mathcal C(1,1,u_w)=\langle P^2g_{2d},u_w\rangle_m
=\langle g_{4d},u_w\rangle_m.
\end{aligned}
$$

Equality of the two full laws therefore implies all twelve marginal equations. Fixing the third label to $3$ gives $A^D=A^f$, and Proposition 135.2 then gives rank two. Consequently a tuple for which every marginal-feasible partition has rank at least three cannot have a partition attaining the full law.

For representative invariance, the essential norm defining $M$ and $c$ is unchanged. Any two allowed $b$ differ only on an $m$-null set, so their $f_y$ are the same bounded $m$-classes, their marginal targets agree, and $\mathcal C$ has the same values. The actual formula for $A^D$ contains no chosen representative $b$. Likewise any Borel null-set alteration of a finite partition, if kept disjoint and exhaustive, preserves its indicator classes, its marginal integrals and its actual coefficients. If one begins with completed-measurable partition classes, take finitely many Borel representatives, contain their exceptional overlaps and missing points in a Borel null set, and assign that set to one label after removing it from the other cells. This gives a full Borel partition with the same classes. All three observation epochs are positive and their laws are absolutely continuous with respect to $m$; no assertion about a time-zero read or its value at $e$ follows from this invariance.

Finally $\operatorname{rank}A^D$ is an integer between zero and four. Thus the negation of rank at least three is rank at most two, and Proposition 135.2 identifies these alternatives with the respective nullity conditions. Negating the existential universal statement interchanges its two quantifiers and gives exactly the displayed universal existential alternative. The marginal-feasibility argument proves nonemptiness of each partition class; it yields no bound on this nullity. Representative invariance removes only the null-set choice of $b$, retaining the quantifiers over the original $a,\eta,d$. The compact-fiber and approximation statements of §123, the factorization statements of §124, the conditional constructions of §125, the scalar marginal result of §133 and the joint-pencil result of §134 retain their stated scopes. The full common-readout attainment problem and any native or physical realization remain unresolved here. $\square$

## 追加锚（本行以下为增补区）

## 136. Invariant coarse partitions of the original marginal class

**Definition 136.1 (the actual invariant coarse interface).** Fix any original tuple $\theta=(a,\eta,d,b)\in\Theta$ of Definition 135.1, with every endpoint, source and regularity hypothesis inherited there. All subsequent statements retain this entire telescope. In particular, the group product, raw measure $\mu$, unit-source field $\Gamma$, actual selector, coefficient-positive normalized $h$, probability $m=h^2\mu$, full conservative operator $K$ and its source summand remain unchanged. The diffusion starts at the original source $e$, and the observation epochs are $2d,3d,4d$. Retain $P=T_d$, $g=g_{2d}$ and the original $b,M,c,f,t_r$ of §135.

Use symmetric coordinates $\xi=\zeta-xy/2$ and cylindrical coordinates $(r,\alpha,z,\xi)$ where $r>0$. Let $R_\gamma$ rotate $(x,y)$ through $\gamma$ while fixing $(z,\xi)$, and set

$$
\Omega=\{r>0\},\qquad N=G\setminus\Omega=\{x=y=0\},\qquad
X=(0,\infty)\times\mathbb R^2,\qquad
\pi(r,\alpha,z,\xi)=(r,z,\xi).
$$

The full-form rotation symmetry, including the source trace and original source law, is the one proved in Appendix II §120. In particular $m$, every $g_s$, and $T_s$ are invariant under this circle action, $m(N)=0$, and $T_s$ commutes with its pullbacks. The analytic heat-image and local differential suppliers are Appendix II (120.6)–(120.11), (122.6)–(122.11), (122.20)–(122.23), and the corresponding actual-operator uses in §§126 and 129. They concern the full extension off the source; no differential identity through the source is required. The finite global bound used here is exactly Theorem 133.2 for the fixed tuple. Markov propagation gives $\|g\|_\infty\le\|g_d\|_\infty<M$.

Write

$$
\nu_j(A)=\int_Ag_{jd}\,dm\quad(j=2,3,4).
$$

Let $\mathscr E_\theta$ be the class of pointwise Borel partitions $E=(S,C,B)$ of the whole $G$ whose three cells are invariant under every $R_\gamma$ and satisfy

$$
\nu_j(S)=\frac34-t_j,\qquad
\nu_j(C)=t_j,\qquad
\nu_j(B)=\frac14
\quad(j=2,3,4).
\tag{136.1}
$$

For each $E\in\mathscr E_\theta$, define its single actual terminal factor, ordered bilinear form, quadratic form and coarse matrix by

$$
\begin{aligned}
q_E&=P\mathbf1_C,\\
Q_E(u,v)&=\int_Gg\,u\,P(q_Ev)\,dm,\qquad Q_E(v)=Q_E(v,v),\\
(A_E)_{ij}&=Q_E(\mathbf1_{E_i},\mathbf1_{E_j}),
\qquad (E_1,E_2,E_3)=(S,C,B).
\end{aligned}
\tag{136.2}
$$

These forms and matrices are real and need not be symmetric. For an invariant Borel simplex tuple $u=(u_S,u_C,u_B)$, define analogously

$$
q_u=Pu_C,\qquad (A(u))_{ij}=\mathcal C(u_i,u_j,u_C).
\tag{136.3}
$$

Call $u$ admissible when its components lie in $[0,1]$, sum to one everywhere and have the nine integrals in (136.1). Its third argument is its own $u_C$.

**Proposition 136.2 (nonempty invariant coarse class and the original targets).** For every original $\theta$, the class $\mathscr E_\theta$ is nonempty. There is a bounded pointwise invariant Borel function $\beta$ with $0<\beta\le M$ everywhere and $[\beta]=[b]=g_d$. Replacing $b$ by this representative for a computation changes none of the original marginal targets, prescribed coordinates, or partition classes. For every $E\in\mathscr E_\theta$,

$$
0<q_E<1\quad m\text{-a.e.},\qquad
q_E/g\text{ is not constant }m\text{-a.e.}
\tag{136.4}
$$

*Proof.* The quotient probability and the three quotient source measures are

$$
d\bar m=2\pi r h(r,z,\xi)^2\,dr\,dz\,d\xi,
\qquad d\bar\nu_j=g_{jd}\,d\bar m.
\tag{136.5}
$$

Here the invariant smooth representative of $h$ is used. The change from $\zeta$ to $\xi$ has Jacobian one, and angular integration gives (136.5). The omitted axis is null for all four measures. Every invariant Borel cell on $\Omega$ is the inverse image of a Borel subset of $X$: evaluate membership on the Borel section $\alpha=0$ and use invariance on its circular orbit. Each quotient measure is finite and atomless, being absolutely continuous with respect to three-dimensional Lebesgue measure. For example, slicing any Borel set by the $r$ coordinate gives a continuous distribution, hence a proper subdivision of every set of positive measure.

Angular averaging of the original bounded Borel $b$ gives a Borel quotient function

$$
\bar\beta(r,z,\xi)=\frac1{2\pi}\int_0^{2\pi}b(r,\alpha,z,\xi)\,d\alpha.
$$

It lies in $(0,M]$ everywhere on $X$. Invariance of the $L^2$ class $g_d$ and Fubini's theorem show that its lift equals $b$ almost everywhere. Give its lift the value $1$ on $N$. This is the asserted $\beta$. On any open patch where the analytic representative of $g_d$ is strictly positive it can, without changing its class, be taken equal to that analytic representative: the latter is invariant, nonnegative and at most $\|g_d\|_\infty<M$ by continuity and full local support of $m$. Repair the remaining exceptional invariant null set within $(0,M]$. All these choices have the same integrals.

Apply the finite atomless vector-measure theorem of Dvoretzky–Wald–Wolfowitz, [*Relations among certain ranges of vector measures*, Pacific J. Math. 1 (1951), §3 Theorem 4 and Lemma 2, pp. 66–67](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), on $X$, to the three measures $\bar\nu_j$ and the simplex tuple

$$
u^0=(3/4-c\bar\beta,c\bar\beta,1/4).
\tag{136.6}
$$

Their equality of probability-vector and decomposition-vector ranges gives one Borel three-cell partition of $X$ with all nine prescribed integrals. Pull all cells back by $\pi$ and put the whole axis in $S$. This is an invariant whole-$G$ partition satisfying (136.1). This application fixes linear integrals only.

Since $0<t_j\le1/4$, the cells $C$ and $G\setminus C$ both have positive $m$-measure. Positivity improvement and conservation give $0<P\mathbf1_C<1$ almost everywhere, as in Proposition 135.2. If $q_E=\lambda g$, then $g=P\beta$ and injectivity of $P$, proved by spectral calculus in §135, imply $\mathbf1_C=\lambda\beta$ almost everywhere. Positivity forces $\lambda>0$, contradicting the positive measure of $G\setminus C$ and $\beta>0$ almost everywhere. This proves (136.4) without replacing $q_E$ by $cg$.

Finally all allowed representatives of $b$ give the same $M,c$ and bounded classes $f_y$. Proposition 135.3 or direct integration shows that every original target is unchanged. No value of an observation at time zero is inferred from this representative invariance. $\square$

## 137. Two-sided odd index with the coarse terminal cell fixed

**Theorem 137.1 (actual odd two-weight index).** For every original $\theta$ and every fixed $E=(S,C,B)\in\mathscr E_\theta$, the form $Q_E$ has infinite positive and negative indices on the real vector space

$$
\mathcal V_{S,-}=\{v\in L^\infty(G,m;\mathbb R):
v=0\text{ a.e. on }G\setminus S,\quad v\circ R_\pi=-v\text{ a.e.}\}.
\tag{137.1}
$$

Each index remains infinite on the common kernel of any finite family of homogeneous bounded real linear functionals on this space. The cells $S,C,B$ and the terminal factor $q=q_E$ remain fixed in all these assertions.

*Proof.* Use the analytic representatives of $g$ and $q=T_d\mathbf1_C$ on $\Omega$. They are nonnegative and invariant there by continuity, the Markov property and full local support of $m$, and both are strictly positive almost everywhere. Set $\sigma=d/2$, $R=R_\pi$ and let $L^2_-$ be the complex odd subspace. Equip

$$
\mathcal H_-=T_\sigma L^2_-,\qquad
\|T_\sigma u\|_{\mathcal H_-}=\|u\|_2
\tag{137.2}
$$

with its inverse-heat norm. Injectivity makes this well defined. Use the half-circle section $F=\{r>0,\ 0\le\alpha<\pi\}$. Every odd function is determined by its restriction to $F$. The evaluation and kernel identities of Appendix II §120 show that this restriction is a Hilbert function space with kernel

$$
k(x,y)=\frac{p_d(x,y)-p_d(x,Ry)}2.
\tag{137.3}
$$

Indeed the projection onto $L^2_-$ is $(I-R)/2$, which commutes with heat propagation. For distinct representatives $x_1,\ldots,x_n\in F$, the $2n$ points $x_i,Rx_i$ are distinct. The full heat-kernel Gram quadratic form on coefficients $(a_1,\ldots,a_n,-a_1,\ldots,-a_n)$ is

$$
4\sum_{i,j}\overline{a_i}a_jk(x_i,x_j)>0
\quad(a\ne0).
\tag{137.4}
$$

Thus $k$ is nonsingular on $F$.

Every member of $\mathcal H_-$ is analytic on the connected open set $\Omega$, by the actual heat-image identity (122.11). This identity uses the analytic coefficients from (122.6)–(122.9), the local weak equation (120.6), and the spectral differential-iterate bounds (122.10). The analytic regularity intermediary is Kotake–Narasimhan, [*Regularity theorems for fractional powers of a linear elliptic operator*, Theorem 1, p. 451](https://www.numdam.org/item/BSMF_1962__90__449_0.pdf). Products and sums of these analytic functions remain analytic. Consequently every positive-measure subset of the interior of $F$ is a uniqueness set both for $\mathcal H_-$ and for $\mathcal H_-\mathcal H_-+\mathcal H_-\mathcal H_-$. Here one applies Mityagin, [*The zero set of a real analytic function*, Proposition 0](https://arxiv.org/html/1512.07276v1), to the real and imaginary parts of the differences on $\Omega$. Local equivalence of $m$ and Lebesgue measure supplies its positive-measure hypothesis. These are attributed analytic intermediates for the actual heat space.

Write $Q^{\rm sym}(u,v)=(Q_E(u,v)+Q_E(v,u))/2$. Suppose that its negative index on $\mathcal V_{S,-}$ were finite, equal to $\kappa$. Choose a positive-measure relatively compact Borel subset $E_0\subset S\cap\operatorname{int}F$ on which $g+q>0$, and let $E_0^*$ consist of those points of $E_0$ which are its density points. Such a subset exists because $\nu_2(S)>0$, $g,q>0$ almost everywhere and $S$ is invariant. At distinct points $x_i\in E_0^*$ choose small disjoint neighborhoods, also disjoint from their reflected neighborhoods, and set

$$
\phi_{i,\epsilon}=
\frac{\mathbf1_{E_0\cap B(x_i,\epsilon)}}{m(E_0\cap B(x_i,\epsilon))},
\qquad v_{i,\epsilon}=\phi_{i,\epsilon}-\phi_{i,\epsilon}\circ R.
$$

These are bounded odd tests supported in $S$. Local continuity of the two weights and the actual heat kernel, and rotation invariance of the weights, give

$$
\bigl(Q^{\rm sym}(v_{i,\epsilon},v_{j,\epsilon})\bigr)_{i,j}
\longrightarrow 4\bigl(s(x_i,x_j)\bigr)_{i,j},
\qquad
s(x,y)=\frac{g(x)q(y)+q(x)g(y)}2\,k(x,y).
\tag{137.5}
$$

For completeness, the four reflected double integrals have kernel sum $2(p_d(x,y)-p_d(x,Ry))=4k(x,y)$; symmetrizing their weights gives precisely (137.5). Strict negativity of a fixed finite matrix subspace persists under entrywise convergence. Hence every finite Gram matrix of $s$ on $E_0^*$ has at most $\kappa$ negative eigenvalues. Repetitions of points follow by pullback from a distinct-point matrix.

Define the real invariant bounded class

$$
\gamma=\frac{g-q}{g+q}\quad\text{where }g+q>0,
\qquad \gamma=0\text{ on its null complement}.
$$

It satisfies $|\gamma|\le1$. On $E_0^*$ the exact identity is

$$
s(x,y)=\frac{(g(x)+q(x))(g(y)+q(y))}4
\bigl(1-\gamma(x)\gamma(y)\bigr)k(x,y).
\tag{137.6}
$$

The diagonal congruence is positive and invertible on every such finite point set. Real symmetric and complex Hermitian inertia agree for these real matrices. Therefore $(1-\gamma(x)\overline{\gamma(y)})k(x,y)$ has at most $\kappa$ negative squares on $E_0^*$.

Apply Agler–Young, [*Functions which are almost multipliers of Hilbert function spaces*, Theorem 2.1](https://arxiv.org/html/math/9605224v1#S2.Thmtheorem1), to $\mathcal H_-|_F$, with uniqueness domain $E_0^*$, multiplier $\gamma$ and their scalar parameter $t=1$. Nonsingularity is (137.4), and both required uniqueness hypotheses were checked above. The theorem gives a closed finite-codimensional $W\subset\mathcal H_-$ and a bounded $L:W\to\mathcal H_-$ with $Lu=\gamma u$ on $E_0^*$. Extend this relation by using the analytic identity

$$
(g+q)Lu=(g-q)u.
\tag{137.7}
$$

Both sides are analytic on all $\Omega$ because $g$ and $q=T_d\mathbf1_C$ are actual heat images. Positive-measure uniqueness makes (137.7) valid throughout $\Omega$. Since $g+q>0$ almost everywhere, $Lu=\gamma u$ in $L^2(m)$ globally. This argument requires no globally positive lower bound on $q$ or $g+q$.

Consider the actual multiplication domain

$$
D=\{u\in\mathcal H_-:\gamma u\in\mathcal H_-\}.
\tag{137.8}
$$

It contains $W$. Its quotient by $W$ is a subspace of the finite-dimensional space $\mathcal H_-/W$, hence $D$ is closed and finite codimensional. The inclusion $\mathcal H_-\hookrightarrow L^2(m)$ is continuous. If $u_n\to u$ in $\mathcal H_-$ and $\gamma u_n\to v$ there, bounded multiplication in $L^2$ gives $v=\gamma u$. Thus the multiplication map on $D$ has closed graph and is bounded.

The full rotation circle acts unitarily and strongly continuously on $\mathcal H_-$. Since $\gamma$ is invariant, $D$ and $D^\perp$ are invariant. The finite-dimensional circle representation on $D^\perp$ has only finitely many angular characters. Choose a positive odd integer $\ell$ absent from that list. The whole $\ell$ heat sector is contained in $D$. This sector is nonzero: take the heat image of a nonzero punctured smooth compact function of character $\ell$. If $K_\ell$ is the self-adjoint restriction of the full $K$ to this sector, boundedness on $D$ gives

$$
B_\ell=e^{\sigma K_\ell}M_\gamma e^{-\sigma K_\ell}
\quad\text{bounded on }L^2_\ell.
\tag{137.9}
$$

We give the commutator consequence explicitly. For $\Pi_R=\mathbf1_{[0,R]}(K_\ell)$, interpret

$$
F_R(z)=\Pi_Re^{zK_\ell}M_\gamma e^{-zK_\ell}\Pi_R
\tag{137.10}
$$

with spectral cutoffs on both sides. It is an entire bounded-operator-valued function, bounded on each closed vertical strip. On $\Re z=\sigma$, its norm is at most $\|B_\ell\|$, by unitary imaginary-time conjugation. On $\Re z=-\sigma$, use the adjoint of (137.9), since $\gamma$ is real, to obtain the same bound. Three-lines interpolation and Cauchy's estimate on the circle $|z|=\sigma/2$ give

$$
\|F_R'(0)\|\le 2\|B_\ell\|/\sigma.
\tag{137.11}
$$

For $u,v\in D(K_\ell)$, spectral convergence in the graph norm identifies the limit of the derivative pairing with

$$
\langle K_\ell u,\gamma v\rangle_m-
\langle\gamma u,K_\ell v\rangle_m.
$$

It is bounded by the right-hand constant of (137.11) times $\|u\|_2\|v\|_2$. Thus the commutator is a bounded form; no prior global domain invariance of multiplication is assumed. Whenever $v$ and $\gamma v$ are smooth compact punctured vectors, density of $D(K_\ell)$ identifies this form with the actual vector $[K,M_\gamma]v$ and bounds its norm by the same constant times $\|v\|_2$.

Choose a rotation-saturated compact patch inside $\{r>0,g+q>0\}$. On this patch $\gamma$ is smooth analytic. For an arbitrary compactly supported smooth amplitude $\chi(r,z,\xi)$ there and an arbitrary $\omega\in\mathbb R^3$, use the genuine punctured-core vectors

$$
u_N=e^{i\ell\alpha}\chi(r,z,\xi)e^{iN\omega\cdot(r,z,\xi)}.
$$

Both $u_N$ and $\gamma u_N$ belong to the original smooth punctured core. The original local principal symbol is

$$
a\left[p_r^2+\left(\frac{p_\alpha}{r}+\frac r2p_\xi\right)^2+p_z^2\right]+\eta p_\xi^2.
\tag{137.12}
$$

The divergence-form Leibniz identity (122.22), evaluated on these vectors, gives

$$
\begin{aligned}
[K,M_\gamma]u_N={}&-2iN e^{i\ell\alpha+iN\omega\cdot(r,z,\xi)}\chi\,
\left[a\gamma_r\omega_r+a\gamma_z\omega_z+
\left(\eta+\frac{ar^2}{4}\right)\gamma_\xi\omega_\xi\right]+O_{L^2}(1).
\end{aligned}
\tag{137.13}
$$

For fixed $\ell,\chi,\omega$, the remainder is bounded independently of $N$ and $\|u_N\|_2$ is independent of $N$. The commutator bound therefore makes the bracket vanish on the support of every such $\chi$. Taking the three coordinate directions for $\omega$, and using $a,\eta>0$, proves $\gamma_r=\gamma_z=\gamma_\xi=0$. Invariance gives $\gamma_\alpha=0$. On a connected open patch meeting $\{gq>0\}$ it follows that $\gamma=\gamma_0\in(-1,1)$. The analytic function

$$
g-q-\gamma_0(g+q)
$$

vanishes on that open patch, hence on connected $\Omega$. It follows that $q/g=(1-\gamma_0)/(1+\gamma_0)$ almost everywhere, contradicting (136.4). Thus the negative index is infinite. This uses infinitely many nonzero angular characters of the original operator, in addition to analytic uniqueness.

For the positive index, choose a density point $x\in S\cap\Omega$ where $g(x)q(x)>0$. Every rotated point on its orbit is also a density point of $S$: rotations preserve $S$ and have smooth invertible local coordinate maps. For any $n$, choose $n$ distinct representatives of this orbit in $\operatorname{int}F$. Both weights have their same positive values at all these points. The limiting matrix (137.5) is then

$$
4g(x)q(x)\bigl(k(x_i,x_j)\bigr)_{i,j},
$$

which is positive definite by (137.4). Small localized odd tests consequently give an $n$-dimensional positive-definite subspace. This proves infinite positive index.

Finally, in either sign choose a definite subspace of dimension $n+r$, where $r$ is the number of prescribed homogeneous scalar linear constraints. Its intersection with their common kernel has dimension at least $n$. Restriction preserves definiteness, proving both finite-constraint index assertions. No assertion about exact signs satisfying those extra constraints is used. $\square$

## 138. Exact odd sign cancellation and the original four-cell consumer

**Theorem 138.1 (a fixed-terminal exact sign).** For every original $\theta$ and every fixed $E=(S,C,B)\in\mathscr E_\theta$, there is a whole-$G$ Borel function $v$ such that

$$
v^2=\mathbf1_S\quad\text{everywhere},\qquad
v\circ R_\pi=-v\quad m\text{-a.e.},\qquad Q_E(v)=0.
\tag{138.1}
$$

The cells $C,B$ and $q_E$ are unchanged. If $S\cap N=\varnothing$, oddness may hold everywhere. If $S$ meets $N$, everywhere oddness and the everywhere identity $v^2=\mathbf1_S$ are incompatible.

*Proof.* Theorem 137.1 supplies bounded odd real tests $u_+,u_-$ supported in $S$ with $Q_E(u_+)>0>Q_E(u_-)$. Scale them into the unit ball without changing these strict signs. Their classes have Borel representatives which are exactly odd on $S\setminus N$: take representatives on the half-circle section $S\cap F$ and extend by reflection. Set them to zero elsewhere for the moment.

On the finite atomless standard Borel space $S\cap F$, signs are weak-star dense in the unit ball. To see the precise instance needed here, take refining finite Borel partitions generating its sigma-algebra. For a unit-ball function $u$ and each atom $A$, split $A$ into a Borel set of $m$-measure $\int_A(1+u)/2\,dm$ and its complement. Give the two pieces signs $+1,-1$. This matches $\int_Au\,dm$ exactly. Approximation of any $L^1$ test by simple functions from the refining partitions proves weak-star convergence. Reflect these signs oddly to $S\setminus N$ and give value zero outside $S$. The same convergence holds on $G$, since every $L^1$ pairing there reduces to a pairing on the section and its reflection.

The actual ordered kernel for $Q_E$ is

$$
a_E(x,y)=g(x)p_d(x,y)q_E(y)\ge0,\qquad
\|a_E\|_{L^1(m^2)}=\int_GgPq_E\,dm\le1.
\tag{138.2}
$$

For bounded weak-star convergent tests, approximation of $a_E$ in $L^1$ by finite sums $\sum_l a_l(x)b_l(y)$, with $a_l,b_l\in L^1(m)$, proves convergence of their quadratic values. Indeed each tensor pairing is the product of the two convergent scalar integrals, and the error is bounded by the kernel's $L^1$ approximation error uniformly on the unit ball. Thus the approximating Borel signs contain $\sigma_+,\sigma_-$ with

$$
Q_E(\sigma_+)>0>Q_E(\sigma_-).
$$

They are signs on $S\setminus N$, are exactly odd there and vanish outside $S$.

Let $A\subset S\cap F$ be their disagreement set. Choose nested Borel subsets $A_t\subset A$, $0\le t\le1$, with $A_0=\varnothing$, $A_1=A$ and $m(A_t)=t\,m(A)$. Such a family follows, for example, by the continuous distribution of the $r$ coordinate restricted to $A$, using endpoint assignments at $t=0,1$; its coordinate level sets are null. Starting from $\sigma_+$, switch to $\sigma_-$ on $A_t$ and $RA_t$. The resulting signs $\sigma_t$ satisfy

$$
\|\sigma_t-\sigma_s\|_1=4m(A)|t-s|.
\tag{138.3}
$$

If $m(A)=0$ the endpoint quadratic values would agree, so this case cannot occur. The actual bilinear formula, self-adjointness and the Markov contraction give, on the unit ball,

$$
|Q_E(u)-Q_E(v)|
\le2\|g\|_\infty\|q_E\|_\infty\|u-v\|_1.
\tag{138.4}
$$

For the first difference term use $\|P(q_Eu)\|_\infty\le\|q_E\|_\infty$; for the second move $P$ to $gv$ and use $\|P(gv)\|_\infty\le\|g\|_\infty$. Hence $t\mapsto Q_E(\sigma_t)$ is continuous. The intermediate value theorem gives an exact zero.

Give that zero sign the value $+1$ on $S\cap N$ and zero on $N\setminus S$. Since $N$ is invariant, Borel and null, this repairs the pointwise square identity without changing the quadratic value or almost-everywhere oddness. At a fixed point $x\in S\cap N$, everywhere oddness would require $v(x)=-v(x)$, hence $v(x)=0$, whereas the square identity requires $|v(x)|=1$. This proves the obstruction and the stated boundary. No additional finite constraints on the exact sign are asserted. $\square$

**Theorem 138.2 (one original common partition and an ordered congruence).** With $v$ from Theorem 138.1, put

$$
D_0=\{v=1\},\qquad D_1=\{v=-1\},\qquad D_3=C,\qquad D_B=B.
\tag{138.5}
$$

This is a single pointwise Borel partition of the whole $G$, belongs to the original $\mathscr D_{12}(\theta)$, and has $q_D=q_E$. In the original order $(0,1,3,B)$, the invertible matrix

$$
J=\begin{pmatrix}
1&0&0&1\\
1&0&0&-1\\
0&1&0&0\\
0&0&1&0
\end{pmatrix}
\tag{138.6}
$$

satisfies

$$
J^{\mathsf T}A^D J=\begin{pmatrix}A_E&0\\0&0\end{pmatrix}.
\tag{138.7}
$$

Consequently

$$
\operatorname{rank}A^D=\operatorname{rank}A_E\le3,\qquad
\operatorname{rank}A^D\le2\ \Longleftrightarrow\ \det A_E=0
\tag{138.8}
$$

for this constructed partition.

*Proof.* The square identity makes $D_0,D_1$ a disjoint exhaustive split of $S$, so (138.5) is a whole-$G$ partition. Each $\nu_j$ is $R_\pi$-invariant and vanishes on $N$. Almost-everywhere oddness gives $\int g_{jd}v\,dm=0$ and therefore

$$
\nu_j(D_0)=\nu_j(D_1)=\frac{3/4-t_j}{2},\qquad
\nu_j(D_3)=t_j,\qquad \nu_j(D_B)=1/4.
$$

These are exactly the twelve original targets, for the original $b$, at the three original epochs.

The columns of $J$ express the function basis $(\mathbf1_S,\mathbf1_C,\mathbf1_B,v)$ in the original indicator basis. They are independent, since $\mathbf1_{D_0}=(\mathbf1_S+v)/2$ and $\mathbf1_{D_1}=(\mathbf1_S-v)/2$. For any invariant bounded $u$, both ordered cross pairings vanish:

$$
Q_E(u,v)=\int guP(q_Ev)\,dm=0,\qquad
Q_E(v,u)=\int gvP(q_Eu)\,dm=0.
\tag{138.9}
$$

In the first integral $gu$ is even and $P(q_Ev)$ is odd under $R_\pi$. In the second $P(q_Eu)$ and $g$ are even while $v$ is odd. Invariance of $m$ gives zero in both cases. This proves (138.7), using $Q_E(v)=0$ and without any symmetry assumption on $A^D$ or $A_E$. Invertible left and right multiplication preserve rank, and a real three-by-three matrix has rank at most two exactly when its determinant is zero. $\square$

## 139. The interval of actual invariant coarse determinants

**Theorem 139.1 (exact-marginal approximation with an endogenous terminal factor).** For every admissible invariant stochastic tuple $u$ of Definition 136.1, there are $E_n\in\mathscr E_\theta$ whose indicators converge componentwise weak-star to $u$ and satisfy

$$
A_{E_n}\longrightarrow A(u),\qquad
\det A_{E_n}\longrightarrow\det A(u).
\tag{139.1}
$$

In this limit each actual matrix uses its own terminal factor $P\mathbf1_{C_n}$.

*Proof.* Work on the actual quotient $(X,\bar m)$ of (136.5). Let $\mathcal P_n$ be refining finite Borel partitions generating its Borel sigma-algebra modulo null sets. In the Dvoretzky–Wald–Wolfowitz theorem cited in Proposition 136.2, use the finite list consisting of $\bar\nu_2,\bar\nu_3,\bar\nu_4$ and all measures $\bar m|_A$ for $A\in\mathcal P_n$. They are finite atomless measures on the same Borel space. The resulting single three-cell partition $E_n$ satisfies, simultaneously,

$$
\bar\nu_j(E_{n,i})=\int_Xu_i\,d\bar\nu_j,
\qquad
\bar m(E_{n,i}\cap A)=\int_Au_i\,d\bar m.
\tag{139.2}
$$

The first equations are precisely the nine required marginals. The second equations imply weak-star convergence: for any $L^1(\bar m)$ test $\phi$, approximate it by $\mathcal P_n$-simple $\psi_n$ in $L^1$. The pairing with $\psi_n$ of $\mathbf1_{E_{n,i}}-u_i$ is zero, and the remaining pairing has absolute value at most $\|\phi-\psi_n\|_1$. Lift the cells to $G$ and assign the null axis to $S$. Pairing with an arbitrary $L^1(m)$ test reduces by angular integration to a quotient $L^1$ test, so the lifted indicators converge weak-star on $G$ as well.

The actual three-time density from Appendix II §123 is

$$
W(x,y,z)=g(x)p_d(x,y)p_d(y,z)\ge0,\qquad
\int_{G^3}W\,dm^{\otimes3}=1.
\tag{139.3}
$$

The equality follows by integrating first in $z$, then in $y$, using conservation, and finally the mass-one source density. Thus $W\in L^1(m^3)$. Approximate it in $L^1$ by finite sums of rectangular tensors $a(x)b(y)c(z)$ with factors in $L^1(m)$. On each tensor, the integral against three bounded weak-star convergent components factors into three convergent scalar pairings. The approximation error is uniform for components in $[0,1]$. It follows that

$$
\mathcal C(\mathbf1_{E_{n,i}},\mathbf1_{E_{n,j}},\mathbf1_{C_n})
\longrightarrow\mathcal C(u_i,u_j,u_C).
$$

This is exactly (139.1), including the changing terminal factor. Continuity of the determinant polynomial completes the proof. The use of $W$ is the actual common-readout continuity mechanism of §123, specialized with the exact linear-marginal constraints (139.2); it is not an exact nonlinear purification theorem. $\square$

**Theorem 139.2 (positive value, zero closure and deterministic paths).** For every original $\theta$, the actual determinant image

$$
I_\theta=\{\det A_E:E\in\mathscr E_\theta\}\subset\mathbb R
\tag{139.4}
$$

is an interval containing a strictly positive value, and $0\in\overline{I_\theta}$. Moreover any two members of $\mathscr E_\theta$ can be joined by a path of invariant deterministic partitions retaining all nine marginals, along which the actual determinant is continuous. In particular there is an original $D\in\mathscr D_{12}(\theta)$ with $\operatorname{rank}A^D=3$ exactly.

*Proof.* First produce a positive stochastic value. Choose six disjoint positive-$\bar m$ Borel subsets of $X$. Their six indicators span a six-dimensional space of bounded invariant functions. The common kernel of the three source moment functionals has dimension at least three and therefore contains a $v$ outside $\operatorname{span}\{1,\beta\}$. Normalize $\|v\|_\infty\le1$. For $0<\epsilon\le1/8$ set

$$
u^+=(3/4-c\beta-\epsilon v,\ c\beta,\ 1/4+\epsilon v).
\tag{139.5}
$$

All components are nonnegative: $c\beta\le1/4$, the first is at least $3/8$ and the last at least $1/8$. Their sum is one. The three zero source moments of $v$ give exactly the prescribed marginals. The functions $1,\beta,v$ are independent, since $\beta$ is nonconstant by §135 and $v$ was chosen outside their span. The three components of $u^+$ are consequently independent as well: their sum gives $1$, the middle gives $\beta$, and the last then gives $v$.

For this stochastic tuple, and only using its own terminal component, $Pu_C^+=cP\beta=cg$. Hence

$$
A(u^+)_{ij}=c\langle gu_i^+,P(gu_j^+)\rangle_m.
\tag{139.6}
$$

For every nonzero coefficient vector $a\in\mathbb R^3$, independence of the components, positivity of $g$ and injectivity of $T_{d/2}$ give

$$
a^{\mathsf T}A(u^+)a
=c\left\|T_{d/2}\left(g\sum_i a_i u_i^+\right)\right\|_2^2>0.
$$

Thus this stochastic matrix is symmetric positive definite and has positive determinant. Theorem 139.1 supplies an actual invariant partition with strictly positive determinant. It does not identify its actual terminal factor with $cg$.

For the unperturbed tuple $u^0=(3/4-c\beta,c\beta,1/4)$, the same weighted Gram formula holds and its components span exactly $\operatorname{span}\{1,\beta\}$. Its matrix has rank two by strict heat positivity on that span, hence determinant zero. Applying Theorem 139.1 to $u^0$ gives actual invariant determinants tending to zero. This establishes closure, without asserting attainment.

It remains to prove the interval property on the deterministic class itself. Given feasible quotient partitions $E,F$, write their mismatch blocks as $H_{ij}=E_i\cap F_j$, $i\ne j$. On each block use the four finite atomless measures

$$
\lambda=(\bar m,\bar\nu_2,\bar\nu_3,\bar\nu_4).
$$

Their simultaneous proportional subdivision follows from Dvoretzky–Wald–Wolfowitz Lemma 2, applied recursively. More explicitly, halve every block into two Borel pieces of equal $\lambda$-vector measure, then halve each piece, and continue. Order the level-$n$ pieces by their binary words. Each has vector measure $2^{-n}\lambda(H_{ij})$. The unions of the first $k$ pieces are nested at dyadic parameters $k2^{-n}$ and compatible across levels. For arbitrary $t\in(0,1)$ take the union of these initial unions at dyadic parameters below $t$; by continuity from below this defines nested Borel $T_{ij,t}$ with

$$
\lambda(T_{ij,t})=t\lambda(H_{ij}).
\tag{139.7}
$$

Set $T_{ij,0}=\varnothing$, $T_{ij,1}=H_{ij}$. Any endpoint discrepancy in the union construction is null for all four measures and these assignments retain (139.7).

At parameter $t$, switch the label from $i$ to $j$ on $T_{ij,t}$ in each mismatch block, leaving all other points at their $E$ labels. Call the resulting partition $E(t)$. It is Borel, disjoint and exhaustive. For every label $l$ and source measure,

$$
\bar\nu_r(E_l(t))
=\bar\nu_r(E_l)+t\bigl(\bar\nu_r(F_l)-\bar\nu_r(E_l)\bigr)
=\bar\nu_r(E_l).
\tag{139.8}
$$

Its lift, with the fixed axis assigned to $S$, is feasible and invariant. If an original endpoint assigned the axis differently, it has the same integrals and actual matrix; either null assignment can be made at the endpoint without affecting continuity below.

For $s<t$, the changed set $H$ has $\nu_r(H)\le t-s$ for $r=2,3,4$, by (139.7) and disjointness of the mismatch blocks. Each actual entry is the probability of the event that the common partition gives labels $(i,j,C)$ at the three original epochs. This event changes only if at least one of the three states belongs to $H$. The union bound with the three original source laws gives

$$
|(A_{E(t)})_{ij}-(A_{E(s)})_{ij}|\le3|t-s|.
\tag{139.9}
$$

In particular this bound includes the terminal-cell change. Every entry is between zero and one. Expanding the determinant into six signed products and telescoping each product in its three factors gives

$$
|\det A_{E(t)}-\det A_{E(s)}|\le54|t-s|.
\tag{139.10}
$$

The intermediate value theorem along this path proves that $I_\theta$ is an interval. Apply Theorem 138.2 to the positive actual endpoint already obtained: $A_E$ is invertible, so its corresponding original four-cell matrix has rank exactly three. $\square$

## 140. A conditional negative-direction bridge and the exact rank boundary

**Theorem 140.1 (negative stochastic determinant implies an exact original rank-two bound).** If an admissible invariant stochastic tuple $u$ has $\det A(u)<0$, then there is $E\in\mathscr E_\theta$ with $\det A_E=0$, and hence an original $D\in\mathscr D_{12}(\theta)$ with $\operatorname{rank}A^D\le2$.

*Proof.* By Theorem 139.1 some actual feasible invariant partition has negative determinant. Theorem 139.2 supplies an actual positive determinant partition and an exact-marginal deterministic path between them. Continuity gives an actual zero determinant on the path. The fixed-$C$ sign and congruence of Theorems 138.1–138.2 then give the original partition with the claimed rank bound. All parts use a single partition at all three original epochs. $\square$

**Theorem 140.2 (an interior terminal perturbation and a sufficient constrained negative vector).** For every original $\theta$, one can choose a nonzero bounded invariant real $w$, supported in a compact subset of a positive analytic-$\beta$ quotient patch, with

$$
\int_Gg_{jd}w\,dm=0\quad(j=2,3,4).
\tag{140.1}
$$

For sufficiently small nonzero real $\tau$, the function

$$
k=c\beta+\tau w
\tag{140.2}
$$

is everywhere strictly positive, at most $3/8$, has the three prescribed $C$ marginals, and satisfies $q_k/g$ nonconstant almost everywhere, where $q_k=Pk$. Define the ordered compression

$$
Q_k(u,v)=\int_Gg\,u\,P((Pk)v)\,dm,\qquad
\Delta_k=\det\begin{pmatrix}
Q_k(1,1)&Q_k(1,k)\\
Q_k(k,1)&Q_k(k,k)
\end{pmatrix}.
\tag{140.3}
$$

The same sufficiently small choices of $\tau$ can ensure $\Delta_k>0$.

For any such $k$, suppose there exists a bounded invariant real $v$ with the three zero source moments and four ordered equations

$$
\begin{gathered}
\int_Gg_{jd}v\,dm=0\quad(j=2,3,4),\\
Q_k(1,v)=Q_k(k,v)=Q_k(v,1)=Q_k(v,k)=0,
\qquad Q_k(v,v)<0.
\end{gathered}
\tag{140.4}
$$

Then a sufficiently small $\epsilon>0$ gives an admissible invariant stochastic tuple

$$
u^\epsilon=(3/4-k-\epsilon v,\ k,\ 1/4+\epsilon v)
\tag{140.5}
$$

with

$$
\det A(u^\epsilon)=\epsilon^2\Delta_k Q_k(v,v)<0.
\tag{140.6}
$$

Consequently this antecedent implies an exact invariant coarse zero and an original rank-at-most-two partition.

*Proof.* The analytic representative of $\beta=g_d$ is positive almost everywhere on $\Omega$, so there is a quotient open patch with compact closure inside $X$ on which it is continuous and bounded below by some $b_*>0$. Use the representative of Proposition 136.2 equal to this analytic function there. Choose four disjoint positive-measure Borel subsets of a compact subpatch. Their invariant lifted indicators span a four-dimensional space. Three homogeneous source moment equations have a nonzero solution in this space, giving $w$ with (140.1). Its support in the quotient is compact; the angular lift is compact and stays away from $N$. Give it value zero on $N$.

Choose $\tau\ne0$ so small that

$$
|\tau|\|w\|_\infty<\min(cb_*/2,1/8).
\tag{140.7}
$$

On the support of $w$, $k\ge cb_*/2>0$ and $k\le1/4+1/8=3/8$; elsewhere $k=c\beta\in(0,1/4]$. The moments are unchanged by (140.1).

At $\tau=0$, $Pk=cg$, and the compression in (140.3) is the symmetric weighted heat Gram matrix of the independent functions $1,c\beta$:

$$
Q_{c\beta}(u,v)=c\langle gu,P(gv)\rangle_m.
$$

Its determinant is strictly positive by $g>0$ and injectivity of $T_{d/2}$, exactly as in §135. Each entry of (140.3) is continuous in $\tau$: expanding the bounded factors $k=c\beta+\tau w$ and $Pk=cg+\tau Pw$ gives a finite polynomial of integrable terms. Therefore $\Delta_k>0$ for all sufficiently small $|\tau|$.

For the nonconstant ratio, write $\delta=\tau Pw=P(k-c\beta)$. It is nonzero by injectivity and $w\ne0$. Moreover, self-adjointness, $P\beta=g$ and (140.1) give

$$
\langle\beta,\delta\rangle_m
=\tau\langle g,w\rangle_m=0.
$$

If $Pk=\lambda g$, this identity would imply $(\lambda-c)\langle\beta,g\rangle_m=0$. The last inner product is finite and strictly positive, hence $\lambda=c$, contradicting $\delta\ne0$. Thus $q_k/g$ is nonconstant. This fact alone asserts no invariant negative index.

Now assume precisely (140.4). Representatives of $v$ may be made invariant Borel with the same bound by angular averaging and null-set repair. Choose $\epsilon>0$ with $\epsilon\|v\|_\infty\le1/8$. In (140.5) the first component is at least $1/4$, the last at least $1/8$, the middle is strictly positive and their sum is one. The moments follow from those of $k$ and $v$, so the tuple is admissible, with its actual terminal factor $Pk$.

Let $H$ be the ordered matrix of $Q_k$ in the function list $(1,k,v)$. All four ordered equations are needed to give

$$
H=\begin{pmatrix}
Q_k(1,1)&Q_k(1,k)&0\\
Q_k(k,1)&Q_k(k,k)&0\\
0&0&Q_k(v,v)
\end{pmatrix}.
\tag{140.8}
$$

The rows of

$$
R_\epsilon=\begin{pmatrix}
3/4&-1&-\epsilon\\
0&1&0\\
1/4&0&\epsilon
\end{pmatrix}
\tag{140.9}
$$

express the three components of $u^\epsilon$ in that list. Direct bilinearity gives $A(u^\epsilon)=R_\epsilon H R_\epsilon^{\mathsf T}$, valid for this nonsymmetric ordered form. Since $\det R_\epsilon=\epsilon$, taking determinants yields (140.6). Theorem 140.1 proves the final implication. $\square$

**Proposition 140.3 (the remaining quantified alternatives).** The preceding conclusions preserve the original unresolved event and its exact negation:

$$
\begin{aligned}
\mathcal R&:\quad
\exists\theta\in\Theta\ \forall D\in\mathscr D_{12}(\theta),
\quad\operatorname{rank}A^D\ge3,\\
\neg\mathcal R&:\quad
\forall\theta\in\Theta\ \exists D\in\mathscr D_{12}(\theta),
\quad\operatorname{rank}A^D\le2.
\end{aligned}
\tag{140.10}
$$

For every $\theta$ there is an original rank-exactly-three partition. An invariant coarse singularity for that $\theta$ is sufficient for an original rank-at-most-two partition, but the converse for arbitrary original partitions is not asserted. The existence of the invariant constrained negative vector (140.4) remains an antecedent, rather than a conclusion. Neither alternative in (140.10), nor full $64$-coordinate attainment, follows from the established determinant interval and its zero closure.

*Proof.* The rank-three assertion is Theorem 139.2. The sufficient route is (138.8) and Theorem 140.1. It only concerns partitions obtained by splitting an invariant coarse $S$ while fixing $C$. It imposes no such structure on every member of $\mathscr D_{12}(\theta)$.

If $0\notin I_\theta$, its interval property and positive value force $I_\theta\subset(0,\infty)$; otherwise a negative member and the positive member would enclose zero. Since $0\in\overline{I_\theta}$, in this case $\inf I_\theta=0$. No assertion above excludes this possibility. Thus closure is insufficient for an exact coarse zero. Conversely a strictly negative admissible stochastic value supplies an exact zero by Theorem 140.1; this is a sufficient condition, not an assumption silently imposed on every tuple.

Theorem 137.1 uses nonzero odd angular characters. An invariant $v$ in (140.4) has character zero, so that theorem supplies no negative index on its required space. On the invariant bounded space the seven displayed equations are bounded linear functionals: the source densities are integrable, and in each $Q_k$ pairing the bounded fixed factors and the Markov contraction make the remaining coefficient integrable. Eight negative dimensions on that space would suffice by the finite-codimension argument, but no such eight-dimensional subspace, or even the single vector in (140.4), is established here. Nonconstancy of $q_k/g$ is not substituted for this missing assertion.

Finally negating the original existential-universal statement gives the universal-existential statement in (140.10), since rank is an integer and the negation of rank at least three is rank at most two. A constructed rank three is compatible with both quantified alternatives. Proposition 135.3 proves only the forward implication from full $64$-coordinate attainment to $A^D=A^f$ and rank two. Neither rank two nor the coarse-zero route proves those additional equalities. The endpoint and source hypotheses throughout are precisely the inherited ones of Definition 135.1; these ordinary conditional mathematical deductions assert no further realization of the source or readout. $\square$

## 追加锚（本行以下为增补区）

## 141. A source-preserving reflection and the invariant constrained negative vector

**Proposition 141.1 (reflection of the entire original endpoint and an even terminal perturbation).** Retain the complete original telescope of Definitions 135.1 and 136.1. In symmetric coordinates define

$$
J(x,y,z,\xi)=(x,y,-z,\xi).
\tag{141.1}
$$

Its pullback preserves $m$, the entire form domain $\mathscr V=\mathscr V_0\dotplus\mathbb C1$, its energy and its source trace, and commutes with the actual $K$ and every $T_s$. Every actual source density $g_s$ is $J$-even. The representative $\beta$ of Proposition 136.2 can be chosen both pointwise rotation invariant and $J$-even, without changing the original $b,M,c,f$ classes or any target. For every original $\theta$ there is a nonzero bounded invariant $J$-even real $w$, supported away from $N$ in a compact set, such that the construction (140.1)–(140.3) gives, for sufficiently small nonzero $\tau$,

$$
\begin{gathered}
k=c\beta+\tau w,\qquad 0<k\le3/8\quad\hbox{everywhere},\qquad k\circ J=k,\\
\int_Gg_{jd}k\,dm=t_j\quad(j=2,3,4),\qquad
q=Pk,\qquad q/g\ \hbox{nonconstant almost everywhere},\qquad
\Delta_k>0.
\end{gathered}
\tag{141.2}
$$

*Proof.* The map $J$ is a measure-preserving automorphism of the original $H^1\times\mathbb R$, fixes $e$ and commutes with the rotations. It changes the sign of $X_3=\partial_z$ and leaves $X_1,X_2,\partial_w$ unchanged. Thus the free realization of $L$ commutes with $J$. Its source heat law at $e$ is invariant, and the original identity $\Gamma=\int_0^\infty h_s\,ds$ makes $\Gamma$ invariant as well. Equivalently, the independent Gaussian $z$ factor in the original heat representation is even; (122.6) exhibits this symmetry through $z^2$ on $\Omega$. The Heisenberg heat factor is the attributed [Krötz–Thangavelu–Xu formula, §4.1, (4.1.2)](https://arxiv.org/html/math/0401243v2), with $n=1$ and the original Fourier and raw Haar conventions as in Appendix II §122. This argument concerns the original unit-source field, without changing its normalization.

Consequently $J$ preserves $S$, $S^*$, the Friedrichs form $(\overline q_c,\mathcal Q_c)$ and its domain. The supplied identity $\ker S^*=\mathbb Ch$ makes $Jh$ a multiple of $h$. Positivity, reality and unit norm give $Jh=h$. Hence $J$ preserves the full domain $\mathcal Q_c\dotplus\mathbb Ch$ and the form $q_H[y+ch]=\overline q_c[y]$. Closed-form representation proves commutation with the actual $H_{\rm end}$, including its source summand and selector. Conjugation by this same $h$ gives invariance of $m$, $\mathscr V$ and $\mathscr E$, and commutation with $K,T_s$. Moreover $J$ preserves $\mathscr V_0$, fixes $1$ and therefore preserves $\operatorname{tr}(v_0+c)=c$. Applying the actual source identity (117.2) to $Jv$ and using Riesz uniqueness gives $Jg_s=g_s$ for each $s>0$. Thus neither the full domain nor the source-start law is inferred merely from a differential symmetry.

Replace the pointwise invariant representative of Proposition 136.2 by $(\beta+\beta\circ J)/2$. This preserves its class $g_d$ and the everywhere bounds $0<\beta\le M$. Choose a positive analytic-$\beta$ quotient patch with compact closure in $\{r>0,z>0\}$, and a compact subpatch on which $\beta\ge b_*>0$. Such a patch exists by positivity almost everywhere and analytic continuity. Repair the representative to the analytic one there and on its reflected patch. Select four disjoint positive-measure Borel subsets of the subpatch, and pair each with its reflection. Their four invariant lifted indicators are even and linearly independent. The three source moment equations on their span have a nonzero solution $w$. Its support is compact and disjoint from $N$, and it may be assigned zero on $N$. Both reflected patches have the same lower bound $b_*$, so the smallness bound (140.7) applies to their union. The proof of Theorem 140.2 now applies to this particular $w$: that bound, polynomial continuity of $\Delta_k$, and the injectivity argument for $P(k-c\beta)$ give every assertion of (141.2). No new assumption about the desired negative vector enters this construction. $\square$

**Theorem 141.2 (a bounded character-zero vector satisfying all seven equations).** For every original $\theta$, choose any reflection-even $k$ supplied by Proposition 141.1. There exists a bounded real Borel $v$ on the whole original $G$, pointwise invariant under every rotation and pointwise odd under $J$, such that

$$
\begin{gathered}
\int_Gg_{jd}v\,dm=0\quad(j=2,3,4),\\
Q_k(1,v)=0,\qquad Q_k(k,v)=0,\qquad
Q_k(v,1)=0,\qquad Q_k(v,k)=0,\\
Q_k(v,v)<0.
\end{gathered}
\tag{141.3}
$$

Here $Q_k(u,v)=\int guP(qv)\,dm$ uses exactly $q=Pk$. In particular this is the antecedent (140.4) on the rotation-invariant space.

*Proof.* Let $\mathcal H_0^-$ be the closed complex subspace of $L^2(G,m)$ consisting of rotation-invariant, $J$-odd classes. The commuting rotation and reflection projections reduce the actual $K$; denote its nonnegative self-adjoint restriction by $K_0^-$. This is a restriction of the supplied full operator, with no replacement of its endpoint. The space contains every smooth invariant test compactly supported in $\{r>0,z>0\}$ together with its negative reflection. It is therefore nonzero and contains the local tests used below.

Put

$$
s=g+q,\qquad t=g-q,\qquad
\gamma=t/s\ \hbox{where }s>0,
\qquad \gamma=0\ \hbox{on its null complement},\qquad
\sigma=d/2,\qquad A=e^{-\sigma K_0^-}.
\tag{141.4}
$$

Both weights are bounded, real, rotation invariant, $J$-even and strictly positive almost everywhere. The assertions for $g$ use Theorem 133.2 and the actual source density; those for $q$ use $q=T_dk$, positivity improvement and the Markov contraction. Thus $s>0$ almost everywhere and $|\gamma|\le1$. Multiplication by $s,t,\gamma$ preserves $\mathcal H_0^-$. On $\Omega$ the actual heat-image suppliers (122.9)–(122.11) make $g=T_dg_d$ and $q=T_dk$ analytic. Consequently $\gamma$ is smooth analytic on the open set where $s>0$.

Suppose for contradiction that $Q_k(v,v)\ge0$ for every bounded real $v\in\mathcal H_0^-$. Self-adjointness of $P=A^2$ gives the exact identity

$$
4Q_k(v,v)=\|A(sv)\|_2^2-\|A(tv)\|_2^2.
\tag{141.5}
$$

There is no global positive lower bound on $s$ in this identity or in the next step. For any real $u\in\mathcal H_0^-$ set

$$
u_n=u\,\mathbf1_{\{s\ge1/n,\ |u|\le n\}},\qquad v_n=u_n/s.
\tag{141.6}
$$

Take $v_n=0$ where the indicator vanishes. These are allowed odd invariant tests with $\|v_n\|_\infty\le n^2$, and $u_n\to u$ in $L^2$. Applying (141.5) and passing to the limit proves $\|AM_\gamma u\|_2\le\|Au\|_2$. Real and imaginary parts extend this inequality to the whole complex $\mathcal H_0^-$. Since $A$ is injective with dense range, the rule $B(Au)=AM_\gamma u$ extends to a contraction $B$ on this entire space. Taking adjoints gives

$$
BA=AM_\gamma,\qquad AB^*=M_\gamma A,\qquad
e^{\sigma K_0^-}M_\gamma e^{-\sigma K_0^-}=B^*.
\tag{141.7}
$$

The last equality includes its range assertion, supplied by the middle equality. This is the elementary adjoint-factorization argument also used in Appendix II (128.5)–(128.6), now on the whole invariant reflection-odd space. Its domain is not obtained by discarding a finite-dimensional complement.

Here is the required commutator consequence with its actual domains. For $\Pi_R=\mathbf1_{[0,R]}(K_0^-)$ define the entire bounded-operator-valued function

$$
F_R(z)=\Pi_Re^{zK_0^-}M_\gamma e^{-zK_0^-}\Pi_R.
\tag{141.8}
$$

The spectral cutoffs define both exponential factors on bounded spectral intervals. On $\operatorname{Re}z=\sigma$, (141.7) and imaginary-time unitary conjugation give $\|F_R(z)\|\le1$. On $\operatorname{Re}z=-\sigma$, the adjoint identity gives the same bound. The functions are bounded on each closed vertical strip. Hadamard's three-lines theorem applied to scalar matrix coefficients therefore gives the bound one throughout this strip. Cauchy's estimate on the circle $|z|=\sigma/2$ yields

$$
\|F_R'(0)\|\le2/\sigma.
\tag{141.9}
$$

For $u,v\in D(K_0^-)$, graph-norm convergence of the spectral cutoffs identifies the limit of the derivative pairing with

$$
\langle K_0^-u,\gamma v\rangle_m-
\langle\gamma u,K_0^-v\rangle_m.
\tag{141.10}
$$

Its absolute value is at most $(2/\sigma)\|u\|_2\|v\|_2$. Whenever $v$ and $\gamma v$ are smooth compact punctured tests in this subspace, self-adjointness and density of $D(K_0^-)$ identify (141.10) with the actual vector commutator and give

$$
\|[K,M_\gamma]v\|_2\le(2/\sigma)\|v\|_2.
\tag{141.11}
$$

This does not assume global invariance of $D(K)$ under multiplication by $\gamma$.

Choose any small quotient open patch $U$ compactly contained in $\{r>0,z>0,gq>0\}$, and a real $\chi\in C_c^\infty(U)$. For $\omega\in\mathbb R^3$, on $z>0$ take

$$
u_N=\chi(r,z,\xi)e^{iN\omega\cdot(r,z,\xi)},
\tag{141.12}
$$

extend it negatively by $J$ to $z<0$, and set it zero elsewhere. These tests have angular character zero. Both $u_N$ and $\gamma u_N$ are genuine smooth compact punctured vectors in the original operator domain: multiplication by the positive smooth $h$ takes such vectors to the core $\mathcal D_0$ in (112.4). Their $L^2$ norms are independent of $N$. On the upper patch the original symbol (137.12), or the original Leibniz identity (122.22), gives

$$
[K,M_\gamma]u_N
=-2iN\chi e^{iN\omega\cdot(r,z,\xi)}
\left[a\gamma_r\omega_r+a\gamma_z\omega_z+
\left(\eta+ar^2/4\right)\gamma_\xi\omega_\xi\right]
+O_{L^2(U)}(1).
\tag{141.13}
$$

For fixed $\chi,\omega$ the remainder is bounded independently of $N$, because all coefficients and derivatives involved are bounded on its compact support. The reflected support is disjoint and cannot cancel the norm on $U$. Divide (141.11) by $N$ and let $N\to\infty$. Taking the three coordinate directions for $\omega$ shows $\chi\gamma_r=\chi\gamma_z=\chi\gamma_\xi=0$. The amplitude is arbitrary, and $a,\eta>0$, so $\gamma$ is constant on each connected such patch. Some nonempty patch exists by positivity almost everywhere; on one of them its constant $\gamma_0$ lies in $(-1,1)$.

The analytic function $g-q-\gamma_0(g+q)$ consequently vanishes on a nonempty open subset of the connected $\Omega$. Analytic uniqueness, in the same actual heat-image class as §137, makes it vanish on all $\Omega$. Since $m(N)=0$, this gives

$$
q/g=(1-\gamma_0)/(1+\gamma_0)\quad m\text{-a.e.},
\tag{141.14}
$$

contrary to (141.2). The assumed nonnegativity on all bounded real $\mathcal H_0^-$ is therefore false. There is a bounded real vector in this space with $Q_k(v,v)<0$.

Choose a bounded Borel representative, average it over the circle, apply $(I-J)/2$, and assign zero on $N$. These operations preserve its class and bound and make it pointwise invariant and pointwise $J$-odd on all $G$. In particular it vanishes on the fixed hyperplane $z=0$, so there is no pointwise oddness obstruction. Each source density $g_{jd}$ is even, giving each of the three moment equations separately. For the four ordered equations, self-adjointness gives the explicit coefficients

$$
\begin{aligned}
Q_k(1,v)&=\int_G v\,q\,Pg\,dm,&
Q_k(k,v)&=\int_G v\,q\,P(gk)\,dm,\\
Q_k(v,1)&=\int_G v\,g\,Pq\,dm,&
Q_k(v,k)&=\int_G v\,g\,P(qk)\,dm.
\end{aligned}
\tag{141.15}
$$

All four coefficients multiplying $v$ are integrable and $J$-even, since $g,q,k$ are even and the actual $P$ commutes with $J$. Invariance of $m$ makes each displayed integral zero. This proves all of (141.3), without identifying either order of the bilinear form with the other.

The factorization, three-lines interpolation, Cauchy estimate and analytic uniqueness are established intermediate methods; the factorization is proved explicitly above, and the interpolation and local-symbol computation use exactly the bounded strip and genuine punctured-core hypotheses displayed here. The source-specific composition with the full reflection symmetry and the endogenous terminal factor is `repo-derived`. It uses neither a finite-negative-square extension nor a new general index theorem. $\square$

**Corollary 141.3 (the original quantified rank alternative).** Under precisely the inherited original endpoint and source telescope, the original marginal classes satisfy

$$
\forall\theta\in\Theta\ \exists D\in\mathscr D_{12}(\theta),
\qquad \operatorname{rank}A^D\le2.
\tag{141.16}
$$

Thus this source-conditional statement is $\neg\mathcal R$ in (140.10). It supplies neither $A^D=A^f$ nor full $64$-coordinate attainment.

*Proof.* Fix an arbitrary original $\theta$, including its arbitrary original representative $b$. Proposition 141.1 gives a reflection-even admissible terminal perturbation $k$ with $\Delta_k>0$, and Theorem 141.2 gives precisely (140.4). Theorem 140.2 therefore gives an admissible invariant stochastic tuple (140.5) with strictly negative actual determinant (140.6). Theorem 140.1 supplies an actual invariant coarse partition with zero determinant, using Theorem 139.1 for a negative actual determinant and the deterministic path of Theorem 139.2 for exact attainment. Theorem 138.2 then supplies an original whole-$G$ four-cell Borel partition with all twelve original source marginals and rank at most two. In particular each deterministic matrix in these bridges uses its own actual $P\mathbf1_C$ or $P\mathbf1_{D_3}$; $Pk$ belongs only to the stochastic precursor. The representative changes in Proposition 141.1 preserve the original targets by Proposition 135.3. Since the original $\theta$ was arbitrary, (141.16) follows. The only extra symmetry required of the construction is imposed on its freely chosen $k$, not on the original representative $b$ or on arbitrary members of $\mathscr D_{12}(\theta)$. The forward implication concerning full $64$-coordinate attainment in Proposition 135.3 still has no converse here. $\square$

## 追加锚（本行以下为增补区）

## 142. Finite-moment exact odd signs for the actual coarse terminal

**Theorem 142.1 (exact signs with arbitrary finite moments).** Retain the complete original telescope of Definitions 134.1, 135.1 and 136.1, including every inherited endpoint, source, analytic and clock hypothesis of Appendix II §§115–117, 123–125 and 133. For every original $\theta=(a,\eta,d,b)\in\Theta$, every fixed actual invariant coarse partition $E=(S,C,B)\in\mathscr E_\theta$, and every finite set $\Psi\subset L^1(G,m;\mathbb R)$, there is a bounded whole-$G$ Borel function $v$ such that

$$
\begin{gathered}
v^2=\mathbf1_S\quad\text{everywhere},\qquad
v\circ R_\pi=-v\quad m\text{-a.e.},\\
\int_G\psi v\,dm=0\quad(\psi\in\Psi),\qquad
Q_E(v,v)=\int_Gg\,v\,P\bigl((P\mathbf1_C)v\bigr)\,dm=0.
\end{gathered}
\tag{142.1}
$$

Here $P=T_d$, $g=g_{2d}$, $m=h^2\mu$, the source start is $e$, and the original observation epochs are $2d,3d,4d$. The cells of $E$ and its actual terminal factor $q_E=P\mathbf1_C$ remain fixed. The finite moments and quadratic equality hold for the same sign.

*Proof.* Set $R=R_\pi$, $F=\{r>0,\ 0\le\alpha<\pi\}$ and $Y=S\cap F$. The null axis is $N=\{x=y=0\}$, and $S\setminus N=Y\sqcup RY$. Choose Borel representatives for the finitely many $L^1$ tests. For $x\in Y$ put

$$
\widetilde\psi(x)=\psi(x)-\psi(Rx).
\tag{142.2}
$$

Each $\widetilde\psi$ belongs to $L^1(Y,m)$. If $u$ vanishes outside $S$ and is odd off $N$, invariance of $m$ gives

$$
\int_G\psi u\,dm=\int_Y\widetilde\psi u\,dm.
\tag{142.3}
$$

Theorem 137.1, applied with the finitely many bounded linear functionals $u\mapsto\int\psi u\,dm$, gives two bounded odd real tests $u_+,u_-$ supported in $S$, with all these moments zero and

$$
Q_E(u_+,u_+)>0>Q_E(u_-,u_-).
\tag{142.4}
$$

Scale both into the unit ball. Choose Borel representatives exactly odd on $S\setminus N$ and zero outside $S$; the null-axis values do not affect any integral.

We first approximate either such $u$ by signs retaining every moment exactly. Let $\mathcal P_n$ be refining finite Borel partitions of $Y$ generating its Borel sigma-algebra. On this same Borel space use the finite nonnegative measures with densities

$$
(\widetilde\psi)_+,\ (\widetilde\psi)_-
\quad(\psi\in\Psi),\qquad
\mathbf1_A\quad(A\in\mathcal P_n)
\tag{142.5}
$$

relative to $m|_Y$. They are finite and atomless. Indeed $m\ll dx\,dy\,dz\,d\zeta$, and so is each measure in (142.5); cutting a positive-measure Borel set by a coordinate with null level sets supplies a proper subdivision. Apply Dvoretzky–Wald–Wolfowitz, [*Relations among certain ranges of vector measures*, Pacific J. Math. 1 (1951), Theorem 4, printed pp. 66–67](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), to the probability two-vector $((1+u)/2,(1-u)/2)$ on $Y$. The equality of its range with the decomposition range gives a Borel sign $s_n$ on $Y$ satisfying

$$
\int_Y\widetilde\psi s_n\,dm=\int_Y\widetilde\psi u\,dm=0,
\qquad
\int_A s_n\,dm=\int_Au\,dm\quad(A\in\mathcal P_n).
\tag{142.6}
$$

The use of positive and negative parts in (142.5) justifies the signed equalities without an extra assumption on the tests. Density of the partition-simple functions in $L^1(Y,m)$ gives $s_n\to u|_Y$ weak-star. Lift $s_n$ oddly to $RY$, set it zero outside $S$, and assign $+1$ on $S\cap N$. These are whole-$G$ Borel signs on $S$, with every required moment zero. Formula (142.3) shows that the lifted signs converge weak-star to $u$ on $G$.

The actual ordered kernel is the one in (138.2):

$$
a_E(x,y)=g(x)p_d(x,y)q_E(y)\ge0,\qquad
\int_{G^2}a_E\,dm^2=\int_GgPq_E\,dm\le1.
\tag{142.7}
$$

On the unit ball, $Q_E(u,u)$ is continuous for weak-star convergence: approximate $a_E$ in $L^1(m^2)$ by finite sums $\sum_j a_j(x)b_j(y)$ with $a_j,b_j\in L^1(m)$; each tensor pairing is a product of two convergent scalar pairings, and the integral error is uniformly bounded by the $L^1$ kernel error. Applying this to both tests in (142.4) supplies signs $s_+,s_-$ with all the exact moments and with strictly positive and strictly negative quadratic values, respectively.

It remains to connect these two signs without losing their moments. Let $A\subset Y$ be their disagreement set. On $A$, $s_-=-s_+$, and subtraction of their zero moments gives

$$
\int_A s_+\widetilde\psi\,dm=0\quad(\psi\in\Psi).
\tag{142.8}
$$

On $A$ take the finite vector of nonnegative measures consisting of $m|_A$ and the measures with densities $(s_+\widetilde\psi)_+,(s_+\widetilde\psi)_-$. All are finite and atomless for the same reason as (142.5). Lemma 2 of the same Dvoretzky–Wald–Wolfowitz article, printed pp. 66–67, permits simultaneous proportional subdivision. Repeatedly halve every piece for this entire vector, order the resulting pieces by binary words, and take initial unions at dyadic parameters. Their increasing unions at dyadic parameters below $t$ define nested Borel $A_t\subset A$ with

$$
\lambda(A_t)=t\lambda(A)\quad(0\le t\le1)
\tag{142.9}
$$

for each measure $\lambda$ in that vector; set $A_0=\varnothing$ and $A_1=A$. Continuity from below proves (142.9) for all $t$. In particular (142.8) holds with $A_t$ in place of $A$.

Switch from $s_+$ to $s_-$ on $A_t\sqcup RA_t$, keeping the null-axis assignment fixed, and call the resulting whole-$G$ sign $s_t$. Equations (142.3) and (142.8)–(142.9) show that every moment stays zero. Moreover

$$
\|s_t-s_s\|_1=4m(A)|t-s|.
\tag{142.10}
$$

The actual bilinear form obeys, for $|u|,|v|\le1$,

$$
|Q_E(u,u)-Q_E(v,v)|
\le2\|g\|_\infty\|q_E\|_\infty\|u-v\|_1,
\tag{142.11}
$$

by moving $P$ to the other factor in the second difference term and using its Markov contraction. Here $\|g\|_\infty<\infty$ is supplied by Theorem 133.2 and $\|q_E\|_\infty\le1$. Thus the quadratic value along this moment-preserving path is continuous. Its endpoint signs are opposite, so the intermediate value theorem gives (142.1). The fixed points in $S\cap N$ retain value $+1$; oddness there is only asserted almost everywhere, exactly as in Theorem 138.1.

The finite vector-measure results are attributed linear intermediates. The new source-specific assertion is their composition with the actual two-sided constrained index of Theorem 137.1 and the fixed-terminal kernel (142.7), producing one exact quadratic-zero sign with all the prescribed finite moments. $\square$

## 143. Joint density on the same exact-rank-two common partitions

**Definition 143.1 (the original target and the invariant precursor).** Retain precisely the telescope of Theorem 142.1. In particular $a,\eta,d>0$ are arbitrary original finite parameters and $b$ is any original allowed whole-$G$ Borel representative of $g_d$. The state space, product, raw Haar measure, unit source $L\Gamma=\delta_e$, critical coupling and actual selector are (134.1)–(134.3), with

$$
\begin{gathered}
g_c=16\sqrt{a\eta},\qquad h=w_*/\|w_*\|_2,\qquad
A_{\rm src}(u)=\rho C_{\rm src}(u),\qquad
K=U_h^{-1}H_{\rm end}U_h,\\
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\qquad
m=h^2\mu,\quad P=T_d,\quad g=g_{2d},\quad
M=1+\|g_d\|_\infty,\quad c=(4M)^{-1},\\
f_3=cb,\qquad f_B=1/4,\qquad f_0=f_1=(3/4-cb)/2.
\end{gathered}
\tag{143.1}
$$

Use the full conservative endpoint including its source coordinate, the actual start $e$ at time zero, and the original epochs $2d,3d,4d$. Let $\beta$ be the invariant reflection-even representative supplied by Proposition 141.1. On the actual rotation quotient $X$ of (136.5) define, or equivalently lift to $G$,

$$
u^0=(u_S^0,u_C^0,u_B^0)=(3/4-c\beta,c\beta,1/4).
\tag{143.2}
$$

The original tuple $f$ and $\beta$ are identified only as $m$-classes where appropriate, as in Proposition 135.3. Retain $\mathscr D_{12}(\theta)$, $\mathscr E_\theta$ and the actual matrices $A^D,A_E$ of §§135–136. For every common simplex tuple $u$ write

$$
\nu_u^{(3)}(y,z,w)=\mathcal C(u_y,u_z,u_w),\qquad
\mathcal C(u,v,w)=\int_Gg\,u\,P(vPw)\,dm.
\tag{143.3}
$$

**Theorem 143.2 (one jointly approximating sequence with exact rank two).** For every original $\theta\in\Theta$ there is one sequence of whole-$G$ pointwise Borel partitions $D_n=(D_{n,y})_{y\in\mathcal L}$ such that

$$
\begin{gathered}
D_n\in\mathscr D_{12}(\theta),\qquad
\operatorname{rank}A^{D_n}=2\quad(n\ge1),\\
\mathbf1_{D_{n,y}}\ \overset{*}{\rightharpoonup}\ f_y
\quad\text{in }L^\infty(m)\quad(y\in\mathcal L),\\
\|\nu_{D_n}^{(3)}-\nu_f^{(3)}\|_{\rm TV}
=\frac12\sum_{y,z,w\in\mathcal L}
\left|\mathcal C(\mathbf1_{D_{n,y}},\mathbf1_{D_{n,z}},\mathbf1_{D_{n,w}})
-\mathcal C(f_y,f_z,f_w)\right|\longrightarrow0.
\end{gathered}
\tag{143.4}
$$

Consequently, for every $\varepsilon>0$, the same single partition can satisfy all twelve exact marginal equations, exact rank two, and total-variation error below $\varepsilon$ in the full $64$-coordinate law. Every member is one deterministic common readout at all three original epochs. Its actual terminal factor in a coefficient with last label $w$ is always $P\mathbf1_{D_{n,w}}$; in $A^{D_n}$ it is $P\mathbf1_{D_{n,3}}$.

*Proof.* We first produce exact singular coarse partitions converging to (143.2). Both determinant signs occur arbitrarily close to $u^0$ in the product $L^\infty$ norm. For the positive sign, use the invariant bounded test of (139.5), with its three zero source moments and outside $\operatorname{span}\{1,\beta\}$. The tuples

$$
u^+=(3/4-c\beta-\epsilon v_+,\ c\beta,\ 1/4+\epsilon v_+)
\tag{143.5}
$$

are admissible for all sufficiently small $\epsilon>0$ and tend uniformly to $u^0$. Their actual terminal factor is $cP\beta=cg$, so (139.6) is a strictly positive weighted heat Gram matrix of three independent components. Thus $\det A(u^+)>0$ for every such nonzero $\epsilon$.

For the negative sign, choose the reflection-even $w$ of Proposition 141.1 and take a sufficiently small nonzero $\tau$, so that $k=c\beta+\tau w$ has the original three terminal marginals and $\Delta_k>0$. Theorem 141.2 gives a bounded invariant $v_-$ satisfying exactly the three source moments and four ordered equations in (141.3), with $Q_k(v_-,v_-)<0$. Theorem 140.2 then gives

$$
\begin{gathered}
u^-=(3/4-k-\epsilon v_-,\ k,\ 1/4+\epsilon v_-),\\
\det A(u^-)=\epsilon^2\Delta_k Q_k(v_-,v_-)<0.
\end{gathered}
\tag{143.6}
$$

Given any $\rho>0$, first choose $\tau\ne0$ sufficiently small that $\|k-c\beta\|_\infty<\rho/2$, retaining all the conclusions of Proposition 141.1. After obtaining its bounded $v_-$, choose $\epsilon>0$ sufficiently small that $\epsilon\|v_-\|_\infty<\rho/2$ and that Theorem 140.2 applies. Then $\|u^--u^0\|_\infty<\rho$, while its determinant is strictly negative. No uniform bound on $v_-$ as $\tau\to0$ is required. Likewise (143.5) gives $\|u^+-u^0\|_\infty<\rho$ with positive determinant. These statements use the source-specific suppliers of §§139–141; a dimension count or nonconstant ratio alone is not substituted for their negative-vector conclusion.

Choose a countable dense family $(\psi_l)_{l\ge1}$ in the real $L^1(m)$ unit ball. For each $n$, choose admissible invariant $u_n^+,u_n^-$ of the preceding forms with

$$
\|u_n^\pm-u^0\|_\infty<1/n,\qquad
\det A(u_n^+)>0>\det A(u_n^-).
\tag{143.7}
$$

Theorem 139.1 supplies actual invariant partitions $E_n^+,E_n^-\in\mathscr E_\theta$ of these respective determinant signs and satisfying

$$
\left|\int_G\psi_l(\mathbf1_{E_{n,i}^\pm}-u_{n,i}^\pm)\,dm\right|<1/n
\quad(l\le n,\ i\in\{S,C,B\}).
\tag{143.8}
$$

Indeed, for each fixed stochastic tuple its approximating actual determinants converge to a nonzero value, so sufficiently far terms retain that sign and satisfy the finitely many tests simultaneously. Combining (143.7)–(143.8) gives

$$
\left|\int_G\psi_l(\mathbf1_{E_{n,i}^\pm}-u_i^0)\,dm\right|<2/n
\quad(l\le n).
\tag{143.9}
$$

We join these two endpoints with the finite tests controlled throughout. For invariant cells, pairing with $\psi_l$ reduces on $X$ to pairing with its angular average $\bar\psi_l\in L^1(\bar m)$. On each quotient mismatch block $H_{ij}=E_{n,i}^+\cap E_{n,j}^-$, $i\ne j$, use the finite vector of measures

$$
\bar m,\quad\bar\nu_2,\bar\nu_3,\bar\nu_4,\quad
(\bar\psi_l)_+\bar m,\ (\bar\psi_l)_-\bar m
\quad(l\le n),
\tag{143.10}
$$

restricted to that block. These are finite atomless measures on the original quotient, with its actual measure (136.5). Recursive proportional subdivision by Dvoretzky–Wald–Wolfowitz Lemma 2 gives nested Borel $T_{ij,t}\subset H_{ij}$ proportional to $t$ for every measure in (143.10), as in (142.9). Switch the label from $i$ to $j$ on $T_{ij,t}$. The lifted whole-$G$ partitions $E_n(t)$ are invariant and remain in $\mathscr E_\theta$. Assign the null axis to $S$ throughout. For every tested $l\le n$ and every coarse label $i$, the exact switching formula is

$$
\int_G\psi_l\mathbf1_{E_{n,i}(t)}\,dm
=(1-t)\int_G\psi_l\mathbf1_{E_{n,i}^+}\,dm
+t\int_G\psi_l\mathbf1_{E_{n,i}^-}\,dm.
\tag{143.11}
$$

This follows by adding the incoming blocks and subtracting the outgoing blocks; proportionality for the positive and negative parts gives it also for signed tests. The same formula for the three source measures proves the exact nine marginal equations along the entire path. Thus (143.9) holds at every $t$, even though the endpoint test values need not equal one another.

The actual determinant is continuous along this path. Between parameters $s<t$, the changed set has $\nu_j$-measure at most $t-s$ for each $j=2,3,4$, since the mismatch blocks are disjoint and their subdivisions are proportional for $\bar\nu_j$. Each actual coefficient can change only when one of the three original states lies in that set. The union bound gives an entrywise difference at most $3|t-s|$, including the change in the terminal cell, exactly as in (139.9). The determinant polynomial is therefore continuous. Its endpoint signs in (143.8) yield a parameter $t_n$ with

$$
E_n=E_n(t_n)\in\mathscr E_\theta,\qquad
\det A_{E_n}=0.
\tag{143.12}
$$

Equations (143.9)–(143.11), the density of the $\psi_l$, and the uniform bound of the indicators imply

$$
\mathbf1_{E_{n,i}}\ \overset{*}{\rightharpoonup}\ u_i^0
\quad(i\in\{S,C,B\}).
\tag{143.13}
$$

Write $E_n=(S_n,C_n,B_n)$. The actual common three-time density is still

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3),\qquad
W\ge0,\quad\|W\|_{L^1(m^3)}=1.
\tag{143.14}
$$

Finite rectangular-tensor approximation in $L^1(m^3)$, as in §123 and (139.3), makes every trilinear coefficient continuous under componentwise bounded weak-star convergence. In particular (143.13) gives $A_{E_n}\to A(u^0)$, with the actual $P\mathbf1_{C_n}$ used in every $A_{E_n}$.

The limiting coarse matrix has rank two and a strictly positive principal minor on its $C,B$ indices. Indeed $Pu_C^0=cg$, and hence

$$
A(u^0)_{ij}=c\langle gu_i^0,P(gu_j^0)\rangle_m.
\tag{143.15}
$$

Its components span $\operatorname{span}\{1,\beta\}$; the functions $u_C^0=c\beta$ and $u_B^0=1/4$ are independent because $\beta$ is nonconstant by Proposition 135.2. Strict positivity of $g$ and injectivity of $T_{d/2}$ make their two-by-two weighted heat Gram matrix positive definite. That principal minor remains positive in $A_{E_n}$ for all sufficiently large $n$. Together with (143.12), this proves $\operatorname{rank}A_{E_n}=2$ for all sufficiently large $n$.

Apply Theorem 142.1 to each $E_n$ with $\Psi_n=\{\psi_1,\ldots,\psi_n\}$. It gives a whole-$G$ Borel $v_n$ with

$$
\begin{gathered}
v_n^2=\mathbf1_{S_n}\quad\text{everywhere},\qquad
v_n\circ R_\pi=-v_n\quad m\text{-a.e.},\\
Q_{E_n}(v_n,v_n)=0,\qquad
\int_G\psi_l v_n\,dm=0\quad(l\le n).
\end{gathered}
\tag{143.16}
$$

Since $\|v_n\|_\infty\le1$, the growing exact test family implies $v_n\overset{*}{\rightharpoonup}0$. Define

$$
D_{n,0}=\{v_n=1\},\quad D_{n,1}=\{v_n=-1\},\quad
D_{n,3}=C_n,\quad D_{n,B}=B_n.
\tag{143.17}
$$

These are disjoint pointwise Borel partitions of the whole $G$. Invariance of each source density under $R_\pi$ and oddness of $v_n$ give its three zero source moments. Together with the nine coarse marginals this proves all twelve original equations for $D_n$. The ordered congruence (138.7), using the same matrix of (138.6), applies with the actual terminal factor $P\mathbf1_{C_n}$ and gives

$$
\operatorname{rank}A^{D_n}=\operatorname{rank}A_{E_n}.
\tag{143.18}
$$

Discard finitely many initial terms and relabel to obtain exact rank two for every member. This leaves all the convergence statements intact. Pointwise,

$$
\mathbf1_{D_{n,0}}=(\mathbf1_{S_n}+v_n)/2,\qquad
\mathbf1_{D_{n,1}}=(\mathbf1_{S_n}-v_n)/2.
\tag{143.19}
$$

Equations (143.13), (143.16) and (143.19) now give weak-star convergence of all four indicators to the original $f$ classes of (143.1). Applying the actual density (143.14) to each of the $64$ triples gives coordinatewise convergence. The finite sum defining total variation tends to zero, proving (143.4).

The source-specific composition in this theorem is `repo-derived`: the arbitrary-smallness consequence of the reflection construction, interpolation controlling a growing finite test family, exact coarse singularity with a surviving positive minor, and the consumed finite-moment signs yield the same jointly approximating sequence. Dvoretzky–Wald–Wolfowitz supplies only finite linear subdivisions; the weighted Gram identity supplies the positive minor; the actual path density supplies continuity. None alone asserts this same-witness result or exact full-law attainment. $\square$

## 144. The noncompactness and exact-attainment boundary

**Proposition 144.1 (the constant $B$ limit is separated in $L^1$).** For every original $\theta$, the sequence of Theorem 143.2 satisfies

$$
\mathbf1_{D_{n,B}}\overset{*}{\rightharpoonup}\frac14,\qquad
m(D_{n,B})\longrightarrow\frac14,\qquad
\left\|\mathbf1_{D_{n,B}}-\frac14\right\|_{L^1(m)}
\longrightarrow\frac38.
\tag{144.1}
$$

It has no $L^1(m)$-convergent subsequence in its $B$ component, and the four-component sequence is not relatively compact in the product $L^1$ topology.

*Proof.* The first limit is (143.4); pairing it with the constant $1\in L^1(m)$ gives the second. For any Borel $B'\subset G$, $m(G)=1$ gives the exact identity

$$
\left\|\mathbf1_{B'}-\frac14\right\|_1
=\frac34m(B')+\frac14(1-m(B'))
=\frac14+\frac12m(B').
\tag{144.2}
$$

This proves the last limit. If a subsequence converged in $L^1$ to $u$, then pairing with every bounded test, together with its weak-star limit, would give $u=1/4$ almost everywhere. This contradicts the last limit in (144.1). Product relative compactness would imply relative compactness of this component, so it fails as well. $\square$

**Proposition 144.2 (zero residual infimum and the unchanged exact target).** For every original $\theta\in\Theta$,

$$
\inf_{\substack{D\in\mathscr D_{12}(\theta)\\\operatorname{rank}A^D=2}}
\|\nu_D^{(3)}-\nu_f^{(3)}\|_{\rm TV}=0.
\tag{144.3}
$$

The exact target remains

$$
\begin{aligned}
F_{64}(\theta):\quad&\exists\text{ one whole-}G\text{ Borel partition }D,\\
&\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
=\mathcal C(f_y,f_z,f_w)
\quad\text{for every }(y,z,w)\in\mathcal L^3.
\end{aligned}
\tag{144.4}
$$

Neither attainment of (144.3), equality $A^D=A^f$ for an exact-rank-two partition, nor the universal statement $\forall\theta\in\Theta\ F_{64}(\theta)$ is established here.

*Proof.* The same sequence in (143.4) proves (144.3), since each of its members lies in the displayed exact-marginal, exact-rank-two class and the residual is nonnegative. This in particular precludes a strictly positive residual lower bound on that class for any fixed original $\theta$. It does not turn an infimum into a minimum.

The weak-star compact stochastic class of Proposition 123.2 contains the limit $f$; its deterministic partition subset need not contain that limit. Proposition 144.1 exhibits this distinction for the constructed sequence and supplies no $L^1$ compactness from which to extract an attaining partition. Nor does noncompactness prove nonattainment: a different partition could attain (144.4). Proposition 135.3 gives the forward implication from (144.4) to the twelve marginals and $A^D=A^f$ of rank two; the converse is still absent. Theorem 143.2 gives $A^{D_n}\to A^f$ and full-law convergence, not equality at any finite index. The missing inference for exact attainment is existence of an indicator tuple in the exact fiber $\Phi_3^{-1}(\Phi_3(f))$, or another argument producing all $64$ equalities for one partition; the limits above do not supply it.

All these statements are conditional on the complete original endpoint and source suppliers retained in Definition 143.1. Every deterministic function is defined on the original $G$ and used at every original observation epoch, with the actual terminal $P\mathbf1_{D_w}$. The sequence is a mathematical family of common readouts. No additional randomness, controller, memory, stationary initial law, killed endpoint, time change, separate slot partition or postselection is introduced. A native source/evolution/readout correspondence remains the separate unresolved bridge specified in §§115–117. $\square$

## 追加锚（本行以下为增补区）
## 145. One odd sign for all three actual terminal forms

**Definition 145.1 (the signed terminal family on an invariant support).** Retain the complete original telescope of Theorems 142.1 and 143.2. Write
$\mathscr R=R_\pi$, let $E=(E_S,E_C,E_B)=(S,C,B)\in\mathscr E_\theta$, and put

$$
q_i=P\mathbf1_{E_i},\qquad
Q_i(u,v)=\int_G g\,u\,P(q_i v)\,dm,
\qquad i\in\{S,C,B\}.
\tag{145.1}
$$

For a half-turn-invariant Borel set $A\subset S$ with $m(A)>0$, let

$$
\mathcal V_{A,-}=\{u\in L^\infty(G,m;\mathbb R):u=0\ \text{a.e. on }G\setminus A,
\ u\circ\mathscr R=-u\ \ m\text{-a.e.}\}.
\tag{145.2}
$$

The quadratic value of $Q_i$ is its symmetric value $Q_i(u,u)$. For
$\lambda=(\lambda_S,\lambda_C,\lambda_B)\in\mathbb R^3$ write

$$
r_\lambda=\sum_i\lambda_i\mathbf1_{E_i},\qquad
q_\lambda=Pr_\lambda,\qquad
Q_\lambda=\sum_i\lambda_iQ_i.
\tag{145.3}
$$

**Proposition 145.2 (the signed-pencil index on every invariant slack set).** For every nonzero $\lambda\in\mathbb R^3$, the symmetric quadratic form $u\mapsto Q_\lambda(u,u)$ has infinite negative index on $\mathcal V_{A,-}$. The same remains true after imposing any finite family of homogeneous real bounded linear constraints on $\mathcal V_{A,-}$.

*Proof.* Use the invariant analytic representatives of $g$ and $q_i$ on the connected set $\Omega=\{x^2+y^2>0\}$ supplied by Appendix II §§120, 122 and 133. Write $q=q_\lambda$. This is a real invariant analytic function. Injectivity of the actual $P$ shows that $q\ne0$: otherwise $r_\lambda=0$ almost everywhere, and the positive measure of each cell in (136.1) forces $\lambda=0$.

The ratio $q/g$ is not constant almost everywhere. Indeed $g=P\beta$ by Proposition 136.2. If $q=c_0g$, injectivity gives $r_\lambda=c_0\beta$. The case $c_0=0$ has just been excluded. For $c_0\ne0$, this identity makes the analytic representative of $g_d=[\beta]$ constant on each positive-measure cell. Analytic uniqueness on $\Omega$ would make $g_d$ constant everywhere there, contradicting Proposition 135.2. This argument concerns the analytic representative of $g_d$, not the arbitrary values of the Borel representative $\beta$ on null sets.

Let $F$ be the half-circle section of Theorem 137.1, and let $k$ be its nonsingular odd heat kernel (137.3). The localized kernel of the symmetric polarization is

$$
s_\lambda(x,y)=\frac{g(x)q(y)+q(x)g(y)}2\,k(x,y).
\tag{145.4}
$$

First suppose $m(A\cap\{q<0\})>0$. Intersect with the density points of $A$ and with $\{g>0\}$. In the quotient coordinates of (136.5), Fubini's theorem gives one rotation orbit containing a positive-angular-measure set of these points in $\operatorname{int}F$. For every $n$, choose $n$ distinct such points $x_1,\ldots,x_n$. Invariance makes $g(x_j)=g_0>0$ and $q(x_j)=q_0<0$ independent of $j$. Half-turn invariance of $A$ makes all reflected points density points as well. The bounded odd localized indicators supported in $A$, constructed as in (137.5), have symmetric Gram matrices tending to

$$
4g_0q_0\bigl(k(x_i,x_j)\bigr)_{i,j=1}^n.
$$

Nonsingularity makes this limit negative definite. Small enough neighborhoods therefore give an $n$-dimensional negative subspace. This uses a slice of the density set, not invariance of $A$ under the full rotation circle.

It remains to consider $q\ge0$ almost everywhere on $A$. Since $q$ is nonzero analytic, its zero set is null. Choose a relatively compact positive-measure Borel set $A_0\subset A\cap\operatorname{int}F$ on which $g,q\ge\epsilon_0>0$, and let $A_0^*$ be its density points. Continuity gives the same lower bounds at every point of $A_0^*$. Suppose, for a contradiction, that the negative index on $\mathcal V_{A,-}$ is finite, say $\kappa$. Localization as in (137.5) implies that every finite Gram matrix of $s_\lambda$ on $A_0^*$ has at most $\kappa$ negative eigenvalues.

For each positive scalar $\tau$, define on $A_0^*$

$$
\gamma_\tau=\frac{\tau g-q}{\tau g+q},\qquad |\gamma_\tau|\le1.
\tag{145.5}
$$

The exact identity

$$
s_\lambda(x,y)=\frac{(\tau g(x)+q(x))(\tau g(y)+q(y))}{4\tau}
\bigl(1-\gamma_\tau(x)\gamma_\tau(y)\bigr)k(x,y)
\tag{145.6}
$$

and positive diagonal congruence give at most $\kappa$ negative squares for the last kernel. Repeated points follow by pullback from a distinct-point matrix; the real symmetric matrices have the same real and complex Hermitian inertia. Use $\mathcal H_-=T_{d/2}L^2_-$ with its inverse-heat norm, restricted to $F$, exactly as in (137.2). Its kernel is nonsingular by (137.4). Every member of $\mathcal H_-$ and every sum of two products of its members is analytic on $\Omega$. Thus $A_0^*$ is a uniqueness set for both classes: apply Mityagin, [*The zero set of a real analytic function*, Proposition 0](https://arxiv.org/html/1512.07276v1), to real and imaginary parts, using local equivalence of $m$ and Lebesgue measure. These are both uniqueness hypotheses of Agler--Young, [*Functions which are almost multipliers of Hilbert function spaces*, Theorem 2.1](https://arxiv.org/html/math/9605224v1#S2.Thmtheorem1).

That theorem, with its kernel parameter equal to $1$, gives a closed finite-codimensional $W_\tau\subset\mathcal H_-$ and a bounded $L_\tau:W_\tau\to\mathcal H_-$ satisfying $L_\tau u=\gamma_\tau u$ on $A_0^*$. Analytic uniqueness extends the product identity to all of $\Omega$:

$$
(\tau g+q)L_\tau u=(\tau g-q)u\qquad(u\in W_\tau).
\tag{145.7}
$$

This identity forces $q\ge0$ on all of $\Omega$ under the finite-index supposition. To prove this, if $q<0$ somewhere, continuity and $g>0$ almost everywhere give a point $x_0\in\Omega$ with $g(x_0)>0>q(x_0)$. Choose $\tau=-q(x_0)/g(x_0)>0$. Along the whole rotation orbit of $x_0$, the left coefficient in (145.7) is zero and the right coefficient is the same strictly positive number $2\tau g(x_0)$. Consequently every $u\in W_\tau$ vanishes at every point of that orbit. Choose arbitrarily many distinct representatives $x_1,\ldots,x_n$ in $\operatorname{int}F$. Their evaluation vectors $k(\cdot,x_j)$ are linearly independent by (137.4), and all belong to $W_\tau^\perp$. This contradicts its finite dimension. This is the finite singular-set obstruction underlying Agler--Young Lemma 2.3, applied here to the actual odd heat kernel and the original rotation orbit.

In particular the finite-index supposition now supplies, rather than assumes, a global real invariant multiplier

$$
\gamma=\frac{g-q}{g+q}\quad\text{where }g+q>0,\qquad
\gamma=0\quad\text{on its null complement},\qquad |\gamma|\le1.
$$

A zero of a signed denominator with $g>0$ forces the common orbit vanishing in (145.7). After the deduction $q\ge0$, all zeros of $g+q$ lie in $\{g=0\}$, which is null. With $\tau=1$, (145.7) gives $L_1u=\gamma u$ globally as $L^2(m)$ classes. Here no global lower bound on $g+q$ is used.

For clarity, the operator steps of (137.8)--(137.13) now have the following global premises. The space

$$
D=\{u\in\mathcal H_-:\gamma u\in\mathcal H_-\}
$$

contains the closed finite-codimensional $W_1$, so it is itself closed and finite codimensional: $D/W_1$ is a subspace of the finite-dimensional quotient $\mathcal H_-/W_1$. Its multiplication map has closed graph, because convergence in $\mathcal H_-$ implies convergence in $L^2(m)$ and $M_\gamma$ is bounded on that entire $L^2$ space. The closed graph theorem makes multiplication bounded on $D$ in the heat norm. The full rotation circle preserves $D$ and $D^\perp$. Choose a positive odd angular character $\ell$ absent from the finite-dimensional representation on $D^\perp$. Its entire heat sector is contained in $D$ and is nonzero by injectivity of heat propagation on nonzero smooth punctured character-$\ell$ tests. With $\sigma=d/2$ and the original self-adjoint sector restriction $K_\ell$, it follows that

$$
B_\ell=e^{\sigma K_\ell}M_\gamma e^{-\sigma K_\ell}
\quad\text{is bounded on }L^2_\ell.
$$

For $\Pi_R=\mathbf1_{[0,R]}(K_\ell)$ the entire cutoff functions

$$
F_R(z)=\Pi_Re^{zK_\ell}M_\gamma e^{-zK_\ell}\Pi_R
$$

are bounded on each closed vertical strip. On $\Re z=\sigma$ their norms are bounded by $\|B_\ell\|$ through imaginary-time unitary conjugation; on $\Re z=-\sigma$ the same follows by adjointness, since $\gamma$ is real. Three-lines interpolation and Cauchy's estimate give $\|F_R'(0)\|\le2\|B_\ell\|/\sigma$, uniformly in $R$. Since $M_\gamma$ is globally bounded in $L^2$, spectral convergence in the graph norm of $K_\ell$ gives the bounded form

$$
\left|\langle K_\ell u,\gamma v\rangle_m-
\langle\gamma u,K_\ell v\rangle_m\right|
\le\frac{2\|B_\ell\|}{\sigma}\|u\|_2\|v\|_2
\qquad(u,v\in D(K_\ell)).
$$

On a rotation-saturated compact patch in $\{r>0,g>0,q>0\}$, $\gamma$ is smooth analytic. Such a patch exists because $g,q>0$ almost everywhere. For

$$
u_N=e^{i\ell\alpha}\chi(r,z,\xi)e^{iN\omega\cdot(r,z,\xi)},
\qquad\chi\in C_c^\infty,\quad\omega\in\mathbb R^3,
$$

with amplitude supported there, both $u_N$ and $\gamma u_N$ are genuine original punctured-core vectors. The form bound identifies and bounds the actual vector commutator on these tests. By the original principal symbol (137.12) and the Leibniz identity (137.13), its order-$N$ term is

$$
-2iN e^{i\ell\alpha+iN\omega\cdot(r,z,\xi)}\chi
\left[a\gamma_r\omega_r+a\gamma_z\omega_z+
\left(\eta+\frac{ar^2}{4}\right)\gamma_\xi\omega_\xi\right],
$$

and the remainder is bounded in $L^2(m)$ independently of $N$. Divide the commutator bound by $N$ and use arbitrary amplitudes and the three coordinate choices of $\omega$. Since $a,\eta>0$, this forces $\gamma_r=\gamma_z=\gamma_\xi=0$; rotation invariance gives $\gamma_\alpha=0$. On a connected nonempty such patch $\gamma=\gamma_0\in(-1,1)$. Analytic continuation of $g-q-\gamma_0(g+q)$ then yields

$$
q=c_0g\quad\text{on }\Omega,\qquad
c_0=\frac{1-\gamma_0}{1+\gamma_0}.
\tag{145.8}
$$

This contradicts the nonconstant-ratio conclusion above. The negative index is therefore infinite in this branch too.

Finally, for any $n$ and any $r$ homogeneous linear constraints, intersect a negative-definite subspace of dimension $n+r$ with their common kernels. The intersection has dimension at least $n$ and remains negative definite. This proves infinite index after every stated finite family of constraints. No sign restriction on $\lambda$, and no full rotation invariance of $A$, has been imposed. $\square$

**Theorem 145.3 (one same sign cancels all three actual terminal forms).** For every original $\theta=(a,\eta,d,b)\in\Theta$, every fixed actual invariant coarse partition $E=(S,C,B)\in\mathscr E_\theta$, and every finite set $\Psi\subset L^1(G,m;\mathbb R)$, there is a bounded whole-$G$ Borel function $v$ such that

$$
\begin{gathered}
v^2=\mathbf1_S\quad\text{everywhere},\qquad
v\circ\mathscr R=-v\quad m\text{-a.e.},\\
\int_G\psi v\,dm=0\quad(\psi\in\Psi),\\
\mathcal C(v,v,\mathbf1_S)=\mathcal C(v,v,\mathbf1_C)
=\mathcal C(v,v,\mathbf1_B)=0.
\end{gathered}
\tag{145.9}
$$

The three equalities use the same sign and the same actual cells and terminal heat images.

*Proof.* Let $\mathcal V_{S,-}^{\Psi}$ be the subspace (145.2) with the moment equations in (145.9). Choose a basis of the finite-dimensional span of the three quadratic forms $Q_i(u,u)$. Proposition 145.2 and Lemma 125.3, applied to every real pencil in that basis, give a two-dimensional real subspace $U\subset\mathcal V_{S,-}^{\Psi}$ on which all three quadratic forms vanish identically. If the span is zero, any two-dimensional subspace of $\mathcal V_{S,-}^{\Psi}$ has this property. Choose a nonzero $u\in U$ and scale it so that $\|u\|_\infty\le1$.

Let $\mathcal K$ be the set of real classes $w$ with support in $S$, $w\circ\mathscr R=-w$, $\|w\|_\infty\le1$, the moments in $\Psi$ equal to zero, and $Q_i(w,w)=0$ for $i=S,C,B$. It is nonempty by $u$. It is weak-star compact. Indeed the linear conditions are weak-star closed, and each quadratic form is weak-star continuous on the unit ball: its ordered kernel is

$$
a_i(x,y)=g(x)p_d(x,y)q_i(y)\ge0,\qquad
\|a_i\|_{L^1(m^2)}=\int_GgPq_i\,dm\le1,
\tag{145.10}
$$

so finite rectangular-tensor approximation in $L^1(m^2)$ reduces continuity to finitely many scalar pairings.

Choose a Borel representative of $w$ which is odd on $S\setminus N$ by using the half-circle section and reflection. Choose a countable separating family $(\psi_n)$ in the real unit ball of $L^1(m)$ and maximize on $\mathcal K$ the strictly convex function

$$
J(w)=\sum_{n\ge1}2^{-n}\left(\int_G\psi_nw\,dm\right)^2.
\tag{145.11}
$$

Let $w$ be a maximizer. Suppose the half-turn-invariant slack set

$$
A_n=S\cap\{|w|\le1-1/n\}
\tag{145.12}
$$

has positive measure for some $n$. Replacing it by $A_n\cap\mathscr R A_n$ if necessary makes it exactly half-turn invariant without changing its positive measure. Use Proposition 145.2 on this invariant set with the finite constraints consisting of the moments $\int\psi\,\cdot\,dm$ and the three symmetric polar equations $Q_i^{\rm sym}(w,\cdot)=0$. Lemma 125.3 supplies a nonzero bounded $z$ supported in $A_n$ with

$$
Q_i(z,z)=Q_i^{\rm sym}(w,z)=0\qquad(i=S,C,B).
\tag{145.13}
$$

For sufficiently small nonzero $\varepsilon$, both $w+\varepsilon z$ and $w-\varepsilon z$ remain in the unit ball, and (145.13) keeps them in $\mathcal K$. They are distinct, while strict convexity gives

$$
J(w)<\frac{J(w+\varepsilon z)+J(w-\varepsilon z)}2,
$$

contradicting maximality. Hence $|w|=1$ almost everywhere on $S$.

Take a Borel representative, put $v=\operatorname{sgn}(w)$ on the full-measure set where $|w|=1$, assign either sign on the remaining null subset of $S$, and put $v=0$ off $S$. Then $v^2=\mathbf1_S$ pointwise, and all displayed integrals and quadratic values are unchanged. Since $Q_i(v,v)=\mathcal C(v,v,\mathbf1_{E_i})$, (145.9) follows. $\square$

The signed-pencil step is source-specific because $q_\lambda=P(\lambda_S\mathbf1_S+\lambda_C\mathbf1_C+\lambda_B\mathbf1_B)$ is the actual terminal heat image in the original clock. Agler--Young is used only with the nonsingular odd heat kernel and the analytic uniqueness sets supplied in §137; Dvoretzky--Wald--Wolfowitz is not being used to turn nonlinear quadratic constraints into linear ones. The extremal argument instead uses the exact signed-pencil property on each half-turn-invariant slack set.

## 146. The same-partition exact-contrast sequence

**Theorem 146.1 (rank-two common partitions with four exact terminal contrasts).** For every original $\theta\in\Theta$, there is a sequence of whole-$G$ pointwise Borel partitions

$$
D_n=(D_{n,0},D_{n,1},D_{n,3},D_{n,B})
\tag{146.1}
$$

such that

$$
\begin{gathered}
D_n\in\mathscr D_{12}(\theta),\qquad \operatorname{rank}A^{D_n}=2,\\
\mathcal C(v_n,v_n,\mathbf1_{D_{n,w}})=0
\quad(w=0,1,3,B),\\
\mathbf1_{D_{n,y}}\overset{*}{\rightharpoonup}f_y
\quad\text{in }L^\infty(m)\quad(y=0,1,3,B),\\
\|\nu_{D_n}^{(3)}-\nu_f^{(3)}\|_{\rm TV}\longrightarrow0,
\end{gathered}
\tag{146.2}
$$

where $v_n=\mathbf1_{D_{n,0}}-\mathbf1_{D_{n,1}}$. Each equality in the second line is an equality for the corresponding actual terminal $P\mathbf1_{D_{n,w}}$.

*Proof.* The determinant-sign and proportional-subdivision construction in (143.7)--(143.15), applied with its exact original marginal measures, supplies invariant coarse partitions $E_n=(S_n,C_n,B_n)\in\mathscr E_\theta$ for which

$$
\operatorname{rank}A_{E_n}=2,\qquad
\mathbf1_{E_{n,i}}\overset{*}{\rightharpoonup}u_i^0
\quad(i=S,C,B),\qquad
A_{E_n}\longrightarrow A(u^0).
\tag{146.3}
$$

The positive principal minor in (143.15) is retained when the finite initial segment is discarded and the sequence is relabelled. This is a new choice of the coarse partitions; no sign identity is assumed from the sequence used in Theorem 143.2.

Choose a countable dense family $(\psi_l)_{l\ge1}$ in the real unit ball of $L^1(m)$. Apply Theorem 145.3 to $E_n$ and $\Psi_n=\{\psi_1,\ldots,\psi_n\}$, and call the resulting sign $v_n$. Define

$$
D_{n,0}=\{v_n=1\},\quad D_{n,1}=\{v_n=-1\},\quad
D_{n,3}=C_n,\quad D_{n,B}=B_n.
\tag{146.4}
$$

Because the three source densities $g_{2d},g_{3d},g_{4d}$ are invariant under $\mathscr R$, oddness gives
$\int g_{jd}v_n\,dm=0$. Together with the nine equations for $E_n$, this proves all twelve original marginal equations for $D_n$.

The half-turn commutation of $P$ gives $P v_n$ odd. Hence $v_nPv_n$ is invariant, $P(v_nPv_n)$ is invariant, and

$$
\mathcal C(v_n,v_n,v_n)=\int_Gg\,v_nP(v_nPv_n)\,dm=0.
\tag{146.5}
$$

Theorem 145.3 gives the three coarse terminal equalities. Since

$$
\mathbf1_{D_{n,0}}=\frac{\mathbf1_{S_n}+v_n}{2},\qquad
\mathbf1_{D_{n,1}}=\frac{\mathbf1_{S_n}-v_n}{2},
\tag{146.6}
$$

(146.5) yields

$$
\mathcal C(v_n,v_n,\mathbf1_{D_{n,0}})=
\mathcal C(v_n,v_n,\mathbf1_{D_{n,1}})=0.
\tag{146.7}
$$

For the other two labels, (145.9) is exactly the same assertion, proving all four actual-terminal contrasts in (146.2).

For any invariant bounded $u$, the two cross pairings with an odd $v_n$ vanish by the half-turn change of variables:

$$
Q_{E_n}(u,v_n)=Q_{E_n}(v_n,u)=0.
\tag{146.8}
$$

The ordered congruence (138.7), with the actual terminal $P\mathbf1_{C_n}$, therefore gives

$$
\operatorname{rank}A^{D_n}=\operatorname{rank}A_{E_n}=2.
\tag{146.9}
$$

The moments imposed in Theorem 145.3 imply $v_n\overset{*}{\rightharpoonup}0$. Equations (146.3) and (146.6) thus give the four weak-star limits in (146.2). The actual path density

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3)
\tag{146.10}
$$

is nonnegative and integrable with mass one. Rectangular-tensor approximation in $L^1(m^3)$, as in Proposition 123.2, makes every one of the 64 trilinear coefficients continuous under these bounded componentwise weak-star limits. Their finite sum is the displayed total-variation convergence.

In the restricted invariant coarse/odd construction, the invertible change of components from $(\mathbf1_{D_0},\mathbf1_{D_1},\mathbf1_{D_3},\mathbf1_{D_B})$ to $(\mathbf1_S,\mathbf1_C,\mathbf1_B,v)$ sends the target tuple to $(u_S^0,u_C^0,u_B^0,0)$ as $m$-classes. Multilinearity makes exact equality of the two 64-coordinate arrays equivalent to equality in these transformed components. There are the 27 coarse equations

$$
\mathcal C(\mathbf1_{E_i},\mathbf1_{E_j},\mathbf1_{E_k})
=\mathcal C(u_i^0,u_j^0,u_k^0),
\qquad i,j,k\in\{S,C,B\},
\tag{146.11}
$$

and, after the three equations in (145.9) and the automatic cubic identity (146.5), the six remaining ordered quadratic obligations

$$
\mathcal C(v,\mathbf1_{E_j},v)=0\quad(j=S,C,B),\qquad
\mathcal C(\mathbf1_{E_i},v,v)=0\quad(i=S,C,B).
\tag{146.12}
$$

The 27 terms with exactly one $v$ and the cubic term vanish by half-turn parity; of the nine terms with exactly two $v$ factors, (145.9) cancels three and (146.12) lists the other six. These counts enumerate ordered coefficients, not independent equations. Thus (146.11)--(146.12) describe the obligations left by this restricted construction; they do not exhaust all possible $F_{64}$ witnesses and do not establish the universal target (144.4). $\square$

The source-specific content of Theorems 145.3 and 146.1 is the signed-pencil-to-extreme-sign composition and its insertion into the actual rank-two coarse sequence. The heat-image analyticity, odd kernel nonsingularity, source boundedness, exact coarse sequence, ordered congruence, and common path density are the supplied results of §§120, 133, 138, 143 and 123. Dvoretzky--Wald--Wolfowitz, [*Relations among certain ranges of vector measures*, §3 Theorem 4 and Lemma 2](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), is used only for the finite linear proportional subdivisions in the coarse construction. These results give a conditional actual three-terminal sign and its same-partition sequence consumer; they do not prove attainment of (144.4), nonattainment, a physical realization or the universal $\forall\theta\,F_{64}(\theta)$ statement.

## 追加锚（本行以下为增补区）

## 147. A regular binary zero for the original source

**Definition 147.1 (the original binary moment map).** Fix an arbitrary original tuple $\theta=(a,\eta,d,b)\in\Theta$ of Definition 134.1, with the complete endpoint, source and analytic suppliers of Appendix II §§115–117, 123–125 and 133, and §§134–144 above. In particular, $G=H^1\times\mathbb R$ has the original product and raw Haar measure $\mu$; $h$ is the coefficient-positive normalized original zero state; $m=h^2\mu$; $K=U_h^{-1}H_{\rm end}U_h$ is the full conservative self-adjoint operator with its source coordinate; and the diffusion starts at $e$ at time zero. Put

$$
P=T_d=e^{-dK},\qquad g=g_{2d},\qquad p=\frac14,
\qquad g_j=P^jg\quad(j=0,1,2).
\tag{147.1}
$$

Thus the epochs remain $2d,3d,4d$. Keep exactly the original $b,M,c$ and four functions $f$ in (134.5)–(134.8). The functions $g_j$ are bounded by Theorem 133.2. All spaces below are real bounded Borel $m$-classes unless otherwise specified; representatives on null sets can be chosen arbitrarily. For such $v$ define

$$
\begin{aligned}
L(v)&=(\langle g_0,v\rangle_m,\langle g_1,v\rangle_m,
                         \langle g_2,v\rangle_m),\\
q_1(v)&=\langle gv,Pv\rangle_m,
&q_2(v)&=\langle gv,P^2v\rangle_m,
&q_3(v)&=\langle Pg\,v,Pv\rangle_m,\\
q(v)&=(q_1(v),q_2(v),q_3(v)),
&B_j(v,w)&=\tfrac12(q_j(v+w)-q_j(v)-q_j(w)),\\
\tau(v)&=\mathcal C(v,v,v),
&\mathcal F(u)&=(L(u-p),q(u-p),\tau(u-p))\in\mathbb R^7.
\end{aligned}
\tag{147.2}
$$

Here $\mathcal C(u,v,w)=\int guP(vPw)\,dm$ is the original form, including its actual terminal factor. The seven coordinates are, respectively, the three centered one-time, three centered two-time and one centered three-time moments under the original source-start law. Rotations $R_\alpha$ act in the original symmetric coordinates $(r,\vartheta,z,\xi)$ of (120.4), on $\Omega=\{r>0\}$. Its complement is $m$-null. A function is called odd or even according to its transformation under $R_\pi$. A real pure positive frequency $n$ means the real span of the complex angular characters $n$ and $-n$, allowing Borel amplitudes in $(r,z,\xi)$.

**Lemma 147.2 (three independent source marginals).** The functions $g,Pg,P^2g$ are linearly independent in $L^2(m)$.

*Proof.* Suppose $A_0g+A_1Pg+A_2P^2g=0$ for a nonzero real coefficient vector. Spectral calculus for $K$ says that the spectral measure of $g$ is supported on the zeros, for $\lambda\ge0$, of

$$
A_0+A_1e^{-d\lambda}+A_2e^{-2d\lambda}.
\tag{147.3}
$$

There are at most two such zeros. Write $g=\sum_{\lambda\in E}v_\lambda$, where $E$ is this finite set and $Kv_\lambda=\lambda v_\lambda$. For every $0<s<2d$, the original propagation identity gives $g=T_{2d-s}g_s$. Each $T_t$ is injective. Applying the spectral projection outside $E$ therefore shows that $g_s$ has no component outside $E$, and applying the projections onto its members gives

$$
g_s=\sum_{\lambda\in E}e^{(2d-s)\lambda}v_\lambda
\longrightarrow r:=\sum_{\lambda\in E}e^{2d\lambda}v_\lambda
\quad\hbox{in }L^2(m)\quad(s\downarrow0).
\tag{147.4}
$$

The original continuous source-start paths of Theorem 117.2 give $\int\psi g_s\,dm\to\psi(e)$ for every $\psi\in C_c(G)$. Since $m(G)=1$, (147.4) implies that the finite measure $r\,m$ equals $\delta_e$. This contradicts $m(\{e\})=0$. Thus (147.3) cannot arise. In particular, the Gram matrix of the three bounded functions $g_j$ is positive definite. $\square$

**Lemma 147.3 (high-frequency correction with three independent differentials).** Let $N$ be any positive odd integer. Let $V_N$ be the space of bounded real classes invariant under $R_{2\pi/N}$ and odd under $R_\pi$. For every $c\in\mathbb R^3$ there exist $w,h_1,h_2,h_3\in V_N$ such that

$$
q(w)=c,\qquad B_j(w,h_k)=\delta_{jk}\quad(1\le j,k\le3).
\tag{147.5}
$$

*Proof.* First, every nonzero pencil $q_\lambda=\sum_j\lambda_jq_j$ has infinite negative index on $V_N$. If $(\lambda_1,\lambda_3)\ne(0,0)$, use Corollary 133.3 with source time $2d$, gap $d$, and coefficients $(\alpha,\beta,\gamma)=(\lambda_1,\lambda_3,\lambda_2)$. It supplies a negative bounded real test at each of the distinct positive odd multiples of $N$, with zero polar cross-pairings. Those tests belong to $V_N$. If only $\lambda_2\ne0$, apply the same corollary with source time $2d$, gap $2d$, and coefficients $(\lambda_2,0,0)$. Its form is exactly $\lambda_2\langle gv,T_{2d}v\rangle_m=\lambda_2q_2(v)$. This invocation concerns the same operator's pair form; it changes none of the observation epochs in (147.1). Intersecting arbitrarily large negative subspaces with any finite-codimensional linear subspace $W\subset V_N$ proves the same infinite-index property on $W$.

We need the following consequence, proved here on these spaces:

$$
q(W)=\mathbb R^3
\quad\hbox{for every finite-codimensional }W\subset V_N.
\tag{147.6}
$$

For each unit vector $\lambda\in\mathbb R^3$, select a five-dimensional negative subspace for $q_\lambda$ in $W$. Negativity on its unit sphere persists for pencil coefficients in a neighborhood of $\lambda$. A finite cover of the coefficient sphere and the sum of the selected subspaces give a finite-dimensional $E\subset W$ on which every unit pencil has at least five negative eigenvalues. Equip $E$ with any Euclidean inner product. Continuity of eigenvalues and compactness supply a single $\delta>0$ such that the fifth smallest eigenvalue of every unit pencil is at most $-\delta$.

Fix a target $c$, choose $R>0$ with $R^2>\|c\|/\delta$, and minimize $H(x)=\|q(x)-c\|^2$ on $\|x\|=R$ in $E$. Suppose its residual $\lambda=q(x)-c$ is nonzero. In a five-dimensional negative spectral subspace for $q_{\lambda/\|\lambda\|}$ choose $w\ne0$ satisfying the four linear equations

$$
B_j(x,w)=0\quad(j=1,2,3),\qquad (x,w)_E=0.
\tag{147.7}
$$

Along $x(t)=R(x+tw)/\|x+tw\|$, differentiation gives

$$
\begin{aligned}
\left.\frac{d^2}{dt^2}H(x(t))\right|_{t=0}
&=4\left(q_\lambda(w)-\frac{\lambda\cdot q(x)}{R^2}\|w\|^2\right)\\
&\le4\|\lambda\|\|w\|^2
             \left(-\delta+\frac{\|c\|}{R^2}\right)<0.
\end{aligned}
\tag{147.8}
$$

Here $\lambda\cdot q(x)=\|\lambda\|^2+\lambda\cdot c\ge-\|\lambda\|\|c\|$. This contradicts minimality and proves (147.6). The argument uses a finite sphere to find an actual vector; it asserts no compactness of the full bounded-function space.

Now set $T_jx=B_j(x,\cdot)\in V_N^*$, using the algebraic dual. Every nonzero linear combination of these three operators has infinite rank: a negative definite subspace of dimension $k$ for its polar form forces rank at least $k$. Thus they span a three-dimensional operator space with no nonzero finite-rank member. The contrapositive of Meshulam–Šemrl, *Locally linearly dependent operators*, Theorem 2.2, with real field, $n=3$ and $c=1$, gives some $x\in V_N$ for which the three functionals $B_j(x,\cdot)$ are independent. This theorem applies to arbitrary vector spaces, including $V_N$ and its algebraic dual. Choose $h_k\in V_N$ with $B_j(x,h_k)=\delta_{jk}$.

On the finite-codimensional subspace

$$
W=\{z\in V_N:B_j(x,z)=0,\ B_j(z,h_k)=0
                         \text{ for all }j,k\},
\tag{147.9}
$$

apply (147.6) to find $z$ with $q(z)=c-q(x)$. Then $w=x+z$ satisfies (147.5). The cited primary result is R. Meshulam and P. Šemrl, *Pacific Journal of Mathematics* **203** (2002), 441–459, [doi:10.2140/pjm.2002.203.441](https://doi.org/10.2140/pjm.2002.203.441), Theorem 2.2 and its proof, pp. 444–445. Its local-dependence alternative is the known intermediate; the source-specific inputs to this correction are the original pencils and their angular tests. $\square$

**Lemma 147.4 (an even cubic differential surviving separated angular correction).** There exist a bounded real odd function $v_0$ with finitely many angular frequencies $|n|\le L$, a positive even integer $s\le2L$, and a bounded real pure-frequency-$s$ function $h_*$, such that

$$
\int h_*H_{v_0}\,dm\ne0,\qquad
H_v:=gP(vPv)+(Pv)P(gv)+P(vP(gv)).
\tag{147.10}
$$

Moreover, if $N>3L$ is odd and $w\in V_N$, then

$$
\int h_*H_{v_0+w}\,dm=\int h_*H_{v_0}\,dm.
\tag{147.11}
$$

*Proof.* The original local smoothing and kernel construction (120.7)–(120.11) give the continuous symmetric kernel $p_d(x,y)$ on the punctured product, its rotation equivariance, and strict positive definiteness on every finite set of distinct punctured points. Choose $x_0\in\Omega$ with $g(x_0)=g_0>0$ and put $R=R_\pi$,

$$
k(\alpha)=p_d(x_0,R_\alpha x_0),\qquad
\Delta=k(0)-k(\pi)>0.
\tag{147.12}
$$

The strict inequality follows by applying finite Gram strictness to $x_0,Rx_0$ and coefficients $(1,-1)$. Symmetry and equivariance make $k$ a real even continuous positive-definite function on the circle. Its Fourier coefficients satisfy

$$
k(\alpha)=\sum_{n\in\mathbb Z}a_ne^{in\alpha},\qquad
a_n=a_{-n}\ge0,\qquad \sum_na_n=k(0).
\tag{147.13}
$$

For completeness, nonnegativity of each coefficient follows by integrating the finite Gram inequalities against a character, first as Riemann sums and then by continuity. The nonnegative Fejér kernels have mass one and concentrate at zero, so their convolution with continuous $k$ converges uniformly to $k$. At zero their values are the sums $\sum_{|n|\le M}(1-|n|/(M+1))a_n$. Monotone convergence gives $\sum a_n=k(0)$, absolute convergence follows, and the Fourier representation is (147.13). Since $\Delta>0$, at least one positive odd $\ell$ has $a_\ell>0$.

Let $A_\varepsilon$ be shrinking coordinate balls about $x_0$, with positive mass, disjoint from $RA_\varepsilon$, and with compact closure in $\Omega$. Define the bounded odd function

$$
v_\varepsilon=
       \frac{\mathbf1_{A_\varepsilon}-\mathbf1_{RA_\varepsilon}}
            {m(A_\varepsilon)}.
\tag{147.14}
$$

The local joint continuity of the original kernel, continuity of $g$, and rotation invariance give, uniformly for $\alpha$ on the circle,

$$
H_{v_\varepsilon}(R_\alpha x_0)\longrightarrow
2g_0\Delta[k(\alpha)+k(\alpha+\pi)]
       +g_0[k(\alpha)-k(\alpha+\pi)]^2.
\tag{147.15}
$$

Indeed $Pv_\varepsilon$ tends uniformly on the compact orbit and on the two shrinking supports to the corresponding difference of kernel values; $P(gv_\varepsilon)$ tends to $g_0$ times that difference. The signed measures $v_\varepsilon Pv_\varepsilon\,m$ and $v_\varepsilon P(gv_\varepsilon)\,m$ tend, respectively, to $\Delta(\delta_{x_0}+\delta_{Rx_0})$ and $g_0\Delta(\delta_{x_0}+\delta_{Rx_0})$. Inserting these limits into the three terms of (147.10) proves (147.15), with uniformity supplied by continuity on compact neighborhoods. These are spatial tests for the same full semigroup, not a replacement for its source law.

All Fourier coefficients of $k(\alpha)+k(\alpha+\pi)$ are nonnegative, and those of $k(\alpha)-k(\alpha+\pi)$ are $2a_n$ at odd $n$ and zero otherwise. Consequently the coefficient at $s=2\ell$ of the right side of (147.15) is at least $4g_0a_\ell^2>0$. Choose one sufficiently small, fixed $\varepsilon$ whose left side has nonzero coefficient at this $s$.

Apply the real angular Fejér means to this fixed $v_\varepsilon$. They remain odd, are uniformly bounded, have finite angular bands, and converge in $L^2(m)$. If $v_n\to v$ in $L^2(m)$ with a uniform bound, the Markov contractions give

$$
v_nPv_n\to vPv,\qquad
v_nP(gv_n)\to vP(gv)\quad\hbox{in }L^2(m).
\tag{147.16}
$$

For example, split the first difference as $v_n(Pv_n-Pv)+(v_n-v)Pv$; both terms converge in $L^2$, since $Pv$ is bounded. The second uses the bounded original $g$. The local $L^2$-to-continuous bound (120.8) then gives uniform convergence of $H_{v_n}$ on the orbit. Hence one finite-band odd mean $v_0$ retains its nonzero frequency-$s$ coefficient. Enlarge its integer band bound $L$ if needed so $s\le2L$.

Every $H_v$ is smooth on $\Omega$: each smoothed factor has this property by (120.7)–(120.8), and $g$ is smooth there. Its frequency-$s$ coefficient is therefore continuous in the quotient coordinates $(r,z,\xi)$. On a sufficiently small compact quotient neighborhood of the base of $x_0$, choose a fixed real sine/cosine phase for which that coefficient has a strictly nonzero real pairing. Multiplying that sine/cosine by a nonnegative smooth quotient bump produces bounded pure-frequency-$s$ $h_*$ with (147.10), using the positive invariant density $rh^2$ in (120.12). Since $s$ is positive and even, $h_*$ is even and has zero pairing with each rotation-invariant $g_j$.

Finally expand $H_{v_0+w}$ into its two quadratic pure terms and its mixed terms. The term $H_w$ is invariant under $R_{2\pi/N}$, so has only frequencies divisible by $N$. Each mixed term has frequencies congruent modulo $N$ to one of the odd frequencies $n$ of $v_0$, with $|n|\le L$. It cannot have frequency $s$: otherwise $s-n$ is divisible by $N$, whereas $|s-n|\le3L<N$ and $s\ne n$ by parity. Also $0<s<N$, so $H_w$ has no frequency $s$. This calculation is valid for arbitrary bounded $w\in V_N$, without a finite-band assumption on $w$: multiplication by each of the finitely many characters of $v_0$ shifts its closed angular sectors, and $P$ and multiplication by invariant $g$ preserve them. Projection onto frequency $s$ proves (147.11). $\square$

**Theorem 147.5 (a regular interior zero for every original tuple).** For every original $\theta\in\Theta$, there are a Borel function $u_*:G\to(0,1)$, a number $\epsilon>0$, and seven bounded real Borel directions $e_1,\ldots,e_7$ such that

$$
\epsilon\le u_*\le1-\epsilon,\qquad
\mathcal F(u_*)=0,\qquad
A:=\left.D_t\mathcal F\left(u_*+\sum_{j=1}^7t_je_j\right)\right|_{t=0}
\text{ is invertible}.
\tag{147.17}
$$

*Proof.* Choose $v_0,L,s,h_*$ from Lemma 147.4 and an odd $N>3L$. Apply Lemma 147.3 to $c=-q(v_0)$, obtaining $w,h_1,h_2,h_3\in V_N$. Distinct positive angular frequencies have zero polar cross-pairings, as in Corollary 133.3, since their weights are invariant and $P$ preserves sectors. Thus $v=v_0+w$ satisfies

$$
q(v)=0,\qquad B_j(v,h_k)=\delta_{jk}.
\tag{147.18}
$$

The function $v$ is odd. Invariance of the three source marginals gives $L(v)=0$. Rotation invariance of the original trilinear form gives $\tau(v)=\tau(-v)=-\tau(v)$, so $\tau(v)=0$. Choose a sufficiently small $\lambda>0$ and put $u_*=p+\lambda v$, giving the first two assertions of (147.17). Bounded Borel representatives, repaired on one common null set, give the pointwise interior bounds on all of $G$.

Self-adjointness of $P$ and differentiation of the original trilinear form give

$$
D\tau(v)[h]=\mathcal C(h,v,v)+\mathcal C(v,h,v)+\mathcal C(v,v,h)
            =\int hH_v\,dm.
\tag{147.19}
$$

For odd $v$, the density $H_v$ is even. On the three odd directions $h_k$, the linear and cubic differentials therefore vanish, while the pair differentials at $\lambda v$ are the invertible matrix $2\lambda I_3$ by (147.18). On even directions all pair differentials vanish. Use the three invariant even directions $g_0,g_1,g_2$ and the even direction $h_*$. Their linear differential has the positive-definite three-by-three Gram matrix of Lemma 147.2, and its $h_*$ column is zero. Its cubic differential in that last column is

$$
\lambda^2\int h_*H_v\,dm
 =\lambda^2\int h_*H_{v_0}\,dm\ne0.
\tag{147.20}
$$

In the ordered directions $(g_0,g_1,g_2,h_*,h_1,h_2,h_3)$ and with the pair rows placed last, the full differential is block triangular with invertible diagonal blocks. This proves (147.17). Every direction is a function on the original $G$; no additional state, randomness or operation has been added. $\square$

## 148. Exact attainment by one actual common Borel indicator

**Theorem 148.1 (original universal exact binary three-time law).** Under precisely the original suppliers retained in Definition 147.1, for every $\theta\in\Theta$ there exists a single whole-$G$ Borel set $B$ such that, setting $u_1=\mathbf1_B$ and $u_0=1-\mathbf1_B$,

$$
\mathcal C(u_i,u_j,u_k)
 =p^{i+j+k}(1-p)^{3-i-j-k}
\quad\text{for every }(i,j,k)\in\{0,1\}^3,
\qquad p=\frac14.
\tag{148.1}
$$

This uses the actual full $K$, source at $e$, original epochs $2d,3d,4d$, and the actual terminal $Pu_k$. The set $B$ is the same at all three epochs.

*Proof.* Take the regular interior zero and the seven directions of Theorem 147.5. For $t\in\mathbb R^7$ near zero put

$$
u_t=u_*+\sum_{j=1}^7t_je_j,\qquad F(t)=\mathcal F(u_t).
\tag{148.2}
$$

This is a polynomial map of degree at most three, with $F(0)=0$ and derivative $A$ invertible. Choose a positive radius $r$ sufficiently small that every $u_t$, $\|t\|\le r$, takes values in $[\epsilon/2,1-\epsilon/2]$ and

$$
\sup_{\|t\|\le r}\|t-A^{-1}F(t)\|<r/3.
\tag{148.3}
$$

The latter follows directly from $F(t)=At+O(\|t\|^2)$ and needs no global regularity or connectedness assertion for a moment fiber.

Choose increasing finite Borel partitions $\mathcal P_n$ whose generated sigma-algebra is the Borel sigma-algebra of $G$. For example, finite partitions generated by the first $n$ members of a countable coordinate basis have this property. On every positive-mass cell $E$ of each partition fix a nested Borel family $E(s)$, $0\le s\le m(E)$, with $m(E(s))=s$, $E(0)=\varnothing$ and $E(m(E))=E$. Such a family exists here without adding any random coordinate: the first original coordinate $x$ has $m$-null level sets, because $m\ll\mu$. Hence $a\mapsto m(E\cap\{x\le a\})$ is continuous, has limits zero and $m(E)$ at the two infinities, and its quantile thresholds give the required nested family for all intermediate $s$. Assign zero-mass cells the empty selected subset.

For each $n$ and parameter $t$ define the actual whole-$G$ Borel set

$$
B_n(t)=\bigcup_{E\in\mathcal P_n}
             E\!\left(\int_Eu_t\,dm\right).
\tag{148.4}
$$

Every cell mass of $\mathbf1_{B_n(t)}$ equals that of $u_t$. Nestedness gives the exact continuity estimate

$$
\begin{aligned}
m(B_n(t)\mathbin\triangle B_n(t'))
 &=\sum_{E\in\mathcal P_n}\left|\int_E(u_t-u_{t'})\,dm\right|\\
 &\le\|u_t-u_{t'}\|_{L^1(m)}.
\end{aligned}
\tag{148.5}
$$

Thus this is a continuous family in the metric of symmetric difference, for each fixed finite partition. It is a deterministic family of subsets of the original state space; the quantile thresholds are used to choose a subset of each cell, not to supply a stochastic readout.

Use the actual joint density of §§123 and 143,

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3)
\in L^1(m^{\otimes3}),\qquad \int W\,dm^{\otimes3}=1.
\tag{148.6}
$$

Let $W_n$ be its conditional expectation on $\mathcal P_n^{\otimes3}$. Then $\|W-W_n\|_1\to0$. One can see this directly from density of the union of the finite-partition simple functions in $L^1(m^{\otimes3})$ and contractivity of conditional expectation. This union generates the product Borel sigma-algebra.

Each of the seven coordinates in (147.2) is an integral against $W$ of a product of a selected nonempty subset of the three centered factors $u(x_j)-p$. For $W_n$, the integral factors on every product cell. Equality of the one-cell masses in (148.4) therefore gives exact equality between the seven coordinates computed with $u_t$ and with $\mathbf1_{B_n(t)}$, when $W$ is replaced by $W_n$. All the centered factors have absolute value at most one. Consequently, with $F_n(t)=\mathcal F(\mathbf1_{B_n(t)})$,

$$
\sup_{\|t\|\le r}\|F_n(t)-F(t)\|
 \le2\sqrt7\,\|W-W_n\|_1\longrightarrow0.
\tag{148.7}
$$

This is uniform approximation of the entire parameter family, not a claim that a limiting stochastic function is an indicator.

The maps $F_n$ are continuous. To check this in the original law, let $a,a':G\to[0,1]$ be two indicators or two bounded stochastic functions. Telescoping any centered product of at most three factors gives a sum of at most three terms bounded by $|a-a'|(x_j)$. The three marginal densities of $W$ are precisely $g_j$, so each coordinate changes by at most

$$
3\max_{0\le j\le2}\|g_j\|_\infty\,\|a-a'\|_1.
\tag{148.8}
$$

Equations (148.5) and (148.8) prove continuity on the closed parameter ball, using the original global bounds of §133.

Choose one sufficiently large, finite $n$ so that $\|A^{-1}\|\sup_{\|t\|\le r}\|F_n(t)-F(t)\|<r/3$. Equations (148.3) and (148.7) imply that the continuous map

$$
\Psi_n(t)=t-A^{-1}F_n(t)
\tag{148.9}
$$

sends the closed radius-$r$ ball in $\mathbb R^7$ into its radius-$2r/3$ ball. Brouwer's fixed-point theorem supplies $t_n$ with $\Psi_n(t_n)=t_n$, and therefore

$$
\mathcal F(\mathbf1_{B_n(t_n)})=0.
\tag{148.10}
$$

The primary fixed-point input is L. E. J. Brouwer, “Über Abbildung von Mannigfaltigkeiten,” *Mathematische Annalen* **71** (1911), 97–115, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), Satz 4, p. 115. Its finite-dimensional closed-ball hypothesis is exactly the domain in (148.9). No fixed point of a noncompact function-space map is invoked.

Set $B=B_n(t_n)$ for this one finite $n$. For $v=\mathbf1_B-p$, (148.10) says that each of the seven nonempty centered joint moments of $v(Z_{2d}),v(Z_{3d}),v(Z_{4d})$ is zero. Expanding each product of $u_1=p+v$ and $u_0=(1-p)-v$ leaves only its constant term, which is (148.1). This proves every ordered triple simultaneously. In particular the cubic equation is fulfilled for this actual set, rather than inferred from opposite signs or a vanishing residual infimum. $\square$

**Proposition 148.2 (source and realization boundary of the binary assertion).** Theorem 148.1 is a conditional mathematical consequence of the same complete original suppliers as §§134–144. It imposes no additional connectedness, compactness, regularity, finite-witness or indicator-attainment premise. The one set in its conclusion is Borel on the original $G$, and its complement completes the whole-space binary partition. It uses neither an invariant initial law nor a killed source, new seed, controller, memory, postselection, changed clock or separate epoch partitions. The result supplies only this binary readout law and no native physical correspondence.

*Proof.* The marginal independence uses the actual propagation, continuous entrance and null source mass, not a stationary distribution. The high-frequency correction uses §133 for the original full semigroup. The cubic differential uses the already supplied punctured kernel and its strict finite Gram property from §120. The finite ball and finite partition in (148.3)–(148.10) are constructed within the proof; they are not assumptions about the original infinite-dimensional fiber. The final readout is exactly the indicator of (148.4) for one fixed parameter. Since the actual joint law has density (148.6), arbitrary repairs on $m$-null sets do not change its coefficients. The source, evolution and physical identification obligations of §§115–117 remain separate. $\square$

## 149. The binary coarsening and the exact four-label refinement still required

**Proposition 149.1 (coarsening and the remaining coordinate equations).** Retain the original label set $\mathcal L=\{0,1,3,B\}$, tuple $f$, and target $F_{64}(\theta)$ of (144.4). Define $\pi:\mathcal L\to\{0,1\}$ by $\pi(B)=1$ and $\pi(0)=\pi(1)=\pi(3)=0$. Then $F_{64}(\theta)$ implies the binary conclusion (148.1), with its set equal to the actual partition cell $D_B$.

For any fixed B8 witness $B$, extending that witness to $F_{64}(\theta)$ is equivalent to finding one whole-$G$ Borel partition with $D_B=B$ and $D_0,D_1,D_3$ partitioning $G\setminus B$, satisfying the following 56 coefficient equations. For $\varepsilon\in\{0,1\}^3$ put

$$
I_\varepsilon=\{(y,z,w)\in\mathcal L^3:
                 (\pi(y),\pi(z),\pi(w))=\varepsilon\},
\tag{149.1}
$$

and let $a_\varepsilon\in I_\varepsilon$ be the triple using $B$ in each coordinate equal to one and $0$ in each coordinate equal to zero. The required equations are

$$
\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
   =\mathcal C(f_y,f_z,f_w)
\quad\text{for every }(y,z,w)\in
     \bigcup_{\varepsilon\in\{0,1\}^3}
                 (I_\varepsilon\setminus\{a_\varepsilon\}).
\tag{149.2}
$$

All terminal factors in (149.2) are their own actual $P\mathbf1_{D_w}$. The number 56 counts independent ambient coordinate conditions after the eight disjoint block sums have been fixed; it asserts neither independence nor feasibility of the nonlinear constraints on the three refining sets.

*Proof.* By (134.7), $f_B=p$ and $f_0+f_1+f_3=1-p$ pointwise. Multilinearity therefore gives

$$
\sum_{(y,z,w)\in I_\varepsilon}\mathcal C(f_y,f_z,f_w)
 =p^{\varepsilon_1+\varepsilon_2+\varepsilon_3}
       (1-p)^{3-\varepsilon_1-\varepsilon_2-\varepsilon_3}.
\tag{149.3}
$$

For a partition, the same summation replaces the three grouped indicators by $\mathbf1_{D_B}$ or $1-\mathbf1_{D_B}$. This proves the forward coarsening implication. For a refinement of a fixed B8 witness, its block sums already equal (149.3). In each block, equality of all coordinates other than $a_\varepsilon$ then forces equality at $a_\varepsilon$ by subtraction from the known block sum. Conversely full equality supplies (149.2). Finally,

$$
\sum_{\varepsilon\in\{0,1\}^3}(|I_\varepsilon|-1)
 =\sum_\varepsilon(3^{\#\{j:\varepsilon_j=0\}}-1)=64-8=56.
\tag{149.4}
$$

The omitted coordinate in each block is determined by its sum, so these are independent coordinate conditions in the ambient affine space with those eight sums prescribed. Their pullback to actual common partitions remains the exact refinement problem. In particular Theorem 148.1 proves $\forall\theta\in\Theta\ B_8(\theta)$ but proves neither that every B8 witness is refinable nor that some B8 witness is refinable for every $\theta$. The latter existential refinement, equivalently universal $F_{64}$, remains unresolved. $\square$

**Definition 149.2 (mathematical attribution and scope).** The source-specific composition in §§147–149 is `repo-derived`: it combines the original all-frequency marginal pencils with a protected cubic differential and a finite-dimensional fixed-point construction of an actual common indicator. Spectral calculus, polar forms, finite-dimensional minimization, nonnegative angular Fejér averaging, conditional expectation and Brouwer's fixed-point theorem are mature intermediates. The consumed local-dependence theorem is attributed in Lemma 147.3 and the fixed-point theorem in Theorem 148.1; the other elementary intermediate calculations are given in their proofs. No priority claim is attached to this composition.

The exact finite linear subdivisions of A. Dvoretzky, A. Wald and J. Wolfowitz, “Relations among certain ranges of vector measures,” *Pacific Journal of Mathematics* **1** (1951), 59–74, [doi:10.2140/pjm.1951.1.59](https://doi.org/10.2140/pjm.1951.1.59), Theorem 4 and Lemma 2, pp. 66–67, remain the known linear suppliers used in §§142–143. Their linear purification statement alone does not imply the cubic equation. Theorem 148.1 instead obtains exactness from the regular zero and the continuous finite-partition family. The common exact-rank-two sequence and all-64 density of Theorem 143.2 and the noncompactness distinction in §144 are retained directly; no limit of that sequence is asserted to be a deterministic witness. The original universal four-label assertion retains precisely the common-refinement obligations of Proposition 149.1.

## 追加锚（本行以下为增补区）

## 150. One original common partition for all three pair laws and finite moments

**Definition 150.1 (the original three-pair fiber).** Retain the complete original endpoint, source, analytic and readout telescope of Definitions 134.1 and 135.1, including every inherited hypothesis and supplier of Appendix II §§115–117, 123–125 and 133. Thus $\Theta$ contains every original tuple $\theta=(a,\eta,d,b)$ with finite $a,\eta,d>0$ and every permitted everywhere Borel representative $b$ of $g_d$ satisfying $0<b\le M$. The group and raw Haar measure remain

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad
(x,y,z,\zeta)(x',y',z',\zeta')
 =(x+x',y+y',z+z',\zeta+\zeta'+xy'),\\
e=(0,0,0,0),\qquad d\mu=dx\,dy\,dz\,d\zeta.
\end{gathered}
$$

Keep the unit-source field $L\Gamma=\delta_e$, the coefficient-one $w_*$, the coefficient-positive normalized $h=w_*/\|w_*\|_{L^2(\mu)}$, and precisely the actual full self-adjoint endpoint with selector $A_{\rm src}=\rho C_{\rm src}$. In particular

$$
\begin{gathered}
m=h^2\mu,\qquad K=U_h^{-1}H_{\rm end}U_h,\qquad T_s=e^{-sK},\\
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\qquad
P=T_d,\quad g=g_{2d},\quad g_{s+r}=T_rg_s,\\
M=1+\|g_d\|_\infty,\qquad c=(4M)^{-1},\qquad
f_3=cb,\quad f_B=\tfrac14,\quad f_0=f_1=(\tfrac34-cb)/2.
\end{gathered}
\tag{150.1}
$$

The conservative process starts at the original $e$ at time zero, and the three epochs are $2d,3d,4d$. The stochastic comparison uses this same $f$ at all epochs, with fresh read noises conditionally independent given the original path. For bounded real functions define the ordered pair forms

$$
\begin{aligned}
Q_{12}(u,v)&=\mathcal C(u,v,1)=\int_G guPv\,dm,\\
Q_{13}(u,v)&=\mathcal C(u,1,v)=\int_G guP^2v\,dm,\\
Q_{23}(u,v)&=\mathcal C(1,u,v)=\int_G(Pg)uPv\,dm.
\end{aligned}
\tag{150.2}
$$

The last equality uses self-adjointness and the original source propagation, so the three forms are exactly the $(2d,3d)$, $(2d,4d)$ and $(3d,4d)$ marginals of the same original law. Write $\mathcal R=\{12,13,23\}$, $\mathcal L=\{0,1,3,B\}$ and $q_r(v)=Q_r(v,v)$. These are the three existing forms in (147.2).

**Theorem 150.2 (simultaneous original pair laws with arbitrary finite moments).** Under exactly the retained original suppliers of Definition 150.1, for every $\theta\in\Theta$ and every finite $\Psi\subset L^1(G,m;\mathbb C)$ there exists one pointwise Borel partition $D=(D_y)_{y\in\mathcal L}$ of the whole original $G$ such that

$$
\begin{gathered}
Q_r(\mathbf1_{D_y},\mathbf1_{D_z})=Q_r(f_y,f_z)
\quad(r\in\mathcal R,\ y,z\in\mathcal L),\\
\int_G\psi\mathbf1_{D_y}\,dm=\int_G\psi f_y\,dm
\quad(\psi\in\Psi,\ y\in\mathcal L).
\end{gathered}
\tag{150.3}
$$

In particular this same partition belongs to $\mathscr D_{12}(\theta)$. The quantifier order is $\forall\theta\ \forall\Psi\ \exists D$; the three pairs and all finite moments use that single $D$.

*Proof.* Replace the finite complex moment list by its real and imaginary parts, obtaining a finite real list $\Psi_{\mathbb R}$. Work first with real $L^\infty(m)$ classes. We verify the entire three-form pencil on every possible overlap, before choosing any extremal tuple.

For $\lambda=(\lambda_{12},\lambda_{13},\lambda_{23})\ne0$ and a Borel $E$ with $m(E)>0$, put $\mathcal V_E=\{v\in L^\infty(m;\mathbb R):v=0\text{ a.e. off }E\}$. If $(\lambda_{12},\lambda_{23})\ne(0,0)$, use Corollary 133.3 with original source time $t=2d$, gap $d$, and

$$
(\alpha,\beta,\gamma)
 =(\lambda_{12},\lambda_{23},\lambda_{13}).
\tag{150.4}
$$

Its pencil (133.17) is exactly

$$
q_\lambda(v)=\sum_{r\in\mathcal R}\lambda_rq_r(v)
 =\int_G(\lambda_{12}g+\lambda_{23}Pg)vPv\,dm
   +\lambda_{13}\int_GgvP^2v\,dm.
\tag{150.5}
$$

All hypotheses are supplied for this actual source: Theorem 133.2 gives the global essential bounds, Markov contraction gives the bound for $Pg$, and the rotation, analytic regularity and nonconstancy of $\alpha g+\beta Pg$ are the original suppliers used in Corollary 129.3. Localization (127.4), as consumed in (133.18), gives infinite negative index on $\mathcal V_E$ for arbitrary $E$, without requiring $E$ to be rotation invariant.

If $(\lambda_{12},\lambda_{23})=(0,0)$, then $\lambda_{13}\ne0$. Apply Corollary 133.3 with the same source time $2d$, semigroup gap $2d$, and coefficients $(\lambda_{13},0,0)$. Its form is exactly $\lambda_{13}\int gvT_{2d}v\,dm=\lambda_{13}q_{13}(v)$, again with infinite negative index on $\mathcal V_E$. This is an index statement about the existing total-gap pair form, with $T_{2d}=P^2$; the observation epochs in (150.2) remain unchanged.

Consequently every nonzero $q_\lambda$ has infinite negative index on each $\mathcal V_E$. This property survives any finite family of homogeneous linear constraints: intersect an arbitrarily large negative-definite subspace with their common kernel and apply rank–nullity. It also implies that the three restricted forms are linearly independent, since a zero pencil cannot have negative index.

Let $\mathcal S$ be the weak-star compact simplex of Proposition 123.2 and define the single fiber

$$
\mathcal K=\left\{a\in\mathcal S:
\begin{array}{ll}
Q_r(a_y,a_z)=Q_r(f_y,f_z)&(r\in\mathcal R,\ y,z\in\mathcal L),\\
\int\psi a_y\,dm=\int\psi f_y\,dm
 &(\psi\in\Psi_{\mathbb R},\ y\in\mathcal L)
\end{array}\right\}.
\tag{150.6}
$$

It is nonempty because it contains $f$. It is compact: each ordered pair coordinate is a marginal sum of the continuous map $\Phi_3$ of Proposition 123.2, and each moment against an $L^1(m)$ function is weak-star continuous. No convexity of $\mathcal K$ is needed.

Use the continuous strictly convex separating functional $J$ of (122.30), with a countable separating family in the real $L^1(m)$ unit ball, and choose a maximizer $a$ on $\mathcal K$. Choose pointwise Borel simplex representatives as in Proposition 123.2. If $a$ is not an indicator tuple almost everywhere, finiteness of the label set gives distinct $i,j$ and $\kappa>0$ for which

$$
E=\{a_i\ge\kappa,\ a_j\ge\kappa\},\qquad m(E)>0.
\tag{150.7}
$$

Inside $\mathcal V_E$ impose the finite linear constraints

$$
\begin{gathered}
Q_r(v,a_z)=Q_r(a_z,v)=0
\quad(r\in\mathcal R,\ z\in\mathcal L),\\
\int_G\psi v\,dm=0\quad(\psi\in\Psi_{\mathbb R}),
\end{gathered}
\tag{150.8}
$$

and call their common kernel $V$. There are at most $24+|\Psi_{\mathbb R}|$ real constraints. They are defined on bounded classes; for example the two densities for $Q_{12}$ are $gPa_z$ and $P(ga_z)$, and the corresponding densities for the other two forms are obtained using $P^2$ or $Pg$. All are in $L^1(m)$ by the original Markov contractions and source integrability. Each nonzero pencil still has infinite negative index on $V$, and the three forms remain independent there. Apply the already proved common-zero-plane assertion of Lemma 125.3 to these three forms on $V$. In particular it supplies a nonzero $v\in V$ with

$$
q_{12}(v)=q_{13}(v)=q_{23}(v)=0.
\tag{150.9}
$$

Only that quadratic assertion of the lemma is used. The individual weighted joint forms of (125.3) and their all-pencil premise are not invoked.

Choose a bounded Borel representative of $v$ vanishing pointwise off $E$, and a number $s>0$ with $s\|v\|_\infty\le\kappa$. Put $\sigma_i=1$, $\sigma_j=-1$ and $\sigma_y=0$ otherwise, and set $a_y^\pm=a_y\pm s\sigma_yv$. As in (122.28), these are distinct pointwise Borel simplex tuples, with midpoint $a$. For every ordered pair, the exact expansion is

$$
\begin{aligned}
Q_r(a_y^\pm,a_z^\pm)-Q_r(a_y,a_z)
={}&\pm s\{\sigma_yQ_r(v,a_z)+\sigma_zQ_r(a_y,v)\}\\
 &+s^2\sigma_y\sigma_zq_r(v)=0.
\end{aligned}
\tag{150.10}
$$

Their prescribed moments are unchanged by (150.8). Thus $a^+,a^-\in\mathcal K$. Strict convexity gives $J(a)<(J(a^+)+J(a^-))/2$, contradicting maximality. It follows that $a$ is an indicator tuple almost everywhere. The contradiction uses perturbations inside this one common fiber, rather than separately chosen pair witnesses.

On the Borel null set where the four chosen representatives do not give exactly one indicator equal to one, assign the label $B$. This produces a pointwise Borel partition of all of $G$. Each positive-time marginal is absolutely continuous with respect to $m$, and the pair laws are marginals of the actual density $W$ in (123.3). Hence this common null-set repair preserves all pair coordinates, as well as every $L^1(m)$ moment, proving (150.3). The argument depends on $b$ only through its permitted $m$-class and its everywhere simplex bounds, so it applies to every representative allowed in $\Theta$.

Finally the row and column sums of the preserved pair laws give, respectively,

$$
Q_{12}(u,1)=\int gu\,dm,\qquad
Q_{12}(1,u)=\int(Pg)u\,dm,\qquad
Q_{23}(1,u)=\int(P^2g)u\,dm.
\tag{150.11}
$$

The original source identities identify these densities with $g_{2d},g_{3d},g_{4d}$. Summing (150.3) over the other label therefore gives all twelve marginal equalities defining $\mathscr D_{12}(\theta)$ for this same $D$. $\square$

**Proposition 150.3 (the third-order residual after the three pair laws).** For any common partition $D$ satisfying the pair equalities in (150.3), define

$$
\Delta_{yzw}=\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
               -\mathcal C(f_y,f_z,f_w).
\tag{150.12}
$$

Full equality of all 64 coordinates is equivalent to the 27 equations $\Delta_{ijk}=0$ for $i,j,k\in\{0,1,3\}$. These are 27 free coordinates of the ambient linear residual space with all pair marginals zero; no independence or feasibility assertion for their nonlinear pullback to partitions is implied.

*Proof.* Summing $\Delta$ in any one index gives the difference of the corresponding preserved pair laws, and is therefore zero. Let $e_y$ be the standard basis of $\mathbb R^{\mathcal L}$ and $H_0=\{x:\sum_yx_y=0\}$. The tensors with all three pair sums zero are exactly $H_0^{\otimes3}$: split $\mathbb R^{\mathcal L}=H_0\oplus\mathbb Re_B$ and apply the three index-sum maps to the resulting tensor decomposition. The nine one-time and 27 two-time coordinates, together with normalization, account for the complementary 37 ambient coordinates. The vectors $e_i-e_B$, $i\in\{0,1,3\}$, form a basis of $H_0$, and

$$
\Delta=\sum_{i,j,k\in\{0,1,3\}}
 \Delta_{ijk}(e_i-e_B)\otimes(e_j-e_B)\otimes(e_k-e_B).
\tag{150.13}
$$

Equivalently, replace each occurrence of $\mathbf1_{D_B}$ by $1-\mathbf1_{D_0}-\mathbf1_{D_1}-\mathbf1_{D_3}$ and use the already fixed lower-order sums. This proves the equivalence and the ambient count $\dim H_0^{\otimes3}=3^3=27$. Theorem 150.2 asserts none of these additional triple equations. Its terminal factors in (150.12) remain the actual $P\mathbf1_{D_w}$; no identification with $Pf_w$ is made. Its partition is not required to satisfy B8, to refine a supplied B8 witness, or to have rank-two $A^D$. $\square$

**Definition 150.4 (attribution and mathematical boundary).** The source-specific simultaneous attainment in Theorem 150.2 is `repo-derived`. It reuses the original scalar marginal pencils and their arbitrary-set localization from Appendix II §§127, 129 and 133, the finite-dimensional quadratic-zero argument of Lemma 125.3, the compactness of Proposition 123.2 and the separating extremum argument (122.28)–(122.30). The new conclusion places all three ordered pair laws and the arbitrary finite moments in one original-source partition. No separate theorem or priority claim is made for those intermediates. Analytic uniqueness in the localization step has the source cited in Proposition 127.2: B. S. Mityagin, *The zero set of a real analytic function*, [arXiv:1512.07276v1](https://arxiv.org/abs/1512.07276v1), Proposition 0.

The known finite linear subdivision theorem of A. Dvoretzky, A. Wald and J. Wolfowitz, *Relations among certain ranges of vector measures*, Pacific Journal of Mathematics **1** (1951), 59–74, [doi:10.2140/pjm.1951.1.59](https://doi.org/10.2140/pjm.1951.1.59), Theorem 4 and Lemma 2, pp. 66–67, supplies the linear results already used in §§135 and 142–143. It is not used to identify the quadratic common fiber (150.6) with a linear vector-measure range. The three-pair result retains exactly the full original suppliers; it adds no joint-feasibility, compactness of the partition class or deterministic-limit premise. It asserts no new third-order equation, full $F_{64}$ attainment, source realization or physical correspondence. The original endpoint, source, measure, clock and state space are unchanged throughout.

## 追加锚（本行以下为增补区）

## 151. A common refinement paying the complete two-B layer

**Theorem 151.1 (source-specific B8 refinement with all two-B coefficients).** Retain precisely the original suppliers and quantifiers of Definitions 134.1, 135.1 and 147.1, including the complete endpoint, source and analytic telescope of Appendix II §§115–117, 123–125 and 133. Thus $a,\eta,d>0$ are arbitrary finite original parameters, and $b$ is any permitted everywhere Borel representative of $g_d$ satisfying $0<b\le M$. Keep the original product on $G=H^1\times\mathbb R$, raw Haar measure $\mu$, source $e$, unit-source field $L\Gamma=\delta_e$, coefficient-one $w_*$, positive normalized $h=w_*/\|w_*\|_{L^2(\mu)}$, actual full self-adjoint endpoint with selector $A_{\rm src}=\rho C_{\rm src}$, and $m=h^2\mu$. The full conservative $K$ retains its source coordinate and form domain $\mathscr V=\mathscr V_0\dotplus\mathbb C1$. Use $T_s=e^{-sK}$, $P=T_d$, the original source-start densities with $g_{s+r}=T_rg_s$, $g=g_{2d}$, and the original epochs $2d,3d,4d$. Put

$$
\begin{gathered}
M=1+\|g_d\|_\infty,\quad c=(4M)^{-1},\quad
p=f_B=\tfrac14,\quad r=f_3=cb,\\
f_S=f_0+f_1=\tfrac34-r,\qquad f_0=f_1=f_S/2,\qquad
\mathcal C(u,v,w)=\int_G guP(vPw)\,dm.
\end{gathered}
$$

The prescribed stochastic comparison uses this same $f$ at all three epochs, with fresh read noises conditionally independent given the original path. For every such $\theta=(a,\eta,d,b)$ there exists one pointwise Borel partition $D=(D_0,D_1,D_3,D_B)$ of the whole original $G$ such that $D\in\mathscr D_{12}(\theta)$, $D_B$ is an exact B8 witness in the sense of Theorem 148.1, and

$$
\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
=\mathcal C(f_y,f_z,f_w)
\quad\left(y,z,w\in\{0,1,3,B\},
\#\{j\in\{1,2,3\}:(y,z,w)_j=B\}\ge2\right).
$$

The quantifier order is $\forall\theta\ \exists D$, with the same $D$ for B8, all twelve source marginals and all ten displayed coefficients. Every terminal is its own actual $P\mathbf1_{D_w}$. The remaining 24 one-$B$ and 26 zero-$B$ equations of Proposition 149.1 remain unresolved. This partition need not be the partition of Theorem 150.2.

*Proof.* Work first with $m$-classes. Replace $r=cb$ by its rotation-invariant heat-density representative $r^0$, with $0<r^0\le1/4$ after a Borel null repair. This changes no target integral. Write $g_j=P^jg$ for $j=0,1,2$, $L(z)=(\langle g_0,z\rangle_m,\langle g_1,z\rangle_m,\langle g_2,z\rangle_m)$, and $t=L(r^0)$. For prospective $B$- and $3$-cell functions $s,z$, set

$$
H(s,z)=(\mathcal C(z,s,s),\mathcal C(s,z,s),\mathcal C(s,s,z)).
$$

The first two entries have actual terminal $Ps$, and the third has actual terminal $Pz$. For $s=p+\lambda v$, self-adjointness and $P1=1$ give

$$
H_i(s,z)=p^2\langle g_{i-1},z\rangle_m
+p\lambda\langle A_iv,z\rangle_m
+\lambda^2\langle J_i(v),z\rangle_m\quad(i=1,2,3),
\tag{151.1}
$$

where

$$
\begin{array}{lll}
A_1v=g(Pv+P^2v),&A_2v=(Pg)Pv+P(gv),&A_3v=P((Pg)v)+P^2(gv),\\
J_1(v)=gP(vPv),&J_2(v)=(Pv)P(gv),&J_3(v)=P(vP(gv)).
\end{array}
$$

Choose $v_0,L_0,h_*$ from Lemma 147.4 and odd $N>3L_0$. On the space $V_N$ of Lemma 147.3,

$$
\langle v,(\alpha_1A_1+\alpha_2A_2+\alpha_3A_3)v\rangle_m
=(\alpha_1+\alpha_2)q_1(v)+(\alpha_1+\alpha_3)q_2(v)
 +(\alpha_2+\alpha_3)q_3(v).
\tag{151.2}
$$

The coefficient map is invertible. By the all-pencil infinite-negative-index argument of Lemma 147.3, every nonzero pencil on the right has infinite-rank polar form. Hence no nonzero combination of the bounded-function operators $A_i:V_N\to V_N$ has finite rank: finite rank of such an operator would give finite rank of its symmetric pairing. Meshulam–Šemrl, Theorem 2.2, therefore supplies $x_A\in V_N$ for which the three $A_ix_A$ are independent. Lemma 147.3 also supplies $x_B\in V_N$ for which the three functionals $B_i(x_B,\cdot)$ are independent. Both independence requirements can be imposed on the same $x$: choose fixed dual test triples at $x_A$ and $x_B$, respectively, and evaluate their two determinants along $x(u)=(1-u)x_A+ux_B$. Each determinant is a polynomial in $u$, nonzero at its respective endpoint. Avoiding their finitely many roots gives $x$ satisfying both requirements. Choose $h_k\in V_N$ with $B_i(x,h_k)=\delta_{ik}$.

Choose odd dual tests for $A_ix$, truncate them by the invariant set $E_\varepsilon=\{r^0\ge\varepsilon\}$, and take $\varepsilon>0$ small enough to retain invertibility. Since $r^0>0$ almost everywhere and Lemma 147.2 gives a positive-definite full Gram matrix, take this $\varepsilon$ small enough also that $(\langle g_i,\mathbf1_{E_\varepsilon}g_j\rangle_m)_{0\le i,j\le2}$ is positive definite. Multiplying the truncated test triple by the inverse pairing matrix gives bounded odd $\eta_k\in V_N$, supported in $E_\varepsilon$, with $\langle A_ix,\eta_k\rangle_m=\delta_{ik}$. Impose on $z\in V_N$ the finite constraints

$$
B_i(x,z)=B_i(z,h_k)=\langle A_iz,\eta_k\rangle_m=0
\quad(1\le i,k\le3).
\tag{151.3}
$$

The finite-codimensional surjectivity (147.6) supplies such a $z$ with $q(z)=-q(v_0)-q(x)$. Frequency separation gives $B_i(v_0,x+z)=0$ for $i=1,2,3$. Thus $v=v_0+x+z$ satisfies $q(v)=0$, $B_i(v,h_k)=\delta_{ik}$, and $\langle A_iv,\eta_k\rangle_m=\delta_{ik}$. The latter uses both (151.3) and the separation of the frequencies of $A_iv_0$ from $V_N$. Lemma 147.4 gives $\langle h_*,H_v\rangle_m\ne0$. The proof of Theorem 147.5 now gives the regular binary zero $s_*=p+\lambda v$ for small $\lambda>0$, with the same seven binary directions.

Set $\omega=-p^{-1}\sum_i\langle J_i(v),r^0\rangle_m\eta_i$. It is odd, supported in $E_\varepsilon$, and $L(\omega)=0$. Equation (151.1), parity and the dual identities give, for $z_*=r^0+\lambda\omega$,

$$
L(z_*)=t,\qquad H(s_*,z_*)=p^2t.
\tag{151.4}
$$

The only possibly nonzero new order-$\lambda^2$ terms cancel as $p\langle A_iv,\omega\rangle_m+\langle J_i(v),r^0\rangle_m=0$; all other new terms vanish by parity. Shrink $\lambda$ so $s_*,z_*,1-s_*-z_*$ are nonnegative, with uniform slack wherever their respective directions are supported.

Put $\chi=\mathbf1_{E_\varepsilon}$ and $\rho_j=\chi g_j$, $j=0,1,2$. Use these and the $\eta_k$ as six $z$-directions. The derivative of $(L(z),H(s,z))$ in those directions has diagonal blocks $G_\chi=(\langle g_i,\chi g_j\rangle_m)$ and $p\lambda I_3$: the odd $\eta_k$ have zero $L$-pairing, and $J_i(v)$ is even. Together with the seven binary directions this makes the differential of the thirteen-coordinate map

$$
(s,z)\longmapsto(\mathcal F(s),L(z)-t,H(s,z)-p^2t)
\tag{151.5}
$$

invertible at $(s_*,z_*)$. Here invertibility means restriction to these thirteen directions; no differential on an infinite-dimensional space is inverted.

Take a small closed ball in these directions on which $s,z,1-s-z\in[0,1]$. As in Theorem 148.1, use increasing finite Borel partitions and, on each cell $E$, the original $x$-coordinate quantiles to choose a nested family $E(a)$ of mass $a$. Put $a=\int_Es\,dm$ and $b_E=\int_Ez\,dm$, select the $B$-slice $E(a)$ and the disjoint $3$-slice $E(a+b_E)\setminus E(a)$, and assign the remainder to $S$. These three-cell families match all cell masses and are continuous in symmetric difference; for the $3$-slice its change is bounded by $2|a-a'|+|b_E-b_E'|$. The actual joint density $W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3)$ lies in $L^1(m^{\otimes3})$. Its conditional expectations on the product partitions converge in $L^1$, so the rectangular-tensor argument of (148.7) gives uniform convergence of all thirteen actual coordinates to (151.5). Their continuity follows from the bounded original source marginals as in (148.8). The same finite-dimensional Brouwer argument as (148.3)–(148.10), using the invertible thirteen-dimensional differential, therefore produces one actual common Borel partition $(S,C,B)$ satisfying

$$
\mathcal F(\mathbf1_B)=0,\qquad
L(\mathbf1_C)=t,\qquad H(\mathbf1_B,\mathbf1_C)=p^2t.
\tag{151.6}
$$

Thus $B$ is B8, and $C$ has all three prescribed source marginals and all three ordered two-$B$ coefficients. The same remainder $S=G\setminus(B\cup C)$ has source masses $L(\mathbf1_S)=(1-p)\mathbf1-t$, where $\mathbf1=(1,1,1)$.

Finally split this same $S$ by Dvoretzky–Wald–Wolfowitz Theorem 4 with constant selector $1/2$, simultaneously for the six finite atomless measures, restricted to $S$, whose densities are

$$
g_0,g_1,g_2,\qquad
\ell_1=gP(\mathbf1_BP\mathbf1_B),\quad
\ell_2=P(g\mathbf1_B)P\mathbf1_B,\quad
\ell_3=P(\mathbf1_BP(g\mathbf1_B)).
$$

The last three densities represent the three linear functionals $z\mapsto H_i(\mathbf1_B,z)$, with their actual terminals retained. The two Borel pieces $D_0,D_1$ each receive half of all six measures. Set $D_3=C$ and $D_B=B$. Since $f_0=f_1=f_S/2$, all twelve source marginals are exact. B8 and (151.6) give

$$
H(\mathbf1_B,\mathbf1_S)=p^2((1-p)\mathbf1-t),\qquad
H(\mathbf1_B,\mathbf1_{D_0})
=H(\mathbf1_B,\mathbf1_{D_1})
=\tfrac12p^2((1-p)\mathbf1-t).
\tag{151.7}
$$

These are exactly the six target coefficients with label $0$ or $1$ and two $B$'s. The three label-$3$ coefficients are (151.6), and $BBB$ is B8. A common Borel null repair completes the pointwise partition without changing any coefficient, because all three positive-time marginals are absolutely continuous with respect to $m$. $\square$

**Proposition 151.2 (attribution and remaining refinement boundary).** Theorem 151.1 is a conditional source-specific composition of the inherited telescope with Meshulam–Šemrl, Brouwer and Dvoretzky–Wald–Wolfowitz. Its composition is `repo-derived`; no priority claim is attached to the mature intermediates. The precise local-dependence input is R. Meshulam and P. Šemrl, *Locally linearly dependent operators*, Pacific Journal of Mathematics **203** (2002), 441–459, [doi:10.2140/pjm.2002.203.441](https://doi.org/10.2140/pjm.2002.203.441), Theorem 2.2, with the real-field $n=3,c=1$ application already used in Lemma 147.3. The fixed-point input is L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, Mathematische Annalen **71** (1911), 97–115, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), Satz 4. The common six-measure half split uses A. Dvoretzky, A. Wald and J. Wolfowitz, *Relations among certain ranges of vector measures*, Pacific Journal of Mathematics **1** (1951), 59–74, [doi:10.2140/pjm.1951.1.59](https://doi.org/10.2140/pjm.1951.1.59), Theorem 4 and Lemma 2, pp. 66–67.

The theorem constructs some B8 witness and its refinement in the same $\mathscr D_{12}(\theta)$; it does not assert that every B8 witness refines. In the anchor bookkeeping of Proposition 149.1, the six newly paid equations have labels $1$ or $3$ and two $B$'s. Together with the three label-$0$ anchor consequences and $BBB$, they are exactly the ten coefficients containing at least two $B$'s. The 24 one-$B$ and 26 zero-$B$ equations remain obligations on this same partition, so the original $F_{64}$ quantifier and target are unchanged. No identification with the separate witness of Theorem 150.2 is supplied. There is no exact-rank-two assertion for $A^D$, no full $F_{64}$ conclusion, and no new kernel, physical-realization or nonattainment assertion. The construction uses only the original $G$, endpoint, source, measure and clock, with no extra state, seed, controller, postselection or separate slot partitions.

## 追加锚（本行以下为增补区）

## 152. One original common partition for the pair laws and the ordered 013 coefficient

**Definition 152.1 (the retained source and the thirty-seven coordinates).** Retain the complete endpoint, source and analytic telescope of Appendix II §§115–117, 123–125 and 133, including their inherited suppliers, and Definitions 134.1 and 135.1. In particular, for arbitrary original finite $a,\eta,d>0$, the carrier, product, raw Haar measure and source are

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad
(x,y,z,\zeta)(x',y',z',\zeta')
 =(x+x',y+y',z+z',\zeta+\zeta'+xy'),\\
d\mu=dx\,dy\,dz\,d\zeta,\qquad e=(0,0,0,0),\\
X_1=\partial_x,\quad X_2=\partial_y+x\partial_\zeta,
\quad X_3=\partial_z,\quad L=-\sum_{i=1}^3X_i^2,
\quad D_\zeta=-i\partial_\zeta,\quad L\Gamma=\delta_e.
\end{gathered}
\tag{152.1}
$$

The positive degree-$-3$ unit-source field $\Gamma$, central units, coefficient-one zero vector $w_*$, source coefficients and actual full self-adjoint endpoint are precisely the original ones:

$$
\begin{gathered}
S=(aL+\eta D_\zeta^2-16\sqrt{a\eta}\,\Gamma)
       |_{C_c^\infty(G\setminus\{e\};\mathbb C)},\\
C_{\rm src}(w_*)=1,\qquad h=w_*/\|w_*\|_{L^2(\mu)},
\qquad C_{\rm src}(h)>0,\qquad
\rho=A_{\rm src}(h)/C_{\rm src}(h),\\
D(H_{\rm end})=
 \{v\in D(S^*):A_{\rm src}(v)=\rho C_{\rm src}(v)\},
\qquad H_{\rm end}v=S^*v,\\
m=h^2\mu,\quad m(G)=1,\quad U_hv=hv,
\quad K=U_h^{-1}H_{\rm end}U_h\ge0,\quad T_s=e^{-sK}.
\end{gathered}
\tag{152.2}
$$

Here $h$ is real and strictly positive off the source. The full conservative form, with its source coordinate, remains

$$
\begin{gathered}
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\qquad
\mathscr V_0=\overline{C_c^\infty(G\setminus\{e\})}^{\,(115.14)},\\
\mathscr E[v]=\int_{G\setminus\{e\}}
 \left(a\sum_{i=1}^3|X_iv|^2+\eta|\partial_\zeta v|^2\right)dm.
\end{gathered}
\tag{152.3}
$$

The original conservative diffusion starts at $e$ at time zero. Its original source-start densities satisfy

$$
\mathbb P_e(Z_s\in dx)=g_s(x)m(dx),\quad
 g_s>0\ \ m\text{-a.e.},\quad \int g_s\,dm=1,
\quad g_s\in L^2(m),\quad g_{s+r}=T_rg_s
\quad(s>0,\ r\ge0).
\tag{152.4}
$$

Keep the original epochs $2d,3d,4d$, and set

$$
\begin{gathered}
P=T_d,\quad g=g_{2d},\quad g_j=P^jg=g_{(2+j)d}\quad(j=0,1,2),\\
M=1+\|g_d\|_\infty<\infty,\quad c=(4M)^{-1},\quad
\mathcal L=\{0,1,3,B\},\quad I=\{0,1,3\}.
\end{gathered}
\tag{152.5}
$$

For every permitted everywhere Borel representative $b$ of $g_d$ with $0<b\le M$, the prescribed common readout is

$$
f_3=cb,\qquad f_B=\tfrac14,\qquad
f_0=f_1=(\tfrac34-cb)/2.
\tag{152.6}
$$

It is used at all three epochs, with fresh read noises conditionally independent given the original path. For bounded real Borel classes retain

$$
\begin{aligned}
\mathcal C(u,v,w)&=\int_GguP(vPw)\,dm,\\
Q_{12}(u,v)&=\int_GguPv\,dm,\\
Q_{13}(u,v)&=\int_GguP^2v\,dm,\\
Q_{23}(u,v)&=\int_G(Pg)uPv\,dm,\\
L_j(u)&=\langle g_j,u\rangle_m\quad(j=0,1,2).
\end{aligned}
\tag{152.7}
$$

Thus the operator in $Q_{13}$ is $M_gP^2$, and the operator in $Q_{23}$ is $M_{Pg}P$, as in (150.2). Write $\mathcal R=\{12,13,23\}$ and $q_r(v)=Q_r(v,v)$, with symmetric polar forms $B_r$. For a simplex tuple $u$, whose fourth component is $u_B=1-u_0-u_1-u_3$, define

$$
\mathcal H(u)=
 \left((L_j(u_a))_{j=0,1,2;\ a\in I},
       (Q_r(u_a,u_b))_{r\in\mathcal R;\ a,b\in I},
       \mathcal C(u_0,u_1,u_3)\right)\in\mathbb R^{37}.
\tag{152.8}
$$

These are nine source marginals, twenty-seven ordered pair coordinates and the individual ordered $013$ coefficient. No other moment coordinates are included.

**Theorem 152.2 (conditional simultaneous pair laws and the original 013 coefficient).** Under exactly the complete retained suppliers of Definition 152.1, for every original $\theta=(a,\eta,d,b)\in\Theta$ there exists one pointwise Borel partition $D=(D_0,D_1,D_3,D_B)$ of the whole original $G$ such that

$$
\begin{gathered}
D\in\mathscr D_{12}(\theta),\\
Q_r(\mathbf1_{D_y},\mathbf1_{D_z})=Q_r(f_y,f_z)
 \quad(r\in\mathcal R,\ y,z\in\mathcal L),\\
\mathcal C(\mathbf1_{D_0},\mathbf1_{D_1},\mathbf1_{D_3})
 =\mathcal C(f_0,f_1,f_3).
\end{gathered}
\tag{152.9}
$$

The quantifier order is $\forall\theta\ \exists D$, with this same $D$ in all equations. In every triple coefficient its terminal is its own actual $P\mathbf1_{D_w}$.

*Proof.* All intermediate function spaces are spaces of real bounded Borel $m$-classes, except where a complex angular character or a Hilbert completion is explicitly used.

### 152.A. The original invariant slack set and sector localization

Use the symmetric coordinates $(r,\vartheta,z,\xi)$ of (120.4) on the connected full-measure set $\Omega=\{r>0\}$. The rotations act on $\vartheta$, and

$$
dm=rh^2\,dr\,d\vartheta\,dz\,d\xi
\tag{152.10}
$$

has a positive smooth rotation-invariant density there. The retained heat analyticity (122.11) and rotation invariance give an analytic invariant representative $\beta$ of $g_d$ on $\Omega$. It is positive almost everywhere and bounded there by $\|g_d\|_\infty$: the essential bound extends pointwise by continuity and full support. Choose $\tau>0$ such that

$$
E=\{x\in\Omega:\beta(x)\ge\tau\},\qquad m(E)>0.
\tag{152.11}
$$

Such a $\tau$ exists since $\beta>0$ almost everywhere. Choose an everywhere positive invariant bounded Borel representative $b^0$ of $g_d$, agreeing with $\beta$ wherever $\beta>0$ in $\Omega$, by an invariant null repair on its zero set and on $G\setminus\Omega$. Use $b^0$ in (152.6) during the proof. This leaves every target integral unchanged for the originally given $b$. On $E$ it gives $f_3\ge c\tau$, while $f_0,f_1\ge1/4$ and $f_B=1/4$ on all of $G$.

For a positive angular frequency $\ell$, let $H_\ell$ be the complex character sector and $V_{E,\ell}$ its bounded Borel vectors supported in $E$. Let $V_{E,\ell}^{\mathbb R}$ denote the bounded real cosine-sine sector with frequencies $\pm\ell$. For a real pencil

$$
q_\lambda=\lambda_{12}q_{12}+\lambda_{13}q_{13}+\lambda_{23}q_{23},
\qquad \varphi=\lambda_{12}g+\lambda_{23}Pg,\qquad A_d=T_{d/2},
\tag{152.12}
$$

use the feature map from (127.6), restricted to the sector,

$$
Z(v)=(A_dv,A_d(\varphi v),Pv,P(gv)).
\tag{152.13}
$$

The bounded symmetric matrix $J$ in (127.6), with $\gamma=\lambda_{13}$, represents $q_\lambda$ by $\langle JZ(v),Z(v)\rangle$ on real vectors. All its operators are bounded on $L^2(m)$ by §133.

We prove the sectorwise closure equality needed on this particular $E$. If $z\in H_\ell^4$ is orthogonal to $Z(V_{E,\ell})$, then the adjoint pairing is represented by

$$
F_z=A_dz_1+\varphi A_dz_2+Pz_3+gPz_4.
\tag{152.14}
$$

Every summand has an analytic representative on $\Omega$ by (122.11). It lies in the same character, so $F_z=e^{i\ell\vartheta}F_{z,\ell}(r,z,\xi)$ with an analytic quotient amplitude. Rotation invariance makes $E$ a quotient set times the circle, with quotient of positive Lebesgue measure by (152.10). Testing against every bounded amplitude supported in that quotient makes $F_{z,\ell}$ zero almost everywhere there. Mityagin's analytic zero-set theorem, Proposition 0, applied to its real and imaginary parts on the connected quotient $(0,\infty)\times\mathbb R^2$, makes this amplitude identically zero. Thus $z$ is orthogonal to $Z(V_{G,\ell})$. The opposite orthogonal-complement inclusion follows from $V_{E,\ell}\subset V_{G,\ell}$, proving

$$
\overline{Z(V_{E,\ell})}=\overline{Z(V_{G,\ell})}.
\tag{152.15}
$$

The same pairing calculation on real cosine-sine amplitudes proves (152.15) for $V_{E,\ell}^{\mathbb R}$ and $V_{G,\ell}^{\mathbb R}$. Equivalently, conjugate the character calculation and take its real fixed subspace. On the common closure the form defined by $J$ has the same negative index on either dense image: approximate a basis of any finite strictly negative subspace, and its Gram matrix remains strictly negative for sufficiently close approximants. Passing through $Z$ preserves the index, since $Z$ is injective on a strictly negative subspace and a basis in its image can be lifted. This proves sectorwise equality of the real negative indices.

Corollary 133.3 now supplies a negative vector in $V_{E,\ell}^{\mathbb R}$ for every positive $\ell$ and every nonzero $\lambda$. When $(\lambda_{12},\lambda_{23})\ne(0,0)$, use its source time $2d$, gap $d$ and coefficients $(\lambda_{12},\lambda_{23},\lambda_{13})$. When only $\lambda_{13}\ne0$, use the same supplier with gap $2d$ and coefficients $(\lambda_{13},0,0)$, then the same sectorwise closure argument with $P$ replaced by $P^2$. This is a statement about $q_{13}$ for the original operator; the observation epochs remain (152.5).

For any infinite set $S$ of positive odd frequencies put

$$
X_{E,S}=\bigoplus_{\ell\in S}V_{E,\ell}^{\mathbb R},
\tag{152.16}
$$

where the sum is algebraic, so every vector is bounded, Borel, odd and has finitely many angular frequencies. Distinct positive sectors have zero ordered $Q_r$ cross-pairings, because $P$ and each multiplier in (152.7) preserve sectors. Taking one negative vector in each of arbitrarily many sectors proves infinite negative index of every nonzero $q_\lambda$ on $X_{E,S}$. Intersecting an $N$-dimensional negative subspace with the kernels of $k$ homogeneous linear constraints loses at most $k$ dimensions. Consequently every nonzero pencil still has infinite negative index after any finite list of homogeneous constraints on this space. No sector localization for a non-invariant $E$ has been used.

### 152.B. The six ordered functionals and their rank obstruction

For $r\in\mathcal R$ let $A_r$ be the operator satisfying $Q_r(u,v)=\langle u,A_rv\rangle_m$ on real vectors. In the exact source order these operators and their adjoints are

$$
(A_{12},A_{12}^*,A_{13},A_{13}^*,A_{23},A_{23}^*)
 =(M_gP,PM_g,M_gP^2,P^2M_g,M_{Pg}P,PM_{Pg}).
\tag{152.17}
$$

On $X_{E,S}$ no nonzero coefficient combination of their pairings has finite rank. To see this, form the bounded operator

$$
R=\alpha_1M_gP+\alpha_2PM_g
 +\beta_1M_gP^2+\beta_2P^2M_g
 +\gamma_1M_{Pg}P+\gamma_2PM_{Pg}.
\tag{152.18}
$$

Let $\chi=\mathbf1_E$. The algebraic space $X_{E,S}$ is dense in the Hilbert direct sum of the $E$-supported real sectors in $S$: truncate quotient amplitudes and then the angular sum. If the pairing map $x\mapsto\langle\cdot,Rx\rangle$ on $X_{E,S}$ had rank at most $k$, every $(k+1)$-by-$(k+1)$ evaluation determinant would vanish. Density and continuity extend these identities to the Hilbert completion, so the compression $\chi R\chi$ has rank at most $k$ there.

This compression is block diagonal. A finite-rank block diagonal operator can have only finitely many nonzero blocks, since outputs in distinct blocks are independent. Choose $\ell\in S$ for which its entire real $\pm\ell$ block is zero, and complexify to the character $\ell$. For every $E$-supported input $v$ in this character, $Rv$ is analytic on $\Omega$: in (152.18) each heat factor acts at a positive time, and the outside multipliers $g,Pg$ are analytic and invariant. The compression says that $Rv$ vanishes almost everywhere on $E$. The quotient uniqueness argument from 152.A gives $Rv=0$ on all of $\Omega$, hence in $H_\ell$. For an arbitrary $u\in H_\ell$, duality then gives $\chi R^*u=0$. The outputs of $R^*$ are analytic for the same reason, so a second quotient continuation gives $R^*u=0$. Thus

$$
R|_{H_\ell}=0.
\tag{152.19}
$$

This proves the required continuation in both input and output variables, even though $E$ need not have interior. It suffices to continue a zero block; no unproved finite-rank continuation is needed.

The symmetric part of (152.19), on the real cosine-sine sector, has quadratic form

$$
(\alpha_1+\alpha_2)q_{12}
 +(\beta_1+\beta_2)q_{13}
 +(\gamma_1+\gamma_2)q_{23}.
\tag{152.20}
$$

The negative tests of 152.A, or their global suppliers before localization, force all three displayed coefficient sums to vanish. The remaining relation on $H_\ell$ is

$$
[M_\phi,P]+\kappa[M_g,P^2]=0,
\qquad \phi=\alpha g+\gamma Pg,
\quad \alpha=\alpha_1,\ \gamma=\gamma_1,\ \kappa=\beta_1.
\tag{152.21}
$$

Define the bounded self-adjoint operator on that sector

$$
C_0=M_\phi+\kappa(M_gP+PM_g).
\tag{152.22}
$$

The exact ordered identity $[M_gP+PM_g,P]=[M_g,P^2]$ gives $[C_0,P]=0$. Hence $C_0$ commutes with every spectral projection of $P$. Since $P=e^{-dK}$ is injective and $\lambda\mapsto e^{-d\lambda}$ is one-to-one on $[0,\infty)$, the spectral projections of $K$ are Borel functions of $P$. Therefore $C_0$ preserves $D(K_\ell)$ and commutes with $K_\ell$ there. This conclusion concerns the actual full self-adjoint restriction, rather than a formal inversion of $P$ on all vectors.

For bounded self-adjoint $A$ and $u\in D(K_\ell)$ set

$$
\mathcal D_A(u)=\langle Ku,Au\rangle_m-\langle Au,Ku\rangle_m.
\tag{152.23}
$$

Use the genuine compact punctured core vectors of (129.11), written with a quotient covector $\omega\ne0$,

$$
u_N=e^{i\ell\vartheta}\chi_0(r,z,\xi)
                 e^{iN\omega\cdot(r,z,\xi)},
\qquad \chi_0\in C_c^\infty((0,\infty)\times\mathbb R^2;\mathbb R).
\tag{152.24}
$$

Their norms are independent of $N$ and $\|Ku_N\|=O(N^2)$. The retained local smoothing and duality estimate (129.12) gives $\|Pu_N\|+\|PKu_N\|=O(N^{-j})$ for every $j$. With $H_g=M_gP+PM_g$, self-adjointness gives the form estimate

$$
|\mathcal D_{H_g}(u_N)|
 \le2\|g\|_\infty
       \bigl(\|Ku_N\|\|Pu_N\|+\|PKu_N\|\|u_N\|\bigr)=o(1).
\tag{152.25}
$$

There is no assumption that an arbitrary bounded multiplier preserves $D(K)$. Only $u_N$ and $\phi u_N$ are used as compact core vectors, which they are by local smoothness. The proved commutation of $C_0$ gives $\mathcal D_{C_0}(u_N)=0$, so (152.22)–(152.25) imply $\mathcal D_{M_\phi}(u_N)=o(1)$. The exact local divergence calculation (129.15) for this invariant analytic multiplier is

$$
\mathcal D_{M_\phi}(u_N)=
 -2iN\int|\chi_0|^2
 \left[a\phi_r\omega_r+a\phi_z\omega_z+
        (\eta+ar^2/4)\phi_\xi\omega_\xi\right]dm+O(1).
\tag{152.26}
$$

Varying $\chi_0$ and $\omega$, positivity of the density and $a,\eta>0$ force $\phi_r=\phi_z=\phi_\xi=0$. Rotation invariance gives its remaining derivative zero, so connectedness makes $\phi$ constant. The source-start nonconstancy result of Corollary 126.2 now forces $\alpha=\gamma=0$. If $\kappa\ne0$, (152.21) would give $[M_g,P^2]=0$; the same injective spectral calculus and local calculation would make $g$ constant, contradicting that same source-start result. Thus $\kappa=0$, and every coefficient in (152.18) is zero. This establishes the no-finite-rank assertion, including its antisymmetric part.

For $X=X_{E,S}$ apply this assertion to the six operators into the algebraic dual $X^*$,

$$
x\longmapsto\bigl[h\longmapsto Q_r(h,x)\bigr],\qquad
x\longmapsto\bigl[h\longmapsto Q_r(x,h)\bigr]
\quad(r\in\mathcal R).
\tag{152.27}
$$

Their span has dimension six and no nonzero finite-rank member. The contrapositive of Meshulam–Šemrl, Theorem 2.2, over $\mathbb R$ with $n=6,c=1$, supplies an $x\in X$ for which these six functionals are independent. Indeed, local dependence would supply a nonzero operator of rank at most five. This application allows arbitrary vector spaces and the algebraic dual.

### 152.C. Exact bounded corrections retaining the six functionals

Choose pairwise disjoint infinite sets of positive odd frequencies, for example

$$
S_0=\{16k+1:k\ge0\},\quad
S_1=\{16k+3:k\ge0\},\quad
S_3=\{16k+5:k\ge0\}.
\tag{152.28}
$$

On each $X_{E,S_a}$ the finite-dimensional sphere argument (147.6)–(147.8) applies after every finite homogeneous constraint, because 152.A supplies its exact all-pencil hypothesis. More explicitly, for each unit coefficient vector choose a five-dimensional negative subspace in the constrained space. A finite cover of the coefficient sphere supplies a finite-dimensional sum $F$ on which every unit pencil has at least five eigenvalues at most $-\delta$, for one $\delta>0$. For a target $v\in\mathbb R^3$, minimize $\|q(x)-v\|^2$ on the radius-$R$ sphere in $F$, with $R^2>\|v\|/\delta$. If $\lambda=q(x)-v\ne0$, its five-dimensional negative spectral space contains a nonzero $w$ satisfying $B_r(x,w)=0$ for all three $r$ and $(x,w)_F=0$. Along the normalized curve $R(x+sw)/\|x+sw\|$, the second derivative is

$$
4\left(q_\lambda(w)
   -\frac{\lambda\cdot q(x)}{R^2}\|w\|^2\right)
 \le4\|\lambda\|\|w\|^2
           \left(-\delta+\frac{\|v\|}{R^2}\right)<0.
\tag{152.29}
$$

Here $\lambda\cdot q(x)=\|\lambda\|^2+\lambda\cdot v\ge-\|\lambda\|\|v\|$. This contradicts minimality. Thus $q(W)=\mathbb R^3$ for each such constrained subspace $W$. This invocation of the existing correction argument finds an actual vector in a finite-dimensional space.

For each $a\in I$, choose $x\in X_{E,S_a}$ from (152.27) and dual tests $h_1,\ldots,h_6$ for its six functionals, with evaluation matrix the identity. Denote these functionals, as functions of their base vector, by $\ell_i(x)(h)$, $i=1,\ldots,6$. Impose on $z\in X_{E,S_a}$ precisely the finite constraints

$$
\ell_i(z)(h_k)=0\quad(1\le i,k\le6),\qquad
B_r(x,z)=0\quad(r\in\mathcal R).
\tag{152.30}
$$

The preceding surjectivity gives a $z$ satisfying these constraints and $q(z)=-q(x)$. Set $x_a=x+z$. Then

$$
q_r(x_a)=0\quad(r\in\mathcal R),\qquad
\ell_i(x_a)(h_k)=\delta_{ik}.
\tag{152.31}
$$

Thus each $x_a$ is bounded, Borel, supported in $E$, odd, has finitely many angular frequencies in $S_a$, and has six independent ordered functionals. These are internal evaluation and polar constraints, not additional moments in (152.8). Distinct $a$ have zero ordered pair cross-pairings by (152.28).

### 152.D. An exact stochastic point in the prescribed fiber

For sufficiently small $t>0$ put

$$
u_a^*=f_a+t x_a\quad(a\in I),\qquad
u_B^*=f_B-t(x_0+x_1+x_3).
\tag{152.32}
$$

The four functions sum to one. On $E$ all four original components have a fixed positive lower bound, and outside $E$ they are unchanged. Choose $t$ so that all four components retain positive slack on $E$. All source marginals are unchanged by oddness. In each ordered pair, its two first-order terms vanish because the $f_a$ and weights are invariant; the second-order term vanishes by (152.31) for equal labels and by disjoint sectors for distinct labels.

Expand $\mathcal C(u_0^*,u_1^*,u_3^*)$. Each term with one $x_a$ vanishes by oddness. Each term with two distinct $x_a$ vanishes by angular separation: the third factor is invariant, and multiplication by invariant functions and application of $P$ preserve every character. The term with three $x_a$ is odd under the half-turn and also vanishes. Hence

$$
\mathcal H(u^*)=\mathcal H(f).
\tag{152.33}
$$

This identity is exact; no small-residual argument is used to obtain it.

### 152.E. The thirty-six lower-order rows and the surviving 013 row

Use independent variations of the three components $u_a$, $a\in I$, always compensating their sum in $u_B$. The nine invariant directions $\mathbf1_Eg_j$ in the respective components have marginal differential consisting of three copies of

$$
G_E=(\langle g_i,\mathbf1_Eg_j\rangle_m)_{0\le i,j\le2}.
\tag{152.34}
$$

This matrix is positive definite. If its quadratic form vanished, the corresponding analytic invariant combination of $g,Pg,P^2g$ would vanish almost everywhere on $E$. Quotient uniqueness would make it vanish globally, contradicting Lemma 147.2. The functions are bounded by §133, so these are admissible bounded directions supported in $E$.

For an odd direction $h$ varying component $a$, the pair differential is exactly

$$
D Q_r(u_i,u_j)[\delta u_a=h]
 =t\bigl(\mathbf1_{i=a}Q_r(h,x_j)
              +\mathbf1_{j=a}Q_r(x_i,h)\bigr),
\qquad i,j\in I.
\tag{152.35}
$$

The invariant $f$ terms have vanished by parity. For each diagonal pair $(a,a)$, the three functionals $Q_r(h,x_a)+Q_r(x_a,h)$ are independent on $X_{E,S_a}$: a dependence would be a dependence of the six functionals in (152.31). Choose three dual directions there varying component $a$. They affect precisely its three diagonal pair rows; every other pair row vanishes by frequency separation.

For each unordered distinct pair $\{a,b\}$, choose six directions $h\in X_{E,S_b}$ varying component $a$. By (152.31) for $x_b$, their six rows

$$
\bigl(Q_r(h,x_b),Q_r(x_b,h)\bigr)_{r\in\mathcal R}
\tag{152.36}
$$

can be made an invertible evaluation matrix. They affect precisely the six ordered rows $(a,b),(b,a)$; in particular the $(a,a)$ rows pair their $S_b$ frequencies with $S_a$ and vanish. Every remaining pair row either has no varied component or pairs with a third disjoint sector. These twenty-seven odd directions have zero marginal differential and an invertible pair differential. Together with the nine invariant directions, whose pair entries need not vanish, the lower-order thirty-six-row differential is block triangular with invertible diagonal blocks.

To obtain one more row define the bounded real function

$$
\psi=gP(x_1Px_3).
\tag{152.37}
$$

It is even and has no zero angular frequency. Indeed $x_1$ and $Px_3$ have finite angular spectra in the disjoint positive sets $S_1,S_3$ and their negatives; none of their sums is zero. Multiplication by $g$ and application of $P$ preserve the absence of the zero mode. Also $\psi\ne0$ in $L^2(m)$. The vector $x_3$ is nonzero by its independent functionals, so $Px_3$ is a nonzero analytic function on $\Omega$ by injectivity of $P$ and (122.11). Its zero set is null by analytic uniqueness. Since $x_1\ne0$, the bounded product $x_1Px_3$ is nonzero; injectivity of $P$ and $g>0$ almost everywhere then prove the assertion.

Vary only $u_0$ by $\psi$, and $u_B$ by $-\psi$. All marginal derivatives vanish by its zero angular mean. Its pair derivatives vanish as well: its pairing with the invariant part of each $u_j^*$ has zero angular mean, and its pairing with the odd part is odd. Its triple derivative is

$$
\begin{aligned}
D\mathcal C(u_0,u_1,u_3)[(\psi,0,0)]\big|_{u=u^*}
 &=\mathcal C(\psi,u_1^*,u_3^*)\\
 &=t^2\mathcal C(\psi,x_1,x_3)
 =t^2\int_G\psi^2\,dm>0.
\end{aligned}
\tag{152.38}
$$

The constant term vanishes by zero angular mean and the two linear terms by parity. This proves that the full thirty-seven-row differential is onto. Restricting to the thirty-six directions above and this last one makes it an isomorphism.

All directions involving component $3$ are supported in $E$, where that component has uniform slack. The same is true of the other earlier directions. The only new direction outside $E$ varies components $0$ and $B$, which have uniform positive slack on all of $G$. Thus bounded Borel representatives can be chosen, with one common null repair, so that a small closed ball in these thirty-seven directions consists of pointwise simplex tuples on the whole $G$. This pays the domain condition without assuming a global positive lower bound for $f_3$.

### 152.F. Attainment by one finite Borel partition

Write the selected directions as $e_1,\ldots,e_{37}$, including their compensating $B$ components, and put

$$
u(s)=u^*+\sum_{j=1}^{37}s_je_j,\qquad
F(s)=\mathcal H(u(s))-\mathcal H(f),\qquad A=DF(0).
\tag{152.39}
$$

The map is polynomial of degree at most three, $F(0)=0$ and $A$ is invertible. Choose a radius $\varepsilon>0$ so that the closed parameter ball consists of pointwise simplex tuples as just proved and

$$
\sup_{\|s\|\le\varepsilon}\|s-A^{-1}F(s)\|<\varepsilon/3.
\tag{152.40}
$$

This follows from $F(s)=As+O(\|s\|^2)$.

Use increasing finite Borel partitions $\mathcal P_n$ generated by the first $n$ members of a countable coordinate basis of the original $G$. On each positive-mass cell $A_0$ choose a nested family $A_0(v)$, $0\le v\le m(A_0)$, of Borel subsets of mass $v$, with empty and full endpoints. This is the original-coordinate construction of §148: $m\ll\mu$ makes every level set of the first original coordinate $x$ null, so $q\mapsto m(A_0\cap\{x\le q\})$ is continuous from zero to $m(A_0)$, and quantile thresholds give all intermediate masses.

In the fixed label order $(0,1,3,B)$, take consecutive slices of this same nested family with masses $\int_{A_0}u_y(s)\,dm$. Do this on all cells, assigning every zero-mass cell to $B$, and call the resulting pointwise whole-$G$ Borel partition $D_n(s)$. All four cell masses agree with those of $u(s)$. If $v_k(s)=\sum_{j=1}^k\int_{A_0}u_{y_j}(s)\,dm$, the symmetric difference of the $k$th slice at $s,s'$ has mass at most

$$
|v_k(s)-v_k(s')|+|v_{k-1}(s)-v_{k-1}(s')|.
\tag{152.41}
$$

Summing over cells and labels bounds the sum of the four symmetric-difference masses by $6\sum_y\|u_y(s)-u_y(s')\|_1$. Thus $D_n(s)$ is continuous in that metric. The quantile coordinate only chooses subsets of the original $G$.

The actual three-time density is exactly

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3)
 \in L^1(m^{\otimes3}),\qquad W\ge0,\qquad\int W\,dm^{\otimes3}=1.
\tag{152.42}
$$

Let $W_n$ be its conditional expectation on $\mathcal P_n^{\otimes3}$. The product partitions generate the product Borel sigma-algebra, so density of their simple functions and contractivity give $\|W-W_n\|_1\to0$. Every coordinate in (152.8) is an integral against $W$ of a product of at most three selected slot factors: the $L_j$ use slot $j+1$, the three pairs use their indicated slots, and $013$ uses all three. With $W_n$ the product-cell integrals factor, so cell-mass agreement makes all thirty-seven coordinates exactly equal for $u(s)$ and $\mathbf1_{D_n(s)}$. All factors lie in $[0,1]$, whence, with

$$
F_n(s)=\mathcal H(\mathbf1_{D_n(s)})-\mathcal H(f),
\qquad
\sup_{\|s\|\le\varepsilon}\|F_n(s)-F(s)\|
 \le2\sqrt{37}\,\|W-W_n\|_1\longrightarrow0.
\tag{152.43}
$$

Each $F_n$ is continuous for the actual density $W$, not just $W_n$. Telescoping a product bounds each coordinate difference by the sum of at most three slot differences integrated against the corresponding source marginals. These marginals are the bounded $g_0,g_1,g_2$ by §133. Consequently (152.41) makes every coordinate continuous on the parameter ball.

Choose one finite $n$ so large that $\|A^{-1}\|\sup\|F_n-F\|<\varepsilon/3$. By (152.40)–(152.43), the continuous map

$$
s\longmapsto s-A^{-1}F_n(s)
\tag{152.44}
$$

sends the closed radius-$\varepsilon$ ball into its radius-$2\varepsilon/3$ ball. Brouwer's finite-dimensional fixed-point theorem gives $s_n$ with $F_n(s_n)=0$. Thus $D=D_n(s_n)$ is one actual pointwise Borel partition with $\mathcal H(\mathbf1_D)=\mathcal H(f)$. This is attainment at one finite partition and one parameter, rather than a claim that a weak limit of indicators is an indicator.

### 152.G. Recovery of the fourth label and the precise residual boundary

For any bounded $v$, the original propagation and self-adjointness give the row and column sums

$$
\begin{array}{c|cc}
 r&Q_r(v,1)&Q_r(1,v)\\ \hline
12&L_0(v)&L_1(v)\\
13&L_0(v)&L_2(v)\\
23&L_1(v)&L_2(v).
\end{array}
\tag{152.45}
$$

Write these left and right marginal functionals as $L_r^{\rm left},L_r^{\rm right}$. For either tuple $v=\mathbf1_D$ or $v=f$, the pointwise complement identity gives

$$
\begin{aligned}
Q_r(v_a,v_B)&=L_r^{\rm left}(v_a)-\sum_{b\in I}Q_r(v_a,v_b),\\
Q_r(v_B,v_a)&=L_r^{\rm right}(v_a)-\sum_{b\in I}Q_r(v_b,v_a),\\
Q_r(v_B,v_B)&=1-\sum_{a\in I}
  \bigl(L_r^{\rm left}(v_a)+L_r^{\rm right}(v_a)\bigr)
  +\sum_{a,b\in I}Q_r(v_a,v_b).
\end{aligned}
\tag{152.46}
$$

Every term on the right is already fixed by (152.8). This proves all ordered pair coordinates with label $B$. Likewise $L_j(v_B)=1-\sum_{a\in I}L_j(v_a)$ gives the fourth marginal at each epoch, proving $D\in\mathscr D_{12}(\theta)$ by (152.4)–(152.5). The $013$ equation is the last coordinate of (152.8). Restoring the originally prescribed representative $b$ changes none of these target integrals. All intermediate null repairs are harmless because all three positive-time source marginals are absolutely continuous with respect to $m$. This proves (152.9). $\square$

The source-specific composition in Theorem 152.2 is `repo-derived`: the invariant-slack sector continuation and the six ordered functionals feed the same original-source thirty-seven-coordinate attainment argument. Heat analyticity, local smoothing, the principal-symbol calculation, source-start nonconstancy and the global sector negative tests are the supplied results (122.11), Corollary 126.2, §§129.C–D and Corollary 133.3. The marginal independence and the finite-dimensional correction and quantile templates are Lemmas 147.2–147.3 and Theorem 148.1. They are used within this proof, not asserted as new standalone results.

The known analytic uniqueness input is B. S. Mityagin, *The zero set of a real analytic function*, [arXiv:1512.07276v1](https://arxiv.org/abs/1512.07276v1), Proposition 0; its connected-open-domain and positive-measure-zero-set hypotheses are paid in 152.A. The known local-dependence input is R. Meshulam and P. Šemrl, *Locally linearly dependent operators*, [doi:10.2140/pjm.2002.203.441](https://doi.org/10.2140/pjm.2002.203.441), Theorem 2.2, pp. 444–445; (152.27) uses its contrapositive for real vector spaces and $n=6,c=1$. The fixed-point input is Brouwer's theorem, *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), in its finite-dimensional closed-ball form, as used in §148. No priority claim is attached to these intermediates or to their source-specific composition.

For this partition define the actual residual $\Delta_{yzw}=\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})-\mathcal C(f_y,f_z,f_w)$. All its pair sums vanish. By Proposition 150.3 it lies in $H_0^{\otimes3}$, where $H_0=\{v\in\mathbb R^{\mathcal L}:\sum_yv_y=0\}$, and its twenty-seven ambient coordinates are $\Delta_{ijk}$, $i,j,k\in I$. Theorem 152.2 pays precisely $\Delta_{013}=0$ among these. The other twenty-six equations remain obligations for the same $D$; this ambient linear count asserts neither independence nor feasibility of their nonlinear restrictions to partitions. The unchanged original objective is still $\forall\theta\ \exists D:\Phi_3(\mathbf1_D)=\Phi_3(f)$ in all sixty-four ordered coordinates. Every residual uses its actual terminal $P\mathbf1_{D_w}$, with no substitution by $Pf_w$.

The all-pair witness of §150 and the B8/two-$B$ refinement witness of §151 remain separate witnesses. Theorem 152.2 imposes no arbitrary extra $L^1$ moment list, B8 condition, two-$B$ compatibility or rank-two law for $A_D[y,z]=\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_3})$. It does not settle the half-time negative-space lift, the nonsymmetric finite-index continuation or an every-overlap criterion. All its assertions retain the original full endpoint, source, measure, clock, state space and common readout. They introduce no extra seed, controller, postselection or slot-dependent partition, and supply no physical-realization assertion or counterexample to the original $F_{64}$ statement.

## 追加锚（本行以下为增补区）

## 153. One original common partition for the pair laws and the ordered 013, 103 and 031 coefficients

**Definition 153.1 (the retained original telescope and thirty-nine coordinates).** Retain exactly the complete suppliers and objects of Definition 152.1, hence Appendix II §§115–117, 123–125 and 133 and Definitions 134.1 and 135.1, with all their inherited conditions. The parameters are every original finite $a,\eta,d>0$ and every permitted everywhere Borel representative $b$ of $g_d$ satisfying $0<b\le M$. In particular, $G=H^1\times\mathbb R$, its product and raw Haar measure $\mu$, the source $e$, the unit-source field $L\Gamma=\delta_e$, the coefficient-one $w_*$, the positive normalized $h$, the actual selector $A_{\rm src}=\rho C_{\rm src}$ and the entire conservative source-inclusive $K$ are those of (152.1)–(152.4). Keep

$$
\begin{gathered}
m=h^2\mu,\qquad T_s=e^{-sK},\qquad P=T_d,\qquad
g=g_{2d},\qquad g_j=P^jg=g_{(2+j)d},\\
M=1+\|g_d\|_\infty,\qquad c=(4M)^{-1},\qquad
f_3=cb,\quad f_B=\tfrac14,\quad
f_0=f_1=(\tfrac34-cb)/2,\\
\mathcal L=\{0,1,3,B\},\qquad I=\{0,1,3\},\qquad
\mathcal R=\{12,13,23\},\qquad
\mathcal T=\{013,103,031\}.
\end{gathered}
\tag{153.1}
$$

The source starts at $e$ at time zero, the observation epochs are $2d,3d,4d$, and the common readout has the prescribed fresh noises conditionally independent given that path. Use precisely the functionals $\mathcal C,Q_r,L_j,q_r,B_r$ of (152.7) and its polar-form convention. For a pointwise simplex tuple $u$, with $u_B=1-u_0-u_1-u_3$, put

$$
\mathcal H_{39}(u)=
\left(
 (L_j(u_a))_{j=0,1,2;\ a\in I},
 (Q_r(u_a,u_b))_{r\in\mathcal R;\ a,b\in I},
 \mathcal C(u_0,u_1,u_3),
 \mathcal C(u_1,u_0,u_3),
 \mathcal C(u_0,u_3,u_1)
\right).
\tag{153.2}
$$

All coordinates refer to this one tuple on the original $G$. The original full joint equation remains

$$
(\forall\theta\in\Theta)(\exists D\text{ a pointwise Borel partition of }G)
\quad
\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
 =\mathcal C(f_y,f_z,f_w)
\quad(y,z,w\in\mathcal L).
\tag{153.3}
$$

**Theorem 153.2 (conditional coattainment of all ordered pairs and three ordered triples).** Under exactly the retained suppliers of Definition 153.1, for every original $\theta=(a,\eta,d,b)\in\Theta$ there exists one pointwise whole-$G$ Borel partition $D=(D_0,D_1,D_3,D_B)$ such that

$$
\begin{gathered}
D\in\mathscr D_{12}(\theta),\\
Q_r(\mathbf1_{D_y},\mathbf1_{D_z})=Q_r(f_y,f_z)
 \quad(r\in\mathcal R,\ y,z\in\mathcal L),\\
\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
 =\mathcal C(f_y,f_z,f_w)
 \quad(yzw\in\mathcal T).
\end{gathered}
\tag{153.4}
$$

Every terminal factor in these equalities is the same partition's own $P\mathbf1_{D_w}$. For this $D$ the triple residual belongs to $H_0^{\otimes3}$, with $H_0=\{v\in\mathbb R^{\mathcal L}:\sum_yv_y=0\}$, and its coordinates $013,103,031$ vanish. Its other twenty-four ambient $I^3$ coordinates are not prescribed by (153.4).

*Proof.* Fix an arbitrary original $\theta$. All function spaces below consist of real bounded Borel $m$-classes unless complex character sectors or a Hilbert space are specified.

### 153.A. An original orbit and strictly positive character coefficients

Use the original symmetric coordinates $(r,\vartheta,z,\xi)$ on $\Omega=\{r>0\}$ from (120.4) and (152.10). Write

$$
q=(r,z,\xi)\in\mathcal Q=(0,\infty)\times\mathbb R^2,\qquad
dm=d\nu(q)\,\frac{d\vartheta}{2\pi},\qquad
d\nu=2\pi rh(q)^2\,dr\,dz\,d\xi.
\tag{153.5}
$$

The full original $K$, its semigroup and the source densities commute with these rotations. The analytic invariant representative $\beta$ of $g_d$ and the continuous invariant representative of $g$ are positive almost everywhere. Choose $q_\circ$ at which both are positive, choose $0<\tau<\beta(q_\circ)$, and then a relatively compact quotient neighborhood $U$ of $q_\circ$ on which $\beta>\tau$ and $g>0$. Set

$$
p_\circ=(q_\circ,0),\qquad g_\circ=g(q_\circ)>0,\qquad
E=\{(q,\vartheta)\in\Omega:\beta(q)\ge\tau\}.
\tag{153.6}
$$

Thus $m(E)>0$, and $E$ is exactly an admissible invariant slack set of 152.A. Let $b^0$ be the everywhere positive invariant representative constructed in 152.A, and let $f^0$ be (153.1) evaluated at $b^0$. Then $[f_y^0]=[f_y]$ for every label, so $\mathcal H_{39}(f^0)=\mathcal H_{39}(f)$. This intermediate tuple satisfies $f_3^0\ge c\tau$ on $E$ and $f_0^0,f_1^0,f_B^0\ge1/4$ on all of $G$.

Let $p_d$ be the actual full heat kernel (120.8)–(120.10), and define its continuous orbit trace

$$
k(\alpha)=p_d(p_\circ,R_\alpha p_\circ),\qquad
a_j=\int_0^{2\pi} k(\alpha)e^{-ij\alpha}\,
                        \frac{d\alpha}{2\pi}\quad(j\in\mathbb Z).
\tag{153.7}
$$

Symmetry and simultaneous rotation equivariance make $k$ real and even. In the complexification of $L^2(m)$ let $\Pi_j$ project onto the character $e^{ij\vartheta}$. The evaluation vector $k_{d/2,p_\circ}$ in (120.8) gives

$$
a_j=\|\Pi_j k_{d/2,p_\circ}\|_2^2
    =a_{-j}.
\tag{153.8}
$$

Indeed $p_d(p_\circ,R_\alpha p_\circ)$ is the matrix coefficient of the rotation action on this evaluation vector by (120.9); integration against a character gives the squared norm of its character projection. Depending on the pullback convention this first gives the $-j$ projection; reality of the evaluation vector identifies the two norms.

In fact every $a_j$ is strictly positive. Suppose $\Pi_j k_{d/2,p_\circ}=0$. Evaluation at $p_\circ$ would then vanish on $T_{d/2}(H_j)$, where $H_j=\Pi_j L^2(m;\mathbb C)$. The commutation of the entire $K$ with rotations makes $H_j$ reducing. For $w\in D(K^2)\cap H_j$, its original spectral truncations satisfy

$$
w_N=\mathbf1_{[0,N]}(K)w\longrightarrow w
 \quad\hbox{in the graph norm of }D(K^2),\qquad
w_N=T_{d/2}\bigl(e^{(d/2)K}w_N\bigr),
\quad e^{(d/2)K}w_N\in H_j.
\tag{153.9}
$$

Evaluation on this graph domain is continuous by (120.7). It follows that every such $w$ vanishes at $p_\circ$. Choose instead $\chi\in C_c^\infty(\mathcal Q)$ with $\chi(q_\circ)=1$. The genuine punctured smooth function $\chi(q)e^{ij\vartheta}$ belongs to $D(K^N)$ for every $N$, by the core-domain argument following (120.11), and has value one at $p_\circ$. This contradiction proves strict positivity, using the original full domain.

The nonnegative Fejér argument of (147.13) applies to this trace: the weighted coefficient sums at zero increase to $k(0)$, so

$$
a_j>0,\qquad
\sum_{j\in\mathbb Z}a_j=k(0)<\infty,\qquad
k(\alpha)=\sum_{j\in\mathbb Z}a_je^{ij\alpha}.
\tag{153.10}
$$

In particular $a_j\to0$ as $|j|\to\infty$. There are infinitely many positive odd $n\ge3$ with $a_{n+1}\ne a_{n-1}$. Otherwise the positive even subsequence would eventually be constant, and its zero limit would contradict (153.10). Choose two distinct such frequencies and put

$$
n_0,n_1\ge3\text{ odd},\qquad n_0\ne n_1,\qquad n_3=1,\qquad
a_{n_a+1}\ne a_{n_a-1}\ (a=0,1),\qquad
L=\max(n_0,n_1).
\tag{153.11}
$$

These choices restrict no original parameter.

### 153.B. Localization and an explicit three-column rank calculation

For bounded real $w=(w_0,w_1,w_3)$ define the two-component densities

$$
\begin{aligned}
\mathbf R_{013}[w]&=
 \bigl(gP(w_1Pw_3),\ P(gw_0)Pw_3\bigr),\\
\mathbf R_{103}[w]&=
 \bigl(P(gw_1)Pw_3,\ gP(w_0Pw_3)\bigr),\\
\mathbf R_{031}[w]&=
 \bigl(gP(w_3Pw_1),\ P(w_3P(gw_0))\bigr).
\end{aligned}
\tag{153.12}
$$

They are bounded and continuous on $\Omega$: each nonsmooth input inside a heat factor is bounded and in $L^2(m)$, and (120.7)–(120.10) give the continuous representative; the other factors are smoothed inputs or the continuous $g$.

Choose nonnegative $\phi_\epsilon\in C_c^\infty(U)$ with $\int\phi_\epsilon\,d\nu=1$ and supports shrinking to $q_\circ$, and set

$$
v_a^\epsilon(q,\vartheta)
   =\phi_\epsilon(q)\cos(n_a\vartheta)\quad(a\in I).
\tag{153.13}
$$

Each fixed function is bounded, supported in $E$ and odd under $R_\pi$. To compute (153.12) at the orbit, joint continuity of the original kernel gives, uniformly in $\alpha$ and also uniformly when the output quotient lies in the shrinking supports,

$$
\begin{aligned}
Pv_a^\epsilon(p_\alpha)&\longrightarrow
                          a_{n_a}\cos(n_a\alpha),\\
P(gv_a^\epsilon)(p_\alpha)&\longrightarrow
                          g_\circ a_{n_a}\cos(n_a\alpha),
\qquad p_\alpha=R_\alpha p_\circ.
\end{aligned}
\tag{153.14}
$$

Here the limiting integral is convolution by $k$ on the orbit with normalized angular measure. For the nested terms, the same uniformity on the support of $\phi_\epsilon$ first gives $Pv_b^\epsilon(q,\vartheta)\to a_{n_b}\cos(n_b\vartheta)$. Inserting this in the kernel formula, and using $\int\phi_\epsilon\,d\nu=1$, yields, for distinct positive $n,m$ in use,

$$
\begin{aligned}
P\bigl((\phi_\epsilon\cos n\vartheta)
           P(\phi_\epsilon\cos m\vartheta)\bigr)(p_\alpha)
 &\longrightarrow
 \frac{a_m}{2}
 \left(a_{n+m}\cos((n+m)\alpha)
            +a_{n-m}\cos((n-m)\alpha)\right),\\
P\bigl((\phi_\epsilon\cos m\vartheta)
           P(g\phi_\epsilon\cos n\vartheta)\bigr)(p_\alpha)
 &\longrightarrow
 \frac{g_\circ a_n}{2}
 \left(a_{n+m}\cos((n+m)\alpha)
            +a_{n-m}\cos((n-m)\alpha)\right).
\end{aligned}
\tag{153.15}
$$

All limits are uniform on the compact orbit. To justify the substitutions directly, restrict both kernel variables to the compact rotation-invariant neighborhood over $\overline U$. The kernels are uniformly continuous and bounded there. The error in each inner integral is bounded by that uniform modulus times $\int\phi_\epsilon\,d\nu$, and the same estimate applies to the outer integral after multiplication by the bounded cosine. Also $g(q)\to g_\circ$ on the shrinking supports. Thus no global bound uniform in $\epsilon$ is required.

For a continuous real $H$ on the orbit put
$\mathfrak c_sH=2\int_0^{2\pi}H(p_\alpha)\cos(s\alpha)\,d\alpha/(2\pi)$.
Form the real four-by-three matrix $\mathsf E(w)$ with columns in the order $013,103,031$, using the component-$0$ coefficients at $n_1+1,n_1-1$ followed by the component-$1$ coefficients at $n_0+1,n_0-1$. Equations (153.14)–(153.15) give

$$
\frac{2}{g_\circ}\mathsf E(v^\epsilon)
 \longrightarrow
\begin{pmatrix}
a_1a_{n_1+1}&a_{n_1}a_1&a_{n_1}a_{n_1+1}\\
a_1a_{n_1-1}&a_{n_1}a_1&a_{n_1}a_{n_1-1}\\
a_{n_0}a_1&a_1a_{n_0+1}&a_{n_0}a_{n_0+1}\\
a_{n_0}a_1&a_1a_{n_0-1}&a_{n_0}a_{n_0-1}
\end{pmatrix}.
\tag{153.16}
$$

This limiting matrix has rank three. If its columns with coefficients $\lambda_{013},\lambda_{103},\lambda_{031}$ sum to zero, subtraction of the first two equations and their unequal $a_{n_1\pm1}$ give
$a_1\lambda_{013}+a_{n_1}\lambda_{031}=0$.
Either of those equations then gives $\lambda_{103}=0$. Subtraction of the last two gives
$a_1\lambda_{103}+a_{n_0}\lambda_{031}=0$,
so positivity of $a_{n_0}$ gives $\lambda_{031}=0$, and positivity of $a_1$ gives $\lambda_{013}=0$. Some three-by-three minor is therefore nonzero. Uniform convergence preserves that minor for one sufficiently small fixed $\epsilon$. Fix this $\epsilon$ and write $v_a=v_a^\epsilon$. The four low-mode evaluations of these fixed bounded functions have rank three.

### 153.C. Exact corrections protecting those same evaluations

Choose an odd integer $N>10L$ and the infinite positive odd sets

$$
S_0=\{N(8k+5):k\ge0\},\qquad
S_1=\{N(8k+1):k\ge0\},\qquad
S_3=\{N(8k+3):k\ge0\}.
\tag{153.17}
$$

For each $a\in I$ use the exact space $X_{E,S_a}$ of (152.16). Its elements are bounded Borel, supported in this same invariant $E$, and have finitely many frequencies in $\pm S_a$. The conclusions of 152.A–C apply to these sets: every nonzero $q_\lambda$ has infinite negative index after any finite homogeneous constraints; the six ordered functionals have a base with independent evaluations; and $q$ maps each such constrained space onto $\mathbb R^3$. These are the original three pencils $Q_{12},Q_{13},Q_{23}$, not extra moments. In particular the exact surjectivity (152.29) produces an element of an actual finite-dimensional subspace of $X_{E,S_a}$.

Choose $y_a\in X_{E,S_a}$ and dual tests $h_{a,1},\ldots,h_{a,6}\in X_{E,S_a}$ from (152.27). Denote the ordered functionals of a base $w$ by

$$
(\ell_i(w)(h))_{i=1}^6
       =\bigl(Q_r(h,w),Q_r(w,h)\bigr)_{r\in\mathcal R},
\qquad
\ell_i(y_a)(h_{a,k})=\delta_{ik}.
\tag{153.18}
$$

On $z\in X_{E,S_a}$ impose the finite homogeneous constraints

$$
\ell_i(z)(h_{a,k})=0\quad(1\le i,k\le6),\qquad
B_r(y_a,z)=0\quad(r\in\mathcal R).
\tag{153.19}
$$

The cited constrained surjectivity supplies a $z_a$ satisfying these constraints and

$$
q(z_a)=-q(v_a)-q(y_a).
\tag{153.20}
$$

Low and high sectors have zero ordered pair cross-pairings, since $P$ and all the weights in (152.7) preserve characters. Consequently

$$
x_a=v_a+y_a+z_a
\quad\Longrightarrow\quad
q(x_a)=0,\qquad
\ell_i(x_a)(h_{a,k})=\delta_{ik}.
\tag{153.21}
$$

This proves exact cancellation of all three diagonal quadratics and retains all six ordered evaluations for every label. The full positive spectra $\{n_a\}\cup S_a$ are pairwise disjoint.

We verify that (153.21) has not changed the rank calculation. Every term of each density in (153.12) is quadratic in two *distinct* label inputs. Expanding $x_a=v_a+(y_a+z_a)$, a mixed low/high term has frequencies of absolute value at least $N-L>2L$. A high/high term from two distinct labels has frequencies that are sums or differences of their positive frequencies. A sum is at least $2N$, and a nonzero difference between the distinct residue classes $1,3,5$ modulo $8$ has absolute value at least $2N$. The difference is never zero. Multiplication by invariant $g$ and application of $P$ preserve every character. Hence no correction term has any of the protected positive frequencies $n_1\pm1,n_0\pm1$, all at most $L+1\le2L$. We obtain the exact equality

$$
\mathsf E(x)=\mathsf E(v),\qquad \operatorname{rank}\mathsf E(x)=3.
\tag{153.22}
$$

The densities $\mathbf R_\sigma[x]$ are real bounded two-component functions, even under $R_\pi$, and have zero angular mean. The last property follows because the two label spectra in each quadratic expression are disjoint, so their signed sums never include zero. Define their real Gram matrix by

$$
\mathsf G_{\sigma\omega}
 =\int_G\left(
    R_\sigma^{(0)}[x]R_\omega^{(0)}[x]
   +R_\sigma^{(1)}[x]R_\omega^{(1)}[x]\right)dm,
 \qquad \sigma,\omega\in\mathcal T.
\tag{153.23}
$$

It is strictly positive definite. A zero quadratic form would make the corresponding linear combination of the densities zero in $L^2(m;\mathbb R^2)$. Each component is continuous on $\Omega$, where $m$ has full support, so that combination would vanish pointwise there. Applying its four orbit coefficients would contradict (153.22). Thus $\det\mathsf G>0$ has been proved for these actual corrected original-operator inputs.

### 153.D. An exact stochastic preimage and its thirty-nine directions

For sufficiently small $t>0$ put

$$
u_a^*=f_a^0+t x_a\quad(a\in I),\qquad
u_B^*=f_B^0-t(x_0+x_1+x_3).
\tag{153.24}
$$

All $x_a$ are supported in $E$, where every original component has a fixed positive lower bound. Their boundedness gives a choice of $t$ retaining positive slack for all four components on $E$. Outside $E$ the tuple equals $f^0$; in particular $u_0^*,u_1^*,u_B^*$ have one uniform positive lower bound on all of $G$.

Relative to the invariant tuple $f^0$, every marginal is unchanged by oddness. In each pair coordinate, the linear terms vanish by invariance and oddness. The quadratic term is zero for equal labels by (153.21) and for distinct labels by disjoint spectra. In every triple in $\mathcal T$ all three labels are distinct. Its single-$x$ terms vanish by oddness. Its two-$x$ terms pair distinct character sets through invariant multipliers and $P$, so vanish by angular orthogonality. Its three-$x$ term is odd under the simultaneous half-turn and vanishes as well. Therefore

$$
\mathcal H_{39}(u^*)=\mathcal H_{39}(f).
\tag{153.25}
$$

Consider variations in components $0,1,3$, always compensating their sum in $B$. For the lower thirty-six rows take the nine invariant directions $\mathbf1_Eg_j$ in their respective components. Their marginal matrix is three copies of the positive definite matrix

$$
\bigl(\langle g_i,\mathbf1_Eg_j\rangle_m\bigr)_{0\le i,j\le2}.
\tag{153.26}
$$

For completeness, a zero quadratic form would make an invariant analytic combination of $g,Pg,P^2g$ vanish on the positive-measure quotient of $E$. Analytic uniqueness makes it zero globally, and Lemma 147.2 then makes all coefficients zero. The functions are bounded by §133, so these directions are admissible and supported in $E$.

For an odd direction $h$ in component $a$, the ordered pair differential at $u^*$ is exactly

$$
DQ_r(u_i,u_j)[\delta u_a=h]
 =t\left(\mathbf1_{i=a}Q_r(h,x_j)
                 +\mathbf1_{j=a}Q_r(x_i,h)\right),
 \qquad i,j\in I.
\tag{153.27}
$$

For each diagonal $(a,a)$ choose three directions in $X_{E,S_a}$ dual to the three sums $Q_r(h,x_a)+Q_r(x_a,h)$. These sums are independent by the six evaluations in (153.21). These directions affect just that diagonal's three pair rows. For each unordered distinct pair $\{a,b\}$ choose six directions in $X_{E,S_b}$ varying component $a$, dual to
$(Q_r(h,x_b),Q_r(x_b,h))_{r\in\mathcal R}$.
They affect just the six rows $(a,b),(b,a)$. Indeed every other label's low and high frequencies are disjoint from $S_b$. Altogether these twenty-seven odd directions have zero marginal differential and an invertible twenty-seven-row pair differential. Together with (153.26) they give an invertible lower thirty-six-row restriction.

For each $\omega\in\mathcal T$ add the direction

$$
\delta_\omega u_0=R_\omega^{(0)}[x],\qquad
\delta_\omega u_1=R_\omega^{(1)}[x],\qquad
\delta_\omega u_3=0,\qquad
\delta_\omega u_B=-R_\omega^{(0)}[x]-R_\omega^{(1)}[x].
\tag{153.28}
$$

Each new direction has zero lower thirty-six-row differential: its zero angular mean kills the invariant factors, and its even parity kills its pairings with the odd $x_a$. Its triple differentials are computed using self-adjointness in the actual original $\mathcal C$. For a general two-component direction $h=(h_0,h_1)$ varying only $0,1,B$ with the same even, zero-mean properties, the constant-in-$t$ density is invariant and the linear-in-$t$ density is odd. The remaining densities are precisely

$$
D\mathcal C(u_y,u_z,u_w)[h]\big|_{u=u^*}
  =t^2\int_G
     \left(h_0R_{yzw}^{(0)}[x]+h_1R_{yzw}^{(1)}[x]\right)dm
 \quad(yzw\in\mathcal T).
\tag{153.29}
$$

For example the terminal variation in $031$ is
$\mathcal C(x_0,x_3,h_1)
 =\langle h_1,P(x_3P(gx_0))\rangle_m$;
the middle variation in $013$ is
$\mathcal C(x_0,h_1,x_3)
 =\langle h_1,P(gx_0)Px_3\rangle_m$.
The other four terms give exactly (153.12). Thus the last three columns have triple block $t^2\mathsf G$, which is invertible by (153.23). With rows ordered as marginals, pairs, triples, the full thirty-nine-direction matrix is block triangular with invertible diagonal blocks.

Choose bounded Borel representatives of all these finitely many directions and of the $x_a$. Their finite character representations can be taken pointwise on $\Omega$, with zero values on its null complement. Smoothed factors in (153.12) have their continuous representatives there; the Markov bounds extend pointwise by continuity and full support, so these representatives are bounded. All original null modifications can be combined into one Borel null set. The first thirty-six directions involving component $3$ are supported in $E$. The last three leave that component fixed, and only vary $0,1,B$, which have uniform global slack. Hence there is a closed Euclidean ball of positive radius in these thirty-nine directions consisting entirely of pointwise simplex tuples on the whole original $G$.

### 153.E. One finite Borel partition attaining the exact target

Write the chosen directions, including their compensating $B$ components, as $e_1,\ldots,e_{39}$ and put

$$
u(s)=u^*+\sum_{j=1}^{39}s_je_j,\qquad
F(s)=\mathcal H_{39}(u(s))-\mathcal H_{39}(f),\qquad
A=DF(0).
\tag{153.30}
$$

This is a polynomial map of degree at most three with $F(0)=0$ and invertible $A$. Choose $\varepsilon>0$ so that its closed ball is legal as above and

$$
\sup_{\|s\|\le\varepsilon}\|s-A^{-1}F(s)\|<\varepsilon/3.
\tag{153.31}
$$

This follows directly from $F(s)=As+O(\|s\|^2)$.

Use increasing finite Borel partitions $\mathcal P_n$ generated by a countable coordinate basis of the original $G$. On each positive-mass cell $A_0$ use the nested Borel family $A_0(v)$ of 152.F, with $m(A_0(v))=v$, $A_0(0)=\varnothing$ and $A_0(m(A_0))=A_0$. This family exists on the original space: $m\ll\mu$ makes every hyperplane of the first original coordinate null, so the restricted coordinate distribution is continuous and its quantile cuts give all intermediate masses. Consecutive slices of this same family, in order $0,1,3,B$, with masses $\int_{A_0}u_y(s)\,dm$ give one Borel partition on each cell. Assign each zero-mass cell to $B$, and denote the resulting whole-$G$ partition by $D_n(s)$.

Its four cell masses equal those of $u(s)$. With $v_k(s)$ the cumulative slice masses, nestedness gives the bound
$|v_k(s)-v_k(s')|+|v_{k-1}(s)-v_{k-1}(s')|$
for the symmetric difference of the $k$th slice. Thus

$$
\sum_y m(D_{n,y}(s)\mathbin\triangle D_{n,y}(s'))
 \le6\sum_y\|u_y(s)-u_y(s')\|_1.
\tag{153.32}
$$

The original three-time path density is

$$
W(x_1,x_2,x_3)=g(x_1)p_d(x_1,x_2)p_d(x_2,x_3)
 \in L^1(m^{\otimes3}),\qquad W\ge0,\qquad\int W=1.
\tag{153.33}
$$

Its slot marginals are exactly $g,Pg,P^2g$. Its two-slot integrals are exactly $Q_{12},Q_{13},Q_{23}$, using conservation, the semigroup law and the original source propagation. Let $W_n$ be the conditional expectation of $W$ on $\mathcal P_n^{\otimes3}$. These finite product partitions generate the product Borel sigma-algebra, so $\|W-W_n\|_1\to0$.

Every one of the thirty-nine coordinates is an integral against $W$ of a product of selected slot factors. With $W_n$ such integrals factor on product cells. The cell-mass agreement therefore makes the integrals exactly equal for $u(s)$ and $\mathbf1_{D_n(s)}$. Since each factor lies in $[0,1]$, the actual maps

$$
F_n(s)=\mathcal H_{39}(\mathbf1_{D_n(s)})-\mathcal H_{39}(f)
$$

satisfy the uniform estimate

$$
\sup_{\|s\|\le\varepsilon}\|F_n(s)-F(s)\|
 \le2\sqrt{39}\,\|W-W_n\|_1\longrightarrow0.
\tag{153.34}
$$

Each $F_n$ is continuous for the actual $W$. Telescoping any slot product bounds its change by the sum of the changed indicators integrated against the corresponding slot marginals. Those three marginals are bounded by §133, and (153.32) then gives continuity.

Choose one finite $n$ with
$\|A^{-1}\|\sup_{\|s\|\le\varepsilon}\|F_n(s)-F(s)\|<\varepsilon/3$.
By (153.31) and (153.34), the continuous map
$s\mapsto s-A^{-1}F_n(s)$
sends the closed radius-$\varepsilon$ ball into its radius-$2\varepsilon/3$ ball. Brouwer's finite-dimensional closed-ball theorem gives a fixed point $s_n$, hence $F_n(s_n)=0$. Thus

$$
D=D_n(s_n),\qquad
\mathcal H_{39}(\mathbf1_D)=\mathcal H_{39}(f)
\tag{153.35}
$$

is an exact partition at one finite $n$ and one parameter, on the original $G$.

### 153.F. Complement recovery and the full-joint boundary

For this same $D$, (152.45)–(152.46) recover every pair coordinate involving $B$ from the fixed $I\times I$ coordinates and the fixed source marginals. Likewise
$L_j(\mathbf1_{D_B})=1-\sum_{a\in I}L_j(\mathbf1_{D_a})$
gives all twelve original marginals. The last three coordinates of (153.35) are exactly the three equations in (153.4). Restoring the originally prescribed representative $b$ changes no target integral: its difference from $b^0$ is $m$-null, and all three positive-time source marginals are absolutely continuous with respect to $m$. The same observation makes all earlier null repairs harmless.

Finally define
$\Delta_{yzw}=\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
                  -\mathcal C(f_y,f_z,f_w)$.
Summing over the third, middle or first label gives respectively the already vanishing $Q_{12}$, $Q_{13}$ or $Q_{23}$ residual, by conservation and original source propagation. Proposition 150.3 therefore gives $\Delta\in H_0^{\otimes3}$ with its twenty-seven ambient $I^3$ coordinates. Precisely $013,103,031$ have been imposed here, leaving the other twenty-four as equations for this same partition. This count asserts neither nonlinear independence nor feasibility of those remaining equations. In all these residuals the last factor remains $P\mathbf1_{D_w}$. Equation (153.3) retains its full quantifiers and all sixty-four ordered coordinates.

The source-specific coattainment above is the composition of the original evaluation and graph-domain suppliers (120.7)–(120.11), the invariant slack and exact ordered corrections of 152.A–C, the protected matrix (153.16)–(153.22), and the actual-density partition construction (153.30)–(153.35). The classical local-dependence intermediate used in 152.B is R. Meshulam and P. Šemrl, *Locally linearly dependent operators*, [doi:10.2140/pjm.2002.203.441](https://doi.org/10.2140/pjm.2002.203.441), Theorem 2.2: its real $n=6,c=1$ contrapositive applies to the six operators into the algebraic dual because no nonzero combination has finite rank. The analytic uniqueness intermediate in (153.26) and 152.A is B. S. Mityagin, *The zero set of a real analytic function*, [arXiv:1512.07276v1](https://arxiv.org/abs/1512.07276v1), Proposition 0, on the connected quotient with its positive smooth density. The fixed-point intermediate is L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), in the finite-dimensional closed-ball form already used in §§148 and 152.F. These are consumed intermediates in the original-source coattainment proof. $\square$

## 追加锚（本行以下为增补区）

## 154. One original common partition for all six distinct-label coefficients and BBB

**Definition 154.1 (the unchanged original telescope and forty-three coordinates).** Retain exactly Definition 153.1, including the complete original endpoint, source and analytic suppliers of Appendix II §§115–117, 123–125 and 133 and Definitions 134.1, 135.1 and 152.1, with their inherited conditions. Thus $\theta=(a,\eta,d,b)$ ranges over every original finite $a,\eta,d>0$ and every permitted everywhere Borel representative $b$ of $g_d$ with $0<b\le M$. The group $G=H^1\times\mathbb R$, its original product, raw Haar measure $\mu$, source $e$, unit-source field $L\Gamma=\delta_e$, coefficient-one $w_*$, positive normalized $h$, actual selector $A_{\rm src}=\rho C_{\rm src}$ and full conservative source-inclusive operator $K$ are precisely those of (152.1)–(152.4). Keep

$$
\begin{gathered}
m=h^2\mu,\quad T_s=e^{-sK},\quad P=T_d,\quad
 g=g_{2d},\quad g_j=P^jg=g_{(2+j)d},\\
M=1+\|g_d\|_\infty,\quad c=(4M)^{-1},\quad
f_3=cb,\quad f_B=p=\tfrac14,\quad
f_0=f_1=(\tfrac34-cb)/2,\\
I=\{0,1,3\},\quad \mathcal L=I\cup\{B\},\quad
\mathcal R=\{12,13,23\},\quad
\mathcal T_6=\{013,103,031,130,301,310\}.
\end{gathered}
\tag{154.1}
$$

The original diffusion starts at $e$, the epochs are $2d,3d,4d$, and the prescribed stochastic readout uses this same $f$ at all epochs, with its fresh noises conditionally independent given the original path. Use exactly $\mathcal C,Q_r,L_j,q_r,B_r$ of (152.7), with the same polar-form convention. For a pointwise simplex tuple $u$, with $u_B=1-u_0-u_1-u_3$, define

$$
\mathcal H_{43}(u)=\left(
 (L_j(u_a))_{j=0,1,2;\ a\in I},
 (Q_r(u_a,u_b))_{r\in\mathcal R;\ a,b\in I},
 (\mathcal C(u_y,u_z,u_w))_{yzw\in\mathcal T_6},
 \mathcal C(u_B,u_B,u_B)\right)\in\mathbb R^{43}.
\tag{154.2}
$$

**Theorem 154.2 (conditional same-partition coattainment of the six orderings and BBB).** Under exactly Definition 154.1, for every original $\theta$ there exists one pointwise Borel partition $D=(D_0,D_1,D_3,D_B)$ of the whole original $G$ such that

$$
\begin{gathered}
D\in\mathscr D_{12}(\theta),\\
Q_r(\mathbf1_{D_y},\mathbf1_{D_z})=Q_r(f_y,f_z)
 \quad(r\in\mathcal R;\ y,z\in\mathcal L),\\
\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})
 =\mathcal C(f_y,f_z,f_w)
 \quad(yzw\in\mathcal T_6),\\
\mathcal C(\mathbf1_{D_B},\mathbf1_{D_B},\mathbf1_{D_B})=\frac1{64}.
\end{gathered}
\tag{154.3}
$$

The quantifiers are $\forall\theta\ \exists D$, and every terminal factor is this same partition's own $P\mathbf1_{D_w}$. The full equation (153.3) retains all its sixty-four coordinates; the repeated-label ambient $I^3$ coordinates are not individually specified by (154.3).

*Proof.* Fix an arbitrary original $\theta$. All bounded function spaces below consist of real Borel $m$-classes, with representatives specified at the end. Use the original quotient $\mathcal Q$, angular coordinate, measure $\nu$, orbit point $p_\circ=(q_\circ,0)$, invariant slack set $E$, neighborhood $U$, invariant representative $b^0$ and simplex tuple $f^0$ of (153.5)–(153.6). In particular, $g_\circ=g(q_\circ)>0$, $U\Subset\mathcal Q$, $\beta>\tau>0$ on $U$, and

$$
f_3^0\ge c\tau\text{ on }E,\qquad
 f_0^0,f_1^0,f_B^0\ge\tfrac14\text{ on }G,\qquad
 [f_y^0]=[f_y].
\tag{154.4}
$$

### 154.A. Two angular modes and original source variation

Let $a_j$ be the coefficients of the actual original orbit kernel in (153.7). Reuse (153.8)–(153.10): $a_j=a_{-j}>0$ for every integer $j$, and $a_j\to0$ as $|j|\to\infty$. Reuse also the consequence in (153.11) that infinitely many odd $n\ge3$ satisfy $a_{n+1}\ne a_{n-1}$. Choose odd integers

$$
\begin{gathered}
n_0\ge3,\quad n_1>3n_0+2,\quad
 a_{n_a+1}\ne a_{n_a-1}\quad(a=0,1),\\
m_*>3n_1+2,\qquad a_{m_*}\ne a_1,\qquad L=m_*.
\end{gathered}
\tag{154.5}
$$

The last choice is possible because $a_1>0$ and the odd subsequence tends to zero. These choices impose no restriction on $\theta$.

Write $p(q,\alpha)=(q,\alpha)$ in the original symmetric coordinates. For $j\ge0$ put

$$
\begin{aligned}
\mathcal K_j(q,\alpha)
 &=\int_0^{2\pi}p_d(p(q,\alpha),p(q_\circ,\vartheta))
                         \cos(j\vartheta)\,\frac{d\vartheta}{2\pi},\\
\mathfrak c_j^q H
 &=2\int_0^{2\pi}H(q,\alpha)\cos(j\alpha)\,
                                      \frac{d\alpha}{2\pi}\quad(j>0),\\
\kappa_j(q)&=\mathfrak c_j^q\mathcal K_j.
\end{aligned}
\tag{154.6}
$$

Joint continuity of the original kernel makes these functions continuous. Rotation equivariance puts $\mathcal K_j$ in the real pure frequency $j$, and symmetry on the original orbit gives
$\mathcal K_j(q_\circ,\alpha)=a_j\cos(j\alpha)$, hence $\kappa_j(q_\circ)=a_j>0$ for $j>0$. Away from that orbit a sine component is allowed.

The invariant analytic function $g$ is nonconstant by Lemma 147.2, since a constant $g$ would make $g,Pg,P^2g$ dependent. Analytic uniqueness on the connected quotient therefore makes $g$ nonconstant on every quotient neighborhood. By continuity of the three relevant $\kappa_j$, choose $q_\diamond\in U$ sufficiently close to $q_\circ$ that

$$
g(q_\diamond)\ne g_\circ,\qquad
\kappa_{n_1+1}(q_\diamond)>0,\quad
\kappa_{n_1+m_*}(q_\diamond)>0,\quad
\kappa_{n_0+1}(q_\diamond)>0.
\tag{154.7}
$$

For nonnegative $\phi_\epsilon\in C_c^\infty(U)$ with $\int\phi_\epsilon\,d\nu=1$ and supports shrinking to $q_\circ$, set

$$
V_{j,\epsilon}=\phi_\epsilon(q)\cos(j\vartheta),\qquad
v_0^\epsilon=V_{n_0,\epsilon},\quad
v_1^\epsilon=V_{n_1,\epsilon},\quad
v_3^\epsilon=V_{1,\epsilon}+V_{m_*,\epsilon}.
\tag{154.8}
$$

These bounded functions are supported in $E$, odd under the half-turn, and have pairwise disjoint positive angular spectra.

### 154.B. Seven independent quadratic densities on the original space

For bounded real inputs define

$$
\mathsf A(v,w)=gP(vPw),\qquad
\mathsf B(v,w)=P(gv)Pw,\qquad
\mathsf T(v,w)=P(vP(gw)).
\tag{154.9}
$$

For $x=(x_0,x_1,x_3)$ define two-component functions by the following six rows:

$$
\begin{array}{c|cc}
\sigma&R_\sigma^{(0)}[x]&R_\sigma^{(1)}[x]\\ \hline
013&\mathsf A(x_1,x_3)&\mathsf B(x_0,x_3)\\
103&\mathsf B(x_1,x_3)&\mathsf A(x_0,x_3)\\
031&\mathsf A(x_3,x_1)&\mathsf T(x_3,x_0)\\
130&\mathsf T(x_3,x_1)&\mathsf A(x_3,x_0)\\
301&\mathsf B(x_3,x_1)&\mathsf T(x_0,x_3)\\
310&\mathsf T(x_1,x_3)&\mathsf B(x_3,x_0).
\end{array}
\tag{154.10}
$$

Let $\mathsf Z$ remove the angular mean, so
$\mathsf ZH(q,\vartheta)=H(q,\vartheta)-\int H(q,\alpha)\,d\alpha/(2\pi)$.
For $s=x_0+x_1+x_3$ put

$$
\begin{aligned}
S[x]&=\mathsf A(s,s)+\mathsf B(s,s)+\mathsf T(s,s),\\
\mathbf R_{BBB}[x]&=(-\mathsf ZS[x],-\mathsf ZS[x]),\qquad
\mathcal J=\mathcal T_6\cup\{BBB\}.
\end{aligned}
\tag{154.11}
$$

All these functions are bounded and continuous on $\Omega$. Indeed every input to $P$ is bounded and in $L^2(m)$, and the actual local smoothing (120.7)–(120.10) supplies the continuous representative. The Markov bound, continuity and full support make these representatives bounded pointwise on $\Omega$. For the finite odd disjoint spectra in (154.8), the six rows in (154.10) are even with zero angular mean. The seventh row has those properties by $\mathsf Z$.

We prove that the seven rows for one sufficiently small fixed $\epsilon$ are independent, by finitely many Fourier evaluations on the two actual orbits $q_\circ,q_\diamond$. The localization estimates of (153.14)–(153.15), now with the output quotient allowed at either fixed point, give

$$
\begin{gathered}
PV_{j,\epsilon}\longrightarrow\mathcal K_j,\qquad
P(gV_{j,\epsilon})\longrightarrow g_\circ\mathcal K_j,\\
\mathsf A(V_{n,\epsilon},V_{k,\epsilon})
 \longrightarrow g(q)a_k\mathcal S_{n,k},\qquad
\mathsf T(V_{n,\epsilon},V_{k,\epsilon})
 \longrightarrow g_\circ a_k\mathcal S_{n,k},\\
\mathsf B(V_{n,\epsilon},V_{k,\epsilon})
 \longrightarrow g_\circ\mathcal K_n\mathcal K_k,\qquad
\mathcal S_{n,k}=\tfrac12(\mathcal K_{n+k}+\mathcal K_{|n-k|}).
\end{gathered}
\tag{154.12}
$$

The convergences are uniform in the output angle on both orbits, and on the shrinking input supports when computing the nested terms. For the latter terms, the inner heat factor tends uniformly there to $a_k\cos(k\vartheta)$, or to $g_\circ a_k\cos(k\vartheta)$ when its input includes $g$. Multiplication by $\phi_\epsilon\cos(n\vartheta)$ and integration then gives the cosine product in $\mathcal S_{n,k}$. Uniform continuity and boundedness of the kernel on the compact input and output orbit neighborhoods bound every error by its uniform modulus times $\int\phi_\epsilon\,d\nu=1$. This also proves (154.12) for $n=k$, where $\mathcal K_0$ occurs. No bound on $\|\phi_\epsilon\|_\infty$ uniform in $\epsilon$ is required.

Denote the six limiting rows by $\overline{\mathbf R}_\sigma$. At $q_\circ$ they satisfy

$$
\overline{\mathbf R}_{013}=\overline{\mathbf R}_{310},\qquad
\overline{\mathbf R}_{103}=\overline{\mathbf R}_{301},\qquad
\overline{\mathbf R}_{031}=\overline{\mathbf R}_{130}.
\tag{154.13}
$$

Take the component-$0$ coefficients at $n_1+1,n_1-1$ and component-$1$ coefficients at $n_0+1,n_0-1$, all at $q_\circ$. The $m_*$ mode contributes to none of these coefficients by (154.5). On the three folded columns $013,103,031$, the resulting matrix is exactly $g_\circ/2$ times (153.16), with its proved rank three. Thus a zero linear combination of all six columns has coefficients satisfying

$$
\lambda_{310}=-\lambda_{013},\qquad
\lambda_{301}=-\lambda_{103},\qquad
\lambda_{130}=-\lambda_{031}.
\tag{154.14}
$$

Write $\alpha=\lambda_{013}$, $\beta=\lambda_{103}$ and $\gamma=\lambda_{031}$. The product terms $\mathsf B$ cancel in these reversal differences, by (154.12). At an arbitrary quotient $q$, the remaining components are exactly

$$
\begin{aligned}
(g(q)-g_\circ)\bigl[
 &(\alpha a_1+\gamma a_{n_1})\mathcal S_{n_1,1}
 +(\alpha a_{m_*}+\gamma a_{n_1})\mathcal S_{n_1,m_*}\bigr],\\
(g(q)-g_\circ)\bigl[
 &(\beta a_1-\gamma a_{n_0})\mathcal S_{n_0,1}
 +(\beta a_{m_*}-\gamma a_{n_0})\mathcal S_{n_0,m_*}\bigr].
\end{aligned}
\tag{154.15}
$$

At $q_\diamond$ take the component-$0$ coefficients at $n_1+1,n_1+m_*$ and the component-$1$ coefficient at $n_0+1$. The frequencies in each component are distinct by (154.5). Equations (154.6)–(154.7) make the three nonzero scalar factors removable, leaving

$$
\alpha a_1+\gamma a_{n_1}=0,\qquad
\alpha a_{m_*}+\gamma a_{n_1}=0,\qquad
\beta a_1-\gamma a_{n_0}=0.
\tag{154.16}
$$

Since $a_1\ne a_{m_*}$ and $a_1,a_{n_1}>0$, these equations give $\alpha=\gamma=\beta=0$. The seven displayed orbit evaluations therefore have rank six on the six limiting columns.

For the seventh column use the component-$0$ coefficient at $2n_0$ on $q_\circ$. Every six-triple column has zero coefficient there: its component $0$ uses just the frequencies $n_1\pm1,n_1\pm m_*$. In $S[v^\epsilon]$, only the two $n_0$ inputs can contribute to $2n_0$. Indeed (154.5) excludes that frequency from every other signed sum of two frequencies in $\{n_0,n_1,1,m_*\}$. Formula (154.12) at $q_\circ$ gives

$$
\mathfrak c_{2n_0}^{q_\circ}\overline S
 =g_\circ\left(a_{n_0}a_{2n_0}+\tfrac12a_{n_0}^2\right)>0.
\tag{154.17}
$$

Here the first and third terms of (154.11) each contribute $g_\circ a_{n_0}a_{2n_0}/2$, and the middle product contributes $g_\circ a_{n_0}^2/2$. Removing the angular mean leaves this coefficient unchanged. Thus the eight selected evaluations have rank seven on $\mathcal J$. Some seven-by-seven minor is nonzero in the limit. Uniform convergence preserves that minor for one sufficiently small fixed $\epsilon>0$. Fix this value and write $v_a=v_a^\epsilon$. This proves independence for actual bounded original-space inputs, rather than for a limiting matrix alone.

### 154.C. Exact pair corrections preserving the seven-column rank

Choose an odd integer $N>10L$ and use the infinite odd sets

$$
S_0=\{N(8k+5):k\ge0\},\qquad
S_1=\{N(8k+1):k\ge0\},\qquad
S_3=\{N(8k+3):k\ge0\}.
\tag{154.18}
$$

Apply the exact sectorwise results 152.A–C on $X_{E,S_a}$. They supply six independent ordered functionals and exact surjectivity of the three diagonal quadratics after any finite homogeneous constraints. These are the original three pencils, with the original measure and operator. Their finite-dimensional sphere step is (147.6)–(147.8), as localized in (152.29).

More explicitly, for each $a\in I$ choose $y_a,h_{a,1},\ldots,h_{a,6}\in X_{E,S_a}$ with
$\ell_i(y_a)(h_{a,k})=\delta_{ik}$, where
$(\ell_i(w)(h))_{i=1}^6=(Q_r(h,w),Q_r(w,h))_{r\in\mathcal R}$.
Use (152.29) to choose an actual $z_a\in X_{E,S_a}$ satisfying

$$
\begin{gathered}
\ell_i(z_a)(h_{a,k})=0\quad(1\le i,k\le6),\qquad
 B_r(y_a,z_a)=0\quad(r\in\mathcal R),\\
q(z_a)=-q(v_a)-q(y_a),\qquad x_a=v_a+y_a+z_a.
\end{gathered}
\tag{154.19}
$$

Low and high sectors have zero ordered pair cross-pairings. Consequently

$$
q_r(x_a)=0,\qquad
\ell_i(x_a)(h_{a,k})=\delta_{ik},\qquad
Q_r(x_a,x_b)=0\quad(a\ne b).
\tag{154.20}
$$

All $x_a$ are bounded, supported in $E$, odd, and have finitely many angular frequencies. Their positive spectra lie respectively in
$\{n_0\}\cup S_0$, $\{n_1\}\cup S_1$ and $\{1,m_*\}\cup S_3$, which are pairwise disjoint.

The eight evaluations used in 154.B are preserved exactly. Every density in (154.10)–(154.11) is quadratic in its inputs, and multiplication by $g$ and application of $P$ preserve angular characters. A low/high product has absolute frequency at least $N-L>2L$. A high/high product has frequency a multiple of $N$, so its positive frequencies are at least $N$; its possible zero mode contributes to none of our evaluations. Every protected frequency is positive and at most $2L$. Thus all high correction terms have zero coefficients at every protected frequency, on both output orbits. In particular the seven rows $\mathbf R_\sigma[x]$, $\sigma\in\mathcal J$, retain rank seven under those evaluations.

They are bounded continuous two-component functions on $\Omega$, even with zero angular mean. Their Gram matrix

$$
\mathsf G_{\sigma\omega}
 =\int_G\bigl(R_\sigma^{(0)}[x]R_\omega^{(0)}[x]
             +R_\sigma^{(1)}[x]R_\omega^{(1)}[x]\bigr)dm
 \quad(\sigma,\omega\in\mathcal J)
\tag{154.21}
$$

is positive definite. A zero Gram quadratic form would make the corresponding combination zero in $L^2(m;\mathbb R^2)$. Continuity and full support on $\Omega$ would then make it zero pointwise there, contradicting the proved evaluation rank. Thus positive definiteness is established for these actual corrected inputs.

### 154.D. One exact stochastic point and all forty-three directions

Put $s=x_0+x_1+x_3$ and choose sufficiently small $t>0$ so that

$$
u_a^*=f_a^0+t x_a\quad(a\in I),\qquad
u_B^*=p-ts
\tag{154.22}
$$

has positive slack on $E$ in all four components. Outside $E$ it equals $f^0$. In particular its components $0,1,B$ have a uniform positive lower bound on $G$.

The marginal and pair equalities follow exactly as in (153.24)–(153.25): single odd terms integrate to zero, and all quadratic pair terms vanish by (154.20). For each permutation of $013$, the terms with one $x$ vanish by parity, those with two $x$ vanish by disjoint spectra through invariant factors, and the cubic term vanishes by simultaneous half-turn oddness. For BBB, (154.20) also gives $q_r(s)=0$ for every $r$. Conservation and source propagation give

$$
\begin{aligned}
\mathcal C(p-ts,p-ts,p-ts)
={}&p^3-p^2t\sum_{j=0}^2L_j(s)
       +pt^2\sum_{r\in\mathcal R}q_r(s)
       -t^3\mathcal C(s,s,s)\\
={}&p^3=\frac1{64}.
\end{aligned}
\tag{154.23}
$$

The linear and cubic terms vanish by oddness. Thus BBB is attained at this same stochastic point, together with all six orderings and all lower laws:

$$
\mathcal H_{43}(u^*)=\mathcal H_{43}(f^0)
                    =\mathcal H_{43}(f).
\tag{154.24}
$$

For the lower thirty-six rows reuse the directions of 153.D, with the $x_a$ of (154.19). Namely the nine invariant directions $\mathbf1_Eg_j$ in the respective components have three copies of the positive definite marginal matrix (153.26), using Lemma 147.2 and quotient analytic uniqueness. For each diagonal pair choose three odd directions in $X_{E,S_a}$ dual to the three sums of the ordered functionals in (154.20). For each unordered pair $\{a,b\}$ choose six odd directions in $X_{E,S_b}$ varying component $a$, dual to the six ordered functionals of $x_b$. The exact differential is (153.27). Disjoint spectra make these twenty-seven directions affect only their designated pair rows; their marginal rows vanish. Compensate every variation of $0,1,3$ in $B$. These thirty-six directions have an invertible lower thirty-six-row restriction. All their component-$3$ variations are supported in $E$.

For each $\omega\in\mathcal J$ add the direction

$$
\delta_\omega u_0=R_\omega^{(0)}[x],\qquad
\delta_\omega u_1=R_\omega^{(1)}[x],\qquad
\delta_\omega u_3=0,\qquad
\delta_\omega u_B=-R_\omega^{(0)}[x]-R_\omega^{(1)}[x].
\tag{154.25}
$$

For any even zero-mean two-component direction $h=(h_0,h_1)$ of this form, the lower thirty-six differentials vanish. In the pair rows, its invariant pairings vanish by zero angular mean and its odd pairings vanish by parity. Self-adjointness in the original $\mathcal C$ gives the six triple differentials

$$
D\mathcal C(u_y,u_z,u_w)[h]\big|_{u=u^*}
 =t^2\int_G(h_0R_{yzw}^{(0)}[x]+h_1R_{yzw}^{(1)}[x])\,dm
 \quad(yzw\in\mathcal T_6).
\tag{154.26}
$$

Indeed, varying a first, middle or terminal factor gives respectively $\mathsf A$, $\mathsf B$ or $\mathsf T$ of the other two inputs, exactly as listed in (154.10). The constant-in-$t$ term is invariant, and the linear-in-$t$ term is odd, so only the displayed quadratic density survives pairing with $h$.

For BBB the same expansion, with $\delta u_B=-h_0-h_1$, gives

$$
D\mathcal C(u_B,u_B,u_B)[h]\big|_{u=u^*}
 =-t^2\int_G(h_0+h_1)S[x]\,dm
 =t^2\int_G(h_0R_{BBB}^{(0)}[x]+h_1R_{BBB}^{(1)}[x])\,dm.
\tag{154.27}
$$

Its constant density is invariant, its linear density is odd, and zero angular mean permits replacement of $S$ by $\mathsf ZS$. Hence the last seven directions have the invertible seven-row block $t^2\mathsf G$. Together with the thirty-six earlier directions the full forty-three-row differential is block triangular with invertible diagonal blocks.

Choose bounded Borel representatives of all finitely many directions and inputs, with their finite angular representations on $\Omega$ and zero values on its null complement. Smoothed factors have the bounded continuous representatives described above. After one common Borel null repair all sums and slack inequalities hold pointwise. Component $3$ varies only on $E$, while the last seven directions vary just the globally positive components $0,1,B$. Therefore a closed Euclidean ball of positive radius in these forty-three directions consists entirely of pointwise simplex tuples on the whole original $G$.

### 154.E. Exact attainment at one finite common partition

Write these directions, including their compensating $B$ components, as $e_1,\ldots,e_{43}$, and put

$$
u(z)=u^*+\sum_{k=1}^{43}z_ke_k,\qquad
F(z)=\mathcal H_{43}(u(z))-\mathcal H_{43}(f),\qquad A=DF(0).
\tag{154.28}
$$

The polynomial $F$ has degree at most three, $F(0)=0$ and invertible $A$. Choose $\varepsilon>0$ so that its closed ball is legal as above and
$\sup_{\|z\|\le\varepsilon}\|z-A^{-1}F(z)\|<\varepsilon/3$; this follows from $F(z)=Az+O(\|z\|^2)$.

Apply the actual common-partition construction of 153.E to this ball. Explicitly, let $\mathcal P_n$ be increasing finite Borel partitions generated by a countable coordinate basis of the original $G$. In each positive-mass cell $A_0$, use its nested coordinate-quantile sets $A_0(v)$ with $m(A_0(v))=v$, $A_0(0)=\varnothing$ and $A_0(m(A_0))=A_0$. They exist because $m\ll\mu$ makes each first-coordinate hyperplane null, so the restricted coordinate distribution is continuous. Consecutive slices in the order $0,1,3,B$, of masses $\int_{A_0}u_y(z)\,dm$, give the cells of one common partition $D_n(z)$. Assign every zero-mass cell to $B$. This is a pointwise Borel partition of the whole original $G$ for every $z$ in the ball, and

$$
\sum_y m(D_{n,y}(z)\mathbin\triangle D_{n,y}(z'))
 \le6\sum_y\|u_y(z)-u_y(z')\|_1.
\tag{154.29}
$$

Use the original path density $W$ of (153.33), with its actual gap-$d$ heat kernels and slot marginals $g,Pg,P^2g$. Let $W_n$ be its conditional expectation on $\mathcal P_n^{\otimes3}$. These product partitions generate the product Borel sigma-algebra, so $\|W-W_n\|_1\to0$. Every coordinate of $\mathcal H_{43}$ is an integral against $W$ of a product of slot factors in $[0,1]$, with unused slots replaced by $1$. With $W_n$ the products factor cellwise, and the slice masses make the corresponding integrals for $u(z)$ and $\mathbf1_{D_n(z)}$ equal. Thus the actual maps

$$
F_n(z)=\mathcal H_{43}(\mathbf1_{D_n(z)})-\mathcal H_{43}(f)
\quad\text{satisfy}\quad
\sup_{\|z\|\le\varepsilon}\|F_n(z)-F(z)\|
 \le2\sqrt{43}\,\|W-W_n\|_1\longrightarrow0.
\tag{154.30}
$$

Each $F_n$ is continuous: telescope the products of indicators, integrate each changed indicator against its corresponding bounded slot marginal $g,Pg,P^2g$, and apply (154.29). Choose one finite $n$ for which the right-hand approximation error, multiplied by $\|A^{-1}\|$, is less than $\varepsilon/3$. Then $z\mapsto z-A^{-1}F_n(z)$ sends the closed radius-$\varepsilon$ ball into its radius-$2\varepsilon/3$ ball. Brouwer's finite-dimensional closed-ball theorem supplies a fixed point $z_n$. Consequently

$$
D=D_n(z_n),\qquad
\mathcal H_{43}(\mathbf1_D)=\mathcal H_{43}(f).
\tag{154.31}
$$

This is one actual partition at one finite $n$, evaluated throughout with its own propagated terminal indicators.

### 154.F. Complement recovery and the remaining full joint equations

The complement identities (152.45)–(152.46) recover every ordered pair involving $B$ from the fixed $I\times I$ pairs and source marginals of this same $D$. The identity
$L_j(\mathbf1_{D_B})=1-\sum_{a\in I}L_j(\mathbf1_{D_a})$
recovers its other three marginals. The last seven coordinates of (154.31) give all six distinct-label coefficients and BBB. Conservation gives $\mathcal C(p,p,p)=p^3=1/64$. Restoring the originally prescribed $b$ affects no target integral, because $b=b^0$ almost everywhere and all three original positive-time slot laws are absolutely continuous with respect to $m$. This proves (154.3) for every permitted representative.

For this same partition put
$\Delta_{yzw}=\mathcal C(\mathbf1_{D_y},\mathbf1_{D_z},\mathbf1_{D_w})-\mathcal C(f_y,f_z,f_w)$.
The pair laws imply $\Delta\in H_0^{\otimes3}$ as in Proposition 150.3. Complement expansion in all three slots therefore gives

$$
\Delta_{BBB}=-\sum_{a,b,c\in I}\Delta_{abc}=0,\qquad
\Delta_\sigma=0\quad(\sigma\in\mathcal T_6),\qquad
\sum_{\substack{a,b,c\in I\\\text{a repeated label occurs}}}\Delta_{abc}=0.
\tag{154.32}
$$

The twenty-one repeated-label ambient $I^3$ coordinates are not individually forced to zero by these equations. The last sum is a linear consequence of the jointly attained BBB coordinate; it asserts neither nonlinear independence nor feasibility of the remaining equations. In particular the full equation (153.3), the refined two-$B$ coordinates and the rank-two requirement remain outside the conclusion of this theorem. Every residual still uses $P\mathbf1_{D_w}$ from the one partition in (154.31).

The original-source inputs to this derivation are the exact correction and ordered-functional results 152.A–C, their consumed sphere argument (147.6)–(147.8), the orbit positivity (153.8)–(153.10), the proved folded rank (153.16), and the finite-partition construction 153.E. The classical intermediates in those reused correction results are R. Meshulam and P. Šemrl, *Locally linearly dependent operators*, [doi:10.2140/pjm.2002.203.441](https://doi.org/10.2140/pjm.2002.203.441), Theorem 2.2, and B. S. Mityagin, *The zero set of a real analytic function*, [arXiv:1512.07276v1](https://arxiv.org/abs/1512.07276v1), Proposition 0. The fixed-point intermediate is L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, [doi:10.1007/BF01456931](https://doi.org/10.1007/BF01456931), in its finite-dimensional closed-ball form. Their original hypotheses and the retained endpoint, source and analytic suppliers remain in force. The additional coattainment follows from the two-mode reversal separation (154.13)–(154.16), the BBB coefficient (154.17), their exact protected corrections and the single finite partition (154.31). $\square$

## 追加锚（本行以下为增补区）

## 155. Positive BB3 inputs, finite coupled improvement and source-ratio selection

**Definition 155.1 (the original full-law consumer and the calibrated fiber).** Retain the complete telescope of Definitions 134.1, 135.1 and 154.1, including all inherited endpoint, source and analytic suppliers of Appendix II §§115–117, 123–125 and 133. Thus $\theta=(a,\eta,d,b)$ ranges over every original finite $a,\eta,d>0$ and every permitted everywhere Borel representative $b$ of $g_d$ satisfying $0<b\le M$. The original product on $G=H^1\times\mathbb R$, raw Haar measure $\mu$, source $e$, unit-source field $L\Gamma=\delta_e$, coefficient-one $w_*$, coefficient-positive normalized $h$, actual full self-adjoint endpoint with selector $A_{\rm src}=\rho C_{\rm src}$, and full conservative source-inclusive $K$ are unchanged. Keep

$$
\begin{gathered}
m=h^2\mu,\qquad T_s=e^{-sK},\qquad P=T_d,\qquad
 g_j=P^jg=g_{(2+j)d}\ (j=0,1,2),\qquad g=g_{2d},\\
M=1+\|g_d\|_\infty,\qquad c=(4M)^{-1},\qquad p=\tfrac14,\\
f_3=cb,\qquad f_B=p,\qquad f_0=f_1=(\tfrac34-cb)/2,\\
\mathcal C(u,v,w)=\int_GguP(vPw)\,dm,\qquad
\Phi_3(u)=(\mathcal C(u_y,u_z,u_w))_{y,z,w\in\mathcal L},\qquad
\Delta(u)=\Phi_3(u)-\Phi_3(f),\quad \mathcal L=\{0,1,3,B\}.
\end{gathered}
\tag{155.1}
$$

The diffusion starts at the original $e$, with source law $g_{s+r}=T_rg_s$, epochs $2d,3d,4d$, and the same prescribed $f$ at all three epochs with conditionally independent fresh read noises. For a whole-$G$ pointwise Borel partition $D$, write $\Delta(D)=\Delta(\mathbf1_D)$ and $r(D)=\Delta(D)_{BB3}$. Its terminal factors are always its own $P\mathbf1_{D_w}$. Put

$$
\mathscr F_{154}(\theta)
 =\{D:\ D\text{ is such a partition and }
             \mathcal H_{43}(\mathbf1_D)=\mathcal H_{43}(f)\}.
\tag{155.2}
$$

By the complement identities in 154.F, membership means all twelve original source marginals, every ordered pair law at each pair of epochs, all six permutations of $013$, and BBB are exact. The governing universal target remains

$$
\forall\theta\quad F_{64}(\theta),\qquad
F_{64}(\theta):\ \exists D\text{ one whole-}G
 \text{ pointwise Borel partition with }\Delta(D)=0.
\tag{155.3}
$$

For two actual partitions let $A(D,D')$ be the Borel set where their labels differ. Set $G_0=\|g\|_\infty<\infty$; source propagation and Markov contraction give $\|g_j\|_\infty\le G_0$ for $j=0,1,2$.

**Theorem 155.2 (coupled actual endpoints with positive BB3 and controlled full-residual improvement).** Under exactly Definition 155.1, for every original $\theta$ there exist bounded Borel functions $X_y$, a number $t_0>0$, and a vector $R\in\mathbb R^{64}$ such that, with

$$
\mathfrak M=\sum_{y\in\mathcal L}\|X_y\|_1,\qquad
\kappa=R_{BB3}>0,\qquad J=\|R\|_\infty>0,
\tag{155.4}
$$

the following quantifiers hold. Here $t$ and $t'$ are readout amplitudes. For every $0<t<t_0$, every $0<\varepsilon<1$, and every

$$
t'=(1-\varepsilon)t,\qquad q_\varepsilon=2\varepsilon-\varepsilon^2,
\qquad
0<\delta<\tfrac14\min\{(t')^2\kappa,
                              q_\varepsilon t^2J\},
\tag{155.5}
$$

there exist actual $D,D'\in\mathscr F_{154}(\theta)$, co-selected by the same finite-cell quantile construction on the original $G$, satisfying

$$
\begin{gathered}
\|\Delta(D)-t^2R\|_\infty<\delta,\qquad
\|\Delta(D')-(t')^2R\|_\infty<\delta,\\
r(D)>t^2\kappa-\delta>0,\qquad
r(D')>(t')^2\kappa-\delta>0,\\
m(A(D,D'))\le3\varepsilon t\mathfrak M+\delta,\\
\|\Delta(D')\|_\infty
 \le\|\Delta(D)\|_\infty-q_\varepsilon t^2J+2\delta
 <\|\Delta(D)\|_\infty-\tfrac12q_\varepsilon t^2J.
\end{gathered}
\tag{155.6}
$$

In particular, the improvement concerns the norm of the complete sixty-four-coordinate residual. More precisely,

$$
\|\Delta(D')-(1-\varepsilon)^2\Delta(D)\|_\infty
 <\bigl(1+(1-\varepsilon)^2\bigr)\delta.
\tag{155.7}
$$

All constants may depend on $\theta$ and the selected original-space functions. No parameter-uniform inverse estimate is part of the assertion.

*Proof.* Use the actual corrected functions $x_0,x_1,x_3$ from (154.19)–(154.21), with their invariant slack set $E$ and invariant representative $f^0$. They are bounded Borel, supported in $E$, odd under the original half-turn, and have disjoint positive angular spectra. They satisfy

$$
q_r(x_a)=0,\qquad Q_r(x_a,x_b)=0\quad(a\ne b),
\qquad r\in\{12,13,23\}.
\tag{155.8}
$$

Retain also the seven-column Gram nonsingularity in (154.21) and the thirty-six lower directions of 154.D. Define

$$
s=x_0+x_1+x_3,\qquad
X_a=x_a\ (a=0,1,3),\quad X_B=-s,\qquad
u^{(\tau)}=f^0+\tau X.
\tag{155.9}
$$

Choose $t_0>0$ small enough that every $0\le\tau\le t_0$ gives a pointwise simplex tuple, with a common positive lower bound for its components $0,1,B$ on $G$ and for component $3$ on $E$. This follows from (154.4), boundedness, and the support of the $X_y$ in $E$. All identities of classes may be made pointwise on a common Borel conull set and repaired on its complement as in 154.D.

For every coordinate, expansion of the original trilinear form has zero linear term: each such term contains one odd function and otherwise invariant factors. Its cubic term also vanishes, since all three $X$ factors are odd and the original measure, $g$ and $P$ are half-turn invariant. Consequently

$$
\Delta(u^{(\tau)})=\tau^2R,\qquad
R_{yzw}=\mathcal C(X_y,X_z,f_w^0)
       +\mathcal C(X_y,f_z^0,X_w)
       +\mathcal C(f_y^0,X_z,X_w).
\tag{155.10}
$$

The marginal, pair, six distinct-label and BBB equalities in (154.20), (154.23)–(154.24) hold for every such $\tau$. Thus $\mathcal H_{43}(u^{(\tau)})=\mathcal H_{43}(f)$. The invariance and disjoint-spectrum cancellations used there do not select a single value of $\tau$.

Here $s\ne0$: its frequency-$n_0$ component is the nonzero low-frequency input $v_0$ of (154.8), which occurs in neither of the other two functions or their high corrections. Source propagation gives $Pf_3^0=cg$. Hence (155.8) gives the following actual stochastic coefficient, before any partition approximation:

$$
\begin{aligned}
R_{BB3}
 &=\mathcal C(s,s,f_3^0)
       -p\mathcal C(s,1,x_3)-p\mathcal C(1,s,x_3)\\
 &=c\langle gs,P(gs)\rangle_m
       -pQ_{13}(s,x_3)-pQ_{23}(s,x_3)\\
 &=c\|T_{d/2}(gs)\|_2^2=:\kappa>0.
\end{aligned}
\tag{155.11}
$$

The last inequality uses $g>0$ almost everywhere, $s\ne0$, and the injective full self-adjoint heat operator of (134.17)–(134.18). The two ordered pair terms vanish because each summand is either a diagonal term or a disjoint-spectrum term in (155.8). This is the source-specific positive coefficient of §134 applied to $s$; it asserts no coercive lower bound.

Fix $t,\varepsilon,\delta$ as in the statement. The forty-three bounded directions $e_k$ of (154.25)–(154.28) can be chosen once from these fixed $x_a$, independently of $\tau>0$. For

$$
u_\tau(z)=u^{(\tau)}+\sum_{k=1}^{43}z_ke_k,\qquad
F_\tau(z)=\mathcal H_{43}(u_\tau(z))-\mathcal H_{43}(f),\qquad
A_\tau=DF_\tau(0),
\tag{155.12}
$$

$A_\tau$ is invertible for every $0<\tau<t_0$. Indeed the marginal block is the same invertible source Gram block, the twenty-seven pair-direction block is $\tau$ times its fixed invertible block, and the final seven-direction block is $\tau^2\mathsf G$. The off-diagonal blocks do not alter the block triangular argument of 154.D. Component-$3$ directions remain supported in $E$, so each center has a legal closed ball in these directions.

Use Euclidean norm on $\mathbb R^{43}$ and choose a finite $B>0$ with

$$
\sum_y\left\|\sum_kz_ke_{k,y}\right\|_1\le B\|z\|.
\tag{155.13}
$$

Choose one sufficiently small radius $r>0$ for both centers $\tau=t,t'$ such that their closed balls are legal,

$$
6Br<\delta,\qquad 3G_0Br<\delta/2,\qquad
\sup_{\|z\|\le r}\|z-A_\tau^{-1}F_\tau(z)\|<r/3
 \quad(\tau=t,t').
\tag{155.14}
$$

The last inequalities follow from $F_\tau(0)=0$ and its invertible derivative at each of the two fixed positive centers. No common lower bound as $t'$ tends to zero has been assumed.

Apply exactly the common coordinate-quantile construction of 154.E, using the same finite partitions $\mathcal P_n$, the same nested cuts in each cell, and the same order $0,1,3,B$ for both balls. Denote this common rounding map by $\mathcal D_n(u)$. It satisfies

$$
\begin{gathered}
m(A(\mathcal D_n(u),\mathcal D_n(v)))
 =\tfrac12\sum_y m(\mathcal D_{n,y}(u)\mathbin\triangle
                                      \mathcal D_{n,y}(v))
 \le3\sum_y\|u_y-v_y\|_1,\\
\|\Phi_3(\mathbf1_{\mathcal D_n(u)})-\Phi_3(u)\|_\infty
 \le2\|W-W_n\|_1,\\
\|\mathcal H_{43}(\mathbf1_{\mathcal D_n(u)})
                         -\mathcal H_{43}(u)\|_2
 \le2\sqrt{43}\,\|W-W_n\|_1.
\end{gathered}
\tag{155.15}
$$

The first estimate is (154.29) divided by two. For the other two estimates, with the original path density $W$ and its cellwise conditional expectation $W_n$, the integrals against $W_n$ agree by the four cell masses, for every slot product in question. Replacing $W_n$ by $W$ costs at most $2\|W-W_n\|_1$ per coordinate. This applies to all sixty-four triple coordinates, as well as the forty-three calibrated coordinates. These bounds are uniform over both balls, and $\|W-W_n\|_1\to0$.

Choose one finite $n$ so large that

$$
2\|W-W_n\|_1<\delta/2,\qquad
2\sqrt{43}\max_{\tau=t,t'}\|A_\tau^{-1}\|\,
                     \|W-W_n\|_1<r/3.
\tag{155.16}
$$

For each center let $F_{n,\tau}(z)=\mathcal H_{43}(\mathbf1_{\mathcal D_n(u_\tau(z))})-\mathcal H_{43}(f)$. The same continuity argument as in 154.E makes these actual maps continuous. By (155.14)–(155.16), $z\mapsto z-A_\tau^{-1}F_{n,\tau}(z)$ maps the closed radius-$r$ ball into itself. Brouwer supplies roots $z_t,z_{t'}$ in that ball. Put

$$
D=\mathcal D_n(u_t(z_t)),\qquad
D'=\mathcal D_n(u_{t'}(z_{t'})).
\tag{155.17}
$$

They are pointwise Borel partitions of all of the original $G$, exact for $\mathcal H_{43}$. Each is evaluated against the original $W$, hence with its own propagated terminal indicators.

For any two legal simplex tuples, telescoping the three factors against $W$ bounds one coefficient difference by

$$
\int g_0|u_y-v_y|\,dm+
\int g_1|u_z-v_z|\,dm+
\int g_2|u_w-v_w|\,dm
 \le3G_0\sum_a\|u_a-v_a\|_1.
\tag{155.18}
$$

Equations (155.13)–(155.16) and (155.18) give the two residual approximations in (155.6). The first line of (155.15) gives

$$
m(A(D,D'))\le3\bigl(\varepsilon t\mathfrak M
                         +B\|z_t\|+B\|z_{t'}\|\bigr)
 <3\varepsilon t\mathfrak M+\delta.
\tag{155.19}
$$

The positive BB3 bounds and (155.7) follow from (155.10)–(155.11) and these approximations. Finally $\|\Delta(D)\|_\infty\ge t^2J-\delta$ and $\|\Delta(D')\|_\infty\le(t')^2J+\delta$ prove the improvement in (155.6). Restoring the originally given representative $b$ changes no target integral, by the original positive-time absolute continuity. $\square$

**Theorem 155.3 (the exact source-ratio donor identity and a necessary selection cost).** Retain Definition 155.1. Let $D\in\mathscr D_{12}(\theta)$ satisfy $r(D)>0$. For every actual whole-$G$ pointwise Borel partition $D^*$ satisfying $\Delta(D^*)=0$, define the coarse cells

$$
E_S=D_0\cup D_1,\quad E_3=D_3,\quad E_B=D_B,
\qquad
E_S^*=D_0^*\cup D_1^*,\quad E_3^*=D_3^*,\quad E_B^*=D_B^*.
\tag{155.20}
$$

For $k=0,1,2$ put $\nu_k(A)=\int_Ag_k\,dm$ and $\bar g=(g_0+g_1+g_2)/3$. These are the original three source marginals and their bookkeeping average; every joint coefficient remains the original integral (155.1). Write

$$
\begin{gathered}
t_r=\int_Gg_{rd}f_3\,dm\quad(r=2,3,4),\qquad
\bar t=(t_2+t_3+t_4)/3,\\
\pi_i=\int_{E_i}\bar g\,dm,\qquad
\rho_i^{(k)}=\nu_k(E_i)/\pi_i\quad(i=S,3,B),\\
T_{ij}=\int_{E_i\cap E_j^*}\bar g\,dm,\qquad
Z_{ij}^{(k)}=\nu_k(E_i\cap E_j^*)-\rho_i^{(k)}T_{ij}.
\end{gathered}
\tag{155.21}
$$

The row reference is always the original donor $E_i$. The exact table identities are

$$
\begin{gathered}
\sum_jT_{ij}=\pi_i,\qquad \sum_iT_{ij}=\pi_j,\qquad
\sum_jZ_{ij}^{(k)}=0,\\
\sum_i\bigl(\rho_i^{(k)}T_{ij}+Z_{ij}^{(k)}\bigr)
        =\rho_j^{(k)}\pi_j,\\
\sum_{i,j}(\rho_i^{(k)}-\rho_j^{(k)})^2T_{ij}
 =2\sum_{i,j}(\rho_j^{(k)}-\rho_i^{(k)})Z_{ij}^{(k)}
 \quad(k=0,1,2).
\end{gathered}
\tag{155.22}
$$

In particular put $\rho_i=\rho_i^{(0)}$. Their source-specific values obey

$$
\begin{gathered}
\pi_3=\bar t,\quad \pi_B=\tfrac14,\quad \pi_S=\tfrac34-\bar t,\\
\rho_3=t_2/\bar t>1=\rho_B>
 \rho_S=(\tfrac34-t_2)/(\tfrac34-\bar t),\\
\gamma=\min\{\rho_3-1,1-\rho_S\}>0,\qquad
\mathfrak d_\rho=\rho_3-\rho_S>0.
\end{gathered}
\tag{155.23}
$$

Let $A_c$ be the set where $D,D^*$ have different coarse labels in $\{S,3,B\}$. Every such exact correction must pay

$$
\begin{gathered}
\mathfrak S(D,D^*):=\sum_{i\ne j}|Z_{ij}^{(0)}|
 \ge\frac{\gamma^2}{2\mathfrak d_\rho}\int_{A_c}\bar g\,dm
 \ge\frac{\gamma^2}{6\mathfrak d_\rho}\,r(D)>0,\\
 m(A_c)\ge\frac{r(D)}{3G_0}>0.
\end{gathered}
\tag{155.24}
$$

Thus nonproportional selection across coarse labels is necessary. The conclusion applies to every exact full correction, with no restriction on its direction, support, number of pieces or construction.

*Proof.* Summing a full law over its other two labels gives each of its three original source marginals. Therefore $D^*\in\mathscr D_{12}(\theta)$. In fact the table identities (155.22) hold for any two members of $\mathscr D_{12}(\theta)$, independently of their pair or triple laws. Additivity of the intersections gives the first two lines. For fixed $k$, abbreviate $\rho_i^{(k)}$ to $a_i$ and $Z_{ij}^{(k)}$ to $Z_{ij}$. Expansion of the square, the two table margins, and the recipient equations give

$$
\begin{aligned}
\sum_{i,j}(a_i-a_j)^2T_{ij}
 &=2\sum_j a_j^2\pi_j-2\sum_j a_j\sum_i a_iT_{ij}\\
 &=2\sum_{i,j}a_jZ_{ij}
 =2\sum_{i,j}(a_j-a_i)Z_{ij}.
\end{aligned}
\tag{155.25}
$$

The last equality uses the zero row sums of $Z$. This is the elementary finite-table variance identity; its general algebra is a classical intermediate, not an additional source theorem.

Proposition 135.2 gives $0<t_4<t_3<t_2\le1/4$ for every original tuple. The prescribed source masses of $3,B,S$ at epoch $rd$ are $t_r,1/4,3/4-t_r$. These facts give (155.23), with positive denominators and three distinct ratios. Hence the $k=0$ identity in (155.22) yields

$$
\gamma^2\sum_{i\ne j}T_{ij}
 \le\sum_{i,j}(\rho_i-\rho_j)^2T_{ij}
 \le2\mathfrak d_\rho\sum_{i\ne j}|Z_{ij}^{(0)}|.
\tag{155.26}
$$

The off-diagonal table mass is exactly $\int_{A_c}\bar g\,dm$.

The input and corrected BB3 coefficients differ by $r(D)$. Telescoping their three actual indicator factors against the original $W$ bounds that difference by the probability of a changed $B$ label in the first slot, a changed $B$ label in the second, or a changed $3$ label in the third. Each changed set is contained in $A_c$. Thus

$$
0<r(D)\le\nu_0(A_c)+\nu_1(A_c)+\nu_2(A_c)
             =3\int_{A_c}\bar g\,dm\le3G_0m(A_c).
\tag{155.27}
$$

This proves (155.24). Every factor used in this telescoping is the actual partition indicator for its own slot; the calculation neither fixes an external terminal nor substitutes $cg$ for $P\mathbf1_{D_3^*}$.

If transfers preserve the original donor source profiles, in the precise sense

$$
\nu_k(E_i\cap E_j^*)=\rho_i^{(k)}T_{ij}
       \quad(i,j=S,3,B;\ k=0,1,2),
\tag{155.28}
$$

then $Z=0$, so (155.26) forces every off-diagonal $T_{ij}$ to vanish. Already preservation of the single $k=0$ ratio in (155.28) suffices. Since $\bar g>0$ almost everywhere, $E_B^*=E_B$ and $E_3^*=E_3$ modulo $m$. Their own propagated indicators and their BB3 coefficient are consequently unchanged. Such transfers cannot repair this positive-BB3 input.

The same exclusion holds if “preserving the donor source ratio” refers just to the native ratio of epochs $3d$ and $2d$. Indeed these donor ratios are

$$
\widetilde\rho_3=t_3/t_2<1=\widetilde\rho_B<
 \widetilde\rho_S=(\tfrac34-t_3)/(\tfrac34-t_2).
\tag{155.29}
$$

Apply (155.25) with $T_{ij}$ replaced by $\nu_0(E_i\cap E_j^*)$, margins $\nu_0(E_i)$, and errors $\nu_1(E_i\cap E_j^*)-\widetilde\rho_i\nu_0(E_i\cap E_j^*)$. If all those errors vanish, the distinct ratios again force all off-diagonal masses to vanish. Equivalence of $\nu_0$ and $m$ gives the same conclusion. Null modifications of a partition remain possible, and affect none of the original positive-time laws.

Finite proportional subdivisions of a donor under the three measures $\nu_k$ are the linear operation supplied by Dvoretzky–Wald–Wolfowitz, *Relations among certain ranges of vector measures*, [DOI 10.2140/pjm.1951.1.59, §3 Theorem 4 and Lemma 2, pp. 66–67](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf). Their finite atomless-measure hypotheses hold on every donor, since $\nu_k\ll m\ll\mu$. When a transfer uses one common fraction for all three measures, it satisfies (155.28). The obstruction above concerns combining such transfers with preservation of all recipient source masses and repair of the positive BB3 coefficient; DWW itself prescribes only linear integrals. $\square$

**Corollary 155.4 (the coupled full-law obligation).** For every original $\theta$ and every choice of the endpoints in Theorem 155.2, each hypothetical exact full correction $D^*$ of its selected input $D$ satisfies the exact donor identity (155.22) and

$$
\mathfrak S(D,D^*)>
 \frac{\gamma^2}{6\mathfrak d_\rho}(t^2\kappa-\delta)>0.
\tag{155.30}
$$

Both endpoints are genuinely partially calibrated inputs with their own terminals: they have positive BB3 residual and a strict finite improvement in the complete residual norm, and neither is a full $F_{64}$ witness. No assertion is made that an arbitrary nonproportional table is realizable as a full correction, or that paying this necessary cost suffices.

For the selected input $D$, a sufficient remaining obligation for the original $F_{64}(\theta)$ is a sequence of actual partitions $D_n\in\mathscr F_{154}(\theta)$, starting at $D_1=D$, such that

$$
\|\Delta(D_n)\|_\infty\longrightarrow0,\qquad
\sum_{n=1}^{\infty}m(A(D_n,D_{n+1}))<\infty.
\tag{155.31}
$$

Under (155.31) there is one whole-$G$ pointwise Borel partition $D_\infty$ attaining the full original law, and

$$
m(A(D_n,D_\infty))\le
 \sum_{k=n}^{\infty}m(A(D_k,D_{k+1})).
\tag{155.32}
$$

The quantifiers of Theorem 155.2 co-select $D$ and $D'$ after $t,\varepsilon,\delta$ and a common finite refinement have been chosen. They do not supply a successor starting at a previously fixed actual $D$, or a sequence satisfying (155.31). The lower selection cost (155.24) is necessary for an exact repair; it does not assert that such costs fail to be summable.

*Proof.* Apply Theorem 155.3 to (155.6). Positivity of BB3 excludes exact full-law equality for either endpoint. Theorem 155.3 quantifies over every actual full correction, so its conditional necessity does not require the existence of one.

The measure of the union of the change sets from index $n$ onward is at most the right side of (155.32). Finiteness of the series makes the limsup of those sets null. Outside that Borel null set the finite-valued labels are eventually constant. Their eventual values define Borel cells; assign $B$ on the exceptional set to obtain one pointwise partition of all of $G$. This proves (155.32). For any pair of actual partitions $E,F$, telescoping as in (155.27) gives

$$
\|\Phi_3(\mathbf1_E)-\Phi_3(\mathbf1_F)\|_\infty
 \le3G_0m(A(E,F)).
\tag{155.33}
$$

Thus (155.31)–(155.32) imply $\Delta(D_\infty)=0$, with its own propagated terminals. The same argument for one-slot and two-slot products preserves the calibrated equalities. The finite construction in Theorem 155.2 gives two roots in one newly chosen rounding family; neither root is required to equal any partition fixed before that family was selected. Consequently iteration from an existing endpoint is an additional obligation, even when the numerical upper bounds $\varepsilon t$ could be chosen summably.

Theorem 146.1 supplies actual $\mathscr D_{12}$ partitions of exact rank two, with all four exact terminal contrasts and full-law error tending to zero. It supplies no positive-BB3 hypothesis, and is not required to lie in $\mathscr F_{154}$. The necessity in Theorem 155.3 therefore gives no uniform residual floor on $\mathscr D_{12}$ and no obstruction to those §146 partitions. The universal exact target (155.3) and a fixed-start summable correction chain remain unresolved by these results.

The source-specific composition (155.11), (155.17)–(155.19) and (155.23)–(155.27) is repository-derived relative to the retained conditional suppliers. The spectral positivity is the existing §134 result, the regular directions and finite partition mechanism are those of §§147 and 154, and the fixed-point intermediate is the finite-dimensional closed-ball form of Brouwer, [*Über Abbildung von Mannigfaltigkeiten*, DOI 10.1007/BF01456931](https://doi.org/10.1007/BF01456931). These classical tools and the finite-table variance calculation are consumed within this source application; no historical novelty is asserted for them. The eventual-label limit uses the elementary summable-set argument within this full-law consumer. $\square$

## 追加锚（本行以下为增补区）

## 156. The repeated-label rank boundary and the corrected finite completion route

**Definition 156.1 (the repeated-label residual map).** Retain the original telescope, the whole-$G$ partition space and the calibrated fiber $\mathscr F_{154}(\theta)$ of Definition 155.1. Let

$$
\mathcal R_{\mathrm{rep}}
 =\{(y,z,w)\in I^3:\text{ at least two of }y,z,w\text{ are equal}\},
 \qquad |\mathcal R_{\mathrm{rep}}|=21.
\tag{156.1}
$$

For $D\in\mathscr F_{154}(\theta)$ write

$$
\Gamma_\theta(D)
 =\bigl(\Delta(D)_{yzw}\bigr)_{(y,z,w)\in\mathcal R_{\mathrm{rep}}}
 \in\mathbb R^{21}.
\tag{156.2}
$$

The six distinct-label coordinates, BBB, all source marginals and all ordered pair coordinates are already fixed on this fiber. Every coordinate in (156.2) still uses the same partition's own terminal factor $P\mathbf1_{D_w}$.

**Proposition 156.2 (one exact relation removes one repeated-label row).** Under the unchanged hypotheses of Definition 156.1, every $D\in\mathscr F_{154}(\theta)$ satisfies

$$
\sum_{\rho\in\mathcal R_{\mathrm{rep}}}\Gamma_\theta(D)_\rho=0.
\tag{156.3}
$$

Consequently the repeated-label residuals on the exact $\mathcal H_{43}$ fiber take values in the twenty-dimensional hyperplane

$$
V_{20}=\left\{q\in\mathbb R^{21}:\sum_{\rho\in\mathcal R_{\mathrm{rep}}}q_\rho=0\right\}.
\tag{156.4}
$$

In particular, no local family that remains in the exact $\mathcal H_{43}$ fiber can have a $21\times21$ Jacobian from its parameters onto all twenty-one repeated-label coordinates.

*Proof.* Equation (154.32) is obtained by expanding the complement $u_B=1-\sum_{a\in I}u_a$ in the three slots. On $\mathscr F_{154}(\theta)$ the pair residuals vanish, the six distinct-label residuals vanish, and the BBB residual vanishes. The remaining term in that complement expansion is exactly the sum in (156.3). Thus every differentiable or polynomial family in the fiber has differential in $V_{20}$, whose dimension is twenty. The conclusion is a rank bound and does not use a choice of coordinates, a rounding construction or a parameterization of the family. $\square$

The rank bound is a route boundary rather than a negative result for the original target. It shows that a proposed $21$-row Schur-complement determinant would be identically singular for the structural reason (156.3). One repeated-label coordinate must be recovered from the other twenty after the calibrated equations have been solved.

**Route condition 156.3 (SRS-20 finite repeated-label completion).** Fix one $\rho_\ast\in\mathcal R_{\mathrm{rep}}$ and put

$$
\mathcal R_\ast=\mathcal R_{\mathrm{rep}}\setminus\{\rho_\ast\}.
\tag{156.5}
$$

A source-specific finite completion certificate for an original $\theta$ consists of a bounded invariant slack set $E$, a positive Section 155 ray $X$, a number $t_\theta>0$, a closed ball $B_{20}\subset\mathbb R^{20}$ centered at $0$ with positive radius, and pointwise simplex tuples $u^{(t,z)}$ on the original $G$, for $0<t<t_\theta$ and $z\in B_{20}$, such that

$$
\begin{aligned}
&u^{(t,0)}=f^0+tX,\qquad
  \mathcal H_{43}(u^{(t,z)})=\mathcal H_{43}(f^0),\\
&t^{-2}\bigl(\Delta_{\mathcal R_\ast}(u^{(t,z)})\bigr)
   =r_{\theta,\ast}+S_\theta z+\varepsilon_\theta(t,z),\\
&\sup_{z\in B_{20}}\|\varepsilon_\theta(t,z)\| \longrightarrow0
\quad(t\downarrow0),
 \qquad \det S_\theta\ne0.
\end{aligned}
\tag{156.6}
$$

Here $\Delta_{\mathcal R_\ast}$ is evaluated with the original trilinear form and the common tuple in all three slots. The certificate must also supply a closed-ball degree or boundary estimate that places a zero of the finite map in $B_{20}$; invertibility of $S_\theta$ by itself is not such a degree estimate. Its legal perturbations must preserve the original source marginals, the pointwise simplex inequalities and the actual terminal convention throughout the ball. The constants and the choice of the omitted row may depend on $\theta$, but the original $G$, $m$, $P$, $g$, epochs, source law, readout and permitted representative $b$ may not change.

The intended algebraic mechanism is finite-dimensional. A zero of the twenty rows in (156.6), together with the exact $\mathcal H_{43}$ equations, gives sixty-three exact coordinates. Proposition 156.2 then recovers the omitted $\rho_\ast$ coordinate. Proposition 150.3 and its three-slot complement expansion (150.13) recover every coordinate containing $B$, so all sixty-four ordered equations follow for the same whole-$G$ tuple.

**Proposition 156.4 (what an actual-partition realization must add).** Suppose the certificate of Route condition 156.3 is available with a same-dimensional finite-cell realization as follows. There are an admissible $t\in(0,t_\theta)$ and an index $n_0$ such that, for every $n\ge n_0$ and $z\in B_{20}$, a finite Borel partition $D_{n,t}(z)$ of the original $G$ is obtained from one common quantile construction, its four cells are Borel, pairwise disjoint and cover $G$, and

$$
\mathcal H_{43}(\mathbf1_{D_{n,t}(z)})=\mathcal H_{43}(f)
\quad\text{for every }z\in B_{20}.
\tag{156.7}
$$

The remaining-coordinate map

$$
R_{n,t}(z)=t^{-2}\Delta_{\mathcal R_\ast}(\mathbf1_{D_{n,t}(z)})
\colon B_{20}\longrightarrow\mathbb R^{20}
\tag{156.8}
$$

is continuous for each $n$ and converges uniformly on $B_{20}$, as $n\to\infty$ with this fixed $t$, to the fractional map

$$
t^{-2}\Delta_{\mathcal R_\ast}(u^{(t,z)})
 =r_{\theta,\ast}+S_\theta z+\varepsilon_\theta(t,z).
$$

Assume in addition that one selected $n\ge n_0$ has a boundary or degree estimate for this $20\to20$ map, for example that $R_{n,t}$ is nonzero on $\partial B_{20}$ and has nonzero degree at $0$ relative to $B_{20}$. Uniform approximation alone does not supply this estimate; it is part of the finite completion certificate. Then one actual whole-$G$ Borel partition $D_{n,t}(z_0)$ has all twenty coordinates in $\mathcal R_\ast$ exact for some $z_0\in B_{20}$, and (156.3) and the complement identities give

$$
\Delta(D_{n,t}(z_0))=0.
\tag{156.9}
$$

*Proof.* The exact $\mathcal H_{43}$ condition removes those forty-three coordinates before the degree argument, so $R_{n,t}$ has equal-dimensional domain and codomain. The boundary or degree hypothesis therefore gives $R_{n,t}(z_0)=0$ by the finite-dimensional argument used in Section 154.E. The resulting partition is produced by one common quantile construction, so every slot uses its own indicator and propagated terminal. Equation (156.3) supplies the omitted repeated coordinate, while Proposition 150.3 and (150.13) recover the coordinates containing $B$. No weak fractional limit is substituted for this finite actual partition. $\square$

The two propositions isolate the unpaid bridge without changing the original problem. The remaining proof obligations are the existence of the invariant reservoir and twenty legal perturbation directions, the weighted Schur-complement determinant and its nonlinear remainder estimate, pointwise simplex legality, an exact-$\mathcal H_{43}$ finite-cell family with the stated continuity and boundary estimate, and preservation of the actual terminal factors. A quantile realization that only makes the $\mathcal H_{43}$ coordinates small gives a $20\to43+20$ residual map and is insufficient by itself; it would require a separate $63$-parameter calibration theorem. A failure of any one of these conditions for one permitted $\theta$ falsifies this SRS-20 route only; it does not refute $F_{64}(\theta)$ or the universal target.

The fixed-start summable continuation of Corollary 155.4 remains an independent sufficient route. It is not implied by (156.6), and it is not needed if the finite actual completion succeeds. Conversely, failure of the finite rank certificate leaves the fixed-start route open. The scalar four-score contrast and finite-horizon tests described in the proportional-containment advisory provide a diagnostic for candidate families, but they do not supply the source-specific rank or the actual finite partition required here.

## 追加锚（本行以下为增补区）
## 157. Two zero contrast channels and the quadratic rank boundary

**Definition 157.1 (the original affine readout and its zero channels).** Retain the complete original supplier telescope of Definition 155.1, the same trilinear form $\mathcal C$, the same readout $f$ and the exact $\mathcal H_{43}$ calibration of Sections 154 and 156. The calibration notation also applies to bounded Borel pointwise simplex tuples $u=(u_y)_{y\in\mathcal L}$ on the original $G$, with the same tuple in all three slots. Put

$$
\begin{gathered}
V=\mathbb R^{\mathcal L},\qquad
s(v)=\sum_{y\in\mathcal L}v_y,\qquad H=\ker s,\\
a=(3/8,3/8,0,1/4),\qquad
q=(-c/2,-c/2,c,0),\qquad f(x)=a+b(x)q,\\
\Lambda(v)=\bigl(v_0-v_1,\ v_B-\tfrac14s(v)\bigr),
\qquad \pi=\Lambda|_H.
\end{gathered}
\tag{157.1}
$$

The two components of $\Lambda(f)$ vanish pointwise, including for the originally prescribed representative $b$. For a simplex tuple $u$, their actual values are

$$
\eta_1(u)=u_0-u_1,\qquad \eta_2(u)=u_B-\tfrac14.
\tag{157.2}
$$

These are linear combinations of the same four readout channels, not new observations, independent noises or a changed terminal. The restriction $\pi:H\to\mathbb R^2$ is onto and has kernel $\mathbb Rq$. Indeed $\pi(v)=0$ on $H$ means $v_0=v_1$, $v_B=0$ and $v_3=-2v_0$, while $c>0$.

**Proposition 157.2 (the thirteen-dimensional quadratic limit).** Fix any original $\theta$. Let $B$ be a positive-radius closed ball in a finite-dimensional parameter space. For $0<t<t_0$ and $z\in B$, suppose that $u^{(t,z)}$ is a bounded Borel pointwise simplex tuple satisfying

$$
\mathcal H_{43}(u^{(t,z)})=\mathcal H_{43}(f).
\tag{157.3}
$$

Assume that there is a finite constant $K$ such that

$$
\sup_{z\in B}\max_{y\in\mathcal L}
\|u_y^{(t,z)}-f_y\|_{L^\infty(m)}\le Kt,
\tag{157.4}
$$

and that the full finite-dimensional residual has a uniform quadratic limit

$$
\sup_{z\in B}
\|t^{-2}\Delta(u^{(t,z)})-Q(z)\|\longrightarrow0.
\tag{157.5}
$$

Then every $Q(z)$ belongs to the fixed linear space

$$
\begin{aligned}
\mathcal W
 &=q\otimes H\otimes H+H\otimes q\otimes H
                         +H\otimes H\otimes q,\\
\mathcal W_{13}
 &=\{R\in\mathcal W:R_\sigma=0
                         \text{ for all }\sigma\in\mathcal T_6\},\\
\dim\mathcal W&=19,\qquad \dim\mathcal W_{13}=13.
\end{aligned}
\tag{157.6}
$$

The dimension is that of a containing linear space. The proposition does not assert that all thirteen directions are realized by legal source-specific tuples.

*Proof.* The exact marginal and ordered-pair coordinates in (157.3), completed with the simplex identities in the slots, give all pair equalities, including those involving $B$. For example the two marginal densities of $Q_{12}$ are $g,Pg$, those of $Q_{13}$ are $g,P^2g$, and those of $Q_{23}$ are $Pg,P^2g$. Therefore every one-index contraction of $\Delta(u^{(t,z)})$ vanishes. The same calculation as Proposition 150.3, which uses only the simplex sums and multilinearity, gives

$$
\Delta(u^{(t,z)})\in H^{\otimes3}.
\tag{157.7}
$$

Write $\delta=u-f$. Because $\Lambda f=0$ pointwise, the exact three-channel projection is

$$
\begin{aligned}
\bigl(\Lambda^{\otimes3}\Delta(u)\bigr)_{\alpha\beta\gamma}
 &=\mathcal C\bigl((\Lambda\delta)_\alpha,
                   (\Lambda\delta)_\beta,
                   (\Lambda\delta)_\gamma\bigr),\\
&\hspace{30mm}\alpha,\beta,\gamma\in\{1,2\}.
\end{aligned}
\tag{157.8}
$$

The original Markov contraction and $\int g\,dm=1$ give

$$
|\mathcal C(v_1,v_2,v_3)|
 \le\|v_1\|_\infty\|v_2\|_\infty\|v_3\|_\infty.
\tag{157.9}
$$

On $H$, $(\Lambda\delta)_1=\delta_0-\delta_1$ and $(\Lambda\delta)_2=\delta_B$. Thus (157.4) implies the uniform bound

$$
\sup_{z\in B}\|\Lambda^{\otimes3}
                 \Delta(u^{(t,z)})\|_{\max}
 \le8K^3t^3.
\tag{157.10}
$$

Equations (157.5), (157.7) and (157.10) show that
$Q(z)\in\ker(\pi^{\otimes3})$. Choose any linear complement $U$ of $\mathbb Rq$ in $H$. The tensor decomposition of
$H=\mathbb Rq\oplus U$ shows that this kernel is exactly the sum of the seven tensor summands having at least one $q$ slot. The only surviving quotient summand is $U^{\otimes3}$, of dimension eight. Hence the kernel is $\mathcal W$ and has dimension $27-8=19$.

Every tensor in $\mathcal W$ has zero BBB coordinate because $q_B=0$. The six coordinate restrictions indexed by $\mathcal T_6$ are independent on $\mathcal W$. To see this, put $h_i=e_i-e_B$ for $i\in I$. If a functional
$\ell=\sum_{\{i,j,k\}=I}\lambda_{ijk}[ijk]$ vanishes on $\mathcal W$, evaluate it on $q\otimes h_j\otimes h_k$ for each ordered pair of distinct $j,k\in I$. With $i$ the remaining label, exactly one summand survives:

$$
0=\ell(q\otimes h_j\otimes h_k)=q_i\lambda_{ijk}.
\tag{157.11}
$$

All three $q_i$ are nonzero, so all six coefficients vanish. This proves that the restrictions have rank six and that their joint kernel in $\mathcal W$ has dimension $19-6=13$. The exact six distinct-label equations in (157.3) put every limit $Q(z)$ in that kernel. $\square$

**Corollary 157.3 (the additional scaling obligation for SRS-20).** Retain Route condition 156.3 and require in addition the uniform proximity bound (157.4) throughout its twenty-dimensional ball. Then its proposed affine leading map cannot have $\det S_\theta\ne0$. More precisely,

$$
\operatorname{rank}S_\theta\le13.
\tag{157.12}
$$

The same conclusion holds if (157.4) is replaced by

$$
\sup_{z\in B_{20}}\max_y
\|u_y^{(t,z)}-f_y\|_\infty=o(t^{2/3}).
\tag{157.13}
$$

*Proof.* On the exact $\mathcal H_{43}$ fiber, the full residual is determined linearly by the twenty selected repeated-label coordinates: Proposition 156.2 recovers the omitted row, and Proposition 150.3 recovers the coordinates containing $B$. Thus the uniform limit in (156.6) supplies the full limit (157.5). The space satisfying all pair constraints, the six distinct-label zeros and BBB has dimension $27-6-1=20$. Deleting one repeated-label row identifies it with $\mathbb R^{20}$. Proposition 157.2 puts the leading residuals inside the image of $\mathcal W_{13}$ under this identification. Since $B_{20}$ has positive radius, differences of the affine values $r_{\theta,\ast}+S_\theta z$ show that the range of $S_\theta$ lies in that thirteen-dimensional image. This proves (157.12). Under (157.13), the right side of (157.10) is replaced by $8o(t^{2/3})^3=o(t^2)$, giving the same limit argument. $\square$

The new condition is not present in (156.6): its center is fixed to $f^0+tX$, but its off-center tuples are not required to remain uniformly $O(t)$ close to $f$. Since $f=f^0$ almost everywhere, the essential-supremum estimates above respect the original permitted representative and do not add a pointwise identification on the null exceptional set. Corollary 157.3 excludes a regular small-amplitude scaling class; it neither refutes Route condition 156.3 without that additional condition nor refutes $F_{64}(\theta)$.

The seven unpaid leading directions have an explicit observable description. The eight tensors in (157.8) use the channels $u_0-u_1$ and $u_B-1/4$. On a zero-pair residual their all-second-channel coordinate is BBB, already fixed by $\mathcal H_{43}$. The other seven impose seven additional independent constraints on the twenty-dimensional calibrated quadratic limit. Their independence is the dimension calculation in (157.6), not a claim that seven source-specific cubic corrections exist.

For an all-odd deviation under the original half-turn, the three factors in each right side of (157.8) are odd. The original invariant $g$ and commuting $P$ make that integral zero exactly. Such an exactly calibrated odd family has residual in $\mathcal W_{13}$ at every amplitude, not merely at quadratic order. Even corrections or a different scaling therefore require an actual nonzero three-channel contribution if they are to leave this subspace. For a general family, the identity (157.8) and bound (157.9) show that a nonzero projected $t^2$ limit at some fixed parameter cannot arise from deviations of size $o(t^{2/3})$. Meeting this necessary scale does not supply legality, rank, a zero or a degree estimate.

Consequently one cannot replace the remaining twenty equations by thirteen equations and discard the higher-order terms. A prospective finite completion must still solve the seven contrast equations at their actual order together with the thirteen quadratic directions, the original forty-three calibrations and the whole-$G$ partition realization. The source-specific rank, mixed-scale legality, nonlinear boundary control and finite actual partition remain unresolved. The fixed-start summable route of Corollary 155.4 remains separate and unchanged.

The tensor quotient, multilinearity and finite-dimensional rank count used here are standard linear-algebra tools. The source-specific thirteen-dimensional boundary is repo-derived from the retained FIB suppliers and the definitions above; no historical novelty is claimed for the standard tools. Their role is to identify the two zero channels of the original prescribed $f$ and the resulting source-specific obstruction to the uniform quadratic SRS scaling. They do not provide a new general purification theorem, a full-law witness, physical realization or Lean/kernel certification.

## 追加锚（本行以下为增补区）
## 158. Positive 003 energy and the terminal compensator boundary

**Definition 158.1 (a two-label first-order-calibrated ray with terminal compensation).** Retain the complete telescope of Definition 155.1, hence Definitions 134.1, 135.1 and 154.1, including the residual $\Delta$, the positivity-improvement and conservation suppliers, the trilinear form $\mathcal C$, and the prescribed tuple $f$. Retain also the full first-order map $\Lambda_{134}$ and kernel $V=\ker\Lambda_{134}$ of Definition 134.1, Proposition 134.2, and the propagation identity $Pf_3=cg$. For bounded real Borel representatives $v,w$ and a nonzero real $t$, consider the pointwise tuple

$$
\begin{aligned}
u^{(t;v,w)}_0&=f_0+tv,&
u^{(t;v,w)}_1&=f_1-tv,\\
u^{(t;v,w)}_3&=f_3+t^2w,&
u^{(t;v,w)}_B&=f_B-t^2w.
\end{aligned}
\tag{158.1}
$$

The sum of its four coordinates is one identically. Whenever the four coordinates lie in the pointwise simplex, call (158.1) legal. In the $(0,0,3)$ coefficient the terminal is this tuple's own $P u^{(t;v,w)}_3$; every other coefficient retains its corresponding tuple terminal.

**Proposition 158.2 (strict positive energy on the pure two-label ray).** If $v\in V$, then every legal tuple (158.1) satisfies

$$
\begin{aligned}
\Delta\bigl(u^{(t;v,w)}\bigr)_{003}
={}&t^2\left[c\langle gv,P(gv)\rangle_m
                 +\mathcal C(f_0,f_0,w)\right]\\
&+t^3\left[\mathcal C(v,f_0,w)+\mathcal C(f_0,v,w)\right]
+t^4\mathcal C(v,v,w).
\end{aligned}
\tag{158.2}
$$

In particular, for the uncompensated ray $w=0$ and every nonzero $v\in V$,

$$
\Delta\bigl(u^{(t;v,0)}\bigr)_{003}
=t^2c\langle gv,P(gv)\rangle_m>0.
\tag{158.3}
$$

Thus a nonzero pure two-label direction in the exact first-order kernel cannot by itself be an exact full-law correction at any nonzero amplitude.

*Proof.* Expand the $(0,0,3)$ coefficient using multilinearity and (158.1). The coefficient of $t$ is the first-order functional $\ell_{003}(v)$ in (134.11), which vanishes because $v\in V$. The coefficient of $t^2$ from the two $0$ slots is

$$
\mathcal C(v,v,f_3)=c\langle gv,P(gv)\rangle_m
$$

by (134.15)–(134.16). The $t^2w$ change in the third slot contributes $\mathcal C(f_0,f_0,w)$; the two mixed $t^3$ terms and the $t^4$ term are the remaining multilinear choices. Equation (134.13) makes the first term strictly positive when $v\ne0$. The actual terminal convention is used throughout the expansion. $\square$

**Proposition 158.3 (a quantitative terminal compensator cost).** For bounded real $v,w$, define

$$
\begin{aligned}
\psi_0&=P\bigl(f_0P(gf_0)\bigr),\\
\psi_{\mathrm{mix}}&=P\bigl(f_0P(gv)\bigr)+P\bigl(vP(gf_0)\bigr),\\
\psi_v&=P\bigl(vP(gv)\bigr).
\end{aligned}
\tag{158.4}
$$

If $v\in V$ is nonzero, (158.1) is legal, and its $(0,0,3)$ residual vanishes, then

$$
\|w\|_{L^\infty(m)}
\ge
\frac{c\langle gv,P(gv)\rangle_m}
     {\|\psi_0\|_{L^1(m)}+|t|\,\|\psi_{\mathrm{mix}}\|_{L^1(m)}
                         +t^2\|\psi_v\|_{L^1(m)}}
>0.
\tag{158.5}
$$

The denominator is finite, and $\|\psi_0\|_{L^1(m)}>0$ for every original tuple.

*Proof.* Self-adjointness of $P$ gives

$$
\begin{aligned}
\mathcal C(f_0,f_0,w)&=\int_Gw\,\psi_0\,dm,\\
\mathcal C(v,f_0,w)+\mathcal C(f_0,v,w)&=\int_Gw\,\psi_{\mathrm{mix}}\,dm,\\
\mathcal C(v,v,w)&=\int_Gw\,\psi_v\,dm.
\end{aligned}
\tag{158.6}
$$

If the residual in (158.2) is zero, divide by $t^2$ and move the compensator terms to the other side. The $L^1$–$L^\infty$ bound and (158.6) give (158.5). The original bounds $g\in L^2(m)$, $f_0,v\in L^\infty(m)$ and the $L^2$ contraction of $P$ give finiteness. Since $f_0\ge1/4$ and $gf_0>0$ almost everywhere, positivity improvement gives $P(gf_0)>0$ almost everywhere. Conservation then gives

$$
\int_G\psi_0\,dm
=\int_G f_0P(gf_0)\,dm>0,
$$

so $\psi_0\ne0$ in $L^1(m)$. The numerator is strictly positive by (134.13), so the displayed lower bound is positive. $\square$

**Corollary 158.4 (the fixed-ray route boundary).** Fix a nonzero $v\in V$. No sequence of legal tuples of the form (158.1) can make the $(0,0,3)$ residual zero while its compensators satisfy $\|w\|_{L^\infty(m)}\to0$ and $t\to0$. In particular, shrinking the amplitude does not remove the positive energy that a second-order terminal correction must cancel. The lower bound is a necessary cost for this fixed-ray ansatz, not a uniform residual floor for arbitrary exact partitions. Mixed orders, a varying first-order direction, or corrections outside $V$ remain separate routes; the result neither refutes the general SRS-20 condition nor settles $F_{64}$.

The source-specific statements (158.2)–(158.5) are `repo-derived` applications of the retained positive coefficient (134.13)–(134.16), self-adjointness and the original terminal convention. The positivity and $L^1$–$L^\infty$ estimates are standard intermediate tools; no historical novelty, physical realization, Lean/kernel certification or full-law witness is asserted.

## 追加锚（本行以下为增补区）
