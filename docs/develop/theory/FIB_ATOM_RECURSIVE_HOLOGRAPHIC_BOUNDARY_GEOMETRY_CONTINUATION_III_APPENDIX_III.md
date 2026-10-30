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
