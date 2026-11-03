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
