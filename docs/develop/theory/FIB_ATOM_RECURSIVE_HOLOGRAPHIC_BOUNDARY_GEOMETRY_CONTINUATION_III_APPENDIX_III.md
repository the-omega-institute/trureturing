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

*Proof.* The functions $g$ and $q_i$ have the invariant analytic representatives on
$\Omega=\{x^2+y^2>0\}$ supplied by Appendix II §§120, 122 and 133. Hence $q_\lambda$ is analytic and invariant there. It is not zero: if $q_\lambda=0$ almost everywhere, injectivity of $P$ gives $r_\lambda=0$ almost everywhere. Each of $S,C,B$ has positive measure from (136.1), so this forces $\lambda=0$.

Let $Q_\lambda^{\rm sym}$ be the symmetric polarization. On the half-circle section $F$ of Theorem 137.1 its localized odd kernel is

$$
s_\lambda(x,y)=\frac{g(x)q_\lambda(y)+q_\lambda(x)g(y)}2\,k(x,y),
\tag{145.4}
$$

where $k$ is the nonsingular odd heat kernel (137.3). If $q_\lambda$ is negative at a density point of $A\cap\Omega$, continuity gives arbitrarily many disjoint reflected neighborhoods in $A$ on which the matrices in (145.4) converge to a negative multiple of the positive definite Gram matrix of $k$. Their odd localized indicators give arbitrarily large negative subspaces of $\mathcal V_{A,-}$.

It remains to treat the case in which $q_\lambda\geq0$ almost everywhere on $A$. Choose a positive-measure density subset $A_0\subset A\cap F$ and set

$$
\gamma=\frac{g-q_\lambda}{g+q_\lambda}\quad\text{on }A_0.
\tag{145.5}
$$

Here $g>0$ and $|\gamma|\leq1$. If the negative index were finite, the exact Gram identity

$$
s_\lambda(x,y)=\frac{(g(x)+q_\lambda(x))(g(y)+q_\lambda(y))}{4}
\bigl(1-\gamma(x)\gamma(y)\bigr)k(x,y)
\tag{145.6}
$$

would give finitely many negative squares for the kernel on the density set $A_0^*$. Agler--Young, [*Functions which are almost multipliers of Hilbert function spaces*, Theorem 2.1](https://arxiv.org/html/math/9605224v1#S2.Thmtheorem1), applies with the actual odd heat space, its nonsingular kernel $k$, uniqueness domain $A_0^*$, real multiplier $\gamma$ and scalar parameter $1$. It supplies a finite-codimensional domain and a bounded multiplication operator $L$ satisfying

$$
(g+q_\lambda)Lu=(g-q_\lambda)u
\tag{145.7}
$$

on $A_0^*$. Both sides are analytic on $\Omega$, so (145.7) holds on all of $\Omega$ by the same positive-measure uniqueness argument as in Theorem 137.1. The commutator argument there applies on any compact patch where $g+q_\lambda>0$: the actual principal symbol (137.12), high-frequency punctured-core tests, and the three-lines bound force the derivatives of $\gamma$ to vanish. Thus $\gamma$ is constant on a nonempty open patch, and analytic continuation in (145.7) gives

$$
q_\lambda=cg\quad\text{on }\Omega
\tag{145.8}
$$

for a real constant $c$. Since $g=P\beta$ with the nonconstant positive representative $\beta$ of Proposition 136.2, injectivity of $P$ gives $r_\lambda=c\beta$ almost everywhere. The left side is constant on each of the three positive-measure cells, whereas the analytic function $\beta$ cannot be constant on a positive-measure subset without being constant on the connected $\Omega$. This is impossible; $c=0$ is already excluded by $r_\lambda\ne0$. Therefore the negative index is infinite in the nonnegative case as well.

For any finite constraints, choose a negative-definite subspace of dimension larger than their number and intersect it with their common kernels. This proves the final assertion. The argument explicitly treats every real signed combination in (145.3); it uses no positivity of the three terminal weights. It also applies to every half-turn-invariant slack set $A$, which is the only support geometry used below. $\square$

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
a_i(x,y)=g(x)p_d(x,y)q_i(y)\ge0,qquad
\|a_i\|_{L^1(m^2)}=\int_GgPq_i\,dm\le1,
\tag{145.10}
$$

so finite rectangular-tensor approximation in $L^1(m^2)$ reduces continuity to finitely many scalar pairings.

Choose a Borel representative of $w$ which is odd on $S\setminus N$ by using the half-circle section and reflection. Choose a countable separating family $(\psi_n)$ in the real unit ball of $L^1(m)$ and maximize on $\mathcal K$ the strictly convex function

$$
J(w)=\sum_{n\ge1}2^{-n}\left(\int_G\psi_nw\,dm\right)^2.
\tag{145.11}
$$

Let $w$ be a maximizer. If the half-turn-invariant slack set

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
\operatorname{rank}A_{E_n}=2,qquad
\mathbf1_{E_{n,i}}\overset{*}{\rightharpoonup}u_i^0
\quad(i=S,C,B),qquad
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
\(\int g_{jd}v_n\,dm=0\). Together with the nine equations for $E_n$, this proves all twelve original marginal equations for $D_n$.

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

In the restricted invariant coarse/odd construction, the exact full $F_{64}$ equations split as follows. There are the 27 coarse coefficients

$$
\mathcal C(\mathbf1_{E_i},\mathbf1_{E_j},\mathbf1_{E_k}),
\qquad i,j,k\in\{S,C,B\},
\tag{146.11}
$$

and, after the three equations in (145.9) and the automatic cubic identity (146.5), the six remaining ordered quadratic obligations

$$
\mathcal C(v,\mathbf1_{E_j},v)=0\quad(j=S,C,B),qquad
\mathcal C(\mathbf1_{E_i},v,v)=0\quad(i=S,C,B).
\tag{146.12}
$$

All terms with exactly one $v$ vanish by half-turn parity. Thus (146.11)--(146.12) describe the obligations left by this restricted construction; they do not exhaust all possible $F_{64}$ witnesses and do not establish the universal target (144.4). $\square$

The source-specific content of Theorems 145.3 and 146.1 is the signed-pencil-to-extreme-sign composition and its insertion into the actual rank-two coarse sequence. The heat-image analyticity, odd kernel nonsingularity, source boundedness, exact coarse sequence, ordered congruence, and common path density are the supplied results of §§120, 133, 138, 143 and 123. Dvoretzky--Wald--Wolfowitz, [*Relations among certain ranges of vector measures*, §3 Theorem 4 and Lemma 2](https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf), is used only for the finite linear proportional subdivisions in the coarse construction. These results give a conditional actual three-terminal sign and its same-partition sequence consumer; they do not prove attainment of (144.4), nonattainment, a physical realization or the universal $\forall\theta\,F_{64}(\theta)$ statement.

## 追加锚（本行以下为增补区）
