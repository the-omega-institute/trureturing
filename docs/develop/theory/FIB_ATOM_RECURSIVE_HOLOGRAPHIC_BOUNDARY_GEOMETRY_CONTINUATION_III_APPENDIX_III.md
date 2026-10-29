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
