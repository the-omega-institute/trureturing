# FIB-ATOM recursive holographic boundary geometry · Continuation III

**Notation.** The source and actor are those of the [original volume](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md). Sections55–68 are in the [first continuation](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md); Sections69–77 are in the [second continuation](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md).

## 78. A conditional fixed-commission spatial limit for the full retained-field generator

**Definition 78.1 (fixed data, original target and actual spatial carriers).** Fix an authentic nonempty finite source $D$, its original leaf cap $H$, commissioned $a,g>0$, $\nu\ge0$, $0<\delta\le1$, finite $\Omega\ge1$, and an integer $s\ge3$. All remain fixed as $\varepsilon\downarrow0$. Use the exact unit-cylinder assembly, source chambers, distinct ground half-chambers, grounding, normalizations and kinetic coefficient $\beta=a/\delta$ of72.1–72.10. Choose a sufficiently small aperture after the fixed skeleton's separation and angle margins have been chosen, as in72.4, and then hold that aperture fixed. No aperture or source parameter is another limiting variable.

The target particle space and nonnegative kinetic operator are exactly

$$
\mathcal K=\mathbb Cr\oplus\mathcal K_{D,1}\oplus\mathcal K_{D,2}^{\rm hc},
\qquad
A=0\oplus A_{\delta,D,1}\oplus A_{\delta,D,2}.
\tag{78.1}
$$

Here every atom, entire interval, mixed slice, rectangle and both same-cable triangles, their weights $1,\delta,\delta^2$, symmetry, missing atomic collision coordinates, exterior killing and all Hilbert-valued traces are those of Definition64.5. In particular the singleton still has its complete continuum two-position sector. The target is not a harmonic or atomic subspace.

For clarity write the full spatial particle space as

$$
\mathcal P_\varepsilon=\mathbb Cr\oplus L^2(\Omega_\varepsilon^+)
                    \oplus L^2_{\rm sym}((\Omega_\varepsilon^+)^2).
\tag{78.2}
$$

Use either of the following installations, separately. In the hard installation, retain75.9's allowed two-position carrier, zero-extension isometry and Dirichlet exclusion form, with either $R_\varepsilon=\kappa r_\varepsilon$, fixed $\kappa>0$, $r_\varepsilon=\varepsilon^{(s-1)/s}$, or precisely75.12's alternative $R_\varepsilon\to0$, $R_\varepsilon/r_\varepsilon\to\infty$. In the finite-height installation retain the full product carrier and75.13's nonnegative penalty $\Lambda_\varepsilon\mathbf1_{\{|x-y|\le R_\varepsilon\}}$, with fixed $\kappa>0$, $R_\varepsilon=\kappa r_\varepsilon$ and finite $\Lambda_\varepsilon\ge0$ satisfying $\Lambda_\varepsilon R_\varepsilon\to\infty$. The mesoscopic hard alternative does not assert a finite-height theorem for a different schedule.

Let $\mathcal P_\varepsilon^{\rm a}$ be the direct sum of reference, full one-position carrier and the chosen actual two-position carrier. Let $\iota_\varepsilon^{\rm p}:\mathcal P_\varepsilon^{\rm a}\to\mathcal P_\varepsilon$ be identity on reference and one-position sectors and zero extension on the hard two-position sector; it is identity in the finite-height installation. Its adjoint is actual restriction. Denote by $B_\varepsilon\ge0$ the direct sum of zero,72.10's full one-position kinetic operator and the chosen75 $C_0$ spatial operator, with no $W_{\varepsilon,\diamond}$ pair multiplier. Thus the latter form is, respectively,

$$
\begin{aligned}
q_{\varepsilon,2}^{\rm a}[u]
 &=\beta\int_{(\Omega_\varepsilon^+)^2}
       (|\nabla_x\iota_\varepsilon^{\rm p}u|^2+
        |\nabla_y\iota_\varepsilon^{\rm p}u|^2),\\
q_{\varepsilon,2}^{\Lambda}[u]
 &=\beta\int_{(\Omega_\varepsilon^+)^2}(|\nabla_xu|^2+|\nabla_yu|^2)
       +\Lambda_\varepsilon\int_{|x-y|\le R_\varepsilon}|u|^2 .
\end{aligned}
\tag{78.3}
$$

Their domains are exactly75.9's zero-extended mixed-ground $H^1$ domain and75.13's entire symmetric mixed-ground $H^1$ domain, respectively. The one-position form domain is the mixed-ground $H^1$ domain of72.10. Exterior Neumann conditions are natural conditions of these forms.

The actual raw particle isometry is

$$
L_\varepsilon^{\rm p}=I_r\oplus J_{\varepsilon,1}\oplus J_{\varepsilon,2}E,
\qquad (L_\varepsilon^{\rm p})^*L_\varepsilon^{\rm p}=I.
\tag{78.4}
$$

$J_{\varepsilon,1}$ is72.30's map, $J_{\varepsilon,2}$ is the complete product map75.7, and $E$ inserts zero at each atomic $(p,p)$ and otherwise identifies the literal hard-core Hilbert coordinates. More explicitly, with $c_\varepsilon=\sqrt\delta\,\varepsilon^{-(s-1)/2}$, $J_{\varepsilon,1}$ multiplies both chamber values and longitudinal cable functions by $c_\varepsilon$, and is zero on ground half-chambers. The product map multiplies every chamber/chamber, chamber/cylinder, cylinder/chamber and cylinder/cylinder value by $c_\varepsilon^2$. Its adjoint integrates only the chamber and transverse variables, with factors $b_p=c_\varepsilon$, $b_e=c_\varepsilon/\delta$ in each coordinate. The one-position adjoint has these same individual factors. The target two-position adjoint then applies $E^*$, deleting atomic $(p,p)$ coordinates. These are the adjoints on all spatial Hilbert data, including ground half-chamber functions, and not just on a prepared range.

The restricted particle lift is $T_\varepsilon^{\rm p}=(\iota_\varepsilon^{\rm p})^*L_\varepsilon^{\rm p}$, with adjoint $(L_\varepsilon^{\rm p})^*\iota_\varepsilon^{\rm p}$. It is a contraction. Neither it nor the raw map is an asserted kinetic operator intertwiner.

**Definition 78.2 (complete field and additional chamber-count coupling).** Choose either complete common or complete killed commission, separately, with the original formulas

$$
\begin{aligned}
G_D^{\rm c}(p,q)&=\frac23\,2^{-d(p,q)}
                      +\frac13\,2^{-(|p|+|q|)},&
F_D^{\rm c}&=L_D-P_{\operatorname{Leaf}(D)},\\
G_D^{\rm k}(p,q)&=(L_D^{-1})_{pq},&
F_D^{\rm k}&=L_D,\\
(F_D^\diamond)^{-1}&=G_D^\diamond,&
\lambda I&\le F_D^\diamond\le6I,\qquad \lambda=3-2\sqrt2.
\end{aligned}
\tag{78.5}
$$

Here $L_D$ retains root diagonal two, every other diagonal three and every inherited seam; $d(p,q)$ is the original occurrence distance. Extend $F_D^\diamond$ by identity without cross blocks to the entire bank $\mathcal B_H=\{p:|p|\le H-1\}$. On the full $\mathcal F_H=\Gamma_s(\ell^2(\mathcal B_H))$ use exactly67.3–67.4:

$$
h=d\Gamma(\widehat F_D^\diamond),\quad
\mathsf n=d\Gamma(I),\quad
q_p=(b_p+b_p^*)/\sqrt2,\quad
\lambda\mathsf n\le h\le6\mathsf n .
\tag{78.6}
$$

This is the balanced coordinate/momentum bank with $2^H-1$ modes, its declared normal-ordering zero, every excitation and every unused spectator. Its canonical momentum couplings and calibration are apparatus hypotheses. Fix any auxiliary Hilbert space $\mathcal A$, with no restriction on correlations.

On $\mathcal K$ use67.2's literal atomic counts $m_p$. On the entire spatial particle space define instead

$$
m_{\varepsilon,p}(x_1,\ldots,x_N)
       =\sum_{i=1}^N\mathbf1_{Z_p^\varepsilon}(x_i),\qquad N=1,2,
\quad m_{\varepsilon,p}r=0.
\tag{78.7}
$$

They count actual chamber membership, including two distinct positions in the same chamber. On the actual carrier use their restrictions $m_{\varepsilon,p}^{\rm a}$. All counts are bounded self-adjoint multipliers. Their definition is an explicit additional spatial-model installation, not a native operation or a derived ambient force.

Suppress auxiliary identities in formulas and put $k_f=\sqrt{\nu\Omega}$. On the ambient joint space $\mathcal X_\varepsilon=\mathcal P_\varepsilon\otimes\mathcal F_H\otimes\mathcal A$, and on the target joint space $\mathcal X=\mathcal K\otimes\mathcal F_H\otimes\mathcal A$, respectively, set

$$
\begin{aligned}
V_\varepsilon&=V_{\varepsilon,0}-k_f Q_\varepsilon,&
Q_\varepsilon&=\sum_{p\in D}m_{\varepsilon,p}\otimes q_p,\\
V_{\varepsilon,0}
 &=-g\sum_p\phi(p)m_{\varepsilon,p}
       +\frac\nu2\sum_pG_D^\diamond(p,p)m_{\varepsilon,p},&
\phi(p)&=2^{-|p|},\\
V_D&=-g\sum_p\phi(p)m_p
       -k_f\sum_pm_p\otimes q_p
       +\frac\nu2\sum_pG_D^\diamond(p,p)m_p .
\end{aligned}
\tag{78.8}
$$

The spatial and target generators are

$$
\begin{aligned}
\mathsf M_\varepsilon&=B_\varepsilon\otimes I+
                         I\otimes\Omega h+V_\varepsilon^{\rm a}
              &&\text{on }\mathcal P_\varepsilon^{\rm a}\otimes\mathcal F_H\otimes\mathcal A,\\
\mathsf M_D&=A\otimes I+I\otimes\Omega h+V_D
              &&\text{on }\mathcal X.
\end{aligned}
\tag{78.9}
$$

The second is exactly $\mathbb M_D$ of(67.5), on the full literal64.5 target. It is neither $\mathbb M_D^{\rm d}$ nor $\mathbb H_D^0$. There is no installed off-diagonal pair multiplier in either line of(78.9); the pair is generated by the same field inverse and its actual inverse-diagonal linear compensation. On the reference both generators are precisely $\Omega h$.

Write $\ell_\varepsilon=L_\varepsilon^{\rm p}\otimes I$, $\iota_\varepsilon=\iota_\varepsilon^{\rm p}\otimes I$, $T_\varepsilon=\iota_\varepsilon^*\ell_\varepsilon$, and $N=(\mathsf n+I)^{1/2}$ on every joint carrier. Particle maps commute with $N$ and preserve its domain.

**Lemma 78.3 (full Hilbert covariance, correct charge and diagonal boundary).** On the full particle spaces and, for the field coupling, on $\operatorname{Dom}N$,

$$
\begin{aligned}
m_{\varepsilon,p}L_\varepsilon^{\rm p}&=L_\varepsilon^{\rm p}m_p,&
(L_\varepsilon^{\rm p})^*m_{\varepsilon,p}
     &=m_p(L_\varepsilon^{\rm p})^*,\\
m_{\varepsilon,p}\iota_\varepsilon^{\rm p}
     &=\iota_\varepsilon^{\rm p}m_{\varepsilon,p}^{\rm a},&
V_\varepsilon\ell_\varepsilon&=\ell_\varepsilon V_D,\qquad
\ell_\varepsilon^*V_\varepsilon=V_D\ell_\varepsilon^* .
\end{aligned}
\tag{78.10}
$$

With $M_0=2g+\nu/\lambda$, the full spatial and target bounds are

$$
\|V_{\varepsilon,0}\|\le M_0,\qquad
\|Q_\varepsilon\Xi\|\le2\sqrt2\,\|N\Xi\|,\qquad
\|V_\varepsilon\Xi\|\le M_0\|\Xi\|+2\sqrt2 k_f\|N\Xi\|.
\tag{78.11}
$$

The target has the better charge bound $2\|N\Psi\|$, but it is not a full spatial bound. The same estimates hold after restriction and with arbitrary auxiliary correlations. No count is required to preserve a kinetic Sobolev or operator domain.

**Proof.** In a chamber/cylinder product a chamber indicator detects exactly the atomic coordinate of its raw lifted stratum; in a cylinder/cylinder product it detects none. The same-chamber product has zero raw lift because $E$ inserted zero at $(p,p)$. Ground half-chambers also have zero raw lift. These cases prove the first equality, including independent atomic, mixed and cell data. Taking adjoints proves the second. Zero extension commutes with a bounded measurable multiplier, proving the restriction equality. Finite field-particle tensors in $\operatorname{Dom}N$ give the coupling equalities; the creation/annihilation estimate below and approximation in the $N$ graph norm give them on all of that domain. The bounded terms then give(78.10). Consequently $V_\varepsilon^{\rm a}T_\varepsilon=T_\varepsilon V_D$ and $T_\varepsilon^*V_\varepsilon^{\rm a}=V_DT_\varepsilon^*$ on the corresponding number domains; these are Hilbert-space coupling identities, not kinetic domain or intertwining assertions.

For a real bank vector $z$, the standard estimates
$\|b(z)\psi\|\le\|z\|\|\mathsf n^{1/2}\psi\|$ and
$\|b^*(z)\psi\|\le\|z\|\|N\psi\|$
give $\|q(z)\psi\|\le\sqrt2\|z\|\|N\psi\|$. At every spatial configuration $z_p=m_{\varepsilon,p}$ is nonnegative, $\sum_pz_p\le2$, and $\|z\|\le2$. Apply this inequality in the particle-position fibres and integrate. It applies to Hilbert-valued fibres with auxiliary identities, so it proves(78.11) for correlated states. On the target, $m_p^2=m_p$ and $\sum_pm_p\le2$, giving $\|z\|\le\sqrt2$ and the bound two of67.10. Finally $0\le\phi\le1$, $G_D^\diamond(p,p)\le\lambda^{-1}$ and $\sum_pm_{\varepsilon,p}\le2$ prove the bounded-potential estimate.

The distinction is substantive. The full spatial chamber/chamber region contains a positive-measure same-chamber product with $z=2e_p$. Normalized particle functions supported there and real coherent field vectors of amplitude $t e_p$ give $\|2q_p\psi_t\|/\|N\psi_t\|\to2\sqrt2$ as $t\to\infty$. Thus two cannot bound the full spatial charge. Finite-height carriers retain that region; a hard radius covering an entire chamber removes it only on that allowed carrier, not on the ambient carrier needed in the comparison.

Nor is idempotency available in general. For this fibre the displacement calculation of67.7, with the unchanged linear compensation, gives

$$
-\frac\nu2 z^{\mathsf T}G_D^\diamond z
 +\frac\nu2\sum_pG_D^\diamond(p,p)z_p
=-\nu\sum_{p<q}G_D^\diamond(p,q)z_pz_q
 -\frac\nu2\sum_pG_D^\diamond(p,p)(z_p^2-z_p).
\tag{78.12}
$$

The last term is $-\nu G_D^\diamond(p,p)$ when $z=2e_p$. It vanishes on the literal target, and is not removed from the finite-width model by changing the compensation to a quadratic expression. The nonnegative exclusion or repulsion and the complete $C_0$ limit, not a false physical idempotency assertion, control this distinction. The displacement is only a fibre calculation. In particular multiplying a physical trace-matching function by a chamber indicator generally introduces a jump at a plate; the corresponding atomic multiplier on64.5 also breaks endpoint matching. Neither operation is a kinetic domain invariance or an exact kinetic conjugacy. $\square$

**Proposition 78.4 (self-adjoint operators, complete forms and uniform lower bound).** Both operators(78.9) are self-adjoint on the exact domains

$$
\begin{aligned}
\operatorname{Dom}\mathsf M_\varepsilon
 &=\operatorname{Dom}(B_\varepsilon\otimes I)
       \cap\operatorname{Dom}(I\otimes\mathsf n),\\
\operatorname{Dom}\mathsf M_D
 &=\operatorname{Dom}(A\otimes I)
       \cap\operatorname{Dom}(I\otimes\mathsf n).
\end{aligned}
\tag{78.13}
$$

Their form domains are the corresponding complete Hilbert-valued particle form domains intersected with $\operatorname{Dom}N$. They retain every original target trace and every installed spatial essential trace. Their unitary groups preserve their own form and operator domains. If $c=\Omega\lambda$ and

$$
L_0=M_0+\frac c2+\frac{4k_f^2}{c},
\tag{78.14}
$$

both operators are bounded below by $-L_0$, uniformly in $\varepsilon$ and in the auxiliary space.

**Proof.** Write $H_0=B_\varepsilon\otimes I+I\otimes\Omega h$, or $A\otimes I+I\otimes\Omega h$ on the target. Its two nonnegative summands strongly commute. Their joint spectral calculus gives self-adjointness with the intersection operator domain and the intersection form domain. The inequalities $\lambda\mathsf n\le h\le6\mathsf n$ identify the field operator domain with $\operatorname{Dom}\mathsf n$. For $u$ in the operator domain,

$$
\|Nu\|^2\le c^{-1}\langle u,H_0u\rangle+\|u\|^2
       \le c^{-1}\|u\|\|H_0u\|+\|u\|^2.
\tag{78.15}
$$

Together with(78.11) and the scalar Young inequality, this makes $V$ infinitesimally $H_0$-bounded. It is symmetric on $\operatorname{Dom}N$: the fibre coefficients are bounded real functions and every $q_p$ is symmetric there. Kato–Rellich, in the precise version cited in78.13, therefore gives(78.13).

On the free form domain the same estimate gives an infinitesimal relative form bound. More explicitly,

$$
|\langle u,Vu\rangle|
\le M_0\|u\|^2+2\sqrt2 k_f\|u\|\|Nu\|
\le \frac c2\|Nu\|^2+
            \left(M_0+\frac{4k_f^2}{c}\right)\|u\|^2
\le \frac12\langle u,H_0u\rangle+L_0\|u\|^2 .
\tag{78.16}
$$

Replacing $c/2$ by any positive sufficiently small coefficient gives arbitrary relative form bound. The closed-form perturbation theorem gives a closed semibounded form on exactly the stated domain, with an equivalent shifted form norm. Its represented operator is the operator sum already obtained: testing a free operator-domain vector gives the sum, and the free operator domain is a form core, by its spectral truncations. This also proves the lower bound(78.14).

For avoidance of any hidden multidimensional regularity premise, the kinetic operator domains used here have the exact weak meaning

$$
\operatorname{Dom}B_\varepsilon
 =\{u\in\mathcal Q_\varepsilon^{\rm a}:
       \exists w\in\mathcal P_\varepsilon^{\rm a},\
       q_\varepsilon^{\rm a}(u,v)=\langle w,v\rangle
       \text{ for every }v\in\mathcal Q_\varepsilon^{\rm a}\},
\tag{78.17}
$$

with output $w$, and the identical representation definition for $A$ using64.5's full form and measure. Density makes $w$ unique. Finite-height penalty is included in $q_\varepsilon^{\rm a}$. Vector-valued versions mean the closed tensor forms. No global $H^2$ assertion, corner trace, invariant domain for a count multiplier or operator-domain property of $L_\varepsilon^{\rm p}$ is added. For a semibounded self-adjoint operator the spectral calculus makes its unitary group commute with its shifted square root and with the operator itself, proving the stated invariance. $\square$

**Lemma 78.5 (complete free Fock transfer and half-number smoothing).** Choose once and for all

$$
\begin{gathered}
\sigma\ge\max(1,c),\qquad \sigma>L_0,\qquad
s_\sigma=\sup_{j\in\mathbb N_0}
                 \frac{\sqrt{j+1}}{\sigma+cj},\\
\theta=\frac{M_0}{\sigma}+2\sqrt2 k_f s_\sigma<1.
\end{gathered}
\tag{78.18}
$$

Such a fixed $\sigma$ exists. Define the complete particle $C_0$ error

$$
\eta_\varepsilon=
\left\|\iota_\varepsilon^{\rm p}(B_\varepsilon+\sigma)^{-1}
          (\iota_\varepsilon^{\rm p})^*
       -L_\varepsilon^{\rm p}(A+\sigma)^{-1}(L_\varepsilon^{\rm p})^*
\right\|\longrightarrow0.
\tag{78.19}
$$

The reference block of this error is zero. The one- and two-position blocks are the entire72/75 free comparisons, including their spatial complements. Put $w_\varepsilon=\sqrt{2\eta_\varepsilon/c}$ and, on $\mathcal X_\varepsilon$, put

$$
\begin{aligned}
R_\varepsilon&=\iota_\varepsilon
 (B_\varepsilon\otimes I+I\otimes\Omega h+\sigma)^{-1}
                                      \iota_\varepsilon^*,\\
S_\varepsilon&=\ell_\varepsilon
 (A\otimes I+I\otimes\Omega h+\sigma)^{-1}
                                      \ell_\varepsilon^*.
\end{aligned}
\tag{78.20}
$$

Then

$$
\begin{aligned}
\|R_\varepsilon-S_\varepsilon\|&\le\eta_\varepsilon,&
\|N(R_\varepsilon-S_\varepsilon)\|&\le w_\varepsilon,\\
\|R_\varepsilon\|,\|S_\varepsilon\|&\le\sigma^{-1},&
\|NR_\varepsilon\|,\|NS_\varepsilon\|&\le s_\sigma,\\
\|V_\varepsilon R_\varepsilon\|,
\|V_\varepsilon S_\varepsilon\|&\le\theta .
\end{aligned}
\tag{78.21}
$$

These bounds hold on the full Fock and auxiliary spaces without a final number cutoff.

**Proof.** The nonnegative particle suppliers72.10,75.4,75.12 and75.13 give(78.19). One may transfer their nonreal comparison to $-\sigma$ directly by the rational resolvent identity: for $t\ge0$ the inverse factor $(t-i)/(t+\sigma)$ has modulus at most $\max(1,\sigma^{-1})$, and the lifted zero complement has inverse factor one. Thus a common negative point requires no additional spatial theorem.

For a nonnegative operator, including a zero-extended resolvent, the change from $\sigma$ to any $b\ge\sigma$ is the bounded function
$X\mapsto X(I+(b-\sigma)X)^{-1}$. Its difference at two positive $X,Y$ is

$$
(I+(b-\sigma)X)^{-1}(X-Y)(I+(b-\sigma)Y)^{-1}.
\tag{78.22}
$$

Both inverse factors have norm at most one. Consequently the complete particle error at every $-b$, $b\ge\sigma$, is at most $\eta_\varepsilon$.

The finite bank has a simultaneous orthonormal eigenbasis for $h$ and $\mathsf n$. In its $j$-particle sector every eigenvalue $E$ of $\Omega h$ satisfies $E\ge cj$. The corresponding block of(78.20) is the particle comparison at $b=\sigma+E$. Its discrepancy is bounded both by $\eta_\varepsilon$ and by $2/(\sigma+cj)$. Since $\sigma\ge c$,

$$
\sqrt{j+1}\min\left(\eta_\varepsilon,\frac2{\sigma+cj}\right)
 \le\sqrt{\frac{2\eta_\varepsilon}{c}}.
\tag{78.23}
$$

Taking the supremum of the orthogonal block norms proves the first line of(78.21); the same block calculus gives the second. Auxiliary tensor identities do not change any operator norm. This argument includes arbitrary superpositions and correlations; it does not assume an input supported in finitely many blocks.

Also $s_\sigma\le(c\sigma)^{-1/2}$: $\sigma+cj$ is at least both $\sigma$ and $c(j+1)$, so its square is at least $c\sigma(j+1)$. Hence $\theta\to0$ as $\sigma\to\infty$, proving existence. Applying(78.11) to the ranges of $R_\varepsilon,S_\varepsilon$, which are in $\operatorname{Dom}N$, proves the final line. $\square$

**Lemma 78.6 (same-ambient perturbation identity with an unbounded charge).** Let $R,S$ be bounded positive self-adjoint operators on one Hilbert space, with ranges in $\operatorname{Dom}N$, and let $V$ be symmetric on $\operatorname{Dom}N$ with
$\|Vu\|\le M_0\|u\|+2\sqrt2 k_f\|Nu\|$.
Suppose $\|VR\|,\|VS\|\le\theta<1$, $\|NR\|,\|NS\|\le s_\sigma$, $\|R-S\|\le\eta$ and $\|N(R-S)\|\le w$. Define

$$
\mathcal C(R)=R(I+VR)^{-1},\qquad
\mathcal C(S)=S(I+VS)^{-1}.
\tag{78.24}
$$

All products in this definition are bounded. Then

$$
\begin{aligned}
\|\mathcal C(R)-\mathcal C(S)\|
 &\le\frac{\eta}{(1-\theta)^2},\\
\|N(\mathcal C(R)-\mathcal C(S))\|
 &\le\frac{w}{1-\theta}
       +\frac{s_\sigma(M_0\eta+2\sqrt2 k_f w)}{(1-\theta)^2},\\
\|N\mathcal C(R)\|,\|N\mathcal C(S)\|
 &\le\frac{s_\sigma}{1-\theta}.
\end{aligned}
\tag{78.25}
$$

**Proof.** $VR$ and $VS$ are everywhere defined bounded operators; their Neumann inverses $Z_R,Z_S$ have norm at most $(1-\theta)^{-1}$. Since $\operatorname{Dom}N$ is dense and $V$ is symmetric there, for $u\in\operatorname{Dom}N$ the products $RVu$ and $SVu$ agree with $(VR)^*u$ and $(VS)^*u$. Thus throughout the identity below $\overline{RV}$ and $\overline{SV}$ mean these bounded extensions; no undefined left product is used. The push-through identity, verified first on $\operatorname{Dom}N$ and then by bounded extension, gives

$$
\mathcal C(R)-\mathcal C(S)
 =(I+\overline{RV})^{-1}(R-S)(I+VS)^{-1}.
\tag{78.26}
$$

For example multiplication by the two outer inverse denominators reduces this equation to $R-S$: the two mixed terms cancel because
$\overline{RV}S=RVS$. This also proves the identity when $R$ or $S$ has a nontrivial kernel. The inverse on the left has the same bound as $Z_R$, by adjunction. This proves the unweighted estimate.

For the weighted estimate use instead the everywhere bounded identity

$$
\mathcal C(R)-\mathcal C(S)
 =(R-S)Z_R-SZ_SV(R-S)Z_R,
\quad
Z_R-Z_S=-Z_SV(R-S)Z_R.
\tag{78.27}
$$

$V(R-S)$ has norm at most $M_0\eta+2\sqrt2 k_f w$. Multiplying(78.27) by the closed operator $N$ is legitimate because each displayed output factor has range in its domain and bounded product with it. The estimates $\|NSZ_S\|\le s_\sigma/(1-\theta)$ and $\|Z_R\|\le(1-\theta)^{-1}$ give exactly the second line of(78.25). The last line follows directly from(78.24). No commutation of $N$ with $V$ was assumed. $\square$

**Theorem 78.7 (complete conditional spatial generator theorem).** Under78.1–78.2's explicit installations, for each of the two complete commissions separately, define the actual zero-extended and target-lifted coupled resolvents

$$
\begin{aligned}
\mathcal R_\varepsilon(z)
 &=\iota_\varepsilon(\mathsf M_\varepsilon-z)^{-1}\iota_\varepsilon^*,\\
\mathcal S_\varepsilon(z)
 &=\ell_\varepsilon(\mathsf M_D-z)^{-1}\ell_\varepsilon^*,\\
\Delta_\varepsilon(z)&=\mathcal R_\varepsilon(z)-\mathcal S_\varepsilon(z).
\end{aligned}
\tag{78.28}
$$

With the one fixed $\sigma$ of(78.18), the complete ambient quantitative estimates are exactly

$$
\begin{aligned}
\|\Delta_\varepsilon(-\sigma)\|
 &\le E_\varepsilon:=\frac{\eta_\varepsilon}{(1-\theta)^2},\\
\|N\Delta_\varepsilon(-\sigma)\|
 &\le H_\varepsilon:=
   \frac{w_\varepsilon}{1-\theta}
   +\frac{s_\sigma(M_0\eta_\varepsilon+2\sqrt2 k_f w_\varepsilon)}
                 {(1-\theta)^2},
\qquad w_\varepsilon=\sqrt{2\eta_\varepsilon/c}.
\end{aligned}
\tag{78.29}
$$

The analogous right-weighted product has the same bound, understood by bounded closure. Each individual coupled shifted resolvent has half-number smoothing norm at most $s_\sigma/(1-\theta)$.

For every fixed compact $K\subset\mathbb C\setminus\mathbb R$, both

$$
\sup_{z\in K}\|\Delta_\varepsilon(z)\|\longrightarrow0,\qquad
\sup_{z\in K}\|N\Delta_\varepsilon(z)\|\longrightarrow0
\tag{78.30}
$$

hold on the entire ambient joint space. The right-weighted products also converge uniformly on $K$. On the entire actual joint carrier,

$$
(\mathsf M_\varepsilon-z)^{-1}
       -T_\varepsilon(\mathsf M_D-z)^{-1}T_\varepsilon^*
       =\iota_\varepsilon^*\Delta_\varepsilon(z)\iota_\varepsilon,
\tag{78.31}
$$

so all corresponding allowed-carrier bounds follow with no increase. The complete complement and both cross-block conclusions are78.8, and the full joint fixed-vector finite-clock conclusion is78.9. Together these statements concern the full original64.5 generator(67.5), all field modes and every auxiliary correlation. They make no unweighted unitary operator-norm assertion.

**Proof.** We first identify the perturbation formula without imposing a kinetic property on a raw lift. Restriction and zero extension commute with $V_\varepsilon$ on $\operatorname{Dom}N$. On the actual carrier, factor the operator on its domain as

$$
\mathsf M_\varepsilon+\sigma
 =(I+V_\varepsilon^{\rm a}
       (B_\varepsilon\otimes I+I\otimes\Omega h+\sigma)^{-1})
           (B_\varepsilon\otimes I+I\otimes\Omega h+\sigma).
\tag{78.32}
$$

The first factor has a bounded inverse by(78.21);(78.13) justifies the second factor and its range. Zero-extending the inverse of(78.32) gives precisely
$\mathcal R_\varepsilon(-\sigma)=\mathcal C(R_\varepsilon)$.
One can check this directly term by term in the norm-convergent Neumann series
$R_\varepsilon\sum_{n\ge0}(-V_\varepsilon R_\varepsilon)^n$.
Every term annihilates the forbidden subspace; no densely defined ambient operator with that subspace deleted is being asserted.

On the target use the identical factorization. Covariance(78.10) and $\ell_\varepsilon^*\ell_\varepsilon=I$ give, term by term,

$$
S_\varepsilon(V_\varepsilon S_\varepsilon)^n
 =\ell_\varepsilon R_D^0(V_D R_D^0)^n\ell_\varepsilon^*,
\quad
R_D^0=(A\otimes I+I\otimes\Omega h+\sigma)^{-1}.
\tag{78.33}
$$

Hence $\mathcal S_\varepsilon(-\sigma)=\mathcal C(S_\varepsilon)$. This is a resolvent-series identity using Hilbert covariance of the charge; it does not move the kinetic operator across $\ell_\varepsilon$. Applying78.6 with78.5 proves(78.29) and the individual smoothing estimates. At $-\sigma$ the two coupled extended resolvents are self-adjoint, so adjunction proves the right-weighted assertion.

Here are explicit uniform bounds for the continuation to $K$. Both coupled generators have lower bound $-L_0$ by78.4. Thus the positive operators
$X=\mathcal R_\varepsilon(-\sigma)$,
$Y=\mathcal S_\varepsilon(-\sigma)$
have spectra in $[0,b_*]$, where $b_*=(\sigma-L_0)^{-1}$. For $z\in K$, set $a_z=z+\sigma$ and

$$
d_K=\min_{\substack{z\in K\\0\le t\le b_*}}|1-a_zt|>0,
\qquad A_K=\max_{z\in K}|a_z|.
\tag{78.34}
$$

The minimum is positive because at $t=0$ the expression is one, while a zero with $t>0$ would make $z$ real. The functional calculus with value zero on the kernels gives

$$
\mathcal R_\varepsilon(z)=X(I-a_zX)^{-1},\qquad
\mathcal S_\varepsilon(z)=Y(I-a_zY)^{-1}.
\tag{78.35}
$$

The two inverse factors have norm at most $d_K^{-1}$. The algebraic identity used in(78.22), now with coefficient $-a_z$, gives the unweighted bound

$$
\sup_{z\in K}\|\Delta_\varepsilon(z)\|
       \le d_K^{-2}E_\varepsilon .
\tag{78.36}
$$

For the weighted bound write $Z_X=(I-a_zX)^{-1}$ and $Z_Y=(I-a_zY)^{-1}$. The bounded identity

$$
\Delta_\varepsilon(z)=(X-Y)Z_X
                     +a_zYZ_Y(X-Y)Z_X
\tag{78.37}
$$

requires no commutation with $N$. Since $\|NY\|\le s_\sigma/(1-\theta)$, it gives

$$
\sup_{z\in K}\|N\Delta_\varepsilon(z)\|
 \le d_K^{-1}H_\varepsilon
       +A_Kd_K^{-2}\frac{s_\sigma}{1-\theta}E_\varepsilon .
\tag{78.38}
$$

The ranges in(78.37) are in $\operatorname{Dom}N$, so the product is well defined and bounded. Apply this also to $\overline K$ and take adjoints for the right-weighted estimate. Finally(78.31) is compression by the actual zero-extension isometry; it commutes with the number weight. This proves all resolvent assertions, with the same error for arbitrary auxiliaries. Both prescriptions form a finite family, share the same $C_0$ particle error, and obey the same bounds $c,M_0,\theta,L_0$. Thus maxima over the two complete prescriptions have the same convergence. $\square$

**Proposition 78.8 (both complements, cross blocks and the genuine restriction loss).** Let

$$
P_\varepsilon=\ell_\varepsilon\ell_\varepsilon^*,\quad
Q_\varepsilon^{\rm ran}=I-P_\varepsilon,\quad
A_\varepsilon^{\rm a}=\iota_\varepsilon\iota_\varepsilon^*,\quad
F_\varepsilon^{\rm forb}=I-A_\varepsilon^{\rm a}.
\tag{78.39}
$$

The charge $Q_\varepsilon$ of(78.8) is distinct from the range-complement projection $Q_\varepsilon^{\rm ran}$. At every permitted $z$,

$$
\begin{aligned}
\|Q_\varepsilon^{\rm ran}\mathcal R_\varepsilon(z)Q_\varepsilon^{\rm ran}\|,
\quad\|Q_\varepsilon^{\rm ran}\mathcal R_\varepsilon(z)P_\varepsilon\|,
\quad\|P_\varepsilon\mathcal R_\varepsilon(z)Q_\varepsilon^{\rm ran}\|
 &\le\|\Delta_\varepsilon(z)\|,\\
\|F_\varepsilon^{\rm forb}\mathcal S_\varepsilon(z)\|,
\quad\|\mathcal S_\varepsilon(z)F_\varepsilon^{\rm forb}\|
 &\le\|\Delta_\varepsilon(z)\|.
\end{aligned}
\tag{78.40}
$$

The same block bounds with $N$ on the left hold with $\|N\Delta_\varepsilon(z)\|$, and with the right weight by adjunction at $\overline z$. In the hard installation

$$
T_\varepsilon^*T_\varepsilon\longrightarrow I
\quad\hbox{strongly on each fixed target joint vector},\qquad
\|I-T_\varepsilon^*T_\varepsilon\|=1
\quad\hbox{for all sufficiently small }\varepsilon
\tag{78.41}
$$

when $\mathcal A\ne\{0\}$. In the finite-height installation $T_\varepsilon=\ell_\varepsilon$ is an isometry.

**Proof.** The lifted target resolvent is supported on $P_\varepsilon$ in both directions, whereas the actual extended resolvent is supported on $A_\varepsilon^{\rm a}$. Multiplying their difference proves(78.40). These projections are particle projections tensored with field/auxiliary identity and hence commute with $N$. The weighted conclusions follow without requiring either projection to preserve a kinetic domain.

The range complement includes both the complement of the full free product raw map and its excluded effective atomic part. On the two-position sector it decomposes orthogonally as

$$
I-J_{\varepsilon,2}EE^*J_{\varepsilon,2}^*
 =(I-J_{\varepsilon,2}J_{\varepsilon,2}^*)
       +J_{\varepsilon,2}(I-EE^*)J_{\varepsilon,2}^* .
\tag{78.42}
$$

Thus nonconstant chamber modes, transverse modes, ground half-chamber data and the effective atomic $(p,p)$ coordinates are all covered, together with their cross blocks to the retained target. The forbidden projection is a different complement; no commutation of $P_\varepsilon$ with $A_\varepsilon^{\rm a}$ is assumed. Compressing the last two bounds of(78.40) also controls its two cross blocks and its diagonal block relative to $A_\varepsilon^{\rm a}$.

To prove the strong assertion, let $R_D=(\mathsf M_D+\sigma)^{-1}$. Since $F_\varepsilon^{\rm forb}\mathcal R_\varepsilon(-\sigma)=0$,

$$
\|F_\varepsilon^{\rm forb}\ell_\varepsilon R_D\Psi\|
 \le E_\varepsilon\|\Psi\|.
\tag{78.43}
$$

$R_D$ has dense range, and $\ell_\varepsilon$ is an isometry. Approximation by this dense range proves
$F_\varepsilon^{\rm forb}\ell_\varepsilon\Psi\to0$
for each fixed $\Psi$. Since
$I-T_\varepsilon^*T_\varepsilon
=\ell_\varepsilon^*F_\varepsilon^{\rm forb}\ell_\varepsilon$,
the strong assertion follows. This also shows that aligned actual inputs exist mathematically, for example $u_\varepsilon=T_\varepsilon\Psi$; it supplies no preparation procedure.

For the norm assertion retain exactly75.11's normalized same-cable target form vector supported in the interior diagonal strip $|x-y|<R_\varepsilon/4$, vanishing on the diagonal and all outer traces. Its raw spatial lift is entirely forbidden for small $\varepsilon$, because $R_\varepsilon/\varepsilon\to\infty$ in either hard schedule. Tensor any nonzero field/auxiliary unit vector. This is a unit kernel vector for $T_\varepsilon$, while $0\le I-T_\varepsilon^*T_\varepsilon\le I$. Hence its norm is one. The vector depends on $\varepsilon$ and has diverging particle energy as already quantified in75.11; it does not contradict the fixed-vector assertion. $\square$

**Theorem 78.9 (full joint dynamics on aligned actual inputs).** Fix any $\Psi\in\mathcal X$, any fixed auxiliary Hilbert space and any actual input family
$u_\varepsilon\in\mathcal P_\varepsilon^{\rm a}\otimes\mathcal F_H\otimes\mathcal A$
satisfying

$$
\|\iota_\varepsilon u_\varepsilon-\ell_\varepsilon\Psi\|
                 \longrightarrow0.
\tag{78.44}
$$

No field-number, energy, vacuum or product-input condition is imposed on this fixed vector. For every finite $T\ge0$,

$$
\sup_{|t|\le T}
\|\iota_\varepsilon e^{-it\mathsf M_\varepsilon}u_\varepsilon
       -\ell_\varepsilon e^{-it\mathsf M_D}\Psi\|
                 \longrightarrow0 .
\tag{78.45}
$$

The reference evolves by $e^{-it\Omega h}$ on every field state, including its correlations with particle and auxiliary branches.

**Proof.** First establish the continuous functional calculus actually needed on these varying carriers. For a continuous compactly supported $f$ on $\mathbb R$, restrict to the common spectral half-line $[-L_0,\infty)$ and define
$g(t)=f(t^{-1}-\sigma)$ for $t>0$, $g(0)=0$, on $[0,b_*]$. It is continuous at zero. Approximate $g$ uniformly by polynomials with zero constant term: subtract the value at zero from any ordinary polynomial approximation. Products of either zero-extended shifted resolvent equal the corresponding lifted powers, because $\iota_\varepsilon^*\iota_\varepsilon=I$ and $\ell_\varepsilon^*\ell_\varepsilon=I$. The norm convergence in(78.29), polynomial telescoping, and uniform approximation therefore prove

$$
\left\|\iota_\varepsilon f(\mathsf M_\varepsilon)\iota_\varepsilon^*
       -\ell_\varepsilon f(\mathsf M_D)\ell_\varepsilon^*\right\|
                       \longrightarrow0 .
\tag{78.46}
$$

Only functions vanishing at infinity are used here; assigning the wrong value to the zero complement would invalidate this argument.

Choose continuous $0\le\chi_m\le1$ with compact support and $\chi_m=1$ on $[-m,m]$, tending pointwise to one. The target spectral theorem gives
$\|(I-\chi_m(\mathsf M_D))\Psi\|\to0$.
For each fixed $m$, the family
$f_{m,t}(x)=e^{-itx}\chi_m(x)$, $|t|\le T$, is compact in the uniform norm: it is continuous in $t$ uniformly on its fixed compact support. A finite uniform net, the functional calculus contraction and(78.46) prove its convergence uniformly for $|t|\le T$.

Here is the complete tail passage, retaining the actual input. Write
$v_\varepsilon=\iota_\varepsilon u_\varepsilon$,
$d_\varepsilon=\|v_\varepsilon-\ell_\varepsilon\Psi\|$,
$b_m=\|(I-\chi_m(\mathsf M_D))\Psi\|$,
and let $\alpha_{\varepsilon,m}$ and $\beta_{\varepsilon,m,T}$ denote the norms in(78.46) for $\chi_m$ and the supremum for $f_{m,t}$. The actual high-energy tail satisfies

$$
\|\iota_\varepsilon(I-\chi_m(\mathsf M_\varepsilon))u_\varepsilon\|
       \le2d_\varepsilon+b_m+\alpha_{\varepsilon,m}\|\Psi\|.
\tag{78.47}
$$

Indeed subtract $\ell_\varepsilon\Psi$, use the cutoff comparison on that vector, and then add the target tail; the cutoff operator has norm at most one. The low-energy time comparison is at most
$d_\varepsilon+\beta_{\varepsilon,m,T}\|\Psi\|$.
Unitarity on the actual carrier preserves the actual tail norm, and target unitarity preserves $b_m$. Therefore the left side of(78.45) is at most

$$
3d_\varepsilon+2b_m+
       (\alpha_{\varepsilon,m}+\beta_{\varepsilon,m,T})\|\Psi\|.
\tag{78.48}
$$

First let $\varepsilon\downarrow0$ with $m$ fixed, and then $m\to\infty$. This proves(78.45) for every full target joint vector. The cutoffs are proof approximations removed by the last limit, not a changed target, a final cutoff, an input moment promise or a physical control. All arguments are on full tensor spaces, so arbitrary auxiliary and reference correlations are retained. On the reference the couplings and kinetic operator are zero by definition, proving its stated full field evolution. $\square$

**Proposition 78.10 (failure of full-number norm convergence).** The half-number conclusion cannot be replaced by
$\|(\mathsf n+I)\Delta_\varepsilon(-\sigma)\|\to0$.
In fact, for every fixed commission in this chapter with nonzero auxiliary space, either installation and either complete field prescription, there is a bank eigenvalue $f>0$ such that for every $\varepsilon$

$$
\|(\mathsf n+I)\Delta_\varepsilon(-\sigma)\|
                         \ge\frac1{\Omega f}.
\tag{78.49}
$$

Here the product is an everywhere bounded operator for each fixed $\varepsilon$; its norm nevertheless fails to vanish. This is a boundary within the declared apparatus model, not a physical impossibility statement.

**Proof.** Work in the one-position sector, where the actual and ambient particle spaces agree. The raw one-position isometry has a nonzero proper-range complement, for example a mean-zero nonconstant chamber function. Choose a unit vector $v$ in this complement and a unit auxiliary vector. Choose a unit eigenvector of $\widehat F_D^\diamond$ with eigenvalue $f>0$, and let $\xi_j$ be its normalized $j$-boson number vector. Set $v_j=v\otimes\xi_j$ with that auxiliary vector. Since $\ell_\varepsilon^*v_j=0$, the entire lifted coupled target resolvent annihilates $v_j$.

Let $R=R_\varepsilon$ on this sector, $V=V_\varepsilon$, and $C=\mathcal R_\varepsilon(-\sigma)$. The free operator on $v_j$ is the one-position particle resolvent at $\sigma+\Omega f j$. The particle spectral theorem gives

$$
(j+1)\langle v_j,Rv_j\rangle\longrightarrow(\Omega f)^{-1}
                    \quad(j\to\infty).
\tag{78.50}
$$

For the coupled correction, $V_{\varepsilon,0}$ preserves number and the charge changes it by exactly one. For $j\ge2$, therefore,

$$
\|RVRv_j\|
 \le\frac{M_0+2\sqrt2 k_f\sqrt{j+1}}
              {(\sigma+c(j-1))(\sigma+\Omega f j)}
 =O(j^{-3/2}).
\tag{78.51}
$$

Indeed the rightmost resolvent preserves number $j$, the middle output is in the orthogonal sum of number sectors $j-1,j,j+1$, and the leftmost resolvent has norm at most $(\sigma+c(j-1))^{-1}$ there. All constants may be held fixed for this commission. The inverse bound of78.6 and
$C-R=-(I+\overline{RV})^{-1}RVR$
give $\|(C-R)v_j\|=O(j^{-3/2})$. Thus(78.50) remains true with $C$ in place of $R$.

By(78.13) each actual and target resolvent maps into $\operatorname{Dom}\mathsf n$. The operators $(\mathsf n+I)C$ and $(\mathsf n+I)\mathcal S_\varepsilon(-\sigma)$ are bounded by the closed graph theorem. On the unit vector $v_j$,

$$
\left|\left\langle v_j,
       (\mathsf n+I)\Delta_\varepsilon(-\sigma)v_j\right\rangle\right|
 =(j+1)|\langle v_j,Cv_j\rangle|
                   \longrightarrow(\Omega f)^{-1}.
\tag{78.52}
$$

Taking the supremum proves(78.49). This uses arbitrarily large number states; it is consistent both with the half-number estimate and with78.9's fixed-vector conclusion. $\square$

**Proposition 78.11 (full-carrier geometric covariance and the precise renewal boundary).** A rigid Euclidean motion of a fixed commissioned assembly, with grounding, chamber labels, cylinder coordinates and exclusion transported with it, induces a unitary on every full spatial particle carrier. Tensoring with field and auxiliary identity conjugates its spatial generator, its form and operator domains, zero extensions, raw lifts and every comparison above to the corresponding transported objects. It retains both quadratures and the complete reference field.

For an actual accepted whole-rho, let $\mathsf T=I_r\oplus\mathsf T_{D'D,1}\oplus\mathsf T_{D'D,2}$ be66.2's full stratified inclusion, and keep67's same fixed bank with field identity. It maps the full target coupled form domain into the next one and obeys the exact form update

$$
\begin{aligned}
\mathfrak m_{D'}[(\mathsf T\otimes I)\Psi]-\mathfrak m_D[\Psi]
={}&\Omega\langle\Psi,I\otimes(h_{D'}-h_D)\Psi\rangle\\
 &+\frac\nu2\sum_{p\in D}
       \bigl(G_{D'}^\diamond(p,p)-G_D^\diamond(p,p)\bigr)
                 \langle\Psi,m_p\otimes I\,\Psi\rangle .
\end{aligned}
\tag{78.53}
$$

Here $\mathfrak m$ is the complete form of(67.5), and the field difference is its quadratic form on $\operatorname{Dom}\mathsf n^{1/2}$. For the common prescription the old diagonal differences are zero; for killed they are the actual inverse updates. Neither(78.53) nor78.7 supplies a physical spatial renewal map or an exact propagator intertwiner. Accepted Left/Right grafts retain66.8's separate boundary.

**Proof.** Pullback by a rigid motion preserves Lebesgue measure, gradients, distances, symmetric exchange, transported Dirichlet traces and the nonnegative penalty. It sends every chamber indicator to its labelled transported indicator. The raw-map formulas use exactly these chambers, transverse measures and intrinsic longitudinal coordinates, so their maps and adjoints intertwine with this unitary. The field operator and its canonical coordinates are unchanged. Substitution in the closed forms and uniqueness of their represented operators prove the conjugacies, including the full proper-range complements. This is mathematical placement covariance for an assembly with transported data; it does not supply an original actor operation.

For whole-rho,66.3 supplies the full isometry, composition law, kinetic-form equality and all literal target trace matches, including the old ground tips assigned new atomic value zero. On every old stratum
$m_{D',p}\mathsf T=\mathsf Tm_{D,p}$ for $p\in D$, while the counts at newborn ports annihilate $\mathsf T$. This follows directly by counting the copied coordinates, so it holds on all old Hilbert data, not just harmonic inputs. Old depths and $\phi$ are unchanged. Consequently the linear charge and one-body forms agree on the image, and the compensation difference is exactly the second line of(78.53). The field bank is retained with identity, so its contribution is exactly the first line, on reference as well as particle branches.

The field form difference is well defined: the finite matrices have a bounded difference and
$|\langle\Psi,d\Gamma(\widehat F_{D'}-\widehat F_D)\Psi\rangle|
\le\|\widehat F_{D'}-\widehat F_D\|\langle\Psi,\mathsf n\Psi\rangle$.
Thus the common number form domain is retained. Combined with66.3's particle form inclusion this proves the domain assertion and(78.53), first on finite field tensors and then by form continuity. For common, the inverse is the restriction of the same infinite kernel, hence every old diagonal agrees; for killed,62.4 and(66.5) give the actual complete update.

The kinetic statement is an equality of forms on an isometric image, with no assertion of equality of operator domains. Moreover $h_{D'}$ changes on the retained bank even when old common static pair coefficients agree. Arbitrary unknown field states cannot be replaced by a new vacuum. The theorem therefore does not identify the two idle propagators across renewal. At a beta-empty acceptance the geometry and commissioned generator are unchanged but the actual labels and record still update; Read and refusal retain67.7's original identity action on quantum factors and actual classical record. Distinct grafts are not these inclusions. A source-owned spatial implementation and switching certificate, including its complete correlations, clock and error, remains an additional requirement. $\square$

**Definition 78.12 (exact scope and all retained obligations).** The proved conditional assertion is78.7–78.9, with78.3–78.6 supplying the domain-safe mechanics and78.10 the full-number boundary. It supplies the fixed-commission interacting spatial generator comparison missing in77.10 for the explicitly installed chamber-count/balanced-field model. The target remains precisely(67.5) on64.5. On its literal fibres(78.12) has no extra diagonal term, so67.7 gives both original complete pair laws with their unchanged one-body field and actual compensation. All ten entries of each64.1/75.15 witness table, all its diagonals, the original $H3$ complete $2/3/5$ history, and all seven modes at cap three remain. Formula(78.5), not this finite witness, specifies every pair in general $D$.

Every duty in77.10 and its cited66.10,67.11,68.7,71.2,72.13 and75.16 persists, subject only to the conditional fixed-commission generator comparison just proved. In particular the following boundaries are part of the assertion.

The original history, immutable INITIAL, source-independent actor initialization, actual contexts and versions, cap, labels, brackets, left/right order, distinct occurrences, whole-candidate guards, every acceptance and refusal, original Read, acquired chronological records and absorbing Stop are unchanged. There is no event after an infinite prefix or after Stop. The original actor's arbitrary, unbounded or possibly zero $a$, untagged radius-$7/25$ $b$, destructive actions and joint adversarial or history-dependent errors are not the positive commissioned parameters here. Whole-rho, beta-empty updates and separate grafts keep their actual domain, degree, field, dynamic and record duties. No declined candidate is installed or observed.

The entire reference plus one- and two-position particle carrier, every oscillator excitation and unused spectator, both canonical quadratures, all auxiliary factors and every unknown joint correlation remain. The mathematical aligned-family premise(78.44) supplies no acquisition, recovery, copying or preparation procedure. The fixed-vector spatial conclusion does not remove67's moment/energy ingress conditions for its separate source-uniform $\delta,\Omega$ estimates. Neither a hidden growing-energy input family nor unrestricted unitary operator norm is covered by78.45. The no-full-number result78.10 is distinct from67.8's no-unrestricted-scaling comparison. There is no licensed partial trace, reset, vacuum replacement, independent resampling, final projection or final cutoff.

This spatial limit is only $\varepsilon\downarrow0$ with the commission fixed. The hard mesoscopic alternative and finite-height schedule remain separate75 hypotheses. No joint limit with $\delta\downarrow0$ or $\Omega\uparrow\infty$, source-growing estimate, effective finite precision schedule, uniform acquisition class or unbounded time horizon is inferred. Applying67's later moment-dependent limit would require its own quantitative promises and its separate order of choices. The present $C_0$ error is a complete supplier error, not an asserted explicit computable thinning rate for75's hard-core theorem.

Original operation and metric correspondence, unknown-state ingress and recovery, original Read/Stop covariance and source-owned switching remain requirements. Proposition78.11 provides mathematical placement covariance and the actual stratified form update, not a physical renewal implementation. Its retained bank is not a dynamic exterior for the infinite common kernel. A Hilbert isomorphism, copied source, static coefficient fit, observer encoding or re-preparation does not supply these requirements. A native JointLaw on its own carrier does not by itself establish spatial-carrier correspondence.

The common $\Pi$ of63.13 retains full-vector and spanning assumptions, common zero, the whole quadratic-distance/positive-semidefinite Gram law, at least two independent directions, alternating bilinear exact-area/Jacobi law, actual orthonormal probes, finite binary calibration and hidden-kernel-preserving generator conditions. Reference preparation, normal-ordering calibration, the common actual clock, every clock conversion, finite execution and precision certificates remain separate. The time $t$ in78.45 is the same declared comparison clock on every branch; it has no newly proved conversion to native events, physical time or paid ticks.

All three acquisition contracts retain their distinct sources, domains and prices. The immutable composition-promised endpoint contract of57 keeps its fixed depth caps, common source-independent initialization, actual query/reply histories, finite correct stopping on every promised positive and negative source and distinct actual-address fees, without an old-source archive. The separate paid positive-root archive/exact nonadvancing-cut contract keeps its exact port, finite stopping and decoding, protected written records after refusal or closure, aligned actual generation, trusted markers, no unrecorded source change, closed strong ports and actual paid write/protect/retain/query rights. All reply-affecting retained source influence belongs in that service price. The phase-coherent full-tail contract keeps its separate once-sampled-depth actual Read process and paid stopped transcript. None supplies cloning, reset, independent resampling, unknown joint-state preparation or exact-limit Read, and none transfers its radii, finite-state counts, update matrices or clock to this spatial theorem.

Actual local and isotropic physical mediation, balanced momentum coupling, stiffness and compensation installation, the original spatial operation/metric bridge, packing, transverse, exterior, leakage and collision controls remain supply obligations. Conditional chamber counts, step fields, ideal exclusion or finite repulsion and the field bank are mathematical apparatus, with no native or physical realization assertion. Every construction, acquisition, preparation, stiffness/compensation/coupling installation, exclusion or repulsion control, switching, source service, production, storage, hold, retention, maintenance and precision charge remains material, including service durations, reference and clock calibration and total lifetime price. Normalized measures, exact lengths, stratum counts and infinite-dimensional intervals and cells yield neither measured physical prices nor a finite digital-memory advantage.

The theorem holds in each fixed $s\ge3$ supplied by72's geometry. The planar obstruction of77 retains exactly its proved prescribed-metric scope. These facts supply neither unique physical dimension three nor a global physical impossibility. Native execution and physical realization require the separate source, field, acquisition, clock and resource correspondences specified above.

**References 78.13 (primary versions, conditions and exact reuse).** The target and spatial premises are55.1,55.6,62.2–62.4,64.1,64.5–64.7,66.1–66.10 and67.1–67.11 in the [first continuation](https://github.com/the-omega-institute/trureturing/blob/b1df53cfbe595dbfba90eab2299e049f11ade7a0/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md), and72–75,77.10 in the [second continuation](https://github.com/the-omega-institute/trureturing/blob/b1df53cfbe595dbfba90eab2299e049f11ade7a0/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md). The [original full source volume](https://github.com/the-omega-institute/trureturing/blob/b1df53cfbe595dbfba90eab2299e049f11ade7a0/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md) retains all its earlier source/actor boundaries.

Tosio Kato, *Perturbation Theory for Linear Operators*, corrected printing of the second edition, Springer,1980, reprinted in Classics in Mathematics,1995, ISBN3-540-58661-X, [primary book scan](https://www.maths.ed.ac.uk/~v1ranick/papers/kato1.pdf), supplies the following precise statements. IV.1.16, printed p196, assumes an invertible closed $T$ with bounded inverse and a $T$-bounded perturbation with $\|Au\|\le a\|u\|+b\|Tu\|$, $a\|T^{-1}\|+b<1$, and proves bounded invertibility by $(T+A)^{-1}=T^{-1}(I+AT^{-1})^{-1}$. IV.3.17, printed p214, uses $a\|R(\zeta,T)\|+b\|TR(\zeta,T)\|<1$ at a resolvent point for the corresponding perturbed resolvent. V.4.3, printed p287, assumes a self-adjoint $T$ and symmetric $T$-bounded $A$ with relative bound strictly below one, and gives self-adjointness of $T+A$ on $\operatorname{Dom}T$. The primary proof of IV.1.16 exhibits the sufficient bounded-product condition $\|AT^{-1}\|<1$ used directly in78.32; no scalar-bound hypothesis is silently substituted. Proposition78.4 checks the symmetry, domain inclusion and relative bound before invoking V.4.3. The identities and the two quantitative transfer estimates needed here are proved in78.5–78.7; these book theorems do not themselves supply a thinning or all-Fock comparison.

Gerald Teschl, *Mathematical Methods in Quantum Mechanics: With Applications to Schrödinger Operators*, Graduate Studies in Mathematics99, AMS,2009, [author's online edition](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), version explicitly marked February12,2009, gives Theorem6.4, printed p135, the symmetric relative-bound-less-than-one Kato–Rellich theorem with unchanged operator domain; Theorem6.24, printed p150, the KLMN theorem for a semibounded closed Hermitian form and a Hermitian perturbation of relative form bound less than one; and Theorem6.25, pp150–151, the form-resolvent representation framework. Theorem6.31, printed p154, gives continuous functional calculus under ordinary norm/strong resolvent convergence, and Corollary6.33, pp154–155, gives strong convergence of unitary groups under strong resolvent convergence. Its subspace convention in Section6.6 requires the subspace projections to converge strongly to identity. Those results do not directly identify the varying raw maps here, and the exponential does not satisfy the norm-calculus condition at spectral infinity. The zero-complement polynomial argument, the aligned-family passage and uniformity on finite time intervals are instead proved explicitly in78.8–78.9. No form-resolvent sign convention from6.25 is needed in those proofs.

Sabine Bögli, [*Convergence of sequences of linear operators and their spectra*, arXiv:1604.07732v1](https://arxiv.org/pdf/1604.07732v1), Theorem3.3 and equations(17)–(20), PDF pp12–13, concerns generalized **strong** resolvent convergence on closed subspaces of a common ambient Banach space. It requires domain inclusions, one common resolvent point, strict target perturbation bound, a uniform approximant bound $\gamma<1$, and both strong convergence of the extended free resolvents and strong convergence of the perturbation-times-resolvent products. It supplies the mature inverse mechanism, not the norm rate in(78.29). Here those bounded products and their quantitative differences are checked by(78.21),(78.23),(78.27), rather than assuming that strong convergence upgrades to norm convergence.

Olaf Post and Sebastian Zimmer, [*Generalised norm resolvent convergence: comparison of different concepts*, arXiv:2202.03234v1](https://arxiv.org/pdf/2202.03234v1), Definition1.1, PDF p2, uses self-adjoint operators, isometries into one parent Hilbert space and norm convergence of their extended resolvents at a common resolvent point. Definition1.4, PDF p4, gives quasi-unitary equivalence with bounded identification maps, resolvent-weighted defects of both identity products, the intertwining defect, and the conjugate-resolvent conditions for a nonreal base point. Theorem1.7, PDF p5, proves equivalence of the two convergence concepts for self-adjoint families. These are framework citations, not a theorem giving physical maps or replacing the restricted contraction by an isometry. In particular unweighted norm convergence of $I-T_\varepsilon^*T_\varepsilon$ is not one of those hypotheses;78.41 demonstrates its failure here. The present comparisons are proved in each actual common ambient carrier by the explicit maps, so no unprovided universal parent embedding is required.

The mature spatial theorem consumed through72 is K.D. Cherednichenko, Yu.Yu. Ershova and A.V. Kiselev, [*Norm-resolvent convergence for Neumann Laplacians on manifolds thinning to graphs*, arXiv:2205.04397v4](https://arxiv.org/html/2205.04397v4), Sections2–3 and Theorem4.5, with its massive-vertex operator equations(16)–(18). Its finite connected all-Neumann double, straight cylinders, resonant chamber volumes, contact geometry and local analytic hypotheses are checked by72.4–72.10 before odd grounding. Only its fixed nonreal compact-set, full-resolvent conclusion in that accepted scope is reused. Chapters73–75 supply the complete product/hard-core domains, spatial recovery, arbitrary-forcing compactness proof and the exact hard/finite-height alternatives; no interacting conclusion is imported from this Neumann supplier.

Creation/annihilation relative bounds and Weyl displacement algebra are the mature field methods already cited with exact scopes in67.10, including Takaesu arXiv:1004.4261v2, §2.1 equations(4)–(5), and Suzuki's RIMS Kôkyûroku1510, §2 Proposition2.2/Corollary2.3 and §3.3 Theorem3.1/Corollary3.2. The estimates and fibre algebra used in this chapter are written in78.3. In particular Suzuki's unbounded-system invariant-domain/commutator assumptions are not available for these discontinuous counts, and his qualitative vacuum scaling theorem is not invoked for78.7 or78.9. Neither a reduced-state thermal theorem nor a vacuum theorem supplies a full retained-correlated-state conclusion.

The deductions specific to these carriers are the exact chamber-count covariance, corrected full spatial charge, common-ambient norm/half-number transfer, compact nonreal continuation, aligned full-joint dynamics and full-number obstruction proved above. Inverse perturbation, self-adjoint form theory, field algebra and the established source/particle limits are reused prior mathematics. Each external supplier is used only for its stated intermediate results.

## 78.99 追加锚（本行以下为增补区）

## 79. Literal whole-rho copying and additive form-domain completions

**Definition 79.1 (current renewal, full domains and the additive completion class).** Fix the authentic accepted current event at cap $H=2$

$$
\beta\longmapsto\langle\beta,\alpha\rangle,
\qquad D_-=\{o\},\qquad D_+=\{o,L,R\},
\tag{79.1}
$$

with commissioned $a,g>0$, $\nu\ge0$, $0<\delta\le1$ and finite $\Omega\ge1$. The word current is essential: INITIAL is the immutable source of55.1,60.1 and66.1, and need not be $\beta$. In particular an earlier accepted $\alpha\mapsto\beta$ can precede(79.1), with its label, epoch and record change retained. The current whole candidate has two leaves and passes the original cap guard at equality. No INITIAL promise, earlier history or source-independent initialization is replaced by this event specification.

Use64.5's complete particle carriers and67.1's reference and field:

$$
\begin{aligned}
\mathcal K_\pm
 &=\mathbb Cr\oplus\mathcal K_{D_\pm,1}
                      \oplus\mathcal K_{D_\pm,2}^{\rm hc},\\
\mathcal E&=\mathcal F_2\otimes\mathcal A,
&\mathcal F_2&=\Gamma_s(\ell^2(\{o,L,R\})),
&\mathcal A&\ne\{0\},\\
\mathcal H_\pm&=\mathcal K_\pm\otimes\mathcal E.
\end{aligned}
\tag{79.2}
$$

Here $\mathcal A$ is any nonzero Hilbert space. All three oscillator modes, both canonical quadratures, every excitation and every spectator are retained under either complete common or complete killed prescription, separately. The Hilbert spaces contain arbitrary unknown particle, reference, field and auxiliary correlations. The field vacuum used below is one test vector in these spaces, not an input promise.

The particle domain is first specified on ordered two-position strata as in64.5, and only then restricted to exchange-symmetric functions. Keep every distinct atomic pair, both orientations of every atom/cable slice, every different-cable rectangle, and both triangles of every same-cable cell. The Hilbert weights are $1,\delta,\delta^2$; the kinetic form is exactly(64.7), with unit slice derivative coefficients and coefficient $\delta$ for cell derivatives. Rectangle boundaries match the corresponding slices; slice endpoints match the atomic pairs, with the missing $(p,p)$ coordinate assigned zero. Ground traces and both same-cable collision traces vanish. Shared-port collisions retain those slice endpoint conditions, without a corner trace for a general two-dimensional $H^1$ function. The one-position cable traces match the mass-one atomic ports. In particular $D_-$ still has its nonzero full two-position continuum carrier;66.3a supplies an admissible mixed vector even though its discrete two-occupation target is zero.

Write $k_\pm$ for the sum of the two particle kinetic forms, zero on $r$, extended as closed Hilbert-valued forms to $\mathcal H_\pm$. Let

$$
b_\pm^0[\Psi]=\|\Psi\|^2+a k_\pm[\Psi]
                 +\Omega\|(I\otimes\mathsf n^{1/2}\otimes I)\Psi\|^2,
\qquad \mathcal D_\pm=\operatorname{Dom}b_\pm^0.
\tag{79.3}
$$

Thus $\mathcal D_\pm$ is the complete field/auxiliary-valued particle form domain intersected with the number form domain, including the reference field. It is not the algebraic tensor product or a calibrated range. Closedness and density are the existing64.5a and67.3 assertions;67.3 and78.4 identify it also as the complete form domain of the unchanged coupled generator $\mathbb M_{D_\pm}$.

Let $\mathcal R_\pm$ be arbitrary additional Hilbert spaces, possibly zero or infinite-dimensional, with densely defined closed nonnegative forms $r_\pm$. Define the orthogonal additive completion by

$$
\begin{aligned}
\mathcal X_\pm&=\mathcal H_\pm\oplus\mathcal R_\pm,
&\mathcal Q_\pm&=\mathcal D_\pm\oplus\operatorname{Dom}r_\pm,\\
b_\pm[\Psi\oplus z]
 &=b_\pm^0[\Psi]+\|z\|^2+r_\pm[z],
&i_-\Psi&=\Psi\oplus0,\\
P_-&=i_-i_-^*,
&J\Psi&=((\mathsf T\otimes I_{\mathcal E})\Psi)\oplus0,\\
\mathsf T&=I_r\oplus\mathsf T_{D_+D_-,1}
                       \oplus\mathsf T_{D_+D_-,2}.
\end{aligned}
\tag{79.4}
$$

The maps $\mathsf T_{D_+D_-,N}$ are the literal66.2 maps, defined on all old Hilbert data before exchange restriction: they copy the two old open stubs as the seams $oL,oR$, copy every old stratum in each coordinate, and assign zero to every stratum involving a newborn atom or cable. The zero assigned at a new atom is independent of an $L^2$ representative's value at the old mass-zero ground tip. Theorem66.3 supplies their full isometry and one-way form inclusion, so $J$ is an isometry. Its adjoint is weighted Hilbert restriction to the copied old strata, and $P=JJ^*$ is the orthogonal projection onto precisely that range, with zero reserve component. Additivity gives $P_-\mathcal Q_-\subseteq\mathcal Q_-$ and $b_-[P_-u]\le b_-[u]$.

A candidate completion is one fixed linear unitary $U:\mathcal X_-\to\mathcal X_+$, independent of the input vector, with both complete domain inclusions

$$
U\mathcal Q_-\subseteq\mathcal Q_+,
\qquad U^*\mathcal Q_+\subseteq\mathcal Q_-;
\quad\text{equivalently }U\mathcal Q_-=\mathcal Q_+.
\tag{79.5}
$$

Its inverse is its actual Hilbert adjoint. These conditions permit joint action on the completed spaces; in particular they include particle/reserve maps tensored with field and auxiliary identities. Exact literal copying means $Ui_-=J$ on the entire $\mathcal H_-$, and therefore fixes the retained field and auxiliaries on every copied vector. The reserve coordinate zero in $i_-$ is an orthogonal-summand coordinate, not a vacuum or clean-state promise for an independently occupied tensor factor. The domain and energy conditions concern all reserve inputs as well.

**Theorem 79.2 (no exact additive two-sided completion of this literal inclusion).** For every choice in79.1 there is no unitary satisfying both(79.5) and $Ui_-=J$. No bounded-energy constant, finite reserve dimension or field cutoff is needed for this impossibility. It excludes this two-sided additive upgrade of78.11's full one-way form inclusion, not that inclusion itself.

**Proof.** Orient $oL,oR$ from $o$ to the respective child, and each newborn grounded stub from its child to ground. Define a scalar one-position outlet vector $F$ by

$$
\begin{gathered}
F(o)=0,\qquad F(L)=1,\qquad F(R)=0,\\
F_{oL}(x)=x,\qquad
F_{L,\mathrm{ground},1}(x)=F_{L,\mathrm{ground},2}(x)=1-x,\\
F_{oR}(x)=F_{R,\mathrm{ground},1}(x)
                         =F_{R,\mathrm{ground},2}(x)=0.
\end{gathered}
\tag{79.6}
$$

There are exactly six outlet cables: two seams promoted from the old stubs and four newborn grounded stubs. The three displayed nonzero cable functions and the three zero functions exhaust them. Every cable endpoint equals its incident atomic value, and every outer grounded value is zero. Set the reference and entire two-position component to zero. Hence $F$ is in the full outlet particle form domain. Directly in64.5's norm and kinetic coefficients,

$$
\|F\|^2=1+\delta,
\qquad a k_{\delta,D_+,1}[F]=3a.
\tag{79.7}
$$

Choose a unit $\zeta\in\mathcal A$, let $\eta=|0\rangle_{\mathcal F_2}\otimes\zeta$, and put $f=(F\otimes\eta)\oplus0\in\mathcal Q_+$. Its field-number energy is zero and $b_+[f]=1+\delta+3a$. The nonzero auxiliary assumption ensures this is a nonzero vector.

The copied-range projection $P$ keeps the seam function $x\eta$ on $oL$ and the old root value zero, while deleting the newborn $L$ atom and both its new grounded-stub functions. Thus the seam endpoint at $L$ is $\eta$ but the projected atomic value there is zero. Consequently $Pf\notin\mathcal Q_+$. This is a one-dimensional endpoint mismatch in the actual outlet domain; it uses no two-dimensional corner value and removes no two-position stratum from the quantified carrier.

On the other hand exact copying and unitarity imply

$$
UP_-U^*=(Ui_-)(Ui_-)^*=JJ^*=P.
\tag{79.8}
$$

For $f\in\mathcal Q_+$, the reverse inclusion in(79.5) places $U^*f$ in $\mathcal Q_-$, the additive projection $P_-$ keeps it there, and the forward inclusion places $UP_-U^*f$ in $\mathcal Q_+$. This contradicts the preceding endpoint mismatch. The argument uses the standard conjugacy of range projections; the source-specific obstruction is that the projection onto66.2's copied strata fails64.5's newborn-port trace equality. The complete ordered trace conditions and their symmetric restrictions remain those supplied by66.3, not new collision assumptions. $\square$

**Theorem 79.3 (necessary full-carrier defect and two-sided energy inequality).** Keep79.1 and(79.5), but allow $Ui_-\ne J$. Suppose finite positive constants $C_+,C_-$ satisfy, on the entire respective form domains,

$$
b_+[Uu]\le C_+b_-[u]\quad(u\in\mathcal Q_-),
\qquad
b_-[U^*v]\le C_-b_+[v]\quad(v\in\mathcal Q_+).
\tag{79.9}
$$

Define the full old-carrier operator norm and the constants

$$
h=\|Ui_--J\|_{\mathcal B(\mathcal H_-,\mathcal X_+)},
\qquad K=C_+C_-,
\qquad B=1+\delta+3a,
\qquad e=2h\sqrt{1+\delta}.
\tag{79.10}
$$

Whenever $e<1$ it is necessary that

$$
(1-e)^2\le\frac{e^2}{\delta}
 +\frac{2e}{\sqrt\delta}
             \left(\sqrt{\frac{KB}{a}}+1\right).
\tag{79.11}
$$

If $e\ge1$, then already $h\ge1/(2\sqrt{1+\delta})$ and this small-defect regime is absent. The inequality is necessary, with no assertion of sufficiency or sharpness. The norm $h$ ranges over every normalized old Hilbert input, including vectors outside the energy form domain. The energy inequalities hold for every vector in their complete form domains, without a common input-energy ceiling. All retained modes and arbitrary correlations are included.

**Proof.** Set $V=Ui_-$ and $P_U=VV^*=UP_-U^*$. Both $V$ and $J$ are isometries. The standard range-projection estimate gives

$$
\|P_U-P\|
\le\|(V-J)V^*\|+\|J(V^*-J^*)\|\le2h.
\tag{79.12}
$$

Use exactly the vector $f$ from79.2 and let $w=P_Uf$. Both directions of(79.5) give $w\in\mathcal Q_+$; both inequalities in(79.9) and the additive form contraction give

$$
b_+[w]\le C_+b_-[P_-U^*f]
          \le C_+b_-[U^*f]\le Kb_+[f]=KB,
\qquad \|w-Pf\|\le e.
\tag{79.13}
$$

Let $g$ be the entire $\mathcal E$-valued one-position component of $w$. It belongs to the actual one-position form domain, so $g_{oL}(1)=g_L$. The mass-one $L$ atom, cable density $\delta$ and unweighted derivative coefficient $a$ imply

$$
\|g_L\|_{\mathcal E}\le e,
\qquad \|g_{oL}-x\eta\|_{L^2(0,1;\mathcal E)}
                        \le\frac e{\sqrt\delta},
\qquad \|g_{oL}'\|_{L^2(0,1;\mathcal E)}
                        \le\sqrt{\frac{KB}{a}}.
\tag{79.14}
$$

The other particle components and the reserve contribute nonnegative terms to(79.13); extracting this component does not assume $U$ preserves particle sectors or product states. For $v(x)=g_{oL}(x)-x\eta$, the standard Hilbert-valued $H^1$ endpoint estimate on the unit interval is

$$
\|v(1)\|^2\le\|v\|_{L^2}^2
                         +2\|v\|_{L^2}\|v'\|_{L^2}.
\tag{79.15}
$$

This is the usual one-dimensional Sobolev estimate obtained by the fundamental theorem for $\|v(x)\|^2$ and Cauchy–Schwarz; it is used here as a mature trace inequality. Since $\|\eta\|=1$, the endpoint relation gives $\|v(1)\|=\|g_L-\eta\|\ge1-e$ when $e<1$. Formula(79.14) gives $\|v'\|_{L^2}\le\sqrt{KB/a}+1$. Substitution in(79.15) proves(79.11), with the cable density and the kinetic coefficient in their distinct places.

The comparison class before imposing a small defect is nonempty. For example take $\mathcal R_-=\mathcal H_+$, $\mathcal R_+=\mathcal H_-$, with reserve forms $b_+^0-\|\cdot\|^2$ and $b_-^0-\|\cdot\|^2$, respectively. The exchange $U(\Psi\oplus\Phi)=\Phi\oplus\Psi$ is a unitary identifying both full form domains with $C_+=C_-=1$. Its defect is $h=\sqrt2$, since its old output is wholly in the outlet reserve and orthogonal to $J\Psi$. This example only shows consistency of the additive domain/energy hypotheses; it is no approximate literal transfer or physical renewal. $\square$

**Corollary 79.4 (coupled-energy conversion and the current certificate consumer).** At this renewal suppose a proposed completion satisfying(79.9) has finite upper budgets $0\le h\le\bar h$, $0<K\le\bar K$, and set $\bar e=2\bar h\sqrt{1+\delta}$. If $\bar e<1$ and

$$
(1-\bar e)^2>\frac{\bar e^2}{\delta}
 +\frac{2\bar e}{\sqrt\delta}
             \left(\sqrt{\frac{\bar K(1+\delta+3a)}a}+1\right),
\tag{79.16}
$$

these budgets are incompatible with the additive two-sided class. For any sequence satisfying(79.9) at fixed $a>0$ and fixed $\delta>0$, $h_j\to0$ forces $K_j\to\infty$; in particular bounded amplification in both directions cannot accompany vanishing full-carrier defect.

If energy bounds are supplied in other positive closed forms $E_\pm$ on exactly $\mathcal Q_\pm$, require explicit constants

$$
0<\ell_\pm\le u_\pm<\infty,
\qquad \ell_\pm b_\pm\le E_\pm\le u_\pm b_\pm.
\tag{79.17}
$$

Bounds $E_+[Uu]\le D_+E_-[u]$ and $E_-[U^*v]\le D_-E_+[v]$, with finite $D_+,D_->0$ on the entire respective domains, then permit the explicit choices

$$
C_+=\frac{D_+u_-}{\ell_+},\qquad
C_-=\frac{D_-u_+}{\ell_-},\qquad
K=\frac{D_+D_-u_-u_+}{\ell_-\ell_+}.
\tag{79.18}
$$

For the unchanged coupled source forms $\mathfrak m_{D_\pm}$ of(67.5), one concrete conversion uses78.4's constants

$$
\begin{gathered}
\lambda=3-2\sqrt2,\quad c=\Omega\lambda,\quad
k_f=\sqrt{\nu\Omega},\quad M_0=2g+\nu/\lambda,\\
L_0=M_0+c/2+4k_f^2/c,\qquad \sigma_0=2L_0+1>L_0,\\
E_\pm[\Psi\oplus z]
 =\mathfrak m_{D_\pm}[\Psi]+\sigma_0\|\Psi\|^2
                              +\|z\|^2+r_\pm[z],\\
\ell_-=\ell_+=\lambda/2,\qquad
u_-=u_+=u_0:=\max\{9,3L_0+1\},
\qquad K=(2u_0/\lambda)^2D_+D_-.
\end{gathered}
\tag{79.19}
$$

The positive reference energy forms in(79.19) include a strictly positive shift; they are not unshifted physical-energy prices. A different reserve energy or a coupled inlet form must establish its own domain and every constant in(79.17);(79.19) assigns none to it.

The consumer is a proposed stronger renewal implementation for78.11: when its ideal complete output is $J$, its actual old-input map $Ui_-$ can provide a66.7 full-map certificate only with a valid bound on the norm $h$ above, including any reserve output. Formula(79.16) rejects incompatible defect/amplification budgets for that class. The original66.7 admissible one-way isometries or unconditioned contractions do not require(79.5). Theorem67.7's moment-dependent retained-field/history estimate continues to use the one-way66.2 inclusion and is unaffected. No lower bound on the accumulated history error follows by reversing its upper error estimate or by treating $\sum_k h_k$ as a lower bound; possible cancellations are not excluded.

**Proof.** On $0\le e\le\bar e<1$, the left side of(79.11) decreases and its right side increases with $e$ and $K$. Thus(79.16) contradicts the necessary inequality. If $h_j\to0$ and some subsequence of $K_j$ stayed bounded, its left side would tend to one and its right side to zero. This proves the stated fixed-$a,\delta$ limit, including $K_j\to\infty$ rather than merely failure of a common bound.

Apply(79.17) on the two sides of each supplied energy inequality to obtain(79.18). For(79.19), reuse(78.16) on the target free form $t_\pm=a k_\pm+\Omega\langle h_{D_\pm}\rangle$. It gives

$$
\tfrac12t_\pm+(L_0+1)\|\Psi\|^2
\le \mathfrak m_{D_\pm}[\Psi]+\sigma_0\|\Psi\|^2
\le\tfrac32t_\pm+(3L_0+1)\|\Psi\|^2.
\tag{79.20}
$$

The same-field inequalities $\lambda\mathsf n\le h_{D_\pm}\le6\mathsf n$ give exactly $\ell_\pm=\lambda/2$ and $u_\pm=u_0$ against(79.3). The additive reserve norm obeys the same bounds because $\lambda/2<1\le u_0$. This uses the established form perturbation estimate, without asserting that atomic counts preserve kinetic domains or reproving fixed-commission78. Finally66.7's full-space norm hypothesis and67.7's isometric telescoping have no surjectivity requirement, which establishes the stated scope of the consumer. The argument supplies no $\delta$-uniform defect floor, joint thinning exclusion, field-scaling exclusion, work or clock lower bound, or monetary price. $\square$

**Definition 79.5 (inlet correspondence, surviving alternatives and literature scope).** The additive class is a mathematical comparison of the complete64.5/67 carriers at one authentic current event. It has no premise identifying an original physical source-times-reserve inlet with $\mathcal X_-$. In particular an independently occupied tensor inlet $\mathcal H_{\rm source}\otimes\mathcal H_{\rm reserve}$, with its joint collision and transmission domain, is not an orthogonal reserve summand by definition. To apply79.2 or79.3 to it requires an explicit faithful identification retaining every permitted source/reserve configuration, every sector, all field/reference/auxiliary correlations, the literal old-input comparison, both domain directions and the claimed energy constants. An abstract Hilbert isomorphism alone supplies none of those domain relations. Replacing that tensor promise by global total position number at most two, deleting occupied-reserve configurations, or installing a new collision wall after INITIAL is not such an identification. A newly prepared clean reserve would be a separate preparation/ingress premise, not a consequence of source-independent actor initialization. The direct-sum graft accounts of68 are different objects and are not a physical reserve contract for this whole-rho.

At finite spatial width retain72–75's actual old ground half-chambers $H_g^\varepsilon$ and their full function spaces, with the independently prescribed positive ground reference volumes $m_g$; they are not identified with $1/\delta$. The cylinder/ground contact plates are distinct from the grounded equators. The newborn source chambers $Z_L^\varepsilon,Z_R^\varepsilon$ have volumes $\varepsilon^{s-1}/\delta$ and hence effective atomic mass one, and each newborn child has two distinct new grounded unit stubs. Thus both old ground pieces and all four new grounded stubs need a declared correspondence; neither the old ground functions nor their plate traces may be discarded. A physical renewal still requires a source-compatible INITIAL ingress for every promised occupied configuration and a full ordered collision/transmission correspondence, before symmetry, in both directions with its actual inverse. The projection witness in79.2 is on the literal limiting carrier and does not furnish this finite-width construction or infer its impossibility.

The original source of55.1,60.1 and66.1, with78.12's complete obligations, remains the source of any application. In particular keep immutable INITIAL, source-independent actor initialization, fixed cap, labels, brackets, left/right order, equal-valued distinct occurrences, actual versions, complete supplied contexts, whole-candidate guards, original Read, every acceptance and paid refusal, beta-empty label/epoch updates and absorbing Stop. A refusal supplies no candidate Read; separate Left/Right grafts are not whole-rho. Keep actual chronological records and permissions, paid write/protect/retain/query and copy rights, write-before-latch release of complete records and responses, and each applicable COMPLETE condition. Partial paid histories, full tails and noncompletion remain possible under their original contracts; there is no event or observation after an infinite prefix, and Stop allows no new source service or quantum interaction. Its already prescribed finite record-delivery and consumer-output routines retain60.3's separate allowance.

An admissible positive route must still supply actual source-owned control authority, unknown-state ingress/recovery, unchanged Read/Stop behavior, the original operation and metric correspondence, finite duration and precision, and complete errors on its declared carrier. Compensation uses the diagonal of the same actual common or killed Green inverse as every pair coefficient; neither this inverse nor the control's actual inverse can be replaced by a fitted surrogate. Keep both field quadratures, every excitation and spectator and the full reference evolution on a single declared common comparison clock, with separately supplied conversion to source events, apparatus ticks and physical time. No partial trace, reset, vacuum replacement, independent resampling, postselection, normalization after a restricted contraction, input-dependent choice of a controller, or unpaid perfect hold is provided by the comparison. Construction, preparation, storage, retention, hold, acquisition, source service, control, stiffness/coupling/compensation, collision/exterior/leakage control and precision costs remain separate from reference-form energy and error amplification; all actual resource accounts and lifetime charges remain due.

The one-way inclusion and unconditioned-contraction route, nonadditive or coupled-reserve domains, controlled nonzero full-map defect, fixed-vector or energy-limited comparisons, growing amplification, and genuinely geometric or varying-domain transport are not excluded by79.2–79.4. Each needs its own original-input inclusion and operational certificate. The separately quantified finite-height alternative remains precisely75.13's full mixed-ground product domain, fixed $\kappa>0$, $R_\varepsilon=\kappa\varepsilon^{(s-1)/s}$ and finite $\Lambda_\varepsilon\ge0$ with $\Lambda_\varepsilon R_\varepsilon\to\infty$, under78.1's fixed commission. It is not an executed switching law or a theorem for a different joint schedule. The limit restriction in79.4 fixes $a,\delta$; it neither rules out $\delta\downarrow0$ jointly with other changes nor supplies a uniform input-energy promise. The spatial comparisons of78 remain conditional for every fixed $s\ge3$, with77's planar result only in its prescribed-metric scope. The present trace obstruction selects no physical space dimension, gives no universal actuator no-go and supplies no physical renewal or full-history realization.

The exact source prerequisites are60.1–60.3,64.5–64.5a,66.1–66.3a,66.7 and67.1–67.7 in the [first continuation at its fixed source version](https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md),72–75 in the [second continuation at that version](https://github.com/the-omega-institute/trureturing/blob/f022384d6e4a8b9e457f646f377ac2f0398b0c6f/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md), and78.4,78.11–78.13 above. The source-owned finite compiler of60 supplies its stated ideal packet, guard, record and finite-gate correspondence, not a continuum domain actuator. Closed-form theory, orthogonal range projections and the unit-interval Sobolev endpoint inequality are mature tools used inside79.2–79.4. The additional deduction concerns their interaction with the literal copied range at(79.1) and its current full-map consumer; it carries no global literature-priority claim.

Balmaseda–Lonigro–Pérez-Pardo, [*Stability of non-autonomous Schrödinger equations*, arXiv:2306.10203v2](https://arxiv.org/html/2306.10203v2), Assumption3.4 and Theorems3.9–3.10, provides a stability framework with one common form domain and lower bound, uniform equivalence of the associated Hilbert-scale norms, $C^2$ form regularity for3.9 and the stated piecewise-$C^2$/integrable derivative control for3.10. Its stability norm is $\mathcal B(\mathcal H^+,\mathcal H^-)$, not the unrestricted Hilbert operator norm $h$ in(79.10). That result is not an identification of the two domains here and cannot supply the missing inlet or an automatic66.7 full-map bound.

Duca–Joly, [*Schrödinger equation in moving domains*, arXiv:2006.02082v3](https://arxiv.org/html/2006.02082v3), Theorem1.1, assumes a bounded reference domain and a supplied $C^2$ family of space/time diffeomorphisms onto the moving domains for its Dirichlet unitary-flow assertion; its additional $C^3$ hypothesis yields the stated strong-solution regularity. It supplies neither the source's mixed-ground transmission/collision identification nor a physical INITIAL reserve inclusion. Ren, [*Persistent bundles over configuration spaces and obstructions for regular embeddings*, arXiv:2502.07476v2](https://arxiv.org/html/2502.07476v2), Theorem1.1, bounds real or complex target dimension for $(k,r)$-regular maps using inverse Stiefel–Whitney or Chern classes of the specified configuration-space bundles. Those embedding bounds do not establish a Sobolev-domain transport, a source-control history or a physical dimension choice. These literature results retain their own hypotheses and are not alternative proofs of the source-specific obstruction.

## 78.99 追加锚（本行以下为增补区）
