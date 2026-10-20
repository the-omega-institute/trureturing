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

## 80. A full-carrier bound for the form-adapted polar renewal

**Definition 80.1 (the fixed additive completion and its trace shear).** Use exactly79.1–79.5, with current event $\beta\mapsto\langle\beta,\alpha\rangle$ at $H=2$, fixed $a,g>0$, $\nu\ge0$, finite $\Omega\ge1$, and $0<\delta\le1$. Write $T=\mathsf T\otimes I_{\mathcal E}$ and $Z=\operatorname{Ran}(T)^\perp\subset\mathcal H_+$. Thus $C(x,z)=Tx+z$ is a Hilbert unitary from $\mathcal H_-\oplus Z$ onto $\mathcal H_+$. Before exchange restriction, the one-position atomic/cable counts are $(1,2)$ and $(3,6)$, and the two-position atomic-pair/slice/cell counts are $(0,4,4)$ and $(6,36,36)$. In $Z$ these counts are $(2,4)$ and $(6,32,32)$. Every same-cable cell still consists of both triangles. No old continuum component is removed.

Let $\mathcal D_Z$ impose all64.5 trace conditions internal to these new strata, together with the number form domain. A retained boundary of a new stratum remains new: a new cable ends at a newborn atom or ground, and fixing a newborn atom keeps the other-coordinate boundaries in $Z$. Let $k_Z$ contain exactly the kinetic terms on these strata, with coefficients one on intervals and $\delta$ on cells. Set

$$
\begin{gathered}
\mathcal R_-=Z,\quad\mathcal R_+=0,\quad\operatorname{Dom}r_-=\mathcal D_Z,\qquad
r_-[z]=a k_Z[z]+\Omega\|\mathsf n^{1/2}z\|^2,\quad
b_Z[z]=\|z\|^2+r_-[z],\\
\mathcal Q=\mathcal D_-\oplus\mathcal D_Z,\qquad
b_{\rm in}=b_-^0\oplus b_Z,\qquad b_{\rm out}=b_+^0.
\end{gathered}
\tag{80.1}
$$

The reserve is an orthogonal comparison summand, with no physical INITIAL ingress or independently prepared tensor-factor assertion.

Name the copied old cables $e_\ell=o\ell$, $\ell\in\{L,R\}$, oriented from $o$ to $\ell$. For ordered two-position data put

$$
v_\ell=z_1(\ell),\quad d_{\ell m}=z_2(\ell,m),\quad
b_{\ell m}(y)=z_2(\ell;e_m,y),\quad
 t_{\ell m}(x)=z_2(e_\ell,x;m).
\tag{80.2}
$$

Missing atomic collision values are zero. Define $E:Z\to\mathcal H_-$ by zero reference and old-root components, and by

$$
\begin{aligned}
(Ez)_{1,e_\ell}(x)&=xv_\ell,\\
(Ez)_2(o;e_\ell,x)&=x z_2(o,\ell),&
(Ez)_2(e_\ell,x;o)&=x z_2(\ell,o),\\
(Ez)_{2,e_\ell,e_m}(x,y)
 &=x b_{\ell m}(y)+y t_{\ell m}(x)-xy d_{\ell m}\quad(\ell\ne m),\\
(Ez)_{2,e_\ell,e_\ell}(x,y)
 &=\begin{cases}
y t_{\ell\ell}(x)-x t_{\ell\ell}(y),&x<y,\\
x b_{\ell\ell}(y)-y b_{\ell\ell}(x),&x>y.
\end{cases}
\end{aligned}
\tag{80.3}
$$

These are maps of entire $L^2$ components, not evaluations of cell functions at corners. They act by identity on field and auxiliary coefficients. With

$$
N=\begin{pmatrix}0&E\\0&0\end{pmatrix},\qquad
L=I+N,\qquad S=CL,
\tag{80.4}
$$

one has $N^2=0$. All subsequent adjoints use the actual weighted Hilbert spaces. In particular

$$
S^*=\begin{pmatrix}I&0\\E^*&I\end{pmatrix}C^*,\qquad
S^*S=\begin{pmatrix}I&E\\E^*&I+E^*E\end{pmatrix}.
\tag{80.5}
$$

**Lemma 80.2 (complete source domains and shear energies).** The reserve form in(80.1) is densely defined, closed and nonnegative. The shear satisfies

$$
\begin{gathered}
S\mathcal Q=\mathcal D_+,\qquad Si_-=T,\qquad
\|N\|\le\sqrt\delta,\qquad
\|S\|,\|S^{-1}\|\le1+\sqrt\delta,\\
b_{\rm out}[Su]\le M b_{\rm in}[u],\qquad
b_{\rm in}[S^{-1}v]\le M b_{\rm out}[v],\qquad M=6a+3,
\end{gathered}
\tag{80.6}
$$

for every $u\in\mathcal Q$ and $v\in\mathcal D_+$. All statements hold on ordered strata and pass to exchange symmetry and complete Hilbert-valued domains.

Proof. A useful explicit description of the trace domains will also be used below. On either boundary-closed collection of strata, old or new, start with independent atomic data, independent interval functions in $H^1_0(0,1)$, and independent cell functions in $H^1_0$ of each rectangle or triangle. Reference data is unrestricted. Write $\theta_0(x)=1-x$, $\theta_1(x)=x$. Add $\theta_i$ times each available endpoint atomic value to its interval. On a rectangle add

$$
\sum_{i=0}^1\theta_i(x)g_{p_i,f}(y)
+\sum_{j=0}^1\theta_j(y)g_{e,q_j}(x)
+\sum_{i,j=0}^1\theta_i(x)\theta_j(y)c_{p_iq_j}
\tag{80.7}
$$

to its independent cell function. Here the $g$'s are the independent zero-endpoint slices; missing ground or collision data is zero. On a same-cable triangle $x<y$, with cable endpoints $p_0,p_1$, add

$$
\begin{aligned}
&\theta_0(x)g_{p_0,e}(y)-\theta_0(y)g_{p_0,e}(x)\\
&\quad+\theta_1(y)g_{e,p_1}(x)-\theta_1(x)g_{e,p_1}(y)
 +(y-x)c_{p_0p_1}.
\end{aligned}
\tag{80.8}
$$

The other triangle uses the exchanged ordered data. The atomic term is the restriction of $\theta_0(x)\theta_1(y)-\theta_1(x)\theta_0(y)$. Formula(80.8) has zero diagonal trace, and its two exterior edges give precisely the lifted slices. Formula(80.7) gives all four matching boundaries. No corner trace of an arbitrary cell function is used.

This triangular lifting, denoted $\mathcal T$, is $I+R$, where $R$ strictly raises stratum dimension and $R^3=0$; hence its Hilbert inverse is $I-R+R^2$. Both are bounded on the finite direct sum of $L^2$ strata and on the raw direct sum of $H^1$ strata, for each fixed positive $\delta$. Subtracting its lifts leaves exactly zero boundary traces on every interval and cell. Thus $\mathcal T$ maps the independent Dirichlet form domain bijectively onto the required trace domain. The raw norm plus derivative norm is equivalent to the transported Dirichlet form norm. This proves density and closedness, in particular for $\mathcal D_Z$. The formulas commute with exchange; Hilbert-valued versions and the complete number-form intersection follow by direct sums over field number, with no surviving truncation.

For the shear, the one-position correction has old-root trace zero and newborn trace $v_\ell$. Each old slice obtains its required newborn pair endpoint and retains its zero collision endpoint. On a different-cable square, $t_{\ell m}(1)=b_{\ell m}(1)=d_{\ell m}$ makes the $x=1$ and $y=1$ boundaries in(80.3) equal to $b_{\ell m}$ and $t_{\ell m}$. Its remaining boundaries are the corrected old slices. On $x<y$ in a same-cable cell, $t_{\ell\ell}(1)=0$ gives the $y=1$ boundary $t_{\ell\ell}$, the $x=0$ boundary is $y z_2(o,\ell)$, and the diagonal is zero. The other triangle gives the exchanged ordered assertion. New strata are unchanged. Conversely restrict an outlet form vector to $Z$ and subtract $Ez$ on the old strata. Every old grounded and transmission condition is restored. This proves both domain directions.

For the estimates let $C_{\rm at}$ sum the squared norms of $z_2(o,\ell),z_2(\ell,o)$, let $D_{\rm at}$ sum those of $d_{\ell m}$ for $\ell\ne m$, and let $B_{\rm sl},B'_{\rm sl}$ sum the squared $L^2$ norms of the $b,t$ slices and their derivatives. Direct integration and the two- and three-term Cauchy–Schwarz inequalities give

$$
\begin{aligned}
\|E z_2\|^2&\le\delta C_{\rm at}/3+
               \delta^2(B_{\rm sl}+D_{\rm at}/3),\\
k_{-,\rm raw}[E z_2]&\le C_{\rm at}+
               \delta(B'_{\rm sl}+3B_{\rm sl}+2D_{\rm at}),\\
\|z_2\|^2&\ge C_{\rm at}+D_{\rm at}+\delta B_{\rm sl},\qquad
k_Z[z_2]\ge B'_{\rm sl}.
\end{aligned}
\tag{80.9}
$$

For example the two squared terms on $x<y$ give
$\int_{x<y}|y t(x)-x t(y)|^2\le(2/3)\|t\|^2$; the corresponding derivative bound is $(2/3)\|t'\|^2+2\|t\|^2$. The one-position contributions are exactly $\delta\sum_\ell\|v_\ell\|^2/3$ and $\sum_\ell\|v_\ell\|^2$. Consequently

$$
\|Ez\|^2\le\delta\|z\|^2,\quad
k_{-,\rm raw}[Ez]\le3\|z\|^2+\delta k_Z[z],\quad
\|\mathsf n^{1/2}Ez\|^2\le\delta\|\mathsf n^{1/2}z\|^2.
\tag{80.10}
$$

The raw old positive energy of $Ez$ is at most $(3a+1)b_Z[z]$; $Ez$ itself need not be in $\mathcal D_-$. Applying the squared triangle inequality to $x+Ez$, and then to $f_{\rm old}-Ez$, gives(80.6). Finally $L^{-1}=I-N$ and $C$ is unitary. $\square$

**Lemma 80.3 (a fractional estimate for this entire source shear).** Let $B\ge I$ represent $b_{\rm in}$, and put

$$
\vartheta=\tfrac18,\qquad
H_a=1+10^4(1+a),\qquad d_\delta=H_a^7\delta^{3/8}.
\tag{80.11}
$$

The following compositions have bounded extensions on the entire completed input space:

$$
\|B^\vartheta N B^{-\vartheta}\|\le d_\delta,\qquad
\|B^\vartheta N^* B^{-\vartheta}\|\le d_\delta.
\tag{80.12}
$$

The constants are uniform over every field-number block and every auxiliary Hilbert space.

Proof. This is a source estimate on the displayed intervals, rectangles and triangles. Normalize the Hilbert measure on a stratum of dimension $q$ by multiplying its function by $\delta^{q/2}$. Atomic components, including the reference, have $q=0$. The kinetic-to-Hilbert weight ratio on every positive-dimensional stratum is then $1/\delta$, not one. In a total-field-number block $j\ge0$, write $\tau=1+\Omega j$ and let $\Lambda$ be the direct sum of Dirichlet Laplacians on the independent intervals and cells, zero on atomic and reference components. Define

$$
D_j=\tau I+(a/\delta)\Lambda.
\tag{80.13}
$$

This is a comparison operator on all independent strata, not a replacement for $B_j=\tau I+aK_j$, where $K_j$ represents the actual $k_-\oplus k_Z$ in this block and these normalized coordinates. The triangular lifting $\mathcal T=I+R$ of(80.7)–(80.8) maps the complete form domain of $D_j$ onto that of $B_j$.

Here are uniform quantitative bounds for that lifting and for $N$. In normalized coordinates each dimension-raising term has coefficient $\delta^{(q-p)/2}$, $q>p$. Its underlying map is multiplication of a scalar by $\theta_i$ or by a product of two $\theta_i$'s, the lift $g\mapsto\theta_i\otimes g$ or its coordinate exchange, or the restriction of an antisymmetric pair of these lifts to one triangle. Triangle atomic lifts are antisymmetric products. These descriptions apply to(80.3) as well. Their Hilbert adjoints are the corresponding integral contractions. There are at most $512$ such terms in $R$, and fewer in $N$: the full ordered collection has $42$ intervals, $30$ different-cable rectangles and $12$ triangles, besides $9$ atomic coordinates and the reference. The old-plus-new partition only removes boundary terms. Even counting the two terms of each antisymmetric expression separately gives at most $84+120+120+48+24=396$ terms in $R$.

For completeness, the bounds on these particular elementary maps can be checked directly in sine series. The normalized interval functions $s_n(x)=\sqrt2\sin(n\pi x)$ diagonalize $\Lambda$; both $\theta_i$ have coefficients of absolute value $\sqrt2/(\pi n)$. At $\vartheta=1/8$,

$$
\sum_{n\ge1}\frac{2(1+n^2)^{1/4}}{\pi^2 n^2}<4,
\qquad
\sum_{n\ge1}\frac{2(\pi^2 n^2)^{1/4}}{\pi^2 n^2}<4,
\tag{80.14}
$$

using $\sum n^{-3/2}\le3$. On a square, for a slice frequency $m\ge1$ and $c=a/\delta$,

$$
\frac{(\tau+c\pi^2(n^2+m^2))^\vartheta}
     {(\tau+c\pi^2m^2)^\vartheta}
\le(1+n^2)^\vartheta.
\tag{80.15}
$$

Equations(80.14)–(80.15) bound the conjugated tensor lift by two. For its adjoint contraction the reversed spectral ratio is at most one, so Cauchy–Schwarz bounds it by $\|\theta_i\|$. The Dirichlet Laplacian on a right triangle is unitarily equivalent, by antisymmetric reflection and normalization, to the antisymmetric part of the square Dirichlet Laplacian. Its eigenfunctions are the antisymmetric pairs $s_n(x)s_m(y)-s_m(x)s_n(y)$, $n\ne m$. Thus the same bounds apply to the antisymmetric lifts and their actual adjoints, with an additional factor at most two.

For an atomic-to-interval term use $(\tau+c\lambda)^\vartheta\le\tau^\vartheta+c^\vartheta\lambda^\vartheta$ and(80.14). Its conjugated norm, including its $\sqrt\delta$ coefficient, is at most $3(1+a)\delta^{1/2-\vartheta}$. Atomic-to-square or triangle terms have coefficient $\delta$; splitting $(\lambda_n+\lambda_m)^\vartheta\le\lambda_n^\vartheta+\lambda_m^\vartheta$ gives the same upper bound with constant $16$ and the weaker exponent $1/2-\vartheta$. The reverse atomic contractions have spectral ratio at most one. It follows that every elementary term, or antisymmetric pair treated together, has conjugated norm at most $16(1+a)\delta^{3/8}$. This includes both directions needed for $N^*$; no assertion that $N^*$ preserves a full trace domain is made. Summing at most $512$ terms yields

$$
\begin{aligned}
\|D_j^\vartheta R D_j^{-\vartheta}\|&\le(H_a-1)\delta^{3/8},\\
\max\{\|D_j^\vartheta N D_j^{-\vartheta}\|,
       \|D_j^\vartheta N^* D_j^{-\vartheta}\|\}
 &\le(H_a-1)\delta^{3/8}.
\end{aligned}
\tag{80.16}
$$

The same elementary formulas have Hilbert norm at most $16(1+a)$ and raw form-norm bound at most $16(1+a)$. For example, for a normalized slice lift $\sqrt\delta\,\theta_i\otimes g$, its squared raw $\tau+c|\nabla|^2$ norm is at most $\delta\|g\|_{D_j^{1/2}}^2+a\|g\|^2\le(1+a)\|g\|_{D_j^{1/2}}^2$. Atomic lifts and antisymmetric pairs obey the stated larger bound by differentiation of their displayed polynomials. Therefore $\mathcal T$ has Hilbert and form-map norms at most $H_a$, and $\mathcal T^{-1}=I-R+R^2$ has the corresponding norms at most $H_a^2$. Interpolation of these Hilbert and form bounds gives

$$
\|B_j^\vartheta\mathcal T D_j^{-\vartheta}\|\le H_a,
\qquad
\|D_j^\vartheta\mathcal T^{-1}B_j^{-\vartheta}\|\le H_a^2.
\tag{80.17}
$$

This use of Hilbert-scale interpolation follows by applying the three-lines theorem to the matrix elements of $B_j^{z/2}\mathcal T D_j^{-z/2}$ and its inverse map, initially with spectral cutoffs and then by closure. The endpoint at $\operatorname{Re}z=1$ is exactly the proved complete form-map bound; it is not an assumed domain identification.

Equation(80.16) and $R^3=0$ also give
$\|D_j^\vartheta\mathcal T D_j^{-\vartheta}\|\le H_a$ and
$\|D_j^\vartheta\mathcal T^{-1}D_j^{-\vartheta}\|\le H_a^2$.
Combining with(80.17) proves

$$
\|B_j^\vartheta D_j^{-\vartheta}\|\le H_a^3,
\qquad \|D_j^\vartheta B_j^{-\vartheta}\|\le H_a^3.
\tag{80.18}
$$

Sandwich(80.16) between these two bounded maps to obtain(80.12). These estimates hold for every $\tau\ge1$, independently of its size. Finite sine sums are used only to establish bounded operators by density; all sine frequencies remain. Taking the orthogonal sum over all $j$, and tensoring each block with its full multiplicity and auxiliary space, gives the asserted complete operators. Exchange symmetry is a reducing subspace of the source forms and maps, so restriction preserves the bounds. $\square$

**Theorem 80.4 (one unitary with both domains, both energies and vanishing full copying norm).** For the completion(80.1) and the fixed shear(80.3), let

$$
A=B^{-1/2},\quad F=SA,\quad P=(A S^*S A)^{1/2},
\qquad V=\operatorname{polar}(F).
\tag{80.19}
$$

Then $V:\mathcal H_-\oplus Z\to\mathcal H_+$ is one input-independent onto linear unitary, with actual adjoint and exact domains

$$
V=F P^{-1}\text{ on }\mathcal Q,\qquad
V^*=P^{-1}A S^*,\qquad
V\mathcal Q=\mathcal D_+,\qquad V^*\mathcal D_+=\mathcal Q.
\tag{80.20}
$$

The adjoint composition is everywhere defined; neither $P^{-1}$ nor $A^{-1}$ is asserted bounded on the whole Hilbert space. On the entire respective form domains the constants

$$
C_{+,\delta}=C_{-,\delta}=(6a+3)(1+\sqrt\delta)^2,
\qquad K_\delta\le16(6a+3)^2
\tag{80.21}
$$

satisfy(79.9). Moreover, on all completed inputs, and consequently on the entire old carrier,

$$
\begin{gathered}
\|C^*V-I\|\le\eta_a(\delta),\qquad
h_\delta=\|Vi_--J\|\le\eta_a(\delta),\\
\eta_a(\delta)=\min\{2,\ 1024[1+10^4(1+a)]^7\delta^{3/8}\}
\longrightarrow0\quad(\delta\downarrow0).
\end{gathered}
\tag{80.22}
$$

Here $J=T$ because the outlet reserve is zero. The norm includes every output coordinate, all continuum frequencies, every field excitation, reference superpositions and arbitrary auxiliary correlations, including old inputs outside every energy ceiling.

Proof. First establish the domains and energies for this very $V$. The bounded operator $F$ is injective and has dense range $S\mathcal Q=\mathcal D_+$. Its polar partial isometry is therefore an onto unitary. Polar decomposition gives $F=VP$ and $F^*=PV^*=A S^*$. Since $S^*$ is onto,

$$
\operatorname{Ran}P=\operatorname{Ran}F^*
 =\operatorname{Ran}A=\mathcal Q,\qquad
V\operatorname{Ran}P=\operatorname{Ran}F=\mathcal D_+.
\tag{80.23}
$$

This proves(80.20), including the types and the domain of the adjoint composition. The forms and shear reduce particle sector and total field number, so their polar construction does too; no particle-only tensor factorization of $V$ is assumed. On the reference $A$ is positive and $N=0$, so $V=C$ there for every reference-field excitation. Put $s=\|S\|$, $q=\|S^{-1}\|$. For $u=F^*y\in\mathcal Q$ one has $B^{1/2}u=S^*y$ and $Vu=F V^*y$. For $v=Fx\in\mathcal D_+$ one has $V^*v=Px=F^*Vx$. Hence(80.6) gives

$$
\begin{aligned}
b_{\rm out}[Vu]&\le M\|y\|^2\le Mq^2 b_{\rm in}[u],\\
b_{\rm in}[V^*v]&=\|S^*Vx\|^2\le s^2\|x\|^2
 =s^2 b_{\rm in}[S^{-1}v]\le Ms^2 b_{\rm out}[v].
\end{aligned}
\tag{80.24}
$$

This proves(80.21) on all domain vectors, including reserve inputs.

It remains to prove the unrestricted norm, rather than infer it from $\|N\|$. Work in $C$ coordinates and put $\gamma=1/4$, $d=d_\delta$. Equation(80.12), its adjoint, and $A=B^{-1/2}$ imply

$$
\|N\|\le d,\qquad
\|A^{-\gamma}NA^\gamma\|\le d,\qquad
\|A^\gamma N A^{-\gamma}\|\le d.
\tag{80.25}
$$

For $d>1/4$ the bound by two already proves(80.22), so assume $d\le1/4$. Regularize only inside this proof: $A_\epsilon=A+\epsilon I$, $\epsilon>0$. Functional calculus and $0<\gamma<1$ give

$$
\|A_\epsilon^{-\gamma}N A_\epsilon^\gamma\|\le2d,
\qquad \|A_\epsilon^\gamma N A_\epsilon^{-\gamma}\|\le2d.
\tag{80.26}
$$

Indeed $A_\epsilon^\gamma=(A^\gamma+\epsilon^\gamma I)Z_\epsilon$ with a commuting contraction $Z_\epsilon$; both $A_\epsilon^{-\gamma}A^\gamma$ and $\epsilon^\gamma A_\epsilon^{-\gamma}$ are contractions. Expanding proves the first estimate. Apply it to $N^*$ and take adjoints for the second.

For $0\le t\le1$ define the bounded invertible operators

$$
L_t=I+tN,\quad F_t=L_tA_\epsilon=Q_tU_t,
\qquad Q_t=|F_t^*|>0,
\tag{80.27}
$$

where $U_t$ is unitary. This path is an auxiliary operator estimate, not a time-dependent source or physical control. Nilpotence gives $L_t^{-1}=I-tN$. The identities
$A_\epsilon^{-1}L_t^{-1}Q_t=U_t^*$ and
$Q_t^{-1}L_t A_\epsilon=U_t$, followed by Hilbert-scale interpolation, imply

$$
\begin{aligned}
\|A_\epsilon^{-\gamma}L_t^{-1}Q_t^\gamma\|
 &\le(1+d)^{1-\gamma},\\
\|Q_t^{-\gamma}L_t A_\epsilon^\gamma\|
 &\le(1+d)^{1-\gamma}.
\end{aligned}
\tag{80.28}
$$

Using(80.26) to insert or remove $L_t$ in these equations shows
$\|A_\epsilon^{-\gamma}Q_t^\gamma\|,
\|Q_t^{-\gamma}A_\epsilon^\gamma\|
\le(1+2d)(1+d)^{1-\gamma}<2$.
Taking adjoints and sandwiching(80.26) therefore yields

$$
\|Q_t^\gamma NQ_t^{-\gamma}\|\le8d,
\qquad\|Q_t^{-\gamma}NQ_t^\gamma\|\le8d.
\tag{80.29}
$$

We give the operator-norm summation that makes these fractional estimates useful. Let $P_k=\mathbf1_{[2^k,2^{k+1})}(Q_t)$, and solve
$Q_t X+XQ_t=NQ_t$. On the $(k,l)$ block the convergent semigroup integral gives

$$
X_{kl}=\int_0^\infty e^{-uQ_k}N_{kl}Q_l e^{-uQ_l}\,du,
\qquad \|X_{kl}\|\le2\|N_{kl}\|,
\tag{80.30}
$$

where $Q_k$ is the restriction to $P_k$. Equation(80.29), with $c_*=8d$, bounds the blocks with $k-l=m\ne0$ by
$c_*2^{-\gamma(|m|-1)}$, and diagonal blocks by $c_*$. Each fixed block diagonal maps mutually orthogonal input blocks to mutually orthogonal output blocks, so its norm is the supremum of its block norms. Summing the geometric series in block-diagonal operator norm proves

$$
\|X-X^*\|
 \le4c_*\left(1+\frac2{1-2^{-\gamma}}\right)<1024d.
\tag{80.31}
$$

No dimension or spectral condition number occurs in this bound.

The invertible polar factors in(80.27) are norm differentiable. Since $F_t'=NF_t$, differentiating $F_t=Q_tU_t$ and its adjoint gives, for the skew-adjoint $Y_t=U_t'U_t^*$,

$$
Q_tY_t+Y_tQ_t=NQ_t-Q_tN^*,\qquad Y_t=X-X^*.
\tag{80.32}
$$

Uniqueness follows from $Q_t>0$. Equations(80.31)–(80.32) and $U_0=I$ imply
$\|U_1-I\|\le1024d$, uniformly in $\epsilon>0$.

Finally $L A_\epsilon\to L A$ in norm, and their positive polar moduli converge in norm by continuous functional calculus. If $W=\operatorname{polar}(LA)$ and $P_0=|LA|$, then

$$
\|(U_1-W)P_0x\|
\le\|(P_0-|L A_\epsilon|)x\|
       +\|(L A_\epsilon-LA)x\|\longrightarrow0.
\tag{80.33}
$$

The range of $P_0$ is dense and all these factors are unitary, so $U_1\to W$ strongly. The uniform bound $\|(U_1-I)x\|\le1024d\|x\|$ now passes to every $x$, proving the operator-norm bound $\|W-I\|\le1024d$. This is a uniform bounded-operator estimate followed by a limit, not an inference of operator-norm convergence from fixed-vector convergence. Since $W=C^*V$, it proves(80.22). $\square$

**Corollary 80.5 (scope of the additive mathematical certificate).** For each separate complete common or killed commission, use the unchanged coupled forms and the constants $\lambda,u_0,\sigma_0$ of(79.19), with the reserve(80.1). The same $V$ obeys both complete shifted-energy inequalities with

$$
D_{+,\delta}=D_{-,\delta}
 =\frac{2u_0}{\lambda}(6a+3)(1+\sqrt\delta)^2.
\tag{80.34}
$$

Together with(80.22) this supplies an existential joint-thinning family in the additive class(79.3)–(79.5) for this current renewal. It supplies the full-map norm required by the79.4 to stronger78.11 to66.7 mathematical consumer, with every reserve output included. It is not an executed ingress, renewal actuator, clock or finite-price certificate.

Proof. Apply $\lambda b/2\le E\le u_0b$ from(79.19) on the two sides of each inequality(80.24). These are positive shifted-form amplification constants, not physical energy prices. Theorem80.4 supplies one map and its actual adjoint for all three requirements. The fixed-$\delta$ obstruction79.2 and necessary inequality79.11 are reused without change. In particular exact copying at positive $\delta$ remains impossible; under bounded $K$,79.11 excludes $h=o(\sqrt\delta)$ if $h\to0$. The slower sufficient upper bound(80.22) does not assert an optimal rate. $\square$

**Definition 80.6 (mathematical attribution and retained boundaries).** Polar decomposition, exact polar/adjoint identities, Hilbert-scale interpolation, Dirichlet sine series, reflection on a right triangle and Sylvester equations are mature mathematics used inside this source certificate. Gesztesy–Malamud–Mitrea–Naboko, [*Generalized Polar Decompositions for Closed Operators in Hilbert Spaces and Some Applications*, arXiv:0808.1731v2](https://arxiv.org/html/0808.1731v2), Theorems2.6–2.7, supplies the closed-operator polar identities: here $F$ is bounded, injective and dense-range, so both support projections are identities. The exact range deductions in(80.23) use these identities. The source-specific content is the bound(80.12) for the entire weighted ordered carrier and its use in(80.22) for the fixed form-adapted polar candidate, together with the same candidate's source domains and energies. No generic polar or interpolation theorem is claimed as new.

Duong–Philipp, [*The effect of perturbations of linear operators on their polar decomposition*, arXiv:1602.05304v2](https://arxiv.org/html/1602.05304v2), Theorems1.1–1.2, assumes semi-Fredholm or closed-range operators and bounds involving positive reduced minimum moduli. The present inverse square root has no such lower bound. Liu–Luo–Xu, [*New multiplicative perturbation bounds for the generalized polar decomposition*, arXiv:1807.03298v1](https://arxiv.org/html/1807.03298v1), Theorem3.1, gives a finite-matrix Frobenius-norm bound. Neither result is used as an unrestricted infinite-carrier norm estimate;(80.25)–(80.33) prove the required estimate with its source-specific fractional hypotheses.

Post–Zimmer, [arXiv:2202.03234v1](https://arxiv.org/html/2202.03234v1), Definition1.4, imposes resolvent-weighted defects at a common resolvent point, with conjugate-resolvent conditions when that point is nonreal. Zahn, [arXiv:1512.05512v3](https://arxiv.org/html/1512.05512v3), Section2 and Proposition1, retains positive boundary mass and matching bulk/boundary traces in its half-space model. Cherednichenko–Ershova–Kiselev, [arXiv:2205.04397v4](https://arxiv.org/html/2205.04397v4), Theorem4.5, compares resolvents for its thin-domain geometry and massive-vertex limit through its stated partial isometry. These are related domain and singular-mass settings; none is a theorem supplying(80.22) for the present ordered hard-core carrier. No global priority or literature-exhaustion assertion is made.

Every original label, order, occurrence, optional earlier history and immutable INITIAL, cap equality, source-independent actor initialization, source/control right, Read, refusal, Stop, chronological record, copy and COMPLETE condition remains that of55.1,60.1–60.3 and66.1. The complete common and killed inverses and their actual diagonal compensation remain separate, with both quadratures, all three modes, the reference and every auxiliary correlation. The parameter $\delta$ indexes mathematical commissions; neither it nor the auxiliary $t$ in(80.27) is an executed switching law. Source-compatible physical ingress, full operational implementation, metric and clock conversion, finite precision and finite execution, acquisition and lifetime-resource accounting remain unpaid. The original nonrecurrent common-zero, $j_c$,155, attainment and sustained programme are not settled. The finite-tree retained-record developments supply no automatic interface, domain, norm, operation or resource identification here. The one-way, nonadditive/coupled-reserve and geometric alternatives keep their own evidence requirements.

## 78.99 追加锚（本行以下为增补区）

## 81. Source-matched coarse growth and exact Markov-factor obstructions

**Definition 81.1 (the whole-rho occurrence metric).** Use the whole-rho contract of §55.1–§55.2, and write

$$
\mathcal P=\{L,R\}^{*},\qquad
p\sim pL,\quad p\sim pR,
$$

with one unit-length, unit-conductance seam for each displayed parent–child pair, counting measure $\mu(\{p\})=1$, and graph distance $d_{\mathcal P}$. The root is $o=\varepsilon$. Throughout the packing argument, $R\in\mathbb N_0=\{0,1,2,\ldots\}$ is a nonnegative integer graph radius. Thus

$$
B_{\mathcal P}(o,R)=\{p:|p|\le R\},\qquad
|B_{\mathcal P}(o,R)|=\sum_{k=0}^{R}2^k=2^{R+1}-1.
\tag{81.1}
$$

This is the complete occurrence graph in the explicit §55 realization. It is not the one-spine direct-limit graph used by §52.1–§52.4, and neither graph distance nor the cardinality in (81.1) is a physical spatial radius or a dimension assignment.

**Proposition 81.2 (bounded-density coarse-Euclidean obstruction).** There is no map $F:\mathcal P\to\mathbb R^3$ and real constants $A\ge1$, $B\ge0$, $0\le M<\infty$ such that

$$
\|F(p)-F(q)\|_2\le A d_{\mathcal P}(p,q)+B
\tag{81.2}
$$

for all $p,q$, and, for the one fixed standard tiling $Q_z=z+[0,1)^3$, $z\in\mathbb Z^3$, every tile contains at most $M$ image points counted with their occurrence multiplicity:

$$
\#\{p\in\mathcal P:F(p)\in Q_z\}\le M\qquad(z\in\mathbb Z^3).
\tag{81.3}
$$

Proof. By (81.2), $F(B_{\mathcal P}(o,R))$ lies in the Euclidean ball of radius $AR+B$ about $F(o)$. Each coordinate projection of this ball has length $2(AR+B)$ and meets at most $2AR+2B+3$ intervals of the fixed tiling by $[m,m+1)$, $m\in\mathbb Z$. Thus the ball meets at most $(2AR+2B+5)^3$ tiles $Q_z$. Hence (81.1) and (81.3) would give

$$
2^{R+1}-1\le M(2AR+2B+5)^3
\tag{81.4}
$$

for every $R\in\mathbb N_0$. The left side eventually exceeds every cubic polynomial, which is a contradiction. $\square$

The proposition rules out the stated globally bounded-density, coarse-Lipschitz realization of the §55 unit-seam occurrence metric. The same packing argument applies to every fixed finite-dimensional Euclidean target $\mathbb R^d$, $d\ge1$: replace the fixed tiles by $z+[0,1)^d$, $z\in\mathbb Z^d$, and the exponent $3$ in (81.4) by $d$. The zero-dimensional target has one tile and already violates (81.3). Changing conductances alone leaves this metric/counting obstruction intact. A finite cutoff, unbounded tile occupancy, failure of (81.2), a changed metric or counting convention, or a target with different volume growth changes a stated hypothesis; none of these changes by itself supplies an escape construction. A quotient followed by a map still satisfies the obstruction if occupancy counts all original occurrences as in (81.3); counting quotient classes instead changes the measure. No physical impossibility theorem or dimension inference from vertex degree follows.

**Definition 81.3 (the §52 exact Markov-factor contract).** Now use the distinct §52.1–§52.4 graph $\Gamma_{52}$: its direct limit retains the finite INITIAL tree $t$, one infinite spine $r_0,r_1,\ldots$, and the finite $T_j$ branches attached along that spine. Use its common infinite operator without finite-domain killing, its unit seam conductances and counting measure. Let

$$
L_{52}=L_\infty,\qquad P_{52}=I-L_{52}/3,
\tag{81.5}
$$

as in (52.3)–(52.4). An exact representative-independent factor consists of a surjection $\pi:\Gamma_{52}\to\mathcal B$ onto a nonempty countable state space and a stochastic kernel $\overline P$ satisfying

$$
\sum_{\pi(z)=b}P_{52}(x,z)
 =\overline P(\pi(x),b)
\qquad(x\in\Gamma_{52},\ b\in\mathcal B),
\tag{81.6}
$$

where the right side is independent of the representative $x$ in its fibre. Under (81.6), $Y_n=\pi(X_n)$ is a Markov chain in the same discrete step clock whenever $X_n$ has transition kernel $P_{52}$.

**Theorem 81.4 (the §52 same-clock Markov-factor obstruction).** Under (81.6), every factor state is recurrent. In particular its return probabilities cannot satisfy a summable $O((n+1)^{-3/2})$ bound in the same discrete clock.

Proof. First establish recurrence of the source chain, as an intermediate step. Each spine edge $\{r_k,r_{k+1}\}$ is a one-edge cutset separating $r_0$ from infinity: the component containing $r_0$ consists of the finite INITIAL tree and finitely many finite attached branches. These cutsets are pairwise edge-disjoint. With counting reversible measure, each nonloop edge has conductance $1/3$ for $P_{52}$, so each cutset has reciprocal total conductance $3$. Apply the classical [Nash–Williams Criterion (2.14), Lyons–Peres, *Probability on Trees and Networks*, Chapter 2, §5](https://rdlyons.pages.iu.edu/prbtree/book_online.pdf): the divergent sum of reciprocal cutset conductances implies recurrence. Holding does not affect escape or return recurrence here: the embedded jump chain uses the same nonloop conductances, and at each vertex the probability of a jump is $\deg(x)/3>0$. Connectedness makes $P_{52}$ irreducible, so recurrence holds at every vertex, equivalently

$$
\sum_{n\ge0}P_{52}^{\,n}(x,x)=\infty.
\tag{81.7}
$$

This use of the classical recurrence criterion is an intermediate deduction for the particular §52 source, not a new general recurrence theorem. Exact lumpability (81.6), iterated in the same step clock, now gives, for $b=\pi(x)$,

$$
\overline P^{\,n}(b,b)
 =\mathbb P_x(\pi(X_n)=b)
 =\sum_{\pi(y)=b}P_{52}^{\,n}(x,y)
 \ge P_{52}^{\,n}(x,x).
\tag{81.8}
$$

Summing proves recurrence at $b$; surjectivity covers every factor state. If a finite constant $C\ge0$ satisfied

$$
\overline P^{\,n}(b,b)\le C(n+1)^{-3/2},
\tag{81.9}
$$

for all sufficiently large integers $n$, its summable right side and the finitely many earlier probabilities would contradict (81.8). $\square$

This conclusion uses the exact factor law and the §52 chain and clock. It does not apply the one-spine proof to the whole-rho graph of §55. A non-Markov projection, representative-dependent transition data, changed rates, or a clock conversion would require a separately stated model and analysis; naming such a change proves neither transience nor (81.9). In particular any changed chain that remains recurrent has the same obstruction for its exact same-clock factors.

**Specification 81.5 (a conditional source-to-spatial bridge).** The native ordered source supplies its binary parent–child relation. Separately, [Process44, Definition 44.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) stipulates an oriented three-component Euclidean cross-product interface: $q(\alpha)=a$, $q(\beta)=b$, $q(\langle s,t\rangle)=q(s)\times q(t)$, with $a=e_1$, $b=e_2$, $k=b\times a=-e_3$ and readout in $\{0,\pm a,\pm b,\pm k\}$. Zero is an allowed reply and is not a direction of unit length. This interface does not derive the dimension of an ambient propagation space.

A proposed spatial interpretation must declare which source carrier, actual version and boundary convention it uses. The common whole-rho carrier $\mathcal P$, its actual finite domains $D_j(t)$ with the §55 missing-child killing, and the §52 common graph or its finite N/D conventions are different choices. A mathematical infinite carrier does not add an event or a Read after an infinite prefix or after Stop. The joint object's source projection must retain immutable INITIAL, source-independent initialization, labels, brackets, left/right order and distinct occurrences, actual versions, legal operations and whole-candidate guards, each acceptance and refusal, original Reads, chronological history, Stop, and the original acquisition, record and copy permissions and charges. A geometric quotient does not erase those coordinates from that projection or grant access to them.

For the chosen carrier $X$, supply an actual map $F:X\to M$, or a declared quotient and placement $X\xrightarrow{\pi}\mathcal B\xrightarrow{\iota}M$ with $F=\iota\circ\pi$, its fibres and legal identifications, and the target metric and measure. State how occurrence lengths, counting weights, adjacency and conductances correspond, including boundary or killing terms. The operator correspondence must be induced by this same map and these choices, with its function spaces, measure convention, variance and domains specified; an unrelated operator, in particular a zero intertwiner, is not a realization.

For example, in precisely the exact §52 quotient of (81.6), use complex bounded functions with supremum norm on the two countable state spaces, counting measure on each, and kernels acting on observables by $(Pf)(x)=\sum_yP(x,y)f(y)$. The actual map induces the pullback

$$
\begin{aligned}
U_\pi &: \ell^\infty(\mathcal B)\longrightarrow\ell^\infty(\Gamma_{52}),
& (U_\pi f)(x)&=f(\pi(x)),\\
P_{52}U_\pi&=U_\pi\overline P,
& L_{52}U_\pi&=U_\pi\overline L,
\qquad \overline L=3(I-\overline P).
\end{aligned}
\tag{81.10}
$$

All operators here are bounded on their displayed spaces; the identities hold on all of $\ell^\infty(\mathcal B)$ and use the same clock. The first identity is exactly (81.6), tested on state indicators and extended by absolutely convergent stochastic sums; the second follows from (81.5). Surjectivity makes $U_\pi$ an isometry and $U_\pi1=1$, excluding the zero map. This is pullback of observables, not pushforward of states. It makes no counting-measure $\ell^2$ assertion: if a fibre is infinite, the indicator of its target state has finite $\ell^2(\mathcal B)$ norm but its pullback has infinite $\ell^2(\Gamma_{52})$ norm. A Hilbert-space correspondence therefore needs its own measures, domain and boundedness proof. A continuous target operator likewise needs its own domain and boundary correspondence; (81.10) supplies none by itself.

The field and potential must correspond under the same map and boundary convention as the kinetic law. In an exact scalar quotient, descent of a source field means equality to a target field composed with $\pi$, and thus requires constancy on each fibre; the source term, exterior data and potential multiplier must also be matched. Choosing the §52 screened distributed field or the §55 isolated unscreened field is part of the model, not an implicit substitution. Supply any claimed conversion among propagation, source-event, apparatus and physical clocks, and any causal or finite-speed condition separately.

If the particular claimed Euclidean model requires cubic volume growth or a three-dimensional resistance/return estimate, specify its metric balls, measure, scales, constants, clock and return normalization and establish those controls for that model. They are not automatic properties of an arbitrary three-dimensional manifold, nor do those controls together constitute a sufficient dimension theorem. The foregoing items specify conditional correspondence obligations; neither their minimality nor their sufficiency for a spatial realization is proved here.

The resulting source-matched exclusions are precisely (81.4) for the §55 unit-seam metric with bounded occurrence occupancy, and (81.8)–(81.9) for the §52 exact same-clock factor. The source-to-spatial construction remains open. The proofs are mathematical deductions under the displayed contracts, with no claim of literature novelty; Lean formalization remains open. The stipulated local three-component readout supplies no physical dimension theorem.

## 78.99 追加锚（本行以下为增补区）
## 82. Rank-three transport carrier: point-source stability and target-fibre defect

**Definition 82.1 (rank-three stratified point-source contract).** Let $G$ be a connected, simply connected stratified nilpotent Lie group,
$$
\mathfrak g=V_1\oplus\cdots\oplus V_s,\qquad [V_1,V_j]=V_{j+1},\qquad \dim V_1=3,
$$
and let $V_1$ generate the whole Lie algebra. Left translation of $V_1$ is the horizontal bundle. Fix a positive horizontal inner product, an orthonormal left-invariant frame $X_1,X_2,X_3$, and one Haar measure $\mu$, and put
$$
L=-\sum_{i=1}^3X_i^2,\qquad H_t=e^{-tL}=e^{t\sum_iX_i^2}.
$$
The field and kinetic form use this same $L$, this same $\mu$ and this same clock. The homogeneous dimension is
$$
Q=\sum_{j=1}^s j\,\dim V_j,\qquad \mu(\delta_rA)=r^Q\mu(A).
$$
Assume that the positive point-source kernel $\Gamma$ satisfies $L\Gamma=\delta_e$, $\Gamma(\delta_rp)=r^{2-Q}\Gamma(p)$, and is positive and smooth on $G\setminus\{e\}$. Define
$$
\mathcal D_0=C_c^\infty(G\setminus\{e\}),\qquad
T[\psi]=\sum_i\|X_i\psi\|_{L^2(\mu)}^2,\qquad
V[\psi]=\int_G\Gamma|\psi|^2\,d\mu,
$$
and
$$
q_0[\psi]=aT[\psi]-gV[\psi],\qquad a,g>0.
\tag{82.1}
$$
The stability contract requires a finite lower bound on all point-source scales in $\mathcal D_0$, with any closed form agreeing with $q_0$ on this core. Rank three is an input assumption; it is not a physical dimension derived from the stability conclusion.

**Proposition 82.2 (semibounded point-source stability forces zero Levi leakage).** Under the positive-Green contract, semiboundedness of $q_0$ forces the Levi image $[V_1,V_1]=V_2$ to vanish. In this stratified class, a nonabelian group has $V_2\ne0$ and hence $Q\ge3+2=5$. Choose a nonzero normalized $\psi\in\mathcal D_0$ supported in a compact homogeneous annulus away from $e$, and set
$$
\psi_r(p)=r^{-Q/2}\psi(\delta_{1/r}p),\qquad 0<r<1.
$$
Then
$$
\|\psi_r\|_2=1,\qquad T[\psi_r]=r^{-2}T[\psi],\qquad
V[\psi_r]=r^{2-Q}V[\psi].
\tag{82.2}
$$
Since $V[\psi]>0$, for $Q\ge5$,
$$
q_0[\psi_r]=aT[\psi]r^{-2}-gV[\psi]r^{2-Q}\longrightarrow-\infty.
\tag{82.3}
$$
Thus no semibounded closed extension agreeing with $q_0$ on this core exists. Conversely, if the Levi image vanishes, the stratification relations force all higher layers to vanish, so $G$ is abelian; in the rank-three simply connected case it is $\mathbb R^3$. This conclusion excludes transverse brackets inside the declared contract and does not turn a local three-dimensional leaf into an ambient space. In the existing §22.3 scope, the zero-Levi case supplies only the corresponding local Frobenius leaves; it supplies neither unrestricted flow execution nor a spatial realization.

Proof. The stratification gives $V_j=[V_1,V_{j-1}]=0$ for $j\ge2$ once $V_2=0$. Under dilation, $X_i$ has degree one and $\Gamma$ degree $2-Q$, so the displayed identities follow by change of variables. If $V_2\ne0$, at least one second-layer direction contributes weight two and $Q\ge5$; the negative term in (82.3) has strictly larger order than $r^{-2}$. The core values are therefore unbounded below, which rules out every semibounded closed form agreeing on that core. $\square$

The abelian intermediate is the classical Coulomb form, not a new theorem of this appendix. For this intermediate choose coordinates orthonormal for the horizontal inner product and Lebesgue Haar normalization $d\mu=dx$, so $L=-\Delta$. Put $\Gamma_3(x)=(4\pi|x|)^{-1}$, $b=g/(4\pi)$ and $\kappa=b/(2a)=g/(8\pi a)$. On $H^1(\mathbb R^3)$, Hardy/KLMN form theory and integration by parts give
$$
q_0[u]+a\kappa^2\|u\|_2^2
 =a\left\|\nabla u+\kappa\frac{x}{|x|}u\right\|_2^2.
\tag{82.4}
$$
The form bound is $q_0[u]\ge -a\kappa^2\|u\|_2^2$; for normalized states the lower energy is $-a\kappa^2=-b^2/(4a)$, attained in the full $H^1$ form domain by
$$
 u_0(x)=\left(\frac{\kappa^3}{\pi}\right)^{1/2}e^{-\kappa|x|}.
$$
For another fixed Haar normalization $d\mu=c\,dx$, $c>0$, the same unit point source requires $\Gamma_3(x)=(4\pi c|x|)^{-1}$; the finite attained negative ground-state conclusion holds with $b=g/(4\pi c)$, $\kappa=b/(2a)$ and $u_0(x)=(\kappa^3/(c\pi))^{1/2}e^{-\kappa|x|}$. This minimizer is not in the punctured compactly supported core; (82.4) is used only as a mature intermediate in excluding the nonabelian branch. The critical Hardy weight and $\Gamma$ itself are different objects; see Kombe, *Sharp Hardy type inequalities on the Carnot Group*, [arXiv:math/0501522](https://arxiv.org/abs/math/0501522), §2 and Theorem 4.1. Bureš--Siegl, *Hydrogen atom in space with a compactified extra dimension and potential defined by Gauss' law*, [arXiv:1409.8530](https://arxiv.org/abs/1409.8530), §2 treats a Euclidean four-dimensional inverse-square threshold and a different compactified domain; it does not identify topological dimension four or $Q=5$ with (82.4).

The exterior gradient integral does not discriminate this class. On a fixed homogeneous annulus $A$ away from $e$, $\nabla_H\Gamma$ has degree $1-Q$, so
$$
\int_{\delta_R A}|\nabla_H\Gamma|^2d\mu
 =R^{2-Q}\int_A|\nabla_H\Gamma|^2d\mu.
$$
The dyadic sum over exterior annuli is finite for $Q>2$. This concerns only the exterior of the identity, not point-source self-energy, and it does not alter (82.3).

**Proposition 82.3 (literal §22.2 carrier and bounded-Borel heat factor).** On the §22.2 coordinates $p=(x,y,z,w)$ take
$$
 p\,p'=(x+x',y+y',z+z',w+w'+xy'),
$$
$$
X_1=\partial_x,\qquad X_2=\partial_y+x\partial_w,\qquad X_3=\partial_z,
$$
$$
 d\mu=dx\,dy\,dz\,dw,\qquad
\delta_r(x,y,z,w)=(rx,ry,rz,r^2w),\qquad \pi(p)=(x,y,z).
\tag{82.5}
$$
This is the rank-three carrier $H^1\times\mathbb R$, with topological dimension four, homogeneous dimension $Q=5$, and $[X_1,X_2]=\partial_w$. For a bounded Borel function $f$, let $U_\pi f=f\circ\pi$. The diffusion from $p_0$ can be written
$$
\begin{aligned}
X_t&=x_0+\sqrt2B_t^1,&Y_t&=y_0+\sqrt2B_t^2,&Z_t&=z_0+\sqrt2B_t^3,\\
W_t&=w_0+\sqrt2\int_0^tX_s\,dB_s^2,
\end{aligned}
\tag{82.6}
$$
where the $B^i$ are independent standard Brownian motions. Its generator is $\sum_iX_i^2$, and its projection is three-dimensional Brownian motion with generator $\Delta_3$. Thus, in the same $t$ clock,
$$
H_tU_\pi f=U_\pi e^{t\Delta_3}f
\qquad(t\ge0)
\tag{82.7}
$$
for every bounded Borel $f$. This is a bounded-observable Markov-semigroup identity, not only a smooth-generator computation. Since the $w$ fibres have infinite Haar measure, a nonzero $L^2(\mathbb R^3)$ function generally has no $L^2(G,d\mu)$ pullback; (82.7) makes no Hilbert-space assertion.

Proof. Itô's formula applied to (82.6) gives the generator $\sum_iX_i^2$; the first three components have the three-dimensional Brownian law with variance $2t$. The Markov-semigroup identity follows for bounded Borel observables and hence gives (82.7). $\square$

**Proposition 82.4 (Folland kernel and its actual three-dimensional marginal).** For (82.5), Folland, *Subelliptic estimates and function spaces on nilpotent Lie groups*, Arkiv för Matematik 13 (1975), 161–207, [doi:10.1007/BF02386204](https://doi.org/10.1007/BF02386204), Theorem 2.1 and Example 2.10 give the homogeneous fundamental kernel for $Q>2$; Theorem 3.1 and (3.2) give smooth nonnegative mass-one symmetric heat densities $h_t$ and their scaling; Corollaries 3.4–3.6 give smoothness off the identity and decay; Proposition 3.17 at $\alpha=2$ and the paragraph following Proposition 3.18 identify
$$
\Gamma(p)=\int_0^\infty h_t(p)\,dt
\tag{82.8}
$$
with that fundamental kernel. Theorem 3.1 supplies nonnegativity, not a silent claim of strict pointwise positivity. Symmetry and the semigroup law give
$$
 h_1(e)=\int_G h_{1/2}(q)^2d\mu(q)>0,
$$
so continuity gives a positive neighbourhood of $e$ for $h_1$. By (3.2), for every fixed $p$, sufficiently large $t$ satisfy $h_t(p)=t^{-Q/2}h_1(\delta_{1/\sqrt t}p)>0$. Thus (82.8) is finite and strictly positive for $p\ne e$.

The heat factor also gives the actual marginal. For every compactly supported continuous $f(\xi)$, the diffusion started at $e$ satisfies
$$
\int_{\mathbb R^3}f(\xi)\left(\int_{\mathbb R}h_t(\xi,w)\,dw\right)d\xi
 =\int_{\mathbb R^3}f(\xi)(4\pi t)^{-3/2}e^{-|\xi|^2/(4t)}d\xi.
$$
The decay in Corollaries 3.5–3.6 makes the fibre integral continuous and upgrades this almost-everywhere identity to
$$
\int_{\mathbb R}h_t(\xi,w)\,dw
 =(4\pi t)^{-3/2}e^{-|\xi|^2/(4t)}.
\tag{82.9}
$$
Tonelli and (82.8) then give, for $\xi\ne0$,
$$
\int_{\mathbb R}\Gamma(\xi,w)\,dw
 =\int_0^\infty(4\pi t)^{-3/2}e^{-|\xi|^2/(4t)}dt
 =\frac1{4\pi|\xi|}.
\tag{82.10}
$$
This is the marginal for the $e^{t\Delta_3}$ clock, not $e^{t\Delta_3/2}$, and it is neither scalar-field descent nor equality of potential multipliers. The right side diverges at $\xi=0$.

**Theorem 82.5 (point-source energy separation in one reader fibre).** Take a normalized nonzero $\psi\in\mathcal D_0$ supported in a compact homogeneous annulus. Fix $c=(0,0,0,w_0)$ with $w_0\ne0$, and set
$$
\psi_r(p)=r^{-5/2}\psi(\delta_{1/r}p),\qquad
\psi_r^c(p)=\psi_r(c^{-1}p).
\tag{82.11}
$$
For sufficiently small $r$, both supports avoid $e$. Write
$$
 m_\psi(\xi)=\int_{\mathbb R}|\psi(\xi,w)|^2dw,
$$
and let $\mathscr R(\psi)$ consist of the full projected initial probability density $m_\psi$, all source-free projected heat laws $\{e^{t\Delta_3}m_\psi:t\ge0\}$, and the full horizontal kinetic value $T[\psi]$. Then
$$
 m_{\psi_r}(\xi)=m_{\psi_r^c}(\xi)=r^{-3}m_\psi(\xi/r),
\qquad T[\psi_r]=T[\psi_r^c]=r^{-2}T[\psi],
\tag{82.12}
$$
and $T[\psi]>0$. Thus the two states have identical full three-coordinate probability data and all source-free projected heat observations in the same clock, and identical full kinetic value; the reader is a probability density and an observation family, not three real numbers.

By the homogeneity in (82.8),
$$
V[\psi_r]=r^{-3}V[\psi],\qquad V[\psi]>0.
\tag{82.13}
$$
Central translation preserves Haar measure, all three $X_i$ and $\pi$. Substituting $p=cq$, the support contracts to $e$ as $r\downarrow0$, while $\Gamma$ is continuous at $c\ne e$, so
$$
V[\psi_r^c]=\int_G\Gamma(cq)|\psi_r(q)|^2d\mu(q)\longrightarrow\Gamma(c).
\tag{82.14}
$$
Both states use the same fixed field $\Gamma$ centred at $e$. Consequently
$$
q_0[\psi_r]=aT[\psi]r^{-2}-gV[\psi]r^{-3}\longrightarrow-\infty,
\qquad
q_0[\psi_r^c]=aT[\psi]r^{-2}-g\Gamma(c)+o(1)\longrightarrow+\infty.
\tag{82.15}
$$
This is the §25 target-fibre escape: two states in one $\mathscr R$ fibre have different, oppositely diverging point-source energies. It does not assert equal interacting Schrödinger futures; only the source-free heat reader agrees, and the point-source interaction is precisely what separates the states.

Proof. Homogeneous change of variables gives the norm, kinetic and projected-density identities in (82.12); central left-translation gives the second kinetic equality. If $T[\psi]=0$, then $\partial_x\psi=0$, and compact support forces $\psi=0$, a contradiction. Equation (82.13) follows from $\Gamma(\delta_rq)=r^{-3}\Gamma(q)$. Uniform continuity on a compact neighbourhood of $c$ and normalization give (82.14), hence (82.15). $\square$

**Corollary 82.6 (lost relation and the actual §81.5 gap).** For $m_\psi(\xi)>0$, define
$$
\rho_\psi(w\mid\xi)=\frac{|\psi(\xi,w)|^2}{m_\psi(\xi)},
$$
and choose any probability density on fibres where $m_\psi=0$. Then
$$
V[\psi]=\int_{\mathbb R^3}m_\psi(\xi)
 \left(\int_{\mathbb R}\Gamma(\xi,w)\rho_\psi(w\mid\xi)dw\right)d\xi.
\tag{82.16}
$$
The marginal (82.10) integrates against the unweighted Haar fibre measure $dw$; it is not this state-dependent conditional expectation and cannot replace it. In particular $\Gamma$ cannot be $\Gamma_3\circ\pi$: at $c=(0,0,0,w_0)$, $\Gamma(c)$ is finite while $\Gamma_3(\pi(c))=\Gamma_3(0)$ is singular. Equivalently, $\pi(c)=\pi(\delta_2c)=0$ but $\Gamma(\delta_2c)=2^{-3}\Gamma(c)\ne\Gamma(c)$, so the field is not constant on fibres.

This is the missing “same map for field, potential and kinetic law” relation required by §81.5: projected heat data and one kinetic scalar do not recover the interaction expectation. It does not imply that every restricted state class needs global scalar-field descent. A separately declared sufficient conditional statistic, or a restriction making that statistic fixed, could close a different contract, but native admissibility of the states, the legal state class and the source-map are still unproved.

**Specification 82.7 (conditional scope, mature attribution and remaining correspondence).** Propositions 82.2–82.6 are a repository-derived conditional application joining the literal §22.2 transport carrier to the §81.5 point-source/kinetic contract. They are not new global Carnot, Hardy or Coulomb theorems and make no Lean-verification or literature-novelty claim. Folland supplies the fundamental kernel, heat mass/symmetry/scaling, decay and heat representation; the SDE/Lévy-area construction can be compared with Bonnefont--Juillet, [arXiv:1801.04109](https://arxiv.org/abs/1801.04109), §2.1. Kombe's Hardy results and Bureš--Siegl's Euclidean inverse-square threshold mark applicability boundaries only.

The concentrating tests in (82.3) remain in the original punctured core $\mathcal D_0$; removing only $e$ or a fixed annulus away from $e$ does not exclude all such tests. A fixed ultraviolet cutoff such as replacing $\Gamma$ by $\Gamma_M=\min(\Gamma,M)$, $M>0$, changes the source/potential contract and gives $q_M[\psi]=aT[\psi]-g\int_G\Gamma_M|\psi|^2\,d\mu\ge-gM\|\psi\|_2^2$ because $T\ge0$. This lower bound alone makes no ground-state attainment claim. This carrier is not the recurrent §52 one-spine occurrence chain, so its Brownian factor does not contradict §81.4. The native source/INITIAL, chronological legal actions, Reads/refusals/Stop, acquisition/copy permissions, clock and resource contracts remain unchanged. Equation (82.5) supplies no occurrence-to-group map, physical displacement, spatial meaning for the central coordinate, native-history access, causal implementation or resource execution. The source-to-space correspondence therefore remains open; the next substantive gap is to prove native admissibility of a state class and a sufficient conditional statistic recovering (82.16), or to prove an admissible restriction under the same source/metric/operator/clock contract.

## 78.99 追加锚（本行以下为增补区）
## 83. Fixed-source local extension of the rank-three stability contract

**Definition 83.1 (supplied smooth carrier and matched local field).** Fix a point $o$ in a smooth manifold $M$ of topological dimension $n$, a smooth positive density $\mu$, and smooth vector fields $X_1,X_2,X_3$ that are linearly independent throughout a neighbourhood $U$ of $o$. Declare them orthonormal for the horizontal metric on $D=\operatorname{span}(X_1,X_2,X_3)$. Assume the strong Hörmander condition there: their iterated brackets span $T_pM$ at every $p\in U$. Choose a connected smooth relatively compact domain $\Omega\ni o$ whose closure lies in $U$ and in a flow box for $X_1$. Shrink $U$ if necessary so that finitely many brackets of a common bounded length span on $\overline\Omega$. Such a choice follows already from a finite bracket basis at $o$ and continuity; it does not require constant bracket ranks.

With formal adjoints taken in this supplied density, set
$$
X_i^*=-X_i-\operatorname{div}_\mu X_i,\qquad
T_\Omega[u]=\sum_{i=1}^3\int_\Omega|X_i u|^2\,d\mu,
\qquad L_\Omega=\left(\sum_{i=1}^3X_i^*X_i\right)_{\mathrm{F},\Omega}.
\tag{83.1}
$$
Here $L_\Omega$ is the nonnegative Friedrichs operator associated with the closure of $T_\Omega$ initially on $C_c^\infty(\Omega)$; this fixes the Dirichlet boundary convention. Let $p_t^\Omega(p,q)$ be the density of $e^{-tL_\Omega}$ with respect to $\mu$, in the single clock $t$. Define the extended nonnegative integral
$$
\Gamma_{\Omega,o}(p)=\int_0^\infty p_t^\Omega(o,p)\,dt.
\tag{83.2}
$$
For fixed $a,g>0$ the matched point-source energy is
$$
\begin{aligned}
\mathcal D_{\Omega,o}&=C_c^\infty(\Omega\setminus\{o\}),\\
q_{\Omega,o}[u]&=aT_\Omega[u]-g\int_\Omega\Gamma_{\Omega,o}|u|^2\,d\mu.
\end{aligned}
\tag{83.3}
$$
The stability requirement is one finite lower bound for all normalized states in this entire punctured test domain. The kinetic form and the full field (83.2) use the same free operator, density, boundary condition and clock. In particular the free heat generator is
$$
-L_\Omega=\sum_iX_i^2+X_0,
\qquad X_0=\sum_i(\operatorname{div}_\mu X_i)X_i\in\Gamma(D)
\tag{83.4}
$$
in the interior, with zero smooth potential. The singular multiplier in (83.3) is not inserted into that heat generator.

At the fixed point $o$, let $D_o^j$ be the span of brackets of length at most $j$, let $d_j(o)=\dim D_o^j$, and choose weights $w_1(o),\ldots,w_n(o)$ with $d_j(o)-d_{j-1}(o)$ entries equal to $j$. Put
$$
Q(o)=\sum_{k=1}^n w_k(o)=\sum_{j\ge1}j\bigl(d_j(o)-d_{j-1}(o)\bigr),\qquad d_0(o)=0.
\tag{83.5}
$$
This is a pointwise flag weight sum. Horizontal rank three, ambient dimension $n$ and $Q(o)$ are distinct quantities; no neighbourhood Hausdorff dimension is identified with (83.5).

**Theorem 83.2 (fixed-source stability excludes higher ambient reachability).** Under Definition 83.1, the full integral $\Gamma_{\Omega,o}$ is finite and smooth off $o$, strictly positive there, and integrable on $\Omega$. Its unit-source relation is
$$
\int_\Omega\Gamma_{\Omega,o}(p)L_\Omega\varphi(p)\,d\mu(p)=\varphi(o)
\qquad\bigl(\varphi\in C_c^\infty(\Omega)\bigr).
\tag{83.6}
$$
Thus (83.3) is finite on its stated test domain and supplies a nonempty local Dirichlet Green setting. If $Q(o)>4$, there are normalized $u_r\in\mathcal D_{\Omega,o}$ and constants $C,c,r_0>0$ such that
$$
T_\Omega[u_r]\le Cr^{-2},\qquad
\int_\Omega\Gamma_{\Omega,o}|u_r|^2\,d\mu\ge cr^{2-Q(o)}
\qquad(0<r<r_0).
\tag{83.7}
$$
Consequently $q_{\Omega,o}[u_r]\to-\infty$, and no semibounded form agreeing with (83.3) on all these tests exists. In the supplied rank-three full-reachability contract, $n>3$ entails $Q(o)\ge 2n-3\ge5$, so semiboundedness excludes $n>3$. This implication is for each fixed $o$, $\Omega$, density, frame and pair $a,g$; its constants need not be uniform in the source, even within a singular stratum.

Proof. We use the mature free-heat and nilpotentization results of Colin de Verdière--Hillairet--Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, [doi:10.5802/ahl.93](https://doi.org/10.5802/ahl.93). Their §3.1.2 supplies smooth positive free heat kernels and the selfadjoint semigroup; §2.5.3 supplies convergence of rescaled horizontal fields; §2.5.6 fixes the tangent of the supplied smooth density. Theorem B, (2.8), pp.915–916 permits an arbitrary fixed point, regular or singular, with horizontal smooth drift and bounded local bracket step. Theorem 3.2 supplies interior localization for the Dirichlet realization. These suppliers enter the §22/§81.5 stability application below; none is a heat theorem for the singular perturbed energy (83.3).

First the local boundary condition makes the full Green integral genuine. In a containing flow box write $X_1=\partial_s$, $d\mu=h(s,\eta)\,ds\,d\eta$, $|s|<\ell$, and $0<m\le h\le M_0$ on a compact containing box. Extend a compactly supported test on $\Omega$ by zero in that box. The one-dimensional Dirichlet Poincaré inequality on each $s$-interval gives
$$
\|u\|_{L^2(\mu)}^2\le\frac{M_0}{m}\left(\frac{2\ell}{\pi}\right)^2\|X_1u\|_{L^2(\mu)}^2
\le\lambda^{-1}T_\Omega[u],\qquad
\lambda=\frac{m}{M_0}\left(\frac{\pi}{2\ell}\right)^2>0.
\tag{83.8}
$$
It passes to the form closure, so $L_\Omega\ge\lambda$. The closed horizontal Dirichlet form is sub-Markovian, hence $\int_\Omega p_t^\Omega(o,p)\,d\mu(p)\le1$. Positivity and interior smoothness follow from the free Hörmander heat theory just cited. Extend the fixed-source heat density by zero for $t<0$. Its parabolic distribution equation is $(\partial_t+L_\Omega)p=\delta_{(0,o)}$. Away from $o$, parabolic hypoellipticity makes this extension smooth across $t=0$ and flat there. Thus for every compact $K\Subset\Omega\setminus\{o\}$ and every $N$, $p_t^\Omega(o,p)=O_K(t^N)$ as $t\downarrow0$.

For large times, symmetry, the semigroup law and (83.8) give
$$
0\le p_t^\Omega(o,p)\le e^{-\lambda(t-1)}
\sqrt{p_1^\Omega(o,o)p_1^\Omega(p,p)}\qquad(t\ge1).
\tag{83.9}
$$
Indeed the two $p_{1/2}$ rows have squared $L^2$ norms $p_1^\Omega(o,o)$ and $p_1^\Omega(p,p)$, and the intervening operator is $e^{-(t-1)L_\Omega}$. This proves uniform integrability in time on every off-source compact set. For global spatial integrability, use the sub-Markov bound for $0<t<1$ and, for $t\ge1$, use
$$
\int_\Omega p_t^\Omega(o,p)\,d\mu(p)
\le\mu(\Omega)^{1/2}e^{-\lambda(t-1/2)}\sqrt{p_1^\Omega(o,o)}.
$$
Tonelli therefore gives $\Gamma_{\Omega,o}\in L^1(\Omega)$, including near the source. Integrating $-\partial_t(e^{-tL_\Omega}\varphi)(o)$ from zero to infinity gives (83.6): the initial value is $\varphi(o)$ and the terminal value vanishes by the spectral gap and smoothing. The interchange is justified by $\Gamma_{\Omega,o}\in L^1$ and bounded $L_\Omega\varphi$. Hypoellipticity of the spatial operator in (83.6) gives smoothness off $o$; the preceding uniform bounds give the same continuous representative as (83.2). Positivity of the heat kernel gives strict positivity of that representative.

Now fix privileged coordinates $\Phi$ at this one source, $\Phi(o)=0$, with image $V$, and write $d\mu=\rho(x)\,dx$ in them. Set
$$
\delta_r(y)=(r^{w_1(o)}y_1,\ldots,r^{w_n(o)}y_n),\qquad
F_r(y)=\Phi^{-1}(\delta_r y),\qquad
d\widehat\mu_o=\rho(0)\,dy.
$$
The rescaled fields $Y_i^{(r)}=r\,\delta_r^*(\Phi_*X_i)$ converge smoothly on compact sets to the nilpotent approximations $\widehat X_i^o$. Here the pullback of a vector field means $D\delta_r^{-1}$ applied to its value at $\delta_r y$. The tangent heat kernel $\widehat p_o$ is for $\sum_i(\widehat X_i^o)^2$ with respect to $\widehat\mu_o$. At a singular source it is not assumed to be the heat kernel of a transitive Carnot group. The cited fixed-source theorem and interior localization give
$$
r^{Q(o)}p_{r^2t}^\Omega\bigl(o,F_r(y)\bigr)
\longrightarrow\widehat p_o(t,0,y)
\tag{83.10}
$$
uniformly for $t$ in compact subsets of $(0,\infty)$ and $y$ in compact subsets of $V$. The positive tangent density uses $\rho(0)$, rather than an independently chosen Haar normalization. The horizontal drift in (83.4) disappears in this scaling, as required by Theorem B.

Choose a compact set $A\Subset V\setminus\{0\}$ containing the support of a nonzero $f\in C_c^\infty(V\setminus\{0\})$. The tangent heat kernel is strictly positive, so its minimum on $[1,2]\times\{0\}\times A$ is positive. By (83.10), for small $r$ and every $y\in A$,
$$
\Gamma_{\Omega,o}(F_r(y))
\ge\int_{r^2}^{2r^2}p_t^\Omega(o,F_r(y))\,dt
\ge cr^{2-Q(o)}.
\tag{83.11}
$$
This is a lower bound on the full actual Green field (83.2), not a replacement of that field by the displayed finite time window; nonnegativity makes all omitted times harmless for the lower bound.

Put $Z_r=\int_A|f(y)|^2\rho(\delta_r y)\,dy$, so $Z_r\to Z_0=\rho(0)\int_A|f|^2dy>0$, and define, with zero extension outside the coordinate support,
$$
u_r(F_r(y))=r^{-Q(o)/2}Z_r^{-1/2}f(y).
\tag{83.12}
$$
For small $r$ its support is compact in $\Omega\setminus\{o\}$; for every such $r$ it is smooth and has norm exactly one. The coordinate Jacobian is $r^{Q(o)}$, and thus
$$
T_\Omega[u_r]=r^{-2}Z_r^{-1}
\sum_i\int_A|Y_i^{(r)}f|^2\rho(\delta_r y)\,dy\le Cr^{-2}.
\tag{83.13}
$$
Smooth convergence of the fields and positivity of $Z_0$ justify the bound. Combining normalization with (83.11) proves (83.7), hence
$$
q_{\Omega,o}[u_r]\le aCr^{-2}-gc r^{2-Q(o)}\longrightarrow-\infty
\qquad\bigl(Q(o)>4\bigr).
\tag{83.14}
$$
Finally exactly three flag weights are one; all $n-3$ other weights are at least two. This proves $Q(o)\ge2n-3$ and the asserted ambient exclusion. Nothing in this argument supplies a converse, an attained lower energy, or a global ground state. $\square$

**Proposition 83.3 (singular Levi-zero source with a reachable higher bracket).** On $\mathbb R^4$ with coordinates $(x,y,z,w)$ and ordinary density $dx\,dy\,dz\,dw$, take
$$
X_1=\partial_x+\frac{y^2}{2}\partial_z,\qquad
X_2=\partial_y,\qquad X_3=\partial_w,\qquad o=(0,0,0,0).
\tag{83.15}
$$
This supplies a constant-rank-three smooth carrier with strong Hörmander generation everywhere, but at $o$ the entire pointwise Levi form of §22.1 vanishes. Its flag at $o$ has dimensions $(3,3,4)$, with weights $(1,1,1,3)$ on $(x,y,w,z)$ and $Q(o)=6$. It is not equiregular on any neighbourhood of $o$ and its horizontal structure is not a transitive Carnot-group structure. Nevertheless every sufficiently small domain as in Definition 83.1 supplies the same actual Dirichlet Green and punctured energy contract, for which normalized energies are unbounded below.

Proof. The $x,y,w$ components of the three fields form the identity matrix, proving rank three at all points, and
$$
[X_2,X_1]=y\partial_z,\qquad
[X_2,[X_2,X_1]]=\partial_z.
\tag{83.16}
$$
At $o$, all frame-pair brackets vanish. The $C^\infty$ bilinearity of the Levi form established in §22.3 then gives $\mathcal F_o=0$ for all pairs of horizontal vectors. The third bracket in (83.16) is transverse and, together with the frame, spans the full tangent space everywhere. The coordinates $x,y,w$ have nonholonomic order one. All horizontal derivatives of $z$ of orders one and two vanish at $o$, while $X_2^2X_1z(o)=1$, so $z$ has order three. These are privileged coordinates at $o$, and
$$
\delta_r(x,y,z,w)=(rx,ry,r^3z,rw)
$$
makes each field homogeneous of degree $-1$ and the density homogeneous of degree six. At $y\ne0$ the second bracket already spans the missing direction, so the nearby growth vector is $(3,4)$ and its weight sum is five. This changing growth vector prevents a transitive Carnot-group identification; homogeneity at this source does not restore equiregularity or identify a neighbourhood Hausdorff dimension.

The transverse direction is also a literal flow displacement, rather than only a formal bracket symbol. Apply the four short local flows $X_2$ for time $b$, $X_1$ for time $a$, $X_2$ for time $-b$, and $X_1$ for time $-a$. Starting at $o$, their successive points are
$$
(0,b,0,0),\quad(a,b,ab^2/2,0),\quad(a,0,ab^2/2,0),\quad(0,0,ab^2/2,0).
\tag{83.17}
$$
Thus arbitrarily small such loops return all three coordinates $(x,y,w)$ and change $z$ at cubic order. Signed $a$ gives either transverse sign. This mathematical flow statement applies to an execution contract only when these forward and reverse flows are permitted. If $z$ is readable and is a target, the unchanged triple is insufficient for that target, exactly the transport distinction in §22.2. On every neighbourhood of $o$ there are $y\ne0$ points with nonzero Levi form; hence the neighbourhood involutivity hypothesis of §22.3 fails, although $\mathcal F_o=0$.

All three fields have zero divergence in the declared density, so the free interior operator is $-\sum_iX_i^2$. A flow box for $X_1$ is given by $(s,\eta)=(x,(y,z-xy^2/2,w))$, and a small smooth domain with closure in it satisfies (83.8). Theorem 83.2 therefore uses its full finite off-source Green field and genuine tests (83.12) with
$$
q_{\Omega,o}[u_r]\le aCr^{-2}-gc r^{-4}\longrightarrow-\infty.
\tag{83.18}
$$
The structure is the classical Martinet-type horizontal model with an extra independent direction; the project-specific discriminator is its Levi-zero fixed source in the same matched stability and target contract. $\square$

**Corollary 83.4 (the local transport consumer and the remaining source bridge).** If the smooth §22 carrier is supplied with full ambient Hörmander reachability and with the field, density, Dirichlet domain, clock and entire test-state class of Definition 83.1, semibounded point-source stability forces $n=3$. In particular stability excludes the higher-bracket leakage of Proposition 83.3 even though its single-point Levi form vanishes. The stratified §82.2 implication $V_2=0\Rightarrow V_j=0$ for all $j\ge2$ cannot be substituted for this smooth singular-source argument. This local conclusion requires no scalar heat projection or translated-energy pair from §§82.3–82.6.

Proof. Rank three implies $n\ge3$, and Theorem 83.2 excludes $n>3$ under the displayed full-state contract. For $n=3$, $D=TM$, so no transverse quotient remains. In a higher-dimensional involutive distribution, §22.3 instead gives three-dimensional leaves and does not give full ambient bracket generation; that different premise is therefore outside this exclusion. Proposition 83.3 proves directly that pointwise Levi vanishing can coexist with a transverse third bracket. By contrast the graded generation relation in Definition 82.1 makes $V_2=0$ annihilate every higher layer. It is that global stratified relation, not pointwise Levi vanishing alone, that supports the inference in §82.2.

For the §81.5 and §82.1 consumers, (83.2) is the actual point field of the specified local free Dirichlet realization. If a contract independently prescribes a larger-domain or global field $\Gamma^{\mathrm{ext}}$, this theorem does not replace it by $\Gamma_{\Omega,o}$. The collapse implication also applies to that prescribed field only under a proved comparison such as $\Gamma^{\mathrm{ext}}\ge\Gamma_{\Omega,o}$ on the concentrating supports, with finite actual energy integrals there, or under its own matched free-heat lower estimate and Green/domain assumptions. Compatible killed-domain inclusion for the same free operator and density supplies such domination when both actual Green fields exist; it does not prove existence of a global field. A cutoff, massive resolvent, or finite-window potential is a different source contract. Likewise a restricted admissible state class needs an independent proof that it contains the normalized concentrating tests; exclusion for the entire punctured class does not settle stability of an unspecified restriction.

The retained inference joins the mature fixed-source heat limit and elementary normalized localization to the existing transport and point-source consumers, beyond the global stratified hypothesis of §82. No new general heat, nilpotentization or Coulomb theorem is asserted. A native application still requires the §22.1 bundle correspondence and lawful flow execution, and the §81.5 common map for states, source, field, measure, boundary convention, operator and clock. It must preserve the original source and INITIAL, chronological legal actions, authentic Reads and refusals, Stop, and acquisition, record and copy permissions and resource charges. The carrier above supplies none of those maps or admissibility proofs, nor a physical meaning for $n$ or $z$. In particular it neither recovers the conditional interaction statistic (82.16) from a source-free reader nor derives a physical three-dimensional space. $\square$

## 78.99 追加锚（本行以下为增补区）

## 84. Supplied fibre-density cap: same-field energy and distinct free evolutions

**Definition 84.1 (unchanged point source and supplied cap class).** Fix exactly the carrier, horizontal metric, Haar measure, projection and clock of (82.5):
$$
\begin{gathered}
p\,p'=(x+x',y+y',z+z',w+w'+xy'),\qquad d\mu=dx\,dy\,dz\,dw,\\
X_1=\partial_x,\qquad X_2=\partial_y+x\partial_w,\qquad X_3=\partial_z,\\
L=-X_1^2-X_2^2-X_3^2,\qquad \xi=(x,y,z),\qquad \pi(p)=\xi,\qquad H_t=e^{-tL}.
\end{gathered}
\tag{84.1}
$$
The source remains the unit point source at $e$, with the actual positive kernel $\Gamma=\int_0^\infty h_t\,dt$ of (82.8), $L\Gamma=\delta_e$, and its actual fibre marginal (82.10). In particular neither $\Gamma$ nor its source is truncated or replaced. Let $L$ on $L^2(G,d\mu)$ denote the nonnegative self-adjoint operator associated with the closure of the free horizontal kinetic form, and put
$$
\mathcal H_H^1=D(L^{1/2})
 =\{\psi\in L^2(G):X_i\psi\in L^2(G),\ i=1,2,3\},\qquad
T[\psi]=\sum_{i=1}^3\|X_i\psi\|_2^2.
\tag{84.2}
$$
Here derivatives are distributional. The free Sobolev-domain characterization and smooth-core density are the mature supplies of Folland, [doi:10.1007/BF02386204](https://doi.org/10.1007/BF02386204), Theorems 4.10 at $p=2,\alpha=0$ and 4.5. This invokes only the free form.

For independently supplied $M>0$, define
$$
\begin{aligned}
m_\psi(\xi)&=\int_{\mathbb R}|\psi(\xi,w)|^2dw,\\
\mathcal C_M&=\{\psi\in\mathcal H_H^1:\ \|\psi\|_2=1,
\quad |\psi(\xi,w)|^2\le M m_\psi(\xi)\ \text{for almost every }(\xi,w)\}.
\end{aligned}
\tag{84.3}
$$
The marginal is an $L^1$ function and is finite almost everywhere. On fibres with $m_\psi>0$ the inequality says $\rho_\psi(w\mid\xi)\le M$, with $\rho_\psi=|\psi|^2/m_\psi$. On a zero-marginal fibre, $\psi=0$ almost everywhere in $w$, and no division is made. If a conditional probability density is desired there, choose $M\mathbf1_{[0,1/M]}(w)$; this choice has zero weight in (82.16). Exceptional marginal representatives on null sets do not change any assertion. For $a,g>0$ the expression
$$
q[\psi]=aT[\psi]-gV[\psi],\qquad
V[\psi]=\int_G\Gamma|\psi|^2d\mu
\tag{84.4}
$$
will be a finite functional on the normalized nonlinear class $\mathcal C_M$. Neither a linear domain nor an interacting operator is defined by this class.

**Proposition 84.2 (inhabited same-field energy certificate on the whole cap class).** For every $M>0$, $\mathcal C_M$ contains states in the original punctured smooth core $\mathcal D_0$. For every $\psi\in\mathcal H_H^1$,
$$
f_\psi:=\sqrt{m_\psi}\in H^1(\mathbb R^3),\qquad
\|f_\psi\|_2=\|\psi\|_2,\qquad
\|\nabla f_\psi\|_2^2\le T[\psi].
\tag{84.5}
$$
For every $\psi\in\mathcal C_M$, define the finite projected integral
$$
J_\psi=\int_{\mathbb R^3}\frac{m_\psi(\xi)}{|\xi|}d\xi.
$$
Then the actual conditional field expectation in (82.16) obeys, for almost every $\xi\ne0$,
$$
0\le G_\psi(\xi):=\int_{\mathbb R}\Gamma(\xi,w)\rho_\psi(w\mid\xi)dw
\le\frac{M}{4\pi|\xi|},\qquad
V[\psi]=\int m_\psi G_\psi\,d\xi\le\frac{M}{4\pi}J_\psi<\infty.
\tag{84.6}
$$
Consequently the same-field energy has the interval certificate and normalized lower bound
$$
\begin{gathered}
aT[\psi]-\frac{gM}{4\pi}J_\psi\le q[\psi]\le aT[\psi],\\
q[\psi]\ge-\frac{g^2M^2}{64\pi^2a}.
\end{gathered}
\tag{84.7}
$$

Proof. First choose $u\in C_c^\infty(\mathbb R^3\setminus\{0\})$ and $h\in C_c^\infty(\mathbb R)$ with both $\|u\|_2=1$ and $\|h\|_2=1$. For
$$
h_R(w)=R^{-1/2}h(w/R),\qquad R\ge\frac{\|h\|_\infty^2}{M},\qquad
\psi(\xi,w)=u(\xi)h_R(w),
$$
we have $\|h_R\|_2=1$, $\|\psi\|_2=1$, $m_\psi=|u|^2$ and $|h_R|^2\le M$. The support avoids $e$. All horizontal derivatives are square integrable, including
$X_2\psi=(\partial_yu)h_R+xu h_R'$, because $u$ has compact support. Thus $\psi\in\mathcal D_0\cap\mathcal C_M$.

For a general compactly supported smooth $\psi$, fibre integration gives
$$
\partial_{\xi_i}m_\psi
 =2\operatorname{Re}\int_{\mathbb R}\overline\psi X_i\psi\,dw.
\tag{84.8}
$$
For $i=2$, the additional $x\partial_w$ contribution cancels because
$$
\operatorname{Re}\int\overline\psi\partial_w\psi\,dw
 =\frac12\int\partial_w|\psi|^2dw=0.
$$
To include zeros of $m_\psi$, use $f_\varepsilon=\sqrt{m_\psi+\varepsilon^2}-\varepsilon$. Cauchy--Schwarz gives
$$
|\partial_{\xi_i}f_\varepsilon|^2
 =\frac{|\operatorname{Re}\int\overline\psi X_i\psi\,dw|^2}{m_\psi+\varepsilon^2}
 \le\frac{m_\psi}{m_\psi+\varepsilon^2}\int|X_i\psi|^2dw
 \le\int|X_i\psi|^2dw.
$$
These $f_\varepsilon$ are bounded in $H^1$, satisfy $0\le f_\varepsilon\le\sqrt{m_\psi}$, and converge in $L^2$ to $\sqrt{m_\psi}$. Weak lower semicontinuity proves (84.5) for smooth states. Now approximate any $\psi\in\mathcal H_H^1$ by $\psi_n\in C_c^\infty(G)$ in the free form norm. The fibre $L^2$ reverse triangle inequality implies
$$
\|\sqrt{m_{\psi_n}}-\sqrt{m_\psi}\|_{L^2(\mathbb R^3)}
 \le\|\psi_n-\psi\|_{L^2(G)}.
\tag{84.9}
$$
Together with weak lower semicontinuity and $T[\psi_n]\to T[\psi]$, this proves (84.5) on the whole free form domain. No cap condition on the approximating sequence is used. The punctured core has the same free form closure: if $\chi\in C_c^\infty(G)$ equals one near $e$ and $\chi_\varepsilon=\chi\circ\delta_{1/\varepsilon}$, the $Q=5$ dilation gives
$$
\|\chi_\varepsilon\|_2^2=\varepsilon^5\|\chi\|_2^2,\qquad
T[\chi_\varepsilon]=\varepsilon^3T[\chi].
$$
The product rule then gives $(1-\chi_\varepsilon)\psi\to\psi$ in the free form norm for each compactly supported smooth $\psi$.

The Coulomb estimate used next is a mature intermediate of (82.4). Its integrability and constant can also be seen directly. For smooth compactly supported $f$, integrate against $v_\varepsilon(\xi)=\xi/\sqrt{|\xi|^2+\varepsilon^2}$, whose divergence is
$$
\operatorname{div}v_\varepsilon
 =\frac2{\sqrt{|\xi|^2+\varepsilon^2}}
   +\frac{\varepsilon^2}{(|\xi|^2+\varepsilon^2)^{3/2}}.
$$
Integration by parts and $|v_\varepsilon|\le1$, followed by Fatou, give
$$
J[f]:=\int\frac{|f|^2}{|\xi|}d\xi\le\|f\|_2\|\nabla f\|_2.
\tag{84.10}
$$
Smooth $H^1$ approximation and Fatou extend the inequality to every $f\in H^1$. Applying it to differences of approximants also gives convergence in $L^2(|\xi|^{-1}d\xi)$. Thus the integration-by-parts identity extends without an unaccounted singular boundary term:
$$
a\|\nabla f\|_2^2-kJ[f]
 =a\left\|\nabla f+\frac{k}{2a}\frac{\xi}{|\xi|}f\right\|_2^2
   -\frac{k^2}{4a}\|f\|_2^2,\qquad k>0.
\tag{84.11}
$$
For $f=f_\psi$ in the normalized class, (84.5) and (84.10) give $J_\psi\le\sqrt{T[\psi]}<\infty$.

Apply the cap to the actual nonnegative $\Gamma$ and use Tonelli with its genuine marginal (82.10). This proves (84.6); $\xi=0$ is a Lebesgue null set, so its divergent fibre marginal contributes no extra term. Substitution in (84.4) yields the interval in (84.7). With $k=gM/(4\pi)$, (84.5) and (84.11) yield $q[\psi]\ge-k^2/(4a)$; equivalently $q[\psi]\ge aT[\psi]-k\sqrt{T[\psi]}\ge-k^2/(4a)$. This proves the stated constant. The calculation bounds the conditional expectation in (82.16); it never identifies that expectation with the unweighted marginal (82.10). $\square$

**Proposition 84.3 (same-cap invariance for the free probability-density heat law).** Let
$$
\mathcal P_M=\{p\in L^1(G):\ p\ge0,\ \int_Gp\,d\mu=1,
\quad p(\xi,w)\le M m_p(\xi)\ \text{almost everywhere}\},\qquad
m_p(\xi)=\int_{\mathbb R}p(\xi,w)dw.
\tag{84.12}
$$
For $p_0\in\mathcal P_M$, the actual free Markov density $p_t=H_tp_0$ has mass one and satisfies
$$
m_{p_t}=P_tm_{p_0}\quad\text{almost everywhere},\qquad
p_t\le M(m_{p_t}\circ\pi),\qquad P_t=e^{t\Delta_3},\qquad t\ge0.
\tag{84.13}
$$
In particular $H_t\mathcal P_M\subseteq\mathcal P_M$ with the same $M$, including unbounded initial marginals and infinite Haar fibres.

Proof. Reuse the bounded-Borel factor (82.7), writing $Uf=f\circ\pi$. Folland's Theorem 3.1 supplies the nonnegative mass-one symmetric heat kernel. Let $K_t(p,q)$ be that kernel for $H_t$ relative to $d\mu$, so $K_t(p,q)=K_t(q,p)$ and each variable has integral one. Extend its action to every nonnegative measurable $F$ by
$$
\widetilde H_tF(p)=\int_GK_t(p,q)F(q)d\mu(q)\in[0,\infty],\qquad t>0.
$$
Choose a finite nonnegative Borel representative of $m_0=m_{p_0}$ outside its null exceptional set. The bounded truncations $m_0\wedge n$, (82.7), and monotone convergence give
$$
\widetilde H_t(Um_0)
 =\lim_{n\to\infty}H_t(U(m_0\wedge n))
 =\lim_{n\to\infty}U(P_t(m_0\wedge n))
 =U(P_tm_0).
\tag{84.14}
$$
This is a positive-kernel extension, requiring no $L^1$ or $L^2$ membership of the pullback $Um_0$ on the infinite fibres. Since $\|m_0\|_1=1$, for positive time its Euclidean heat marginal has a representative satisfying
$$
0<P_tm_0(\xi)\le(4\pi t)^{-3/2}\qquad\text{for every }\xi.
\tag{84.15}
$$
Positivity now yields $p_t\le M U(P_tm_0)$. To identify the true marginal rather than only a dominating function, test with any bounded Borel $f$ on $\mathbb R^3$. Kernel symmetry, integrability against $p_0$, (82.7), and Euclidean heat symmetry give
$$
\begin{aligned}
\int f\,m_{p_t}\,d\xi
 &=\int_G(Uf)H_tp_0\,d\mu
  =\int_GH_t(Uf)p_0\,d\mu\\
 &=\int(P_tf)m_0\,d\xi
  =\int f(P_tm_0)\,d\xi.
\end{aligned}
\tag{84.16}
$$
Thus $m_{p_t}=P_tm_0$ almost everywhere. The mass-one kernel preserves $\int p_t=1$, and the dominance proves (84.13). Time zero is the defining inequality, including zero fibres. This is evolution of a probability density. It supplies no identity between $H_t|\psi|^2$ and the squared modulus of a wave evolution, and no invariance assertion for an interacting Schrödinger law. $\square$

**Proposition 84.4 (an exact normalized free-unitary cap violation on the same carrier).** For every $M>0$ there is $\psi_0\in\mathcal C_M$ with finite horizontal kinetic energy such that, at a finite positive time in the $L$ clock, $\psi_t=e^{-itL}\psi_0$ violates the same cap on an open set of positive Haar measure. Specifically put
$$
\begin{gathered}
s=w-\frac{xy}{2},\qquad r^2=x^2+y^2,\qquad
b=\frac2{\pi M},\qquad \tau=4b,\\
A=b+\frac{r^2}{4},\qquad C_b=\frac{b}{\sqrt2\,\pi},\qquad
\phi(z)=\pi^{-1/4}e^{-z^2/2},\\
\phi_t(z)=\frac{\pi^{-1/4}}{\sqrt{1+2it}}
 \exp\!\left(-\frac{z^2}{2(1+2it)}\right),\\
F_d(A,s)=\frac1{(A-i(s+d))^2}+\frac1{(A+i(s-d))^2},\qquad
\psi_t(x,y,z,w)=C_b\phi_t(z)F_{\tau-t}(A,s).
\end{gathered}
\tag{84.17}
$$
The square root in $\phi_t$ is the continuous branch equal to one at $t=0$. These states satisfy
$$
\psi_t=e^{-itL}\psi_0,\qquad
\|\psi_t\|_2=1,\qquad
T[\psi_t]=\frac1b+\frac12,
\tag{84.18}
$$
and at $t=\tau$ their conditional density exceeds $M$ on such an open set. If instead the declared free wave Hamiltonian is $aL$, its evolution parameter $\theta$ gives $e^{-i\theta aL}\psi_0=\psi_{a\theta}$, and the violation time is $\theta=\tau/a$.

Proof. The one-sided central-translation ingredient is mature: Bahouri--Barilari--Gallagher, *Restriction theorems and Strichartz estimates on the Heisenberg group*, [arXiv:1911.03729v2](https://arxiv.org/abs/1911.03729v2), Proposition 1.1 and (1.12)--(1.15), attributes it to Bahouri--Gérard--Xu, *Espaces de Besov et estimations de Strichartz généralisées sur le groupe de Heisenberg*, Journal d'Analyse Mathématique 82 (2000), 93--118. Their fields $\partial_{y_j}+2\eta_j\partial_\sigma$, $\partial_{\eta_j}-2y_j\partial_\sigma$ and equation $i\partial_tu-\Delta_Hu=0$ have different constants and sign conventions. The following calculation fixes those correspondences directly for (84.1); the cap violation uses both frequency signs.

The coordinate change to $s$ has Jacobian one, keeps $\pi=(x,y,z)$, and rewrites the actual fields as
$$
X_1=\partial_x-\frac y2\partial_s,\qquad
X_2=\partial_y+\frac x2\partial_s,\qquad X_3=\partial_z.
$$
On a central Fourier mode $e^{i\lambda s}$, the Heisenberg part is
$$
L_\lambda=-\partial_x^2-\partial_y^2
 -i\lambda(x\partial_y-y\partial_x)+\frac{\lambda^2r^2}{4}.
$$
Direct differentiation gives, for $\lambda\ne0$,
$$
L_\lambda e^{-|\lambda|r^2/4}=|\lambda|e^{-|\lambda|r^2/4}.
\tag{84.19}
$$
Moreover the convergent Laplace integrals are
$$
F_d(A,s)=\int_0^\infty\lambda e^{-A\lambda}e^{id\lambda}
 (e^{i\lambda s}+e^{-i\lambda s})d\lambda.
\tag{84.20}
$$
Both frequency sectors therefore acquire the factor $e^{-it\lambda}$ under the free wave evolution, giving $d=\tau-t$. The normalized Gaussian satisfies $\phi_t=e^{it\partial_z^2}\phi$. This proves the evolution identity with the literal $L$ and fixes the two central packet velocities at $+1$ and $-1$. Here $e^{-itL}$ is the first-order-in-time Schrödinger unitary on wave amplitudes, not the second-order wave equation or the half-wave law $e^{-it\sqrt L}$.

For completeness, take the central Fourier convention $F(s)=\int_{\mathbb R}\alpha(\lambda)e^{i\lambda s}d\lambda$, so $\int|F|^2ds=2\pi\int|\alpha|^2d\lambda$. The two terms in (84.20) have disjoint positive and negative Fourier supports. Thus, for every real $d$,
$$
\int_{\mathbb R}|F_d(A,s)|^2ds
 =4\pi\int_0^\infty\lambda^2e^{-2A\lambda}d\lambda
 =\frac{\pi}{A^3},\qquad
\int_{\mathbb R^2}\frac{\pi}{(b+r^2/4)^3}dx\,dy
 =\frac{2\pi^2}{b^2}.
\tag{84.21}
$$
The Gaussian has $\|\phi_t\|_2=1$, and $C_b^2=b^2/(2\pi^2)$, proving normalization. Integrating $e^{-\lambda r^2/2}$ over $\mathbb R^2$ gives $2\pi/\lambda$, so the horizontal Heisenberg kinetic contribution is
$$
C_b^2\,8\pi^2\int_0^\infty\lambda^2e^{-2b\lambda}d\lambda=\frac1b.
$$
The remaining contribution is $\|\phi'\|_2^2=1/2$. The same spectral integral with any additional nonnegative integer power of $\lambda$ is finite, and the Gaussian has finite spectral moments of all orders for $-\partial_z^2$. In particular $\psi_0\in D(L)$, so the displayed evolution is the actual strong free solution, not merely a formal mode equation; it belongs to $\mathcal H_H^1$ at every time.

Since $\phi_t(z)$ is everywhere nonzero, the genuine marginal and conditional density are
$$
m_{\psi_t}(x,y,z)=C_b^2|\phi_t(z)|^2\frac{\pi}{A^3}>0,\qquad
\rho_t(w\mid x,y,z)=\frac{A^3}{\pi}|F_{\tau-t}(A,s)|^2.
\tag{84.22}
$$
Initially at least one of $|s+\tau|$, $|s-\tau|$ is at least $\tau$, so the triangle inequality gives
$$
\rho_0\le\frac1{\pi A}
 \left(1+\frac{A^2}{A^2+\tau^2}\right)^2.
$$
For $b\le A\le2b$, this is at most $36/(25\pi b)<2/(\pi b)=M$. For $A\ge2b$, the separate bound on each summand gives $\rho_0\le4/(\pi A)\le M$. These two ranges cover all $x,y$, and the estimates hold for every $s,z$. Hence $\psi_0\in\mathcal C_M$ globally.

At $t=\tau$, $x=y=s=0$ gives $F_0(b,0)=2/b^2$ and
$$
\rho_\tau(0\mid0,0,z)=\frac4{\pi b}=2M.
\tag{84.23}
$$
For instance the original-coordinate point $(0,0,1,0)$ lies away from $e$, has positive marginal and this strict violation. Continuity gives a bounded open neighbourhood on which $\rho_\tau>M$; its Haar measure is positive because the coordinate change preserves Lebesgue measure. This proves $e^{-i\tau L}\psi_0\notin\mathcal C_M$. Replacing $t$ by $a\theta$ proves the stated $aL$ clock relation. No step introduces the singular interaction $-g\Gamma$. $\square$

**Corollary 84.5 (restricted quantifier and continuing exact-energy defect).** The supplied fixed cap changes the state-and-scale quantifier of (82.3), while retaining its literal source field. It makes (84.7) a certificate from $m_\psi$, $T[\psi]$ and independently supplied $M$, but those data, even together with all projected free heat laws, do not determine exact $V$ or $q$ on $\mathcal C_M$.

Proof. Under the original normalized dilation $\psi_r(p)=r^{-5/2}\psi(\delta_{1/r}p)$,
$$
m_{\psi_r}(\xi)=r^{-3}m_\psi(\xi/r),\qquad
\rho_{\psi_r}(w\mid\xi)=r^{-2}\rho_\psi(w/r^2\mid\xi/r)
\tag{84.24}
$$
on positive marginal fibres. If $M_\psi$ is the essential supremum of the conditional density over those fibres, then a capped normalized state has $0<M_\psi\le M$, and $M_{\psi_r}=r^{-2}M_\psi$. Thus each such fixed state eventually leaves $\mathcal C_M$ as $r\downarrow0$. The unrestricted concentrating core family of §82.2 is not a family at fixed $M$. This restriction changes neither $\Gamma$ nor the proof or conclusion of the all-core collapse contract.

For exact nonrecovery, reuse the central-translation mechanism of §82.5 with the normalized compact product inhabitant from 84.2. For $c\in\mathbb R$ set
$$
\psi^c(\xi,w)=u(\xi)h_R(w-c).
$$
Central translation preserves the measure, all $X_i$, the marginal, the kinetic value and the bound $|h_R|^2\le M$. Hence every $\psi^c$ belongs to the same $\mathcal C_M$ and has the same reader $\mathscr R$ of §82.5. The unchanged positive field gives $V[\psi^0]>0$. Its decay off the identity, already supplied in §82.4, is uniform on the translated compact support as $|c|\to\infty$; consequently $V[\psi^c]\to0$. A sufficiently large finite $c$ therefore gives distinct actual energies with identical $m,T,M$ and projected free heat observations. This is the existing translation defect with cap membership checked, not a new unrestricted escape theorem. The interval certifies the actual expectation in (82.16) but does not decode it. $\square$

**Definition 84.6 (conditional consumer and unresolved native obligations).** A native application of (84.7) must supply a source-to-carrier correspondence preserving the actual source and immutable INITIAL, the state, field, Haar measure, horizontal kinetic law, projection, boundary convention and clock of §81.5. It must separately establish admissibility and authentic preparation or acquisition of a state in $\mathcal C_M$, lawful acquisition of its cap information, and the permission and costs of observation, copying and retention. Same-source chronology, legal actions, authentic Reads and refusals, Stop, preparation, acquisition, copy, retention, clock and resource obligations remain those of the original source. A supplied analytic cap grants none of these operations or their costs. A native source certificate or a retained calibration has its own target and actual acquisition contract; without a proved correspondence it supplies neither a smooth carrier state nor access to $M$.

The retained conditional inference is the same-field interval (84.7), probability-density invariance (84.13), and explicit free-unitary failure (84.17)--(84.23). The free Sobolev and positive-kernel suppliers, the Coulomb intermediate and the one-sided central translations remain attributed ingredients; their combination here is a source-specific application with no literature-priority assertion. The nonlinear normalized class and its finite functional supply no closed interacting quadratic form, invariant linear Hilbert space, sharp constant, attained ground state, exact decoder, or singular interacting dynamics. Construction and propagation of an admissible interacting class, native access to the cap, recovery of the exact conditional interaction statistic, and the source-to-carrier realization remain open. No physical space dimension follows from these conditional estimates.

## 78.99 追加锚（本行以下为增补区）

## 85. Finite central spectral sector: linear stability, compressed response and cutoff removal

**Definition 85.1 (the same source on a different state sector).** Keep exactly (82.5), its Lebesgue Haar measure, $L$, $\pi$, $a,g>0$, and the actual unit-source field $\Gamma=\int_0^\infty h_t\,dt$. In particular the source and potential are not cut off. Write $\xi=(x,y,z)$, $R=|\xi|$, $r_\perp^2=x^2+y^2$, and use the measure-preserving gauge
$$
s=w-\frac{xy}{2},\qquad
\Psi(\xi,s)=\psi(x,y,z,s+xy/2).
\tag{85.1}
$$
In these coordinates the group product and inverse, with the independent $z$ coordinate understood, are
$$
\begin{aligned}
(x,y,z,s)(x',y',z',s')
 &=\left(x+x',y+y',z+z',s+s'+\frac{xy'-yx'}2\right),\\
(x,y,z,s)^{-1}&=(-x,-y,-z,-s),
\end{aligned}
$$
and
$$
X_1=\partial_x-\frac y2\partial_s,\qquad
X_2=\partial_y+\frac x2\partial_s,\qquad X_3=\partial_z.
$$
The central Fourier convention throughout this section is
$$
\widetilde\Psi(\xi,\lambda)=\int_{\mathbb R}e^{-i\lambda s}\Psi(\xi,s)ds,
\qquad
\Psi(\xi,s)=\frac1{2\pi}\int_{\mathbb R}e^{i\lambda s}\widetilde\Psi(\xi,\lambda)d\lambda,
\qquad
\|\Psi\|_2^2=\int_{\mathbb R^3}\int_{\mathbb R}|\widetilde\Psi|^2\frac{d\lambda}{2\pi}d\xi.
\tag{85.2}
$$
For $\Lambda>0$ set
$$
\begin{gathered}
B_\Lambda=[-\Lambda,\Lambda],\qquad
P_\Lambda=\mathcal F_s^{-1}\mathbf1_{B_\Lambda}\mathcal F_s,\qquad
\mathcal H_\Lambda=P_\Lambda L^2(G),\\
\mathcal F_\Lambda=\mathcal H_\Lambda\cap D(L^{1/2}),\qquad
T[\psi]=\sum_i\|X_i\psi\|_2^2,\qquad
V[\psi]=\int_G\Gamma|\psi|^2d\mu,\qquad
q_\Lambda[\psi]=aT[\psi]-gV[\psi].
\end{gathered}
\tag{85.3}
$$
Central Fourier transformation in $w$ gives the same band: its transform differs from (85.2) only by the phase $e^{-i\lambda xy/2}$. Thus this restriction has no dependence on a choice between the two gauges. The free form domain is the actual distributional horizontal domain (84.2), not an independently chosen Euclidean Sobolev domain.

**Proposition 85.2 (sharp fibre cap and strong free reduction).** The domain $\mathcal F_\Lambda$ is nonzero and dense in $\mathcal H_\Lambda$, is closed in the free form norm, and satisfies
$$
\mathcal F_\Lambda=P_\Lambda D(L^{1/2}).
\tag{85.4}
$$
Every band state has a continuous central representative on almost every fibre, with
$$
|\psi(\xi,w)|^2\le\frac{\Lambda}{\pi}m_\psi(\xi),\qquad
m_\psi(\xi)=\int_{\mathbb R}|\psi(\xi,w)|^2dw.
\tag{85.5}
$$
The constant $\Lambda/\pi$ is optimal even on $\mathcal F_\Lambda$. The projection strongly commutes with $L$: it commutes with every spectral projection of $L$, hence with $e^{-tL}$ for $t\ge0$ and $e^{-itL}$ for real $t$. These free evolutions preserve $\mathcal H_\Lambda$ and $\mathcal F_\Lambda$.

Proof. The mature Fourier inversion and Plancherel supplies (Teschl, *Mathematical Methods in Quantum Mechanics*, §7.1), in the explicitly fixed normalization (85.2), and Cauchy--Schwarz on $B_\Lambda$ give (85.5). A fibre of zero marginal has zero Fourier transform and zero continuous representative; no conditional division is used there. On positive-marginal fibres the normalized density is bounded by $\Lambda/\pi$. The zero-fibre convention of Definition 84.1 remains available, for example $(\Lambda/\pi)\mathbf1_{[0,\pi/\Lambda]}$ if a probability density is wanted.

For sharpness put
$$
h_\Lambda(w)=\frac{\sin(\Lambda w)}{\sqrt{\pi\Lambda}\,w},\qquad
h_\Lambda(0)=\sqrt{\frac{\Lambda}{\pi}}.
\tag{85.6}
$$
Its Fourier transform in $w$ is $\sqrt{\pi/\Lambda}\,\mathbf1_{B_\Lambda}$, so $\|h_\Lambda\|_2=1$ and $\|h_\Lambda'\|_2^2=\Lambda^2/3$. For nonzero $u\in C_c^\infty(\mathbb R^3)$, the state $u(\xi)h_\Lambda(w)$ belongs to $\mathcal F_\Lambda$: in particular its second horizontal derivative of order one is $(\partial_yu)h_\Lambda+xu h_\Lambda'$. Its conditional density is $|h_\Lambda|^2$, whose essential supremum is $\Lambda/\pi$ by continuity at zero. This also verifies that the sharp cap is attained as a fibre evaluation norm, not as a claim about the finite-band energy constant.

More generally finite sums of products $u(\xi)h(w)$ with $u\in C_c^\infty(\mathbb R^3)$ and $\widetilde h\in C_c^\infty((-\Lambda,\Lambda))$, using the $w$ transform, lie in the actual horizontal domain and are dense in $\mathcal H_\Lambda$. The central projection commutes with all three horizontal distributional derivatives, and Plancherel gives $T[P_\Lambda\psi]\le T[\psi]$. It therefore splits the closed free form into orthogonal band and complementary forms. Equivalently the central direct integral has fibre form
$$
\begin{aligned}
t_\lambda[b]&=\left\|\left(\partial_x-\frac{i\lambda y}{2}\right)b\right\|_2^2
 +\left\|\left(\partial_y+\frac{i\lambda x}{2}\right)b\right\|_2^2
 +\|\partial_zb\|_2^2,\\
L_\lambda&=-\partial_x^2-\partial_y^2
 -i\lambda(x\partial_y-y\partial_x)+\frac{\lambda^2r_\perp^2}{4}-\partial_z^2,
\end{aligned}
\tag{85.7}
$$
with the operator interpreted through its closed free form. The standard direct-integral spectral theorem now gives strong commutation, rather than just a formal commutator on smooth functions. The restriction of the closed free form to the closed band subspace proves (85.4). Its spectral calculus proves preservation of the form domain; the unitary preserves $T$ and norm, whereas heat can decrease both. The time in these formulas is precisely the $L$ clock of (82.7). For a declared free Hamiltonian $aL$, the unitary parameter $\theta$ corresponds to $t=a\theta$. $\square$

**Theorem 85.3 (closed same-field restricted form).** On the Hilbert space $\mathcal H_\Lambda$, $q_\Lambda$ is a densely defined closed semibounded Hermitian form with domain exactly $\mathcal F_\Lambda$. For all $\psi$ in this domain,
$$
\begin{gathered}
V[\psi]\le\frac{\Lambda}{4\pi^2}\|\psi\|_2\sqrt{T[\psi]},\\
q_\Lambda[\psi]\ge-\frac{g^2\Lambda^2}{64\pi^4a}\|\psi\|_2^2.
\end{gathered}
\tag{85.8}
$$
It has a unique associated self-adjoint representation operator $A_\Lambda$ on $\mathcal H_\Lambda$.

Proof. Reuse the complete global contraction (84.5), including its treatment of zero marginals and its form-domain approximation. Put $f=\sqrt{m_\psi}$, so $\|f\|_2=\|\psi\|_2$ and $\|\nabla f\|_2^2\le T[\psi]$. The actual marginal (82.10), (85.5), and the mature Coulomb estimate (84.10) give
$$
V[\psi]\le\frac{\Lambda}{4\pi^2}\int\frac{|f(\xi)|^2}{R}d\xi
 \le\frac{\Lambda}{4\pi^2}\|\psi\|_2\sqrt{T[\psi]}.
\tag{85.9}
$$
Thus every state in $\mathcal F_\Lambda$ lies in $D(M_{\sqrt\Gamma})$. The sesquilinear potential form is the actual integral $v(\phi,\psi)=\int\Gamma\overline\phi\psi\,d\mu$; Cauchy--Schwarz in this weighted space makes it well defined. For each $\varepsilon>0$,
$$
gV[\psi]\le\varepsilon T[\psi]
 +\frac{g^2\Lambda^2}{64\pi^4\varepsilon}\|\psi\|_2^2.
\tag{85.10}
$$
The free form restricted to the band is closed and dense by Proposition 85.2. Choose $\varepsilon<a$ to make the relative bound strictly less than one. Teschl, *Mathematical Methods in Quantum Mechanics*, version February 12, 2009, [primary text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorem 6.24 (KLMN), applies on this Hilbert space and this domain. Completing the scalar square $aT-(g\Lambda/(4\pi^2))\|\psi\|_2\sqrt T$ gives the sharper displayed lower bound. Teschl's Theorem 2.13 supplies the representation operator, characterized by
$$
\begin{aligned}
D(A_\Lambda)=\{\psi\in\mathcal F_\Lambda:\ &\text{there is }F\in\mathcal H_\Lambda\text{ such that}\\
&q_\Lambda(\phi,\psi)=\langle\phi,F\rangle\text{ for all }\phi\in\mathcal F_\Lambda\},\\
&A_\Lambda\psi=F.
\end{aligned}
\tag{85.11}
$$
This is the form representation, with no identification of its domain with a free operator domain. The abstract supplier proves no client bound until (85.9)--(85.10) and the dense closed free restriction have been established. $\square$

**Proposition 85.4 (actual central Green kernel and normalized field bound).** Set
$$
\mathcal G(\xi,s)=\Gamma(x,y,z,s+xy/2).
$$
For $\xi\ne0$ the unnormalized central transform of this actual field is the strictly positive even kernel
$$
\begin{aligned}
K_\xi(\eta)&=\int_0^\infty B_t(\xi,\eta)dt,\\
B_t(\xi,\eta)&=
 \frac{|\eta|}{4\pi\sinh(|\eta|t)}
 \exp\!\left(-\frac{|\eta|\coth(|\eta|t)}4r_\perp^2\right)
 (4\pi t)^{-1/2}e^{-z^2/(4t)},\\
B_t(\xi,0)&=(4\pi t)^{-3/2}e^{-R^2/(4t)}.
\end{aligned}
\tag{85.12}
$$
In particular
$$
0<K_\xi(\eta)\le K_\xi(0)=\frac1{4\pi R},\qquad
\mathcal G(\xi,s)=\frac1{2\pi}\int_{\mathbb R}e^{i\eta s}K_\xi(\eta)d\eta,
\qquad
0<\mathcal G(\xi,s)\le\frac1{8R^3}.
\tag{85.13}
$$
The inverse integral is absolutely convergent for $R>0$; no finite kernel value is assigned at the exceptional fibre $\xi=0$.

Proof. The mature Heisenberg heat supplier is Krötz--Thangavelu--Xu, *The heat kernel transform for the Heisenberg group*, [arXiv:math/0401243v2](https://arxiv.org/abs/math/0401243v2), §4.1, equation (4.1.2), with $n=1$. Its product law is exactly the symmetric law in (85.1), its Haar measure is Lebesgue, and its partial transform uses $e^{+i\eta s}$. Replacing its parameter by $-\eta$ matches (85.2); the displayed radial coefficient is even. Its heat generator is the horizontal sum of squares. The additional $z$ direction here contributes the independent $(4\pi t)^{-1/2}e^{-z^2/(4t)}$ factor. In particular its §2 full Laplacian, which also includes the central second derivative and the factor $e^{-t\eta^2}$, is not the supplier for this problem.

The inverse central transform contributes $1/(2\pi)$, independently of the $(4\pi)^{-1}$ in (4.1.2). At $\eta=0$ formula (85.12) gives the actual marginal heat density (82.9), checking both mass and the literal $e^{-tL}$ clock. The heat representation of the actual unit-source Green field, its positivity and decay are those of Folland's Theorem 3.1, Proposition 3.17 at $\alpha=2$, and §§82.4, 84.1. Thus this parameter match gives the transform of that field, rather than a replacement potential.

For $u>0$, $u/\sinh u\le1$ and $u\coth u\ge1$. They imply $B_t(\xi,\eta)\le B_t(\xi,0)$. Integration proves the upper bound for $K$ and its value at zero; positivity of every integrand proves strict positivity. To justify the inverse and its bound, use also
$$
\int_{\mathbb R}\frac{|\eta|}{4\pi\sinh(|\eta|t)}d\eta
 =\frac{\pi}{8t^2},
\qquad
\int_0^\infty\frac{u}{\sinh u}du=\frac{\pi^2}{4}.
$$
The latter identity follows from the positive expansion $1/\sinh u=2\sum_{j\ge0}e^{-(2j+1)u}$. Tonelli now gives
$$
\begin{aligned}
\frac1{2\pi}\int_{\mathbb R}K_\xi(\eta)d\eta
 &\le\frac1{32\sqrt\pi}\int_0^\infty t^{-5/2}e^{-R^2/(4t)}dt
 =\frac1{8R^3}.
\end{aligned}
\tag{85.14}
$$
For $R>0$, the heat inverse and its time integral can therefore be interchanged absolutely. This identifies $K$ as the Fourier transform of $\mathcal G$ as well as proving (85.13), since $\mathcal G\ge0$ and the modulus of its inverse is bounded by (85.14). All constants concern the fixed Haar normalization and source of §82. $\square$

**Theorem 85.5 (actual leakage and the centrally nonlocal compression).** For every finite $\Lambda>0$, there is
$$
0\ne\psi\in\mathcal H_\Lambda\cap D(L)\cap D(M_\Gamma)
\quad\text{with}\quad
(I-P_\Lambda)M_\Gamma\psi\ne0.
\tag{85.15}
$$
Consequently the free spectral sector does not reduce actual multiplication by $\Gamma$. The band form retains the same actual expectation $V$, but its interaction response is compressed.

Proof. Choose nonzero nonnegative $u\in C_c^\infty(\{\xi:R>\delta\})$ for some $\delta>0$ and nonzero nonnegative $b\in C_c^\infty((-\Lambda,\Lambda))$. In the symmetric gauge set
$$
\widetilde\Psi(\xi,\lambda)=u(\xi)b(\lambda),\qquad
\Psi(\xi,s)=u(\xi)\frac1{2\pi}\int e^{i\lambda s}b(\lambda)d\lambda.
\tag{85.16}
$$
The central factor is Schwartz, all derivatives of $u$ have compact support, and the coefficients of (85.7) are bounded on that support. The direct-integral operator, or smooth free-graph approximation, therefore gives $\psi\in D(L)$. On this support (85.13) bounds $\Gamma$ by $1/(8\delta^3)$, proving $\psi\in D(M_\Gamma)$ independently of the form argument. The exact product formula is
$$
\widetilde{\mathcal G\Psi}(\xi,\lambda)
 =\frac{u(\xi)}{2\pi}\int_{B_\Lambda}K_\xi(\lambda-\eta)b(\eta)d\eta.
\tag{85.17}
$$
Indeed $\mathcal G(\xi,\cdot)\in L^1\cap L^\infty$ for $R>0$, and $b\in L^1$, so insertion of Fourier inversion and Fubini are valid. The integral is strictly positive for every real $\lambda$ wherever $u(\xi)>0$. It is therefore nonzero outside $B_\Lambda$ on a set of positive $(\xi,\lambda)$ measure. Since $M_\Gamma\psi\in L^2$, this proves (85.15) in the actual Hilbert space.

For a measurable fibre formulation let $\mathfrak h_\Lambda=L^2(B_\Lambda,d\lambda/(2\pi))$. For $R>0$ define
$$
(C_{\Lambda,\xi}b)(\lambda)
 =\frac1{2\pi}\int_{B_\Lambda}K_\xi(\lambda-\eta)b(\eta)d\eta,
\qquad\lambda\in B_\Lambda.
\tag{85.18}
$$
These are measurable bounded nonnegative self-adjoint fibre operators: they are the compressions of the bounded positive multiplier $\mathcal G(\xi,\cdot)$. The kernel is measurable by (85.12), and Schur's estimate together with (85.13) gives
$$
\|C_{\Lambda,\xi}\|\le
 \min\left\{\frac{\Lambda}{4\pi^2R},\frac1{8R^3}\right\}.
\tag{85.19}
$$
Values on $\xi=0$ may be set to zero without affecting the direct integral. Fibre Fourier transformation identifies their positive direct-integral form with $V$ on its natural weighted domain. In particular for $\phi,\psi\in\mathcal F_\Lambda$,
$$
v(\phi,\psi)=\int_{\mathbb R^3}
 \langle\widetilde\Phi(\xi,\cdot),C_{\Lambda,\xi}\widetilde\Psi(\xi,\cdot)\rangle_{\mathfrak h_\Lambda}d\xi.
\tag{85.20}
$$
This identity extends from the fibre formula by weighted Cauchy--Schwarz, since both weighted norms are finite by (85.9). It does not require the general form state to belong to $D(M_\Gamma)$. When $\psi$ does belong to that multiplier domain, the form response is represented by $P_\Lambda M_\Gamma\psi$; on the common free operator and multiplier domain the form identity gives $A_\Lambda\psi=aL\psi-gP_\Lambda M_\Gamma\psi$. No converse domain assertion is made.

The multiplier-domain distinction is substantive. Choose $u\in C_c^\infty(\mathbb R^3)$ equal to one near zero and a Schwartz central factor $h$ whose transform is nonnegative, nonzero and compactly supported in $(-\Lambda,\Lambda)$. Then $h(0)>0$, and $u(\xi)h(w)$ is in $\mathcal F_\Lambda\cap D(L)$ by the same product derivative calculation, but it is not in $D(M_\Gamma)$. Indeed its modulus is bounded below on a neighbourhood of $e$. For the homogeneous norm $N(\xi,s)=(R^4+s^2)^{1/4}$, positivity and homogeneity give $\Gamma\ge cN^{-3}$ there for some $c>0$, and $\int_{N<\epsilon}\Gamma^2d\mu=\infty$: on disjoint dyadic homogeneous annuli the integrals scale as $\rho^{5-6}=\rho^{-1}$ and have a positive base value. Thus finiteness of the actual potential form must not be promoted to multiplier-domain membership.

The distinction is also explicit in the central coordinate. The projection kernel is
$$
p_\Lambda(s-s')=\frac{\sin(\Lambda(s-s'))}{\pi(s-s')},\qquad p_\Lambda(0)=\frac{\Lambda}{\pi}.
$$
For fixed $\xi\ne0$, the kernel of the compressed potential, initially acting on Schwartz functions of $s'$, is instead
$$
J_{\Lambda,\xi}(s,s')
 =\int_{\mathbb R}p_\Lambda(s-u)\mathcal G(\xi,u)p_\Lambda(u-s')du.
\tag{85.21}
$$
This integral converges absolutely because $p_\Lambda$ is bounded and $\mathcal G(\xi,\cdot)\in L^1$. Inserting the two projections justifies the formula by Fubini on Schwartz inputs. It defines a continuous kernel. Its diagonal is strictly positive, since $\mathcal G>0$ and $p_\Lambda^2$ is positive except at a discrete set. Continuity consequently gives nonzero off-diagonal values near every diagonal point, proving central nonlocality. The sinc alone is the projection kernel, not the kernel of the compressed potential.

Thus equality of the band expectation with the same-field expectation does not identify the responses: (85.17) has an actual discarded component. The represented band Hamiltonian defines its own closed-form evolution on $\mathcal H_\Lambda$. No full-space singular interacting realization has been specified, and no reduction or invariance of such a realization follows from the free commutation or the equality of expectations. $\square$

**Corollary 85.6 (the existing conditional-energy reader gap inside the band).** The reader $\mathscr R$ of §82.5, even supplemented with $\Lambda$ and its sharp cap, does not determine exact $V$ or $q_\Lambda$ on the normalized band form domain.

Proof. This is the §82 central-translation defect with actual band membership checked. Choose normalized $u\in C_c^\infty(\{R>\delta\})$ and normalized Schwartz $h$ with nonzero smooth Fourier transform supported in $(-\Lambda,\Lambda)$, now in the original $w$ gauge. For $c\in\mathbb R$ put $\psi^c(\xi,w)=u(\xi)h(w-c)$. Every state lies in $\mathcal F_\Lambda$ and has the cap (85.5). Central translations commute with every $X_i$ and preserve $m_\psi$, $T$, norm and central frequency support; all projected free heat observations in $\mathscr R$ agree. The actual field gives $V[\psi^0]>0$. For each fixed $(\xi,v)$ on the support of $u$, $\Gamma(\xi,v+c)\to0$ as $|c|\to\infty$ by the actual Green decay. The uniform bound $\Gamma\le1/(8\delta^3)$ there permits dominated convergence against $|u(\xi)|^2|h(v)|^2d\xi\,dv$, giving $V[\psi^c]\to0$. Some finite $c$ therefore gives distinct energies in one reader fibre. This proves neither another all-scale escape statement nor any equality of interacting futures. The missing statistic is still the actual conditional field expectation (82.16), not the Haar marginal (82.10). $\square$

**Theorem 85.7 (finite-band variational boundary and negative-infimum attainment).** For fixed $a,g,\Lambda>0$ define
$$
\begin{aligned}
E_\Lambda(a,g)&=\inf\{q_\Lambda[\psi]:\psi\in\mathcal F_\Lambda,\ \|\psi\|_2=1\},\\
C_\Lambda&=\sup_{0\ne\psi\in\mathcal F_\Lambda}\frac{V[\psi]}{T[\psi]}.
\end{aligned}
\tag{85.22}
$$
Then $0<C_\Lambda\le\sqrt\Lambda/(\sqrt2\pi)$, $C_\Lambda=\sqrt\Lambda C_1$, and
$$
\begin{gathered}
-\frac{g^2\Lambda^2}{64\pi^4a}\le E_\Lambda(a,g)\le0,\\
E_\Lambda(a,g)=0\quad\Longleftrightarrow\quad gC_\Lambda\le a,\qquad
E_\Lambda(a,g)<0\quad\Longleftrightarrow\quad gC_\Lambda>a.
\end{gathered}
\tag{85.23}
$$
In particular $g\sqrt\Lambda\le\sqrt2\pi a$ is a sufficient no-negative-energy region. If $E_\Lambda(a,g)<0$, the infimum is attained by a normalized state in $\mathcal F_\Lambda$, which is an eigenvector of $A_\Lambda$ with eigenvalue $E_\Lambda(a,g)$. The numerical value of $C_1$ and attainment at the critical coupling $g=a/C_\Lambda$ are not determined here.

Proof. The conditional expectation on a positive-marginal fibre is bounded both by (85.9)'s pointwise cap estimate and by the actual-field supremum (85.13). Therefore
$$
V[\psi]\le\int m_\psi(\xi)
 \min\left\{\frac{\Lambda}{4\pi^2R},\frac1{8R^3}\right\}d\xi
 \le\frac{\sqrt\Lambda}{4\sqrt2\pi}\int\frac{m_\psi(\xi)}{R^2}d\xi
 \le\frac{\sqrt\Lambda}{\sqrt2\pi}T[\psi].
\tag{85.24}
$$
For the middle inequality, $\min(AR,B/R)\le\sqrt{AB}$ with $A=\Lambda/(4\pi^2)$, $B=1/8$. The final step uses the classical three-dimensional Hardy inequality $\int|f|^2/R^2\le4\|\nabla f\|_2^2$ on the actual $f=\sqrt{m_\psi}$ supplied by (84.5). Thus the stated constant is a sufficient estimate; no sharpness at fixed bandwidth is asserted. Also $T[\psi]=0$ forces $\nabla f=0$ and then $f=0$ because $f\in L^2(\mathbb R^3)$, so the ratios in (85.22) have nonzero denominators. Positivity of $\Gamma$ and an inhabitant of $\mathcal F_\Lambda$ prove $C_\Lambda>0$.

Use the same normalized dilation as §82,
$$
(U_\rho\psi)(p)=\rho^{-5/2}\psi(\delta_{1/\rho}p),\qquad
U_\rho\mathcal F_\Lambda=\mathcal F_{\Lambda/\rho^2},\qquad
T[U_\rho\psi]=\rho^{-2}T[\psi],\qquad
V[U_\rho\psi]=\rho^{-3}V[\psi].
\tag{85.25}
$$
Central Fourier scaling proves the sector identity, and the last two identities use the actual kinetic degree and actual Green homogeneity. Taking $\rho=\Lambda^{-1/2}$ maps $\mathcal F_1$ onto $\mathcal F_\Lambda$ and proves $C_\Lambda=\sqrt\Lambda C_1$. Taking $\rho\to\infty$ on any fixed normalized band inhabitant keeps it in $\mathcal F_\Lambda$ and gives $q_\Lambda[U_\rho\psi]\to0$. Hence $E_\Lambda\le0$. The definition of the supremum now proves both alternatives in (85.23), including equality at the threshold; (85.8) supplies the lower bound. For strictly subcritical $gC_\Lambda<a$, every nonzero state's form value is positive, so the zero infimum is not attained. At critical coupling this argument does not decide attainment.

For the negative case the required compactness concerns the actual full field. We prove that
$$
\mathcal F_\Lambda\longrightarrow L^2(G,\Gamma d\mu),\qquad\psi\longmapsto\psi,
\quad\text{is compact for the norm }(\|\psi\|_2^2+T[\psi])^{1/2}.
\tag{85.26}
$$
First, $\|\partial_w\psi\|_2\le\Lambda\|\psi\|_2$ by the band restriction. In the original coordinates $\partial_x=X_1$, $\partial_z=X_3$, and $\partial_y=X_2-x\partial_w$. A form-bounded sequence is consequently bounded in ordinary $H^1$ on every relatively compact coordinate box, after multiplication by a smooth compact cutoff. The classical Rellich--Kondrachov theorem, applied to these cutoffs on bounded smooth coordinate balls in dimension four with $H^1$ boundedness and target $L^2$, gives a diagonal subsequence converging strongly in local $L^2$; the weak form limit identifies that limit.

Second, uniformly for all $\phi\in\mathcal F_\Lambda$, the singular central cylinder is small in the weighted norm:
$$
\int_{R<\delta}\Gamma|\phi|^2d\mu
 \le\frac{\Lambda}{4\pi^2}\int_{R<\delta}\frac{m_\phi}{R}d\xi
 \le\frac{\Lambda\delta}{\pi^2}T[\phi].
\tag{85.27}
$$
This uses the marginal cap and Hardy, and covers the entire infinite central fibre, not merely a small Euclidean neighbourhood of the source. Third let $N(\xi,s)=(R^4+s^2)^{1/4}$. Folland's smoothness and homogeneous degree $-3$ on the compact unit $N$ sphere give $\mathcal G(\xi,s)\le C N^{-3}$. Consequently
$$
\int_{N>K}\Gamma|\phi|^2d\mu\le CK^{-3}\|\phi\|_2^2.
\tag{85.28}
$$
The remaining region $\{R\ge\delta,N\le K\}$ is compact, and its potential is bounded by $1/(8\delta^3)$. Local strong $L^2$ convergence controls the weighted norm there. Apply (85.27)--(85.28) to differences of the convergent subsequence, first making $\delta$ small and $K$ large and then using local convergence. This proves weighted Cauchy convergence; local identification gives its weighted limit as the weak form limit. Thus (85.26) is a compact embedding with the actual $\Gamma$, including its singularity and its full central tail.

Now let $\|\psi_n\|_2=1$ and $q_\Lambda[\psi_n]\to E=E_\Lambda(a,g)<0$. Estimate (85.10) with $\varepsilon=a/2$ bounds $T[\psi_n]$. Pass to a weakly convergent subsequence in $\mathcal F_\Lambda$ with limit $\psi$. Weighted compactness gives $V[\psi_n]\to V[\psi]$, and weak lower semicontinuity gives $q_\Lambda[\psi]\le E$. Set $m=\|\psi\|_2^2\le1$. Homogeneity and the definition of $E$ give $q_\Lambda[\psi]\ge Em$, also when $m=0$. Hence
$$
E\ge q_\Lambda[\psi]\ge Em\ge E.
\tag{85.29}
$$
Since $E<0$, equality forces $m=1$ and $q_\Lambda[\psi]=E$. This supplies the missing norm/mass conclusion as well as attainment. Constrained variation of the Hermitian form gives $q_\Lambda(\phi,\psi)=E\langle\phi,\psi\rangle$ for every $\phi\in\mathcal F_\Lambda$. The representation characterization (85.11) yields the asserted eigenvector. Semiboundedness alone was used for neither negativity nor attainment. $\square$

**Theorem 85.8 (matched leading collapse as the finite cutoff is removed).** For the same actual field and fixed $a,g>0$,
$$
\lim_{\Lambda\to\infty}\frac{E_\Lambda(a,g)}{\Lambda^2}
 =-\frac{g^2}{64\pi^4a}.
\tag{85.30}
$$
In particular the fixed-band lower bound has the correct leading coefficient in this limit, without a claim that it is sharp at any finite $\Lambda$.

Proof. The lower limit follows from (85.8). For the matching upper limit, use the mature normalized Coulomb minimizer from (82.4), with the different, explicitly matched coupling
$$
k_0=\frac{g}{4\pi^2},\qquad \kappa_0=\frac{k_0}{2a},\qquad
\nu(\xi)=\left(\frac{\kappa_0^3}{\pi}\right)^{1/2}e^{-\kappa_0R}.
$$
Thus $\|\nu\|_2=1$, $\nu\in H^1(\mathbb R^3)$, $x\nu\in L^2$, and
$$
a\|\nabla\nu\|_2^2-\frac{g}{4\pi^2}\int\frac{|\nu|^2}{R}d\xi
 =-\frac{g^2}{64\pi^4a}.
\tag{85.31}
$$
Define, in the original $w$ gauge,
$$
\nu_\Lambda(\xi)=\Lambda^{3/2}\nu(\Lambda\xi),\qquad
\psi_\Lambda(\xi,w)=\nu_\Lambda(\xi)h_\Lambda(w),
\tag{85.32}
$$
where $h_\Lambda$ is exactly (85.6). This normalized state is in $\mathcal F_\Lambda$: its weak horizontal derivatives are square integrable. Both factors are real, and $\int h_\Lambda h_\Lambda'\,dw=0$, so the actual $X_2=\partial_y+x\partial_w$ gives
$$
T[\psi_\Lambda]
 =\Lambda^2\|\nabla\nu\|_2^2
  +\frac13\int_{\mathbb R^3}x^2|\nu(\xi)|^2d\xi.
\tag{85.33}
$$
In particular the magnetic contribution is controlled rather than silently omitted.

Let $h_1(t)=\sin t/(\sqrt\pi t)$ with its continuous value at zero. Substituting $\xi=v/\Lambda$ and $w=t/\Lambda^2$, and using the actual degree $-3$ Green homogeneity in the original coordinates, gives the exact identity
$$
\frac{V[\psi_\Lambda]}{\Lambda^2}
 =\int_{\mathbb R^3}\int_{\mathbb R}|\nu(v)|^2\Gamma(v,t)
   |h_1(t/\Lambda)|^2dt\,dv.
\tag{85.34}
$$
Here $|h_1(t/\Lambda)|^2\le1/\pi$ and it tends to $1/\pi$ for every finite $t$. The dominating integral is finite by the actual fibre marginal:
$$
\frac1\pi\int|\nu(v)|^2\left(\int\Gamma(v,t)dt\right)dv
 =\frac1{4\pi^2}\int\frac{|\nu(v)|^2}{|v|}dv<\infty.
$$
Dominated convergence therefore proves $V[\psi_\Lambda]/\Lambda^2\to(4\pi^2)^{-1}\int|\nu|^2/R$. Equations (85.31)--(85.34) give the upper limit, hence (85.30). The trial proves an energy asymptotic on the actual field; it makes no state/profile convergence claim and supplies no rate beyond the stated limit. $\square$

**Proposition 85.9 (the admissible-state quantifier and one-sided collapse).** The finite-band form does not extend the all-core form contract of §82, nor the relatively compact zero-extension contract of §83. It has no nonzero state with compact central support. Restricting instead to a half-infinite central frequency range, with no upper bound in one direction, still permits collapse for the same actual field.

Proof. On almost every $\xi$ fibre, a function whose Fourier transform is supported in $B_\Lambda$ has the entire extension $(2\pi)^{-1}\int_{B_\Lambda}e^{i\lambda\zeta}b(\lambda)d\lambda$ in $\zeta\in\mathbb C$, since $b\in L^2(B_\Lambda)\subset L^1(B_\Lambda)$. If it has compact support in the real central coordinate, its continuous representative vanishes on an open real interval. The identity theorem forces that entire function to vanish. Fubini therefore proves the claimed absence of nonzero compact-central-support states, even if the compact interval is allowed to depend on the fibre. In particular $\mathcal H_\Lambda\cap\mathcal D_0=\{0\}$. Whenever a relatively compact §83 domain is placed on this carrier, its zero extensions have bounded central support and hence cannot be nonzero band states. For other §83 carriers no identification with $\mathcal H_\Lambda$ is supplied.

Under (85.25), central Fourier support scales by $\rho^{-2}$. A nonzero $L^2$ band state cannot have central support only at frequency zero, so its concentrating dilates eventually leave every fixed $\mathcal H_\Lambda$. Thus fixed-band stability changes precisely the admissible-state quantifier that carried the §82 collapse. It does not change the proof or conclusion on the whole punctured core.

For the half-infinite restriction, take the smooth product witness of Corollary 85.6 with its central transform supported in $[\alpha,\beta]\subset(0,\infty)$, with $\alpha$ beyond any prescribed finite lower endpoint. It has finite $T$ and strictly positive finite $V$. Its dilates $U_\rho\psi$, $\rho\downarrow0$, remain in that half-infinite sector and satisfy
$$
aT[U_\rho\psi]-gV[U_\rho\psi]
 =a\rho^{-2}T[\psi]-g\rho^{-3}V[\psi]\longrightarrow-\infty.
\tag{85.35}
$$
A negative-frequency interval gives the other direction, with its negative endpoint beyond any prescribed finite upper endpoint. These are actual horizontally admissible states; no compact-central-support assertion is needed. A finite bound in both frequency directions, not just a sign selection or one finite endpoint, is what excluded this scaling family. $\square$

**Definition 85.10 (conditional application and open source correspondences).** The retained analytic consumer consists of the sharp cap and free reduction in Proposition 85.2, the closed same-field restricted form in Theorem 85.3, the actual leakage and compressed response in Theorem 85.5, the finite-band variational alternatives with their proved compactness condition in Theorem 85.7, and the matched energy asymptotic in Theorem 85.8. Fourier evaluation, direct-integral spectral calculus, Hardy, local Rellich, the Coulomb minimizer, Folland's heat/Green supplies and Teschl's form theorems are mature ingredients. The source-specific parameter matching, leakage witness, full-field weighted compactness and simultaneous bandwidth/horizontal trial connect those ingredients to the unchanged §82 contract. These applications are repository-derived; no exhaustive novelty or literature-priority claim is made.

A native use must separately supply the same source and immutable INITIAL, the state-to-carrier and field correspondence, Haar and kinetic laws, projection, boundary convention, clock, and an admissible native operation producing or acquiring a state in $\mathcal H_\Lambda$. The exact conditional statistic in (82.16) remains an additional reader obligation by Corollary 85.6. Same-source chronology, authentic Reads/refusals/Stop, preparation and acquisition, observation, copying and retention, clock and resource permissions and costs keep their original contracts. A native static retained-row/depth recovery or coding statement under its complete same-source handoff supplies its own read conclusion, not a band state or a map to this carrier. Frequency restriction provides none of those bridges.

The $\Lambda^2$ analytic energy scale in (85.30) is cutoff dependent, not a proved native resource price. No source-independent preparation, exact-energy decoder, full-space singular interacting realization, full-space resolvent limit, state/profile limit, or physical dimension follows. In particular the original all-core instability, the separate §83 local domain result, and the nonlinear cap/free-density and free-unitary distinctions of §84 retain their stated scopes.

## 78.99 追加锚（本行以下为增补区）

## 86. Finite amplitude observations and the missing interaction stability control

**Definition 86.1 (actual energy, domains and the different observation model).** Fix the same unit source at $e$, $G=H^1\times\mathbb R$, Lebesgue Haar measure, projection $\pi$, horizontal metric and free $L$ clock as (82.5). Thus, in the original coordinates,

$$
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\quad L=-\sum_{i=1}^3X_i^2,
\quad \delta_r(\xi,w)=(r\xi,r^2w),\quad Q=5.
\tag{86.1}
$$

Here $L$ is the nonnegative self-adjoint free realization of Definition 84.1, and $\Gamma$ is exactly (82.8), with degree $-3$, not a truncated, massive or compressed substitute. Put $\mathcal H=L^2(G,d\mu)$, with inner product $\langle f,u\rangle=\int\overline f u\,d\mu$, conjugate linear in the first argument. Write

$$
\begin{gathered}
\mathcal D=D(L^{1/2})\cap D(M_{\sqrt\Gamma}),\qquad
\mathcal R=D(L)\cap D(M_\Gamma),\qquad
\mathcal D_0=C_c^\infty(G\setminus\{e\}),\\
t(f,u)=\sum_i\langle X_if,X_iu\rangle,\quad T[u]=t(u,u),\quad
V[u]=\|\sqrt\Gamma u\|_2^2,\quad q[u]=aT[u]-gV[u],\quad a,g>0,\\
\|u\|_H^2=\|u\|_2^2+T[u].
\end{gathered}
\tag{86.2}
$$

The functional $q$ has finite integrals on $\mathcal D$. No closed or semibounded full-space singular interacting form is assumed. In particular $\mathcal R\subset\mathcal D$: the free spectral calculus gives $D(L)\subset D(L^{1/2})$, and $V[u]\le\|\Gamma u\|_2\|u\|_2$ on $D(M_\Gamma)$. Every punctured compact test belongs to $\mathcal R$, by the free integration-by-parts domain and boundedness of $\Gamma$ on its support. All these domains are complex vector spaces.

For any $m\ge0$ and any $f_1,\ldots,f_m\in\mathcal H$, the finite amplitude observation is

$$
Au=(\langle f_1,u\rangle,\ldots,\langle f_m,u\rangle),\qquad
F=\operatorname{span}_{\mathbb C}\{f_1,\ldots,f_m\},\quad
E=A\mathcal H\subseteq\mathbb C^m,\quad k=\dim F=\dim E.
\tag{86.3}
$$

Each observation is bounded, complex linear, and $\ker A=F^\perp$. Dependent and zero probes are allowed; a right inverse has domain $E$, not an assumed $\mathbb C^m$. These amplitudes are a different observation model from the continuous marginal reader $\mathscr R$ of Theorem 82.5. Neither amplitudes nor the optional scalar $T$ are identified with native Reads. The band $\mathcal H_\Lambda$, projector $P_\Lambda$ and conditional-density cap $\mathcal C_M$ retain Definitions 85.1 and 84.1, including the convention on zero marginal fibres.

For support arguments use the homogeneous norm $N(\xi,s)=(|\xi|^4+s^2)^{1/4}$ in the gauge $s=w-xy/2$. It is continuous, vanishes only at $e$, and satisfies $N(\delta_rp)=rN(p)$. Smoothness, positivity and homogeneity of the actual field give $\Gamma\le C N^{-3}$ off $e$, by its maximum on $N=1$.

**Lemma 86.2 (finite-codimension concentration with a genuine exterior right inverse).** For every list (86.3) there exist $\rho>0$, a fixed finite family of punctured compact tests supported in $\{N>\rho\}$ giving a right inverse $J:E\to\mathcal D_0$ of $A$, and normalized $v_r\in\mathcal D_0\cap\ker A$, for all sufficiently small $r>0$, such that

$$
T[v_r]\sim A_0r^{-2},\qquad V[v_r]\sim B_0r^{-3},\qquad
q[v_r]\longrightarrow-\infty,
\quad A_0,B_0>0,\quad v_r\rightharpoonup0\text{ in }\mathcal H.
\tag{86.4}
$$

The correction family has the full effective rank $k$. The choice of $\rho$ depends on the list; no assertion of full rank on an arbitrary preassigned exterior is needed. The conclusion also holds after adjoining any finite list of actual $L^2$ representers.

Proof. Choose an orthonormal basis $g_1,\ldots,g_k$ of $F$. The Gram matrix of $\mathbf1_{\{N>\rho\}}g_j$ tends to the identity as $\rho\downarrow0$, by absolute continuity of the $L^2$ integrals and the null measure of $e$. For a sufficiently small positive $\rho$ it is positive definite. Thus the effective independent functionals remain independent on $L^2(\{N>\rho\})$. Compact smooth tests in this open exterior are dense there. Their image under $A$ is a linear subspace of the finite-dimensional space $E$, hence closed; density and the preceding rank show that this image is all of $E$. Choose tests whose images are a basis of $E$ and invert their image matrix. This defines $J$, with $AJ=I_E$. If $k=0$, take $J=0$. This argument is the mature finite-dimensional right-inverse construction, with its exterior rank verified here.

Choose a fixed normalized $u\in\mathcal D_0$ supported in a compact annulus $0<c\le N\le C_1$, and let $u_r=r^{-5/2}u\circ\delta_{1/r}$. The §82 change of variables gives

$$
\|u_r\|_2=1,\qquad T[u_r]=A_0r^{-2},\quad
V[u_r]=B_0r^{-3},\qquad A_0=T[u]>0,\ B_0=V[u]>0.
\tag{86.5}
$$

For any $f\in\mathcal H$, $|\langle f,u_r\rangle|\le\|\mathbf1_{\{N\le C_1r\}}f\|_2\to0$. Consequently $Au_r\to0$ and $c_r=JAu_r\to0$ in the $L^2$, free form and $\Gamma$-weighted norms, since $J$ has a fixed finite smooth range. For $C_1r<\rho$, the supports of $u_r$ and $c_r$, and of their horizontal derivatives, are disjoint. Hence $z_r=u_r-c_r$ has $Az_r=0$ and

$$
\|z_r\|_2^2=1+\|c_r\|_2^2,quad
T[z_r]=A_0r^{-2}+T[c_r],\quad V[z_r]=B_0r^{-3}+V[c_r].
\tag{86.6}
$$

Set $v_r=z_r/\|z_r\|_2$. Equations (86.6) prove the two asymptotics, with no rate assumption on $Au_r$; the negative term has higher order. Weak convergence follows from that of $u_r$ and strong convergence of $c_r$ to zero. Each support is compact and avoids $e$. Adjoining finitely many $L^2$ representers simply repeats the rank argument for the enlarged effective span. $\square$

**Theorem 86.3 (local free-form ambiguity, approximate readings and exact normalized fibres).** Let $\phi\in\mathcal D$, $\|\phi\|_2=1$, and fix (86.3). There are normalized $\psi_r\in\mathcal D$ with

$$
\|\psi_r-\phi\|_H\to0,\qquad A\psi_r\to A\phi,\qquad
T[\psi_r]\to T[\phi],\qquad V[\psi_r]\to\infty,
\qquad q[\psi_r]\to-\infty.
\tag{86.7}
$$

If $\phi\in\mathcal R$, the perturbations can all be taken in $\mathcal R$. For exact amplitudes, the normalized fibre in $\mathcal H$ is a singleton if and only if $\phi\in F$. The same singleton criterion holds after intersecting the fibre with $\mathcal D$, or with $\mathcal R$ when $\phi\in\mathcal R$. If $\phi\notin F$, (86.7) can be achieved with $A\psi_r=A\phi$ for every $r$. This is not a claim of exact kinetic equality.

Proof. Apply Lemma 86.2 with the additional representer $\phi$ to obtain $\langle\phi,v_r\rangle=0$. Fix $1<\beta<3/2$, put $b_r=r^\beta$, and first take

$$
\psi_r=\frac{\phi+b_rv_r}{\sqrt{1+b_r^2}}.
\tag{86.8}
$$

Normalization is exact, and $A\psi_r=A\phi/\sqrt{1+b_r^2}$. The free-form change is bounded by the normalization change times $\|\phi\|_H$, plus $b_r\|v_r\|_H$, and tends to zero since $b_r/r\to0$. Triangle inequality for the actual weighted $L^2$ space, on the whole domain $\mathcal D$, gives

$$
\sqrt{V[\psi_r]}\ge
\frac{b_r\sqrt{V[v_r]}-\sqrt{V[\phi]}}{\sqrt{1+b_r^2}}\longrightarrow\infty,
\tag{86.9}
$$

because $b_rr^{-3/2}\to\infty$. Free-form convergence gives kinetic convergence and then $q\to-\infty$. All sums remain in $\mathcal D$, and in $\mathcal R$ if the target is regular. In particular an explicit regular target is any normalized nonzero punctured compact test; (86.8) already proves its local ambiguity. No smoothness-to-multiplier-domain inference is used for a general target.

For the exact fibre, let $p=P_F\phi$. Hilbert orthogonal projection gives exactly

$$
\{\psi:\|\psi\|_2=1, A\psi=A\phi\}
 =\{p+z:z\in F^\perp,\ \|z\|_2^2=1-\|p\|_2^2\}.
\tag{86.10}
$$

If $\phi\in F$, the right side is $\{\phi\}$. If $\phi\notin F$, it is a nontrivial sphere. To prove the stronger local assertion in the actual domains, rather than merely use that sphere, note that $\mathcal D_0\cap\ker A$ is $L^2$ dense in $\ker A$: approximate any $z\in\ker A$ by $z_n\in\mathcal D_0$, then subtract $JAz_n\to0$ using Lemma 86.2. Since $P_{F^\perp}\phi\ne0$, choose a normalized $u\in\mathcal D_0\cap\ker A$ and change its phase so $d=\langle\phi,u\rangle>0$ is real. Apply Lemma 86.2 with the additional representers $\phi,u$, so $v_r$ is orthogonal to both. For $b_r<d$ put

$$
c_r=-d+\sqrt{d^2-b_r^2}
 =-\frac{b_r^2}{d+\sqrt{d^2-b_r^2}},\qquad
\psi_r=\phi+b_rv_r+c_ru.
\tag{86.11}
$$

Then $A\psi_r=A\phi$ and $\|\psi_r\|_2^2=1+2dc_r+c_r^2+b_r^2=1$. Also $c_r=O(b_r^2)$, so free-form convergence still holds. The weighted norm of $\phi+c_ru$ stays bounded, whereas $b_r\sqrt{V[v_r]}\to\infty$. The weighted reverse triangle again proves potential divergence. Thus every nonsingleton case has actual local witnesses, including in the original regular subclass. No assumption that $P_F\phi$ itself is regular is necessary. $\square$

**Proposition 86.4 (a genuine additional singleton from exact kinetic equality).** There exist a normalized $\phi\in\mathcal D_0$, a single bounded amplitude probe with representer $f\in\mathcal H$, and $T_\phi=T[\phi]>0$, for which the normalized exact amplitude fibre is nonsingleton, but

$$
\{\psi\in D(L^{1/2}):\|\psi\|_2=1,\ \langle f,\psi\rangle=\langle f,\phi\rangle,
\ T[\psi]=T_\phi\}=\{\phi\}.
\tag{86.12}
$$

Proof. Choose a normalized product $\phi(x,y,z,w)=b(x,y,w)\zeta(z)$ of nonzero smooth compact factors, with $b$ supported away from $(x,y)=(0,0)$. It is a punctured compact test. It is not an eigenfunction of $L$. Indeed, if $L\phi=\lambda\phi$, projection in $(x,y,w)$ against $b$ gives $-\zeta''+c\zeta=\lambda\zeta$ for a real constant $c$. A compactly supported nonzero smooth solution of this constant-coefficient ODE is impossible by uniqueness from zero Cauchy data outside its support. Fix $\tau>0$ and take $f=(L+\tau)\phi\in L^2$. Then $f$ is not proportional to $\phi$, so $\phi\notin\operatorname{span}\{f\}$ and Theorem 86.3 proves that the amplitude-only fibre is nonsingleton.

For $\psi$ in (86.12), define the strictly positive free inner product $t_\tau(u,v)=t(u,v)+\tau\langle u,v\rangle$. The operator-form identity gives

$$
t_\tau(\phi,\psi)=\langle (L+\tau)\phi,\psi\rangle
 =T_\phi+\tau,qquad
t_\tau(\phi,\phi)=t_\tau(\psi,\psi)=T_\phi+\tau.
\tag{86.13}
$$

Equality in Cauchy--Schwarz forces $\psi$ to be proportional to $\phi$, and the positive exact complex response forces the proportionality factor to be one. This proves (86.12). In contrast, Theorem 86.3 produces exact-amplitude collapsing perturbations with $T[\psi_r]\to T_\phi$, so every positive kinetic tolerance still permits those perturbations. A simpler amplitude-only singleton uses $f=\phi$ and the exact response one. These examples forbid a blanket collapse assertion on every normalized exact record. $\square$

**Theorem 86.5 (a joint zero-amplitude norm/kinetic/band/cap fibre).** For every finite list (86.3), every $0<\Lambda<\infty$, every $M>0$ and every prescribed $T_*>0$, there exist

$$
\phi\in\mathcal R\cap\mathcal H_\Lambda\cap\mathcal C_M,qquad
\psi_r\in\mathcal R,
\tag{86.14}
$$

with, simultaneously for these actual states,

$$
A\phi=A\psi_r=0,qquad \|\phi\|_2=\|\psi_r\|_2=1,qquad
T[\phi]=T[\psi_r]=T_*,qquad
V[\psi_r]\to\infty,quad q[\psi_r]\to-\infty.
\tag{86.15}
$$

Every sufficiently small $r$ has $\psi_r\notin\mathcal H_\Lambda$, and eventually $\psi_r\notin\mathcal C_M$. There is also a normalized $b\in\mathcal R\cap\mathcal H_\Lambda\cap\mathcal C_M\cap\ker A$ with $T_b=T[b]<T_*$ such that $\psi_r\to b$ in $L^2$, but not in the free form norm. All states use the same actual analytic source, field, projection and clock.

Proof. First verify a regular test class. In the original $w$ gauge, finite sums of $u(\xi)h(w)$, with $u\in C_c^\infty(\{R>\delta\})$, $\delta>0$, and $\widetilde h\in C_c^\infty(\mathbb R)$, have compact horizontal support and Schwartz central factors. Explicitly

$$
\begin{aligned}
X_1(uh)&=(\partial_xu)h,\quad X_2(uh)=(\partial_yu)h+xuh',\quad
X_3(uh)=(\partial_zu)h,\\
L(uh)&=-(\Delta_\xi u)h-2x(\partial_yu)h'-x^2uh''.
\end{aligned}
\tag{86.16}
$$

These derivatives are in $L^2$ because $x$ is bounded on the horizontal support. Multiplying by a central cutoff $\chi(w/n)$ gives punctured compact tests converging with both the first horizontal derivatives and $L$; the additional terms contain $x\chi'/n$ or $x^2\chi''/n^2$ and vanish by the Schwartz tails. The closed free operator therefore contains the products in $D(L)$. Independently, the actual field estimate (85.13) gives $\Gamma\le1/(8\delta^3)$ on their support, so they are in $D(M_\Gamma)$. This proves regularity, also for their finite sums, without asserting it for arbitrary smooth band states. The non-multiplier-domain example after (85.18) retains its full force.

Choose a real normalized Schwartz $h$ with smooth even Fourier transform supported in a small interval $[-\sigma_0,\sigma_0]$, and real normalized horizontal products supported away from $x=0$. Take $m+1$ disjoint $z$ translates of one such product times $h$. They are normalized, have disjoint horizontal supports, and all have one finite kinetic value $t_0>0$. Homogeneous expansion $U_Su=S^{-5/2}u\circ\delta_{1/S}$, with $S$ sufficiently large, makes their common kinetic value $t_0S^{-2}<T_*$ and their bandwidth $\sigma=\sigma_0S^{-2}<\min(\Lambda,\pi M)$. Their horizontal supports remain disjoint and away from $R=0$. The linear map $A$ on their $(m+1)$-dimensional span has a nonzero kernel vector. Normalize one to obtain $b$. Disjoint supports make its kinetic value exactly $T_b=t_0S^{-2}$, regardless of its complex coefficients. The sharp cap (85.5) gives $b\in\mathcal C_M$.

Take a second set of $m+1$ disjoint $z$ translates of the expanded templates, with supports disjoint from those of $b$, and multiply all of them by $e^{iKz}$. Their bandwidth is still $\sigma$. Since their unmodulated horizontal factors are real, the $\partial_z$ cross term has zero real part, and each normalized template has kinetic value $T_b+K^2$. A normalized kernel vector $d$ in this second span therefore has $Ad=0$, $T_d=T_b+K^2$, and disjoint horizontal support from $b$. Choose $K$ with $T_d>T_*$. The single band comparison state

$$
\phi=\sqrt{1-\theta}\,b+\sqrt\theta\,d,qquad
\theta=\frac{T_*-T_b}{T_d-T_b}\in(0,1)
\tag{86.17}
$$

has exact norm one, amplitudes zero and kinetic $T_*$. It remains in the narrower band $\mathcal H_\sigma$, hence has cap at most $\sigma/\pi<M$, and it is regular by (86.16).

Now apply Lemma 86.2 to the original list with the additional $L^2$ representers $b,Lb$. They are legitimate because regularity was proved separately. We obtain normalized punctured compact $v_r$ with $Av_r=0$, $\langle b,v_r\rangle=0$ and $t(b,v_r)=\langle Lb,v_r\rangle=0$. Let $T_r=T[v_r]$ and set

$$
\eta_r=\frac{T_*-T_b}{T_r-T_b},\qquad
\psi_r=\sqrt{1-\eta_r}\,b+\sqrt{\eta_r}\,v_r.
\tag{86.18}
$$

For small $r$, $0<\eta_r<1$ and $\eta_r\sim (T_*-T_b)r^2/A_0$. Orthogonality gives the exact three equalities in (86.15), not separate feasibility statements. Weighted Cauchy--Schwarz bounds the potential cross term by $2\sqrt{\eta_r(1-\eta_r)V[b]V[v_r]}$. Consequently

$$
V[\psi_r]\sim\eta_rV[v_r]
 \sim\frac{(T_*-T_b)B_0}{A_0}\,r^{-1}\longrightarrow\infty.
\tag{86.19}
$$

Here the bounded $V[b]$ term and the cross term of order $r^{-1/2}$ are lower order than $r^{-1}$. Each state is regular by linearity of the two operator domains.

Proposition 85.9 says that a nonzero compact-central-support state cannot belong to $\mathcal H_\Lambda$. Since $v_r\in\mathcal D_0$ is nonzero and $b\in\mathcal H_\Lambda$, $(I-P_\Lambda)\psi_r=\sqrt{\eta_r}(I-P_\Lambda)v_r\ne0$. If a normalized $\psi_r$ satisfied $\mathcal C_M$, (84.6) and (84.10) would give $V[\psi_r]\le M\sqrt{T_*}/(4\pi)$, contradicting (86.19) for small $r$. Finally $\eta_r\to0$ gives $L^2$ convergence to $b$, whereas

$$
T[\psi_r-b]=(\sqrt{1-\eta_r}-1)^2T_b+\eta_rT_r
 \longrightarrow T_*-T_b>0.
\tag{86.20}
$$

Thus a fixed positive kinetic increment is not free-form convergence. $\square$

The positivity endpoints in this theorem are essential. The zero central band contains only zero, since the singleton frequency set has zero Plancherel measure. A normalized free form state cannot have $T=0$: (84.5) forces $\sqrt{m_\psi}$ to be a constant $L^2(\mathbb R^3)$ function, hence zero. A normalized cap-zero state is also impossible, since its conditional density must integrate to one on positive-marginal fibres.

**Theorem 86.6 (uniform bounded adaptive acceptance and its stopping exceptions).** Fix $\Lambda,M,T_*>0$ as in Theorem 86.5. Let

$$
\mathcal P=\{u\in\mathcal R\cap\mathcal H_\Lambda\cap\mathcal C_M:
 \|u\|_2=1, T[u]=T_*\},\qquad
\mathcal U=\{u\in\mathcal R:\|u\|_2=1, T[u]=T_*\}.
\tag{86.21}
$$

Consider a deterministic protocol whose only state-dependent answers are bounded complex amplitudes and the scalar kinetic value. Probe selection, output and stopping depend only on the preceding answers and declared fixed parameters. Suppose it stops and accepts every input in $\mathcal P$ within a uniform finite $N$ total queries, counting amplitude and kinetic queries. It cannot be sound on $\mathcal U$ if its accepting output certifies band membership, cap membership, or a finite lower bound on the actual $q$. Refusal is allowed in general; complete acceptance on $\mathcal P$ is an essential premise here. Soundness restricted to $\mathcal P$ is a different assertion and is compatible with the supplied bounds of §§84–85.

Proof. Follow the response branch with every amplitude equal to zero and every kinetic answer $T_*$. Follow it only until its first stopping decision or $N$ total queries. It selects a finite list of actual bounded representers. Theorem 86.5 realizes this list by a state $\phi\in\mathcal P$. Induction on queries shows that $\phi$ has this exact record: the preceding zero answers select the same next probe. Therefore a refusal before $N$, or failure to accept by the $N$-query deadline, contradicts complete uniformly bounded acceptance. This includes a decision after zero queries when $N=0$. Let $j\le N$ be its total number of queries at acceptance. Apply Theorem 86.5 to the selected accepting prefix. Its collapsing $\psi_r\in\mathcal U$ gives the same amplitudes, norm and kinetic scalar and hence exactly the same accepting record and output. For small $r$ it is outside both restrictions, and its actual energy is below any finite lower bound in that output. This is a realized finite-fibre argument. It does not apply a theorem requiring continuity of the singular target $V$. $\square$

The fixed-record principle used here also says that any other finite deterministic adaptive record has the fibre of its selected functionals, intersected with any norm or exact kinetic constraints actually supplied. It does not assert that this intersection is always large: (86.10) and (86.12) exhibit singleton exceptions. The induction is the linear adaptive-record observation in Krieg--Novak--Ullrich, *How many continuous measurements are needed to learn a vector?*, [arXiv:2412.06468v1](https://arxiv.org/abs/2412.06468v1), pp. 1–2. Their nonlinear adaptive measurement results concern a different family.

Per-state finite stopping is not a uniform budget. A concrete exception to any unqualified finite-stopping impossibility is as follows. Since $\mathcal D_0$ is dense in the separable Hilbert space $\mathcal H$, Gram--Schmidt on a countable total list gives an orthonormal basis $(e_j)$ with every $e_j\in\mathcal R$. On normalized states, query $\langle e_j,u\rangle$ successively and stop as soon as $\sum_{j\le n}|\langle e_j,u\rangle|^2=1$. At a stop, Pythagoras forces $u=\sum_{j\le n}\langle e_j,u\rangle e_j$, so the fibre in the entire normalized Hilbert sphere is a singleton. On the promise class of normalized finite expansions, this protocol terminates for every state, has no uniform bound, and its record determines the actual finite energy of the regular state. This is an information assertion, without a bound on computation or acquisition cost. Infinite expansions do not terminate. Moreover every finite zero prefix is realized by $e_{n+1}$, while the entire infinite zero sequence is realized by no normalized state, by completeness. Thus witnesses depending on a finite horizon do not manufacture an infinite normalized zero path. This example does not claim finite stopping on every member of $\mathcal P$.

**Theorem 86.7 (finite accepting noisy records with positive response margins).** Consider a finite accepting branch of a deterministic protocol as above, realized with reports $y_j$ for its selected amplitude probes and reports $s_\ell$ for its finitely many kinetic queries. Let a normalized $\phi\in\mathcal D$ satisfy all branch response constraints with strict positive margins:

$$
|\langle f_j,\phi\rangle-y_j|<\varepsilon_j,quad\varepsilon_j>0,qquad
|T[\phi]-s_\ell|<\kappa_\ell,quad\kappa_\ell>0.
\tag{86.22}
$$

Then the same reports and accepting branch are compatible with normalized $\psi_r\in\mathcal D$ having $q[\psi_r]\to-\infty$. If $\phi\in\mathcal R$, all witnesses are regular. Thus no finite actual-energy lower certificate can be sound on all states compatible with such a record. For every fixed positive finite $\Lambda$ and $M>0$, these witnesses are also eventually outside $\mathcal H_\Lambda$ and $\mathcal C_M$.

Proof. Freeze the finite probe list selected by those reports and apply the approximate-reading construction (86.8). Free-form convergence gives $T[\psi_r]\to T[\phi]$, and boundedness of every selected functional gives its amplitude convergence. The minimum of the finitely many strictly positive response margins is positive. For sufficiently small $r$, each actual amplitude and kinetic value remains within its declared error radius about the same report. Induction using the same reports gives the same selected probes and stopping decision, while (86.9) makes the energy arbitrarily negative. Since their kinetic values remain bounded and their norms are one, the potential bounds (84.6), (84.10) and (85.9) exclude membership in each fixed band and cap for sufficiently small $r$. The proof uses permitted error sets, not a claim that a noise mechanism must generate every compatible report. $\square$

For an accepting quantized branch the same argument requires that every actual response lie in the interior of its reported cell, with a strictly positive neighbourhood contained in that cell. Zero-margin boundaries are excluded. If amplitudes are exact and $\phi\notin F$, (86.11) instead gives their exact equality together with any strictly positive kinetic tolerance. Exact kinetic equality is not covered by this extension, by Proposition 86.4. No statement about arbitrary nonlinear observations, randomized probabilities, or infinitely many response constraints is supplied.

**Theorem 86.8 (actual interaction-weighted error and a conditional energy-transfer consumer).** For any $\psi,\phi\in\mathcal D$, define

$$
d_\Gamma=\|\sqrt\Gamma(\psi-\phi)\|_2,qquad
d_H=\left(\sum_i\|X_i(\psi-\phi)\|_2^2\right)^{1/2}.
\tag{86.23}
$$

On this whole domain, without any multiplier-domain assumption,

$$
\begin{aligned}
|V[\psi]-V[\phi]|&\le2\sqrt{V[\phi]}d_\Gamma+d_\Gamma^2,\\
|T[\psi]-T[\phi]|&\le2\sqrt{T[\phi]}d_H+d_H^2.
\end{aligned}
\tag{86.24}
$$

Suppose a comparator $\phi$ and actual state $\psi$ are normalized, and independently justified data supply $V[\phi]\le B<\infty$, $d_\Gamma\le\epsilon$ and $|T[\psi]-T[\phi]|\le\kappa$. Then

$$
\begin{aligned}
|q[\psi]-q[\phi]|&\le a\kappa+g(2\sqrt B\epsilon+\epsilon^2),\\
q[\psi]&\ge a(T[\phi]-\kappa)-g(\sqrt B+\epsilon)^2.
\end{aligned}
\tag{86.25}
$$

For an independently justified $\phi\in\mathcal C_M$, one may take $B=M\sqrt{T[\phi]}/(4\pi)$ and use the actual §84 lower bound to obtain

$$
q[\psi]\ge-\frac{g^2M^2}{64\pi^2a}
 -a\kappa-g(2\sqrt B\epsilon+\epsilon^2).
\tag{86.26}
$$

For an independently justified $\phi\in\mathcal H_\Lambda$, replace $B$ by $\Lambda\sqrt{T[\phi]}/(4\pi^2)$ and the first constant by $g^2\Lambda^2/(64\pi^4a)$. These are sufficient scalar error and admissibility interfaces; they do not require full-state, full marginal or conditional-density recovery. In particular, a valid supplied cap on $\psi$ itself already suffices for its existing §84 lower bound, without comparison with $\phi$.

Proof. Put $h=\psi-\phi$. In the genuine Hilbert space $L^2(G,\Gamma d\mu)$, expansion and Cauchy--Schwarz give

$$
V[\psi]-V[\phi]
 =2\operatorname{Re}\langle\sqrt\Gamma\phi,\sqrt\Gamma h\rangle+d_\Gamma^2.
\tag{86.27}
$$

All terms are finite by $\mathcal D$; this neither uses $\Gamma\phi\in L^2$ nor introduces it as a bounded-probe representer. The same expansion in the three-component horizontal derivative space proves the kinetic estimate. Substitute the separately supplied kinetic accuracy and potential bound to obtain (86.25). The cap estimate is (84.6) combined with (84.10); its normalized lower bound is (84.7). The band estimates are exactly (85.8)–(85.9). Substituting them in the first line of (86.25) proves (86.26) and its band version. The original regular subclass is included, but is not needed for these weighted Hilbert calculations. $\square$

A concrete way to close the missing weighted control is to supply, in addition to an $L^2$ error $\|\psi-\phi\|_2\le e_0$, an actual weighted remainder estimate

$$
\int_{G\setminus\Omega}\Gamma|\psi-\phi|^2d\mu\le\eta^2,qquad
\Omega=\{\rho\le N\le R_0\},\quad 0<\rho<R_0<\infty.
\tag{86.28}
$$

Then the bounded field on $\Omega$ gives

$$
d_\Gamma^2\le C\rho^{-3}e_0^2+\eta^2.
\tag{86.29}
$$

Alternatively separately supplied weighted tail norms of $\psi$ and $\phi$ bound the remainder by their sum through triangle inequality. The remainder includes the puncture and the exterior tail, so an unweighted far-tail estimate alone does not discharge (86.28). Theorem 86.3 has $d_H\to0$ and $\|\psi_r-\phi\|_2\to0$ while $d_\Gamma\to\infty$, by the reverse triangle and $V[\psi_r]\to\infty$. Theorem 86.5 has exact common amplitudes and kinetic value with the same divergent weighted obstruction relative to its fixed comparison state. Thus neither a name for $\eta$ or $\epsilon$, nor finite amplitudes plus free-kinetic accuracy, acquires the missing estimate. The conditional consumer in (86.25) becomes valid when the estimate or a sufficient actual admissibility bound is independently established.

**Definition 86.9 (reference correspondence and remaining source bridges).** The finite-dimensional Gram inversion, Riesz representation, Hilbert projection and equality cases used inside these proofs are mature supplies; see Teschl, *Mathematical Methods in Quantum Mechanics*, [primary text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), §1.3, Theorems 1.7–1.8, and §7.1 for Fourier inversion and Plancherel. Here the Hilbert space is the actual $L^2(G,d\mu)$, the effective output space is $E$, the auxiliary representers in (86.18) are $b,Lb\in L^2$, and the positive equality inner product in (86.13) is the free $t+\tau\langle\cdot,\cdot\rangle$. In the band construction the Fourier convention and fibre evaluation constant are precisely (85.2) and (85.5), with the gauge equivalence already proved in §85. No non-$L^2$ multiplier target is inserted into a probe list.

Folland's [1975 primary paper](https://doi.org/10.1007/BF02386204), Theorem 2.1, Theorem 3.1, Corollaries 3.4–3.6 and Proposition 3.17 at $\alpha=2$, is matched through Proposition 82.4 to this Haar normalization, horizontal generator and actual degree-$-3$ point-source field. The client steps supplied here are exterior rank retention, correction estimates, horizontal/operator-domain checks, local normalized fibre constructions and joint kinetic matching. The heat or Fourier supplier names alone do not prove these steps. Kombe, [arXiv:math/0501522v1](https://arxiv.org/abs/math/0501522v1), Theorem 4.1 at $\alpha=0$ and $Q=5$, has the degree-$-2$ Hardy weight $|\nabla_HN_F|^2/N_F^2$, where $N_F$ is defined from Folland's solution. It is not the degree-$-3$ actual $\Gamma$, and its H-type explicit kernel is not substituted for this product-group field. The cap and band consumer bounds instead use the previously matched three-dimensional marginal and Hardy/Coulomb estimates in §§84–85.

Hinrichs--Novak--Woźniakowski, *Discontinuous information in the worst case and randomized settings*, [arXiv:1106.2945v1](https://arxiv.org/abs/1106.2945v1), §2, equation (2), takes the radius over realized information values $y\in N(F)$. Its Theorem 1 assumes a continuous target operator. Here the singular $V$ is not continuous in the free form norm, as (86.7) proves, and that theorem is not an impossibility supplier for $V$. The finite-record induction and the actual fibre witnesses establish the present conclusions directly. Krieg--Novak--Ullrich's linear fixed-record observation supplies only that induction, not the concentration or the norm/kinetic/admissibility intersection. The present source-specific applications are repository-derived, with mature ingredients acknowledged. The correspondence is bounded to these references and §§82–85, not an exhaustive absence-of-overlap or originality claim.

The analytic source equality in (86.15) means one fixed $e,\Gamma,G,L,\mu,\pi$ and free clock, not a proved common native source-to-state realization. A native application must separately preserve the original source and immutable INITIAL, its same-source chronology, authentic Read/refusal/Stop semantics, and lawful state/probe acquisition, preparation, copying, retention, clocks, resources, permissions and costs. Neither the construction of an $L^2$ representer nor a band/cap certificate as a mathematical premise grants an operation acquiring it. Native retained-literal/root-depth or serial service results concern their own complete acquired source fibres and tasks; without an explicit correspondence they supply no analytic probe, carrier state, preparation, admissibility or optimal cost. All source-to-carrier, source-to-probe and source-to-state maps remain open. The weighted interface is a conditional analytic stability application, not a physical why-three conclusion or a resolution of those native bridges.

## 78.99 追加锚（本行以下为增补区）

## 87. Central regularity order: sharp endpoint, closed kinetic laws and fixed-budget escape

**Definition 87.1 (three distinct contracts on the unchanged source).** Keep the literal $G=H^1\times\mathbb R$, $e$, Lebesgue Haar measure, $X_i$, $L$, $\Gamma$, $\pi$ and free clock of (82.5), (82.8) and (84.1). In particular $\Gamma$ is the actual positive degree-$-3$ Green field, with $\int\Gamma(\xi,w)dw=(4\pi|\xi|)^{-1}$. Put $D_w=-i\partial_w$, and for $\sigma>0$ define

$$
\begin{gathered}
D_\sigma[\psi]=\big\||D_w|^{\sigma/2}\psi\big\|_2^2,qquad
\mathcal E_\sigma=D(L^{1/2})\cap D(|D_w|^{\sigma/2}),\
\|\psi\|_{\mathcal E_\sigma}^2=\|\psi\|_2^2+T[\psi]+D_\sigma[\psi],\
\mathcal A_\sigma=\mathcal E_\sigma\cap D(M_{\sqrt\Gamma}),\qquad
q_0[\psi]=aT[\psi]-gV[\psi],\
q_{\sigma,\eta}[\psi]=aT[\psi]+\eta D_\sigma[\psi]-gV[\psi],\
\mathcal B_{\sigma,B}=\{\psi\in\mathcal A_\sigma:\|\psi\|_2=1,\ D_\sigma[\psi]\le B\},
\qquad a,g,\eta>0.
\end{gathered}
\tag{87.1}
$$

The added-law contract is $q_{\sigma,\eta}$, whose kinetic functional differs from $q_0$. The fixed-budget contract is the original $q_0$ restricted to $\mathcal B_{\sigma,B}$. Mere finiteness means membership in $\mathcal A_\sigma$, with no common $B$ and no added term. For $\sigma\ge2$ the estimates below prove $\mathcal A_\sigma=\mathcal E_\sigma$; no such whole-domain equality is required for $0<\sigma<2$. All potential integrals on $\mathcal A_\sigma$ are actual same-field integrals.

Use the shear $s=w-xy/2$ of (85.1). For convenience write the unitary central transform as $b(\xi,\lambda)=(2\pi)^{-1/2}\int e^{-i\lambda s}\Psi(\xi,s)ds$. Then

$$
D_\sigma[\psi]=\int_{\mathbb R^3\times\mathbb R}|\lambda|^\sigma|b(\xi,\lambda)|^2d\xi d\lambda.
\tag{87.2}
$$

The phase relating the $w$ and $s$ transforms does not change this expression. The intersection domain in (87.1) is a dense Hilbert form domain. The punctured core $\mathcal D_0$ is dense in it for every finite $\sigma$: first truncate central frequencies, using the strong free commutation in Proposition 85.2, and approximate the free form by compact smooth functions before applying that truncation. These projected tests have compact horizontal support and smooth central tails, with every central derivative square integrable. Central smooth cutoffs converge in any fixed integer central Sobolev norm and in the horizontal norm, by their tails and the bounded horizontal coefficients on this support; interpolation gives convergence in the required fractional central norm. Finally remove a horizontal cylinder $|\xi|<\varepsilon$. For a fixed smooth compact test, its squared horizontal cutoff-gradient cost is $O(\varepsilon)$ in three horizontal variables; central derivatives commute with this cutoff. The other terms tend to zero by dominated convergence. This proves punctured-core density without using a high-order cutoff at a point in four Euclidean variables.

For an $L^2$ state, $D_\sigma=0$ implies that its central Fourier transform is supported at the null singleton $\{0\}$, hence the state is zero. Likewise $T=0$ implies zero by (84.5). Thus $\mathcal B_{\sigma,0}$ is empty, whereas the zero vector is included in every linear form domain. Bounds involving powers of the norm are read at the zero vector by their continuous value zero. Budget assertions below require $0<B<\infty$.

**Theorem 87.2 (whole-domain sharp same-field estimate and a closed comparison).** For every nonzero $\psi\in\mathcal E_2$,

$$
0<V[\psi]<\frac18\sqrt{T[\psi]D_2[\psi]}.
\tag{87.3}
$$

The optimal non-strict constant on this whole domain, and already on $\mathcal D_0$, is $C_\star=1/8$. For every $\sigma\ge2$ and $\psi\in\mathcal E_\sigma$,

$$
V[\psi]\le\frac18\sqrt{T[\psi]}D_\sigma[\psi]^{1/\sigma}
 \|\psi\|_2^{1-2/\sigma}.
\tag{87.4}
$$

For nonzero states the estimate is strict; the constant in (87.4) is only asserted sharp at $\sigma=2$.

Proof. The mature trace-Hardy ingredient is Alvino--Ferone--Volpicelli, *Sharp Hardy inequalities in the half space with trace remainder term*, [arXiv:1105.0335v1](https://arxiv.org/abs/1105.0335v1), Theorem 1.1 and (8), with $n=4$, $\beta=2$. Each halfspace has constant $2/\pi$, so on both halfspaces

$$
A[f]+C[f]\ge\frac4\pi J[f],\qquad
A[f]=\|\nabla_\xi f\|_2^2,\quad C[f]=\|\partial_t f\|_2^2,
\quad J[f]=\int\frac{|\operatorname{Tr}f(\xi,0)|^2}{|\xi|}d\xi.
\tag{87.5}
$$

Here the trace belongs to its weighted space for every $f\in H^1(\mathbb R^4)$. The following representation also supplies the closure needed by the actual critical client. Write $r=|\xi|$, $\rho=(r^2+t^2)^{1/2}$ and $\Omega_*=\mathbb R^4\setminus\{0\}$. The auxiliary positive profile is

$$
\Phi(\xi,t)=\frac2{\pi r}\arctan\frac r{|t|},\qquad
\Phi(\xi,0)=\frac1r,\quad \Phi(0,t)=\frac2{\pi|t|},\qquad
\frac2{\pi\rho}\le\Phi\le\frac1\rho.
\tag{87.6}
$$

This is the $n=4$ integral in AFV (12), with its boundary value normalized. It is harmonic on each open halfspace, and $\partial_t\Phi(\xi,0^\pm)=\mp2/(\pi r^2)$. On $\mathscr C=C_c^\infty(\Omega_*;\mathbb C)$, expansion of $f=\Phi v$ and integration by parts in both halfspaces give

$$
\mathfrak t_0[f]:=A[f]+C[f]-\frac4\pi J[f]
 =\int\Phi^2|\nabla(f/\Phi)|^2.
\tag{87.7}
$$

Indeed the two outward normal derivatives contribute $4/(\pi r^2)$, multiplied by $|f(\xi,0)|^2/\Phi(\xi,0)$; the support avoids the origin, so no puncture boundary survives. This is the usual ground-state representation, with the singular interface term computed explicitly rather than treated as an ordinary bounded potential.

The densely defined operator $B_0f=\Phi\nabla(f/\Phi)$ from $L^2$ to $L^2(\mathbb R^4;\mathbb C^4)$ is closable. On every compact subset of $\Omega_*$, $\Phi,\Phi^{-1}$ are bounded and locally Lipschitz. If $f_n\to0$ and $B_0f_n\to F$ in their $L^2$ spaces, then $f_n/\Phi\to0$ locally and its gradients converge to $F/\Phi$. Closedness of distributional derivatives forces $F=0$. Consequently the closure $\mathfrak t$ has domain $\mathcal Q_\delta=D(\overline B_0)$ and

$$
\mathfrak t[f]=\|\overline B_0f\|_2^2
 =\int\Phi^2|\nabla(f/\Phi)|^2,\qquad f\in\mathcal Q_\delta.
\tag{87.8}
$$

The last equality follows by local distributional limits of graph approximants. The punctured smooth core is dense in $H^1(\mathbb R^4)$: a cutoff about the point costs $O(\varepsilon^2)$ for a fixed compact smooth function. Since $0\le\mathfrak t_0[h]\le\|\nabla h\|_2^2$, this density and (87.5) put every $H^1$ function in $\mathcal Q_\delta$, and give (87.7) on $H^1$ with the actual trace. No difference of infinite integrals defines (87.8). If $\mathfrak t[f]=0$, then $f/\Phi$ is constant on the connected $\Omega_*$. But $\Phi\notin L^2$ at infinity, since its lower bound in (87.6) gives $\int_1^\infty\rho^3\rho^{-2}d\rho=\infty$. Thus

$$
\{f\in\mathcal Q_\delta:\mathfrak t[f]=0\}=\{0\}.
\tag{87.9}
$$

For nonzero $f\in H^1$, apply (87.5) strictly to $k^{-1/2}f(\xi,t/k)$ and minimize $kA+C/k$. This yields $J[f]<(\pi/2)\sqrt{A[f]C[f]}$. Neither derivative can vanish for a nonzero $L^2$ function.

Now take the actual state $\psi\in\mathcal E_2$, put $U=\mathcal F_s^{-1}|b|$, and use the actual covariant derivatives

$$
\mathsf D^\lambda b=
 (\partial_xb-i\lambda yb/2,\ \partial_yb+i\lambda xb/2,\ \partial_zb).
\tag{87.10}
$$

The weak modulus chain rule gives $|\partial_i|b||\le|\mathsf D_i^\lambda b|$: away from zero take the real part of $\overline b\mathsf D_i^\lambda b/|b|$, whose magnetic term is imaginary, and use a regularized modulus at zero. Plancherel therefore gives $A[U]\le T[\psi]$, $C[U]=D_2[\psi]$ and $\|U\|_2=\|\psi\|_2$, so $U\in H^1$. On almost every central fibre the transform is in $L^1$ by its weighted $L^2$ norm with weight $1+\lambda^2$. Fourier inversion and triangle inequality give $|\Psi(\xi,s)|\le U(\xi,0)$, where this positive value agrees with the Sobolev trace. Apply the actual nonnegative $\mathcal G(\xi,s)=\Gamma(\xi,s+xy/2)$ and its actual marginal:

$$
V[\psi]\le\frac1{4\pi}J[U]
 <\frac18\sqrt{A[U]C[U]}\le\frac18\sqrt{TD_2}.
\tag{87.11}
$$

This is a comparison, not substitution of a marginal for the full multiplier. It proves finiteness on the whole intersection domain. Positivity of $\Gamma$ gives strict positive $V$ for a nonzero state.

For $\sigma>2$, Hölder in the genuine measure $|b|^2d\xi d\lambda$ gives

$$
D_2\le D_\sigma^{2/\sigma}\|\psi\|_2^{2-4/\sigma}.
\tag{87.12}
$$

Thus $\mathcal E_\sigma\subset\mathcal E_2$, and (87.11) gives (87.4), including its zero convention. The same-state sharpness of (87.3) is established next. $\square$

**Proposition 87.3 (joint punctured profiles and the endpoint threshold).** For every prescribed $h>0$ there are real normalized $f_j\in C_c^\infty(\mathbb R^3\times\mathbb R)$ supported in $r>\delta_j>0$, with

$$
\frac{A_j}{C_j}=h^2,\qquad
\frac{J_j}{4\pi\sqrt{A_jC_j}}\longrightarrow\frac18,
\quad A_j=A[f_j]>0,\ C_j=C[f_j]>0,\ J_j=J[f_j].
\tag{87.13}
$$

For each fixed such profile define an actual normalized punctured state by

$$
\Psi_{\varepsilon,j}(\xi,s)=\varepsilon^{-2}f_j(\xi/\varepsilon,s/\varepsilon),
\qquad
\psi_{\varepsilon,j}(\xi,w)=\Psi_{\varepsilon,j}(\xi,w-xy/2).
\tag{87.14}
$$

For every fixed finite $\sigma>0$ these states satisfy jointly

$$
\begin{aligned}
D_\sigma[\psi_{\varepsilon,j}]&=\varepsilon^{-\sigma}C_{\sigma,j},
 &C_{\sigma,j}&=\||D_t|^{\sigma/2}f_j\|_2^2>0,\
T[\psi_{\varepsilon,j}]&=\varepsilon^{-2}A_j+O_j(\varepsilon^{-1})+O_j(1),\
\varepsilon^2V[\psi_{\varepsilon,j}]&\longrightarrow J_j/(4\pi).
\end{aligned}
\tag{87.15}
$$

In particular $C_\star=1/8$, and the sharp critical coupling for the added $\sigma=2$ law is

$$
g_c=16\sqrt{a\eta}.
\tag{87.16}
$$

For $0<g\le g_c$ the law is nonnegative on $\mathcal E_2$; for $g>g_c$ it is unbounded below already on normalized $\mathcal D_0$.

Proof. For the trace ingredient, cut $\Phi$ off radially on $e^{-j}<\rho<1$, with transition regions of fixed multiplicative width. Equation (87.7) bounds the cutoff remainder by a constant independent of $j$, while its trace has $J=4\pi j+O(1)$. Hence $J/(A+C)\to\pi/4$. The optimized version of (87.5) and $2\sqrt{AC}\le A+C$ give $J/\sqrt{AC}\to\pi/2$. Smooth $H^1$ approximation removes the interface kink, and a horizontal cylindrical cutoff removes $r=0$ with arbitrarily small $H^1$ cost for each fixed smooth profile. The weighted trace converges by (87.5). Normalize in $L^2$ and centrally rescale by $k^{-1/2}f(\xi,t/k)$ to obtain exactly $A/C=h^2$. This rescaling leaves $J/\sqrt{AC}$ unchanged. These operations construct actual smooth profiles; they do not assert the existence of a trace extremizer.

The actual horizontal derivatives of (87.14), after change of variables $(\xi,s)=(\varepsilon v,\varepsilon u)$, are

$$
\varepsilon^{-1}\partial_{v_x}f_j-v_y\partial_uf_j/2,quad
\varepsilon^{-1}\partial_{v_y}f_j+v_x\partial_uf_j/2,quad
\varepsilon^{-1}\partial_{v_z}f_j.
\tag{87.17}
$$

Their squared norms give the second line of (87.15), with finite profile-dependent constants. Central Fourier scaling proves the first line. For the potential instead change variables $(\xi,s)=(\varepsilon v,\varepsilon^2t)$ and use the actual Carnot homogeneity:

$$
\varepsilon^2V[\psi_{\varepsilon,j}]
 =\int\mathcal G(v,t)|f_j(v,\varepsilon t)|^2dvdt
 \longrightarrow\frac1{4\pi}\int\frac{|f_j(v,0)|^2}{|v|}dv.
\tag{87.18}
$$

The dominating function is $\mathcal G(v,t)\sup_u|f_j(v,u)|^2$. It is integrable by the actual marginal and the compact horizontal support away from zero. This is dominated convergence for the same field, including all central frequencies and the full central tail. First fix $j$; only then take $\varepsilon\downarrow0$. Equations (87.13)--(87.18) give the sharp ratio. Choosing $h=\sqrt{\eta/a}$ makes $aA_j=\eta C_j$. If $g>g_c$, choose $j$ so that $aA_j+\eta C_j-gJ_j/(4\pi)<0$ and then concentrate. The leading energy is this negative coefficient times $\varepsilon^{-2}$. Nonnegativity at and below $g_c$ follows from (87.3) and $aT+\eta D_2\ge2\sqrt{a\eta TD_2}$. $\square$

**Theorem 87.4 (subcritical domain, proper critical completion and absence of a critical zero mode).** For $0<g<g_c$, $q_{2,\eta}$ is a closed nonnegative form on exactly $\mathcal E_2$. At $g=g_c$ its restriction to $\mathcal D_0$ has a nonnegative Friedrichs closure $\overline q_c$ with domain $\mathcal Q_c$, and

$$
\mathcal E_2\subsetneq\mathcal Q_c,\qquad
\{\psi\in\mathcal Q_c:\overline q_c[\psi]=0\}=\ker H_F=\{0\}.
\tag{87.19}
$$

Here $H_F$ is the associated nonnegative self-adjoint operator. On $\mathcal E_2$ the closure agrees with the finite integral expression. On all of $\mathcal Q_c$ the closed form, rather than subtraction of its separate kinetic and potential integrals, defines the energy. For $0<g\le g_c$ the normalized infimum is zero and is not attained in the respective closed domain. There is no positive uniform spectral gap. No complete intrinsic characterization of $\mathcal Q_c$ or original-field threshold resonance classification is asserted.

Proof. Set $S=aT+\eta D_2$ and $\theta=g/g_c$. Equation (87.3) gives $(1-\theta)S\le q_{2,\eta}\le S$ for $\theta<1$. The free intersection form is closed, and this norm equivalence proves the subcritical assertion, equivalently KLMN with relative bound $\theta<1$. At the endpoint the densely defined symmetric differential operator $aL+\eta D_w^2-g_c\Gamma$ on $\mathcal D_0$ is nonnegative by Proposition 87.3. The Friedrichs theorem gives a closable core form and its injective $L^2$ completion. Punctured-core density in $\mathcal E_2$ and $0\le q_c\le S$ imply inclusion and agreement there. They do not imply closedness on $\mathcal E_2$.

To verify that the inclusion is proper for the actual field, put $\kappa=\sqrt{\eta/a}$ and take a smooth radial outer cutoff $\chi(\rho)$ equal to one near zero. Let $f_*=\chi\Phi$ and

$$
\Psi_*(\xi,s)=\kappa^{-1/2}f_*(\xi,s/\kappa).
\tag{87.20}
$$

This is in $L^2$, but its ordinary gradient has a logarithmically divergent squared integral at zero. On compact boxes the $\mathcal E_2$ norm controls the ordinary $H^1$ norm, because $\partial_s$ is controlled and the shear coefficients are bounded. Thus the actual state in (87.20) is not in $\mathcal E_2$.

Choose inner radial cutoffs $\zeta_\varepsilon$ that vanish for $\rho\le\varepsilon^2$, equal one for $\rho\ge\varepsilon$, and satisfy $|\nabla\zeta_\varepsilon|\le C/(\rho|\log\varepsilon|)$. Set $f_\varepsilon=f_*\zeta_\varepsilon$ and use (87.20) to define $\psi_\varepsilon$. Each is in $\mathcal E_2$ and has punctured-core approximants. For a difference $F=f_\varepsilon-f_{\varepsilon'}$ write $d=\max(\varepsilon,\varepsilon')$, small enough that $\chi=1$ on its support. Equation (87.7) gives

$$
\mathfrak t[F]\le C\bigl(|\log\varepsilon|^{-1}+|\log\varepsilon'|^{-1}\bigr),
\quad |F|\le C/\rho,\quad |\nabla F|\le C/\rho^2,
\quad \operatorname{supp}F\subset\{\rho\le d\}.
\tag{87.21}
$$

These differences are real and radial in $\xi$, so the two magnetic cross terms cancel. The actual form identity for their scaled states is

$$
q_c[\psi_F]=a\mathfrak t[F]
 +\frac a{4\kappa^2}\int r_\perp^2|\partial_tF|^2d\xi dt
 +g_c\left(\frac{J[F]}{4\pi\kappa}-V[\psi_F]\right).
\tag{87.22}
$$

All terms here are finite for each cutoff difference. The magnetic integral is $O(d^2)$. To bound the signed last difference, use the actual homogeneous bound $\mathcal G(\xi,s)\le C(r^4+s^2)^{-3/4}$. For any fixed $0<\alpha<1/2$ it implies

$$
\int|s|^\alpha\mathcal G(\xi,s)ds\le C_\alpha r^{2\alpha-1}.
\tag{87.23}
$$

The power follows by $s=r^2v$; the tail integral converges precisely for $\alpha<1/2$. The bounds in (87.21) give, uniformly in the cutoffs,

$$
\bigl||F(\xi,0)|^2-|F(\xi,s/\kappa)|^2\bigr|
 \le C_\kappa r^{-2}\min\{|s|/r,1\}.
\tag{87.24}
$$

For $|s|\le\kappa r$ this is the central derivative bound for $|F|^2$; beyond that range its two values are each bounded by $C/r^2$. The expression vanishes for $r>d$. Use the actual marginal for the trace term and $\min(u,1)\le u^\alpha$ in (87.23)--(87.24). Integration in $\xi$ then gives

$$
\left|\frac{J[F]}{4\pi\kappa}-V[\psi_F]\right|
 \le C_{\kappa,\alpha}\int_0^d r^{\alpha-1}dr
 \le C'_{\kappa,\alpha}d^\alpha.
\tag{87.25}
$$

Thus $q_c[\psi_\varepsilon-\psi_{\varepsilon'}]\to0$, and the states converge in $L^2$ to (87.20). Approximating each cutoff in $\mathcal E_2$ also in the $q_c+\|\cdot\|_2^2$ norm produces a genuine Friedrichs core sequence. Its limit proves $\psi_*\in\mathcal Q_c\setminus\mathcal E_2$. This uses a controlled same-field error, not identification of $\Gamma$ with a delta interface.

The zero-kernel assertion requires a separate whole-closure argument. Define on all of $L^2(G)$ the nonlinear map

$$
\mathcal M_{a,\eta}\psi(\xi,t)=\kappa^{1/2}U(\xi,\kappa t),\qquad
U=\mathcal F_s^{-1}|b_\psi|.
\tag{87.26}
$$

Shear, Fourier transformation and this scaling are unitary, while $||b|-|c||\le|b-c|$. Hence $\|\mathcal M\psi\|_2=\|\psi\|_2$ and $\|\mathcal M\psi-\mathcal M\phi\|_2\le\|\psi-\phi\|_2$. The actual comparison (87.11), before its strict scalar optimization, gives on $\mathcal D_0$

$$
q_c[\psi]\ge a\mathfrak t[\mathcal M\psi],\qquad
\mathcal M\psi\in H^1\subset\mathcal Q_\delta.
\tag{87.27}
$$

Indeed $A[\mathcal M\psi]=A[U]$, $C[\mathcal M\psi]=\kappa^2D_2$, $J[\mathcal M\psi]=\kappa J[U]$, and $g_c/(4\pi)=4a\kappa/\pi$. Take a core form approximating sequence $\psi_n\to\psi\in\mathcal Q_c$. Its $q_c$ values tend to $\overline q_c[\psi]$, and $\mathcal M\psi_n\to\mathcal M\psi$ in $L^2$. A nonnegative closed form, extended by $+\infty$ outside its domain, is lower semicontinuous in $L^2$; this follows also by weak compactness in its graph Hilbert space for a bounded-energy subsequence. Therefore

$$
\mathcal M\psi\in\mathcal Q_\delta,\qquad
\overline q_c[\psi]\ge a\mathfrak t[\mathcal M\psi]
 =a\int\Phi^2|\nabla(\mathcal M\psi/\Phi)|^2.
\tag{87.28}
$$

No estimate for $\mathfrak t[\mathcal M\psi_n-\mathcal M\psi_m]$ is used or inferred. If the left side is zero, (87.9) gives $\mathcal M\psi=0$, and norm preservation gives $\psi=0$. The form representation $\overline q_c[\psi]=\|H_F^{1/2}\psi\|_2^2$ identifies its zero set with $\ker H_F$. The remainder in (87.28) is strictly positive for every nonzero $\psi\in\mathcal Q_c$; it is generally a nonlinear functional, not a quadratic form or a uniform multiple of $\|\psi\|_2^2$.

Finally normalized outward Carnot dilates of any core state have energy $aR^{-2}T+\eta R^{-4}D_2-gR^{-3}V\to0$. Subcritical strict positivity and (87.19) show nonattainment. At critical coupling $0\in\sigma(H_F)\setminus\sigma_p(H_F)$. The auxiliary $\Phi$ is not thereby an original-field resonance: (87.26) is nonlinear and (87.28) is only a comparison, with no inverse operator equivalence. $\square$

**Theorem 87.5 (higher-order added laws and the full weighted compactness condition).** Fix $\sigma>2$ and $a,g,\eta>0$. The added-law form $q_{\sigma,\eta}$ is closed and semibounded on exactly $\mathcal E_\sigma$. Put $p=2/\sigma\in(0,1)$ and $K=g^2/(256a)$. Then

$$
q_{\sigma,\eta}[\psi]\ge
 -(1-p)K\left(\frac{pK}{\eta}\right)^{p/(1-p)}\|\psi\|_2^2.
\tag{87.29}
$$

The embedding $\mathcal E_\sigma\to L^2(G,\Gamma d\mu)$ is compact. If the normalized infimum $I_{\sigma,\eta}<0$, it is attained by a normalized form state, an eigenvector of the represented operator with eigenvalue $I_{\sigma,\eta}$. Always $I_{\sigma,\eta}\le0$; negativity at every positive coupling, a sharp value of this infimum, and attainment when it is zero are not supplied by this theorem.

Proof. Let $N=\|\psi\|_2^2$ and $S=aT+\eta D_\sigma$. From (87.4), $gV\le C S^{1/2+1/\sigma}N^{1/2-1/\sigma}$ with $C=g/(8\sqrt a\,\eta^{1/\sigma})$. The exponent of $S$ is strictly less than one, so Young's inequality gives $gV\le\epsilon S+C_\epsilon N$ for every $\epsilon>0$. The free intersection form is closed and dense by Definition 87.1. KLMN, as in Theorem 85.3, therefore applies with relative bound zero, on this exact domain. To obtain the displayed finite constant, first complete the scalar square in $\sqrt T$:

$$
q_{\sigma,\eta}\ge\eta D_\sigma-KD_\sigma^pN^{1-p}.
\tag{87.30}
$$

For $N>0$ minimize $\eta d-Kd^p$ over $d=D_\sigma/N\ge0$. Its minimizer is $d=(pK/\eta)^{1/(1-p)}$, giving (87.29); the zero state is immediate. This bound does not assert simultaneous equality in the scalar and spectral interpolation steps.

Full weighted compactness needs the central tail in addition to the finite-band result (85.26). The actual complementary state obeys

$$
\begin{aligned}
T[(I-P_\Lambda)\psi]&\le T[\psi],\
D_2[(I-P_\Lambda)\psi]&\le\Lambda^{2-\sigma}D_\sigma[\psi],\
V[(I-P_\Lambda)\psi]&\le\frac18\Lambda^{1-\sigma/2}
 \sqrt{T[\psi]D_\sigma[\psi]}.
\end{aligned}
\tag{87.31}
$$

The first line uses the genuine strong free reduction; the second follows by $|\lambda|^2\le\Lambda^{2-\sigma}|\lambda|^\sigma$ outside the band; the third is the whole-domain endpoint estimate. Thus the weighted norm of the tail tends uniformly to zero on every bounded $\mathcal E_\sigma$ set. For each fixed band its images are bounded in $\mathcal F_\Lambda$, whose actual full-field weighted embedding is compact by (85.26), including both the source puncture and the central/exterior tails. A diagonal band subsequence and (87.31), applied to differences, give weighted Cauchy convergence for the unprojected states. Local $L^2$ identification, or testing on compact boxes away from $e$, identifies the weighted limit with the weak $\mathcal E_\sigma$ limit. This proves the asserted compactness, rather than just compactness of a selected band.

An infimizing normalized sequence has bounded $T+D_\sigma$ by the relative bound with $\epsilon<1$. Pass to a weak form limit $\psi$, use weighted compactness for $V$ and lower semicontinuity for the two nonnegative kinetic terms. If $I=I_{\sigma,\eta}<0$ and $m=\|\psi\|_2^2\le1$, the same mass argument as (85.29) gives $I\ge q_{\sigma,\eta}[\psi]\ge Im\ge I$. Thus $m=1$ and the infimum is attained; form variation and representation give the eigenvector. Outward Carnot dilation has $D_\sigma[U_R\psi]=R^{-2\sigma}D_\sigma[\psi]$ and energy tending to zero, proving $I\le0$. A fixed core trial proves negativity when $g>(aT+\eta D_\sigma)/V$ for that trial, but establishes no all-coupling alternative. $\square$

**Theorem 87.6 (exact original-law budget floor and same-state noncompactness).** For every $a,g>0$ and $B>0$,

$$
I_{2,B}:=\inf_{\psi\in\mathcal B_{2,B}}q_0[\psi]
 =-\frac{g^2B}{256a},
\tag{87.32}
$$

and this infimum is not attained anywhere in $\mathcal E_2$. There are normalized actual $\psi_j\in\mathcal D_0$ with $D_2[\psi_j]=B$ exactly and

$$
T[\psi_j]\longrightarrow\frac{g^2B}{256a^2},\qquad
V[\psi_j]\longrightarrow\frac{gB}{128a},\qquad
q_0[\psi_j]\longrightarrow I_{2,B}.
\tag{87.33}
$$

They can be chosen weakly convergent to zero, with these nonzero kinetic and potential limits carried by a spike whose $L^2$ mass tends to zero. Hence the weighted embedding on $\mathcal E_2$ is not compact, and the fixed-budget negative floor supplies no normalized lowest state.

Proof. By (87.3), every normalized state with $D_2\le B$ satisfies

$$
q_0[\psi]>aT[\psi]-\frac g8\sqrt{BT[\psi]}
 \ge-\frac{g^2B}{256a}.
\tag{87.34}
$$

This proves the lower bound and whole-domain nonattainment, including states with $D_2<B$.

For the matching upper bound choose the single profiles (87.13) with $h=g/(16a)$, and let $u_{\varepsilon,j}$ be (87.14). Independently choose a normalized fixed $b\in\mathcal D_0$. Expand it by the Carnot dilation $U_L$ and translate only its $z$ coordinate by $L^2$, obtaining $b_L$. If the original $z$ support is in $[-C_b,C_b]$, then

$$
\operatorname{supp}_zb_L\subset L^2+[-C_bL,C_bL],\quad
T[b_L]=L^{-2}T[b],\quad d_L:=D_2[b_L]=L^{-4}D_2[b],\quad V[b_L]\longrightarrow0.
\tag{87.35}
$$

The last limit uses $|z|\ge L^2/2$ on the support for large $L$ and $\Gamma\le CN^{-3}$, giving $V[b_L]\le C'L^{-6}$. These are actual translations and derivatives, not a replacement of the potential by a translation-invariant field.

For fixed $j$, choose $\varepsilon$ small so $C_j\varepsilon^{-2}>B$, then $L$ large so $d_L<B$ and the two horizontal $z$ supports are disjoint. Define one actual state by

$$
\theta_{\varepsilon,j,L}=
 \frac{B-d_L}{C_j\varepsilon^{-2}-d_L}\in(0,1),\qquad
\psi_{\varepsilon,j,L}=
 \sqrt{\theta_{\varepsilon,j,L}}u_{\varepsilon,j}
 +\sqrt{1-\theta_{\varepsilon,j,L}}b_L.
\tag{87.36}
$$

Disjoint horizontal supports make the norm, $T$ and $V$ cross terms zero. They also make central derivative cross terms zero: the central operator, even at fractional orders, acts only in $s$ and preserves horizontal support. Thus the state has norm one and $D_2=B$ exactly, lies in $\mathcal D_0$, and its other integrals are the corresponding weighted sums. For fixed $j$, (87.15), with $\varepsilon\downarrow0$ and $L\to\infty$, gives

$$
\theta\sim\frac{B\varepsilon^2}{C_j}\to0,\qquad
T[\psi]\to\frac{BA_j}{C_j}=\frac{g^2B}{256a^2},\qquad
V[\psi]\to\frac{BJ_j}{4\pi C_j}.
\tag{87.37}
$$

The last limit tends, as $j\to\infty$, to $gB/(128a)$ by (87.13). A legal diagonal is explicit: select the profile $j$ first, then $\varepsilon_j<1/j$ so its dominated-convergence and derivative errors, after multiplication by $B\varepsilon_j^2/C_j$, are less than $1/j$ and its spike mass is less than $1/j$; only then select $L_j>j$ so the background errors, budget correction and support separation have the same accuracy. Increase $L_j$ if necessary to keep its support outside $|z|\le j$. This proves (87.33) on a single normalized exact-budget sequence, rather than on separate optimizers.

The spike's norm tends to zero while $b_{L_j}$ escapes every compact $z$ set, so $\psi_j\rightharpoonup0$. Equations (87.33) give bounded $\mathcal E_2$ norm and a strictly positive limiting weighted norm. A strongly convergent weighted subsequence would have zero limit on every compact set away from $e$, by weak $L^2$ convergence and the local boundedness of $\Gamma$; exhaustion would make its limit zero everywhere. This contradicts the nonzero limit of $V$. Thus weighted compactness fails at this endpoint. The energy in the vanishing mass spike is not discarded as a small norm perturbation. $\square$

**Theorem 87.7 (lower-order exact-budget collapse and the safe higher-order boundary).** For every $0<\sigma<2$, $B>0$ and $a,g,\eta>0$ there are normalized actual $\psi_n\in\mathcal D_0$ with $D_\sigma[\psi_n]=B$ and

$$
q_0[\psi_n]\longrightarrow-\infty,\qquad
q_{\sigma,\eta}[\psi_n]=q_0[\psi_n]+\eta B\longrightarrow-\infty.
\tag{87.38}
$$

Consequently neither law has a finite floor on this fixed positive budget at lower orders. For every $\sigma>2$, the unchanged-law budget instead has the safe bound

$$
q_0[\psi]\ge-\frac{g^2B^{2/\sigma}}{256a},
 \qquad \psi\in\mathcal B_{\sigma,B}.
\tag{87.39}
$$

Its sharp value and attainment are not asserted. For every finite $\sigma>0$, mere finiteness of $D_\sigma$ leaves the original $q_0$ unbounded below, even on normalized $\mathcal D_0$.

Proof. Choose a real normalized smooth compact central $h$ with $h(0)\ne0$. The Coulomb intermediate (84.11), or its exponential minimizer followed by smooth punctured approximation, supplies a real normalized $u\in C_c^\infty(\mathbb R^3\setminus\{0\})$ with

$$
a\|\nabla u\|_2^2-
 \frac{g|h(0)|^2}{4\pi}\int\frac{|u|^2}{r}d\xi<0.
\tag{87.40}
$$

For example horizontal expansion of any fixed such nonzero test makes the negative $r^{-1}$ term dominate its $r^{-2}$ kinetic term. Let $f(\xi,t)=u(\xi)h(t)$, $A=A[f]$, $J=J[f]$ and $C_\sigma=\||D_t|^{\sigma/2}f\|_2^2>0$. The actual state (87.14) for this fixed profile has $D_\sigma=C_\sigma\varepsilon^{-\sigma}$ and

$$
q_0[u_\varepsilon]=\varepsilon^{-2}
 \left(aA-\frac{gJ}{4\pi}+o(1)\right),
\qquad aA-gJ/(4\pi)<0.
\tag{87.41}
$$

Use the same horizontally disjoint $b_L$ as in (87.35), now with $d_L=D_\sigma[b_L]=L^{-2\sigma}D_\sigma[b]$, and replace $C_j\varepsilon^{-2}$ in (87.36) by $C_\sigma\varepsilon^{-\sigma}$. Exact orthogonality for the actual fractional central operator proves norm one and exact $D_\sigma=B$. With $\varepsilon\downarrow0$ and then a sufficiently large $L=L(\varepsilon)$, its spike mass is asymptotic to $B\varepsilon^\sigma/C_\sigma$, the background energy tends to zero, and

$$
q_0[\psi_\varepsilon]
 \sim\frac{B}{C_\sigma}\left(aA-\frac{gJ}{4\pi}\right)
 \varepsilon^{\sigma-2}\longrightarrow-\infty.
\tag{87.42}
$$

The error in (87.41) is small relative to the fixed strictly negative coefficient; no quantitative convergence rate is assumed. The background choice follows the fixed profile and concentration choice, and enforces actual disjoint $z$ supports, so no nonlocal central cross term has been omitted. Adding $\eta B$ proves the second law's collapse on the same sequence. All trials are punctured compact tests, with finite actual potential and central moments.

For higher-order fixed budgets apply (87.4) with norm one and $D_\sigma\le B$, then minimize $aT-(g/8)B^{1/\sigma}\sqrt T$. This proves (87.39) without a matching upper construction. It is not the added-law result (87.29), and the compactness proof for minimizing an added law does not prove attainment under this safe scalar floor.

Finally a fixed normalized core state $v$ has $T[v],V[v]>0$ and finite $D_\sigma[v]$ for every finite $\sigma$. Its inward Carnot dilates have

$$
q_0[U_rv]=ar^{-2}T[v]-gr^{-3}V[v]\to-\infty,
\qquad D_\sigma[U_rv]=r^{-2\sigma}D_\sigma[v]<\infty
 \quad\text{for each }r>0.
\tag{87.43}
$$

There is no common budget here. This proves precisely the mere-finiteness assertion; it does not contradict any fixed-budget bound. $\square$

**Proposition 87.8 (regularity and budgets do not recover the conditional interaction).** For every finite $\sigma>0$ and $B>0$, the reader $\mathscr R$ of Theorem 82.5, even supplemented with $D_\sigma$ and $B$, does not determine $V$, $q_0$ or $q_{\sigma,\eta}$ on $\mathcal B_{\sigma,B}$.

Proof. Take a normalized compact smooth product $u(\xi)h(w)$ with the horizontal support in $r>\delta>0$. Expand its central factor enough that $D_\sigma\le B$. It lies in the actual horizontal domain by $X_2(uh)=(\partial_yu)h+xuh'$, and in the weighted domain by (85.13). Central translates preserve norm, every $X_i$, $T$, $D_\sigma$, the marginal and all projected free heat observations. The field is positive, so the untranslated $V$ is positive; its value on translates tends to zero by the actual field's decay and boundedness on $r>\delta$. Dominated convergence against this compact product proves distinct values at some finite translation. Both kinetic laws therefore retain the same reader defect. This concerns the free projected reader, not an interacting evolution invariance. $\square$

**Definition 87.9 (mathematical correspondence and remaining realization conditions).** The trace ingredient (87.5) and the profile (87.6) correspond to AFV's $n=4,\beta=2$ halfspace problem, not a formula for $\Gamma$. Fourier inversion, Plancherel, spectral interpolation, weak modulus differentiation and closed-form lower semicontinuity are mature ingredients. The actual free Fourier fibres and band compactness are (85.7) and (85.26); both the full-frequency tail (87.31) and the same-field dominated convergence (87.18) are necessary clients. KLMN and form representation are the supplies used in Theorem 85.3, with Teschl's [primary text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorem 6.24 and Theorem 2.13. The Friedrichs construction is applied only after core nonnegativity, not to the collapsing original form. The actual Green, its marginal, positivity and homogeneous bounds retain Proposition 82.4's correspondence to Folland's [1975 paper](https://doi.org/10.1007/BF02386204), Theorem 3.1 and Proposition 3.17 at $\alpha=2$. No H-type closed Green formula, Euclidean inverse-square potential or marginal multiplier replaces that field.

The same-field sharpness, cutoff error, critical-domain transfer, joint exact-budget constructions and their stated limits are source-specific deductions from these ingredients. Their literature correspondence is bounded to these supplies and §§82–86; it makes no exhaustive overlap, priority or originality assertion. The critical comparison proves neither $\mathcal Q_c=\mathcal M^{-1}(\mathcal Q_\delta)$ nor a full asymptotic description of its singular elements. It does exclude $L^2$ zero modes in the actual Friedrichs domain, while leaving the original-field non-$L^2$ threshold problem separate. Higher-order safe budget constants are not sharp-value or attainment statements; the higher-order added-law attainment result requires a strictly negative infimum.

A source application must separately provide maps preserving the original source and immutable INITIAL, same-source chronology, authentic Read/refusal/Stop behavior, the carrier, state, field, Haar measure, horizontal metric, boundary and clock conventions. State and budget acquisition, preparation, observation, copying, retention, permissions, resources and costs remain separate conditions. An analytic derivative or budget premise does not supply those operations or a source-to-state realization, and the reader still needs the actual conditional interaction statistic (82.16). The added kinetic term defines a different mathematical law; a fixed budget restricts the original law; finiteness alone supplies neither change. None of these analytic contracts identifies a native invariant interacting sector or a physical space dimension.

## 78.99 追加锚（本行以下为增补区）

## 88. Terminal overlap is a source-side persistence certificate

The latest DEV terminal-overlap synthesis gives a terminating result for a
recognized class of acquired signed inputs. Its cofinality sentence is useful
for the present geometry question, but it has to be kept at its actual level:
it certifies persistence of common finite prefixes of source outputs. It does
not by itself define a metric carrier, a propagation clock, or a spatial
dimension.

**Definition 88.1 (recognized source-overlap datum).** Let \(I\) be a complete
acquired input and let \(B\) be a finite set of distinct attained complete
target rows. Let \(J_B(h)\) be the joint finite-prefix predicate for the same
source contract at depth \(h\). Call \((I,B)\) terminal-recognized when every
source-cover chart tuple either has a finite constructor clash or passes the
terminal comparison test of the DEV synthesis.

For a nonclash tuple and one scalar-divergence face \(K\), write
\(\mathcal C_K\) for its exact joint cofinal support sentence. The sentence
holds only after all finite scalar anchors and forced finite residuals have
been fixed; its lower bounds are then imposed simultaneously on every
divergent original scalar.

**Theorem 88.2 (source-side persistence certificate).** For a
terminal-recognized \((I,B)\), exactly one of the following alternatives is
returned by the finite procedure:

1. Some face has \(\mathcal C_K\) true. The procedure then constructs, for
   every requested \(h\), actual finite originals in every row of \(B\) whose
   complete outputs share one prefix of depth \(h\).
2. Every face has \(\mathcal C_K\) false. The procedure then returns a finite
   \(H\) with \(\neg J_B(H)\).

This is a source-level theorem. The first alternative says that the acquired
contract admits fresh finite witnesses at every requested depth; the second
says that this selected joint set is separated at a finite depth. Neither
alternative supplies a metric realization or a physical signal law.

**Proof.** The complete mixed covers are finite, and terminal recognition
reduces each nonclash tuple to finitely many scalar faces. The DEV cofinal
support theorem is necessary and sufficient for one fixed tuple to have
witnesses at all depths. If one face is true, its finite-prefix lifting
constructs the required sources at each requested depth. If all faces are
false, each chart tuple fails at some finite depth; the maximum of those
finitely many failures excludes the whole finite cover. The fixed-depth
source query then finds the first exclusion depth. The construction retains
the complete old row, all signed endpoint conditions, repeated occurrences,
and the common-source contract throughout. \(\square\)

The theorem improves the boundary calculation in a precise way. It replaces
an unproved phrase such as “the two rows remain indistinguishable forever” by
one of two finite certificates: a uniform construction parameterized by the
requested depth, or a finite separating depth. It does not turn source rank
into radius.

**Definition 88.3 (cofinal source rank).** In a true face \(\mathcal C_K\),
call \(K\) the escaping source set. Its cofinality is the statement

$$
\forall b\in\mathbb N\ \exists \mathbf v\quad
\Phi_K(\mathbf t,\mathbf q,\mathbf v)\ \land\
\bigwedge_{i\in K}v_i\ge b,
$$

with the finite anchors \(\mathbf t,\mathbf q\) fixed before the lower-bound
request. Thus all coordinates in \(K\) escape jointly in source-index space.

**Proposition 88.4 (cofinality is not metric escape).** Source cofinality
does not imply that a corresponding geometric realization escapes to
infinite distance.

**Proof.** Let \(n\in\mathbb N\) be a cofinal source index. The maps

$$
\chi_1(n)=(n,0,\ldots,0)\in\mathbb R^d,\qquad
\chi_2(n)=(2^{-n},0,\ldots,0)\in\mathbb R^d
$$

are both injective source placements. The first has unbounded distance from
the origin, while the second has a finite accumulation point. Replacing the
second by
\(\chi_3(n)=(\sin(\theta n),\cos(\theta n),0,\ldots,0)\), with
\(\theta/(2\pi)\) irrational, gives an injective bounded placement as well.
The source predicate, its cofinality sentence, and every \(J_B(h)\) value are
unchanged because none of these definitions contains \(\chi_i\) or a metric.
Therefore cofinal source rank alone cannot establish properness, radial
escape, or a physical infinite boundary. \(\square\)

The counterexample is deliberately elementary. It identifies the missing
bridge rather than denying that a useful bridge may exist for FIB. A native
transport could rule out the bounded placements, but that requires a theorem
about the transport and its metric compatibility.

**Definition 88.5 (source-to-geometry bridge).** A bridge for a source
family consists of a carrier \((X,d,\mu)\), a source-state map
\(\chi:D\to X\), and an explicit response map satisfying all of the following
where they are needed:

* source actions and same-register forward updates map to declared local
  transports on \(X\);
* prefix depth is related to a declared observation scale \(r(h)\), with
  both directions of the implication needed by the target task;
* escaping source coordinates are proper in the relevant sector, for example
  \(v_i\to\infty\Rightarrow d(o,\chi(u_{\mathbf v}))\to\infty\);
* the carrier has a measure and local operator whose volume, heat, or Green
  estimates are proved at that scale;
* the acquired clock, boundary, and interaction readouts are the same
  objects used in the claimed propagation or energy statement.

A source-cover result supplies none of these clauses unless they are included
as additional hypotheses or proved from the native operations.

**Theorem 88.6 (conditional composition with the stability window).**
Suppose a terminal-recognized source family admits a source-to-geometry
bridge whose coarse carrier has volume exponent \(d\), whose field operator
has homogeneous order \(\sigma\), and whose localizing operator has order
\(\tau\). Suppose further that the Green and variational hypotheses of the
stability analysis hold on that same carrier. Then the scale competition has
a finite strict minimum only in the window

$$
\sigma<d<\sigma+\tau.
$$

For the ordinary second-order field and second-order localization contract,
\(\sigma=\tau=2\), so the integer window is \(d=3\).

**Proof.** Under the bridge, a point response has homogeneous order
\(d-\sigma\), while localization has order \(\tau\). At scale \(R\) the
two terms therefore have the form

$$
AR^{-\tau}-BR^{-(d-\sigma)},\qquad A,B>0.
$$

The strict finite-scale minimum criterion is
\(0<d-\sigma<\tau\), which is exactly the displayed window. The
terminal-overlap certificate is used only to establish the source family and
its finite-prefix persistence; the analytic lower bound, attainment, and
transport compatibility remain separate bridge obligations. \(\square\)

**Proposition 88.7 (no reverse inference from persistent overlap).** A true
\(\mathcal C_K\), even for every finite target-row set \(B\) considered by the
acquisition, does not imply \(d=3\), the existence of a second-order field,
or the existence of a stable negative-energy state.

**Proof.** The same source datum can be placed on a line, a planar lattice,
or a four-dimensional lattice while leaving all source rows, signed records,
prefix replies, and cofinal support sentences unchanged. The differing
carriers have different volume growth and Green kernels. The analytic
stability conclusion therefore cannot be recovered from the source predicate
alone. Theorem 88.6 becomes applicable only after one of these placements is
selected by a proved bridge and its operator estimates are established. \(\square\)

This separates two kinds of persistence that had previously been easy to
conflate:

| persistence statement | what it certifies | what it does not certify |
| --- | --- | --- |
| \(\mathcal C_K\) true | fresh finite source witnesses at every requested prefix depth | metric properness or a dimension |
| source rank escapes every bound | a necessary unbounded parameter in the chosen source chart | unbounded physical radius |
| bridge plus Green estimates | a carrier-level propagation and stability model | that the bridge is native to FIB unless proved |
| \(\sigma<d<\sigma+\tau\) | a conditional scale window in the declared analytic model | a source-to-physics realization |

The next concrete proof obligation is therefore not another list of
three-dimensional properties. It is to construct, or refute, a native bridge
from the FIB legal transport and acquired clock to a carrier with a proved
volume exponent and local operator. Terminal overlap can certify that the
source family persists through arbitrary finite observation depth; it cannot
choose the carrier on which that persistence propagates.

## 88.99 追加锚（本行以下为增补区）

## 89. Cubic capacity and recurrent propagation on the complete finite atomic orbit

**Definition 89.1 (one source orbit and its declared comparison geometry).**
Use the free ordered source and forward substitution of the base volume,
Definition 1.1, equivalently [Process44, Definition 44.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
Fix INITIAL to be the actual one-leaf tree $\alpha$, and put

$$
T_n=\rho^n(\alpha),\qquad
h_n=(\underbrace{\rho,\ldots,\rho}_{n\text{ forward updates}}),\qquad
s_n=(\mathrm{INITIAL}=\alpha,h_n,\mathrm{current}=T_n),
\quad n\in\mathbb N_0.
\tag{89.1}
$$

Every $h_n$ is a finite legal history in that contract. It has one current
register, no graft, no Read and no Stop yet. Any chosen finite prefix may be
stopped under the original contract; no later update is appended to a stopped
history. Each $T_n$ retains its entire ordered labelled tree, including every
bracket and occurrence. The collection $\mathcal S=\{s_n:n\in\mathbb N_0\}$
is a mathematical family of finite snapshots of the same forward lineage,
not an acquired simultaneous archive and not a source after an infinite
execution. Retaining, reconstructing or comparing these snapshots as actual
records would require its own acquisition and retention contract. No such
operation is needed to define this family.

Take the carrier to be an identical copy $X=\{x_n:n\in\mathbb N_0\}$ of
these complete states, with $\chi(s_n)=x_n$. Thus $\chi$ has singleton
fibres and does not identify states with equal direction, composition,
prefix reply or leaf position. Declare

$$
d(x_m,x_n)=|m-n|^{1/3},\qquad
\mu(\{x_n\})=1,\qquad
F(x_n)=x_{n+1}=\chi(s_{n+1}).
\tag{89.2}
$$

The exponent in this metric is a supplied scale choice. It is not inferred
from a three-component readout. The standard operation $d_0\mapsto d_0^a$,
$0<a\le1$, is snowflaking; its metric property is stated in
Naor–Neiman, [*Assouad's theorem with dimension independent of the snowflaking*,
Introduction, p. 1](https://arxiv.org/pdf/1012.2307v1).
Only that elementary metric construction is used here, not an embedding
theorem or an assertion about an ambient Euclidean dimension. The measure in
(89.2) counts complete source states, not leaves of $T_n$, spatial sites of
an apparatus or quotient multiplicities. Balls are closed:
$B_d(x,R)=\{y:d(x,y)\le R\}$. A strict $\varepsilon$-packing consists of
points with pairwise distance greater than $\varepsilon$.

Supply one comparison operator on $\ell^2(X,\mu)$, with unit conductance
on each adjacent pair:

$$
\begin{aligned}
(Lu)_0&=u_0-u_1,\\
(Lu)_n&=2u_n-u_{n-1}-u_{n+1}\quad(n\ge1),\\
\mathcal E(u)&=\langle u,Lu\rangle
 =\sum_{n\ge0}|u_{n+1}-u_n|^2,\qquad P=I-L/2,\\
(Pu)_0&=(u_0+u_1)/2,\qquad
(Pu)_n=(u_{n-1}+u_{n+1})/2\quad(n\ge1).
\end{aligned}
\tag{89.3}
$$

Here $u_n=u(x_n)$. The propagation clock is one unit per application of
$P$; the normalization $L=2(I-P)$ is fixed throughout. The root boundary
is reflecting, with holding probability $1/2$ at $x_0$; there is no killing
at infinity and no screening term. The local energy of a set $A$ is
$\mathcal E_A(u)=\sum_{x_n,x_{n+1}\in A}|u_{n+1}-u_n|^2$.
All nonholding transitions have declared metric length one. The reverse
comparison transition $x_{n+1}\to x_n$ is not a native source action:
Process44's source contract supplies forward $\rho$, not an inverse update,
a reset or a copied old current register. Equation (89.3) is an additional
analytic law on the state carrier; it does not grant those operations.

For $N\in\mathbb N_0$, let $D_N=\{x_0,\ldots,x_N\}$ and define $L_N^D$
by restricting this same $L$ with zero exterior value at $x_{N+1}$.
The superscript distinguishes this outer Dirichlet killing from the
unchanged reflecting root. In particular

$$
\mathcal E_N^D(u)
 =\sum_{n=0}^{N-1}|u_{n+1}-u_n|^2+|u_N|^2,
\qquad P_N^D=I-L_N^D/2.
\tag{89.4}
$$

The empty sum applies when $N=0$. This is a killed restriction of the
declared propagation, not a new finite reflecting propagation. Its field
Green is $G_N=(L_N^D)^{-1}$, and the nonnegative unscreened occupation
Green of the infinite comparison law is the extended-valued kernel

$$
G(x,y)=\frac12\sum_{j=0}^{\infty}P^j(x,y).
\tag{89.5}
$$

The factor $1/2$ matches $L=2(I-P)$ and the counting measure. No subtraction
of a recurrent constant, pseudoinverse, finite-time truncation or screened
inverse is meant by (89.5).

**Theorem 89.2 (source-matched cubic-capacity counterexample).** For the
single datum (89.1)–(89.5), the trees $T_n$ are pairwise distinct finite
actual source terms, $\chi$ is injective, the carrier is proper, and its
original forward transport $F$ is an isometry with unit displacements.
The comparison law is reversible for the declared counting measure and
has uniformly local unit edges. Nevertheless the following capacity,
energy and Green statements coexist.

For every $k\in\mathbb N_0$, $R\ge0$ and $\varepsilon>0$, set
$q=\lfloor R^3\rfloor$, $a=\max(0,k-q)$, $b=k+q$ and
$h=\lfloor\varepsilon^3\rfloor+1$. Then

$$
\begin{aligned}
B_d(x_k,R)&=\{x_a,\ldots,x_b\},\\
\mu(B_d(x_k,R))&=q+\min(k,q)+1,\\
\operatorname{Pack}_{>\varepsilon}(B_d(x_k,R))
 &=\left\lfloor\frac{q+\min(k,q)}{h}\right\rfloor+1.
\end{aligned}
\tag{89.6}
$$

In particular the two-sided cubic bounds, uniformly in the centre, are

$$
\begin{aligned}
R^3&\le\mu(B_d(x_k,R))\le3R^3&& (R\ge1),\\
\frac12(R/\varepsilon)^3
 &\le\operatorname{Pack}_{>\varepsilon}(B_d(x_k,R))
 \le3(R/\varepsilon)^3&& (R\ge\varepsilon\ge1).
\end{aligned}
\tag{89.7}
$$

For $N\ge1$, put $R_N=N^{1/3}$, so that $D_N=B_d(x_0,R_N)$.
If $C_N$ is the best reflecting-ball Poincaré constant defined by

$$
C_N=\sup_{u\text{ nonconstant on }D_N}
\frac{\sum_{n=0}^N|u_n-\bar u_{D_N}|^2}
     {\mathcal E_{D_N}(u)},\qquad
\bar u_{D_N}=\frac1{N+1}\sum_{n=0}^N u_n,
\tag{89.8}
$$

then

$$
\frac{(N+1)(N+2)}{12}\le C_N\le\frac{N^2}{2}.
\tag{89.9}
$$

Thus $C_N$ is of order $R_N^6$, not $R_N^2$. More strongly, for every
fixed $\lambda\ge1$ and every finite $C\ge0$, the quadratic inequality

$$
\sum_{x\in B_d(x_0,R)}|u(x)-\bar u_{B_d(x_0,R)}|^2
 \le C R^2\mathcal E_{B_d(x_0,\lambda R)}(u)
\tag{89.10}
$$

fails for some $R\ge1$ and finitely supported real $u$.
The same assertion holds with the larger full energy $\mathcal E(u)$ on
the right. Quantitatively the witnesses below give a quotient at least
$R_N^4/24$ for every $N\ge1$, even against that full energy.

For the same operator, measure, clock and specified boundaries, the killed
root field and the mean exit time are exactly

$$
\begin{aligned}
G_N(x_0,x_n)&=N+1-n &&(0\le n\le N),\\
\mathbb E_{x_n}\tau_N
 &=(N+1)(N+2)-n(n+1)&& (0\le n\le N),
\end{aligned}
\tag{89.11}
$$

where $\tau_N$ is the first arrival at $x_{N+1}$ in the unit $P$ clock.
Consequently $\mathbb E_{x_0}\tau_N$ is of order $R_N^6$ and

$$
G(x_0,x_0)=\infty.
\tag{89.12}
$$

The comparison propagation is recurrent, and there is no finite
nonnegative root-source solution $g$ of $Lg=1_{\{x_0\}}$ on $X$.
In particular these cubic-capacity and locality hypotheses do not supply
a finite nonnegative unscreened three-dimensional second-order root
Green for the same datum.

**Proof.** Finiteness of every $T_n$ follows from the finite tree
substitution. Distinctness does not use a direction readout. Writing
$c(t)=(A,B)$, the source formula $c(\rho t)=(B,A+B)$ gives

$$
(2,3)c(\rho t)-(2,3)c(t)=A+2B>0
\tag{89.13}
$$

for every nonempty tree. This is the strict forward source quantity of
Process44, Theorem 44.6. It separates all $T_n$, while (89.1) also retains
their original history and INITIAL. The calculation is a proof of source
distinctness, not a free CountRead. It changes none of the legal source
actions.

The usual snowflake triangle inequality here follows directly from
$|i-k|\le|i-j|+|j-k|$ and
$(v+w)^{1/3}\le v^{1/3}+w^{1/3}$ for $v,w\ge0$. This is the elementary
metric tool credited in Definition 89.1. Formula (89.2) also gives
$d(Fx_i,Fx_j)=d(x_i,x_j)$ and $d(x_n,Fx_n)=1$. Its ball condition is
$|n-k|\le R^3$, giving the first two equalities of (89.6). Every bounded
set is contained in a finite ball, and every closed bounded set is compact;
hence the carrier is proper. In particular the source rank escapes every
bounded metric ball.

For a strict packing, successive ordered indices must differ by at least
$h$: the condition is $|i-j|>\varepsilon^3$, including when
$\varepsilon^3$ is an integer. If there are $M$ points in the interval
$[a,b]$, its span gives $(M-1)h\le b-a$. Conversely
$a,a+h,\ldots,a+\lfloor(b-a)/h\rfloor h$ attains this bound.
This proves the packing equality. For $R\ge1$,
$q+1\ge R^3$ and $2q+1\le3R^3$. For $\varepsilon\ge1$,
$\varepsilon^3<h\le2\varepsilon^3$, while
$q+1\le b-a+1\le2R^3+1$. Since

$$
\left\lfloor\frac{b-a}{h}\right\rfloor+1
 =\left\lceil\frac{b-a+1}{h}\right\rceil,
\tag{89.14}
$$

the lower bound in (89.7) follows from $(b-a+1)/h$; the upper follows
from $(b-a)/h+1\le2(R/\varepsilon)^3+1$ and $R\ge\varepsilon$.
For $0<\varepsilon<1$, every distinct carrier point is separated and the
exact packing is instead the ball cardinality. Thus (89.7) is a coarse
capacity statement on its displayed scale domain, not a continuum
three-dimensional small-scale measure law.

The matrix of $P$ in (89.3) is symmetric and stochastic, including the
root row. Counting measure is therefore reversible. Jensen's inequality
and its column sums make $P$ a contraction on $\ell^2(X,\mu)$; thus
$L=2(I-P)$ is bounded self-adjoint and nonnegative on that entire space.
Its energy identity follows by summing the edge differences, first on
finite support and then by $\ell^2$ approximation. No metric or measure
is changed in this calculation.

For the finite ball, the standard path finite-difference estimate is an
intermediate energy calculation. The variance identity and Cauchy–Schwarz
along its actual adjacent chain give

$$
\begin{aligned}
\sum_{n=0}^N|u_n-\bar u_{D_N}|^2
 &=\frac1{N+1}\sum_{0\le i<j\le N}|u_j-u_i|^2,\\
|u_j-u_i|^2
 &\le(j-i)\sum_{n=i}^{j-1}|u_{n+1}-u_n|^2
 \le N\mathcal E_{D_N}(u).
\end{aligned}
\tag{89.15}
$$

There are $N(N+1)/2$ pairs, proving the upper bound in (89.9).
For $u_n=n$ on $D_N$, the mean is $N/2$, the energy is $N$, and

$$
\sum_{n=0}^N(n-N/2)^2=\frac{N(N+1)(N+2)}{12}.
\tag{89.16}
$$

This proves the lower bound. To keep (89.10) inside the common full
operator domain, use the finitely supported test

$$
u^{(N)}_n=
\begin{cases}
n,&0\le n\le N,\\
2N-n,&N<n\le2N,\\
0,&n>2N.
\end{cases}
\qquad \mathcal E(u^{(N)})=2N.
\tag{89.17}
$$

It has the same ball variance (89.16). For every $\lambda\ge1$,
$\mathcal E_{B_d(x_0,\lambda R_N)}(u^{(N)})\le2N$, so

$$
\frac{\sum_{D_N}|u^{(N)}-\bar u^{(N)}_{D_N}|^2}
     {R_N^2\mathcal E(u^{(N)})}
 =\frac{(N+1)(N+2)}{24N^{2/3}}
 \ge\frac{R_N^4}{24}\longrightarrow\infty.
\tag{89.18}
$$

This also disproves (89.10) with its local energy and any fixed dilation.
The finite-difference method and the network interpretation of edge energy
are standard tools, not additional general theorems claimed here; the latter
is recorded in Lyons–Peres, [*Probability on Trees and Networks*,
Chapter 2, §§2.1–2.3](https://rdlyons.pages.iu.edu/prbtree/book_online.pdf).

For the Green calculation, (89.4) is strictly positive on every nonzero
finite vector: zero energy forces all entries equal and $u_N=0$.
The candidate $g^{(N)}_n=N+1-n$, with $g^{(N)}_{N+1}=0$, satisfies

$$
(L_N^Dg^{(N)})_0=1,\qquad
(L_N^Dg^{(N)})_n=0\quad(1\le n\le N).
\tag{89.19}
$$

It is the unique killed root field. This is the unit-resistance path
calculation; the classical Green-as-voltage relation and series law are
credited to Lyons–Peres, Proposition 2.1 and §2.3. The direct equation
(89.19) fixes the reflecting-root and counting-measure normalization
needed for this source datum.

From any state of $D_N$, taking forward steps reaches $x_{N+1}$ within
$N+1$ steps with probability at least $2^{-(N+1)}$. Applying this bound
in successive blocks shows that $P_N^D$ is absorbed almost surely, has
finite mean absorption time, and its matrix powers tend to zero
geometrically. Therefore

$$
G_N=\frac12\sum_{j\ge0}(P_N^D)^j.
\tag{89.20}
$$

Each killed path is an allowed comparison path of $P$, so its return
probability is bounded by the corresponding infinite-chain probability.
The nonnegative sum (89.5) hence dominates $G_N(x_0,x_0)=N+1$ for
every $N$, proving (89.12). Infinite expected return occupation is the
standard recurrence criterion for this irreducible chain. Equivalently,
for an excursion from $x_1$, the probability of reaching $x_{N+1}$ before
$x_0$ is $1/(N+1)$, by the harmonic function $n/(N+1)$ on that finite
interval. A path that avoids $x_0$ cannot stay in a fixed finite interval
forever, by the same block argument. Letting $N\to\infty$ makes its
escape probability zero, giving recurrence directly. Holding at the root
does not alter this conclusion.

The first-step equations for the finite mean exit time $v_n$ are
$v_0-v_1=2$ and $2v_n-v_{n-1}-v_{n+1}=2$ for $1\le n\le N$, with
$v_{N+1}=0$. The unique solution is
$v_n=(N+1)(N+2)-n(n+1)$, proving the second line of (89.11) in exactly
the declared unit clock. Finally, if a finite nonnegative root field on
the infinite carrier solved $Lg=1_{\{x_0\}}$, its root equation would
give $g_1=g_0-1$ and every subsequent second difference would vanish.
Thus $g_n=g_0-n$, contradicting nonnegativity for $n>g_0$.
All three tests use the same $L$, $P$, $d$, $\mu$ and root boundary.
$\square$

**Definition 89.3 (scale and operator tests for a proposed source bridge).**
For a declared source-to-carrier map, specify the legal forward relation,
the carrier metric and measure, the propagation $P$, its energy operator
$L$ and normalization, the propagation clock, and both root and exterior
boundaries before taking any scale limit. Two distinct calibration tests
for a quadratic propagation claim are a radius-independent Poincaré bound
of the form (89.10), on the claimed centres and scale range, and a
radius-independent mean-exit bound

$$
\mathbb E_x\tau_{B_d(x,R)}\le C_{\mathrm{exit}}R^2.
\tag{89.21}
$$

The exit time in (89.21) is measured in that declared propagation clock.
If the proposed claim includes a nonnegative unscreened root response,
its Green test concerns (89.5) for that same operator, measure and
boundary. These tests specify particular mathematical obligations; their
sufficiency for a three-dimensional Green estimate is not assumed.
They are distinct from the acquisition of any metric or energy readout
and from the native or physical implementation of the propagation.

**Proposition 89.4 (the diagnosed calibration defect and its scope).**
On the complete finite orbit of Definition 89.1, the shortest adjacent
comparison-chain length and the number of forward native updates from
$s_m$ to $s_n$, for $m\le n$, both equal

$$
\ell(x_m,x_n)=n-m=d(x_m,x_n)^3.
\tag{89.22}
$$

The ratio of this length to $d$ is unbounded. Properness, forward metric
escape, isometric unit transport, reversible unit conductances and the
two-sided cubic capacity (89.7) therefore do not imply either calibration
test of Definition 89.3 or finiteness of its unscreened root response.
The defect occurs without forgetting any source state in a quotient.
The conditional assertions in the base §9 and in §§81, 82 and 88 retain
their original hypotheses.

**Proof.** An adjacent chain must change its index by one at every
nonholding step, so the monotone chain attains the shortest length
$|n-m|$. Each native $\rho$ advances the index by exactly one, and
distinctness in (89.13) prevents any shorter forward word from reaching
$T_n$. This proves (89.22), and for $m=0$ the ratio is $n^{2/3}$.
Although the two distances agree on every unit edge, their long-range
scales differ. The path's energy and unit-clock exit scale are quadratic
in $\ell$ and hence sixth order in this supplied $d$. Equations
(89.18), (89.11) and (89.12) prove the three failures directly; naming a
missing condition does not prove its repair.

The base §9 uses smooth three-dimensional comparison surfaces, an induced
Euclidean metric and a calibration form. None is supplied by (89.2).
Section 81's whole-rho occurrence tree and its separate §52 common
spine carrier are different from the present carrier of complete
successive source states; no factor map or replacement of their
operators is asserted. Section 82 assumes a stratified transport group
and its horizontal field, not (89.3). The carrier and analytic hypotheses
of Theorem 88.6 include an operator order and Green estimates on that
same carrier. The present choice proves that cubic packing and proper
source escape do not discharge those additional hypotheses; it does not
refute their conditional consequence or turn source rank into physical
radius.

The source identity in (89.1) is exact, but a native bridge to the
comparison operator would additionally have to realize its reverse
transitions and its clock under the actual permission contract. Neither
the metric nor the counting measure grants that realization. A physical
interpretation would further need a map from complete source states to
spatial positions, with its joint field, measure, acquisition, boundary
and clock correspondences. A different metric, rate law, measure,
screening or boundary would be a different datum requiring its own
analysis. The counterexample excludes the stated inference within this
comparison class; it proves neither impossibility of a native bridge nor
a physical dimension assignment. $\square$

## 89.99 追加锚（本行以下为增补区）

## 90. Actual source quotients and two incompatible source scales

This appendix compares complete finite sources in the acquired fiber of
[ARH, Proposition 23.2](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md).
Its serial metric uses the full event list of
[NativeFullSourceProducer](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.md),
including local actions. The source, the canonical cut row and a numerical
observation are different objects. All conclusions below are ordinary
mathematics; no new Lean validation or physical realization is asserted.

### 90.1. The entire retained-input fiber and its distinct targets

**Definition 90.1 (unchanged acquired input).** Let $\mathcal T$ be the nonempty
finite free ordered trees generated by $\alpha,\beta$ and pairing, with

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

An address is a finite word in $L,R$, rooted at $\varepsilon$. The original
reply $r_u(p)$ is $\alpha,\beta,\mathsf{branch}$ or $\mathsf{absent}$.
Fix any common certified $N\ge2$. Retain exactly the CE input
$I=(P,(C,\pi),H_0,H_{\rm rel},Q,N)$, where

$$
\begin{aligned}
P&=\{LL,LR,R\},&
C&=\langle\langle\square_1,\square_2\rangle,\square_3\rangle,&
\pi&=\{\{1\},\{2\},\{3\}\},\\
H_0&=((0,RLR,\alpha),(0,RRR,\beta)),\\
H_{\rm rel}&=((1,LL,0,RLL,=),(2,LR,0,RRL,=),\\
&\hspace{14mm}(0,LL,2,LR,\ne),(0,LR,1,LL,\ne),(1,LL,2,LR,\ne)),\\
Q&=\{LL,LR,RLL,RLR,RRL,RRR\}.
\end{aligned}
\tag{90.1}
$$

Here a relation requires both endpoints to be reached at their stated epochs
and compares their entire ordered subtrees. The complete retained state
recovers $I$ and factors through $I$ and common parameters, under ARH
Assumption 1.3. Every accessible source-bearing acquisition field is subject
to that access cut. No source size, label, traversal length or original-tree
archive is added to $I$.

**Proposition 90.2 (full fiber and native target).** The entire original-source
fiber of (90.1), without a restriction on size or shape, is

$$
\begin{aligned}
\mathcal D_{\rm CE}&=\{u(x,y):x,y\in\mathcal T,\ D(x,y)\},\\
u(x,y)&=\langle\langle x,y\rangle,
 \langle\langle\rho(x),\alpha\rangle,\langle\rho^2(y),\beta\rangle\rangle\rangle,\\
D(x,y)&\iff x\ne y\ \land\ x\ne\rho^2(y)\ \land\ y\ne\rho(x)
 \ \land\ \rho(x)\ne\rho^2(y).
\end{aligned}
\tag{90.2}
$$

The native $R_Q(u)$ is the reached original holes, their whole concrete
numbered-hole exterior, and the complete equality partition of their whole
subtrees. All six holes are reached on (90.2), with exterior

$$
C_Q=\langle\langle\square_1,\square_2\rangle,
 \langle\langle\square_3,\square_4\rangle,
             \langle\square_5,\square_6\rangle\rangle\rangle.
\tag{90.3}
$$

Apart from identities and their transitive consequences, the partition is
generated by

$$
\begin{array}{c|c}
\text{source condition}&\text{equal hole ordinals}\\ \hline
x=\alpha&1=4,\ 3=6\\
x=\beta&1=6\\
y=\alpha&2=4\\
y=\beta&2=6.
\end{array}
\tag{90.4}
$$

The separately named **complete subtree valuation** is the stronger target

$$
V_Q(u(x,y))=(x,y,\rho(x),\alpha,\rho^2(y),\beta).
\tag{90.5}
$$

It determines $R_Q$ and is injective on $\mathcal D_{\rm CE}$; $R_Q$ is not
asserted to determine (90.5) or the source.

Proof. This is the exact source correspondence of ARH Proposition 23.2,
with its guards retained. To check both directions, write the old three
class values as $x,y,z$. The literals force
$z=\langle\langle a,\alpha\rangle,\langle b,\beta\rangle\rangle$.
The reached positive endpoints force $a=\rho(x),b=\rho^2(y)$; the three
negative records give the last three inequalities of $D$. The remaining
old-class condition is $x\ne y$. The other two old inequalities follow from

$$
\ell(z)=\ell(\rho(x))+\ell(\rho^2(y))+2>\ell(x),\ell(y),
$$

where $\ell$ counts leaf occurrences. Every finite pair satisfying $D$
conversely satisfies the old row, both literals and all five guarded
relations. Thus (90.2) is the complete fiber, not just a family of witnesses.

Cutting at $Q$ gives (90.3) and the six values (90.5). For the partition,
the four values $x,y,\rho(x),\rho^2(y)$ are pairwise distinct: four pairs
are guarded by $D$, and $x\ne\rho(x),y\ne\rho^2(y)$ follow from the clock
$\kappa(\rho^j t)=\kappa(t)+j$ in ARH.4.2. No positive image is $\alpha$;
$\rho(t)=\beta$ holds exactly for $t=\alpha$; no second image is $\beta$.
These facts follow directly from the three constructors of $\rho$. They
leave exactly (90.4), exhausting all fifteen unordered comparisons.
The first two entries of (90.5) reconstruct (90.2), proving its injectivity.
The row omits those values. This agrees with
[ActualCutPartitionDecoder.canonicalRow_record_iff](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean),
whose record contains the exterior and partition, with no source value,
size or acquisition trace. $\square$

**Definition 90.3 (the three-component observation).** Use precisely the
$q$ port of [Process Geometry, Definition 44.1](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md):
in the fixed oriented Euclidean space $\mathbb R^3$, put

$$
a=e_1=(1,0,0),\quad b=e_2=(0,1,0),\qquad
q(\alpha)=a,\quad q(\beta)=b,\quad
q(\langle s,t\rangle)=q(s)\times q(t).
\tag{90.6}
$$

The observation here is the ordered triple
$(q_1(u),q_2(u),q_3(u))$ of the **entire original source** in that fixed
basis. It is not $V_Q$, a tuple of subtree observations, the composition
port $c$, the joint port $\eta=(c,q)$ or a spatial position. Evaluating this
mathematical function supplies no numerical read permission or free acquisition.

### 90.2. Unbounded finite source families and their actual quotients

**Definition 90.4 (test sources).** For $h\ge1$, let
$L_h=\{L,R\}^h$, $m=2^h$, and $\omega:L_h\to\{0,1\}$.
The perfect height-$h$ tree $X_{h,\omega}$ has branches above depth $h$
and leaf $\alpha$ or $\beta$ at $p$ according as $\omega(p)=0$ or $1$.
Set

$$
B_0=\alpha,\quad B_{j+1}=\langle B_j,B_j\rangle,\quad
Y_h=B_{h+3},\quad \nu_{h,\omega}=u(X_{h,\omega},Y_h),\quad
\mathcal F_h=\{\nu_{h,\omega}:\omega\in\{0,1\}^{L_h}\}.
\tag{90.7}
$$

These are tested subfamilies of the entire domain (90.2). The retained $I$
does not include $h$ or the promise of membership in $\mathcal F_h$.

**Proposition 90.5 (identity survives while both actual observations collapse).**
For every $h\ge1$ and every labelling, $\nu_{h,\omega}\in\mathcal D_{\rm CE}$.
The map $\omega\mapsto\nu_{h,\omega}$ is injective,
$|\mathcal F_h|=2^m$, and the families have no finite bound on cardinality.
On their union the native row is the single row with reached set $Q$,
exterior $C_Q$ and six singleton classes; $q(\nu_{h,\omega})=(0,0,0)$.
The complete subtree valuation remains injective, also across different $h$.
Consequently, on each $\mathcal F_h$, the source and $V_Q$ equality quotients
have $2^m$ classes, while the $R_Q$, $q$ and joint $(R_Q,q)$ quotients each
have one class.

Proof. The right-spine clock is
$\kappa(\alpha)=0,\kappa(\beta)=1,
\kappa(\langle s,t\rangle)=2+\kappa(t)$ (ARH.4.2).
It gives $\kappa(X)\in\{2h,2h+1\}$, $\kappa(Y)=2h+6$, and hence

$$
\kappa(X)<\kappa(\rho X)<\kappa(Y)<\kappa(\rho^2Y).
\tag{90.8}
$$

All four CE inequalities hold. The construction and Proposition 90.2 retain
every old-class, literal and reached-endpoint guard, not just these clocks.
Different labellings differ at an actual $LLp$ leaf; $X$ has exactly height
$h$, so different heights cannot coincide either. There are $m$ independent
binary labels and therefore $2^m$ different sources.

Both $X,Y$ are branches. So are $\rho X,\rho^2Y$; their mutual
inequalities are already established. None equals either constant leaf,
and $\alpha\ne\beta$. Thus (90.4) gives six singleton classes at every
height. For $j\ge1$, $q(B_j)=0$, since $a\times a=0$ at the first pairing
and $0\times0=0$ thereafter. In particular $q(Y)=0$, whence
$q(\langle X,Y\rangle)=q(X)\times0=0$ and $q(\nu)=0$.
Injectivity of $V_Q$ follows from its first entry and the source formula.
This proves all the quotient assertions. $\square$

The row collapse holds on this family, not on all of $\mathcal D_{\rm CE}$.
For example, $y=\langle\alpha,\alpha\rangle$ and either $x=\alpha$ or
$x=\beta$ satisfy $D$ but have different partitions in (90.4). On the full
domain ARH Proposition 23.2 supplies a static at-most-two-read service:
at the actual $\rho^N u$ it reads $LLR^{\lceil N/2\rceil}$ and
$LRR^{\lceil N/2\rceil}$, decodes the original root cases of $x,y$, and
outputs (90.3)--(90.4). On the promised union of (90.7), the constant row
can instead be output with zero new raw reads. Neither task identifies $\omega$.

### 90.3. Address depth and its source-specific packing obstruction

**Definition 90.6 (full-source address scale).** For distinct $u,v$ in
$\mathcal F_h$, put

$$
\delta_A(u,v)=\min\{|p|:r_u(p)\ne r_v(p)\}=h+2,
\qquad
 d^A_h(u,v)=s_h>0,\qquad d^A_h(u,u)=0.
\tag{90.9}
$$

Here $s_h$ is any independently chosen positive scale. In particular it
may be $a_h2^{-(h+2)}$ with any $a_h>0$. To verify the stated minimum,
$X$ first varies at $LLp$, of full address length $h+2$. Above that depth
all of $X$ has its fixed branch shape. Its other occurrence is inside
$\rho X$ at prefix $RLL$, whose first varying replies occur at depth
$h+3$: a changed $X$ leaf becomes $\beta$ versus a branch under $\rho$.
All other source subtrees are fixed at this $h$. Thus original prefixes
through depth $h+1$ coincide and the minimum is exactly $h+2$.
The resulting equilateral $d^A_h$ is an ultrametric on this actual family.

**Proposition 90.7 (uniform finite-dimensional exclusion).** Fix an integer
$k\ge1$ and $0<c\le C<\infty$. No family of maps
$\Phi_h:\mathcal F_h\to\mathbb R^k$ satisfies simultaneously for all
$h\ge1$ and all pairs

$$
 c\,d^A_h(u,v)\le\|\Phi_h(u)-\Phi_h(v)\|_2\le C\,d^A_h(u,v).
\tag{90.10}
$$

This holds for every independent choice of the $s_h$. More quantitatively,
any such constants on a single $\mathcal F_h$ must satisfy

$$
2^m\le(1+2C/c)^k,
\qquad C/c\ge\tfrac12(2^{m/k}-1).
\tag{90.11}
$$

Proof. Fix one image point. All $2^m$ images lie within radius $Cs_h$
of it; the open balls of radius $cs_h/2$ about the images are disjoint.
Their union lies within radius $(C+c/2)s_h$ of that point. Euclidean
volume scales as the $k$th power of radius, giving (90.11). The scale
cancels and the cardinality tends to infinity. This is the classical
disjoint-ball estimate applied after the actual fiber construction and
its quotient calculation; it does not turn source cardinality into
physical dimension. $\square$

In particular $k=3$ has no uniform distortion constants here, just as
any other fixed finite $k$ does. The source configurations being compared
are not spatial points. A finite cutoff or a changed metric changes a
premise; no minimal coding dimension is asserted.

### 90.4. The actual full-event prefix scale and a bounded-coordinate code

**Definition 90.8 (sourcewise chronology).** Write $T_a(t)$ for the exact
$\operatorname{productionTrace}\ a\ t$. With read tokens carrying epoch,
physical address and reply, and $\mathsf{Local}$ the real local-step token,
its recursion is

$$
\begin{aligned}
T_a(\alpha)&=[\mathsf{Read}(0,a,\alpha)],&
T_a(\beta)&=[\mathsf{Read}(0,a,\beta)],\\
T_a(\langle s,t\rangle)&=[\mathsf{Read}(0,a,\mathsf{branch})]
 \mathbin{+\!+}T_{aL}(s)\mathbin{+\!+}[\mathsf{Local}]
 \mathbin{+\!+}T_{aR}(t)\mathbin{+\!+}[\mathsf{Local}],\\
E_{h,\omega}&=T_\varepsilon(\nu_{h,\omega}).
\end{aligned}
\tag{90.12}
$$

The run starts at the common $\mathsf{Visit}(\varepsilon,[])$ control,
epoch zero, empty prior trace and the source-specific register
$\nu_{h,\omega}$. It ends at $\mathsf{Deliver}(\nu_{h,\omega},[])$, whose
instruction is $\mathsf{Stop}(\nu_{h,\omega})$. Native Stop is terminal:
it is not an additional event in $E$ and has no outgoing native step.
The complete chronology object here is $(E,\mathsf{Stop}(\nu))$.
No original address, local step or terminal control is discarded.

Order $L_h$ lexicographically as $p_1,\ldots,p_m$, the actual preorder
of its leaf occurrences. Let $e_h(j)$ be the one-based full-event index
of leaf $p_j$ in the perfect $X$ subtree's own trace. The index is
independent of the labels. It is specified for all $j$ by

$$
\begin{aligned}
e_0(1)&=1,\\
e_{r+1}(j)&=
 \begin{cases}
 1+e_r(j),&1\le j\le2^r,\\
 4\cdot2^r-1+e_r(j-2^r),&2^r<j\le2^{r+1},
 \end{cases}\\
n_h(j)&=2+e_h(j).
\end{aligned}
\tag{90.13}
$$

For distinct sources in $\mathcal F_h$, put

$$
j(u,v)=\min\{j:\omega(p_j)\ne\omega'(p_j)\},\qquad
 n(u,v)=n_h(j(u,v)),\qquad
 d^E_h(u,v)=3^{-n(u,v)},\quad d^E_h(u,u)=0.
\tag{90.14}
$$

Thus the exponent is an actual **full-event** index, including preceding
branch reads and local actions, not the rank in a filtered reply list.

**Proposition 90.9 (exact index correspondence and code).** For every $h$
and pair of labellings, the first unequal full event of their chronologies
is exactly the read at $LLp_{j(u,v)}$, at index $n(u,v)$ in (90.14).
The extrema of the selected leaf indices are

$$
n_h(1)=h+3,\qquad n_h(m)=4m-h-1.
\tag{90.15}
$$

The full-event prefix metric is an ultrametric, and the code

$$
Z^E_h(\nu_{h,\omega})=\sum_{j=1}^{m}2\omega(p_j)3^{-n_h(j)}\in[0,1)
\tag{90.16}
$$

satisfies, uniformly in $h$,

$$
 d^E_h(u,v)\le|Z^E_h(u)-Z^E_h(v)|\le3d^E_h(u,v).
\tag{90.17}
$$

At fixed known $h$, it is an injective one-coordinate representation of
the entire source and hence of its complete event list and terminal Stop.
This is a mathematical encoding on (90.7), not a new native output port.

Proof. A full binary tree with $M$ leaves has $2M-1$ node reads and
$2(M-1)$ local actions under (90.12), hence $4M-3$ full events. The left
half of a perfect tree therefore contributes $4\cdot2^r-3$ events.
Adding the parent read and the switch gives exactly (90.13). Two ancestor
reads, at $\varepsilon$ and $L$, precede the $X$ trace, giving its global
shift of two. The first leaf of $X$ follows $h$ branch reads; the last
leaf is followed by exactly $h$ combinations. These give (90.15).

Before the first differently labelled $X$ leaf, all visited replies,
addresses, epochs, switches and combinations in (90.12) agree. The rest
of the original source has not yet been visited except for the two
common ancestors. At the stated leaf the replies are $\alpha$ versus
$\beta$. This proves the actual first-event claim for every labelling,
even when later transformed subtrees and total trace lengths differ.
The usual common-prefix inequality for three binary label words and
the increasing $n_h(j)$ proves the ultrametric inequality for (90.14).

For $n=n(u,v)$, the leading summand in the code difference has magnitude
$2\cdot3^{-n}$. All later selected indices are distinct integers greater
than $n$, so the absolute tail is bounded by
$\sum_{r>n}2\cdot3^{-r}=3^{-n}$. This proves (90.17).
Also the finite sum in (90.16) is less than
$\sum_{r\ge1}2\cdot3^{-r}=1$. Injectivity follows from its positive lower
bound. Recover the finite ternary digits at the known indices, then
$X$, then (90.2), then (90.12) and its terminal output. This proves
complete representation on the declared source domain without inventing
a free acquisition, copying operation or execution after Stop. $\square$

For comparison only, the selected-leaf projection has metric
$d^P_h(u,v)=3^{-j(u,v)}$ and code
$Z^P_h(u)=\sum_{j=1}^m2\omega(p_j)3^{-j}$, with the same bounds $1,3$.
Its exponent omits intervening events. At the first and last selected
leaves its indices are $1,m$, whereas the full-event indices are
(90.15). The projection is not the full-event metric used in (90.17).

**Proposition 90.10 (non-correspondence under independent rescaling).**
There are no constants $0<c\le C<\infty$ and positive factors
$a_h,b_h$ such that, for every $h$ and every pair in $\mathcal F_h$,

$$
c\,a_hd^A_h(u,v)\le b_hd^E_h(u,v)\le C\,a_hd^A_h(u,v).
\tag{90.18}
$$

Proof. Compare two sources differing only at $p_1$, and two differing
only at $p_m$. Both address distances are $s_h$. Their full-event
distances have ratio

$$
\frac{3^{-(h+3)}}{3^{-(4m-h-1)}}=3^{4m-2h-4}\longrightarrow\infty.
\tag{90.19}
$$

Equation (90.18) would bound this ratio by $C/c$, independently of both
scale factors. This is impossible. Thus an exact bounded-coordinate
serial code and the address-depth packing obstruction coexist on the
same sources; the missing implication is metric correspondence.
The projected metric also fails to correspond uniformly to $d^E_h$:
its endpoint ratio is $3^{m-1}$, so the ratio of the full-event endpoint
ratio to that projected ratio is $3^{3m-2h-3}$, unbounded. Independent
per-$h$ rescaling cannot remove this discrepancy either. $\square$

### 90.5. Exact producer resources and representation-relative precision

**Proposition 90.11 (resources of this producer on all the test sources).**
Let $t=|\{p\in L_h:\omega(p)=1\}|$. For precisely the run (90.12),

$$
\begin{aligned}
\ell(\nu_{h,\omega})&=26m+t+2,\\
\#\mathsf{Read}(E)&=52m+2t+3,\\
\#\text{leaf replies}(E)&=26m+t+2,\\
\#\mathsf{Local}(E)&=52m+2t+2,\\
|E|&=104m+4t+5,\\
\operatorname{ht}(\nu_{h,\omega})&=h+7,
\qquad \max\#\text{stack frames}=h+7.
\end{aligned}
\tag{90.20}
$$

There are no absent replies or updates. The terminal acquired tree has
$52m+2t+3$ node occurrences. These are counts for the declared symbolic
tree, trace and frame-list representations, not machine-byte or physical
space lower bounds for arbitrary algorithms.

Proof. The six $Q$ subtrees contribute respectively
$m,8m,m+t,1,16m,1$ leaves. In $\rho X$ each original alpha supplies one
leaf and each beta two. Each of the $8m$ alpha leaves of $Y$ supplies two
leaves in $\rho^2Y$. This proves the first and third formulas. A full
binary tree with $L$ leaves has $L-1$ branches and $2L-1$ nodes;
(90.12) reads each node once and adds two locals per branch, proving all
trace counts. Stop itself is not counted in $|E|$.

The depths of $X,Y,\rho X,\alpha,\rho^2Y,\beta$ beneath their hole
addresses give global heights $h+2,h+5,\le h+4,3,h+7,3$.
In particular $\rho^2\alpha=\langle\beta,\alpha\rangle$ makes the
fifth height exactly $h+7$. In sourceControl, visiting a child adds one
frame for its parent; switching left to right replaces that frame;
combining removes it. Induction along the traversal makes stack length
at a visit equal the address depth. Every intervening delivery has the
frames for its ancestors. The maximum is therefore exactly the maximum
leaf depth $h+7$. The stopped control carries the complete acquired tree
by the producer contract. All statements are sourcewise and apply to
every labelling. $\square$

**Proposition 90.12 (finite codebook separation and sufficient resolution).**
At fixed $h$, the exact minimum separations of (90.16) and of the named
projection code are

$$
\Delta_E=2\cdot3^{-(4m-h-1)},\qquad \Delta_P=2\cdot3^{-m}.
\tag{90.21}
$$

For $p\in\mathbb N_0$ and $z\in[0,1)$ specify the uniform binary quantizer
$Q_p(z)=\lfloor2^pz\rfloor$, with exactly $2^p$ possible labels.
A sufficient resolution for injectivity on either codebook is

$$
2^{-p}\le\Delta_E\quad\hbox{or, respectively,}\quad2^{-p}\le\Delta_P.
\tag{90.22}
$$

These are sufficient conditions, not necessary conditions for this
finite codebook and this alignment of bins. The necessary cardinality
condition for any injective $p$-bit output on $\mathcal F_h$ is only
$p\ge m$; no stronger necessary precision bound is inferred here.

Proof. For selected exponents $n_1<\cdots<n_m$ and first difference at
$n_j$, bounding the tail by all integer positions through $n_m$ gives

$$
\left|\sum_l2(\omega_l-\omega'_l)3^{-n_l}\right|
\ge 2\cdot3^{-n_j}-\sum_{r=n_j+1}^{n_m}2\cdot3^{-r}
=3^{-n_j}+3^{-n_m}\ge2\cdot3^{-n_m}.
$$

Equality is attained by changing only the last bit. Use (90.15) for
$Z^E$ and $n_j=j$ for $Z^P$ to get (90.21). Two points in one half-open
quantizer bin are separated by strictly less than its width $2^{-p}$;
(90.22) thus suffices. Necessity of $p\ge m$ follows instead from
$2^p\ge|\mathcal F_h|=2^m$ and uses no metric or bin-width argument.
For example, at $h=1$ the projected codebook is
$0,2/9,2/3,8/9$; $Q_3$ gives $0,1,5,7$. Thus an alleged necessary
$p>m\log_2 3$ would already fail on this codebook. $\square$

A sharp cardinality representation exists for every $h$: with $h$ known,

$$
W_h(\nu_{h,\omega})=\sum_{j=1}^m\omega(p_j)2^{-j},\qquad
Q_m(W_h)=\sum_{j=1}^m\omega(p_j)2^{m-j}.
\tag{90.23}
$$

The integer on the right ranges bijectively over $0,\ldots,2^m-1$;
its $m$-bit expansion reconstructs the entire source by (90.7).
Its finite codebook separation is $2^{-m}$. This proves sufficiency of
$m$ bits for identity at fixed $h$, without preserving either specified
metric with uniform distortion. For $d^A$ this follows from Proposition
90.7 with $k=1$. For $d^E$, the two endpoint-bit changes have $W_h$ distance
ratio $2^{m-1}$, while their event-distance ratio is (90.19). The quotient
$2^{m-1}/3^{4m-2h-4}$ tends to zero, excluding uniform multiplicative
constants even after per-$h$ rescaling. Knowing $h$ in this representation task
is an explicit side input, not an extra field of the CE retained $I$.
The radix separations (90.21) tend to zero. A single exact real coordinate
therefore supplies no uniform positive separation for these codebooks;
Proposition 90.13 also excludes a fixed-bit exact source output across all
$h$. The acquired-tree and trace counts remain those of (90.20).

### 90.6. Task, input access and the handoff boundary

**Proposition 90.13 (what source counting does and does not force).** Fix
$h$. A finite-valued code from which a deterministic decoder recovers the
source or $V_Q$ on $\mathcal F_h$, using only that code and common
parameters, has at least $2^m$ code values. If those values are stored
as a fixed $p$-bit word, then $p\ge m$. The same holds for a retained
state that is the decoder's sole source-bearing input. For the $R_Q$,
$q$ or $(R_Q,q)$ task on this family, one output value suffices.

Proof. If two different sources gave the same code or sole retained
state, the decoder would return the same answer for them. Source
identity and (90.5) distinguish them, so the map must be injective.
Proposition 90.5 counts its domain and proves that each of the three
other tasks is constant. This argument counts output or sole-state
values; it asserts no lower bound on working memory when other input
access, streamed output or externally retained data is allowed. $\square$

A consumer independently supplied the already acquired original tree
can compute $V_Q$, $R_Q$ or an encoding locally with **zero additional raw
reads**. A consumer independently supplied (90.12) can decode the original
labelled tree from its preorder reads and then do the same, again with
zero new raw reads. These are different input contracts from receiving
only $I$. Their acquisition and retention costs are not refunded. Even
for raw acquisition, on the separately promised epoch-zero $\mathcal F_h$
with known $h$, the $m$ reads at $LLp_1,\ldots,LLp_m$ suffice to reconstruct
$X$ and then the whole source (90.7). Consequently the producer's
$52m+2t+3$ reads, its frame-stack bound and the radix-specific sufficient
precision in (90.22) cannot be transferred to arbitrary source consumers.

The mathematical epoch-zero producer comparison is separate from the
actual CE handoff. NativeFullSourceProducer has the same initialControl
in every run, but each immutable register is initialized to its own
$\nu_{h,\omega}$ and remains at that source and epoch zero. It terminates
with the acquired tree and complete trace at an absorbing Stop. Its theorem
supplies neither entry into a later task nor a post-Stop handoff right.

ARH Proposition 2.1 and Proposition 23.2 supply a different paid
acquisition contract: acquire original descriptions and the specified
literals, execute real updates on the same register, acquire the required
epoch-one and epoch-two endpoint descriptions, compare them while retained,
reach the common certified $N$, then impose the complete access cut.
The resulting accessible state has exactly fiber (90.2) and the physical
register is $\rho^N u$. The original descriptions and traversal are no
longer accessible. The sourcewise function $u\mapsto E(u)$ is not an
archive inside that state, and its coding theorem is not an instruction
to rerun an epoch-zero producer there. Neither source continuity nor
certified $N$ gives a reset, inverse, clone, source identity port or
old-version access. Alternative mathematical sources in the family are
not live modifications of one register.

### 90.7. Combined result, sources and remaining bridge

**Theorem 90.14 (source-fiber scale contrast with faithful task quotients).**
For the full CE fiber (90.2) there are finite subfamilies $\mathcal F_h$
of unbounded cardinality, all with the same acquired $I$, the same native
$Q$-row and the same three-component $q$ observation. Complete source
identity and the stronger $V_Q$ distinguish all their members. On these
same subfamilies, the full-source address metric has no uniformly bounded
distortion into any fixed finite-dimensional Euclidean space, even with
independent scale choices. The actual full-event prefix metric has the
uniform bounded-coordinate code (90.16)--(90.17), but it cannot correspond
to address depth under independent per-scale rescaling. Its producer costs,
representation precision and sole-state capacity have exactly the scopes
in Propositions 90.11--90.13. In particular no whole-row memory lower bound
follows from this family.

Proof. Proposition 90.2 establishes the unchanged entire input and target.
Proposition 90.5 gives the actual source counts and all stated quotients;
Proposition 90.7 applies packing to these source identities. Propositions
90.9--90.10 use the real first unequal event to prove both the code and
the non-correspondence. Propositions 90.11--90.13 prove the separately
qualified cost and information conclusions. The access distinction in
§90.6 prevents substituting an acquired full source for the CE retained
input or treating sourcewise initialization as a post-cut reset. $\square$

The repository overlap is bounded to the unchanged contracts used here:
ARH Definitions 1.1--1.2, Assumption 1.3, ARH.4.2 and Proposition 23.2;
[FFM Definitions 1.2--1.3 and §§6, 9](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_FRAME_MEMORY.md)
for full-row versus complete-field tasks and access-qualified memory;
Process Geometry Definition 44.1 for the specific $q$ port;
[NativeFullSourceProducer.sourceControl, productionTrace and native_source_producer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean)
for the exact program and chronology; and
[NativeSerialMachine.nativeStep](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean)
for terminal Stop and the retained event types. These source definitions,
and ActualCutPartitionDecoder's canonical-row equivalence, are consumed
with their existing targets. Earlier occurrence-space packing in §81 and
atomic-orbit metrics in §89 do not identify the present source-fiber
quotient or the first-event indices (90.13).

The disjoint-ball volume bound is a mature intermediate (J. Matoušek,
[*Lectures on Discrete Geometry*](https://doi.org/10.1007/978-1-4613-0039-7)).
Finite prefix coding and fixed-length output counting are mature
intermediates (T. M. Cover and J. A. Thomas,
[*Elements of Information Theory*](https://doi.org/10.1002/047174882X)).
Their elementary forms used here are proved above. The source-specific
combined result is repository-derived: these ingredients are applied
after the full CE guards, actual target quotients and native event
positions are established. This bounded source comparison makes no
exhaustive literature or global originality claim.

A source-to-space conclusion still requires a separately supplied map
with its task, metric, measure, lawful operations, operator domain, clock
and resource correspondence. Neither $q\in\mathbb R^3$, the radix code,
the absence of uniform address-metric distortion, nor the complete-source
producer supplies that bridge. No physical space dimension, minimal
coding dimension, native operator transport or physical clock transport
is inferred; the §52/§55 propagation contracts retain their own premises.

## 90.99 追加锚（本行以下为增补区）

## 91. Native prefix certificates for the same screened root response

### 91.1. The original table and the owned scalar

For a nonempty finite ordered native tree $t$, retain every actual occurrence, its
left/right address and its $\alpha/\beta$ leaf label. For $h\geq0$, define the
inclusive four-reply table

$$
p_h(t)(a)=
\begin{cases}
\alpha,\ \beta,&a\text{ is an actual leaf occurrence},\\
\mathsf{branch},&a\text{ is an actual pair occurrence},\\
\mathsf{absent},&a\text{ is not an occurrence},
\end{cases}
\qquad |a|\leq h .
\tag{91.1}
$$

The root, early terminals and all absent strict extensions are part of this table. Let
$L_t$ be the closed finite $N$ combinatorial Laplacian of §52.1–§52.7: every
parent–child seam has unit conductance, counting measure is used, and the root has no
outgoing killing seam. Put

$$
P_t=I-L_t/3,\qquad
G_\lambda(t)=\langle\delta_r,(L_t+\lambda I)^{-1}\delta_r\rangle,\qquad
q_\lambda=\frac3{3+\lambda}\quad(\lambda>0).
\tag{91.2}
$$

The native source and the immutable $\mathrm{INITIAL}$ are the same object in
$p_h(t)$ and $G_\lambda(t)$; a later current register is not substituted for either.
The native substitution $\rho$ is unchanged; $P_t$ is only the declared comparison
law on the retained actual occurrences.
Because $L_t=3(I-P_t)$,

$$
G_\lambda(t)=\frac1{3+\lambda}
 \sum_{n\geq0}q_\lambda^n\mu_n(t),\qquad
\mu_n(t):=\langle\delta_r,P_t^n\delta_r\rangle .
\tag{91.3}
$$

For $n\leq2h+2$, define $\mu_n(p)$ to be $\mu_n(t)$ for any finite native
tree with $p_h(t)=p$, and set

$$
S_h(p)=\frac1{3+\lambda}\sum_{n=0}^{2h+2}q_\lambda^n\mu_n(p).
\tag{91.4}
$$

### 91.2. Prefix locality and a uniform certificate

**Lemma 91.1 (closed-walk locality).** The quantities $\mu_n(p)$ in (91.4) are
well-defined. If $p_h(t)=p_h(u)$, then

$$
\mu_n(t)=\mu_n(u)\quad(0\leq n\leq2h+2).
\tag{91.5}
$$

**Proof.** The matrix $P_t$ is nonnegative and stochastic: an edge step has weight
$1/3$, while a hold at $x$ has weight $1-\deg(x)/3$. Expand $\mu_n(t)$ as the
sum of weights of length-$n$ walks which start and end at the root, allowing holds.
A walk which reaches depth $d$ and returns has at least $2d$ edge steps. Thus, for
$n\leq2h+2$, it cannot use a vertex below depth $h+1$. The table gives every
vertex and every edge through depth $h$, and it gives the number of children of every
branch at depth $h$. A newly exposed depth-$h+1$ vertex can only be an immediate
turning point at this length, so its hold weight and its children are not used. Hence
each walk has the same weight in any two trees with the same table. This includes a
singleton, an early terminal leaf and every absent address. The sum is therefore
independent of the realizing tree, proving (91.5). This is the finite-tree instance of
the sparse-matrix locality viewpoint of Benzi–Boito–Razouk, [BBR](https://arxiv.org/abs/1203.3953); no general decay theorem is invoked. $\square$

**Theorem 91.2 (same-operator prefix approximation).** For every finite native ordered
tree $t$, every $h\geq0$ and every $\lambda>0$,

$$
0\leq G_\lambda(t)-S_h(p_h(t))
 \leq \lambda^{-1}q_\lambda^{\,2h+3}.
\tag{91.6}
$$

Consequently, if $p_h(t)=p_h(u)$, then

$$
|G_\lambda(t)-G_\lambda(u)|
 \leq \lambda^{-1}q_\lambda^{\,2h+3}.
\tag{91.7}
$$

There is no factor $2$ in (91.7). At $\lambda=1$, $G_1(t)$ is exactly the
closed INITIAL response $F_{\mathrm{spec}}(t)$ of §52.21.

**Proof.** By Lemma 91.1, (91.4) is the initial segment of (91.3). Every
$\mu_n(t)$ is nonnegative and at most one because $P_t$ is stochastic. Therefore

$$
0\leq G_\lambda(t)-S_h(p_h(t))
\leq\frac1{3+\lambda}\sum_{n\geq2h+3}q_\lambda^n
=\lambda^{-1}q_\lambda^{2h+3}.
$$

If the two tables agree, both responses lie in the same interval
$[S_h,S_h+\lambda^{-1}q_\lambda^{2h+3}]$, which proves (91.7). The identity at
$\lambda=1$ is $L_t+I=\mathcal H_t^{(0)}+2I$ by §52.21. $\square$

### 91.3. All-depth native witnesses and sharpness

Let $t_{\mathrm{bal}}$ and $t_{\mathrm{comb}}$ be the two actual fifteen-node trees
with common word

$$
\omega=\alpha\beta\beta\alpha\beta\alpha\alpha\beta
$$

and the balanced and left-comb bracketings displayed in §52.19–§52.20. For
$h\geq0$, define actual finite sources

$$
W_0(t)=t,\qquad W_{h+1}(t)=\langle W_h(t),\alpha\rangle .
\tag{91.8}
$$

**Lemma 91.3 (common native data).** For every $h$, the two sources
$W_h(t_{\mathrm{bal}})$ and $W_h(t_{\mathrm{comb}})$ have the same leaf word
$\omega\alpha^h$, composition $(4+h,4)$, $15+2h$ occurrences, and root
cross-product value $q_0=0$. They also satisfy

$$
p_h(W_h(t_{\mathrm{bal}}))=p_h(W_h(t_{\mathrm{comb}})).
\tag{91.9}
$$

**Proof.** The first three assertions follow by appending one $\alpha$ leaf and its
parent at each step. §52.20 gives the common word, composition and $q_0=0$ at
$h=0$; the parent rule $q\langle x,y\rangle=q(x)\times q(y)$ preserves zero.
If a fixed leaf cap $H$ is imposed, the source has $8+h$ leaves and therefore
requires $H\geq8+h$; this is a per-source cap condition, not free cap growth.
At depth at most $h$, a table address either meets the added left spine or the
right $\alpha$ leaf, or reaches the root of the original fifteen-node tree exactly
at depth $h$. That root is a branch in both sources; the first differing descendants
are below the observed depth. Thus all four replies, including absence, agree. $\square$

Put $g_h(t)=G_1(W_h(t))$ and

$$
f(g)=\frac{2(1+g)}{5+3g}.
\tag{91.10}
$$
Here $f^0$ is the identity and $f^{h+1}=f\circ f^h$.

**Theorem 91.4 (all-depth response ambiguity).** For every $h\geq0$,

$$
g_h(t_{\mathrm{bal}})=f^h\!\left(\frac5{12}\right),\qquad
g_h(t_{\mathrm{comb}})=f^h\!\left(\frac{62614}{136883}\right),
\tag{91.11}
$$

and the second value is strictly larger. Hence every scalar estimator depending only
on $p_h$ has two-source worst-case error at least

$$
\frac12\left[f^h\!\left(\frac{62614}{136883}\right)-
f^h\!\left(\frac5{12}\right)\right]>0.
\tag{91.12}
$$

**Proof.** If a rooted tree has response $g$, attaching one parent seam changes the
child-root response to $g/(1+g)$ by the rank-one Schur complement. In
$W_{h+1}$, the other child is a leaf with attached response $1/2$, while the new
root diagonal of $L+I$ is $3$. Therefore

$$
g_{h+1}=\frac1{3-g_h/(1+g_h)-1/2}=f(g_h).
$$

The initial values are exactly §52.21–§52.22. Since
$f'(g)=4/(5+3g)^2>0$, strict inequality persists under every iterate. Any common
$p_h$-based estimate has the same output on the pair in (91.9); the elementary
two-point midpoint bound gives (91.12). $\square$

**Theorem 91.5 (sharp moment horizon, not a rate claim).** With
$\mu_n^{\mathrm{bal}}=\mu_n(W_h(t_{\mathrm{bal}}))$ and
$\mu_n^{\mathrm{comb}}=\mu_n(W_h(t_{\mathrm{comb}}))$,

$$
\mu_n^{\mathrm{comb}}-\mu_n^{\mathrm{bal}}=0\quad(0\leq n\leq2h+2),
\qquad
\mu_{2h+3}^{\mathrm{comb}}-\mu_{2h+3}^{\mathrm{bal}}
=\frac2{3^{\,2h+3}}.
\tag{91.13}
$$

**Proof.** The first equality is Lemma 91.1. At the original root, the comb has a
right $\beta$ leaf and the balanced tree has a right branch. After the common left
spine of length $h$, these are the only newly visible vertices whose hold weight can
differ at length $2h+3$: the leaf has diagonal $1-1/3=2/3$, whereas the
non-root branch has diagonal $1-3/3=0$. The unique differing walk goes down the
spine and to that right child, holds once, and returns. Its two edge traversals have
weight $3^{-(2h+2)}$, so the difference is
$3^{-(2h+2)}(2/3)=2/3^{2h+3}$. Every other walk of this length either stays within
the common table or reaches the new level without a hold and has equal weight. This
proves (91.13). It identifies the first missing moment; it does not assert an optimal
resolvent constant or approximation rate. $\square$

### 91.4. Lawful prefix supply and limits

**Assumption 91.6 (conditional prefix supply).** A certified even epoch $N=2k\geq2$
may supply $p_h(t)$ through the original-root, same-source ordered support/address
service of [ABT §12](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md),
with its source/version authentication, epoch certification, refusal and absorbing
Stop rules. Under the paid presence-only service of [FFM §§10–11](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_FRAME_MEMORY.md), the supplied prefix has

$$
q\leq2(2^{h+1}-1),\qquad \max|a|\leq h+k+1,\qquad a_{\mathrm{post}}=0.
\tag{91.14}
$$

These are premises of the cited services, not consequences of a numerical response
catalog, old $q/c/\text{word}$ replies, a CE post-cut state or mathematical existence
of a decoder.

**Corollary 91.7 (conditional original target estimate).** Under Assumption 91.6,
the actual original $G_\lambda(t)$ admits the certified output $S_h(p_h(t))$ with
the uniform error (91.6). The corollary concerns fixed positive screening and the
scalar root response of the same closed operator. It supplies no full-spectrum or
multiplicity recovery, no operator-factor or physical-dimension statement, no clock or
metric transport, no native symmetric-transport permission, no unrestricted sensor,
and no infinite-completion correspondence. Native realization, acquisition, clock,
source-state versus spatial-position, and operator/boundary permissions remain
separate hypotheses; the exclusions of §§55, 81, 89 and 90 continue to apply.

The witnesses and estimate are ordinary finite-source mathematics on the original
counting-measure operator. They do not identify a physical space dimension or complete
the broader why-three programme.

## 91.99 追加锚（本行以下为增补区）

## 92. 三分量接口与高秩源纤维的分离

§90 已经把三分量端口 $q$ 与完整子树估值 $V_Q$、原生行 $R_Q$ 和实际空间位置区分开。本节把这一区分推进到几何桥的最低检验：一个端口如果只通过 $q$ 产生空间状态，就不能同时保留 §90 的完整源身份；一个保留缺陷族的度量几何，则必须另外声明它允许的线性或非线性实现。

**定义 92.1（只经三分量端口的空间因子）。** 设 $\mathcal X$ 是一组实际来源，$q:\mathcal X\to\mathbb R^3$ 是 §90.1 的固定有向三分量端口。称一个空间状态因子为 $q$-only，如果存在映射 $\iota$ 使

$$
F=\iota\circ q:\mathcal X\longrightarrow M.
\tag{92.1}
$$

这里 $M$ 可以是 $\mathbb R^3$、带度量的三维流形，或任何其它目标；定义不把目标误称为空间位置。

**命题 92.2（$q$-only 因子不能保留 §90 的完整源任务）。** 对 §90.4 的每个测试族 $\mathcal F_h$，若 $F$ 是 $q$-only，则 $F$ 在 $\mathcal F_h$ 上为常值。因此在该族上不存在解码器 $D$ 满足

$$
D(F(\nu))=\nu
\qquad(\nu\in\mathcal F_h),
\tag{92.2}
$$

也不存在解码器恢复完整子树估值 $V_Q$。同一结论适用于任何任务目标 $G$，只要 $G$ 在 $\mathcal F_h$ 上不是常值。

**证明。** 命题 90.5 给出 $q(\nu)=0$ 对所有 $\nu\in\mathcal F_h$，而 $\mathcal F_h$ 至少含有两个不同来源。于是式 (92.1) 给出 $F(\nu)=\iota(0)$，所以 $F$ 不是单射。若式 (92.2) 成立，则不同来源的像必须不同，矛盾。命题 90.5 同时给出 $V_Q$ 在该族上单射，故相同论证排除 $V_Q$ 的恢复。对一般 $G$，只需取该族中两个 $G$ 值不同的来源。证毕。

这个结论只排除“完整空间状态完全因子化于 $q$”的桥。它没有排除把 $q$ 作为一个局部接口、再与历史、来源标签、共同环境或其它响应一起使用的桥，也没有把三分量的数值端口解释成坐标位置。

**定理 92.3（已验证的原生缺陷族具有增长的内在方向秩）。** 对 $n\ge3$，令

$$
\mathcal S_n=\operatorname{sourceFamily}(T_n),\qquad
\mathcal A_n=\operatorname{normalizedAreaFamily}(n).
\tag{92.3}
$$

D5.S3.Arith.FibonacciAtomic.Geometry.NativeAncestryDefectCube.normalized_cube_diameter
给出以下同一层级的事实：

$$
\begin{aligned}
|\mathcal S_n|&=2^{F_{n-2}},\\
\operatorname{diam}(\mathcal A_n)
&=\frac{\sqrt{2F_{n-2}}}{\binom{F_{n+1}}2},\\
\operatorname{diam}(\mathcal A_n)&\longrightarrow0.
\end{aligned}
\tag{92.4}
$$

同一模块的 native_area_cube 还给出：由这些来源差异张成的内在方向空间满足

$$
\operatorname{finrank}_{\mathbb R}\operatorname{directionSpan}(T_n)=F_{n-2}.
\tag{92.5}
$$

这里的 $F_k$ 是项目中的 Fibonacci 数列。式 (92.4) 的直径是归一化面积坐标的直径；式 (92.5) 是未把这些独立差异压成三根方向所得的内在线性秩。两者分别测量压缩后的尺度和保留差异所需的方向数，不能互相替代。

**证明。** 这是两个已声明结果的直接合取：normalized_cube_diameter 的逐 $n$ 分支给出前两式及极限，native_area_cube 的方向分支给出式 (92.5)。本节不把这些声明改写成新的专门化定理。证毕。

**推论 92.4（线性三维桥的秩障碍）。** 假设某个候选桥在 $\mathcal A_n$ 的仿射方向上由线性映射

$$
L_n:\operatorname{directionSpan}(T_n)\longrightarrow\mathbb R^3
$$

实现，并要求它在所有独立缺陷方向上保持线性独立性，特别要求 $L_n$ 为单射。若 $F_{n-2}>3$，这样的桥不存在。

**证明。** 由式 (92.5)，定义域的实维数为 $F_{n-2}>3$。线性单射会给出

$$
F_{n-2}\le\dim\mathbb R^3=3,
$$

与假设矛盾。证毕。

这个推论的量词很窄：它排除的是保持该内在线性结构的固定三维线性桥。它不排除一般的非线性编码，也不声称源集合本身不能被注入 $\mathbb R^3$；一个任意集合当然可以有许多不同的编码。要把非线性桥解释成实际空间，还必须另行提供距离、邻接、测度、边界、运输和算子相容性。

**命题 92.5（两个坍缩方向必须分账）。** 在 $\mathcal F_h$ 上，完整源任务的商有 $2^{2^h}$ 个类，而 $q$ 和 $(R_Q,q)$ 只有一个类；在 $\mathcal A_n$ 上，归一化面积直径趋于零，而内在方向秩为 $F_{n-2}$。因此下列两种说法不等价：

1. 当前三分量读数把许多来源合并；
2. 选定几何坐标在细化时把许多点压到小直径。

**证明。** 第一项是命题 90.5 的商计数，第二项是定理 92.3。前者是观察因子核，后者是一个已指定坐标族的尺度行为；它们的定义域、目标和保持条件不同。证毕。

因此，当前最小的三维桥接义务可以写成四项同时存在的对象：

$$
\boxed{
\text{来源或合法商}
\;+\;
\text{实际状态映射}
\;+\;
\text{距离/测度与边界}
\;+\;
\text{由同一映射诱导的运输算子}.
}
\tag{92.6}
$$

仅有 $q:\mathcal X\to\mathbb R^3$ 不能提供式 (92.6)；仅有 $\mathcal A_n$ 的三维外部坐标也不能提供式 (92.6)。相反，若一个候选桥明确保留完整源纤维，并在其声明的任务上证明这些对象相容，那么三维可以作为局部接口继续存在，而不被误报为完整关系体的总信息维数。

本节消费 §90 的严格源纤维结果和 NativeAncestryDefectCube 的已编译结果；它没有添加 FIB 到物理三维空间的实现假设，也没有把三分量端口、归一化面积坐标或内在方向秩中的任一项单独提升为三维唯一性证明。

## 92.99 追加锚（本行以下为增补区）

## 93. 固定三维桥的统一失真门

前节的两个族不能合并成一个未声明的共同域。$\mathcal F_h$ 是 §90 的完整事件前缀中的测试来源，$q$ 是其精确观察；$\mathcal S_n$ 和 $\mathcal A_n$ 是 NativeAncestryDefectCube 中的替换来源及其归一化面积表示。下面的距离结论只对后者成立，不能把它转写成 $q$ 的距离结论。

**定义 93.1（归一化面积顶点与统一度量桥）。** 令

$$
P_n=\operatorname{positions}(T_n),\qquad
K_n=|P_n|,\qquad
C_n=\binom{F_{n+1}}2,
$$

并对每个 $A\subseteq P_n$ 定义

$$
a_{n,A}
=
C_n^{-1}\,
\operatorname{areaVector}\bigl((T_n).\operatorname{length},
\operatorname{variant}(T_n,A)\bigr).
\tag{93.1}
$$

令 $\mathcal A_n^\ast$ 表示这些带有 $A$ 标签的点，而不是只把它们写成一个未标记集合。一个固定三维的统一双 Lipschitz 桥，是一族映射

$$
\Phi_n:\mathcal A_n^\ast\longrightarrow\mathbb R^3
$$

以及与 $n$ 无关的常数 $0<c\le C<\infty$，满足所有 $A,B\subseteq P_n$

$$
c\|a_{n,A}-a_{n,B}\|
\le
\|\Phi_n(A)-\Phi_n(B)\|
\le
C\|a_{n,A}-a_{n,B}\|.
\tag{93.2}
$$

这里下界承担来源差异的保真，上界承担不把同一归一化尺度任意放大的约束；若允许每层任意重标度，式 (93.2) 的跨层内容就不成立。

**定理 93.2（统一双 Lipschitz 桥不能落入固定 $\mathbb R^3$）。** 不存在满足定义 93.1 的统一双 Lipschitz 桥。

**证明。** native_area_cube 的平方距离分支给出，对 $A\ne B$，

$$
\|a_{n,A}-a_{n,B}\|^2
=
\frac{2\,|A\mathbin\triangle B|}{C_n^2}.
\tag{93.3}
$$

因此不同点的最小距离为

$$
\lambda_n=\frac{\sqrt2}{C_n},
$$

而 normalized_cube_diameter 给出直径

$$
D_n=\frac{\sqrt{2K_n}}{C_n}.
$$

由下界，半径 $c\lambda_n/2$ 的三维球在各个 $\Phi_n(A)$ 周围两两不交。固定一个标签 $A_0$，由上界它们都包含在半径

$$
CD_n+\frac{c\lambda_n}{2}
$$

的球内。比较三维体积并约去 $(c\lambda_n/2)^3$，得到

$$
2^{K_n}
\le
\left(1+2\frac Cc\frac{D_n}{\lambda_n}\right)^3
=
\left(1+2\frac Cc\sqrt{K_n}\right)^3.
\tag{93.4}
$$

但 $K_n=F_{n-2}$ 无界，左侧按 $2^{K_n}$ 增长，右侧仅按 $K_n^{3/2}$ 增长，故对充分大的 $n$ 矛盾。证毕。

这个结论的对象和量词必须保留：它针对归一化面积顶点、固定欧氏三维目标、跨所有 $n$ 的统一失真常数。它不声称单个有限族不能注入 $\mathbb R^3$，也不声称任意非线性桥都不存在。

**反例 93.3（有限层可以编码，代价是失去度量保真）。** 固定 $n$，枚举 $P_n=\{p_1,\ldots,p_{K_n}\}$，定义

$$
e_n(A)=\sum_{j=1}^{K_n}\mathbf1_{\{p_j\in A\}}\,2^{-j}.
\tag{93.5}
$$

不同的子集有不同的二进制值，所以 $e_n$ 把这一有限来源族注入 $[0,1]\subset\mathbb R\subset\mathbb R^3$。但是当 $n$ 增长时，式 (93.5) 不保持式 (93.3) 的距离比例；它是编码，不是统一空间实现。

**推论 93.4（$q$-only 的下界立即失败）。** 在 §90 的 $\mathcal F_h$ 中取两个不同来源 $u,v$。因 $q(u)=q(v)$，任意 $q$-only 桥 $\Phi\circ q$ 都满足

$$
\|\Phi(q(u))-\Phi(q(v))\|=0.
$$

若来源距离规定 $d_{\mathrm{src}}(u,v)>0$，则任何要求

$$
c\,d_{\mathrm{src}}(u,v)
\le
\|\Phi(q(u))-\Phi(q(v))\|
\qquad(c>0)
$$

的桥立即失败。这是观察核造成的零距离，不是归一化面积直径趋零造成的压缩；两者不能互换。

因此，当前的三维桥接问题至少分成三个互不替代的层次：

$$
\boxed{
\begin{array}{c}
\text{精确观察 }q:\text{Source}\to\mathbb R^3,\\
\text{变维归一化表示 }a_{n,A},\\
\text{原生来源到实际空间的映射、度量、边界与算子合同}.
\end{array}
}
\tag{93.6}
$$

第一层的三分量数目不能推出第三层的物理空间维数；第二层的方向秩和直径也不能单独提供第三层的来源映射。下一步若要获得三维的实质解释，必须在同一个有类型的来源族上给出第三层的映射及其运输、测度和时钟相容性。

## 93.99 追加锚（本行以下为增补区）

## 94. 联合终端响应：代数零点不等于合法来源碰撞

最新 DEV 的[严格实数联合相交卷](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md)把上一节的来源保真义务再推进了一步。对一个固定的已获取历史，必须把“存在两个完整世界在某个终端动作下响应相同”与“两个终端动作分别出现了相同的代数指标”分开。前者要求完整来源、原始读数、严格不等式、非奇异分母以及全部严格源方程和守卫同时成立；后者至多提供候选零点。

**定义 94.1（合法联合碰撞）。** 设 $p\ne24$，且 $C(p,v)$ 是固定历史与固定新读出的完整合法世界纤维；沿用严格实数卷的记号，令 $f_J=f_{MJ}$、$f_M=f_{MM}$ 为两种允许终端动作的响应。定义

$$
\begin{aligned}
D_J&=\{(p,v):\exists W\ne W'\in C(p,v),\ f_J(W)=f_J(W')\},\\
D_M&=\{(p,v):\exists W\ne W'\in C(p,v),\ f_M(W)=f_M(W')\}.
\end{aligned}
\tag{94.1}
$$

真正的联合事件是 $D_J\cap D_M$。一个候选参数只有在同一个合法来源纤维中完成两个分别带有来源不等性的碰撞，才属于这个集合。

**命题 94.2（投影零点的提升义务）。** 若一个参数化坐标中的方程组 $G(z)=0$ 只表达投影后的终端指标相等，则

$$
G(z)=0
\quad\Longrightarrow\quad
\text{候选联合零点},
$$

而不能直接推出 $(p,v)\in D_J\cap D_M$。要得到后者，还必须证明：

$$
\boxed{
\begin{gathered}
z\text{ 对应完整合法世界};\\
\text{两个配对中的世界各自不同};\\
\text{所有原始历史读数与严格源方程成立};\\
\text{没有被投影、奇异分母或重复根伪造的标签}.
\end{gathered}}
\tag{94.2}
$$

**证明。** 式 $G(z)=0$ 只约束其所写出的投影坐标。若参数化域还包含不满足来源方程的代数点、重复标签或奇异极限，则这些点不属于 $C(p,v)$，因而不属于 $D_J$ 或 $D_M$。即使它们都合法，若完整纤维中的终端响应仍分别单射，也不存在定义 94.1 所需的来源不等性碰撞。证毕。

严格实数联合相交卷给出了一个精确的反例：在一个极小有理盒中，六个投影方程有唯一横截共同零点；但完整合法子纤维恰有三个世界，且 $f_J$ 与 $f_M$ 在这三个世界上都单射。因此该共同零点不是 $D_J\cap D_M$ 的成员。这个结果把“维数足够”与“联合响应真正可碰撞”明确分离开来。

**推论 94.3（对三维桥的约束）。** 若一个候选三维状态桥只保留投影坐标，并把 $G(z)=0$ 当作联合来源碰撞的证据，则它可能把不属于同一合法来源纤维的代数标签错误地合并。任何声称三维接口已经保留联合终端任务的桥，至少要提供：

$$
\boxed{
\text{合法来源纤维}
\;+\;
\text{终端动作的联合响应}
\;+\;
\text{来源不等性以及全部严格源方程、守卫与历史读数约束的证明}.
}
\tag{94.3}
$$

这项约束与第 92、93 节的两种障碍正交：第 92 节排除只经 $q$ 的完整来源恢复，第 93 节排除跨层统一双 Lipschitz 的固定三维保真桥；本节说明即使某个代数图看起来已经出现共同相交，也必须先完成来源与联合响应的提升。

**开放边界 94.4。** 严格实数卷的结果把一个共同代数零点排除为合法联合碰撞，并缩小了零漂移分支的外部候选集；它没有完成整个 $D_J\cap D_M$ 的全局分类。因而当前可保留的结论是：

$$
\boxed{
\text{三维接口的联合充分性必须在完整合法来源纤维上核验；}
}
\tag{94.4}
$$

而不是“联合碰撞已被三维坐标完全刻画”。这为后续研究提供了明确检验顺序：先验证来源提升和合法性，再验证终端响应，最后才讨论固定维数的几何实现。

## 94.99 追加锚（本行以下为增补区）
