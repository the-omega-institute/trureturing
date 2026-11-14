# QUANTUM ORIGIN: FINITE TENSOR QUOTIENT AND GLOBAL NONCOLLAPSE XIV

> **Permanent reading convention.** This `generic-v1` volume is a theory reference input containing ordinary mathematical definitions, theorems and paper proofs. Once merged, its text and labels are append-only; corrections and additions belong after the final append anchor. The paper is not Lean-kernel verified; Lean remains the formal source of truth.

**Provenance.** The skills are `formal-thinking-and-answer` and `theory-volume-template`. The mathematical text is authored by native Codex (GPT-6 family). Native validation covers source preservation, labels and reading references; authorship and validation share one model family and supply no independent or cross-family mathematical verification.

**Cross-volume reading.** [Volume XII, §159](QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_XII.md#159-有限量子面实际面非塌缩与任意有限秩的同原重建) contains the one-copy background. §§160–162, the definitions of $\mathsf G_3$ and $\mathsf R_3$, and their conditional reconstruction suppliers are in [volume XIII](QUANTUM_ORIGIN_BINARY_TANGENT_CLOSURE_AND_GLOBAL_NONCOLLAPSE_XIII.md). Chapter 165 specifies its own construction hypotheses. The aligned low-two-layer seed and pencil chapters in XIII are not premises of its proofs.

## 165. A fixed-local-space tensor quotient with all finite binary geometries and collapsing neighbor faces

**Definition 165.1 (one quotient and its entire tensor hierarchy).**
Fix an integer $m\ge3$, put $d=2m$, and equip the real space
$A=\operatorname{Herm}_d(\mathbb C)$ with the positive-definite real
pairing $\langle X,Y\rangle=\operatorname{Tr}(XY)$. Set

$$
H=\operatorname{diag}(I_m,-I_m),\qquad R=H^\perp\subset A,\qquad
V=A/\mathbb RH,\qquad \pi:A\longrightarrow V,\qquad
u(\pi X)=\operatorname{Tr}X.
\tag{165.1}
$$

Trace is well defined since $\operatorname{Tr}H=0$. For every finite
$N\ge1$, use the real tensor products and the definitions

$$
\begin{gathered}
D_N=d^N,\qquad A_N=\operatorname{Herm}_{D_N}(\mathbb C)
             =A^{\otimes_{\mathbb R}N},\qquad
W_N=V^{\otimes_{\mathbb R}N},\qquad \pi_N=\pi^{\otimes N},\\
C_N=\pi_N(\operatorname{PSD}_{D_N}),\qquad
u_N=u^{\otimes N},\qquad
K_N=\pi_N(\mathcal D_{D_N}),\qquad
\mathcal N_N=\ker\pi_N,\qquad R_N=R^{\otimes N}.
\end{gathered}
\tag{165.2}
$$

The tensor identification in (165.2) is the actual
Kronecker map on Hermitian matrices. Indeed tensor products of real
Hermitian bases are independent, and both spaces have real dimension
$d^{2N}=D_N^2$. Its pairing is exactly

$$
\operatorname{Tr}\bigl((X_1\otimes\cdots\otimes X_N)
 (Y_1\otimes\cdots\otimes Y_N)\bigr)
=\prod_{i=1}^N\operatorname{Tr}(X_iY_i).
\tag{165.3}
$$

Thus this is one fixed $V$ at every level, with its original tensor
products, dual products, units, evaluation, brackets and position
permutations. The cones are the whole displayed images, including the
images of every correlated density matrix. Each own effect menu is
$\mathcal E_N=[0,u_N]_{C_N^{\ast}}$; $P_N$, $\mathcal F_{N,p}$,
$T_{N,p}$, $p_N^\perp$ and $F_N$ have exactly the original meanings
in (161.4)–(161.6). No subset of effects is substituted for this menu.

**Theorem 165.2 (complete original background at every finite split).**
The data of Definition 165.1 satisfy all of (161.1)–(161.3), with the
actual original permutations and reassociation. Under dual pullback by
$\pi_N$ and the trace pairing, the full dual, effects, confirmers and
minimum on every original mixed input are exactly

$$
\begin{gathered}
W_N^{\ast}\simeq R_N,\qquad C_N^{\ast}\simeq R_N\cap\operatorname{PSD}_{D_N},
\qquad
\mathcal E_N\simeq R_N\cap[0,I_{D_N}],\\
f_E(\pi_NX)=\operatorname{Tr}(EX),\\
\mathcal F_{N,\pi_NP_v}\simeq
 \{E\in R_N:0\preceq E\preceq I_{D_N},\ Ev=v\},\\
T_{N,\pi_NP_v}(\pi_N\rho)
 =\min_{\substack{E\in R_N,\ 0\preceq E\preceq I_{D_N}\\Ev=v}}
      \operatorname{Tr}(E\rho),\qquad \rho\in\mathcal D_{D_N}.
\end{gathered}
\tag{165.4}
$$

The confirmer and minimum lines apply to any unit $v$ whose image is
pure; Theorem 165.4 below shows that this includes every unit $v$ and
exhausts $P_N$.

Proof. The orthogonal splitting $A=R\oplus\mathbb RH$ and the
isomorphism $\pi|_R:R\to V$ give

$$
\mathcal N_N
 =\sum_{i=1}^N A^{\otimes(i-1)}\otimes\mathbb RH
                      \otimes A^{\otimes(N-i)},\qquad
\mathcal N_N^\perp=R_N.
\tag{165.5}
$$

These identities use the tensor trace pairing (165.3); in particular
they are identities of the actual real spaces, not just of product
positive elements. The tensor map $\pi_N$ is surjective, and equality
of the trace and $u_N\pi_N$ on simple tensors proves
$u_N\pi_N=\operatorname{Tr}$ on all of $A_N$.

The image $K_N$ of the compact density set is compact, convex and
contained in $u_N=1$. Moreover $C_N=\mathbb R_{\ge0}K_N$, and a
positive lift of a nonzero element has strictly positive trace. Thus
$u_N$ is strictly positive on $C_N\setminus\{0\}$, and
$C_N\cap\{u_N=1\}=K_N$. For a convergent sequence $t_jk_j$ in this
cone, $t_j=u_N(t_jk_j)$ converges. Compactness of $K_N$ proves that
the limit is in the cone, including when $t_j\to0$. Hence $C_N$ is
closed. Strict positivity excludes a nonzero element of both $C_N$
and $-C_N$. Finally PSD spans $A_N$, so surjectivity makes $C_N$
generating. This verifies the complete single-level background at each
$N$.

A real functional descends exactly when its trace matrix annihilates
$\mathcal N_N$, giving $W_N^{\ast}\simeq R_N$. It is positive on the
whole image cone exactly when $\operatorname{Tr}(EX)\ge0$ for every
$X\succeq0$, equivalently $E\succeq0$ by testing rank-one $X$.
The matrix of $u_N$ is $I_{D_N}\in R_N$, since $I_d\in R$.
Applying positivity also to $u_N-f_E$ gives the effect interval in
(165.4). For a positive contraction, $v^{\ast}Ev=1$ is equivalent to
$Ev=v$, because $v^{\ast}(I-E)v=0$ forces $(I-E)^{1/2}v=0$.
This proves the confirmer and minimum formulas. All evaluations are
independent of the positive lift by (165.5). The matrix interval is
compact and the confirmer set contains $I_{D_N}$, so every minimum
exists. No affine formula for this lower envelope is assumed.

Now fix any split $a+b=N$. Arbitrary $x\in C_a,y\in C_b$ have
positive lifts $X\in A_a,Y\in A_b$. Their tensor $X\otimes Y$ is
positive and maps to the actual $x\otimes y$, proving
$C_a\otimes_{\min}C_b\subseteq C_N$. Conversely any positive
functionals on the two whole block cones have matrices
$E\in R_a\cap\operatorname{PSD}_{D_a}$ and
$G\in R_b\cap\operatorname{PSD}_{D_b}$. For every positive lift
$Z\in A_N$, including every correlated one,

$$
(f_E\otimes f_G)(\pi_N Z)=\operatorname{Tr}((E\otimes G)Z)\ge0.
\tag{165.6}
$$

The last inequality follows by taking the trace of
$Z^{1/2}(E\otimes G)Z^{1/2}\succeq0$. This proves the maximum
bound with $C_a,C_b$ themselves at every split. It also proves the
positivity of every product of original positive effects; product
normalized effects and their complements have the usual unit bound.

For a position permutation $s$, let $U_s$ be the quantum unitary
which actually permutes those tensor factors, and let $S_s$ permute
the factors of $W_N$. Equality on simple tensors, followed by spanning,
gives

$$
S_s\pi_N(X)=\pi_N(U_sXU_s^{\ast}).
\tag{165.7}
$$

Conjugation preserves PSD, so $S_s$ and $S_s^{-1}$ are positive on
the entire original cone. The same tensor identities show that
reassociation is the actual canonical identity, in every grouping.
Equation (165.3) gives exact evaluation on products; product linear
functionals separate $W_N$ by finite-dimensional tensor duality.
One can also use product effects for separation: every Hermitian
$E\in R_a$ lies between $-cI$ and $cI$ for some $c>0$, so the
own effect interval spans $R_a$, and similarly at every block.
Discarding agrees with the quotient of the matrix partial trace,

$$
(\operatorname{id}_{W_a}\otimes u_b)\pi_{a+b}Z
 =\pi_a(\operatorname{Tr}_{\mathbb C^{D_b}}Z),
\tag{165.8}
$$

as follows first on simple tensors and then on all $Z$. It is therefore
positive on every correlated input. All asserted products, pairings,
units, permutations and brackets are the original ones. ∎

**Theorem 165.3 (sharp tensor-kernel inertia at every finite level).**
For every finite $N\ge1$ and every nonzero $X\in\mathcal N_N$,

$$
n_+(X)\ge m,\qquad n_-(X)\ge m,
\tag{165.9}
$$

where $n_\pm$ count strictly positive and strictly negative eigenvalues
with multiplicity. Both bounds are attained at every level.

Proof. We first prove the scalar null-cone lemma: if $B\in A$ and
$a^{\ast}Ba=0$ for every unit $a$ with $a^{\ast}Ha=0$, then
$B=cH$ for some $c\in\mathbb R$. In the two $m$-by-$m$ blocks of
$H$, use $a=(x,e^{it}y)/\sqrt2$ with arbitrary unit
$x,y\in\mathbb C^m$. The hypothesis gives

$$
x^{\ast}B_{++}x+y^{\ast}B_{--}y
       +2\operatorname{Re}(e^{it}x^{\ast}B_{+-}y)=0
             \qquad(t\in\mathbb R).
\tag{165.10}
$$

Varying $t$ forces $B_{+-}=0$. The remaining equality for all $x,y$
forces $B_{++}=cI_m$ and $B_{--}=-cI_m$, by Hermitian polarization.
For the matrix-valued version, expand any Hermitian $Y$ on
$\mathbb C^d\otimes\mathbb C^k$ as $Y=\sum_jB_j\otimes F_j$
in a real Hermitian basis $(F_j)$ of the second factor. If every
isotropic compression vanishes, each real coefficient
$a^{\ast}B_ja$ vanishes. The scalar lemma therefore gives

$$
\bigl[(a^{\ast}\otimes I_k)Y(a\otimes I_k)=0
       \text{ for every unit }a\text{ with }a^{\ast}Ha=0\bigr]
\ \Longrightarrow\ Y=H\otimes A\quad(A\in\operatorname{Herm}_k).
\tag{165.11}
$$

Now induct on $N$. At $N=1$, the nonzero kernel elements are the
nonzero multiples of $H$, with $m$ eigenvalues of each sign. For
$N\ge2$ and $0\ne X\in\mathcal N_N$, each unit isotropic $a$
defines a functional $\ell_a(B)=a^{\ast}Ba$ on $A$ that annihilates
$H$, so it descends to $\bar\ell_a\in V^{\ast}$. Set

$$
J_a=a\otimes I_{D_{N-1}},\qquad X_a=J_a^{\ast}XJ_a\in A_{N-1}.
\tag{165.12}
$$

The actual tensor maps give

$$
\pi_{N-1}(X_a)
 =(\bar\ell_a\otimes\operatorname{id}_{W_{N-1}})(\pi_NX)=0,
\tag{165.13}
$$

so $X_a\in\mathcal N_{N-1}$. If some $X_a\ne0$, induction gives
$n_\pm(X_a)\ge m$. The isometry $J_a$ maps any strictly positive
or strictly negative subspace for $X_a$ to one for $X$, hence

$$
n_\pm(X)\ge n_\pm(X_a)\ge m.
\tag{165.14}
$$

Otherwise every $X_a=0$, so (165.11) yields $X=H\otimes A$ with
$0\ne A\in A_{N-1}$. Each nonzero eigenvalue of $A$ produces $m$
positive and $m$ negative tensor eigenvalues, and therefore

$$
n_+(X)=n_-(X)=m\operatorname{rank}A\ge m.
\tag{165.15}
$$

For sharpness, at every $N$ the nonzero matrix
$H\otimes P_e^{\otimes(N-1)}$ belongs to (165.5), for any unit
$e\in\mathbb C^d$, and has $m$ eigenvalues of each sign; at $N=1$
this means $H$. ∎

**Theorem 165.4 (unique positive lifts, all pure states, and actual small support faces).**
For every $N\ge1$, any $\sigma\succeq0$ of rank at most $m-1$
is the unique positive lift of $\pi_N\sigma$. For every complex
subspace $S\subseteq\mathbb C^{D_N}$ of dimension at most $m-1$,
$\pi_N\mathcal D(S)$ is an actual face of $K_N$, and

$$
\pi_N^{-1}(\pi_N\mathcal D(S))\cap\mathcal D_{D_N}=\mathcal D(S).
\tag{165.16}
$$

The restriction of $\pi_N$ to $\operatorname{Herm}(S)$ is a
trace-preserving linear order isomorphism onto the span of that face
cone. Its state restriction is an affine isomorphism. All the original
pure points are exactly the distinct images $p_v=\pi_NP_v$, and

$$
\mathbb{CP}^{D_N-1}\longrightarrow P_N,\qquad [v]\longmapsto p_v
\tag{165.17}
$$

is a homeomorphism. For any finite family of unit vectors with
$S=\operatorname{span}_{\mathbb C}\{v_1,\ldots,v_k\}$ of dimension
at most $m-1$,

$$
F_N(p_{v_1},\ldots,p_{v_k})=\pi_N\mathcal D(S).
\tag{165.18}
$$

The empty family gives the empty face. The vectors in these statements
are arbitrary, including vectors entangled across the original slots.

Proof. If $\rho\succeq0$ is another lift of $\pi_N\sigma$, put
$X=\rho-\sigma\in\mathcal N_N$. On $\ker\sigma$ its quadratic
form is nonnegative. A negative spectral subspace of dimension larger
than $\operatorname{rank}\sigma$ would intersect $\ker\sigma$
nontrivially, which is impossible. Thus
$n_-(X)\le\operatorname{rank}\sigma\le m-1$, and (165.9) forces
$X=0$. This is the elementary sign-rank comparison underlying the
mature low-rank-versus-all-state criterion [CHST165, §4.1, Lemma 1(c),
Lemma 2(a), Theorem 1(a)]; that general criterion is background, not a
new state-determination theorem here. Its tensor-kernel premise has
been proved in Theorem 165.3.

Let $r=\dim S\le m-1$. Every Hermitian matrix supported on $S$
has at most $r$ positive and at most $r$ negative eigenvalues; (165.9)
therefore makes $\pi_N$ injective on $\operatorname{Herm}(S)$.
For $\sigma\in\mathcal D(S)$ and an original convex decomposition
$\pi_N\sigma=tx+(1-t)y$, $0<t<1$, choose density lifts
$\alpha,\beta$ of $x,y$. Their mixture is a positive lift of
$\pi_N\sigma$, so uniqueness gives
$\sigma=t\alpha+(1-t)\beta$. For $z\in S^\perp$, positivity and
$z^{\ast}\sigma z=0$ force $\alpha z=\beta z=0$; hence both lifts are
supported on $S$. This proves the actual face property and (165.16).

The image of $\operatorname{PSD}(S)$ is exactly the cone of this
face. To check order also on its entire real span, suppose
$Y\in\operatorname{Herm}(S)$ and $\pi_NY=\pi_N\rho$ for some
$\rho\succeq0$. Choose $\eta\in\mathcal D(S)$ positive definite
on $S$ and $c>0$ large enough that $c\eta+Y\succeq0$. This matrix
has rank at most $r$ and shares its image with $c\eta+\rho\succeq0$.
Uniqueness gives $Y=\rho\succeq0$. Together with injectivity and
trace preservation this proves the full order-isomorphism assertion.
The zero subspace has zero cone span and empty normalized face, so is
covered separately without choosing $\eta$.

In particular every rank-one image is a singleton actual face and
hence pure. Distinct rank-one projectors have distinct images by unique
positive lifting. Conversely, a density lift of an arbitrary original
extreme point has a finite spectral decomposition. Its image is a
convex combination of these rank-one images, so extremality makes
it one of them. This proves exhaustion. The continuous map (165.17)
is therefore a bijection from compact complex projective space to the
pure set in a finite-dimensional Hausdorff space; it is a homeomorphism.

For a nonempty family in (165.18), its equally weighted lifted mixture
is positive definite on $S$. The standard matrix support-face rule,
recalled in §159.1, says that the lifted projectors generate exactly
$\mathcal D(S)$. The image set is an actual face, so the minimal
original face is contained in it. Pulling that minimal face back by the
affine isomorphism gives a face of $\mathcal D(S)$ containing all
these projectors, hence all of $\mathcal D(S)$. This proves equality,
not merely containment in a convex copy. ∎

**Theorem 165.5 (all-level L2 and TC, and every fixed finite geometric face budget).**
For $m\ge3$, L2 and TC of §161.1 hold on the whole $K_N$ for
every finite $N\ge1$. For $m\ge4$, L3 of Definition 160.2 also
holds at every level. More generally, for any fixed integer $r\ge1$,
choosing $m\ge\max\{3,r+1\}$ ensures that at every finite level
every face generated by at most $r$ pure points is the full intrinsic
complex density face on their lifted vector span. These assertions
concern actual state-face geometry with the original unit.

Proof. Fix $N$ and suppress its index on $\pi_N$ temporarily.
Two distinct pure points have distinct lifted lines spanning a complex
two-space $S$, so (165.18) identifies their entire actual face with
$\mathcal D(S)$. The usual Pauli parametrization identifies this
space with the full closed Euclidean three-ball, proving L2.
All its extreme points are precisely the images of the unit vectors
in $S$, by the affine isomorphism and the global pure injectivity.

For TC take arbitrary $a=p_\alpha,b=p_\beta,p=p_v$ with $a\ne b$
and $p\notin B_N(a,b)$. Put $S=\operatorname{span}_{\mathbb C}
\{\alpha,\beta\}$. Equation (165.16) gives the exact external-point
condition $v\notin S$. Consequently

$$
Q_v=I-P_v,\qquad U=Q_vS=v^\perp\cap
\operatorname{span}_{\mathbb C}\{v,\alpha,\beta\}
\tag{165.19}
$$

has complex dimension two, with basis $z_\alpha=Q_v\alpha$,
$z_\beta=Q_v\beta$. For $z\perp v$, the normalized rank-one curve
and its derivative are

$$
\gamma_z(t)=\frac{(v+tz)(v+tz)^{\ast}}{1+t^2\|z\|^2},\qquad
\gamma_z'(0)=\Theta_v(z)=vz^{\ast}+zv^{\ast}.
\tag{165.20}
$$

For every unit $w\in S$, its actual binary ball with $p_v$ is
$\pi\mathcal D(\operatorname{span}\{v,w\})$. Differentiating its
rank-one boundary through the affine isomorphism gives its entire
intrinsic tangent direction,

$$
\tau_{N,p_v}(p_w)=\pi\Theta_v(\mathbb C Q_vw).
\tag{165.21}
$$

The map $\Theta_v$ is real linear; complex coefficients on a line
are carried by the two real directions $\Theta_v(z)$ and
$\Theta_v(iz)$. Since $Q_vw\in U$, (165.21) implies

$$
\tau_{N,p_v}(p_w)\subseteq\pi\Theta_v(U)
 =\tau_{N,p_v}(a)+\tau_{N,p_v}(b),
\tag{165.22}
$$

for every original pure point of $B_N(a,b)$. This is exactly TC with
all its quantifiers, for arbitrary correlated lifted vectors.

For completeness these are the noncollapsed tangent spaces themselves.
If $z\ne0$ and $z\perp v$, then $\Theta_v(z)$ has eigenvalues
$\|z\|,-\|z\|$ and zeros, by restricting to
$\operatorname{span}\{v,z\}$. Thus it has sign ranks $(1,1)$ and
cannot belong to $\mathcal N_N$ by (165.9). Also
$\Theta_v(z)v=z$, so $\Theta_v$ is injective. Therefore each single
tangent direction has real dimension two and the endpoint sum
$\pi\Theta_v(U)$ has dimension four. On
$\mathbb RP_v\oplus\Theta_v(U)$, taking trace first kills the
coefficient of $P_v$ for a kernel element, and the same inertia
argument kills the remaining direction. The homogeneous space has
real dimension five and is injectively mapped, just as required by
the original affine tangency convention. This is a derivative on actual
binary faces, without assuming a global differential structure on $P_N$.

If $m\ge4$, a triple outside every binary face must have three
independent lifted lines: a dependent triple would lie in the actual
support-two face already proved. Its support-three density face is
actual by Theorem 165.4 and is a full qutrit, proving L3. For the general
budget, at most $r$ lifted lines span dimension at most $r\le m-1$,
so (165.18) proves the assertion simultaneously at every $N$. ∎

The small-face assertions identify intrinsic positive cones, normalized
state spaces and their intrinsic affine effect intervals. They do not
assert that restriction of $R_N\cap[0,I_{D_N}]$ is onto such an
intrinsic interval at the same unit budget. Formula (165.4), including
the condition $E\in R_N$, remains the full original menu. In
particular the geometric budget theorem does not cover arbitrary tests
of restricted original effects, and it gives no formula for all-level
pure minima or pure PR. The single-level pure-minimum calculation of
Theorem 159.1 is not used to replace any higher-level menu.

**Theorem 165.6 (a finite original-neighbor mixture collapses the actual face at every level).**
For every $m\ge3$ and every $N\ge1$, let
$v_0=e_1^{\otimes N}$ and $p=\pi_NP_{v_0}$. Then

$$
F_N(p_N^\perp)=K_N.
\tag{165.23}
$$

In particular both NC and the proper-neighbor-face condition fail at
this pure point at every finite level, including $N=3$.

Proof. Use the standard tensor coordinate basis of $\mathbb C^{D_N}$.
For any coordinate vector
$w=e_{j_1}\otimes\cdots\otimes e_{j_N}\ne v_0$, choose a slot $\ell$ with $j_\ell\ne1$. Choose an index
$k$ of the opposite $H$ sign from $j_\ell$, with $k\ne1$.
There is such an index: each sign block has $m\ge3$ entries, so
excluding index 1 still leaves an opposite-sign choice when needed.
On this local slot set

$$
A_w=P_{e_{j_\ell}}+P_{e_k},\qquad
E_w=I_d^{\otimes(\ell-1)}\otimes A_w
                    \otimes I_d^{\otimes(N-\ell)}.
\tag{165.24}
$$

The two local projectors are distinct and orthogonal, so
$0\preceq A_w\preceq I_d$,
$\operatorname{Tr}(HA_w)=0$, $A_we_1=0$, and
$A_we_{j_\ell}=e_{j_\ell}$. Since $I_d\in R$, it follows that

$$
E_w\in R_N\cap[0,I_{D_N}],\qquad
E_wv_0=0,\qquad E_ww=w.
\tag{165.25}
$$

Thus every $q_w=\pi_NP_w$ is an original pure zero neighbor of
$p$: the original effect $I_{D_N}-E_w$ confirms $p$ and vanishes
at $q_w$. Its complement confirms $q_w$ and vanishes at $p$.
All these witnesses belong to the same full original menu (165.4) at
this level. They are allowed to vary with $w$; no common confirmer
or simultaneous measurement has been assumed.

Write $D=D_N$. The equally weighted mixture of these $D-1$ neighbors
has the density lift

$$
x=\frac1{D-1}\sum_{w\ne v_0}q_w=\pi_N\rho,\qquad
\rho=\frac{I_D-P_{v_0}}{D-1}.
\tag{165.26}
$$

Take the actual tensor-kernel direction

$$
Z=H\otimes P_{e_1}^{\otimes(N-1)}\in\mathcal N_N.
\tag{165.27}
$$

It has trace zero. For $0<t<1/(D-1)$ the diagonal matrix $\rho+tZ$
is positive definite: its formerly missing $v_0$ entry is $t>0$;
all other entries in the slice with slots $2,\ldots,N$ equal to
$e_1$ are $1/(D-1)+t$ or $1/(D-1)-t$, both positive; all
untouched entries are $1/(D-1)>0$. At $N=1$ the slice is the
whole coordinate basis and the same calculation applies. Its trace
is one and $\pi_N(\rho+tZ)=x$.

The restriction of $\pi_N$ from the trace-one affine hyperplane
onto $\{u_N=1\}$ is a surjective affine map, hence open. A positive
definite density has a neighborhood in that hyperplane contained in
the density set. Its image therefore belongs to $\operatorname{ri}K_N$.
Thus $x\in\operatorname{ri}K_N$. Any actual face containing the
neighbors contains their finite mixture $x$ and hence all of $K_N$:
for any $y\in K_N$, relative interior lets $x$ be an open-segment
point between $y$ and another point of $K_N$, and the face property
then includes $y$. This proves (165.23) directly using only original
effects and an explicit interior lift. ∎

**Theorem 165.7 (NC cannot be deleted from the three-copy candidate in the full finite background).**
In the unchanged original domain (161.1)–(161.3), the condition
that $K_3$ satisfy L2 and TC does not imply the proper-neighbor-face
condition or NC. Even requiring L2 and TC at every finite level does
not imply either condition at level 3, or at every level. For every
fixed finite geometric face budget $r$, there is one fixed-local-space
hierarchy satisfying that budget at every level while (165.23) holds
at every level.

Proof. Take the hierarchy of Definition 165.1. Theorem 165.2 supplies
the whole all-finite background; Theorems 165.4–165.5 supply the
actual faces and L2/TC, and Theorem 165.6 contradicts the desired
neighbor-face conclusion. For budget $r$, choose
$m\ge\max\{3,r+1\}$ once, before choosing $N$, and use this same
$V$ at all levels.

There is also a direct carrier obstruction to a full complex matrix
cone at level 3:

$$
\dim_{\mathbb R}V=4m^2-1,\qquad
\dim_{\mathbb R}W_3=(4m^2-1)^3.
\tag{165.28}
$$

Since $(2m-1)^2<4m^2-1<(2m)^2$, the local dimension is not a
square. Its cube is not a square either: if an integer cube is a
square, parity of prime exponents makes the integer itself a square.
A full complex Hermitian matrix cone has square real dimension. At
$m=3$, the dimensions are exactly $35$ and $35^3=42875$.
Consequently this whole $C_3$ is not linearly order isomorphic to
any full complex matrix cone. The actual-neighbor-face obstruction
(165.23) gives the explicit geometric failure in addition to this
dimension obstruction. ∎

The mathematical picture is that a quotient can leave every sufficiently
small support face intact while identifying mixtures of many different
pure points. 中文图景：把原态体看成由许多纯端点围成的整块凸体，每两端点之间的
完整三球及其切向接合都能原样保留，甚至任意预先规定数目的端点所生成的小面都
能保留；但固定一个端点后，全部能用原尺与它完全区分的邻点，仍可混成凸体内部的
一点。一张实际面只要含这个内部点，就不得不吞下整块凸体，也吞下原端点。
这里每一有限份数使用同一个局部商的张量幂，所有原尺、相关态、分组、交换和
重括号同时存在；缺失的是全局邻点面不塌缩这一关系，而非局部小球或其切方向。

The complete candidate $\mathsf G_3$ of §161.1 remains
L2 + TC + proper neighbor face; its existing correspondence in Theorem
161.5 and §161.10 retains exactly its stated suppliers and hypotheses.
The countermodel excludes the attempted deletion of its third clause;
it does not furnish a further reconstruction or a minimum independent
axiom set. The finite face-budget assertion is intrinsic state geometry,
not an assertion about unrestricted face-effect extensions. No
all-level pure PR or whole EB3 property is a conclusion here, and the
bare whole-EB3 + pure-PR reconstruction question of §160.7 remains
outside this countermodel. The construction supplies mathematical
ordered cones and their complete dual menus; physical realization,
available instruments and calibrated dynamics are additional questions.

Relative to Lemma 162.3 and Theorem 162.16, the intrinsic state-face
identifications here do not establish AD or DS at every finite level;
in particular, AD at level 3 has not been supplied. This hierarchy
separates L2 and TC from NC in the full finite background. It does not
remove NC from $\mathsf R_3=\mathrm{L2}_3+\mathrm{NC}_3+\mathrm{AD}_3$.

The new mathematical assertion is the joint all-finite construction
with its tensor-kernel bound, actual-face range and direct original
neighbor mixtures. The one-copy balanced quotient and its one-copy
pure minima already occur in Theorem 159.1; its TC specialization is
Theorem 160.7. The tensor sign-rank premise is proved here rather than
assumed from those one-copy statements. The general low-rank/inertia
criterion is mature background, attributed to [CHST165] and the existing
[literature note](../../../Library/HilbertOperators/carmeliheinosaarischultztoigo2014tasks.md).
Related tensor measurement arguments use kernel decompositions, phase
variation, compression and inertia [CHSTTensor165, §§III–V]; this is
method context, not a citation for the all-$N$ bound (165.9).
The construction and its geometric combination are `repo-derived`;
this describes the derivation and asserts no historical priority for
the tensor inertia argument or the construction. No Hermitian-cap classification,
conditional reconstruction supplier or propagation theorem is a premise
of Theorems 165.2–165.7.

[CHST165]: https://arxiv.org/pdf/1308.5502v2 "C. Carmeli, T. Heinosaari, J. Schultz and A. Toigo, Tasks and premises in quantum state determination, J. Phys. A 47 (2014), 075302; §4.1, Lemmas 1–2 and Theorem 1(a), DOI 10.1088/1751-8113/47/7/075302."
[CHSTTensor165]: https://arxiv.org/pdf/1411.0828v2 "C. Carmeli, T. Heinosaari, J. Schultz and A. Toigo, Expanding the Principle of Local Distinguishability, Phys. Rev. A 91 (2015), 042121; §§III–V, DOI 10.1103/PhysRevA.91.042121."

## 追加锚（本行以下为增补区）
