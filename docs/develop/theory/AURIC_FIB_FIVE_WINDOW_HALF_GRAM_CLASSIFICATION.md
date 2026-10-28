# AURIC FIB Five-Window Exceptional-Half Gram Classification

> This is a continuation of [Five-Window Quantum Memory][FW]. It is an
> appendable ordinary mathematical reference in the `generic-v1` structure.
> Incorporated text and numbering remain fixed; corrections and extensions
> follow the final append anchor and identify the statements they supersede.

## 1. Model, mathematical scope, and supplied results

**Convention 1.1 (The retained system and the meaning of mixing).** Throughout,
$H=\mathbb C^5$ has orthonormal basis $e_0,\ldots,e_4$, and
$\eta=1/2$. A single fixed complex-linear CPTP map $\Phi:M_5(\mathbb C)
\to M_5(\mathbb C)$ is iterated. Each application uses a fresh environment,
which is discarded. A reference is an arbitrary finite-dimensional external
system, untouched by the channel. Exact recovery, when mentioned, is a CPTP
operation after the last application. No environment, syndrome, feedback, or
history register is retained between applications. The statements are ordinary
finite-dimensional mathematics, without a Lean-kernel assertion. They make no
capacity, QFT, physical-realization, native-operation, or varying-channel claim.

A density is a positive matrix of trace one. A channel is *mixing* if there is
one density $\sigma$ such that $\Phi^n(X)\to\sigma\operatorname{Tr}X$ for
all complex $X\in M_5$. This definition includes transient inputs and their
cross terms with stationary supports. Nonmixing means the failure of this
property, rather than the failure of a uniform rate over a family of channels.
For a subspace $S$, $P_S$ is its orthogonal projection. An *enclosure* is a
subspace invariant under every Kraus operator, equivalently
$VS\subseteq S\otimes\mathcal E$ for an actual Stinespring isometry $V$.
A density supported on $S$ is faithful on $S$ when its restriction there is
strictly positive; faithfulness on all of $H$ is never assumed.

**Convention 1.2 (Ownership and the additional conclusion).** The complete
all-input lift model is [FW, Definition 2.2 and Theorems 4.1–4.2][FW]. Its
nonfaithful support and peripheral reductions are FW §32; its pure-line
obstruction, rank-four compression, and mixed-sector reductions are FW
Lemmas 33.1, 34.1, and 35.1. FW Theorem 36.1 distinguishes parameters admitting
some nonmixing lift, and proves mixing of every lift away from half. The
question here is finer: exactly which *individual actual complex Grams* at
half fail to mix?

The new ingredients are the U-type complementary-plane obstruction in Lemma
3.1 and the complete half-parameter factorization in Lemma 4.1. Theorem 5.1
combines them with the supplied reductions to answer that question. The
canonical construction, its two stationary sectors, conserved effect,
full-input limit, and finite-time NPT and code suppliers remain FW Definition
17.2 and Theorems 18.1, 18.3, 19.1–19.2, 20.2, and 21.2. Sections 6–7 give
the precise transfer of those facts to the classified family; they do not
attribute those canonical facts to the classification proof.

## 2. The actual complex Gram and its phase convention

**Definition 2.1 (All-input half lifts).** Set $q=1/\sqrt2$ and
$E_j=|e_j\rangle\langle e_j|$. An allowed channel satisfies

$$
\operatorname{diag}\Phi(X)=Q^{\mathsf T}\operatorname{diag}X
\quad\text{for every }X\in M_5(\mathbb C),\qquad
Q=\begin{pmatrix}
1/2&0&0&1/2&0\\
1/2&0&0&1/2&0\\
0&1/2&0&0&1/2\\
0&0&1&0&0\\
0&0&1&0&0
\end{pmatrix}.
\tag{2.1}
$$

The entry $Q_{ij}$ goes from input $i$ to output $j$.
In particular (2.1) is a condition on every non-Hermitian matrix unit, and
not just on the images of the five basis densities. Inner products are
conjugate-linear in the first argument; $\dagger$ denotes adjoint.

In the notation of FW (4.4), the actual common-environment isometry is

$$
\begin{aligned}
Ve_0&=q e_0\otimes\alpha_0+q e_3\otimes\beta_0,&
Ve_1&=q e_0\otimes\alpha_1+q e_3\otimes\beta_1,\\
Ve_2&=q e_1\otimes\gamma_0+q e_4\otimes\gamma_1,&
Ve_3&=e_2\otimes\delta_0,& Ve_4&=e_2\otimes\delta_1.
\end{aligned}
\tag{2.2}
$$

All eight vectors are unit vectors in the *same* complex Hilbert space
$\mathcal E$, with precisely the prescribed orthogonalities

$$
\alpha_0\perp\alpha_1,\qquad\beta_0\perp\beta_1,
\qquad\delta_0\perp\delta_1.
\tag{2.3}
$$

Other overlaps, including $\langle\gamma_0,\gamma_1\rangle$, are arbitrary
subject to one common PSD Gram matrix. No environment rank is specified.
The common span has dimension at most eight; arbitrary unused ambient
vectors do not change the channel. These are exactly the parameters in
FW Theorem 4.1: testing $Ve_i=\sum_j e_j\otimes e_{ji}$ on all matrix units
gives $\langle e_{ji'},e_{ji}\rangle=\delta_{ii'}Q_{ij}$, so zero edges
vanish and the nonzero edges give (2.2)–(2.3). Conversely those equations
make $V$ isometric and give (2.1) on all matrix units.

**Definition 2.2 (Ordered Gram, edge weights, and Choi block).** In this volume
use the order

$$
\begin{aligned}
f&=(\alpha_0,\alpha_1,\beta_0,\beta_1,
                    \gamma_0,\gamma_1,\delta_0,\delta_1),\\
\mathcal A&=((0,0),(0,1),(3,0),(3,1),(1,2),(4,2),(2,3),(2,4)),\\
w&=(q,q,q,q,q,q,1,1),\qquad G_{ab}=\langle f_a,f_b\rangle.
\end{aligned}
\tag{2.4}
$$

Thus $G\ge0$, $G_{aa}=1$, and, with one-based Gram indices,
$G_{12}=G_{34}=G_{78}=0$. The order $\mathcal A$ is the permutation
$(1,2,6,7,3,8,4,5)$ of FW's one-based order (4.3).
For the unnormalized output-first Choi matrix

$$
J_\Phi=\sum_{i,i'}\Phi(|e_i\rangle\langle e_{i'}|)
                         \otimes|e_i\rangle\langle e_{i'}|,
\qquad
(J_\Phi)_{\mathcal A_a,\mathcal A_b}=w_aw_bG_{ba}.
\tag{2.5}
$$

All other Choi rows and columns vanish. In particular the active block is
$\operatorname{diag}(w)\overline G\operatorname{diag}(w)$, not
$\operatorname{diag}(w)G\operatorname{diag}(w)$.
This follows because the environment trace of
$|f_a\rangle\langle f_b|$ is $\langle f_b,f_a\rangle$.
All weights are positive, so Gram rank and Choi rank agree. The orthogonal
pairs force rank at least two. These conventions retain the complex
conjugation in FW (4.6); they merely permute the edges.

**Definition 2.3 (Canonical channel and the four-phase template).** Put

$$
\begin{aligned}
u&=q(e_0+e_3),&v&=q(e_1+e_4),&z&=e_2,\\
R_3&=\operatorname{span}\{u,v,z\},&s&=(u+v+z)/\sqrt3,\\
K_0&=|u\rangle\langle e_0|+q|v\rangle\langle e_2|
                                  +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+q|v\rangle\langle e_2|
                                  +|z\rangle\langle e_3|,\\
\Phi_\circ(X)&=K_0XK_0^\dagger+K_1XK_1^\dagger.
\end{aligned}
\tag{2.6}
$$

This is FW Definition 17.2. For an orthonormal environment pair $f_0,f_1$,
let $c=q(f_0+f_1)$. The canonical ordered vector list is
$(f_0,f_1,f_0,f_1,c,c,f_1,f_0)$, so its Gram is

$$
B=\begin{pmatrix}1&0&1&0&q&q&0&1\\0&1&0&1&q&q&1&0\end{pmatrix},
\qquad G^\circ=B^\dagger B.
\tag{2.7}
$$

For $t_j\in\mathbb C$, $|t_j|=1$, set

$$
\begin{aligned}
D&=\operatorname{diag}(t_0,t_1,t_2,t_3,t_4),\\
\chi&=(1,t_0\overline{t_1},t_3\overline{t_0},t_3\overline{t_1},
 t_1\overline{t_2},t_4\overline{t_2},t_2\overline{t_3},t_2\overline{t_4}).
\end{aligned}
\tag{2.8}
$$

The *template condition* is equality of the entire actual Gram:

$$
G_{ab}=\overline{\chi_a}\chi_bG^\circ_{ab}
\qquad(1\le a,b\le8).
\tag{2.9}
$$

For an explicitly four-phase form, set $t_0=1$ and
$(t_1,t_2,t_3,t_4)=(A,B_1,C,D_1)$, all of modulus one. Then

$$
\chi=(1,A^{-1},C,CA^{-1},AB_1^{-1},D_1B_1^{-1},
                                  B_1C^{-1},B_1D_1^{-1}).
\tag{2.10}
$$

The symbols $B_1,D_1$ here are phases, not the matrix $B$ or an operator.
The literal zero entries of $G^\circ$ remain zero in (2.9). The condition
is not a list of modulus tests and does not permit independently chosen
overlap phases.

## 3. The complementary-plane obstruction

**Lemma 3.1 (No U-type stationary or swapped pair at half).** Suppose two
orthogonal two-dimensional subspaces $S_0,S_1$ carry densities faithful on
their respective supports, both with diagonal

$$
p=(1,1,2,1,1)^{\mathsf T}/6,
\tag{3.1}
$$

and $\Phi(\rho_a)=\rho_{\tau(a)}$, where $\tau$ is the identity or the swap.
Such a pair is impossible for an allowed half lift, without a restriction
on the rank or phases of its actual Gram.

Proof. Their mean is a stationary density with rank-four support
$R=S_0\oplus S_1$. FW Lemma 34.1 applies to exactly this density and this
actual isometry: the output compression holds on *all* $H$, not merely on
$R$. Its two possible diagonal gauges are U and V in FW (34.1). FW Lemma
35.1 excludes V for stationary and swapped sectors alike. Here is the
compressed-effect consequence of that lemma needed for U, including its
hypotheses.

Let $P_a=P_{S_a}$ and $b=\tau(a)$. Invariance of the supports gives a CPTP
restriction $T_a:\mathcal B(S_a)\to\mathcal B(S_b)$. Its adjoint is positive
and unital between these two identities. Each $P_ae_j$ is nonzero, because
$\langle e_j,\rho_a e_j\rangle=p_j>0$. Compress the full-input identities
$\Phi^\dagger(E_1)=\Phi^\dagger(E_4)=E_2/2$:

$$
T_a^\dagger(P_bE_1P_b)=T_a^\dagger(P_bE_4P_b)
                                      =\tfrac12P_aE_2P_a.
\tag{3.2}
$$

If $P_be_1,P_be_4$ were independent, the sum of their rank-one effects
would dominate $\epsilon I_{S_b}$ for some $\epsilon>0$. Its image under
the positive unital $T_a^\dagger$ would dominate $\epsilon I_{S_a}$,
whereas (3.2) makes that image rank one. Thus the two nonzero effects are
proportional. Equation (3.2) fixes their positive proportionality constant
to one. Consequently, on each sector,

$$
P_a(E_1-E_4)P_a=0.
\tag{3.3}
$$

No unitality of the Schrödinger map has been assumed.

In the U gauge write $x=e_1$, $y=e_2$, $w=e_4$. Then

$$
R=\operatorname{span}\{u,x,y,w\},\qquad
L=\operatorname{span}\{u,y\},\quad N=\operatorname{span}\{x,w\},
\quad R=L\oplus N,
\tag{3.4}
$$

and $\beta_i=\alpha_i$. Restricting the *actual* isometry (2.2) gives

$$
\begin{aligned}
Vu&=q u\otimes\alpha_0+q y\otimes\delta_0,&
Vx&=u\otimes\alpha_1,\\
Vy&=q x\otimes\gamma_0+q w\otimes\gamma_1,&
Vw&=y\otimes\delta_1.
\end{aligned}
\tag{3.5}
$$

In particular $Vu\in L\otimes\mathcal E$ has norm one and
$Vy\in N\otimes\mathcal E$. No unspecified environment overlap has
been set to zero in these equations.

On $R$ put $J=P_0-P_1$ and $D_0=|x\rangle\langle x|-|w\rangle\langle w|$.
By (3.3), $D_0$ has zero diagonal blocks for $S_0\oplus S_1$, so
$JD_0=-D_0J$. Hence $J$ commutes with $D_0^2=P_N$, and both $P_a$
reduce $L$ and $N$. On $N$, a self-adjoint unitary anticommuting with
$\operatorname{diag}(1,-1)$ has the form

$$
J|_N=\begin{pmatrix}0&\omega\\\overline\omega&0\end{pmatrix},
\qquad |\omega|=1.
\tag{3.6}
$$

It has one eigenline of each sign. Each $S_a$ has dimension two;
therefore $L_a=S_a\cap L$ is a line, and $L_0\perp L_1$ exhaust $L$.
Choose a unit generator $h_a=A_a u+B_a y$ of $L_a$. Since
$P_Re_0=qu$ and $P_ae_0\ne0$, the reduction just established implies
$P_au\ne0$, so $A_a\ne0$ for *both* $a$.

Transport of the source sectors gives $Vh_a\in S_{\tau(a)}\otimes\mathcal E$.
Projecting its system output onto $L$, which commutes with the target
sector projection, and using (3.5) yields

$$
(P_L\otimes I)Vh_a=A_aVu\in L_{\tau(a)}\otimes\mathcal E.
\tag{3.7}
$$

Divide by the nonzero $A_a$. Both source sectors put the same $Vu$ in
both orthogonal target-line tensor spaces. This is true for either
permutation $\tau$. Their intersection is zero, contradicting
$\|Vu\|=1$. Together with the supplied V exclusion this proves the lemma.
The only divisions in this new obstruction are by coordinates made
nonzero by actual positive populations. Literal Gram zeros, arbitrary
complex $\omega$, nonminimal environments, and every allowed Gram rank
remain included. $\square$

## 4. A pure line determines all eight environment vectors

**Lemma 4.1 (Full-input factorization from an orthogonal stationary pair).**
If an allowed half lift has a pure stationary density and an orthogonally
supported stationary density, then a diagonal unitary conjugation makes
its entire actual environment list equal to that in (2.7), up to an
isometry of the common environment span. In particular the conclusion
fixes the channel on all of $H$, including transient inputs, and not just
on the stationary supports.

Proof. The stationary population is (3.1), by FW §32, so all coordinates
of a stationary pure vector $\psi$ are nonzero. A diagonal gauge makes
$\psi=s$ from (2.6). Let $S\ne0$ be the orthogonal stationary support.
It is an enclosure by FW (32.2). Purity gives $Vs=s\otimes c$ for a unit
$c\in\mathcal E$. Comparing the five output coordinates in (2.2) yields

$$
\gamma_0=\gamma_1=c,\qquad
q(\alpha_0+\alpha_1)=q(\beta_0+\beta_1)
                         =q(\delta_0+\delta_1)=c.
\tag{4.1}
$$

The three orthonormal pairs can therefore be written, in this very same
environment, with unit $a,b,d_{\mathcal E}\perp c$ as

$$
\begin{aligned}
\alpha_0&=q(c+a),&\alpha_1&=q(c-a),\\
\beta_0&=q(c+b),&\beta_1&=q(c-b),\\
\delta_0&=q(c+d_{\mathcal E}),&\delta_1&=q(c-d_{\mathcal E}).
\end{aligned}
\tag{4.2}
$$

No mutual overlap of $a,b,d_{\mathcal E}$ has been assumed. Use the
half specialization of the supplied decomposition FW (33.4)–(33.5):

$$
\begin{aligned}
h_A&=q(e_0+e_1),&h_D&=q(e_3+e_4),\\
l_A&=q(e_0-e_1),&l_D&=q(e_3-e_4),\\
K&=|u\rangle\langle h_A|+|v\rangle\langle z|
                                      +|z\rangle\langle h_D|,\\
x_A&=\langle l_A,x\rangle,&x_D&=\langle l_D,x\rangle,\\
Vx&=Kx\otimes c+Wx,\\
Wx&=x_A(qe_0\otimes a+qe_3\otimes b)+x_Dz\otimes d_{\mathcal E}.
\end{aligned}
\tag{4.3}
$$

Here $Ks=K^\dagger s=s$ and
$K^\dagger K=P_{\operatorname{span}\{h_A,z,h_D\}}$.
The environment components along $c$ and perpendicular to $c$ in
$VS\subseteq S\otimes\mathcal E$ separately give $KS\subseteq S$ and
$WS\subseteq S\otimes\mathcal E$. Projection of the latter onto $s$
gives, with the nonzero common factor $1/\sqrt3$ removed,

$$
\tfrac12(a+b)x_A+d_{\mathcal E}x_D=0\qquad(x\in S).
\tag{4.4}
$$

The possibility that $x_A$ vanishes on all $S$ must be disposed of first.
Then (4.4), because $d_{\mathcal E}$ is unit, makes $x_D$ vanish there
as well; hence $W|_S=0$. Since $V$ is isometric and $KS\subseteq S$,
$K|_S$ would be a finite-dimensional unitary. But the supplied polynomial
in FW §33 specializes to

$$
\det(\lambda I-K)=\lambda^3(\lambda+1/2)(\lambda-1),
\qquad\ker(K-I)=\mathbb Cs.
\tag{4.5}
$$

For completeness, the eigenline assertion also follows from
$K^\dagger K$ above: a unit-modulus eigenvector belongs to
$\operatorname{span}\{h_A,z,h_D\}$. Writing it $x h_A+y z+t h_D$,
the coordinate-0 equation gives eigenvalue one if $x\ne0$; the other
coordinates then give $x=y=t$. If $x=0$, the coordinate-3 and
coordinate-2 equations force $t=y=0$. Thus every unit-modulus eigenvector
is in $\mathbb Cs$, inconsistent with $S\subseteq s^\perp$.

There is consequently an $x\in S$ with $x_A\ne0$. Equation (4.4) fixes
one complex scalar $t$, independent of $x$, such that

$$
(a+b)/2=t d_{\mathcal E},\qquad x_D=-t x_A\quad(x\in S).
\tag{4.6}
$$

The functional $L_t=t\langle l_A|+\langle l_D|$ annihilates $S$.
Equation (4.3) and the chosen nonzero $x_A$ put

$$
F=qe_0\otimes a+qe_3\otimes b-tz\otimes d_{\mathcal E}
                                                   \quad\text{in }S\otimes\mathcal E.
\tag{4.7}
$$

Applying $L_t\otimes I$ gives $(ta+b)/2=0$. Thus $t\ne0$,
$b=\beta a$ for a unit phase $\beta$, and $t=-\beta$. Substitution of
(4.6) into (4.7) gives $F=w_\beta\otimes a$, where

$$
w_\beta=qe_0+q\beta e_3-(1+\beta)z/2\in S.
\tag{4.8}
$$

No division by $1+\beta$ has been made. Since $Kw_\beta\in S$,
applying the annihilating functional gives the exact factorization

$$
0=L_tKw_\beta=\tfrac12(1-\beta)(1+\beta/2).
\tag{4.9}
$$

The second factor cannot vanish for $|\beta|=1$. Hence
$\beta=1$, $t=-1$, and (4.6) yields $d_{\mathcal E}=-a$.
The orthonormal pair $f_0=q(c+a)$, $f_1=q(c-a)$ now makes (4.1)–(4.2)
exactly

$$
(\alpha_0,\alpha_1,\beta_0,\beta_1,\gamma_0,\gamma_1,\delta_0,\delta_1)
=(f_0,f_1,f_0,f_1,q(f_0+f_1),q(f_0+f_1),f_1,f_0).
\tag{4.10}
$$

These are all columns of (2.2), including columns outside the recurrent
support. The argument handled the vanishing-functional case before any
division, ruled out $t=0$, and included $\beta=-1$ and arbitrary complex
phases. It is the stronger full-input conclusion of the pure-line
calculation, rather than an assumption that a pure fixed state existed.
$\square$

## 5. Necessary and sufficient classification of every half Gram

**Theorem 5.1 (The exact exceptional-half class).** For every allowed actual
complex Gram in Definition 2.2, the following five assertions are equivalent:

1. $\Phi$ is nonmixing on the full complex algebra $M_5$.
2. $\Phi$ has at least two stationary densities.
3. $\Phi$ has a pure stationary density and an orthogonally supported
   stationary density.
4. For a diagonal unitary $D$,
   $\Phi=\operatorname{Ad}_D\circ\Phi_\circ\circ\operatorname{Ad}_{D^\dagger}$,
   where $\operatorname{Ad}_D(X)=DXD^\dagger$.
5. The complete actual Gram satisfies (2.9).

The diagonal unitary in assertion 4 is unique modulo a scalar phase. Thus
the class is exactly the four-phase orbit (2.10). Every member has Gram
and Choi rank two, and its joint stationary support has dimension three.
Every allowed Gram outside (2.9) mixes, at every compatible rank and with
arbitrary complex phases or literal zero entries. In particular rank
greater than two implies mixing, while rank two alone is insufficient.
The mixing conclusion holds with every untouched finite reference and
includes all transient inputs.

Proof. We first establish exhaustion of the stationary and peripheral
possibilities, using the actual supports rather than a faithful state on
$H$. The needed supplied results and their hypothesis correspondence are
spelled out below.

By FW §32, the unique stationary probability for $Q$, and for each $Q^m$,
is (3.1). For example, $Q^4$ has all entries positive, and
$(Q^m)^4=(Q^4)^m$ also has all entries positive. Hence each $\Phi^m$-fixed
density has diagonal $p$. All five populations used in the reductions
are consequently positive, even when the density has deficient rank.

For any stationary $\rho$, its support is an enclosure: if $y$ is
orthogonal to the support, positivity and a Kraus representation give

$$
0=\langle y,\Phi(\rho)y\rangle
 =\sum_\ell\|\rho^{1/2}K_\ell^\dagger y\|^2,
\quad K_\ell\operatorname{supp}\rho\subseteq\operatorname{supp}\rho.
\tag{5.1}
$$

Conversely, every nonzero enclosure supports a stationary density by
Cesàro compactness. These are exactly FW (32.2), or Burgarth et al.,
Lemma 2 [MIX]. If two stationary densities differ, take the positive
and negative Jordan parts $D_+,D_-$ of their traceless Hermitian
difference. Trace preservation and trace-norm contraction give equality in

$$
\|D_+-D_-\|_1
=\|\Phi(D_+)-\Phi(D_-)\|_1
\le\operatorname{Tr}\Phi(D_+)+\operatorname{Tr}\Phi(D_-).
\tag{5.2}
$$

For positive matrices equality means orthogonal supports: the positive
spectral projection of their difference in the trace-norm variational
formula must contain the first support and annihilate the second.
Uniqueness of Jordan parts therefore makes $D_+,D_-$ themselves fixed.
Their normalizations are orthogonally supported stationary densities.
This is FW (32.3), supplied generally by Burgarth et al., Lemma 1 and
Corollaries 1–2 [MIX]; it requires neither global faithfulness nor a pure
fixed state. Applying the same argument to Hermitian real and imaginary
parts of an arbitrary fixed operator shows that uniqueness of a stationary
density $\sigma$ implies $\operatorname{Fix}(\Phi)=\mathbb C\sigma$.

Suppose first that there are two stationary densities. Replace them by
this orthogonally supported pair. If neither support is a line, their
dimensions in $H$ can only be $2+2$ or $2+3$. For $2+3$, FW Lemma 35.1
applies with $\tau$ the identity, faithful densities on their actual
supports, and common diagonal $p$; it excludes that case. To recall why
complete exhaustion matters here, let $P_a$ be the rank-two source
projection and $P_b$ its target projection. Because the two sectors fill
$H$, their transport laws give $VP_a=(P_b\otimes I)V$. Thus

$$
VP_ae_3=(P_be_2)\otimes\delta_0,\qquad
VP_ae_4=(P_be_2)\otimes\delta_1.
\tag{5.3}
$$

Both are nonzero, orthogonal, and of equal norm. They come from a basis
of the source plane, so its whole output has system support in the one
line $\mathbb CP_be_2$, contrary to target faithfulness in dimension at
least two. This works for the identity and for a swap, regardless of
which of the two dimensions is the target dimension. For $2+2$, Lemma
3.1 now excludes both possible rank-four compressions. It follows that
one stationary support is a line. This proves assertion 2 implies
assertion 3, and Lemma 4.1 proves assertion 3 implies assertion 4.

It remains essential to exclude a uniquely stationary but periodic
channel. This cannot be bypassed by presupposing two fixed states.
Let $\sigma$ be the unique stationary density and
$R=\operatorname{supp}\sigma$. For a peripheral eigenoperator
$\Phi(A)=\lambda A$, $|\lambda|=1$, write $A=U B_0$ with
$B_0=|A|$, extending the polar partial isometry to a unitary on $H$.
The nonfaithful polar argument in FW (32.4), also Burgarth et al.,
Theorem 5 and Remark 4 [MIX], can be applied before any restriction:
with $X_\ell=K_\ell U\sqrt{B_0}$ and
$Y_\ell=UK_\ell\sqrt{B_0}$, trace preservation gives

$$
\begin{aligned}
\sum_\ell\|X_\ell\|_2^2
 &=\sum_\ell\|Y_\ell\|_2^2=\operatorname{Tr}B_0,\\
\sum_\ell\langle Y_\ell,X_\ell\rangle
 &=\operatorname{Tr}(U^\dagger\Phi(A))
 =\lambda\operatorname{Tr}B_0.
\end{aligned}
\tag{5.4}
$$

Equality in Cauchy–Schwarz gives $X_\ell=\lambda Y_\ell$ for every
$\ell$. Right multiplication by $\sqrt{B_0}$ and the Kraus sum give
$\Phi(A)=\lambda U\Phi(B_0)$, so $\Phi(B_0)=B_0$.
Applying this also to $A^\dagger$ makes $|A^\dagger|$ stationary.
Uniqueness implies both moduli are the same positive scalar multiple
of $\sigma$. Hence $A=P_RAP_R$, its polar unitary on $R$ commutes with
$\sigma$, and invertibility on that support gives

$$
K_\ell U=\lambda UK_\ell\quad\text{on }R.
\tag{5.5}
$$

The restriction to $R$ is faithful and irreducible: a proper nonzero
enclosure would have another stationary density. This is where faithful
irreducible hypotheses enter, only on $R$. It is also the precise domain
on which the adjoint restriction meets the hypotheses of Carbone–Jenčová,
Proposition 5 and Corollary 2 [CYCLE].

For clarity, the cyclic sectors needed from that result follow directly
from (5.5). If $\mu$ is an eigenvalue of $U$, TP implies every nonzero
vector in its eigenspace has a nonzero image under at least one Kraus
operator. That image has eigenvalue $\lambda^{-1}\mu$. Thus the finite
spectrum is closed under this rotation and $\lambda$ is a root of
unity. A union of a rotation orbit is an enclosure, so irreducibility
forces just one orbit. For $\lambda\ne1$ there are $m\ge2$ orthogonal
spectral sectors $R_a$, and every Kraus operator maps $R_a$ into
$R_{a+1}$, cyclic indices. Their projections commute with $\sigma$;
stationarity gives

$$
\Phi(P_{R_a}\sigma P_{R_a})=P_{R_{a+1}}\sigma P_{R_{a+1}}.
\tag{5.6}
$$

The block traces are equal and positive. Normalizing gives faithful
cyclic densities $\rho_a$ of diagonal $p$, since each is $\Phi^m$-fixed.
This is the specific cyclic conclusion of FW (32.5)–(32.6); no faithful
stationary state on $H$ has been introduced.

A cycle containing a line forces every sector to be a line. Indeed, if
the target is $\mathbb C\psi_b$ with $\|\psi_b\|=1$, the isometry on its
predecessor is $Vx=\psi_b\otimes W x$, where $W$ is isometric. The
coordinate-1 equation of the actual (2.2) is

$$
q x_2\gamma_0=(\psi_b)_1 W x.
\tag{5.7}
$$

The left-hand side has rank at most one as a linear map of $x$, and
the right-hand side has rank equal to the predecessor dimension, because
$|(\psi_b)_1|^2=p_1>0$. Repeat backwards around the cycle. If $\psi_a$
are its unit vectors, (5.7) makes the environment factors in
$V\psi_a=\psi_{a+1}\otimes c_a$ unit-phase multiples of the *same*
$\gamma_0$, since $q^2p_2=p_1$. Thus the whole cyclic span has channel
restriction $\operatorname{Ad}_{U_{\mathrm{cyc}}}$ for a cyclic unitary.
It has at least two orthogonal stationary eigenstate projectors when
$m\ge2$, contradicting uniqueness. This uses the line argument in
FW Theorem 36.1 with exactly the same actual coordinate equation.

Every remaining cyclic sector has dimension at least two. Total dimension
at most five leaves only two sectors of dimensions $2+2$ or $2+3$, now
transported by a swap. The supplied mixed-sector exclusion (5.3) and
Lemma 3.1 exclude these too. Therefore a unique stationary density cannot
coexist with any $\lambda\ne1$ on the unit circle.

Finally CPTP powers are bounded on the full complex algebra. The adjoint
is a unital CP map and an operator-norm contraction by its isometric
dilation; trace-norm duality gives a trace-norm contraction on complex
inputs as well. Hence unit-circle Jordan blocks are semisimple. If the
stationary density were unique, the preceding argument and
$\operatorname{Fix}(\Phi)=\mathbb C\sigma$ would leave a simple
peripheral eigenvalue one. All other modes decay, and trace preservation
identifies the limiting rank-one map as $X\mapsto\sigma\operatorname{Tr}X$.
This is mixing on *all* $M_5$, including the transient blocks. Thus
assertion 1 implies assertion 2. Assertion 2 also directly obstructs
mixing by applying its alleged single reset limit to the two fixed
densities.

The canonical channel fixes the orthogonal densities
$P=|s\rangle\langle s|$ and $M=(P_{R_3}-P)/2$, by FW Theorem 18.1.
Consequently it and every diagonal conjugate are nonmixing. Together
with the implications just proved, this establishes equivalence of
assertions 1–4.

To translate to the *actual Gram*, conjugate the canonical dilation on
output by $D$ and on input by $D^\dagger$. The vector on edge $(j,i)$
is multiplied by $t_j\overline{t_i}$, exactly the corresponding $\chi_a$
in (2.8). This proves (2.9) for assertion 4. Conversely, if (2.9) holds,
the actual list and the list $\chi_a f_a^\circ$ have identical Grams.
The map sending the latter list to the former preserves the norm of
every linear combination, so is well-defined and isometric on their
spans. It intertwines the two full Stinespring isometries. Taking the
environment trace gives assertion 4 on every complex input. This proves
assertions 4 and 5 equivalent without dividing by any Gram entry.

The template span has dimension two. The canonical stationary density
family is exactly $tP+(1-t)M$, $0\le t\le1$, as shown in FW §19 (or by
the recurrent commutant calculation in §6 below). Its only pure member
is $P$, and the union of stationary supports is $R_3$. A diagonal unitary
stabilizing the canonical channel must preserve $\mathbb Cs$. Since all
five coordinates of $s$ are nonzero, that unitary is a scalar. Therefore
two gauges giving the same channel differ only by a scalar phase.
All five claims about rank, support, and four independent phases follow.
Minimal environments differ by a common unitary on their two-dimensional
spans; additional ambient dimensions are unused. Independent input-column
rephasing without the corresponding output conjugation is not a further
channel equivalence.

Reference convergence is proved in §6 using full matrix-unit convergence,
which has already been established here on both sides of the classification.
The rank-two insufficiency has the explicit independent proof in
Proposition 8.1. Neither point adds a stationary or peripheral hypothesis.
$\square$

## 6. Recurrent algebra, full-space observables, and transient feeding

**Corollary 6.1 (The complete limit for every nonmixing half lift).** Suppose
$\Phi$ satisfies the equivalent conditions of Theorem 5.1, and let $D$ be
its diagonal gauge. First use the canonical gauge $D=I$ and define

$$
\begin{aligned}
P&=|s\rangle\langle s|,& M&=(P_{R_3}-P)/2,\\
d&=(e_0-e_1-e_3+e_4)/2,&
E&=P+\tfrac23|d\rangle\langle d|.
\end{aligned}
\tag{6.1}
$$

Then the whole stationary density family is
$\{tP+(1-t)M:0\le t\le1\}$, the only peripheral eigenvalue is one,
and the full peripheral operator space is $\operatorname{span}\{P,M\}$.
The full-input limit is

$$
\begin{aligned}
T(X)&=P\operatorname{Tr}(EX)
                    +M\operatorname{Tr}((I_H-E)X),\\
\Phi_\circ^n(X)&\longrightarrow T(X)\qquad(X\in M_5),\\
T&=(\Phi_\circ^2+2\Phi_\circ^3)/3,\\
\Phi_\circ^n-T&=(-1/2)^{n-2}(\Phi_\circ^2-T)\qquad(n\ge2),\\
\|\Phi_\circ^n-T\|_\diamond
 &\le\tfrac43\,2^{-(n-2)}\qquad(n\ge2).
\end{aligned}
\tag{6.2}
$$

On the recurrent support $R_3$, the ordinary fixed-observable algebra is
$\mathbb CP\oplus\mathbb C(P_{R_3}-P)\cong\mathbb C\oplus\mathbb C$.
On the full $H$, the fixed-observable space is the operator system
$\operatorname{span}\{I_H,E\}$; it is not closed under ordinary operator
multiplication, and $E$ is not a projection. For general $D$, conjugate
every state, support, effect, and limiting map above by $D$.

For an arbitrary finite reference $\mathcal K$ and every complex
$Z\in\mathcal B(H\otimes\mathcal K)$, the canonical limiting output is

$$
(T\otimes\mathrm{id}_{\mathcal K})(Z)
=P\otimes\operatorname{Tr}_H[(E\otimes I)Z]
 +M\otimes\operatorname{Tr}_H[((I_H-E)\otimes I)Z].
\tag{6.3}
$$

The convergence is in diamond norm. On the mixing side of Theorem 5.1,
the corresponding limit is $\sigma\otimes\operatorname{Tr}_H Z$, also
in diamond norm. No projection onto $R_3$ of the initial input is required.

Proof. These are the transfer of the canonical suppliers FW Theorems
18.1, 18.3, and 19.1–19.2 through the exact conjugacy in Theorem 5.1.
The following correspondence also makes explicit the distinction between
the recurrent algebra and the full-space extension.

Every output of (2.6) is supported on $R_3$. In its ordered basis $(u,v,z)$,
the restricted Kraus operators are $qU_0,qU_1$, with

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},
\qquad U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix}.
\tag{6.4}
$$

Thus $F=\Phi_\circ|_{\mathcal B(R_3)}$
is $(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{U_1})/2$.
The two permutations fix $s$, so they fix $P$ and $M$. If
$F(A)=\lambda A$ with $|\lambda|=1$, equality in the Hilbert–Schmidt
norm of an average of two equal-norm vectors forces
$U_0AU_0^\dagger=U_1AU_1^\dagger=\lambda A$.
Since $U_0^2=I$ and $U_1^3=I$, one has
$\lambda^2=\lambda^3=1$, hence $\lambda=1$. The permutations generate
$S_3$. A matrix commuting with them has constant diagonal entries and
constant ordered off-diagonal entries, because those are the two orbits
of the simultaneous action on its indices. Their commutant is therefore
$\operatorname{span}\{P,P_{R_3}-P\}$. The adjoint has the same fixed
space, either by its inverse permutations or the same norm equality.
This is the canonical recurrent calculation underlying FW §§18–19.

Every full-input eigenoperator of nonzero eigenvalue lies in
$\mathcal B(R_3)$, since $A=\lambda^{-1}\Phi_\circ(A)$.
Thus there are no additional peripheral transient eigenoperators.
Positive normalized elements of this fixed space are exactly
$tP+(1-t)M$; the unique pure member is $P$.

The effect in FW Theorem 18.3 uses precisely the unit vector $d$ in (6.1).
It satisfies $d\perp R_3$. To see the full-input rather than just the
compressed effect, the adjoint Kraus images are

$$
\begin{aligned}
h_0=K_0^\dagger s&=(e_0+e_4)/\sqrt3+e_2/\sqrt6,\\
h_1=K_1^\dagger s&=(e_1+e_3)/\sqrt3+e_2/\sqrt6,\\
\Phi_\circ^\dagger(P)
 &=|h_0\rangle\langle h_0|+|h_1\rangle\langle h_1|
 =P+\tfrac23|d\rangle\langle d|=E.
\end{aligned}
\tag{6.5}
$$

In particular $0\le E\le I_H$, with eigenvalues $1,2/3,0,0,0$.
Its compression to $R_3$ is $P$, so full output support in $R_3$ gives
$\Phi_\circ^\dagger(E)=\Phi_\circ^\dagger(P)=E$.
The signs and normalization of $d$ in (6.1) are essential to both identities.

The supplied full-superoperator identities, FW Theorem 19.1, are

$$
\begin{aligned}
\det(tI-\Phi_\circ)&=t^{20}(t-1)^2(t+1/2)^3,\\
\Phi_\circ^2(\Phi_\circ-\mathrm{id})
                    (\Phi_\circ+\tfrac12\mathrm{id})&=0.
\end{aligned}
\tag{6.6}
$$

They act on all 25 complex matrix units, including the zero-mode
transient. The annihilating polynomial gives the polynomial $T$ and
recurrence in (6.2). Its limiting range is $\operatorname{span}\{P,M\}$.
Conservation of $E$ gives the coefficient of $P$, since
$\operatorname{Tr}(EP)=1$ and $\operatorname{Tr}(EM)=0$;
trace preservation gives the coefficient of $M$. This proves the first
line of (6.2) on every complex input, including initial off-diagonal
blocks meeting $R_3^\perp$. In particular an initial state on
$\mathbb Cd$ feeds the $P$ sector with weight $2/3$, not zero.
The norm bound is exactly FW Theorem 19.2: the identity
$\Phi_\circ^2-T=(2/3)(\Phi_\circ^2-\Phi_\circ^3)$ and channel diamond
norm one give $\|\Phi_\circ^2-T\|_\diamond\le4/3$.

The adjoint of the full-input limit is

$$
T^\dagger(Y)=E\operatorname{Tr}(PY)
                   +(I_H-E)\operatorname{Tr}(MY).
\tag{6.7}
$$

Its range is exactly $\operatorname{span}\{I_H,E\}$, hence the full-space
fixed-observable system is that space. If $E^2=aI_H+bE$, restriction to
$\ker E$ gives $a=0$, restriction to $\mathbb Cs$ gives $b=1$, and
restriction to $\mathbb Cd$ would assert $4/9=2/3$, a contradiction.
Thus the full-space system is not an ordinary algebra. Under the
Choi–Effros product $A\circ B=T^\dagger(AB)$ it is the same abstract
two-scalar algebra: $E\circ E=E$ and $E\circ(I_H-E)=0$.
The ordinary recurrent algebra has unit $P_{R_3}$, whereas the full-space
operator system has unit $I_H$. This is the concrete fixed-point-support
and extension distinction in Blume-Kohout et al., Theorem 5 [IPS], not an
inference of a full-space commutant from a faithful classical population.
The rank-two sector $R_3\cap s^\perp$ carries one stationary density
$M$, not a persistent matrix algebra $M_2$.

Tensoring the full map proves (6.3). To include arbitrary finite
references also on the mixing side, there is a useful elementary bound.
For any linear map $L:M_5\to M_5$ and
$Z=\sum_{ij}|e_i\rangle\langle e_j|\otimes Z_{ij}$,

$$
\|(L\otimes\mathrm{id})(Z)\|_1
\le \max_{ij}\|L(|e_i\rangle\langle e_j|)\|_1
                                \sum_{ij}\|Z_{ij}\|_1
\le5\max_{ij}\|L(|e_i\rangle\langle e_j|)\|_1\,\|Z\|_1.
\tag{6.8}
$$

For the last inequality, use an SVD of $Z$. A rank-one term
$|a\rangle\langle b|$ has blocks $|a_i\rangle\langle b_j|$ and
$\sum_{ij}\|a_i\|\|b_j\|\le5\|a\|\|b\|$ by Cauchy–Schwarz;
summing its singular values gives the bound. It is independent of
reference dimension. Apply it to $L=\Phi^n-T$ or
$L=\Phi^n-\mathcal R_\sigma$, as appropriate. Full matrix-unit
convergence therefore gives the asserted diamond convergence. The
nonmixing limit is measure-and-prepare with POVM $\{E,I_H-E\}$ and
prepared states $P,M$, hence is entanglement breaking. These claims
concern a limit of powers of one fixed channel. $\square$

## 7. What the classification transfers about finite memory

**Corollary 7.1 (Classical sectors, finite NPT, and terminal codes).** Every
nonmixing half lift has a perfectly distinguishable permanent classical
two-sector label, while every finite iterate is non-entanglement-breaking.
These statements coexist with the entanglement-breaking limit in
Corollary 6.1. Its maximal exactly correctable complex subspace dimensions,
with terminal recovery as in Convention 1.1, are

$$
(k_0,k_1,k_2,k_3,k_4,\ldots)=(5,3,2,1,1,\ldots).
\tag{7.1}
$$

The canonical NPT witness and restricted-code facts used here are FW
Theorem 20.2 and Theorem 21.2. The classification transfers them by one
fixed diagonal conjugation to every nonmixing member; this does not add a
quantum-capacity conclusion or an intermediate operation.

Proof. It suffices to use $D=I$. Encode the classical label by $P$ and
any density supported on $R_3\cap s^\perp$. Both supports are invariant
under the Kraus operators in (6.4); the terminal POVM $\{P,I_H-P\}$
distinguishes their labels perfectly after any number of steps.
This is a two-scalar label, consistently with §6, and not a passive
noncommuting qubit algebra.

For the finite entanglement witness, take

$$
w_0=(u-2v+z)/\sqrt6,\qquad
|\Omega\rangle=(|0\rangle_{\rm ref}s+|1\rangle_{\rm ref}w_0)/\sqrt2.
\tag{7.2}
$$

Here $w_0\perp s$ is unit, and (6.4) gives
$\Phi_\circ(|s\rangle\langle w_0|)=-|s\rangle\langle w_0|/2$.
After $n$ steps the state has reference blocks

$$
\tfrac12\begin{pmatrix}
P&c_n|s\rangle\langle w_0|\\
c_n|w_0\rangle\langle s|&A_n
\end{pmatrix},\qquad
c_n=(-1/2)^n,\quad A_n=\Phi_\circ^n(|w_0\rangle\langle w_0|),
\tag{7.3}
$$

where $A_n$ is supported in $R_3\cap s^\perp$.
Its reference partial transpose, compressed to
$(|1\rangle_{\rm ref}s,|0\rangle_{\rm ref}w_0)$, is

$$
\begin{pmatrix}0&c_n/2\\c_n/2&0\end{pmatrix},
\qquad\det=-4^{-n}/4<0.
\tag{7.4}
$$

It has negative eigenvalue $-2^{-n-1}$, so the full partial transpose
is not positive. A separable state has positive reference partial
transpose, proving non-EB for every finite $n$. This is precisely the
FW Theorem 20.2 witness; its coherence decays and is not peripheral.
For a general gauge use $(I_{\rm ref}\otimes D)|\Omega\rangle$.

To connect the code suppliers faithfully to arbitrary *full-input* codes,
write $U=U_0$, $a=(u-v)/\sqrt2$, and $P_a=|a\rangle\langle a|$ on $R_3$.
Since $U_0^\dagger U_1$ is the transposition of $u,v$, rotating the
actual Kraus labels gives restricted errors

$$
A_0=U(I_{R_3}-P_a),\qquad A_1=UP_a.
\tag{7.5}
$$

The plane $a^\perp\cap R_3$ is a one-step isometric code. All $R_3$
is not correctable, because the error product $P_a$ is not scalar
there. This is the Knill–Laflamme scalar-compression criterion [KL],
with the actual errors, as used in FW Theorem 21.2.

For two restricted steps, the error-product span contains $P_a$ by
summing $(A_jA_1)^\dagger(A_jA_1)$ over $j$. It also contains
$F^\dagger(P_a)=\sum_i(A_1A_i)^\dagger(A_1A_i)$.
Put $b=Ua=(u-z)/\sqrt2$ and $c_0=(2b-a)/\sqrt3$. Then $a,c_0$ are
orthonormal in $R_3\cap s^\perp$ and

$$
F^\dagger(P_a)=\tfrac14P_a+\tfrac34|c_0\rangle\langle c_0|.
\tag{7.6}
$$

Thus the span contains both orthogonal rank-one projections. A scalar
compression of a positive rank-one matrix to a code of dimension at
least two must be zero. The criterion would therefore make a two-step
qubit code perpendicular to $a,c_0$, leaving only $\mathbb Cs$.
No such restricted code exists. This recovers exactly the restricted
sequence $(3,2,1,1,\ldots)$ supplied by FW §21.

For full inputs let
$H_+=\operatorname{span}\{q(e_0+e_1),e_2,q(e_3+e_4)\}$.
The rotated Kraus operator $(K_0+K_1)/\sqrt2$ maps its displayed
orthonormal basis to $(u,v,z)$, while $(K_0-K_1)/\sqrt2$ vanishes
there. Hence the first channel is isometric from $H_+$ onto $R_3$.
A three-dimensional one-step code exists, and pulling the restricted
one-step plane back to $H_+$ gives a full-input two-step code of
dimension two.

The upper bounds do not assume an initial code lies in $R_3$.
Here is the relevant output-rank consequence of the same criterion,
consistent with FW Theorems 5.1 and 6.1–6.2. On a correctable
$k$-dimensional code $C$, restricted errors satisfy
$A_i^\dagger A_j=\alpha_{ij}I_C$. Diagonalizing the positive matrix
$\alpha$ gives restricted errors $\sqrt{p_j}W_j$, where the nonzero
$W_j$ are isometries with pairwise orthogonal output ranges. Since
every output here is in dimension three,

$$
k\,\operatorname{rank}\alpha\le3.
\tag{7.7}
$$

Thus no one-step code exceeds dimension three; if $k\ge2$, its first
step must be a single isometry. A code correctable after $n$ steps is
correctable after the first step, by composing its terminal decoder
with the remaining $n-1$ channel applications. A hypothetical
three-dimensional full-input two-step code would therefore map
isometrically onto all $R_3$ after its first step and make $F$
correctable there, contrary to (7.5). Thus $k_2=2$.
A hypothetical full-input qubit code after three steps would similarly
map isometrically onto a qubit plane in $R_3$, correctable for $F^2$,
contrary to (7.6). Prefix monotonicity gives $k_n\le1$ for $n\ge3$;
a terminal reset always recovers a one-dimensional code. This proves
(7.1). These decoder compositions establish necessary properties and
do not insert a recovery into the actual iteration. Diagonal conjugacy
transfers every code and decoder without changing dimensions. $\square$

## 8. Actual complex examples and the failure of rank-only tests

**Proposition 8.1 (A rank-two mixing Gram outside the template).** In one
common orthonormal environment pair $f_0,f_1$, set

$$
\alpha_0=\beta_0=\gamma_0=\delta_0=f_0,\qquad
\alpha_1=\beta_1=\gamma_1=\delta_1=f_1.
\tag{8.1}
$$

This is a legal actual Gram of rank two. Its channel mixes on full $M_5$
and has exact characteristic polynomial

$$
\det(tI-\Phi)=t^{21}(t-1)(t+1/2)(t^2-1/2).
\tag{8.2}
$$

In particular a two-dimensional environment does not by itself imply a
permanent classical label or nonmixing.

Proof. The list (8.1) has a single common Gram and satisfies every
orthogonal pair in (2.3), so (2.2) proves legality on all inputs. Its
rank is exactly two. It cannot satisfy (2.9), because
$\langle\gamma_0,\gamma_1\rangle=0$, while the template forces the
modulus of this overlap to be one. The following full-space polynomial
calculation proves mixing independently of that use of the classification.

Its actual Kraus operators are

$$
L_0=|u\rangle\langle e_0|+q|e_1\rangle\langle e_2|
                                      +|e_2\rangle\langle e_3|,
\quad
L_1=|u\rangle\langle e_1|+q|e_4\rangle\langle e_2|
                                      +|e_2\rangle\langle e_4|.
\tag{8.3}
$$

All outputs lie in $R_4=\operatorname{span}\{u,e_1,e_2,e_4\}$.
In its ordered orthonormal basis $(u,x=e_1,y=e_2,w=e_4)$, their
restrictions are the real matrices

$$
A=\begin{pmatrix}q&0&0&0\\0&0&q&0\\q&0&0&0\\0&0&0&0\end{pmatrix},
\qquad
B_2=\begin{pmatrix}0&1&0&0\\0&0&0&0\\0&0&0&1\\0&0&q&0\end{pmatrix}.
\tag{8.4}
$$

We compute the characteristic polynomial of
$X\mapsto AXA^{\mathsf T}+B_2XB_2^{\mathsf T}$ on this 16-dimensional
matrix space. Let $F_{ij}$ be its matrix units with indices $0,1,2,3$,
and, for $i<j$, put $S_{ij}=F_{ij}+F_{ji}$ and
$T_{ij}=F_{ij}-F_{ji}$. The symmetric off-diagonal and antisymmetric
spaces, each of dimension six, are invariant. Their nonzero image rules
are

$$
\begin{array}{c|c|c}
(i,j)&\Phi(S_{ij})&\Phi(T_{ij})\\\hline
(0,1)&0&0\\
(0,2)&(S_{01}+S_{12})/2&(T_{01}-T_{12})/2\\
(0,3)&0&0\\
(1,2)&qS_{03}&qT_{03}\\
(1,3)&S_{02}&T_{02}\\
(2,3)&qS_{23}&-qT_{23}
\end{array}
\tag{8.5}
$$

All entries outside $S_{23},T_{23}$ form nilpotent chains. Hence these
two spaces contribute $t^5(t-q)$ and $t^5(t+q)$.
Modulo the symmetric off-diagonal space, the four diagonal matrix units
have action, in the order $F_{00},F_{11},F_{22},F_{33}$,

$$
C=\begin{pmatrix}1/2&1&0&0\\0&0&1/2&0\\1/2&0&0&1\\0&0&1/2&0\end{pmatrix},
\qquad\det(tI-C)=t^2(t-1)(t+1/2).
\tag{8.6}
$$

Indeed the actual images are
$\Phi(F_{00})=(F_{00}+F_{22}+S_{02})/2$,
$\Phi(F_{11})=F_{00}$,
$\Phi(F_{22})=(F_{11}+F_{33})/2$, and
$\Phi(F_{33})=F_{22}$, giving the displayed quotient matrix and its
determinant. The two transpose eigenspaces exhaust the 16-dimensional
space, so multiplication gives
$t^{12}(t-1)(t+1/2)(t^2-1/2)$ on $\mathcal B(R_4)$.
The full map has range in that invariant space; the nine-dimensional
quotient $M_5/\mathcal B(R_4)$ is zero under it. This supplies the
additional factor $t^9$ and proves (8.2).

There is just one unit-circle eigenvalue, the simple root one; the
others are $0,-1/2,1/\sqrt2,-1/\sqrt2$. A stationary density exists by
Cesàro compactness. The simple root and trace preservation identify the
limiting projection as $X\mapsto\sigma\operatorname{Tr}X$; all other
Jordan modes decay because their eigenvalues have modulus less than one.
This proves full-input mixing directly. $\square$

**Proposition 8.2 (Complex phases and a maximal-rank mixing example).** The
choice $t=(1,i,1,1,1)$ gives an actual complex rank-two nonmixing Gram
with

$$
\chi=(1,-i,1,-i,i,1,1,1),\quad
\langle\alpha_0,\gamma_0\rangle=i/\sqrt2,\quad
\langle\gamma_0,\gamma_1\rangle=-i.
\tag{8.7}
$$

The actual rank-eight Gram $G=I_8$ instead gives the mixing channel

$$
\Psi(X)=\sum_{i,j}Q_{ij}X_{ii}E_j.
\tag{8.8}
$$

Proof. Multiply the canonical vector list by the eight phases in (8.7).
Its Gram is PSD, unit-diagonal, and satisfies the prescribed zeros.
The two overlaps follow directly from (2.9), including its conjugation
order. Theorem 5.1 gives its exact diagonal conjugacy and nonmixing.
For $G=I_8$, all edge cross terms vanish under the environment trace,
which gives (8.8) on every matrix unit. After one step the output is
diagonal, and $Q^n$ tends to its stationary probability because $Q^4>0$.
Thus $\Psi$ mixes directly. Both examples preserve the same all-input
population law, so that law alone cannot choose the hidden memory
behavior. $\square$

## 9. Primary correspondences and mathematical boundaries

**Convention 9.1 (Sources and the hypotheses actually used).** The notation
`literature-attested` identifies supplied general results; `repo-derived`
identifies the model-specific derivations here. The latter is not a
literature-priority claim. No general reference below is asserted to
contain the individual eight-vector phase classification.

| Source | Exact supplied statement and its use |
| --- | --- |
| [Five-Window Quantum Memory][FW], Definition 2.2, Theorems 4.1–4.2, §§32–35 | The actual all-input complex CPTP class, common Gram, reversed Choi conjugation, support and polar reductions, rank-four full-input compression, $2+3$ exclusion, and V-type $2+2$ exclusion. The parameter is exactly $\eta=1/2$, and the edge permutation is (2.4). Lemma 3.1 adds the U exclusion, and Lemma 4.1 extracts all eight vectors from the pure-line calculation. |
| FW Definition 17.2; Theorems 18.1, 18.3, 19.1–19.2 | The canonical $K_0,K_1$, states $P,M$, unit vector $d=(e_0-e_1-e_3+e_4)/2$, full-input effect $E$, polynomial and complete-norm limit. Corollary 6.1 transfers precisely these facts through the classified conjugacy. The recurrent algebra and full-$H$ fixed operator system have their separate units and products. |
| FW Theorem 20.2; Theorem 21.2; Theorems 5.1, 6.1–6.2, 9.2 and 10.2 | The canonical finite NPT witness, restricted exact codes, and full-input code framework and bounds. Corollary 7.1 uses the actual Kraus words, shows the full-input correspondence, and transfers the resulting canonical sequence to all nonmixing half lifts. It does not turn the class-optimal code sequence into a claim about all mixing members. |
| D. Burgarth, G. Chiribella, V. Giovannetti, P. Perinotti, and K. Yuasa, *Ergodic and Mixing Quantum Channels in Finite Dimensions*, [arXiv:1210.5625v3][MIX] | `literature-attested`: Lemma 1 and Corollaries 1–2, printed pp.7–8, give fixed Jordan parts and orthogonal stationary supports for general CPTP maps; Lemma 2, p.9, concerns enclosures and stationary densities; Theorem 5 and Remark 4, p.17, give the peripheral polar modulus and Kraus relation without global faithfulness. Equations (5.1)–(5.5) give the exact finite-dimensional uses. The faithful hypotheses of its Theorem 9 are not assigned to the full $H$. |
| R. Carbone and A. Jenčová, *On period, cycles and fixed points of a quantum channel*, [arXiv:1905.00857v1][CYCLE] | `literature-attested`: §3.1, Proposition 5 and Corollary 2, p.10, and Proposition 6, p.11, concern an irreducible unital Heisenberg channel with a faithful invariant state. The applicable map is the adjoint of the restriction to the actual support of the unique stationary density. Equations (5.5)–(5.7) construct the needed spectral cycle and its faithful densities explicitly. |
| R. Blume-Kohout, H. K. Ng, D. Poulin, and L. Viola, *Information-preserving structures: A general framework for quantum zero-error information*, [arXiv:1006.1358v1][IPS] | `literature-attested`: Theorem 5, p.9, describes arbitrary finite-dimensional CPTP fixed points on their joint support, the recurrent fixed-observable algebra, and its unique full-space extension. Here (6.5)–(6.7) identify that extension explicitly. A recurrent $\mathbb C\oplus\mathbb C$ does not assert an ordinary full-$H$ algebra. No full-rank-code lemma is used without its hypotheses. |
| E. Knill and R. Laflamme, *A Theory of Quantum Error-Correcting Codes*, [arXiv:quant-ph/9604034v1][KL] | `literature-attested`: Theorem 3.2, equations (19)–(20), PDF p.13, is the exact scalar-compression criterion. Section 7 applies it to the actual one-step and two-step Kraus products and terminal CPTP recovery on arbitrary complex subspace codes. |
| Lemmas 3.1 and 4.1, Theorem 5.1, Proposition 8.1 | `repo-derived`: complementary-plane exclusion, full-input half factorization, exact necessary-and-sufficient four-phase actual-Gram classification, and a rank-two non-template mixing example with the polynomial (8.2). Corollaries 6.1–7.1 are consequences for the classified family using the canonical suppliers specified above. |

**Convention 9.2 (Quantifiers retained and excluded extensions).** The theorem
quantifies over every actual PSD unit-diagonal common Gram satisfying
(2.3), including literal zeros, ranks two through eight when compatible,
and arbitrary complex phases. A nonmixing member has no additional
transient-feeding parameter beyond its diagonal gauge; every input
column was fixed in Lemma 4.1. Mixing members may have nonfaithful
stationary densities, including rank-four support; the excluded object
was a decomposition into stationary or swapped orthogonal mixed
sectors, not rank four itself. A pure stationary state without an
orthogonal stationary state does not by itself imply nonmixing.

The limit of a nonmixing member is EB, but every finite iterate is non-EB.
The theorem does not give an EB-index classification for mixing members.
The finite NPT witness, the finite exact-code sequence, and a persistent
classical label are distinct properties. The model supplies no access to
a discarded environment and no conclusion about a channel family whose
member changes at each step. The endpoints $\eta=0,1$, native complete
windows, physical time calibration, quantum capacity, and QFT are outside
these hypotheses. The environmental access model of
[Environment Record Memory][ER] is a different model and supplies no
operation on the retained system in this theorem.

[FW]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[ER]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[MIX]: https://arxiv.org/pdf/1210.5625v3
[CYCLE]: https://arxiv.org/pdf/1905.00857v1
[IPS]: https://arxiv.org/pdf/1006.1358v1
[KL]: https://arxiv.org/pdf/quant-ph/9604034v1

## 追加锚（本行以下为增补区）
