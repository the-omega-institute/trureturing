# AURIC FIB actual erased-history terminal recovery

## 93. Actual channel, identity target and reference convention

**Definition 93.1 (Actual fair chronological channel).** Let $A=\mathbb C^3$
and $M_3=\mathcal B(A)$. Use the actual matrices and chronological law of
[Purity arithmetic, Definition 87.1, (87.1)–(87.3)][PA] and
[Environment record memory, Definition 27.1, (27.3)][ENV]. In the original
coordinates set

$$
|0\rangle=\xi=\frac{(1,1,1)^{\mathsf T}}{\sqrt3},\qquad
|1\rangle=e=\frac{(1,1,-2)^{\mathsf T}}{\sqrt6},\qquad
|2\rangle=f=\frac{(1,-1,0)^{\mathsf T}}{\sqrt2}.
\tag{93.1}
$$

These vectors form the ordered orthonormal basis used for all matrix and
tensor coordinates below. In this basis the actual matrices are

$$
W=\operatorname{diag}(1,1,-1),\qquad
U_0=1\oplus\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},
\qquad U_1=U_0W.
\tag{93.2}
$$

For any real $\theta$, the chronological letters are
$V_0(\theta)=U_0e^{i\theta W}$ and $V_1(\theta)=V_0(\theta)W$.
The actual law assigns every word
$V_{h_n}\cdots V_{h_1}$ probability $2^{-n}$. Write
$\operatorname{Ad}_U(X)=UXU^\dagger$ and put

$$
\Delta_W=\tfrac12(\operatorname{id}+\operatorname{Ad}_W),\qquad
F=\operatorname{Ad}_{U_0}\circ\Delta_W
 =\tfrac12(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{U_1}),\qquad
\mathcal N_n=F^n\quad(n\ge0).
\tag{93.3}
$$

The cited identities identify this $F^n$ with the actual erased-history
channel at every angle. In particular $F^0=\operatorname{id}_{M_3}$.
The input and output are the whole complex qutrit; the history is not
an output register.

**Definition 93.2 (Signed parameter and reduced channel).** For $n\ge1$ set

$$
s=s_n=(-1/2)^{n-1},\qquad t=|s|,\qquad
a=\frac{1+s}{2},\qquad b=\frac{1-s}{2}.
\tag{93.4}
$$

Thus $(a,b)=(\alpha,\beta)$ in Purity arithmetic (87.3); the sign of $s$
is retained in both populations. For every complex matrix $X=(x_{ij})$,
use precisely $\Phi_s=\Psi_s$ of Purity arithmetic (87.7):

$$
\Phi_s(X)=
\begin{pmatrix}
x_{00}&s x_{01}&0\\
s x_{10}&a x_{11}+b x_{22}&0\\
0&0&b x_{11}+a x_{22}
\end{pmatrix},\qquad
F^n=\operatorname{Ad}_{U_0}\circ\Phi_s.
\tag{93.5}
$$

This identity is reused, including its action on non-Hermitian matrix
units. The parameter domain of the terminal result is

$$
\mathcal S_{\rm actual}
=\{(-1/2)^{n-1}:n=1,2,\ldots\}\cup\{0\}.
\tag{93.6}
$$

For its limiting member write $s_\infty=0$, $a=b=1/2$, and

$$
\mathcal N_\infty(X)=\Phi_0(X)
=x_{00}|0\rangle\langle0|
 +\frac{x_{11}+x_{22}}2
   (|1\rangle\langle1|+|2\rangle\langle2|).
\tag{93.7}
$$

The output in (93.7) is invariant under $\operatorname{Ad}_{U_0}$.
Consequently (93.5) tends to (93.7). The existence and the
measure-and-prepare form of this limit are already the qutrit restriction
of [Five-window quantum memory, Theorem 19.2, (19.4)–(19.7)][QM], under
the intertwining isometry specified in Purity arithmetic Definition 87.1.
The notation $\Phi_0$ means the reduced channel at parameter zero, whereas
$\mathcal N_0$ means the empty-horizon identity channel.

**Definition 93.3 (Terminal error and tensors).** A decoder is one CPTP map
$D:M_3\to M_3$ chosen for its horizon. It acts only on the terminal
qutrit and is independent of the unknown input. The target is always the
identity on the original input qutrit in (93.1). For
$n\in\{0,1,2,\ldots,\infty\}$ put

$$
\begin{aligned}
\delta_n
&=\min_{D\ {\rm CPTP}}\frac12\|D\circ\mathcal N_n
                            -\operatorname{id}_{M_3}\|_\diamond,\\
\frac12\|D\mathcal N_n-\operatorname{id}\|_\diamond
&=\sup_{\substack{R\text{ finite-dimensional}\\
                  \rho_{AR}\in\mathsf D(A\otimes R)}}
 \frac12\left\|[(D\mathcal N_n-\operatorname{id})
                     \otimes\operatorname{id}_R](\rho_{AR})\right\|_1,
\qquad \eta_n=1-\delta_n.
\end{aligned}
\tag{93.8}
$$

Here $\mathsf D(H)$ denotes the positive operators of trace one on $H$,
and $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$. The diamond norm is
the completely bounded trace norm: for a linear map $\Lambda$ it is
$\sup_{k\ge1,\,X\ne0}\|(\Lambda\otimes\operatorname{id}_k)(X)\|_1/\|X\|_1$.
The density-operator equality in (93.8) is applicable because a difference
of channels preserves Hermiticity. Stabilization and pure-input
attainment are [Watrous, The Theory of Quantum Information, Chapter 3,
Theorems 3.46 and 3.51, printed pp.173 and 176][TQI3]
([book reference][TQIL]). The quantifiers in (93.8)
include every finite untouched reference and all joint mixed states.
There is no reference access, retained record, smaller input code,
intermediate correction or postselection.

All Choi matrices are output-first:

$$
\begin{gathered}
|\Omega\rangle=\sum_{i=0}^2|i\rangle_{\rm out}|i\rangle_{\rm in},\qquad
|\Omega_3\rangle=|\Omega\rangle/\sqrt3,\\
J(\Lambda)=\sum_{i,j=0}^2\Lambda(|i\rangle\langle j|)
                  \otimes|i\rangle\langle j|,\qquad
J(\operatorname{id})=|\Omega\rangle\langle\Omega|,\qquad
\omega_\Lambda=J(\Lambda)/3.
\end{gathered}
\tag{93.9}
$$

Thus $\omega_{F^n}$ is exactly the normalized $\omega_n$ in Purity
arithmetic (87.2); $\omega_{\operatorname{id}}$
is $|\Omega_3\rangle\langle\Omega_3|$. When a reference copy is used
as an actual probe it is the second tensor factor, and it is untouched.

For $n\ge1$ the correspondence

$$
\mathcal R=D\circ\operatorname{Ad}_{U_0},\qquad
D=\mathcal R\circ\operatorname{Ad}_{U_0^\dagger},\qquad
D F^n=\mathcal R\Phi_s
\tag{93.10}
$$

is a bijection between all terminal CPTP decoders and all CPTP maps
$\mathcal R:M_3\to M_3$. It changes no input, reference or identity
target in (93.8).

## 94. Exact actual-horizon values and terminal decoders

**Definition 94.1 (Terminal Kraus family).** For $r,z\in[0,1]$ and
$\sigma\in\{+1,-1\}$ let $\mathcal R_{r,z}^{\sigma}$ have Kraus operators

$$
\begin{aligned}
K_0&=|0\rangle\langle0|+\sigma r|1\rangle\langle1|,\\
K_1&=\sqrt{1-r^2}\,|2\rangle\langle1|,\\
K_2&=\sqrt{1-z}\,|1\rangle\langle2|,\\
K_3&=\sqrt z\,|2\rangle\langle2|.
\end{aligned}
\tag{94.1}
$$

Their adjoint products sum to
$|0\rangle\langle0|+[r^2+(1-r^2)]|1\rangle\langle1|
+[(1-z)+z]|2\rangle\langle2|=I_3$, so the family is CPTP on the full
qutrit. The superscript $-1$ in $\mathcal R_{r,z}^{-1}$ denotes
$\sigma=-1$, never an inverse map.

**Theorem 94.2 (Sharp actual erased-history terminal recovery).** With the
channel and metric of §93, the following are exact values:

$$
\boxed{
\begin{array}{c|c}
\text{horizon}&\eta_n=1-\delta_n\\ \hline
0&1\\[2pt]
n\ge1\text{ odd}&\displaystyle\frac{(1+s)(1+2s)}{5+7s}\\[6pt]
2&\displaystyle\frac3{H(r_*)}\\[6pt]
n\ge4\text{ even}&\displaystyle\frac{h^2(h^2+3)}{K(h)}\\[6pt]
\infty&\displaystyle\frac15
\end{array}}
\tag{94.2}
$$

Here $s=s_n$ in the odd formula. The number $r_*$ is the unique root in
$(3/10,1/3)$ of

$$
(2-r)(1-r^2)^2=4r,
\qquad\text{equivalently}\qquad
r^5-2r^4-2r^3+4r^2+5r-2=0,
\tag{94.3}
$$

and

$$
H(r)=7+r^2-4r+\frac4{1-r^2}.
\tag{94.4}
$$

For every even $n\ge4$ use

$$
t=2^{1-n},\qquad
h=\sqrt{\frac{1+t}{1-t}}=\sqrt{\frac ba},\qquad
K(h)=(1+h^2)^2+(h+1)^2(h^2+3).
\tag{94.5}
$$

The following single terminal decoder attains the minimum for each horizon:

$$
\begin{aligned}
D_0&=\operatorname{id},\\
D_n&=\operatorname{Ad}_{U_0^\dagger}
                         &&(n\ge1\text{ odd}),\\
D_2&=\mathcal R_{r_*,0}^{-1}\circ\operatorname{Ad}_{U_0^\dagger},\\
D_n&=\mathcal R_{r,z}^{-1}\circ\operatorname{Ad}_{U_0^\dagger}
                         &&(n\ge4\text{ even}),\\
D_\infty&=\operatorname{id},
\end{aligned}
\qquad
\begin{aligned}
r&=\frac{1+h^2}{(h+1)(h^2+3)},\\
z&=h^2r^2-\frac{h(h-1)}{h+1}
       &&(n\ge4\text{ even}).
\end{aligned}
\tag{94.6}
$$

In particular $0<r<1$, $0<z<1$ in the later even regime. For these
decoders, for every finite $R$ and every $\rho_{AR}\in\mathsf D(A\otimes R)$,

$$
\frac12\left\|[(D_n\mathcal N_n-\operatorname{id})
          \otimes\operatorname{id}_R](\rho_{AR})\right\|_1\le\delta_n.
\tag{94.7}
$$

For each $n\ge1$, and also for $n=\infty$, an explicit probability vector
$p$ below defines one probe

$$
|\psi_p\rangle=\sum_{i=0}^2\sqrt{p_i}\,|i\rangle_A|i\rangle_R,
\qquad R=\mathbb C^3,
\tag{94.8}
$$

whose output half trace distance is at least $\delta_n$ for every
competing CPTP decoder and is exactly $\delta_n$ for (94.6). Thus the
lower certificate covers arbitrary untwirled CPTP decoders. The formulas
give

$$
\delta_1=\frac12,\qquad \delta_3=\frac{13}{18},\qquad
\lim_{n\to\infty}\delta_n=\delta_\infty=\frac45.
\tag{94.9}
$$

The empty-horizon identity case is immediate. The one-step value is the
specialization of [Purity arithmetic, Theorem 59.2, (59.1)–(59.2)][PA] to
$(\operatorname{id}+\operatorname{Ad}_W)/2$, with weights $1/2,1/2$
and spectral convex hull containing zero. That theorem uses the unhalved
diamond norm; (93.8) divides its value by two. The certificate below
also includes this endpoint without an inverse of a singular matrix.
The $n\ge2$ values, feasible parameter choices and limiting recovery
value are the fixed-channel deductions proved in §§95–100.

## 95. Proof of Theorem 94.2: matching certificates for the actual channel

### 95.1. Exact overlap against an unrestricted decoder

Fix $s\in\mathcal S_{\rm actual}$, with $a,b,t$ as in (93.4), and a
probability vector $p$. For an arbitrary CPTP decoder $\mathcal R$ define

$$
T_{ij}=\langle i|\mathcal R(|j\rangle\langle j|)|i\rangle,\qquad
\ell=\langle0|\mathcal R(|0\rangle\langle1|)|1\rangle.
\tag{95.1}
$$

Positivity and trace preservation make $T$ entrywise nonnegative with
$\sum_iT_{ij}=1$ for each column $j$. The decoder Choi principal block
on $(|00\rangle,|11\rangle)$ is
$\left(\begin{smallmatrix}T_{00}&\ell\\\overline\ell&T_{11}\end{smallmatrix}\right)$.
Its positivity gives $|\ell|^2\le T_{00}T_{11}$.

Expanding (94.8) and using every matrix unit in (93.5) gives the exact
target overlap

$$
\begin{aligned}
G_{\mathcal R}(p)
&=\langle\psi_p|(\mathcal R\Phi_s\otimes\operatorname{id})
     (|\psi_p\rangle\langle\psi_p|)|\psi_p\rangle\\
&=p_0^2T_{00}
 +p_1^2(aT_{11}+bT_{12})
 +p_2^2(bT_{21}+aT_{22})
 +2s p_0p_1\operatorname{Re}\ell.
\end{aligned}
\tag{95.2}
$$

Put $u=\sqrt{T_{11}}$ and $v=T_{22}$. Then $u,v\in[0,1]$ and

$$
T_{00}\le1,\quad T_{12}\le1-v,\quad
T_{21}\le1-u^2,\quad |\ell|\le u.
$$

Since $a,b\ge0$ on the actual domain, these inequalities imply

$$
\begin{aligned}
G_{\mathcal R}(p)&\le L_s(p;u,v),\\
L_s(p;u,v)
&=p_0^2+b(p_1^2+p_2^2)
 +(ap_1^2-bp_2^2)u^2
 +2t p_0p_1u+(ap_2^2-bp_1^2)v.
\end{aligned}
\tag{95.3}
$$

In particular a probability vector satisfying
$L_s(p;u,v)\le\eta$ for every $u,v\in[0,1]$ gives, for every
$\mathcal R$,

$$
\frac12\|\mathcal R\Phi_s-\operatorname{id}\|_\diamond
\ge\frac12\|(\mathcal R\Phi_s\otimes\operatorname{id})
       (|\psi_p\rangle\langle\psi_p|)-|\psi_p\rangle\langle\psi_p|\|_1
\ge1-G_{\mathcal R}(p)\ge1-\eta.
\tag{95.4}
$$

The second inequality is the two-outcome measurement with first effect
$|\psi_p\rangle\langle\psi_p|$. It uses a legitimate normalized
entangled input, with marginals $\operatorname{diag}(p)$ on both factors.
No covariance assumption was imposed on $\mathcal R$.

### 95.2. The recovered Choi block and CP-order upper bound

Choose $r,z\in[0,1]$ and $\sigma=\operatorname{sgn}(s)$, with
$\sigma=+1$ at $s=0$. Put
$\mathcal C=\mathcal R_{r,z}^{\sigma}\Phi_s$. Applying (94.1) to
(93.5) shows that the Choi block of $\mathcal C$ on
$(|00\rangle,|11\rangle,|22\rangle)$ is

$$
M=\begin{pmatrix}1&tr&0\\tr&q_1&0\\0&0&q_2\end{pmatrix},\qquad
q_1=ar^2+b(1-z),\qquad q_2=b(1-r^2)+az.
\tag{95.5}
$$

All remaining nonzero entries of $J(\mathcal C)$ are

$$
(1-q_1)|21\rangle\langle21|
 +(1-q_2)|12\rangle\langle12|.
\tag{95.6}
$$

Indeed the populations starting at $|1\rangle$ and $|2\rangle$ sum to
one, and the only surviving off-diagonal matrix units have multiplier
$tr$. We have $0\le q_1,q_2\le1$. The block $M$ is positive
semidefinite, as a principal block of a channel Choi matrix. Explicitly,
$a-t^2=(1-s)(1+2s)/2\ge0$ on $-1/2\le s\le1$, so
$q_1-t^2r^2=(a-t^2)r^2+b(1-z)\ge0$, also proving its positivity.
The corresponding block of the normalized Choi state is $M/3$.

Suppose the chosen $p$ and a number $\eta\in(0,1)$ satisfy

$$
Mp=\eta\mathbf1,\qquad \mathbf1=(1,1,1)^{\mathsf T}.
\tag{95.7}
$$

Then $p^\dagger Mp=\eta$, since $\sum_i p_i=1$. Cauchy–Schwarz for
the positive semidefinite form defined by $M$ gives, for every complex
$w\in\mathbb C^3$,

$$
\eta^2|\mathbf1^\dagger w|^2
=|p^\dagger Mw|^2
\le(p^\dagger Mp)(w^\dagger Mw)=\eta\,w^\dagger Mw.
$$

No invertibility is required. It follows that

$$
M-\eta\mathbf1\mathbf1^\dagger\succeq0,
\qquad J(\mathcal C)-\eta J(\operatorname{id})\succeq0.
\tag{95.8}
$$

Equivalently the normalized inequality is
$\omega_{\mathcal C}-\eta|\Omega_3\rangle\langle\Omega_3|\succeq0$.
To spell out its CP consequence, factor the positive matrix in (95.8)
as $\sum_\nu|w_\nu\rangle\langle w_\nu|$ and define operators
$B_\nu$ by $(B_\nu)_{ij}=\langle i,j|w_\nu\rangle$. The map
$X\mapsto\sum_\nu B_\nu X B_\nu^\dagger$ has exactly this Choi
matrix, by (93.9). The matrix-unit definition of $J$ is injective,
so this map is $\mathcal C-\eta\operatorname{id}$. Hence

$$
\mathcal C-\eta\operatorname{id}\ \text{is CP},\qquad
\mathcal C=\eta\operatorname{id}+(1-\eta)\mathcal E,
\qquad
\mathcal E=\frac{\mathcal C-\eta\operatorname{id}}{1-\eta}\ \text{is CPTP}.
\tag{95.9}
$$

Trace preservation follows from
$\operatorname{Tr}[(\mathcal C-\eta\operatorname{id})(X)]
=(1-\eta)\operatorname{Tr}X$. This is the usual Choi-to-Kraus
factorization of [Watrous, Chapter 2, Theorems 2.22 and 2.26,
pp.82–83 and 87–89][TQI2] ([book reference][TQIL]), used here inside
the fixed-channel certificate.

For every finite reference and every joint density, (95.9) yields

$$
\begin{aligned}
\frac12\|[(\mathcal C-\operatorname{id})\otimes\operatorname{id}_R]
                          (\rho_{AR})\|_1
&=\frac{1-\eta}{2}\|(\mathcal E\otimes\operatorname{id}_R)
                          (\rho_{AR})-\rho_{AR}\|_1\\
&\le1-\eta,
\end{aligned}
\tag{95.10}
$$

because both terms in the difference are densities. Thus (95.7) and
$L_s(p;u,v)\le\eta$ jointly prove exact optimality in (93.8).

For the family (94.1) all the overlap estimates used above are attained:

$$
T_{00}=1,\quad T_{11}=r^2,\quad T_{12}=1-z,\quad
T_{21}=1-r^2,\quad T_{22}=z,\quad\ell=\sigma r.
\tag{95.11}
$$

In particular $G_{\mathcal R_{r,z}^{\sigma}}(p)
=L_s(p;r,z)=p^{\mathsf T}Mp$. These identities will also establish
attainment by the same probe.

The coefficient $\eta$ in (95.9) is a CP-order identity component of an
unflagged channel. There is no accessible flag or instrument in this
decomposition, and it grants no postselection operation.

### 95.3. Diagonal covariance and the range of the reduction

For a diagonal unitary $V$ in (93.1), direct substitution in (93.5) gives

$$
\Phi_s\circ\operatorname{Ad}_V=\operatorname{Ad}_V\circ\Phi_s.
\tag{95.12}
$$

The normalized Haar average over the diagonal unitary group,

$$
\overline{\mathcal R}
=\int\operatorname{Ad}_{V^\dagger}\circ\mathcal R
                         \circ\operatorname{Ad}_V\,dV,
\tag{95.13}
$$

is CPTP and diagonal covariant. Moreover
$\overline{\mathcal R}\Phi_s-\operatorname{id}$ is the average of
$\operatorname{Ad}_{V^\dagger}\circ(\mathcal R\Phi_s-\operatorname{id})
\circ\operatorname{Ad}_V$. Convexity and unitary invariance of the
diamond norm therefore give

$$
\tfrac12\|\overline{\mathcal R}\Phi_s-\operatorname{id}\|_\diamond
\le\tfrac12\|\mathcal R\Phi_s-\operatorname{id}\|_\diamond.
\tag{95.14}
$$

This symmetry is CDUC in [S. Singh and I. Nechita, Diagonal unitary and
orthogonal symmetries in quantum theory, Quantum 5, 519 (2021),
Definition 6.3, p.28][SN]. Their (37), p.30, and Lemmas 6.11 and 6.13,
p.33, describe the common
diagonal population/coherence representation: the population matrix is
entrywise nonnegative and column stochastic, and the coherence matrix
is positive semidefinite. These are intermediate channel constraints
in this proof. The symmetry statement here concerns $\Phi_s$, the
twirled decoder, and their composition. The output conjugation by
$U_0$ in (93.5) is retained; no such assertion about $F^n$ follows
automatically. The lower bound (95.4) already covers decoders before
twirling.

## 96. Proof of Theorem 94.2: all odd horizons and the singular endpoint

For actual odd $n\ge1$ we have $0<s\le1$. The following algebra is
also valid at $s=0$. Choose $r=z=1$ and $\sigma=+1$. Then

$$
M=\begin{pmatrix}1&s&0\\s&a&0\\0&0&a\end{pmatrix},\qquad
p=\frac{(1+s,\ 2(1+s),\ 2(1+2s))^{\mathsf T}}{5+7s},\qquad
\eta=\frac{(1+s)(1+2s)}{5+7s}.
\tag{96.1}
$$

Every entry of $p$ is positive and their numerators sum to $5+7s$.
For the three rows respectively,

$$
\begin{aligned}
p_0+s p_1&=\frac{(1+s)(1+2s)}{5+7s},\\
s p_0+a p_1&=\frac{s(1+s)+(1+s)^2}{5+7s}
                         =\frac{(1+s)(1+2s)}{5+7s},\\
a p_2&=\frac{(1+s)(1+2s)}{5+7s}.
\end{aligned}
\tag{96.2}
$$

Thus $Mp=\eta\mathbf1$. Also $0<\eta<1$: its first-row expression
is $p_0+s p_1\le p_0+p_1<1$.

For the unrestricted-decoder lower certificate, write $y=u^2$. In
(95.3), $L_s(p;\sqrt y,v)$ is concave in $y\in[0,1]$, because its
only non-affine term is $2s p_0p_1\sqrt y$. Its derivative at $y=1$
and its coefficient of $v$ are

$$
\begin{aligned}
d_y&=ap_1^2-bp_2^2+s p_0p_1
 =p_1^2\frac{s(1+2s)(1+3s)}{2(1+s)^2}\ge0,\\
d_v&=ap_2^2-bp_1^2
 =p_1^2\frac{s(4+5s)}{2(1+s)}\ge0.
\end{aligned}
\tag{96.3}
$$

For example these identities follow by substituting
$p_0/p_1=1/2$ and $p_2/p_1=(1+2s)/(1+s)$; no denominator vanishes
on $[0,1]$. The tangent inequality for the concave function, including
$y=0$ by continuity, gives

$$
L_s(p;\sqrt y,v)-L_s(p;1,1)
\le d_y(y-1)+d_v(v-1)\le0\qquad(y,v\in[0,1]).
\tag{96.4}
$$

Since $L_s(p;1,1)=p^{\mathsf T}Mp=\eta$, this proves the required
global lower bound. The map $\mathcal R_{1,1}^{+1}$ only pinches
between $\operatorname{span}\{|0\rangle,|1\rangle\}$ and
$\mathbb C|2\rangle$. That pinching is redundant after $\Phi_s$ by
(93.5). Hence the actual decoder $\operatorname{Ad}_{U_0^\dagger}$
in (94.6) realizes precisely the recovered channel in this certificate.
Equations (95.4) and (95.10) prove

$$
\delta_n=1-\frac{(1+s)(1+2s)}{5+7s}
        =\frac{4+4s-2s^2}{5+7s}\qquad(n\ge1\text{ odd}).
\tag{96.5}
$$

At $n=1$, $s=1$, $p=(1,2,3)^{\mathsf T}/6$ and $\eta=1/2$.
The upper-left block of $M$ is
$\left(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\right)$, so $M$
is singular. All the displayed row identities, the concavity bound and
the positive-semidefinite Cauchy–Schwarz argument remain valid. This
recovers the existing one-step value without using $M^{-1}$. At $n=3$,
$s=1/4$ gives $\eta=5/18$ and $\delta_3=13/18$.

## 97. Proof of Theorem 94.2: the exceptional horizon two

Here $s=-1/2$, $t=1/2$, $a=1/4$ and $b=3/4$. Define

$$
g(r)=(2-r)(1-r^2)^2-4r.
$$

For $0\le r\le1$,

$$
g'(r)=-(1-r^2)^2-4r(2-r)(1-r^2)-4<0,
\qquad
g(3/10)=\frac{20777}{100000}>0,\quad
g(1/3)=-\frac4{243}<0.
\tag{97.1}
$$

Continuity and strict decrease prove existence and uniqueness of the
root $r_*$ in (94.3), and in fact uniqueness on $[0,1]$. Expanding
$g(r)=0$ gives the stated quintic. In what follows let $r=r_*$,
$z=0$, $H=H(r)$, and $\sigma=-1$. Then

$$
M=\begin{pmatrix}
1&r/2&0\\
r/2&(3+r^2)/4&0\\
0&0&3(1-r^2)/4
\end{pmatrix},\qquad
p=\frac1H
\begin{pmatrix}3+r^2-2r\\4-2r\\4/(1-r^2)\end{pmatrix},\qquad
\eta=\frac3H.
\tag{97.2}
$$

Since $0<r<1$, the three numerators are positive and sum to $H$.
All Kraus coefficients are legitimate. Direct multiplication gives

$$
\begin{aligned}
H(Mp)_0&=(3+r^2-2r)+(r/2)(4-2r)=3,\\
H(Mp)_1&=(r/2)(3+r^2-2r)+\frac{3+r^2}{4}(4-2r)=3,\\
H(Mp)_2&=\frac{3(1-r^2)}4\,\frac4{1-r^2}=3.
\end{aligned}
\tag{97.3}
$$

In particular $Mp=\eta\mathbf1$ and $0<\eta<1$, since
$\eta=p_0+(r/2)p_1<p_0+p_1<1$.

To prove the lower certificate on the whole square, put

$$
A=\tfrac14p_1^2-\tfrac34p_2^2,\qquad
B=\tfrac14p_2^2-\tfrac34p_1^2.
\tag{97.4}
$$

The interval $0<r<1/3$ implies

$$
1<\frac{p_2}{p_1}
=\frac1{(1-r^2)(1-r/2)}
<\frac{27}{20}<\sqrt3.
\tag{97.5}
$$

Indeed the denominator is less than one and greater than
$(8/9)(5/6)=20/27$, and $(27/20)^2<3$. Therefore both $A<0$ and
$B<0$. The root equation supplies the exact stationary identity

$$
H^2\left(Ar+\tfrac12p_0p_1\right)
=3(2-r)-\frac{12r}{(1-r^2)^2}=0.
\tag{97.6}
$$

The polynomial terms in its left side before cancellation are
$r[(4-2r)^2/4-12/(1-r^2)^2]
+(3+r^2-2r)(4-2r)/2$, which reduce to the middle expression.
By (95.11) and (97.3), $L_s(p;r,0)=\eta$. Completing the square in
(95.3) using (97.6) now gives the exact identity

$$
L_s(p;u,v)-\eta=A(u-r)^2+Bv\le0
\qquad(u,v\in[0,1]).
\tag{97.7}
$$

This is the bound against all decoders, including those not in (94.1).
Together with (97.3) and (95.9)–(95.10), it proves

$$
\boxed{\delta_2
=1-\frac3{7+r_*^2-4r_*+4/(1-r_*^2)}}.
\tag{97.8}
$$

## 98. Proof of Theorem 94.2: every later even horizon

For even $n\ge4$, $s=-t$ and $0<t\le1/8$. In the notation (94.5),

$$
a=\frac1{1+h^2},\qquad b=\frac{h^2}{1+h^2},\qquad
t=\frac{h^2-1}{h^2+1}=b^2-a^2,\qquad
1<h\le\frac3{\sqrt7}<\frac87.
\tag{98.1}
$$

Set $r,z$ as in (94.6), $\sigma=-1$, and take

$$
p=\frac1K
\begin{pmatrix}
(1+h^2)^2\\
(h+1)(h^2+3)\\
h(h+1)(h^2+3)
\end{pmatrix},\qquad
\eta=\frac{h^2(h^2+3)}K.
\tag{98.2}
$$

Every entry is positive. Their sum is one by the definition of $K$.

### 98.1. Feasibility throughout the actual domain

The identity

$$
(h+1)(h^2+3)=4(1+h^2)+(h-1)^3
\tag{98.3}
$$

gives $0<r<1/4$ for $h>1$; the endpoint $h=1$ gives $r=1/4$.
The expression for $z$ immediately gives
$z<h^2r^2<4/49<1$, using $h<8/7$ and $r\le1/4$.
Its positivity is equivalent to that of

$$
S(h)=h(1+h^2)^2-(h^2-1)(h^2+3)^2,
\tag{98.4}
$$

because multiplying $z$ by the positive denominator
$(h+1)^2(h^2+3)^2$ gives $hS(h)$. For
$k=h-1\in(0,1/7)$ the exact expansion is

$$
S(h)=4-20k-32k^2-28k^3-15k^4-5k^5-k^6.
\tag{98.5}
$$

The last four negative terms have total magnitude
$k^3(28+15k+5k^2+k^3)\le49k^3$. It follows that

$$
S(h)\ge4-\frac{20}7-\frac{32}{49}-\frac{49}{343}
=\frac{17}{49}>0.
\tag{98.6}
$$

Thus $0<z<1$ on the whole actual later-even domain. In particular
(94.1) defines a CPTP attainer there, including $t=1/8$ at $n=4$.
All denominators in (94.5), (94.6) and (98.2) are positive.

### 98.2. All three row identities

The chosen parameters satisfy

$$
\frac{p_0}{p_1}=\frac ra,\qquad
\frac{p_2}{p_1}=h,\qquad
q_2=b(1-r^2)+az
=b-\frac{ah(h-1)}{h+1}=\frac h{h+1}.
\tag{98.7}
$$

For the first row of (95.5),

$$
\frac{(Mp)_0}{p_1}
=r(1/a+t)
=\frac{1+h^2}{(h+1)(h^2+3)}
  \frac{h^2(h^2+3)}{1+h^2}
=\frac{h^2}{h+1}.
\tag{98.8}
$$

For the second row use $b^2-a^2=t$ and $b/a=h^2$ to obtain

$$
\begin{aligned}
\frac{(Mp)_1}{p_1}
&=\frac{tr^2}a+ar^2+b(1-z)\\
&=b\bigl(h^2r^2+1-z\bigr)
=b\left(1+\frac{h(h-1)}{h+1}\right)
=\frac{h^2}{h+1}.
\end{aligned}
\tag{98.9}
$$

For the third row,

$$
\frac{(Mp)_2}{p_1}=q_2\frac{p_2}{p_1}
=\frac{h^2}{h+1}.
\tag{98.10}
$$

Since $p_1h^2/(h+1)=h^2(h^2+3)/K$, these identities prove
$Mp=\eta\mathbf1$. Also $0<\eta<1$, because its first-row
expression is $p_0+tr p_1<p_0+p_1<1$.

### 98.3. The unrestricted-decoder square certificate

Substitution of $p_2/p_1=h$ gives

$$
ap_2^2-bp_1^2=0,\qquad
ap_1^2-bp_2^2=-\frac ta p_1^2.
\tag{98.11}
$$

Together with $p_0/p_1=r/a$, (95.3) therefore has quadratic term
$-(t/a)p_1^2u^2$ and linear term $2(t/a)p_1^2ru$, with no dependence
on $v$. At $(u,v)=(r,z)$ its value is
$p^{\mathsf T}Mp=\eta$. Consequently

$$
\boxed{L_s(p;u,v)-\eta
=-\frac ta p_1^2(u-r)^2\le0\qquad(u,v\in[0,1]).}
\tag{98.12}
$$

This proves the lower bound for every CPTP decoder and, with the row
identities and the CP-order bound, establishes the later-even value in
(94.2) without a remaining optimization.

## 99. Proof of Theorem 94.2: the limit and both parity limits

At $s=0$ use the reduced identity decoder. As in §96, the Kraus choice
$r=z=1$, $\sigma=+1$ has the same action after $\Phi_0$. Its data are

$$
M=\operatorname{diag}(1,1/2,1/2),\qquad
p=\frac{(1,2,2)^{\mathsf T}}5,\qquad \eta=\frac15,
\qquad Mp=\tfrac15\mathbf1.
\tag{99.1}
$$

For this $p$, the coefficients of $u^2$ and $v$ in (95.3) vanish and $t=0$,
so for every $u,v\in[0,1]$,

$$
L_0(p;u,v)=p_0^2+\tfrac12(p_1^2+p_2^2)=\frac15.
\tag{99.2}
$$

Thus the limit channel itself, with its own arbitrary-decoder lower
certificate and all-reference upper certificate, has $\delta_\infty=4/5$.
By (93.7) it is invariant under $U_0$, so the actual identity decoder
$D_\infty$ attains this value. It is unnecessary to infer its optimality
solely from finite-horizon convergence.

For odd $n\to\infty$, $s\to0$ in (96.1), giving $\eta_n\to1/5$.
For even $n\to\infty$, $t\to0$ and $h\to1$ in (94.5); the positive
denominator tends to

$$
K(1)=4+16=20,\qquad h^2(h^2+3)\longrightarrow4.
\tag{99.3}
$$

Hence the even values also satisfy $\eta_n\to1/5$. The later-even
attainer has the well-defined parameter limit $r\to1/4$, $z\to1/16$,
and its probe tends to $(1,2,2)^{\mathsf T}/5$. The odd probe has the
same limit. These endpoint statements use no division by $t$ or by $s$.
Both parity sequences therefore converge to the directly computed
$\delta_\infty=4/5$.

## 100. Attainment by the same probe and failure of an unweighted proxy

**Proof of the probe-attainment assertion in Theorem 94.2.** For every
finite $n\ge1$ and for $n=\infty$, the corresponding $p$ in (96.1),
(97.2), (98.2) or (99.1) is a strictly positive probability vector.
Equations (95.11) and $Mp=\eta\mathbf1$ give recovered overlap
exactly $\eta$ for the proposed attainer. Let
$P_p=|\psi_p\rangle\langle\psi_p|$. In (95.9) put
$\tau=(\mathcal E\otimes\operatorname{id})(P_p)$. Then

$$
\langle\psi_p|[\eta P_p+(1-\eta)\tau]|\psi_p\rangle=\eta
\quad\Longrightarrow\quad
\langle\psi_p|\tau|\psi_p\rangle=0.
\tag{100.1}
$$

Positivity gives $\|\sqrt\tau\,|\psi_p\rangle\|^2=0$, so $\tau$ has
support orthogonal to $|\psi_p\rangle$. Both $\tau$ and $P_p$ have
trace one, and thus $\|\tau-P_p\|_1=2$. Consequently

$$
\frac12\|(\mathcal C\otimes\operatorname{id})(P_p)-P_p\|_1
=1-\eta.
\tag{100.2}
$$

For every competing decoder, (95.4) gives at least $1-\eta$ on this
same probe. The original-channel equality follows from (93.10), and
at infinity from (93.7). At $n=0$ the identity decoder has zero error
on every joint input, including every $P_p$; nonnegativity is its
matching lower bound. This completes the proof of Theorem 94.2.

**Proposition 100.1 (Unweighted normalized Choi probe is insufficient).**
At $n=1$, for the attaining decoder $D_1=\operatorname{Ad}_{U_0^\dagger}$,
the maximally entangled qutrit input has half trace distance
$\sqrt2/3<1/2=\delta_1$.

Proof. Here $\Phi_1=\Delta_W$ pinches the two-dimensional $+1$
eigenspace of $W$ against its one-dimensional $-1$ eigenspace. Put

$$
|u\rangle=(|00\rangle+|11\rangle)/\sqrt2,\qquad |v\rangle=|22\rangle,
\qquad |\Omega_3\rangle=\sqrt{2/3}|u\rangle+\sqrt{1/3}|v\rangle.
$$

The channel on the first tensor factor deletes just the cross term
between these two components of this input. The difference between
target and output, restricted to their span, is

$$
\begin{pmatrix}0&\sqrt2/3\\\sqrt2/3&0\end{pmatrix}.
\tag{100.3}
$$

Its trace norm is $2\sqrt2/3$. Hence the half trace distance is
$\sqrt2/3$, and $\sqrt2/3<1/2$ because $2/9<1/4$. By contrast the
probe $p=(1,2,3)^{\mathsf T}/6$ in §96 attains $1/2$.
Thus diagonal covariance does not make the unweighted normalized Choi
probe worst-case. The weighted two-density Choi expression in
[Watrous, Simpler semidefinite programs for completely bounded norms,
arXiv:1207.5726v2, Theorem 6, §3.1, p.10][W12]
([paper reference][W12L]) allows variable input densities; it imposes
no maximally mixed-input restriction. The proof of Theorem 94.2 uses
the explicit CP-order certificate (95.8)–(95.10) to obtain the
full diamond bound, rather than substituting a Choi overlap for the metric.

## 101. Mathematical scope and source correspondence

**Definition 101.1 (Scope of the terminal conclusion).** The quantifier
pattern of Theorem 94.2 is one $D_n$ for each horizon and every unknown
qutrit input and untouched finite reference at that horizon. It does not
assert a single decoder attaining all horizons simultaneously. Its
parameter set is (93.6), with the empty horizon treated separately.
The formulas and certificates cover $n=1$, the exceptional $n=2$, all
later odd and even horizons, and the limiting channel. No classification
of all attaining decoders or recovery phase diagram on the other real
values of $s$ is part of the statement.

The actual channel identity, basis and angular independence are the
reused results in Purity arithmetic Definition 87.1 and (87.7), and
Environment record memory Definition 27.1 and (27.3). The restricted
iteration, invariant sectors and EB limit are the reused results in
Five-window quantum memory §§18–20, transported by the isometry in
Purity arithmetic Definition 87.1. The all-reference common-test and
CPTP-residual methods already occur in Purity arithmetic Theorem 66.2
and §§69–78, especially Theorem 72.1. Its six-record horizon-three
optimization permits record-dependent decoders and has a different
channel from the erased-history $F^3$ used here. These prior results
are used with their stated hypotheses; the actual $n\ge2$ terminal
values and the limiting recovery value follow from the parameter and
probe calculations in §§95–100.

Haar averaging, stochastic population constraints, Choi positivity,
positive-semidefinite Cauchy–Schwarz, Kraus factorization and stabilized
trace norms are general mathematical suppliers inside those calculations.
The Singh–Nechita citation supplies the CDUC terminology and channel
criteria. The cited Watrous results supply the norm and channel
representation interfaces. No exact value for this actual sequence is
attributed to those general results, and no literature priority is asserted.

**Definition 101.2 (Distinct task and memory problems).** For the sharp-task
problem of Environment record memory (27.1), the loss for
$E_v=|v\rangle\langle v|$ is

$$
\min_{D\ {\rm CPTP}}\sup_{\rho\in\mathsf D(A)}
\left|\operatorname{Tr}(E_v D F^n(\rho))
              -\operatorname{Tr}(E_v\rho)\right|,
\tag{101.1}
$$

with a decoder allowed to depend on $v$. Its optimization is different
from (93.8). Theorem 94.2 gives a uniform bound for any such effect
under the decoder $D_n$ in (94.6), since measurement cannot increase trace
distance; it does not identify every task's optimum in (101.1).
In the task populations
$p_v=|\langle\xi,v\rangle|^2$, $q_v=|\langle e,v\rangle|^2$,
$r_v=|\langle f,v\rangle|^2$, the all-$v$, all-finite-horizon target,
the $r_v=0$, $p_vq_v>0$ root-rule candidate, and the interior
$p_vq_vr_v>0$ outside Environment (27.24) remain separate unresolved
problems. The root in (94.3) specifies the erased-history horizon-two
diamond value and makes no assertion about that task root rule.

Separate task-optimal decoders also do not determine one decoder
simultaneously attaining a prescribed collection of task optima.
The single horizon decoder here attains the whole-channel minimax
loss (93.8); that property does not assert simultaneous optimality for
each task in (101.1). The critical-spin and critical-norm estimates,
causal recovery policies, positive-error memory tradeoffs and uniform
unbounded-memory questions of Purity arithmetic Definition 50.1 and
§90 and Environment record memory §§27.8 and 28 remain distinct.
QC11's calibrated-source and delayed-catalogue bounds are not hypotheses
of Theorem 94.2. The conclusion concerns the declared actual fair
erased-history qutrit channel and terminal permissions only.

[PA]: AURIC_FIB_ACTUAL_WORD_PURITY_ARITHMETIC.md
[ENV]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[QM]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[SN]: https://quantum-journal.org/papers/q-2021-08-09-519/pdf/
[TQI2]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
[TQI3]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf
[TQIL]: ../../../Library/Quantum/watrous2018theory.md
[W12]: https://arxiv.org/pdf/1207.5726v2
[W12L]: ../../../Library/QuantumChannels/watrous2012simpler.md

## 追加锚（本行以下为增补区）
