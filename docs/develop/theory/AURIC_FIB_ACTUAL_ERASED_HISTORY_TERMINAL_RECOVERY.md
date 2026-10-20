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
## 102. Restricted-unital terminal decoders

**Definition 102.1 (Restricted terminal value).** For a finite horizon or the
limiting channel, let

$$
\delta_n^{\mathrm u}=
 \min_{\substack{D\ \mathrm{CPTP}\\D(I_3)=I_3}}
 \frac12\lVert D\mathcal N_n-\operatorname{id}_{M_3}\rVert_\diamond .
\tag{102.1}
$$

For $n\ge1$ use the bijection (93.10), and write
$\mathcal C=\mathcal R\Phi_s$. Since conjugation by $U_0$ is a unitary
channel, $D$ is unital exactly when $\mathcal R(I_3)=I_3$. Thus the
restricted problem can be studied entirely in the reduced frame.

**Theorem 102.2 (The unital equality set).** For the actual horizons,

$$
\delta_n^{\mathrm u}=\delta_n
\quad(n=0,\ n\ge1\text{ odd},\ n=\infty),
\qquad
\delta_n^{\mathrm u}>\delta_n
\quad(n\ge2\text{ finite even}).
\tag{102.2}
$$

At every finite even horizon, every unrestricted optimal terminal decoder is
therefore nonunital. The strict inequality is per horizon; no uniform lower
bound for $\delta_n^{\mathrm u}-\delta_n$ is asserted.

*Proof.* The unrestricted class contains the unital class, so the first
inequality in the comparison is always $\delta_n^{\mathrm u}\ge\delta_n$.
At $n=0$ the identity is an attainer. For every odd $n\ge1$, the decoder
$D_n=\operatorname{Ad}_{U_0^\dagger}$ in (94.6) is unitary and unital. At
the limit the identity decoder is unital and attains the value $\delta_\infty
=4/5$ in (94.2). It remains to exclude equality at a finite even horizon.

Fix such a horizon, put $s=-t$ with $t>0$, and let $p$ be the strictly
positive probe in (97.2) when $n=2$, or in (98.2) when $n\ge4$. For an
arbitrary reduced decoder define $T_{ij}$ and $\ell$ as in (95.1), put
$u=\sqrt{T_{11}}$ and $z=T_{22}$, and let $G_{\mathcal R}(p)$ and
$L_s(p;u,z)$ be (95.2) and (95.3). The exact even-sign remainder is

$$
\begin{aligned}
L_s(p;u,z)-G_{\mathcal R}(p)
={}&p_0^2(1-T_{00})
 +b p_1^2(1-z-T_{12})\\
&+b p_2^2(1-u^2-T_{21})
 +2t p_0p_1(u+\operatorname{Re}\ell).
\end{aligned}
\tag{102.3}
$$

Every term is nonnegative. The first three assertions follow from
column stochasticity and $T_{00}\le1$; for the last one,
$|\ell|^2\le T_{00}T_{11}$ gives $\operatorname{Re}\ell\ge-u$.
The lower certificate (95.4), together with the optimal value
$\delta_n=1-\eta_n$, gives for every decoder

$$
\delta_n\ge 1-G_{\mathcal R}(p)\ge1-L_s(p;u,z)\ge\delta_n
$$

whenever the decoder attains $\delta_n$. Hence equality holds throughout,
and (102.3) forces

$$
T_{00}=1,\qquad T_{12}=1-z,\qquad T_{21}=1-u^2,
\qquad \ell=-u.
\tag{102.4}
$$

Indeed all coefficients in (102.3) are strictly positive, and the last
identity uses $|\ell|\le u$. Column sums then give
$T_{10}=T_{20}=T_{01}=T_{02}=0$. If $\mathcal R$ is unital, its population
matrix is doubly stochastic; the sum of row one in (102.4) gives

$$
 z=u^2.
\tag{102.5}
$$

We next record the complete consequence of saturation in the trace-distance
certificate. Let $P_p=|\psi_p\rangle\langle\psi_p|$ and
$\rho=(\mathcal C\otimes\operatorname{id})(P_p)$. Equality in the
measurement bound in (95.4) says

$$
\frac12\lVert\rho-P_p\rVert_1
 =1-\langle\psi_p|\rho|\psi_p\rangle=1-\eta_n.
\tag{102.6}
$$
Put $H=P_p-\rho$ and write its Jordan decomposition
$H=H_+-H_-$. Since $\operatorname{Tr}H=0$,
$\operatorname{Tr}H_+=\operatorname{Tr}H_-=1-\eta_n$; and (102.6) gives
$\operatorname{Tr}(P_pH)=1-\eta_n$. Therefore
$\operatorname{Tr}(P_pH_-)=0$ and $H_+=(1-\eta_n)P_p$.
Consequently

$$
\rho=\eta_nP_p+H_-,\qquad H_-\succeq0.
\tag{102.7}
$$

Let $S=\operatorname{diag}(\sqrt{p_0},\sqrt{p_1},\sqrt{p_2})$. In the
output-first Choi convention (93.9),
$\rho=(I\otimes S)J(\mathcal C)(I\otimes S)$ and
$P_p=(I\otimes S)J(\operatorname{id})(I\otimes S)$. All $p_i$ are positive,
so the inverse congruence in (102.7) yields

$$
J(\mathcal C)-\eta_nJ(\operatorname{id})\succeq0,
\qquad
\mathcal C-\eta_n\operatorname{id}\ \text{is completely positive}.
\tag{102.8}
$$

This is a necessity for an equality case in the present weighted probe; it is
not a general trace-distance equality theorem for unrelated channels.

For $n=2$, (97.7) and the strict signs in (97.4) give

$$
L_s(p;u,z)-\eta_2=A(u-r_*)^2+Bz,
\qquad A<0,\quad B<0.
\tag{102.9}
$$

The ratio estimate (97.5) is the reason both signs are strict. Equality in
(102.9) forces $u=r_*$ and $z=0$, whereas (102.5) would require
$z=r_*^2>0$. Thus an unital decoder cannot attain $\delta_2$.

Now let $n\ge4$ be even. Use $h,r,z_*,p,\eta$ from (98.1)--(98.2), where
$z_*$ is the attainer's parameter in (94.6). Equality in (98.12) forces
$u=r$; a unital equality case would have $z=r^2$. The principal Choi block
of $\mathcal C=\mathcal R\Phi_{-t}$ on
$|00\rangle,|11\rangle,|22\rangle$, using (102.4), (102.5), is

$$
M=\begin{pmatrix}1&tr&0\\tr&q&0\\0&0&q\end{pmatrix},
\qquad q=b-tr^2.
\tag{102.10}
$$

By (102.8), $N=M-\eta\mathbf1\mathbf1^{\mathsf T}$ must be positive
semidefinite. Let $M_*$ be the block (95.5) with the same $r$ and with
$z=z_*$. Equations (98.7)--(98.10) say $M_*p=\eta\mathbf1$. Put

$$
 d=r^2-z_*
 =\frac{h-1}{h+1}
   \left[h-\left(\frac{1+h^2}{h^2+3}\right)^2\right]>0.
\tag{102.11}
$$

The positivity is immediate from $h>1$ and
$(1+h^2)/(h^2+3)<1$. Since $p_2=hp_1$ and $b=ah^2$, direct subtraction of
$M_*p=\eta\mathbf1$ from (102.10) gives

$$
Np=\begin{pmatrix}0\\-b p_1d\\a p_2d\end{pmatrix},
\qquad
p^{\mathsf T}Np=-bp_1^2d+ap_2^2d=0.
\tag{102.12}
$$

A positive semidefinite matrix whose quadratic form vanishes on $p$ must
annihilate $p$; (102.12) does not. This contradiction excludes every unital
optimal decoder at every later finite even horizon.

Finally, for fixed $n$ the unital Choi set is closed and bounded: it is
specified by complete positivity, trace preservation, and the additional
unital partial-trace constraint, while its trace is fixed at three. It is
therefore compact, and the diamond objective is continuous in the Choi
entries. The restricted minimum exists. Since it cannot equal the
unrestricted minimum by the preceding arguments, the inequality is strict.
This proves (102.2). $\square$

The parity in (102.2) is a statement about the actual horizon parameter of
this qutrit channel. A structurally related analysis in a different setting
is [Shahbeigi et al.][SHA]. That work concerns dimension $d>3$ and average
fidelity, with a dimension-parity issue rather than the horizon parity here. No general
nonunital-correction principle is inferred from either result.

## 103. Rank-one task optima and a common decoder

Use the original ordered basis (93.1), so that
$P_i=|i\rangle\langle i|$ and define

$$
Q=\frac12(|0\rangle+|2\rangle)(\langle0|+\langle2|).
\tag{103.1}
$$

For each finite $n\ge1$ and for the limiting member $s=0$, write
$\tau=|s|$, $A=(1+\tau)/2$, and $B=(1-\tau)/2$. For a reduced decoder
put

$$
 e_E(\mathcal R;s)=
 \left\|\Phi_s^\dagger(\mathcal R^\dagger(E))-E\right\|_{\rm op}.
\tag{103.2}
$$

By the effect interface in [Environment record memory, equation (27.4)][ENV],
this is exactly the supremum of the absolute expectation error over all
complex qutrit density matrices; (93.10) transports it back to the actual
terminal decoder. The terminal permissions are those of Definitions
93.1--93.3.

At each fixed horizon a common decoder is chosen before the unknown input
and the subsequently selected task from the prescribed family. It may
depend on the horizon and that family. Each individual minimum instead
allows a task-specific decoder, as in (101.1). Simultaneous attainment is
therefore an intersection of taskwise argmin sets; it is distinct from the
whole-channel half-diamond minimax (93.8).

The exact observable-correction interface of
[Bény--Kempf--Kribs, Definition 8 and Theorem 9][BKK] requires one decoder
with $\Phi_s^\dagger(\mathcal R^\dagger(X))=X$ for every $X$ in a specified
unital $*$-subalgebra of $M_3$. Here their code projection is $I_3$, since
the input space is the whole qutrit space. The present taskwise objective
allows nonzero individual residual minima and asks that one decoder attain
all of them; exact observable correction does not supply that argmin
intersection.

**Proposition 103.1 (Three individual task optima).** For every finite
$n\ge1$ and at the actual limit,

$$
\inf_{\mathcal R\ {\rm CPTP}}e_{P_0}(\mathcal R;s)=0,\qquad
\inf_{\mathcal R\ {\rm CPTP}}e_{P_2}(\mathcal R;s)=B,\qquad
\inf_{\mathcal R\ {\rm CPTP}}e_Q(\mathcal R;s)=\frac12.
\tag{103.3}
$$

At the empty horizon all three optima are zero.

*Proof.* The first value is attained by $\mathcal R=\operatorname{id}$,
since $\Phi_s^\dagger(P_0)=P_0$. For the second, let
$K=\mathcal R^\dagger(P_2)$ and $C=\Phi_s^\dagger(K)$. Since $C$ is an
effect,

$$
 e_{P_2}(\mathcal R;s)\ge\max\{C_{11},1-C_{22}\}.
$$
The displayed formula (93.5) gives $C_{22}-C_{11}\le\tau$, hence
$2e_{P_2}\ge1-\tau=2B$. If $s\ge0$, the choice $\mathcal R=\operatorname{id}$
attains $B$; if $s<0$, use the unitary swapping $|1\rangle$ and $|2\rangle$
and fixing $|0\rangle$, which makes $\mathcal R^\dagger(P_2)=P_1$ and
again gives error $B$. At $s=0$ the first choice applies.

For $Q$, every $\Phi_s^\dagger(K)$ has zero $(0,2)$ entry, while $Q_{02}=1/2$; therefore $e_Q\ge1/2$. Taking $K=I_3/2$ attains this bound, because
$\Phi_s^\dagger(I_3/2)=I_3/2$ and $I_3/2-Q$ has operator norm $1/2$.
$\square$

The two operators

$$
\begin{aligned}
\mathcal R_{0Q}(X)&=\operatorname{Tr}(P_0X)P_0
 +\operatorname{Tr}((I_3-P_0)X)P_2,\\
\mathcal R_j(X)&=\operatorname{Tr}(P_jX)P_2
 +\operatorname{Tr}((I_3-P_j)X)P_0\qquad(j=1,2)
\end{aligned}
\tag{103.4}
$$

are CPTP measure-and-prepare channels. For the first, Kraus operators are
$P_0,|2\rangle\langle1|,|2\rangle\langle2|$; for the second they are
$|2\rangle\langle j|$ and $|0\rangle\langle k|$ for $k\ne j$. Their
adjoint actions satisfy

$$
\mathcal R_{0Q}^\dagger(P_0)=P_0,
\quad \mathcal R_{0Q}^\dagger(Q)=I_3/2,
\quad
\mathcal R_j^\dagger(P_2)=P_j,
\quad \mathcal R_j^\dagger(Q)=I_3/2.
\tag{103.5}
$$

Consequently every proper subset of $\{P_0,P_2,Q\}$ has a common
individual-optimum decoder. For $\{P_0,P_2\}$ use $\operatorname{id}$ when
$s\ge0$ and the $|1\rangle\leftrightarrow|2\rangle$ swap when $s<0$.
For $\{P_0,Q\}$ use $\mathcal R_{0Q}$, and for $\{P_2,Q\}$ use
$\mathcal R_j$ with $j=2$ for $s\ge0$ and $j=1$ for $s<0$. The displayed
Kraus families prove complete positivity and trace preservation directly.
These measure-and-prepare maps are the elementary form of the
entanglement-breaking construction in
[Horodecki--Shor--Ruskai, equation (1) and Theorem 2][HSR].

**Proposition 103.2 (The common all-complex optima at the first two
horizons).** A single decoder attains every rank-one task optimum at
$n=0$ and at $n=1$. No restriction to real vectors is involved.

*Proof.* At $n=0$ take the identity. At $n=1$, $\Phi_1=\Delta_W$. Let
$W_+=P_0+P_1$ and $W_-=P_2$. For any complex unit vector $v$, write
$v=u+z$ with $u=W_+v$ and $z=W_-v$, and let $E=|v\rangle\langle v|$. Then

$$
\Delta_W(E)-E=-|u\rangle\langle z|-|z\rangle\langle u|,
\qquad
\|\Delta_W(E)-E\|_{\rm op}=\|u\|\,\|z\|.
\tag{103.6}
$$

For an arbitrary decoder, $C=\Phi_1^\dagger(\mathcal R^\dagger(E))$
is block diagonal with respect to $W_+\oplus W_-$. The $W_+$--$W_-$
compression of $C-E$ is $-|u\rangle\langle z|$, whose norm is
$\|u\|\|z\|$. Therefore $\|C-E\|_{\rm op}\ge\|u\|\|z\|$, while
$\mathcal R=\operatorname{id}$ attains equality in (103.6). The actual
terminal decoder is $D=\operatorname{Ad}_{U_0^\dagger}$ by (93.10). $\square$

## 104. A uniform three-task obstruction

For the later actual horizons

$$
\mathcal S_{\rm late}
=\{(-1/2)^{n-1}:n\ge2\}\cup\{0\},
\tag{104.1}
$$

define the triple regret

$$
\Gamma_T(s)=\inf_{\mathcal R\ {\rm CPTP}}
 \max\left\{e_{P_0}(\mathcal R;s),
 e_{P_2}(\mathcal R;s)-B,
 e_Q(\mathcal R;s)-\frac12\right\},
\qquad T=\{P_0,P_2,Q\}.
\tag{104.2}
$$

**Theorem 104.1 (Quantitative incompatibility of the triple).** For every
$s\in\mathcal S_{\rm late}$,

$$
\Gamma_T(s)\ge\frac1{250}>\frac1{256}.
\tag{104.3}
$$

*Proof.* Here $0\le\tau\le1/2$, so $1/2\le A\le3/4$ and
$B\le A$. Suppose that a CPTP $\mathcal R$ has all three quantities in
(104.2) at most $\gamma$, with $0\le\gamma\le1/250$. Put

$$
\sigma_i=\mathcal R(\Phi_s(P_i))\qquad(i=0,1,2).
$$

The $P_0$ bound, evaluated on inputs $P_1$ and $P_2$, gives
$(\sigma_1)_{00},(\sigma_2)_{00}\le\gamma$. For $s\ge0$, put
$v=\langle2|\mathcal R(P_1)|2\rangle$ and
$w=\langle2|\mathcal R(P_2)|2\rangle$. Then

$$
(\sigma_1)_{22}=Av+Bw\le B+\gamma,
\qquad
(\sigma_2)_{22}=Bv+Aw\le A+\frac BA\gamma\le A+\gamma.
\tag{104.4}
$$

The second inequality follows by writing the second expression as
$(B/A)(Av+Bw)+(A^2-B^2)w/A$. For $s<0$ the two input populations are
interchanged and the same calculation applies; at $s=0$ it remains valid
with $A=B=1/2$. Thus, with
$x=(\sigma_2)_{00}$ and $y=(\sigma_2)_{22}$,

$$
0\le x\le\gamma,\qquad 0\le y\le A+\gamma.
$$

Positivity of $\sigma_2$ gives
$|(\sigma_2)_{02}|\le\sqrt{xy}$. Since
$C=\Phi_s^\dagger(\mathcal R^\dagger(Q))$ has
$C_{22}=\operatorname{Tr}(Q\sigma_2)$, we obtain

$$
C_{22}\le\frac{x+y}{2}+\sqrt{xy}
 \le\frac38+\gamma+\sqrt{\gamma(3/4+\gamma)}.
\tag{104.5}
$$

At $\gamma=1/250$ the last expression is
$(379+\sqrt{3016})/1000<434/1000=217/500$; it is increasing in
$\gamma$, so this bound holds throughout the assumed interval. The erased
$(0,2)$ entry of every $\Phi_s^\dagger(K)$ gives

$$
(C-Q)|2\rangle=-\tfrac12|0\rangle+(C_{22}-\tfrac12)|2\rangle,
$$

and hence

$$
 e_Q(\mathcal R;s)^2
 \ge\frac14+(C_{22}-\tfrac12)^2
 >\frac14+\left(\frac{33}{500}\right)^2
 =\frac{63589}{250000}
 >\left(\frac12+\frac1{250}\right)^2.
\tag{104.6}
$$

This contradicts the assumed third bound. Therefore every decoder has the
maximum in (104.2) greater than $1/250$, which implies (104.3) for its
infimum. The CPTP Choi set is compact and the three task losses are
continuous, so the infimum is also a minimum; this observation is not
needed for the numerical lower bound. $\square$

**Theorem 104.2 (Exact horizon set and minimal witness).** There exists a
single terminal decoder attaining the individual optimum of every rank-one
task exactly at the empty horizon and at the one-step horizon, and at no
other actual finite horizon. The same failure holds at the actual limiting
channel. The witness $T=\{P_0,P_2,Q\}$ is inclusion-minimal: every proper
subset has a common attainer, while (104.3) holds for all
$s\in\mathcal S_{\rm late}$.

*Proof.* Proposition 103.2 proves existence at $n=0,1$. If a decoder were
optimal for every rank-one task at a later horizon or at the limit, it would
be optimal simultaneously for the three tasks in $T$, contradicting
Theorem 104.1. Proposition 103.1 and (103.4)--(103.5) show that every
proper pair, and hence every proper subset, has a common individual-optimum
attainer. Thus the exact finite set is $\{0,1\}$, with the actual limit
excluded as well. The claim is only inclusion-minimality of this particular
triple; it does not assert that all pairs are compatible or that three is a
global minimum obstruction size. $\square$

The effect formulation (103.2) is the standard worst-state/operator-norm
interface used in the task definition; see [Janssens, §2][JAN]. His
convention for completely positive maps includes unitality, as holds for
the adjoint of every CPTP decoder here. For a unital completely positive
map, the multiplicative-domain criterion uses both Schwarz equalities; see
[Choi--Johnston--Kribs, Theorem 8][CJK]. No multiplicative-domain
classification is needed for the displayed pair constructions or for the
PSD obstruction. The Choi positivity and trace-preservation interfaces are
those recorded in [Watrous, Chapter 2, Theorems 2.22 and 2.26][TQI2].

[HSR]: https://arxiv.org/pdf/quant-ph/0302031v2 "M. Horodecki, P. W. Shor and M. B. Ruskai, Entanglement Breaking Channels"
[CJK]: https://arxiv.org/pdf/0811.0947v1 "M.-D. Choi, K. Johnston and D. W. Kribs, The Multiplicative Domain in Quantum Error Correction"
[JAN]: https://arxiv.org/pdf/quant-ph/0606093v1 "G. Janssens, Unifying Decoherence and the Heisenberg Principle"
[SHA]: https://arxiv.org/abs/2104.06062 "Shahbeigi et al., Journal of Physics A 54, 345301 (2021)"
[BKK]: https://arxiv.org/pdf/0705.1574 "C. Bény, A. Kempf and D. W. Kribs, Quantum Error Correction of Observables"

## 追加锚（本行以下为增补区）

## 105. Terminal recovery tested without a reference

**Definition 105.1 (No-reference minimax).** Keep the complex qutrit,
original identity target and actual powers $\mathcal N_n=F^n$ of
Definition 93.1. Write

$$
d(\rho,\tau)=\frac12\|\rho-\tau\|_1,\qquad
\mu_n=\min_{D\ {\rm CPTP}}\ \max_{\rho\in\mathsf D(\mathbb C^3)}
 d(D\mathcal N_n(\rho),\rho).
\tag{105.1}
$$

For each horizon, one terminal CPTP map $D:M_3\to M_3$ is chosen before
the unknown input. The input set contains every complex density matrix,
including mixed states and pure states with arbitrary complex phases.
The decoder receives only the terminal qutrit. There is no reference
input or reference access, history register, intermediate correction,
postselection or restriction to a smaller input code. A CPTP decoder may
use an internal ancillary system and discard it, as usual; its induced
map on the qutrit is still the single map in (105.1).

For the channel $\Phi_s$ in (93.5), define

$$
e_s(\mathcal R)=\max_{\rho\in\mathsf D(\mathbb C^3)}
 d(\mathcal R\Phi_s(\rho),\rho),\qquad
\mu(s)=\min_{\mathcal R\ {\rm CPTP}}e_s(\mathcal R),
\qquad -\frac12\le s\le1.
\tag{105.2}
$$

The precise correspondence (93.10) gives

$$
\mathcal N_n=\operatorname{Ad}_{U_0}\circ\Phi_{s_n},\qquad
\mathcal R=D\circ\operatorname{Ad}_{U_0},\qquad
D=\mathcal R\circ\operatorname{Ad}_{U_0^\dagger},\qquad
\mu_n=\mu(s_n)\quad(n\ge1).
\tag{105.3}
$$

At infinity, (93.7) gives $\mu_\infty=\mu(0)$. The empty horizon instead
has $\mathcal N_0=\operatorname{id}$; it is not the parameter $s=0$.
No additional unitary is applied to the target in (105.3).

**Lemma 105.2 (Physical parameter interval and attainment).** The map
$\Phi_s$ is CPTP exactly for real $s\in[-1/2,1]$. Every maximum and minimum
in (105.1)–(105.2) is attained.

*Proof.* Put $a=(1+s)/2$ and $b=(1-s)/2$. On the stated interval a Kraus
representation of $\Phi_s$ is

$$
\operatorname{diag}(1,s,0),\quad
\sqrt{a-s^2}\,|1\rangle\langle1|,\quad
\sqrt a\,|2\rangle\langle2|,\quad
\sqrt b\,|2\rangle\langle1|,\quad
\sqrt b\,|1\rangle\langle2|.
\tag{105.4}
$$

Here $a-s^2=(1-s)(1+2s)/2\ge0$, and the adjoint products sum to $I$.
Conversely positivity of the output populations requires $a,b\ge0$.
In the output-first convention (93.9), the Choi principal block on
$|00\rangle,|11\rangle$ is $\left(\begin{smallmatrix}1&s\\s&a\end{smallmatrix}\right)$.
Complete positivity therefore requires $a-s^2\ge0$, which together with
$a,b\ge0$ gives exactly $-1/2\le s\le1$.

The density matrices form a compact set. The Choi matrices of qutrit
CPTP maps form the compact set
$\{J\ge0:\operatorname{Tr}_{\rm out}J=I\}$: it is closed and every
member has trace three. The error is continuous in the channel and input.
Maximizing over a compact input set preserves continuity, and minimizing
over the compact decoder set attains the minimum. $\square$

**Lemma 105.3 (Inputs, metric and continuity).** For each fixed decoder,
the input maximum in (105.2) equals the maximum over pure states. Moreover

$$
|e_s(\mathcal R)-e_t(\mathcal R)|\le |s-t|,
\qquad |\mu(s)-\mu(t)|\le |s-t|
\quad(s,t\in[-1/2,1]).
\tag{105.5}
$$

*Proof.* The error is convex in $\rho$. A spectral decomposition of any
mixed density matrix bounds its error by a convex combination of pure
input errors, hence by the largest such error. The reverse inequality
holds because pure states are among the allowed inputs.

For any Hermitian traceless $3\times3$ matrix $X$,

$$
\frac12\|X\|_1=\|X\|_{\rm op}.
\tag{105.6}
$$

Indeed, unless $X=0$, the sum of its positive eigenvalues equals the sum
of the absolute values of its negative eigenvalues. In dimension three,
at least one of these two sums consists of a single eigenvalue, whose
absolute value is at least that of each other eigenvalue. Every recovery
error on a density input has this Hermitian traceless form. Equation
(105.6) does not identify (105.2) with an induced Schatten norm whose
supremum also includes arbitrary non-Hermitian matrices.

For a density matrix $\rho$, write $z=\rho_{01}$ and
$h=(\rho_{11}-\rho_{22})/2$. Directly from (93.5),

$$
(\Phi_s-\Phi_t)(\rho)=(s-t)
 \begin{pmatrix}0&z&0\\\overline z&h&0\\0&0&-h\end{pmatrix},
\qquad
\frac12\|(\Phi_s-\Phi_t)(\rho)\|_1
 \le |s-t|(|z|+|h|)\le |s-t|.
\tag{105.7}
$$

The first bound splits the matrix into its off-diagonal and diagonal
parts. Positivity gives $|z|\le\sqrt{\rho_{00}\rho_{11}}\le1/2$,
and $|h|\le1/2$. A CPTP map contracts the trace norm of Hermitian
matrices: applying it to the positive and negative parts proves this
from positivity and trace preservation. The reverse triangle inequality
and (105.7) thus bound the change in each input error by $|s-t|$,
uniformly in the decoder. Taking input maxima and then decoder minima
proves (105.5). $\square$

## 106. Exact Fourier guessing and a lower bound for every decoder

Let $E_{ij}=|i\rangle\langle j|$, $Q_j=E_{jj}$,
$Q_{01}=Q_0+Q_1$, and $\omega=e^{2\pi i/3}$. Define the Fourier basis
and its output ensemble by

$$
|\psi_k\rangle=\frac{|0\rangle+\omega^k|1\rangle+
                              \omega^{2k}|2\rangle}{\sqrt3},
\quad P_k=|\psi_k\rangle\langle\psi_k|,
\quad \sigma_k=\Phi_s(P_k)=\frac{I+sA_k}{3},
\quad A_k=\omega^{-k}E_{01}+\omega^k E_{10},
\quad k=0,1,2.
\tag{106.1}
$$

The projectors $P_k$ are pairwise orthogonal and sum to $I$, since
$1+\omega+\omega^2=0$. The outputs form an equiprobable geometrically
uniform ensemble:
$\sigma_k=S^k\sigma_0S^{-k}$ with
$S=\operatorname{diag}(1,\omega,\omega^2)$.
The primal POVM and dual positive-operator formulations for this setting
are those of [Assalini–Cariolaro–Pierobon, §§II–III][ACP-FG]. The following
calculation gives both certificates for the particular ensemble (106.1).

**Theorem 106.1 (Fourier guessing).** For every $-1/2\le s\le1$, the
optimal equal-prior guessing probability for $\{\sigma_0,\sigma_1,\sigma_2\}$
is exactly

$$
G(s)=\max_{\substack{M_k\ge0\\\sum_kM_k=I}}
       \frac13\sum_{k=0}^2\operatorname{Tr}(M_k\sigma_k)
     =\frac13+\frac{2|s|}{9}.
\tag{106.2}
$$

*Proof.* Write $q=|s|$. The matrices $A_k$ satisfy

$$
A_k^\dagger=A_k,\qquad A_k^2=Q_{01},\qquad
\operatorname{Tr}A_k=0,\qquad \sum_kA_k=0.
\tag{106.3}
$$

For $s\ne0$ put $\varepsilon=\operatorname{sign}s$. The operators

$$
M_k=\frac{I+\varepsilon A_k}{3}
\tag{106.4}
$$

are positive, have eigenvalues $0,1/3,2/3$, and sum to $I$. Each one gives

$$
\operatorname{Tr}(M_k\sigma_k)
 =\frac{\operatorname{Tr}I+\varepsilon s\operatorname{Tr}Q_{01}}9
 =\frac13+\frac{2q}{9}.
\tag{106.5}
$$

The equal-prior average has the same value. At $s=0$ use $M_k=I/3$.

For the dual certificate set

$$
Y=\frac I9+\frac q9Q_{01},\qquad
Y-\frac{\sigma_k}{3}=\frac{qQ_{01}-sA_k}{9}\ge0,
\qquad \operatorname{Tr}Y=\frac13+\frac{2q}{9}.
\tag{106.6}
$$

The residual has eigenvalues $0,0,2q/9$: in the $01$ block its diagonal
entries are $q/9$ and its off-diagonal entries are
$-s\omega^{-k}/9,-s\omega^k/9$. In particular the $Q_0,Q_1$ in this
certificate are computational projectors, not Fourier projectors.
For any POVM $\{N_k\}$, the trace of the product of two positive matrices
is nonnegative, so

$$
\frac13\sum_k\operatorname{Tr}(N_k\sigma_k)
 \le\sum_k\operatorname{Tr}(N_kY)=\operatorname{Tr}Y.
\tag{106.7}
$$

The displayed primal attains the dual value, proving (106.2), including
$q=0$. $\square$

**Theorem 106.2 (All-decoder obstruction).** On the entire physical
parameter interval,

$$
\boxed{\displaystyle
\mu(s)\ge\max\left\{\frac12,\frac23-\frac{2|s|}{9}\right\}.}
\tag{106.8}
$$

*Proof.* Fix an arbitrary CPTP decoder $\mathcal R$. Its adjoint is CP
and unital, so $N_k=\mathcal R^\dagger(P_k)$ form a POVM. By (106.2),

$$
\frac13\sum_k\operatorname{Tr}
       [P_k\mathcal R\Phi_s(P_k)]
 =\frac13\sum_k\operatorname{Tr}(N_k\sigma_k)\le G(s).
\tag{106.9}
$$

Consequently some $k$, allowed to depend on this fixed decoder, has
$\operatorname{Tr}[P_k\mathcal R\Phi_s(P_k)]\le G(s)$.
For any state $\tau$ and rank-one projector $P$, the trace-distance
variational formula, tested on the effect $P$, gives
$d(\tau,P)\ge1-\operatorname{Tr}(P\tau)$. Thus

$$
e_s(\mathcal R)\ge
 d(\mathcal R\Phi_s(P_k),P_k)\ge1-G(s)
 =\frac23-\frac{2|s|}{9}.
\tag{106.10}
$$

Independently, the two orthogonal pure states

$$
H_\pm=|a_\pm\rangle\langle a_\pm|,
\qquad |a_\pm\rangle=(|0\rangle\pm|2\rangle)/\sqrt2
\tag{106.11}
$$

have the identical output
$\Phi_s(H_\pm)=\operatorname{diag}(1/2,(1-s)/4,(1+s)/4)$.
Their decoded outputs are therefore the same state $\tau$.
The triangle inequality yields
$1=d(H_+,H_-)\le d(H_+,\tau)+d(\tau,H_-)$, and hence
$e_s(\mathcal R)\ge1/2$. Both bounds hold for each decoder separately.
Taking its minimum proves (106.8), without exchanging the input and
decoder quantifiers. $\square$

## 107. Endpoints, positive parameters and actual finite intervals

**Lemma 107.1 (Replacer and the zero-parameter identity decoder).** The
CPTP replacer $\mathcal T(X)=\operatorname{Tr}(X)I/3$ has
$e_s(\mathcal T)=2/3$ for every physical $s$. Also
$e_0(\operatorname{id})=2/3$. Its pure maximizing inputs are exactly
those with $p_0=1/3$, where $p_j=|\langle j,v\rangle|^2$.

*Proof.* Kraus operators $E_{ij}/\sqrt3$ realize $\mathcal T$.
For every pure state $P$, $I/3-P$ has eigenvalues $-2/3,1/3,1/3$.
Convexity handles mixed inputs and gives the stated replacer error.

For the identity decoder at $s=0$, put $t=p_1+p_2$.
A unitary on $\operatorname{span}\{|1\rangle,|2\rangle\}$ sends the lower
part of a pure input to $(\sqrt t,0)$ and leaves the lower output
$tI_2/2$ invariant. After also removing the upper phase, its error is
unitarily conjugate to

$$
\begin{pmatrix}
0&-\sqrt{t(1-t)}&0\\
-\sqrt{t(1-t)}&-t/2&0\\
0&0&t/2
\end{pmatrix}.
\tag{107.1}
$$

The eigenvalues are $t/2$ and
$(-t\pm\sqrt{t(16-15t)})/4$. Since
$\sqrt{t(16-15t)}\ge t$ on $[0,1]$, (105.6) gives the error

$$
f(t)=\frac{t+\sqrt{t(16-15t)}}4\le\frac23.
\tag{107.2}
$$

Indeed $8/3-t>0$ and

$$
(8/3-t)^2-t(16-15t)=16(t-2/3)^2.
\tag{107.3}
$$

Equality holds exactly at $t=2/3$. At every such input $P$,
$\Phi_0(P)=I/3$ and the error is $I/3-P$. $\square$

**Proposition 107.2 (Endpoints and positive-branch upper bound).**

$$
\mu_0=0,\qquad \mu_1=\mu(1)=\frac12,\qquad
\mu_\infty=\mu(0)=\frac23,
\tag{107.4}
$$

and, for $0\le s\le1$,

$$
e_s(\operatorname{id})=\frac23-\frac{s}{6},\qquad
\mu(s)\le\frac23-\frac{s}{6}.
\tag{107.5}
$$

*Proof.* The empty horizon is recovered exactly by the identity decoder.
At parameter one, $\Phi_1$ is pinching into the $01$ block and the $2$
block. For a pure state with population $p_2$, its error has eigenvalues
$0,\pm\sqrt{p_2(1-p_2)}$, so
$e_1(\operatorname{id})=1/2$. The lower bound (106.8) proves
$\mu(1)=1/2$. At parameter zero, (106.8) and the replacer prove
$\mu(0)=2/3$.

Linearity gives $\Phi_s=s\Phi_1+(1-s)\Phi_0$ for $0\le s\le1$.
The triangle inequality and Lemma 107.1 therefore give the upper bound
in (107.5) for every density input. To see equality for this fixed
decoder, use the pure state with real coordinates

$$
v=(\sqrt{1/3},\sqrt{1/6},\sqrt{1/2})^{\mathsf T},\qquad P=vv^\dagger.
\tag{107.6}
$$

Here $(\Phi_0(P)-P)v=-2v/3$, and direct block pinching gives
$(\Phi_1(P)-P)v=-v/2$. Thus
$(\Phi_s(P)-P)v=-(2/3-s/6)v$. Its error is at least $2/3-s/6$,
matching the upper bound. This proves the identity-decoder value,
without asserting that this decoder minimizes (105.2). $\square$

**Corollary 107.3 (Actual-horizon intervals and convergence).** For
$q_n=2^{1-n}$, the exact transport (105.3) yields

$$
\begin{aligned}
\frac23-\frac{2q_n}{9}\le\mu_n\le\frac23
 &&(n\ge2\text{ even}),\\
\frac23-\frac{2q_n}{9}\le\mu_n\le\frac23-\frac{q_n}{6}
 &&(n\ge3\text{ odd}).
\end{aligned}
\tag{107.7}
$$

In particular,

$$
\frac59\le\mu_2\le\frac23,\qquad
\frac{11}{18}\le\mu_3\le\frac58.
\tag{107.8}
$$

*Proof.* Even horizons have $s_n=-q_n$, and odd horizons have $s_n=q_n$.
For every $n\ge2$, $0<q_n\le1/2$, so the Fourier term of (106.8)
is greater than $1/2$. Use the replacer for the even upper bound
and (107.5) for the odd upper bound. In the original coordinates the
latter decoder is $\operatorname{Ad}_{U_0^\dagger}$, by (93.10).
Substitution of $q_2=1/2,q_3=1/4$ gives (107.8). Also

$$
0\le\frac23-\mu_n\le\frac{2q_n}{9}\quad(n\ge2),
\qquad \lim_{n\to\infty}\mu_n=\frac23.
\tag{107.9}
$$

This agrees with continuity (105.5) and $\mu(0)=2/3$.
No finite $s_n$ is zero. $\square$

The interval widths in (107.7) are $2q_n/9$ for even horizons and
$q_n/18$ for odd horizons. These are upper and lower certificates for
the common-decoder, all-input problem; they do not give its exact value
at any actual finite $n\ge2$.

## 108. A CPTP family for the negative branch

For parameters

$$
0<u<1,\qquad 0<\eta\le\sqrt{(1-u)/2},\qquad
 a_u=\frac{1-u}{2},\quad b_u=\frac{1+u}{2},
\tag{108.1}
$$

define a terminal map on every complex matrix by

$$
\mathcal R_{u,\eta}(X)=
\begin{pmatrix}
x_{00}&-\eta x_{01}&0\\
-\eta x_{10}&a_u x_{11}+b_u x_{22}&0\\
0&0&b_u x_{11}+a_u x_{22}
\end{pmatrix}.
\tag{108.2}
$$

**Lemma 108.1 (Complete positivity and exact composition).** The map
(108.2) is CPTP, including the equality case in (108.1). For
$0\le q\le1/2$, its composition
$\Lambda_q=\mathcal R_{u,\eta}\circ\Phi_{-q}$ is

$$
\Lambda_q(X)=
\begin{pmatrix}
x_{00}&q\eta x_{01}&0\\
q\eta x_{10}&\frac{1+uq}{2}x_{11}+\frac{1-uq}{2}x_{22}&0\\
0&0&\frac{1-uq}{2}x_{11}+\frac{1+uq}{2}x_{22}
\end{pmatrix},\qquad \Lambda_0=\Phi_0.
\tag{108.3}
$$

*Proof.* Kraus operators for (108.2) are

$$
\operatorname{diag}(1,-\eta,0),\quad
\sqrt{a_u-\eta^2}\,|1\rangle\langle1|,\quad
\sqrt{a_u}\,|2\rangle\langle2|,\quad
\sqrt{b_u}\,|2\rangle\langle1|,\quad
\sqrt{b_u}\,|1\rangle\langle2|.
\tag{108.4}
$$

All square roots are real and nonnegative, and the adjoint products sum
to $I$. Composition multiplies the lower population mixing parameters
$-u$ and $-q$, giving $uq$, and multiplies the surviving coherence
parameters $-\eta$ and $-q$, giving $q\eta$. This gives (108.3) on every
matrix unit. $\square$

Both $\Phi_{-q}$ and $\mathcal R_{u,\eta}$ commute with conjugation by
every diagonal unitary. For a pure input
$z_j=e^{i\theta_j}\sqrt{p_j}$, its recovery error is therefore a diagonal
unitary conjugate of the error at

$$
v(p)=(\sqrt{p_0},\sqrt{p_1},\sqrt{p_2})^{\mathsf T},\qquad
P(p)=v(p)v(p)^\dagger,\qquad
\mathcal P=\{p_j\ge0:\ p_0+p_1+p_2=1\}.
\tag{108.5}
$$

When a coordinate vanishes its phase is immaterial. The matrices are
continuous on this entire closed simplex. By Lemma 105.3 and (105.6),

$$
E_{u,\eta}(q):=e_{-q}(\mathcal R_{u,\eta})
 =\max_{p\in\mathcal P}f_q(p),\qquad
f_q(p)=\|\Delta(q,p)\|_{\rm op},\qquad
\Delta(q,p)=\Lambda_q(P(p))-P(p).
\tag{108.6}
$$

Thus this maximization includes every complex pure input and every
mixed input, rather than only the real-coordinate representatives used
to compute it. Directly from (108.3),

$$
\Delta(q,p)=\Delta(0,p)+qB(p),\qquad
B(p)=
\begin{pmatrix}
0&\eta\sqrt{p_0p_1}&0\\
\eta\sqrt{p_0p_1}&u(p_1-p_2)/2&0\\
0&0&-u(p_1-p_2)/2
\end{pmatrix}.
\tag{108.7}
$$

By Lemma 107.1 the full maximizing set at zero is

$$
\mathcal S=\{(1/3,x,2/3-x):\ 0\le x\le2/3\},\qquad
f_0|_{\mathcal S}=\frac23,\qquad
\Delta(0,p)=I/3-P(p)\quad(p\in\mathcal S).
\tag{108.8}
$$

The last matrix has eigenvalues $-2/3,1/3,1/3$. Its minimum eigenvalue
is simple with normalized eigenvector $v(p)$, even at the endpoints
$x=0$ and $x=2/3$. Its first variation in $q$ is

$$
\begin{aligned}
g(x)&=v(p)^\dagger B(p)v(p)
 =\frac u2(p_1-p_2)^2+2\eta p_0p_1\\
 &=2u(x-1/3)^2+\frac{2\eta}{3}x.
\end{aligned}
\tag{108.9}
$$

The two nonnegative terms cannot both vanish. Hence

$$
\kappa(u,\eta)=\min_{0\le x\le2/3}g(x)>0.
\tag{108.10}
$$

Its explicit value follows by completing the square:

$$
g(x)=2u\left(x-\frac13+\frac{\eta}{6u}\right)^2
       +\frac{\eta(4u-\eta)}{18u},\qquad
\kappa(u,\eta)=
\begin{cases}
\displaystyle\frac{\eta(4u-\eta)}{18u},&0<\eta\le2u,\\[5pt]
\displaystyle\frac{2u}{9},&\eta\ge2u.
\end{cases}
\tag{108.11}
$$

Here $u>0$ ensures the denominators are nonzero. In the first case the
quadratic's vertex $1/3-\eta/(6u)$ belongs to $[0,2/3]$; in the second
it is nonpositive, so the interval minimum is at zero. The cases agree
at $\eta=2u$ and always retain the CPTP restriction (108.1).

## 109. Uniform maximizer envelope and a strict negative tail

**Theorem 109.1 (Fixed-decoder negative-branch expansion).** For each
fixed admissible pair $(u,\eta)$ in (108.1),

$$
E_{u,\eta}(q)=\frac23-\kappa(u,\eta)q+o(q)
\qquad(q\downarrow0).
\tag{109.1}
$$

The remainder is for the maximum over the full input set in (105.2).

*Proof.* Put $M=2/3$. The simplex $\mathcal P$ is compact, and both
$\Delta(0,p)$ and $B(p)$ are continuous on it. At each $p\in\mathcal S$,
the minimum eigenvalue has gap one from the other two eigenvalues,
and its absolute value exceeds theirs by $1/3$. Compactness and
continuity of the ordered Hermitian eigenvalues give a relative open
neighborhood $\mathcal U$ of $\mathcal S$ in $\mathcal P$, with compact
closure, and $\epsilon>0$, such that on
$[0,\epsilon]\times\overline{\mathcal U}$ the minimum eigenvalue stays
simple and its absolute value alone determines the operator norm.
In particular

$$
f_q(p)=-\lambda_{\min}(\Delta(q,p))
\quad(0\le q\le\epsilon,\ p\in\overline{\mathcal U}).
\tag{109.2}
$$

No differentiability with respect to $p$ is needed here, including at
zero coordinates. To make the uniformity explicit, write the ordered
eigenvalues as $\lambda_1<\lambda_2\le\lambda_3$. The minimum-eigenvalue
projector on this neighborhood is the continuous matrix

$$
\Pi(q,p)=
\frac{(\Delta(q,p)-\lambda_2I)(\Delta(q,p)-\lambda_3I)}
     {(\lambda_1-\lambda_2)(\lambda_1-\lambda_3)}.
\tag{109.3}
$$

The denominator is bounded away from zero after shrinking the
neighborhood and $\epsilon$ if necessary; equality of $\lambda_2$ and
$\lambda_3$ causes no difficulty. For fixed $p$, the variational
characterization of the minimum eigenvalue bounds its difference
quotient between the expectations of $B(p)$ in the two corresponding
minimum eigenspaces. Continuity of $\Pi$ then gives

$$
\partial_q f_q(p)=-\operatorname{Tr}(\Pi(q,p)B(p)).
\tag{109.4}
$$

This derivative is jointly continuous on the compact neighborhood.
Integrating in $q$ proves

$$
f_q(p)=f_0(p)+q h(p)+r(q,p),\qquad
h(p)=-\operatorname{Tr}(\Pi(0,p)B(p)),\qquad
\sup_{p\in\overline{\mathcal U}}\frac{|r(q,p)|}{q}\longrightarrow0.
\tag{109.5}
$$

Indeed the quotient is bounded by

$$
\sup_{0\le a\le q,\,p\in\overline{\mathcal U}}
|\partial_a f_a(p)-h(p)|,
$$

which tends to zero by uniform continuity. On $\mathcal S$, (108.9)
gives $h(1/3,x,2/3-x)=-g(x)$.

It remains to pass from this neighborhood to the global input maximum.
Let $L=\max_{p\in\mathcal P}\|B(p)\|_{\rm op}$. The reverse triangle
inequality gives $|f_q(p)-f_0(p)|\le Lq$ throughout $\mathcal P$.
For any maximizer $p_q$ of $f_q$, comparison with a point of $\mathcal S$
therefore yields

$$
E_{u,\eta}(q)\ge M-Lq,\qquad f_0(p_q)\ge M-2Lq.
\tag{109.6}
$$

Every accumulation point of such maximizers as $q\downarrow0$ belongs
to the exact maximizing set $\mathcal S$. Thus all global maximizers
lie in $\mathcal U$ for sufficiently small $q$: otherwise a sequence
outside that neighborhood would have an accumulation point outside
$\mathcal U$ but inside $\mathcal S$.

Using (109.5) at these maximizers gives

$$
\frac{E_{u,\eta}(q)-M}{q}
 =\frac{f_0(p_q)-M}{q}+h(p_q)+o(1)
 \le h(p_q)+o(1).
\tag{109.7}
$$

Compactness and localization imply that the limsup is at most
$\max_{\mathcal S}h=-\kappa(u,\eta)$. Choose a fixed $p_*\in\mathcal S$
minimizing $g$. Then (109.5) at $p_*$ gives the reverse bound

$$
E_{u,\eta}(q)\ge f_q(p_*)=M-\kappa(u,\eta)q+o(q).
\tag{109.8}
$$

The liminf and limsup agree, proving (109.1). $\square$

**Corollary 109.2 (Explicit strict tail).** Set

$$
u_* =\frac{\sqrt{33}-1}{16},\qquad
\eta_*=2u_*,\qquad
\kappa_* =\frac{\sqrt{33}-1}{72}>0.
\tag{109.9}
$$

Then $0<u_*<1$, and $8u_*^2+u_*-1=0$ gives
$\eta_*^2=(1-u_*)/2$. Thus the decoder is CPTP even at the saturated
constraint. Equation (108.9) becomes
$g(x)=2u_*x^2+2u_*/9$, so its minimum is $\kappa_*=2u_*/9$.
There exists $q_0\in(0,1/2]$ such that

$$
\mu(-q)\le e_{-q}(\mathcal R_{u_*,\eta_*})
 \le\frac23-\frac{\kappa_*}{2}q
 =\frac23-\frac{\sqrt{33}-1}{144}q<\frac23
\quad(0<q<q_0).
\tag{109.10}
$$

*Proof.* Divide the remainder in (109.1) by $q$ and choose a positive
neighborhood on which its absolute value is at most $\kappa_*/2$.
The minimax is at most the error of this particular decoder. $\square$

Since $q_n=2^{1-n}\to0$, every sufficiently large even actual horizon
satisfies

$$
\mu_n\le\frac23-\frac{\sqrt{33}-1}{144}\,2^{1-n}<\frac23.
\tag{109.11}
$$

In the original coordinates the legal decoder is
$D=\mathcal R_{u_*,\eta_*}\circ\operatorname{Ad}_{U_0^\dagger}$.
It is a single CPTP map for all inputs, with the permissions in
Definition 105.1. Equation (109.1) is the asymptotic error of a fixed
decoder; it is not an asymptotic equality for $\mu(-q)$. The existence
of $q_0$ supplies no numerical threshold and makes no assertion about
every individual even horizon.

## 110. A uniform gap from stabilized terminal recovery

Use exactly $\delta_n$ of (93.8): a reference may participate in the
input test and remains untouched, while the decoder still acts only on
the terminal qutrit. This differs from (105.1) in its input test, not in
the decoder's available registers. The stabilized trace-norm convention
is the one cited in §93 from [Watrous, Chapter 3][TQI3]. Its operational
channel-comparison setting, with auxiliary input systems and CPTP
composition, is also developed in [Jenčová][JC-COMP].

**Lemma 110.1 (Comparison and power monotonicity).** For all horizons,
$\mu_n\le\delta_n$. For finite $n\ge0$,

$$
\delta_n\le\delta_{n+1}.
\tag{110.1}
$$

*Proof.* For each fixed decoder, the reference tests in (93.8) include
every no-reference density input, by taking a one-dimensional reference.
Its stabilized error therefore dominates its error in (105.1).
Taking decoder minima preserves this inequality.

For every CPTP decoder $D$ at horizon $n+1$, $D\circ F$ is a legal
terminal CPTP decoder at horizon $n$, and the original powers obey

$$
(D\circ F)\circ F^n=D\circ F^{n+1}.
\tag{110.2}
$$

These recovered channels are identical also after tensoring with any
untouched reference. Hence $\delta_n$ is at most the stabilized error
of $D$ at horizon $n+1$. Minimize over that $D$ to obtain (110.1).
The composition is $D\circ F$, with no operation on the reference.
$\square$

**Theorem 110.2 (Uniform stabilized-versus-no-reference gap).** For every
finite $n\ge2$, and also at the limiting channel,

$$
\boxed{\displaystyle
\delta_n-\mu_n\ge\delta_2-\frac23>\frac{2}{87}.}
\tag{110.3}
$$

At the two smaller horizons the gap is zero, and its exact limit is

$$
\delta_0-\mu_0=\delta_1-\mu_1=0,\qquad
\lim_{n\to\infty}(\delta_n-\mu_n)
 =\delta_\infty-\mu_\infty=\frac{2}{15}.
\tag{110.4}
$$

*Proof.* Theorem 94.2, (94.3)–(94.4), gives

$$
\delta_2=1-\frac3{H(r_*)},\qquad
H(r)=7+r^2-4r+\frac4{1-r^2},\qquad 0<r_*<\frac13.
\tag{110.5}
$$

The denominator $1-r_*^2$ is positive, and the exact identity

$$
H(r_*)-\frac{29}{3}
 =r_*^2+4\left(\frac13-r_*\right)
       +\frac{4r_*^2}{1-r_*^2}>0
\tag{110.6}
$$

implies $H(r_*)>29/3>9$. Consequently

$$
\delta_2-\frac23
 =\frac13-\frac3{H(r_*)}
 >\frac13-\frac9{29}=\frac2{87}.
\tag{110.7}
$$

For $n\ge2$, Lemma 110.1 gives $\delta_n\ge\delta_2$ and the legal
replacer gives $\mu_n\le2/3$. These prove (110.3) at every such finite
horizon. By (94.9) and (107.9), the two sequences converge respectively
to $4/5$ and $2/3$. Taking their difference proves both the limiting
case of (110.3) and the limit $4/5-2/3=2/15$. Finally Theorem 94.2 and
(107.4) give identical values zero at horizon zero and $1/2$ at horizon
one, proving the two zero gaps. $\square$

This proof uses the exact stabilized horizon-two theorem, the original
power composition and a no-reference replacer. The comparison
$\mu_n\le\delta_n$ alone would not yield a strictly positive gap.
The constants in (110.3)–(110.4) concern the declared half trace-distance
and half diamond-distance conventions throughout; no reference is made
available to a decoder.

## 111. Mathematical correspondence and the remaining finite minimax

The Fourier ensemble in §106 has precisely the equal-prior cyclic
symmetry required by [Assalini–Cariolaro–Pierobon, §§II–III][ACP-FG].
That framework supplies the primal POVM and dual domination problems.
The displayed matrices $M_k,Y$, their matching value $G(s)$ and the
adjoint pullback through a common decoder give the channel-specific
bound (106.8). The optimality of that finite guessing task does not
establish optimality of a recovery channel over all density inputs.

The negative-branch construction uses a full-qutrit Kraus family,
phase covariance, the Hermitian traceless qutrit identity (105.6), and
a uniform simple-eigenvalue expansion localized at the entire compact
maximizing set. These statements concern a worst-state half trace
distance without a reference. The stabilized framework in
[Watrous, Chapter 3][TQI3] and [Jenčová][JC-COMP] supplies the distinction
between that test and a test with an untouched reference. Neither that
norm distinction nor the general discrimination framework supplies the
model-specific coefficients $2/9$, $\kappa_*$, $2/87$ or $2/15$;
their derivations are (106.2), (108.9)–(109.9) and (110.5)–(110.7),
using the actual-channel and stabilized results in §§93–94.

The remaining exact finite problem is the unrestricted optimization

$$
\min_{\mathcal R\ {\rm CPTP}}
\max_{\rho\in\mathsf D(\mathbb C^3)}
\frac12\|\mathcal R\Phi_{(-1/2)^{n-1}}(\rho)-\rho\|_1
\qquad(n\ge2).
\tag{111.1}
$$

The intervals (107.7)–(107.8), the sufficiently large even-horizon
improvement (109.11), and the uniform comparison (110.3) leave its exact
finite values and minimizing decoders undetermined. The fixed-decoder
coefficient in (109.1) is not a minimax coefficient. No uniform numerical
asymptotic threshold or strict improvement at all even horizons follows
from that expansion. The exact endpoint and limiting values, the finite
bounds and the gap all retain the original input set, identity target
and terminal permissions of (105.1).

[ACP-FG]: https://arxiv.org/abs/1001.1385 "Assalini, Cariolaro and Pierobon, Sections II–III"
[JC-COMP]: https://arxiv.org/abs/1512.07016 "Jenčová, arXiv:1512.07016"

## 追加锚（本行以下为增补区）
