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

## 112. The complete uniform-modulus phase orbit

**Definition 112.1 (Orbit and simultaneous approximation).** In the
ordered basis (93.1), let

$$
|z_{\theta,\varphi}\rangle
 =\frac{|0\rangle+e^{i\theta}|1\rangle+e^{i\varphi}|2\rangle}{\sqrt3},
\qquad
P_{\theta,\varphi}=|z_{\theta,\varphi}\rangle
                         \langle z_{\theta,\varphi}|,
\qquad
\mathcal O=\{P_{\theta,\varphi}:\theta,\varphi\in\mathbb R\}.
\tag{112.1}
$$

Thus $\mathcal O$ is the whole two-phase orbit, including every relative
complex phase. For each physical $s\in[-1/2,1]$ put

$$
h_s(\mathcal R)=\max_{P\in\mathcal O}
 d(\mathcal R\Phi_s(P),P),\qquad
\nu(s)=\min_{\mathcal R\ {\rm CPTP}}h_s(\mathcal R),\qquad
q=|s|.
\tag{112.2}
$$

The decoder is one common terminal CPTP map, with exactly the permissions
in Definition 105.1. Compactness of $\mathcal O$ and of the decoder Choi
set gives attainment, by the same continuity argument as Lemma 105.2.
The full-input objective remains $e_s$ in (105.2), so
$h_s(\mathcal R)\le e_s(\mathcal R)$ and $\nu(s)\le\mu(s)$.

These objectives are simultaneous approximation problems for quantum
statistical experiments. In [Keiji Matsumoto, §5, Theorem 5][MAT-EXP],
take the source experiment to be $\rho_\alpha=\Phi_s(P_\alpha)$, the
target experiment to be $\sigma_\alpha=P_\alpha$, and the common map to
be $\mathcal R$. Its unhalved trace-norm tolerance $e_\alpha=2\epsilon$
then expresses $h_s(\mathcal R)\le\epsilon$. The same substitution in
[Anna Jenčová, §4, Theorem 4][JC-EXP] uses its tolerance $2\epsilon$.
For the full objective, instead index both experiments by all
$\rho\in\mathsf D(\mathbb C^3)$, with source $\Phi_s(\rho)$ and target
$\rho$; feasibility is exactly $e_s(\mathcal R)\le\epsilon$.
Auxiliary systems in decision tests do not enter $\mathcal R$'s input.
This correspondence uses the density-input half trace distance, not the
diamond objective (93.8) or an induced norm over arbitrary matrices.

**Lemma 112.2 (Averaging arbitrary decoders over phases).** For every
CPTP $\mathcal R$, its normalized Haar average over diagonal unitaries

$$
\overline{\mathcal R}
 =\int\operatorname{Ad}_{T^\dagger}\circ\mathcal R
                          \circ\operatorname{Ad}_T\,dT
\tag{112.3}
$$

is CPTP and diagonal covariant, and satisfies

$$
h_s(\overline{\mathcal R})\le h_s(\mathcal R),\qquad
e_s(\overline{\mathcal R})\le e_s(\mathcal R).
\tag{112.4}
$$

Every diagonal-covariant decoder has the representation

$$
\overline{\mathcal R}(E_{jj})=\sum_i c_{ij}E_{ii},\qquad
\overline{\mathcal R}(E_{ij})=\xi_{ij}E_{ij}\quad(i\ne j),
\qquad
B_{ii}=c_{ii},\quad B_{ij}=\xi_{ij}\quad(i\ne j),
\tag{112.5}
$$

where $C=(c_{ij})$ is entrywise nonnegative and column stochastic and
$B\succeq0$. In particular,

$$
|\xi_{01}|^2\le c_{00}c_{11},\qquad 0\le c_{jj}\le1.
\tag{112.6}
$$

*Proof.* Equation (95.12) gives covariance of $\Phi_s$ under every
diagonal unitary $T$. For every density input $\rho$,

$$
\overline{\mathcal R}\Phi_s(\rho)-\rho
 =\int T^\dagger\bigl[\mathcal R\Phi_s(T\rho T^\dagger)
                                      -T\rho T^\dagger\bigr]T\,dT.
\tag{112.7}
$$

Convexity and unitary invariance of the trace norm give (112.4), because
both the full density set and $\mathcal O$ are invariant under these
conjugations. Averaging preserves complete positivity and trace
preservation. Invariance of Haar measure gives covariance of the average.
This proves the inequalities for a decoder that was arbitrary before
averaging.

The diagonal matrices are the fixed subspace of diagonal conjugation,
and each off-diagonal matrix unit spans a distinct character space.
Covariance therefore gives (112.5). In the output-first convention,
its Choi matrix is

$$
J(\overline{\mathcal R})
 =\sum_{i\ne j}c_{ij}|ij\rangle\langle ij|
   +\sum_{i,j}B_{ij}|ii\rangle\langle jj|.
\tag{112.8}
$$

Its orthogonal blocks show that complete positivity is equivalent to
$c_{ij}\ge0$ and $B\succeq0$, while trace preservation is equivalent to
the column sums of $C$ being one. These are precisely the CDUC
population and coherence parameters of [Singh–Nechita, Definition 6.3,
(37), Lemmas 6.11 and 6.13, and Proposition 4.1][SN]: their population
matrix $A$ is $C$, their coherence matrix is $B$, and their covariance
is $\mathcal R(TXT^\dagger)=T\mathcal R(X)T^\dagger$.
The $01$ principal minor gives (112.6). $\square$

**Lemma 112.3 (Swap contraction at the uniform probe).** Put
$P=P_{0,0}$ and let $S$ swap $|0\rangle$ and $|1\rangle$ while fixing
$|2\rangle$. Given $\overline{\mathcal R}$ as above, define

$$
\mathcal R^\#=\frac12\left(\overline{\mathcal R}
       +\operatorname{Ad}_S\circ\overline{\mathcal R}
                                  \circ\operatorname{Ad}_S\right).
\tag{112.9}
$$

This map is CPTP and diagonal covariant. Its parameters satisfy
$c_{00}=c_{11}$, $\xi_{01}\in\mathbb R$, and equal row sums in rows zero
and one. If $u$ is that common row sum, put
$\varepsilon=\operatorname{sign}s$ for $s\ne0$ and $\varepsilon=1$ at
zero, and set $x=\varepsilon\xi_{01}$. Then

$$
u\ge c_{00}\ge|x|,\qquad |x|\le1,
\tag{112.10}
$$

and

$$
\begin{aligned}
D(u,x)&=P-\mathcal R^\#\Phi_s(P)\\
&=\frac13\begin{pmatrix}
1-u&1-qx&1\\
1-qx&1-u&1\\
1&1&2u-2
\end{pmatrix},\\
d(\mathcal R^\#\Phi_s(P),P)
&\le d(\overline{\mathcal R}\Phi_s(P),P)
 =h_s(\overline{\mathcal R})\le h_s(\mathcal R).
\end{aligned}
\tag{112.11}
$$

*Proof.* The swap normalizes the diagonal-unitary group, so both terms
of (112.9) are diagonal covariant. Swap invariance of the average gives
the stated equalities of its population parameters, and replaces the
$01$ coherence by its real part. Choi positivity now gives
$|x|\le c_{00}\le1$; the common row sum $u$ is at least $c_{00}$.

At this particular probe,

$$
SPS=P,\qquad
\Phi_s(P)=\frac13\begin{pmatrix}1&s&0\\s&1&0\\0&0&1\end{pmatrix},
\qquad S\Phi_s(P)S=\Phi_s(P).
\tag{112.12}
$$

Consequently the output of (112.9) at $\Phi_s(P)$ is the average of
$\overline{\mathcal R}\Phi_s(P)$ and its conjugate by $S$. The first
inequality in (112.11) follows from trace-norm convexity. Diagonal
covariance makes the error of $\overline{\mathcal R}$ constant on
$\mathcal O$, proving the equality there. Finally the three row sums
of $C$ are $u,u,3-2u$, and its only coherence contributing to this
output is $s\xi_{01}=qx$. Subtraction gives $D(u,x)$.
Only the two probe invariances in (112.12) are used for this swap
contraction; no swap covariance of $\Phi_s$ on other inputs is needed.
$\square$

## 113. Exact minimax on the complete phase orbit

**Theorem 113.1 (Orbit value and matching decoder).** For every physical
$s\in[-1/2,1]$, with $q=|s|$,

$$
\boxed{\displaystyle
\nu(s)=F(q)=\frac{1-q+\sqrt{(1-q)^2+8}}6.}
\tag{113.1}
$$

A matching CPTP decoder is

$$
\mathcal A_\varepsilon(X)
 =K_0XK_0^\dagger+K_1XK_1^\dagger,\qquad
K_0=E_{00}+\varepsilon E_{11},\quad K_1=E_{22},
\tag{113.2}
$$

where $\varepsilon$ is as in Lemma 112.3. It has population matrix
$C=I$, coherence $\xi_{01}=\varepsilon$, and all other off-diagonal
coherence coefficients zero.

*Proof.* Write

$$
r=\frac{\sqrt{(1-q)^2+8}-(1-q)}2,\qquad
w=(1,1,r)^{\mathsf T},\qquad D_*=D(1,1).
\tag{113.3}
$$

Because $0\le q\le1$, the positive root $r$ satisfies

$$
1\le r\le\sqrt2,\qquad r^2+(1-q)r=2,\qquad
D_*w=F(q)w.
\tag{113.4}
$$

For example the polynomial $r^2+(1-q)r-2$ is increasing on the
positive axis and has opposite weak signs at $1$ and $\sqrt2$.
For every $D(u,x)$ obtained in Lemma 112.3, its Rayleigh value differs
from the one at $D_*$ by

$$
\frac{w^\dagger[D(u,x)-D_*]w}{w^\dagger w}
 =\frac{2\bigl[(r^2-1)(u-1)+q(1-x)\bigr]}{3(2+r^2)}.
\tag{113.5}
$$

If $u\ge1$, both terms in the numerator are nonnegative. If $u\le1$,
then $x\le u$, so

$$
\begin{aligned}
(r^2-1)(u-1)+q(1-x)
&\ge\bigl[q-(r^2-1)\bigr](1-u)\\
&=(1-q)(r-1)(1-u)\ge0.
\end{aligned}
\tag{113.6}
$$

Here the last equality follows from the root identity in (113.4).
Thus $\lambda_{\max}(D(u,x))\ge F(q)$. Since $D(u,x)$ is Hermitian
and traceless, its half trace norm is at least its largest eigenvalue.
Equation (112.11) therefore yields, for every original CPTP decoder,

$$
h_s(\mathcal R)\ge\frac12\|D(u,x)\|_1\ge F(q).
\tag{113.7}
$$

For the reverse bound, the adjoint products of the two Kraus operators
in (113.2) sum to $I$. Equivalently, its only nonzero Choi block is
on $|00\rangle,|11\rangle,|22\rangle$ and is

$$
\begin{pmatrix}1&\varepsilon&0\\
                \varepsilon&1&0\\0&0&1\end{pmatrix}.
\tag{113.8}
$$

The full Choi matrix has eigenvalues $2,1$ and seven zeros, and output
partial trace $I$, so this is a full-qutrit CPTP decoder. At $P$ its
target-minus-output matrix is $D_*$. The eigenvalues of $D_*$ are

$$
F(q),\qquad \frac{q-1}{3},\qquad
\frac{1-q-\sqrt{(1-q)^2+8}}6.
\tag{113.9}
$$

Only the first is positive. Hence $\|D_*\|_1/2=F(q)$. Both
$\Phi_s$ and $\mathcal A_\varepsilon$ are diagonal covariant, so every
$P\in\mathcal O$ gives a diagonal-unitary conjugate of this difference
matrix. Thus $h_s(\mathcal A_\varepsilon)=F(q)$ on the whole orbit,
matching (113.7). $\square$

## 114. Strict full-input lower bounds and finite intervals

**Corollary 114.1 (Full-input bound and strict Fourier improvement).**
For every physical $s$, writing $q=|s|$,

$$
\boxed{\displaystyle
\mu(s)\ge\max\left\{\frac12,F(q)\right\}.}
\tag{114.1}
$$

For $L(q)=2/3-2q/9$, the exact difference is

$$
F(q)-L(q)
 =\frac{4q^2}
 {27\bigl(\sqrt{(1-q)^2+8}+3-q/3\bigr)}.
\tag{114.2}
$$

In particular $\mu(s)>L(|s|)$ at every nonzero physical parameter.
At zero, $F(0)=L(0)=\mu(0)=2/3$.

*Proof.* The orbit is a subset of the full input set, so Theorem 113.1
gives $\mu(s)\ge F(q)$. The lost orthogonal pair (106.11) gives the
other lower bound $1/2$ for every decoder. To obtain (114.2), subtract
$L(q)$ from (113.1) and rationalize
$\sqrt{(1-q)^2+8}-(3-q/3)$. The difference of the two squares is
$8q^2/9$, and the displayed denominator is positive on $[0,1]$.
Strictness follows for $q>0$. The zero value is (107.4). $\square$

**Corollary 114.2 (Actual finite intervals of positive width).** With
$q_n=2^{1-n}$,

$$
\begin{aligned}
F(q_n)\le\mu_n\le\frac23
 &&(n\ge2\text{ even}),\\
F(q_n)\le\mu_n\le\frac23-\frac{q_n}{6}
 &&(n\ge3\text{ odd}).
\end{aligned}
\tag{114.3}
$$

In particular,

$$
\boxed{\displaystyle
\mu_2\in\left[\frac{1+\sqrt{33}}{12},\frac23\right],\qquad
\mu_3\in\left[\frac{3+\sqrt{137}}{24},\frac58\right].}
\tag{114.4}
$$

The widths of these two intervals are respectively

$$
\frac{7-\sqrt{33}}{12}>0,\qquad
\frac{12-\sqrt{137}}{24}>0.
\tag{114.5}
$$

*Proof.* Apply (114.1) through the unchanged transport (105.3), and
use the replacer and positive-branch upper bounds of §107. Here
$0<q_n\le1/2$, so $F(q_n)>L(q_n)\ge5/9>1/2$.
Substitution gives (114.4). More generally the widths in (114.3) are

$$
\frac{3+q-\sqrt{(1-q)^2+8}}6
\quad\text{and}\quad
\frac{3-\sqrt{(1-q)^2+8}}6,
\qquad 0<q\le\frac12.
\tag{114.6}
$$

The first is positive because
$(3+q)^2-[(1-q)^2+8]=8q>0$; the second is positive because
$9-[(1-q)^2+8]=q(2-q)>0$. In particular $33<49$ and $137<144$
give the signs in (114.5). $\square$

**Proposition 114.3 (An orbit attainer can fail the full-input problem).**
At $s=-1/2$, the decoder $\mathcal A_{-1}$ in (113.2) has error $3/4$
on the allowed input $E_{11}$. It is therefore not a full-input minimizer
at that parameter.

*Proof.* The channel and the decoder give

$$
\Phi_{-1/2}(E_{11})=\operatorname{diag}(0,1/4,3/4),\qquad
\mathcal A_{-1}\Phi_{-1/2}(E_{11})
 =\operatorname{diag}(0,1/4,3/4).
\tag{114.7}
$$

Subtracting $E_{11}$ gives eigenvalues $0,-3/4,3/4$, hence half trace
distance $3/4$. The legal replacer has full-input error $2/3$.
Thus exact attainment of (113.1) does not solve the full-input
optimization, even though (114.1) remains a lower bound for it.
$\square$

## 115. The unrestricted zero-parameter optimizer set

**Theorem 115.1 (All zero-parameter optimizers).** Among all CPTP maps
$\mathcal R:M_3\to M_3$, without a covariance restriction,

$$
\boxed{\begin{aligned}
\mathcal Z_0
&:=\operatorname*{argmin}_{\mathcal R\ {\rm CPTP}}e_0(\mathcal R)\\
&=\left\{\mathcal R\ {\rm CPTP}:\quad
\mathcal R(I)=I,\quad
\mathcal R(E_{00})=
 \operatorname{diag}\!\left(v,\frac{1-v}{2},\frac{1-v}{2}\right),
\quad\frac13\le v\le1\right\}.
\end{aligned}}
\tag{115.1}
$$

Equivalently, $e_0(\mathcal R)=2/3$ holds exactly under the conditions
on the right. For each such map put $k=(3v-1)/2$. If $v=1/3$, then
$\mathcal R\Phi_0$ is the constant $I/3$ channel and every pure input
maximizes its error. If $v>1/3$, its pure maximizing inputs are exactly

$$
P_z=|z\rangle\langle z|,\qquad
\|z\|=1,\quad |z_0|^2=\frac13,
\tag{115.2}
$$

with arbitrary complex phases and arbitrary lower-coordinate direction.

*Proof.* The common minimum $\mu(0)=2/3$ is (107.4). Suppose first that
an arbitrary CPTP $\mathcal R$ satisfies $e_0(\mathcal R)\le2/3$.
For the three complex Fourier states $P_j$ of (106.1),
$\Phi_0(P_j)=I/3$. Put $\tau=\mathcal R(I/3)$. The effect bound gives

$$
1-\langle\psi_j|\tau|\psi_j\rangle
 \le d(P_j,\tau)\le\frac23.
\tag{115.3}
$$

The three expectations sum to $\operatorname{Tr}\tau=1$, so each equals
$1/3$. The Hermitian matrix $A_j=P_j-\tau$ has largest eigenvalue at
most $2/3$, while its Rayleigh value on $\psi_j$ is $2/3$. Equality in
the Rayleigh bound forces

$$
A_j\psi_j=\frac23\psi_j,\qquad
\tau\psi_j=\frac13\psi_j.
\tag{115.4}
$$

Because the Fourier vectors form a basis, $\tau=I/3$ and
$\mathcal R(I)=I$. This conclusion concerns the original untwirled map.

Write $\sigma=\mathcal R(E_{00})$ and $H=(3\sigma-I)/2$. For a pure
input $z$ with $t=|z_0|^2$, unitality alone gives

$$
\begin{aligned}
h(t):=\mathcal R\Phi_0(P_z)
 &=t\sigma+\frac{1-t}{2}(I-\sigma)\\
 &=\frac I3+\left(t-\frac13\right)H.
\end{aligned}
\tag{115.5}
$$

For every complex unit $u\in\operatorname{span}\{|1\rangle,|2\rangle\}$,
consider the analytic path near $t_0=1/3$

$$
z(t)=\sqrt t\,|0\rangle+\sqrt{1-t}\,u,\qquad
A(t)=P_{z(t)}-h(t).
\tag{115.6}
$$

At $t_0$, $A(t_0)=P_{z(t_0)}-I/3$ has simple largest eigenvalue $2/3$
and normalized eigenvector $z(t_0)$. The simple-eigenvalue derivative
formula of [Greenbaum–Li–Overton, Assumption 1 and Theorem 1][GLO-EIG]
applies to this analytic Hermitian path. Its largest eigenvalue is at
most the input error and hence at most $2/3$ for every nearby $t$.
It therefore has derivative zero at the interior point $t_0$. Since
normalization gives
$\langle z(t_0)|P'_{z(t_0)}|z(t_0)\rangle=0$, the formula yields

$$
0=-\langle z(t_0)|H|z(t_0)\rangle.
\tag{115.7}
$$

Let $H_L$ denote the lower $2\times2$ block. Expanding this identity
for every complex unit $u$ gives

$$
H_{00}+2\langle u|H_L|u\rangle
       +2\sqrt2\operatorname{Re}\langle0|H|u\rangle=0.
\tag{115.8}
$$

Replacing $u$ by $e^{i\alpha}u$ for every real $\alpha$ forces
$\langle0|H|u\rangle=0$. Thus both cross blocks of $H$ vanish.
The remaining identity says that $\langle u|H_L|u\rangle=-H_{00}/2$
for every complex unit $u$. It forces $H_L=-H_{00}I_2/2$: the choices
$u=|1\rangle,|2\rangle$ fix its diagonal, and
$u=(|1\rangle+|2\rangle)/\sqrt2$ and
$u=(|1\rangle+i|2\rangle)/\sqrt2$ fix both parts of its off-diagonal
entry. Hence

$$
H=\operatorname{diag}(k,-k/2,-k/2),\qquad
\sigma=\operatorname{diag}\!\left(v,\frac{1-v}{2},\frac{1-v}{2}\right),
\qquad k=\frac{3v-1}{2}.
\tag{115.9}
$$

Positivity of the state $\sigma$ initially gives $0\le v\le1$, or
$-1/2\le k\le1$. No phase covariance has been imposed on $\mathcal R$.

It remains to find the exact permitted range and prove sufficiency.
For any unital CPTP map with (115.9), set
$t=|z_0|^2$ and $\delta=t-1/3$. Equation (115.5) becomes

$$
h(t)=\operatorname{diag}\!\left(
\frac13+k\delta,\frac13-\frac{k\delta}{2},
                         \frac13-\frac{k\delta}{2}\right).
\tag{115.10}
$$

The Hermitian matrix $A=P_z-h(t)$ is traceless and has at most one
positive eigenvalue. Indeed its quadratic form on $z^\perp$ is
$-\langle y|h(t)|y\rangle\le0$, so a positive eigenspace cannot have
dimension two. Consequently

$$
d(P_z,h(t))=\lambda_{\max}(P_z-h(t)).
\tag{115.11}
$$

This pure-versus-diagonal spectral reduction is also the one in
[Chen–Grogan–Johnston–Li–Plosker, Proposition 2][CGJLP-COH]; its
unhalved trace norm is twice the distance $d$ here. The quadratic-form
argument includes the diagonal and boundary inputs as well.

Put $B=h(t)+(2/3)I$. Its diagonal entries are
$1+k\delta,1-k\delta/2,1-k\delta/2$. Since
$-1/2\le k\le1$ and $-1/3\le\delta\le2/3$, each is at least $2/3$.
Thus $B$ is positive definite, including when $h(t)$ is singular.
The exact rank-one congruence gives

$$
\begin{aligned}
\lambda_{\max}(P_z-h(t))\le\frac23
&\iff B-P_z\succeq0\\
&\iff I-|B^{-1/2}z\rangle\langle B^{-1/2}z|\succeq0\\
&\iff f_k(t):=\frac{t}{1+k\delta}
                  +\frac{1-t}{1-k\delta/2}\le1.
\end{aligned}
\tag{115.12}
$$

Putting the fractions over their common denominator yields

$$
\boxed{\displaystyle
1-f_k(t)=
\frac{k(3-k)\delta^2}
 {2(1+k\delta)(1-k\delta/2)}.}
\tag{115.13}
$$

If $k<0$, the right side is negative for every $t\ne1/3$, so the error
exceeds $2/3$ at every such pure input. Necessity therefore requires
$k\ge0$, equivalently $v\ge1/3$.

Conversely, if $0\le k\le1$, the right side of (115.13) is nonnegative
for every $t$. Equations (115.11)–(115.12) bound every complex pure input
error by $2/3$, and convexity bounds every mixed input error by $2/3$.
At $t=1/3$ the output is $I/3$, so equality is attained. This proves
(115.1).

For $k=0$, (115.5) gives $\mathcal R\Phi_0(X)=\operatorname{Tr}(X)I/3$
on every matrix, and every pure input has error $2/3$. For $k>0$,
(115.13) is strictly positive when $t\ne1/3$. Then $f_k(t)<1$, so the
congruent matrix in (115.12) is positive definite and
$\lambda_{\max}(P_z-h(t))<2/3$. When $t=1/3$, equality holds as above.
This proves the complete pure maximizing set (115.2). $\square$

## 116. Examples and the geometry of the zero optimizer set

**Proposition 116.1 (Every parameter occurs).** Every $v\in[1/3,1]$
in (115.1) is realized by a CPTP decoder. In the diagonal-covariant
class, the complete zero-parameter condition is that $C$ be doubly
stochastic with column zero
$(v,(1-v)/2,(1-v)/2)^{\mathsf T}$, $1/3\le v\le1$; the coherence
parameters are constrained only by complete positivity.

*Proof.* Let

$$
\sigma_v=\operatorname{diag}\!\left(v,\frac{1-v}{2},\frac{1-v}{2}\right),
\qquad \beta_v=\frac{I-\sigma_v}{2},\qquad
\mathcal R_v(X)=x_{00}\sigma_v+(x_{11}+x_{22})\beta_v.
\tag{116.1}
$$

Both $\sigma_v$ and $\beta_v$ are states. The output-first Choi matrix
is

$$
J(\mathcal R_v)=\sigma_v\otimes E_{00}
                  +\beta_v\otimes(E_{11}+E_{22})\succeq0,
\qquad \operatorname{Tr}_{\rm out}J(\mathcal R_v)=I.
\tag{116.2}
$$

Thus the map is CPTP, with $\mathcal R_v(I)=\sigma_v+2\beta_v=I$ and
$\mathcal R_v(E_{00})=\sigma_v$. Theorem 115.1 applies.
For a diagonal-covariant map (112.5), unitality is exactly the additional
row-sum condition on $C$, and its column zero is
$\mathcal R(E_{00})$. Since $\Phi_0$ deletes every off-diagonal input
matrix unit, no further restriction on the coherence parameters enters
the zero objective. $\square$

**Proposition 116.2 (Cancelling lower coherences are allowed).** The
conditions in (115.1) do not require $\mathcal R(E_{11})$ and
$\mathcal R(E_{22})$ to be individually diagonal.

*Proof.* Let $\mathcal R=\operatorname{Ad}_V$, where

$$
V=1\oplus\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
\tag{116.3}
$$

This unitary channel is unital and fixes $E_{00}$, so it belongs to
$\mathcal Z_0$ with $v=1$. Nevertheless

$$
\begin{aligned}
\mathcal R(E_{11})&=\tfrac12(E_{11}+E_{22}+E_{12}+E_{21}),\\
\mathcal R(E_{22})&=\tfrac12(E_{11}+E_{22}-E_{12}-E_{21}).
\end{aligned}
\tag{116.4}
$$

The coherences cancel in their sum. In general (115.1) specifies only
that sum, $\mathcal R(E_{11})+\mathcal R(E_{22})=I-\sigma_v$,
in addition to $\mathcal R(E_{00})=\sigma_v$ and the CPTP conditions.
$\square$

**Proposition 116.3 (The optimizer set is not a face of the CPTP set).**
The set $\mathcal Z_0$ in (115.1) is convex but is not a face of the
convex set of all qutrit CPTP maps.

*Proof.* Convexity follows because $e_0$ is a maximum of convex functions
of the decoder and $\mathcal Z_0$ is its minimum set. For the face
claim, consider the two CPTP replacers

$$
\mathcal T_\pm(X)=\operatorname{Tr}(X)\tau_\pm,\qquad
\tau_+=\operatorname{diag}(1/2,1/6,1/3),\qquad
\tau_-=\operatorname{diag}(1/6,1/2,1/3).
\tag{116.5}
$$

Neither is unital, so neither lies in $\mathcal Z_0$. Their average is
the $I/3$ replacer, which belongs to $\mathcal Z_0$. This contradicts
the defining implication for a face. $\square$

## 117. Necessary accumulation of finite minimizers

**Theorem 117.1 (Every zero-limit minimizer accumulation is optimal at
zero).** Let $s_j\in[-1/2,1]$ tend to zero, and for each $j$ choose any
full-input minimizer $\mathcal R_j$ of $e_{s_j}$. Every accumulation
point of these decoders, in Choi-matrix topology, belongs to
$\mathcal Z_0$.

*Proof.* The uniform estimate (105.5) holds for every CPTP decoder.
Since $e_{s_j}(\mathcal R_j)=\mu(s_j)$ and $\mu(0)=2/3$, it gives

$$
\frac23\le e_0(\mathcal R_j)
 \le\mu(s_j)+|s_j|
 \le\frac23+2|s_j|.
\tag{117.1}
$$

The compact CPTP Choi set supplies convergent subsequences. If
$\mathcal R_{j_\ell}\to\mathcal R_*$, continuity of $e_0$ in the decoder,
as in Lemma 105.2, and (117.1) imply $e_0(\mathcal R_*)=2/3$.
Theorem 115.1 gives exactly

$$
\mathcal R_*(I)=I,\qquad
\mathcal R_*(E_{00})=
 \operatorname{diag}\!\left(v,\frac{1-v}{2},\frac{1-v}{2}\right),
\qquad\frac13\le v\le1.
\tag{117.2}
$$

This proves the assertion for every accumulation point, without any
assumption of covariance or unitality of the finite minimizers.
$\square$

**Corollary 117.2 (Actual terminal decoder limits).** If $n_j\to\infty$
and $D_j$ is any minimizer in (105.1) at horizon $n_j$, every
accumulation point $D_*$ satisfies the same conditions (117.2) with
$D_*$ in place of $\mathcal R_*$.

*Proof.* The transport (105.3) gives
$\mathcal R_j=D_j\circ\operatorname{Ad}_{U_0}$, which minimizes
$e_{s_{n_j}}$, and $s_{n_j}\to0$. Composition with this fixed unitary
channel is a homeomorphism of the CPTP set, with inverse
$D=\mathcal R\circ\operatorname{Ad}_{U_0^\dagger}$. Moreover
$U_0|0\rangle=|0\rangle$, so
$\mathcal R_j(I)=D_j(I)$ and
$\mathcal R_j(E_{00})=D_j(E_{00})$, also at every limit. Apply
Theorem 117.1. The limiting channel is $\mathcal N_\infty=\Phi_0$;
the empty-horizon identity $\mathcal N_0$ remains a different channel.
$\square$

**Definition 117.3 (Remaining full finite optimization).** The exact
finite target is still (111.1), with every complex density input, the
original identity target and an unrestricted terminal CPTP decoder.
Theorem 113.1 evaluates the complete-orbit auxiliary problem, and
Theorem 115.1 characterizes the full-input optimizer set at parameter
zero. The positive-width intervals (114.4) leave the exact values
$\mu(-1/2)$ and $\mu(1/4)$ undetermined, as well as the general actual
finite values and their minimizing decoders. Theorem 117.1 is a necessary
accumulation implication; it does not establish that every element of
$\mathcal Z_0$ occurs as a limit of nonzero-parameter minimizers.
Neither an exact full finite minimax nor a minimax asymptotic equality
is asserted by the orbit value or the zero-parameter characterization.

[MAT-EXP]: https://arxiv.org/pdf/1012.2650v7 "Keiji Matsumoto, A quantum version of randomization criterion, Section 5, Theorem 5"
[JC-EXP]: https://arxiv.org/pdf/1512.07016v2 "Anna Jenčová, Comparison of quantum channels and statistical experiments, Section 4, Theorem 4"
[CGJLP-COH]: https://arxiv.org/pdf/1601.06269v2 "Jianxin Chen, Shane Grogan, Nathaniel Johnston, Chi-Kwong Li and Sarah Plosker, Quantifying the coherence of pure quantum states, Proposition 2"
[GLO-EIG]: https://arxiv.org/pdf/1903.00785v2 "Anne Greenbaum, Ren-Cang Li and Michael L. Overton, First-order Perturbation Theory for Eigenvalues and Eigenvectors, Assumption 1 and Theorem 1"

## 追加锚（本行以下为增补区）

## 118. Exact unrestricted recovery at the second horizon

**Definition 118.1 (Objective and coordinate convention).** Work on
$M_3=\mathcal B(\mathbb C^3)$ in the ordered basis of (93.1). For every
complex matrix $X=(x_{jk})$, the reduced channel is

$$
\Phi_s(X)=
\begin{pmatrix}
x_{00}&sx_{01}&0\\
sx_{10}&\frac{1+s}{2}x_{11}+\frac{1-s}{2}x_{22}&0\\
0&0&\frac{1-s}{2}x_{11}+\frac{1+s}{2}x_{22}
\end{pmatrix},\qquad -\frac12\le s\le1.
\tag{118.1}
$$

Use the original density-input objective

$$
e_s(\mathcal R)=
\max_{\rho\succeq0,\ \operatorname{Tr}\rho=1}
\frac12\|\mathcal R\Phi_s(\rho)-\rho\|_1,
\qquad
\mu(s)=\min_{\mathcal R:M_3\to M_3\ {\rm CPTP}}e_s(\mathcal R).
\tag{118.2}
$$

There is one common terminal CPTP map, fixed before the unknown input.
The maximum includes complex pure states and all mixed densities. The
target is the original input, without a target rotation. Neither the
input test nor the decoder has a reference or a history register.
The actual horizons and their decoder transport are

$$
\begin{aligned}
s_n&=(-1/2)^{n-1},\qquad
\mathcal N_n=\operatorname{Ad}_{U_0}\circ\Phi_{s_n}\quad(n\ge1),\\
\mathcal R&=D\circ\operatorname{Ad}_{U_0},\qquad
D=\mathcal R\circ\operatorname{Ad}_{U_0^\dagger},\qquad
\mu_n=\mu(s_n),\\
U_0&=1\oplus
\begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix}.
\end{aligned}
\tag{118.3}
$$

In particular $n=2$ means $s=-1/2$. The empty identity horizon
$\mathcal N_0=\operatorname{id}$ is distinct from $s=0$.

**Theorem 118.2 (Exact second-horizon minimax).** Let $L_*$ be the
$L$-coordinate of the unique real solution specified in §§119–120.
Then

$$
\boxed{\mu_2=\mu(-1/2)=L_*},
\qquad
0.606446991399069890043817252242
<L_*<
0.606446991399069890063817252242.
\tag{118.4}
$$

The five-Kraus map $\mathcal R_*$ in §121 attains this value, and
$D_*=\mathcal R_*\circ\operatorname{Ad}_{U_0^\dagger}$ attains the
original terminal problem. The upper certificate holds for every
density input. The matching lower certificate holds for every complex
CPTP decoder, without covariance, realness or sparsity assumptions.
Here $L_*$ denotes the isolated root coordinate, not a decimal
approximation. The proof is given by the root isolation in §120,
the upper inequality in §122 and the lower inequality in §125.

## 119. Eleven rational polynomials and their exact centre

**Definition 119.1 (Polynomial data).** In this appendix the symbols
$a,b,c,\eta$ are decoder parameters, independent of the channel
parameter $s$. Order the eleven real variables as

$$
\theta=(a,b,c,\eta,L,p_e,p_i,x_i,\alpha,\beta,\tau).
\tag{119.1}
$$

For independent population coordinates $p,x$ put

$$
\begin{aligned}
y&=1-p-x,& v_1&=(x+3y)/4,&v_2&=(3x+y)/4,\\
h_0&=ap,&h_1&=bv_1+cv_2,&h_2&=1-h_0-h_1,\\
d_0&=L+h_0-p,&d_1&=L+h_1-x,&d_2&=L+h_2-y,\\
\kappa&=1-\eta/2.
\end{aligned}
\tag{119.2}
$$

Define the rational-coefficient polynomial

$$
N(p,x)=d_0d_1d_2-d_0xy-d_1py-\kappa^2d_2px-2\kappa pxy.
\tag{119.3}
$$

A derivative $N_t$ means that $a,b,c,\eta,L,p,x$ are independent
before differentiation. For example
$N_{e,a}=N_a(p_e,0)$ and $N_{i,p}=N_p(p_i,x_i)$; the subscripts
$e,i$ indicate substitution only after differentiation. Set
$N_e=N(p_e,0)$ and $N_i=N(p_i,x_i)$.
The eleven polynomials, with zero-based indexing, are

$$
\begin{aligned}
F_0&=ab-\eta^2,\\
F_1&=N_e,&F_2&=N_{e,p},\\
F_3&=N_i,&F_4&=N_{i,p},&F_5&=N_{i,x},\\
F_6&=\alpha N_{e,L}+\beta N_{i,L}-1,\\
F_7&=\alpha N_{e,a}+\beta N_{i,a}+\tau b,\\
F_8&=\alpha N_{e,b}+\beta N_{i,b}+\tau a,\\
F_9&=\alpha N_{e,c}+\beta N_{i,c},\\
F_{10}&=\alpha N_{e,\eta}+\beta N_{i,\eta}-2\tau\eta.
\end{aligned}
\tag{119.4}
$$

These formulas define every coefficient of $F$ over $\mathbb Q$.
For an explicit population expansion, write

$$
N(p,x)=\sum_{i+j\le3}n_{ij}p^ix^j,\qquad
B=a-1,\quad V=(3b+c)/4,\quad D=(c-b)/2-1.
\tag{119.5}
$$

All ten coefficients, including the zero cubic coefficient, are

$$
\begin{aligned}
n_{00}&=L(L-V)(L+V),\\
n_{01}&=-L(2DV+1),\\
n_{02}&=-L(D-1)(D+1),\\
n_{03}&=0,\\
n_{10}&=-BLV-BV^2+2LV^2-L-V,\\
n_{11}&=-BDL-2BDV-B+2DLV-D-L\kappa^2+2L
          +V\kappa^2+V-2\kappa,\\
n_{12}&=-BD^2+B+D\kappa^2+D+2\kappa,\\
n_{20}&=-B^2L-B^2V+BLV+2BV^2-LV^2+L+2V,\\
n_{21}&=-B^2D+2BDV+B\kappa^2+B+D-V\kappa^2-V+2\kappa,\\
n_{30}&=V(B^2-BV-1).
\end{aligned}
\tag{119.6}
$$

**Definition 119.2 (Rational isolating box).** Every terminating decimal
in the following table is an exact rational number. They give the
centre $\bar\theta$ in the variable order (119.1).

| Coordinate | Exact rational centre |
| --- | --- |
| $a$ | $0.937622401511151627969041446134$ |
| $b$ | $0.337737953327691343771408026078$ |
| $c$ | $0.443127649705020756905449237135$ |
| $\eta$ | $0.562734991697309686859337984905$ |
| $L$ | $0.606446991399069890053817252242$ |
| $p_e$ | $0.388582338267081579168412985646$ |
| $p_i$ | $0.284461108116364144368507390598$ |
| $x_i$ | $0.388490198578206978698502224224$ |
| $\alpha$ | $0.414839545542267246309701403648$ |
| $\beta$ | $0.811692993910961133702563979045$ |
| $\tau$ | $0.067973872064879450850865285313$ |

Let

$$
r=10^{-20},\qquad
\mathcal B=\{\theta\in\mathbb R^{11}:\|\theta-\bar\theta\|_\infty\le r\}.
\tag{119.7}
$$

The parameters used below are the coordinates of the unique zero
$\theta_*$ of (119.4) in $\mathcal B$. Existence and uniqueness are
part of the following lemma.

## 120. Rational isolation and finite arithmetic bounds

**Lemma 120.1 (Unique root and positive domains).** The system
$F(\theta)=0$ has exactly one real zero in $\mathcal B$. It is in the
interior of that box and satisfies

$$
\begin{gathered}
0<a,b,c,\eta<1,\qquad L,\alpha,\beta,\tau>0,\\
0<p_e<1,\qquad p_i,x_i>0,\qquad p_i+x_i<1.
\end{gathered}
\tag{120.1}
$$

*Proof.* Here are finite rational formulas for the isolation bounds.
They also specify how to reproduce the arithmetic without any root
search. Expand $F_i=\sum_\nu f_{i\nu}\theta^\nu$ using
(119.2)–(119.6), where $\nu\in\mathbb N^{11}$ and only nonzero
coefficients are included. The rational Jacobian $J=DF(\bar\theta)$
has entries

$$
J_{ij}=\sum_{\nu:\nu_j>0}\nu_j f_{i\nu}
               \bar\theta^{\nu-e_j}.
\tag{120.2}
$$

For a fully integral evaluation of its inverse, let $q$ be the least
common multiple of the positive reduced denominators of all $J_{ij}$,
let $H=qJ$, and let

$$
\begin{aligned}
d&=\sum_{\pi\in S_{11}}\operatorname{sgn}(\pi)
                       \prod_{i=0}^{10}H_{i,\pi(i)},\\
C_{ij}&=(-1)^{i+j}\det H[\widehat i\mid\widehat j].
\end{aligned}
\tag{120.3}
$$

The determinants of the ten-by-ten minors use the same permutation
formula. Let $m$ be the least common multiple of the positive reduced
denominators of $F_i(\bar\theta)$ and set $w_i=mF_i(\bar\theta)$.
Thus $H,C,d,w$ are integers and $q,m$ are positive integers. Direct
integer substitution gives $d^2\ge1$ and

$$
\begin{aligned}
A&=J^{-1}=\frac qd C^{\mathsf T},\qquad AJ=I,\\
\|A\|_\infty
 &=\frac q{|d|}\max_i\sum_{j=0}^{10}|C_{ji}|,\\
\|AF(\bar\theta)\|_\infty
 &=\frac q{m|d|}\max_i\left|\sum_{j=0}^{10}C_{ji}w_j\right|.
\end{aligned}
\tag{120.4}
$$

In particular the integer inequalities needed below are

$$
q\max_i\sum_j|C_{ji}|<23|d|,\qquad
10^{29}q\max_i\left|\sum_j C_{ji}w_j\right|<m|d|.
\tag{120.5}
$$

More precise outward rational bounds for these same expressions are

$$
\begin{aligned}
22.572405920453996305
&<\|A\|_\infty<22.572405920453996306<23,\\
4\cdot10^{-31}
&<\|AF(\bar\theta)\|_\infty<5\cdot10^{-31}<10^{-29}.
\end{aligned}
\tag{120.6}
$$

Equations (119.2)–(120.4), including the determinant permutation sums,
are finite formulas for all entries and integers in these inequalities;
no fitted inverse or floating point tolerance occurs in (120.5).

For the second derivatives use the exact coefficient sums

$$
H_i=\sum_{|\nu|\ge2}|f_{i\nu}|\,|\nu|(|\nu|-1)2^{|\nu|-2}.
\tag{120.7}
$$

In the order $F_0,\ldots,F_{10}$ they are

$$
(H_i)_{i=0}^{10}=
(4,2992,2192,8470,4624,2150,2646,10454,10609,4785,1632).
\tag{120.8}
$$

Indeed, summing the absolute coefficient bounds for
$\partial_j\partial_k\theta^\nu$ over $j,k$ gives
$|\nu|(|\nu|-1)2^{|\nu|-2}$ on the cube $|\theta_j|\le2$.
Consequently

$$
\sup_{|\theta_j|\le2}\sum_{j,k}
|\partial_j\partial_k F_i(\theta)|\le H_i,
\qquad \max_i H_i=10609.
\tag{120.9}
$$

The entire box $\mathcal B$ is in that cube. For
$G(\theta)=\theta-AF(\theta)$, $DG(\bar\theta)=0$, and the mean-value
bound along a segment from the centre gives

$$
\sup_{\mathcal B}\|DG\|_\infty
\le23\cdot10609\cdot r=244007\cdot10^{-20}<10^{-14}.
\tag{120.10}
$$

It follows that for every $\theta\in\mathcal B$,

$$
\|G(\theta)-\bar\theta\|_\infty
<10^{-29}+244007\cdot10^{-40}
=1.00000244007\cdot10^{-29}<r.
\tag{120.11}
$$

Thus $G$ maps the closed box strictly into itself and is a contraction.
The contraction theorem supplies a unique fixed point. Since $A$ is
invertible, fixed points of $G$ are exactly zeros of $F$.

For clarity, all further interval bounds in this appendix use the
following rational interval method. Start with the eleven independent
intervals $[\bar\theta_j-r,\bar\theta_j+r]$. A rational constant is a
singleton interval. Add and subtract endpoints, multiply by taking the
minimum and maximum of the four endpoint products, and divide only by
an interval excluding zero, using its reciprocal interval. Nonnegative
integer powers can be evaluated by repeated multiplication. Evaluate
the displayed expressions in their indicated order; repeated variables
may be treated as independent interval occurrences. Every endpoint
operation is rational. The decimal endpoints displayed below are
outward enlargements, so they require no decimal rounding convention
inside a computation.

For example this method, directly on the initial coordinate intervals,
gives the strict outer bounds

$$
\begin{aligned}
&0.937<a<0.939,\quad 0.337<b<0.339,\quad 0.443<c<0.444,\\
&0.562<\eta<0.564,\quad 0.606<L<0.607,\\
&0.388<p_e<0.389,\quad 0.284<p_i<0.285,\quad 0.388<x_i<0.389,\\
&0.414<\alpha<0.415,\quad 0.811<\beta<0.812,\quad 0.067<\tau<0.069.
\end{aligned}
\tag{120.12}
$$

Hence $p_i+x_i<0.674<1$, and (120.1) follows. Strict interior inclusion
in (120.11) gives the two strict endpoints in (118.4) by taking the
$L$-coordinate of (119.7). $\square$

## 121. Legal decoder and the actual composite channel

**Lemma 121.1 (Five-Kraus decoder).** At $\theta_*$ define

$$
\begin{aligned}
K_0&=\operatorname{diag}(\sqrt a,-\sqrt b,0),\\
K_1&=\sqrt{1-a}\,|2\rangle\langle0|,&
K_2&=\sqrt{1-b}\,|2\rangle\langle1|,\\
K_3&=\sqrt c\,|1\rangle\langle2|,&
K_4&=\sqrt{1-c}\,|2\rangle\langle2|,\\
\mathcal R_*(X)&=\sum_{j=0}^4K_jXK_j^\dagger.
\end{aligned}
\tag{121.1}
$$

This is CPTP, and for arbitrary complex $X$ its action is

$$
\mathcal R_*(X)=
\begin{pmatrix}
ax_{00}&-\eta x_{01}&0\\
-\eta x_{10}&bx_{11}+cx_{22}&0\\
0&0&(1-a)x_{00}+(1-b)x_{11}+(1-c)x_{22}
\end{pmatrix}.
\tag{121.2}
$$

*Proof.* All square roots are real by (120.1), and

$$
\sum_{j=0}^4K_j^\dagger K_j
=\operatorname{diag}(a+1-a,b+1-b,c+1-c)=I.
\tag{121.3}
$$

The equation $F_0=0$ and $\eta>0$ give $\sqrt{ab}=\eta$, proving
(121.2). At the relevant parameter $\Phi=\Phi_{-1/2}$, a Kraus list is

$$
\operatorname{diag}(1,-1/2,0),\quad
\frac{\sqrt3}{2}|2\rangle\langle1|,\quad
\frac{\sqrt3}{2}|1\rangle\langle2|,\quad
\frac12|2\rangle\langle2|.
\tag{121.4}
$$

Its squared sum is $I$. In particular $\Phi$ and $\mathcal R_*$ both
preserve density matrices. Their actual composite, on all matrix units
and hence every complex $X$, is

$$
\mathcal C_*(X):=\mathcal R_*\Phi(X)=
\begin{pmatrix}
ax_{00}&\frac\eta2x_{01}&0\\
\frac\eta2x_{10}&\frac b4(x_{11}+3x_{22})+\frac c4(3x_{11}+x_{22})&0\\
0&0&(1-a)x_{00}+\frac{1-b}{4}(x_{11}+3x_{22})
                     +\frac{1-c}{4}(3x_{11}+x_{22})
\end{pmatrix}.
\tag{121.5}
$$

No change of the target is involved in this composition. $\square$

**Lemma 121.2 (Determinant polynomial).** For $p,x,y\ge0$ with
$p+x+y=1$, put $z=(\sqrt p,\sqrt x,\sqrt y)^{\mathsf T}$ and
$P_z=zz^\dagger$. Then

$$
\sigma:=\mathcal C_*(P_z)=
\begin{pmatrix}
h_0&\frac\eta2\sqrt{px}&0\\
\frac\eta2\sqrt{px}&h_1&0\\
0&0&h_2
\end{pmatrix},\qquad
B(p,x):=LI+\sigma-P_z=
\begin{pmatrix}
d_0&-\kappa\sqrt{px}&-\sqrt{py}\\
-\kappa\sqrt{px}&d_1&-\sqrt{xy}\\
-\sqrt{py}&-\sqrt{xy}&d_2
\end{pmatrix}.
\tag{121.6}
$$

In particular $\det B(p,x)=N(p,x)$.

*Proof.* Formula (121.5) gives the entries. For a symmetric three-by-three
matrix with diagonal $d_0,d_1,d_2$ and off-diagonal entries $t_{01}$,
$t_{02}$, $t_{12}$, its determinant is

$$
d_0d_1d_2-d_0t_{12}^2-d_1t_{02}^2-d_2t_{01}^2
                      +2t_{01}t_{02}t_{12}.
\tag{121.7}
$$

Substitution gives (119.3), including its negative last term.
Expansion with $y=1-p-x$ gives all coefficients (119.6). $\square$

## 122. Contact-derived cubic certificate on the whole simplex

**Lemma 122.1 (Cubic identity from five contacts).** At $\theta_*$ let

$$
\begin{aligned}
k&=(p_i-p_e)/x_i,\qquad u=p-p_e-kx,\\
A_0&=n_{20}+3p_en_{30},\quad A_1=n_{30},\quad A_2=3kn_{30}+n_{21},\\
\delta&=3k^2n_{30}+2kn_{21}+n_{12},\\
\gamma&=k^3n_{30}+k^2n_{21}+kn_{12}+n_{03},\\
Q(p,x)&=A_0+A_1(p-p_e)
       +\left(A_2-kA_1-\frac{\delta^2}{4\gamma}\right)x.
\end{aligned}
\tag{122.1}
$$

Then $x_i,\gamma>0$ and the following polynomial identity holds for all
real $p,x$:

$$
\boxed{N(p,x)=Q(p,x)u^2+
\gamma x\left(x-x_i+\frac{\delta}{2\gamma}u\right)^2.}
\tag{122.2}
$$

*Proof.* This identity is a consequence of the five contact equations
$F_1=\cdots=F_5=0$, and can be derived for a generic cubic with ten
coefficients. Substitute $p=p_e+kx+u$ and expand in $u$. Its constant
coefficient $f_0(x)$ has degree at most three, leading coefficient
$\gamma$, a zero at $x=0$, and a double zero at $x=x_i$:

$$
f_0(0)=N_e=0,\quad f_0(x_i)=N_i=0,\quad
f_0'(x_i)=kN_{i,p}+N_{i,x}=0.
\tag{122.3}
$$

Because $x_i\ne0$, $f_0(x)=\gamma x(x-x_i)^2$.
The coefficient $f_1(x)$ of $u$ has degree at most two, leading
coefficient $\delta$, and
$f_1(0)=N_{e,p}=0$, $f_1(x_i)=N_{i,p}=0$. Thus
$f_1(x)=\delta x(x-x_i)$. The remaining terms are
$(A_0+A_2x)u^2+A_1u^3$, directly from the coefficients of the generic
cubic. Therefore

$$
N=\gamma x(x-x_i)^2+\delta x(x-x_i)u
                    +(A_0+A_1u+A_2x)u^2.
\tag{122.4}
$$

Completing the square gives (122.2), since
$Q=A_0+A_1u+(A_2-\delta^2/(4\gamma))x$.
This is an exact identity modulo the five contacts; the contacts are
not approximate zeros.

For the denominator signs and the global inequality, apply the rational
interval method of §120 to (119.6) and then (122.1), on the whole box
$\mathcal B$. Coarse outward rational enclosures are

| Expression | Lower endpoint | Upper endpoint |
| --- | --- | --- |
| $k$ | $-0.268016$ | $-0.268014$ |
| $\delta$ | $-0.023055$ | $-0.023052$ |
| $\gamma$ | $0.000436$ | $0.000437$ |
| $Q(0,0)$ | $0.944714$ | $0.944715$ |
| $Q(1,0)$ | $0.590314$ | $0.590315$ |
| $Q(0,1)$ | $0.720186$ | $0.720187$ |

All entries lie strictly between the stated endpoints. In particular

$$
\frac1{2500}<\gamma<\frac1{2000},\quad
Q(0,0)>\frac9{10},\quad Q(1,0)>\frac12,\quad Q(0,1)>\frac12.
\tag{122.5}
$$

The bound $x_i>0.388$ in (120.12) justifies division by $x_i$ before
this evaluation. The positive lower bound for $\gamma$ then justifies
every division in $Q$ and (122.2). $\square$

**Proposition 122.2 (All-density upper bound and contacts).** The decoder
$\mathcal R_*$ satisfies $e_{-1/2}(\mathcal R_*)=L$.

*Proof.* Let $p,x,y\ge0$ and $p+x+y=1$. Since $Q$ is affine,

$$
Q(p,x)=yQ(0,0)+pQ(1,0)+xQ(0,1)>1/2.
\tag{122.6}
$$

The identity (122.2), $\gamma>0$ and $x\ge0$ imply $N(p,x)\ge0$ on
the entire closed simplex. In particular the edge $x=0$ gives
$N(p,0)=Q(p,0)(p-p_e)^2$. The edges $p=0$ and $y=0$, their vertices,
and zero amplitudes are included in the same identity. There is no
division by a variable population.

Write $B_0=LI+\sigma$. This matrix is positive definite because
$L>0$ and $\sigma\succeq0$. The rank-one determinant formula gives

$$
N=\det(B_0-P_z)=\det B_0\,(1-z^\dagger B_0^{-1}z).
\tag{122.7}
$$

It follows that $\|B_0^{-1/2}z\|^2\le1$. Equivalently
$I-(B_0^{-1/2}z)(B_0^{-1/2}z)^\dagger\succeq0$, so
$P_z\preceq B_0$ and $\lambda_{\max}(P_z-\sigma)\le L$.

The trace metric at a pure target requires an inertia argument. On the
two-dimensional subspace $z^\perp$, the Hermitian matrix
$H=P_z-\sigma$ has quadratic form $-\langle v,\sigma v\rangle\le0$.
Thus $H$ has at most one positive eigenvalue: a two-dimensional positive
spectral subspace would intersect $z^\perp$ nontrivially. Since
$\operatorname{Tr}H=0$, its positive eigenvalues sum to
$\frac12\|H\|_1$, and consequently

$$
\frac12\|P_z-\sigma\|_1=\lambda_{\max}(P_z-\sigma)\le L.
\tag{122.8}
$$

If $H$ has no positive eigenvalue, trace zero forces $H=0$, and the
same equality holds. Trace zero alone, without the pure-target inertia
property, would not justify (122.8).

For every diagonal unitary $U$, (121.5) directly gives
$\mathcal C_*(UXU^\dagger)=U\mathcal C_*(X)U^\dagger$.
Every complex unit vector is $Uz$ for nonnegative populations $z$;
zero components cause no exception. Unitary invariance of the trace
norm therefore proves (122.8) for every complex pure state. If
$\rho=\sum_j t_jP_j$ is a spectral decomposition, linearity and the
triangle inequality give

$$
\frac12\|\rho-\mathcal C_*(\rho)\|_1
\le\sum_j t_j\frac12\|P_j-\mathcal C_*(P_j)\|_1\le L.
\tag{122.9}
$$

Hence $e_{-1/2}(\mathcal R_*)\le L$ on all densities.

The strict signs of $Q,\gamma$ in (122.2) show that $N=0$ on the
simplex exactly when $u=0$ and $x=0$ or $x=x_i$. The two population
contacts are therefore exactly $(p_e,0)$ and $(p_i,x_i)$.
At either contact (122.7) is zero, so $B_0-P_z$ has a kernel and
$P_z-\sigma$ has eigenvalue $L>0$. Thus both contacts attain the
half trace distance $L$, and arbitrary complex phases give their
complete pure-state orbits. This proves the asserted equality for this
decoder, without classifying other minimizing decoders. $\square$

## 123. Twelve physical inputs, adjugate effects and weights

**Definition 123.1 (Contact projectors and legal effects).** Let

$$
\begin{aligned}
&(p_r,x_r,y_r)=
\begin{cases}(p_e,0,1-p_e),&r=e,\\
(p_i,x_i,1-p_i-x_i),&r=i,
\end{cases}\\
&z_r=(\sqrt{p_r},\sqrt{x_r},\sqrt{y_r})^{\mathsf T},\qquad
P_r=z_rz_r^\dagger,\qquad B_r=B(p_r,x_r).
\end{aligned}
\tag{123.1}
$$

For either contact evaluate the $d_j$ of (119.2) and put

$$
\begin{aligned}
m_{0r}&=d_{1r}d_{2r}-x_ry_r,\\
m_{1r}&=d_{0r}d_{2r}-p_ry_r,\\
m_{2r}&=d_{0r}d_{1r}-\kappa^2p_rx_r,\\
A_r:=\operatorname{adj}B_r
&=\begin{pmatrix}
m_{0r}&\sqrt{p_rx_r}(y_r+\kappa d_{2r})
       &\sqrt{p_ry_r}(d_{1r}+\kappa x_r)\\
\sqrt{p_rx_r}(y_r+\kappa d_{2r})&m_{1r}
       &\sqrt{x_ry_r}(d_{0r}+\kappa p_r)\\
\sqrt{p_ry_r}(d_{1r}+\kappa x_r)
       &\sqrt{x_ry_r}(d_{0r}+\kappa p_r)&m_{2r}
\end{pmatrix},\\
T_r&=\frac{A_r}{N_{r,L}},\qquad
\lambda_e=\alpha N_{e,L},\qquad \lambda_i=\beta N_{i,L}.
\end{aligned}
\tag{123.2}
$$

**Lemma 123.2 (Effects and probability normalization).** Each $T_r$ is
a rank-one orthogonal projector, $0\preceq T_r\preceq I$, and
$\lambda_e,\lambda_i>0$, $\lambda_e+\lambda_i=1$. Moreover

$$
\operatorname{Tr}\bigl[T_r(P_r-\mathcal C_*(P_r))\bigr]=L.
\tag{123.3}
$$

*Proof.* By §122, $B_r\succeq0$ and $\det B_r=0$.
The congruence in (122.7) identifies $B_r$ with a rank-one update
$I-vv^\dagger$ of the identity, where $\|v\|=1$. It follows that
$\operatorname{rank}B_r=2$. Thus $A_r\succeq0$ has rank one.
Differentiating $\det B$ with respect to $L$, since $\partial_LB=I$,
gives

$$
N_{r,L}=\operatorname{Tr}A_r=m_{0r}+m_{1r}+m_{2r}>0.
\tag{123.4}
$$

Consequently $T_r$ is a rank-one orthogonal projector. The entries in
(123.2) follow by the six three-by-three cofactors; equivalently
$B_rA_r=0$ and
$A_r^2=(\operatorname{Tr}A_r)A_r$ at the contact. Since
$(P_r-\mathcal C_*(P_r))T_r=LT_r$, (123.3) follows.

Rational interval evaluation of (123.2)–(123.4), on all of
$\mathcal B$, gives the following strict outward enclosures:

| Expression | Lower endpoint | Upper endpoint |
| --- | --- | --- |
| $N_{e,L}$ | $0.821001$ | $0.821002$ |
| $N_{i,L}$ | $0.812395$ | $0.812397$ |
| $\lambda_e$ | $0.340583$ | $0.340585$ |
| $\lambda_i$ | $0.659415$ | $0.659417$ |

In particular every effect denominator is greater than $4/5$.
The positivity of $\alpha,\beta$ gives positive weights, and $F_6=0$
is precisely $\lambda_e+\lambda_i=1$. $\square$

**Definition 123.3 (All physical tests).** Let $\omega=e^{2\pi i/3}$
and $U_{k\ell}=\operatorname{diag}(1,\omega^k,\omega^\ell)$ for
$k,\ell\in\{0,1,2\}$. The eighteen indexed input/effect pairs are

$$
P_{r,k\ell}=U_{k\ell}P_rU_{k\ell}^\dagger,\qquad
T_{r,k\ell}=U_{k\ell}T_rU_{k\ell}^\dagger,
\qquad w_{r,k\ell}=\lambda_r/9.
\tag{123.5}
$$

Here is the full list of twelve distinct physical pure inputs. Each
ket in the middle column defines its projector; its effect is the
corresponding conjugate in (123.5). The right column gives its total
weight after repeated indexed pairs are combined. Write
$P=p_e$, $Y_e=1-p_e$, and $p=p_i$, $x=x_i$, $y=1-p_i-x_i$
only in this table.

| Input label | Unit ket | Total weight |
| --- | --- | --- |
| $e,0$ | $(\sqrt P,0,\sqrt{Y_e})^{\mathsf T}$ | $\lambda_e/3$ |
| $e,1$ | $(\sqrt P,0,\omega\sqrt{Y_e})^{\mathsf T}$ | $\lambda_e/3$ |
| $e,2$ | $(\sqrt P,0,\omega^2\sqrt{Y_e})^{\mathsf T}$ | $\lambda_e/3$ |
| $i,00$ | $(\sqrt p,\sqrt x,\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,01$ | $(\sqrt p,\sqrt x,\omega\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,02$ | $(\sqrt p,\sqrt x,\omega^2\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,10$ | $(\sqrt p,\omega\sqrt x,\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,11$ | $(\sqrt p,\omega\sqrt x,\omega\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,12$ | $(\sqrt p,\omega\sqrt x,\omega^2\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,20$ | $(\sqrt p,\omega^2\sqrt x,\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,21$ | $(\sqrt p,\omega^2\sqrt x,\omega\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |
| $i,22$ | $(\sqrt p,\omega^2\sqrt x,\omega^2\sqrt y)^{\mathsf T}$ | $\lambda_i/9$ |

The edge ket and effect are independent of $k$: $x_e=0$ makes both
$01$ and $12$ entries of $A_e$ zero. Each edge pair is repeated for
$k=0,1,2$. The first component of each ket is positive, fixing its
global phase; positivity of the other occupied populations proves the
claimed distinctness. All effects are fixed matrices, and all tests
are unassisted qutrit inputs.

## 124. Exact phase twirl and explicit Choi matrices

**Definition 124.1 (Output-first convention).** Put $E_{jk}=|j\rangle
\langle k|$. For any complex linear map $\mathcal R:M_3\to M_3$ use

$$
J_{\mathcal R}=\sum_{j,k=0}^2\mathcal R(E_{jk})\otimes E_{jk},\qquad
\operatorname{Tr}[T\mathcal R(Q)]
=\operatorname{Tr}[(T\otimes Q^{\mathsf T})J_{\mathcal R}].
\tag{124.1}
$$

For CPTP maps $J_{\mathcal R}\succeq0$ and
$\operatorname{Tr}_{\rm out}J_{\mathcal R}=I$.
The transpose is the ordinary matrix transpose, including for complex
$Q$; it is essential to the phase cancellation below. Define

$$
W=\sum_{r=e,i}\sum_{k,\ell=0}^2
\frac{\lambda_r}{9}\,
T_{r,k\ell}\otimes\Phi(P_{r,k\ell})^{\mathsf T}.
\tag{124.2}
$$

**Lemma 124.2 (All entries of the twirled functional).** Let

$$
\begin{aligned}
v_r&=(p_r,(x_r+3y_r)/4,(3x_r+y_r)/4),\\
\zeta_e&=\alpha,\qquad\zeta_i=\beta,\\
M_{ij}&=\sum_{r=e,i}\zeta_r m_{ir}v_{jr}\quad(0\le i,j\le2),\\
g&=\sum_{r=e,i}\zeta_r p_rx_r(y_r+\kappa d_{2r}).
\end{aligned}
\tag{124.3}
$$

In the ordered tensor basis
$(00,01,02,10,11,12,20,21,22)$, all 81 entries of $W$ are specified by

$$
W=\begin{pmatrix}
M_{00}&0&0&0&-g/2&0&0&0&0\\
0&M_{01}&0&0&0&0&0&0&0\\
0&0&M_{02}&0&0&0&0&0&0\\
0&0&0&M_{10}&0&0&0&0&0\\
-g/2&0&0&0&M_{11}&0&0&0&0\\
0&0&0&0&0&M_{12}&0&0&0\\
0&0&0&0&0&0&M_{20}&0&0\\
0&0&0&0&0&0&0&M_{21}&0\\
0&0&0&0&0&0&0&0&M_{22}
\end{pmatrix}.
\tag{124.4}
$$

*Proof.* The exact nine-element character average is

$$
\frac19\sum_{k,\ell=0}^2\omega^{ku+\ell v}
=\begin{cases}1,&u=v=0\pmod3,\\0,&\text{otherwise}.\end{cases}
\tag{124.5}
$$

Set $c_0=(0,0)$, $c_1=(1,0)$, $c_2=(0,1)$ in $\mathbb Z_3^2$.
The nine matrix-unit characters $c_i-c_{i'}$ are exactly

$$
\begin{array}{c|ccc}
i\backslash i'&0&1&2\\\hline
0&(0,0)&(2,0)&(0,2)\\
1&(1,0)&(0,0)&(1,2)\\
2&(0,1)&(2,1)&(0,0)
\end{array}.
\tag{124.6}
$$

The entry $(ii',jj')$ of
$T_{r,k\ell}\otimes\Phi(P_{r,k\ell})^{\mathsf T}$ has character
$c_i-c_{i'}+c_{j'}-c_j$. By (124.6) this vanishes only if both factors
are diagonal, or if $i\ne i'$ and $(j,j')=(i,i')$.
The channel $\Phi$ has only $01$ and $10$ off-diagonal output entries.
Consequently only the $00,11$ and $11,00$ off-diagonal tensor entries
survive. Since $\lambda_rT_r=\zeta_rA_r$, their common value is

$$
\sum_r\zeta_r\sqrt{p_rx_r}(y_r+\kappa d_{2r})
                  \left(-\frac12\sqrt{p_rx_r}\right)=-g/2.
\tag{124.7}
$$

The diagonal entries are exactly $M_{ij}$ in (124.3). This proves
every entry in (124.4), including all its zero entries. $\square$

**Lemma 124.3 (Stationarity identities and positive slack).** At the
isolated root,

$$
M_{20}-M_{00}=\tau b,\quad
M_{21}-M_{11}=\tau a,\quad
M_{12}=M_{22},\quad g=2\tau\eta.
\tag{124.8}
$$

Let

$$
\begin{aligned}
Y&=\operatorname{diag}(M_{20},M_{21},M_{22}),\qquad
S=I_{\rm out}\otimes Y-W,\\
s_{10}&=M_{20}-M_{10},\quad
s_{01}=M_{21}-M_{01},\quad
s_{02}=M_{22}-M_{02}.
\end{aligned}
\tag{124.9}
$$

Then $S\succeq0$ and $SJ_*=0$, where $J_*=J_{\mathcal R_*}$.

*Proof.* Differentiating (119.3), or using its adjugate entries, gives
polynomial identities

$$
\begin{aligned}
N_a&=p(m_0-m_2),&
N_b&=v_1(m_1-m_2),\\
N_c&=v_2(m_1-m_2),&
N_\eta&=px(y+\kappa d_2).
\end{aligned}
\tag{124.10}
$$

Here $m_j$ have the same population formulas as in (123.2), before
contact substitution. Therefore, even before imposing $F=0$,

$$
\begin{aligned}
M_{20}-M_{00}-\tau b&=-F_7,\\
M_{21}-M_{11}-\tau a&=-F_8,\\
M_{12}-M_{22}&=F_9,\\
g-2\tau\eta&=F_{10}.
\end{aligned}
\tag{124.11}
$$

This proves (124.8) as exact identities at the root.
For explicit magnitudes, applying the rational interval operations of
§120 to (119.2), (123.2) and (124.3) on $\mathcal B$ yields the strict
entrywise enclosures $M^-<M<M^+$, with

$$
M^-=\begin{pmatrix}
0.109494&0.130511&0.093541\\
0.077977&0.093862&0.102283\\
0.132451&0.157595&0.102283
\end{pmatrix},\qquad
M^+=\begin{pmatrix}
0.109495&0.130512&0.093542\\
0.077978&0.093863&0.102284\\
0.132452&0.157596&0.102284
\end{pmatrix}.
\tag{124.12}
$$

The corresponding strict bounds for $g$ and the slacks are

$$
\begin{aligned}
0.076502&<g<0.076503,\\
0.054474&<s_{10}<0.054475,\\
0.027084&<s_{01}<0.027085,\\
0.008742&<s_{02}<0.008743.
\end{aligned}
\tag{124.13}
$$

In particular all three slacks exceed $1/1000$ on the entire root box.
Their signs do not rely on evaluating only the centre.

All entries of $S$ can now be written as

$$
\begin{aligned}
S={}&\tau\bigl(b|00\rangle\langle00|
 +\eta|00\rangle\langle11|+\eta|11\rangle\langle00|
 +a|11\rangle\langle11|\bigr)\\
&+s_{10}|10\rangle\langle10|
 +s_{01}|01\rangle\langle01|
 +s_{02}|02\rangle\langle02|.
\end{aligned}
\tag{124.14}
$$

The first block is $\tau\begin{pmatrix}b&\eta\\\eta&a\end{pmatrix}$.
It is positive semidefinite of rank one since $a,b,\tau>0$ and
$ab=\eta^2$; it is the outer product with vector
$\sqrt\tau(\sqrt b,\sqrt a)^{\mathsf T}$. The remaining displayed
terms are positive, and all unlisted entries vanish. This proves the
complex-Hermitian matrix inequality $S\succeq0$.

For completeness the entire Choi matrix of the decoder is

$$
J_*=\begin{pmatrix}
a&0&0&0&-\eta&0&0&0&0\\
0&0&0&0&0&0&0&0&0\\
0&0&0&0&0&0&0&0&0\\
0&0&0&0&0&0&0&0&0\\
-\eta&0&0&0&b&0&0&0&0\\
0&0&0&0&0&c&0&0&0\\
0&0&0&0&0&0&1-a&0&0\\
0&0&0&0&0&0&0&1-b&0\\
0&0&0&0&0&0&0&0&1-c
\end{pmatrix}.
\tag{124.15}
$$

Its $00,11$ block is the outer product with
$(\sqrt a,-\sqrt b)^{\mathsf T}$, and the other nonzero diagonal
entries are $1-a,1-b,c,1-c>0$. Its partial output trace is
$\operatorname{diag}(a+1-a,b+1-b,c+1-c)=I$.
The two blocks multiply to

$$
\tau\begin{pmatrix}b&\eta\\\eta&a\end{pmatrix}
\begin{pmatrix}a&-\eta\\-\eta&b\end{pmatrix}
=\tau(ab-\eta^2)I_2=0.
\tag{124.16}
$$

The other support positions of $J_*$ lie at zero entries of $S$.
Hence $SJ_*=0$ exactly. $\square$

## 125. Matching lower bound for every CPTP decoder

**Theorem 125.1 (Unrestricted lower certificate).** For every complex
CPTP map $\mathcal R:M_3\to M_3$,

$$
e_{-1/2}(\mathcal R)\ge L_*.
\tag{125.1}
$$

*Proof.* Define the constant

$$
b_{\rm test}=\sum_{r=e,i}\lambda_r\operatorname{Tr}(T_rP_r).
\tag{125.2}
$$

For a trace-zero Hermitian matrix $H$, its positive and negative parts
have equal trace, and every effect $0\preceq T\preceq I$ satisfies
$\operatorname{Tr}(TH)\le\operatorname{Tr}(H_+)=\frac12\|H\|_1$.
Apply this inequality to every legal pair (123.5). Their weights are
positive and sum to one. The error maximum is at least their weighted
average, so (124.1)–(124.2) give

$$
\begin{aligned}
e_{-1/2}(\mathcal R)
&\ge\sum_{r,k,\ell}\frac{\lambda_r}{9}
 \operatorname{Tr}\!\left[T_{r,k\ell}
 (P_{r,k\ell}-\mathcal R\Phi(P_{r,k\ell}))\right]\\
&=b_{\rm test}-\operatorname{Tr}(WJ_{\mathcal R}).
\end{aligned}
\tag{125.3}
$$

The first term is $b_{\rm test}$ by unitary invariance of trace.
Since $S\succeq0$ and $J_{\mathcal R}\succeq0$,
$\operatorname{Tr}(SJ_{\mathcal R})\ge0$; this follows, for example,
by tracing $S^{1/2}J_{\mathcal R}S^{1/2}\succeq0$.
Trace preservation and (124.9) imply

$$
\operatorname{Tr}(WJ_{\mathcal R})
\le\operatorname{Tr}[(I_{\rm out}\otimes Y)J_{\mathcal R}]
=\operatorname{Tr}Y.
\tag{125.4}
$$

Thus every complex CPTP map obeys
$e_{-1/2}(\mathcal R)\ge b_{\rm test}-\operatorname{Tr}Y$.
This argument has not averaged, restricted or changed $\mathcal R$.
The phase twirl constructed the fixed supporting functional $W$;
it imposed no symmetry on the arbitrary decoder in (125.3).

It remains to identify the lower value exactly. Covariance of
$\mathcal C_*$, (123.3), and $\lambda_e+\lambda_i=1$ give

$$
b_{\rm test}-\operatorname{Tr}(WJ_*)
=\sum_{r,k,\ell}\frac{\lambda_r}{9}L=L.
\tag{125.5}
$$

Complementarity $SJ_*=0$ and $\operatorname{Tr}_{\rm out}J_*=I$ give
$\operatorname{Tr}(WJ_*)=\operatorname{Tr}Y$. Consequently

$$
\boxed{b_{\rm test}-\operatorname{Tr}Y=L.}
\tag{125.6}
$$

An additional polynomial form of the matching identity makes its finite
algebra explicit. Define

$$
\begin{aligned}
t_r={}&p_rm_{0r}+x_rm_{1r}+y_rm_{2r}
 +2p_rx_r(y_r+\kappa d_{2r})\\
&+2p_ry_r(d_{1r}+\kappa x_r)
 +2x_ry_r(d_{0r}+\kappa p_r).
\end{aligned}
\tag{125.7}
$$

Then $t_r=\operatorname{Tr}(A_rP_r)$ and
$b_{\rm test}=\alpha t_e+\beta t_i$ at the root. In fact, before
imposing the polynomial equations, direct substitution of
(119.2)–(119.4), (123.2), (124.3) and (125.7) gives the identity

$$
\begin{aligned}
\alpha t_e+\beta t_i-\operatorname{Tr}Y-L
={}&LF_6-3\alpha F_1-3\beta F_3
 +aF_7+bF_8+cF_9+\eta F_{10}-2\tau F_0.
\end{aligned}
\tag{125.8}
$$

Every term on the right vanishes at $\theta_*$. This also proves
(125.6) by polynomial arithmetic alone. Outward rational enclosures,
provided only to locate the constants, are

$$
\begin{aligned}
0.998777&<b_{\rm test}<0.998779,\\
0.392330&<\operatorname{Tr}Y<0.392332.
\end{aligned}
\tag{125.9}
$$

The equality in (125.6) is exact, not obtained by subtracting these
intervals. Combining it with (125.3)–(125.4) proves (125.1).
Proposition 122.2 supplies the opposite inequality and its attaining
map, proving Theorem 118.2. Transport (118.3) proves the assertion for
the original terminal decoder $D_*$. $\square$

The proof separates two uses of the inputs. The twelve fixed physical
states support a lower bound for all decoders. The independent
polynomial identity (122.2) supplies the upper bound for every input
of the single decoder $\mathcal R_*$. A finite test optimum alone
would not establish (118.4).

## 126. Mathematical correspondences and scope of the exact value

The Choi supporting inequality and complementarity in §§124–125 are
of the form treated by [Coutts, Girard and Watrous, Theorem 3][CGW-N2].
For the linear functional $J\mapsto-\operatorname{Tr}(WJ)$ the domain
is the full Hermitian matrix space, and the channel Choi set has a
positive definite relative-interior point $I_9/3$; hence the
relative-interior hypothesis in that theorem presents no additional
restriction here. Equations (125.3)–(125.6) give the required weak-duality
and equality argument directly, so no uncomputed dual optimum is a
premise of the certificate.

For the statistical experiment indexed by pure qutrit states,
$\rho_\theta=\Phi(P_\theta)$ and $\sigma_\theta=P_\theta$,
[Matsumoto, Theorem 5][MAT-EXP] uses a single common CPTP reconstruction
map and the full trace norm. Its tolerance here is
$e_\theta=2L_*$. [Jenčová, §4, Theorem 4(iii)][JC-EXP] writes the
reconstruction inequality as a full-trace bound $2\epsilon$, so the
corresponding parameter is $\epsilon=L_*$. Decision-space ancillary
systems in comparison criteria do not supply a reference input or
history access to the terminal map in (118.2). These correspondences
identify the objective and its factor of two; the explicit certificates
above carry the value.

The exact assertion is confined to $s=-1/2$, equivalently the actual
horizon $n=2$, with the original identity target and unassisted
half-trace-distance density tests. The defining algebraic object is the
unique eleven-variable root in (119.7); no minimal polynomial or radical
formula is needed. The equality-set statement in §122 concerns the pure
maximizers of the displayed decoder. It gives neither a classification
of all unrestricted optimal decoders nor a minimum possible size of a
supporting certificate. Exact values for other finite horizons
$n\ge3$ are outside this appendix.

[CGW-N2]: https://arxiv.org/pdf/1810.13295v4 "Bryan Coutts, Mark Girard and John Watrous, Certifying optimality for convex quantum channel optimization problems, Theorem 3"

## 追加锚（本行以下为增补区）

## 127. A saturated decoder on the entire negative branch

Keep the ordered basis (93.1), the actual powers $F^n$ of (93.3),
and the reduced channel $\Phi_s$ of (93.5). Throughout §§127–132,
$e_s(\mathcal R)$ and $\mu(s)$ mean precisely (105.2): one terminal
CPTP map is chosen before the unknown input, and its error is maximized
over every complex qutrit density matrix. The identity target and
terminal permissions of Definition 105.1 are unchanged. The symbols
$(u,\eta)$ and $\kappa(u,\eta)$ refer to the family (108.2) and its
coefficient (108.10), independently of the root coordinates and scalar
$\kappa$ in §119. The decoder $\mathcal R_{\mathrm{fam}}$ below is
distinct from the exact horizon-two decoder $\mathcal R_*$ of §121;
the corresponding terminal maps are $D_{\mathrm{fam}}$ and $D_*$.
The unrestricted horizon-two value is exactly (118.4).

**Lemma 127.1 (A boundary CPTP decoder and its nine matrix-unit images).**
The single map

$$
\mathcal R_{\mathrm{fam}}:=\mathcal R_{1/2,1/2}=\Phi_{-1/2}
\tag{127.1}
$$

is CPTP and is independent of both the input and $q$. For every
$0\le q\le1/2$ it satisfies the complex-linear channel identity

$$
\boxed{\mathcal R_{\mathrm{fam}}\circ\Phi_{-q}=\Phi_{q/2}\quad\text{on }M_3.}
\tag{127.2}
$$

*Proof.* In (108.1), $u=\eta=1/2$ gives
$\eta^2=(1-u)/2=1/4$. The nonzero specialized Kraus operators in
(108.4) are

$$
K_0=\operatorname{diag}(1,-1/2,0),\qquad
K_1=\tfrac12 E_{22},\qquad
K_2=\tfrac{\sqrt3}{2}E_{21},\qquad
K_3=\tfrac{\sqrt3}{2}E_{12}.
\tag{127.3}
$$

Their adjoint products sum to
$E_{00}+(1/4+3/4)E_{11}+(1/4+3/4)E_{22}=I$.
The additional $E_{11}$ Kraus coefficient in (108.4) is exactly zero.
Thus complete positivity and trace preservation hold on the saturated
boundary, without any strict positivity hypothesis. Comparing (108.2)
with (93.5) gives the equality in (127.1).

Lemma 105.2 supplies CPTP input channels throughout the closed interval
$0\le q\le1/2$. In its Kraus formula the possibly vanishing squared
coefficient is
$((1-q)/2)-q^2=(1+q)(1-2q)/2\ge0$, including $q=1/2$.
Applying (108.3) at the displayed pair gives all nine images:

$$
\begin{aligned}
(\mathcal R_{\mathrm{fam}}\Phi_{-q})(E_{00})&=E_{00},\\
(\mathcal R_{\mathrm{fam}}\Phi_{-q})(E_{11})
 &=\tfrac{2+q}{4}E_{11}+\tfrac{2-q}{4}E_{22},\\
(\mathcal R_{\mathrm{fam}}\Phi_{-q})(E_{22})
 &=\tfrac{2-q}{4}E_{11}+\tfrac{2+q}{4}E_{22},\\
(\mathcal R_{\mathrm{fam}}\Phi_{-q})(E_{01})&=\tfrac q2 E_{01},\qquad
(\mathcal R_{\mathrm{fam}}\Phi_{-q})(E_{10})=\tfrac q2 E_{10},\\
(\mathcal R_{\mathrm{fam}}\Phi_{-q})(E_{ij})&=0
 \quad\bigl((i,j)\in\{(0,2),(2,0),(1,2),(2,1)\}\bigr).
\end{aligned}
\tag{127.4}
$$

For the two population columns this is multiplication of the mixing
matrices with parameters $-1/2$ and $-q$; the surviving coherence
multipliers also multiply. These are exactly the images of $\Phi_{q/2}$.
The matrix units form a complex basis of $M_3$, proving (127.2) for all
complex matrices. $\square$

## 128. The exact all-input error of the fixed decoder

**Theorem 128.1 (Finite fixed-decoder error).** With the full input set
of Definition 105.1,

$$
\boxed{\displaystyle
 e_{-q}(\mathcal R_{\mathrm{fam}})
 =\max_{\rho\in\mathsf D(\mathbb C^3)}
   \frac12\|\mathcal R_{\mathrm{fam}}\Phi_{-q}(\rho)-\rho\|_1
 =\frac23-\frac q{12}\qquad(0\le q\le1/2).}
\tag{128.1}
$$

The same input $P$ in (107.6) attains this error for every such $q$.
Consequently

$$
\mu(-q)\le\frac23-\frac q{12}<\frac23
\qquad(0<q\le1/2).
\tag{128.2}
$$

*Proof.* Put $r=q/2\in[0,1/4]$. The channel identity (127.2) and the
positive-branch identity-decoder equality (107.5) give

$$
e_{-q}(\mathcal R_{\mathrm{fam}})=e_r(\operatorname{id})
 =\frac23-\frac r6=\frac23-\frac q{12}.
\tag{128.3}
$$

The reused equality (107.5) bounds every complex density input; its
pure-input reduction and endpoint calculation are those of Lemma 105.3
and Proposition 107.2. No restriction to real states or selected probes
is introduced by this substitution. For the matching input, reuse
$v=(\sqrt{1/3},\sqrt{1/6},\sqrt{1/2})^{\mathsf T}$ and $P=vv^\dagger$
of (107.6). The same proposition and (127.2) give

$$
(\mathcal R_{\mathrm{fam}}\Phi_{-q}(P)-P)v
 =-\left(\frac23-\frac q{12}\right)v.
\tag{128.4}
$$

Together with (105.6), this attains the all-input upper bound. Finally,
$\mathcal R_{\mathrm{fam}}$ is one admissible member of the decoder minimum, which
gives (128.2) in the upper-bound direction. The decoder is fixed before
both the unknown input and the choice of $q$. $\square$

## 129. Improved even-horizon intervals with the phase-orbit lower bound

**Corollary 129.1 (A single terminal decoder at every even horizon).**
For every even integer $n\ge2$, put $q_n=2^{1-n}$. The same CPTP map

$$
D_{\mathrm{fam}}:=\mathcal R_{\mathrm{fam}}\circ\operatorname{Ad}_{U_0^\dagger}
\tag{129.1}
$$

has exact whole-input error $2/3-q_n/12$ at horizon $n$, and

$$
\boxed{\displaystyle
F(q_n)=\frac{1-q_n+\sqrt{(1-q_n)^2+8}}6
 \le\mu_n\le\frac23-\frac{q_n}{12}<\frac23
 \qquad(n\ge2\text{ even}).}
\tag{129.2}
$$

At horizon two, Theorem 118.2 identifies the value inside this enclosure:

$$
\boxed{\displaystyle
\mu_2=L_*\in\left[\frac{1+\sqrt{33}}{12},\frac58\right].}
\tag{129.3}
$$

*Proof.* The transport (105.3) and $s_n=-q_n$ give
$D_{\mathrm{fam}}F^n=\mathcal R_{\mathrm{fam}}\Phi_{-q_n}$, with $0<q_n\le1/2$.
This cancels only an output unitary; the target remains the original
input. Theorem 128.1 gives the error and upper bound. Theorem 113.1
and Corollary 114.1 give the lower bound
$\mu(-q_n)\ge\nu(-q_n)=\nu(q_n)=F(q_n)$.
Here $F(q_n)>2/3-2q_n/9\ge5/9>1/2$, so the orthogonal-pair term in
(114.1) does not strengthen it. Substituting $q_2=1/2$ proves (129.3).
The value $5/8$ is the exact error of $D_{\mathrm{fam}}$. Theorem 118.2
supplies the equality $\mu_2=L_*$, and the strict upper bound in (118.4)
is less than $5/8$. Thus this decoder is not optimal at horizon two;
(129.3) is an enclosing inequality, not a sharp minimax certificate.
$\square$

The enclosing interval in (129.2) has width

$$
W(q)=\frac{3+q/2-\sqrt{(1-q)^2+8}}6>0
 \qquad(0<q\le1/2).
\tag{129.4}
$$

Indeed $3+q/2>0$ and
$(3+q/2)^2-[(1-q)^2+8]=q(20-3q)/4>0$.
At horizon two the width is $(13-2\sqrt{33})/24>0$.
Relative to the even interval in (114.3), the upper endpoint is reduced
by $q/12$ while retaining its stronger lower endpoint. By (114.2),
$W(q)<5q/36$, the width obtained from the earlier linear Fourier lower
bound and the same upper certificate.

The map $D_{\mathrm{fam}}$ acts only on the terminal qutrit and is common to all
these horizons and all inputs. Its Kraus realization permits the usual
internal ancilla and discard of a CPTP map. It adds no history or
reference access, intermediate intervention, postselection or smaller
input code.

## 130. No-reference power monotonicity and endpoint guards

**Proposition 130.1 (Monotonicity for the full input objective).** For
every finite integer $n\ge0$,

$$
\mu_n\le\mu_{n+1}.
\tag{130.1}
$$

*Proof.* Fix any terminal CPTP decoder $D$ for horizon $n+1$. The
composition $D\circ F$ is an admissible terminal CPTP decoder for
horizon $n$, and the original powers give the identity (110.2),
$(D\circ F)F^n=DF^{n+1}$. It holds on every input with the same identity
target. Thus

$$
\mu_n\le\max_{\rho\in\mathsf D(\mathbb C^3)}
 d(DF^{n+1}(\rho),\rho).
\tag{130.2}
$$

Minimizing over $D$ proves (130.1) directly for (105.1).
For even $n\ge2$, the next horizon is odd, and (107.5) yields the
independent derivation

$$
\mu_n\le\mu_{n+1}
 \le\frac23-\frac{q_{n+1}}6
 =\frac23-\frac{q_n}{12}.
\tag{130.3}
$$

The channel $F$ here is composed inside the terminal decoder. It does
not call for an additional observed chronological letter or an
intermediate correction. $\square$

The exact endpoints and the limit remain (107.4) and (107.9):

$$
\mu_0=0,\qquad \mu_1=\frac12,\qquad
\mu_\infty=\mu(0)=\lim_{n\to\infty}\mu_n=\frac23.
\tag{130.4}
$$

Horizon zero is the empty identity channel, whereas parameter zero is
$\Phi_0$. Horizon one has $s_1=1$ and is outside the negative branch.
At $q=0$, (128.1) equals $2/3$ and strict improvement ends. No finite
$s_n$ is zero. For odd $n\ge3$, the stronger phase-orbit intervals in
(114.3)–(114.4) still apply, including
$\mu_3\in[(3+\sqrt{137})/24,5/8]$.

## 131. Exact global optimization of the displayed family coefficient

**Theorem 131.1 (Unique best coefficient within the two-parameter
family).** On the parameter domain

$$
\mathcal D=\{(u,\eta):0<u<1,\ 0<\eta\le h(u)\},\qquad
h(u)=\sqrt{(1-u)/2},
\tag{131.1}
$$

let $\kappa(u,\eta)$ be the fixed-decoder coefficient in
(108.10)–(109.1). Then

$$
\boxed{\displaystyle
\max_{(u,\eta)\in\mathcal D}\kappa(u,\eta)=\frac1{12},\qquad
\operatorname*{argmax}_{\mathcal D}\kappa
 =\{(1/2,1/2)\}.}
\tag{131.2}
$$

More precisely, put $u_0=(\sqrt{33}-1)/16$. For fixed $u$, the maximum
$g(u)=\max_{0<\eta\le h(u)}\kappa(u,\eta)$ and its complete equality
conditions are

$$
\begin{aligned}
g(u)&=\begin{cases}
2u/9,&0<u\le u_0,\\[2pt]
h(u)(4u-h(u))/(18u),&u_0<u<1,
\end{cases}\\
\operatorname*{argmax}_{0<\eta\le h(u)}\kappa(u,\eta)
 &=\begin{cases}
[2u,h(u)],&0<u<u_0,\\
\{2u_0\},&u=u_0,\\
\{h(u)\},&u_0<u<1.
\end{cases}
\end{aligned}
\tag{131.3}
$$

This is an optimization of the coefficient of the family (108.2),
with each pair fixed as $q\downarrow0$. It is not an optimization over
all CPTP maps.

*Proof.* The interval minimization in (108.9) is obtained by completing
the square. Its vertex is $x=1/3-\eta/(6u)$, which belongs to
$[0,2/3]$ exactly when $\eta\le2u$; for $\eta\ge2u$ the minimum is at
$x=0$. Thus the two branches already computed in (108.11) are

$$
\kappa(u,\eta)=\begin{cases}
\eta(4u-\eta)/(18u),&0<\eta\le2u,\\[2pt]
2u/9,&\eta\ge2u.
\end{cases}
\tag{131.4}
$$

They agree at $\eta=2u$. For fixed $u>0$, the derivative in the first
branch is $(2u-\eta)/(9u)$: the coefficient is strictly increasing up
to $2u$ and constant thereafter. Since both sides are nonnegative,

$$
h(u)\ge2u
\iff 8u^2+u-1\le0
\iff 0<u\le u_0.
\tag{131.5}
$$

The positive root is $u_0$, and $0<u_0<1/2$. These observations give
both the formula and all fixed-$u$ equality cases in (131.3).
In particular a plateau at fixed $u<u_0$ cannot be replaced by a
claim of a unique maximizing $\eta$ there.

On $(0,u_0]$, $g(u)=2u/9$ is strictly increasing. On $(u_0,1)$,
$h^2=(1-u)/2$ and $h'=-1/(4h)$ give

$$
g(u)=\frac{2h(u)}9-\frac{1-u}{36u},\qquad
g'(u)=\frac{h(u)-2u^2}{36h(u)u^2}.
\tag{131.6}
$$

All denominators here are positive. The numerator has the sign of
$h(u)^2-4u^4$, since $h(u)+2u^2>0$. Its exact factorization is

$$
h(u)^2-4u^4
 =\frac{1-u-8u^4}{2}
 =\frac{(1/2-u)(8u^3+4u^2+2u+2)}2.
\tag{131.7}
$$

The cubic factor is positive for $0<u<1$. Consequently $g$ is
strictly increasing up to $u=1/2$ and strictly decreasing thereafter;
the two formulas in (131.3) agree at $u_0$. The unique global maximizing
$u$ is therefore $1/2$. At that point $h(1/2)=1/2<2u$, so its unique
maximizing $\eta$ is $1/2$, and substitution into (131.4) gives $1/12$.

The open endpoints introduce no additional equality cases. For every
admissible pair $0<\kappa(u,\eta)\le g(u)$, and
$g(u)\to0$ both as $u\downarrow0$ and as $u\uparrow1$.
For an interior fixed $u$, $\kappa(u,\eta)\to0$ as $\eta\downarrow0$.
If the domain is closed by allowing these boundary parameters, the
original minimum (108.10), rather than a formula dividing by $u$, is
well-defined: at $u=0$ it is zero by $x=0$, and at $\eta=0$ it is zero
by $x=1/3$. At $u=1$ the constraint forces $\eta=0$.
None of these boundary values is $1/12$. $\square$

The earlier pair in (109.9) is exactly $(u_0,2u_0)$, at the junction of
the two fixed-$u$ regimes. Its coefficient
$(\sqrt{33}-1)/72$ is strictly smaller than $1/12$, since
$\sqrt{33}<7$. Its fixed-decoder expansion and existential threshold
remain valid. For the unique coefficient-maximizing pair, Theorem 128.1
strengthens the expansion to an exact error on the full closed interval
$0\le q\le1/2$. Theorem 131.1 makes no assertion that this pair minimizes
the finite error even within the family at each nonzero $q$.

## 132. The zero optimizer set and the remaining unrestricted gap

Every member $\mathcal R_{u,\eta}$ of (108.2) is unital and fixes
$E_{00}$: its lower population matrix is doubly stochastic.
Thus it belongs to the already characterized set $\mathcal Z_0$ in
(115.1), in the stratum $v=1$, $k=1$. The maximizing inputs at zero
are consequently exactly the set (115.2), as used in (108.8).
The coefficient optimization in §131 selects one decoder inside this
specified family of zero optimizers. The complete set $\mathcal Z_0$
also includes every other permitted $v\in[1/3,1]$ and the additional
CPTP degrees of freedom described in §116.

For $q>0$, Lemma 112.2 permits diagonal averaging of a full-input
minimizer without increasing its error. At zero, Proposition 116.1
gives the complete population and coherence constraints for that
covariant class. For minimizers with $q\downarrow0$, Theorem 117.1
already places every accumulation point in $\mathcal Z_0$, without
requiring covariance of the original minimizers. These results do not
force the limit to lie in (108.2), do not require finite minimizers to
be unital, and do not identify which zero optimizers arise as limits.
In particular the $v=1/3$ endpoint has every pure input as a maximizer,
whereas $v>1/3$ has precisely (115.2); the zero optimizer geometry does
not itself evaluate a uniform first-order minimax over all decoders.

**Corollary 132.1 (Certified unrestricted coefficient interval).** Set
$I(q)=2/3-\mu(-q)$ for $0<q\le1/2$. Then

$$
\frac1{12}\le\frac{I(q)}q
 \le\frac{2/3-F(q)}q
 =\frac{4}{3\bigl(3+q+\sqrt{(1-q)^2+8}\bigr)},
\tag{132.1}
$$

and therefore

$$
\boxed{\displaystyle
\frac1{12}\le\liminf_{q\downarrow0}\frac{I(q)}q
 \le\limsup_{q\downarrow0}\frac{I(q)}q\le\frac29.}
\tag{132.2}
$$

*Proof.* Theorem 128.1 bounds $\mu(-q)$ from above, giving the lower
bound for $I(q)/q$. Corollary 114.1 bounds it from below by $F(q)$,
giving the upper bound. To rationalize the latter expression, use
$(3+q)^2-[(1-q)^2+8]=8q$; division is legal because $q>0$.
Its limit at zero is $4/(3\cdot6)=2/9$, proving (132.2).
$\square$

If an expansion $\mu(-q)=2/3-cq+o(q)$ exists, (132.2) implies only
$1/12\le c\le2/9$. Neither existence of such a coefficient nor equality
$c=1/12$ follows from the exact fixed-family maximum. Establishing that
particular unrestricted coefficient would additionally require a
matching bound on the full-input error for every CPTP decoder, uniform
also for decoder choices depending on $q$. The phase-orbit bound has
the different leading coefficient $2/9$ and does not provide this
matching inequality. The necessary accumulation condition in §117
does not supply that first-order bound either.

For horizons $n\ge3$, the exact unrestricted finite values in (111.1)
and their minimizing CPTP decoders remain undetermined by these
intervals and by §§118–126. At $n=2$, Theorem 118.2 gives the exact
value and an attaining decoder; the positive width in (129.3) is a
limitation of the displayed family bound, not an unresolved value.
The single value at $q=1/2$ does not determine the unrestricted
coefficient as $q\downarrow0$.
The results here are deductions from the owning channel, Kraus family,
positive-branch error, phase-orbit obstruction and zero-optimizer
structure in §§93 and 105–117; no literature priority or new general
channel family is asserted. The stabilized reference-input problem,
the restricted-unital problem and the individual-task common-decoder
obstruction retain their distinct objectives. No realization bridge
to the original strict same-child $J/M$ H4 target, global joint
completion or ancestor claim is supplied; those questions remain
separate from these terminal-qutrit certificates.

## 追加锚（本行以下为增补区）

## 133. The unrestricted first-order coefficient

Throughout this section use the channel and objective in (118.1)--(118.2),
write $q\in[0,1/2]$ and put $\mu_q=\mu(-q)$. The decoder is one common
CPTP map chosen before the unknown complex qutrit input; no reference,
history, postselection, or code restriction is added. Ordinary ancillary
CPTP implementations remain included.

**Lemma 133.1 (Phase averaging and the finite certificate).** Let
$T=\operatorname{diag}(t_0,t_1,t_2)$ range over the diagonal unitary torus and
set

$$
\overline{\mathcal R}=\int \operatorname{Ad}_{T^\dagger}\circ
\mathcal R\circ\operatorname{Ad}_{T}\,dT.
\tag{133.1}
$$

Then $e_{-q}(\overline{\mathcal R})\le e_{-q}(\mathcal R)$. Moreover

$$
\overline{\mathcal R}(E_{jj})=\sum_i c_{ij}E_{ii},\qquad
\overline{\mathcal R}(E_{ij})=\xi_{ij}E_{ij}\ (i\ne j),
\tag{133.2}
$$

where $C=(c_{ij})$ is entrywise nonnegative and column-stochastic. The
coherence Choi block is positive semidefinite, so in particular
$|\xi_{01}|^2\le c_{00}c_{11}$.

*Proof.* The covariance
$\Phi_{-q}\operatorname{Ad}_T=\operatorname{Ad}_T\Phi_{-q}$, invariance of
the full density set, convexity of trace norm, and unitary invariance give
the stated inequality after integrating the unitary conjugates of each
error. Twirling separates the characters of the torus, giving (133.2).
Complete positivity of the diagonal Choi blocks gives $C\ge0$ and positivity
of the coherence block; trace preservation gives the column sums and its
$(0,1)$ principal minor gives the last inequality. Put

$$
a=-\operatorname{Re}\xi_{01},\quad w=C(1,1,1)^{\mathsf T},\quad
D=C_{\cdot2}-C_{\cdot1},\quad \Delta=D_1-D_2,\quad
L=2a+\min(0,\Delta).
\tag{133.3}
$$

For $-2/3\le r\le2/3$, let
$p_r=(1/3,1/3+r/2,1/3-r/2)$ and
$z_r=(\sqrt{p_{r,0}},\sqrt{p_{r,1}},\sqrt{p_{r,2}})^{\mathsf T}$. Direct
substitution in (118.1) and (133.2) gives

$$
\langle z_r|\overline{\mathcal R}\Phi_{-q}(|z_r\rangle\langle z_r|)|z_r\rangle
=\frac13+\frac{2qa}{9}
+\frac r6(w_1-w_2+2qa)+\frac{q\Delta r^2}{4}.
\tag{133.4}
$$

Since $d(P,\tau)\ge1-\operatorname{Tr}(P\tau)$ for a pure $P$, the $r=0$
probe and the average of the two endpoint probes yield, for every CPTP
$\mathcal R$ and every $0\le q\le1/2$,

$$
e_{-q}(\mathcal R)\ge e_{-q}(\overline{\mathcal R})
\ge\frac23-\frac q9L(\overline{\mathcal R}).
\tag{133.5}
$$

This is an exact finite inequality and uses no unitality assumption.
$\square$

**Lemma 133.2 (The certificate on the complete zero-optimizer set).** If
$\overline{\mathcal R}\in\mathcal Z_0$, then $L(\overline{\mathcal R})\le\sqrt2$.

*Proof.* By Theorem 115.1, unitality and the zero column give
$C_{\cdot0}=(v,(1-v)/2,(1-v)/2)^{\mathsf T}$ with $1/3\le v\le1$. Write
$y=c_{11}$ and $z=c_{21}$. Row sums and column zero give
$\Delta=2(z-y)$, while column one gives $y+z\le1$. Complete positivity gives
$a\le\sqrt{vy}$. Therefore

$$
\frac L2\le\sqrt{vy}+\min(0,z-y).
\tag{133.6}
$$

For $y\le1/2$ the right side is at most $\sqrt{v/2}$. For $y\ge1/2$ use
$z\le1-y$; the right side is at most
$\sqrt{vy}+1-2y$, whose derivative is
$\sqrt v/(2\sqrt y)-2<0$ on this interval. Thus $L/2\le\sqrt{v/2}$ and
$L\le\sqrt{2v}\le\sqrt2$, including the endpoint $v=1/3$.
$\square$

**Lemma 133.3 (Decoder-uniform lower asymptotics).** For every
$\varepsilon>0$ there is $\delta>0$ such that, simultaneously for every CPTP
$\mathcal R$ and $0<q<\delta$,

$$
e_{-q}(\mathcal R)\ge\frac23-\left(\frac{\sqrt2}{9}+\varepsilon\right)q.
\tag{133.7}
$$

*Proof.* From (118.1),
$(\Phi_s-\Phi_t)(\rho)=(s-t)\begin{psmallmatrix}0&\rho_{01}&0\\
\rho_{10}&h&0\\0&0&-h\end{psmallmatrix}$ with
$h=(\rho_{11}-\rho_{22})/2$. Positivity gives
$|\rho_{01}|+|h|\le1$, and CPTP trace-norm contraction gives the uniform
estimate $|e_s(\mathcal R)-e_t(\mathcal R)|\le|s-t|$.
If (133.7) failed, choose $q_j\downarrow0$ and decoders violating it, and
replace each by its phase average. The compact CPTP Choi set supplies a
convergent subsequence; moreover
$2/3\le e_0(\overline{\mathcal R}_j)\le
e_{-q_j}(\overline{\mathcal R}_j)+q_j$, so continuity of $e_0$ puts its
limit in $\mathcal Z_0$ by Theorem 115.1. But (133.5) and the violation imply
$L(\overline{\mathcal R}_j)>\sqrt2+9\varepsilon$. Continuity of $L$ in
Choi entries contradicts Lemma 133.2 at the limit. $\square$

**Lemma 133.4 (A moving nonunital decoder and all nine compositions).** Put
$h=1/\sqrt2$, $b_q=(1-hq)/2$, and $a_q=\sqrt{b_q}$. Define

$$
\mathcal R_q(X)=
\begin{pmatrix}
x_{00}&-a_qx_{01}&0\\
-a_qx_{10}&b_q(x_{11}+x_{22})&0\\
0&0&(1-b_q)(x_{11}+x_{22})
\end{pmatrix}.
\tag{133.8}
$$

It is CPTP for $0\le q\le1/2$, is nonunital for $q>0$, and
$\Lambda_q=\mathcal R_q\Phi_{-q}$ has the following nine matrix-unit images:

$$
\begin{array}{c|ccc}
X&E_{00}&E_{11}&E_{22}\\ \hline
\Lambda_q(X)&E_{00}&b_qE_{11}+(1-b_q)E_{22}&b_qE_{11}+(1-b_q)E_{22}
\end{array}
$$

$$
\begin{aligned}
\Lambda_q(E_{01})&=qa_qE_{01},&
\Lambda_q(E_{10})&=qa_qE_{10},\\
\Lambda_q(E_{02})&=\Lambda_q(E_{20})=
\Lambda_q(E_{12})=\Lambda_q(E_{21})=0.
\end{aligned}
\tag{133.9}
$$

Thus (133.9) holds on all complex $M_3$, and
$\mathcal R_q(I)=\operatorname{diag}(1,1-hq,1+hq)$.

*Proof.* Kraus operators

$$
E_{00}-a_qE_{11},\quad \sqrt{1-b_q}E_{21},\quad
\sqrt{b_q}E_{12},\quad \sqrt{1-b_q}E_{22}
\tag{133.10}
$$

have adjoint products summing to $I$, proving complete positivity and trace
preservation. Applying (118.1) to each matrix unit gives (133.9) directly;
(133.8) also gives the displayed nonunital value. $\square$

**Lemma 133.5 (Uniform input maximum for the moving path).** For the path in
Lemma 133.4,

$$
e_{-q}(\mathcal R_q)=\frac23-\frac{\sqrt2}{9}q+o(q).
\tag{133.11}
$$

*Proof.* For a pure $P_z=|z\rangle\langle z|$ and any output state $\tau$,
$P_z-\tau$ has at most one positive eigenvalue, since its quadratic form is
nonpositive on $z^\perp$. It follows that
$d(P_z,\tau)=\lambda_{\max}(P_z-\tau)$; convexity reduces the full density
maximum to the full complex unit sphere. Let
$F(q,z)=\lambda_{\max}(P_z-\Lambda_q(P_z))$. At $q=0$, the established
zero analysis in §107 gives $\max F(0,z)=2/3$ and the complete active set
$A=\{z:\|z\|=1,\ |z_0|^2=1/3\}$. On $A$, the matrix is $P_z-I/3$ with
simple top eigenvalue $2/3$ and gap one.

Writing $t=|z_0|^2$ and $x=|z_1|^2$, direct differentiation of (133.9) gives

$$
\langle z|\Lambda'_0(P_z)|z\rangle
=h\left(\frac{(1-t)^2}{2}+(3t-1)x\right).
\tag{133.12}
$$

Hence it equals $2h/9=\sqrt2/9$ on $A$. The simple-eigenvalue derivative
formula [GLO-EIG] applies there. The gap and compactness of $A$ give a closed
neighborhood on which the top eigenvalue stays simple and its derivative is
jointly continuous, so integration gives a uniform first-order expansion
there. Any sequence of maximizers $z_q$ has accumulation in $A$ (otherwise
its zero-order value is strictly below $2/3$), and the uniform expansion gives
$\limsup_{q\downarrow0}(\max_zF(q,z)-2/3)/q\le-\sqrt2/9$.
A fixed $z\in A$ gives the reverse liminf. This proves (133.11). $\square$

**Theorem 133.6 (Unrestricted first-order minimax coefficient).**

$$
\boxed{\displaystyle
\lim_{q\downarrow0}\frac{2/3-\mu(-q)}q=\frac{\sqrt2}{9}},
\qquad
\mu(-q)=\frac23-\frac{\sqrt2}{9}q+o(q).
\tag{133.13}
$$

*Proof.* Lemma 133.3 supplies the lower bound uniformly over all moving,
possibly nonunital decoders. Lemmas 133.4--133.5 supply one legal path with
the matching upper expansion. Taking the decoder infimum proves (133.13).
$\square$

## 134. The exact complete-$\mathcal Z_0$ restriction

**Theorem 134.1 (Finite minimax on the whole zero-optimizer set).** For every
$0\le q\le1/2$,

$$
\boxed{\displaystyle\min_{\mathcal R\in\mathcal Z_0}e_{-q}(\mathcal R)=\frac23-\frac q{12}.}
\tag{134.1}
$$

*Proof.* Phase averaging preserves $\mathcal Z_0$ and cannot increase the
error. For a phase-averaged member, use the notation of Lemma 133.2 and test
$p=(1/3,x,2/3-x)$. Direct substitution gives the fidelity

$$
\frac13+qg(x),\qquad
g(x)=2(z-y)(x-1/3)^2+\frac{2ax}{3}.
\tag{134.2}
$$

At $x=1/6$, complete positivity and column stochasticity give
$a^2\le vy\le y$ and $z-y\le1-2y$, hence

$$
g(1/6)=\frac{z-y+2a}{18}
\le\frac{1-2a^2+2a}{18}
=\frac1{12}-\frac{(a-1/2)^2}{9}\le\frac1{12}.
\tag{134.3}
$$

Therefore every member has $e_{-q}\ge2/3-q/12$. The decoder
$\mathcal R_{\rm fam}=\Phi_{-1/2}$ belongs to $\mathcal Z_0$ and Theorem
128.1 gives equality for every $q$ in the stated interval. $\square$

**Corollary 134.2 (Three distinct optimizations).** The fixed limiting map
$\mathcal R_0$ from (133.8) has coefficient zero: for this fixed
composition only the coherence derivative remains, and on its active set the
gain is $2h|z_1|^2/3$, whose minimum is zero. The best fixed
map in $\mathcal Z_0$ has coefficient $1/12$ by Theorem 134.1, whereas the
unrestricted optimized coefficient is $\sqrt2/9$ by Theorem 133.6. The
positive-q exact unrestricted value and the optimality of the moving path are
not determined here.

**Corollary 134.3 (Necessary effective accumulation data).** Let
$q_j>0$ tend to zero and let $\mathcal R_j$ be exact minimizers of
$e_{-q_j}$. Every Choi accumulation point of their phase averages
$\overline{\mathcal R}_j$ has

$$
C=\begin{pmatrix}1&0&0\\0&1/2&1/2\\0&1/2&1/2\end{pmatrix},
\qquad \xi_{01}=-\frac1{\sqrt2}.
\tag{134.4}
$$

*Proof.* Averaging preserves exact optimality, and Lemma 133.3 plus
Theorem 133.6 place every limit in $\mathcal Z_0$. From (133.5),
$L(\overline{\mathcal R}_j)\ge9(2/3-\mu(-q_j))/q_j\to\sqrt2$.
Lemma 133.2 bounds the limit by $\sqrt2$, so equality holds throughout its
proof: $v=1$, $y=z=1/2$, and $a=1/\sqrt2$. Row and column sums then give the
population matrix in (134.4). The principal CP minor and
$\operatorname{Re}\xi_{01}=-a$ force $\operatorname{Im}\xi_{01}=0$.
This is necessary effective phase-averaged data only; unused coherences and
untwirled finite minimizers are not classified. No positive-q finite value,
finite-path optimality, or H4 bridge is asserted. $\square$

## 追加锚（本行以下为增补区）
