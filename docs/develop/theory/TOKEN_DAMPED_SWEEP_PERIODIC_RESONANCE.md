# Periodic resonance of the original Token-1 mixed transfers

## 1. Original centered matrices and the mixed domain

**Definition 1.1 (Source coordinates and matrices).** Let $m\geq1$ be an integer, let $n=m+1$, and let $v=(v_1,\ldots,v_{m+1})\in(0,\infty)^{m+1}$. A centered pair vector is $z=(z_1,\ldots,z_m)^T\in\mathbb R^m$, extended by $z_0=z_{m+1}=0$; use the same zero extension for $w$. Define the real $m\times m$ matrices $A=A(m,v)$ and $B=B(m,v)$ by their rows:

$$
(Aw)_i=
\begin{cases}
w_i,&i\text{ odd},\\
(v_i+v_{i+1})w_i-2v_{i+1}w_{i-1}-2v_iw_{i+1},&i\text{ even},
\end{cases}
\qquad 1\leq i\leq m,
$$

$$
(Bz)_i=
\begin{cases}
-z_i+\dfrac{2v_{i+1}}{v_i+v_{i+1}}z_{i-1}
     +\dfrac{2v_i}{v_i+v_{i+1}}z_{i+1},&i\text{ odd},\\
-(v_i+v_{i+1})z_i,&i\text{ even}.
\end{cases}
$$

For a real parameter $0<\alpha<1$, define $B_\alpha=B_\alpha(m,v)$ by

$$
(B_\alpha z)_1=
\frac{v_2(1-2\alpha)-\alpha v_1}{v_2+\alpha v_1}z_1
+\frac{2\alpha v_1}{v_2+\alpha v_1}z_2,
\qquad
(B_\alpha z)_i=(Bz)_i\quad(2\leq i\leq m).
$$

Here $z_2=0$ when $m=1$. All denominators are positive. The equations $Aw=b$ determine the odd coordinates $w_i=b_i$ first; each even row then determines its sole remaining unknown $w_i$, since $v_i+v_{i+1}>0$. Thus $A$ is invertible. The two transfers are the literal matrices

$$
M=A^{-1}B,\qquad N_\alpha=A^{-1}B_\alpha.
$$

These rows are the centered odd/even relations and the solved Token-1 first row of Wallner, Krupke, Schmidt and Fekete, *Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots*, [arXiv:2608.27085v1, Sections IV.A and IV.B.1](https://arxiv.org/html/2608.27085v1#S4). In the [repository definitions `A`, `B`, `Balpha`, `Malpha`](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), source pair $i$ has index $i-1$ and source velocity $v_j$ has index $j-1$; in particular, `i.val % 2 = 0` denotes an odd source row, and `Malpha` is $N_\alpha$. No basis change is made.

**Definition 1.2 (Mixed trajectories and damping occurrences).** Fix $m,v,\alpha$ in Definition 1.1 for an entire trajectory. A schedule is a binary sequence $\varepsilon=(\varepsilon_t)_{t\geq0}$. Put

$$
T_t=
\begin{cases}
N_\alpha,&\varepsilon_t=1,\\
M,&\varepsilon_t=0,
\end{cases}
\qquad
u_{t+1}=T_tu_t\quad(t\geq0),
$$

An occurrence of $N_\alpha$ means $\varepsilon_t=1$. Infinitely often damping means that $\{t\geq0:\varepsilon_t=1\}$ is infinite. Damping has gap bound $L$ if $L\geq1$ is an integer and, for every $s\geq0$, at least one of $\varepsilon_s,\ldots,\varepsilon_{s+L-1}$ equals $1$. A chronological word $(S_0,\ldots,S_{p-1})$ acts as $S_{p-1}\cdots S_0$ on column vectors. Its periodic repetition uses $T_t=S_{t\bmod p}$.

The schedule is an unconstrained choice of these two linear transfers. The source's collision process imposes further conditions on collision order and token pickup and carriage; these conditions are not hypotheses of this mixed linear model. The distinction is the one in [v1, Section IV.B.1](https://arxiv.org/html/2608.27085v1#S4.SS2.SSS1), where $M_\alpha$ is used when the first robot carries the token and $M$ otherwise.

## 2. A common periodic family for every interior damping parameter

**Theorem 2.1 (An original-matrix three-phase family).** There exist one dimension $m\geq1$, one strictly positive velocity vector $v$, one nonzero real vector $u_0$, one binary periodic schedule containing both transfer types, and positive integers $p,L$, all independent of $\alpha$, such that for every fixed $\alpha\in(0,1)$ the recurrence of Definition 1.2 satisfies

$$
u_{t+p}=u_t\neq0\qquad(t\geq0),
$$

has the same complete phase sequence for every such $\alpha$, and has an occurrence of $N_\alpha$ in every block of $L$ transfers. Explicitly, one can take

$$
m=2,\qquad v=(1,1,1),\qquad
u_0=\begin{pmatrix}1\\2\end{pmatrix},\qquad
p=L=3,\qquad
\varepsilon_t=
\begin{cases}
1,&t\equiv0\pmod3,\\
0,&t\equiv1,2\pmod3,
\end{cases}
$$

The chronological word is $(N_\alpha,M,M)$, and all its phases are

$$
u_{3k}=\begin{pmatrix}1\\2\end{pmatrix},\qquad
u_{3k+1}=\begin{pmatrix}1\\-1\end{pmatrix},\qquad
u_{3k+2}=\begin{pmatrix}-2\\-1\end{pmatrix}
\qquad(k\geq0),
$$

In particular $\|u_t\|_2^2\in\{2,5\}$ for every $t\geq0$.

*Proof.* Substitute $m=2$ and $v_1=v_2=v_3=1$ into the original rows of Definition 1.1, with both centered endpoints still zero. This gives exactly

$$
A=\begin{pmatrix}1&0\\-2&2\end{pmatrix},\qquad
B=\begin{pmatrix}-1&1\\0&-2\end{pmatrix},\qquad
B_\alpha=
\begin{pmatrix}
\dfrac{1-3\alpha}{1+\alpha}&\dfrac{2\alpha}{1+\alpha}\\
0&-2
\end{pmatrix}.
$$

Multiplication in both orders verifies

$$
A^{-1}=\begin{pmatrix}1&0\\1&\tfrac12\end{pmatrix}.
$$

Consequently the actual source transfers, without any conjugation or substitution of another pair of matrices, are

$$
M=\begin{pmatrix}-1&1\\-1&0\end{pmatrix},\qquad
N_\alpha=\frac1{1+\alpha}
\begin{pmatrix}
1-3\alpha&2\alpha\\
1-3\alpha&\alpha-1
\end{pmatrix}.
$$

For every $(x,y)^T\in\mathbb R^2$ their difference is

$$
(N_\alpha-M)\begin{pmatrix}x\\y\end{pmatrix}
=\frac{1-\alpha}{1+\alpha}(2x-y)\begin{pmatrix}1\\1\end{pmatrix}.
$$

Thus they agree on the line $y=2x$. This is the specialization of the source first-event equality mechanism: the first undamped reflection is $E_1(x,y)^T=(-x+y,y)^T$, so that $E_1z=z$ precisely on that line. The existing identities `dampedEvent_eq_of_fixed`, `sweepTheta_of_fixed` and `source_factorization` in [TokenDampedSweepContraction](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean) identify the same agreement for the original matrices; the displayed difference also proves it directly here. The damping parameter remains fixed, and the chosen line does not depend on it.

Write

$$
a=\begin{pmatrix}1\\2\end{pmatrix},\qquad
b=\begin{pmatrix}1\\-1\end{pmatrix},\qquad
c=\begin{pmatrix}-2\\-1\end{pmatrix}.
$$

Every transition in the proposed word is verified by the following exact products:

$$
\begin{aligned}
N_\alpha a
&=\frac1{1+\alpha}
  \begin{pmatrix}(1-3\alpha)+4\alpha\\(1-3\alpha)+2(\alpha-1)\end{pmatrix}
 =\frac1{1+\alpha}\begin{pmatrix}1+\alpha\\-1-\alpha\end{pmatrix}=b,\\
Mb&=\begin{pmatrix}-1-1\\-1\end{pmatrix}=c,\\
Mc&=\begin{pmatrix}2-1\\2\end{pmatrix}=a.
\end{aligned}
$$

These equalities hold for every $0<\alpha<1$ since $1+\alpha>0$. They establish the chronological order $a\xrightarrow{N_\alpha}b\xrightarrow{M}c\xrightarrow{M}a$ and the period product $M^2N_\alpha a=a$. Starting at $u_0=a$, induction on $k$ now proves all three displayed phase identities: the first product gives time $3k+1$, the second gives time $3k+2$, and the third gives time $3(k+1)$. The induction uses the same $\alpha$, velocities, matrices and initial vector at every step. It also proves that the entire sequence is common to all $\alpha\in(0,1)$.

The three vectors are nonzero and have squared Euclidean norms $5,2,5$, respectively. Hence $u_{t+3}=u_t\neq0$ at every time, including both intermediate phases, and $\|u_t\|_2\geq\sqrt2$. The indices of $N_\alpha$ are exactly $0,3,6,\ldots$. Three consecutive integers have the three distinct residues modulo $3$, so every block of three transfers contains exactly one damped occurrence. Thus $p=L=3$ meets all assertions. $\square$

**Corollary 2.2 (Failure of frequency-only decay criteria).** For each fixed $\alpha\in(0,1)$, both of the following universal assertions about the mixed model of Definition 1.2 are false:

1. For every finite $m\geq1$, every $v\in(0,\infty)^{m+1}$, every schedule with infinitely many occurrences of $N_\alpha$, and every $u_0\in\mathbb R^m$, one has $u_t\to0$.
2. For every finite $m\geq1$, every $v\in(0,\infty)^{m+1}$, every schedule admitting a positive finite gap bound, and every $u_0\in\mathbb R^m$, one has $u_t\to0$.

One common choice of $m,v,u_0$ and binary schedule disproves both assertions for the whole open interval of fixed damping parameters.

*Proof.* Use Theorem 2.1. Its schedule has infinitely many damped occurrences and gap bound $3$, while $\|u_t\|_2\geq\sqrt2$ at every time. Convergence to zero would imply that these norms tend to zero, a contradiction. The counterexample therefore violates each asserted universal conclusion for each fixed $\alpha\in(0,1)$ with exactly the same parameters, schedule and initial vector.

These are assertions about the repository's mixed extension. The fixed-map result [`TokenDampedSweepContraction.result`](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean) instead gives, for every finite $m\geq1$, every strictly positive $v$, and every fixed $0<\alpha<1$, the strict complex spectral bound $\rho(N_\alpha)<1$ and $N_\alpha^ku\to0$ for every real $u$. Its power-decay implication uses [`FinitePathDynamics.real_mulVec_powers_tendsto_zero`](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean). That is precisely the repeated single-map domain of [v1, Conjecture 1, Section IV.B.1](https://arxiv.org/html/2608.27085v1#S4.SS2.SSS1). Here the period product is $M^2N_\alpha$, with $(M^2N_\alpha)^ku_0=u_0$ at the period boundaries. The fixed-map theorem and its rotational-regime scope therefore remain intact.

The counterexample concerns real centered vectors with zero centered endpoints and a prescribed abstract mixed schedule. It asserts no physical collision trajectory, no collision-order or token-carrying feasibility, and no entry of the full collision process into the rotational regime. The domains are those of Definition 1.2 and [v1, Sections III and IV.A](https://arxiv.org/html/2608.27085v1#S4.SS1); a physical realization would require additional hypotheses connecting that process to this particular schedule. The existence and the two failures proved here make no assertion about all other words or parameters, nonperiodic schedules, a uniform decay rate, or the excluded parameter endpoints $\alpha=0,1$. $\square$

## 追加锚（本行以下为增补区）

## 3. Complete periodic classification for two pair coordinates

**Definition 3.1 (Positive triples, angle and complete periods).** Specialize Definitions 1.1 and 1.2 to $m=2$ and write

$$
a=v_1>0,\qquad b=v_2>0,\qquad c=v_3>0,\qquad
u=(x,y)^T\in\mathbb R^2.
$$

The coordinates are the original centered coordinates, with both exterior coordinates zero. For each fixed $\alpha\in(0,1)$ the source matrices are exactly

$$
A=\begin{pmatrix}1&0\\-2c&b+c\end{pmatrix},\qquad
B=\begin{pmatrix}-1&\dfrac{2a}{a+b}\\0&-(b+c)\end{pmatrix},\qquad
B_\alpha=\begin{pmatrix}
\dfrac{b(1-2\alpha)-\alpha a}{b+\alpha a}&\dfrac{2\alpha a}{b+\alpha a}\\
0&-(b+c)
\end{pmatrix},
\qquad M=A^{-1}B,\quad N_\alpha=A^{-1}B_\alpha.
$$

Define the dimensionless coefficients and angle

$$
\xi=\frac{a}{a+b},\qquad \eta=\frac{c}{b+c},\qquad
\tau_\alpha=\frac{\alpha(a+b)}{b+\alpha a},\qquad
C=2\xi\eta-1,\qquad
\theta=\arccos C
=\arccos\left(\frac{2ac}{(a+b)(b+c)}-1\right).
$$

Since $0<\xi,\eta<1$, one has $-1<C<1$ and $0<\theta<\pi$. Also $0<\tau_\alpha<1$: the denominator is positive, and its difference from the numerator is $b(1-\alpha)>0$. The symbol $\theta$ denotes the undamped angle; $\tau_\alpha$ denotes the first-event damping weight. Put

$$
Q(x,y)=\frac{x^2}{a}+\frac{(y-x)^2}{b}+\frac{y^2}{c},\qquad
H=\{(x,y)^T:x=\xi y\},\qquad
h=\begin{pmatrix}a\\a+b\end{pmatrix}.
$$

A complete periodic orbit means that there is an integer $q\geq1$ for which $u_{t+q}=u_t\ne0$ for every $t\geq0$. The binary schedule itself has a period $p\geq1$ when $\varepsilon_{t+p}=\varepsilon_t$ for every $t\geq0$; $p$ and $q$ need not coincide.

These matrices specialize the odd/even equations and Token-1 equation of [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, Sections IV.A and IV.B.1](https://arxiv.org/html/2608.27085v1#S4). In the definitions `A`, `B`, `Balpha`, `Malpha` of [TokenDampedSweepContraction](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), the velocity indices $0,1,2$ mean $a,b,c$, the pair indices $0,1$ mean $x,y$, and `Malpha` means $N_\alpha$. The local weight named `theta` there is $\tau_\alpha$ here. The corresponding [Scribe definitions](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs) use the same index correspondence.

**Theorem 3.2 (Periodic resonance for every original positive triple).** For every $a,b,c>0$ and every fixed $\alpha\in(0,1)$, there exists a finite periodic binary schedule containing both $M$ and $N_\alpha$ and admitting a nonzero complete periodic orbit if and only if

$$
\frac{\theta}{2\pi}\in\mathbb Q.
$$

More precisely, if $\theta/(2\pi)=k/r$ in lowest terms, where $k,r$ are positive integers, $\gcd(k,r)=1$ and $0<2k<r$, put

$$
d=\frac{r}{\gcd(r,2)},\qquad
\varepsilon_t=\begin{cases}1,&d\mid t,\\0,&d\nmid t.\end{cases}
$$

This one schedule and the one original-coordinate initial vector $u_0=h$ work simultaneously for every fixed $\alpha\in(0,1)$. Their entire phase sequence is

$$
u_t=M^t h\qquad(t\geq0),
$$

independent of $\alpha$. The least schedule period is $d\geq2$, and the least full vector period is $r$. Writing $\ell=d\theta/\pi\in\mathbb Z$, every phase is also given by

$$
u_{nd+j}=(-1)^{n\ell}M^j h,
\qquad n\geq0,\quad 0\leq j<d.
$$

In particular the full vector period is $d$ when $r$ is odd and $2d$ when $r$ is even.

*Proof.* First compute the literal transfers. The inverse of $A$ is

$$
A^{-1}=\begin{pmatrix}1&0\\2\eta&\dfrac1{b+c}\end{pmatrix}.
$$

Thus, with the auxiliary matrices acting on the same coordinates,

$$
R=\begin{pmatrix}-1&2\xi\\0&1\end{pmatrix},\qquad
S=\begin{pmatrix}1&0\\2\eta&-1\end{pmatrix},\qquad
D_\alpha=(1-\tau_\alpha)I+\tau_\alpha R,
$$

one obtains

$$
\begin{aligned}
M&=SR=\begin{pmatrix}-1&2\xi\\-2\eta&4\xi\eta-1\end{pmatrix},\\
N_\alpha&=SD_\alpha
=\begin{pmatrix}
1-2\tau_\alpha&2\tau_\alpha\xi\\
2\eta(1-2\tau_\alpha)&4\tau_\alpha\xi\eta-1
\end{pmatrix}.
\end{aligned}
\tag{3.1}
$$

Indeed $1-2\tau_\alpha=[b(1-2\alpha)-\alpha a]/(b+\alpha a)$ and $2\tau_\alpha\xi=2\alpha a/(b+\alpha a)$, so the first row is exactly the Token-1 row. The second row follows from $-2c x'+(b+c)y'=-(b+c)y$. No change of coordinates is involved.

Use the weighted Dirichlet form and first-event loss of `local_energy_decomposition`, `Q_dampedEvent_loss`, `Q_event`, `Q_sweepTheta_eq_iff` and `source_factorization` in [TokenDampedSweepContraction](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean). Their two-coordinate specialization can be written completely as

$$
\begin{aligned}
Q(x,y)
&=\frac{a+b}{ab}(x-\xi y)^2+
  \left(\frac1{a+b}+\frac1c\right)y^2\\
&=\left(\frac1a+\frac1{b+c}\right)x^2+
  \frac{b+c}{bc}(y-\eta x)^2.
\end{aligned}
\tag{3.2}
$$

These identities follow by expanding the squares; their mixed term is $-2xy/b$ and their diagonal coefficients are $1/a+1/b$ and $1/b+1/c$. The map $R$ negates $x-\xi y$ while fixing $y$; $S$ negates $y-\eta x$ while fixing $x$. Hence each preserves $Q$. The map $D_\alpha$ fixes $y$ and multiplies $x-\xi y$ by $1-2\tau_\alpha$. Applying (3.2) and then the $Q$-isometry $S$ therefore gives

$$
Q(Mu)=Q(u),\qquad
Q(N_\alpha u)=Q(u)-\gamma_\alpha(x-\xi y)^2,
\qquad
\gamma_\alpha=4\tau_\alpha(1-\tau_\alpha)\frac{a+b}{ab}>0.
\tag{3.3}
$$

The form is positive definite, since its defining sum can vanish only if $x=y=0$. Thus every scheduled step is nonexpansive for $Q$, and equality at a damped step holds exactly when its input belongs to $H$. On $H$, both $R$ and $D_\alpha$ fix the input, whence

$$
N_\alpha u=Mu=Su\qquad(u\in H).
\tag{3.4}
$$

This is also the specialization of `dampedEvent_eq_of_fixed` and `sweepTheta_of_fixed` in the same supplier. The Dirichlet form and its rigidity and power-decay uses are described in [FinitePathDynamics](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean) and its [Scribe](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs); only the form and equality mechanism are needed for the mixed products here.

We next compute the powers of this particular $M$. Formula (3.1) gives $\det M=1$ and $\operatorname{tr}M=4\xi\eta-2=2C$. Multiplying the displayed two-by-two matrix gives

$$
M^2-2CM+I=0.
$$

Let $s=\sin\theta>0$ and $J=(M-CI)/s$. The last identity and $1-C^2=s^2$ give $J^2=-I$ and $M=\cos\theta\,I+\sin\theta\,J$. Induction on $t$, multiplying this last expression and using the sine and cosine addition formulas, yields

$$
M^t=\cos(t\theta)I+\sin(t\theta)J\qquad(t\geq0).
\tag{3.5}
$$

The trigonometric identities used in this induction are the classical addition formulas, [NIST DLMF, §4.21(i)](https://dlmf.nist.gov/4.21#i). For any nonzero real $w$, the vectors $w,Jw$ are linearly independent: a dependence would have $Jw=\lambda w$ for some real $\lambda$, and applying $J$ again would give $-w=\lambda^2w$, impossible over $\mathbb R$. Consequently, for every integer $t\geq1$,

$$
\begin{aligned}
M^t w\in\mathbb Rw
&\quad\Longleftrightarrow\quad t\theta\in\pi\mathbb Z,\\
M^t w=w
&\quad\Longleftrightarrow\quad t\theta\in2\pi\mathbb Z.
\end{aligned}
\tag{3.6}
$$

Indeed the coefficient of $Jw$ in (3.5) must vanish in either assertion, and the second additionally requires $\cos(t\theta)=1$. The converse implications follow from the same formula. Notice also that $H=\mathbb Rh$, since $a+b>0$ and $x=ay/(a+b)$.

Suppose a periodic schedule containing both transfer types has a nonzero complete periodic orbit of vector period $q$. For each $t$, (3.3) and periodicity give

$$
Q(u_t)\geq Q(u_{t+1})\geq\cdots\geq Q(u_{t+q})=Q(u_t).
$$

Every inequality is equality. At every damped occurrence the input is therefore in $H$, and (3.4) makes that step equal to $M$ on its actual input. The undamped steps already equal $M$. Induction gives $u_t=M^t u_0$ for all $t\geq0$. In particular $M^q u_0=u_0$, where $u_0\ne0$. By (3.6), $q\theta\in2\pi\mathbb Z$, proving $\theta/(2\pi)\in\mathbb Q$. This argument uses complete vector periodicity and does not identify its period with the schedule period.

Conversely assume $\theta/(2\pi)=k/r$ as in the statement. For an integer $t\geq1$, the two conditions in (3.6) become respectively

$$
r\mid 2t,\qquad r\mid t,
$$

because $k$ is coprime to $r$. The least positive integer satisfying the first is $d=r/\gcd(r,2)$, and the least satisfying the second is $r$. In particular $d\theta=\ell\pi$ for an integer $\ell$, and (3.5) gives

$$
M^d=(-1)^\ell I,\qquad M^r=I.
\tag{3.7}
$$

The inequality $0<\theta<\pi$ excludes $d=1$. Thus the schedule in the statement repeats the chronological word consisting of $N_\alpha$ followed by $d-1$ copies of $M$, and contains both maps. Start from $h\ne0$. At times $t=nd$, the proposed state $M^{nd}h=(-1)^{n\ell}h$ lies in $H$. Formula (3.4) makes the scheduled $N_\alpha$ step at that time equal to $M$ on this state for every $\alpha\in(0,1)$. At every other time the scheduled step is $M$ itself. Induction on time proves $u_t=M^t h$ at every phase, simultaneously for each fixed interior $\alpha$. Splitting $t=nd+j$ and using (3.7) proves the asserted full phase formula.

Every phase is nonzero: $M$ is invertible, or equivalently $Q(M^t h)=Q(h)>0$. By (3.6) the least full vector period is $r$. Any period of the binary schedule must take its occurrence at time zero to another occurrence, hence must be divisible by $d$; $d$ itself is a period. If $r$ is odd, then $d=r$ and $\ell=2k$ is even. If $r$ is even, then $d=r/2$ and coprimality forces $k=\ell$ to be odd; the state changes sign after one schedule period and returns after two. This proves all the assertions. $\square$

## 4. The exact boundary for all schedules with a finite gap bound

**Definition 4.1 (First return of a real line).** For the arbitrary positive triple and angle of Definition 3.1 put

$$
\delta=\min\{d\in\mathbb Z_{\geq1}:d\theta\in\pi\mathbb Z\}
$$

when this set is nonempty, and put $\delta=\infty$ otherwise. Every finite integer is less than $\infty$. Damping gap bound $L$ retains Definition 1.2: every length-$L$ window of the entire one-sided binary schedule contains an occurrence of $N_\alpha$.

**Theorem 4.2 (Universal finite-gap convergence, including singular damping).** For every $a,b,c>0$, every fixed $\alpha\in(0,1)$ and every integer $L\geq1$, the following equivalence holds:

$$
\left[
\begin{gathered}
\text{For every binary schedule with damping gap bound }L\\
\text{and every }u_0\in\mathbb R^2,\quad u_t\longrightarrow0
\end{gathered}
\right]
\quad\Longleftrightarrow\quad L<\delta.
$$

If $\theta/(2\pi)=k/r$ in lowest terms, then $\delta=r/\gcd(r,2)$. If $\theta/(2\pi)$ is irrational, then $\delta=\infty$, so the universal assertion holds for each finite $L$. When $\delta$ is finite, failure already occurs at $L=\delta$, with a complete nonzero periodic orbit and a schedule and phase sequence common to every fixed $\alpha\in(0,1)$. The equivalence includes the interior parameter $\alpha=b/(a+2b)$ at which $N_\alpha$ is singular.

*Proof.* Fix an arbitrary positive triple, an arbitrary fixed $\alpha\in(0,1)$, and an integer $L\geq1$. If there is a positive $d$ with $d\theta\in\pi\mathbb Z$, then $\theta/(2\pi)$ is rational. Conversely the divisibility calculation in the proof of Theorem 3.2 shows, when $\theta/(2\pi)=k/r$ in lowest terms, that the least such $d$ is $r/\gcd(r,2)$. This proves the asserted formula for $\delta$, including its infinite case. Since $0<\theta<\pi$, a finite $\delta$ is at least two.

If $L=1$, every step is $N_\alpha$, and convergence for every real initial vector is the repeated-map conclusion of [TokenDampedSweepContraction.result](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), using [FinitePathDynamics.real_mulVec_powers_tendsto_zero](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean). Also $1<\delta$, so the asserted equivalence holds in this case. Now assume $2\leq L<\delta$. Choose any binary schedule having damping gap bound $L$ and any real initial state. The constants $\alpha,a,b,c$ remain fixed throughout the following argument. By (3.3) the nonnegative sequence $Q(u_t)$ is nonincreasing. It has a limit $e\geq0$, and

$$
Q(u_t)\leq Q(u_0),\qquad
\frac{x_t^2}{a}+\frac{y_t^2}{c}\leq Q(u_t).
\tag{4.1}
$$

Thus the entire real trajectory is bounded. List the damping times increasingly as $t_0<t_1<t_2<\cdots$. This list is infinite: otherwise a length-$L$ window after the last occurrence would contain none. The initial window gives $0\leq t_0\leq L-1$. For every $j$, the window starting at $t_j+1$ gives

$$
1\leq d_j:=t_{j+1}-t_j\leq L.
\tag{4.2}
$$

As $t_j\to\infty$, the loss at that damping step satisfies

$$
\gamma_\alpha(x_{t_j}-\xi y_{t_j})^2
=Q(u_{t_j})-Q(u_{t_j+1})\longrightarrow e-e=0.
\tag{4.3}
$$

Since $\gamma_\alpha>0$ is fixed, $x_{t_j}-\xi y_{t_j}\to0$.

Suppose for contradiction that $e>0$. There are only the $L$ possible values in (4.2), so some $d\in\{1,\ldots,L\}$ occurs for infinitely many $j$. Along those indices the inputs $u_{t_j}$ are bounded. The classical Bolzano–Weierstrass theorem in $\mathbb R^2$ supplies a subsequence, still with $d_j=d$, converging to a vector $w$. Polynomial continuity of $Q$ and (4.3) imply

$$
Q(w)=e>0,\qquad w\in H.
\tag{4.4}
$$

In particular $w\ne0$. Between two consecutive damping times there are exactly $d-1$ undamped transfers. The chronological recurrence therefore gives, on this subsequence,

$$
u_{t_{j+1}}=M^{d-1}N_\alpha u_{t_j}
\longrightarrow M^{d-1}N_\alpha w=M^d w,
\tag{4.5}
$$

where the last equality uses $w\in H$ and (3.4). Formula (4.3), applied to the next damping times $t_{j+1}$, also gives $x_{t_{j+1}}-\xi y_{t_{j+1}}\to0$. Passing to the limit in this linear functional and using (4.5) proves $M^d w\in H$.

Both $w$ and $M^d w$ thus lie in the one-dimensional space $H=\mathbb Rh$, and $w\ne0$. Hence $M^d w\in\mathbb Rw$, so (3.6) gives $d\theta\in\pi\mathbb Z$. The defining minimality of $\delta$ now yields $\delta\leq d\leq L$, contradicting $L<\delta$; if $\delta=\infty$, the existence of this $d$ is itself the contradiction. Therefore $e=0$. From (4.1), $x_t^2\leq aQ(u_t)\to0$ and $y_t^2\leq cQ(u_t)\to0$, proving $u_t\to0$ at all times. The schedule and initial vector were arbitrary, which proves the full universal side, including consecutive damped steps and every intermediate undamped phase.

For the converse let $\delta$ be finite and let $L\geq\delta$. Use Theorem 3.2 with $d=\delta$, initial vector $h$, and the schedule having damped occurrences exactly at $0,\delta,2\delta,\ldots$. Each window of $\delta$ consecutive integers contains a multiple of $\delta$, and each length-$L$ window contains such a subwindow, so this schedule has the required gap bound $L$. Its trajectory is $M^t h$ for every fixed $\alpha\in(0,1)$ and every time $t$. It is completely periodic, with $Q(M^t h)=Q(h)>0$, and cannot converge to zero by continuity of $Q$. It therefore disproves the universal assertion already at $L=\delta$ and for every larger integer $L$. If $\delta=\infty$, every finite $L$ was covered by the first part. This proves the equivalence with all boundary cases in its stated domain.

Finally (3.1) gives

$$
\det N_\alpha=2\tau_\alpha-1,
\qquad
\det N_\alpha=0
\quad\Longleftrightarrow\quad
\alpha=\frac{b}{a+2b}\in(0,1).
$$

At this parameter $\tau_\alpha=1/2$, so $\gamma_\alpha=(a+b)/(ab)>0$. Formulas (3.3), (3.4) and (4.5) therefore apply unchanged. No step of the convergence proof or the periodic construction requires an inverse of $N_\alpha$, which verifies the singular case explicitly.

The equal-velocity choice $a=b=c$ has $\theta=2\pi/3$ and $\delta=3$; its three-phase instance is Theorem 2.1. The present equivalences concern arbitrary positive triples and the chronological binary transfers of Definition 1.2. $\square$

## 追加锚（本行以下为增补区）

## 5. Irrational angles with diverging damping gaps

**Theorem 5.1 (Common initial state and schedule for every interior damping parameter).** For every $a,b,c>0$, retain the original centered matrices of Definition 3.1,

$$
A=\begin{pmatrix}1&0\\-2c&b+c\end{pmatrix},\qquad
B=\begin{pmatrix}-1&\dfrac{2a}{a+b}\\0&-(b+c)\end{pmatrix},\qquad
B_\alpha=\begin{pmatrix}
\dfrac{b(1-2\alpha)-\alpha a}{b+\alpha a}&\dfrac{2\alpha a}{b+\alpha a}\\
0&-(b+c)
\end{pmatrix},\qquad
M=A^{-1}B,\quad N_\alpha=A^{-1}B_\alpha,
$$

and put

$$
\theta=\arccos\left(\frac{2ac}{(a+b)(b+c)}-1\right),\qquad
Q(x,y)=\frac{x^2}{a}+\frac{(y-x)^2}{b}+\frac{y^2}{c},\qquad
\|u\|_Q=\sqrt{Q(u)}.
$$

Assume $\theta/(2\pi)\notin\mathbb Q$. There exist one $u_0\in\mathbb R^2\setminus\{0\}$ and one infinite binary schedule $\varepsilon$, both depending only on $(a,b,c)$, such that for every fixed $\alpha\in(0,1)$ the chronological recurrence

$$
u_{t+1}=\begin{cases}
N_\alpha u_t,&\varepsilon_t=1,\\
Mu_t,&\varepsilon_t=0
\end{cases}
\qquad(t\in\mathbb Z_{\geq0})
$$

has infinitely many damped times $t_0<t_1<t_2<\cdots$, with

$$
\{t\geq0:\varepsilon_t=1\}=\{t_j:j\geq0\},\qquad
\lim_{j\to\infty}(t_{j+1}-t_j)=\infty,\qquad
\inf_{t\in\mathbb Z_{\geq0}}\|u_t\|_Q
\geq\frac34\|u_0\|_Q>0.
$$

The choices of $u_0$, $\varepsilon$ and hence the times $t_j$ precede the universal quantifier over $\alpha$. The interval includes $\alpha=b/(a+2b)$, where $N_\alpha$ is singular. Each trajectory uses one fixed $\alpha$; its later states need not be common to different values of $\alpha$.

*Proof.* Fix an arbitrary positive triple satisfying the irrationality assumption. The form $Q$ and all coordinates remain as displayed. In particular $\|\cdot\|_Q$ is a norm: it is the Euclidean norm of the injective linear image

$$
(x,y)\longmapsto\left(\frac{x}{\sqrt a},\frac{y-x}{\sqrt b},\frac{y}{\sqrt c}\right).
$$

Thus its triangle inequality and reverse triangle inequality apply to differences of states as well as to states.

Use the coefficients $\xi,\eta,\tau_\alpha,C$ of Definition 3.1. The original-matrix identities (3.1), (3.3) and (3.4) give, for every $z=(x,y)^T\in\mathbb R^2$ and every $\alpha\in(0,1)$,

$$
\begin{gathered}
\|Mz\|_Q=\|z\|_Q,\qquad
Q(N_\alpha z)=Q(z)-4\tau_\alpha(1-\tau_\alpha)
                    \frac{a+b}{ab}(x-\xi y)^2\leq Q(z),\\
N_\alpha z=Mz\quad\text{if }z\in H=\{(x,y)^T:x=\xi y\}.
\end{gathered}
\tag{5.1}
$$

The weighted Dirichlet form is the one used in [the finite-path source](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean) and [the damped-sweep source](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), with their corresponding [finite-path](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs) and [damped-sweep](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs) statements; the first-event loss and equality mechanism are those of the damped-sweep source. The parameter correspondence is $m=2$, $(v_1,v_2,v_3)=(a,b,c)$, $(z_1,z_2)=(x,y)$ and $z_0=z_3=0$; zero-based indices are smaller by one. The first-event weight denoted `theta` in the damped-sweep source is $\tau_\alpha=\alpha(a+b)/(b+\alpha a)$ here, whereas $\theta$ in this theorem is the angle. The source transfer $M_\alpha$ is $N_\alpha$. The odd/even sweep and Token-1 first row have the hypotheses of [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, Sections IV.A and IV.B.1](https://arxiv.org/html/2608.27085v1#S4): positive velocities, zero centered endpoints, and a fixed interior damping parameter. The schedule here has precisely the abstract meaning of Definition 1.2.

Choose a unit vector on the common equality line by setting

$$
w=\begin{pmatrix}\xi\\1\end{pmatrix},\qquad
r=\sqrt{\frac1{a+b}+\frac1c},\qquad
u_0=\frac{w}{r}.
\tag{5.2}
$$

Indeed (3.2) gives $Q(w)=1/(a+b)+1/c=r^2>0$, and therefore $u_0\in H$, $u_0\ne0$ and $\|u_0\|_Q=1$. This choice depends only on the triple.

We next obtain arbitrarily late, arbitrarily close returns of $M^q u_0$ to $u_0$. Put $\beta=\theta/(2\pi)$, an irrational real number. For a real $s$, write $\{s\}=s-\lfloor s\rfloor$ and $\operatorname{dist}(s,\mathbb Z)=\min_{p\in\mathbb Z}|s-p|$; a nearest integer is one of $\lfloor s\rfloor$ and $\lfloor s\rfloor+1$. For every integer $R\geq2$, the number

$$
\mu_R=\min_{1\leq q<R}\operatorname{dist}(q\beta,\mathbb Z)
$$

is strictly positive: this is a minimum of finitely many positive numbers, since a positive integer multiple of an irrational number is not an integer. Given any $\rho>0$, choose a positive integer $K$ with $1/K<\min(\mu_R,\rho)$. Partition $[0,1)$ into the $K$ half-open intervals of length $1/K$. Two of the $K+1$ fractional parts $\{i\beta\}$, $0\leq i\leq K$, lie in the same interval. If their indices are $i<k$, put $q=k-i$ and $p=\lfloor k\beta\rfloor-\lfloor i\beta\rfloor$. Then

$$
1\leq q\leq K,\qquad
|q\beta-p|=|\{k\beta\}-\{i\beta\}|<\frac1K.
$$

If $q<R$, this contradicts $\mu_R\leq\operatorname{dist}(q\beta,\mathbb Z)\leq|q\beta-p|$. Consequently $q\geq R$ and $\operatorname{dist}(q\beta,\mathbb Z)<\rho$. This is the classical pigeonhole approximation argument, used here with the explicit exclusion of every $q<R$.

To pass from angular returns to the original vectors, use (3.5) with

$$
J=\frac{M-CI}{\sin\theta},\qquad
M^q=\cos(q\theta)I+\sin(q\theta)J,\qquad
D=1+\|Ju_0\|_Q>0.
$$

These expressions are defined because $0<\theta<\pi$. For a nearest integer $p$ to $q\beta$, put $s=q\theta-2\pi p$. The elementary bounds $|\sin s|\leq|s|$ and $|\cos s-1|\leq|s|$ follow from the real mean value theorem, since the derivatives of sine and cosine have absolute value at most one; see [NIST DLMF, §4.20](https://dlmf.nist.gov/4.20). Periodicity and the triangle inequality therefore give

$$
\begin{aligned}
\|M^q u_0-u_0\|_Q
&\leq|\cos s-1|\,\|u_0\|_Q+|\sin s|\,\|Ju_0\|_Q\\
&\leq D|s|
=2\pi D\operatorname{dist}(q\beta,\mathbb Z).
\end{aligned}
\tag{5.3}
$$

The addition formulas underlying (3.5) are [DLMF, (4.21.2) and (4.21.3)](https://dlmf.nist.gov/4.21#i). Given any $e>0$ and $R\geq2$, the preceding pigeonhole argument with $\rho=e/(2\pi D)$ supplies a $q\geq R$ for which $\|M^q u_0-u_0\|_Q<e$. All quantities in this return statement depend only on the triple, $e$ and $R$.

For each integer $j\geq0$, set $e_j=2^{-j-3}$ and define

$$
\begin{aligned}
d_j&=\min\{q\in\mathbb Z_{\geq1}:q\geq j+2
                 \text{ and }\|M^q u_0-u_0\|_Q\leq e_j\},\\
t_0&=0,\qquad t_{j+1}=t_j+d_j,\qquad
\varepsilon_t=\begin{cases}1,&t=t_j\text{ for some }j\geq0,\\0,&\text{otherwise}.
\end{cases}
\end{aligned}
\tag{5.4}
$$

The return statement proves that each set defining $d_j$ is nonempty; well-ordering of the positive integers supplies its minimum. These definitions contain no $\alpha$. Every $d_j$ is finite and at least $j+2$, so $t_j$ is strictly increasing, $t_j\geq2j$ and $t_j\to\infty$. Thus (5.4) defines the schedule at every integer time, its damped times are exactly the $t_j$, and $t_{j+1}-t_j=d_j\to\infty$. Each interval between consecutive damped times has $d_j-1\geq1$ undamped transfers.

Only now fix an arbitrary $\alpha\in(0,1)$, and let $(u_t)$ be its actual recurrence with (5.2) and (5.4). Define

$$
E_j=\sum_{i=0}^{j-1}e_i=\frac14(1-2^{-j})\qquad(j\geq0),
\tag{5.5}
$$

where the empty sum is zero. We prove by induction that

$$
\|u_{t_j}-u_0\|_Q\leq E_j.
\tag{5.6}
$$

It holds for $j=0$ because $t_0=0$. Suppose it holds for $j$. The schedule first applies $N_\alpha$ at $t_j$ and then applies $M$ at each of the next $d_j-1$ transfer times. In particular, at every intermediate phase, including the next damped input, the exact chronological formula is

$$
u_{t_j+k}=M^{k-1}N_\alpha u_{t_j}\qquad(1\leq k\leq d_j).
\tag{5.7}
$$

There is no omitted transfer between these states. Since $u_0\in H$, (5.1) says $N_\alpha u_0=Mu_0$. Linearity, the $Q$-isometry of $M$ and nonexpansiveness of $N_\alpha$ now yield, for every such $k$,

$$
\begin{aligned}
\|u_{t_j+k}-M^k u_0\|_Q
&=\|M^{k-1}N_\alpha(u_{t_j}-u_0)\|_Q\\
&=\|N_\alpha(u_{t_j}-u_0)\|_Q
\leq\|u_{t_j}-u_0\|_Q\leq E_j.
\end{aligned}
\tag{5.8}
$$

Taking $k=d_j$ in (5.8) and using the defining return bound in (5.4) gives

$$
\|u_{t_{j+1}}-u_0\|_Q
\leq\|u_{t_j+d_j}-M^{d_j}u_0\|_Q
   +\|M^{d_j}u_0-u_0\|_Q
\leq E_j+e_j=E_{j+1}.
$$

This completes the induction. At the input time $t_j$, (5.6) and the reverse triangle inequality give $\|u_{t_j}\|_Q\geq1-E_j$. At every phase $t_j+k$ with $1\leq k\leq d_j$, (5.8) and $\|M^k u_0\|_Q=1$ give the same lower bound. Every integer $t\geq0$ belongs to one of these intervals, since $t_0=0$ and $t_j\to\infty$. As $E_j\leq1/4$, it follows that

$$
\|u_t\|_Q\geq\frac34=\frac34\|u_0\|_Q>0
\qquad\text{for every integer }t\geq0.
$$

Taking the infimum proves the asserted all-time bound. The argument applies to each fixed $\alpha$ using the very same choices (5.2) and (5.4); it uses neither an $\alpha$-dependent return time nor equality of the resulting trajectories.

Finally, for $\alpha_*=b/(a+2b)$ positivity gives $0<\alpha_*<1$, and substitution into $\tau_\alpha$ gives $\tau_{\alpha_*}=1/2$. By (3.1), $\det N_{\alpha_*}=2\tau_{\alpha_*}-1=0$. Nevertheless the loss coefficient in (5.1) is then $(a+b)/(ab)>0$, the map is still nonexpansive in the same norm, and its equality $N_{\alpha_*}u_0=Mu_0$ still holds. Formulas (5.7) and (5.8) use no inverse of $N_\alpha$, so the entire proof includes this singular parameter. $\square$

## 追加锚（本行以下为增补区）

## 6. Exact decay and stable spaces for a prescribed schedule

**Definition 6.1 (Angular energy and original-coordinate stable space).** Fix an arbitrary triple $a,b,c>0$, one parameter $\alpha\in(0,1)$, and one prescribed infinite binary sequence $\varepsilon=(\varepsilon_t)_{t\geq0}$. Retain the literal matrices

$$
A=\begin{pmatrix}1&0\\-2c&b+c\end{pmatrix},\qquad
B=\begin{pmatrix}-1&\dfrac{2a}{a+b}\\0&-(b+c)\end{pmatrix},\qquad
B_\alpha=\begin{pmatrix}
\dfrac{b(1-2\alpha)-\alpha a}{b+\alpha a}&\dfrac{2\alpha a}{b+\alpha a}\\
0&-(b+c)
\end{pmatrix},\qquad M=A^{-1}B,\quad N_\alpha=A^{-1}B_\alpha,
$$

and the chronological recurrence $u_{t+1}=N_\alpha u_t$ when $\varepsilon_t=1$, and $u_{t+1}=Mu_t$ otherwise, for every $u_0\in\mathbb R^2$. Set

$$
\begin{gathered}
Q(x,y)=\frac{x^2}{a}+\frac{(y-x)^2}{b}+\frac{y^2}{c},\qquad
\|u\|_Q=\sqrt{Q(u)},\qquad
\theta=\arccos\left(\frac{2ac}{(a+b)(b+c)}-1\right),\\
\tau=\frac{\alpha(a+b)}{b+\alpha a},\qquad
\lambda=2\tau-1\in(-1,1),\qquad
S_{\varepsilon,\alpha}=\{u_0\in\mathbb R^2:u_t\longrightarrow0\}.
\end{gathered}
\tag{6.1}
$$

List the damped times as $t_0<t_1<\cdots$, allowing an empty list, a finite list of length $r\geq1$, or an infinite list. For each consecutive pair put $d_j=t_{j+1}-t_j\geq1$ and define

$$
\mathcal E_\varepsilon=\sum_j\sin^2(d_j\theta)\in[0,\infty].
\tag{6.2}
$$

The sum is over exactly the consecutive event pairs and is zero if there are fewer than two events. A consecutive gap is resonant if $\sin(d_j\theta)=0$, and orthogonal if $\cos(d_j\theta)=0$. The schedule is held fixed when comparing different fixed values of $\alpha$.

The positive definite inner product associated with $Q$ is

$$
\langle (x,y),(x',y')\rangle_Q
=\frac{xx'}a+\frac{(y-x)(y'-x')}b+\frac{yy'}c.
\tag{6.3}
$$

Write $H=\mathbb R(a,a+b)^T$, $h=(a,a+b)^T$, $e=h/\|h\|_Q$, and $Pz=e\langle e,z\rangle_Q$. Thus $P$ is the $Q$-orthogonal projection onto $H$. These are the parameters and equality line of Definition 3.1. In the [finite-path](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean) and [damped-sweep](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean) sources and their full [finite-path](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs) and [damped-sweep](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs) expositions, the correspondence is $m=2$, $(v_1,v_2,v_3)=(a,b,c)$, $(z_1,z_2)=(x,y)$, $z_0=z_3=0$, with indices reduced by one in the zero-based notation. Their first-event weight is $\tau$, and their transfer $M_\alpha$ is $N_\alpha$. The underlying odd/even rows, the entry $A_{21}=-2c$, and the Token-1 row are those of [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, Sections IV.A and IV.B.1](https://arxiv.org/html/2608.27085v1#S4), for positive velocities and zero centered endpoints in the rotational linear regime; the corresponding source locators are also given in the [source note](../../../Library/Dynamics/wallner2026passbucket.md).

**Theorem 6.2 (Prescribed-schedule classification).** In the full domain of Definition 6.1, every initial state tends to zero if and only if the following appropriate condition holds:

$$
\begin{array}{ll}
\lambda\ne0:&\text{there are infinitely many events and }\mathcal E_\varepsilon=\infty;\\[2pt]
\lambda=0:&\text{an orthogonal consecutive gap exists, or there are infinitely many events and }\mathcal E_\varepsilon=\infty.
\end{array}
\tag{6.4}
$$

Here $\lambda=0$ is exactly $\alpha=b/(a+2b)\in(0,1)$. The exact stable spaces are as follows.

1. In every case in (6.4), $S_{\varepsilon,\alpha}=\mathbb R^2$. At $\lambda=0$, an orthogonal gap from $t_j$ to $t_{j+1}$ makes every trajectory exactly zero from time $t_{j+1}+1$ onward.
2. If there are infinitely many events, $\mathcal E_\varepsilon<\infty$, and no orthogonal-gap annihilation at $\lambda=0$, then $S_{\varepsilon,\alpha}$ is a line. The schedule-and-parameter functional $L_{\varepsilon,\alpha}$ given by (6.9) in the singular case and (6.20) in the nonsingular case is nonzero and satisfies

$$
S_{\varepsilon,\alpha}=\ker L_{\varepsilon,\alpha},\qquad
\lim_{t\to\infty}\|u_t\|_Q=|L_{\varepsilon,\alpha}(u_0)|.
\tag{6.5}
$$

3. With no events, $S_{\varepsilon,\alpha}=\{0\}$. With finitely many events and $\lambda\ne0$, it is also $\{0\}$.
4. With $1\leq r<\infty$ events, $\lambda=0$, and no orthogonal gap, it is the line

$$
S_{\varepsilon,\alpha}
=\{u:\langle M^{-t_0}e,u\rangle_Q=0\}.
\tag{6.6}
$$

Every state outside the specified stable space has a strictly positive limiting $Q$-norm. The descriptions cover both rational and irrational $\theta/(2\pi)$ and bounded or unbounded gaps; in (6.20) the stable line may depend on the fixed value of $\alpha$.

*Proof.* The weighted Dirichlet identities (3.1)–(3.4) provide the common norm and equality line. Their first-event ingredients are the full local energy decomposition, damped-event loss, reflection invariance, equality case and source factorization in the damped-sweep source cited in Definition 6.1. To identify the factors used here, put $\xi=a/(a+b)$, $\eta=c/(b+c)$ and use exactly

$$
R=\begin{pmatrix}-1&2\xi\\0&1\end{pmatrix},\qquad
S=\begin{pmatrix}1&0\\2\eta&-1\end{pmatrix},\qquad
D=(1-\tau)I+\tau R.
$$

Equations (3.1) and (3.2) say $M=SR$, $N_\alpha=SD$, $R^2=I$, and that $R$ is the $Q$-orthogonal reflection fixing $H$. Hence $R=2P-I$, and, with no change to the source transfers,

$$
K=RD=\tau I+(1-\tau)R=P+\lambda(I-P),\qquad N_\alpha=MK.
\tag{6.7}
$$

In particular $M$ preserves $Q$, $K$ fixes $H$ and multiplies $H^{\perp_Q}$ by $\lambda$. The identity $0<\tau<1$ was proved in Definition 3.1. Solving $2\alpha(a+b)=b+\alpha a$ gives the asserted singular value. Also $\det M=1$ and $\det K=\lambda$, so the damped transfer is invertible exactly when $\lambda\ne0$.

For an event index $j$, put

$$
e_j=M^{-t_j}e,\qquad
P_jz=e_j\langle e_j,z\rangle_Q,\qquad
K_j=P_j+\lambda(I-P_j).
\tag{6.8}
$$

These are explicit maps in the original real coordinates. For example, if $G=\begin{pmatrix}1/a+1/b&-1/b\\-1/b&1/b+1/c\end{pmatrix}$, then $P_j=e_je_j^TG$ and $\langle z,w\rangle_Q=z^TGw$. The interaction vectors at the damped inputs are $v_j=M^{-t_j}u_{t_j}$. Before the first event there are $t_0$ undamped transfers, so $v_0=u_0$. The exact interval between consecutive damped inputs is

$$
u_{t_{j+1}}=M^{d_j-1}N_\alpha u_{t_j}=M^{d_j}Ku_{t_j},
\qquad v_{j+1}=K_jv_j.
$$

At the event itself, $M^{-(t_j+1)}u_{t_j+1}=K_jv_j$; this interaction vector stays constant through all subsequent undamped steps until the next event. For a finite list of $r$ events define $v_r$ by this formula after the last event. Thus the limiting norm of the full chronological trajectory is exactly the limiting norm of these interaction vectors, or $\|v_r\|_Q$ for a finite list. Moreover $u_t\to0$ if and only if its $Q$-norm tends to zero: the defining sum for $Q$ gives $x_t^2\leq aQ(u_t)$ and $y_t^2\leq cQ(u_t)$, and the reverse implication follows by continuity. In particular this reduction includes every intermediate undamped phase.

Each map $K_j$ in (6.8) fixes the range of $P_j$ and has a fixed strict contraction in its $Q$-orthogonal complementary direction. They are paracontractions for $\|\cdot\|_Q$ in the terminology of [Beyn and Elsner, *Infinite products and paracontracting matrices*, §2](https://doi.org/10.13001/1081-3810.1006): $K_jz\ne z$ implies $\|K_jz\|_Q<\|z\|_Q$. At $\lambda=0$ they are orthogonal projections. The classical cyclic projection theorem of von Neumann–Halperin fixes a finite family of closed subspaces; its hypotheses and angle conventions are recalled in [Badea, Grivaux and Müller, arXiv:1006.2047v1, §1A–B](https://arxiv.org/abs/1006.2047v1). The projections here are specified individually by (6.8); the subsequent argument proves the needed conclusions for this entire possibly infinite family.

First consider $\lambda=0$. Each $K_j=P_j$ has rank one. Formula (3.5), the $Q$-isometry of $M$, and the rotation calculation below give $\langle e_{j+1},e_j\rangle_Q=\cos(d_j\theta)$. Consequently for $r\geq1$ events,

$$
\|v_r\|_Q
=|\langle e_0,u_0\rangle_Q|
  \prod_{j=0}^{r-2}|\cos(d_j\theta)|.
$$

Indeed $v_1=e_0\langle e_0,u_0\rangle_Q$, and projecting a multiple of $e_j$ onto $\mathbb Re_{j+1}$ multiplies its coefficient by the indicated inner product. This proves the formula by induction, including $r=1$ with its empty product. An orthogonal gap makes $P_{j+1}P_j=0$, so after the second of those events all interaction vectors, and therefore all actual states, are zero. With a finite list and no such gap the product is positive and proves (6.6).

For an infinite list with no orthogonal gap, the same finite-product formula gives the exact functional, whenever $\mathcal E_\varepsilon<\infty$,

$$
L_{\varepsilon,\alpha}(u)
=\left(\prod_{j=0}^{\infty}|\cos(d_j\theta)|\right)
  \langle M^{-t_0}e,u\rangle_Q.
\tag{6.9}
$$

To justify its nonzero scalar factor, put $z_j=\sin^2(d_j\theta)$. Every factor is $\sqrt{1-z_j}>0$. On $0\leq z\leq1/2$, integration of $1/(1-z)$ between $0$ and $z$ gives

$$
\frac z2\leq-\frac12\log(1-z)\leq z.
$$

Thus if $\sum_jz_j<\infty$, all sufficiently late $z_j$ are at most $1/2$ and the logarithmic series converges; the finitely many earlier factors are positive. The product in (6.9) is positive. If instead $\sum_jz_j=\infty$, the inequality $-\frac12\log(1-z)\geq z/2$ on $[0,1)$ forces the product to vanish. This proves all infinite-event assertions at the singular parameter directly, with orthogonal gaps treated separately.

We now give an angular description that also treats every nonzero $\lambda\in(-1,1)$. Set $C=\cos\theta$ and

$$
J=\frac{M-CI}{\sin\theta}.
$$

Here $0<\theta<\pi$ ensures a positive denominator. The characteristic identity proved before (3.5) gives $J^2=-I$ and $M^{-1}=2CI-M$. If a star denotes the adjoint for (6.3), $M^*=M^{-1}$ by (3.3), so $J^*=-J$ and $J^*J=I$. It follows that $e,Je$ are $Q$-orthonormal. Formula (3.5) extends to negative powers by $M^{-1}=\cos\theta I-\sin\theta J$, hence

$$
e_{j+1}=\cos(d_j\theta)e_j-\sin(d_j\theta)Je_j.
\tag{6.10}
$$

This also proves the inner product used in the singular case.

Choose signs using only the gap angles. For $x\in\mathbb R$, let $\operatorname{sgn}_+(x)=1$ if $x\geq0$, and $-1$ otherwise. Define

$$
\begin{gathered}
\sigma_0=1,\qquad
\sigma_{j+1}=\sigma_j\operatorname{sgn}_+(\cos(d_j\theta)),\qquad
p_j=\sigma_je_j,\quad q_j=Jp_j,\\
c_j=|\cos(d_j\theta)|,\qquad
s_j=-\operatorname{sgn}_+(\cos(d_j\theta))\sin(d_j\theta).
\end{gathered}
\tag{6.11}
$$

Then $c_j\geq0$, $c_j^2+s_j^2=1$, $s_j^2=\sin^2(d_j\theta)$, and (6.10) gives $p_{j+1}=c_jp_j+s_jq_j$, $q_{j+1}=-s_jp_j+c_jq_j$. The convention at a zero cosine makes these formulas valid there as well. Writing $v_j=A_jp_j+B_jq_j$ therefore gives the exact scalar relations

$$
A_{j+1}=c_jA_j+\lambda s_jB_j,\qquad
B_{j+1}=-s_jA_j+\lambda c_jB_j,
\tag{6.12}
$$

and the loss identity

$$
\|v_{j+1}\|_Q^2=\|v_j\|_Q^2-(1-\lambda^2)B_j^2.
\tag{6.13}
$$

For an infinite list the norms are nonincreasing and have a limit $\ell\geq0$. Telescoping (6.13), using $1-\lambda^2>0$, shows $\sum_jB_j^2<\infty$ and hence $B_j\to0$. If $\ell>0$, then $A_j^2=\|v_j\|_Q^2-B_j^2\geq\ell^2/2$ for all sufficiently large $j$. The second relation in (6.12) implies

$$
s_j^2A_j^2=(\lambda c_jB_j-B_{j+1})^2
\leq2\lambda^2B_j^2+2B_{j+1}^2.
$$

Summation proves $\sum_js_j^2<\infty$. Thus infinite angular energy forces $\ell=0$ for every initial vector. This argument uses one actual trajectory and its two consecutive event inputs throughout; it imposes no restriction on the gaps.

For completeness, an explicit functional and its positivity will prove the converse for infinite lists with finite angular energy and $\lambda\ne0$. All the following coefficients are defined from the schedule, $a,b,c$ and the fixed $\alpha$, before choosing an initial state. Put

$$
\rho=|\lambda|\in(0,1),\qquad
\delta=\frac{1-\rho}{8},\qquad
\kappa=1-2\delta=\frac{3+\rho}{4},\qquad
\omega=\frac{\rho}{\kappa^2}<1.
\tag{6.14}
$$

The last inequality follows from $\kappa^2-\rho=(1-\rho)(9-\rho)/16>0$. Since $\sum_js_j^2<\infty$, there is a least integer

$$
J_0=\min\{j\geq0:|s_k|\leq\delta\text{ for every }k\geq j\}.
$$

For $j\geq J_0$ and $|r|\leq1$ define the real fractional linear function

$$
F_j(r)=\frac{\lambda(s_j+c_jr)}{c_j-s_jr}.
\tag{6.15}
$$

There are no vanishing denominators on this interval. Indeed $c_j=\sqrt{1-s_j^2}\geq1-\delta$, whence $c_j-s_jr\geq\kappa>0$. Also

$$
|F_j(r)|\leq\frac{\rho(1+\delta)}\kappa<1,
\qquad
|F'_j(r)|=\frac{\rho}{(c_j-s_jr)^2}\leq\omega<1.
$$

For the strict first bound, $\kappa-\rho(1+\delta)=1-\rho-(2+\rho)\delta\geq1-\rho-3\delta>0$. The derivative formula uses $c_j^2+s_j^2=1$ and is valid also for negative $\lambda$.

For each $n\geq J_0$ define the finite continued fraction by its terminal value $r_{n+1}^{[n]}=0$ and the backward recursion $r_j^{[n]}=F_j(r_{j+1}^{[n]})$, $j=n,n-1,\ldots,J_0$. Every entry lies in $[-1,1]$. For $m>n\geq j$, the common contractions at indices $j,\ldots,n$ give

$$
|r_j^{[m]}-r_j^{[n]}|\leq\omega^{n+1-j}.
$$

The right side tends to zero. Thus the following limits exist as ordinary real numbers, and continuity supplies their displayed recursion:

$$
r_j=\lim_{n\to\infty}r_j^{[n]}\in[-1,1],\qquad
r_j=F_j(r_{j+1})\quad(j\geq J_0).
\tag{6.16}
$$

This defines the coefficients by convergent scalar continued fractions rather than by any initial-state trajectory. To control their tails, the derivative bound and $|F_j(0)|=\rho|s_j|/c_j$ imply

$$
|r_j|\leq\frac{\rho}{1-\delta}|s_j|+\omega|r_{j+1}|
\leq\frac{\rho}{1-\delta}\sum_{k=j}^{\infty}\omega^{k-j}|s_k|.
\tag{6.17}
$$

The second inequality follows by iteration, since the bounded remainder tends to zero. Weighted Cauchy–Schwarz gives

$$
\left(\sum_{k=j}^{\infty}\omega^{k-j}|s_k|\right)^2
\leq\frac1{1-\omega}\sum_{k=j}^{\infty}\omega^{k-j}s_k^2.
$$

Sum this nonnegative inequality over $j\geq J_0$ and interchange the sums; for each $k$ the sum of its weights is at most $1/(1-\omega)$. Consequently

$$
\sum_{j=J_0}^{\infty}r_j^2
\leq\frac{\rho^2}{(1-\delta)^2(1-\omega)^2}
     \sum_{j=J_0}^{\infty}s_j^2<\infty,
$$

so in particular $r_j\to0$.

Define positive scalar factors and their infinite product by

$$
g_j=c_j-s_jr_{j+1}\geq\kappa,\qquad
\Gamma=\prod_{j=J_0}^{\infty}g_j.
\tag{6.18}
$$

This product converges to a strictly positive finite number. In fact $1-c_j=s_j^2/(1+c_j)\leq s_j^2$, and (6.17) and Cauchy–Schwarz yield

$$
\sum_{j=J_0}^{\infty}|g_j-1|
\leq\sum_{j=J_0}^{\infty}s_j^2
 +\left(\sum_{j=J_0}^{\infty}s_j^2\right)^{1/2}
  \left(\sum_{j=J_0}^{\infty}r_{j+1}^2\right)^{1/2}<\infty.
$$

Eventually $|g_j-1|\leq1/2$. The mean value theorem for $\log$ on $[1/2,3/2]$ gives $|\log g_j|\leq2|g_j-1|$ there, and the finitely many earlier $g_j$ are positive. Exponentiating the convergent logarithmic series proves the assertion about $\Gamma$.

Only a finite original-coordinate map is needed before this scalar construction. Set

$$
V=\begin{cases}I,&J_0=0,\\K_{J_0-1}\cdots K_1K_0,&J_0\geq1,\end{cases}
\qquad
w=\Gamma V^*(p_{J_0}+r_{J_0}q_{J_0}).
\tag{6.19}
$$

Here $V^*$ is the adjoint for $Q$; every $K_j$ is self-adjoint, so the second expression uses the reverse finite product $K_0K_1\cdots K_{J_0-1}$. The promised functional is

$$
\boxed{\quad L_{\varepsilon,\alpha}(u)=\langle w,u\rangle_Q
=\Gamma\langle p_{J_0}+r_{J_0}q_{J_0},Vu\rangle_Q.\quad}
\tag{6.20}
$$

Equations (6.8), (6.10), (6.11) and (6.14)–(6.20) are its complete schedule-and-parameter description. In the original initial-state coordinates its row is $w^TG$. All powers in the finite prefix are of the given $M$, every projection is $e_je_j^TG$, the signs are specified in (6.11), and the remaining quantities are scalar continued fractions and an absolutely convergent logarithmic product. None of these definitions asks which initial vectors decay.

To prove the formula for the norm limit, let $A_j,B_j$ now be the coefficients of an arbitrary actual trajectory in (6.12). The recursion (6.16) is precisely the identity

$$
A_{j+1}+r_{j+1}B_{j+1}
=(c_j-s_jr_{j+1})A_j
 +\lambda(s_j+c_jr_{j+1})B_j
=g_j(A_j+r_jB_j).
\tag{6.21}
$$

Iterating from $J_0$ to $n$ and using (6.18) shows

$$
\lim_{n\to\infty}(A_n+r_nB_n)
=\Gamma(A_{J_0}+r_{J_0}B_{J_0})
=L_{\varepsilon,\alpha}(u_0),
$$

because $v_{J_0}=Vu_0$. By (6.13), $B_n\to0$, and $r_n$ is bounded, so $A_n$ has that same limit. Since $\|v_n\|_Q^2=A_n^2+B_n^2$, this proves (6.5) for the full chronological trajectory. The functional is nonzero: each $K_j$ has eigenvalues $1,\lambda$ and is invertible, so $V^*$ is invertible; $p_{J_0}+r_{J_0}q_{J_0}\ne0$ by orthonormality, and $\Gamma>0$. Thus $w\ne0$ and its orthogonal kernel is a one-dimensional subspace of the original coordinate plane. This proves both necessity in (6.4) and the claimed exact stable line without requiring that the states themselves have a nonzero vector limit.

It remains to include the finite-event nonsingular case and the empty list. With $r<\infty$ events and $\lambda\ne0$, the finite map $K_{r-1}\cdots K_0$ is invertible; its value at a nonzero $u_0$ has positive $Q$-norm. After the last event that norm stays constant, since all remaining transfers are $M$. Thus only zero decays. With no events every step preserves $Q$, for any allowed $\alpha$, and again only zero decays. The singular finite-event case was proved by the rank-one formula, including $r=1$ and every possible zero cosine. All cases of (6.4)–(6.6) and every positive-limit assertion now follow. $\square$

**Corollary 6.3 (Angle arithmetic, subspaces and parameter quantifiers).** For a fixed positive triple and prescribed schedule, the following consequences hold.

If $\theta/(2\pi)\in\mathbb Q$, finite angular energy is equivalent to having only finitely many nonresonant consecutive gaps. If $\theta/(2\pi)\notin\mathbb Q$, no positive integer gap is resonant or orthogonal. For every fixed interior $\alpha$ the universal-decay criterion is the same divergence condition in (6.4), subject exactly to its singular orthogonal-gap exception.

For the exact space $S=S_{\varepsilon,\alpha}$ and every linear subspace $W\subseteq\mathbb R^2$,

$$
\begin{aligned}
(\forall u_0\in W,\ u_t\to0)&\quad\Longleftrightarrow\quad W\subseteq S,\\
(\forall u_0\in W\setminus\{0\},\ u_t\not\to0)
&\quad\Longleftrightarrow\quad W\cap S=\{0\}.
\end{aligned}
\tag{6.22}
$$

The full set of nondecaying initial states is $\mathbb R^2\setminus S$.

*Proof.* If $\theta/(2\pi)=k/r\in\mathbb Q$, the values $\sin^2(d\theta)$ for integers $d\geq1$ belong to a finite set. Its nonzero elements have a positive minimum. Infinitely many nonresonant gaps therefore force an infinite sum, whereas finitely many contribute a finite sum; the assertion also covers every finite event list. If the angle ratio is irrational, an equation $d\theta\in\pi\mathbb Z$ or $d\theta\in\pi/2+\pi\mathbb Z$ with $d\geq1$ would make the ratio rational, which proves both exclusions. These facts and (6.4) prove the parameter assertion, with the same fixed event times and gap angles on each comparison. The coefficients in (6.14)–(6.20) retain the fixed $\lambda$ and therefore describe each finite-energy stable line with its own parameter.

Theorem 6.2 identifies $S$ as the whole plane, a kernel of a nonzero functional, or zero; in particular it is a linear subspace. An initial vector decays exactly when it belongs to that identified space. Restricting this equivalence to $W$ proves the first statement of (6.22); restricting to its nonzero vectors proves the second, and taking the complement gives the last assertion.

For the specializations, $\varepsilon_t\equiv1$ has $d_j=1$ and $\sin\theta>0$, so its angular energy diverges, in agreement with the repeated fixed-map conclusion in [TokenDampedSweepContraction.result](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), its finite-path power-decay intermediary, and the [source-bound fixed-map statement](../../../Problems/wallner-krupke-schmidt-fekete-2026-token-spectral-contraction.md). The periodic family of Theorem 3.2 has only resonant gaps and keeps its common nondecaying state. If the entire schedule has gap bound $L<\delta$ in Definition 4.1, the possible gaps form a finite set with positive minimum squared sine, so (6.2) diverges and gives the convergence in Theorem 4.2. The irrational schedule and common initial state in Theorem 5.1 remain covered by that theorem: (6.4) implies that its angular energy is finite, since the uniform lower bound in Theorem 5.1 gives a strictly positive norm limit. All statements concern the prescribed centered linear recurrence of Definition 6.1 with one fixed interior damping parameter. $\square$

## 追加锚（本行以下为增补区）

## 7. Variable damping with a uniform upper bound

**Definition 7.1 (Prescribed variable event parameters).** Fix any $a,b,c>0$. Retain the original centered coordinates, zero exterior coordinates, and literal matrices of Definition 3.1:

$$
A=\begin{pmatrix}1&0\\-2c&b+c\end{pmatrix},\qquad
B=\begin{pmatrix}-1&\dfrac{2a}{a+b}\\0&-(b+c)\end{pmatrix},\qquad
B_\alpha=\begin{pmatrix}
\dfrac{b(1-2\alpha)-\alpha a}{b+\alpha a}&\dfrac{2\alpha a}{b+\alpha a}\\
0&-(b+c)
\end{pmatrix},\qquad
M=A^{-1}B,\quad N_\alpha=A^{-1}B_\alpha.
\tag{7.1}
$$

Prescribe a binary schedule $(\varepsilon_t)_{t\geq0}$ and, for its increasingly listed event times $t_j$, parameters $\alpha_j\in(0,1)$. The event list may be empty, finite, or infinite. Both the schedule and all these parameters are fixed before the initial vector is chosen. For every $u_0\in\mathbb R^2$, with no restriction on its norm, define the entire chronological trajectory by

$$
u_{t+1}=\begin{cases}
N_{\alpha_j}u_t,&t=t_j,\\
Mu_t,&\varepsilon_t=0,
\end{cases}\qquad t\in\mathbb Z_{\geq0}.
\tag{7.2}
$$

Put

$$
\begin{gathered}
Q(x,y)=\frac{x^2}{a}+\frac{(y-x)^2}{b}+\frac{y^2}{c},\qquad
\|u\|_Q=\sqrt{Q(u)},\qquad
G=\begin{pmatrix}1/a+1/b&-1/b\\-1/b&1/b+1/c\end{pmatrix},\\
\langle z,w\rangle_Q=z^TGw,\qquad
\theta=\arccos\left(\frac{2ac}{(a+b)(b+c)}-1\right)\in(0,\pi),\\
\tau_j=\frac{\alpha_j(a+b)}{b+\alpha_j a},\qquad
\lambda_j=2\tau_j-1=\frac{\alpha_j(a+2b)-b}{b+\alpha_j a}\in(-1,1),\\
d_j=t_{j+1}-t_j\geq1,\qquad
\mathcal E_\varepsilon=\sum_j\sin^2(d_j\theta),\qquad
S_{\varepsilon,\boldsymbol\alpha}=\{u_0:u_t\longrightarrow0\}.
\end{gathered}
\tag{7.3}
$$

The sum has one term for each consecutive event pair, and is zero for fewer than two events. The uniform upper bound hypothesis is

$$
\mathrm{(U)}\qquad
\text{there is a }\rho\in[0,1)\text{ such that }|\lambda_j|\leq\rho
\text{ at every event.}
\tag{7.4}
$$

This imposes no positive lower bound on $|\lambda_j|$. The singular parameter at an event is exactly $\alpha_j=b/(a+2b)$, or $\lambda_j=0$. No arithmetic condition on $\theta/(2\pi)$ and no upper bound on the positive integer gaps or on $t_0$ is part of these definitions.

The matrices in (7.1) specialize [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, Sections IV.A and IV.B.1](https://arxiv.org/html/2608.27085v1#S4), with $m=2$, $(v_1,v_2,v_3)=(a,b,c)$, $(z_1,z_2)=(x,y)$ and $z_0=z_3=0$. In particular the even-row coefficient is $A_{21}=-2c$. The source's $M_\alpha$ is $N_\alpha$ here. In the [damped-sweep definitions and complete proof](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean) and its [Scribe](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs), indices are reduced by one and the local weight named `theta` is $\tau_j$, rather than the angle $\theta$. The weighted Dirichlet form is the same as in [FinitePathDynamics](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean) and its [Scribe](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs). The [source note](../../../Library/Dynamics/wallner2026passbucket.md) and [fixed-map statement](../../../Problems/wallner-krupke-schmidt-fekete-2026-token-spectral-contraction.md) retain one fixed interior parameter for all powers of $N_\alpha$. Equation (7.2) instead prescribes that parameter separately at each event in the same two-coordinate linear recurrence.

**Theorem 7.2 (Angular divergence under a uniform upper bound).** In Definition 7.1, assume (U). If there are infinitely many events and $\mathcal E_\varepsilon=\infty$, then $u_t\to0$ as $t\to\infty$ for every real $u_0$. This includes arbitrary signs of $\lambda_j$, singular events, rational or irrational $\theta/(2\pi)$, consecutive events, and unbounded gaps.

*Proof.* Use the equality line, projection and rotation from (6.3), (6.7) and (6.10):

$$
h=(a,a+b)^T,\qquad e=\frac{h}{\|h\|_Q},\qquad
P=ee^TG,\qquad J=\frac{M-\cos\theta\,I}{\sin\theta}.
$$

The identities (3.1)–(3.4) and (6.7), applied separately to each $\alpha_j$, give

$$
N_{\alpha_j}=M K^{(j)},\qquad
K^{(j)}=P+\lambda_j(I-P),\qquad
Q(Mz)=Q(z).
\tag{7.5}
$$

These use the original first-event loss and equality mechanism: `local_energy_decomposition`, `Q_dampedEvent_loss`, `Q_event`, `Q_sweepTheta_eq_iff`, `dampedEvent_eq_of_fixed`, `sweepTheta_of_fixed` and `source_factorization` in the damped-sweep source cited in Definition 7.1. In the notation of (3.1), $R=2P-I$, $M=SR$, $N_{\alpha_j}=S((1-\tau_j)I+\tau_jR)$ and $R^2=I$, so multiplication gives (7.5). The rotation identities already established in the proof of Theorem 6.2 give $J^2=-I$, $J$ skew-adjoint and isometric for $Q$, and $e,Je$ orthonormal. They also give $M^k=\cos(k\theta)I+\sin(k\theta)J$ for every integer $k$.

For each event define, in the original real coordinates,

$$
\begin{gathered}
e_j=M^{-t_j}e,\qquad P_j=e_je_j^TG,\qquad
\mathcal K_j=P_j+\lambda_j(I-P_j),\\
V_0=I,\qquad V_{j+1}=\mathcal K_jV_j,\qquad
v_j=M^{-t_j}u_{t_j}.
\end{gathered}
\tag{7.6}
$$

There are exactly $t_0$ undamped transfers before the first event, hence $v_0=u_0$. Between consecutive event inputs the full chronological formula is

$$
\begin{gathered}
u_{t_j+k}=M^{k-1}N_{\alpha_j}u_{t_j}\quad(1\leq k\leq d_j),\\
u_{t_{j+1}}=M^{d_j}K^{(j)}u_{t_j},\qquad
v_{j+1}=\mathcal K_jv_j=V_{j+1}u_0.
\end{gathered}
\tag{7.7}
$$

At time $t_j+1$, the interaction vector $M^{-(t_j+1)}u_{t_j+1}$ is $v_{j+1}$ and it stays equal to that vector through the following undamped transfers. For a finite list the first formula holds for every $k\geq1$ after its last event. More generally let $\nu(t)$ be the number of events strictly before $t$. This is finite at every integer time, and (7.5) proves by induction that

$$
u_t=M^tV_{\nu(t)}u_0,\qquad
\|u_t\|_Q=\|V_{\nu(t)}u_0\|_Q.
\tag{7.8}
$$

Use $V_0=I$ throughout if the event list is empty. Thus the norm limit along an infinite event list is the norm limit of the entire chronological trajectory, including every undamped phase; for $r<\infty$ events it is $\|V_ru_0\|_Q$.

For the infinite list choose oriented representatives of the event lines exactly as in (6.11). Explicitly, put $\chi(x)=1$ for $x\geq0$ and $\chi(x)=-1$ for $x<0$, and define

$$
\begin{gathered}
\sigma_0=1,\qquad \sigma_{j+1}=\sigma_j\chi(\cos(d_j\theta)),\qquad
p_j=\sigma_je_j,\quad q_j=Jp_j,\\
c_j=|\cos(d_j\theta)|,\qquad
s_j=-\chi(\cos(d_j\theta))\sin(d_j\theta).
\end{gathered}
\tag{7.9}
$$

Then $(p_j,q_j)$ is $Q$-orthonormal, $c_j\geq0$, $c_j^2+s_j^2=1$ and $s_j^2=\sin^2(d_j\theta)$. Since $e_{j+1}=\cos(d_j\theta)e_j-\sin(d_j\theta)Je_j$, one has

$$
p_{j+1}=c_jp_j+s_jq_j,\qquad
q_{j+1}=-s_jp_j+c_jq_j.
$$

In particular this convention includes zero cosines. Write $v_j=A_jp_j+B_jq_j$. The map $\mathcal K_j$ sends this vector to $A_jp_j+\lambda_jB_jq_j$; taking its coordinates in the next orthonormal frame gives the variable-parameter version of (6.12)–(6.13):

$$
\begin{aligned}
A_{j+1}&=c_jA_j+\lambda_js_jB_j,\\
B_{j+1}&=-s_jA_j+\lambda_jc_jB_j,\\
\|v_{j+1}\|_Q^2&=\|v_j\|_Q^2-(1-\lambda_j^2)B_j^2.
\end{aligned}
\tag{7.10}
$$

Fix any actual initial vector and choose $\rho$ as in (U). The last identity gives a nonincreasing nonnegative norm sequence with a limit $\ell\geq0$, and telescoping gives

$$
(1-\rho^2)\sum_{j=0}^\infty B_j^2\leq\|u_0\|_Q^2.
\tag{7.11}
$$

Therefore $B_j\to0$. If $\ell>0$, then $A_j^2=\|v_j\|_Q^2-B_j^2\geq\ell^2/2$ for all sufficiently large $j$. The second identity in (7.10) implies

$$
s_j^2A_j^2=(\lambda_jc_jB_j-B_{j+1})^2
\leq2\rho^2B_j^2+2B_{j+1}^2.
$$

Summing on that tail and using (7.11) would give $\sum_js_j^2<\infty$, contradicting $\mathcal E_\varepsilon=\infty$. Hence $\ell=0$, and (7.8) gives $\|u_t\|_Q\to0$ at every chronological time. Since $x_t^2\leq aQ(u_t)$ and $y_t^2\leq cQ(u_t)$, it follows that $u_t\to0$. No inverse of an event factor was used, so zero $\lambda_j$ are included.

For comparison with classical product results, the loss in (7.10) is the paracontraction inequality of [Beyn and Elsner, *Infinite products and paracontracting matrices*, §2](https://doi.org/10.13001/1081-3810.1006): $\mathcal K_jz\ne z$ implies $\|\mathcal K_jz\|_Q<\|z\|_Q$. Their Theorem 2.3 concerns a finite family of matrices. The cyclic projection statement (1.2) in [Badea, Grivaux and Müller, arXiv:1006.2047v1, §1A](https://arxiv.org/html/1006.2047v1#S1.SS1) concerns powers of one cyclic product of a fixed finite family of closed subspaces. Here the possibly infinite family (7.6) has the particular rotation relation (7.9); the conclusion follows from its actual consecutive-input identities (7.10)–(7.11). $\square$

**Theorem 7.3 (Complete pointwise-nonsingular stable-space classification).** In Definition 7.1 assume (U) and $\lambda_j\ne0$ at every event, with no uniform positive lower bound. For an empty or finite event list,

$$
S_{\varepsilon,\boldsymbol\alpha}=\{0\}.
$$

For infinitely many events and $\mathcal E_\varepsilon=\infty$ this space is $\mathbb R^2$. For infinitely many events and $\mathcal E_\varepsilon<\infty$ it is the kernel of the following explicitly specified nonzero original-coordinate linear functional. Use (7.6) and (7.9), and define real rows and a row series by

$$
\begin{gathered}
\mathfrak a_j=p_j^TGV_j,\qquad
\mathfrak b_j=q_j^TGV_j,\\
\Lambda=\mathfrak a_0+
\sum_{j=0}^\infty\bigl((c_j-1)\mathfrak a_j+
                              \lambda_js_j\mathfrak b_j\bigr),\qquad
L_{\varepsilon,\boldsymbol\alpha}(u)=\Lambda u.
\end{gathered}
\tag{7.12}
$$

The row series converges absolutely. All its rows, matrices, signs and scalar coefficients depend solely on the prescribed positive triple, schedule and event parameters; in particular $p_0=M^{-t_0}e$ incorporates the arbitrary first event time. For every real initial vector, at its original norm scale,

$$
\lim_{t\to\infty}\|u_t\|_Q
=|L_{\varepsilon,\boldsymbol\alpha}(u_0)|,\qquad
S_{\varepsilon,\boldsymbol\alpha}=\ker L_{\varepsilon,\boldsymbol\alpha}.
\tag{7.13}
$$

Consequently the stable space in this case is one real line, and every state outside it has a strictly positive limiting $Q$-norm. These assertions cover every finite prefix, both arithmetic types of the angle, every positive integer gap, variable signs, and nonzero event factors arbitrarily close to zero.

*Proof.* The infinite-energy case is Theorem 7.2. Suppose the event list is infinite and its angular energy is finite. The identities (7.5)–(7.11) remain available, since their derivation did not require a constant parameter.

For a real row $f$ use the dual norm $\|f\|_{Q,*}=\sup_{\|z\|_Q=1}|fz|$. Because $e,Je$ are $Q$-orthonormal,

$$
\|f\|_{Q,*}^2=|fe|^2+|fJe|^2.
$$

This follows by writing $z=xe+yJe$: the supremum over $x^2+y^2=1$ is the Euclidean length of $(fe,fJe)$. Every $\mathcal K_j$ is nonexpansive, so $\|V_jz\|_Q\leq\|z\|_Q$ and $\|\mathfrak a_j\|_{Q,*}\leq1$. Apply (7.11) to the two initial vectors $e$ and $Je$. Their $B_j$ coordinates are respectively $\mathfrak b_je$ and $\mathfrak b_jJe$, and both initial norms are one. Adding the resulting inequalities gives

$$
\sum_{j=0}^\infty\|\mathfrak b_j\|_{Q,*}^2
\leq\frac{2}{1-\rho^2}.
\tag{7.14}
$$

Also $1-c_j=s_j^2/(1+c_j)\leq s_j^2$. The triangle inequality and Cauchy–Schwarz therefore give

$$
\begin{aligned}
\sum_{j=0}^\infty
\|(c_j-1)\mathfrak a_j+\lambda_js_j\mathfrak b_j\|_{Q,*}
&\leq\sum_{j=0}^\infty s_j^2+
\rho\left(\sum_{j=0}^\infty s_j^2\right)^{1/2}
\left(\sum_{j=0}^\infty\|\mathfrak b_j\|_{Q,*}^2\right)^{1/2}
<\infty.
\end{aligned}
\tag{7.15}
$$

This proves absolute convergence in the two-dimensional row space, so (7.12) defines a real linear functional without referring to any unknown stable space. Since (7.10) holds for every initial vector, its first identity is the row identity

$$
\mathfrak a_{j+1}-\mathfrak a_j
=(c_j-1)\mathfrak a_j+\lambda_js_j\mathfrak b_j.
$$

The series in (7.12) thus telescopes to $\Lambda=\lim_{n\to\infty}\mathfrak a_n$. For any $u_0$, it follows that $A_n=\mathfrak a_nu_0\to\Lambda u_0$, whereas (7.11) gives $B_n\to0$. Taking the norm in the orthonormal frame proves $\|v_n\|_Q\to|\Lambda u_0|$. Equation (7.8) now proves the full-time limit in (7.13), with no normalization of $u_0$.

It remains to prove $\Lambda\ne0$ using only pointwise nonsingularity. Choose an integer $N\geq0$ for which

$$
E_N:=\sum_{j=N}^\infty s_j^2<\frac{(1-\rho)^2}{4}.
\tag{7.16}
$$

Such an $N$ exists by convergence of the nonnegative series. Each $\mathcal K_j$ has eigenvalues $1,\lambda_j$, so the finite product $V_N$ is invertible. Select the real initial vector $u_*=V_N^{-1}p_N$. This is a legitimate vector in the stated unrestricted initial-state domain; there is no bound imposed on the norm of that finite inverse. Its interaction vector at index $N$ is exactly $v_N=p_N$, with $A_N=1$, $B_N=0$ and $\|v_N\|_Q=1$. Subsequent norms are at most one, and hence $|A_j|\leq1$ for $j\geq N$.

For this trajectory, the second identity in (7.10) gives

$$
|B_{j+1}|\leq|s_j|+\rho|B_j|,\qquad
|B_j|\leq\sum_{k=N}^{j-1}\rho^{j-1-k}|s_k|\quad(j>N).
$$

The second inequality follows by induction from $B_N=0$. Weighted Cauchy–Schwarz and the geometric sum give

$$
|B_j|^2\leq\frac1{1-\rho}
\sum_{k=N}^{j-1}\rho^{j-1-k}s_k^2.
$$

Sum first over a finite range of $j$ and then increase that range. All summands are nonnegative, and for each fixed $k$ the weights sum to $1/(1-\rho)$. Consequently

$$
\sum_{j=N}^\infty B_j^2\leq\frac{E_N}{(1-\rho)^2}.
$$

Telescoping the exact norm loss (7.10), starting at the unit vector $v_N$, now yields

$$
\lim_{j\to\infty}\|v_j\|_Q^2
=1-\sum_{j=N}^\infty(1-\lambda_j^2)B_j^2
\geq1-\frac{E_N}{(1-\rho)^2}>\frac34.
\tag{7.17}
$$

Thus $|L_{\varepsilon,\boldsymbol\alpha}(u_*)|>0$, proving that the row $\Lambda$ is nonzero. Only the finitely many nonzero numbers $\lambda_0,\ldots,\lambda_{N-1}$ were inverted. The tail estimates use (U) and do not divide by any tail $\lambda_j$. In particular no positive lower bound on the entire sequence has entered the proof.

Positive definiteness and continuity of $Q$ imply $u_t\to0$ exactly when $\|u_t\|_Q\to0$. The limit formula therefore identifies the stable space as the kernel of this nonzero row, a one-dimensional subspace in the original coordinate plane, and gives a positive limit at each point outside it. The fixed-parameter functional (6.20) and (7.12) have the same absolute value on every vector when $\lambda_j$ is constant, since both give that same norm limit; either functional describes the same stable line.

For a finite list of $r\geq1$ events, $V_r=\mathcal K_{r-1}\cdots\mathcal K_0$ is invertible for the same pointwise reason. Equation (7.8) gives the eventually constant norm $\|V_ru_0\|_Q$, which is positive exactly when $u_0\ne0$. With no events the norm is always $\|u_0\|_Q$. These observations prove the remaining cases. The arithmetic assertions in Corollary 6.3 concern only $d_j\theta$, so they apply unchanged: for a rational angle ratio, finite energy is equivalent to finitely many nonresonant gaps; an irrational angle ratio admits no resonant or orthogonal positive integer gap. Neither case changes any estimate above. $\square$

**Proposition 7.4 (Every-state failure when damping approaches the undamped endpoint).** In the literal system $a=b=c=1$, prescribe $\varepsilon_t=1$ at every integer time, so $t_j=j$, and prescribe before choosing $u_0$ the nonconstant sequence

$$
\alpha_j=\frac{2^{j+3}-1}{2^{j+3}+1}\in(0,1)\qquad(j\geq0).
\tag{7.18}
$$

Then $\alpha_j\uparrow1$, $\mathcal E_\varepsilon=\infty$, but every nonzero real initial state has a strictly positive limiting original $Q$-norm. More precisely, for the actual recurrence $u_{j+1}=N_{\alpha_j}u_j$,

$$
\frac12\|u_0\|_Q\leq\lim_{t\to\infty}\|u_t\|_Q\leq\|u_0\|_Q,
\qquad S_{\varepsilon,\boldsymbol\alpha}=\{0\}.
\tag{7.19}
$$

Thus the following unrestricted extension of the fixed-parameter angular-divergence implication is false: for every fixed positive triple, every prescribed binary schedule with infinitely many events, every prescribed interior event-parameter sequence and every real initial vector, $\mathcal E_\varepsilon=\infty$ implies $u_t\to0$.

*Proof.* The original matrices from Theorem 2.1 are

$$
A=\begin{pmatrix}1&0\\-2&2\end{pmatrix},\qquad
M=\begin{pmatrix}-1&1\\-1&0\end{pmatrix},\qquad
N_{\alpha_j}=\frac1{1+\alpha_j}
\begin{pmatrix}1-3\alpha_j&2\alpha_j\\1-3\alpha_j&\alpha_j-1\end{pmatrix},
$$

and the original quadratic form is $Q(x,y)=x^2+(y-x)^2+y^2$. The integers $2^{j+3}$ strictly increase to infinity, so $\alpha_j=1-2/(2^{j+3}+1)$ strictly increases to one while remaining strictly interior. Its event factor in (7.3) is exactly

$$
\lambda_j=\frac{3\alpha_j-1}{1+\alpha_j}
=1-2^{-j-2}\in(0,1),\qquad
\sum_{j=0}^\infty(1-\lambda_j)=\frac12.
\tag{7.20}
$$

Use the original-coordinate factorization (7.5), which is valid at each of these interior parameters without (U). Decompose any actual input as $z=Pz+(I-P)z$, orthogonally for $Q$. Since $M$ is a $Q$-isometry and $0<\lambda_j<1$,

$$
\begin{aligned}
\|N_{\alpha_j}z\|_Q^2
&=\|Pz\|_Q^2+\lambda_j^2\|(I-P)z\|_Q^2,\\
\lambda_j\|z\|_Q&\leq\|N_{\alpha_j}z\|_Q\leq\|z\|_Q.
\end{aligned}
$$

Apply these inequalities successively to $z=u_j$ in the prescribed recurrence. For every integer $n\geq1$ this gives

$$
\left(\prod_{j=0}^{n-1}\lambda_j\right)\|u_0\|_Q
\leq\|u_n\|_Q\leq\|u_0\|_Q.
$$

For nonnegative numbers $r_j\leq1$, induction using $(1-x)(1-y)\geq1-x-y$ proves $\prod_{j=0}^{n-1}(1-r_j)\geq1-\sum_{j=0}^{n-1}r_j$. With $r_j=2^{-j-2}$, the right side here is $1/2+2^{-n-1}>1/2$. Hence every chronological norm is at least $\|u_0\|_Q/2$. These are bounds on every actual trajectory, rather than a determinant assertion. The norms are also nonincreasing, so their limits exist and satisfy (7.19), including arbitrary initial scales. For $u_0\ne0$ positive definiteness gives a strictly positive limit; for $u_0=0$ the entire trajectory is zero. The elementary positive-product comparison used here is the same principle underlying (6.9) and (6.18), with its finite-product proof supplied above.

Finally $\theta=\arccos(-1/2)=2\pi/3$ and every gap is one. Thus every term of $\mathcal E_\varepsilon$ is $\sin^2(2\pi/3)=3/4$, and the sum diverges. At the same time $\lambda_j\uparrow1$, so no $\rho<1$ bounds all of them. This verifies the failure of the stated unrestricted implication without contradicting Theorem 7.2 or the fixed-map statements. $\square$

**Definition 7.5 (Unrestricted variable-parameter stable-space problem).** For (7.1)–(7.3) without (U), the unrestricted problem is to determine $S_{\varepsilon,\boldsymbol\alpha}$ for every fixed positive triple, every prescribed binary schedule and every prescribed sequence $\alpha_j\in(0,1)$. This domain permits approach to either endpoint, arbitrary signs of $\lambda_j$, and arbitrary interspersions of zero and nonzero $\lambda_j$. Theorem 7.2 gives angular-divergence sufficiency on the subdomain (U), including singular histories, while Theorem 7.3 gives the complete classification on the smaller subdomain (U) with pointwise nonvanishing. Proposition 7.4 specifies one history outside (U); it supplies no general classification on the unrestricted domain. The fixed-parameter singular classification and orthogonal-pair annihilation in Theorem 6.2 retain their stated constant-parameter hypotheses.

## 追加锚（本行以下为增补区）
## 8. Unrestricted histories and finite total logarithmic loss

**Definition 8.1 (Event products and tail inputs).** Use the entire domain of Definition 7.1, without (U). In particular the literal matrices are

$$
A=\begin{pmatrix}1&0\\-2c&b+c\end{pmatrix},\quad
B=\begin{pmatrix}-1&2a/(a+b)\\0&-(b+c)\end{pmatrix},\quad
B_\alpha=\begin{pmatrix}
[b(1-2\alpha)-\alpha a]/(b+\alpha a)&2\alpha a/(b+\alpha a)\\
0&-(b+c)
\end{pmatrix},\quad M=A^{-1}B,\quad N_\alpha=A^{-1}B_\alpha,
$$

where $a,b,c>0$, and the binary schedule and its interior event parameters are prescribed before $u_0$. Retain the original $Q,G,\theta,t_j,d_j$ of (7.3), and set

$$
\lambda_j=\frac{\alpha_j(a+2b)-b}{b+\alpha_j a},\qquad
\delta_j=1-\lambda_j^2\in(0,1],\qquad
\alpha_j=\frac{b(1+\lambda_j)}{a+2b-a\lambda_j}.
\tag{8.1}
$$

The last formula is an increasing bijection from $(-1,1)$ to $(0,1)$: its denominator is positive, its derivative is $2b(a+b)/(a+2b-a\lambda)^2>0$, and its endpoint values are $0,1$. Thus a prescribed sequence in $(-1,1)$ specifies actual original event parameters. Zero $\lambda_j$ means exactly the singular parameter $b/(a+2b)$.

Let $e=h/\|h\|_Q$, $h=(a,a+b)^T$, and $J=(M-\cos\theta I)/\sin\theta$, as in Section 7. For each event set

$$
e_j=M^{-t_j}e,\quad q_j=Je_j,\quad
P_j=e_je_j^TG,\quad K_j=P_j+\lambda_j(I-P_j).
$$

For event indices $s\leq n$ define only the finite products

$$
\Phi_{s,s}=I,\qquad
\Phi_{s,n}=K_{n-1}\cdots K_s\quad(n>s),\qquad
F_n=\Phi_{0,n}.
\tag{8.2}
$$

These definitions are also used on a finite list, within its index range. The adjoint of a real matrix $T$ is $T^*=G^{-1}T^TG$. All norms and orthogonality below refer to $Q$. An infinite nonsingular tail starts at an index $s$ such that $\lambda_j\ne0$ for every $j\geq s$; put

$$
D_s=\sum_{j=s}^\infty-\log|\lambda_j|\in(0,\infty].
\tag{8.3}
$$

Its input $z$ is in interaction coordinates. For an actual whole history this input is

$$
z=M^{-t_s}u_{t_s}=F_su_0.
\tag{8.4}
$$

The finite products do not invert any event factor. The source correspondence is the one in Definition 7.1: source $m=2$, velocities $(a,b,c)$, centered coordinates $(x,y)$ and zero exterior coordinates; source indices are reduced by one in Lean. The source $M_\alpha$ is $N_\alpha$, and its private first-event weight `theta` is $\tau_j=\alpha_j(a+b)/(b+\alpha_ja)$, not the rotation angle $\theta$. The local energy decomposition, loss, reflection identities and literal factorization are the complete `local_energy_decomposition`, `Q_dampedEvent_loss`, `Q_event`, `Q_sweepTheta_eq_iff`, `dampedEvent_eq_of_fixed`, `sweepTheta_of_fixed` and `source_factorization` bodies in [TokenDampedSweepContraction](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), with its complete [Scribe](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs). The same Dirichlet form, zero extension, rigidity, observability and fixed-map power implication occur in [FinitePathDynamics](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean) and its complete [Scribe](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs). The [source note](../../../Library/Dynamics/wallner2026passbucket.md) and [fixed-map statement](../../../Problems/wallner-krupke-schmidt-fekete-2026-token-spectral-contraction.md) concern repeated fixed $\alpha$. Their primary original is [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, Sections III and IV](https://arxiv.org/html/2608.27085v1#S3): the linear map has positive velocities and zero centered endpoints in the alternating, catch-up-free rotational regime. Arbitrarily prescribed variable histories remain the abstract linear domain (7.2); no collision realization is assumed.

**Theorem 8.2 (Finite lists, chronology and finite annihilation).** For every allowed history let $\nu(t)$ count events strictly before time $t$. Then

$$
u_t=M^tF_{\nu(t)}u_0,\qquad
\|u_t\|_Q=\|F_{\nu(t)}u_0\|_Q.
\tag{8.5}
$$

For $r<\infty$ events the exact full-time limiting norm is $\|F_ru_0\|_Q$, and the stable space is $\ker F_r$. Its dimension is $2-\operatorname{rank}F_r$. In particular the empty list has $F_0=I$ and stable space $\{0\}$; so does every finite wholly nonsingular list. Every finite list containing a singular factor has rank zero or one, distinguishable by its finite matrix $F_r$.

For any finite or infinite event list, an initial vector reaches zero in finite time exactly when $F_nu_0=0$ for some finite event prefix $n$, with $n=0$ allowed for $u_0=0$. A nonzero vector can first reach zero only just after a singular event $j$, and the exact condition at that event is

$$
F_ju_0\ne0,\qquad \lambda_j=0,\qquad e_j^TGF_ju_0=0.
\tag{8.6}
$$

All initial states have been annihilated by the end of event $j$ exactly when $F_{j+1}=0$. If $F_j\ne0$, this is equivalent to $\lambda_j=0$ and the finite row $e_j^TGF_j=0$.

*Proof.* The original factorization (7.5), with its actual event parameter at each occurrence, is $N_{\alpha_j}=M(P+\lambda_j(I-P))$. Conjugating its second factor by $M^{t_j}$ gives exactly $K_j$. Before the first event the interaction vector is $u_0$; an undamped transfer leaves it fixed and event $j$ multiplies it by $K_j$. Induction over chronological time proves (8.5). This is the identity (7.8) without any use of (U). Also

$$
\|K_jw\|_Q^2=\|w\|_Q^2-\delta_j|\langle q_j,w\rangle_Q|^2,
\qquad |\lambda_j|\|w\|_Q\leq\|K_jw\|_Q\leq\|w\|_Q.
\tag{8.7}
$$

After a finite list the norm therefore remains exactly $\|F_ru_0\|_Q$. Positive definiteness gives decay precisely on its kernel: $x_t^2\leq aQ(u_t)$ and $y_t^2\leq cQ(u_t)$, while continuity supplies the converse implication. Rank-nullity gives the dimension assertions. Each $K_j$ has eigenvalues $1,\lambda_j$, so finite nonsingular products are invertible; a singular factor has rank one and cannot subsequently increase rank.

The map $M$ never kills a nonzero vector. A nonsingular $K_j$ cannot do so either. At a singular event $K_j=P_j=e_je_j^TG$, which kills exactly $e_j^{\perp_Q}$. This proves (8.6), including the actual first zero time $t_j+1$. Applied to every input, the same calculation proves the matrix and row conditions. Zero is preserved by every later transfer. These finite tests therefore cover every possible finite annihilation, also within an infinite history. $\square$

**Theorem 8.3 (Exact positive-definite norm for a finite-loss nonsingular tail).** Suppose the event list is infinite, every $\lambda_j$ for $j\geq s$ is nonzero, and $D_s<\infty$. Define the prescribed real rows

$$
b_{s,j}=q_j^TG\Phi_{s,j}\quad(j\geq s),\qquad
H_{s,n}=G-\sum_{j=s}^{n-1}\delta_j b_{s,j}^Tb_{s,j}.
$$

Then the following matrix series converges entrywise, with absolute convergence of every entry:

$$
H_s=G-\sum_{j=s}^\infty\delta_j b_{s,j}^Tb_{s,j}.
\tag{8.8}
$$

It is positive definite and satisfies, for every $z\in\mathbb R^2$ and $n\geq s$,

$$
e^{-2D_s}Q(z)\leq z^TH_sz\leq Q(z),\qquad
0\leq z^T(H_{s,n}-H_s)z\leq2D_nQ(z).
\tag{8.9}
$$

The exact full chronological limiting norm for tail input $z$ is $\sqrt{z^TH_sz}$. Consequently no nonzero vector reaching this tail is erased, and its stable space is $\{0\}$. This plane norm is not the absolute value of one linear functional.

*Proof.* Apply the exact loss (8.7) successively, starting with $z$ at index $s$. For every finite $n$ it gives

$$
\|\Phi_{s,n}z\|_Q^2
=Q(z)-\sum_{j=s}^{n-1}\delta_j|b_{s,j}z|^2
=z^TH_{s,n}z.
\tag{8.10}
$$

The nonnegative loss sum is bounded by $Q(z)$. Applied to the two ordinary coordinate vectors this bounds the sums of both diagonal entries of the series in (8.8). Absolute summability of its off-diagonal entries follows from Cauchy--Schwarz:

$$
\sum_j\delta_j|(b_{s,j})_1(b_{s,j})_2|
\leq\left(\sum_j\delta_j|(b_{s,j})_1|^2\right)^{1/2}
     \left(\sum_j\delta_j|(b_{s,j})_2|^2\right)^{1/2}.
$$

Thus (8.8) exists with the asserted convergence. The lower inequality in (8.7) gives

$$
\|\Phi_{s,n}z\|_Q\geq
\exp\left(-\sum_{j=s}^{n-1}-\log|\lambda_j|\right)\|z\|_Q
\geq e^{-D_s}\|z\|_Q.
$$

Pass to the limit in (8.10) to obtain positive definiteness and the first two bounds of (8.9). For $0<r<1$, integrating $1/x$ on $[r,1]$ gives $1-r\leq-\log r$, so $1-r^2\leq2(-\log r)$. Since each $\Phi_{s,j}$ is nonexpansive, $|b_{s,j}z|^2\leq Q(z)$. The remaining loss after index $n$ is therefore at most

$$
Q(z)\sum_{j=n}^\infty\delta_j\leq2D_nQ(z),
$$

which proves the prescribed-data error bound. In particular it tends to zero independently of any unknown trajectory limit. Formula (8.5) transfers this limiting norm through every undamped phase: the interaction vector is constant between events and $M$ preserves its norm. Every nonzero $z$ has a positive limit. An absolute linear functional on a real plane vanishes on a nonzero vector, whereas this positive-definite norm does not; hence a single covector cannot represent it. $\square$

## 追加锚（本行以下为增补区）

## 9. A disjoint-block criterion for infinite logarithmic loss

**Definition 9.1 (Prescribed loss blocks and their junctions).** Consider an infinite nonsingular tail starting at $s$, with $D_s=\infty$. Its block boundaries are the prescribed integers

$$
n_0=s,\qquad
n_{k+1}=\min\left\{n>n_k:
\sum_{j=n_k}^{n-1}-\log|\lambda_j|\geq\log2\right\}.
\tag{9.1}
$$

Each defining set is nonempty, since removing a finite number of finite terms leaves an infinite sum. Thus every block is finite, $n_k\to\infty$, and the blocks are disjoint consecutive portions of the tail. Define

$$
T_k=\Phi_{n_k,n_{k+1}},\qquad \mathfrak d_k=\det T_k,
\qquad R_k=T_k^*T_k,\qquad r_k=\operatorname{tr}R_k,
$$

$$
\sigma_k=\left(\frac{r_k+\sqrt{r_k^2-4\mathfrak d_k^2}}2\right)^{1/2},\qquad
\zeta_k^2=\frac{\mathfrak d_k^2}{\sigma_k^2},\qquad
\mu_k=\frac{\mathfrak d_k}{\sigma_k^2}.
\tag{9.2}
$$

All these are finite-block data. In particular $\mathfrak d_k=\prod_{j=n_k}^{n_{k+1}-1}\lambda_j\ne0$ and $|\mathfrak d_k|\leq1/2$. The two eigenvalues of $R_k$ are $\sigma_k^2\geq\zeta_k^2>0$. Let $E_k$ be the projection onto the larger eigenspace:

$$
E_k=\begin{cases}
(R_k-\zeta_k^2I)/(\sigma_k^2-\zeta_k^2),&\sigma_k^2>\zeta_k^2,\\
I,&\sigma_k^2=\zeta_k^2.
\end{cases}
$$

Choose $\bar f_k$ by projecting the first of the ordered pair $e,Je$ with nonzero projection, and normalizing that projection to unit $Q$-norm. Starting with $f_0=\bar f_0$, specify signs and unit output vectors recursively by

$$
g_k=\sigma_k^{-1}T_kf_k,\qquad
f_{k+1}=\chi(\langle\bar f_{k+1},g_k\rangle_Q)\bar f_{k+1},
\qquad \chi(x)=\begin{cases}1,&x\geq0,\\-1,&x<0.\end{cases}
$$

Set

$$
c_k=\langle f_{k+1},g_k\rangle_Q\geq0,\qquad
s_k=\langle f_{k+1},Jg_k\rangle_Q,\qquad
\eta_k=s_k^2=1-\langle\bar f_{k+1},g_k\rangle_Q^2.
\tag{9.3}
$$

The two prescribed nonnegative series are

$$
\mathcal B_s=\sum_{k=0}^\infty(1-\sigma_k),\qquad
\mathcal A_s=\sum_{k=0}^\infty\eta_k.
\tag{9.4}
$$

The loss-block criterion is $\mathcal B_s+\mathcal A_s=\infty$. It uses a contraction deficit from each disjoint finite block and the junction between that block's principal output line and the next block's principal input line. No block is the growing prefix from $s$ to $n_k$, except the first block. The boundaries use only $|\lambda_j|$, and neither series asks for the norm limit of growing prefix products or the fate of an initial vector.

**Theorem 9.2 (Infinite-loss tail classification and exact functional).** On the entire domain of Definition 9.1, every tail input decays if and only if

$$
\boxed{\quad\mathcal B_s+\mathcal A_s=\infty.\quad}
\tag{9.5}
$$

In this branch the stable space is $\mathbb R^2$ and every full chronological limiting norm is zero. In the complementary branch both series are finite; the stable space is one line and the exact full chronological limiting norm is $|\ell_s(z)|$, for the following nonzero prescribed-data functional.

Let $K$ be the least nonnegative integer such that $\sigma_k\geq3/4$ for every $k\geq K$, and put $\rho=8/9$. Define real rows, starting at $K$, by

$$
a_K=f_K^TG,\qquad b_K=(Jf_K)^TG,
$$

$$
a_{k+1}=c_ka_k+\mu_ks_kb_k,\qquad
b_{k+1}=-s_ka_k+\mu_kc_kb_k\quad(k\geq K).
\tag{9.6}
$$

The row series and scalar product

$$
\Lambda=a_K+\sum_{k=K}^\infty\big((c_k-1)a_k+\mu_ks_kb_k\big),
\qquad \gamma=\prod_{k=K}^\infty\sigma_k
\tag{9.7}
$$

converge, the row series absolutely and the product to a positive number. The functional is

$$
\boxed{\quad\ell_s(z)=\gamma\Lambda\Phi_{s,n_K}z.\quad}
\tag{9.8}
$$

For $n\geq K$, write $S_n=\sum_{k=n}^\infty(1-\sigma_k)$ and $E_n=\sum_{k=n}^\infty s_k^2$. In dual $Q$-norm the independently specified truncations satisfy

$$
\left\|\ell_s-
\left(\prod_{k=K}^{n-1}\sigma_k\right)a_n\Phi_{s,n_K}\right\|_{Q,*}
\leq S_n+E_n+\rho\sqrt{\frac{2E_n}{1-\rho^2}}.
\tag{9.9}
$$

Thus the limiting object has a prescribed-data error bound as well as exact original-model correspondence. There is no finite annihilation of a nonzero tail input in either branch.

*Proof.* All finite-dimensional constructions in Definition 9.1 take place in the original plane with its fixed inner product $Q$. To verify them, represent a $Q$-self-adjoint matrix in the orthonormal basis $e,Je$. The matrix of $R_k$ then has the real symmetric form $\begin{pmatrix}x&y\\y&z\end{pmatrix}$. Its characteristic discriminant is $(x-z)^2+4y^2\geq0$. Its quadratic form is $\|T_kw\|_Q^2>0$ for $w\ne0$, so both characteristic roots are positive. The ordinary two-by-two characteristic identity gives exactly the roots (9.2) and, when they differ, the self-adjoint idempotent $E_k$ displayed above. When they agree, $x=z$ and $y=0$, so $R_k=\sigma_k^2I$. This also verifies that $E_k$ is nonzero and that projecting one of $e,Je$ must succeed. This is the real two-dimensional spectral decomposition, consumed here only to decompose the actual finite blocks.

Nonexpansiveness of the factors gives $0<\sigma_k\leq1$. The orthonormal pair $f_k,Jf_k$ diagonalizes $R_k$, so $T_kf_k$ and $T_kJf_k$ are orthogonal, with lengths $\sigma_k,\zeta_k$. Orientation in the basis $e,Je$ gives

$$
T_kf_k=\sigma_kg_k,\qquad
T_kJf_k=\sigma_k\mu_kJg_k,
\qquad 0<|\mu_k|\leq1.
\tag{9.10}
$$

Indeed the coefficient of $Jg_k$ has modulus $\zeta_k$ and sign $\operatorname{sgn}(\det T_k)$, and $\zeta_k=|\mathfrak d_k|/\sigma_k$. Since $J$ is an orthogonal quarter-turn, (9.3) yields

$$
g_k=c_kf_{k+1}-s_kJf_{k+1},\qquad
Jg_k=s_kf_{k+1}+c_kJf_{k+1},\qquad c_k^2+s_k^2=1.
$$

Thus a block input with coordinates $(A,B)$ in $f_k,Jf_k$ has output coordinates

$$
\sigma_k(c_kA+\mu_ks_kB,\ -s_kA+\mu_kc_kB)
\tag{9.11}
$$

in $f_{k+1},Jf_{k+1}$. This is an exact finite identity for the prescribed original block, with its sign of determinant retained.

If $\mathcal B_s=\infty$, the original input at boundary $n_m$ has norm at most

$$
\left(\prod_{k=0}^{m-1}\sigma_k\right)\|z\|_Q
\leq\exp\left(-\sum_{k=0}^{m-1}(1-\sigma_k)\right)\|z\|_Q\longrightarrow0.
$$

Only disjoint-block submultiplicativity is used in this bound. Monotonicity of every intermediate event norm proves full-time decay. This establishes (9.5) in the first branch without any angle assumption.

Suppose henceforth $\mathcal B_s<\infty$. Then $\sigma_k\to1$, so the prescribed $K$ exists, and

$$
|\mu_k|\leq\frac{1/2}{(3/4)^2}=\rho=\frac89<1\quad(k\geq K).
\tag{9.12}
$$

Also the product in (9.7) is positive: on $[3/4,1]$, integration of $1/x$ gives $0\leq-\log x\leq(4/3)(1-x)$, so its logarithmic sum is finite. The finitely many blocks before $K$ are nonsingular. This is the only reduction to a uniform contraction bound, and it concerns the normalized disjoint blocks, not the original $\lambda_j$.

For an arbitrary input at boundary $n_K$, divide the actual input at boundary $n_k$ by $\prod_{i=K}^{k-1}\sigma_i$. Write the resulting vector as $A_kf_k+B_kJf_k$. By (9.11),

$$
A_{k+1}=c_kA_k+\mu_ks_kB_k,\qquad
B_{k+1}=-s_kA_k+\mu_kc_kB_k,
$$

$$
A_{k+1}^2+B_{k+1}^2
=A_k^2+B_k^2-(1-\mu_k^2)B_k^2.
\tag{9.13}
$$

These are exactly the scalar identities used in (7.10), with the block junctions supplying the angles. The proof uses these identities and the bound (9.12), rather than requiring the block angles to be integer multiples of $\theta$. In particular the normalized norms decrease to a limit $l\geq0$, and

$$
(1-\rho^2)\sum_{k=K}^\infty B_k^2\leq A_K^2+B_K^2.
\tag{9.14}
$$

If $l>0$, eventually $A_k^2\geq l^2/2$, since $B_k\to0$. The second recurrence gives

$$
s_k^2A_k^2=(\mu_kc_kB_k-B_{k+1})^2
\leq2\rho^2B_k^2+2B_{k+1}^2.
$$

It follows that $\sum s_k^2<\infty$. Thus $\mathcal A_s=\infty$ forces $l=0$ for every normalized input, and hence for every original input. Monotonicity between block boundaries again gives the full chronological conclusion.

It remains to prove the complementary branch, its exact functional and its nonzero value on some input. Suppose $\mathcal A_s<\infty$. The rows in (9.6) give $A_k=a_kw$ and $B_k=b_kw$ for normalized input $w$ at $n_K$. The maps in (9.13) are nonexpansive, so $\|a_k\|_{Q,*}\leq1$. Apply (9.14) to the two unit inputs $e,Je$ and add. The dual norm identity $\|f\|_{Q,*}^2=|fe|^2+|fJe|^2$ gives

$$
\sum_{k=K}^\infty\|b_k\|_{Q,*}^2\leq\frac2{1-\rho^2}.
\tag{9.15}
$$

Because $c_k\geq0$, one has $1-c_k=s_k^2/(1+c_k)\leq s_k^2$. Therefore, for every $n\geq K$,

$$
\begin{aligned}
\sum_{k=n}^\infty
\|(c_k-1)a_k+\mu_ks_kb_k\|_{Q,*}
&\leq E_n+\rho\sqrt{E_n}
\left(\sum_{k=n}^\infty\|b_k\|_{Q,*}^2\right)^{1/2}\\
&\leq E_n+\rho\sqrt{\frac{2E_n}{1-\rho^2}}.
\end{aligned}
\tag{9.16}
$$

This proves absolute convergence of (9.7), including the displayed tail bound. Its summands are $a_{k+1}-a_k$, so $a_k\to\Lambda$ in the row space. For every $w$, (9.14) gives $B_k\to0$, and hence (9.13) gives the exact normalized norm limit $|\Lambda w|$. In particular $\|\Lambda\|_{Q,*}\leq1$.

To show this row is nonzero, choose $N\geq K$ with

$$
\sum_{k=N}^\infty s_k^2<\frac{(1-\rho)^2}{4}.
$$

The finite normalized blocks from $K$ to $N$ are all invertible, so an input $w$ at $n_K$ can be chosen whose normalized vector at $n_N$ is $f_N$. Its subsequent coordinates satisfy $A_N=1,B_N=0$ and $|A_k|\leq1$. The second recurrence implies by induction

$$
|B_k|\leq\sum_{i=N}^{k-1}\rho^{k-1-i}|s_i|\quad(k>N).
$$

Weighted Cauchy--Schwarz gives

$$
|B_k|^2\leq\frac1{1-\rho}
\sum_{i=N}^{k-1}\rho^{k-1-i}s_i^2,
\qquad
\sum_{k=N}^\infty B_k^2\leq
\frac1{(1-\rho)^2}\sum_{i=N}^\infty s_i^2<\frac14.
$$

The second inequality follows by summing the nonnegative geometric weights, first over finite ranges and then taking their increasing limit. Telescoping (9.13) from this unit input yields $l^2\geq1-\sum_{k=N}^\infty B_k^2>3/4$. Consequently $\Lambda w\ne0$. This is the finite-prefix nonsingularity argument of (7.16)--(7.17), now applied to the explicitly normalized original blocks; it requires no uniform inverse.

The actual tail input $z$ reaches $n_K$ as $\Phi_{s,n_K}z$. Restoring the divided scalar factors gives (9.8) and the exact limiting norm. Both $\gamma>0$ and invertibility of $\Phi_{s,n_K}$ preserve nonzeroness of the functional. Its kernel is therefore a line. At every intermediate time the actual norm lies between successive block-boundary norms, so this is the limit along the entire chronological history, including unbounded gaps and arbitrary first-event time.

For completeness, $\gamma_n=\prod_{k=K}^{n-1}\sigma_k$ satisfies $0\leq\gamma_n-\gamma\leq S_n$: finite products of $1-r_i$ are at least $1-\sum r_i$, and passage to the limit gives this bound. Combine it with (9.16), $\|a_n\|_{Q,*}\leq1$, $\gamma\leq1$ and nonexpansiveness of $\Phi_{s,n_K}$ to obtain (9.9). Thus neither the scalar product nor the functional is an unspecified limiting remainder. All tail factors are nonsingular, so Theorem 8.2 excludes finite annihilation of a nonzero input. This completes both directions of (9.5) and all limiting-space assertions. $\square$

## 追加锚（本行以下为增补区）

## 10. Singular events and every finite-prefix composition

**Theorem 10.1 (Infinitely many singular events).** Suppose the event list is infinite and its singular event indices, in increasing order, are $i_0<i_1<\cdots$. Define the prescribed nonzero row and finite-block coefficients

$$
\beta=e_{i_0}^TG\Phi_{0,i_0},\qquad
\kappa_k=\left\langle e_{i_{k+1}},
\Phi_{i_k+1,i_{k+1}}e_{i_k}\right\rangle_Q.
\tag{10.1}
$$

Every $|\kappa_k|\leq1$. If any $\kappa_k=0$, every initial state is annihilated by time $t_{i_{k+1}}+1$. Otherwise put

$$
C=\sum_{k=0}^\infty-\log|\kappa_k|\in[0,\infty],\qquad
p=e^{-C},\quad e^{-\infty}=0.
\tag{10.2}
$$

The exact full chronological limit and stable space are

$$
\lim_{t\to\infty}\|u_t\|_Q=p|\beta u_0|,\qquad
S_{\varepsilon,\boldsymbol\alpha}=
\begin{cases}
\ker\beta,&C<\infty,\\
\mathbb R^2,&C=\infty.
\end{cases}
\tag{10.3}
$$

In the case of a zero $\kappa_k$ the limit is zero and the stable space is also $\mathbb R^2$. The row $\beta$ has one-dimensional kernel. A vector in that kernel is killed at the first singular event. If all $\kappa_k$ are nonzero, every vector outside that kernel remains nonzero at every finite time; when $C=\infty$, these surviving vectors decay only asymptotically. These alternatives are entirely prescribed finite-block and scalar-series conditions.

*Proof.* Every factor preceding $i_0$ is nonsingular, so $\Phi_{0,i_0}$ is invertible. Since $e_{i_0}^TG\ne0$, the row $\beta$ is nonzero. Immediately after the first singular event the interaction vector is $e_{i_0}\beta u_0$. Each intervening factor up to the next singular event is one of the factors in the finite map $\Phi_{i_k+1,i_{k+1}}$; the singular event itself is projection onto $\mathbb Re_{i_{k+1}}$. Induction therefore gives the exact vectors immediately after the successive singular events:

$$
F_{i_m+1}u_0=e_{i_m}(\beta u_0)
\prod_{k=0}^{m-1}\kappa_k\quad(m\geq0).
\tag{10.4}
$$

Nonexpansiveness of the intervening finite map and Cauchy--Schwarz imply $|\kappa_k|\leq1$. A zero coefficient kills the whole already rank-one image. If all are nonzero, the absolute finite products in (10.4) converge to $e^{-C}$, simply by taking their logarithms. At the singular-event subsequence the norms thus have exactly the limit (10.3). All chronological norms are nonincreasing by (8.7), and this subsequence tends to infinite time, so the same limit holds at every time.

For $\beta u_0=0$, (10.4) already vanishes at $m=0$. For $\beta u_0\ne0$ and all $\kappa_k\ne0$, its vectors never vanish. Nonsingular intervening factors cannot kill them either. Before $i_0$ all factors are invertible. This proves every finite-annihilation and survival assertion and distinguishes an infinite logarithmic sum from a zero finite factor. $\square$

**Theorem 10.2 (Eventually nonsingular histories and exact prefix transport).** Suppose an infinite event list has only finitely many singular events. Take $s=0$ if there are none, and otherwise take $s$ to be one plus the last singular event index. Put $F=\Phi_{0,s}$. Apply the following alternatives to the wholly nonsingular tail beginning at $s$.

1. If $D_s<\infty$, its prescribed matrix $H_s$ from Theorem 8.3 gives

$$
\lim_{t\to\infty}\|u_t\|_Q
=\sqrt{u_0^TF^TH_sFu_0},\qquad
S_{\varepsilon,\boldsymbol\alpha}=\ker F.
\tag{10.5}
$$

The dimension is $2-\operatorname{rank}F$. Every nonzero prefix image persists with positive limiting norm.

2. If $D_s=\infty$ and $\mathcal B_s+\mathcal A_s=\infty$, every limiting norm is zero and $S_{\varepsilon,\boldsymbol\alpha}=\mathbb R^2$.

3. If $D_s=\infty$ and $\mathcal B_s+\mathcal A_s<\infty$, let $\ell_s$ be (9.8) and form the prescribed row $f=\ell_sF$. Then

$$
\lim_{t\to\infty}\|u_t\|_Q=|fu_0|,\qquad
S_{\varepsilon,\boldsymbol\alpha}=
\begin{cases}
\ker f,&f\ne0,\\
\mathbb R^2,&f=0.
\end{cases}
\tag{10.6}
$$

In every alternative an individual state is annihilated in finite time exactly when $Fu_0=0$. Thus $F=0$ means finite all-state annihilation. If $F\ne0$ and $f=0$ in alternative 3, the nonzero prefix image is asymptotically erased even though the tail functional is nonzero. The same distinction applies to alternative 2. If $F$ has rank one and $f\ne0$, then $\ker f=\ker F$; if $F$ has rank two, $f\ne0$ and its kernel is a line. These statements decide all stable-space dimensions, including the possible zero composed functional.

*Proof.* The exact interaction input at index $s$ is $Fu_0$, by (8.4). All later event factors are nonsingular. Consequently a zero in the tail is equivalent to having reached it with zero input, and a vector killed anywhere in the prefix also has $Fu_0=0$. This proves the finite-annihilation assertion without inverting a singular factor.

If $D_s<\infty$, apply Theorem 8.3 to $z=Fu_0$. Positive definiteness of $H_s$ makes its limiting quadratic form zero precisely on $\ker F$, proving (10.5) and its dimension. In particular a rank-one prefix image is not erased unless it was zero. In the second alternative Theorem 9.2 gives zero for every tail input. In the third it gives exactly the composition (10.6). The nonzero functional $\ell_s$ vanishes on a line, but a rank-one image of $F$ may be precisely that line, giving $f=0$ with $F\ne0$. If $F$ is invertible this cannot happen. If $\operatorname{rank}F=1$ and $\ell_s$ is nonzero on its image, both $f$ and $F$ vanish exactly on the same kernel. These facts prove all assertions in the original coordinate plane and at the original initial-state scale. $\square$

**Corollary 10.3 (Whole-history decision and angle arithmetic).** For every prescribed history in Definition 8.1 the following disjoint cases give the complete stable space and exact full-time norm limit: a finite event list is Theorem 8.2; an infinite list with infinitely many singular indices is Theorem 10.1; an infinite list with finitely many singular indices is Theorem 10.2. In particular universal decay is decided as follows:

$$
\begin{array}{c|l}
\text{history}&\text{necessary and sufficient condition for universal decay}\\ \hline
r<\infty&F_r=0\\
\text{infinitely many singular indices}&
\text{some }\kappa_k=0\text{, or all nonzero and }C=\infty\\
\text{eventually nonsingular, }D_s<\infty&F=0\\
\text{eventually nonsingular, }D_s=\infty&
\mathcal B_s+\mathcal A_s=\infty\text{, or }
[\mathcal B_s+\mathcal A_s<\infty\text{ and }\ell_sF=0].
\end{array}
\tag{10.7}
$$

The stable-space dimensions in these cases are respectively the finite rank-nullity value, one or two, the rank-nullity value for $F$, and one or two. The stable space is zero-dimensional exactly in the finite nonsingular case or the finite-$D_s$ case with rank-two $F$. Every state outside the specified stable space has strictly positive limiting $Q$-norm. Finite annihilation remains the separate finite condition in Theorem 8.2.

All block and series data are prescribed independently of the initial state. Convergent series determine the functionals and their kernels exactly; no uniform finite-time decision procedure for arbitrary real infinite histories is asserted. The cases allow arbitrary signs, arbitrarily small nonzero factors, approaches to either endpoint, every first-event time and all positive integer gaps. They impose no arithmetic restriction on the original angle.

*Proof.* Every event list has exactly one of the three listed types. The corresponding theorems give (10.7), the exact limits and the stable subspaces, so rank-nullity and the kernels of the nonzero rows give the asserted dimensions. In particular, if an infinite list is wholly nonsingular and has infinite $D_s$, its stable space is either the whole plane or a line by Theorem 9.2, never $\{0\}$. Any singular prefix has rank at most one, so cannot produce another zero-dimensional case. The zero and nonzero composed rows in (10.6) are both included.

For the arithmetic boundary, if $\theta/(2\pi)$ is rational, the possible event lines $\mathbb RM^{-t_j}e$ form a finite family. If it is irrational, $d\theta$ is neither an integer multiple of $\pi$ nor an odd multiple of $\pi/2$ for any positive integer $d$, since either equation would force the ratio to be rational. These are precisely the arithmetic observations of Corollary 6.3. None is needed to form the finite products, loss blocks, their principal lines or the singular coefficients (10.1). Consequently both arithmetic types, including exact resonances and orthogonal gaps whenever available, are already covered. Arbitrarily long blocks in (9.1) remain finite by divergence of their prescribed logarithmic loss; no compactness or uniform inverse assumption on the original event factors has been introduced. $\square$

**Proposition 10.4 (A nonzero tail functional erased by a surviving prefix image).** There is an actual original history with just one singular event, a nonzero rank-one prefix image, and a nonzero infinite-loss tail functional whose composition with that prefix is zero. The entire history decays for every input, but no finite time annihilates the whole plane.

Take $(a,b,c)=(2,1,3)$, events $t_j=j$, and

$$
\lambda_0=0,\qquad \lambda_{2k+1}=\frac12,\qquad
\lambda_{2k+2}=1-2^{-k-3},\qquad
\alpha_j=\frac{1+\lambda_j}{4-2\lambda_j}\quad(k\geq0).
\tag{10.8}
$$

*Proof.* For this triple the literal transfer is $M=\begin{pmatrix}-1&4/3\\-3/2&1\end{pmatrix}$, the angle is $\pi/2$, and the unit vectors $e=(2,3)^T/\sqrt6$, $q=(2,0)^T/\sqrt6$ obey $Me=q$, $Mq=-e$ and $\langle e,q\rangle_Q=0$. Hence the interaction factors at even indices fix $e$ and those at odd indices fix $q$. The first factor is exactly $F_1=P_0=ee^TG$, which has a nonzero rank-one image. The tail starting at $s=1$ is nonsingular and has $D_1=\infty$, since every odd index contributes $\log2$.

For an arbitrary tail input $z=xe+yq$, the odd tail factors multiply its $e$ coordinate by $1/2$, and the even tail factors multiply its $q$ coordinate by $1-2^{-k-3}$. Therefore its exact limiting norm is $p|y|$, where $p=\prod_{k\geq0}(1-2^{-k-3})\geq3/4$, by the finite-product inequality used above. One may take $\ell_1=pq^TG\ne0$, while $\ell_1F_1=0$. For an actual initial input $u_0$, write $\beta=e^TGu_0$. After $n\geq1$ events its interaction vector is

$$
F_nu_0=2^{-\#\{j<n:j\text{ odd}\}}\beta e.
$$

It tends to zero for every $u_0$. When $\beta\ne0$ it remains nonzero at every finite $n$, and when $\beta=0$ it is killed at the first event. In particular $F_n$ is never the zero map at a finite time. Identity (8.5) transfers these exact facts to the full original chronological trajectory. This realizes the zero-composition alternative in (10.6) without replacing asymptotic erasure by finite annihilation. $\square$

## 追加锚（本行以下为增补区）

## 11. Weighted sufficiency and actual original-matrix consumers

**Theorem 11.1 (Adjacent-minimum weighted sufficiency).** For every infinite original history in Definition 8.1, including singular events, define

$$
W=\sum_{j=0}^\infty
\min(\delta_j,\delta_{j+1})\sin^2(d_j\theta).
\tag{11.1}
$$

If $W=\infty$, every original initial state tends to zero. No uniform bound on $|\lambda_j|$, inverse, sign, angle or gaps is required. This condition is sufficient and is not necessary.

*Proof.* Use the prescribed frames (7.9) and the exact recurrences (7.10), whose algebra applies to every $\lambda_j\in(-1,1)$. For an arbitrary actual trajectory put

$$
L_j=\delta_jB_j^2,\qquad w_j=\min(\delta_j,\delta_{j+1}).
$$

The loss identity gives $\sum_jL_j\leq Q(u_0)$. The second coordinate recurrence yields

$$
s_j^2A_j^2=(\lambda_jc_jB_j-B_{j+1})^2
\leq2\lambda_j^2c_j^2B_j^2+2B_{j+1}^2.
$$

Multiplying by $w_j$ and using both $w_j\leq\delta_j$ and $w_j\leq\delta_{j+1}$ gives

$$
w_js_j^2A_j^2\leq2L_j+2L_{j+1}.
$$

The other coordinate has $w_js_j^2B_j^2\leq L_j$. Hence

$$
w_js_j^2\|v_j\|_Q^2\leq3L_j+2L_{j+1}.
\tag{11.2}
$$

The actual norms decrease to some $l\geq0$. If $l>0$, summing (11.2) would give $l^2W\leq5Q(u_0)<\infty$, a contradiction. Thus $l=0$, and (8.5) gives decay at every chronological time, with no restriction on $\|u_0\|_Q$. Zero factors cause no difficulty in these inequalities. Nonnecessity follows from Propositions 11.3 and 11.4 below. $\square$

**Proposition 11.2 (Refutation of the asymmetric weight).** The proposed sufficient weight

$$
\omega_j=\begin{cases}
\min\left(\delta_{j+1},
\dfrac{\delta_j}{\lambda_j^2\cos^2(d_j\theta)}\right),
&\lambda_j\cos(d_j\theta)\ne0,\\
\delta_{j+1},&\lambda_j\cos(d_j\theta)=0
\end{cases}
\tag{11.3}
$$

is not sufficient for universal decay. There is an actual wholly nonsingular original history for which $\sum_j\omega_j\sin^2(d_j\theta)=\infty$ and a nonzero state has strictly positive full-time limiting $Q$-norm.

Take the positive triple $(a,b,c)=(2,1,3)$, an event at every time $t_j=j$, and prescribe

$$
r_k=2^{-k-3},\qquad
\lambda_{2k}=1-r_k,\qquad \lambda_{2k+1}=\frac12,\qquad
\alpha_j=\frac{1+\lambda_j}{4-2\lambda_j}.
\tag{11.4}
$$

Then the exact limit for $u_0=xe+yq$ is

$$
\lim_{t\to\infty}\|u_t\|_Q=p|y|,\qquad
p=\prod_{k=0}^\infty(1-r_k)\geq\frac34,
\tag{11.5}
$$

where $e=(2,3)^T/\sqrt6$ and $q=(2,0)^T/\sqrt6$. In particular the prescribed state $u_0=q$ has limit at least $3/4$.

*Proof.* Direct specialization of the original matrices gives

$$
A=\begin{pmatrix}1&0\\-6&4\end{pmatrix},\quad
B=\begin{pmatrix}-1&4/3\\0&-4\end{pmatrix},\quad
M=\begin{pmatrix}-1&4/3\\-3/2&1\end{pmatrix},\quad
Q(x,y)=\frac{x^2}{2}+(y-x)^2+\frac{y^2}{3}.
\tag{11.6}
$$

Here $2ac/((a+b)(b+c))-1=0$, so the original angle is $\theta=\pi/2$, $M^2=-I$, and $J=M$. Calculation gives $Q(e)=Q(q)=1$, $\langle e,q\rangle_Q=0$, $Me=q$ and $Mq=-e$. Thus the actual event lines $\mathbb RM^{-j}e$ are alternately $\mathbb Re$ and $\mathbb Rq$. In interaction coordinates $K_{2k}$ fixes $e$ and multiplies $q$ by $\lambda_{2k}$, whereas $K_{2k+1}$ fixes $q$ and multiplies $e$ by $1/2$. These are the factors of the literal $N_{\alpha_j}=M(P+\lambda_j(I-P))$, with no replacement of the original maps. Equation (8.1) is exactly the last formula in (11.4), so all parameters are interior and every event determinant is nonzero.

For $u_0=xe+yq$, the exact interaction vector after $n$ events is

$$
F_nu_0=
2^{-\#\{j<n:j\text{ odd}\}}xe+
\left(\prod_{\{k:2k<n\}}(1-r_k)\right)yq.
\tag{11.7}
$$

Its first coefficient tends to zero. The second coefficient tends to the product $p$. Finite products satisfy $\prod(1-r_k)\geq1-\sum r_k$, by induction from $(1-x)(1-y)\geq1-x-y$. As $\sum_{k\geq0}r_k=1/4$, this gives $p\geq3/4$. Formula (8.5) now proves (11.5) for the entire chronological trajectory, not merely a selected subsequence.

Every actual gap is one, so $\cos(d_j\theta)=0$ and $\sin^2(d_j\theta)=1$. The second branch of the stated candidate (11.3) therefore gives, for every $k$,

$$
\omega_{2k}\sin^2(d_{2k}\theta)=\delta_{2k+1}=\frac34.
$$

Its series diverges, despite (11.5). Both types of event factor remain nonsingular; the zero cosine is a legal orthogonal gap, not a singular transfer. For comparison the correct series is finite:

$$
W\leq2\sum_{k=0}^\infty\delta_{2k}
=2\sum_{k=0}^\infty(2r_k-r_k^2)<4\sum_{k=0}^\infty r_k=1.
$$

The example isolates the failure of assigning the next large loss to a component that the next event fixes. It refutes the full proposed weight, including its explicitly stated zero-cosine endpoint. $\square$

**Proposition 11.3 (Wholly nonsingular endpoint approach with $W<\infty$ and universal decay).** In the same actual original system $(a,b,c)=(2,1,3)$, with $t_j=j$, prescribe before choosing any initial vector

$$
\lambda_{3k}=\frac{k+1}{k+2},\qquad
\lambda_{3k+1}=\lambda_{3k+2}=1-2^{-k-4},\qquad
\alpha_j=\frac{1+\lambda_j}{4-2\lambda_j}\quad(k\geq0).
\tag{11.8}
$$

Then $0<\lambda_j<1$, $\alpha_j\to1$, $W<1$, and every original initial state tends to zero. No nonzero initial state is annihilated at any finite time. Thus (11.1) is genuinely nonnecessary even for wholly nonsingular endpoint-approaching variable histories.

*Proof.* The inverse parameter correspondence (8.1) gives actual $0<\alpha_j<1$ at each event, and $\lambda_j\to1$ along all three residue classes implies $\alpha_j\to1$. The geometry and matrices are exactly (11.6). For $u_0=xe+yq$ the interaction vector is

$$
F_nu_0=
\left(\prod_{\substack{0\leq j<n\\j\text{ odd}}}\lambda_j\right)xe+
\left(\prod_{\substack{0\leq j<n\\j\text{ even}}}\lambda_j\right)yq.
\tag{11.9}
$$

This follows because each even event contracts only the $q$ coordinate and each odd event only the $e$ coordinate, exactly as in (11.7). Among the indices $3k$, parity agrees with the parity of $k$. The sums

$$
\sum_{\substack{k\geq0\\k\text{ even}}}(1-\lambda_{3k})
=\sum_{r=0}^\infty\frac1{2r+2}=\infty,\qquad
\sum_{\substack{k\geq0\\k\text{ odd}}}(1-\lambda_{3k})
=\sum_{r=0}^\infty\frac1{2r+3}=\infty
$$

both diverge. For example the second is at least one half of $\sum_{r\geq0}1/(r+2)$, and grouping the latter in consecutive dyadic ranges gives a positive lower bound on each group. Since $-\log\lambda\geq1-\lambda$, both parity products in (11.9) tend to zero. It follows that $\|F_nu_0\|_Q\to0$ for every $x,y$, and (8.5) proves actual full-time decay at every initial scale.

To bound $W$, call the indices $3k+1,3k+2$ weak indices. Every consecutive pair of indices contains a weak index, and its minimum loss is at most the sum of the losses of its weak members. Each weak index belongs to at most two such pairs. As every gap has squared sine one,

$$
W\leq2\sum_{j\text{ weak}}\delta_j
=4\sum_{k=0}^\infty\left[1-(1-2^{-k-4})^2\right]
<8\sum_{k=0}^\infty2^{-k-4}=1.
$$

Every finite event product is invertible since all its $\lambda_j$ are positive. The original $M$ is also invertible, so a nonzero input never becomes zero at a finite time. The decay just proved is therefore asymptotic and is not an annihilation artifact. The history and parameters depend on neither $x$ nor $y$. $\square$

**Proposition 11.4 (Singular-history nonnecessity).** In the same system prescribe

$$
t_0=0,\qquad t_j=2j-1\quad(j\geq1),\qquad
\alpha_j=\frac14\quad(j\geq0).
\tag{11.10}
$$

Then every initial state is zero from time $2$ onward, while the infinite series (11.1) equals $1$.

*Proof.* The singular parameter is $b/(a+2b)=1/4$, hence every $\lambda_j=0$ and every $\delta_j=1$. The literal first Token-1 row and the inverse of $A$ in (11.6) give

$$
B_{1/4}=\begin{pmatrix}0&2/3\\0&-4\end{pmatrix},\qquad
N_{1/4}=A^{-1}B_{1/4}
=\begin{pmatrix}0&2/3\\0&0\end{pmatrix},\qquad N_{1/4}^2=0.
$$

The first two events are consecutive at times $0,1$, so every actual state is annihilated by time $2$, and every later transfer preserves zero. This is also the orthogonal singular-projection mechanism of Theorem 6.2, used here as an original-history consumer. The first gap is $d_0=1$ and every later gap is $2$. Since $\theta=\pi/2$, their squared sines are respectively $1$ and $0$, giving $W=1$. This supplies singular nonnecessity with infinitely many events and infinitely many singular factors. $\square$

## 追加锚（本行以下为增补区）
## 12. An evaluated boundary determinant for every original chain

**Definition 12.1 (Fixed transfer, normalized observation and source correspondence).** Let $m\geq1$, $v_1,\ldots,v_{m+1}>0$ and $0<\alpha<1$. Throughout Sections 12–15 set

$$
T=A^{-1}B_\alpha=N_\alpha,\qquad U=A^{-1}B=M,
\qquad z_0=z_{m+1}=0,
$$

with exactly the real matrices of Definition 1.1, acting also on $\mathbb C^m$. Thus $T$ is one fixed map at every iteration. Define

$$
\begin{gathered}
s_i=v_i+v_{i+1},\qquad g_i=\frac{s_i}{v_iv_{i+1}},\qquad
G_{ii}=g_i,\quad G_{i,i+1}=G_{i+1,i}=-\frac1{v_{i+1}},\quad
G_{ij}=0\quad(|i-j|>1),\\
\langle x,y\rangle_Q=x^*Gy,\qquad
Q(z)=z^*Gz=\sum_{j=1}^{m+1}\frac{|z_j-z_{j-1}|^2}{v_j},\qquad
f_i=\frac{e_i}{\sqrt{g_i}},\qquad
\ell(z)=\langle f_1,z\rangle_Q
=\sqrt{g_1}\left(z_1-\frac{v_1}{s_1}z_2\right),\\
\theta_\alpha=\frac{\alpha s_1}{v_2+\alpha v_1},\qquad
q=2\theta_\alpha-1
=\frac{\alpha(v_1+2v_2)-v_2}{v_2+\alpha v_1},\qquad
\sigma=1-q^2
=\frac{4\alpha(1-\alpha)v_2s_1}{(v_2+\alpha v_1)^2}>0.
\end{gathered}
\tag{12.1}
$$

Here $e_i$ is the original coordinate vector; $z_2=0$ for $m=1$. A star on a vector or an ordinary matrix means conjugate transpose. For an endomorphism of the state space, $R^{\dagger}=G^{-1}R^*G$ denotes its $Q$-adjoint. Observation output spaces have the standard Hermitian inner product, so $\ell^{\dagger}a=af_1$ and $\mathcal O_T^{\dagger}=G^{-1}\mathcal O_T^*$. The form is positive definite, since its defining sum can vanish only when all consecutive differences, and hence all coordinates, vanish. Put

$$
\mathcal O_Tz=(\ell(z),\ell(Tz),\ldots,\ell(T^{m-1}z))^T,
\qquad H_T=\mathcal O_T^{\dagger}\mathcal O_T
=\sum_{k=0}^{m-1}(T^{\dagger})^k f_1\ell T^k.
\tag{12.2}
$$

The determinant of $H_T$ is the normalized boundary-observation Gram determinant: in any $Q$-orthonormal basis it is the usual determinant of $\mathcal O_T^*\mathcal O_T$. Equivalently it is $\det(\mathcal O_T^*\mathcal O_T)/\det G$ when the observation matrix is written in the original coordinates.

The original hypotheses and rows are those of [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, Section III and Section IV.A, page 3, and Section IV.B.1, page 4](https://arxiv.org/html/2608.27085v1#S4). Their $u=x-x^*$ is $z$ here, their $M_\alpha$ is $T$, their $M$ is $U$, and their endpoint values after centering are zero. The collision interpretation presupposes the alternating, catch-up-free rotational regime. No entry time into that regime is a hypothesis or conclusion of the estimates below.

For the complete [finite-path source](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean), [damped-sweep source](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), and their [finite-path](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs) and [damped-sweep](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs) expositions, pair $i$ and velocity $v_j$ have indices $i-1$ and $j-1$. The definitions `A`, `B`, `Balpha`, `Malpha` are the literal $A,B,B_\alpha,T$; the private weight `theta` is $\theta_\alpha$. The form, local reflection identity, first-event loss and factorization used below are the intermediates `local_energy_decomposition`, `Q_dampedEvent_loss`, `Q_event`, `Q_phase`, `sweep_stacked` and `source_factorization`. The rigidity and boundary-zero implications are `harmonic_dirichlet_zero` and `boundary_zero_observability`. The fixed-map qualitative conclusion is `TokenDampedSweepContraction.result`, with its power implication `real_mulVec_powers_tendsto_zero`; the [source note](../../../Library/Dynamics/wallner2026passbucket.md) and [fixed-map statement](../../../Problems/wallner-krupke-schmidt-fekete-2026-token-spectral-contraction.md) specify the same correspondence. These results are supporting conclusions, rather than additional claims about variable histories.

The homogeneous qualitative antecedent is R. A. Mensing, *Ansätze für Bewegungsplanungs-Probleme mit dem Ziel der verketteten Arbeitsteilung*, bachelor's thesis (2021), credited in [v1, Section II and reference [11]](https://arxiv.org/html/2608.27085v1#bib.bib11). Its full-text quantitative coverage is unknown and no quantitative result from it is used. No non-overlap or publication-priority assertion concerning that thesis is part of these statements.

**Theorem 12.2 (Explicit velocity product and damping independence).** For every chain and parameter in Definition 12.1, put

$$
\boxed{\displaystyle
\mathcal D(v)=
\frac{\left(\sum_{j=1}^{m+1}v_j\right)\prod_{j=2}^{m}v_j}
     {\prod_{i=1}^{m}(v_i+v_{i+1})}
\prod_{i=1}^{m-1}
\left(\frac{4v_iv_{i+2}}
{(v_i+v_{i+1})(v_{i+1}+v_{i+2})}\right)^{m-i}.}
\tag{12.3}
$$

Every empty product is one. Then

$$
\det H_T=\det H_U=\mathcal D(v),\qquad 0<\mathcal D(v)\leq1.
\tag{12.4}
$$

In particular this determinant is independent of $\alpha$, including the singular interior parameter

$$
\alpha_* =\frac{v_2}{v_1+2v_2},\qquad q=0.
\tag{12.5}
$$

For $m=1$ it is exactly one. The determinant identity also holds for the endpoint extensions $\alpha=0,1$ of the original rows.

*Proof.* We first use the local reflection identities cited in Definition 12.1 in their present coordinates. Set $P_i z=f_i\langle f_i,z\rangle_Q$ and $E_i=I-2P_i$. Since $\langle f_i,f_i\rangle_Q=1$, $P_i$ is an orthogonal projection for $Q$. Directly,

$$
(E_i z)_i=-z_i+\frac{2v_{i+1}}{s_i}z_{i-1}
                         +\frac{2v_i}{s_i}z_{i+1},
\qquad (E_i z)_j=z_j\quad(j\ne i).
\tag{12.6}
$$

The local energy decomposition cited in Definition 12.1 has center $c=(v_{i+1}z_{i-1}+v_i z_{i+1})/s_i$ and coefficient $g_i$ on $|z_i-c|^2$. Consequently it is exactly this $Q$-reflection: $E_i^2=I$ and $Q(E_i z)=Q(z)$, also for complex inputs. Distinct same-parity normals are orthogonal, so same-parity reflections commute. Write

$$
F=\prod_{i\ {m odd}}E_i,\qquad J_0=\prod_{i\ {m even}}E_i.
$$

The product over an empty parity class is $I$. The original odd rows give the first phase $Fz$; the original even rows then give the second phase $J_0Fz$. Invertibility of $A$ therefore identifies $U=J_0F$. For the first damped event the original row is precisely $D_1=(1-\theta_\alpha)I+\theta_\alpha E_1$. Indeed its first diagonal coefficient is $1-2\theta_\alpha=-q$ and its right coefficient is $2\theta_\alpha v_1/s_1=2\alpha v_1/(v_2+\alpha v_1)$. Every other odd row and every even relation is unchanged. Since the remaining odd reflections commute with $E_1$ and with $D_1$,

$$
\begin{gathered}
U^{\dagger}U=I,\qquad
T=UK_q,\qquad K_q=E_1D_1=I-(1-q)P_1,\\
Q(Tz)=Q(z)-(1-q^2)|\ell(z)|^2.
\end{gathered}
\tag{12.7}
$$

This is the source factorization and loss, expressed with a unit normal. It uses no inverse of $T$ or of $K_q$. Positivity of the original parameters gives $0<\theta_\alpha<1$ because the denominator exceeds the numerator by $v_2(1-\alpha)>0$. Thus $-1<q<1$ and every $T$ is nonexpansive for $Q$. At $\alpha=0,1$, $q=-1,1$ respectively; the same factorization is valid and both endpoint transfers are $Q$-isometries.

We next evaluate the undamped observation determinant. The Gram matrix $C$ of $f_1,\ldots,f_m$ has diagonal one and adjacent entries $-c_i$, where

$$
c_i=\frac{1/v_{i+1}}{\sqrt{g_i g_{i+1}}}
=\sqrt{\frac{v_iv_{i+2}}{s_i s_{i+1}}}>0
\qquad(1\leq i<m).
\tag{12.8}
$$

For adjacent indices the reflection rule gives $E_i f_j=f_j+2c_{\min(i,j)}f_i$; it gives $E_i f_i=-f_i$ and fixes every other $f_j$. In the ordered list

$$
w_1=f_1,\quad w_{2r}=U^r f_1\ (r\geq1),\quad
w_{2r+1}=U^{-r}f_1\ (r\geq1),\qquad 1\leq j\leq m,
\tag{12.9}
$$

$w_j$ lies in $\operatorname{span}(f_1,\ldots,f_j)$, and the absolute value of its $f_j$ coefficient is

$$
a_j=2^{j-1}\prod_{i=1}^{j-1}c_i.
\tag{12.10}
$$

Here is an explicit induction that accounts for both parities. First $Uf_1=-J_0f_1=-f_1-2c_1f_2$ when $m\geq2$. On a normal with even index $i$, applying $U=J_0F$ can reach index $i+2$ only through $f_i\mapsto2c_i f_{i+1}\mapsto4c_i c_{i+1}f_{i+2}$. On a normal with odd index $i$, $U$ reaches at most $i+1$. Therefore, for an input supported through an even index $i$, only its last coefficient contributes at index $i+2$, by the multiplier $4c_i c_{i+1}$. This proves (12.10) on all even indices from the displayed base. For $U^{-1}=FJ_0$, an odd index $i$ reaches $i+2$ by the same multiplier $4c_i c_{i+1}$, whereas an even index reaches at most $i+1$. Starting with $f_1$, this proves the odd-index assertion. Every such induction step is used only when its terminal index is at most $m$; no nonexistent endpoint normal is introduced.

The Laurent order (12.9) is the cyclic unitary order $1,z,z^{-1},z^2,z^{-2},\ldots$ used in [Simon, *CMV matrices: Five years after*, arXiv:math/0603093v1, Section 2, (2.15) and (2.33)–(2.34)](https://arxiv.org/pdf/math/0603093v1). Here unitarity is (12.7), and cyclicity follows from the nonzero coefficients (12.10). The coefficients in this calculation are the explicit overlaps (12.8) of the original chain; no identification of original coordinates with an unspecified CMV matrix is required.

Triangularity in (12.9)–(12.10) now gives

$$
\det\big(\langle w_i,w_j\rangle_Q\big)_{i,j=1}^m
=\det C\prod_{j=1}^m a_j^2
=\det C\prod_{i=1}^{m-1}(4c_i^2)^{m-i}.
\tag{12.11}
$$

The exponents of $U$ in (12.9) form the consecutive integer interval
$-\lfloor(m-1)/2\rfloor,\ldots,\lfloor m/2\rfloor$, in a different order. Applying the common isometry $U^{\lfloor m/2\rfloor}$ to $f_1,U^{-1}f_1,\ldots,U^{-(m-1)}f_1$ gives exactly that interval. A common isometry and a simultaneous permutation preserve a Gram determinant. The vectors $U^{-k}f_1$ represent the rows $\ell U^k$, so (12.11) is $\det H_U$.

It remains to evaluate $\det C$. Let $\Delta_k$ be the leading $k\times k$ determinant of $G$ and let $S_k=\sum_{j=1}^k v_j$. Expanding the last row of this tridiagonal determinant gives

$$
\Delta_0=1,\qquad \Delta_1=\frac{v_1+v_2}{v_1v_2},\qquad
\Delta_k=g_k\Delta_{k-1}-\frac1{v_k^2}\Delta_{k-2}
=\frac{S_{k+1}}{\prod_{j=1}^{k+1}v_j}.
\tag{12.12}
$$

For the final equality induction substitutes the formulas for $k-1,k-2$; the numerator reduces by
$(v_k+v_{k+1})S_k-v_{k+1}S_{k-1}=v_kS_{k+1}$.
Consequently

$$
\det C=\frac{\det G}{\prod_{i=1}^m g_i}
=\frac{S_{m+1}\prod_{j=2}^{m}v_j}{\prod_{i=1}^m s_i}.
\tag{12.13}
$$

Combining (12.8), (12.11) and (12.13) proves exactly the finite velocity product (12.3), with no remaining determinant or recurrence in that expression.

Finally, the rank-one difference $T-U=-(1-q)Uf_1\ell$ gives, for $k\geq1$, the finite identity

$$
T^k=U^k-(1-q)\sum_{j=0}^{k-1}U^{k-j}f_1\ell T^j.
\tag{12.14}
$$

It follows either by telescoping $T^k-U^k$ or by induction using $T=U-(1-q)Uf_1\ell$. Applying $\ell$ shows that the $k$th damped observation row is the $k$th undamped row minus a linear combination of earlier damped rows. Successive substitution makes the change from $\mathcal O_U$ to $\mathcal O_T$ lower triangular with diagonal entries one. Its determinant is one. Taking the squared absolute determinant in orthonormal coordinates proves $\det H_T=\det H_U$. This argument works for every real $q$, so in particular at zero and at both endpoints. Every factor in (12.3) is positive. The undamped observation rows have norm one, because $U$ is an isometry and $f_1$ is a unit vector. Hadamard's inequality therefore gives $\det H_U\leq1$. When $m=1$, both the prefactor and the empty product in (12.3) equal one. This proves all claims. $\square$

## 13. Evaluated contraction, spectrum and finite annihilation

**Definition 13.1 (Constants evaluated from the velocities).** In the domain of Definition 12.1, define

$$
\begin{gathered}
b_1=1,\qquad b_m=\left(\frac{m-1}{m}\right)^{m-1}\quad(m\geq2),\\
d(v)=\begin{cases}1,&\mathcal D(v)=1,\\b_m\mathcal D(v),&\mathcal D(v)<1,\end{cases}
\qquad \eta=\sigma d(v),\qquad r=1-\eta.
\end{gathered}
\tag{13.1}
$$

These are finite expressions in the dimension, original velocities and original damping. In particular $0<d(v)\leq1$, $0<\eta\leq1$ and $0\leq r<1$. Powers $0^0$ in integer-time bounds mean one.

**Theorem 13.2 (Finite-step, all-time and complex-spectral certificates).** For every $m\geq1$, every positive velocity vector of length $m+1$, every fixed $0<\alpha<1$, every $z\in\mathbb C^m$ and every integer $t\geq0$,

$$
\boxed{\quad Q(T^m z)\leq rQ(z),\qquad
Q(T^t z)\leq r^{\lfloor t/m\rfloor}Q(z).\quad}
\tag{13.2}
$$

Every complex spectral value $\mu$ of the original $T$ satisfies

$$
\boxed{\quad |\mu|\leq r^{1/(2m)}<1.\quad}
\tag{13.3}
$$

For every integer $0\leq p<m$ there is a nonzero complex, and also a nonzero real, input with $Q(T^p z)=Q(z)$; thus no such window gives a strict contraction for all inputs. At $q=0$ all statements remain valid. All initial states are annihilated after finitely many sweeps if and only if

$$
q=0\quad\hbox{and}\quad \mathcal D(v)=1.
\tag{13.4}
$$

In that case $T^m=0$, and $m$ is the least all-state annihilation time. More generally, for any fixed initial state, finite annihilation is equivalent to $T^m z=0$. For $m=1$, the exact identities are $Tz=-qz$, $d(v)=1$, $r=q^2$, including $T=0$ at $\alpha_*$.

*Proof.* Since $T$ is nonexpansive, each functional $\ell T^k$ has dual $Q$-norm at most one. Thus $H_T$ is positive definite by Theorem 12.2, has determinant $\mathcal D(v)$, and has trace at most $m$. Let its positive eigenvalues be $h_1\leq\cdots\leq h_m$. For $m\geq2$, the arithmetic-geometric mean inequality gives

$$
\prod_{j=2}^m h_j
\leq\left(\frac{\sum_{j=2}^m h_j}{m-1}\right)^{m-1}
\leq\left(\frac m{m-1}\right)^{m-1},
\qquad h_1\geq b_m\mathcal D(v).
\tag{13.5}
$$

If $\mathcal D(v)=1$, the product of all $h_j$ is one while their sum is at most $m$. The same inequality applied to all $m$ numbers forces equality and $h_j=1$ for every $j$, so $H_T=I$. For $m=1$ this follows directly from the unit observation. These arguments prove, in all cases,

$$
\sum_{k=0}^{m-1}|\ell(T^k z)|^2
=\langle z,H_Tz\rangle_Q\geq d(v)Q(z).
\tag{13.6}
$$

Summing the exact loss (12.7) along these $m$ actual iterates gives

$$
Q(T^m z)=Q(z)-\sigma\sum_{k=0}^{m-1}|\ell(T^k z)|^2.
\tag{13.7}
$$

Combining (13.6)–(13.7) proves the first estimate in (13.2). Apply it repeatedly at block boundaries and use nonexpansiveness for the remaining $0,\ldots,m-1$ steps to obtain the second, including $t=0$ and the convention when $r=0$. A complex spectral value in finite dimension has a nonzero complex eigenvector. Substitution in the first estimate yields $|\mu|^{2m}Q(z)\leq rQ(z)$, and $Q(z)>0$ proves (13.3). The constants came from the evaluated velocity product, rather than an unknown spectral radius or a norm of a growing power.

For a shorter window $p<m$, its $p$ observation functionals have a common kernel of dimension at least $m-p>0$. Their real coefficients also give a nonzero vector in the real kernel. The loss summed over those $p$ steps vanishes on that kernel, proving the assertion about every shorter window. This is the usual finite-observability rank argument, here consumed by the literal source map and the determinant (12.3).

Every reflection has determinant $-1$, so (12.7) gives

$$
\det U=(-1)^m,\qquad \det T=(-1)^m q.
\tag{13.8}
$$

If $\mathcal D(v)=1$, the stronger identity $H_T=I$ already proved gives $Q(T^m z)=q^2Q(z)$. Hence $q=0$ implies $T^m=0$. Conversely, if every input is annihilated in finite time, apply this assertion to a basis and take the largest of its finitely many annihilation times. This makes $T$ nilpotent. Its determinant is zero, so $q=0$ by (13.8). A nilpotent map in dimension $m$ satisfies $T^m=0$: its increasing sequence of kernels must stabilize by index $m$, and once two consecutive kernels coincide all later ones coincide. At $q=0$, (13.7) then gives $H_T=I$, so $\mathcal D(v)=1$. A nilpotence time $p<m$ is impossible by the shorter-window assertion. This proves (13.4) and its exact time.

The same kernel-stabilization argument proves the individual-state assertion without assuming that the whole map is nilpotent. Explicitly, if $\ker T^j=\ker T^{j+1}$, then $T^{j+2}z=0$ implies $Tz\in\ker T^{j+1}=\ker T^j$, hence $z\in\ker T^{j+1}$; induction gives equality of every later kernel. If no equality occurs before index $m$, all $m$ inclusions from $\ker I=0$ are strict, so $\ker T^m$ is the entire space and again stable. Thus $\bigcup_{j\geq0}\ker T^j=\ker T^m$. Finally, in dimension one the original first row is $-q$ and $A=1$, proving the exact scalar formulas.

An actual two-coordinate consumer also describes the finite-annihilation branch. For every $a>b>0$, take

$$
m=2,\qquad (v_1,v_2,v_3)=\left(a,b,\frac{b(a+b)}{a-b}\right),
\qquad \alpha=\frac b{a+2b}.
\tag{13.9}
$$

Then the original transfer is

$$
T=\begin{pmatrix}0&a/(a+b)\\0&0\end{pmatrix},\qquad
T\ne0,\quad T^2=0,\quad \mathcal D(v)=1.
\tag{13.10}
$$

These velocities and this parameter are strictly in their required domains. The singular first row has zero diagonal and right coefficient $a/(a+b)$. The original even relation has left coefficient $2v_3/(b+v_3)=(a+b)/a$ when solved for its new coordinate. It therefore gives $z'_2=-z_2+[(a+b)/a]z'_1=0$. This proves exactly the displayed matrix and its nilpotence. Alternatively (12.8) gives $c_1^2=1/2$, and (12.11) gives $\mathcal D=(1-c_1^2)4c_1^2=1$. The orthogonal singular mechanism is the one in Theorem 6.2; here its original velocity family consumes the evaluated condition $\mathcal D=1$ in (13.4), with no inverse of the damped map. $\square$

## 14. Original-coordinate error tolerances and sweep counts

**Definition 14.1 (Initial error and a finite zero test).** For the same original parameters let

$$
S=\sum_{j=1}^{m+1}v_j,\qquad S_i=\sum_{j=1}^i v_j,\qquad
x_i^*=\frac{S_i}{S},\qquad z_i=x_i(0)-x_i^*,
\qquad E_0=\max_{1\leq i\leq m}|z_i|.
\tag{14.1}
$$

The initial data $x(0)$ may be real or complex. The centered iterates are $x_i(t)-x_i^*=(T^t z)_i$. Set

$$
h_i=\frac{S_i(S-S_i)}{S},\qquad h=\max_{1\leq i\leq m}h_i>0,
\qquad Q_0=\sum_{j=1}^{m+1}\frac{|z_j-z_{j-1}|^2}{v_j},
\qquad A_0=\sqrt{hQ_0}.
\tag{14.2}
$$

A zero tolerance has the following finite algebraic criterion in the original parameters and data. To specify it without an unevaluated power norm, write $L_i=2v_{i+1}/s_i$, $R_i=2v_i/s_i$ and let $\delta_{ij}$ be the Kronecker symbol, zero whenever an index is outside $1,\ldots,m$. For odd $i$ define rows

$$
\begin{aligned}
D_{1j}&=-q\delta_{1j}+\frac{2\alpha v_1}{v_2+\alpha v_1}\delta_{2j},\\
D_{ij}&=-\delta_{ij}+L_i\delta_{i-1,j}+R_i\delta_{i+1,j}
\quad(i\geq3\text{ odd}),
\end{aligned}
$$

and set $D_{0j}=D_{m+1,j}=0$ whenever these exterior rows are needed. The following coefficients are completely explicit:

$$
C_{ij}=\begin{cases}
D_{ij},&i\text{ odd},\\
-\delta_{ij}+L_iD_{i-1,j}+R_iD_{i+1,j},&i\text{ even}.
\end{cases}
\tag{14.3}
$$

Define the finite vector

$$
Z_i=\sum_{j_0,\ldots,j_{m-1}=1}^{m}
C_{i,j_{m-1}}\left(\prod_{a=1}^{m-1}C_{j_a,j_{a-1}}\right)z_{j_0}
\qquad(1\leq i\leq m).
\tag{14.4}
$$

For $m=1$ the product is empty. All sums and products in (14.1)–(14.4) are finite, with ranges fixed by $m$.

**Theorem 14.2 (An evaluated tolerance certificate with every tolerance branch).** Define the original-coordinate error $E(t)=\max_i|x_i(t)-x_i^*|$. For every initial state and every integer $t\geq0$,

$$
E(t)\leq A_0 r^{\lfloor t/m\rfloor/2}.
\tag{14.5}
$$

For a prescribed real tolerance $\epsilon$, a certificate means an integer $K\geq0$ such that $E(t)\leq\epsilon$ for every integer $t\geq K$. The following complete alternatives apply.

1. If $\epsilon<0$, no such integer exists.
2. If $\epsilon\geq0$ and $Q_0=0$, take $K=0$.
3. If $\epsilon=0$ and $Q_0>0$, a certificate exists exactly when the explicit vector $Z$ of (14.4) is zero. In that case $K=m$ is a certificate; otherwise no finite $K$ is a certificate.
4. If $\epsilon>0$ and $A_0\leq\epsilon$, take $K=0$.
5. If $\epsilon>0$, $A_0>\epsilon$ and $r=0$, take $K=m$.
6. If $\epsilon>0$, $A_0>\epsilon$ and $0<r<1$, take

$$
\boxed{\quad K=m\left\lceil
\frac{\log(A_0^2/\epsilon^2)}{-\log r}
\right\rceil.\quad}
\tag{14.6}
$$

These are sufficient sweep counts, with no assertion of minimality. Every positive tolerance has a finite certificate. The singular interior parameter (12.5), every finite-annihilation input and the scalar case are included.

*Proof.* Fix an index $i$. Cauchy–Schwarz on the first $i$ edge differences and on the last $m+1-i$ edge differences separately gives, for any complex zero-endpoint vector $w$,

$$
\sum_{j=1}^i\frac{|w_j-w_{j-1}|^2}{v_j}
\geq\frac{|w_i|^2}{S_i},\qquad
\sum_{j=i+1}^{m+1}\frac{|w_j-w_{j-1}|^2}{v_j}
\geq\frac{|w_i|^2}{S-S_i}.
$$

Both denominators are positive, including at $i=1,m$. Addition yields

$$
|w_i|^2\leq h_iQ(w),\qquad
\max_i|w_i|\leq\sqrt{hQ(w)}.
\tag{14.7}
$$

This coefficient is the exact Dirichlet point-evaluation coefficient: equality for a prescribed value $w_i$ is obtained by taking $w_j=(S_j/S_i)w_i$ on the left and $w_j=[(S-S_j)/(S-S_i)]w_i$ on the right. Thus (14.7) uses the original coordinates and both zero endpoints, rather than an unspecified equivalence constant between norms. Applying (13.2) proves (14.5).

The original odd row gives exactly $D_{ij}$, and the original even equation solved for its new coordinate is $w'_i=-w_i+L_iw'_{i-1}+R_iw'_{i+1}$. Consequently $C$ in (14.3) is exactly $T$ in original coordinates. Repeated finite matrix multiplication shows that (14.4) is $T^m z$, with no limit involved. By the individual-state assertion of Theorem 13.2, a nonzero state reaches zero at a finite time precisely when $Z=0$. Zero is invariant under all subsequent powers. This proves branch 3; if $Z\ne0$, the state is nonzero at every finite time, so its maximum coordinate modulus cannot meet zero tolerance.

Branch 1 follows from $E(t)\geq0$. Positive definiteness of $Q$ proves branch 2. In branch 4, (14.5) and $r\leq1$ prove the assertion for all times. In branch 5, (13.2) makes every state zero after $m$ steps. For branch 6 the logarithm in the numerator is positive and $-\log r>0$. The integer in (14.6) ensures $r^{K/m}A_0^2\leq\epsilon^2$. Every $t\geq K$ has $\lfloor t/m\rfloor\geq K/m$, so (14.5) proves the desired all-later-time bound. These alternatives exhaust all real tolerances and initial states. No step divides by $q$; the zero test is finite even at $q=0$, where a general spectral-radius formula would not decide individual finite annihilation. $\square$

**Theorem 14.3 (A usable certificate in dimension, velocity ratio and damping).** Let

$$
v_- =\min_j v_j,\qquad v_+=\max_j v_j,\qquad R=\frac{v_+}{v_-}\geq1,
$$

and define the fully evaluated positive constants

$$
\boxed{\quad
d_R=\frac{b_m(m+1)}{2^mR^{m^2}},\qquad
\eta_R=\frac{4\alpha(1-\alpha)}{1+\alpha R}\,d_R,
\qquad A_R=\sqrt{m(m+1)R}\,E_0.\quad}
\tag{14.8}
$$

Then $0<\eta_R<1$ and, for all integer times and all real or complex initial states,

$$
\begin{gathered}
Q(T^m z)\leq(1-\eta_R)Q(z),\qquad
E(t)\leq A_R\exp\left(-\frac{\eta_R}2\lfloor t/m\rfloor\right),\\
|\mu|\leq(1-\eta_R)^{1/(2m)}\quad(\mu\in\operatorname{spec}_{\mathbb C}T).
\end{gathered}
\tag{14.9}
$$

For $\epsilon>0$, if $E_0=0$ or $A_R\leq\epsilon$, take $K_R=0$; otherwise the following depends only on $m,R,\alpha,E_0,\epsilon$:

$$
\boxed{\quad K_R=m\left\lceil
\frac{\log\big(m(m+1)R E_0^2/\epsilon^2\big)}{\eta_R}
\right\rceil.\quad}
\tag{14.10}
$$

It guarantees $E(t)\leq\epsilon$ for every $t\geq K_R$. Zero and negative tolerances retain the exact alternatives of Theorem 14.2.

*Proof.* Scale every velocity by $v_-^{-1}$ in (12.3), which leaves each factor unchanged. The scaled velocities lie in $[1,R]$. The prefactor in that formula is at least $(m+1)/(2R)^m$, and each factor inside the product is at least $R^{-2}$. As $\sum_{i=1}^{m-1}(m-i)=m(m-1)/2$,

$$
\mathcal D(v)\geq\frac{m+1}{2^mR^{m^2}}.
\tag{14.11}
$$

This also holds for $m=1$, where its right side is $R^{-1}\leq1=\mathcal D$. Hence $d(v)\geq d_R$, including the branch $\mathcal D=1$. If $a=v_1/v_2\leq R$, then (12.1) gives

$$
\sigma=4\alpha(1-\alpha)\frac{1+a}{(1+\alpha a)^2}
\geq\frac{4\alpha(1-\alpha)}{1+\alpha a}
\geq\frac{4\alpha(1-\alpha)}{1+\alpha R}.
\tag{14.12}
$$

The first inequality uses $1+a\geq1+\alpha a$. Therefore $\eta\geq\eta_R>0$. Also $d_R\leq1$ and $4\alpha(1-\alpha)\leq1<1+\alpha R$, proving $\eta_R<1$. The $Q$ and spectral bounds follow directly from Theorem 13.2 with this smaller evaluated constant.

For the coordinate prefactor, $h_i\leq S/4\leq(m+1)v_+/4$. The elementary estimate $|a-b|^2\leq2|a|^2+2|b|^2$, summed along the zero-endpoint path, gives

$$
Q_0\leq\frac4{v_-}\sum_{i=1}^m|z_i|^2
\leq\frac{4m}{v_-}E_0^2,\qquad
hQ_0\leq m(m+1)R E_0^2=A_R^2.
\tag{14.13}
$$

Use (14.7), the $m$-step bound, and $1-x\leq e^{-x}$ for $x\geq0$ to prove the coordinate estimate in (14.9). The stated integer (14.10) makes its square at the block boundary at most $\epsilon^2$. The same floor argument as in Theorem 14.2 proves it for every later integer time. All constants are explicit finite expressions; the use of $R$ removes absolute velocity scale from this conservative certificate. $\square$

## 15. Fixed-chain endpoint orders and two failures of uniform gaps

**Theorem 15.1 (Matching linear endpoint orders for every fixed chain).** Fix any $m\geq1$ and any positive velocity vector. Let $\rho_\alpha$ be the complex spectral radius of the literal $T=A^{-1}B_\alpha$. With $d=d(v)>0$ from (13.1), for all $0<\alpha<1$,

$$
\frac{d}{2m}\,
\frac{4\alpha(1-\alpha)v_2s_1}{(v_2+\alpha v_1)^2}
\leq1-\rho_\alpha\leq1-|q|^{1/m}\leq1-|q|.
\tag{15.1}
$$

In particular set

$$
c_v=\frac{dv_2}{ms_1}>0,\qquad
\alpha_* =\frac{v_2}{v_1+2v_2}.
$$

The following explicit two-sided estimates establish linear order at each endpoint:

$$
\begin{array}{ll}
c_v\alpha\leq1-\rho_\alpha\leq\dfrac{2s_1}{v_2}\alpha,
&0<\alpha\leq\min(1/2,\alpha_*),\\[5pt]
c_v(1-\alpha)\leq1-\rho_\alpha\leq2(1-\alpha),
&\max(1/2,\alpha_*)\leq\alpha<1.
\end{array}
\tag{15.2}
$$

At the exact endpoint extensions of the original matrices, $\rho_0=\rho_1=1$ and $Q$ is preserved. The constants in (15.2) are fixed-chain bounds, with no assertion of optimal coefficients or an optimal damping parameter.

*Proof.* Put $a=1/(2m)\in(0,1]$. The function $(1-x)^a$ is concave on $[0,1)$ and continuous at one, so its tangent at zero gives $(1-x)^a\leq1-ax$ for $0\leq x\leq1$. Theorem 13.2 therefore implies

$$
1-\rho_\alpha\geq1-(1-\sigma d)^{1/(2m)}\geq\frac{\sigma d}{2m}.
$$

By (13.8), the product of the $m$ eigenvalue moduli, counted with algebraic multiplicity, is $|q|$. Each is at most $\rho_\alpha$, hence $\rho_\alpha\geq|q|^{1/m}$. Finally $|q|^{1/m}\geq|q|$ for $|q|\in[0,1]$. This proves (15.1), including $q=0$ and $m=1$.

For $\alpha\leq1/2$, the numerator in $\sigma$ has $\alpha(1-\alpha)\geq\alpha/2$, and its denominator is at most $s_1^2$. Thus $\sigma\geq2\alpha v_2/s_1$, giving the first lower bound of (15.2). For $\alpha\geq1/2$ the same calculation with $\alpha(1-\alpha)\geq(1-\alpha)/2$ gives its second lower bound. If $\alpha\leq\alpha_*$ then $q\leq0$ and

$$
1-|q|=1+q=2\theta_\alpha
=\frac{2\alpha s_1}{v_2+\alpha v_1}
\leq\frac{2s_1}{v_2}\alpha.
$$

If $\alpha\geq\alpha_*$ then $q\geq0$ and

$$
1-|q|=1-q=2(1-\theta_\alpha)
=\frac{2v_2(1-\alpha)}{v_2+\alpha v_1}\leq2(1-\alpha).
$$

These inequalities prove both upper bounds in (15.2) on the displayed nonempty endpoint neighborhoods. At $\alpha=0,1$, (12.7) makes the endpoint matrices isometries for the positive definite $Q$. Each complex eigenvalue therefore has modulus one, and the nonempty finite-dimensional spectrum gives radius one. This also identifies the exact endpoint obstruction to an interior contraction certificate. $\square$

**Proposition 15.2 (Increasing dimensions with a bounded velocity ratio).** For every fixed $\alpha\in(0,1)$ there is a family of actual original chains, with dimensions $m\to\infty$ and velocity ratios at most two, whose fixed-map spectral gaps tend to zero. More explicitly choose

$$
a=\begin{cases}1,&\alpha\ne1/3,\\2,&\alpha=1/3,\end{cases}
\qquad v^{(m)}=(a,1,\ldots,1),\qquad
q_a=\frac{\alpha(a+2)-1}{1+\alpha a}.
\tag{15.3}
$$

Then $0<|q_a|<1$ and

$$
0<1-\rho(T_m)\leq1-|q_a|^{1/m}\longrightarrow0.
\tag{15.4}
$$

*Proof.* All $m+1$ velocities are positive and their ratio is $a\leq2$. For $a=1$, $q_a$ vanishes exactly at $\alpha=1/3$. At that excluded value the choice $a=2$ gives $q_a=1/5\ne0$. In either case $-1<q_a<1$ follows from (12.1), independently of $m$. These are the literal first velocities and unchanged tails of the original matrices; (13.8) gives $|\det T_m|=|q_a|$. The spectral-radius lower bound used in (15.1) proves (15.4), and $|q_a|^{1/m}=\exp(\log|q_a|/m)\to1$. Thus even with fixed interior damping and a fixed upper bound on the velocity ratio, a dimension-independent positive gap cannot hold across this family. This is a spectral obstruction for actual source transfers, rather than an inference from a small finite-time loss alone. $\square$

**Proposition 15.3 (Increasing velocity ratios in the original two-coordinate system).** Fix any $\alpha\in(0,1)$ and take

$$
m=2,\qquad (v_1,v_2,v_3)=(1,1,c),\qquad 0<c\leq1,
\qquad \theta=\frac{2\alpha}{1+\alpha},\qquad q=2\theta-1.
\tag{15.5}
$$

Then $R=1/c$ and the literal original transfer is

$$
T_c=\begin{pmatrix}
-q&\theta\\
-\dfrac{2cq}{1+c}&\dfrac{2c\theta}{1+c}-1
\end{pmatrix}.
\tag{15.6}
$$

Its complex spectral gap obeys

$$
0<1-\rho(T_c)\leq\sqrt{\frac{2c\theta}{1+c}}
\longrightarrow0\qquad(c\downarrow0).
\tag{15.7}
$$

Consequently fixed dimension and fixed interior damping alone give no positive gap uniform over all positive velocity vectors. This includes $\alpha=1/3$, when all maps in this family are singular.

*Proof.* Solving the original first row gives $z'_1=-qz_1+\theta z_2$. The original second row gives $z'_2=-z_2+[2c/(1+c)]z'_1$. These are exactly (15.6), with both original centered endpoints zero. Direct evaluation gives

$$
\det T_c=q,\qquad
\operatorname{tr}T_c=-q-1+\frac{2c\theta}{1+c},\qquad
\det(-I-T_c)=1+\operatorname{tr}T_c+\det T_c
=\frac{2c\theta}{1+c}>0.
$$

If $\mu_1,\mu_2$ are its two complex eigenvalues with multiplicity, then

$$
|1+\mu_1|\,|1+\mu_2|=\frac{2c\theta}{1+c}.
$$

At least one factor is at most the square root of this positive number. The corresponding eigenvalue satisfies $|\mu_j|\geq1-|1+\mu_j|$, proving the upper bound in (15.7). Strict positivity of the gap follows from Theorem 13.2 for every $c>0$; the right side tends to zero with $c$. The argument neither divides by $q$ nor assumes distinct or real eigenvalues. At $\alpha=1/3$, $q=0$ and $\theta=1/2$, so it includes that entire singular family explicitly. $\square$

## 追加锚（本行以下为增补区）
## 16. Undamped spectral information and the first dimension of optimizer failure

**Definition 16.1 (The full complex spectral objective in the original family).** For every integer $m\geq1$ and every $v\in(0,\infty)^{m+1}$, use exactly $A,B,B_\alpha$ of Definition 1.1, with $z_0=z_{m+1}=0$, and put $U_v=A^{-1}B$. Extend the displayed original first row continuously to $\alpha\in[0,1]$. Its denominator $v_2+\alpha v_1$ is positive on this closed interval. Use the increasing normalized parameter from (12.1), with its inverse,

$$
q_v(\alpha)=\frac{\alpha(v_1+2v_2)-v_2}{v_2+\alpha v_1},
\qquad
\alpha_v(q)=\frac{v_2(1+q)}{v_1+2v_2-v_1q},
\qquad -1\leq q\leq1,
\tag{16.1}
$$

and write $T_{v,q}=A^{-1}B_{\alpha_v(q)}$. In particular $T_{v,1}=U_v$; $T_{v,-1}$ is the other original endpoint extension. The first row of $B_{\alpha_v(q)}$ is

$$
(B_{\alpha_v(q)}z)_1=-qz_1+(1+q)\frac{v_1}{v_1+v_2}z_2,
\tag{16.2}
$$

where $z_2=0$ if $m=1$, and every other row is unchanged from $B$. Thus no original coordinate or zero endpoint is changed by this notation.

For $q\in[-1,1]$ let

$$
p_v(\zeta,q)=\det(\zeta I_m-T_{v,q}),\qquad
\mathsf S_v(q)=\{\mu_1(q),\ldots,\mu_m(q)\}
\tag{16.3}
$$

be its monic complex characteristic polynomial and its entire multiset of complex roots, counted with algebraic multiplicities. Define

$$
\rho_v(q)=\max_{1\leq j\leq m}|\mu_j(q)|,\qquad
\gamma_v=\min_{q\in[-1,1]}\rho_v(q),\qquad
Q_v=\{q\in[-1,1]:\rho_v(q)=\gamma_v\}.
\tag{16.4}
$$

The observation is

$$
\mathsf O(v)=(m,\mathsf S_v(1)).
\tag{16.5}
$$

Equality of observations means equality of dimensions and equality of the entire undamped complex multisets, including multiplicities. The set $Q_v$ is an optimizer set; the energy form $Q(z)$ retains exactly its meaning in (12.1).

The literal odd/even equations, centering, and Token-1 first row are those of [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, Section IV.A, page 3, and Section IV.B.1, page 4](https://arxiv.org/pdf/2608.27085v1). Their pair count is $m=n-1$, their centered $u$ is $z$, their $M$ is $U_v$, and their fixed $M_\alpha$ is $T_{v,q_v(\alpha)}$. Lemma 2 there supplies the undamped positive quadratic invariant, and Lemma 3 supplies determinant contraction in the open damping interval. The explicit energy, rank-one factorization, strict fixed-map contraction, low-dimensional transfers, finite-annihilation criteria and rate bounds in Sections 3 and 12–15 are supporting results here. In the complete [damped-sweep source](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean) and [finite-path source](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean), source pair $i$ and velocity $v_j$ have indices $i-1$ and $j-1$; `A`, `B`, `Balpha`, `Malpha` denote $A,B,B_\alpha,T_{v,q_v(\alpha)}$. The first-event weight `theta` there is $(1+q)/2$, not an undamped rotation angle. The local energy, loss and literal sweep identities used below are `local_energy_decomposition`, `Q_dampedEvent_loss`, `Q_event`, `Q_phase`, `sweep_stacked` and `source_factorization`; the strict fixed-map conclusion is `result`, with the finite-path rigidity, boundary observability and power-decay intermediates. Their complete [damped-sweep](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs) and [finite-path](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs) expositions have the same correspondence.

Polynomial factorization with multiplicities, the elementary symmetric functions of the roots and the quadratic formula are used in their classical sense; see [NIST DLMF, version 1.2.8, §1.11(ii)–(iv), especially (1.11.10), (1.11.11) and (1.11.21)–(1.11.23)](https://dlmf.nist.gov/1.11). These facts and the cited Token identities are intermediates to the information assertion below. Mensing's homogeneous qualitative antecedent is credited in [the same Token v1, Section II and reference [11]](https://arxiv.org/html/2608.27085v1#bib.bib11); its quantitative full-text overlap is unknown and no result from that full text is assumed. The attribution is confined to the stated sources and versions, with no exhaustive-literature or priority assertion.

**Theorem 16.2 (Retention through dimension two and exact failure in dimension three).** In Definition 16.1, equality of observations in dimension $m=1$ or $m=2$ determines $p_v(\zeta,q)$ for every $q\in[-1,1]$, and consequently determines the entire function $\rho_v$, the set $Q_v$ and the number $\gamma_v$.

In dimension $m=3$, the actual strictly positive chains

$$
v^{(0)}=(3,1,2,6),\qquad v^{(1)}=(3,1,14,42)
\tag{16.6}
$$

instead satisfy

$$
\mathsf O(v^{(0)})=\mathsf O(v^{(1)})
=\left(3,\left\{-1,\frac{1+i\sqrt3}{2},\frac{1-i\sqrt3}{2}\right\}\right),
\tag{16.7}
$$

with each undamped eigenvalue simple, and have identical original parameter maps

$$
q(\alpha)=\frac{5\alpha-1}{1+3\alpha},\qquad
\alpha(q)=\frac{1+q}{5-3q}.
\tag{16.8}
$$

Nevertheless their exact global full-spectrum optima are

$$
\boxed{\quad
Q_{v^{(0)}}=\{0\},\quad \gamma_{v^{(0)}}=0;
\qquad
Q_{v^{(1)}}=\{-1/4\},\quad \gamma_{v^{(1)}}=\frac1{\sqrt2}>0.
\quad}
\tag{16.9}
$$

Both minima are attained uniquely on the entire closed interval. In the original damping variable their unique minimizing sets are respectively $\{1/5\}$ and $\{3/23\}$. Thus dimension three is the first possible failure of these normalized-$q$ information targets in the original positive-velocity family.

*Proof.* First verify the domain and the existence of the minima used in (16.4). In (16.1), the inverse denominator is at least $2v_2>0$ for $-1\leq q\leq1$. Direct differentiation gives

$$
q_v'(\alpha)=\frac{2v_2(v_1+v_2)}{(v_2+\alpha v_1)^2}>0,
\qquad q_v(0)=-1,\quad q_v(1)=1.
\tag{16.10}
$$

Solving the first equation of (16.1) for $\alpha$ gives exactly its displayed inverse, so the correspondence is a bijection between the two closed intervals and between their interiors. Substituting it into the original first row gives (16.2). This also shows that the entries of $T_{v,q}$ and the coefficients of $p_v$ are continuous in $q$, indeed affine entries before taking the determinant. The only singular value is $q=0$, corresponding to $\alpha_*=v_2/(v_1+2v_2)$: by (13.8), $\det T_{v,q}=(-1)^m q$.

For the full complex root domain, retain the original positive definite Hermitian form

$$
Q(z)=\sum_{j=1}^{m+1}\frac{|z_j-z_{j-1}|^2}{v_j},
\qquad z_0=z_{m+1}=0.
$$

The source local reflection and sweep identities give precisely (12.7): if $P_1z=f_1\langle f_1,z\rangle_Q$, with the unit normal $f_1$ of Definition 12.1, then

$$
T_{v,q}=U_v\bigl(I-(1-q)P_1\bigr),\qquad
Q(T_{v,q}z)=Q(z)-(1-q^2)|\langle f_1,z\rangle_Q|^2.
\tag{16.11}
$$

These are polynomial identities in $q$, so the endpoint extensions and the singular interior value are included. The factor $U_v$ preserves $Q$. For every nonzero complex eigenvector, (16.11) implies $|\mu|\leq1$. At $q=-1$ the second factor is $I-2P_1$, a $Q$-reflection, and at $q=1$ it is $I$. Thus both endpoint maps preserve $Q$, and every eigenvalue at either endpoint has modulus one. Consequently $\rho_v(-1)=\rho_v(1)=1$. On $-1<q<1$, the strict fixed-map conclusion in Theorem 13.2 gives $\rho_v(q)<1$.

Here is a root argument that includes every multiplicity and proves continuity of the actual maximum in (16.4). Given any sequence $q_n\to q$, list all $m$ complex roots of $p_v(\zeta,q_n)$ in any order, with multiplicities. The resulting tuples belong to the compact product of $m$ closed unit disks, by (16.11). Along any convergent subsequence of such tuples, with limit $(\nu_1,\ldots,\nu_m)$, continuity of the coefficients and of finite multiplication gives

$$
p_v(\zeta,q)=\prod_{j=1}^m(\zeta-\nu_j).
$$

Thus the limiting tuple is exactly the full root multiset at $q$. Its maximum modulus is $\rho_v(q)$, so along that subsequence $\rho_v(q_n)\to\rho_v(q)$. If convergence failed for the original sequence, an infinite subsequence staying a fixed positive distance from $\rho_v(q)$ would have a further convergent root-tuple subsequence, contradicting this conclusion. This proves continuity without a choice of continuously labeled roots. The extreme-value theorem now makes $\gamma_v$ attained and $Q_v$ nonempty and compact. The strict interior bound and the endpoint values also give $Q_v\subset(-1,1)$. These facts justify the optimization definitions on their full stated domain, independently of any simple-root assumption.

In dimension one the existing scalar identity of Theorem 13.2 is $T_{v,q}=-q$ and $U_v=-1$. Therefore

$$
p_v(\zeta,q)=\zeta+q,\qquad
\rho_v(q)=|q|,\qquad Q_v=\{0\},\qquad\gamma_v=0.
\tag{16.12}
$$

All chains of that dimension have this same normalized polynomial, including its zero root and its two endpoint values.

For dimension two use the original transfer formula (3.1), with positive velocities $(a,b,c)$, $\xi=a/(a+b)$, $\eta=c/(b+c)$ and the original event weight $\tau=(1+q)/2$. It gives, still in the original coordinates,

$$
T_{v,q}=\begin{pmatrix}
-q&(1+q)\xi\\
-2\eta q&2\eta\xi(1+q)-1
\end{pmatrix}.
\tag{16.13}
$$

Set $\kappa=2\xi\eta-1\in(-1,1)$. The determinant and trace of (16.13) are $q$ and $\kappa(1+q)$, respectively; at $q=1$ the undamped trace is $2\kappa$. If $\{\nu_1,\nu_2\}$ is the observed undamped multiset, its sum is that trace. Hence the observation fixes $\kappa=(\nu_1+\nu_2)/2$ and the entire polynomial

$$
p_v(\zeta,q)=\zeta^2-\kappa(1+q)\zeta+q.
\tag{16.14}
$$

For completeness its full root and radius alternatives follow directly from the classical quadratic formula. Put $\Delta=\kappa^2(1+q)^2-4q$. If $\Delta\geq0$, the two real roots, with a double root when $\Delta=0$, are $[\kappa(1+q)\pm\sqrt\Delta]/2$, and

$$
\rho_v(q)=\frac{|\kappa|(1+q)+\sqrt\Delta}{2}.
$$

Indeed for real $t$ and $s\geq0$, $\max(|t+s|,|t-s|)=|t|+s$. If $\Delta<0$, then $q>0$ and the roots are a nonreal conjugate pair of product $q$; each has modulus $\sqrt q$, so $\rho_v(q)=\sqrt q$. At $q=-1$, (16.14) is $\zeta^2-1$; at $q=1$ it is $\zeta^2-2\kappa\zeta+1$; and at $q=0$ it is $\zeta(\zeta-\kappa)$, including the double zero when $\kappa=0$. Thus every branch, endpoint and multiplicity is determined by the observation. Equations (16.12)–(16.14), consumed here from the published scalar and two-coordinate transfers, prove the asserted retention, since equal radius functions have equal global minimum and argmin set on the same compact interval. This retention concerns normalized $q$; the conversion from $q$ back to $\alpha$ retains the actual first two velocities in (16.1).

For the dimension-three comparison take the positive one-parameter velocity family

$$
v(c)=(3,1,c,3c),\qquad c>0.
\tag{16.15}
$$

Substituting into the literal original rows, with $z_0=z_4=0$, gives

$$
A_c=\begin{pmatrix}1&0&0\\-2c&1+c&-2\\0&0&1\end{pmatrix},\qquad
B_c=\begin{pmatrix}-1&3/2&0\\0&-(1+c)&0\\0&3/2&-1\end{pmatrix},
\tag{16.16}
$$

$$
B_{c,\alpha}=\begin{pmatrix}
\dfrac{1-5\alpha}{1+3\alpha}&\dfrac{6\alpha}{1+3\alpha}&0\\
0&-(1+c)&0\\
0&3/2&-1
\end{pmatrix}
=\begin{pmatrix}
-q&\tfrac34(1+q)&0\\
0&-(1+c)&0\\
0&3/2&-1
\end{pmatrix}.
\tag{16.17}
$$

In particular the entire family has exactly the original parameter correspondence (16.8). The original even row is $-2cw_1+(1+c)w_2-2w_3=b_2$. Solving it after the two odd rows gives

$$
A_c^{-1}=\begin{pmatrix}
1&0&0\\
\dfrac{2c}{1+c}&\dfrac1{1+c}&\dfrac2{1+c}\\
0&0&1
\end{pmatrix},
\qquad
T_{v(c),q}=\begin{pmatrix}
-q&\tfrac34(1+q)&0\\
-\dfrac{2cq}{1+c}&-1+\dfrac{3c(1+q)}{2(1+c)}+\dfrac3{1+c}&-\dfrac2{1+c}\\
0&3/2&-1
\end{pmatrix}.
\tag{16.18}
$$

This is $A_c^{-1}B_{c,\alpha}$ itself. To compute its full characteristic polynomial, use $\det A_c=1+c>0$ and expand

$$
\zeta A_c-B_{c,\alpha}=
\begin{pmatrix}
\zeta+q&-\tfrac34(1+q)&0\\
-2c\zeta&(1+c)(\zeta+1)&-2\zeta\\
0&-3/2&\zeta+1
\end{pmatrix}.
$$

The first-row expansion, divided by $1+c$, is

$$
\begin{aligned}
p_{v(c)}(\zeta,q)
&=(\zeta+q)\left((\zeta+1)^2-\frac{3\zeta}{1+c}\right)
 -\frac{3c}{2(1+c)}(1+q)\zeta(\zeta+1)\\
&=\zeta^3+\frac{c-2}{2(c+1)}(1-q)\zeta^2
 -\frac{c-2}{2(c+1)}(1-q)\zeta+q.
\end{aligned}
\tag{16.19}
$$

For example, the coefficients of $\zeta^2$ and $\zeta$ before simplification are
$2-3/(1+c)-3c/[2(1+c)]+q(1-3c/[2(1+c)])$
and
$1-3c/[2(1+c)]+q(2-3/(1+c)-3c/[2(1+c)])$;
these are respectively $[(c-2)/(2(c+1))](1-q)$ and its negative. Thus (16.19) evaluates the determinant with no spectral value omitted.

At $q=1$ this polynomial is $\zeta^3+1=(\zeta+1)(\zeta^2-\zeta+1)$ for every $c>0$. Its three distinct roots are exactly those in (16.7). The choices $c=2$ and $c=14$ in (16.15) give (16.6). Both chains therefore have the same entire undamped complex spectrum, not just the same trace, determinant or spectral radius, and (16.17) proves equality of their full original $\alpha$-to-$q$ maps.

For $c=2$, (16.19) reduces to

$$
p_{v^{(0)}}(\zeta,q)=\zeta^3+q.
\tag{16.20}
$$

At $q=0$ all three roots are zero, with algebraic multiplicity three. At any $q\ne0$ the three roots are distinct and all have modulus $|q|^{1/3}$: if $\mu^3=-q$, they are $\mu,\mu\omega,\mu\omega^2$, where $\omega=(-1+i\sqrt3)/2$ has modulus one. Hence $\rho_{v^{(0)}}(q)=|q|^{1/3}$ for the entire closed interval, proving its unique optimum in (16.9). In particular the singular value is included; its characteristic polynomial is exactly $\zeta^3$, in agreement with the finite-annihilation criterion of Theorem 13.2.

For $c=14$, (16.19) instead gives

$$
p_{v^{(1)}}(\zeta,q)=\zeta^3+\frac25(1-q)\zeta^2
                                  -\frac25(1-q)\zeta+q.
\tag{16.21}
$$

Let $r=1/\sqrt2$ and $q_*=-1/4$. At this value the entire polynomial factors as

$$
p_{v^{(1)}}(\zeta,q_*)
=(\zeta^2-1/2)(\zeta+1/2).
\tag{16.22}
$$

Its full multiset is $\{r,-r,-1/2\}$, with all roots simple, and $1/2<r$ since $1/4<1/2$. Thus the actual maximum over all three complex roots is exactly $r$ at $q_*$. For every real $q$, evaluation at both boundary points of this candidate optimal disk gives the exact identities

$$
p_{v^{(1)}}(r,q)=\frac{4+\sqrt2}{5}(q+1/4),\qquad
p_{v^{(1)}}(-r,q)=\frac{4-\sqrt2}{5}(q+1/4).
\tag{16.23}
$$

To verify them, note that both values vanish at $q_*$ by (16.22) and that their coefficients of $q$ are $1-(2/5)(r^2-r)$ and $1-(2/5)(r^2+r)$, respectively. Substitution of $r^2=1/2$ gives precisely (16.23), whose two coefficients are strictly positive.

If $-1\leq q<q_*$, the first value in (16.23) is negative. The monic real cubic (16.21) tends to $+\infty$ as its real argument tends to $+\infty$. The intermediate value theorem therefore gives a real root strictly larger than $r$. That root is an eigenvalue of the actual $T_{v^{(1)},q}$, so the maximum over its entire complex spectrum is strictly larger than $r$. If $q_*<q\leq1$, the second value in (16.23) is positive. The same monic cubic tends to $-\infty$ at $-\infty$, giving a real root strictly smaller than $-r$ and the same strict lower bound for the full spectral radius. Together with the exact three-root factorization at $q_*$, these two comparisons prove both global minimality and uniqueness on all of $[-1,1]$.

The comparison uses a real root only as a lower bound for the maximum of all three root moduli; equality at the minimizer uses the complete complex factorization (16.22). In particular the other two roots at an arbitrary $q$ may be real, nonreal or multiple without altering either strict comparison. The determinant identity (16.21) remains the specification of all three algebraic roots at every such parameter, so no simple-root or real-spectrum restriction enters the argument.

The endpoint and singular multisets can also be stated explicitly. For the first chain, $q=-1$ gives $\{1,(-1+i\sqrt3)/2,(-1-i\sqrt3)/2\}$, and $q=1$ gives (16.7); both radii are one. For the second chain the corresponding polynomials are

$$
\begin{aligned}
p_{v^{(1)}}(\zeta,-1)&=(\zeta-1)(\zeta^2+\tfrac95\zeta+1),\\
p_{v^{(1)}}(\zeta,1)&=(\zeta+1)(\zeta^2-\zeta+1),\\
p_{v^{(1)}}(\zeta,0)&=\zeta(\zeta^2+\tfrac25\zeta-\tfrac25).
\end{aligned}
\tag{16.24}
$$

Their full multisets are respectively

$$
\left\{1,\frac{-9+i\sqrt{19}}{10},\frac{-9-i\sqrt{19}}{10}\right\},
\qquad
\left\{-1,\frac{1+i\sqrt3}{2},\frac{1-i\sqrt3}{2}\right\},
\qquad
\left\{0,\frac{-1+\sqrt{11}}5,\frac{-1-\sqrt{11}}5\right\}.
\tag{16.25}
$$

All entries in each multiset are simple. The first two have radius one; the last is the singular interior map and has radius $(1+\sqrt{11})/5>r$. For the strict inequality, both sides are positive and $(1+\sqrt{11})^2/25>1/2$ is equivalent to $\sqrt{11}>1/4$, which holds. Thus both endpoint extensions, the two different zero-root multiplicities at $q=0$, and nonreal endpoint roots agree with the global comparison.

Finally, applying the same strictly increasing inverse (16.8) to $0$ and $-1/4$ yields respectively $1/5$ and $3/23$. No other original $\alpha\in[0,1]$ can minimize, by bijectivity. The dimension-one and dimension-two retention already proved excludes a failure of either information target in those dimensions; (16.6)–(16.9) establishes both failures in dimension three. $\square$

**Corollary 16.3 (No global optimizer selector or minimum-radius function of the observation).** There is no function of $\mathsf O(v)$ that selects an element of $Q_v$ for every original positive-velocity chain, and no function of $\mathsf O(v)$ equal to $\gamma_v$ for every such chain. The same two impossibilities hold even if the observation is augmented by the entire original map $\alpha\mapsto q_v(\alpha)$. In particular $Q_v$ itself is not a function of that augmented observation.

*Proof.* For the two chains (16.6), both the ordinary and augmented observations coincide, by (16.7)–(16.8). A selector would have to return the same $q$ on these equal observations, but the two required singleton sets in (16.9) are disjoint. A minimum-radius function would have to return both $0$ and $1/\sqrt2$ on that same input, which is impossible. Likewise an exact set-valued rule would have to return both different singletons. This proves each assertion within the literal original family.

The missing information is a distinction between actual chains in one undamped-spectral fiber: in (16.19) the coefficient $(c-2)/(2(c+1))$ disappears at $q=1$, while it changes the full damped polynomial for $q\ne1$. The equality of observations therefore does not identify the relation between the boundary damping and the undamped dynamics. The scalar and two-coordinate identities (16.12) and (16.14) retain enough of that relation to determine their normalized polynomials.

These are fixed-map spectral-information statements. Each $T_{v,q}$ is held fixed when its spectrum or its powers are considered. The arbitrary-dimensional problem of determining $Q_v$ and $\gamma_v$ from the full original velocity chain, rather than from $\mathsf O(v)$ alone, remains unresolved here. The prescribed and mixed histories in Sections 1–11 keep their own distinct domains. The collision process, entry into the rotational regime, switching realizations, and uniform quantitative rates are not consequences of this information obstruction; the original energy and the fixed-chain bounds of Sections 12–15 retain their stated hypotheses. $\square$

## 追加锚（本行以下为增补区）

## 17. A finite critical-parameter theorem for affine root radii

**Definition 17.1 (Real field, affine polynomial and root-product polynomial).** Let $F\subseteq\mathbb R$ be a field with its given real embedding, let $d\geq1$, and let

$$
p(Z,t)=a(Z)+t b(Z)\in F[t,Z],\qquad
\deg a=d,\quad a\text{ monic},\quad \deg b<d.
\tag{17.1}
$$

For real $t$, list the $d$ complex roots of $p(Z,t)$ as $\lambda_1(t),\ldots,\lambda_d(t)$, with algebraic multiplicity, and put

$$
r(t)=\max_j|\lambda_j(t)|,\qquad s(t)=r(t)^2.
\tag{17.2}
$$

The list is a multiset; it imposes no continuous labeling. Define the polynomial

$$
\begin{aligned}
p^{\flat}(Z,X,t)&=Z^d p(X/Z,t),\\
\mathcal R(X,t)&=\operatorname{Res}_Z
             \bigl(p(Z,t),p^{\flat}(Z,X,t)\bigr).
\end{aligned}
\tag{17.3}
$$

The first line means polynomial expansion, so it is defined also at $Z=0$. The resultant uses the Sylvester determinant, with both degree bounds in $Z$ equal to $d$; vanishing leading coefficients are retained as zero coefficients in that determinant. If the first polynomial is monic, the convention is

$$
\operatorname{Res}_Z(f,g)=\prod_{f(\lambda)=0}g(\lambda),
\tag{17.4}
$$

with multiplicities. This identity remains valid when the degree of $g$ falls. The Sylvester determinant, its root-product formula and its common-root property are classical; see [Sturmfels, *Solving Systems of Polynomial Equations*, §4.1, Theorem 4.1, (4.3) and the product formulas following it](https://math.berkeley.edu/~bernd/cbms.pdf). The root-radius objective is the one in [Eaton, Grundel, Gürbüzbalaban and Overton, *Polynomial root radius optimization with affine constraints*, §2 and §3](https://cs.nyu.edu/overton/papers/pdffiles/PolyRootRadOptAffConPublished.pdf), [DOI 10.1007/s10107-016-1092-5](https://doi.org/10.1007/s10107-016-1092-5).

**Assumption 17.2 (Unit-circle endpoints and strict interior roots).** For the polynomial in Definition 17.1, assume that all roots at $t=-1$ and at $t=1$ have modulus one, and that

$$
|\lambda_j(t)|<1\qquad(-1<t<1,\ 1\leq j\leq d).
\tag{17.5}
$$

The parameter is fixed when a root multiset is taken. No simplicity, diagonalizability, nonvanishing constant term or rationality assumption is imposed.

**Theorem 17.3 (Every minimizer from a nonzero polynomial of cubic degree bound).** Under Definition 17.1 and Assumption 17.2, factor $\mathcal R$ in $F[t,X]$ into distinct monic-in-$X$ irreducible factors and their positive multiplicities:

$$
\mathcal R(X,t)=\prod_{\nu=1}^h h_\nu(X,t)^{e_\nu},
\qquad
V(X,t)=\prod_{\nu=1}^h h_\nu(X,t).
\tag{17.6}
$$

These normalizations exist. Every $h_\nu$ has positive degree in both $X$ and $t$. Write $D=\deg_X V$ and $E=\deg_t V$, and define

$$
\begin{aligned}
\Delta_1(t)&=\operatorname{Res}_X(V,V_X),\\
\Delta_2(t)&=\operatorname{Res}_X(V,V_t),\\
\Delta(t)&=\Delta_1(t)\Delta_2(t),\\
C&=\{c\in\mathbb R:-1<c<1,\ \Delta(c)=0\}.
\end{aligned}
\tag{17.7}
$$

Subscripts on $V$ are partial derivatives. Resultants of a monic polynomial and a nonzero constant have their usual value, the constant raised to the degree of the monic polynomial. Then

$$
\begin{gathered}
1\leq D\leq d^2,\qquad 1\leq E\leq2d,\qquad
\Delta\in F[t]\setminus\{0\},\\
1\leq\deg\Delta\leq(4D-2)E\leq8d^3-4d<8d^3.
\end{gathered}
\tag{17.8}
$$

The finite set $C$ is nonempty and contains every global minimizing parameter of $r$ on $[-1,1]$. For each real $c\in[-1,1]$, define the ordered real root

$$
\mathfrak s(c)=\max\{x\in\mathbb R:x\geq0,\ \mathcal R(x,c)=0\}.
\tag{17.9}
$$

This root always exists and equals $s(c)$. Consequently the exact minimum and the entire optimizer set are

$$
\begin{aligned}
s_*&=\min_{c\in C}\mathfrak s(c),\\
\min_{-1\leq t\leq1}r(t)&=\text{the nonnegative real root of }Y^2-s_*=0,\\
\operatorname*{argmin}_{[-1,1]}r
 &=\{c\in C:\mathfrak s(c)=s_*\}.
\end{aligned}
\tag{17.10}
$$

In particular the optimizer set is finite, nonempty and contained in $(-1,1)$; each of its elements and the minimum value are algebraic over $F$. The factorization in (17.6) is taken for the given polynomial over the given field, including all its actual coefficient equalities.

*Proof.* Expand $p^{\flat}$ before taking the resultant. Its coefficients in $Z$ are polynomials in $X$ and are affine in $t$, as are the coefficients of $p$. The Sylvester determinant has $d$ rows from each polynomial. Each determinant term therefore has degree at most $2d$ in $t$, whence

$$
\deg_t\mathcal R\leq2d.
\tag{17.11}
$$

For any fixed real $t$ at which $p(0,t)\ne0$, the product formula (17.4) gives

$$
\begin{aligned}
\mathcal R(X,t)
 &=\prod_{i=1}^d\bigl(\lambda_i(t)^d
                         p(X/\lambda_i(t),t)\bigr)\\
 &=\prod_{i=1}^d\prod_{j=1}^d
                         (X-\lambda_i(t)\lambda_j(t)).
\end{aligned}
\tag{17.12}
$$

The identity includes every ordered pair, also $i=j$, and all repeated roots. It holds without the restriction $p(0,t)\ne0$. One way to see this directly at a zero root is to note that $p^{\flat}(0,X,t)=X^d$: the factor in (17.4) for $\lambda_i=0$ is $X^d$, exactly the product of its $d$ factors on the right. For a nonzero $\lambda_i$ the preceding calculation still applies. Thus (17.12) is valid at every real $t$, including a vanishing constant term. Equivalently it is the polynomial identity obtained from the classical resultant formula before any specialization.

In particular $\mathcal R$ is monic of degree $d^2$ in $X$, and is nonzero. For a real parameter, complex conjugation permutes the complete root multiset. If $|\lambda_i|=r(t)$, its conjugate is some $\lambda_j$ with the appropriate multiplicity, so $s(t)=\lambda_i\lambda_j$ is a nonnegative real root of $\mathcal R(X,t)$. Every other nonnegative real root is some product $\lambda_k\lambda_l$ and hence satisfies

$$
0\leq\lambda_k\lambda_l
   =|\lambda_k\lambda_l|\leq r(t)^2.
\tag{17.13}
$$

This proves (17.9) on the whole interval, including $s(t)=0$. It uses the full complex root multiset, not just its real roots or any selected conjugate pairs.

The polynomial ring $F[t,X]$ is a unique factorization domain. The relevant Gauss-lemma passage between $F[t,X]$ and $F(t)[X]$ is the classical one for a polynomial ring over a field; see [The Stacks Project, Example 10.27.3, tag 00F0](https://stacks.math.columbia.edu/tag/00F0). Monicity of $\mathcal R$ in $X$ has two consequences. It has no nonconstant factor in $F[t]$, and every factor of positive $X$ degree can be normalized to be monic in $X$ with coefficients still in $F[t]$. Indeed the product of the $X$-leading coefficients of all factors, with multiplicity, is the constant one, so each such coefficient is a unit of $F[t]$. This proves existence and uniqueness, up to ordering, of (17.6).

There is also no nonconstant factor of $\mathcal R$ in $F[X]$. For if $g(X)$ were such a factor and $\xi\in\mathbb C$ one of its roots, then $\mathcal R(\xi,1)=0$. Formula (17.12) and the endpoint hypothesis would give $|\xi|=1$. But $\mathcal R(\xi,0)=0$, and every product on the right of (17.12) at $t=0$ has modulus strictly less than one by (17.5). This would give $|\xi|<1$, a contradiction. Thus every $h_\nu$ depends on $t$ as well as $X$.

Degrees in either variable add under nonzero products over an integral domain. Taking distinct factors once instead of $e_\nu$ times therefore gives

$$
1\leq\deg_X V\leq\deg_X\mathcal R=d^2,
\qquad
1\leq\deg_t V\leq\deg_t\mathcal R\leq2d.
\tag{17.14}
$$

Moreover, for every real $c$, monicity of all the $h_\nu$ ensures that none specializes to the zero polynomial. Equation (17.6) then implies equality of zero sets

$$
\{x\in\mathbb C:\mathcal R(x,c)=0\}
  =\{x\in\mathbb C:V(x,c)=0\}.
\tag{17.15}
$$

Factors may acquire repeated roots or collide after specialization; this equality still holds. In particular $V(s(t),t)=0$ at every parameter in the interval.

We prove that both resultants in (17.7) are nonzero polynomials. Work temporarily in the univariate polynomial ring $F(t)[X]$. Each monic $h_\nu$ remains irreducible there by Gauss's lemma, and distinct factors remain relatively prime. In characteristic zero, $(h_\nu)_X$ is nonzero and has $X$ degree less than $\deg_X h_\nu$. Also $(h_\nu)_t\ne0$, since $h_\nu$ depends on $t$, and its $X$ degree is strictly smaller than $\deg_X h_\nu$, since the leading coefficient in $X$ is the constant one. Hence $h_\nu$ divides neither of these two partial derivatives. Reducing the product rule modulo $h_\nu$ gives

$$
\begin{aligned}
V_X&\equiv(h_\nu)_X\prod_{\mu\ne\nu}h_\mu
                                      \pmod{h_\nu},\\
V_t&\equiv(h_\nu)_t\prod_{\mu\ne\nu}h_\mu
                                      \pmod{h_\nu}.
\end{aligned}
\tag{17.16}
$$

Both right sides are nonzero in the field $F(t)[X]/(h_\nu)$. It follows that

$$
\gcd(V,V_X)=\gcd(V,V_t)=1\quad\text{in }F(t)[X].
\tag{17.17}
$$

The common-root criterion for a Sylvester resultant, or its equivalent Bézout criterion, now shows that $\Delta_1$ and $\Delta_2$ are nonzero in $F(t)$. They were defined as polynomial determinants over $F[t]$, so they are nonzero polynomials in $F[t]$. This step proves nonvanishing for the actual coefficients; it uses no unspecified generic parameter.

For polynomials of $X$ degrees $A,B$ whose coefficient degrees in $t$ are at most $P,Q$, respectively, the Sylvester determinant gives

$$
\deg_t\operatorname{Res}_X(f,g)\leq BP+AQ.
\tag{17.18}
$$

Indeed its determinant terms take $B$ coefficients from $f$ and $A$ from $g$. For $B=0$ the same inequality follows from $\operatorname{Res}_X(f,g)=g^A$ when $f$ is monic. Here each derivative of $V$ has $X$ degree at most $D-1$, while its coefficient degrees in $t$ are at most $E$. Applying (17.18) twice yields

$$
\deg\Delta_1\leq(2D-1)E,
\qquad
\deg\Delta_2\leq(2D-1)E,
\qquad
\deg\Delta\leq(4D-2)E\leq8d^3-4d.
\tag{17.19}
$$

It remains to prove that every optimizer is captured, rather than only a selected smooth branch. First $r$ and $s$ are continuous. The full-multiset compactness proof used in Theorem 16.2 applies verbatim: for a sequence of real parameters tending to $t_0\in[-1,1]$, all root tuples lie in the product of $d$ closed unit disks by (17.5) and the endpoint hypothesis. Every convergent subsequence of those tuples factors the limiting monic polynomial into exactly its $d$ roots with multiplicity. Its maximum modulus is therefore $r(t_0)$. A subsequence contradicting continuity would have a further convergent root tuple and so is impossible. The polynomial factorization with multiplicities used here is the classical fundamental theorem of algebra; see [NIST DLMF, §1.11(ii)](https://dlmf.nist.gov/1.11#ii).

The extreme-value theorem supplies a minimum on $[-1,1]$. Both endpoint radii are one, whereas $r(0)<1$, so every minimizer $t_0$ lies in the interior. Put $s_0=s(t_0)$. If $V_X(s_0,t_0)=0$, then $V$ and $V_X$ have the common root $s_0$ after specialization, and $\Delta_1(t_0)=0$.

Suppose instead that $V_X(s_0,t_0)\ne0$. We can differentiate $s$ at this one point without choosing or differentiating individual eigenvalues. For $t\ne t_0$ sufficiently near $t_0$, use $V(s(t),t)=V(s_0,t_0)=0$ and apply the ordinary real mean value theorem separately in $X$ and in $t$. There are $\xi_t$ between $s(t)$ and $s_0$, and $\eta_t$ between $t$ and $t_0$, such that

$$
0=(s(t)-s_0)V_X(\xi_t,t)
           +(t-t_0)V_t(s_0,\eta_t).
\tag{17.20}
$$

When $s(t)=s_0$, the same formula holds with $\xi_t=s_0$. Continuity gives $\xi_t\to s_0$ and $\eta_t\to t_0$. Thus $V_X(\xi_t,t)$ is nonzero for all sufficiently close $t$, and division in (17.20) proves

$$
s'(t_0)=-\frac{V_t(s_0,t_0)}{V_X(s_0,t_0)}.
\tag{17.21}
$$

Since $s$ has an interior minimum at $t_0$, its derivative there is zero. Therefore $V_t(s_0,t_0)=0$, so $\Delta_2(t_0)=0$. Monicity of $V$ makes the common-root resultant implication valid even if a specialized derivative has smaller degree or is the zero polynomial. These two alternatives also cover a zero minimum and every collision. Hence every minimizer belongs to $C$.

The nonzero polynomial $\Delta$ has at least this one real interior root, so it has positive degree and $C$ is finite and nonempty. This completes (17.8). Because $s(t)=r(t)^2$ and $r(t)\geq0$, these two functions have the same minimizers. Every candidate is in the original interval, and every global minimizer is a candidate. Taking the least of the finitely many exact values (17.9) therefore proves both equalities and the entire-set assertion in (17.10).

Finally, each $c\in C$ is algebraic over $F$, being a root of the nonzero polynomial $\Delta$. The polynomial $\mathcal R(X,c)$ is monic, so $\mathfrak s(c)$ is algebraic over $F(c)$ and hence over $F$. The minimum of a nonempty finite set of these numbers is one of them. Its nonnegative square root is algebraic as well. This is transitivity of algebraicity, as in [Milne, *Fields and Galois Theory*, version 5.10, Proposition 1.30 and Corollary 1.31](https://www.jmilne.org/math/CourseNotes/FT.pdf). It proves the asserted field boundary without requiring $F$ to be a number field.

The affine-space result of Eaton, Grundel, Gürbüzbalaban and Overton cited in Definition 17.1, Proposition 1 and Theorem 1, establishes existence of an optimizer with a specified number of active roots. The finite description of every minimizing parameter here follows instead from (17.12), the exclusion of $t$-independent factors by the two spectral scales, and the exhaustive alternatives (17.20)–(17.21) or $V_X=0$. The classical resultant, factorization and field-extension facts are supporting steps in this implication. $\square$

## 18. The entire original damping optimizer set from the actual chain

**Definition 18.1 (Actual field and original-row polynomial).** Fix any integer $m\geq1$ and any strictly positive real chain $v=(v_1,\ldots,v_{m+1})$. Set

$$
F_v=\mathbb Q(v_1,\ldots,v_{m+1})\subseteq\mathbb R,
\qquad s_i=v_i+v_{i+1}.
\tag{18.1}
$$

Use the literal $A,B,B_\alpha$ of Definition 1.1, the zero endpoints $z_0=z_{m+1}=0$, and their endpoint extensions from Definition 16.1. Define $\mathcal B_v(q)$ to have the same rows as $B$ except for its first row

$$
(\mathcal B_v(q)z)_1=-qz_1+(1+q)\frac{v_1}{s_1}z_2,
\qquad z_2=0\quad(m=1).
\tag{18.2}
$$

Keep exactly the original parameter correspondence

$$
q=q_v(\alpha)=\frac{\alpha(v_1+2v_2)-v_2}{v_2+\alpha v_1},
\qquad
\alpha=\alpha_v(q)=\frac{v_2(1+q)}{v_1+2v_2-v_1q}.
\tag{18.3}
$$

The full characteristic polynomial in this notation is

$$
\boxed{\quad
p_v(Z,q)=\frac{\det(Z A-\mathcal B_v(q))}
                  {\displaystyle\prod_{\substack{1\leq i\leq m\\i\ {\rm even}}}s_i}.
\quad}
\tag{18.4}
$$

All determinants in (18.4) are finite determinants in the original coordinates. For each fixed actual $v$, apply (17.3), (17.6) and (17.7) to this $p_v$ over $F_v$; denote the resulting polynomials by $\mathcal R_v,V_v,\Delta_v$. The factorization and the derivatives are taken after fixing the actual chain, not by specializing a squarefree factorization chosen for algebraically independent velocities.

The source rows are [Wallner, Krupke, Schmidt and Fekete, arXiv:2608.27085v1, §IV.A and §IV.B.1](https://arxiv.org/html/2608.27085v1#S4). Their centered $u$ is $z$, their $M$ is $U=A^{-1}B$, their $M_\alpha$ is $T=A^{-1}B_\alpha$, and their pair count is $m=n-1$. In the repository definitions `A`, `B`, `Balpha`, `Malpha` of [TokenDampedSweepContraction](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.lean), pair $i$ and velocity $v_j$ have indices $i-1,j-1$; `Malpha` is this literal $T$. Its local weight `theta` is $(1+q)/2$. The complete [damped-sweep Scribe](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction.scribe.cs) has the same correspondence. The weighted form is the $Q$ in Definition 12.1 and [FinitePathDynamics](../../../D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.lean), with its [Scribe](../../../Blueprint/D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.scribe.cs). These are the original-row and contraction premises used below.

**Theorem 18.2 (Finite exact value and every original optimizer).** For every actual chain in Definition 18.1, the polynomial $\Delta_v\in F_v[q]$ is nonzero. Put $L_v=\deg\Delta_v$ and define the polynomial in the unchanged original damping parameter

$$
\begin{aligned}
d_v(\alpha)&=v_2+\alpha v_1,\\
n_v(\alpha)&=\alpha(v_1+2v_2)-v_2,\\
\Xi_v(\alpha)&=d_v(\alpha)^{L_v}
                     \Delta_v\bigl(n_v(\alpha)/d_v(\alpha)\bigr),\\
\mathcal Y_v(X,\alpha)&=d_v(\alpha)^{2m}
                     \mathcal R_v\bigl(X,n_v(\alpha)/d_v(\alpha)\bigr).
\end{aligned}
\tag{18.5}
$$

The powers clear all denominators, so $\Xi_v\in F_v[\alpha]$ and $\mathcal Y_v\in F_v[X,\alpha]$. They satisfy

$$
\Xi_v\ne0,\qquad
1\leq\deg\Xi_v\leq L_v\leq8m^3-4m<8m^3.
\tag{18.6}
$$

The original interior candidate set

$$
C_v^\alpha=\{a\in\mathbb R:0<a<1,\ \Xi_v(a)=0\}
\tag{18.7}
$$

is finite and nonempty. For each $a\in C_v^\alpha\cup\{0,1\}$, define solely by ordered real roots

$$
\begin{aligned}
S_v(a)&=\max\{x\in\mathbb R:x\geq0,\ \mathcal Y_v(x,a)=0\},\\
S_v^*&=\min_{a\in C_v^\alpha}S_v(a),\\
\gamma_v^\alpha&=\text{the nonnegative real root of }Y^2-S_v^*=0,\\
\mathcal A_v&=\{a\in C_v^\alpha:S_v(a)=S_v^*\}.
\end{aligned}
\tag{18.8}
$$

Each maximum exists. These expressions determine the actual value and the entire fixed-map optimizer set on the full original domain:

$$
\boxed{\quad
\gamma_v^\alpha=\min_{0\leq\alpha\leq1}\rho(A^{-1}B_\alpha)=\gamma_v,
\qquad
\mathcal A_v=\operatorname*{argmin}_{[0,1]}
                          \rho(A^{-1}B_\alpha).
\quad}
\tag{18.9}
$$

In particular $\mathcal A_v$ contains every optimizer, has between one and $8m^3-4m$ elements, and is contained in $(0,1)$. Every element of $\mathcal A_v$, and the minimum value, is algebraic over the actual field $F_v$. In normalized coordinates the corresponding complete answer is

$$
\begin{aligned}
C_v^q&=\{c\in(-1,1):\Delta_v(c)=0\},\\
Q_v&=\{c\in C_v^q:
       \max\{x\geq0:\mathcal R_v(x,c)=0\}=S_v^*\},\\
\mathcal A_v&=\{\alpha_v(c):c\in Q_v\}.
\end{aligned}
\tag{18.10}
$$

At every parameter, the entire complex spectrum with algebraic multiplicity remains the multiset of roots of (18.4), with $q=q_v(\alpha)$. No roots are removed from that spectral specification by the reduced polynomial $V_v$.

*Proof.* First verify the polynomial and the literal operator. An odd row of $A$ is its coordinate row, and an even row has diagonal $s_i$ and off-diagonal entries only in odd columns. Ordering the odd coordinates before the even coordinates therefore makes $A$ block lower triangular, with identity in the odd block and diagonal entries $s_i$ in the even block. Simultaneously permuting rows and columns leaves its determinant unchanged. Hence

$$
\det A=\prod_{i\ {\rm even}}s_i>0.
\tag{18.11}
$$

This verifies the denominator in (18.4), including an empty even block and the scalar case. All entries are in $F_v$. Equations (16.1)–(16.2), already established for these exact rows, identify $\mathcal B_v(q)=B_{\alpha_v(q)}$. In particular

$$
p_v(Z,q)=\det\bigl(ZI-A^{-1}B_{\alpha_v(q)}\bigr).
\tag{18.12}
$$

Only the first row of $Z A-\mathcal B_v(q)$ depends on $q$, and that row depends affinely on $q$. Multilinearity of the determinant shows that $p_v(Z,q)$ is affine in $q$. Its coefficient of $Z^m$ is $\det A/\det A=1$, independently of $q$, so it has precisely the form (17.1) with $d=m$. The determinant identity (13.8) also gives, with all parity signs retained,

$$
\det U=(-1)^m,\qquad
\det T_{v,q}=(-1)^m q,\qquad p_v(0,q)=q.
\tag{18.13}
$$

These identities in particular show that the affine dependence is not constant. They do not require a nonzero $q$.

The hypotheses of Assumption 17.2 follow from the supporting fixed-map results, not from a change of spectral objective. More explicitly, retain the same positive definite Hermitian form and first normal as in Definition 12.1:

$$
Q(z)=\sum_{j=1}^{m+1}\frac{|z_j-z_{j-1}|^2}{v_j},
\qquad P_1z=f_1\langle f_1,z\rangle_Q.
$$

The source reflection and sweep identities, in the normalization already proved in (12.7) and (16.11), are

$$
T_{v,q}=U\bigl(I-(1-q)P_1\bigr),\qquad
U^\dagger U=I,\qquad
Q(T_{v,q}z)=Q(z)-(1-q^2)|\langle f_1,z\rangle_Q|^2.
\tag{18.14}
$$

At $q=1$ the second factor is the identity; at $q=-1$ it is a $Q$-orthogonal reflection. Thus both endpoint transfers preserve this very same $Q$, and every complex eigenvalue there has modulus one. For $-1<q<1$, the exact bijection (18.3) gives $0<\alpha_v(q)<1$, and Theorem 13.2 gives $\rho(T_{v,q})<1$. Equivalently this is the qualitative `result` of the damped-sweep source in Definition 18.1, whose proof uses the complete private local loss, reflection, source factorization and boundary-rigidity intermediates. These statements have every positive velocity, both zero endpoints, every dimension $m\geq1$, and one fixed interior parameter as their hypotheses. They are exactly the hypotheses needed here.

Consequently Theorem 17.3 applies over $F_v$ to (18.4). It proves that $\Delta_v$ is nonzero, that

$$
1\leq L_v\leq8m^3-4m,
\tag{18.15}
$$

and that $C_v^q$ contains all normalized optimizers. Its construction concerns the actual entries of the entire original transfer, including their coupling to the damped first row. It does not replace them by undamped spectral data.

The denominators in (18.3) are positive on their closed intervals: $d_v(\alpha)\geq v_2>0$ for $\alpha\in[0,1]$, and $v_1+2v_2-v_1q\geq2v_2>0$ for $q\in[-1,1]$. As proved in (16.10), $q_v$ and $\alpha_v$ are mutually inverse increasing bijections, taking endpoints to endpoints. A polynomial of $q$ degree at most $L_v$ becomes a polynomial in $\alpha$ after multiplication by $d_v^{L_v}$, of degree at most $L_v$. This proves the polynomial assertion for $\Xi_v$. It is nonzero: substitution by a fractional linear transformation with the rational inverse (18.3) is an injective map of rational function fields. If $\Xi_v$ vanished identically, substituting the inverse would make the nonzero polynomial $\Delta_v$ vanish identically. Positivity of $d_v$ then gives the exact set equality

$$
C_v^\alpha=\{\alpha_v(c):c\in C_v^q\}.
\tag{18.16}
$$

Thus this candidate set is finite and nonempty. In particular $\Xi_v$ has a real root and has positive degree, completing (18.6).

By (17.11), $\deg_q\mathcal R_v\leq2m$, so the second denominator clearance in (18.5) also yields a polynomial. Its $X$-leading coefficient at a real $a\in[0,1]$ is $d_v(a)^{2m}>0$. Multiplication by this positive scalar changes none of its $X$ roots. The exact identity (17.12) now says that these roots, with multiplicities, are

$$
\mu_i(q_v(a))\mu_j(q_v(a)),\qquad 1\leq i,j\leq m,
\tag{18.17}
$$

where $\mu_1,\ldots,\mu_m$ are all roots of the actual characteristic polynomial (18.12). By (17.9), the largest nonnegative real root is therefore exactly

$$
S_v(a)=\rho(A^{-1}B_a)^2.
\tag{18.18}
$$

This is an equality with the original spectral radius, not a norm bound. Every global minimizing original parameter belongs to $C_v^\alpha$ by (18.16), and every candidate remains in the original admissible interval. Comparing their finitely many exact ordered roots proves (18.8)–(18.9), including the entire set rather than a selector. The endpoint comparisons are $S_v(0)=S_v(1)=1$, while an interior value is strictly less than one. Hence adding both endpoints to the finite comparison would give precisely the same minimum and optimizer set.

Each root $a$ of $\Xi_v$ is algebraic over $F_v$. At such an $a$, (18.5) is a nonzero polynomial of fixed positive $X$ degree with coefficients in $F_v(a)$, so $S_v(a)$ is algebraic over that field. Transitivity of algebraicity, as cited in Theorem 17.3, proves algebraicity over $F_v$ of every compared value, of $S_v^*$, and of its nonnegative square root. Rational substitution by (18.3) gives the corresponding assertion for all elements of $Q_v$. The ordered-root definitions use the fixed real embedding of $F_v$ and its algebraic extensions; they require no assumption that arbitrary real input data have an effective presentation.

Finally, (18.12) supplies all $m$ eigenvalues at every fixed parameter, with algebraic multiplicity as in (16.3). The auxiliary polynomial $\mathcal R_v$ records their products to express the maximum modulus, and $V_v$ is used only in the critical-parameter proof. Neither is a substituted transfer operator. No eigenvalue has been discarded from $p_v$, and no power with a varying parameter has entered the argument. This proves the full original-operator assertion. $\square$

## 19. Singular, repeated and exceptional specializations

**Theorem 19.1 (Specialization and the zero-radius branch of the complete answer).** The description in Theorem 18.2 holds separately for each positive chain, including every coefficient specialization, and has the following precise boundary properties.

At either original endpoint the complete multiset is still given by (18.4) and every root has modulus one. No endpoint is an optimizer. The only singular original parameter is

$$
\alpha_* =\frac{v_2}{v_1+2v_2},\qquad q_v(\alpha_*)=0.
\tag{19.1}
$$

It belongs to the permitted interior domain, and none of the finite constructions excludes it. The actual minimum is zero exactly on the already evaluated finite-annihilation branch:

$$
\boxed{\quad
\gamma_v=0\quad\Longleftrightarrow\quad\mathcal D(v)=1.
\quad}
\tag{19.2}
$$

In that branch

$$
Q_v=\{0\},\qquad \mathcal A_v=\{\alpha_*\},\qquad
p_v(Z,0)=Z^m,
\tag{19.3}
$$

and the original map at $\alpha_*$ has least all-state annihilation time $m$. For $m=1$ this gives $\gamma_v=0$ and the unique original optimizer $\alpha_*$ for every positive pair. Outside the zero-radius branch the comparison in (18.8) retains every minimizer, without an assertion that there is only one.

Repeated eigenvalues, collisions of distinct product roots, nonreal conjugate pairs, and either parity of $m$ require no additional hypotheses in these assertions. The full-data answer does not make $Q_v$ or $\gamma_v$ a function of the observation $\mathsf O(v)$ in (16.5), even when that observation includes the entire original map $\alpha\mapsto q_v(\alpha)$.

*Proof.* Endpoint preservation and the endpoint radii follow from the exact factorization (18.14), as used in Theorems 15.1, 16.2 and 18.2. A finite nonempty complex spectrum of a positive definite $Q$-isometry has all eigenvalue moduli one, including repeated eigenvalues; an eigenvector gives the equality directly. A fixed interior parameter has radius strictly below one. This proves exclusion of both endpoints without deleting their characteristic polynomials from the spectral specification.

Equation (18.13) proves that singularity is equivalent to $q=0$. The inverse correspondence (18.3) then gives (19.1), with $0<\alpha_*<1$ by positivity. The determinant formula (18.4), the product formula (17.12), factorization into actual monic factors, differentiation and the real-root comparisons involve no inverse of $T_{v,q}$, no reciprocal of $q$, and no reciprocal of an eigenvalue. Formula (17.12) explicitly treats a zero eigenvalue. Hence the singular map is present with all its zero-root multiplicities.

If $\gamma_v=0$, take any minimizing parameter, whose existence is already proved. Every root of its monic characteristic polynomial must have modulus zero, so that polynomial is $Z^m$. Its constant term is $q$ by (18.13), forcing $q=0$. The Cayley–Hamilton theorem then gives $T_{v,0}^m=0$. The exact nilpotence criterion of Theorem 13.2 says that this occurs if and only if $q=0$ and $\mathcal D(v)=1$, with least all-state annihilation time $m$. Conversely $\mathcal D(v)=1$ gives $T_{v,0}^m=0$ by that same supporting theorem, so the spectral radius at zero is zero and is necessarily the minimum. If $q\ne0$, the determinant is nonzero, so its spectral radius cannot be zero. Thus zero is the only normalized optimizer in this branch, and bijectivity of (18.3) proves (19.3). This uses the already published criterion and evaluated product (12.3), not a new restriction on the velocity chain.

In the scalar case, reuse the exact identity $p_v(Z,q)=Z+q$ in (16.12). Definitions (17.3), (17.6) and (17.7) give directly

$$
\mathcal R_v(X,q)=V_v(X,q)=X-q^2,\qquad
\Delta_v(q)=-2q,\qquad
\Xi_v(\alpha)=-2\bigl(\alpha(v_1+2v_2)-v_2\bigr).
\tag{19.4}
$$

Thus the finite comparison indeed has the sole original candidate $\alpha_*$ and gives the actual minimum zero, agreeing with the existing scalar and nilpotent conclusions. These identities also include both scalar endpoints. In every dimension the parity sign in $\det T=(-1)^m q$ is canceled by the sign in the constant coefficient $\det(-T)$, so $p_v(0,q)=q$ for both parities. No odd or even factor of the original characteristic polynomial has been removed in forming (18.4).

For the remaining specializations, fix the actual velocities first. The real field $F_v$ still has characteristic zero, and the polynomial (18.4) is still monic, affine in $q$, with unit-circle endpoints and strict interior roots. The nonvanishing argument (17.16)–(17.17) is therefore valid for that actual polynomial, regardless of any extra coefficient equalities. If an irreducible factor occurs to higher multiplicity for this chain, its multiplicity is retained in $\mathcal R_v$ and it occurs once in $V_v$. If distinct factors or roots collide at a particular parameter, their product may have $V_{v,X}=0$ there; that is the first resultant alternative in (17.7). If $V_{v,X}\ne0$ at a minimizing squared radius, (17.20)–(17.21) give the second alternative using only the actual continuous squared radius. The argument does not assume that the original eigenvalues are differentiable, simple, or diagonalizable. It applies as well at a zero squared radius. The product formula uses conjugation of the entire real-coefficient root multiset to supply an actual $|\mu|^2$, and bounds every other real nonnegative product by the same actual maximum. Nonreal eigenvalues therefore enter with their full multiplicities rather than being omitted from the objective.

It follows that no exceptional positive chain invalidates the candidate polynomial by forcing it identically to zero: the squarefree factorization and the proof of its two nonzero resultants are performed anew for the specified actual coefficients. There is no assertion that taking squarefree parts or resultants for an indeterminate velocity family and subsequently specializing would preserve their nonvanishing. It is precisely the definition in the actual field that gives the stated all-chain result.

Finally, the two actual chains (16.6) have identical observations, even augmented as in Corollary 16.3, but their entire optimizer sets and minimum values are different. The polynomial (18.4) uses their distinct full first-row-to-tail couplings and so is not required to coincide on that observational fiber. Equations (18.8)–(18.10) consequently preserve both answers in (16.9) and the insufficiency conclusion of Corollary 16.3. All statements here concern a fixed original map at each spectrum or power. The mixed histories and physical collision conditions retain their separate domains. $\square$

## 追加锚（本行以下为增补区）
