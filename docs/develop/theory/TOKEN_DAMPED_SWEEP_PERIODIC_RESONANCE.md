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

