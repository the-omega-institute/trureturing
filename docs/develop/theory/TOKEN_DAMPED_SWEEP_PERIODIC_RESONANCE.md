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
