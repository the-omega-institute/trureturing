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
