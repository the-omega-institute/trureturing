# FIB shared Gaussian instruments and indexed record-law fibres

## 1. Original worlds, histories and the two terminal alternatives

**Definition 1.1 (The complete original domain).** Let $\mathcal W$ consist of all triples $W=(P,g,d)$ with

$$
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),\qquad
g(t)=\sum_{k=0}^3a_kt^k\ne0,\qquad d\in\mathbb R.
$$

The equation $g\ne0$ means that its four coefficients are not all zero. In particular all degrees from zero to three, sampled zeros, repeated roots and zero drift are included. There is no upper bound on $b,c$, the coefficients or $d$. The matrix $P$ has strictly positive real entries, trace one and rank one. It is a real program matrix; it need not be symmetric and is not assumed to be a quantum density operator.

The original actions and deterministic mathematical responses are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I_2,\quad Q_i=E_iQ_{i-1},\quad
y_i(W)=d+g(i)\operatorname{tr}(Q_iP).
$$

A word $E_1\cdots E_t$ is chronological, so $Q_i=E_i\cdots E_1$. One complete $P$, one whole polynomial $g$ and one fixed $d$ are used at every clock and in every alternative continuation. These are the definitions of [Common Parent, Definition 1.1](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md) and [Strict Real, Definition 1.1](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md). The acquisitions have their original clocks $0,\ldots,7$, including the initial read and a read immediately after each executed action. No additional outward acquisition is part of this definition.

**Definition 1.2 (Entire histories and the original joint relation).** For a history $H=(h_0,E_1,h_1,\ldots,E_t,h_t)$ define

$$
\mathcal F(H)=
\{W\in\mathcal W:(y_0(W),\ldots,y_t(W))=(h_0,\ldots,h_t)\}.
$$

In the notation of [Common Parent, Definitions 1.1–1.3](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), set

$$
H_4=(0,J,24,M,147/5,J,24,M,18),\qquad
C(p,v)=\mathcal F(H_4,M,p,M,v),\qquad
h(p,v)=(0,24,147/5,24,18,p,v).
$$

The acquired actions for this child are $J,M,J,M,M,M$. The strict-real joint question uses $p\ne24$, as in [Strict Real, Definitions 1.1–1.2](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md). The set $\mathcal F(H_4,M,p,M,v)$ itself is also meaningful at $p=24$.

Write

$$
j=b+c,\qquad n=j+r,\qquad T=1+b,\qquad U=1+2b.
$$

After the acquired sixth $M$, the seventh-clock alternatives on the same world are

$$
f_{MJ}(W)=d+(T+2j+4r)g(7),\qquad
f_{MM}(W)=d+(3U+2n)g(7).
$$

They are the functions denoted $a(W)$ and $m(W)$ in [Strict Real III, Definition 1.1](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md) and [Strict Real IV, Definition 1.1](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md). Define

$$
\begin{aligned}
D_J&=\{(p,v):p\ne24,\ \exists W_0\ne W_1\in C(p,v),\
f_{MJ}(W_0)=f_{MJ}(W_1)\},\\
D_M&=\{(p,v):p\ne24,\ \exists W_2\ne W_3\in C(p,v),\
f_{MM}(W_2)=f_{MM}(W_3)\}.
\end{aligned}
$$

The joint relation is $D_J\cap D_M$. Both pairs use one entire child, including worlds unused by the chosen pairs. The pairs may differ or overlap, and their common terminal values may differ. Each run executes only one seventh action.

**Definition 1.3 (Original recursive predicates and three observation levels).** For $S\subseteq\mathcal F(H)$, retain [Common Parent, Definition 1.2](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md):

$$
\begin{aligned}
L_0(S,H)&\iff |S|\ge2,\\
L_{k+1}(S,H)&\iff |S|\ge2\ \land\
\bigwedge_{E\in\{J,M\}}\exists u\in\mathbb R:\ 
L_k(S\cap\mathcal F(H,E,u),(H,E,u)).
\end{aligned}
$$

Here $k$ is restricted to the remaining original acquisition horizon. Cardinality counts complete worlds. A shared acquired response is selected before taking its alternative continuations.

For a fixed chronological word $w$, let $y_w(W)$ be its entire deterministic response vector, including clock zero. A population-law interface assigns to each labelled world a probability law $\nu_w(W)$ of a random vector $R_w$. The vector $y_w(W)$, the law $\nu_w(W)$, and a realized acquisition $R_w$ are three different mathematical objects. Equality of population laws will be used as a relation on the indexed family $W\mapsto\nu_w(W)$.

## 2. An injective normal-state program for every original world

**Assumption 2.1 (Carrier and preparation contract).** Use the complex Schrödinger space

$$
\mathcal H=L^2(\mathbb R^{17},dx;\mathbb C),\qquad
q_a\psi(x)=x_a\psi(x),\qquad
\pi_a\psi(x)=-i\partial_a\psi(x),\qquad \hbar=1.
$$

Seventeen counts system modes, equivalently position coordinates. The Hilbert space is infinite dimensional. No minimum number of modes is assumed.

Use column vectorization $\operatorname{vec}(X)=(X_{11},X_{21},X_{12},X_{22})^T$. For each original $W$ supply the preparation

$$
m_W=(d,\operatorname{vec}(a_0P),\operatorname{vec}(a_1P),
\operatorname{vec}(a_2P),\operatorname{vec}(a_3P))\in\mathbb R^{17},
$$

$$
\psi_W(x)=\pi^{-17/4}\exp\!\left(-\frac{\|x-m_W\|^2}{2}\right),
\qquad
\rho_W=|\psi_W\rangle\langle\psi_W|.
$$

Availability is assumed for this specified family of initial preparations. No transformation extracting $m_W$ from an unknown original carrier, world-identification measurement, preparation algorithm or preparation cost is included in the assumption. The coefficients enter the initial state, rather than a world-dependent choice of subsequent apparatus.

**Theorem 2.2 (Faithful preparation of the full FIB domain).** Under Assumption 2.1, every $\rho_W$ is a normal pure state. The map $\iota:W\mapsto\rho_W$ is injective on all of $\mathcal W$, including every lower degree and every sampled-zero stratum. The initial position and momentum means and covariances are

$$
\mathbb E_W q=m_W,\qquad \mathbb E_W\pi=0,\qquad
\operatorname{Cov}_W(q)=\operatorname{Cov}_W(\pi)=I_{17}/2,
$$

with zero symmetrized position–momentum cross covariance. For any $W,W'$,

$$
\langle\psi_W,\psi_{W'}\rangle
=\exp\!\left(-\frac{\|m_W-m_{W'}\|^2}{4}\right).
$$

For the unit-frequency oscillator $H_{\rm osc}=\frac12\sum_{a=1}^{17}(q_a^2+\pi_a^2)$, every preparation has finite energy

$$
\operatorname{tr}(\rho_WH_{\rm osc})
=\frac{17}{2}+\frac{\|m_W\|^2}{2}.
$$

There is no uniform energy bound over $\mathcal W$.

Proof. The squared wavefunction is $\pi^{-17/2}\exp(-\|x-m_W\|^2)$, a product of seventeen normalized real Gaussian densities of variance $1/2$. Thus its integral is one and the rank-one operator $\rho_W$ is positive trace class of trace one. Differentiation gives the stated momentum moments; the wavefunction is real, so the symmetrized cross covariances vanish. Completing the square in the overlap integral gives the displayed overlap.

To recover a world from its mean, reshape each four-coordinate block as $X_k=a_kP$. Then $\operatorname{tr}(X_k)=a_k$, since $\operatorname{tr}P=1$. Recover all four coefficients by these traces, choose any nonzero coefficient, and set $P=X_k/a_k$. Such a coefficient exists because $g$ is not the zero polynomial. The first coordinate recovers $d$. This uses no division by a sampled $g(i)$, so degree drops and sampled zeros do not affect injectivity. Distinct means have overlap strictly between zero and one; in particular their pure density operators differ. The energy follows by summing the second moments. Holding $P,g$ fixed and letting $|d|\to\infty$ proves absence of a uniform bound. These recovery identities are mathematical identities for the indexed preparation; nonorthogonality prevents treating them as perfect single-specimen world-label access. $\square$

## 3. Shared actions and the actual original word

**Definition 3.1 (Fixed controls and clock readouts).** Split a position vector as $x=(x_d,\operatorname{vec}X_0,\ldots,\operatorname{vec}X_3)$. For $E\in\{J,M\}$ put

$$
B_E=I_2\otimes E,\qquad
A_E=\operatorname{diag}(1,B_E,B_E,B_E,B_E).
$$

Thus $A_E$ leaves $x_d$ unchanged and sends every $X_k$ to $EX_k$. For the matrices generated by these controls, choose the explicit half-density pullback

$$
(U_A\psi)(x)=|\det A|^{-1/2}\psi(A^{-1}x).
$$

For each original clock $i=0,\ldots,7$, set $t_0=\operatorname{vec}(I_2)=(1,0,0,1)^T$ and

$$
\ell_i^T=(1,t_0^T,i\,t_0^T,i^2t_0^T,i^3t_0^T),
\qquad F_i(q)=\ell_i^Tq.
$$

In this formula the coefficient of the first matrix block is one also at $i=0$. All coefficients depend only on the original clock, and $U_J,U_M$ depend only on the chosen local action.

**Theorem 3.2 (Original FIB action and readout correspondence).** With the preparation of Theorem 2.2 and the controls of Definition 3.1, chronological actions $E_1,\ldots,E_i$ have the chosen implementer $U_{T_i}$, where

$$
T_0=I_{17},\qquad T_i=A_{E_i}\cdots A_{E_1}.
$$

They act on each program block by the original $Q_i=E_i\cdots E_1$. Their position readout row in initial coordinates is

$$
L_i=\ell_i^TT_i
=(1,\operatorname{vec}(Q_i^T)^T,
i\,\operatorname{vec}(Q_i^T)^T,
i^2\operatorname{vec}(Q_i^T)^T,
i^3\operatorname{vec}(Q_i^T)^T),
$$

and $L_im_W=y_i(W)$ for every original world.

The representation tool is literature-attested: [Arvind, Dutta, Mukunda and Simon, quant-ph/9509002v3](https://arxiv.org/pdf/quant-ph/9509002v3), Eqs. (2.8), (4.7) and (6.6a), give the finite-mode Schrödinger orientation, the embedding $A\mapsto\operatorname{diag}(A,A^{-T})$, and the corresponding pullback. The same half-density and cotangent-lift structures are used in [Symplectic Predictive Completion, §§1.1–1.2](SYMPLECTIC_PREDICTIVE_COMPLETION.md). The block program and the following original-word correspondence are a source-dependent application of these structures.

Proof. Column vectorization gives $\operatorname{vec}(EX)=(I_2\otimes E)\operatorname{vec}X$. Hence products of the $A_E$ act by the required left products on every block. Each $E$ is invertible with determinant $-1$, so $\det B_E=(\det E)^2=1$ and $\det A_E=(\det E)^8=1$. For these matrices apply the cited finite-mode tool with the explicitly chosen pullback of Definition 3.1. Its exact formulas are

$$
U_A^\dagger qU_A=Aq,\qquad
U_A^\dagger\pi U_A=A^{-T}\pi,\qquad
U_AU_B=U_{AB}.
$$

The last equality has the order $B^{-1}A^{-1}=(AB)^{-1}$ in its wavefunction argument. Consequently the chronological product is exactly $U_{T_i}$. These formulas concern this chosen $GL$ subgroup; they make no phase choice for the full symplectic group.

For every $2\times2$ matrix $X$,

$$
\operatorname{tr}(Q_iX)=\operatorname{vec}(Q_i^T)^T\operatorname{vec}X.
$$

Substitute $X=a_kP$ into the row $L_i$ to obtain
$L_im_W=d+\sum_{k=0}^3i^ka_k\operatorname{tr}(Q_iP)=y_i(W)$. The same initial coefficient blocks are used at every clock, including clocks where $g(i)=0$. $\square$

**Proposition 3.3 (The complete original product table).** The products needed for the acquired prefix and its original sixth- and seventh-action alternatives are the following. All traces are against the original $P$ of Definition 1.1.

| Clock | Chronological word | $Q_i$ | $\operatorname{tr}(Q_iP)$ |
| --- | --- | --- | --- |
| $0$ | empty | $\begin{pmatrix}1&0\\0&1\end{pmatrix}$ | $1$ |
| $1$ | $J$ | $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ | $j$ |
| $2$ | $JM$ | $\begin{pmatrix}1&0\\1&1\end{pmatrix}$ | $T$ |
| $3$ | $JMJ$ | $\begin{pmatrix}1&1\\1&0\end{pmatrix}$ | $n$ |
| $4$ | $JMJM$ | $\begin{pmatrix}1&0\\2&1\end{pmatrix}$ | $U$ |
| $5$ | $JMJMM$ | $\begin{pmatrix}2&1\\3&1\end{pmatrix}$ | $U+n$ |
| $6$ | $JMJMMJ$ | $\begin{pmatrix}3&1\\2&1\end{pmatrix}$ | $T+j+2r$ |
| $6$ | $JMJMMM$ | $\begin{pmatrix}3&1\\5&2\end{pmatrix}$ | $2U+n$ |
| $7$ | $JMJMMJJ$ | $\begin{pmatrix}2&1\\3&1\end{pmatrix}$ | $U+n$ |
| $7$ | $JMJMMJM$ | $\begin{pmatrix}2&1\\5&2\end{pmatrix}$ | $2U+j$ |
| $7$ | $JMJMMMJ$ | $\begin{pmatrix}5&2\\3&1\end{pmatrix}$ | $T+2j+4r$ |
| $7$ | $JMJMMMM$ | $\begin{pmatrix}5&2\\8&3\end{pmatrix}$ | $3U+2n$ |

Proof. Start from $Q_0=I_2$ and multiply each successive row on the left by its last action. For $Q=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}$, its trace against $P$ is $\delta+(\alpha-\delta)r+\beta c+\gamma b$. Substitution gives the displayed traces, agreeing with [Common Parent, Definition 1.3](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md). The two sixth-action rows and four seventh-action rows name alternatives; they do not request multiple reads at one original clock. $\square$

**Proposition 3.4 (Shared squeezing, with no success normalization).** The FIB $M$ control changes position covariance even though $\det A_M=1$. For a state with finite position covariance $\Sigma$, the control sends it to $A_M\Sigma A_M^T$. In particular the image of the initial covariance $I_{17}/2$ is $A_MA_M^T/2\ne I_{17}/2$.

Proof. Use the adjoint position formula in Theorem 3.2 and take centered second moments. On each two-coordinate column of a matrix block,

$$
MM^T=\begin{pmatrix}1&1\\1&2\end{pmatrix}\ne I_2.
$$

Its eigenvalues are $(3+\sqrt5)/2$ and $(3-\sqrt5)/2$. The associated full canonical transformation has the inverse-transpose momentum action. Thus the control produces squeezing; determinant one removes the Jacobian prefactor but does not preserve Euclidean covariance. The state update is unitary and requires no outcome selection or success division. $\square$

## 4. A normal instrument at every original acquisition

**Assumption 4.1 (Internal probes and position dynamics).** Fix a common $\sigma>0$. Supply eight independent internal probes, prepared in advance in the same state

$$
k_\sigma(z)=(2\pi\sigma^2)^{-1/4}
\exp\!\left(-\frac{z^2}{4\sigma^2}\right)\in L^2(\mathbb R).
$$

Each probe has zero position and momentum means, position variance $\sigma^2$ and momentum variance $1/(4\sigma^2)$, hence finite oscillator energy for fixed $\sigma>0$. The probes are independent of the initial system and of one another. At clock $i$, after the prescribed control when $i>0$, the available coupling and meter are

$$
\mathsf B_i=\exp(-iF_i(q)\otimes\pi_i^{\rm pr}),\qquad
Z_i^{\rm pr}.
$$

The coupling translates probe position by $F_i(q)$. Its scalar prototype and signs are those of [Ozawa, quant-ph/0210044v2, §VI, Eqs. (36)–(38)](https://arxiv.org/pdf/quant-ph/0210044v2). Here $F_i(q)=\ell_i^Tq$ is the explicit multivariate substitution. These ideal couplings, probe-position measurements and the specified initial preparations are availability assumptions. There is no additional free evolution that changes the system positions between them.

Every meter value is retained. Each probe is used once; no probe or system is reset during the run. The probes add internal degrees of freedom but only the original outward readings $0,\ldots,7$ are produced. No copy of an unknown input, additional gain or source-label port, skipped read or postselection is supplied.

**Theorem 4.2 (The shared FIB Gaussian instrument).** Under Assumptions 2.1 and 4.1, the same apparatus for every $W\in\mathcal W$ defines a normal completely positive, ultraweakly countably additive instrument at each original clock. For a Borel outcome set $B\subseteq\mathbb R$ its Schrödinger map is

$$
\mathcal I_{i,E}(B)(\rho)
=\int_B K_i(z)U_{A_E}\rho U_{A_E}^\dagger K_i(z)^\dagger\,dz,
\qquad
K_i(z)=k_\sigma(z-F_i(q)).
$$

Clock zero uses $U=I$; the notation $E$ at later clocks means that clock's executed action. Whole-outcome integration preserves trace. The integral is defined by the normal instrument, or equivalently by trace pairings, without an operator-norm integral over the outcome line.

Proof. For each $z$, $K_i(z)$ is a bounded positive multiplication operator. Its norm is at most $(2\pi\sigma^2)^{-1/4}$, which need not be at most one. A Kraus density at one real outcome is not required to be a contraction.

For each $x$, normalization of the probe gives

$$
\int_{\mathbb R}|k_\sigma(z-\ell_i^Tx)|^2\,dz=1.
$$

Define

$$
(V_i\psi)(x,z)=k_\sigma(z-\ell_i^Tx)\psi(x),
\qquad
V_i:\mathcal H\longrightarrow\mathcal H\otimes L^2(\mathbb R).
$$

Tonelli's theorem gives $\|V_i\psi\|=\|\psi\|$, so $V_i$ is an isometry. Let $P_B$ be multiplication by $1_B$ on the probe space. For any bounded system observable $O$ define

$$
\mathcal I_{i,E}(B)^*(O)
=U_{A_E}^\dagger V_i^\dagger(O\otimes P_B)V_iU_{A_E}.
$$

The tensor embedding $O\mapsto O\otimes P_B$ is normal and completely positive, as is compression by $V_iU_{A_E}$. For disjoint $B_n$, the projections $P_{\cup B_n}$ are the strong sum of the $P_{B_n}$, so the compressed maps are countably additive ultraweakly. At $B=\mathbb R$ and $O=I$, the result is $I$ by the isometry. The normal predual therefore has the stated complete positivity, countable additivity and whole-outcome trace preservation.

For rank-one trace-class inputs, taking matrix elements in the probe coordinate gives the displayed Kraus expression. Positive trace-class inputs follow by their summable spectral decomposition and Tonelli; general trace-class inputs follow by linearity. Equivalently, the normalization identity for $\int K_i(z)^\dagger K_i(z)\,dz$ holds as quadratic forms and strong integrals over increasing bounded outcome sets. No operator-norm convergence over $\mathbb R$ is used.

In the position representation the coupling of Assumption 4.1 acts by
$\Psi(x,z)\mapsto\Psi(x,z-\ell_i^Tx)$. Applied to $\psi(x)k_\sigma(z)$ it gives exactly $V_i\psi$. It fixes every $q_a$, sends the probe pointer to $Z_i^{\rm pr}+F_i(q)$, and sends $\pi_a$ to $\pi_a-\ell_{i,a}\pi_i^{\rm pr}$. This is the specified FIB substitution in Ozawa's probe model, not an assertion that the cited scalar equations already contain this sequential FIB instrument. $\square$

**Proposition 4.3 (Position preservation and selective disturbance).** Let $\mathcal D_i$ be the whole-outcome readout channel of Theorem 4.2 with the control omitted. For every bounded Borel function $f:\mathbb R^{17}\to\mathbb C$,

$$
\mathcal D_i^*(f(q))=f(q).
$$

Consequently the entire system position spectral distribution, including all finite first and second position moments, is preserved by the nonselective readout. An individual selective update need not preserve it.

Proof. Multiplication operators obey $(f(q)\otimes I)V_i=V_if(q)$. Compressing by $V_i$ gives the bounded identity. Equality of expectations for all bounded Borel $f$ gives equality of position probability measures. Integrate truncations of $x_a^2$ and then the positive and negative parts of $x_a$ against those measures to extend the identity to finite moments. This is an extension through spectral measures, not application of a bounded-observable channel to an unbounded operator without a domain.

At a particular outcome $z$, the new position measure is proportional to
$|k_\sigma(z-\ell_i^Tx)|^2$ times its previous measure. This factor is generally nonconstant, so selective readout changes that measure. All initial Gaussians here are Schwartz functions; invertible linear pullbacks and finitely many Gaussian multipliers preserve that class. Thus every finite selective branch of this protocol has the moments used below. The nonselective mixtures have finite position moments by the distribution identity and the finite linear controls. The probe kick in Theorem 4.2 also shows why position preservation is not preservation of momentum or of the whole state. $\square$

**Proposition 4.4 (The retained fifth-read $M$–read–$M$ identity).** Write $\mathcal U_M(\rho)=U_{A_M}\rho U_{A_M}^\dagger$. The channel from just after read four to just before read six, when the fifth and sixth actions are $M$, is

$$
\Phi=\mathcal U_M\circ\mathcal D_5\circ\mathcal U_M.
$$

For every bounded Borel $f$,

$$
\Phi^*(f(q))
=\mathcal U_M^*\mathcal D_5^*\mathcal U_M^*(f(q))
=f(A_M^2q).
$$

On the finite-moment extension this gives $\Phi^*(q)=A_M^2q$. Including the sixth nonselective read gives
$(\mathcal D_6\circ\Phi)^*(q)=A_M^2q$ on the same extension.

Proof. Pullback by the final $M$ first gives $f(A_Mq)$. Proposition 4.3 leaves this bounded position function fixed under $\mathcal D_5^*$, and the preceding $M$ then gives $f(A_M^2q)$. Extend each coordinate by the finite-moment argument of that proposition. In the original matrix block,

$$
M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix},\qquad
M^2Q_4=\begin{pmatrix}3&1\\5&2\end{pmatrix}=Q_6.
$$

The fifth acquisition is part of the channel and of the record. Whole-outcome integration is its nonselective marginal, not deletion of that acquisition. The identity concerns adjoint maps on observables; the selective fifth update remains the outcome-dependent update of Proposition 4.3. $\square$

## 5. The joint law of the complete acquired word

**Theorem 5.1 (One shared latent vector for all original acquisitions).** Fix a chronological word $w=E_1\cdots E_t$ with $t\le7$, and execute every read $0,\ldots,t$ using Theorem 4.2. Stack the rows of Theorem 3.2 into $L_w\in\mathbb R^{(t+1)\times17}$. Then the entire actual record has law

$$
\nu_w(W)=\mathcal N_{t+1}(y_w(W),C_w),\qquad
C_w=\frac12L_wL_w^T+\sigma^2I_{t+1},\qquad
y_w(W)=L_wm_W.
$$

The covariance depends on the fixed word and $\sigma$, and is independent of $W$. Equivalently, a single latent vector and independent probe noises give the exact representation

$$
X\sim\mathcal N_{17}(m_W,I_{17}/2),\qquad
\epsilon\sim\mathcal N_{t+1}(0,\sigma^2I_{t+1}),\qquad
X\ \hbox{independent of }\epsilon,\qquad
R_w=L_wX+\epsilon.
$$

Thus every unconditional acquired mean equals its original deterministic response. In particular this holds for both complete words $JMJMMMJ$ and $JMJMMMM$ with the common acquired prefix $JMJMMM$ and the entire numeric prefix $h(p,v)$ of Definition 1.2.

Proof. Denote the sequential Kraus density by

$$
\mathsf K_w(z)
=K_t(z_t)U_{A_{E_t}}K_{t-1}(z_{t-1})\cdots
K_1(z_1)U_{A_{E_1}}K_0(z_0).
$$

The bounded functional calculus and Theorem 3.2 give
$U_{T_i}^\dagger K_i(z_i)U_{T_i}=k_\sigma(z_i-L_iq)$.
Induction on $i$ therefore gives

$$
\mathsf K_w(z)=U_{T_t}\prod_{i=0}^t k_\sigma(z_i-L_iq).
$$

Every factor in this last product is a multiplication operator in the same initial position vector, so all the factors commute. No factor for an intervening acquisition has been removed. Taking the squared norm on $\psi_W$ gives the joint density

$$
p_w(z\mid W)=
\int_{\mathbb R^{17}}\pi^{-17/2}e^{-\|x-m_W\|^2}
\prod_{i=0}^t
\frac{\exp(-(z_i-L_ix)^2/(2\sigma^2))}
{\sqrt{2\pi\sigma^2}}\,dx.
$$

Tonelli and each normalized noise factor give integral one over all $z$. This is exactly the density obtained from the single $X$ and the independent noises in the statement. In particular its characteristic function at $s\in\mathbb R^{t+1}$ is

$$
\exp\!\left(is^TL_wm_W-\frac14s^TL_wL_w^Ts
-\frac{\sigma^2}{2}s^Ts\right).
$$

This proves the Gaussian law, covariance and mean. The last mean identity is Theorem 3.2, including the original trace products of Proposition 3.3. $\square$

**Definition 5.2 (Mature Gaussian and word-response correspondences).** The Gaussian observation objects of [GaussianObservationLaw](../../../D5/S3/Observer/Linear/GaussianObservationLaw.lean), namely its action, ambient covariance, observation, input law and posterior kernel, correspond here to the centered latent $X-m_W$, observation matrix $L_w$, prior precision $\beta=2$ and noise precision $\tau=\sigma^{-2}$, followed by the translation $L_wm_W$. The Gaussian integration and conditioning used here belong to that mature observation setting. The concrete passage from the original FIB program, controls and all-acquisition Kraus factors to this matrix $L_w$ is the source-dependent derivation in Theorem 5.1.

The word residuals and finite matrix realizations of [WordHankelRealization](../../../D5/S3/Observer/Hankel/WordHankelRealization.lean) organize responses indexed by concatenated words. Here the concrete correspondence is chronological concatenation with $T_{uv}=T_vT_u$, and a readout row $\ell_{|uv|}^TT_{uv}$. The row is clock dependent. No stationary residual-rank or minimal-mode conclusion is supplied by this correspondence. Seventeen remains the number of coordinates in the explicit program.

The same-source requirement for Gaussian products and marginals in [Second Order Relation Completion, Assumption 14.1 and Theorems 14.2–14.3](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) is met in Theorem 5.1 by using one $X$ throughout. Its independently declared continuous Gaussian source is the relevant comparison; a tree composition is not thereby identified with this $X$.

**Proposition 5.3 (Selective history and the classical latent representation).** For a fixed word prefix with row matrix $L_A$ and an acquired vector $r$, the continuous conditional density of its initial latent position is Gaussian with

$$
B_A=(2I_{17}+\sigma^{-2}L_A^TL_A)^{-1},\qquad
\mu_A(W,r)=m_W+B_A\sigma^{-2}L_A^T(r-L_Am_W).
$$

This is also the initial-coordinate position density of the selective quantum branch. Every recorded joint law in Theorem 5.1 has an exact classical latent-Gaussian realization. It implies no nonclassicality or quantum advantage.

Proof. Multiply the initial density by every likelihood factor in the density of Theorem 5.1 and complete the square in $x$. The quadratic coefficient is $B_A^{-1}$ and the linear coefficient is $2m_W+\sigma^{-2}L_A^Tr$. This yields the stated covariance and mean. Pulling the selective Kraus density back by its final $U_{T_t}$ gives those same factors multiplying $\psi_W$, whose squared modulus is the density just computed. The world label, including its fixed $d$ and whole $g$, is unchanged; conditioning changes the internal position density rather than those original parameters.

Equivalently, in the common system-and-probe dilation the final pointers, expressed in initial observables, are $L_iq+Z_i^{\rm pr}$. Each control uses only $q$ in its position action; every probe coupling fixes $q$ and kicks only momentum. With no intervening position-changing free evolution, none of those kicks returns to a later system position. The pointers consequently commute, and their product-state position distribution is precisely that of $(X,\epsilon)$. This constructs the classical representation of all recorded outcomes, without asserting that every observable on the full quantum system is commutative. $\square$

**Proposition 5.4 (Fixed words and adaptive choices).** The Gaussian covariance formula in Theorem 5.1 applies to a word fixed independently of acquired outcomes. If a later action is selected from earlier outcomes, the law is obtained by joining the corresponding branch densities on their selection sets; one fixed Gaussian record law does not follow.

Proof. For a deterministic causal policy, fix a possible action word $w$. The event selecting that word is a measurable region of its earlier recorded coordinates. The instrument density on that region is $p_w(z\mid W)$ from Theorem 5.1, multiplied by the region's indicator. Summing over words gives the policy's law. The matrices $L_w$ may differ and the indicator truncations need not preserve Gaussianity. An independent randomized policy additionally averages over its independent seed. This is the source-family restriction of [Second Order Relation Completion, Theorem 14.3](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) applied to the actual common latent source, not a replacement of the original fixed-word calculations by a Gaussian assertion for arbitrary policies. $\square$

## 6. Exact preimages of indexed population laws

**Theorem 6.1 (Original response fibres and entire-child preimages).** For every fixed original word $w$ and $W,W'\in\mathcal W$,

$$
y_w(W)=y_w(W')
\quad\Longleftrightarrow\quad
\nu_w(W)=\nu_w(W').
$$

For its response vector $h$, write
$\Lambda_{w,h}=\mathcal N_{|w|+1}(h,C_w)$. Then

$$
\mathcal F(h_0,E_1,h_1,\ldots,E_t,h_t)
=\nu_w^{-1}(\{\Lambda_{w,h}\}).
$$

In particular, for $A=\{0,\ldots,6\}$ and $w_A=JMJMMM$,

$$
\boxed{\ 
C(p,v)=\{W\in\mathcal W:
\nu_{w_A}(W)=\mathcal N_7(h(p,v),C_A)\}\ ,
\qquad C_A=\tfrac12L_AL_A^T+\sigma^2I_7.\
}
$$

This identity holds for every real $p,v$; its use in $D_J,D_M$ retains $p\ne24$. Every original world in the entire child occurs on the right, including unused companions and all gain strata.

Proof. For a fixed word, Theorem 5.1 gives the same covariance for every world. Equal means therefore give equal Gaussian laws. Conversely equality of the laws implies equality of their finite first moments, hence equality of $y_w$. More directly, equality with $\Lambda_{w,h}$ is equivalent to $y_w(W)=h$. Taking the preimage of that equality gives the entire literal fibre by Definition 1.2. The same argument applies whether the fibre is empty, finite or infinite; no reconstruction formula dividing by $g(i)$ or restriction to selected worlds enters it. $\square$

**Theorem 6.2 (The original two terminal pair predicates).** Put $w_J=JMJMMMJ$ and $w_M=JMJMMMM$. For $W,W'\in C(p,v)$,

$$
\begin{aligned}
f_{MJ}(W)=f_{MJ}(W')&\iff\nu_{w_J}(W)=\nu_{w_J}(W'),\\
f_{MM}(W)=f_{MM}(W')&\iff\nu_{w_M}(W)=\nu_{w_M}(W').
\end{aligned}
$$

Consequently $D_J\cap D_M$ is exactly the set of $p\ne24,v$ for which there are indexed worlds $W_0,W_1,W_2,W_3$ in the preimage of Theorem 6.1 satisfying

$$
W_0\ne W_1,\quad\nu_{w_J}(W_0)=\nu_{w_J}(W_1),\qquad
W_2\ne W_3,\quad\nu_{w_M}(W_2)=\nu_{w_M}(W_3).
$$

The two pairs may differ, and no equality between a terminal-$J$ law and a terminal-$M$ law is imposed.

Proof. All seven prefix means of worlds in $C(p,v)$ agree with $h(p,v)$. Within a fixed terminal alternative, equality of the eighth mean is therefore equivalent to equality of the whole eight-dimensional mean vector. Apply Theorem 6.1 separately for the two words. The final assertion is exactly substitution into the same-base pair quantifiers of [Strict Real, Definition 1.2](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md), also retained in [III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md) and [IV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md), Definition 1.1. There is no identification of the two selected pairs. $\square$

**Definition 6.3 (Indexed preparation fibres).** Let $\mathcal P=\{\rho_W:W\in\mathcal W\}$ with its unique world labels supplied by the injection $\iota$. Define
$\widehat\nu_w(\rho_W)=\nu_w(W)$ and

$$
\widehat{\mathcal F}(H)
=\{\rho_W\in\mathcal P:
\widehat\nu_w(\rho_W)=\Lambda_{w,h}\}.
$$

For $\widehat S\subseteq\widehat{\mathcal F}(H)$ define $\widehat L_k(\widehat S,H)$ by the recursion of Definition 1.3, replacing $\mathcal F$ by $\widehat{\mathcal F}$ and retaining distinct prepared states as the counted objects. These are predicates on indexed preparations and laws; their definition does not prescribe an acquired-outcome filter.

**Theorem 6.4 (Recursive transfer without quotienting away worlds).** For every $S\subseteq\mathcal F(H)$ and every $k$ within the original remaining horizon,

$$
\iota(\mathcal F(H))=\widehat{\mathcal F}(H),\qquad
L_k(S,H)\iff\widehat L_k(\iota(S),H).
$$

This also preserves finite or infinite cardinalities of the underlying supports. Replacing an entire nonempty child by the deduplicated set of its prefix laws would instead replace that child by a singleton.

Proof. The first equality is Theorem 6.1 with the injective label map. Injectivity gives $|S|=|\iota(S)|$, including for infinite $S$, and

$$
\iota(S\cap\mathcal F(H,E,u))
=\iota(S)\cap\widehat{\mathcal F}(H,E,u).
$$

The base guard is therefore equivalent. Assuming the equivalence at $k$, apply this intersection equality for each fixed $E,u$ and then retain the same existential $u$ and conjunction over $E$ in the recursion. This proves the step to $k+1$. It keeps one shared acquired response for each child before alternative continuations are considered.

For the last assertion every world of $C(p,v)$ maps to the single law $\mathcal N_7(h(p,v),C_A)$. A set of distinct prefix laws therefore contains one element whenever the child is nonempty, whatever the number of original worlds. The preimage and its injective preparation labels, rather than that quotient set, are what retain the original cardinality predicates. $\square$

## 7. Positive noise, exact histories and the literal target

**Proposition 7.1 (Positive variance and failure of literal acquisition in this model).** For every original world, fixed word and acquired clock,

$$
\operatorname{Var}_W(R_i)=\frac{\|L_i\|^2}{2}+\sigma^2>0.
$$

Already at clock zero,

$$
L_0=(1,t_0^T,0,0,0),\qquad
\operatorname{Var}_W(R_0)=\frac32+\sigma^2.
$$

Thus the law supplied by Theorem 5.1 is not the literal deterministic record law $\delta_{y_w(W)}$, even for a single initial reading. Sending only $\sigma\downarrow0$ leaves the initial latent contribution $3/2$ to that variance.

Proof. The covariance formula of Theorem 5.1 gives the first identity. The row $L_0$ has three entries equal to one and all others zero, so its squared norm is three. A scalar Gaussian with positive variance has no atom, and in particular
$\mathbb P_W(R_0=y_0(W))=0$. Therefore the whole record cannot equal the original deterministic vector with probability one. The displayed limit follows directly. A position Dirac mass would not be the position density of a normal $L^2$ state in Assumption 2.1. This calculation refutes the literal interpretation of this specified instrument, without asserting a prohibition for different carriers or instruments. $\square$

**Theorem 7.2 (The continuous conditional kernel at the original child history).** Fix either original terminal action $E\in\{J,M\}$ after $w_A=JMJMMM$, and split its eight-read covariance as

$$
C^E=\begin{pmatrix}C_A&C_{A7}^E\\C_{7A}^E&C_{77}^E\end{pmatrix}.
$$

For every $W$, the conditional law of $R_7$ given $R_A=r$ has the continuous Gaussian version

$$
\mathsf K_W^E(r,\cdot)=
\mathcal N_1\!\left(
y_7^E(W)+C_{7A}^EC_A^{-1}(r-y_A(W)),\
s_E^2\right),
$$

$$
s_E^2=C_{77}^E-C_{7A}^EC_A^{-1}C_{A7}^E
=\sigma^2+L_7^E B_A(L_7^E)^T>\sigma^2,
\qquad
B_A=(2I_{17}+\sigma^{-2}L_A^TL_A)^{-1}.
$$

For $W\in C(p,v)$, evaluation at $r=h(p,v)$ makes this version's terminal mean equal to $f_{ME}(W)$. Nevertheless
$\mathbb P_W(R_A=h(p,v))=0$ for every $W$. Evaluation at that history is an identity of the specified conditional kernel, not conditioning on a positive-probability event or acquisition of the original child.

Proof. Positive $\sigma$ makes $C^E$ positive definite, since
$s^TC^Es=\|L_w^Ts\|^2/2+\sigma^2\|s\|^2>0$ for $s\ne0$. In particular $C_A$ is invertible. Apply the Gaussian observation correspondence of Definition 5.2: completing the square gives the latent conditional mean and covariance in Proposition 5.3. The independent seventh noise then gives variance $\sigma^2+L_7^EB_A(L_7^E)^T$. The matrix $B_A$ is positive definite and the first coordinate of $L_7^E$ is one, so this variance exceeds $\sigma^2$.

The identity

$$
B_A\sigma^{-2}L_A^T
=\frac12L_A^TC_A^{-1}
$$

follows by multiplication by $2I_{17}+\sigma^{-2}L_A^TL_A$. Substitution into $L_7^E\mu_A(W,r)$ gives the stated mean, since $C_{7A}^E=L_7^EL_A^T/2$. The covariance expression is equivalently the Gaussian Schur complement, the same finite Gaussian calculation used in [Second Order Relation Completion, Theorem 14.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md). This proves the conditional formula and its disintegration identity.

The kernel depends continuously on $r$. A regular conditional law can be changed on a marginal-null set without changing its defining disintegration; the formula above explicitly selects its continuous version. The prefix marginal has a nondegenerate Gaussian density, so every exact point $h$ is null. For $W$ in the child, $y_A(W)=h(p,v)$ by Definition 1.2; hence the correction vanishes at this specified point. It is not identically zero as a function of arbitrary $r$: the original matrices give

$$
C_{70}^J=\frac{1+\operatorname{tr}Q_7^J}{2}=\frac72,\qquad
C_{70}^M=\frac{1+\operatorname{tr}Q_7^M}{2}=\frac92.
$$

Thus even within this model an unconditional terminal mean cannot replace a general selective terminal mean. $\square$

**Proposition 7.3 (Everywhere-positive likelihood is not a whole-child selector).** For any fixed original word and every $W$, the record density $p_w(r\mid W)$ is strictly positive at every $r$. All these laws are mutually absolutely continuous. No event of the acquired record can have probability one for one world and zero for another.

If an additional Borel probability prior $\Pi$ on $\mathcal W$ is supplied, the continuous likelihood update

$$
\Pi_r(dW)=
\frac{p_{w_A}(r\mid W)}
{\int_{\mathcal W}p_{w_A}(r\mid V)\,\Pi(dV)}\,\Pi(dW)
$$

is equivalent to $\Pi$ for every $r$. In particular any positive-prior off-child set retains positive posterior probability at $r=h(p,v)$. Without a supplied prior, no posterior on worlds is defined by the instrument.

Proof. The positive-definite covariance in Theorem 5.1 gives an everywhere-positive finite Gaussian density. Equality of its null sets with Lebesgue null sets proves mutual absolute continuity and the assertion about probability-one versus probability-zero events. The likelihood is measurable in $W$, since the mean is a continuous function of $(r,b,a_0,\ldots,a_3,d)$ on the original domain. For a fixed word its maximum is bounded above by $(2\pi)^{-(t+1)/2}(\det C_w)^{-1/2}$ independently of $W$. The prior normalization is therefore finite and strictly positive. Multiplication by a strictly positive density preserves exactly the prior's null sets, proving the posterior assertion for every $r$ in this explicit version. The actual exact-history event remains null as in Theorem 7.2. $\square$

**Definition 7.4 (The full original common literal-process requirement).** A common literal-process correspondence for $\mathcal W$ must supply one permitted preparation family and shared legal controls and acquisitions such that, for every world and every original executed word through clock seven,

$$
\operatorname{Law}_W(\widetilde R_w)=\delta_{y_w(W)}.
$$

For each original history $H$ with numeric vector $h$, its acquired history event must then obey

$$
\mathbb P_W(\widetilde R_w=h)=1_{\mathcal F(H)}(W),
$$

and continuation on that event must retain the same complete world for the original alternative responses and recursive predicates of Definitions 1.2–1.3. The task retains all original gain strata and clocks, the fifth acquisition between its two $M$ actions, one drift per world, one whole polynomial per world, the entire child, and possibly different terminal pairs. No reset, copy, skipped read, shifted clock, additional outward port or success selection is allowed. If the intended preparation must be obtained from an unknown original carrier, a legal common preparation map from that carrier is an additional required datum.

The existence problem is to furnish such data on the full original domain, or a mathematical obstruction under explicitly stated assumptions on those data. A mean identity, an indexed population-law preimage, a continuous conditional kernel at a null history and an assumed family of initial programs are different conditions from this literal-process requirement.

**Proposition 7.5 (Exact scope of the Gaussian FIB correspondence).** Assumptions 2.1 and 4.1 give all the original deterministic responses as unconditional means and all original equal-response fibres as indexed population-law preimages, with the distinct-world and recursive quantifiers preserved. The supplied instrument fails Definition 7.4. It does not identify the program preparation with a legal encoding of an unknown original carrier or identify its internal probes and unbounded energy family with the resources of that carrier.

Proof. The mean assertion is Theorem 5.1 and the fibre assertions are Theorems 6.1–6.4. Failure of the literal requirement follows already from Proposition 7.1; Proposition 7.3 separately excludes an acquired-child interpretation of positive likelihood. The preparation contract explicitly supplies $\rho_W$ without a carrier-to-program map, while its finite-per-world energy formula has no uniform bound. None of the control or probe assumptions supplies that missing map or a resource comparison.

This distinction uses the task-relative convention of [Second Order Relation Completion, Definition 0.1](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md). In the different native problem of [Joint Transfer–Coherence Interface Geometry, Definition 1.4](FIB_NATIVE_JOINT_TRANSFER_COHERENCE_INTERFACE_GEOMETRY.md), a single history-independent channel acts on one already reached specimen with fixed common metadata; that premise does not supply the world-dependent initial program here. Likewise [Native Nonlinear Readout Capacity, Definition 2.1](FIB_NATIVE_NONLINEAR_READOUT_CAPACITY_AND_MINIMAL_DIMENSION.md) requires an encoder intertwining its own native actions and one deterministic output map. The stochastic output and explicitly different preparation family here supply no correspondence satisfying that contract. These are distinctions of mathematical hypotheses and outputs. The repo-derived content is the concrete conditional FIB program, instrument and indexed-law correspondence proved above, using the cited mature representation and Gaussian tools; no priority, physical identification or nonclassical resource conclusion is entailed. $\square$

## 追加锚（本行以下为增补区）
