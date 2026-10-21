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

**Recalled source data (Common Parent, Definition 1.3).** For use in the action/readout and joint-law derivations, recall the following complete chronological product and trace table from [Common Parent, Definition 1.3](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), writing its $V=U+n$ explicitly. All traces are against the original $P$ of Definition 1.1.

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

The two sixth-action rows and four seventh-action rows name alternatives; they do not request multiple reads at one original clock.

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

This proves the Gaussian law, covariance and mean. The last mean identity is Theorem 3.2, using the original trace products recalled above from [Common Parent, Definition 1.3](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md). $\square$

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

## 8. The retained two-action prefix and its system pair

**Definition 8.1 (A fixed-world nonselective marginal).** Fix any $W\in\mathcal W$ and any $\sigma>0$, with exactly the preparations and apparatus of Assumptions 2.1 and 4.1. Execute the original prefix

$$
\mathrm{read}_0,\ J,\ \mathrm{read}_1,\ M,\ \mathrm{read}_2.
$$

All three acquisitions are made and retained. The state considered here is the final system marginal after averaging their actual records, followed by tracing out fifteen system modes. It is not a state selected by a numeric history. In the column vectorization of Definition 3.1, choose

$$
q_A=X_{3,11}=q_{14},\quad q_B=X_{3,21}=q_{15},\qquad
p_A=\pi_{14},\quad p_B=\pi_{15},\qquad [q_j,p_k]=i\delta_{jk}.
$$

Thus $\mathcal H=\mathcal H_{AB}\otimes\mathcal H_{\rm rest}$ with $\mathcal H_{AB}=L^2(\mathbb R^2)$. Write $\mathcal U_E(\rho)=U_{A_E}\rho U_{A_E}^\dagger$ and retain the whole-outcome channels $\mathcal D_i$ of Proposition 4.3. The pair state is

$$
\rho_{AB}^{W,\sigma}
=\operatorname{Tr}_{\rm rest}
\bigl(\mathcal D_2\circ\mathcal U_M\circ\mathcal D_1
\circ\mathcal U_J\circ\mathcal D_0\bigr)(\rho_W).
$$

Equivalently, if $\mathsf K_{JM}(z)=K_2(z_2)U_{A_M}K_1(z_1)U_{A_J}K_0(z_0)$ is the retained-record Kraus density from Theorem 5.1, this is

$$
\rho_{AB}^{W,\sigma}
=\operatorname{Tr}_{\rm rest}\int_{\mathbb R^3}
\mathsf K_{JM}(z)\rho_W\mathsf K_{JM}(z)^\dagger\,d^3z.
$$

The integral is the normal-instrument integral of Theorem 4.2. It marginalizes a retained record; it does not omit an acquisition, reset a probe or divide by a selected-event probability. The other five supplied probes are unused in this prefix and can be traced out in their independent input states.

**Proposition 8.2 (Pair closure under the actual reads and controls).** The pair projections of the three laboratory readout rows are

$$
(\ell_0)_{AB}=(0,0),\qquad
(\ell_1)_{AB}=(1,0),\qquad
(\ell_2)_{AB}=(8,0).
$$

Each control preserves the pair as a closed canonical subsystem. Nonselective readout reduces to a Gaussian momentum kick on that pair even when the rest is correlated with it.

Proof. The pair is the first column of $X_3$, so Definition 3.1 gives its readout contribution $i^3q_A$ and no $q_B$ term. Left multiplication by $J$ or $M$ acts separately on each matrix column, hence $U_{A_E}=U_E^{AB}\otimes U_E^{\rm rest}$ under this tensor splitting, with the inverse-transpose momentum action of Theorem 3.2.

For a read at clock $i$, split $F_i(q)=f_i^{AB}+f_i^{\rm rest}$, where $f_i^{AB}=i^3q_A$ (zero at clock zero). Put

$$
r_\sigma=\frac{1}{4\sigma^2},\qquad
\mu_\sigma=\mathcal N(0,r_\sigma),\qquad
V_i^{AB}(\eta)=e^{-i\eta f_i^{AB}},\quad
V_i^{\rm rest}(\eta)=e^{-i\eta f_i^{\rm rest}}.
$$

The spectral momentum distribution of the independent probe in Assumption 4.1 and its coupling in Theorem 4.2 give

$$
\mathcal D_i(\rho)=\int
(V_i^{AB}(\eta)\otimes V_i^{\rm rest}(\eta))\rho
(V_i^{AB}(\eta)\otimes V_i^{\rm rest}(\eta))^\dagger
\,\mu_\sigma(d\eta).
$$

This is a common kick parameter on pair and rest, not an assumption of independent kicks on those subsystems. Unitary invariance of the partial trace on the rest gives, for any trace-class $\rho$ including correlated inputs,

$$
\operatorname{Tr}_{\rm rest}\mathcal D_i(\rho)
=\int V_i^{AB}(\eta)
(\operatorname{Tr}_{\rm rest}\rho)
V_i^{AB}(\eta)^\dagger\,\mu_\sigma(d\eta).
$$

Pair-factorization of the controls and this identity justify successive pair reduction throughout the nonselective composition in Definition 8.1. In particular the initial read is still present even though its reduced pair channel is the identity. No such identity for a branch conditioned on the retained records is being asserted. $\square$

## 9. Chronological quadratures and the full centered covariance

**Proposition 9.1 (All three probe contributions).** Denote the initial pair quadratures by uppercase $Q_A,Q_B,P_A,P_B$. In the input state of Assumption 2.1 their means are

$$
\langle Q_A\rangle=a_3P_{11},\quad
\langle Q_B\rangle=a_3P_{21},\quad
\langle P_A\rangle=\langle P_B\rangle=0,
$$

and their centered symmetrized covariance is $I_4/2$ in ordering $(Q_A,P_A,Q_B,P_B)$. Let $\eta_0,\eta_1,\eta_2$ be the three initial probe momentum observables. They commute with the initial system, are independent of it and of one another in the input product state, and each has mean zero and variance $r_\sigma$. They are not the pointer position noises of variance $\sigma^2$ in Theorem 5.1. Uppercase system quadratures here are operators, not a proposed joint classical draw of positions and momenta.

The final pair quadratures, pulled back to this common input dilation, are exactly

$$
q_A=Q_A,\qquad q_B=Q_A+Q_B,\qquad
p_A=P_A-P_B+\eta_1-8\eta_2,\qquad
p_B=P_B-\eta_1.
$$

Proof. Theorem 4.2 sends a pair momentum vector to itself minus $(\ell_i)_{AB}\eta_i$, while leaving the pair positions fixed. Proposition 8.2 and Theorem 3.2 therefore give the chronological list

$$
\begin{aligned}
\mathrm{read}_0:\quad
&(q_A,q_B)=(Q_A,Q_B),&
&(p_A,p_B)=(P_A,P_B),\\
J:\quad
&(q_A,q_B)=(Q_B,Q_A),&
&(p_A,p_B)=(P_B,P_A),\\
\mathrm{read}_1:\quad
&(q_A,q_B)=(Q_B,Q_A),&
&(p_A,p_B)=(P_B-\eta_1,P_A),\\
M:\quad
&(q_A,q_B)=(Q_A,Q_A+Q_B),&
&(p_A,p_B)=(P_A-P_B+\eta_1,P_B-\eta_1),\\
\mathrm{read}_2:\quad
&(q_A,q_B)=(Q_A,Q_A+Q_B),&
&(p_A,p_B)=(P_A-P_B+\eta_1-8\eta_2,P_B-\eta_1).
\end{aligned}
$$

For the $M$ line, $M^{-T}=\begin{pmatrix}-1&1\\1&0\end{pmatrix}$. The initial probe $\eta_0$ has zero pair coefficient; $\eta_1$ is present after both subsequent operations; the last read has coefficient eight, not one. Every line uses the same initial system and three independent probes. $\square$

**Proposition 9.2 (Covariance and moment domain).** For every fixed $W\in\mathcal W$ and $\sigma>0$, $\rho_{AB}^{W,\sigma}$ is a two-mode Gaussian state with finite centered second moments. In ordering $\xi=(q_A,p_A,q_B,p_B)^T$, set

$$
V_{jk}=\frac12\left\langle
\Delta\xi_j\Delta\xi_k+\Delta\xi_k\Delta\xi_j
\right\rangle.
$$

Then

$$
V=\begin{pmatrix}
\frac12&0&\frac12&0\\
0&1+65r_\sigma&0&-(\frac12+r_\sigma)\\
\frac12&0&1&0\\
0&-(\frac12+r_\sigma)&0&\frac12+r_\sigma
\end{pmatrix}.
$$

Proof. Insert Proposition 9.1 into the initial product-state moments. In particular

$$
\begin{aligned}
\operatorname{Var}(p_A)&=\tfrac12+\tfrac12+r_\sigma+64r_\sigma,\\
\operatorname{Var}(p_B)&=\tfrac12+r_\sigma,\\
\operatorname{Cov}_{\rm sym}(p_A,p_B)&=-\tfrac12-r_\sigma,\\
\operatorname{Cov}_{\rm sym}(q_A,q_B)&=\tfrac12.
\end{aligned}
$$

All position–momentum centered cross terms vanish. Gaussianity follows from the specified Gaussian system and probes, their linear canonical controls and couplings, and the nonselective Gaussian kick averages and partial traces in Proposition 8.2. Equivalently the final quadratures in Proposition 9.1 are linear in the quadratures of that common Gaussian input.

For the unbounded quadratures the identities can first be read on the joint Schwartz core: the initial Gaussian is Schwartz, and invertible linear pullbacks and the stated bilinear coupling shears preserve that class. Its first and second quadrature forms are finite. Passing to the reduced state preserves these expectations; alternatively the kick integrals have finite second moments because $r_\sigma<\infty$. Thus the covariance computation does not apply a bounded-observable channel to an unbounded operator without a moment extension. No uniform-in-$W$ energy estimate is used.

Changing $W$ changes the final displacement

$$
\langle\xi\rangle=(a_3P_{11},0,a_3(P_{11}+P_{21}),0)^T,
$$

but leaves $V$ unchanged. In particular $a_3=0$ sets these means to zero; it does not remove the $X_3$ oscillator factors or their vacuum fluctuations of variance $1/2$. All lower-degree and sampled-zero worlds remain included. $\square$

## 10. A sufficient EPR witness and the sharp Gaussian boundary

**Proposition 10.1 (The fixed EPR witness).** For the nonselective pair in Definition 8.1 put

$$
u=q_B-q_A,\qquad v=p_A+p_B.
$$

Then

$$
u=Q_B,\qquad v=P_A-8\eta_2,\qquad
\operatorname{Var}(u)=\tfrac12,\qquad
\operatorname{Var}(v)=\tfrac12+64r_\sigma,
$$

and hence

$$
\operatorname{Var}(u)+\operatorname{Var}(v)
=1+64r_\sigma=1+\frac{16}{\sigma^2}.
$$

The $\eta_1$ terms cancel exactly in $v$, while remaining visible in the full covariance of Proposition 9.2. This cancellation is not removal of read one.

For the mature separability criterion use L.-M. Duan, G. Giedke, J. I. Cirac and P. Zoller, *Inseparability criterion for continuous variable systems*, [quant-ph/9908056v2](https://arxiv.org/pdf/quant-ph/9908056v2), PDF p. 1, Eqs. (2a)–(2b), and pp. 1–2, Theorem 1, Eq. (3); published in *Physical Review Letters* **84**, 2722, [DOI:10.1103/PhysRevLett.84.2722](https://doi.org/10.1103/PhysRevLett.84.2722). Apply its $a=1$ case to mode 1 $(x_1,p_1)=(q_B,p_B)$ and mode 2 $(x_2,p_2)=(-q_A,-p_A)$. The second choice is local parity on A and preserves the canonical commutator. The paper's $u=x_1+x_2$ and $v=p_1-p_2$ are exactly the pair above, so every separable state with these finite variances obeys their sum $\ge2$.

The displayed sum is less than two precisely when $\sigma>4$. Thus this witness proves entanglement for every fixed $W$ when $\sigma>4$. At or below four this particular witness supplies no separability conclusion.

Proof. Subtract and add the quadratures in Proposition 9.1, use their input moments, and apply the cited variance criterion with the stated local canonical choices. $\square$

**Proposition 10.2 (Exact classification for this Gaussian marginal).** For every fixed $W\in\mathcal W$ and $\sigma>0$,

$$
\begin{aligned}
\rho_{AB}^{W,\sigma}\text{ is separable}
&\quad\Longleftrightarrow\quad
0<\sigma\le\frac{4}{\sqrt{1+\sqrt{65}}},\\
\rho_{AB}^{W,\sigma}\text{ is entangled}
&\quad\Longleftrightarrow\quad
\sigma>\frac{4}{\sqrt{1+\sqrt{65}}}.
\end{aligned}
$$

In particular equality at the threshold is separable.

Proof. Apply R. Simon, *Peres-Horodecki Separability Criterion for Continuous Variable Systems*, [quant-ph/9909044v1](https://arxiv.org/pdf/quant-ph/9909044v1), published in *Physical Review Letters* **84**, 2726, [DOI:10.1103/PhysRevLett.84.2726](https://doi.org/10.1103/PhysRevLett.84.2726). The normalization is that paper's $[q,p]=i$: PDF p. 2, Eq. (3) orders the quadratures as $(q_1,p_1,q_2,p_2)$, and Eq. (6) and its variance-matrix paragraph define the same symmetrized $V$, with Eq. (7) giving $V+i\Omega/2\ge0$. Its PDF p. 3, Eq. (16) uses the mode blocks $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$. For Proposition 9.2 these are

$$
A=\operatorname{diag}(\tfrac12,1+65r_\sigma),\quad
B=\operatorname{diag}(1,\tfrac12+r_\sigma),\quad
C=\operatorname{diag}(\tfrac12,-\tfrac12-r_\sigma).
$$

Write $J_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ for the paper's symplectic $J$, distinct from the FIB action $J$. Simon's Eq. (19), PDF p. 4, is

$$
\det A\det B+(\tfrac14-|\det C|)^2
-\operatorname{tr}(AJ_2CJ_2BJ_2C^TJ_2)
\ \ge\ \frac{\det A+\det B}{4}.
$$

The theorem directly below Eq. (19) makes this condition necessary and sufficient for separability of a two-mode Gaussian state. Proposition 9.2 supplies that Gaussian hypothesis and the required finite covariance. The finite substitution here gives

$$
\begin{aligned}
\det A&=\tfrac12+\tfrac{65}{2}r_\sigma,&
\det B&=\tfrac12+r_\sigma,&
\det C&=-\tfrac14-\tfrac12r_\sigma,\\
\operatorname{tr}(AJ_2CJ_2BJ_2C^TJ_2)
&=(\tfrac12+r_\sigma)(\tfrac12+\tfrac{67}{4}r_\sigma).
\end{aligned}
$$

Consequently left side minus right side of Eq. (19) is

$$
\frac{64r_\sigma^2-2r_\sigma-1}{4}.
$$

Since $r_\sigma>0$, this is nonnegative exactly when $r_\sigma\ge(1+\sqrt{65})/64$. Substituting $r_\sigma=1/(4\sigma^2)$ gives the stated classification, with equality included by the non-strict separability condition. This numerical boundary is the substitution for this FIB marginal, not a threshold asserted in Simon's general theorem. The Duan witness of Proposition 10.1 is sufficient on the smaller range $\sigma>4$; its failure to violate the bound does not settle the intermediate range. $\square$

## 11. Classical pointer laws and the scope of the internal entanglement

**Proposition 11.1 (Compatible conclusions for different observable families).** For each fixed original operation word, the exact classical latent-position representation of Theorem 5.1 and Proposition 5.3 coexists with the internal two-mode entanglement classified in Proposition 10.2 for the specified prefix. The original positions-only pointer protocol does not measure the additional conjugate observables needed to evaluate the EPR witness.

Proof. Theorem 5.1 represents the actual fixed-word pointer vector by one common $X$ and independent pointer noises. Proposition 5.3 identifies why: the position controls and probe couplings pull all these pointers back to commuting position observables. This is an exact statement about that record family. In contrast $p_A+p_B$ in Proposition 10.1 contains initial system momentum and probe momentum. A classical representation for the pointer positions does not supply a joint classical representation of all canonical system observables or imply separability of $\rho_{AB}^{W,\sigma}$.

Although $u$ and $v$ commute with one another, accessing their variances requires conjugate-observable measurements beyond the original outward pointer menu. No permission or implementation for such additional measurements is part of Assumption 4.1. The mathematical witness and covariance therefore identify an internal state property without replacing the recorded protocol by an augmented experiment. $\square$

The classification is pointwise in a fixed $W$ under the supplied seventeen-mode Gaussian preparation, and concerns only the nonselective pair after the retained prefix. It makes no assertion about an arbitrary mixture over $W$, a branch conditioned on an exact history, or a word chosen adaptively from outcomes; Proposition 5.4 retains its fixed-word restriction. Zero cubic displacement does not change the mode count. Finite moments and finite preparation energy for each fixed world do not give a uniform energy or preparation-resource bound.

The assumed preparation family, shared ideal controls and probes remain those of §§2–4. The entanglement calculation supplies neither a legal encoding from an unknown native carrier, nor physical realization, Bell violation, quantum advantage, minimum resources or a literature priority claim. It does not repair the positive-noise failure of the literal-process requirement in Propositions 7.1 and 7.5. The additional result is the source-dependent state reduction, covariance and application of the cited separability criteria to that specified Gaussian program.

## 追加锚（本行以下为增补区）

## 12. Whole-companion compactness and the specified preparation

**Definition 12.1 (The entire compact region and its coordinates).**
Write III for [Strict Real Joint Incidence Support III](https://github.com/the-omega-institute/trureturing/blob/30b32d5e17e23590839090a0b244c019c4796817/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md).
Use its Definition 1.1 and Definition 20.1 for the ambient parent
$\mathcal H_{\rm par}$, distinguished here from the system Hilbert
space $\mathcal H=L^2(\mathbb R^{17};\mathbb C)$. Set

$$
K_J=\{W\in\mathcal H_{\rm par}:10\le p(W)\le34,
\quad v(W)=v_J(p(W))\}.
\tag{12.1}
$$

This is III, Definition 23.1: at $p\ne24$ it contains every world of
$C(p,v_J(p))$, and at $p=24$ it retains the same complete-world
equations in the ambient parent. Unused companions, singular sources,
degree drops, sampled gain zeros and zero drift remain included.
No choice of a terminal pair enters (12.1).

Write the full coordinates and the prescribed preparation mean as

$$
\begin{gathered}
W=(P,g,d),\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
c=\frac{r(1-r)}b,\quad 0<r<1,\quad b>0,\quad d=e+24,\\
g(s)=\sum_{k=0}^3a_ks^k\ne0,\qquad
\operatorname{vec}(X)=(X_{11},X_{21},X_{12},X_{22})^T,\\
\mu(W)=m_W=
(d,\operatorname{vec}(a_0P),\operatorname{vec}(a_1P),
\operatorname{vec}(a_2P),\operatorname{vec}(a_3P))\in\mathbb R^{17}.
\end{gathered}
\tag{12.2}
$$

The four coefficients are padded through degree three. In particular
each four-coordinate block in (12.2) is
$a_k(r,c,b,1-r)^T$, with column rather than row vectorization.
The preparation is exactly Assumption 2.1:

$$
\psi_W(x)=\pi^{-17/4}e^{-\|x-\mu(W)\|^2/2},\qquad
\rho_W=|\psi_W\rangle\langle\psi_W|.
\tag{12.3}
$$

**Assumption 12.2 (The reused compactness premise).**
Take III, Theorem 23.2 as the ordinary mathematical premise that
$K_J$ is compact in the full source/drift/padded-gain coordinates.
III, Theorem 16.4 supplies complete worlds above every
$p\in[10,34]$, so this compact set is nonempty, including its
retained twenty-four fibre. Assumptions 2.1 and 4.1 continue to
supply the specified preparations and shared apparatus.

**Proposition 12.3 (Uniform initial energy on all companions).**
Under Assumption 12.2 the following maximum exists and is finite:

$$
\begin{aligned}
\lambda(W)&=\frac{\|\mu(W)\|^2}{2}\\
&=\frac12\left((e+24)^2+
\bigl(r^2+c^2+b^2+(1-r)^2\bigr)\sum_{k=0}^3a_k^2\right),\\
B&=\max_{W\in K_J}\lambda(W)<\infty.
\end{aligned}
\tag{12.4}
$$

For the reference oscillator and its total occupation operator,

$$
H_{\rm osc}=\frac12\sum_{j=1}^{17}(q_j^2+\pi_j^2),\qquad
N_{\rm ref}=H_{\rm osc}-\frac{17}{2}I,
\tag{12.5}
$$

the original preparation satisfies, uniformly on this entire region,

$$
\operatorname{tr}(\rho_WN_{\rm ref})=\lambda(W)\le B,
\qquad
\operatorname{tr}(\rho_WH_{\rm osc})\le\frac{17}{2}+B.
\tag{12.6}
$$

*Proof.* In the full coordinates, (12.2) is polynomial and hence
continuous. Thus (12.4) is a continuous real function on a nonempty
compact set. The extreme-value theorem supplies its finite maximum.
Theorem 2.2 already gives the energy identity in (12.6); substituting
(12.4) into that identity gives the uniform bound.

The correspondence with III does not divide by a gain coefficient,
a sampled $g(i)$, $p-24$, or the parent quantity $\Lambda$.
For clarity, III, Definition 20.1, Eq. (20.2), reconstructs $g$
as the fixed-node interpolant with

$$
(g(0),g(1),g(2),g(3))=
\left(-24-e,-\frac e{b+c},
\frac{27/5-e}{1+b},-\frac e{b+c+r}\right).
\tag{12.7}
$$

The conversion from these four values to $(a_0,a_1,a_2,a_3)$ is a
fixed inverse Vandermonde matrix. Its source denominators in (12.7)
are positive on the original parent. Compactness in the full
coordinates is already the accepted premise; no regularity condition
on individual companion strata is added by this reconstruction.
III, Corollary 23.3 supplies qualitative coordinate bounds and
interior margins, without numerical values for these extrema.
Consequently (12.4) specifies $B$, but gives no certified numerical
upper bound for it. $\square$

## 13. One common finite Fock subspace and normalized preparations

**Definition 13.1 (The cutoff family).**
Use the usual seventeen-mode oscillator Fock basis
$|\mathbf n\rangle$, $\mathbf n=(n_1,\ldots,n_{17})\in\mathbb N^{17}$,
with $|\mathbf n|=\sum_jn_j$ and
$N_{\rm ref}|\mathbf n\rangle=|\mathbf n|\,|\mathbf n\rangle$.
For an integer $N\ge0$, put

$$
\begin{gathered}
\Pi_N=1_{\{N_{\rm ref}\le N\}},\qquad
\mathcal H_N=\operatorname{ran}\Pi_N,\\
q_N(W)=\langle\psi_W,\Pi_N\psi_W\rangle,\qquad
t_N(W)=1-q_N(W),\\
\psi_{W,N}=\frac{\Pi_N\psi_W}{\sqrt{q_N(W)}},\qquad
\rho_{W,N}=|\psi_{W,N}\rangle\langle\psi_{W,N}|.
\end{gathered}
\tag{13.1}
$$

Here $q_N(W)$ is a scalar retained mass, distinct from any position
operator $q_j$. The same projector is used for every companion.
The positivity needed for normalization follows below.

**Proposition 13.2 (Explicit retained mass, dimension and error).**
For all $W\in K_J$ and integers $N\ge0$,

$$
\begin{aligned}
q_N(W)&=e^{-\lambda(W)}\sum_{n=0}^N\frac{\lambda(W)^n}{n!}
\ \ge e^{-B}>0,\\
t_N(W)&\le\min\left\{1,\frac{B}{N+1}\right\},\qquad
\operatorname{rank}\Pi_N=\binom{N+17}{17}.
\end{aligned}
\tag{13.2}
$$

With trace distance defined by $D(\rho,\tau)=\tfrac12\|\rho-\tau\|_1$,
the exact input error and its uniform consequence are

$$
\begin{aligned}
D(\rho_W,\rho_{W,N})&=\sqrt{t_N(W)},\\
\sup_{W\in K_J}D(\rho_W,\rho_{W,N})
&\le\delta_N:=\min\left\{1,\sqrt{\frac{B}{N+1}}\right\}
\xrightarrow[N\to\infty]{}0.
\end{aligned}
\tag{13.3}
$$

*Proof.* Let $\mathfrak a_j=(q_j+i\pi_j)/\sqrt2$ denote the
annihilation operators, distinct from the gain coefficients $a_k$.
Then $N_{\rm ref}=\sum_j\mathfrak a_j^\dagger\mathfrak a_j$.
The real translated vacuum (12.3) is the product coherent state with
amplitude $\alpha=\mu(W)/\sqrt2$, so
$\sum_j|\alpha_j|^2=\lambda(W)$ and
$\langle N_{\rm ref}\rangle=\lambda(W)$.
Substitution into the standard coherent-state Fock expansion gives

$$
\psi_W=e^{-\lambda(W)/2}
\sum_{\mathbf n\in\mathbb N^{17}}
\frac{\prod_{j=1}^{17}\alpha_j^{n_j}}
{\sqrt{\prod_{j=1}^{17}n_j!}}\,|\mathbf n\rangle.
\tag{13.4}
$$

The expansion includes zero amplitudes, with the constant term
interpreted in the usual way. Grouping its squared coefficients by
total occupation and substituting the multinomial identity yields

$$
\mathbb P_W(N_{\rm ref}=n)
=e^{-\lambda(W)}
\sum_{|\mathbf n|=n}\prod_j\frac{|\alpha_j|^{2n_j}}{n_j!}
=e^{-\lambda(W)}\frac{\lambda(W)^n}{n!}.
\tag{13.5}
$$

Thus the total occupation is Poisson with parameter $\lambda(W)$.
Summing through $N$ gives (13.2). Its vacuum term alone gives
$q_N(W)\ge e^{-\lambda(W)}\ge e^{-B}$, including cutoffs for which
the subsequent tail bound is trivial. Hence (13.1) always defines a
unit vector and a trace-one pure state in the common subspace.

The discrete spectral bound
$N_{\rm ref}\ge(N+1)(I-\Pi_N)$, evaluated in this preparation, gives
$(N+1)t_N(W)\le\lambda(W)\le B$. Combining with $t_N\le1$
gives the tail estimate. The overlap is exactly

$$
\langle\psi_W,\psi_{W,N}\rangle=\sqrt{q_N(W)}.
\tag{13.6}
$$

Applying the standard pure-state trace-distance identity
$D(|u\rangle\langle u|,|v\rangle\langle v|)
=\sqrt{1-|\langle u,v\rangle|^2}$ gives (13.3), with no additional
normalization error. Finally, the occupation labels of total at most
$N$ are counted by seventeen-variable stars and bars:

$$
\dim\mathcal H_N
=\sum_{n=0}^N\binom{n+16}{16}=\binom{N+17}{17}.
\tag{13.7}
$$

These are applications of the mature oscillator, counting and
distance formulas identified in Definition 16.1. $\square$

**Corollary 13.3 (A common tolerance choice).**
For any $0<\varepsilon<1$, the integer

$$
N_\varepsilon=
\max\left\{0,\left\lceil\frac{B}{\varepsilon^2}\right\rceil-1\right\}
\tag{13.8}
$$

satisfies $N_\varepsilon+1\ge B/\varepsilon^2$ and gives input trace
distance at most $\varepsilon$ for every $W\in K_J$, in a common
subspace of rank $\binom{N_\varepsilon+17}{17}$.
This is a theoretical choice conditional on $B$, not an evaluated
cutoff or a preparation-resource estimate.

*Proof.* The ceiling inequality and (13.3) give the conclusion.
In a general coherent family with $B=0$, all amplitudes vanish and
$N=0$ is exact. In the actual nonempty family here, $g\ne0$ implies
$\sum_ka_k^2>0$, while $P\ne0$. Equation (12.4) then gives
$\lambda(W)>0$ at every world and $B>0$. For every finite $N$ the
Poisson term at $N+1$ is positive, so $t_N(W)>0$. Exact finite
representation, or $\varepsilon=0$ in (13.8), is unavailable for
these coherent preparations. $\square$

## 14. The unchanged apparatus and the full fixed-word pointer law

**Definition 14.1 (The same joint measurement on both input families).**
Fix any $\sigma>0$ and retain Assumption 4.1: eight independent
Gaussian probes, their original couplings, all original clock reads,
and the controls of Definition 3.1 with adjoint action
$q\mapsto A_Eq$, $\pi\mapsto A_E^{-T}\pi$.
Only the initial system state is replaced by $\rho_{W,N}$.
For an externally fixed chronological word $w=E_1\cdots E_t$,
$E_i\in\{J,M\}$ and $0\le t\le7$, use all reads $0,\ldots,t$.

The normal instruments of Theorem 4.2 compose to a normalized normal
joint POVM $\mathsf E_w$ on $\mathbb R^{t+1}$. In the notation of
Theorem 5.1 its density and normalization are understood weakly:

$$
\begin{gathered}
\mathsf K_w(z)=K_t(z_t)U_{A_{E_t}}\cdots
K_1(z_1)U_{A_{E_1}}K_0(z_0),\\
\mathsf E_w(A)=\int_A\mathsf K_w(z)^\dagger\mathsf K_w(z)\,dz,
\qquad
0\le\mathsf E_w(A)\le I,\qquad
\mathsf E_w(\mathbb R^{t+1})=I,\\
\nu_w(W)(A)=\operatorname{tr}(\rho_W\mathsf E_w(A)),\qquad
\nu_{w,N}(W)(A)=\operatorname{tr}(\rho_{W,N}\mathsf E_w(A)).
\end{gathered}
\tag{14.1}
$$

All $A$ in this section are Borel record events. Normality and
countable additivity are those of the original instruments; no
operator-norm integral over the outcome space is required.
For the empty word, $\mathsf K_{\varnothing}(z_0)=K_0(z_0)$;
only the clock-zero read is executed.
The same measurement acts on both normal input states, independently
of $W$ and of the cutoff used to specify the input.

**Proposition 14.2 (Uniform approximation of the entire retained law).**
Under Assumption 12.2, for every such fixed word,

$$
\begin{gathered}
\nu_w(W)=\mathcal N_{t+1}\left(L_w\mu(W),
\frac12L_wL_w^T+\sigma^2I_{t+1}\right),\\
\operatorname{TV}(\nu_w(W),\nu_{w,N}(W))
\le\sqrt{t_N(W)}\le\delta_N,\qquad
\operatorname{TV}(P,Q):=\sup_{A\ \mathrm{Borel}}|P(A)-Q(A)|.
\end{gathered}
\tag{14.2}
$$

The input is the only approximation. The first law is exactly
Theorem 5.1; the projected-input law is not asserted to be Gaussian.

*Proof.* The original apparatus is defined on normal trace-class
inputs by Theorem 4.2, so (14.1) applies to $\rho_{W,N}$ without
assuming Gaussianity. For each event its effect obeys $0\le\mathsf
E_w(A)\le I$. Apply the variational characterization of trace
distance to the trace-zero self-adjoint trace-class difference:

$$
\begin{aligned}
|\nu_w(W)(A)-\nu_{w,N}(W)(A)|
&=|\operatorname{tr}(\mathsf E_w(A)(\rho_W-\rho_{W,N}))|\\
&\le\tfrac12\|\rho_W-\rho_{W,N}\|_1
=\sqrt{t_N(W)}.
\end{aligned}
\tag{14.3}
$$

Taking the event supremum gives (14.2). This is one measurement of
the complete retained vector. It introduces no factor $t+1$ and no
per-read union bound. Prefix and other record marginals inherit the
same bound by taking cylinder events.

More explicitly, the all-acquisition factorization in Theorem 5.1
is an operator identity, independent of the initial Gaussian:
$\mathsf K_w(z)=U_{T_t}\prod_{i=0}^tk_\sigma(z_i-L_iq)$.
Substitute the normalized projected wavefunction to get its exact
density

$$
p_{w,N}(z\mid W)=\int_{\mathbb R^{17}}|\psi_{W,N}(x)|^2
\prod_{i=0}^t
\frac{\exp(-(z_i-L_ix)^2/(2\sigma^2))}
{\sqrt{2\pi\sigma^2}}\,dx.
\tag{14.4}
$$

Every probe likelihood is retained. Integrating them and then the
normalized input density gives total mass one. Equivalently, (14.4)
uses the latent position density $|\psi_{W,N}|^2$ and the same
independent Gaussian pointer noises as before. That latent density
need not be Gaussian, so neither the target's exact mean and
covariance nor its Gaussian conditional kernels are being assigned
to the approximating law. $\square$

**Corollary 14.3 (Quantifiers and the original two continuations).**
Let $\mathscr W_7=\bigcup_{t=0}^7\{J,M\}^t$ be a menu of words
fixed externally for their respective runs. Then

$$
\sup_{w\in\mathscr W_7}\sup_{W\in K_J}
\operatorname{TV}(\nu_w(W),\nu_{w,N}(W))
\le\delta_N\longrightarrow0.
\tag{14.5}
$$

In particular, for every $\sigma>0$ and $0<\varepsilon<1$,
the same $N_\varepsilon$ in (13.8) works for every companion,
every externally fixed word in this menu and every Borel event.
It depends on the preparation bound $B$ and $\varepsilon$, not on
which word is executed. Different words still denote different runs.

For $W\in K_J$, the three source substitutions most directly
connected to the original child are

$$
\begin{aligned}
w_A&=JMJMMM,&L_{w_A}\mu(W)&=h(p,v_J(p)),\\
w_J&=JMJMMMJ,&L_{w_J}\mu(W)&=(h(p,v_J(p)),a(W)),\\
w_M&=JMJMMMM,&L_{w_M}\mu(W)&=(h(p,v_J(p)),m(W)),\\
h(p,v)&=(0,24,147/5,24,18,p,v).
\end{aligned}
\tag{14.6}
$$

Here $p=p(W)$, and $a,m$ are III, Definition 1.1's original
seventh-clock alternatives, also denoted $f_{MJ},f_{MM}$ in
Definition 1.2. Their covariances are the corresponding
$C_w=\tfrac12L_wL_w^T+\sigma^2I$. These substitutions apply to
unused and singular companions and to $p=24$ as well.

*Proof.* Inequality (14.2) is independent of $W$ and of the chosen
fixed word, giving (14.5) and the stated tolerance quantifiers.
Theorem 3.2 and Theorem 5.1 identify $L_w\mu(W)=y_w(W)$.
Membership in (12.1) supplies all seven prefix values; the two
original seventh actions supply the last entries in (14.6).
No common terminal value is imposed on different alternatives or on
every companion. The fifth read between its two $M$ actions remains
one of the entries of each complete law. $\square$

## 15. Boundaries of the uniform approximation

**Proposition 15.1 (Initial support is not process dimension).**
The common finite space $\mathcal H_N$ constrains the initial
system preparations. It is not an invariant space for the original
controls, and (14.2) supplies no finite-dimensional replacement of
the full process.

*Proof.* Proposition 3.4 gives $A_MA_M^T\ne I$: the unchanged
$M$ control squeezes the vacuum. In position coordinates its image
has wavefunction proportional to
$\exp(-\|A_M^{-1}x\|^2/2)$. A finite reference-Fock expansion is
a polynomial in $x$ times $\exp(-\|x\|^2/2)$. Their ratio here is
an exponential of a nonzero quadratic form, which cannot be such a
polynomial. Thus even $U_{A_M}|0\rangle$ has infinite reference-Fock
support. Since $|0\rangle\in\mathcal H_N$ for every $N$, no such
cutoff space is invariant under this control.

The original probes still have carriers $L^2(\mathbb R)$ and
continuous position outcomes. Neither probe support nor pointer
alphabet is truncated in (14.1). Finite initial system support
therefore gives no finite protocol, invariant process dimension or
numerical total-resource bound. $\square$

**Proposition 15.2 (Why the full original domain is different).**
There is no uniform version of (12.6) or convergence in (13.3) on
the unrestricted $\mathcal W$ of Definition 1.1.

*Proof.* Fix $P=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}$
and $g=1$, and let $|d|\to\infty$. These are strict complete
worlds of $\mathcal W$, with $\lambda=(d^2+1)/2\to\infty$.
The original energy diverges. For each fixed finite $N$,
$e^{-\lambda}\sum_{n=0}^N\lambda^n/n!\to0$, so the exact input
distance $\sqrt{1-q_N}$ tends to one. In particular its supremum
on $\mathcal W$ is one for every $N$. This counterexample uses the
unrestricted domain, not a variation asserted to remain in $K_J$.
The whole-companion compactness premise is the additional datum
that makes the present restricted uniform conclusion possible.
$\square$

**Definition 15.3 (Operational and inferential scope).**
The normalized projection (13.1) specifies an approximating family
of labelled initial states. It does not prescribe a deterministic
physical preparation procedure or a channel encoding an unknown
native carrier. Interpreting $\Pi_N$ as a selective measurement
would require its own allowed operation and success treatment;
the normalization in (13.1) does not add that operation to the
original apparatus. Neither a preparation algorithm nor a numerical
upper bound on $B$ is supplied by compactness.

Equations (14.2)–(14.5) concern unconditional full record laws for
externally fixed words. They assert no bound after rare-event
conditioning, no pointwise control of conditional kernels at exact
histories, and no conclusion for an outcome-dependent action word.
A positive-probability conditioning estimate would require control
relative to that event's probability. Exact histories of the
original Gaussian law have probability zero, as in Theorem 7.2.
No new meaning of conditioning on such a point is introduced here.

Trace-distance and total-variation convergence control bounded
effects and record events. They do not by themselves supply an
energy-error estimate or errors for unbounded quadrature moments.
The covariance and Gaussian separability calculation of §§8–11
therefore is not transferred to the projected, generally
non-Gaussian inputs by this argument. Likewise, approximate laws
do not establish preservation of the exact law-equality fibres,
distinct-state counts or recursive predicates of §§6–7.

**Proposition 15.4 (The literal-history obstruction persists).**
For every $W\in K_J$, finite $N$ and fixed original word $w$,
the approximating law still fails the deterministic literal target:

$$
\nu_{w,N}(W)(\{y_w(W)\})=0,\qquad
\operatorname{TV}(\nu_{w,N}(W),\delta_{y_w(W)})=1.
\tag{15.1}
$$

*Proof.* With $\sigma>0$, (14.4) is a probability density on
$\mathbb R^{t+1}$, so every singleton is null. The Dirac measure
assigns mass one to the displayed singleton, giving (15.1).
Thus convergence to the original Gaussian law does not repair the
literal-process failure of Propositions 7.1 and 7.5. The classical
latent representation of the pointer family and the separate
internal-entanglement statement of Proposition 11.1 remain
different observable claims. No physical realization, quantum
advantage, minimum-resource or novelty conclusion is entailed by
this compactness application. $\square$

## 16. Sources and status of the mathematical application

**Definition 16.1 (Reused results and their substitutions).**
The source of whole-companion compactness is III at the immutable
revision linked in Definition 12.1: Definition 1.1 fixes complete
worlds; Theorem 16.4 supplies the actual arc and nonemptiness;
Definition 20.1 and Eq. (20.2) give the coordinate correspondence;
Definition 23.1, Theorem 23.2 and Corollary 23.3 give the entire
compact region, retained twenty-four fibre and qualitative bounds.
The compactness theorem is used as a premise, without substituting
a compact set of only selected representatives for $K_J$.

The Gaussian source is this volume's original §§1–7, also available
at [the same immutable revision](https://github.com/the-omega-institute/trureturing/blob/30b32d5e17e23590839090a0b244c019c4796817/docs/develop/theory/FIB_SHARED_GAUSSIAN_RECORD_LAWS.md):
Assumption 2.1 and Theorem 2.2 specify the preparation and energy;
Definition 3.1 and Theorem 3.2 fix the controls, clocks and rows;
Proposition 3.4 identifies squeezing; Assumption 4.1 and Theorem
4.2 provide the shared normal instruments; Theorem 5.1 gives the
exact full fixed-word Gaussian law and Kraus factorization;
Proposition 5.4 and §§6–7 distinguish adaptive words, indexed
fibres and literal acquired histories. The subsequent §§8–11
concern the internal pair and remain outside any moment-error
conclusion of this appendix.

The oscillator expansion and coherent-state number statistics are
literature-attested: R. J. Glauber, *Coherent and incoherent states
of the radiation field*, Physical Review **131**, 2766–2788,
[DOI:10.1103/PhysRev.131.2766](https://doi.org/10.1103/PhysRev.131.2766).
Here the amplitude is specifically $\alpha=\mu/\sqrt2$ and the
occupation is the sum over seventeen system modes. The pure-state
distance and effect variational characterization are the standard
trace-distance facts in M. A. Nielsen and I. L. Chuang, *Quantum
Computation and Quantum Information*, tenth-anniversary edition,
§9.2.1 (trace distance), with the fidelity comparison in §9.2.3,
[DOI:10.1017/CBO9780511976667](https://doi.org/10.1017/CBO9780511976667).
Their uses here require only a two-vector pure-state span and the
trace-class/effect pairing, respectively; no finite-dimensional
assumption on the process is introduced. The joint POVM's
infinite-dimensional normality comes from Theorem 4.2.

The compact extreme-value step, occupation tail bound and
stars-and-bars count are mature mathematical tools used inside
this application. The content of §§12–15 is their explicit
source-dependent composition for the entire $K_J$, the specified
seventeen-mode preparations and the unchanged full-pointer law.
It is an application of existing results, with no priority claim
and no new generic compactness or quantum-distance theorem.

## 追加锚（本行以下为增补区）

## 17. Product momentum-noise preparations on the same system

This appendix retains the complete original domain $\mathcal W$ of
Definition 1.1, the seventeen-mode system of Assumption 2.1, and the
shared controls, probes and acquisitions of §§3–4. It enlarges only
the initial preparation family. Write $\mu(W)=m_W$, as in (12.2),
and use $\pi$ for the vector of system momenta. All arguments below
are ordinary mathematical arguments for these specified states and
instruments.

The probes remain independent of one another and of the system,
with state $k_\sigma$, couplings
$\mathsf B_i=e^{-iF_i(q)\otimes\pi_i^{\rm pr}}$ and position meters
as in Assumption 4.1. No additional free evolution changes positions
between the prescribed operations. Each executed probe is used once
and every meter value is retained.

**Definition 17.1 (The enlarged preparation assumption).** For each
$W\in\mathcal W$ and finite $\eta\ge0$, supply the initial state

$$
\begin{gathered}
U_\xi=e^{-i\xi\cdot q},\qquad
\gamma_\eta=\mathcal N_{17}(0,\eta I_{17}),\qquad \gamma_0=\delta_0,\\
\mathcal M_\eta(\rho)
=\int_{\mathbb R^{17}}U_\xi\rho U_\xi^\dagger\,\gamma_\eta(d\xi),
\qquad \rho_{W,\eta}=\mathcal M_\eta(\rho_W).
\end{gathered}
\tag{17.1}
$$

For $\eta=0$ this is exactly $\rho_W$. For $\eta>0$, (17.1)
explicitly replaces the pure coherent preparation in Assumption 2.1
by a mixed preparation. The carrier, $\mu(W)$, apparatus and clock
labels retain their original definitions. Availability of this
enlarged family is a preparation assumption, with no supplied
procedure for obtaining it from an unknown native carrier.

In this appendix let

$$
s=\frac12+\eta,\qquad r=r_\sigma=\frac1{4\sigma^2}>0.
\tag{17.2}
$$

Here $r$ is the **probe-momentum variance**, not the matrix parameter
called $r$ in Definition 1.1. When needed, that world parameter is
written $P_{11}$. The original real program matrix remains $P$.
The seventeen initial system modes are distinct from the eight
supplied probe modes. The JM prefix uses three of those probes.

**Proposition 17.2 (Normal product Gaussian inputs).** The integral
in (17.1) defines a positive trace-class state of trace one. Its
position kernel and Weyl characteristic function are

$$
\begin{aligned}
\rho_{W,\eta}(x,y)
&=\psi_W(x)\overline{\psi_W(y)}
  e^{-\eta\|x-y\|^2/2},\\
\operatorname{tr}\!\left(\rho_{W,\eta}
e^{i(u\cdot q+v\cdot\pi)}\right)
&=\exp\!\left(iu\cdot\mu(W)-\frac{\|u\|^2}{4}
                    -\frac{s\|v\|^2}{2}\right).
\end{aligned}
\tag{17.3}
$$

Consequently it is a product of seventeen single-mode Gaussian
states, with no initial intermode entanglement, and

$$
\mathbb E q=\mu(W),\quad \mathbb E\pi=0,\qquad
V_{qq}=\frac12I_{17},\quad V_{\pi\pi}=sI_{17},\quad V_{q\pi}=0.
\tag{17.4}
$$

*Proof.* Strong continuity of $U_\xi$ implies trace-norm continuity
of $\xi\mapsto U_\xi\rho U_\xi^\dagger$ for every trace-class $\rho$;
one can first check finite-rank operators and then use trace-norm
approximation. Its trace norm is constant, so its probability
integral exists in trace class. Positivity and trace one pass to
that integral. Random-unitary averaging is completely positive
and trace preserving; its adjoint on bounded observables is normal,
as follows by monotone convergence in positive trace pairings.

The position kernel of each integrand is
$e^{-i\xi\cdot(x-y)}\psi_W(x)\overline{\psi_W(y)}$.
The characteristic function of $\gamma_\eta$ gives the first line
of (17.3), including the point-mass case. In particular its diagonal
is unchanged:

$$
\rho_{W,\eta}(x,x)=\pi^{-17/2}e^{-\|x-\mu(W)\|^2}.
\tag{17.5}
$$

Conjugating a Weyl operator by $U_\xi$ multiplies its original
coherent-state expectation by $e^{-iv\cdot\xi}$. Gaussian integration
gives the second line of (17.3) and hence (17.4). Both $\psi_W$ and
$\gamma_\eta$ factor over the seventeen initial coordinates. Thus

$$
\rho_{W,\eta}=\bigotimes_{j=1}^{17}
\left[\int e^{-i\xi_jq_j}
|\psi_{\mu_j(W)}\rangle\langle\psi_{\mu_j(W)}|
e^{i\xi_jq_j}\,\mathcal N(0,\eta)(d\xi_j)\right],
\tag{17.6}
$$

where $\psi_a(x)=\pi^{-1/4}e^{-(x-a)^2/2}$. This proves the product
claim. The same moments give the finite-per-world energy identity

$$
\operatorname{tr}(\rho_{W,\eta}H_{\rm osc})
=\frac{17}{2}+\frac{\|\mu(W)\|^2}{2}+\frac{17\eta}{2}.
\tag{17.7}
$$

It supplies no uniform bound on the unrestricted $\mathcal W$ and
no preparation-cost comparison. $\square$

## 18. Exact equality of every complete fixed-word record measure

Use the externally fixed menu
$\mathscr W_7=\bigcup_{t=0}^7\{J,M\}^t$ of Corollary 14.3.
For $w=E_1\cdots E_t$, every read $0,\ldots,t$ is executed and
retained, including read zero for the empty word. Define

$$
\nu_{w,\eta}(W)(B)
=\operatorname{tr}(\rho_{W,\eta}\mathsf E_w(B)),
\qquad B\in\mathcal B(\mathbb R^{t+1}),
\tag{18.1}
$$

using the same normal joint POVM as (14.1).

**Proposition 18.1 (An invariant complete-record effect).** For
every such $w,B$, the following are bounded-operator identities:

$$
\begin{aligned}
\mathsf K_w(z)&=U_{T_t}f_{w,z}(q),&
f_{w,z}(q)&=\prod_{i=0}^t k_\sigma(z_i-L_iq),\\
\mathsf K_w(z)^\dagger\mathsf K_w(z)
&=\prod_{i=0}^t|k_\sigma(z_i-L_iq)|^2,\\
\mathsf E_w(B)&=g_{w,B}(q),&
g_{w,B}(x)&=\int_B\prod_{i=0}^t
|k_\sigma(z_i-L_ix)|^2\,dz,\\
\mathcal M_\eta^*(\mathsf E_w(B))&=\mathsf E_w(B),&
0&\le g_{w,B}\le1.
\end{aligned}
\tag{18.2}
$$

The effect integrals are weak normal-instrument integrals, as in
Theorem 4.2 and Definition 14.1.

*Proof.* The first identity is the all-acquisition operator
factorization in Theorem 5.1. It uses only the specified controls
and multiplication operators and is independent of the input
state. Taking its adjoint product cancels $U_{T_t}$ and gives the
second identity. For each $x$, the product of the normalized probe
densities integrates to one over $\mathbb R^{t+1}$. Integrating
over $B$ therefore yields the Borel function $g_{w,B}$ between zero
and one; functional calculus gives the third identity.

Every $U_\xi$ commutes with this bounded position function. Hence

$$
\mathcal M_\eta^*(\mathsf E_w(B))
=\int U_\xi^\dagger g_{w,B}(q)U_\xi\,\gamma_\eta(d\xi)
=g_{w,B}(q).
\tag{18.3}
$$

The equalities hold in normal trace pairings. Positivity, boundedness
and the probability measures justify the exchanges of integration;
no operator-norm integral over the outcome space is required.
$\square$

**Corollary 18.2 (The unchanged full Gaussian laws).** Precisely,

$$
\begin{gathered}
\forall W\in\mathcal W,\quad \forall\eta\in[0,\infty),\quad
\forall\sigma\in(0,\infty),\quad \forall w\in\mathscr W_7,\\
\forall B\in\mathcal B(\mathbb R^{|w|+1}),\qquad
\nu_{w,\eta}(W)(B)=\nu_{w,0}(W)(B),\\
\nu_{w,\eta}(W)
=\mathcal N_{t+1}\!\left(L_w\mu(W),
\frac12L_wL_w^T+\sigma^2I_{t+1}\right),\qquad t=|w|.
\end{gathered}
\tag{18.4}
$$

*Proof.* Apply (18.3) to the trace pairing with $\rho_W$:

$$
\operatorname{tr}(\mathcal M_\eta(\rho_W)\mathsf E_w(B))
=\operatorname{tr}(\rho_W\mathcal M_\eta^*(\mathsf E_w(B)))
=\operatorname{tr}(\rho_W\mathsf E_w(B)).
\tag{18.5}
$$

This proves equality on every Borel event before using Gaussianity.
For completeness, the common full density is

$$
p_{w,\eta}(z\mid W)=\int_{\mathbb R^{17}}
\pi^{-17/2}e^{-\|x-\mu(W)\|^2}
\prod_{i=0}^t\frac{e^{-(z_i-L_ix)^2/(2\sigma^2)}}
{\sqrt{2\pi\sigma^2}}\,dx.
\tag{18.6}
$$

It is the law of $R_w=L_wX+\epsilon$ with the same independent
$X\sim\mathcal N_{17}(\mu(W),I_{17}/2)$ and
$\epsilon\sim\mathcal N_{t+1}(0,\sigma^2I_{t+1})$ as Theorem 5.1.
This gives the last line of (18.4). $\square$

Every intervening clock factor is present in (18.2) and (18.6).
The assertion concerns the complete fixed-word record measure,
rather than only its means or covariances. The restriction to
$\mathscr W_7$ keeps the original horizon; different words denote
different runs. No adaptive-word or conditional internal-state
equality is asserted here.

## 19. The actual nonselective JM pair and its uncertainty certificate

**Definition 19.1 (The enlarged-input pair).** Retain exactly the
system pair $q_A=q_{14}=X_{3,11}$, $q_B=q_{15}=X_{3,21}$,
$p_A=\pi_{14}$, $p_B=\pi_{15}$ of Definition 8.1, and set

$$
\begin{aligned}
\rho_{AB,\eta}^{W,\sigma}
&=\operatorname{Tr}_{\rm rest}
\bigl(\mathcal D_2\circ\mathcal U_M\circ\mathcal D_1
\circ\mathcal U_J\circ\mathcal D_0\bigr)(\rho_{W,\eta})\\
&=\operatorname{Tr}_{\rm rest}\int_{\mathbb R^3}
\mathsf K_{JM}(z)\rho_{W,\eta}\mathsf K_{JM}(z)^\dagger\,d^3z.
\end{aligned}
\tag{19.1}
$$

This first averages the actual retained records $(R_0,R_1,R_2)$
and then traces the other fifteen system modes. It is a two-mode
system marginal, with all probe modes excluded. At $\eta=0$ it is
$\rho_{AB}^{W,\sigma}$ of Definition 8.1.

**Proposition 19.2 (Common-probe reduction and covariance).** The
pair remains Gaussian. In ordering $(q_A,p_A,q_B,p_B)$ its mean is
$(a_3P_{11},0,a_3(P_{11}+P_{21}),0)$ and its centered covariance is

$$
V_\eta=\begin{pmatrix}
\frac12&0&\frac12&0\\
0&2s+65r&0&-s-r\\
\frac12&0&1&0\\
0&-s-r&0&s+r
\end{pmatrix}.
\tag{19.2}
$$

*Proof.* Proposition 8.2 gives pair-factorization of each control
and the pair components $(0,0),(1,0),(8,0)$ of the three laboratory
readout rows. To retain the actual probe correlation, split
$F_i=f_i^{AB}+f_i^{\rm rest}$ and write, for a single probe momentum
$u\sim\mathcal N(0,r)$,

$$
\mathcal D_i(\rho)=\int
(e^{-iu f_i^{AB}}\otimes e^{-iu f_i^{\rm rest}})\rho
(e^{-iu f_i^{AB}}\otimes e^{-iu f_i^{\rm rest}})^\dagger
\,\mathcal N(0,r)(du).
\tag{19.3}
$$

The same $u$ acts on pair and rest. Partial-trace invariance under
the rest unitary, valid also for correlated trace-class inputs,
gives

$$
\operatorname{Tr}_{\rm rest}\mathcal D_i(\rho)
=\int e^{-iu f_i^{AB}}(\operatorname{Tr}_{\rm rest}\rho)
e^{iu f_i^{AB}}\,\mathcal N(0,r)(du).
\tag{19.4}
$$

This justifies successive pair reduction of (19.1) without replacing
the common probe by independent pair and rest kicks. Read zero has
zero pair coefficient, while remaining an acquisition in the full
instrument and record.

Let $Q_A,Q_B,P_A,P_B$ be the initial pair quadratures, and rename
the probe momenta $\eta_i$ of Proposition 9.1 as $\zeta_i$ to
distinguish them from the preparation parameter $\eta$. The same
chronological pullback, which is independent of the input state,
gives

$$
\begin{gathered}
q_A=Q_A,\qquad q_B=Q_A+Q_B,\\
p_A=P_A-P_B+\zeta_1-8\zeta_2,\qquad
p_B=P_B-\zeta_1.
\end{gathered}
\tag{19.5}
$$

In the common input state,
$\operatorname{Var}Q_A=\operatorname{Var}Q_B=1/2$,
$\operatorname{Var}P_A=\operatorname{Var}P_B=s$, and each
$\operatorname{Var}\zeta_i=r$. Distinct initial system modes and
probes have zero centered cross covariance, and the initial
symmetrized position–momentum covariances vanish. Thus

$$
\begin{aligned}
\operatorname{Var}q_A&=\tfrac12,&
\operatorname{Var}q_B&=1,&
\operatorname{Cov}_{\rm sym}(q_A,q_B)&=\tfrac12,\\
\operatorname{Var}p_A&=2s+65r,&
\operatorname{Var}p_B&=s+r,&
\operatorname{Cov}_{\rm sym}(p_A,p_B)&=-s-r.
\end{aligned}
\tag{19.6}
$$

All centered position–momentum entries vanish, proving (19.2).
The initial Gaussian states, linear canonical controls, Gaussian
probe couplings and nonselective reductions give Gaussianity.
The means follow directly from (19.5). Their change with $W$ is
a product of local displacements on A and B, so it does not affect
entanglement. A lower degree, including $a_3=0$, changes the
displacement without removing either oscillator or its fluctuations.

The unbounded moments in this calculation are well defined. Each
phase-modulated input Gaussian has a Schwartz representative;
linear pullbacks and the probe shears preserve the corresponding
joint core. Integrating their quadratic forms is finite because
the preparation noise and actual Gaussian probes have finite
second moments. Equivalently, (19.5) expresses each required form
as a finite linear-quadrature Gaussian moment. These facts justify
the reduced-state moments, without applying a channel defined only
on bounded observables directly to an unbounded square. $\square$

**Proposition 19.3 (Physical uncertainty Schur certificate).** With
$\Omega=J_2\oplus J_2$, $J_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$,
the covariance obeys $V_\eta+i\Omega/2>0$ throughout the domain.

*Proof.* Reorder to $(q_A,q_B,p_A,p_B)$ and write

$$
V_\eta'=\mathsf Q\oplus\mathsf P,\qquad
\mathsf Q=\begin{pmatrix}\frac12&\frac12\\\frac12&1\end{pmatrix},
\quad
\mathsf P=\begin{pmatrix}2s+65r&-s-r\\-s-r&s+r\end{pmatrix},
\quad
\mathsf Q^{-1}=\begin{pmatrix}4&-2\\-2&2\end{pmatrix}.
\tag{19.7}
$$

Here $\mathsf P$ is a momentum covariance block, distinct from the
world's program matrix $P$. Since $\mathsf Q>0$, the uncertainty
matrix in this ordering is
$\begin{pmatrix}\mathsf Q&iI_2/2\\-iI_2/2&\mathsf P\end{pmatrix}$.
Its positivity is equivalent by Schur complementation to

$$
\begin{gathered}
\mathsf P-\frac14\mathsf Q^{-1}
=\begin{pmatrix}2\eta+65r&-\eta-r\\-\eta-r&\eta+r\end{pmatrix}>0,\\
\det\!\left(\mathsf P-\frac14\mathsf Q^{-1}\right)
=(\eta+r)(\eta+64r)>0.
\end{gathered}
\tag{19.8}
$$

Both diagonal entries are positive for $\eta\ge0,r>0$. This
certifies the physical covariance required by the separability
criterion, consistently with the normal-state construction.
$\square$

## 20. Exact two-mode separability and the preparation-noise root

Use the covariance convention of Proposition 9.2,
$V_{jk}=\langle\{\Delta\xi_j,\Delta\xi_k\}\rangle/2$ and
$[q_j,p_k]=i\delta_{jk}$. In this convention Simon's
[quant-ph/9909044v1](https://arxiv.org/pdf/quant-ph/9909044v1),
PDF p. 2, Eqs. (3), (6)–(7), uses the same quadrature ordering and
uncertainty normalization. Its PDF p. 4, Eq. (19), and the theorem
directly following it give the exact separability criterion for
the physical two-mode Gaussian state here.

**Proposition 20.1 (Simon polynomial and PPT Schur certificate).**
For (19.2), separability is equivalent to $D(s,r)\ge0$, where

$$
D(s,r)=\frac{s^2}{4}+\frac{65}{4}sr+16r^2
-\frac{3s}{4}-\frac{69r}{8}+\frac1{16}.
\tag{20.1}
$$

*Proof.* In the mode blocks of Simon's Eq. (16), PDF p. 3, put

$$
A=\operatorname{diag}(\tfrac12,2s+65r),\quad
B=\operatorname{diag}(1,s+r),\quad
C=\operatorname{diag}(\tfrac12,-s-r).
\tag{20.2}
$$

The substitution in Eq. (19) is explicitly

$$
\begin{aligned}
\det A&=s+\tfrac{65}{2}r,&\det B&=s+r,&\det C&=-\tfrac{s+r}{2}<0,\\
\operatorname{tr}(AJ_2CJ_2BJ_2C^TJ_2)
&=(s+r)(s+\tfrac{67}{4}r),\\
\det V_\eta&=\tfrac14(s+r)(s+64r),&
\widetilde\Delta&=\det A+\det B-2\det C=3s+\tfrac{69}{2}r.
\end{aligned}
\tag{20.3}
$$

Thus the left side minus right side of that separability inequality is

$$
\det A\det B+(\tfrac14-|\det C|)^2
-\operatorname{tr}(AJ_2CJ_2BJ_2C^TJ_2)
-\frac{\det A+\det B}{4}
=\det V_\eta+\frac1{16}-\frac{\widetilde\Delta}{4}=D(s,r).
\tag{20.4}
$$

Independently, partial transpose on B changes $p_B$ to $-p_B$.
In the reordered covariance it changes the signs of the off-diagonal
entries of $\mathsf P$. The Schur complement of its uncertainty
matrix is therefore

$$
H_\Gamma=\begin{pmatrix}
2\eta+65r&\eta+r+1\\\eta+r+1&\eta+r
\end{pmatrix},\qquad
\det H_\Gamma=\eta^2+(65r-2)\eta+64r^2-2r-1
=4D(\tfrac12+\eta,r).
\tag{20.5}
$$

Both diagonal entries are strictly positive, so $H_\Gamma\ge0$
holds exactly when $D\ge0$. This confirms the sign and equality
case. PPT is sufficient for separability here because the state is
physical, Gaussian, and consists of one mode on each side of A|B;
no arbitrary-state PPT sufficiency is used. $\square$

**Proposition 20.2 (Exact root and endpoints).** Define

$$
\eta_\pm(r)=\frac{2-65r\pm\sqrt{(63r-2)^2+4}}2,
\qquad \eta_c(r)=\max\{0,\eta_+(r)\}.
\tag{20.6}
$$

Then, for every $W$, finite $\sigma>0$ and finite $\eta\ge0$,

$$
\begin{aligned}
\rho_{AB,\eta}^{W,\sigma}\text{ is separable}
&\iff \eta\ge\eta_c(r),\\
\rho_{AB,\eta}^{W,\sigma}\text{ is entangled}
&\iff 0\le\eta<\eta_c(r).
\end{aligned}
\tag{20.7}
$$

*Proof.* The roots in (20.6) are those of the quadratic (20.5),
whose discriminant is $(63r-2)^2+4$. Since its square root is at
least two, $\eta_-(r)\le-65r/2<0$. The positive leading coefficient
then makes the quadratic nonnegative on the allowed domain exactly
at and above the upper root, or everywhere when that root is
nonpositive. This proves (20.7), with equality on the separable side.
In particular $\partial_\eta(4D)=2\eta+65r-2$ can be negative:
the conclusion uses root location, not global monotonicity of $D$.

For a precise distinction between a root and a domain endpoint, set

$$
r_0=\frac{1+\sqrt{65}}{64},\qquad
D(\tfrac12,r)=\frac{64r^2-2r-1}{4}.
\tag{20.8}
$$

For $0<r<r_0$, $\eta_c=\eta_+>0$ and its value is a Simon equality
point. At $r=r_0$, $\eta_c=0$ and $D(1/2,r_0)=0$.
For $r>r_0$, $\eta_+<0$ and $D>0$ for every $\eta\ge0$;
the clipped value $\eta_c=0$ is only the preparation domain's edge.
The complete equality locus is $\eta=\eta_+(r)$ with $0<r\le r_0$.
At $\eta=0$ this recovers Proposition 10.2 exactly:

$$
\rho_{AB,0}^{W,\sigma}\text{ is separable}
\iff r\ge r_0
\iff 0<\sigma\le\frac4{\sqrt{1+\sqrt{65}}}.
\tag{20.9}
$$

No nondegeneracy assumption on the original world enters. $\square$

The fixed Duan witness in Proposition 10.1 retains its limited role.
With $u=q_B-q_A$ and $v=p_A+p_B$, (19.5) gives

$$
u=Q_B,\quad v=P_A-8\zeta_2,\qquad
\operatorname{Var}(u)+\operatorname{Var}(v)=1+\eta+64r.
\tag{20.10}
$$

Duan–Giedke–Cirac–Zoller,
[quant-ph/9908056v2](https://arxiv.org/pdf/quant-ph/9908056v2),
Eqs. (2a)–(2b), Theorem 1 and Eq. (3), PDF pp. 1–2, give the
separable lower bound two under the same commutator convention.
Use their $a=1$, $(x_1,p_1)=(q_B,p_B)$ and
$(x_2,p_2)=(-q_A,-p_A)$, the local-parity substitution of §10.
This proves entanglement when $\eta+64r<1$. Failure of this one
witness to violate its bound supplies no separability conclusion;
the exact classification is (20.7).

## 21. A rational same-record pair and failure of identifiability

**Proposition 21.1 (A common apparatus and two actual preparations).**
Fix $\sigma=2$, hence $r=1/16$. For every original $W$, compare
$\rho_{W,0}$ and $\rho_{W,1}$. Their actual JM pair covariances have
the same $\mathsf Q$ in (19.7), and respectively

$$
\mathsf P_{\eta=0}=\frac1{16}\begin{pmatrix}81&-9\\-9&9\end{pmatrix},
\qquad
\mathsf P_{\eta=1}=\frac1{16}\begin{pmatrix}113&-25\\-25&25\end{pmatrix}.
\tag{21.1}
$$

The first pair is entangled and the second separable, although
their complete fixed-word record laws coincide for every
$w\in\mathscr W_7$.

*Proof.* Direct substitution in (19.7) and (20.1) gives

$$
D(\tfrac12,\tfrac1{16})=-\frac7{32}<0,\qquad
D(\tfrac32,\tfrac1{16})=\frac{35}{64}>0,
\qquad
\eta_c(\tfrac1{16})=\frac{\sqrt{1985}-33}{32}\in(0,1).
\tag{21.2}
$$

Apply (20.7) to classify the two physical Gaussian pair states and
(18.4) to obtain equality of all complete record measures.
Both inputs are product states before the protocol. Only the
explicit preparation assumption changes between them. $\square$

For a concrete legal world take

$$
P=\begin{pmatrix}\frac12&\frac12\\\frac12&\frac12\end{pmatrix},
\qquad g(t)=1,\qquad d=0.
\tag{21.3}
$$

Its $P_{11}=b=c=1/2$ obey the strict original domain conditions,
and its nonzero constant polynomial has $a_3=0$. For both
preparations its entire three-read JM record is

$$
(R_0,R_1,R_2)\sim\mathcal N_3\!\left(
\begin{pmatrix}1\\1\\3/2\end{pmatrix},
\begin{pmatrix}11/2&1/2&3/2\\1/2&17/2&8\\3/2&8&132\end{pmatrix}
\right).
\tag{21.4}
$$

Indeed Theorem 3.2 gives means $(1,1,3/2)$ and row inner products
$\|L_0\|^2=3$, $\|L_1\|^2=9$, $\|L_2\|^2=256$,
$L_0L_1^T=1$, $L_0L_2^T=3$, $L_1L_2^T=16$.
Adding $4I_3$ to half this Gram matrix proves (21.4). This world
illustrates the retained record; Proposition 21.1 holds on all
$\mathcal W$, without restricting to this example or to $K_J$.
The fixed Duan sum is already five for its entangled $\eta=0$
pair, illustrating why nonviolation does not classify that pair.

**Corollary 21.2 (The identifiability implication).** At $\sigma=2$,
no function of the entire family of complete fixed-word population
laws can correctly determine JM pair entanglement for every member
of the enlarged preparation family.

*Proof.* Define the observation of an input $\rho$ by

$$
\mathcal O_\sigma(\rho)
=\bigl(B\mapsto\operatorname{tr}(\rho\mathsf E_w(B))
\bigr)_{w\in\mathscr W_7}.
\tag{21.5}
$$

Equations (18.4) and (21.2) give, for each identical world $W$,
$\mathcal O_2(\rho_{W,0})=\mathcal O_2(\rho_{W,1})$, while the
entanglement indicators of their states (19.1) differ. A function
of that observation would have to assign the same value to both
inputs. It therefore cannot equal the entanglement indicator on
the whole enlarged family. Even supplying the common world label
would leave this pair unresolved by these laws. $\square$

More generally, when $\sigma>4/\sqrt{1+\sqrt{65}}$, each fixed-$W$
family $\{\rho_{W,\eta}:\eta\ge0\}$ lies in one observation fibre
containing both kinds of JM marginal, by (20.7)–(20.9).
At and below that apparatus
threshold this particular family consists entirely of separable
JM marginals. The counterexample concerns the enlarged preparation
class; it does not contradict the original unique coherent-input
classification.

## 22. The least preparation noise uniform over finite probe widths

**Proposition 22.1 (Sharp uniform threshold for this JM marginal).**
For finite $\eta\ge0$, the exact uniform statement is

$$
\left[\forall\sigma\in(0,\infty)\ \forall W\in\mathcal W,
\quad \rho_{AB,\eta}^{W,\sigma}\text{ is separable}\right]
\iff \eta\ge\eta_*:=1+\sqrt2.
\tag{22.1}
$$

For every $0\le\eta<\eta_*$ there is a finite $\sigma>0$ such that
the pair is entangled for every $W$.

*Proof.* The untruncated upper root in (20.6) satisfies

$$
\eta_+'(r)=\frac12\left(-65+
\frac{63(63r-2)}{\sqrt{(63r-2)^2+4}}\right)<-1,
\qquad \lim_{r\downarrow0}\eta_+(r)=1+\sqrt2.
\tag{22.2}
$$

Thus $\sup_{r>0}\eta_c(r)=1+\sqrt2$, and this supremum is not
attained at any positive $r$. The threshold (20.7) proves
sufficiency in (22.1). At $\eta=\eta_*$ it even gives strict PPT:

$$
4D(\tfrac12+\eta_*,r)
=r\bigl(64r+63+65\sqrt2\bigr)>0\qquad(r>0).
\tag{22.3}
$$

For sharpness, if $0\le\eta<\eta_*$, the polynomial (20.5) at
$r=0$ equals $\eta^2-2\eta-1<0$. Continuity gives some strictly
positive, sufficiently small $r$ for which it remains negative.
The corresponding $\sigma=1/(2\sqrt r)$ is finite. Its covariance
is independent of $W$, so the JM pair is entangled for every
original world. This proves necessity and the final assertion.
$\square$

The limit $r\downarrow0$ computes a supremum. An infinite-variance
probe at $\sigma=\infty$ is not an apparatus preparation. The
constant $\eta_*$ belongs to this product-input family, these
controls, all three actual nonselective reads and this selected
two-mode marginal. It is not a general entanglement-breaking
threshold for the random momentum-displacement channel.

## 23. Measurement interface, reused criteria and applicability

The informational restriction can also be stated directly at the
Gaussian-observable interface. Fourier-transforming the full
record effect in (18.2), for $h\in\mathbb R^{t+1}$, gives

$$
\widehat{\mathsf E}_w(h)
:=\int e^{ih^Tz}\,\mathsf E_w(dz)
=e^{-\sigma^2\|h\|^2/2}e^{i(L_w^Th)\cdot q}.
\tag{23.1}
$$

Kiukas–Schultz, *Informationally complete sets of Gaussian
measurements*, [arXiv:1308.2083v1](https://arxiv.org/pdf/1308.2083v1),
§V, Eq. (9) and Theorem 1 (PDF pp. 4–5), characterize informational
completeness by density of the union of Weyl sampling subspaces in
the full phase space. Their convention is
$W(x)=e^{-ix^T\Omega_{17}\xi}$, where
$\Omega_{17}=\bigoplus_{j=1}^{17}J_2$ and
$\xi=(q_1,\pi_1,\ldots,q_{17},\pi_{17})$.
For (23.1), their matrix $A_0$ has odd rows zero and even rows
$L_w^T$, their noise matrix is $B_0=2\sigma^2I_{t+1}$, and their
offset $v_0=0$. Their covariance convention is twice the
half-anticommutator convention used here.

Every sampling vector $A_0h$ therefore lies in the same closed
seventeen-dimensional subspace of $\mathbb R^{34}$, corresponding
to characteristic functions of positions alone. The union is not
dense in full phase space, so this fixed-word measurement family
is not informationally complete on unrestricted normal states.
That general statement alone would not establish failure to
identify a particular entanglement property. The actual
entangled/separable pair in §21 supplies that stronger conclusion
on the stated preparation family.

The reused interfaces are precise: Theorem 5.1 and Definition 14.1
supply the input-independent normal joint effect; Proposition 8.2
supplies common-probe pair reduction; Proposition 9.1 supplies the
chronological quadrature identities. Simon's physical two-mode
Gaussian criterion supplies the separability equivalence, and
Duan's variance inequality supplies only its stated sufficient
witness. The momentum-noise kernel, its invariant complete effects,
the resulting covariance substitution, the explicit separating pair
and the sharp uniform constant are their source-specific
composition for this FIB apparatus. No new general separability or
tomography theorem is asserted.

The exact Gaussian classification here uses (17.1), not the Fock
projections $\rho_{W,N}$ of §§12–16. Their trace-distance and
record-law approximation does not transfer this covariance or
separability classification to their generally non-Gaussian inputs.
All world quantifiers above are pointwise in the complete original
$W$; no arbitrary mixture over world labels is classified. The
state conclusion concerns only (19.1), not conditional branches,
other pairs or separability of the full seventeen-mode output.
The record conclusion retains only externally fixed words through
the original seventh clock.

The preparation and ideal apparatus remain explicit availability
assumptions. These results supply no physical implementation,
unknown-carrier encoding, quantum advantage or resource equivalence.
The positive-noise literal-history obstruction of §§7 and 15
remains. The proofs in this appendix are ordinary analytic proofs,
without a kernel-verification claim.

## 追加锚（本行以下为增补区）
