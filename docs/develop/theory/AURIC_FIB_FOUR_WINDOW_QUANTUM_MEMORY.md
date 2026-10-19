# AURIC FIB Four-Window Partial Quantum Memory

> This volume is an appendable mathematical reference in `generic-v1`
> Markdown. Existing text and numbering remain fixed after incorporation;
> corrections and extensions follow the final append anchor and identify the
> statements they qualify or supersede.

## 1. Scope and the exact memory question

**Convention 1.1 (Mathematical status and ownership).** This volume concerns
finite-dimensional complex channels and ordinary mathematical proofs. The
retained algebra is $M_8(\mathbb C)$, indexed by the eight legal four-bit words.
The owning five-dimensional, three-bit-window theory is [M5][M5]; its theorems
are not being restated as eight-dimensional conclusions. The classical source
interfaces remain owned by [LocalClock][LC] and [Pyramid][PY]. Standard exact
quantum correction is a literature input, used with the explicit hypotheses
and proofs below. The model-specific deductions here are `repo-derived` in
this sense; this attribution makes no literature priority or novelty claim.
These are conditional mathematical statements, without a claim of Lean kernel
verification, physical realization, or asymptotic quantum capacity.

**Convention 1.2 (One retained system and one channel).** Fix one parameter
$0<\eta<1$ for the entire discussion, and write $r=1-\eta$. A chronological
step applies one fixed homogeneous CPTP map $\Phi:M_8\to M_8$. The same map is
repeated at every step. Every application has a fresh environment, which is
traced out; no old bit, environment, outcome, or history register is retained.
Only a terminal CPTP decoder on the entire $M_8$ output is permitted. External
reference systems are arbitrary and are never added to the retained output.
Logical and syndrome factors below are coordinates on subspaces of
$\mathbb C^8$, rather than additional retained systems. A chronological slide
is an index operation, with no physical time calibration assumed.

**Definition 1.3 (Exact subspace dimension).** Let $\mathcal H=\mathbb C^8$.
For an allowed channel as defined in §3, let $k_n(\Phi)$ be the largest integer
$k$ for which there are a complex isometry $J:\mathbb C^k\to\mathcal H$ and a
CPTP map $\mathcal R:M_8\to M_8$ satisfying

$$
\mathcal R\Phi^n(JXJ^\dagger)=JXJ^\dagger
\qquad\text{for every }X\in M_k(\mathbb C).
\tag{1.1}
$$

Set $k_0(\Phi)=8$ and

$$
K_n(\eta)=\max_{\Phi\text{ allowed at }\eta} k_n(\Phi).
\tag{1.2}
$$

The allowed class is nonempty by the canonical construction in §8. The maximum
in (1.2) exists because the achieved dimensions form a nonempty subset of
$\{1,\ldots,8\}$. Different $n$ may use different codes and decoders. Even when
optimizing $K_n$, each candidate uses a single channel throughout its $n$
applications. Codes are arbitrary complex subspaces, with no coordinate,
real, stabilizer, or prescribed-encoding restriction. Equation (1.1) on all
complex matrices implies its tensor extension with every external reference.

**Proposition 1.4 (Prefix monotonicity and the trivial dimension).** For every
allowed $\Phi$,

$$
1\le k_{n+1}(\Phi)\le k_n(\Phi)\le8,
\qquad K_{n+1}(\eta)\le K_n(\eta).
\tag{1.3}
$$

Proof. If $\mathcal R$ corrects $\Phi^{n+1}$, then $\mathcal R\Phi$ corrects
$\Phi^n$. More generally, $\mathcal R\Phi^{n-j}$ is a decoder for a prefix
$\Phi^j$. This is a mathematical consequence of terminal correction; it does
not insert any operation into the original evolution. Every one-dimensional
code $\mathbb C\psi$ is corrected by the terminal reset
$Y\mapsto\operatorname{Tr}(Y)|\psi\rangle\langle\psi|$. Taking maxima proves
the last inequality. $\square$

## 2. The inherited source and the chronological four-bit interface

**Convention 2.1 (Selected source and native-operation boundary).** The
fixed finite-activity source of [LocalClock, Proposition 15.8][LC], also used
in [M5, §3][M5], supplies

$$
P=\begin{pmatrix}r&\eta\\1&0\end{pmatrix},\qquad
\pi=\frac{(1,\eta)}{1+\eta},\qquad
\lambda=\frac{\eta}{r^2},\qquad \Lambda=\frac1r.
\tag{2.1}
$$

Its hypotheses include fixed compatible nonnegative endpoint factors and a
body observation receding from both endpoints. The normalization is the
Perron conjugation

$$
H_\lambda=\begin{pmatrix}1&\lambda\\1&0\end{pmatrix}
=\Lambda\operatorname{diag}(\Lambda,1)P
\operatorname{diag}(\Lambda,1)^{-1},
\tag{2.2}
$$

rather than independent normalization of the guard-matrix rows. Existence of
this source and its body limit are used from that owning result. The
unit-activity golden specialization is [LocalClock, Proposition 15.6][LC].

A general stationary no11 source is a different object. [Pyramid, Theorem
17.3 and §§17–18][PY] own its stationary triple constraints and its explicitly
selected second-order extension. At the parameters
$t=\eta/(1+\eta)$ and $\kappa=\eta^2/(1+\eta)$, the extension's two free
transition parameters both equal $\eta$, giving (2.1). This does not identify
all sources with the same local marginal. The actual same-triple-law sources
of [Pyramid, Proposition 17.4][PY] have distinct distance-three probabilities;
that inherited counterexample supplies the distinction without another proof
here. The native complete-window operation of [LocalClock, Definition
15.1][LC] includes a guard and an unbounded composition state with
$C'=M^3C+d_s$. It is not the chronological overlap step used in this volume.
No native affine operation is being made into a quantum operation by (2.1).

**Definition 2.2 (Alphabet and chronological kernel).** Let $\Omega_m$ denote
the binary words of length $m$ containing no adjacent ones. In the fixed
order

$$
\begin{aligned}
\Omega_4&=(0000,0001,0010,0100,0101,1000,1001,1010),\\
(A,B,C,D,E,F,G,H)&=(0000,0001,0010,0100,0101,1000,1001,1010),
\end{aligned}
\tag{2.3}
$$

use the corresponding orthonormal basis $|A\rangle,\ldots,|H\rangle$ of
$\mathcal H$. The letter $H$ in a ket is the last word, while $\mathcal H$
denotes the space. Under the selected stationary first-order source, set

$$
p_4(s)=\pi_{s_1}\prod_{j=1}^3P_{s_j,s_{j+1}},\qquad
Q_4(s,t)=\mathbf1_{s_2s_3s_4=t_1t_2t_3}P_{s_4,t_4}.
\tag{2.4}
$$

The row index of $Q_4$ is the input. In order (2.3),

$$
Q_4=
\begin{pmatrix}
r&\eta&0&0&0&0&0&0\\
0&0&1&0&0&0&0&0\\
0&0&0&r&\eta&0&0&0\\
0&0&0&0&0&r&\eta&0\\
0&0&0&0&0&0&0&1\\
r&\eta&0&0&0&0&0&0\\
0&0&1&0&0&0&0&0\\
0&0&0&r&\eta&0&0&0
\end{pmatrix}.
\tag{2.5}
$$

**Proposition 2.3 (The selected four-window law and its powers).** The vector
$p_4$ is a strictly positive stationary probability vector for $Q_4$. For every
$n\ge3$ and $s,t\in\Omega_4$,

$$
Q_4^n(s,t)=(P^{n-3})_{s_4,t_1}
\prod_{j=1}^3P_{t_j,t_{j+1}}.
\tag{2.6}
$$

In particular, $Q_4^5$ is entrywise strictly positive.

Proof. Summing (2.4) over all legal continuations successively uses the row
sums of $P$ and finally $\pi_0+\pi_1=1$. Every legal internal transition has
positive weight, so $p_4(s)>0$. Direct multiplication gives $\pi P=\pi$.
For a fixed output $t$, its possible predecessors have the form
$(a,t_1,t_2,t_3)$. Summing their stationary mass times the final transition
uses $\sum_a\pi_aP_{a,t_1}=\pi_{t_1}$ and yields $p_4(t)$. The Markov
assumption on the selected full source makes appending the next bit depend
only on the current last bit, which gives precisely $Q_4$.

After three shifts, the first position of the output is the original last
bit. After $n\ge3$ shifts it is reached by $n-3$ transitions from $s_4$;
the other three output positions then have their displayed internal path
weight. Summing intermediate bits proves (2.6), including the $P^0$ case.
Finally,

$$
P^2=\begin{pmatrix}r^2+\eta&r\eta\\r&\eta\end{pmatrix}>0,
\tag{2.7}
$$

and all legal internal path weights are positive, proving the last assertion.
$\square$

The first-order source choice, its four-bit marginal, the chronological
kernel, and the quantum lift constraint below are separate mathematical
specifications. A local marginal alone does not supply the conditional law
used in the proof of Proposition 2.3.

## 3. The complete complex thirteen-edge lift class

**Definition 3.1 (All-input law and conventions).** An allowed lift is a
complex-linear CPTP map $\Phi:M_8\to M_8$ satisfying

$$
\operatorname{diag}\Phi(X)=Q_4^{\mathsf T}\operatorname{diag}X
\qquad(X\in M_8(\mathbb C)).
\tag{3.1}
$$

Here $\operatorname{diag}X$ is a column, $\mathsf T$ is ordinary transpose,
and inner products are conjugate-linear in their first argument. The symbol
$\dagger$ denotes adjoint. A projection onto a coordinate subspace with
labels $S$ is $P_S$. Off-diagonal and non-Hermitian inputs are included in
(3.1). Output coherences are permitted. Thus (3.1) is stronger than assigning
only the populations of the eight basis inputs, or the scalar diagonal of a
Choi matrix.

The thirteen positive-probability edges are the following. The label $(t,s)$
means output $t$ and input $s$.

| Retained three-bit suffix | Input subspace | Outputs from each input and probabilities | Number of edges |
| --- | --- | --- | --- |
| $000$ | $\operatorname{span}\{A,F\}$ | $A:r$, $B:\eta$ | $4$ |
| $001$ | $\operatorname{span}\{B,G\}$ | $C:1$ | $2$ |
| $010$ | $\operatorname{span}\{C,H\}$ | $D:r$, $E:\eta$ | $4$ |
| $100$ | $\operatorname{span}\{D\}$ | $F:r$, $G:\eta$ | $2$ |
| $101$ | $\operatorname{span}\{E\}$ | $H:1$ | $1$ |

**Theorem 3.2 (Necessary and sufficient complex Gram description).** The
allowed lifts are exactly the maps

$$
\begin{aligned}
V|s\rangle&=\sum_{t:Q_4(s,t)>0}
\sqrt{Q_4(s,t)}\,|t\rangle\otimes e_{t,s},\\
\Phi(X)&=\operatorname{Tr}_{\mathcal E}(VXV^\dagger),
\end{aligned}
\tag{3.2}
$$

where the thirteen $e_{t,s}$ are unit vectors, and precisely the following
five pairs are prescribed to be orthogonal:

$$
\begin{aligned}
e_{A,A}&\perp e_{A,F},& e_{B,A}&\perp e_{B,F},\\
e_{C,B}&\perp e_{C,G},\\
e_{D,C}&\perp e_{D,H},& e_{E,C}&\perp e_{E,H}.
\end{aligned}
\tag{3.3}
$$

All remaining inner products can be arbitrary complex numbers subject to
positivity of the complete thirteen-by-thirteen Gram matrix. Equivalently,
choose any complex Hermitian matrix $G\succeq0$ with diagonal one and the five
zero pairs in (3.3), using $G_{ab}=\langle e_a,e_b\rangle$. Every such $G$
realizes an allowed lift. It is sufficient to use $2\le\dim\mathcal E\le13$;
no dimension bound on a supplied dilation is required.

Proof. A finite-dimensional CPTP map has an isometric Stinespring dilation.
Write any such dilation as $V|s\rangle=\sum_t|t\rangle\otimes v_{t,s}$.
Apply (3.1) to every complex matrix unit $|s\rangle\langle s'|$. Its $t$th
output diagonal entry gives

$$
\langle v_{t,s'},v_{t,s}\rangle
=\delta_{s,s'}Q_4(s,t).
\tag{3.4}
$$

For $s=s'$, a zero probability forces $v_{t,s}=0$; a positive probability
gives the normalization in (3.2). For $s\ne s'$, (3.4) requires orthogonality
only when two allowed edges share the same output. The table lists all such
pairs, exactly (3.3). No other matrix element occurs in (3.4).

Conversely, the stated vector conditions give (3.4), hence every output
diagonal entry of (3.1), for every matrix unit and therefore every complex
matrix. They also imply

$$
\langle Vs',Vs\rangle
=\sum_t\delta_{s,s'}Q_4(s,t)=\delta_{s,s'},
\tag{3.5}
$$

so $V$ is isometric. Partial trace is CP, and (3.5) makes the resulting map
TP. A PSD matrix with diagonal one is realized by a family of unit vectors
by taking a matrix square root; the prescribed zero entries give (3.3).
Their span has dimension $\operatorname{rank}G\le13$, while one prescribed
orthogonal pair forces dimension at least two. Replacing any larger dilation
by this span changes no channel matrix element. $\square$

**Convention 3.3 (Choi and Kraus coordinates).** In the output-first Choi
convention

$$
\mathsf C_\Phi=\sum_{s,s'}\Phi(|s\rangle\langle s'|)
\otimes |s\rangle\langle s'|,
$$

its allowed-edge entries are

$$
(\mathsf C_\Phi)_{(t,s),(t',s')}
=\sqrt{Q_4(s,t)Q_4(s',t')}
\langle e_{t',s'},e_{t,s}\rangle.
\tag{3.6}
$$

Thus (3.1) fixes the whole output-diagonal Choi blocks:
$(\mathsf C_\Phi)_{(t,s),(t,s')}=\delta_{s,s'}Q_4(s,t)$.
The order of the inner product in (3.6) is essential for complex entries.
The Choi matrix is unnormalized and has trace eight. In an orthonormal basis
$|\alpha\rangle$ of the environment, use

$$
A_\alpha=\sum_{(t,s)\text{ allowed}}
\sqrt{Q_4(s,t)}\,(e_{t,s})_\alpha|t\rangle\langle s|,
\qquad (e_{t,s})_\alpha=\langle\alpha|e_{t,s}\rangle.
\tag{3.7}
$$

These are Kraus operators of the same $\Phi$; their actual linear span,
rather than the entire space of graph-supported matrices, will matter in §11.

## 4. Reset algebra and the actual identity-output spectrum

**Proposition 4.1 (Deterministic-output reset algebra).** Every allowed lift
satisfies

$$
\begin{aligned}
\Phi(|B\rangle\langle B|)&=|C\rangle\langle C|,&
\Phi(|G\rangle\langle G|)&=|C\rangle\langle C|,\\
\Phi(|B\rangle\langle G|)&=0,&
\Phi(|G\rangle\langle B|)&=0,\\
\Phi(X)&=\operatorname{Tr}(X)|C\rangle\langle C|
&&\bigl(X\in\mathcal B(\operatorname{span}\{B,G\})\bigr),\\
\Phi(|E\rangle\langle E|)&=|H\rangle\langle H|.
\end{aligned}
\tag{4.1}
$$

Proof. The only output from either $B$ or $G$ is $C$, so their dilation
vectors are $|C\rangle e_{C,B}$ and $|C\rangle e_{C,G}$. Their environment
vectors are orthogonal by (3.3). Partial tracing the four complex matrix units
therefore gives the first four equalities and the entire reset algebra, by
linearity. The unique output from $E$ is $H$, with a unit environment vector,
giving the last equality. $\square$

**Proposition 4.2 (Forced spectrum and rank).** In the orthogonal block order
$AB\,|\,C\,|\,DE\,|\,FG\,|\,H$, the actual positive matrix $\Phi(I_8)$ is

$$
\Phi(I_8)=
\begin{pmatrix}2r&z_1\\\overline z_1&2\eta\end{pmatrix}
\oplus[2]\oplus
\begin{pmatrix}2r&z_2\\\overline z_2&2\eta\end{pmatrix}
\oplus
\begin{pmatrix}r&z_3\\\overline z_3&\eta\end{pmatrix}
\oplus[1],
\tag{4.2}
$$

where

$$
\begin{aligned}
z_1&=\sqrt{r\eta}\bigl(
\langle e_{B,A},e_{A,A}\rangle+
\langle e_{B,F},e_{A,F}\rangle\bigr),\\
z_2&=\sqrt{r\eta}\bigl(
\langle e_{E,C},e_{D,C}\rangle+
\langle e_{E,H},e_{D,H}\rangle\bigr),\\
z_3&=\sqrt{r\eta}\langle e_{G,D},e_{F,D}\rangle.
\end{aligned}
\tag{4.3}
$$

Consequently its spectrum, with multiplicities, is

$$
\left\{
2,\ 1,
1\pm\sqrt{(r-\eta)^2+|z_1|^2},
1\pm\sqrt{(r-\eta)^2+|z_2|^2},
\frac{1\pm\sqrt{(r-\eta)^2+4|z_3|^2}}2
\right\}.
\tag{4.4}
$$

In particular $2$ and $1$ are forced eigenvalues, and

$$
\operatorname{rank}\Phi(I_8)\ge5,\qquad
\operatorname{Tr}\Phi(I_8)=8,\qquad \Phi(I_8)\ne I_8.
\tag{4.5}
$$

Proof. Expand $\Phi(I_8)=\sum_s\Phi(|s\rangle\langle s|)$ using (3.2).
Each input's possible outputs belong to just one block in (4.2), so there
are no cross-block entries. Inputs $A,F$ give the first block, $B,G$ the
singleton $[2]$, $C,H$ the second two-dimensional block, $D$ the third, and
$E$ the singleton $[1]$. Computing their off-diagonal entries gives (4.3).
The elementary two-by-two characteristic polynomials give (4.4).

Positivity gives $|z_1|,|z_2|\le2\sqrt{r\eta}$ and
$|z_3|\le\sqrt{r\eta}$. Each two-dimensional block is positive with strictly
positive trace, hence has rank at least one. Together with the two singleton
blocks this gives rank at least five. The block traces add to eight; the
forced eigenvalue two prevents unitality of $\Phi$. This argument uses an
actual block decomposition, rather than treating the diagonal entries of a
general positive matrix as its eigenvalues. $\square$

## 5. Exact adjoint effects at one, two, three, and four steps

**Proposition 5.1 (Full dual law).** Let

$$
F_t^{(n)}=(\Phi^\dagger)^n(|t\rangle\langle t|),
\qquad t\in\Omega_4,\quad n\ge0.
$$

For every allowed lift,

$$
F_t^{(n)}=\operatorname{diag}_{s\in\Omega_4}Q_4^n(s,t).
\tag{5.1}
$$

In particular the diagonal observable algebra is invariant under
$\Phi^\dagger$. This adjoint is positive and unital.

Proof. Pair $|t\rangle\langle t|$ with the outputs of every complex matrix
unit in (3.1). This gives (5.1) for $n=1$, including zero off-diagonal
entries. Linearity gives invariance of the diagonal algebra, and iteration
then gives every $n$. Complete positivity implies positivity of the adjoint;
TP of $\Phi$ gives $\Phi^\dagger(I_8)=I_8$. Unitality here does not assert
that either map is unitary conjugation. $\square$

**Proposition 5.2 (The compressed-rank input data).** The effects at the first
two steps are as follows. Put

$$
U_{00}=\operatorname{span}\{A,D,F\},\quad
U_{01}=\operatorname{span}\{B,E,G\},\quad
U_{10}=\operatorname{span}\{C,H\}.
\tag{5.2}
$$

| Output $t$ | $F_t^{(1)}$ | $F_t^{(2)}$ |
| --- | --- | --- |
| $A$ | $rP_{AF}$ | $r^2P_{U_{00}}$ |
| $B$ | $\eta P_{AF}$ | $r\eta P_{U_{00}}$ |
| $C$ | $P_{BG}$ | $\eta P_{U_{00}}$ |
| $D$ | $rP_{CH}$ | $rP_{U_{01}}$ |
| $E$ | $\eta P_{CH}$ | $\eta P_{U_{01}}$ |
| $F$ | $rP_D$ | $r^2P_{U_{10}}$ |
| $G$ | $\eta P_D$ | $r\eta P_{U_{10}}$ |
| $H$ | $P_E$ | $\eta P_{U_{10}}$ |

Define the input-last-bit projections

$$
\Pi_0=P_{ACDFH},\qquad \Pi_1=P_{BEG},\qquad
\Pi_0+\Pi_1=I_8.
\tag{5.3}
$$

For every legal word $u=u_1u_2u_3u_4$,

$$
F_u^{(3)}=w(u)\Pi_{u_1},\qquad
w(u)=\prod_{j=1}^3P_{u_j,u_{j+1}}>0.
\tag{5.4}
$$

The fourth-step effects needed below are

$$
\begin{aligned}
F_A^{(4)}&=r^3(r\Pi_0+\Pi_1)\ge r^4I_8>0,\\
F_C^{(4)}&=r\eta(r\Pi_0+\Pi_1)>0,\\
F_H^{(4)}&=\eta^2\Pi_0.
\end{aligned}
\tag{5.5}
$$

Proof. The first column of effects is read from the complete input rows of
(2.5), using (5.1). For two shifts the retained original suffix has length
two, and its three possible values partition the inputs into (5.2). Appending
two bits from each suffix gives the second column. Alternatively, applying
$\Phi^\dagger$ to each entry of the first column yields exactly that column.
Equation (2.6) with $n=3$ gives
$Q_4^3(s,u)=\mathbf1_{s_4=u_1}w(u)$, proving (5.4). For $n=4$ it gives
$Q_4^4(s,u)=P_{s_4,u_1}w(u)$. Substitution of $u=A,C,H$ gives (5.5).
All factors used as positive coefficients remain strictly positive because
$\eta,r>0$. $\square$

## 6. Supported correction and faithful logical-times-syndrome transfer

**Convention 6.1 (Standard correction interface).** We use the complex
Knill–Laflamme criterion [KL, Theorems 3.2 and 3.5][KL]. Its supported form
and rank pullback are the dimension-independent interface described in
[M5, Theorem 5.1][M5]. For a channel $\Psi$ and code isometry $J$, the
criterion is

$$
J^\dagger L_\alpha^\dagger L_\beta J
=\lambda_{\alpha\beta}I_k
\qquad\text{for all ordered Kraus pairs }(\alpha,\beta).
\tag{6.1}
$$

It is equivalent to a supported representation

$$
\Psi(JXJ^\dagger)=W(X\otimes\Gamma)W^\dagger,
\quad \Gamma>0,\quad\operatorname{Tr}\Gamma=1,
\quad W:\mathbb C^k\otimes\mathbb C^g\hookrightarrow\mathcal H.
\tag{6.2}
$$

Here $g=\operatorname{rank}\Gamma$ is the supported syndrome rank, and
$kg\le8$. It is not a postulated dimension of the environment.

For clarity, the finite algebra realizing this interface is as follows.
If $D_\ell$ are recovery Kraus operators, the positive rank-one sum recovering
each pure logical input forces every $D_\ell L_\alpha J$ to take that input
into its original line. A linear map preserving every line is scalar, by
applying it to basis vectors and pairwise sums. Thus
$D_\ell L_\alpha J=c_{\ell\alpha}J$, and recovery TP gives (6.1) with
$\lambda_{\alpha\beta}=\sum_\ell\overline c_{\ell\alpha}c_{\ell\beta}$.
This matrix is PSD and has trace one. Diagonalizing it by a unitary Kraus
change and omitting zero eigenvalues gives
$L'_hJ=\sqrt{\gamma_h}U_h$, with
$U_h^\dagger U_l=\delta_{hl}I_k$. Define
$W(x\otimes|h\rangle)=U_hx$ and
$\Gamma=\operatorname{diag}(\gamma_h)>0$ to obtain (6.2).
These are the standard correction facts, rather than a new M8 theorem.

Conversely, for every (6.2), choose any density matrix $\tau_0$ supported on
the original code. The full terminal decoder is

$$
\mathcal R(Y)=
J\operatorname{Tr}_{g}(W^\dagger YW)J^\dagger
+\operatorname{Tr}[(I_8-WW^\dagger)Y]\tau_0.
\tag{6.3}
$$

The first term is CP, with trace $\operatorname{Tr}(WW^\dagger Y)$; the
second is CP measurement followed by preparation, with complementary trace.
Their sum is TP on all $M_8$, including matrices outside the supported range.
It recovers every complex code matrix because $\operatorname{Tr}\Gamma=1$.
The identity on the code therefore also holds with every reference system.

**Proposition 6.2 (Faithful rank pullback and range implication).** In (6.2),
put $y=W^\dagger|t\rangle$ and
$E_t=J^\dagger\Psi^\dagger(|t\rangle\langle t|)J$. Then

$$
E_t=\operatorname{Tr}_g\left[
(I_k\otimes\Gamma^{1/2})|y\rangle\langle y|
(I_k\otimes\Gamma^{1/2})\right].
\tag{6.4}
$$

Consequently

$$
\operatorname{rank}E_t=\operatorname{SchmidtRank}(y)\le g.
\tag{6.5}
$$

If $\operatorname{ran}E_t\subseteq L\subseteq\mathbb C^k$, then

$$
W^\dagger|t\rangle\in L\otimes\mathbb C^g.
\tag{6.6}
$$

Proof. Trace pairing of (6.2) against $|t\rangle\langle t|$ gives (6.4).
The rank of a vector's reduced positive matrix is its Schmidt rank, and an
invertible operator on one factor preserves that rank. This proves (6.5),
including the zero-vector case. For $x\in L^\perp$, the expectation of (6.4)
on $x$ is

$$
0=\langle x,E_tx\rangle
=\left\|\Gamma^{1/2}(\langle x|\otimes I_g)y\right\|^2.
\tag{6.7}
$$

Faithfulness of $\Gamma$ forces
$(\langle x|\otimes I_g)y=0$. As this holds for every $x\in L^\perp$,
(6.6) follows. All spaces and vectors here may be complex. $\square$

**Proposition 6.3 (Entire supported transfer for a correctable prefix).**
Suppose the same code corrects $\Phi^n$. At every prefix choose the supported
forms

$$
\Phi^j(JXJ^\dagger)=W_j(X\otimes\Gamma_j)W_j^\dagger,
\quad \Gamma_j>0,\quad g_j=\operatorname{rank}\Gamma_j,
\quad S_j=\operatorname{ran}W_j.
\tag{6.8}
$$

For each $0\le j<n$, each Kraus operator $A_\alpha$ of the original fixed
channel maps $S_j$ into $S_{j+1}$. There is a CPTP map
$\Xi_j:M_{g_j}\to M_{g_{j+1}}$ with Kraus matrices $T_{\alpha,j}$ such that

$$
\begin{aligned}
A_\alpha W_j&=W_{j+1}(I_k\otimes T_{\alpha,j}),\\
\sum_\alpha T_{\alpha,j}^\dagger T_{\alpha,j}&=I_{g_j},
&\Xi_j(\Gamma_j)&=\Gamma_{j+1},\\
\Phi(W_jZW_j^\dagger)
&=W_{j+1}\bigl((\operatorname{id}_k\otimes\Xi_j)(Z)\bigr)
W_{j+1}^\dagger
&&\bigl(Z\in M_k\otimes M_{g_j}\bigr).
\end{aligned}
\tag{6.9}
$$

The last equality holds on every complex syndrome block, including blocks not
of the form $X\otimes\Gamma_j$.

Proof. Prefix correction follows from Proposition 1.4, so the supported
forms exist. Fix $j$ and abbreviate its two isometries by $W,W'$, its states
by $\Gamma,\Gamma'$, and its supports by $S,S'$. The positive matrix
$D=W(I_k\otimes\Gamma)W^\dagger$ is strictly positive on all of $S$.
Its image is $W'(I_k\otimes\Gamma')W'^\dagger$, supported on $S'$. For
$z\perp S'$,

$$
0=\langle z,\Phi(D)z\rangle
=\sum_\alpha\|D^{1/2}A_\alpha^\dagger z\|^2.
\tag{6.10}
$$

Every term vanishes. Since $D^{1/2}$ has kernel $S^\perp$, it follows that
$A_\alpha S\subseteq S'$. Define
$M_\alpha=W'^\dagger A_\alpha W$. There is no lost component outside $S'$, so
$A_\alpha W=W'M_\alpha$ and

$$
\sum_\alpha M_\alpha^\dagger M_\alpha=I_{kg_j},\qquad
\sum_\alpha M_\alpha(X\otimes\Gamma)M_\alpha^\dagger
=X\otimes\Gamma'.
\tag{6.11}
$$

Diagonalize $\Gamma=\sum_m p_m|m\rangle\langle m|$, with every $p_m>0$.
Use a reference $R\cong\mathbb C^k$ and the normalized maximally entangled
logical-reference vector $|\Omega\rangle$. Tensoring (6.11) with the reference
identity, its positive output is
$|\Omega\rangle\langle\Omega|\otimes\Gamma'$. It is a sum, over $\alpha,m$,
of the rank-one operators of the vectors

$$
\sqrt{p_m}\,(I_R\otimes M_\alpha)
(|\Omega\rangle\otimes|m\rangle).
\tag{6.12}
$$

The sum has support in $\mathbb C\Omega\otimes\mathbb C^{g_{j+1}}$.
Positivity forces each vector into that support. Because $p_m>0$, for every
$\alpha,m$ there is a vector $v_{\alpha m}$ with

$$
(I_R\otimes M_\alpha)(|\Omega\rangle\otimes|m\rangle)
=|\Omega\rangle\otimes v_{\alpha m}.
\tag{6.13}
$$

Expanding $|\Omega\rangle=k^{-1/2}\sum_i|i\rangle_R|i\rangle$ shows,
coefficient by coefficient in the independent reference basis, that
$M_\alpha(x\otimes|m\rangle)=x\otimes v_{\alpha m}$ for every logical $x$.
Set $T_{\alpha,j}|m\rangle=v_{\alpha m}$. These $|m\rangle$ span the whole
input syndrome, hence $M_\alpha=I_k\otimes T_{\alpha,j}$ on the whole tensor
space. Equation (6.11) gives TP and $\Xi_j(\Gamma_j)=\Gamma_{j+1}$; linearity
then gives the last equality of (6.9) for all $Z$. Faithfulness is essential:
zero-weight syndrome directions would not be tested in (6.12).

This is the supported-transfer mechanism of [M5, §7][M5], with the complete
faithful-support argument displayed for the dimensions used here. The maps
$\Xi_j$ are coordinate descriptions of restrictions of the same $\Phi$ on
possibly different supports. No decoder has been inserted, and they are not
independently selectable replacement channels. $\square$

## 7. Universal one-step and two-step upper bounds

**Theorem 7.1 (One-step dimension at most five).** For every allowed lift,
$k_1(\Phi)\le5$.

Proof. Suppose a correctable code has $k\ge6$. Its supported form has
$kg_1\le8$, so $g_1=1$. Select one positive first-step effect from each of the
five suffix groups $AF$, $BG$, $CH$, $D$, $E$ in §3. Each selected effect is
a positive scalar times the corresponding input projection. Proposition 6.2
gives

$$
\operatorname{rank}(J^\dagger P_{AF}J),\quad
\operatorname{rank}(J^\dagger P_{BG}J),\quad
\operatorname{rank}(J^\dagger P_{CH}J),\quad
\operatorname{rank}(J^\dagger P_DJ),\quad
\operatorname{rank}(J^\dagger P_EJ)\ \le1.
\tag{7.1}
$$

These five orthogonal projections sum to $I_8$, so their compressions sum to
$I_k$. Rank subadditivity yields $k\le5$, a contradiction. $\square$

**Theorem 7.2 (Two-step dimension at most three).** For every allowed lift,
$k_2(\Phi)\le3$.

Proof. A larger code restricts to a four-dimensional code, so it suffices to
exclude $k=4$. Choose supported forms at the first two steps. Both
$g_1,g_2\le2$.

If $g_2=1$, choose one effect from each of the three groups $U_{00},U_{01},U_{10}$ in Proposition 5.2. Each positive coefficient can be divided out;
Proposition 6.2 makes the three projection compressions have rank at most
one. Their sum is $I_4$, giving $4\le3$. Thus $g_2=2$, and $W_2$ is unitary
from $\mathbb C^4\otimes\mathbb C^2$ onto the entire $\mathcal H$.

If also $g_1=2$, then $W_1$ is unitary onto $\mathcal H$. Apply the full
transfer (6.9) to $Z=I_4\otimes I_2$ to obtain

$$
\Phi(I_8)=W_2\bigl(I_4\otimes\Xi_1(I_2)\bigr)W_2^\dagger.
\tag{7.2}
$$

Every eigenvalue on the right has multiplicity a multiple of four.
Proposition 4.2 forces both distinct eigenvalues $2$ and $1$, hence each
would occur at least four times. Positivity would give
$\operatorname{Tr}\Phi(I_8)\ge4\cdot2+4\cdot1=12$, contradicting TP and
trace eight. Therefore $g_1=1$.

Let $M=J^\dagger P_{CH}J$. The first-step effect
$F_D^{(1)}=rP_{CH}$ and $g_1=1$ imply $\operatorname{rank}M\le1$. At the
second step, the three effects at $F,G,H$ compress to

$$
r^2M,\qquad r\eta M,\qquad \eta M.
\tag{7.3}
$$

They cannot be zero. Indeed, $W_2$ is unitary, so $W_2^\dagger|t\rangle$
is nonzero for each coordinate $t$. Formula (6.4) and $\Gamma_2>0$ give a
nonzero reduced positive matrix. Thus $M$ has rank one. Put $L=\operatorname{ran}M$.
Equation (6.6) applied to (7.3) places all three vectors

$$
W_2^\dagger|F\rangle,\qquad W_2^\dagger|G\rangle,\qquad
W_2^\dagger|H\rangle
\tag{7.4}
$$

in $L\otimes\mathbb C^2$, a two-dimensional space. They are three orthonormal
unit vectors because $W_2$ is unitary. This contradiction excludes the
four-dimensional code. $\square$

## 8. One fixed canonical lift and full terminal decoders

**Definition 8.1 (Canonical discarded-first-bit lift).** With a two-dimensional
fresh environment, define

$$
V_{\mathrm{can}}|s_1s_2s_3s_4\rangle
=\sum_{b:P_{s_4,b}>0}\sqrt{P_{s_4,b}}
|s_2s_3s_4b\rangle\otimes|s_1\rangle,
\qquad
\Phi_{\mathrm{can}}=\operatorname{Tr}_{\mathcal E}
\operatorname{Ad}_{V_{\mathrm{can}}}.
\tag{8.1}
$$

Each $e_{t,s}=|s_1\rangle$ satisfies the five orthogonal pairs, so Theorem
3.2 makes this one allowed channel. It is the four-bit instance of the
canonical construction in [M5, §10][M5]; the finite factorizations and exact
dimensions for this instance are given next.

**Proposition 8.2 (Complete prefix factorization and decoders).** For
$1\le n<4$, put $m=4-n$ and $d_m=|\Omega_m|$. For every binary prefix $p$
of length $n$, define $T_p:\mathcal H\to\mathbb C^{d_m}$ by

$$
T_p|s\rangle=\mathbf1_{s_1\cdots s_n=p}
|s_{n+1}\cdots s_4\rangle.
\tag{8.2}
$$

Define $J_n:\mathbb C^{d_m}\to\mathcal H$ and
$W_n:\mathbb C^{d_m}\to\mathcal H$ by

$$
\begin{aligned}
J_n|u\rangle&=|0^nu\rangle,\\
W_n|u\rangle&=
\sum_{b_1,\ldots,b_n:\,ub_1\cdots b_n\ \mathrm{legal}}
\sqrt{P_{u_m,b_1}\prod_{j=1}^{n-1}P_{b_j,b_{j+1}}}
\,|ub_1\cdots b_n\rangle.
\end{aligned}
\tag{8.3}
$$

Both are isometries, and for every complex $X\in M_8$,

$$
\Phi_{\mathrm{can}}^n(X)
=W_n\left(\sum_{p\in\{0,1\}^n}T_pXT_p^\dagger\right)W_n^\dagger.
\tag{8.4}
$$

The code $J_n\mathbb C^{d_m}$ has the entire-output CPTP decoder

$$
\mathcal R_n(Y)=J_nW_n^\dagger YW_nJ_n^\dagger
+\operatorname{Tr}[(I_8-W_nW_n^\dagger)Y]
|0000\rangle\langle0000|,
\tag{8.5}
$$

and $k_n(\Phi_{\mathrm{can}})=d_m$ for $1\le n<4$.

Proof. Every $0^nu$ is legal, so $J_n$ is an isometry. The coefficients of
each $W_n|u\rangle$ have squared sum one by successive stochastic row sums.
Different $u$ have disjoint output supports, proving $W_n^\dagger W_n=I$.

Use the basis $|0\rangle,|1\rangle$ on each fresh discarded environment.
At the first step it records $s_1$, at the second $s_2$, and, for $n<4$,
at step $n$ it records $s_n$, independently of the appended bits. The
ordered Kraus product for the environment string $p$ therefore removes
that original prefix and makes the coherent continuation in (8.3).
It is exactly $W_nT_p$, also on matrix units with unequal input words.
Summing these Kraus products gives (8.4) on all complex matrices. Equivalently,
this follows by induction on the successive appended bits in (8.1).
The maps $T_p$ obey $\sum_pT_p^\dagger T_p=I_8$.

On the selected code, $T_{0^n}J_n=I_{d_m}$ and $T_pJ_n=0$ for all other $p$.
Thus

$$
\Phi_{\mathrm{can}}^n(J_nXJ_n^\dagger)=W_nXW_n^\dagger
\qquad(X\in M_{d_m}).
\tag{8.6}
$$

Write $P_n=W_nW_n^\dagger$. To verify (8.5) on the entire output, explicit
Kraus operators are

$$
J_nW_n^\dagger,\qquad
|0000\rangle\langle t|(I_8-P_n)\quad(t\in\Omega_4).
\tag{8.7}
$$

The squared products sum to $P_n+(I_8-P_n)^2=I_8$, so the map is CP and TP.
Summing the second terms gives exactly the trace-preparation term in (8.5).
Since $|0000\rangle$ is in the selected code and the complementary term
vanishes on $W_nXW_n^\dagger$, (8.6) proves full code correction, also with
arbitrary references.

For the matching upper bound, (8.4) factors the channel through $M_{d_m}$.
If a $k$-dimensional code were correctable, its map from $M_k$ to this
intermediate algebra would have a linear left inverse: compose $\operatorname{Ad}_{W_n}$,
the alleged terminal decoder, and the pullback $Y\mapsto J^\dagger YJ$.
That map must be injective, so $k^2\le d_m^2$ and $k\le d_m$. This proves
optimality. $\square$

**Proposition 8.3 (Fourth-step measurement and the entire canonical sequence).**
For $a\in\{0,1\}$ define the unit vector

$$
|\chi_a\rangle=
\sum_{t\in\Omega_4}
\sqrt{P_{a,t_1}\prod_{j=1}^3P_{t_j,t_{j+1}}}\,|t\rangle.
\tag{8.8}
$$

Then

$$
\Phi_{\mathrm{can}}^4(X)
=\sum_{s\in\Omega_4}X_{ss}
|\chi_{s_4}\rangle\langle\chi_{s_4}|,
\tag{8.9}
$$

and this single channel has the exact sequence

$$
\bigl(k_n(\Phi_{\mathrm{can}})\bigr)_{n\ge0}
=(8,5,3,2,1,1,\ldots).
\tag{8.10}
$$

Proof. At four steps the four environments record all the original bits
$s_1,s_2,s_3,s_4$. Conditional on those bits, the remaining coherent
continuation is exactly (8.8). Its squared norm is one by stochasticity.
The nonzero four-step Kraus operators are
$|\chi_{s_4}\rangle\langle s|$, giving (8.9) and the completeness relation
$\sum_s|s\rangle\langle s|=I_8$.

For any bipartite input state, (8.9) on the retained part produces a sum of
positive reference states tensor the pure states
$|\chi_{s_4}\rangle\langle\chi_{s_4}|$. This is separable; every terminal
channel preserves its separability. For a $k\ge2$ exact code, apply the
claimed correction to one half of the encoded maximally entangled state.
It would have to recover that entangled pure state, which is impossible
from a separable state by a local terminal channel. Thus $k_4=1$.
Monotonicity gives $k_n=1$ for every $n\ge4$. A full terminal decoder for
these one-dimensional codes is the reset
$Y\mapsto\operatorname{Tr}(Y)|0000\rangle\langle0000|$.
At $n=0$ use $J_0=I_8$ and the identity decoder. Finally,
$|\Omega_3|=5$, $|\Omega_2|=3$, $|\Omega_1|=2$, so Proposition 8.2 gives
the three intermediate entries. Throughout, the repeated channel is the
same $\Phi_{\mathrm{can}}$; only the code and final decoder depend on $n$.
$\square$

## 9. The partial universal theorem

**Theorem 9.1 (Partial universal dimension bounds).** For every
fixed $0<\eta<1$, the class of all complex allowed lifts has

$$
K_0(\eta)=8,\qquad K_1(\eta)=5,\qquad K_2(\eta)=3,
\qquad 2\le K_3(\eta)\le3,
\tag{9.1}
$$

and, for every $n\ge4$,

$$
1\le K_n(\eta)\le2.
\tag{9.2}
$$

Proof. The identity iterate gives $K_0=8$. Theorems 7.1 and 7.2 give the
one-step and two-step upper bounds, while Proposition 8.2 attains them.
Monotonicity gives $K_3\le K_2=3$, and the canonical third-step qubit gives
$K_3\ge2$.

For a general allowed lift, Proposition 5.2 gives
$F_A^{(4)}\ge r^4I_8$. Positivity and unitality of the adjoint propagate this
lower bound to every later step:

$$
F_A^{(n)}=(\Phi^\dagger)^{n-4}(F_A^{(4)})
\ge r^4(\Phi^\dagger)^{n-4}(I_8)=r^4I_8
\qquad(n\ge4).
\tag{9.3}
$$

If a $k$-dimensional code corrects $\Phi^n$, the compression
$J^\dagger F_A^{(n)}J$ is strictly positive and has rank $k$. Its supported
syndrome form and (6.5) give $g_n\ge k$. Combining this with $kg_n\le8$
yields $k^2\le8$, hence $k\le2$. The terminal reset gives the lower bound
one. This proves (9.2), without excluding a two-dimensional code. $\square$

The universal maxima in (9.1)–(9.2) are distinct from the exact dimensions
of one realization in (8.10). In particular the canonical fourth-step
measurement does not prove $K_4(\eta)=1$.

## 10. Four-step qubits cannot have full third-step syndrome support

**Theorem 10.1 (Four-Schmidt-direction exhaustion).** If a two-dimensional
code corrects $\Phi^4$ for an allowed lift, then every supported form at its
third prefix has

$$
g_3\le3.
\tag{10.1}
$$

Proof. The dimension bound gives $g_3\le4$. Suppose $g_3=4$.
Then $W_3:\mathbb C^2\otimes\mathbb C^4\to\mathcal H$ is unitary onto
all of $\mathcal H$. Proposition 6.3 at the last step represents the entire
channel, in the $W_3,W_4$ coordinates, as
$\operatorname{id}_2\otimes\Xi$, where
$\Xi:M_4\to M_{g_4}$ is CPTP. In particular every output is supported on
$S_4=\operatorname{ran}W_4$.

Both $|B\rangle$ and $|G\rangle$ reset to the pure state $|C\rangle$ by
Proposition 4.1. Therefore $|C\rangle\in S_4$ and
$c=W_4^\dagger|C\rangle$ is unit. The effect
$F_C^{(4)}=r\eta(r\Pi_0+\Pi_1)>0$ compresses to a rank-two matrix on the
code. Faithfulness in (6.5) says that $c$ has Schmidt rank two across the
logical and output syndrome factors.

Choose a Stinespring isometry
$T:\mathbb C^4\to\mathbb C^{g_4}\otimes\mathcal E$ for $\Xi$, and put

$$
x_B=W_3^\dagger|B\rangle,\qquad
x_G=W_3^\dagger|G\rangle.
$$

The vectors $x_B,x_G$ are orthogonal units. Their output under
$\operatorname{id}_2\otimes\Xi$ is the same pure state $|c\rangle\langle c|$.
A pure marginal of a pure bipartite vector forces product factorization,
so there are unit environment vectors $\varepsilon_B,\varepsilon_G$ such
that

$$
(I_2\otimes T)x_b=c\otimes\varepsilon_b
\qquad(b=B,G).
\tag{10.2}
$$

Since $I_2\otimes T$ is an isometry and $c$ is unit, taking inner products
in (10.2) gives $\langle\varepsilon_B,\varepsilon_G\rangle=0$.
This agrees with the full reset algebra, which also destroys the $BG$ cross
matrix unit.

Take a Schmidt decomposition with both coefficients nonzero:

$$
c=\sqrt{p_0}\,|0'\rangle\otimes h_0
 +\sqrt{p_1}\,|1'\rangle\otimes h_1,
\quad p_0,p_1>0,
\quad \langle h_i,h_l\rangle=\delta_{il}.
\tag{10.3}
$$

Define
$f_{ib}=p_i^{-1/2}(\langle i'|\otimes I_4)x_b$.
There are exactly two logical basis directions, hence

$$
x_b=\sum_{i=0}^1\sqrt{p_i}|i'\rangle\otimes f_{ib},
\qquad Tf_{ib}=h_i\otimes\varepsilon_b.
\tag{10.4}
$$

The four right-hand vectors, indexed by $i=0,1$ and $b=B,G$, are
orthonormal. Isometry of $T$ therefore makes the four $f_{ib}$ orthonormal
in the four-dimensional input syndrome. They exhaust that entire space.
Consequently

$$
\operatorname{ran}T
=\operatorname{span}\{h_i\otimes\varepsilon_b:
 i=0,1,\ b=B,G\}.
\tag{10.5}
$$

Every output of $\Xi$ is supported in the fixed two-dimensional space
$\operatorname{span}\{h_0,h_1\}$. Every output of
$\operatorname{id}_2\otimes\Xi$, and therefore of the whole $\Phi$, is
supported in a space of dimension at most four. In particular
$\operatorname{rank}\Phi(I_8)\le4$, contrary to Proposition 4.2.
This contradiction proves (10.1). No bound on the total environment dimension
was used; the four input syndrome directions, not the environmental space,
are what the proof exhausts. $\square$

## 11. A sufficient cutoff from actual rank-one Kraus directions

**Definition 11.1 (Actual Kraus linear space).** For an allowed channel put

$$
\mathcal K_\Phi=\operatorname{span}_{\mathbb C}\{A_\alpha\}.
\tag{11.1}
$$

It is independent of the Kraus representation: it is the vectorized support
of the Choi matrix. Its elements need not include individual allowed edge
matrix units. For a finite iterate, the corresponding Kraus linear space
is spanned by the ordered products of the actual $A_\alpha$.

**Theorem 11.2 (Two input-first-bit rank-one directions suffice).** Suppose
there are legal words $u_0,u_1$, whose respective first bits are $0,1$, and
nonzero vectors $y_0,y_1\in\mathcal H$ such that

$$
|y_b\rangle\langle u_b|\in\mathcal K_\Phi
\qquad(b=0,1).
\tag{11.2}
$$

Then $k_n(\Phi)=1$ for every $n\ge4$. In particular the actual memberships
$|C\rangle\langle B|,|C\rangle\langle G|\in\mathcal K_\Phi$ suffice.

Proof. If a $k\ge2$ code corrects $\Phi^4$, every $L$ in the linear space
of four-step Kraus products satisfies
$J^\dagger L^\dagger LJ=\mu_LI_k$, by all the ordered conditions (6.1).
For $\operatorname{rank}L\le1$, the left side has rank at most one and is
positive. Thus $\mu_L=0$ and $LJ=0$.

For each three-step actual Kraus product $K$, place
$B_b=|y_b\rangle\langle u_b|$ in the last position. The product $B_bK$
lies in that four-step Kraus space by (11.2) and has rank at most one, so
$B_bKJ=0$. Sum its squared norm matrices over all three-step Kraus products:

$$
0=\sum_KJ^\dagger K^\dagger B_b^\dagger B_bKJ
=\|y_b\|^2J^\dagger F_{u_b}^{(3)}J.
\tag{11.3}
$$

Equation (5.4) gives $F_{u_b}^{(3)}=w(u_b)\Pi_b$ with $w(u_b)>0$.
Positivity implies $\Pi_bJ=0$ for both $b=0,1$. Their sum is $I_8$, which
contradicts $J^\dagger J=I_k$. Hence $k_4=1$, and monotonicity gives every
later step. Words $B=0001$ and $G=1001$ have the required distinct first
bits, giving the stated special case. $\square$

**Proposition 11.3 (Positive definite edge Gram already destroys one-step
qubits).** If the thirteen-edge Gram $G$ is positive definite, then
$k_1(\Phi)=1$, and therefore $k_n(\Phi)=1$ for every $n\ge1$.

Proof. Positive definiteness makes the thirteen environment edge vectors
linearly independent. In their span there are dual linear functionals
selecting each one separately. In (3.7), a complex linear combination of
the Kraus operators with such a functional isolates its edge matrix unit,
with nonzero coefficient $\sqrt{Q_4(s,t)}$. Thus
$\mathcal K_\Phi$ contains all thirteen allowed edge matrix units.
For each input word $s$, choose one outgoing edge $|t\rangle\langle s|$.
If $k\ge2$ were correctable at one step, the rank-one argument in Theorem
11.2, now for that one-step error space, would give
$\langle s|J=0$. This holds for every $s$, contradicting $J^\dagger J=I_k$.
$\square$

**Proposition 11.4 (Allowed graph edges are insufficient for (11.2)).** The
canonical channel has the graph edges $B\to C$ and $G\to C$, but neither
individual edge matrix unit belongs to its actual Kraus space.

Proof. Its two Kraus operators $A_0,A_1$ collect the terms of (8.1) with
input first bit respectively $0,1$. Their input column supports are disjoint.
To isolate $|C\rangle\langle B|$ in $aA_0+bA_1$, the $A$ input column forces
$a=0$, since $A_0|A\rangle=\sqrt r|A\rangle+\sqrt\eta|B\rangle\ne0$ and
$A_1|A\rangle=0$. But then the $B$ input column is zero as well. To isolate
$|C\rangle\langle G|$, the $F$ input column similarly forces $b=0$, since
$A_1|F\rangle=\sqrt r|A\rangle+\sqrt\eta|B\rangle\ne0$; the $G$ input
column then vanishes. Both desired memberships are impossible. $\square$

Thus any four-step qubit realization must lie on the singular-Gram boundary
and avoid the hypothesis of Theorem 11.2. Singularity alone supplies neither
a code nor a counterexample.

## 12. A sufficient cutoff from discarded-first-bit environment sectors

**Theorem 12.1 (Distinguishing the discarded first bit suffices).** Suppose
a dilation (3.2) has orthogonal environment subspaces
$\mathcal E_0\perp\mathcal E_1$ such that

$$
e_{t,s}\in\mathcal E_{s_1}
\qquad\text{for every allowed edge }(t,s).
\tag{12.1}
$$

Then $k_n(\Phi)=1$ for every $n\ge4$. There is no restriction on dimension
or complex Gram structure within either sector.

Proof. Let $P_0^{\mathcal E},P_1^{\mathcal E}$ be the sector projections.
In four fresh environments, the tensor product of these projections for a
word $s$ selects exactly the original discarded bits $s_1,s_2,s_3,s_4$.
Indeed, at the $j$th step with $j\le4$, the first bit of the retained word
is still the original $s_j$, regardless of the newly appended bits. If
$V^{[4]}$ is the four-step isometry with all four environments retained only
for this calculation, and $P_s^{\mathcal E}$ is that sector-product
projection, then

$$
(I_8\otimes P_s^{\mathcal E})V^{[4]}|u\rangle
=\delta_{su}V^{[4]}|u\rangle
\qquad(s,u\in\Omega_4).
\tag{12.2}
$$

Isometry of $V^{[4]}$ gives the complete input effect

$$
(V^{[4]})^\dagger(I_8\otimes P_s^{\mathcal E})V^{[4]}
=|s\rangle\langle s|.
\tag{12.3}
$$

Write $V^{[4]}=\sum_{\boldsymbol\alpha}
K_{\boldsymbol\alpha}\otimes|\boldsymbol\alpha\rangle$, where
$K_{\boldsymbol\alpha}=A_{\alpha_4}\cdots A_{\alpha_1}$.
The pullback of any environment matrix $Z$ is

$$
\sum_{\boldsymbol\alpha,\boldsymbol\beta}
\langle\boldsymbol\alpha|Z|\boldsymbol\beta\rangle
K_{\boldsymbol\alpha}^\dagger K_{\boldsymbol\beta}.
\tag{12.4}
$$

Thus (12.3) lies in the actual noncommutative error operator space of
$\Phi^4$. The ordered Knill–Laflamme equalities make
$J^\dagger|s\rangle\langle s|J$ scalar $I_k$ for any correctable code.
For $k\ge2$ its rank is at most one, so that scalar must be zero.
Summing over $s$ contradicts $J^\dagger J=I_k$. Hence $k_4=1$, and later
cutoff follows from monotonicity. The canonical lift satisfies (12.1) with
$\mathcal E_b=\mathbb C|b\rangle$, providing this second proof of its
cutoff. $\square$

## 13. The remaining fourth-step rank geometry

**Definition 13.1 (Last supported transfer and row matrices).** For a
hypothetical four-step qubit code, take the supported forms of §6 and put

$$
a=g_3,\qquad b=g_4,\qquad
T_\alpha=T_{\alpha,3}:\mathbb C^a\to\mathbb C^b.
\tag{13.1}
$$

Theorems 9.1 and 10.1 imply the necessary ranges

$$
a\in\{1,2,3\},\qquad b\in\{2,3,4\}.
\tag{13.2}
$$

The lower bound on $b$ uses the full-rank compressed $A$ effect, not an
assumption about the environment. The transfer obeys

$$
\sum_\alpha T_\alpha^\dagger T_\alpha=I_a,\qquad
\sum_\alpha T_\alpha\Gamma_3T_\alpha^\dagger=\Gamma_4,
\qquad \Gamma_3>0,\quad\Gamma_4>0.
\tag{13.3}
$$

In fixed product bases define the $2\times g_j$ coordinate row matrix

$$
B_t^{(j)}[i,h]=\langle t|W_j(|i\rangle\otimes|h\rangle).
\tag{13.4}
$$

These are ket coefficient arrays, with ordinary multiplication in the row
equations below. The entries of $W_j^\dagger|t\rangle$ are their complex
conjugates; the matrix ranks agree. The columns of $W_j$ are orthonormal,
so these rows must jointly satisfy $W_j^\dagger W_j=I_{2g_j}$.

**Proposition 13.2 (Every last-step row equation).** With the single
consistent environment basis used in (3.7), the last transfer satisfies

$$
\begin{aligned}
B_A^{(4)}T_\alpha
 &=\sqrt r\bigl((e_{A,A})_\alpha B_A^{(3)}
                 +(e_{A,F})_\alpha B_F^{(3)}\bigr),\\
B_B^{(4)}T_\alpha
 &=\sqrt\eta\bigl((e_{B,A})_\alpha B_A^{(3)}
                 +(e_{B,F})_\alpha B_F^{(3)}\bigr),\\
B_C^{(4)}T_\alpha
 &=(e_{C,B})_\alpha B_B^{(3)}+(e_{C,G})_\alpha B_G^{(3)},\\
B_D^{(4)}T_\alpha
 &=\sqrt r\bigl((e_{D,C})_\alpha B_C^{(3)}
                 +(e_{D,H})_\alpha B_H^{(3)}\bigr),\\
B_E^{(4)}T_\alpha
 &=\sqrt\eta\bigl((e_{E,C})_\alpha B_C^{(3)}
                 +(e_{E,H})_\alpha B_H^{(3)}\bigr),\\
B_F^{(4)}T_\alpha&=\sqrt r(e_{F,D})_\alpha B_D^{(3)},\\
B_G^{(4)}T_\alpha&=\sqrt\eta(e_{G,D})_\alpha B_D^{(3)},\\
B_H^{(4)}T_\alpha&=(e_{H,E})_\alpha B_E^{(3)}.
\end{aligned}
\tag{13.5}
$$

Moreover

$$
\operatorname{rank}B_H^{(4)}
=\operatorname{rank}(J^\dagger\Pi_0J).
\tag{13.6}
$$

Proof. Take the $t$th output coordinate row of
$A_\alpha W_3=W_4(I_2\otimes T_\alpha)$ in (6.9). Its right side is
$B_t^{(4)}T_\alpha$ in (13.4); inserting each input-output coefficient of
(3.7) into its left side gives the eight displayed equations. For the last
rank identity, $F_H^{(4)}=\eta^2\Pi_0$ and (6.5) identify the compressed
rank with the Schmidt rank of $W_4^\dagger|H\rangle$. Faithfulness of
$\Gamma_4$ and conjugation of the coefficient array give (13.6).
$\square$

**Proposition 13.3 (Full-rank $\Pi_0$ compression and the square branch).**
Suppose a hypothetical code has $\operatorname{rank}(J^\dagger\Pi_0J)=2$
and $b=2$. Then necessarily $a=b=2$, and the last supported transfer is
isometric on all of $S_3$.

Proof. By (13.6), the square matrix $B_H^{(4)}$ is invertible. The last row
equation of (13.5) gives

$$
T_\alpha=c_\alpha D,\qquad
c_\alpha=(e_{H,E})_\alpha,\qquad
D=(B_H^{(4)})^{-1}B_E^{(3)}.
\tag{13.7}
$$

The edge vector $e_{H,E}$ has norm one, so $\sum_\alpha|c_\alpha|^2=1$.
Equation (13.3) then gives $D^\dagger D=I_a$ and
$\Gamma_4=D\Gamma_3D^\dagger$. Since $\Gamma_3$ is faithful and $D$ is
injective, the last matrix has rank $a$. Faithfulness of $\Gamma_4$ gives
rank $b=2$, so $a=b=2$ and $D$ is unitary. Thus
$\Xi_3=\operatorname{Ad}_D$, and (6.9) is conjugation by the isometry
$W_4(I_2\otimes D)W_3^\dagger$ on the entire third-step support.
$\square$

This branch has not been excluded. Isometry on a supported subspace is not
itself a contradiction to any preceding result; a universal cutoff would
still have to show that this isometry cannot coexist with the other row
equations, the earlier prefixes, and the same thirteen-edge channel.

**Proposition 13.4 (Rectangular row kernels under full-rank compression).**
Suppose $\operatorname{rank}(J^\dagger\Pi_0J)=2$ and $b\in\{3,4\}$.
Choose any right inverse $R:\mathbb C^2\to\mathbb C^b$ of $B_H^{(4)}$.
All solutions of its last row equation have the form

$$
T_\alpha=c_\alpha R B_E^{(3)}+N_\alpha,
\qquad \operatorname{ran}N_\alpha\subseteq\ker B_H^{(4)},
\quad c_\alpha=(e_{H,E})_\alpha.
\tag{13.8}
$$

Here $\dim\ker B_H^{(4)}=b-2$, respectively one or two.

Proof. Full row rank gives a right inverse. Subtract the particular solution
$c_\alpha RB_E^{(3)}$ from the last equation in (13.5); the difference is
annihilated by $B_H^{(4)}$. Conversely every such difference leaves the
row equation unchanged. Rank-nullity gives the kernel dimension. $\square$

The matrices $N_\alpha$ need not be proportional from this equation alone.
They are constrained jointly by the other seven rows in (13.5), both
identities (13.3), the isometry conditions on $W_3,W_4$, and the PSD Gram
conditions of §3. The existence of these algebraically free row-kernel terms
is an obstruction to the square-row proof, rather than an existence proof
for a correctable qubit.

**Definition 13.5 (Rank-deficient compression branches).** Let
$M_0=J^\dagger\Pi_0J$, with $0\le M_0\le I_2$. The alternatives
$\operatorname{rank}M_0=0$ or $1$ remain part of the fourth-step problem.
If its rank is zero, $\Pi_0J=0$ and $B_H^{(4)}=0$; the last equation in
(13.5) then forces $B_E^{(3)}=0$, since $e_{H,E}$ is a nonzero unit vector.
If its rank is one, (6.6) puts $W_4^\dagger|H\rangle$ in
$\operatorname{ran}M_0\otimes\mathbb C^b$, and $B_H^{(4)}$ has rank one.
In that case even $b=2$ has a nontrivial row kernel. Neither case admits
the inverse used in (13.7). These observations are consequences of the
row identities; they do not exclude either branch.

## 14. The ordered common-channel problem that remains open

**Definition 14.1 (Full complex fourth-step equations).** Choose a PSD
thirteen-edge Gram as in Theorem 3.2, realize its vectors in one environment
basis, and form the fixed Kraus family (3.7). For every ordered environment
multi-index put

$$
K_{\boldsymbol\alpha}=A_{\alpha_4}A_{\alpha_3}
A_{\alpha_2}A_{\alpha_1}.
\tag{14.1}
$$

The rightmost factor is the first chronological step. An exact qubit requires
a complex isometry $J:\mathbb C^2\to\mathcal H$ and scalars satisfying

$$
J^\dagger K_{\boldsymbol\alpha}^\dagger
K_{\boldsymbol\beta}J
=\lambda_{\boldsymbol\alpha,\boldsymbol\beta}I_2
\qquad\text{for every ordered pair }
(\boldsymbol\alpha,\boldsymbol\beta).
\tag{14.2}
$$

The matrix $\lambda$ is PSD and has trace one. All complex cross terms are
included, even when either product vanishes. Every $A_\alpha$ in both
products belongs to the same channel and the same Gram realization.

**Open problem 14.2 (Universal fourth-step exact-qubit cutoff).** Determine,
for each fixed interior parameter, whether

$$
K_4(\eta)=1,
\quad\text{equivalently}\quad
\forall\Phi\text{ satisfying (3.1)},\ k_4(\Phi)=1.
\tag{14.3}
$$

The established bounds leave $K_4(\eta)\in\{1,2\}$. A proof of (14.3)
must exclude all solutions of (14.2), including all the residual branches
$a\in\{1,2,3\}$, $b\in\{2,3,4\}$ and compression ranks zero, one, and two
in §13. In particular it must address the full-rank square isometric branch
of Proposition 13.3 and the rectangular kernel terms of Proposition 13.4.
There is no universal cutoff proof in these partial results.

A refutation at a stated $\eta$ would require actual complex Gram or Kraus
data satisfying the all-input law, an actual isometry $J$, and every ordered
equality (14.2). Diagonal-only compression, separate optimization over
incompatible channels, or a grid of Gram samples does not meet that
requirement. Given such data, diagonalizing its actual $\lambda$ gives a
supported form (6.2) for $\Phi^4$, and (6.3) supplies the required full
terminal CPTP decoder. No actual four-step counterexample is supplied here.

**Open problem 14.3 (Exact third-step optimum and later iterates).** Determine
whether $K_3(\eta)$ is two or three. The canonical value two does not
resolve that maximum. For $n\ge4$, the bounds $1\le K_n(\eta)\le2$ do not
determine whether any of them equals two. A universal fourth-step cutoff
would imply $K_n=1$ for all later $n$ by monotonicity. Conversely a
four-step qubit, if constructed, would not by itself establish a qubit at
every later iterate.

## 15. Primary interfaces and hypothesis boundaries

**Convention 15.1 (Classical and five-dimensional ownership).** The following
mathematical interfaces are reused at their indicated scope. Their general
proofs and the complete M5 classification remain in their owning sources.

| Owning source | Exact use in this volume |
| --- | --- |
| [M5, §§2–3][M5] | Same fixed-channel, all-complex-input and terminal-decoding interpretation, and the selected classical-source interface; the retained dimension here is eight. |
| [M5, §5 and §7][M5] | Standard supported correction and the faithful logical-times-syndrome transfer mechanism; §6 displays the full transfer argument for the present dimensions. |
| [M5, §10][M5] | Canonical discarded-first-bit construction; §8 derives the four-bit factorization and exact terminal decoders. |
| [LocalClock, Definition 15.1][LC] | Guarded native affine complete-window operation and complete-source hypotheses, distinct from a chronological overlap slide. |
| [LocalClock, Propositions 15.6 and 15.8][LC] | Unit-activity specialization and fixed finite-activity Perron–Markov source used in (2.1)–(2.2). |
| [Pyramid, Theorem 17.3, Proposition 17.4, and §§17–18][PY] | General-source constraints, actual same-local-law distinctions, and the separately chosen at-most-second-order extension; no identification of arbitrary sources with that extension. |

The M5 interface used here is the source at immutable revision
`0fe2d3f819cba2129dc736c4c71e4f7a9fb2f0ea`; the LocalClock and Pyramid
interfaces are those at immutable revision
`9f316de1477daccdb5b73d05646c0c6411874668`. These revisions identify
mathematical inputs and do not turn their prose into kernel evidence.

**Convention 15.2 (Standard primary literature).** The following are
`literature-attested` inputs or comparison frameworks. The M8 partial
bounds, effects, rank obstructions, and branch equations are the explicit
`repo-derived` deductions above. The indicated primary results do not
settle Open problems 14.2–14.3, and their comparison is not an exhaustive
literature or novelty determination.

| Primary source | Supported use and precise limitation |
| --- | --- |
| E. Knill and R. Laflamme, *A Theory of Quantum Error-Correcting Codes*, [quant-ph/9604034v1][KL], Theorems 3.2 and 3.5, equations (19)–(20); journal article *Physical Review A* **55**, 900–911, DOI [10.1103/PhysRevA.55.900](https://doi.org/10.1103/PhysRevA.55.900) | Ordered complex Kraus cross conditions and the correctable code-times-syndrome representation. The model-specific dimension arguments use these conditions with the actual Kraus products. |
| R. Duan, S. Severini, and A. Winter, *Zero-error communication via quantum channels, non-commutative graphs and a quantum Lovász $\vartheta$ function*, [1002.2514v2][DSW], §II equation (2), §III | Actual error operator space $\operatorname{span}\{A_\alpha^\dagger A_\beta\}$ and scalar code compression. For the fourth iterate this space must be formed from (14.1), not from all separately allowed edges. |
| R. Blume-Kohout, H. K. Ng, D. Poulin, and L. Viola, *Information-preserving structures: A general framework for quantum zero-error information*, [1006.1358][BKNPV], §III, Definitions 8–9 and Theorem 5 | Preserved, correctable, and noiseless information are distinct, and fixed-point structure has its own hypotheses. Finite-iterate terminal correction here is not automatically a fixed noiseless subsystem. |
| M. M. Wilde, *Quantum-shift-register circuits*, [0903.3894][WILDE], input/output and memory-register setup; DOI [10.1103/PhysRevA.79.062325](https://doi.org/10.1103/PhysRevA.79.062325) | Streaming circuits with their input, output, feedback, and memory registers provide a comparison model. Their register resources do not establish the fixed retained $M_8$ all-input law. |
| T. Rybár and M. Ziman, *Quantum finite-depth memory channels: Case study*, [0907.5521v1][RZ], §§II–IV, equation (4.19), summary after (4.21), and §V; DOI [10.1103/PhysRevA.80.042306](https://doi.org/10.1103/PhysRevA.80.042306) | The depths $0,1,2,\infty$ refer to their qubit process with a qubit internal memory and fresh principal inputs under a fixed interaction. Those depths are not the exact-code dimensions of an autonomous channel on the retained eight-dimensional system. |
| M. Sanz, D. Pérez-García, M. M. Wolf, and J. I. Cirac, *A quantum version of Wielandt's inequality*, [0909.5347v2][WIE], Proposition 3 and Theorem 1 | The primitive quantum-channel hypothesis is substantive. Positivity of $Q_4^5$ alone does not establish it, as Proposition 15.3 shows. |
| K. Korzekwa, S. Czachórski, Z. Puchała, and K. Życzkowski, *Coherifying quantum channels*, [1710.04228v2][COH], §II B, equations (6)–(13), discussion following (13) and (18) | Fixing Choi scalar diagonals permits coherence-to-population terms within output-diagonal blocks. The entire-block zero conditions of (3.4) impose the stronger all-input class used here. |

**Proposition 15.3 (Classical primitivity does not provide quantum
primitivity).** The canonical lift has $Q_4^5>0$, yet it is not primitive
as a channel on $M_8$.

Proof. Classical positivity is Proposition 2.3. By (8.9), every output of
$\Phi_{\mathrm{can}}^4$ is supported on
$L=\operatorname{span}\{\chi_0,\chi_1\}$, with $\dim L\le2$. For every
$n\ge4$, write
$\Phi_{\mathrm{can}}^n=\Phi_{\mathrm{can}}^4\Phi_{\mathrm{can}}^{n-4}$;
all its outputs still lie in this fixed $L$. No such iterate can send every
nonzero positive input to a positive definite eight-by-eight matrix.
If an earlier iterate had that strict-positivity property, all its integer
multiples would have it: applying the same strictly positive iterate to
successive nonzero positive outputs preserves positive definiteness.
A multiple at least four contradicts the support bound. Hence there is no
primitive iterate. This legal lift already disproves the inference from
classical primitivity to quantum primitivity for the entire class. $\square$

**Convention 15.4 (Extent of the partial conclusion).** The parameter is
strictly interior; no endpoint extension is part of these theorems. Exact
subspace correction, a particular channel's measure-and-prepare iterate,
fixed noiseless subsystems, and asymptotic transmission are different
properties. The all-lift statements proved here are exactly Theorem 9.1,
the necessary restriction of Theorem 10.1, and the sufficient hypotheses
of §§11–12. The unresolved alternatives and the required common-channel
complex equations are those of §§13–14.

[M5]: AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[LC]: AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md
[PY]: AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS_SOFT_TO_RIGID_AND_ODD_CYCLE_OBSTRUCTIONS.md
[KL]: https://arxiv.org/pdf/quant-ph/9604034v1
[DSW]: https://arxiv.org/pdf/1002.2514v2
[BKNPV]: https://arxiv.org/pdf/1006.1358
[WILDE]: https://arxiv.org/pdf/0903.3894
[RZ]: https://arxiv.org/pdf/0907.5521v1
[WIE]: https://arxiv.org/pdf/0909.5347v2
[COH]: https://arxiv.org/pdf/1710.04228v2

## 追加锚（本行以下为增补区）
