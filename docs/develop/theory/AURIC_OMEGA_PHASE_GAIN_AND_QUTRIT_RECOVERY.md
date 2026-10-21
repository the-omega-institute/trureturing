# AURIC Ω phase gain and qutrit recovery

## 1. Actual channels, physical coordinates and the native contract

**Definition 1.1 (fixed physical and passive frames).** The logical input is $A=\mathbb C^3$ with physical basis $(|0\rangle,|1\rangle,|2\rangle)$. The physical output is the entire legal three-position chain

$$
B=\mathcal K_3=\mathbb C^5,\qquad
(e_0,e_1,e_2,e_3,e_4)=(000,100,010,001,101).
$$

Use the fixed diagonal matrices $D=\operatorname{diag}(1,i,i,i,1)$ and $L=\operatorname{diag}(1,i,i)$, and $\operatorname{Ad}_U(X)=UXU^\dagger$. A physical encoder $N^{\rm ph}:M_3\to M_5$ and its passive representation are related by

$$
N=\operatorname{Ad}_{D^\dagger}\circ N^{\rm ph}\circ\operatorname{Ad}_L,
\qquad N^{\rm ph}=\operatorname{Ad}_D\circ N\circ\operatorname{Ad}_{L^\dagger}.
\tag{P.1}
$$

These are coordinates for the same channel, not extra physical gates. Kets used as channel arguments denote their rank-one projectors. Set

$$
\theta_\pm=(|0\rangle\pm|1\rangle)/\sqrt2,
\qquad \chi_\pm=(|0\rangle\pm i|1\rangle)/\sqrt2.
$$

The physical candidate inputs throughout are $\theta_\pm$. In passive coordinates their signs swap:

$$
L^\dagger\theta_\pm=\chi_\mp,\qquad
N^{\rm ph}(\theta_\pm)=D N(\chi_\mp)D^\dagger.
\tag{P.2}
$$

The output order and $D$ are those of [the owning theory, Definition 68.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#48-固定初始五人口的全单纯形相位增益). All statements here are finite-dimensional ordinary mathematics. The full-input complement and recovery certificates are developed in the [companion volume](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md).

**Assumption 1.2 (original finite-word native menu).** On the whole $\mathcal K_3$, supply the independent constrained flips

$$
H_j^{(3)}=\left.P_{j-1}^0 X_jP_{j+1}^0\right|_{\mathcal K_3},\quad
P_j^0=|0\rangle\langle0|_j,\quad P_0^0=P_4^0=I,
\quad e^{-itH_j^{(3)}}\quad(t\in\mathbb R).
$$

Only the selected drive is on; drift and all other drives are zero. Allow arbitrary finite serial words and the empty word, together with the single repeatedly usable forward installation

$$
S_{13}=\exp(i\pi n_1n_3/2)=\operatorname{diag}(1,1,1,1,i),\qquad
n_1=\operatorname{diag}(0,1,0,0,1).
$$

The sole terminal measurement is $\{n_1,I-n_1\}$. At budget $k\in\mathbb Z_{\geq0}$ at most $k$ actual forward calls of $S_{13}$ may occur. Implementing $S_{13}^{-1}=S_{13}^3$ costs three calls. The flips have period $2\pi$, so a nonnegative-time formulation gives the same flip words. The exact zero-phase finite-word group is $DSO(5)D^\dagger$, by [the owner, Theorem 64.1, (IX.1)](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#44-固定相位菜单的实际有限字达到), under its Definition 55.1 and Assumption 55.2. Its unlimited-budget universality supplies no fixed-budget bound.

For two fixed actual output states define $B_k$ as the maximum of

$$
\left|\operatorname{Tr}\bigl[n_1 W(\rho^{\rm ph}-\sigma^{\rm ph})W^\dagger\bigr]\right|
\tag{P.3}
$$

over these words. Settings may depend on the known candidate pair and a common already obtained classical record, but the same setting must act on both unknown labels. Different budgets may use different optimizing settings. There is no ancillary quantum bypass, accessible reference, extra input copy, intermediate measurement, postselection, nonunitary preprocessing or free preparation of an input or history. Input supply is a hypothesis. This is the owner's ideal independent-drive menu, not the fixed-total-Hamiltonian waiting menu. A terminal measurement returns one bit, not the exact probability in (P.3).

**Definition 1.3 (actual complex and real encoder classes).** Fix $0\leq\beta\leq1/2$ and $a=1-\beta$. Let $\mathcal C_\beta$ be the set of all complex-linear CPTP maps $N^{\rm ph}:M_3\to M_5$ whose actual states $\rho^{\rm ph}=N^{\rm ph}(\theta_+)$ and $\sigma^{\rm ph}=N^{\rm ph}(\theta_-)$ satisfy

$$
\Delta=D^\dagger(\rho^{\rm ph}-\sigma^{\rm ph})D=iA_0,
\quad A_0\in M_5(\mathbb R),\quad A_0^T=-A_0,
\quad \operatorname{spec}\Delta=(a,\beta,0,-\beta,-a).
\tag{P.4}
$$

Thus the actual passive pair has the same entrywise real part and the same diagonal $z$. Equal populations alone do not imply (P.4). No arbitrary population vector replaces this actual $z$.

Let $\mathcal R_\beta\subseteq\mathcal C_\beta$ consist of those channels for which $N$ in (P.1) has real Kraus matrices $K_\alpha\in M_{5\times3}(\mathbb R)$:

$$
N(X)=\sum_\alpha K_\alpha X K_\alpha^T,
\qquad \sum_\alpha K_\alpha^T K_\alpha=I_3,
\qquad K_\alpha^{\rm ph}=DK_\alpha L^\dagger.
\tag{P.5}
$$

For real passive Kraus matrices, $N(\chi_-)=\overline{N(\chi_+)}$; the spectrum condition still must hold. Real entries of physical Kraus matrices do not establish either this passive real structure or native oldblindness. The sign in (P.2) negates the phase difference, leaving its symmetric spectrum unchanged.

**Definition 1.4 (recovery metrics).** Every recovery below is an arbitrary complex CPTP map $R:M_5\to M_3$, defined on the whole output algebra. State fidelity is the root convention $f(X,Y)=\|\sqrt X\sqrt Y\|_1$. For channels with the same input let

$$
F(\mathcal A,\mathcal B)=\min_{\rho\in\mathsf D(\mathbb C^3)}
f\bigl((\mathcal A\otimes\mathrm{id})(\psi_\rho),
       (\mathcal B\otimes\mathrm{id})(\psi_\rho)\bigr),
\quad g_N=\max_R F(RN,\mathrm{id}_3),
\quad \delta(N)=\inf_R\|RN-\mathrm{id}_3\|_\diamond.
\tag{P.6}
$$

Here $\psi_\rho$ is any purification of the input density $\rho$; its choice is immaterial up to a reference isometry. Diamond and trace norms are unhalved. A reference of dimension three suffices: any pure state with a larger finite reference has Schmidt rank at most three and is the image of such a purification by a reference isometry. Trace norm and fidelity are invariant under this isometry. Mixed inputs cannot increase the channel-difference trace-norm supremum by convexity, or decrease the fidelity infimum by joint concavity after decomposition into pure states. Thus arbitrary finite passive references remain included in (P.6), though they are not native controls in Assumption 1.2.

## 2. Exact native gain on the same encoder

**Theorem 2.1 (phase observability).** For every actual $N^{\rm ph}\in\mathcal C_\beta$, under Assumption 1.2,

$$
B_0=0,\qquad B_1=1-\beta,\qquad B_k=1\ (k\geq2),
\qquad \gamma:=B_2-B_1=\beta.
\tag{P.7}
$$

Each maximum is attained by a finite original-menu word. Saturation first occurs at one call for $\beta=0$ and at two calls for $\beta>0$.

**Proof.** The actual passive states lie in the owner's $\mathcal E(z)$: both are PSD of trace one, with their common actual diagonal and entrywise real part. Their weights are precisely $a_1=a,a_2=\beta$, with total trace distance $a+\beta=1$. [Owner Theorem 79.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#59-同一安装与固定末端事件的完整消费者), using Theorem 67.2, applies with $d=5$, phase rank $p=1$ and readout rank $r=2$. Its dimension condition is $d-2\min(r,d-r)=1=p$. It gives $B_k=\sum_{j\leq\min(k,2)}a_j$, including zero weights, which is (P.7).

More explicitly, in a real skew-normal basis of the actual $\Delta$, let its two planes be $(u_j,v_j)$ and weights $a_j$. A real rank-two projection onto $(u_j+v_j)/\sqrt2$ is an $SO(5)$ conjugate of $n_1$. Conjugating the one installed $S_{13}$ by a real rotation can phase $u_1$, or then $u_2$, by $+i$. With one call the resulting read effect selects one skew eigenvector and gives absolute contrast $a$; with two it selects both and gives $a+\beta$. The unused fifth direction corrects every orientation sign. Each real rotation and its transpose has an exact finite flip word by owner (IX.1), without a phase call. Since $D$ commutes with $S_{13}$ and $n_1$, returning to physical coordinates preserves the count. The matching upper bound is the owner's call-rank bound, not an inference from unlimited-budget controllability. Zero-phase effects are real symmetric, whose trace pairing with $iA_0$ vanishes. The omitted positive second weight explains the minimal saturation budget. $\square$

## 3. A whole-complex-class lower bound

**Theorem 3.1 (same-encoder gain/recovery obstruction).** Every $N^{\rm ph}\in\mathcal C_\beta$ and every complex CPTP $R$ satisfy

$$
\|RN^{\rm ph}-\mathrm{id}_3\|_\diamond
\geq L(\beta):=\frac{2\beta}{3+2\sqrt{2(1-\beta)}}=L(\gamma).
\tag{P.8}
$$

More generally the bound holds for any complex CPTP encoder $N:M_3\to M_5$ having one actual pure input with output nonzero spectrum $(a,\beta)$, omitting the zero weight at $\beta=0$. This sufficient condition does not require real Kraus matrices or a second specified output.

**Proof.** First (P.4) gives $\|\rho^{\rm ph}-\sigma^{\rm ph}\|_1=2$. For density operators, the positive spectral projection $Q$ of their difference then has $\operatorname{Tr}(Q\rho^{\rm ph})=1$ and $\operatorname{Tr}(Q\sigma^{\rm ph})=0$. Positivity forces their supports into orthogonal subspaces. Therefore these actual states are the positive and negative parts of their difference; each has nonzero eigenvalues $(a,\beta)$. The physical $\theta_+$ is an actual pure preimage under this same $N^{\rm ph}$.

For the more general sufficient condition, take a finite Stinespring isometry of the actual encoder and its complement $\Gamma:M_3\to M_r$. Contracting this isometry with a basis of the five-dimensional retained output supplies at most five Kraus matrices for $\Gamma$. Thus its unnormalized input-first Choi matrix $J=\sum_{ij}|i\rangle\langle j|\otimes\Gamma(|i\rangle\langle j|)$ has rank at most five and $\operatorname{Tr}_EJ=I_3$. The complement output $\tau$ at the stipulated pure input has the same nonzero eigenvalues $(a,\beta)$ by Schmidt decomposition.

Fix one environment density $\omega$ and let $t=\lambda_2(\omega)$, with $t=0$ when $r=1$. The eigenvalue trace inequality, applied to $\sqrt\tau$ and $\sqrt\omega$ in the trace-norm variational formula, gives

$$
F(\Gamma,\mathcal C_\omega)\leq f(\tau,\omega)
\leq\sqrt{a\lambda_1(\omega)}+\sqrt{\beta t}
\leq\sqrt{a(1-t)}+\sqrt{\beta t},
\quad \mathcal C_\omega(X)=\operatorname{Tr}(X)\omega.
\tag{P.9}
$$

Here $0\leq t\leq1/2$. To obtain another bound for this same $\omega$, suppose $r\geq2$ and $t>0$, and span its top two eigenvectors by $E_2$. The six-dimensional space $\mathbb C^3\otimes E_2$ meets $\ker J$ in a nonzero vector because $\operatorname{rank}J\leq5$. Choose a unit $\xi$ there, with reference Schmidt support $S$ of dimension $k\leq2$. Put $q=\Pi_S/k$ and $A_q=\sqrt q\otimes I$. The vector $\sum_{ij}(\sqrt q)_{ij}|i\rangle_R|j\rangle_A$ has actual input marginal $q^T$, and gives normalized output states

$$
\Omega_q=A_qJA_q,\qquad Q_q=q\otimes\omega.
$$

Because $A_q\xi=\xi/\sqrt k$ and $J\xi=0$, $\Omega_q\xi=0$. The probability assigned by $Q_q$ to $\xi$ is

$$
p=\langle\xi|Q_q|\xi\rangle
=\langle\xi|I\otimes\omega|\xi\rangle/k\geq t/k\geq t/2.
$$

The binary CPTP measurement $\{|\xi\rangle\langle\xi|,I-|\xi\rangle\langle\xi|\}$ yields distributions $(0,1)$ and $(p,1-p)$. Root-fidelity data processing gives $F(\Gamma,\mathcal C_\omega)^2\leq1-t/2$. If $r<2$ or $t=0$, this inequality is simply fidelity normalization; no six-dimensional subspace is invoked in that branch.

The unrestricted Bény–Oreshkov recovery/complement theorem, with target $\mathrm{id}_3$, now gives

$$
g_N=\max_\omega F(\Gamma,\mathcal C_\omega),\qquad
g_N^2\leq\max_{0\leq t\leq1/2}
\min\{s(t),1-t/2\},\quad
s(t)=(\sqrt{a(1-t)}+\sqrt{\beta t})^2.
\tag{P.10}
$$

The identity complement is the scalar trace, and channels from that scalar system prepare exactly the densities $\omega$. The theorem optimizes all complex CPTP recoveries and permits nonminimal complements. Both inequalities in (P.10) were imposed at the same center before maximizing; centers for separate inputs are never substituted.

For $\beta>0$, $s$ increases on $[0,\beta]$ and decreases thereafter: write $t=\sin^2 u$, $\beta=\sin^2 v$ to get $s(t)=\cos^2(u-v)$ with $u,v\in[0,\pi/4]$. Its unique intersection with $1-t/2$ on $[0,\beta]$ maximizes the lower envelope. In this interval the intersection equation is

$$
\sqrt{\beta(1-t)}-\sqrt{at}=\sqrt{t/2},
\qquad t_0=\frac{2\beta}{3+2\sqrt{2a}},
\qquad g_N^2\leq1-t_0/2.
$$

Indeed moving the nonnegative terms and squaring gives $\beta=t(3/2+\sqrt{2a})$. Beyond $\beta$ the second term only decreases. At $\beta=0$ the envelope is $\min(1-t,1-t/2)=1-t$, with maximum one at zero, giving the same formula without division by $\beta$.

For any single recovery and purification $\psi$, measurement of its pure ideal target gives

$$
\|((RN)\otimes\mathrm{id})(\psi)-\psi\|_1
\geq2\bigl(1-f(((RN)\otimes\mathrm{id})(\psi),\psi)^2\bigr).
$$

Taking the worst purification yields $\|RN-\mathrm{id}\|_\diamond\geq2(1-F(RN,\mathrm{id})^2)\geq2(1-g_N^2)\geq t_0$. The factor two is the unhalved convention. This proves the sufficient-condition theorem and its application to the actual physical channel. The equality $\gamma=\beta$ comes from Theorem 2.1 on that same channel. $\square$

**Definition 3.2 (standard interfaces used in the proof).** Root fidelity and its PSD-channel monotonicity are used in the sense of Watrous, [*The Theory of Quantum Information*, Chapter 3](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf), Definition 3.11, (3.64), and Theorem 3.27, (3.173). The latter requires a CPTP map and PSD operands; all measurement operands above are normalized states, including singular ones. Recovery duality is [Bény–Oreshkov, arXiv:0907.5391v4, Theorem 1, (3)](https://arxiv.org/pdf/0907.5391v4), with the root convention clarified in [arXiv:1103.0649v3, (54)–(56), Corollary 5, (64)](https://arxiv.org/pdf/1103.0649v3). The Kraus-restricted theorem in the latter is not substituted for its unrestricted corollary. These are literature-attested tools within the new composition, not new recovery or fidelity theorems. The existing [repository recovery note](../../../Library/QuantumChannels/beny2010approximate.md) owns this literature interface; [FiniteKrausReversibility](../../../Blueprint/D5/S3/Quantum/Recovery/FiniteKrausReversibility.md) treats exact full-algebra recovery rather than the positive-error estimates here.

## 4. An actual upper family and its individual optimum

**Theorem 4.1 (attained upper family, not a universal upper bound).** In the fixed passive output basis define $u=\sqrt a$, $v=\sqrt\beta$ and

$$
K_0=u(e_0\langle0|+e_1\langle1|)+e_4\langle2|,
\qquad K_1=v(e_2\langle0|+e_3\langle1|).
\tag{P.11}
$$

Its physical channel under (P.1) belongs to $\mathcal R_\beta$, has $\gamma=\beta$, and its optimal all-complex-recovery unhalved diamond error is exactly

$$
\delta(N_\beta)=U(\beta):=1-\sqrt{1-\beta}.
\tag{P.12}
$$

**Proof.** The Kraus TP sum is $I_3$. With $f_1^\pm=(e_0\pm ie_1)/\sqrt2$ and $f_2^\pm=(e_2\pm ie_3)/\sqrt2$,

$$
N_\beta(\chi_\pm)=a|f_1^\pm\rangle\langle f_1^\pm|
+\beta|f_2^\pm\rangle\langle f_2^\pm|.
\tag{P.13}
$$

The four $f$ vectors are orthonormal; the difference has exactly the required spectrum. (P.2) gives the actual physical $\theta$ outputs and Theorem 2.1 applies.

A decoder on the entire output has Kraus matrices

$$
T_0=|0\rangle\langle e_0|+|1\rangle\langle e_1|+|2\rangle\langle e_4|,
\qquad T_1=|0\rangle\langle e_2|+|1\rangle\langle e_3|.
\tag{P.14}
$$

Their TP sum is $I_5$. Put $P=\operatorname{diag}(1,1,0)$, $Q=I-P$, $Z=P-Q$. Direct composition on every complex matrix gives

$$
TN_\beta=\frac{1+u}{2}\,\mathrm{id}_3+
\frac{1-u}{2}\operatorname{Ad}_Z.
\tag{P.15}
$$

The diamond distance between $\operatorname{Ad}_Z$ and the identity is two: the difference-of-channels bound gives the upper bound for every reference, and $(|0\rangle+|2\rangle)/\sqrt2$ gives orthogonal outputs and attains it. Thus this decoder has error $1-u$.

For individual optimality take $\eta_\pm=(|0\rangle\pm|2\rangle)/\sqrt2$. Their encoder output difference is $u(|e_0\rangle\langle e_4|+|e_4\rangle\langle e_0|)$, of trace norm $2u$. For any single recovery $R$, contraction and the triangle inequality give

$$
2\leq\|\eta_+-RN_\beta(\eta_+)\|_1+2u+
\|RN_\beta(\eta_-)-\eta_-\|_1
\leq2\|RN_\beta-\mathrm{id}\|_\diamond+2u.
$$

This proves (P.12). The physical decoder has Kraus matrices $LT_jD^\dagger$. Indeed

$$
R^{\rm ph}=\operatorname{Ad}_L\circ R\circ\operatorname{Ad}_{D^\dagger},\qquad
R^{\rm ph}N^{\rm ph}-\mathrm{id}
=\operatorname{Ad}_L\circ(RN-\mathrm{id})\circ\operatorname{Ad}_{L^\dagger}.
\tag{P.16}
$$

This is a bijection on all complex CPTP recoveries, and unitary invariance of the diamond norm, including every reference, gives $\delta(N^{\rm ph})=\delta(N)$. The same input-purification bijection preserves the worst-input root fidelity and hence $g_N$. The corresponding physical contraction tests are $L\eta_\pm$; they do not replace the native $\theta_\pm$ pair.

Explicit native attainers for (P.13) can also be written in the fixed passive coordinates. Let $O$ have rows

$$
(e_0-e_1)^T/\sqrt2,\quad(e_0+e_1)^T/\sqrt2,\quad
(e_2-e_3)^T/\sqrt2,\quad-e_4^T,\quad(e_2+e_3)^T/\sqrt2.
$$

It has determinant one. For $h=0,2$, let $A_h$ be identity off $\operatorname{span}(e_h,e_4)$, with $A_he_4=e_h$ and $A_he_h=-e_4$. Then $J_h=A_hS_{13}A_h^T$ phases only $e_h$. The words $OJ_0$ and $OJ_2J_0$ have absolute contrasts $a$ and one. Every real conjugator is an exact finite zero-phase flip word in physical coordinates. Each $J_h$ uses one forward call; neither $D$ nor an inverse phase is added as a free gate.

All formulas remain CPTP at both endpoints. At zero $K_1=0$, $K_0$ is an isometry, $\delta=0$, and $B_1=B_2=1$. At $\beta=1/2$, $\delta=1-1/\sqrt2$, $B_1=1/2$ and $B_2=1$. No positive-rank residual hypothesis is used at zero. $\square$

## 5. Identical phase outputs do not determine recovery

**Theorem 5.1 (all-parameter identical-output counterexample).** Replace (P.11) by the real passive Kraus family

$$
B_0=u(e_0\langle0|+e_1\langle1|),\quad
B_1=v(e_2\langle0|+e_3\langle1|),\quad B_2=e_4\langle2|.
\tag{P.17}
$$

For every $\beta\in[0,1/2]$ this actual encoder has the same entire phase output states (P.13), hence the same actual physical $\theta$ outputs and $\gamma=\beta$, but optimal recovery error exactly one.

**Proof.** The TP sum is $I_3$ and the channel agrees with (P.11) on the entire $P$-supported algebra. It erases every $P$–$Q$ coherence. Therefore its outputs on the orthogonal $\eta_\pm$ above are identical. The same-recovery triangle inequality forces diamond error at least one. Decoder (P.14) gives exactly $\Phi(X)=PXP+QXQ=(X+ZXZ)/2$, whose diamond distance from identity is one by the argument for (P.15). This also proves attainability. These are different full channels: (P.11) sends $|0\rangle\langle2|$ to $u|e_0\rangle\langle e_4|$, while (P.17) sends it to zero. Thus neither the gain nor even the two full phase outputs fix the individual recovery error. $\square$

**Theorem 5.2 (the fixed physical embedding at zero gain).** Retain the physical isometry

$$
E=\bigl((e_0+e_4)/\sqrt2,\ (e_1+e_3)/\sqrt2,\ e_2\bigr),
\quad E^\dagger E=I_3,\quad D^\dagger EL=E.
\tag{P.18}
$$

The physical channels $N_0^{\rm ph}(X)=EXE^\dagger$ and $N_1^{\rm ph}(X)=E\Phi(X)E^\dagger$ have the identical native $\theta$ outputs, belong to $\mathcal R_0$, and satisfy

$$
\gamma(N_0^{\rm ph})=\gamma(N_1^{\rm ph})=0,
\qquad \delta(N_0^{\rm ph})=0,\qquad\delta(N_1^{\rm ph})=1.
\tag{P.19}
$$

**Proof.** The two channels agree on the $P$-supported algebra. By the intertwining identity in (P.18), their passive phase outputs are $E\chi_\mp$, conjugate states with difference spectrum $(1,0,0,0,-1)$. Their physical populations are $(1/4,1/4,0,1/4,1/4)$ and $\langle n_1n_3\rangle=1/4$. Hence their actual $B_0=0$ and $B_k=1$ for $k\geq1$.

Set $f_0=(e_0-e_4)/\sqrt2$, $f_1=(e_1-e_3)/\sqrt2$. The full physical decoder with Kraus matrices $E^\dagger$, $|2\rangle\langle f_0|$, $|2\rangle\langle f_1|$ has TP sum $I_5$ and composites $\mathrm{id}_3$ and $\Phi$ respectively on every complex input matrix. The first error is zero. The orthogonal physical states $(|0\rangle\pm|2\rangle)/\sqrt2$ have identical $N_1^{\rm ph}$ outputs; contraction forces error at least one, attained by this decoder. This proves (P.19) using the particular $E$, without replacing it by (P.11)'s embedding.

Using physical $\chi_\pm$ instead would yield passive inputs $L^\dagger\chi_\pm=\theta_\pm$ and real output states $E\theta_\pm$. Their difference has nonzero real part and fails oldblindness. Spectrum and populations do not repair this different-input failure. $\square$

**Theorem 5.3 (common-code restriction).** If an actual pair satisfying the oldblind condition (P.4) is supported in one common three-dimensional complex subspace of $\mathbb C^5$, then $\beta=0$.

**Proof.** Its difference has rank at most three. A purely imaginary Hermitian matrix $iA_0$ with $A_0$ real skew-symmetric has even rank, hence rank at most two here. Its second positive spectral weight must vanish. In particular a common three-dimensional isometric code cannot supply the positive-$\beta$ witnesses, whose combined phase support has dimension four. This is a restriction on that actual common support, not on all noisy qutrit encoders. $\square$

## 6. Class optimization and remaining mathematical obligations

**Theorem 6.1 (bounds with their optimization order).** Define $\delta^*_{\mathcal C}(\beta)=\inf_{N^{\rm ph}\in\mathcal C_\beta}\delta(N^{\rm ph})$ and $\delta^*_{\mathcal R}(\beta)=\inf_{N^{\rm ph}\in\mathcal R_\beta}\delta(N^{\rm ph})$. Then both classes are nonempty and

$$
L(\beta)\leq\delta^*_{\mathcal C}(\beta)
\leq\delta^*_{\mathcal R}(\beta)\leq U(\beta).
\tag{P.20}
$$

Both infima are zero at $\beta=0$. At $\beta=1/2$ the interval is $[1/5,1-1/\sqrt2]$. For $\beta>0$, $0<L(\beta)<U(\beta)$.

**Proof.** Theorem 3.1 supplies the per-encoder lower bound; class inclusion supplies the middle inequality; Theorem 4.1 supplies one actual real-class encoder and its optimum, proving nonemptiness and the upper inequality. At zero the bounds coincide. For $u=\sqrt{1-\beta}<1$, $L/U=2(1+u)/(3+2\sqrt2u)<1$. Theorem 5.1 prevents interpreting $U$ as an upper bound for every encoder. $\square$

**Definition 6.2 (unresolved sharp curve and applicability).** The positive-$\beta$ sharp value of either infimum in (P.20) remains unresolved here. Individual optimality of (P.11) is not optimality over encoders. The [companion certificates](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md) concern $\mathcal R_\beta$; their real-frame geometry is not extended to all of $\mathcal C_\beta$.

For an externally specified source or historical fiber, applying these statements additionally requires identifying its actual encoder, input pair and outputs with the stipulated objects, proving both candidate sources belong to the same source fiber, and proving the words are jointly legitimate there. Neither a population constraint, an isometric embedding, passive coordinates, nor unlimited-budget controllability supplies these bridges. Recovery invariance (P.16) is a bijection inside a mathematical optimization; an arbitrary output-unitary conjugation with the native menu held fixed need not preserve oldblindness or $B_k$. Source preparation, finite-history transport, native encoder/decoder apparatus, hardware resources, the broader U7 programme and physical ontology are not conclusions of these conditional channel statements.

**Definition 6.3 (mathematical attribution).** The owner's exact finite-word and fixed-event results, standard quantum-channel definitions, Watrous fidelity properties and Bény–Oreshkov duality are reused in their stated domains. Exact finite Kraus recovery and full-output completion already have [repository sources](../../../Blueprint/D5/S3/Quantum/Recovery/FiniteKrausReversibility.md); they are not redeclared as new general results here. The same-actual-encoder composition (P.7)–(P.8), the specified witnesses and counterexamples (P.11)–(P.19), and their class comparison (P.20) are repo-derived ordinary application proofs. No global originality or priority is inferred. The owner's [finite-root continuation](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_FINITE_ROOT_CONTINUATION.md#65-精确根指定与原固定菜单的条件接口) treats population-constrained input existence and adds no encoder preparation or recovery theorem. Finite algebraic or numerical controls can check displayed identities on their tested inputs; the all-channel and all-reference claims here depend on the analytic proofs, not finite sampling. These source proofs do not assert Lean/kernel verification.

## 追加锚（本行以下为增补区）

## 7. The fixed complex extension fiber and its channel metric

**Definition 7.1 (the whole observed-input restriction).** Fix $0<\beta\leq1/2$, $a=1-\beta$, and retain the passive input, output and physical correspondence of Definition 1.1. Write

$$
\begin{gathered}
P=|0\rangle\langle0|+|1\rangle\langle1|,\qquad Q=|2\rangle\langle2|,\qquad
H=|e_4\rangle\langle2|,\\
V_0=|e_0\rangle\langle0|+|e_1\rangle\langle1|,\qquad
V_1=|e_2\rangle\langle0|+|e_3\rangle\langle1|,\\
p_0=a,\quad p_1=\beta,\qquad
V_j^\dagger V_k=\delta_{jk}P,\quad H^\dagger H=Q,\quad V_j^\dagger H=0.
\end{gathered}
\tag{P.21}
$$

The fiber $\mathfrak F_\beta$ consists of all complex-linear CPTP maps $N:M_3\to M_5$ satisfying, for every $X\in M_3$,

$$
N(PXP)=aV_0XV_0^\dagger+\beta V_1XV_1^\dagger,
\qquad N(QXQ)=HXH^\dagger.
\tag{P.22}
$$

In particular $N(Q)=|e_4\rangle\langle e_4|$. This fixes the entire $P$-supported matrix algebra, rather than just two states in it. The output sectors are the fixed orthogonal spaces $F=\operatorname{ran}V_0\oplus\operatorname{ran}V_1$ and $\mathbb C e_4$. No output rotation or change of third output is included in this definition.

For a complex column $c=(c_0,c_1)$ with $\|c\|_2\leq1$, put

$$
w(c)=(\sqrt a\,c_0,\sqrt\beta\,c_1),\qquad r(c)=\|w(c)\|_2,
$$

and define its gluing-coordinate map on every complex matrix by

$$
\begin{aligned}
N_c(X)={}&aV_0XV_0^\dagger+\beta V_1XV_1^\dagger+HXH^\dagger\\
&+\sum_{j=0}^1\bigl(w_j(c)V_jXH^\dagger+
                  \overline{w_j(c)}HXV_j^\dagger\bigr).
\end{aligned}
\tag{P.23}
$$

These coordinates use the fixed Kraus choices $(\sqrt a V_0,\sqrt\beta V_1)$ and $H$. The general completeness of such contraction coordinates is the gluing theorem of J. Åberg, [*Gluing of completely positive maps*, arXiv:quant-ph/0302182v2, Proposition 3, (4)–(5)](https://arxiv.org/pdf/quant-ph/0302182v2), with trace preservation supplied by Proposition 1. Its concrete hypotheses and both directions for (P.22) are verified as an intermediate in the following proof. The gluing ball itself is literature-attested.

All diamond norms below are unhalved: for a linear map $\Lambda$ this norm is the supremum of $\|(\Lambda\otimes\mathrm{id}_m)(X)\|_1$ over every finite $m$ and every complex matrix $X$ with $\|X\|_1=1$. Recoveries remain arbitrary complex CPTP maps on all of $M_5$.

**Theorem 7.2 (exact metric on the fixed complex fiber).** In the gluing coordinates (P.23), which biject the complex unit two-ball with $\mathfrak F_\beta$,

$$
\|N_c-N_d\|_\diamond
=\|w(c)-w(d)\|_2
=\sqrt{a|c_0-d_0|^2+\beta|c_1-d_1|^2}.
\tag{P.24}
$$

The upper bound holds for every finite reference and every complex input matrix. A pure input without a reference attains it. The bijection is the cited gluing intermediate; (P.24) is the operational metric in these fixed weighted coordinates.

**Proof.** For the gluing intermediate, Åberg's source spaces are $P A$ and $Q A$, and its target spaces are $F$ and $\mathbb C e_4$. The restricted maps in (P.22) are trace preserving between those spaces: their Kraus TP sums are $P$ and $Q$. Since $a,\beta>0$ and $V_0,V_1$ have orthogonal nonzero ranges, their two Kraus matrices are linearly independent; the other restriction has the single nonzero Kraus matrix $H$. Every $N$ in (P.22) is a trace-preserving gluing. Equivalently it is subspace preserving: for a pure input in either sector its output has zero weight outside the corresponding target sector. In any Kraus representation positivity then forces every Kraus vector at that input into that sector. Thus Proposition 3 applies with a $2\times1$ matrix $C=c$; its condition $cc^\dagger\preceq I_2$ is precisely $\|c\|_2\leq1$, and its cross terms are (P.23).

One can also verify the necessity in this specialization directly, without a locality assumption. Use the input-first unnormalized Choi matrix $J_N=\sum_{i,k=0}^2|i\rangle\langle k|\otimes N(|i\rangle\langle k|)$ and set

$$
\xi_j=\sum_{i=0}^1|i\rangle\otimes V_j|i\rangle,
\qquad h=|2\rangle\otimes e_4.
$$

The two diagonal input blocks of $J_N$ are $\sum_jp_j|\xi_j\rangle\langle\xi_j|$ and $|h\rangle\langle h|$. A vector of zero quadratic form for a PSD matrix is in its kernel, as follows by taking its positive square root. Consequently all remaining Choi entries must join $\operatorname{span}(\xi_0,\xi_1)$ to $\mathbb C h$. The only possible form is

$$
J_N=\sum_jp_j|\xi_j\rangle\langle\xi_j|+|h\rangle\langle h|
+\sum_j\bigl(w_j|\xi_j\rangle\langle h|+
                 \overline{w_j}|h\rangle\langle\xi_j|\bigr).
$$

In the orthonormal basis $(\xi_0/\sqrt2,\xi_1/\sqrt2,h)$ its nonzero block and its Schur-complement condition are

$$
\begin{pmatrix}
2a&0&\sqrt2w_0\\
0&2\beta&\sqrt2w_1\\
\sqrt2\overline{w_0}&\sqrt2\overline{w_1}&1
\end{pmatrix}\succeq0
\quad\Longleftrightarrow\quad
\frac{|w_0|^2}{a}+\frac{|w_1|^2}{\beta}\leq1.
\tag{P.25}
$$

Indeed completing the square in the first two coordinates leaves the last quadratic coefficient $1-|w_0|^2/a-|w_1|^2/\beta$. Taking $c_j=w_j/\sqrt{p_j}$ gives exactly the asserted domain and (P.23). The Choi convention differs from the output-first convention in Watrous by a tensor swap only.

For sufficiency, an explicit Kraus list for every permitted complex $c$ is

$$
K_j=\sqrt{p_j}V_j+\overline{c_j}H\quad(j=0,1),
\qquad K_*=\sqrt{1-\|c\|_2^2}\,H.
\tag{P.26}
$$

Its TP sum is $(a+\beta)P+Q=I_3$ because $V_j^\dagger H=0$; its channel is (P.23) on every matrix. This also covers $\|c\|_2=1$, where $K_*=0$. Positivity, Kraus representation and TP are used in the finite-dimensional sense of [Watrous, *The Theory of Quantum Information*, Chapter 2, Theorem 2.22 and Corollary 2.27](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). The positive weights make $w$ and then $c$ unique, for example by evaluating $N(|0\rangle\langle2|)$ on the independent vectors $e_0,e_2$. This completes the specialized gluing verification.

It remains to prove the metric. Put $v=w(c)-w(d)$ and $s=\|v\|_2$. If $s=0$, (P.23) makes the difference map zero. Otherwise define the isometry $J_v:A\to B$ by

$$
J_v|i\rangle=s^{-1}\sum_{j=0}^1v_jV_j|i\rangle\quad(i=0,1),
\qquad J_v|2\rangle=e_4.
$$

Let $Z=P-Q$ and $\mathcal O(X)=PXQ+QXP=(X-ZXZ)/2$. Direct substitution gives the identity of linear maps

$$
(N_c-N_d)(X)=sJ_v\mathcal O(X)J_v^\dagger.
\tag{P.27}
$$

For every finite reference, unitary invariance and the triangle inequality give $\|(\mathcal O\otimes\mathrm{id})(X)\|_1\leq\|X\|_1$, even for non-Hermitian $X$. Isometric conjugation preserves all singular values other than appended zeros, so (P.27) proves the upper bound $s$ at every reference size. For $\eta=(|0\rangle+|2\rangle)/\sqrt2$, $\mathcal O(|\eta\rangle\langle\eta|)$ has eigenvalues $1/2,-1/2,0$ and trace norm one. Its image in (P.27) has trace norm $s$. This proves (P.24), including attainment and complex phases. These direct bounds agree with the complete-reference diamond interface in [Watrous, Chapter 3, Definition 3.43, Proposition 3.44 and Theorem 3.46](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf). $\square$

## 8. Complete recovery on the complex fiber

**Theorem 8.1 (a recovery budget and simultaneous domination).** For each complex $t=(t_0,t_1)$ with $\|t\|_2\leq1$, define $R_t:M_5\to M_3$ by the Kraus list

$$
T_j=V_j^\dagger+\overline{t_j}H^\dagger\quad(j=0,1),
\qquad T_*=\sqrt{1-\|t\|_2^2}\,H^\dagger.
\tag{P.28}
$$

It is CPTP on the entire output, and with the bilinear scalar $h(c,t)=\sum_jw_j(c)t_j$ its composition on every $X\in M_3$ is

$$
R_tN_c(X)=\Psi_{h(c,t)}(X),\qquad
\Psi_h(X)=PXP+QXQ+hPXQ+\overline h QXP.
\tag{P.29}
$$

For all $c$ and $t$ in their balls,

$$
\|R_tN_c-\mathrm{id}_3\|_\diamond=|1-h(c,t)|.
\tag{P.30}
$$

Conversely, every complex whole-output CPTP recovery $R$ determines a single $t_R$ with $\|t_R\|_2\leq1$ such that simultaneously for every $c$,

$$
\|RN_c-\mathrm{id}_3\|_\diamond
\geq|1-h(c,t_R)|
=\|R_{t_R}N_c-\mathrm{id}_3\|_\diamond.
\tag{P.31}
$$

Thus one member of (P.28) weakly improves that recovery's error at every channel in this fixed fiber. This comparison concerns the stated diamond-error objectives, not equality of the arbitrary recovery maps.

**Proof.** The TP sum of (P.28) is

$$
\sum_jT_j^\dagger T_j+T_*^\dagger T_*
=V_0V_0^\dagger+V_1V_1^\dagger+HH^\dagger=I_5.
\tag{P.32}
$$

All cross terms vanish since $V_j|2\rangle=0$ and $HP=0$. In particular no part of $M_5$ is left undefined. On $PXP$, each branch $V_j$ is decoded identically and its weight is $p_j$; their sum is $PXP$. On $QXQ$, the sum of the squared $H^\dagger$ coefficients is one and gives $QXQ$. The cross basis elements satisfy

$$
R_t\bigl(V_j|i\rangle\langle e_4|\bigr)=t_j|i\rangle\langle2|
\quad(i=0,1),
$$

with the adjoint relation for the opposite block. Applying (P.23) proves (P.29) on a basis of all nine complex matrix units, hence on every matrix, and after tensoring with every reference. In particular $|h(c,t)|\leq r(c)\leq\sqrt a\leq1$.

For the norm identity set $\kappa=h-1$. If $\kappa=0$ the difference map vanishes. Otherwise the unitary $U_\kappa=(\kappa/|\kappa|)P+Q$ gives

$$
\Psi_h-\mathrm{id}_3=|\kappa|\operatorname{Ad}_{U_\kappa}\circ\mathcal O.
$$

The reference-uniform contraction bound for $\mathcal O$ proved in Theorem 7.2 gives an upper bound $|\kappa|$. The same pure state $\eta$ used there gives an output difference with two nonzero eigenvalues $\pm|\kappa|/2$, so it attains this bound. This proves (P.30) for arbitrary complex $h$ that occurs here, without restricting references or input matrices.

For the converse, represent any $R$ by a finite Stinespring isometry $W:B\to A\otimes E$, so $R(Y)=\operatorname{Tr}_E(WYW^\dagger)$. Such an isometry exists for every finite-dimensional complex CPTP map by the cited Corollary 2.27. Define

$$
\begin{gathered}
A_R:\mathbb C^2\to E,\qquad
A_R f_j=(\langle0|\otimes I_E)WV_j|0\rangle,\\
b_R=(\langle2|\otimes I_E)We_4,\qquad
(t_R)_j=b_R^\dagger A_Rf_j
=\langle0|R(V_j|0\rangle\langle e_4|)|2\rangle,
\end{gathered}
\tag{P.33}
$$

where $f_0,f_1$ are the standard coordinate vectors of $\mathbb C^2$. The map $f_j\mapsto V_j|0\rangle$ is an isometry, $W$ is an isometry, and $\langle0|\otimes I_E$ is a contraction. Hence $\|A_R\|_{\rm op}\leq1$; also $\|b_R\|_2\leq1$. Therefore the row $b_R^\dagger A_R$ has Euclidean norm at most one, giving $\|t_R\|_2\leq1$. This budget uses the same isometry $W$ for both branches and all channels.

The matrix $E_{02}=|0\rangle\langle2|$ has trace norm one and

$$
N_c(E_{02})=\sum_jw_j(c)V_j|0\rangle\langle e_4|.
$$

Its recovered $(0,2)$ matrix entry is $h(c,t_R)$. A matrix entry is bounded by the trace norm, so

$$
\|RN_c-\mathrm{id}_3\|_\diamond
\geq\|RN_c(E_{02})-E_{02}\|_1
\geq|h(c,t_R)-1|.
$$

The first inequality uses the defining norm over all complex matrices, with reference size one already sufficient for this lower certificate. Combining it with (P.30) proves (P.31). No assumption that $R$ preserves either input sector, has real Kraus entries, or belongs to the displayed decoder family entered the lower bound. $\square$

**Theorem 8.2 (exact individual optimum and fiber equality cases).** For every $c$ in the complex unit two-ball,

$$
\delta(N_c)=1-r(c).
\tag{P.34}
$$

If $r(c)>0$, a single attaining decoder is (P.28) with $t_j=\overline{w_j(c)}/r(c)$. It serves every unknown input matrix and every finite reference. If $r(c)=0$, then $c=0$ and every decoder (P.28) attains error one. Over the whole fixed fiber,

$$
\min_{N\in\mathfrak F_\beta}\delta(N)=1-\sqrt a,
\qquad \max_{N\in\mathfrak F_\beta}\delta(N)=1.
\tag{P.35}
$$

For $0<\beta<1/2$ the minimizers are exactly $c=(e^{i\phi},0)$, $\phi\in\mathbb R$; for $\beta=1/2$ they are exactly $\|c\|_2=1$. For every positive $\beta$ the unique maximizing channel is $N_0$.

**Proof.** For any $R$, (P.31) and Cauchy–Schwarz imply

$$
\|RN_c-\mathrm{id}_3\|_\diamond
\geq|1-h(c,t_R)|\geq1-|h(c,t_R)|\geq1-r(c).
$$

For $r(c)>0$, the stipulated $t$ has norm one, and $h(c,t)=r(c)$ is real. Equations (P.29)–(P.30) then attain $1-r(c)$. For $r(c)=0$, $h=0$ for every $t$ and the recovered map is $PXP+QXQ$; its error is one by (P.30). Both weights are positive, so $r=0$ forces $c=0$.

Finally,

$$
r(c)^2=a\|c\|_2^2-(a-\beta)|c_1|^2\leq a.
$$

If $a>\beta$, equality requires both $\|c\|_2=1$ and $c_1=0$, and these requirements suffice. If $a=\beta=1/2$, equality is equivalent to $\|c\|_2=1$. The minimum of $r$ is zero only at $c=0$. This proves every equality case in (P.35). $\square$

## 9. Compatibility of one recovery with several full channels

**Theorem 9.1 (exact common-optimal ray criterion).** Let $S$ be any nonempty subset of the complex unit two-ball. There exists one complex whole-output CPTP recovery $R$ such that

$$
\|RN_c-\mathrm{id}_3\|_\diamond=\delta(N_c)
\quad\text{for every }c\in S
\tag{P.36}
$$

if and only if all nonzero $w(c)$, $c\in S$, have one identical unit direction $w(c)/r(c)$. The condition is vacuous when all $w(c)$ vanish. A zero member imposes no additional restriction on this existence criterion. The direction includes complex phase; identifying directions modulo a phase gives an incorrect criterion.

**Proof.** Suppose first that a common $R$ exists, and take its one vector $t_R$ from (P.33). For each member with $r=r(c)>0$, Theorems 8.1–8.2 give

$$
1-r\leq1-|h(c,t_R)|\leq|1-h(c,t_R)|
\leq\|RN_c-\mathrm{id}_3\|_\diamond=1-r.
$$

All terms are equal. Thus $|h(c,t_R)|=r$, and equality in $|1-h|\geq1-|h|$ forces $h(c,t_R)=r$ real and positive. More explicitly the difference between the squares of these two quantities is $2(|h|-\operatorname{Re}h)$, so its vanishing fixes this phase. Equality in Cauchy–Schwarz, together with $\|t_R\|_2\leq1$, then forces

$$
\|t_R\|_2=1,\qquad
t_R=\overline{w(c)}/r(c).
\tag{P.37}
$$

Since the left side is fixed by $R$, all nonzero directions are identical. The argument also covers $r=1$ if it occurs; there is no division by $1-r$.

Conversely, if the nonzero directions equal a unit vector $d$, take $t=\overline d$ in (P.28). Then $h(c,t)=r(c)$ for every nonzero member; it is zero on every zero member. Equation (P.30) gives exactly each individual error (P.34). If all members vanish, take $t=0$. This constructs one whole-output map before the unknown channel member, unknown input and reference are chosen. In particular a pair $w$ and $e^{i\phi}w$ with $w\ne0$ satisfies the criterion exactly when $e^{i\phi}=1$. $\square$

**Theorem 9.2 (shared minimax value and a strict two-channel separation).** For any such nonempty $S$, define

$$
\Delta_{\rm sh}(S)=\inf_{R\ {\rm CPTP}:M_5\to M_3}
\sup_{c\in S}\|RN_c-\mathrm{id}_3\|_\diamond.
$$

The exact common-recovery optimization has the attained representation

$$
\Delta_{\rm sh}(S)=\min_{\|t\|_2\leq1}
\sup_{c\in S}\left|1-\sum_jw_j(c)t_j\right|.
\tag{P.38}
$$

In particular, for the legal parameters

$$
c^A=(\sqrt{\beta/a},0),\qquad c^B=(0,1),\qquad s=\sqrt\beta,
\tag{P.39}
$$

one has

$$
\begin{gathered}
\delta(N_{c^A})=\delta(N_{c^B})=1-\sqrt\beta,\\
\|N_{c^A}-N_{c^B}\|_\diamond=\sqrt{2\beta},\\
\Delta_{\rm sh}(\{c^A,c^B\})=1-\sqrt{\beta/2}
>1-\sqrt\beta.
\end{gathered}
\tag{P.40}
$$

The last value optimizes all complex CPTP recoveries, with one shared decoder required for both encoders and every unknown input and finite reference.

**Proof.** For every $R$, its one $t_R$ in (P.31) bounds all errors below by the objective on the right of (P.38). Conversely, for any allowed $t$, (P.30) realizes that objective simultaneously using $R_t$. This proves equality of the infima. The objective is finite and continuous even if $S$ is infinite or not closed: the reverse triangle inequality and $\|w(c)\|_2\leq\sqrt a$ show that it is $\sqrt a$-Lipschitz in $t$. The complex closed unit ball is compact as a real four-dimensional set, so a minimizing $t$ and its single whole-output decoder exist.

For (P.39), $\beta\leq a$ proves $\|c^A\|_2\leq1$ and $\|c^B\|_2=1$. Their weighted vectors are $w^A=(s,0)$ and $w^B=(0,s)$. Thus (P.34) gives both individual values and (P.24) gives their distance. To give a lower certificate for an arbitrary $R$, let $t=t_R$. Then

$$
\begin{aligned}
\max\{\|RN_{c^A}-\mathrm{id}\|_\diamond,
       \|RN_{c^B}-\mathrm{id}\|_\diamond\}
&\geq\max\{|1-st_0|,|1-st_1|\}\\
&\geq1-s\min\{\operatorname{Re}t_0,\operatorname{Re}t_1\}
\geq1-s/\sqrt2.
\end{aligned}
\tag{P.41}
$$

For the final inequality, if both real parts exceeded $1/\sqrt2$, then $|t_0|^2+|t_1|^2>1$, contrary to (P.33). This certificate makes no restriction on the recovery other than whole-output complex CPTP.

For the matching upper value choose $t_0=t_1=1/\sqrt2$ in (P.28), so that $T_*=0$. Its TP sum is $I_5$ by (P.32), and its composition with either channel is the same map on every complex input matrix:

$$
R_tN_{c^A}=R_tN_{c^B}
=\frac{1+s/\sqrt2}{2}\,\mathrm{id}_3
+\frac{1-s/\sqrt2}{2}\operatorname{Ad}_Z.
\tag{P.42}
$$

Equation (P.30) bounds the diamond error at every finite reference by $1-s/\sqrt2$ and attains it on $\eta$. This proves (P.40). Strictness follows from $s>0$. At $\beta=1/2$, both parameters lie on the unit sphere: the individual value is $1-1/\sqrt2$, their distance is one, and their shared optimum is $1/2$. These are values in the unhalved convention. $\square$

## 10. Endpoints, native observables and mathematical scope

**Theorem 10.1 (the zero-weight coordinate is absent).** At $\beta=0$, the fiber defined by (P.22) is parametrized injectively by a single complex number $\zeta$ with $|\zeta|\leq1$:

$$
N_\zeta(X)=V_0XV_0^\dagger+HXH^\dagger
+\zeta V_0XH^\dagger+\overline\zeta HXV_0^\dagger.
\tag{P.43}
$$

Its exact quantities are

$$
\|N_\zeta-N_\xi\|_\diamond=|\zeta-\xi|,
\qquad \delta(N_\zeta)=1-|\zeta|.
\tag{P.44}
$$

For any nonempty set of these channels, a common individually optimal recovery exists exactly when all its nonzero $\zeta$ have the same phase $\zeta/|\zeta|$. Zeros impose no extra constraint. Its shared minimax value is

$$
\min_{|t|\leq1}\sup_{\zeta\in S}|1-\zeta t|.
\tag{P.45}
$$

The individual minimum is zero exactly at $|\zeta|=1$; the maximum is one exactly at $\zeta=0$. There is no injective two-ball parametrization at this endpoint.

**Proof.** The $P$ restriction has the single nonzero Kraus matrix $V_0$, so Åberg's Proposition 3 now has a $1\times1$ gluing matrix, not a $2\times1$ one. Equivalently the Choi kernel argument above removes the whole $\xi_1$ direction before a Schur complement is taken, leaving $|\zeta|\leq1$. A direct Kraus list is $V_0+\overline\zeta H$ and $\sqrt{1-|\zeta|^2}H$. This proves necessity, sufficiency and injectivity in (P.43).

The metric proof (P.27) applies with the one active component $v=\zeta-\xi$. To complete the decoder on the whole five-dimensional output, for each $|t|\leq1$ take

$$
T_0=V_0^\dagger+\overline t H^\dagger,\qquad
T_1=V_1^\dagger,\qquad T_*=\sqrt{1-|t|^2}H^\dagger.
$$

The inactive branch $T_1$ is needed for the TP sum $I_5$ although the encoder never occupies its range. These Kraus matrices give $\Psi_{\zeta t}$ on every matrix and error $|1-\zeta t|$ by the proof of (P.30). For an arbitrary recovery, retain only the $j=0$ entry in (P.33), obtaining $|t_R|\leq1$ and the bound $|1-\zeta t_R|$. This proves (P.44)–(P.45), the phase criterion by the equality argument (P.37), and all extremal cases. If one formally retains a discarded coordinate $c_1$, maps with the same $c_0=\zeta$ coincide; it is not a channel parameter. The two parameters in (P.39) consequently both reduce to $\zeta=0$ at zero beta, with distance zero and individual and shared errors one, so their strict separation requires $\beta>0$. $\square$

**Theorem 10.2 (fixed native outputs throughout the fiber).** For every positive $\beta$ and every permitted complex $c$, the physical channel $N_c^{\rm ph}$ obtained by (P.1) belongs to $\mathcal C_\beta$ and has the identical native candidate outputs (P.13), with the physical sign interchange (P.2). Under exactly Assumption 1.2,

$$
B_0=0,\qquad B_1=a,\qquad B_k=1\ (k\geq2),\qquad \gamma=\beta
\tag{P.46}
$$

for every member, while its full-input optimum is (P.34). The same assertions at zero beta use (P.43) and (P.44). Real $c$ and real $\zeta$ give real passive Kraus representations, so these subfamilies belong to $\mathcal R_\beta$. All metric, optimum and common-recovery statements transport to the fixed physical frames by (P.16), including the same single shared recovery for each specified set.

**Proof.** The two passive inputs $\chi_\pm$ lie entirely in $P A$, so (P.22) gives exactly (P.13), independently of the cross-block coefficients. The four vectors displayed there are orthonormal and their difference is purely imaginary Hermitian with spectrum $(a,\beta,0,-\beta,-a)$. Thus these are actual members of $\mathcal C_\beta$ in the prescribed physical coordinates, rather than an inference from their populations. Their actual common diagonal is $(a/2,a/2,\beta/2,\beta/2,0)$. Theorem 2.1 applies on each same encoder with the same native candidate pair and proves (P.46); it requires the independent constrained drives and forward-call budget of Assumption 1.2. At zero the inactive branch drops out and the same conclusion follows with $B_1=1$. At half beta it reads $B_1=1/2$, $B_2=1$.

The Kraus lists (P.26) and the list for (P.43) have real entries for real parameters, proving the claimed real subfamilies. For all complex parameters, (P.16) is a fixed bijection on the full recovery class. The same $D,L$ conjugate every member; for a common passive recovery $R$, the one map $R^{\rm ph}=\operatorname{Ad}_L\circ R\circ\operatorname{Ad}_{D^\dagger}$ therefore serves every corresponding physical member. Unitary invariance with every reference proves the physical metric and recovery assertions. These coordinate equalities do not install physical gates or assert that the arbitrary CPTP decoders are realizable by the native unitary-and-terminal-measurement menu. $\square$

**Definition 10.3 (inherited content and applicability limits).** The scalar path $c=(\lambda,0)$, $0\leq\lambda\leq1$, is the interpolation in the supplied phase-budget/recovery manuscript. Its formulas $\delta=1-\sqrt a\lambda$ and $\|N_\lambda-N_\mu\|_\diamond=\sqrt a|\lambda-\mu|$, and its error range $[1-\sqrt a,1]$, are inherited reference content. Its coherent and erased endpoints are already Theorems 4.1 and 5.1. The fixed-fiber extrema (P.35) identify additional equality cases but do not make that scalar error interval a new result.

The [companion certificates, Theorem 18.2](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#18-an-actual-real-kraus-family-with-coupled-third-column-data) allow a varying third output; (P.22) fixes it to the pure state on $e_4$. [Sections 31–32 there](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#31-complete-weighted-rank-two-plane-coordinates) already give real rank-two plane and arbitrary-third-column coordinates, including overlapping real boundary instances of this fiber. Explicitly, at their $\theta=0$, identify $(b_1,g_1,b_2,g_2,h)$ with $(e_0,e_1,e_2,e_3,e_4)$ and take $A=(\sqrt a e_0,\sqrt\beta e_2)$ and $T=(c_0e_4,c_1e_4)$ with real $c$ of norm one. Their (R.149) is then (P.26) with $K_*=0$. These instances are not additional content of this parametrization. No arbitrary-third-output reduction or common-projection estimate is used in (P.24)–(P.45). A channel agreeing only on the two phase states need not satisfy the whole-algebra restriction or the fixed third output in (P.22); the fiber equalities therefore do not settle the broader sharp-curve questions of Definition 6.2 or the companion volumes.

The complete contraction parametrization is literature-attested in Åberg's cited Proposition 3. Kraus rank and extreme-point structure of general gluings also belong to its Propositions 4–5; no claim of new general gluing geometry is attached here. A related implementation-sensitive control-sector description is [Abbott, Wechs, Horsman, Mhalla and Branciard, *Communication Through Coherent Control of Quantum Channels*, Quantum **4**, 333, arXiv:1810.09826v3, Appendix A, (A7)–(A9)](https://arxiv.org/pdf/1810.09826v3). It constrains an implementation transformation matrix by its channel Choi support and pseudoinverse. Its Appendix D, (D1)–(D2), studies channel differences with a separately supplied coherent control sector and defines distance as one half of the diamond norm. That control-sector setting and normalization are distinct from (P.22) and its unhalved qutrit recovery objective; the general fact that restricted channel descriptions can omit coherent information is already present in those sources.

The source-specific compositions here are the weighted full-fiber metric (P.24), the recovery comparison and equality analysis (P.28)–(P.38), and the shared-recovery separation (P.39)–(P.42), together with their explicitly stated endpoint and physical-coordinate consequences. They are repo-derived ordinary finite-dimensional paper arguments using the attributed intermediates. This attribution asserts no global priority or source audit beyond the cited overlap, and no Lean/kernel verification or physical realization.

A known-channel decoder may depend on its known complex direction but acts on all unknown inputs and references. A common decoder in (P.36) or (P.38) is chosen once for the whole specified set. Neither construction supplies the channel parameter by calibration or observation: all native candidate states in (P.46) coincide across the fiber. Identifying an external source with this fiber, acquiring its inputs, transporting histories, and providing native encoder or decoder apparatus require additional hypotheses. The phase-call bounds remain exactly those of Assumption 1.2; passive coordinate changes, arbitrary recoveries and reference systems add no free native operation.

## 追加锚（本行以下为增补区）

## 11. A phase circle inside the fixed extension fiber

**Definition 11.1 (a feasible phase orbit).** Retain Definition 7.1, its fixed passive frames and the unhalved diamond norm. Put $p_0=a=1-\beta$, $p_1=\beta$, where $0<\beta\leq1/2$. For a fixed unit vector $d=(d_0,d_1)\in\mathbb C^2$ choose

$$
0\leq r\leq R_\beta(d):=
\left(\frac{|d_0|^2}{a}+\frac{|d_1|^2}{\beta}\right)^{-1/2}.
\tag{P.47}
$$

Define $c_j(\varphi)=r e^{i\varphi}d_j/\sqrt{p_j}$ and $N_\varphi=N_{c(\varphi)}$. Thus $w(\varphi)=r e^{i\varphi}d$ in (P.23). The radius is a cross-block coherence-transfer strength; it is not an input population. All recoveries below may access the whole five-dimensional output, and must act on every unknown qutrit input and untouched finite reference.

**Theorem 11.2 (chord distance and the known-phase recovery).** For this orbit,

$$
\|N_\varphi-N_\psi\|_\diamond
=2r\left|\sin\frac{\varphi-\psi}{2}\right|,
\qquad \delta(N_\varphi)=1-r.
\tag{P.48}
$$

For $r>0$ the circle modulo $2\pi$ is injectively parametrized by its channels. A target output unitary generating it is

$$
S_\varphi=I_5+(e^{-i\varphi}-1)|e_4\rangle\langle e_4|,
\qquad N_\varphi=\operatorname{Ad}_{S_\varphi}\circ N_0.
\tag{P.49}
$$

Proof. The squared norm of $c(\varphi)$ is $r^2\sum_j|d_j|^2/p_j$, so (P.47) puts every member in the same fiber. Theorems 7.2 and 8.2 give (P.48), using $|e^{i\varphi}-e^{i\psi}|=2|\sin((\varphi-\psi)/2)|$. The zero set of that distance proves injectivity for $r>0$; for $r=0$ every channel is the same. Conjugation by $S_\varphi$ fixes the diagonal blocks of (P.25) and multiplies each $V_jXH^\dagger$ term by $e^{i\varphi}$, proving (P.49). Here $H$ is the embedding in Definition 7.1, not a Hamiltonian.

The same passive-frame correspondence as Theorem 10.2 transports these statements to physical channels. Equation (P.49) specifies a target unitary, without adding a continuously tunable native phase to Assumption 1.2. Under the separate addressable-block assumptions of [Static Compatibility–Fiber Theory, Assumption 30.2 and Theorem 31.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#31-固定非实相位下的有限多块射影通用性), it admits arbitrary projective finite-word approximation. That result gives no exact synthesis for an arbitrary angle and no uniform call or physical-time cost. The same restrictions apply to uses of this orbit as a clock. $\square$

## 12. Exact common recovery on an uncertain phase arc

**Definition 12.1 (one decoder for the whole arc).** For $0\leq\alpha\leq\pi$, set

$$
\Delta_{\rm arc}(r,\alpha)
=\inf_{R\ {\rm CPTP}}\sup_{|\varphi|\leq\alpha}
\|RN_\varphi-\mathrm{id}_3\|_\diamond.
\tag{P.50}
$$

The decoder is chosen before the unknown phase, input and reference. There is no accessible phase label in this experiment.

**Theorem 12.2 (the exact arc formula).** For every radius in (P.47),

$$
\Delta_{\rm arc}(r,\alpha)=
\begin{cases}
1,&r=0\text{ or }\cos\alpha\leq0,\\
\sqrt{1+r^2-2r\cos\alpha},&0<r\leq\cos\alpha,\\
\sin\alpha,&0<\cos\alpha<r.
\end{cases}
\tag{P.51}
$$

The optimum is attained by the one decoder $R_t$ of Theorem 8.1 with

$$
t=q_*\overline d,\qquad
q_*=
\begin{cases}
0,&r=0\text{ or }\cos\alpha\leq0,\\
\min\{1,\cos\alpha/r\},&r>0,\ \cos\alpha>0.
\end{cases}
\tag{P.52}
$$

Proof. Apply Theorem 9.2 to precisely this set of channel parameters. The complex bilinear pairing $z=d\cdot t$ traverses the entire closed unit disk: Cauchy–Schwarz gives $|z|\leq1$, and $t=z\overline d$ realizes every such $z$. The objective becomes

$$
F(z)=\max_{|\varphi|\leq\alpha}|1-rze^{i\varphi}|,
\qquad \min_{|z|\leq1}F(z).
\tag{P.53}
$$

This is a convex function and $F(\overline z)=F(z)$, by the symmetry of the phase interval. Therefore $F(\operatorname{Re}z)\leq F(z)$. If $r>0$ and a real $z=q$ is negative, its value at $\varphi=0$ exceeds one, whereas $F(0)=1$. A minimizer may thus be chosen in $q\in[0,1]$. On that interval the least cosine on the arc is $\cos\alpha$, and

$$
F(q)^2=1+r^2q^2-2rq\cos\alpha.
\tag{P.54}
$$

Minimizing this quadratic gives (P.52) and (P.51), including the shared boundary $r=\cos\alpha$. At $r=0$ the objective is identically one. Theorem 8.1 supplies the stated common decoder on the whole physical output. $\square$

**Definition 12.3 (phase uncertainty and clock calibration).** At $\alpha=0$, (P.51) is the known-channel value $1-r$. An arc of angular length at least $\pi$ has value one. These are recovery errors, not occupation-loss probabilities. If a separately specified clock law is $\varphi=\omega t$ and $|\Delta t|\leq\varepsilon$, its error interval gives $\alpha=|\omega|\varepsilon$ when this is at most $\pi$; a larger interval covers the full circle. This substitution requires the frequency, time scale and bounded-error guarantee as premises. It cannot calibrate them from native phase-candidate outputs, which are identical along the orbit by Theorem 10.2.

## 13. Recorded and discarded phase on the same orbit

**Definition 13.1 (an input-independent phase record).** Let $\{p_\ell\}_{\ell=1}^s$ be a finite probability distribution, independent of the unknown input. Its mechanism chooses a phase $\varphi_\ell$ and supplies an accessible orthonormal classical label $|\ell\rangle$. Define

$$
\mathcal N_{\rm flag}(X)=\sum_{\ell=1}^s
p_\ell|\ell\rangle\langle\ell|\otimes N_{\varphi_\ell}(X),
\qquad \overline N=\sum_{\ell=1}^s p_\ell N_{\varphi_\ell}.
\tag{P.55}
$$

The first channel supplies the record; the second discards it. Neither definition supposes that an unknown phase can be learned for free from $N_\varphi$.

**Theorem 13.2 (the exact recovery cost of discarding the record).** With the same whole-output recovery convention,

$$
\begin{aligned}
\delta(\mathcal N_{\rm flag})&=1-r,\\
\delta(\overline N)&=1-r|\mu|,\qquad
\mu=\sum_\ell p_\ell e^{i\varphi_\ell}.
\end{aligned}
\tag{P.56}
$$

Thus the increase is $r(1-|\mu|)$, even though every individual phase channel has the same recovery error and the same native candidate outputs.

Proof. For the upper bound with records, measure the supplied label and use $R_{t_\ell}$ with $t_\ell=e^{-i\varphi_\ell}\overline d$. Each resulting channel is the same $\Psi_r$ of Theorem 8.1, so the error is $1-r$.

For a lower bound let $\mathcal R$ be an arbitrary recovery of the flagged channel. Its restriction $R_\ell(X)=\mathcal R(|\ell\rangle\langle\ell|\otimes X)$ is a CPTP map for each label. Theorem 8.1 assigns it one vector $t_\ell$ of norm at most one. Testing the same unit-trace-norm matrix $E_{02}$ and its $(0,2)$ output entry gives

$$
\|\mathcal R\mathcal N_{\rm flag}-\mathrm{id}_3\|_\diamond
\geq|1-h|,\qquad
h=\sum_\ell p_\ell r e^{i\varphi_\ell}d\cdot t_\ell,
\qquad |h|\leq r.
\tag{P.57}
$$

Hence the error is at least $1-r$. No cancellation between branch errors is assumed. For the channel without records, linearity of (P.25) identifies its parameter as $\overline w=r\mu d$, still in the fiber because $|\mu|\leq1$. Theorem 8.2 gives its error in (P.56). $\square$

**Definition 13.3 (a specified diffusion model and its distinct population law).** For an unrecorded real Gaussian phase $\varphi_t$ of mean $\omega t$ and variance $2Dt$, with $D\geq0$ and $t\geq0$, the same finite-dimensional channel integral has $\mu_t=e^{i\omega t-Dt}$. Consequently its error is $1-re^{-Dt}$ by (P.56). The Gaussian characteristic-function identity is a standard probability input; the resulting error is an application to this fiber, not a derivation of $D$ from native gates. For number-phase evolution on a number basis, the corresponding average obeys

$$
\rho_{mn}(t)=e^{-i\omega(m-n)t-D(m-n)^2t}\rho_{mn}(0).
\tag{P.58}
$$

In particular every $\rho_{nn}$ is unchanged. This phase averaging is dephasing. A transfer of joint occupation into recorded output events requires an additional instrument, such as the one in [Collective Oscillators and Record Capacity, §4](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md#4-联合占据转移与记录时间的资源差异).

The source-specific results (P.48), (P.51) and (P.56) are repo-derived applications of the existing exact fiber metric and recovery theorems. General gluing and coherent-control antecedents retain the attribution of Definition 10.3. The circle does not reconstruct an unknown channel, supply a native decoder, or identify phase uncertainty with a loss of population.

## 追加锚（本行以下为增补区）

## 14. Partial phase records and their exact finite alphabet budget

**Definition 14.1 (accessible input-independent record).** Use the fixed orbit of Definition 11.1, with $w_\varphi=re^{i\varphi}d$, $\|d\|_2=1$, and the same feasible radius $r$. Write $N(w)$ for the channel with weighted coherence vector $w$ in (P.25). Let $\Phi$ be a random phase and $Y$ a finite or countable classical record. Their joint law is independent of the unknown logical input. Set

$$
p_y=\Pr(Y=y),\qquad m_y=\mathbb E[e^{i\Phi}\mid Y=y],\qquad
c(Y)=\sum_y p_y|m_y|.
\tag{P.59}
$$

Zero-probability labels may be omitted. The supplied record and quantum output form the channel

$$
\mathcal N_Y(X)=\sum_y p_y|y\rangle\langle y|\otimes N(rm_yd)(X).
\tag{P.60}
$$

For countably many labels the sum converges in trace norm. The recovery can read this actual label and access the entire five-dimensional output, as in Theorems 8.1–8.2. There is no additional phase reference correlated with $\Phi$. Since $|m_y|\leq1$, every conditional vector remains in the original feasible fiber. Recording, encoding and accessing $Y$ are supplied resources, not consequences of the channel's definition.

**Theorem 14.2 (partial-record recovery and finite alphabet capacity).** Under Definition 14.1,

$$
\delta(\mathcal N_Y)=1-rc(Y),\qquad
1-c(Y)=\frac12\inf_{|\widehat u(Y)|=1}
\mathbb E|e^{i\Phi}-\widehat u(Y)|^2.
\tag{P.61}
$$

If $\Phi$ is uniform on the circle and $Y$ has at most $K\geq1$ values, even allowing arbitrary randomized encoders, then

$$
\begin{aligned}
\max_Y c(Y)&=\frac K\pi\sin\frac\pi K,\\
\min_Y\delta(\mathcal N_Y)&=1-r\frac K\pi\sin\frac\pi K.
\end{aligned}
\tag{P.62}
$$

An equal-arc label attains both optima. For a fixed-width $b$-bit record, $K=2^b$, and fixed $r$,

$$
\delta_b-(1-r)=\frac{r\pi^2}{6}4^{-b}+O(16^{-b})
\quad(b\to\infty).
\tag{P.63}
$$

Proof. On branch $y$, Theorem 8.1 supplies a decoder with
$t_y=e^{-i\arg m_y}\overline d$ when $m_y\ne0$; any feasible vector works when $m_y=0$. Its composition is $\Psi_{r|m_y|}$. Measuring the label and applying these decoders gives $\Psi_{rc(Y)}$, with error $1-rc(Y)$.

Conversely, an arbitrary recovery restricts on each label to a CPTP map, with one budget vector $t_y$ satisfying $\|t_y\|_2\leq1$. The same $E_{02}$ test used in (P.57) gives

$$
\|\mathcal R\mathcal N_Y-\mathrm{id}_3\|_\diamond\geq|1-h|,
\qquad h=r\sum_y p_ym_yd\cdot t_y,
\qquad |h|\leq rc(Y).
\tag{P.64}
$$

This proves the first formula. Expanding the squared chordal loss gives
$2-2\operatorname{Re}\mathbb E[e^{i\Phi}\overline{\widehat u(Y)}]$.
Conditioning on $Y$ makes its minimum $2-2\sum_yp_y|m_y|$, attained by aligning each estimate with $m_y$. This proves the risk identity.

For (P.62), the circular quantization value is a literature input: Pandey and Roychowdhury, [*Constrained Quantization for Probability Distributions*, arXiv:2305.11110v9, Theorem 4.3 and Propositions 4.1–4.2](https://arxiv.org/html/2305.11110v9), give distortion $a^2+1-2aK\sin(\pi/K)/\pi$ for reconstruction on the radius-$a$ circle. Set $a=1$ and use (P.61). The following fixed-mass argument also verifies the scope for arbitrary randomized labels directly; neither the sine constant nor equal-arc quantization is a new result here. Describe every randomized encoder by measurable functions $0\leq q_y(\varphi)\leq1$, with $\sum_{y=1}^Kq_y(\varphi)=1$ almost everywhere. Define

$$
p_y=\frac1{2\pi}\int_0^{2\pi}q_y(\varphi)\,d\varphi,
\qquad v_y=\frac1{2\pi}\int_0^{2\pi}e^{i\varphi}q_y(\varphi)\,d\varphi.
\tag{P.65}
$$

Then $c(Y)=\sum_y|v_y|$. The next rearrangement is the classical fixed-mass maximization of a linear integral, often called the bathtub principle; see Lieb and Loss, [*Analysis*](https://doi.org/10.1090/gsm/014). It is an intermediate circular quantization argument, not a new general rearrangement theorem. Choose $\theta_y=\arg v_y$ (arbitrary for $v_y=0$), and let $A_y$ be the centered circular arc of length $2\pi p_y$. With $b_y=\cos(\pi p_y)$,

$$
(q_y-\mathbf1_{A_y})(\cos(\varphi-\theta_y)-b_y)\leq0
\quad\hbox{almost everywhere}.
$$

Inside the arc the two factors have opposite signs; outside the arc they also do. Their mass difference integrates to zero. Thus

$$
|v_y|\leq\frac1{2\pi}\int_{A_y}\cos(\varphi-\theta_y)\,d\varphi
=\frac{\sin(\pi p_y)}\pi.
\tag{P.66}
$$

The formula includes $p_y=0,1$. Concavity of sine on $[0,\pi]$, $\sum_yp_y=1$, and Jensen's inequality give $\sum_y|v_y|\leq K\sin(\pi/K)/\pi$. Disjoint equal arcs realize equality, with deterministic labels. Taylor expansion of this value gives (P.63). $\square$

**Definition 14.3 (objective and attribution).** The source-specific content of Theorem 14.2 is the exact conversion of posterior circular estimation risk and the cited finite alphabet capacity into whole-output recovery error in the AURIC fiber; it is repo-derived from Theorem 8.1. The squared-chord estimation identity, the quantization optimum and circular fixed-mass argument are attributed intermediates. The diamond norm is taken after averaging the unknown phase conditional on the supplied record. It is not the worst-case unknown-phase objective of Theorem 12.2. The equal-arc optimum allows any measurable encoder; an implementation with restricted native gates must separately realize that encoder and count all accessible side information, including timestamps and real-valued operands.

## 15. Increasing accessible records and the phase-recovery limit

**Definition 15.1 (a fixed target and nested actual records).** Fix one random unit complex number $X=e^{i\Phi}$ throughout the experiment. Let $\mathcal F_n$ be the sigma-algebra generated by the observer's actual accessible finite or countable record at stage $n$, with $\mathcal F_n\subseteq\mathcal F_{n+1}$. Put

$$
Z_n=\mathbb E[X\mid\mathcal F_n],\qquad
c_n=\mathbb E|Z_n|,\qquad
\mathcal F_\infty=\sigma\left(\bigcup_n\mathcal F_n\right),
\qquad \delta_n=1-rc_n.
\tag{P.67}
$$

By Theorem 14.2, $\delta_n$ is the optimal error for the effective channel supplied with that stage's record. This definition does not replace the fixed target by a newly diffusing phase at every stage.

**Theorem 15.2 (recoverable phase in the accessible limit).** Under Definition 15.1,

$$
\begin{aligned}
c_n&\uparrow\mathbb E|\mathbb E[X\mid\mathcal F_\infty]|,\\
\delta_n&\downarrow1-r\mathbb E|\mathbb E[X\mid\mathcal F_\infty]|,\\
\lim_nc_n=1&\quad\Longleftrightarrow\quad
X\text{ is }\mathcal F_\infty\text{-measurable up to null sets}.
\end{aligned}
\tag{P.68}
$$

For $r>0$, the last condition is equivalent to $\delta_n\to1-r$; for $r=0$ all recovery errors are one regardless of the record.

Proof. Use the standard upward convergence theorem for conditional expectations as an intermediate, with the following $L^2$ argument fixing its hypotheses. The tower property and conditional Jensen inequality give

$$
|Z_n|\leq\mathbb E[|Z_{n+1}|\mid\mathcal F_n],
\qquad c_n\leq c_{n+1}.
$$

Conditional expectation is an orthogonal projection in $L^2$. For $j>i$,
$\|Z_j-Z_i\|_2^2=\|Z_j\|_2^2-\|Z_i\|_2^2$, while $\|Z_n\|_2\leq1$.
Hence $Z_n$ has an $L^2$ limit $Z$. A subsequence converges almost surely, making $Z$ measurable in $\mathcal F_\infty$. For any event in any $\mathcal F_i$, the defining conditional-integral identity passes to the limit. The union of the increasing sigma-algebras is an algebra generating $\mathcal F_\infty$; the monotone-class argument extends that identity to every event in $\mathcal F_\infty$. Therefore $Z=\mathbb E[X\mid\mathcal F_\infty]$.

The inequality $||Z_n|-|Z||\leq|Z_n-Z|$ gives convergence of the expected moduli. If its limit is one, $|Z|\leq1$ implies $|Z|=1$ almost surely. Orthogonal projection then gives

$$
\mathbb E|X-Z|^2=1-\mathbb E|Z|^2=0.
$$

Thus $X=Z$ almost surely. The converse follows by conditional expectation and the convergence already proved. Substituting (P.67) proves all recovery statements. No recovery operation with a physically installed infinite register is required for these finite-stage limits. $\square$

**Proposition 15.3 (record refinement need not improve each realized posterior).** There is a refinement of the accessible record for which half the posterior phase magnitudes decrease while $c_n$ does not change. Consequently neither record length nor an individual realized posterior magnitude is a strictly increasing recovery value.

Proof. Take $X\in\{1,-1\}$ with probabilities $3/4,1/4$, initially no record. Define the joint law

$$
\Pr(X=1,Y=0)=\tfrac14,\quad
\Pr(X=-1,Y=0)=\tfrac14,\quad
\Pr(X=1,Y=1)=\tfrac12.
$$

The initial modulus is $1/2$. Both labels have probability $1/2$, and their conditional means are respectively $0,1$. Thus one branch decreases to zero, but the expected modulus remains $1/2$, and the recovery error remains $1-r/2$. Adding any independent record also leaves $c_n$ unchanged. $\square$

## 追加锚（本行以下为增补区）

## 16. Readable phase length and recovery on the same AURIC orbit

**Definition 16.1 (the fixed recovered probe).** Use precisely the feasible orbit of Definition 11.1, including $0<\beta\leq1/2$ and its ellipsoidal radius bound. Prepare the logical probe $|+_{02}\rangle=(|0\rangle+|2\rangle)/\sqrt2$ and use the single phase-independent recovery $R_{\overline d}$ of Theorem 8.1. On the ordered support $(|0\rangle,|2\rangle)$ its output is

$$
\rho_{r,\varphi}
=R_{\overline d}N(w_\varphi)(|+_{02}\rangle\langle+_{02}|)
=\frac12\begin{pmatrix}1&re^{i\varphi}\\re^{-i\varphi}&1\end{pmatrix}.
\tag{P.69}
$$

For a differentiable state curve and a POVM $(E_y)$ define $p_y=\operatorname{tr}(\rho E_y)$ and $F_E=\sum_{y:p_y>0}(\partial_\varphi p_y)^2/p_y$. The local quantum Fisher information is the supremum over POVMs at the parameter value in question. This is the statistical distinguishability of this specified probe output, not an optimization over the original five-dimensional channel, inputs or ancillas. Arbitrary POVMs and the supplied probe/recovery are mathematical access assumptions; Assumption 1.2 does not install them as native operations.

**Theorem 16.2 (AURIC probe sensitivity and the distinct recovery deficit).** For the same orbit and output (P.69),

$$
F_Q(\rho_{r,\varphi})=r^2,\qquad
d\ell^2=\tfrac14F_Q\,d\varphi^2,\qquad
d\ell=\tfrac r2|d\varphi|,\qquad
\delta(N(w_\varphi))=1-r.
\tag{P.70}
$$

The statistical line element is invariant under differentiable reparameterization. At $r=0$ the recovery deficit is one while every phase outcome distribution from this probe is constant. Thus recovery deficit does not supply a strictly advancing phase clock.

Proof. Theorem 8.1 gives $R_{\overline d}N(w_\varphi)=\Psi_{re^{i\varphi}}$, proving (P.69); Theorem 8.2 gives the last equality of (P.70). For the remaining step use the symmetric logarithmic derivative characterization of quantum Fisher information as an attributed intermediate: S. L. Braunstein and C. M. Caves, [*Statistical distance and the geometry of quantum states*, DOI:10.1103/PhysRevLett.72.3439](https://doi.org/10.1103/PhysRevLett.72.3439). In the usual Pauli convention put

$$
\rho=\tfrac12(I+r\cos\varphi\,\sigma_x-r\sin\varphi\,\sigma_y),\qquad
L=r(-\sin\varphi\,\sigma_x-\cos\varphi\,\sigma_y).
$$

The Pauli anticommutation identities give $\partial_\varphi\rho=(\rho L+L\rho)/2$ and $L^2=r^2I$. For completeness, Hilbert--Schmidt Cauchy--Schwarz applied to $E_y^{1/2}\rho^{1/2}$ and $E_y^{1/2}L\rho^{1/2}$ gives

$$
(\partial_\varphi p_y)^2
\leq p_y\operatorname{tr}(\rho L E_y L),\qquad
F_E\leq\operatorname{tr}(\rho L^2)=r^2.
$$

The two spectral projections of $L$ attain equality when $r>0$: both probabilities are $1/2$ at the calibrated phase and their derivatives are $\pm r/2$. When $r=0$ the state is $I/2$ and the supremum is zero. This is also the standard equatorial-qubit specialization of W. Zhong et al., [*Fisher information under decoherence in Bloch representation*, Eq. (11), DOI:10.1103/PhysRevA.87.022337](https://arxiv.org/abs/1212.0917); the qubit Fisher formula is not a new general result here.

If $\varphi=f(s)$, the chain rule gives $F_s=(f'(s))^2F_\varphi$, so $F_s ds^2/4=F_\varphi d\varphi^2/4$. The line element therefore needs no external parameter name. It still needs an actual clock correspondence to define a rate or a unit of physical time. Finally $\rho_{0,\varphi}=I/2$ proves the stated obstruction. $\square$

**Definition 16.3 (phase, winding and calibration).** The map $z(\varphi)=e^{i\varphi}$ satisfies $\partial_\varphi z=iz$, while an internal clock correspondence $\varphi=f(\tau)$ gives $\partial_\tau z=if'(\tau)z$ and $d\ell/d\tau=r|f'(\tau)|/2$ when the length derivative is taken along increasing $\tau$. Neither the Euler identity nor (P.70) determines $f$. A circle value identifies $\varphi$ only modulo $2\pi$; an unwrapped coordinate additionally requires a retained winding label and a chosen reference. The curve $(\cos\varphi,\sin\varphi,a\varphi)$ is such an augmented coordinate representation, not a deduction of an extra spatial dimension. No native calibration, winding register or physical time unit is supplied by these identities. The optimal local measurement in Theorem 16.2 can depend on the calibrated phase; a globally implementable estimation protocol requires its own readout and record contract.

## 17. One persistent record model for recovery loss and phase sensitivity

**Definition 17.1 (branch records on the physical output blocks).** On the five-dimensional output set

$$
\Pi=V_0V_0^\dagger+V_1V_1^\dagger,\qquad
\Omega=HH^\dagger=|e_4\rangle\langle e_4|,\qquad \Pi+\Omega=I_5.
$$

At position $j$ supply a fresh record carrier with unit vectors $|e_{P,j}\rangle,|e_{Q,j}\rangle$. They are independent tensor factors, initially independent of the input. Record the fixed block distinction using the isometry

$$
F_jx=\Pi x\otimes|e_{P,j}\rangle+\Omega x\otimes|e_{Q,j}\rangle.
$$

During record construction, previously written factors are retained and are not recoupled, overwritten or reversed. The terminal recovery's access to them is specified separately. Put

$$
g_j=\langle e_{Q,j}|e_{P,j}\rangle,\quad c_j=|g_j|,\quad
G_n=\prod_{j=1}^n g_j,\quad C_n=|G_n|,\quad G_0=C_0=1.
\tag{P.71}
$$

Writing $F^{(n)}x=\Pi x\otimes E_P^{(n)}+\Omega x\otimes E_Q^{(n)}$ with $E_b^{(n)}=\bigotimes_{j=1}^n e_{b,j}$ describes one and the same finite joint realization. Erasing records means taking their partial trace; full quantum access means retaining the whole isometric output. These are different allowed-operation contracts, and neither is identified with the classical unknown-phase flags in Definition 14.1.

**Theorem 17.2 (same-record recovery and readable-length law).** For Definition 17.1 applied after $N(w_\varphi)$, erasing the records gives exactly $N(G_nw_\varphi)$. Its optimal whole-five-output recovery error and the Fisher information of the fixed probe/recovery of Definition 16.1 obey

$$
\delta_n^{\rm erase}=1-rC_n,\qquad
F_{Q,n}^{\rm probe}=r^2C_n^2,\qquad
d\ell_n=\tfrac{rC_n}{2}|d\varphi|.
\tag{P.72}
$$

For $c_j>0$ define $\Theta_n=-\log C_n$. Then

$$
\Theta_n=\sum_{j=1}^n-\log c_j,\qquad
C_n\longrightarrow0\ \Longleftrightarrow\
\sum_{j=1}^\infty-\log c_j=+\infty.
\tag{P.73}
$$

In contrast, full quantum access to the records permits error $1-r$, and no smaller error. The joint recovered probe, before its records are discarded, has Fisher information $r^2$ for every finite $n$, including $C_n=0$. Hence a decrease in (P.72) is a restriction of access in this model, rather than destruction of the joint phase dependence.

Proof. The orthogonality $\Pi\Omega=0$ makes $F^{(n)}$ an isometry, regardless of record overlap. The partial trace fixes diagonal blocks and multiplies $\Pi X\Omega$ by $\langle E_Q^{(n)}|E_P^{(n)}\rangle=G_n$. Equation (P.25) then gives $N(G_nw_\varphi)$. This vector is feasible since $|G_n|\leq1$. Theorem 8.2 gives its recovery error; (P.69) gives the probe off-diagonal entry $rG_ne^{i\varphi}/2$. A fixed phase shift $\arg G_n$ leaves Fisher information unchanged, so Theorem 16.2 proves (P.72), also at $G_n=0$.

Full quantum access permits a CPTP left inverse of $\operatorname{Ad}_{F^{(n)}}$. Explicitly, with $F=F^{(n)}$, choose any fixed density matrix $\eta$ on the five-dimensional output and use

$$
\mathcal L(X)=F^\dagger XF+
\operatorname{tr}[(I-FF^\dagger)X]\eta.
$$

Thus $\mathcal L\operatorname{Ad}_F=\mathrm{id}$ and the original recovery is achievable. Conversely any recovery of $\operatorname{Ad}_F N(w_\varphi)$ composes with $\operatorname{Ad}_F$ to give a recovery of $N(w_\varphi)$, so its error cannot be smaller than $1-r$.

Apply $R_{\overline d}$ to the five-dimensional part of the joint probe. The result is

$$
\begin{aligned}
\widetilde\rho_{n,\varphi}
&=\tfrac12\bigl(|u_n\rangle\langle u_n|+|v_n\rangle\langle v_n|
+re^{i\varphi}|u_n\rangle\langle v_n|
+re^{-i\varphi}|v_n\rangle\langle u_n|\bigr),\\
u_n&=|0\rangle E_P^{(n)},\qquad v_n=|2\rangle E_Q^{(n)}.
\end{aligned}
\tag{P.74}
$$

The vectors $u_n,v_n$ are orthonormal even if the record vectors overlap. Equation (P.74) is a parameter-independent isometric embedding of (P.69). Every POVM on its image pulls back to a qubit POVM, and every qubit POVM extends to the joint space, so its Fisher supremum is exactly $r^2$. This assertion concerns the recovered joint probe; it does not assert a value for the optimal Fisher information of the original five-output channel.

The tensor-product inner product proves (P.71), and taking negative logarithms proves (P.73). If a factor vanishes, all later $C_n$ vanish and the extended strength is $+\infty$ from that stage onward; this denotes perfect binary record distinction, not infinite elapsed time. $\square$

**Proposition 17.3 (strict differences with finite cumulative loss).** The same feasible orbit admits a fresh-record sequence with $c_j<1$ at every stage and $C_n\to e^{-1}>0$. For $r>0$, its erased-record recovery error tends to $1-re^{-1}$ and its fixed-probe Fisher information tends to $r^2e^{-2}>0$. Thus a new nonzero record distinction at every stage does not force unlimited strength or complete phase loss.

Proof. Take a two-dimensional carrier at every position, $e_{P,j}=|0\rangle$ and $e_{Q,j}=c_j|0\rangle+\sqrt{1-c_j^2}|1\rangle$, with $c_j=e^{-2^{-j}}$. Then $\Theta_n=\sum_{j=1}^n2^{-j}=1-2^{-n}$, and Theorem 17.2 gives the limits. Conversely a uniform bound $-\log c_j\geq\eta>0$ implies $\Theta_n\geq n\eta$. These are respectively summable and nonsummable strengths, not assertions about physical rates. $\square$

**Definition 17.4 (record scope and mathematical attribution).** Tensor-product dephasing and quantum Fisher information under decoherence are standard intermediates, as in Zhong et al. cited in Theorem 16.2. The constant-overlap record model is already [the history-record volume, Definition 119.1 and Theorem 119.2](AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md#119-持续追加可区分记录的强度与熵). The present application uses the actual AURIC output projectors and the same record isometry to obtain the joint recovery, erased recovery and fixed-probe length formulas (P.72)--(P.74); it makes no priority claim for the product/logarithm criterion or isometric reversibility. $\Theta_n$ measures one binary distinction. Its divergence neither counts indefinitely many perfectly readable histories nor implies that Shannon information about a fixed binary label is unbounded. Fresh tensor storage, preservation and native synthesis are additional premises. Classical readout of only part of the records need not implement the full-quantum left inverse used above.

## 追加锚（本行以下为增补区）
