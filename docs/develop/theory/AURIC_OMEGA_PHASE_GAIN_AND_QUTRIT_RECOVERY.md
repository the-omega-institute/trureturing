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
