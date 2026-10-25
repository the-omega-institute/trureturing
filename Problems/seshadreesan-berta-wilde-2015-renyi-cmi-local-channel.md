---
slug: seshadreesan-berta-wilde-2015-renyi-cmi-local-channel
bibkey: seshadreesan2015renyi
doi: 10.1088/1751-8113/48/39/395303
url: https://arxiv.org/abs/1410.1443v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.result
---

# Local-channel monotonicity of Rényi conditional quantum mutual information

## Problem

K. P. Seshadreesan, M. Berta, M. M. Wilde, *Rényi squashed entanglement, discord,
and relative entropy differences*, §3, Conjecture 1:

> Conjecture 1 The Rényi conditional quantum mutual information obeys monotonicity with respect to CPTP maps on system A, i.e., for ρABE ∈ S(HABE) and α ∈ (0, 1) ∪ (1, 2], Iα(A; B|E)ρ ≥ Iα(A′; B|E)τ, where τA′BE ≡ MA→A′(ρABE) and MA→A′ is a CPTP map acting on system A alone.

Equation (3.18) and the source's hypothesis statements appear in
[the literature note](../Library/QuantumChannels/seshadreesan2015renyi.md).
Issue [#16068](https://github.com/the-omega-institute/trureturing/issues/16068)
preregisters the witness.

## Motivation

The paper uses local-channel monotonicity to obtain LOCC monotonicity for its
Rényi squashed entanglement. Conditional correlation measures must distinguish
monotonicity on the two unconditioned systems when their defining formula is asymmetric.

## Gap

Equation (3.18) has established monotonicity on $B$. The conjecture requires
monotonicity on $A$ for the same expression and parameter range.

## Route

Write $M(p,q,s;u,v)$ for the real Hermitian matrix on $AE$ with rows
$[p,0,0,q]$, $[0,u,0,0]$, $[0,0,v,0]$, $[q,0,0,s]$ in the order $00,01,10,11$.
The state has classical $B$ and blocks
$X_0=M(13,8,7;13,39)/144$, $X_1=M(7,8,13;39,13)/144$.
Both blocks are positive definite: the coupled corner has positive trace and
positive determinant $27/144^2$, and the other entries are positive.
The trace is one. Dephasing $A$ uses $K_0=\operatorname{diag}(1,0)$ and
$K_1=\operatorname{diag}(0,1)$.

The input marginal is $S=M(5,4,5;13,13)/36=H^2$,
$H=M(2,1,2;\sqrt{13},\sqrt{13})/6$ and
$H^{-1}=M(4,-2,4;6/\sqrt{13},6/\sqrt{13})$.
The $E$ marginal is $1/2$ times the identity. At $\alpha=2$, the matrix under
the final square root is $\operatorname{diag}(9,1,1,9)/64$, with square-root
trace one. After dephasing it is $\operatorname{diag}(377,57,57,377)/2880$.
The square-root trace exceeds one; equivalently the output is
$\log((217+\sqrt{21489})/360)>0$, while the input is zero.

## Falsifier

A failure of positivity, normalization, Kraus completeness, the partial traces,
or either CFC power identity would invalidate this witness. A different
Rényi CMI definition requires a separate settlement.

## Evidence

The Lean module defines equation (3.18), its finite-dimensional claim and the
explicit witness, and proves `result : ¬ claim`. It verifies positive semidefiniteness,
trace one, Kraus completeness, the channel output, the marginals and the CFC power
identities. The input value is zero and the output value is strictly positive.
The latter proof bounds the square-root trace
$2\sqrt{377/2880}+2\sqrt{57/2880}>1$; elementary square-root and logarithm
identities give the equivalent expression $\log((217+\sqrt{21489})/360)$.
The axiom closure is exactly `propext`, `Classical.choice` and `Quot.sound`;
there is no `sorry` or `native_decide`.

## Triage

Tier 1: a named conjecture, preregistered in #16068. Admission basis:
`open-problem-resolution`; resolution: `Refuted`; `result` has
`proof_shape: bind-only` under normalization, with external open-problem admission.

### What the refutation shows

- **Proved (Lean):** the three-qubit state with classical $B$ refutes Conjecture 1
  under complete dephasing of $A$ at $\alpha=2$,
  $0\to\log((217+\sqrt{21489})/360)>0$. The explicit block factorizations
  also show that the state is faithful; strict positivity of the input state and
  the closed-form logarithm equality are algebraic consequences, while Lean
  certifies the positive semidefinite state and the strict increase.
- **Reasoning:** for positive definite $S_{AE}$ and a POVM $\{E_b\}$ on $E$,
  blocks $X_b=\sqrt S E_b\sqrt S$ give $I_2=0$. Here
  $E_0=\operatorname{diag}(3/4,1/4)$ and
  $E_1=\operatorname{diag}(1/4,3/4)$. An $A$-channel does not preserve this
  square-root factorization. The input has positive von Neumann CMI and is
  not a quantum Markov chain; the failure is specific to the Rényi formula.
- **Computed:** a rank-four variant with projective $E_b$ gives
  $0\to\log(10/9)$; numerical violations also occur at $\alpha=1.5$.
- **Reasoning:** the optimised sandwiched quantity of arXiv:1403.6102,
  Definition 19 and Remark 25, fails at $\alpha=1/2$ for this state,
  $0\to\log(648/(388+13(\sqrt{195}+\sqrt{35})))$.
  This quantity is not proved here.
- **Consequences (reasoning):** results that assume Conjecture 1, including
  LOCC monotonicity of this Rényi squashed entanglement and Consequences 3–4,
  lose that hypothesis. The $B$-side monotonicity proved in arXiv:1403.6102
  is unaffected.
- **Open:** whether a modified Rényi CMI, such as the log-Euclidean quantities
  of Rubboli–Arqand–Wilde, arXiv:2609.34699, is the right replacement lies
  outside this settlement.

### Readable partial result for the original low-alpha quantity

The deductions below concern the original quantity in
[Seshadreesan–Berta–Wilde, arXiv:1410.1443v3, equation (3.18)](https://arxiv.org/abs/1410.1443v3),
for $0<\alpha<1$. They are readable mathematical reasoning, separate from
the Lean-certified $\alpha=2$ refutation above. The unrestricted low-alpha
$A$-side conjecture remains open here. The proof reuses the published
Carlen–Zhang inequality stated below; the commutation criterion, its family
of applications, and the two stronger-route obstructions are explanatory
deductions, with no claim of novelty or priority.

#### Exact optimisation and support conventions

All spaces are finite dimensional. Fix $0<\alpha<1$, put $s=1-\alpha$, and
let $\rho=\rho_{ABE}$ be a density operator. Write $R=\rho_{AE}$,
$e=\rho_E$, and $\widehat R=R\otimes I_B$, with tensor factors placed in
$ABE$ order. Operators on $BE$ are extended by the identity on $A$ when
they occur in a full trace. Define

$$
C_\alpha(\rho)=e^{-s/2}\operatorname{Tr}_A
 \bigl[\widehat R^{s/2}\rho^\alpha\widehat R^{s/2}\bigr]e^{-s/2},
\qquad
Z_\alpha(\rho)=\operatorname{Tr}C_\alpha(\rho)^{1/\alpha},
\qquad
q_\rho(\sigma)=\operatorname{Tr}[C_\alpha(\rho)\sigma^s].
$$

Negative powers use the inverse on the support and zero on the kernel.
One can first compress $E$ to $\operatorname{supp}e$: positivity implies
that $\rho$ and $R$ are already supported there, and an $A$-channel
preserves $e$. On this compression the congruence by $e^{-s/2}$ is
invertible. Also
$\operatorname{supp}\rho\subseteq\operatorname{supp}\widehat R$, so
$\operatorname{Tr}[\rho^\alpha\widehat R^s]>0$. This is the trace of the
positive operator inside the partial trace defining $C_\alpha$.
Consequently $C_\alpha(\rho)\ne0$ and $Z_\alpha(\rho)>0$. These statements
also apply to the channel output. No inverse of $R$ or full-rank
assumption on $\rho$ is needed.

Schatten Hölder, with conjugate exponents $1/\alpha$ and $1/s$, gives,
for every density operator $\sigma$ on $BE$,

$$
q_\rho(\sigma)\le
 \bigl(\operatorname{Tr}C_\alpha(\rho)^{1/\alpha}\bigr)^\alpha
 \bigl(\operatorname{Tr}\sigma\bigr)^s=Z_\alpha(\rho)^\alpha.
$$

The closed state space contains the maximiser
$\sigma_\alpha=C_\alpha(\rho)^{1/\alpha}/Z_\alpha(\rho)$, and substitution
gives equality. Thus equation (3.18) is exactly

$$
F_\alpha(\rho):=\max_{\sigma\ge0,\ \operatorname{Tr}\sigma=1}
 q_\rho(\sigma)=Z_\alpha(\rho)^\alpha,
\qquad
I_\alpha(A;B\mid E)_\rho=-\frac1s\log F_\alpha(\rho).
$$

In particular, for $\mathcal N=\Phi_A\otimes\operatorname{id}_{BE}$ and
$\rho'=\mathcal N(\rho)$, the desired inequality is
$F_\alpha(\rho')\ge F_\alpha(\rho)$. The negative coefficient of the
logarithm is essential.

The maximiser just used belongs to the closed state space. This does not
assert its feasibility for the support-restricted optimisation in
[Berta–Seshadreesan–Wilde, arXiv:1403.6102v6, Definition 7](https://arxiv.org/abs/1403.6102v6).
With the conditioning system there renamed $E$, that definition requires
$\operatorname{supp}\rho_{ABE}\subseteq
\operatorname{supp}(I_A\otimes\sigma_{BE})$, equivalently
$\operatorname{supp}\rho_{BE}\subseteq\operatorname{supp}\sigma_{BE}$.
The explicit optimiser following Proposition 8 and in Appendix A,
Corollary 37, needs
this qualification for singular inputs. For any $0<\delta<1$,

$$
\sigma_\delta=(1-\delta)\sigma_\alpha+\delta I_{BE}/d_{BE}
$$

is full rank on the compressed space and is admissible.
Continuity of the positive power $\sigma\mapsto\sigma^s$ gives
$q_\rho(\sigma_\delta)\to F_\alpha(\rho)>0$ as $\delta\downarrow0$.
Hence the support-restricted expression has the same value as an
**infimum**, through these approximants; unconditional attained
minimisation is not needed. The exact example below shows why the
distinction matters.

#### An input commutation criterion for every finite A-channel

For the chosen $\alpha$, form the $BE$ operator

$$
W_\alpha=e^{-s/2}\sigma_\alpha^s e^{-s/2}.
$$

If
$[\widehat R,I_A\otimes W_\alpha]=0$, then

$$
I_\alpha(A';B\mid E)_{(\Phi_A\otimes\operatorname{id}_{BE})(\rho)}
 \le I_\alpha(A;B\mid E)_\rho
$$

for **every** CPTP map $\Phi_A$ with arbitrary finite input and output
dimensions and a finite Kraus representation. The condition is on the
input Hölder maximiser alone; it makes no assumption about an output
maximiser. It permits singular $\rho$ and $R$.

Here is the published theorem used in the proof.
[Carlen–Zhang, arXiv:2205.02342v4, Theorem 1.4](https://arxiv.org/abs/2205.02342v4)
states the monotonicity form of Lieb concavity: for a Schwarz map
$\Psi:M_m\to M_n$, its trace adjoint $\Psi^\dagger$, positive semidefinite
$X,Y\in M_n$, $K'\in M_m$, and $0\le t\le1$,

$$
\operatorname{Tr}\bigl[\Psi(K')^*X^t\Psi(K')Y^{1-t}\bigr]
\le
\operatorname{Tr}\bigl[(K')^*\Psi^\dagger(X)^t
 K'\Psi^\dagger(Y)^{1-t}\bigr].
$$

To apply it, set $K=W_\alpha^{1/2}$. Cyclicity and the assumed
commutation give

$$
q_\rho(\sigma_\alpha)
=\operatorname{Tr}\bigl[\rho^\alpha
 \widehat R^{s/2}(I_A\otimes W_\alpha)\widehat R^{s/2}\bigr]
=\operatorname{Tr}\bigl[(I_A\otimes K)\rho^\alpha
 (I_A\otimes K)\widehat R^s\bigr].
$$

Write $R'=(\Phi_A\otimes\operatorname{id}_E)(R)$ and
$\widehat R'=R'\otimes I_B$. Every Kraus operator acts on $A$ alone,
so left and right multiplication by a $BE$ operator pass through
$\mathcal N$. Therefore

$$
[\widehat R',I_{A'}\otimes W_\alpha]
=\mathcal N([\widehat R,I_A\otimes W_\alpha])=0.
$$

Moreover $\mathcal N^*$ is unital completely positive, hence Schwarz,
and $\mathcal N^*(I_{A'}\otimes K)=I_A\otimes K$. In Theorem 1.4 take
$\Psi=\mathcal N^*$, $X=\rho$, $Y=\widehat R$,
$K'=I_{A'}\otimes K$, and $t=\alpha$. Since $\Psi^\dagger=\mathcal N$,
the theorem gives

$$
q_\rho(\sigma_\alpha)
\le\operatorname{Tr}\bigl[(I_{A'}\otimes K)(\rho')^\alpha
 (I_{A'}\otimes K)(\widehat R')^s\bigr]
=q_{\rho'}(\sigma_\alpha).
$$

The last equality uses the output commutation and $e'=e$.
The positive semidefinite version of the theorem applies directly even
when either argument is singular. Finally,

$$
F_\alpha(\rho')\ge q_{\rho'}(\sigma_\alpha)
\ge q_\rho(\sigma_\alpha)=F_\alpha(\rho).
$$

Taking logarithms and multiplying by $-1/s$ proves the stated direction.
The closed-state Hölder representation justifies this comparison even
if $\sigma_\alpha$ is infeasible for Definition 7 at either state; the
support-restricted values are recovered by the approximants above.

#### A singular, nonclassical family on a 16-dimensional space

Let $A=A_1\otimes A_2$, with $A_1,A_2,B,E$ all qubits. Let $P_1,P_2$
be normalised Bell-state projectors on $A_1B,A_2E$, respectively, and
$Q_j=I-P_j$. For the whole interval $1/2<p<1$, consider

$$
\rho_p=pP_1\otimes P_2+
 (1-p)(Q_1/3)\otimes(Q_2/3).
$$

The two occupied sectors are orthogonal, have ranks one and nine, and
have total weights $p$ and $1-p$. Thus $\rho_p$ is a density operator
of rank ten on the 16-dimensional space, and is singular. Its marginals
are

$$
e=I_E/2,\qquad
R=(I_{A_1}/2)\otimes T,\qquad
T=pP_2+(1-p)Q_2/3.
$$

Spectral multiplication on the $P/Q$ sectors, using $\alpha+s=1$,
gives

$$
\widehat R^{s/2}\rho_p^\alpha\widehat R^{s/2}
=2^{-s}\bigl[pP_1\otimes P_2+
 (1-p)3^{-(1+\alpha)}Q_1\otimes Q_2\bigr].
$$

Since $\operatorname{Tr}_{A_1}P_1=I_B/2$,
$\operatorname{Tr}_{A_1}Q_1=3I_B/2$, and the analogous identities hold
for $P_2,Q_2$, its $A$-trace is
$2^{-s}[p+(1-p)3^s]I_{BE}/4$. The two $e^{-s/2}$ factors cancel
$2^{-s}$, so

$$
C_\alpha(\rho_p)=[p+(1-p)3^s]I_{BE}/4,\qquad
\sigma_\alpha=I_{BE}/4,\qquad W_\alpha=2^{-s}I_{BE}.
$$

The commutation criterion therefore proves the original SBW inequality
for every $1/2<p<1$, every $0<\alpha<1$, and every finite-dimensional
$A$-channel, including channels that couple $A_1$ and $A_2$ and change
the output dimension. The input value is

$$
I_\alpha(A;B\mid E)_{\rho_p}
=\log4-\frac1s\log[p+(1-p)3^s]>0.
$$

Indeed, concavity of $x^s$ gives
$p+(1-p)3^s\le(3-2p)^s<4^s$. This family is outside the classical-$E$
and product-$AE$ subclasses: the partial transpose of $T$ has eigenvalue
$(1-2p)/2<0$, equal to $-1/4$ at $p=3/4$. Thus $R$ is entangled across
$A|E$, which also excludes a classical $E$. The missing
$P_1\otimes Q_2$ and $Q_1\otimes P_2$ sectors, while both occupied
sectors have positive weight, exclude factorisation across
$(A_1B)|(A_2E)$.

#### Two exact obstructions to stronger proof routes

The established $B$-processing argument keeps the sandwich fixed:
$q_\rho(\sigma)=\operatorname{Tr}[\rho^\alpha L\sigma^sL^*]$ with
$L=\widehat R^{s/2}(I_A\otimes e^{-s/2})$.
This is the Lieb form used in arXiv:1403.6102v6, Lemma 13.
Under $A$-processing, $R$ changes, so $L$ changes. Remark 17 in that
paper uses commutation for classical conditioning; it does not remove
this dependence for arbitrary states. In fact, the stronger proposed
bridges
$C_\alpha(\mathcal N\rho)\ge C_\alpha(\rho)$ and
$q_{\mathcal N\rho}(\sigma)\ge q_\rho(\sigma)$ for every auxiliary
$\sigma$ both fail for the exact original formula.

For a common exact witness let $A,B,E$ be qubits,
$P_0=|0\rangle\langle0|$, $P_+=|+\rangle\langle+|$, and

$$
\rho=\tfrac12\bigl(|00\rangle\langle00|_{AB}\otimes P_0+
 |11\rangle\langle11|_{AB}\otimes P_+\bigr).
$$

Discard $A$, using Kraus operators $\langle0|,\langle1|$ and a
one-dimensional output. Then

$$
e=(P_0+P_+)/2=\tfrac14
\begin{pmatrix}3&1\\1&1\end{pmatrix},
\qquad \lambda_\pm=(2\pm\sqrt2)/4.
$$

At $\alpha=1/2$, keep the actual quarter powers. In $B$ block $b$,
put $v_0=|0\rangle$ and $v_1=|+\rangle$. The input marginal has block
$|b\rangle\langle b|_A\otimes|v_b\rangle\langle v_b|/2$, so direct
multiplication in the defining expression gives

$$
C_{\mathrm{in},b}=\tfrac12e^{-1/4}|v_b\rangle\langle v_b|e^{-1/4},
\qquad
C_{\mathrm{out},b}=\tfrac1{\sqrt2}|v_b\rangle\langle v_b|.
$$

For the output, this also follows from
$C_{\mathrm{out}}=\rho_{BE}^{1/2}$ because $A'$ is trivial.
Consequently

$$
\langle0_B1_E|(C_{\mathrm{out}}-C_{\mathrm{in}})|0_B1_E\rangle
=-\tfrac12|\langle1|e^{-1/4}|0\rangle|^2<0,
$$

which disproves the operator-order bridge.

The pointwise auxiliary-state bridge fails even for an admissible
full-rank state. In $BE$ basis $00,01,10,11$, choose
$\varepsilon=2^{-20}$ and
$\sigma=\operatorname{diag}(\varepsilon,1-3\varepsilon,
\varepsilon,\varepsilon)$. The displayed output blocks give
$q_{\mathrm{out}}(\sigma)=\sqrt{2\varepsilon}<1/512$.
Set $d=\lambda_-^{-1/4}-\lambda_+^{-1/4}$. The exact bounds
$\lambda_-<1/5$ and $\lambda_+>4/5$ imply
$d>7/5-9/8=11/40$; these rational comparisons follow by fourth powers.
The absolute off-diagonal entry of $e^{-1/4}$ is $d/(2\sqrt2)$.
Keeping only the positive contribution at coordinate $01$ yields

$$
q_{\mathrm{in}}(\sigma)\ge
\sqrt{1-3\varepsilon}\,\frac{d^2}{16}
>\frac{121}{51200}>\frac1{512}>q_{\mathrm{out}}(\sigma),
$$

where $\sqrt{1-3\varepsilon}>1/2$. All comparisons are exact.

**The optimised original SBW inequality holds for this same witness.**
To see this directly, the spectral weight of either $v_b$ on the
$\lambda_\pm$ eigenspace is $\lambda_\pm$. Thus
$\langle v_b|e^{-1/2}|v_b\rangle=\sqrt{\lambda_+}+\sqrt{\lambda_-}$,
and, since $1/\alpha=2$,

$$
Z_{\mathrm{in}}=\tfrac12
 (\sqrt{\lambda_+}+\sqrt{\lambda_-})^2
=\frac{2+\sqrt2}{4}<1=Z_{\mathrm{out}}.
$$

As $I_{1/2}=-\log Z$, the output value is zero and is smaller than the
input value. Both counterexamples obstruct stronger proof routes;
neither refutes the optimised low-alpha conjecture.

This witness also makes the support qualification concrete throughout
$0<\alpha<1$. The same multiplication gives
$C_{\mathrm{in},b}=\tfrac12e^{-s/2}|v_b\rangle\langle v_b|e^{-s/2}$.
Thus in each $B$ block the input Hölder maximiser has support
$\operatorname{span}(e^{-s/2}v_b)$, whereas $\rho_{BE}$ has support
$\operatorname{span}(v_b)$. Each $v_b$ has nonzero components in both
unequal eigenspaces of $e$, so the two lines differ for every $0<s<1$.
The maximiser therefore fails Definition 7's support inclusion. The full-rank
$\sigma_\delta$ above still recover the same infimum value. This
qualifies feasible attainment; it does not invalidate equation (3.18).

#### The remaining low-alpha comparison

Outside the stated commutation class the missing step is the optimised
comparison

$$
\max_\sigma\operatorname{Tr}[C_\alpha(\mathcal N\rho)\sigma^s]
\ge\max_\sigma\operatorname{Tr}[C_\alpha(\rho)\sigma^s],
$$

with the marginal changing from $R$ to
$(\Phi_A\otimes\operatorname{id}_E)(R)$. It would suffice to prove the
pointwise inequality specifically at the input Hölder maximiser, but
that assertion is unproved here outside the commutation class.
Universal pointwise DPI and operator order cannot replace it, as the
two exact obstructions show. A fixed-coefficient concavity theorem
does not transport the marginal-dependent sandwich, and a generic
optimised-divergence DPI needs a separate comparison with an
admissible output reference. These deductions supply neither that
comparison nor an unrestricted proof or counterexample.

## ASSUMED-UNVERIFIED

Worldwide novelty and priority are not conclusions of the formal refutation.
The numerical variants and the optimised sandwiched quantity are distinct
from the theorem's CFC expression and remain outside its proof scope.
