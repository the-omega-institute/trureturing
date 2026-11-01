# Quantum origin endogenous cut atlas and discrete reconstruction boundaries II

## 57. Real forward references and two different approximation targets

**定义 57.1（Unknown angle, logical bypass and work-ready targets）。** Let $(V,g)$ be a nonzero finite-dimensional real inner-product space with a fixed orthogonal complex structure, and supply the common actual reference family

$$
J^*=-J,\quad J^2=-I,\quad J^*J=I,\qquad
Q_\theta=\cos\theta\,I+\sin\theta\,J,\qquad
\theta\in[a,b],\quad0<a<b\le\pi/2.
\tag{57.1}
$$

The angle is unknown. Circuits may depend on the known lower endpoint $a$ and desired accuracy, but not on the actual $\theta$. Real orthogonal gates on finite controllers are free. Supply forward controlled queries for known real orthogonal controller projections $P$:

$$
D_P(Q)=(I-P)\otimes I+P\otimes Q.
\tag{57.2}
$$

An unconditional query has $P=I$; all reference calls are counted. The final menu includes no other free source gate, free reference duration, source preparation or inverse reference. Actual coherent control of the particular $Q$ is supplied, not inferred from its source-only channel. A circuit is a finite orthogonal product of the supplied query factors and controller gates, without measurement, outcome selection or work discard.

Keep a real two-dimensional logical controller $B$ with a fixed orthonormal basis, a separate finite work controller $C$ with fixed unit ready vector $e_0$, and $H=B\otimes_{\mathbb R}V$. Write

$$
S=\begin{pmatrix}I&0\\0&J\end{pmatrix}.
\tag{57.3}
$$

The calibrated and phase-fixed interval contracts are distinguished in the [companion volume, §§48–56](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md). The phase-fixed target here is $e_0\otimes S$ on every input in $H$. A different target, for one fixed nonnegative integer $N$ chosen by the circuit, is

$$
e_0\otimes\bigl((I_B\otimes Q_\theta^N)S\bigr).
\tag{57.4}
$$

Its common source delay acts on both logical branches and remains present in the real linear error criterion. An auxiliary expression will permit counted controlled queries in both directions, approximate the first target, and then eliminate every inverse to obtain the second target using only (57.2).

## 58. Real Laurent approximation and coherent two-reflection amplification

**定理 58.1（Inverse-enabled approximation with an explicit finite query bound）。** Under Definition 57.1, put $\rho=\cos^2a\in(0,1)$. For every integer $r\ge0$, define

$$
\begin{gathered}
d=2r+1,\qquad \eta_r=\rho^{r+1},\qquad
\alpha=r+2,\\
m=\left\lceil\frac{\pi(r+2)}4\right\rceil,\qquad
k=2m+1,\qquad \phi_0=\frac\pi{2k},\qquad s=\sin\phi_0.
\end{gathered}
\tag{58.1}
$$

There is a real orthogonal two-direction circuit $V_\theta$, with at most

$$
q_r\le2(2r+1)
 \left(2\left\lceil\frac{\pi(r+2)}4\right\rceil+1\right)=2dk
\tag{58.2}
$$

counted forward or inverse reference calls, such that

$$
\sup_{\theta\in[a,b]}
\|V_\theta(e_0\otimes\cdot)-e_0\otimes S\|
\le2\eta_r=2\cos^{2r+2}a.
\tag{58.3}
$$

The error is a joint real operator norm on every logical/source input, including the whole work-not-ready component. Finite $r$ generally leaves a nonzero work residual: the conclusion is approximate ready return, not exact work return at every unknown angle. Tensoring an untouched finite real reference preserves the bound. The query estimate is an upper bound and makes no optimality or controller-synthesis-cost claim.

Proof. Use the standard binomial coefficients and the real Laurent polynomial

$$
\begin{aligned}
d_j&=\binom{2j}{j}4^{-j},\qquad
R_r(t)=\sum_{j=0}^r d_jt^j,\\
p_r(z)&=\frac{z-z^{-1}}2\,
R_r\!\left(\left(\frac{z+z^{-1}}2\right)^2\right).
\end{aligned}
\tag{58.4}
$$

Its Laurent degree in either direction is at most $d$. The established binomial expansion gives

$$
d_0=1,\qquad
\frac{d_{j+1}}{d_j}=\frac{2j+1}{2j+2}<1,\qquad
\sum_{j\ge0}d_jt^j=(1-t)^{-1/2}\quad(0\le t<1).
\tag{58.5}
$$

Substitution at the actual reference gives

$$
p_r(Q_\theta)=g_r(\theta)J,\qquad
g_r(\theta)=\sin\theta\,R_r(\cos^2\theta).
\tag{58.6}
$$

For $t=\cos^2\theta$, the monotonicity $d_{j+r+1}\le d_j$ gives the needed relative tail bound:

$$
\begin{aligned}
0\le1-g_r(\theta)
&=\sqrt{1-t}\sum_{j=r+1}^\infty d_jt^j\\
&\le t^{r+1}\sqrt{1-t}\sum_{j=0}^\infty d_jt^j
=t^{r+1}\le\rho^{r+1}=\eta_r.
\end{aligned}
\tag{58.7}
$$

Thus $0<g_r\le1$. Define

$$
S_r(\theta)=\operatorname{diag}(I,g_r(\theta)J)
=S\operatorname{diag}(I,g_r(\theta)I),\qquad
\|S_r(\theta)-S\|\le\eta_r.
\tag{58.8}
$$

The binomial series is an intermediate analytic tool; the tail estimate grants neither a source-normalization primitive nor an actual inverse.

Write $p_r(z)=\sum_{\ell=-d}^d a_\ell z^\ell$. The coefficient one-norm is submultiplicative, and each of $(z-z^{-1})/2$ and $(z+z^{-1})/2$ has coefficient one-norm one. Consequently

$$
\sum_\ell|a_\ell|\le\sum_{j=0}^r d_j\le r+1,
\qquad \sum_\ell a_\ell=p_r(1)=0.
\tag{58.9}
$$

With $Z_B=\operatorname{diag}(1,-1)$ and $C_\ell=\operatorname{diag}(I,Q_\theta^\ell)$ on $H$, this gives the actual algebraic linear combination

$$
S_r(\theta)=\tfrac12I_H+\tfrac12(Z_B\otimes I)
                              +\sum_\ell a_\ell C_\ell.
\tag{58.10}
$$

The first two terms supply the bypass projection, while the remaining sum vanishes there. No nonunitary branch projection is assumed free. Its total coefficient one-norm is at most $\alpha=r+2$. Since $m\ge1$ and $s\le\phi_0\le1/\alpha$, pad the combination with two cancelling identity terms to make that one-norm exactly $\alpha'=1/s$. All coefficients remain known reals independent of $\theta$.

For the padded coefficients $c_j$ and specified orthogonal oracle words $V_j(\theta)$, prepare the real unit controller vector

$$
v=\sum_j\sqrt{|c_j|/\alpha'}\,|j\rangle.
\tag{58.11}
$$

Choose a known real orthogonal $B_v$ with first column $v$. Let $\mathrm{SELECT}$ apply $\operatorname{sign}(c_j)V_j(\theta)$ on label $j$, omitting zero coefficients. The oracle words are specified by their exponents and controller flags; their unknown-angle source powers remain counted primitives. Its signs are controller signs, and its only source operations are the controlled powers $C_\ell$. The real orthogonal block encoding

$$
U_\theta=(B_v^T\otimes I)\,\mathrm{SELECT}\,(B_v\otimes I)
\tag{58.12}
$$

has ready block

$$
(\langle e_0|\otimes I)U_\theta(|e_0\rangle\otimes I)
=sS_r(\theta).
\tag{58.13}
$$

Nothing is measured. This is the established real prepare/select/unprepare algebra of A. M. Childs–N. Wiebe, [Hamiltonian Simulation Using Linear Combinations of Unitary Operations](https://arxiv.org/pdf/1202.5822v1), §II and Appendix A, especially equations (A2)–(A6), used as an intermediate method. Exact known controller rotations are supplied resources.

Schedule $\mathrm{SELECT}$ with $d$ forward and $d$ inverse calls: at step $j=1,\ldots,d$, query forward on the known labels whose positive exponent is at least $j$, and inverse on labels whose negative exponent has magnitude at least $j$, conjoining each flag with $B=1$. The other terms require only known controller gates. Thus either $U_\theta$ or $U_\theta^T$ uses at most $2d$ counted calls, with $d$ inverse slots in this displayed schedule.

Set

$$
P=|e_0\rangle\langle e_0|\otimes I_H,\qquad
R=I-2P,\qquad
G_\theta=-U_\theta R U_\theta^T R,\qquad
V_\theta=G_\theta^mU_\theta.
\tag{58.14}
$$

Both $R$ and the scalar minus sign are known real controller gates. The standard two-reflection amplification mechanism is due to G. Brassard–P. Høyer–M. Mosca–A. Tapp, [Quantum Amplitude Amplification and Estimation](https://arxiv.org/pdf/quant-ph/0005055v1), §2, pp. 5–7, equations (1)–(8). The following invariant-plane calculation gives the real version needed here using the supplied controller gates; the prepare/select/unprepare attribution above supplies that intermediate algebra rather than the complete amplified construction.

On a unit input $y$ in either logical sector, write

$$
U_\theta(e_0\otimes y)
=\sin\phi\,(e_0\otimes Sy)+\cos\phi\,b_y,
\qquad Pb_y=0,\quad\|b_y\|=1.
\tag{58.15}
$$

Here $\phi=\phi_0$ on the bypass and $\phi=\arcsin(sg_r(\theta))$ on the active sector. The polar part of (58.13) is exactly $S$ since $g_r>0$. For orthogonal inputs in these singular sectors, the vectors $b_y$ are orthogonal, by subtracting the ready components from the orthogonal images under $U_\theta$. The planes spanned by $e_0\otimes Sy$ and $b_y$ are mutually orthogonal. Each is invariant under the two reflections: the projection onto $U_\theta\operatorname{ran}P$ has, on this plane, range spanned by the vector with coordinates $(\sin\phi,\cos\phi)$.

In that ordered basis, $G_\theta$ and the amplified output are

$$
G_\theta\big|_{\mathrm{plane}}=
\begin{pmatrix}\cos(2\phi)&\sin(2\phi)\\
-\sin(2\phi)&\cos(2\phi)\end{pmatrix},\qquad
V_\theta(e_0\otimes y)
=\sin(k\phi)(e_0\otimes Sy)+\cos(k\phi)b_y.
\tag{58.16}
$$

The bypass is exact because $k\phi_0=\pi/2$. On the active sector let $\delta_\theta=k(\phi_0-\arcsin(sg_r(\theta)))\ge0$. The derivative bound for $\arcsin$ gives

$$
\delta_\theta
\le\frac{ks}{\sqrt{1-s^2}}(1-g_r(\theta))
\le\frac\pi{\sqrt3}\eta_r<2\eta_r.
\tag{58.17}
$$

Indeed $k\ge3$, $\phi_0\le\pi/6$, $ks\le k\phi_0=\pi/2$, and $\sqrt{1-s^2}=\cos\phi_0\ge\sqrt3/2$. The distance in (58.16) to its unit ready target is $2\sin(\delta_\theta/2)\le\delta_\theta$. Orthogonality of the sector planes proves the whole-input bound (58.3), including work residual. There are $k=2m+1$ factors $U_\theta$ or $U_\theta^T$, each costing at most $2d$ queries, proving (58.2). For any requested $\epsilon>0$, a finite $r$ with $2\rho^{r+1}\le\epsilon$ suffices. No conditional normalization or probability rule is used. $\square$

## 59. Eliminate every inverse and count the common forward delay

**定理 59.1（Forward-only approximate-ready relative operation）。** The displayed schedule of Theorem 58.1 yields a circuit using only the actual forward menu, with fixed integers

$$
N_r=(2r+1)(2m+1)=dk,\qquad q_r=2N_r,
\tag{59.1}
$$

such that

$$
\sup_{\theta\in[a,b]}
\left\|F_\theta(e_0\otimes\cdot)
-e_0\otimes\bigl((I_B\otimes Q_\theta^{N_r})S\bigr)\right\|
\le2\cos^{2r+2}a.
\tag{59.2}
$$

All flags, counts and controller gates are independent of the actual angle. The estimate includes every work-output component and logical/source input, and is preserved by an untouched finite real reference. It approximates ready return and includes an actual counted common source delay; it does not remove that delay from a real orientation-sensitive target.

Proof. For any known controller projection $P$, direct block multiplication gives

$$
D_{I-P}(Q_\theta)
=(I\otimes Q_\theta)D_P(Q_\theta^{-1}).
\tag{59.3}
$$

Replace every inverse controlled query of $V_\theta$ by the forward query with complementary flag. Each replacement introduces one extra $I\otimes Q_\theta$. That factor commutes with all controller gates and with every remaining query, so the factors move to the output. If $N_r$ is the number replaced, the complete joint operators satisfy exactly

$$
F_\theta=(I_{C\otimes B}\otimes Q_\theta^{N_r})V_\theta.
\tag{59.4}
$$

In the specified schedule, every $U_\theta$ and transpose has $d$ inverse slots and $d$ forward slots; hence $N_r=dk$ and $q_r=2dk$. One forward replacement costs exactly one query. Simplifications may reduce the displayed counts, but are not required and no optimality is claimed. Orthogonality of the common delay transfers (58.3) to (59.2). The final circuit requires no physical inverse-query access: the inverse-enabled expression was an intermediate identity whose every inverse has been removed. The delay is neither free nor a calibrated duration. $\square$

## 60. A fixed interval example and the additional complex observation contract

**定理 60.1（A counted delayed target below the phase-fixed interval floor）。** For $E=[\pi/6,\pi/2]$, choose $r=15$. Then $\rho=3/4$, $d=31$, $m=\lceil17\pi/4\rceil=14$, $k=29$, and the displayed forward-only circuit has

$$
N_r=899,\qquad q_r=1798,\qquad
\epsilon\le2(3/4)^{16}<2/81<1/32.
\tag{60.1}
$$

Proof. The counts are (59.1). Since $(3/4)^4=81/256<1/3$, raising to the fourth power gives $(3/4)^{16}<1/81$, and $64<81$ gives $2/81<1/32$. The real target includes $Q_\theta^{899}$ on both logical branches, so this example does not violate [Theorem 54.1 of the companion volume](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) and its $1/32$ floor for the fixed phase-fixed target. It supplies concrete counts and accuracy without an efficiency or optimality claim. $\square$

**假设 60.2（Complex rays or operator conjugation as an additional criterion）。** In addition to the real operation contract, describe $V$ as the complex space $V_J$ with $(u+iv)x=ux+vJx$ and $h(x,y)=g(x,y)+i\,g(Jx,y)$. This is the real-to-complex inner product of the [V78 common-reference construction, Corollary 4.3](https://github.com/the-omega-institute/trureturing/blob/31fa401a7c17858fa323ddd0886ed580e0c57347/docs/develop/theory/AURIC_BINARY_FAILURE_WITNESSES_AND_GLOBAL_QUANTUM_RELATIONS_V78_CONTINUATION.md#statement-4-3). Every actual controller gate and query factor commutes with the common $I_{C\otimes B}\otimes J$, so every circuit factor is complex-linear under this description. Separately stipulate either complex rays as the observations or complex operator conjugation as the channel comparison criterion. This observation contract is supplied, not derived from the real circuit menu.

**定理 60.3（The common delay is scalar only under the stated complex interpretation）。** Under Assumption 60.2,

$$
Q_\theta=e^{i\theta}I,\qquad
I_B\otimes Q_\theta^{N_r}=e^{iN_r\theta}I_H,\qquad
S=\operatorname{diag}(1,i),
\tag{60.2}
$$

and therefore the ideal delayed operation satisfies

$$
\operatorname{Ad}_{(I_B\otimes Q_\theta^{N_r})S}
=\operatorname{Ad}_S.
\tag{60.3}
$$

The approximation in (59.2) is consequently to the relative phase $S$ up to one common scalar, with work approximately ready. Equation (60.3) compares the ideal target operations. The actual finite $F_\theta$ has the joint approximation (59.2), including its work residual; no exact equality with $S$ or exact clean reduced-channel identity is asserted for that circuit.

Proof. The scalar action follows from $J=iI$ on $V_J$, and the common factor acts on both logical branches. It preserves every stipulated complex ray and cancels in conjugation, proving (60.3). With an untouched complex reference it still multiplies the entire joint vector by the same scalar. For real vectors and real observations retaining absolute orientation, the delay can be distinguishable and cannot be deleted. Nor does it become scalar for an arbitrary reference with several actual eigenangles or a quarter turn not acting as a common complex scalar. The single fixed-$J$ uniform-angle realization is essential to this interpretation. No probability law, effects, source preparation or physical tensor-independence principle is inferred. $\square$

## 61. The analytic target boundary and unresolved acquisition duties

**定理 61.1（The delayed approximation and the phase-fixed obstruction have different targets）。** Theorem 59.1 does not make the phase-fixed real target of [Theorem 54.1 of the companion volume](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) attainable, and that earlier error floor does not forbid relative complex phase control under the extra observation contract of Assumption 60.2.

Proof. The earlier real-polynomial proof uses $h=f-i$, for which real $f(0)$ forces $|h(0)|\ge1$. On the active branch of (59.2), the delayed scalar target is instead $iz^{N_r}$. For $N_r>0$, the difference $f(z)-iz^{N_r}$ has no analogous guaranteed nonzero center bound; its value at zero is merely $f(0)$ and can vanish. The circuit-selected delay changes the approximation target, so the Jensen argument is not contradicted. The source-only complex channel $\operatorname{Ad}_J$ is identity, whereas the logical bypass makes the relative operation $\operatorname{diag}(1,i)$ explicit. The forward circuit approximates that operation modulo a common scalar only after Assumption 60.2 is supplied. $\square$

**定义 61.2（Source acquisition and comparison scope）。** The construction supplies the actual controlled oracle (57.1)–(57.2) as a premise. It neither extracts it from the diagnostic gap of the [companion volume, §§43–47](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) nor grants the arbitrary reference durations of its separate echo in Theorem 45.1. The comparison-versus-menu distinctions in that volume’s Definitions 42.2 and 47.1 remain in force. Exact known real controller synthesis, a ready work controller, source acquisition and calibration, and any ray/channel or probability interpretation retain their own acquisition obligations. The binomial expansion, coherent linear combination and two-reflection amplification remain credited intermediate methods; no general-method novelty or literature priority is claimed. The displayed bounds do not settle tighter query costs, restricted native controller synthesis or multifrequency reference extraction. Word reversal has square $I$, whereas $J^2=-I$; this construction identifies neither operation with the other and supplies no retained-failure decoder.

## 追加锚（本行以下为增补区）

## 62. A whole-space spectral band and its skew polar direction

**定义 62.1（Actual spectral-band reference and forward menu）。** Let $(V,g)$ be a nonzero finite-dimensional real inner-product space and $Q$ an actual orthogonal source query. Its real adjoint is denoted by $Q^*$, and put

$$
C_Q=\frac{Q+Q^*}{2},\qquad K_Q=\frac{Q-Q^*}{2}.
\tag{62.1}
$$

Supply a known $0<a<\pi/2$ and the whole-space premise

$$
\|C_Q\|\le\cos a<1.
\tag{62.2}
$$

This is a spectral-band premise for the actual reference, separate from a joint transport diagnostic gap. It includes neither a finite-precision certificate of (62.2) nor a native procedure for acquiring such a certificate. Real orthogonal gates on finite controllers are free. For every known real orthogonal controller projection $P$, supply the actual coherent forward query

$$
D_P(Q)=(I-P)\otimes I+P\otimes Q.
\tag{62.3}
$$

All calls, including unconditional queries, are counted. A circuit is a finite orthogonal product of these factors and known controller gates, without measurement, outcome selection or work discard. The final menu supplies no inverse query, arbitrary reference duration, other free source gate or source preparation. Actual coherent control is a premise, not an inference from the source-only channel. Keep a logical real two-dimensional controller $B$ with a fixed orthonormal basis and a finite work controller $C$ with a fixed unit ready vector $e_0$; write $H=B\otimes_{\mathbb R}V$.

**定义 62.2（Comparison direction for the delivered target）。** Define the source comparison operators

$$
H_Q=(I-C_Q^2)^{1/2},\qquad J_Q=K_QH_Q^{-1}.
\tag{62.4}
$$

The spectral-band premise makes $H_Q$ positive definite; the skew polar calculation inside the circuit proof below verifies its bound and the complex-structure properties used by the target. These formulas introduce no additional callable source operation. Where used below, $V_{J_Q}$ denotes the complex coordinate description $(u+iv)x=ux+vJ_Qx$ with $h(x,y)=g(x,y)+i\,g(J_Qx,y)$, as in Assumption 60.2 with $J_Q$ in place of $J$. Observation and tensor contracts are stated separately.

## 63. One relative-quarter-turn circuit across the actual spectral band

**定理 63.1（Uniform spectral extraction with a counted common delay）。** For the actual reference of Definition 62.1, the comparison direction used by the delivered target satisfies

$$
H_Q\succeq\sin a\,I,\qquad J_Q^*=-J_Q,\qquad
J_Q^2=-I,\qquad J_Q^*J_Q=I,\qquad Q=C_Q+J_QH_Q.
\tag{63.1}
$$

The same actual $Q$ decomposes into orthogonal $J_Q$-invariant real rotation planes on which

$$
Q=\cos\theta_jI+\sin\theta_jJ_Q,\qquad
\theta_j\in[a,\pi-a].
\tag{63.2}
$$

The angles need not agree. Define

$$
\begin{gathered}
S_Q=\operatorname{diag}(I,J_Q)\quad\text{on }H,\qquad
\rho=\cos^2a,\qquad \eta_r=\rho^{r+1},\qquad d=2r+1,\\
m=\left\lceil\frac{\pi(r+2)}4\right\rceil,\qquad
k=2m+1,\qquad N_r=dk,\qquad \epsilon_r=2\eta_r
\quad(r\ge0).
\end{gathered}
\tag{63.3}
$$

One forward-only circuit template $F_Q$, whose controller matrices and flags depend on $a,r$ but not on the actual eigenangles of $Q$, satisfies

$$
\left\|F_Q(e_0\otimes\cdot)
-e_0\otimes\bigl((I_B\otimes Q^{N_r})S_Q\bigr)\right\|
\le\epsilon_r.
\tag{63.4}
$$

The displayed schedule uses $2N_r$ forward reference calls. The bound is a whole joint real operator norm, including every logical/source input and the entire work-not-ready component, and is uniform over finite carrier dimensions satisfying (62.2). Finite $r$ gives approximate work return on the active sector. On the bypass sector this displayed circuit is exactly $e_0\otimes Q^{N_r}$.

Proof. First use the ordinary finite-dimensional skew polar and spectral calculations to identify the comparator of this actual source. Since $Q^*=Q^{-1}$, the symmetric $C_Q$ and skew $K_Q$ commute, and $C_Q^2-K_Q^2=I$. The band implies $I-C_Q^2\succeq\sin^2a\,I$, so its positive square root $H_Q$ is invertible, satisfies the bound in (63.1), and commutes with $C_Q,K_Q,Q$. Consequently

$$
K_Q^2=-H_Q^2,\qquad
J_Q^*=H_Q^{-1}(-K_Q)=-J_Q,\qquad
J_Q^2=K_Q^2H_Q^{-2}=-I.
$$

It follows that $J_Q^*J_Q=I$ and $K_Q=J_QH_Q$. On a $C_Q$ eigenspace of eigenvalue $c$, $H_Q=\sqrt{1-c^2}I$ and $\theta=\arccos c\in[a,\pi-a]$. This eigenspace is $J_Q$ invariant because $[C_Q,J_Q]=0$. Choose a unit vector $x$ and its orthogonal mate $J_Qx$; their orthogonal complement is again $J_Q$ invariant. Repetition gives the rotation-plane decomposition (63.2). This is the ordinary skew polar factor of $K_Q$, used to specify the relative target, rather than a source-normalization primitive or a common-scalar assertion.

Now reuse the coefficients and Laurent polynomial of (58.4):

$$
d_j=\binom{2j}{j}4^{-j},\qquad
R_r(t)=\sum_{j=0}^rd_jt^j,\qquad
p_r(z)=\frac{z-z^{-1}}2
 R_r\!\left(\left(\frac{z+z^{-1}}2\right)^2\right).
\tag{63.5}
$$

Since $(Q+Q^{-1})/2=C_Q$ and $(Q-Q^{-1})/2=K_Q$, functional calculus on the same actual $Q$ gives

$$
p_r(Q)=J_QG_r,\qquad G_r=H_QR_r(C_Q^2),\qquad
(1-\eta_r)I\preceq G_r\preceq I.
\tag{63.6}
$$

For the order bounds, every spectral value $t$ of $C_Q^2$ lies in $[0,\rho]$. The binomial tail calculation (58.5)–(58.7) therefore gives

$$
0\le1-\sqrt{1-t}\sum_{j=0}^rd_jt^j
\le t^{r+1}\le\eta_r.
\tag{63.7}
$$

In particular $G_r$ is positive definite and commutes with $J_Q$. These are joint bounds for all spectral values of one actual operator. The argument uses one polynomial on every rotation plane at once; it does not combine separately optimized realizations.

The Laurent coefficient one-norm of $p_r$ is at most $r+1$ and $p_r(1)=0$, as proved in (58.9). Thus $\operatorname{diag}(I,p_r(Q))$ is the real linear combination (58.10), with $Q$ in place of $Q_\theta$, coefficient one-norm at most $r+2$, and specified controlled oracle words rather than known source matrices. Allow counted inverse calls temporarily. The same padded real prepare/select/unprepare construction (58.11)–(58.13), using the Childs–Wiebe algebra cited there, has ready block

$$
sS_Q\operatorname{diag}(I,G_r),\qquad
s=\sin\!\left(\frac\pi{2k}\right).
\tag{63.8}
$$

Its polar part is exactly $S_Q$. For each spectral value $g$ of $G_r$, the invariant-plane calculation (58.14)–(58.16) has initial singular value $sg$ on the active sector and $s$ on the bypass. The standard two-reflection mechanism credited in §58 gives angular deficit

$$
0\le k\bigl(\arcsin s-\arcsin(sg)\bigr)
\le\frac{ks}{\sqrt{1-s^2}}(1-g)
\le\frac\pi{\sqrt3}\eta_r<2\eta_r.
\tag{63.9}
$$

The distance to each unit ready target is at most that deficit. The singular planes are mutually orthogonal, so their maximum bounds all coherent superpositions and the entire work residual. This proves the inverse-enabled joint bound with target $e_0\otimes S_Q$. Its bypass is exact because $k\arcsin s=\pi/2$.

Finally replace each inverse factor using the exact identity

$$
D_{I-P}(Q)=(I\otimes Q)D_P(Q^{-1}).
\tag{63.10}
$$

The introduced source factors $Q$ commute with every controller gate and every remaining query factor. Each of the $k$ block-encoding or transposed block-encoding factors has $d$ inverse slots and $d$ forward slots in the schedule of §58. Moving the $N_r=dk$ added factors to the output therefore produces $F_Q$ with exactly that common delay and $2N_r$ displayed forward calls. Orthogonality preserves the joint error, proving (63.4). It also preserves exact bypass return to work-ready while delaying its source by $Q^{N_r}$. No inverse access remains in the final circuit, and the common delay is retained in its target. An untouched finite real reference preserves the operator-norm bound. $\square$

## 64. Transport compatibility and alignment with a specified direction

**定理 64.1（Compatibility and exact orientation of the acquired direction）。** If actual real orthogonal transports $U_s$ commute with $Q$, then they commute with $C_Q,K_Q,H_Q,J_Q$. Thus $J_Q$ is a common complex structure for those unchanged transports. Exact commutation is a premise here; small commutators alone are not substituted for it. If $J_0$ is a specified orthogonal complex structure with $[Q,J_0]=0$, define the source operator

$$
A_0=-J_0K_Q.
\tag{64.1}
$$

Then $A_0$ is self-adjoint and invertible, commutes with $J_0$, and

$$
K_Q=J_0A_0,\qquad H_Q=|A_0|,\qquad
J_Q=J_0A_0|A_0|^{-1}=J_0\operatorname{sign}(A_0).
\tag{64.2}
$$

In particular,

$$
J_Q=J_0\quad\Longleftrightarrow\quad A_0\succ0.
\tag{64.3}
$$

Proof. If $[U_s,Q]=0$, commutation with the invertible $Q$ implies commutation with $Q^{-1}=Q^*$, hence with $C_Q,K_Q$. Finite-dimensional spectral calculus gives commutation with $H_Q,H_Q^{-1}$, and then with $J_Q=K_QH_Q^{-1}$. This is the exact common-direction conclusion for those actual transports.

For the specified $J_0$, its commutation premise similarly gives $[K_Q,J_0]=0$. The product of the two commuting skew operators $-J_0,K_Q$ is self-adjoint, and both are invertible because $K_Q^2=-H_Q^2\prec0$. It commutes with $J_0$, and $J_0A_0=K_Q$. Moreover $A_0^2=-K_Q^2=H_Q^2$, so uniqueness of the positive square root gives $|A_0|=H_Q$. Equations (64.2) follow from the skew polar formula. Since $A_0$ is self-adjoint and invertible, $\operatorname{sign}(A_0)=I$ is equivalent to every eigenvalue being positive, proving (64.3).

For a counterexample to alignment from commutation alone, put

$$
\begin{gathered}
V=\mathbb R^2\oplus\mathbb R^2,\qquad
J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
J_0=\operatorname{diag}(J_2,J_2),\\
Q=\operatorname{diag}(e^{\theta J_2},e^{-\theta J_2}),
\qquad a\le\theta\le\pi-a.
\end{gathered}
\tag{64.4}
$$

Then $[Q,J_0]=0$ and $\|C_Q\|=|\cos\theta|\le\cos a$, but $K_Q=\operatorname{diag}(\sin\theta J_2,-\sin\theta J_2)$ and $J_Q=\operatorname{diag}(J_2,-J_2)$. Thus the band selects a direction from the actual $Q$ without forcing a prescribed global orientation. $\square$

## 65. Observable commutants give the exact delay criterion

**定理 65.1（All-input readout invariance and its quantitative implementation bound）。** Let $N\ge0$ be an integer, set $D_N=I_B\otimes Q^N$, and let $E$ be a declared real self-adjoint readout on $H$. Equality of the ideal delayed and undelayed quadratic readouts for every unit input is equivalent to

$$
\begin{aligned}
&\langle D_NS_Qx,E D_NS_Qx\rangle
 =\langle S_Qx,E S_Qx\rangle\quad(\|x\|=1)\\
&\qquad\Longleftrightarrow\quad D_N^*ED_N=E
\quad\Longleftrightarrow\quad [E,D_N]=0.
\end{aligned}
\tag{65.1}
$$

For a family $\mathcal O$ of declared readouts this is exactly $D_N\in\mathcal O'$. The same statement holds for a declared complex carrier and Hermitian readouts. If a real isometry $T:H\to C\otimes H$ satisfies

$$
\|T-e_0\otimes D_NS_Q\|\le\epsilon,
\tag{65.2}
$$

then

$$
\|T^*(I_C\otimes E)T-S_Q^*ES_Q\|
\le2\|E\|\epsilon+\|[E,D_N]\|.
\tag{65.3}
$$

Proof. The orthogonal $S_Q$ is onto, so the equality of quadratic forms for all unit $x$ determines the self-adjoint matrix $D_N^*ED_N-E$. Real polarization makes that matrix zero. Multiplying by $D_N$ gives the equivalent commutation condition. Complex Hermitian polarization proves the complex version. No probability interpretation is needed for these algebraic equivalences.

Write $A=e_0\otimes D_NS_Q$ and $\widetilde E=I_C\otimes E$. Both $A,T$ are isometries. Subtracting the two compressed readouts gives

$$
T^*\widetilde ET-A^*\widetilde EA
=(T-A)^*\widetilde ET+A^*\widetilde E(T-A),
\tag{65.4}
$$

whose norm is at most $2\|E\|\epsilon$. Also

$$
\|A^*\widetilde EA-S_Q^*ES_Q\|
=\|D_N^*ED_N-E\|=\|[E,D_N]\|.
\tag{65.5}
$$

The triangle inequality proves (65.3). In particular it applies to the ready-input isometry of (63.4) with $N=N_r$ and $\epsilon=\epsilon_r$. It bounds the actual output readout and includes work residual; it does not assert exact clean return. Calling any of these quadratic readouts a physical probability requires a separate observation contract. $\square$

**定理 65.2（Logical observations, all real observations and all complex observations）。** Logical-controller readouts commute with every $D_N$. Invariance for all real self-adjoint readouts on $H$ is equivalent to $D_N=I_H$ or $-I_H$. Under the additional $J_Q$-complex description of the carrier, invariance for all Hermitian readouts is equivalent to

$$
Q^N=e^{i\varphi}I
\quad\Longleftrightarrow\quad
N(\theta_j-\theta_\ell)\in2\pi\mathbb Z
\quad\text{for all }j,\ell.
\tag{65.6}
$$

Proof. A logical readout is $E_B\otimes I_V$, so it commutes with the source-only $D_N$. Commutation with every rank-one real projection forces a real operator to be scalar: it preserves every real line, and evaluating it on sums of two independent vectors makes their eigenvalues equal. Orthogonality fixes that scalar to $+1$ or $-1$. Conversely either scalar commutes with all real readouts.

In the complex description, commutation with every rank-one complex projection similarly forces a complex scalar; unitarity gives modulus one. The spectral resolution (63.2) represents $Q$ by eigenvalues $e^{i\theta_j}$, so equality of their $N$th powers is exactly the congruence in (65.6). Multiple actual eigenangles need not satisfy it. The condition belongs to the stipulated observation family, rather than to the mere existence of $J_Q$, and is weaker than the real operator return $Q^N=I$. $\square$

## 66. Two frequencies can give orthogonal source rays despite accurate extraction

**定理 66.1（A maximal ray disturbance with an exact delayed bypass）。** Fix a positive integer $N$ and $0<a<b\le\pi/2$ with $N(b-a)\ge\pi$. Choose

$$
\theta_1=a,\qquad\theta_2=a+\frac\pi N\le b,\qquad
Q=\operatorname{diag}(e^{\theta_1J_2},e^{\theta_2J_2}),\qquad
J_Q=\operatorname{diag}(J_2,J_2).
\tag{66.1}
$$

This satisfies (62.2). In the induced complex space $V_{J_Q}$, choose unit vectors $u,v$ of the two orthogonal complex lines, and put $\psi=(u+v)/\sqrt2$. Then, with $\alpha=N\theta_1$,

$$
Q^N\psi=e^{i\alpha}\frac{u-v}{\sqrt2},\qquad
\langle\psi,Q^N\psi\rangle_{\mathbb C}=0.
\tag{66.2}
$$

For every real isometry $T$ satisfying (65.2) for this $Q,N$, its output on the bypass input $|0\rangle\otimes\psi$ is at distance at least $\sqrt2-\epsilon$ from the undelayed ready target, even after optimization over a common complex phase. The source ray projector onto $\psi$ has quadratic readout at most $\epsilon^2$ there, compared with one on the undelayed target.

Proof. Both angles lie in $[a,b]\subset(0,\pi/2]$, so $\|C_Q\|=\cos a$ and the positive skew polar direction is as displayed. Their accumulated phases differ by $\pi$, proving (66.2). Equivalently, the two real vectors $Q^N\psi$ and $\psi$ are orthogonal, and $Q^N\psi$ is also orthogonal to $J_Q\psi$. Hence it is orthogonal to the entire complex ray of $\psi$ and remains so after any common complex phase choice. The ideal delayed and phase-adjusted undelayed ready outputs therefore have distance $\sqrt2$. The triangle inequality subtracts at most $\epsilon$ for the actual joint-output error.

The complex source ray projector is represented in real coordinates by the orthogonal projection onto $\operatorname{span}_{\mathbb R}\{\psi,J_Q\psi\}$. Its lift acting as identity on controllers annihilates the ideal delayed output. Its norm on the actual output is therefore at most $\epsilon$, and its quadratic readout at most $\epsilon^2$. Availability of this projector as a physical observation is an additional premise.

For the displayed circuit of Theorem 63.1 the bypass is exact, so (66.2) has no work residual there. An explicit instance uses $a=\pi/6$ and $r=15$ from Theorem 60.1:

$$
N_r=899,\qquad q_r=1798,\qquad
\epsilon_r=2(3/4)^{16}<1/32,\qquad
\theta_2=\pi/6+\pi/899<\pi/2.
\tag{66.3}
$$

Thus the same fixed circuit admits an actual two-frequency source whose delayed bypass ray is orthogonal to its initial ray, while its active relative quarter turn obeys (63.4). Logical-control accuracy alone supplies neither small-error source return nor a catalytic source conclusion. $\square$

**定理 66.2（A sufficient narrow-band source-return estimate）。** If the actual $J_Q$-complex eigenangles lie in an interval of width $L$ centered at $\theta_0$, then

$$
\|Q^N-e^{iN\theta_0}I\|\le\min\{2,NL/2\}.
\tag{66.4}
$$

Proof. On each actual eigenangle, $|\theta_j-\theta_0|\le L/2$ and the chord bound gives $|e^{iN\theta_j}-e^{iN\theta_0}|\le\min\{2,N|\theta_j-\theta_0|\}$. The spectral operator norm is the maximum of these quantities. This estimate is useful when $NL$ is small; increasing extraction accuracy alone does not make the actual source disturbance decrease. $\square$

## 67. Composite complex logical control and two different source reductions

**定义 67.1（The induced complex matrix representation）。** For a complex $2\times2$ matrix $M$, let $\rho_{J_Q}(M)$ act on the real $B\otimes V$ by replacing each entry $u+iv$ by $uI+vJ_Q$. This representation preserves products and adjoints because $J_Q^2=-I$ and $J_Q^*=-J_Q$. Let

$$
R_\alpha=\begin{pmatrix}\cos\alpha I&-\sin\alpha I\\
\sin\alpha I&\cos\alpha I\end{pmatrix},\qquad
Z_B=\operatorname{diag}(1,-1).
\tag{67.1}
$$

The standard two-axis Euler form, with its explicit parameter derivation in the [companion volume, Theorem 51.1, equations (51.3)–(51.6)](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md), gives real angles $\alpha,\beta,\gamma$ for each $M\in SU(2)$ such that

$$
\rho_{J_Q}(M)=R_\alpha S_QR_\beta S_Q^{-1}R_\gamma,
\qquad S_Q^{-1}=(Z_B\otimes I)S_Q.
\tag{67.2}
$$

**定理 67.2（A finite composite with the source delay retained）。** Substituting two copies of the forward circuit (63.4) into (67.2), with a known controller sign for the inverse quarter turn, gives at most $4N_r$ forward calls and ready-input joint error at most $2\epsilon_r$ relative to

$$
e_0\otimes (I_B\otimes Q^{2N_r})\rho_{J_Q}(M).
\tag{67.3}
$$

Fresh work registers may be used, or the same work register reused; for fresh registers $e_0$ denotes their joint ready vector.

Proof. Every ideal factor in (67.2) commutes with $I_B\otimes Q$, since $J_Q$ does. The two ideal delays therefore move to the output and combine to $Q^{2N_r}$. Multiplying the second-branch controller sign with one instance of $F_Q$ changes its comparator from $D_{N_r}S_Q$ to $D_{N_r}S_Q^{-1}$ and preserves its norm error. The first approximate step contributes at most $\epsilon_r$. At the second step, apply its error estimate to the ideal previous output, whose work controller is ready; its error is again at most $\epsilon_r$. The orthogonality of the actual second step preserves the earlier error. The triangle inequality gives $2\epsilon_r$, including all work residuals, whether registers are fresh or reused. This proves the finite composite (67.3), with no exact source-return claim. $\square$

**假设 67.3（Complex factors and a complex partial trace）。** Separately stipulate the complex factorization $\mathbb C^2\otimes_{\mathbb C}V_{J_Q}$, any untouched complex reference, and complex partial trace over the source as the chosen reduction. This is an additional tensor and observation contract; it is not inferred from the real controller/source tensor product or from the circuit menu.

**定理 67.4（The ideal complex reduction and the ordinary real reduction differ）。** Under Assumption 67.3 the ideal comparator in (67.3) is $M\otimes Q^{2N_r}$, and its logical/reference reduced action is conjugation by $M$ on the logical factor, even for initial correlations with the source. This statement about the ideal complex reduction does not assert exact reduced action for the finite imperfect circuit. The retained source still undergoes $Q^{2N_r}$. Its effect is invisible to a declared readout family exactly when that family commutes with $I_B\otimes Q^{2N_r}$; invisibility to all Hermitian readouts requires the common-scalar criterion (65.6) with $N=2N_r$. This readout-relative invisibility does not assert that the full retained real source process is unchanged.

For an ordinary real source factor and a real unit vector $x$, however,

$$
S_Q\left(\frac{|0\rangle+|1\rangle}{\sqrt2}\otimes x\right)
=\frac{|0\rangle x+|1\rangle J_Qx}{\sqrt2}
\tag{67.4}
$$

has ordinary real controller reduction $I_2/2$. The complex logical description has instead the pure relative phase $(|0\rangle+i|1\rangle)/\sqrt2$, whose imaginary Pauli readout is represented on the real interface by the joint operator

$$
\rho_{J_Q}\!\begin{pmatrix}0&-i\\i&0\end{pmatrix}
=\begin{pmatrix}0&-J_Q\\J_Q&0\end{pmatrix}.
\tag{67.5}
$$

Proof. In the stipulated complex factorization, $\rho_{J_Q}(M)=M\otimes I$ and the common source factor is $I\otimes Q^{2N_r}$. A unitary on a traced complex factor leaves the other reduced state unchanged, including when that state is initially correlated with the traced factor. Thus for any density operator $\sigma$ on logical, source and untouched reference factors,

$$
\operatorname{Tr}_{V_{J_Q}}\!\left[
(M\otimes Q^{2N_r}\otimes I)\sigma
(M\otimes Q^{2N_r}\otimes I)^*\right]
=(M\otimes I)\operatorname{Tr}_{V_{J_Q}}(\sigma)(M\otimes I)^*.
\tag{67.6}
$$

This is the stated ideal reduction under the supplied complex contract.

For the ordinary real reduction in (67.4), skewness gives $g(x,J_Qx)=0$ and orthogonality gives $\|J_Qx\|=1$. The real partial trace consequently has diagonal entries $1/2$ and zero off-diagonal entries. In the complex description $J_Qx=ix$, so the same real vector is the pure complex product of $(|0\rangle+i|1\rangle)/\sqrt2$ and $x$. Formula (67.5) follows by the entrywise definition of $\rho_{J_Q}$; it is real self-adjoint and has expectation one in (67.4). It uses the reference complex structure on the real source and is not a controller-only real observable. The two reductions therefore have different observation sets. Coordinates alone do not identify them as the same physical discard operation. $\square$

## 68. Reference acquisition and observation boundaries

**定义 68.1（Distinct source, orientation and readout premises）。** The spectral-band premise (62.2), the actual controlled primitive (62.3), the exact transport commutation in Theorem 64.1, the orientation condition (64.3), and the readout commutant (65.1) are distinct assumptions. The comparison-versus-callable distinctions of the [companion volume, Definitions 42.2 and 47.1](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) remain in force. Its Theorem 44.1 obtains an exact common polar structure from a joint transport gap; its Theorem 45.1 supplies an echo only with additional actual reference durations; and its Theorem 47.2 separates a central phase from motion of complex rays. None of those premises alone acquires the spectral-band oracle used here.

The skew polar factor, real spectral calculus, binomial series, real linear combination, two-reflection amplification, polarization, commutants and two-axis Euler decomposition are established intermediate methods. No literature priority or new primitive gate is inferred from their use. The construction neither certifies an actual source's band from finite root data, forces transport commutation, selects a prior $J_0$ without (64.3), nor makes a multifrequency delay invisible outside the actual readout commutant. It does not derive source preparation, a Born probability rule, physical complex observations or complex tensor independence. Word reversal has square $I$, whereas $J_Q^2=-I$; no source-word identification or retained-failure decoder is supplied. Native source acquisition, restricted controller synthesis, tighter counted bounds and any physical observation or discard contract retain their separate mathematical or operational obligations.

## 追加锚（本行以下为增补区）

## 69. Correcting the actual forward delay with counted source calls

**定义 69.1（The delayed extractor and a selected return exponent）。** Use the actual spectral-band source, controller interface and comparison direction of Definitions 62.1–62.2. Thus

$$
C_Q=(Q+Q^*)/2,\qquad K_Q=(Q-Q^*)/2,\qquad
\|C_Q\|\le\cos a<1,\qquad0<a<\pi/2,
\tag{69.1}
$$

and $J_Q=K_Q(I-C_Q^2)^{-1/2}$, $S_Q=\operatorname{diag}(I,J_Q)$. Only actual controlled forward $Q$ queries and known real orthogonal controller gates are supplied. All calls are counted, with no inverse, fractional reference duration, other free source gate, measurement, outcome selection or work discard. For a fixed integer $r\ge0$, Theorem 63.1 supplies the orthogonal $F_Q$ with

$$
\begin{gathered}
N=(2r+1)\left(2\left\lceil\frac{\pi(r+2)}4\right\rceil+1\right),
\qquad\epsilon_r=2\cos^{2r+2}a,\\
\|F_Q(e_0\otimes\cdot)-e_0\otimes(I_B\otimes Q^N)S_Q\|
\le\epsilon_r.
\end{gathered}
\tag{69.2}
$$

Its displayed schedule uses $2N$ forward calls. The bypass source action is exactly $Q^N$, and the error includes the active-sector work residual. The source-return task here corrects that additional delay using further forward calls, uniformly on every unknown logical/source input.

In the $J_Q$-complex comparison coordinates, collect equal eigenangles and write the finite spectral resolution

$$
Q=\sum_{j=1}^s e^{i\theta_j}P_j,\qquad
\theta_j\in[a,\pi-a],\qquad
\sum_{j=1}^sP_j=I,
\tag{69.3}
$$

where the $P_j$ are nonzero orthogonal complex spectral projections. The same formulas represent real rotations on their underlying real subspaces. This spectral description alone supplies no physical ray observations, probabilities or complex partial trace. A selected integer return exponent will always be required to satisfy $T\ge N$.

**定理 69.2（Exact query bookkeeping and two source-return criteria）。** Appending $T-N$ unconditional forward queries to the circuit in (69.2) gives the ready-input isometry

$$
\mathcal T_{Q,T}
=(I_C\otimes I_B\otimes Q^{T-N})F_Q(e_0\otimes\cdot)
\tag{69.4}
$$

with displayed query count and joint error

$$
q_{\rm total}=N+T,\qquad
\|\mathcal T_{Q,T}-e_0\otimes(I_B\otimes Q^T)S_Q\|
\le\epsilon_r.
\tag{69.5}
$$

A certificate $\|Q^T-I\|\le\delta$ therefore gives the phase-fixed real conclusion

$$
\|\mathcal T_{Q,T}-e_0\otimes S_Q\|\le\epsilon_r+\delta.
\tag{69.6}
$$

If a $J_Q$-complex projective criterion is separately stipulated, a different certificate $\|Q^T-e^{i\varphi}I\|\le\delta$ gives the same bound relative to $e_0\otimes e^{i\varphi}S_Q$.

Proof. The appended source factor is orthogonal, so it preserves the error in (69.2). The number of calls is $2N+(T-N)=N+T$. Subtracting the appropriate delayed and undelayed target operators and using $\|S_Q\|=1$ proves both estimates by the triangle inequality. These are whole logical/source operator-norm estimates, including all work-output components, and persist under any untouched finite real reference. Source return removes the extra $Q$ delay: the active branch still intentionally applies $J_Q$, while the bypass intentionally applies identity. Real phase-fixed return and complex projective return are different criteria; neither follows from return on one root vector. $\square$

## 70. Finite catalogs give counted late delay repair

**定理 70.1（Catalog-dependent phase-fixed and projective delay repair）。** Fix a nonempty finite angle catalog $\Theta=\{\theta_1,\ldots,\theta_s\}\subset[a,\pi-a]$, an integer $M\ge2$, and the delay $N$ in (69.2). There is a selected integer

$$
T=N\ell,\qquad 1\le\ell\le M^s,
\tag{70.1}
$$

which works for every actual orthogonal source satisfying (69.1) whose canonical angles belong to this catalog, regardless of their multiplicities or unknown eigenbasis, and yields

$$
\|Q^T-I\|\le\frac{2\pi}{M},\qquad
\|\mathcal T_{Q,T}-e_0\otimes S_Q\|
\le\epsilon_r+\frac{2\pi}{M},\qquad
q_{\rm total}\le N(1+M^s).
\tag{70.2}
$$

For the separately declared complex projective criterion, another selected integer satisfies

$$
\begin{gathered}
T=N\ell,\qquad1\le\ell\le M^{s-1},\\
\|Q^T-e^{iT\theta_1}I\|\le\frac{2\pi}{M},\qquad
\|\mathcal T_{Q,T}-e_0\otimes e^{iT\theta_1}S_Q\|
\le\epsilon_r+\frac{2\pi}{M},\\
q_{\rm total}\le N(1+M^{s-1}).
\end{gathered}
\tag{70.3}
$$

When $s=1$, $\ell=1$ gives exact projective source return without implying an exact phase-fixed operator period.

Proof. Use the standard simultaneous Dirichlet phase-box mechanism already used on a chosen grid in the [clocks continuation, Theorem 9.1](https://github.com/the-omega-institute/trureturing/blob/615d1d58b1cf668e5979245ecb6bdc9ac5ec1525/docs/develop/theory/AURIC_CIRCLES_PERIODS_AND_ENDOGENOUS_CLOCKS_V78_CONTINUATION.md#statement-9-1). That theorem compares a weighted root vector up to a common phase. Here its proof mechanism is applied to all $s$ absolute phases to certify the full real source operator, then to $s-1$ relative phases for the projective criterion.

Put $\alpha_j=N\theta_j/(2\pi)$ and partition $[0,1)^s$ into $M^s$ boxes of side $1/M$. Among $M^s+1$ points $n\alpha\bmod1$, $n=0,\ldots,M^s$, two occupy the same box. Their positive index difference $\ell$ lies between one and $M^s$, with every $\ell\alpha_j$ at distance at most $1/M$ from an integer. The chord bound gives

$$
\max_j|e^{iN\ell\theta_j}-1|\le2\pi/M.
\tag{70.4}
$$

On every actual eigenspace the same scalar residual bound holds. Taking their maximum is exactly the source operator norm, so it covers every unknown vector and every allowed eigenbasis at once. Equation (69.6) and $T\le NM^s$ prove (70.2).

For (70.3), apply the same argument to $N(\theta_j-\theta_1)/(2\pi)$, $j=2,\ldots,s$, in $s-1$ dimensions. All residual phases then lie within $2\pi/M$ of the common phase $e^{iT\theta_1}$. If $s=1$ there are no relative phases and $Q^N=e^{iN\theta_1}I$ exactly. The count follows from (69.5).

The finite pigeonhole step is also the standard principle represented by [mathlib's `Fintype.exists_ne_map_eq_of_card_lt`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Fintype/Pigeonhole.lean). It is an intermediate tool in this counted application. No continuous reference duration or callable logarithm is used. The quantifier fixes the catalog and tolerance before choosing $T$; it gives no one universal exponent for all catalogs in a continuum, no computed return integer, and no general calibration or search procedure. An actual repair uses a selected integer together with its certified residual. $\square$

## 71. Visible phase graphs reduce the return requirement for declared readouts

**定义 71.1（Actual matched spectral blocks and the complex visibility graph）。** Fix the actual matched spectral projections in (69.3) and a declared family $\mathcal O$ of $J_Q$-complex-linear Hermitian readouts on $H=B\otimes_{\mathbb R}V$ in its induced complex description. For $\widehat P_j=I_B\otimes P_j$, define an undirected graph on $\{1,\ldots,s\}$ by joining distinct $j,k$ when some $E\in\mathcal O$ has

$$
\widehat P_jE\widehat P_k\ne0.
\tag{71.1}
$$

Let its connected components be $\mathcal V_1,\ldots,\mathcal V_c$ and put $p=s-c$. The actual graph, catalog and readout family are premises. Their exact block support is not inferred from a finite sample of vanishing readings, and a nominal graph is not substituted for the actual matched blocks.

**定理 71.2（Exact readout return and its counted approximation）。** For $D_T=I_B\otimes Q^T$, the ideal delayed target has the same quadratic readouts as $S_Q$ on every unit input for every $E\in\mathcal O$ if and only if $e^{iT\theta_j}$ is constant on each graph component. Choose one anchor $b_h\in\mathcal V_h$. For every integer $M\ge2$ there is an integer

$$
T=N\ell,\qquad1\le\ell\le M^{s-c}
\tag{71.2}
$$

and the unitary comparison operator

$$
D_0=\sum_{h=1}^c e^{iT\theta_{b_h}}
                    \sum_{j\in\mathcal V_h}P_j
\tag{71.3}
$$

such that

$$
\begin{gathered}
\|Q^T-D_0\|\le2\pi/M,\qquad
[I_B\otimes D_0,E]=0\quad(E\in\mathcal O),\\
\|\mathcal T_{Q,T}-e_0\otimes(I_B\otimes D_0)S_Q\|
\le\epsilon_r+2\pi/M,\\
\|\mathcal T_{Q,T}^*(I_C\otimes E)\mathcal T_{Q,T}-S_Q^*ES_Q\|
\le2\|E\|(\epsilon_r+2\pi/M),\qquad
q_{\rm total}\le N(1+M^{s-c}).
\end{gathered}
\tag{71.4}
$$

These are declared-readout return bounds, not full source return between graph components.

Proof. Apply the actual-source commutant criterion (65.1). On the $j,k$ spectral block,

$$
\widehat P_j[D_T,E]\widehat P_k
=(e^{iT\theta_j}-e^{iT\theta_k})\widehat P_jE\widehat P_k.
\tag{71.5}
$$

A nonzero edge block therefore forces equal phases. Equality propagates along paths. Conversely every readout is block diagonal across graph components; phases constant on each component consequently commute with every such readout. Together with all-input Hermitian polarization in Theorem 65.1 this proves the exact criterion, without interpreting the quadratic readouts as probabilities.

There are exactly $p=s-c$ nonanchor indices. Apply the phase-box argument inside Theorem 70.1 to the $p$ numbers $N(\theta_j-\theta_{b_h})/(2\pi)$ for $j\in\mathcal V_h\setminus\{b_h\}$. It gives (71.2) with every relative phase residual at most $2\pi/M$. The spectral operator norm then proves $\|Q^T-D_0\|\le2\pi/M$. The phases of $D_0$ have unit modulus and are constant on the components, so it is unitary and commutes with the declared readouts. It is a comparison operator, not an additional free source gate.

Combining (69.5) with the source residual gives the joint comparison bound in (71.4). Its comparator is an isometry whose compressed readout equals $S_Q^*ES_Q$. Subtracting two isometric compressions as in (65.4) bounds the actual readout difference by $2\|E\|(\epsilon_r+2\pi/M)$. Finally $T\le NM^{s-c}$ gives the count. These estimates retain every work-output component.

For all complex source/logical Hermitian readouts, every pair of distinct nonzero spectral blocks has an available nonzero Hermitian cross block, so the graph is complete and $c=1$. This recovers the projective bound (70.3). For complex logical-controller-only readouts, $\widehat P_j(E_B\otimes I)\widehat P_k=0$ for $j\ne k$, so $c=s$. Then there are no phase constraints: $\ell=1$ and $D_0=Q^N$ exactly, with no appended return calls needed. This does not identify complex reduction with discarding an ordinary real source factor, as shown in Theorem 67.4. Additional arithmetic relations may lower the number of independent approximation constraints; no optimality is claimed for counting the supplied $s-c$ phase differences. $\square$

## 72. An incommensurate source with a finite delay-repair certificate

**定理 72.1（An explicit 2251-call phase-fixed application）。** Let

$$
Q=\operatorname{diag}(e^{\theta_1J_2},e^{\theta_2J_2}),\qquad
\theta_1=\pi/4,\qquad\theta_2=\frac\pi{2\sqrt2},\qquad
J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
\tag{72.1}
$$

Use $a=\pi/6$, $r=15$, so $N=899$, the extractor uses $1798$ calls, and $\epsilon_r=2(3/4)^{16}<1/32$. Appending $453$ actual forward calls, corresponding to $T=1352$, gives

$$
q_{\rm total}=2251,\qquad
\|\mathcal T_{Q,1352}-e_0\otimes S_Q\|<3/64.
\tag{72.2}
$$

The estimate is real and phase fixed relative to $S_Q$ on every source vector and includes all work residuals. It removes the additional delay while retaining the intended active-branch $J_Q$ action; it does not assert an untouched or catalytic source under coherent logical control. This same source has no positive integer exact power return, either as a real operator or up to a common complex scalar.

Proof. Both angles in (72.1) lie in $[\pi/6,\pi/2]$, so the actual band and extractor bounds hold. An integer power return would require $T\theta_2/(2\pi)=T/(4\sqrt2)$ to be an integer, which is impossible for positive integer $T$. Return up to one common complex scalar would require $T(\theta_2-\theta_1)/(2\pi)$ to be an integer, but $1/(4\sqrt2)-1/8$ is irrational. These statements concern powers of this $Q$ and do not rule out other exact controller circuits.

For the selected $T=1352=8\cdot169$, the first angle returns exactly: $T\theta_1=2\pi\cdot169$. For the second angle use the elementary Pell identity as an intermediate arithmetic certificate,

$$
239^2-2\cdot169^2=-1,\qquad
|169\sqrt2-239|=\frac1{169\sqrt2+239}.
\tag{72.3}
$$

Since $T\theta_2=2\pi\cdot169\sqrt2$, the chord bound on the actual second rotation plane gives

$$
\|Q^{1352}-I\|
\le\frac{2\pi}{169\sqrt2+239}
<\frac\pi{204}<\frac1{64}.
\tag{72.4}
$$

Here $\sqrt2>1$ makes the denominator exceed $408$, and $\pi<22/7$ gives $\pi/204<11/714<1/64$, since $704<714$. The exact first return and second residual bound control the whole source by the maximum of its two spectral residuals. Now $1352-899=453$ and (69.6) give $1798+453=2251$ calls and total error less than $1/32+1/64=3/64$. The arbitrary-$T$ append rule is used; $T$ need not be a multiple of $N$. The certificate neither ignores a common phase nor depends on numerical search or enumeration, and claims neither an optimal count nor a general synthesis procedure. $\square$

## 73. The calibration cost of a selected recurrence

**定理 73.1（Actual-source return and comparison with a nominal direction）。** Let $Q_0$ be a nominal real orthogonal reference on the same actual real carrier $(V,g)$ as $Q$, with a selected integer $T\ge N$ and certificate $\|Q_0^T-I\|\le\delta_0$. Let $Q$ be the actual real orthogonal query with $\|Q-Q_0\|\le\kappa$, separately retaining the actual band premise (69.1). Run the extractor and appended queries with this actual $Q$. Then

$$
\|\mathcal T_{Q,T}-e_0\otimes S_Q\|
\le\epsilon_r+\delta_0+T\kappa.
\tag{73.1}
$$

This comparison requires no matching eigenvectors of $Q$ and $Q_0$, and its target uses the actual $J_Q$. If the nominal reference also has the same certified band parameter $a$, then

$$
\|J_Q-J_{Q_0}\|\le\kappa/\sin a,\qquad
\|\mathcal T_{Q,T}-e_0\otimes S_{Q_0}\|
\le\epsilon_r+\delta_0+(T+1/\sin a)\kappa.
\tag{73.2}
$$

Proof. Product telescoping and orthogonality give

$$
Q^T-Q_0^T=\sum_{j=0}^{T-1}Q^{T-1-j}(Q-Q_0)Q_0^j,
\qquad \|Q^T-Q_0^T\|\le T\kappa.
\tag{73.3}
$$

Thus $\|Q^T-I\|\le\delta_0+T\kappa$ and (69.6) proves (73.1). This uses operator matching on the same actual carrier and common metric, so it does not assume a matched spectral eigenbasis. Closeness of unordered angle lists alone does not supply the premise $\|Q-Q_0\|\le\kappa$.

For (73.2), the skew parts differ by at most $\kappa$, and their least singular values are each at least $\sin a$. Apply the standard polar comparison from the Sylvester calculation in the [companion volume, Theorem 44.1, equations (44.15)–(44.16)](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md):

$$
\|J_Q-J_{Q_0}\|
\le\frac{2\|K_Q-K_{Q_0}\|}
 {\sigma_{\min}(K_Q)+\sigma_{\min}(K_{Q_0})}
\le\frac\kappa{\sin a}.
\tag{73.4}
$$

The polar estimate is an intermediate comparison tool, not a callable polar-map or calibration operation. Since $\|S_Q-S_{Q_0}\|=\|J_Q-J_{Q_0}\|$, another triangle inequality proves the nominal-direction estimate.

For a requested real return tolerance $\epsilon$ relative to the intended $S_Q$, (73.1) supplies the sufficient budget $T\kappa\le\epsilon-\epsilon_r-\delta_0$ when the right side is positive. It is neither necessary nor optimal. A longer selected recurrence does not by itself offset finite uncertainty in the actual query. Uncertainty in the actual band or readout graph is not controlled merely by naming a nominal finite spectrum. $\square$

## 74. Continuous unknown intervals do not share a universal waiting repair

**定理 74.1（A uniform real waiting obstruction and a relative-phase version）。** Fix $0<a<b\le\pi/2$, $L=b-a$, and the single-plane actual family $Q_\theta=e^{\theta J}$. Every positive integer $T$ obeys

$$
\sup_{\theta\in[a,b]}\|Q_\theta^T-I\|
\ge2\sin\!\left(\frac{\min\{TL,2\pi\}}4\right).
\tag{74.1}
$$

For a fixed append-and-wait repair of (69.2), $T\ge N$. Once $NL\ge2\pi$, the displayed extractor followed by that waiting repair has worst-case phase-fixed error exactly two on the bypass. An arbitrary implementation with uniform joint error at most $\epsilon_r$ relative to the same delayed target has corresponding worst-case lower bound $2-\epsilon_r$. These are real phase-fixed statements.

If a permitted angle interval has $TL\ge\pi$, a two-frequency source with angles in that interval can instead have $Q^T$ send a source ray to an orthogonal complex ray. Thus fixing one waiting exponent does not provide uniform multifrequency source return under a complex projective criterion either.

Proof. The phase set $e^{iT\theta}$ traverses an arc of angular length $TL$. If $TL\ge2\pi$, it covers the whole circle and its maximum chord distance from one is two. If $TL<2\pi$, a chord-distance ball of radius $d<2$ about one covers an arc of length $4\arcsin(d/2)$. To contain the whole image arc requires $TL\le4\arcsin(d/2)$; if the maximum is already two, the claimed lower bound also holds. This proves (74.1).

When $NL\ge2\pi$ and $T\ge N$, some actual $\theta$ satisfies $Q_\theta^T=-I$. The displayed bypass is exactly $Q_\theta^T$, so its distance from the identity bypass is two; the norm of the difference of two unit-output isometries is at most two. For any other $\epsilon_r$-accurate delayed implementation, the triangle inequality subtracts at most $\epsilon_r$ at that same angle. Identifying $-I$ with identity would change the real target criterion.

For the projective version choose two actual angles separated by $\pi/T$, which fit in the allowed interval when $TL\ge\pi$. On their equal superposition the relative accumulated phase is $\pi$, yielding an orthogonal complex ray exactly as in Theorem 66.1. That example retains the actual two-frequency source and is independent of any absolute common phase.

There is no conflict with Theorem 70.1: its integer is chosen after fixing a finite catalog. Finite dimension gives an existence result separately for each source, without one selected integer valid over a continuous uncalibrated family. The [companion volume, Theorem 54.1](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) is a separate analytic interval bound for the full forward-only phase-fixed task, rather than solely this append-and-wait strategy. $\square$

## 75. Return certificates, declared observations and acquisition scope

**定义 75.1（The callable return contract）。** An actual repair in §§69–74 uses a supplied coherent controlled reference, its actual certified band, the native real controller resources, a selected integer return certificate and the stated calibration precision. The graph route additionally uses the actual matched spectral blocks and declared $J_Q$-complex-linear Hermitian readouts. These source, operation and observation premises are distinct. Source-only channel data, finite root tests or a single returning trajectory do not acquire all of them.

The [companion volume, Definitions 42.2 and 47.1](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) separates comparison maps from actual menus. Its Theorem 45.1 uses extra reference durations for a special exact echo; those durations are not supplied here. The clocks continuation's phase-box proof, standard Dirichlet pigeonhole arguments, spectral norm identities, the elementary Pell certificate, polar perturbation and graph-block commutator calculation are credited intermediate tools inside this counted source-return application. No new general recurrence theorem, first-return-time claim, general-method novelty or literature priority is asserted. An abstract logarithm of $Q$ is not made a callable flow.

A readout-return certificate preserves only the stated observations and does not establish full source return between visibility components. A complex projective return differs from the real phase-fixed operator criterion, and the complex readout graph does not supply ordinary real discard or complex tensor independence. No Born law, independent ready source, physical complex observation contract, word-reversal identification or native retained-failure decoder is derived. The intended active source action remains $J_Q$, with $J_Q^2=-I$ rather than the square-$I$ word reversal.

## 追加锚（本行以下为增补区）

## 76. Complement determinant quantization and original-menu capacity

**定义 76.1（The unchanged four-dimensional table and integral atoms）。** Let $R=\mathbb Z[i]$. For a dyadic integer $N=2^m$, $m\ge1$, retain the single complete table $p:K_{4,m}\to[0,1]$, all labelled two- and three-result menus including zero and repeated effects, their tolerance $\epsilon\in[0,1/10]$, and the original coordinate tomography matrix $H$ from the [companion volume, Definition 16.1](https://github.com/the-omega-institute/trureturing/blob/4e274edb55f70418baa5abf9c318600017fb6e8c/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md). Write

$$
e(X)=p(X)-\operatorname{Tr}(HX),\qquad X\in K_{4,m}.
\tag{76.1}
$$

A nonzero $G\in\operatorname{Herm}_4(R)$ with $G\succeq0$ is an integral interval atom if

$$
\{X\in\operatorname{Herm}_4(R):0\preceq X\preceq G\}=\{0,G\}.
\tag{76.2}
$$

The spectral predicate for an original target is still

$$
\lambda_{\max}(E)\le1-A/N^2
\quad\text{or}\quad
\lambda_{\min}(E)\ge A/N^2,
\qquad A>2.
\tag{76.3}
$$

There is no relation between tables at different scales. In particular, no congruence covariance of $p$ is supplied.

**定理 76.2（Determinant dichotomy, complementary-atom confinement and legal multiplicity）。** Let $N$ be an integer and let $G\in\operatorname{Herm}_4(R)$ satisfy

$$
0\prec G\prec NI_4,\qquad
1\le d:=\det G<N.
$$

Put $B=NI_4-G$ and $D=\det B$. Then

$$
D=d+kN\quad\text{for some integer }k\ge0.
\tag{76.4}
$$

If $k=0$, both endpoint gaps satisfy

$$
\lambda_{\min}(G)\le\frac{4d}{N},\qquad
\lambda_{\min}(B)\le\frac{4d}{N}.
\tag{76.5}
$$

Consequently, if $N>11$, $d\le11$, and

$$
\lambda_{\max}(G)\le N-A/N,\qquad A>44,
\tag{76.6}
$$

then $D\ge N+d$. In particular $B$ is not an integral interval atom. If instead $G$ and $B$ are both positive-definite integral interval atoms and $N>11$, their determinants are equal and at most $11$, and

$$
\lambda_{\min}(G/N)\le\frac{44}{N^2},\qquad
1-\lambda_{\max}(G/N)\le\frac{44}{N^2}.
\tag{76.7}
$$

Under the hypotheses $d\le11$ and (76.6), if $N\ge2048$, define

$$
\eta=2D^{-1/4},\qquad
 t=\left\lfloor\frac{D^{1/4}}2\right\rfloor.
$$

There is $0\ne q\in R^4$ such that

$$
qq^*\preceq\eta B,\qquad
 tqq^*\preceq B,\qquad
 t\ge\left\lfloor\frac{(N+d)^{1/4}}2\right\rfloor\ge3.
\tag{76.8}
$$

For a dyadic $N\ge2048$ and any original table of Definition 76.1, set

$$
X_j=\frac{jqq^*}{N},\qquad
Y_j=\frac{G+jqq^*}{N},\qquad 1\le j\le t.
$$

All these are original-grid effects. Each $X_j$ is strict rank one, meaning $\|X_j\|_{\rm op}<1$, and $Y_j\prec I_4$ for $j<t$. Their errors satisfy, separately for every such $j$,

$$
|e(Y_j)-e(G/N)|\le53144\epsilon.
\tag{76.9}
$$

Proof. The characteristic polynomial of an integral Hermitian matrix belongs to $\mathbb Z[x]$. Indeed its coefficients are signed sums of principal determinants, and each principal determinant is both a Gaussian integer and real. This is the classical principal-minor coefficient formula, also stated in the [pinned Mathlib source as `Matrix.charpoly_coeff_eq_sum_minors`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean). Write

$$
f(x)=\det(xI_4-G)
=x^4-s_1x^3+s_2x^2-s_3x+d,
\qquad s_1,s_2,s_3\in\mathbb Z.
$$

Since the dimension is even, $f(0)=d$ and $f(N)=D$. Reduction modulo $N$ gives $D\equiv d\pmod N$. Positivity makes $D$ a positive integer; since $0<d<N$, the multiplier in (76.4) is nonnegative.

Suppose $D=d$. The equality $f(N)=f(0)$ yields

$$
s_3=N(N^2-Ns_1+s_2).
\tag{76.10}
$$

If $g_1,\ldots,g_4>0$ are the eigenvalues of $G$, then $s_3=d\sum_{a=1}^4g_a^{-1}>0$. Thus (76.10) makes $s_3$ a positive integral multiple of $N$. With $a=\min_a g_a$,

$$
N\le s_3=d\sum_{a=1}^4g_a^{-1}\le\frac{4d}{a},
$$

which gives the first inequality in (76.5). Interchanging $G$ and $B$ gives the other: both determinants equal $d$ and their sum is $NI_4$.

Under (76.6), $\lambda_{\min}(B)\ge A/N>44/N\ge4d/N$, so $k=0$ is impossible. This proves $D\ge N+d$. The [companion volume, Lemma 57.1](https://github.com/the-omega-institute/trureturing/blob/4e274edb55f70418baa5abf9c318600017fb6e8c/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) shows that a positive-definite four-dimensional integral interval atom has determinant at most $11$. Hence $B$ cannot be an atom. If both $G$ and $B$ are positive-definite atoms, that bound puts both determinants in $\{1,\ldots,11\}$. For $N>11$ their congruence forces equality, and (76.5), divided by $N$, gives (76.7).

For the capacity assertion reuse equation (57.2) of that same lemma. The ordinary real eight-dimensional Hermite constant is $\gamma_8=2$, as recorded by Stephanie Vance, [A Mordell Inequality for Lattices over Maximal Orders, §4.2, Table 3 and its preceding paragraph](https://arxiv.org/html/0810.2336v5#S4.T3). The paragraph states ordinary-lattice optimality in dimensions at most eight; the bound is not restricted to a special Gaussian subclass. Applied to $B$, it supplies $0\ne q\in R^4$ with

$$
c:=q^*B^{-1}q\le2D^{-1/4}=\eta<1,
$$

where $D\ge N+d\ge2049>16$. Cauchy--Schwarz in the $B$ inner product gives $qq^*\preceq cB\preceq\eta B$. Since $t\eta\le1$, this proves $tqq^*\preceq B$. The lower bound on $t$ follows from $D\ge N+d$ and $N+d>6^4$.

For $1\le j\le t$, all entries of $X_j,Y_j$ lie on the original grid, and

$$
0\preceq jqq^*\preceq B\prec NI_4,\qquad
0\prec G+jqq^*\preceq NI_4.
$$

Thus $X_j$ has norm strictly less than one. If $j<t$, then $j\eta\le j/t<1$, so $B-jqq^*\succeq(1-j\eta)B\succ0$ and $Y_j\prec I_4$. At $j=t$ only $Y_t\preceq I_4$ is asserted. Compare the actual permitted menus

$$
(G/N,X_j,I_4-Y_j),\qquad(Y_j,I_4-Y_j).
$$

Their defects differ by $e(G/N)+e(X_j)-e(Y_j)$, whose absolute value is at most $2\epsilon$. Lemma 57.2 of the companion volume gives $|e(X_j)|\le53142\epsilon$, proving (76.9) without summing errors over $j$.

These statements have a direct consumer in the original quadratic-margin problem. For an upper-margin target, Theorems 57.3--57.4 of the companion volume produce $G=0$ or an atom with $G\preceq NE$, determinant at most $11$, and error transfer at most $902824\epsilon$. A nonzero residual inherits that upper margin, so (76.6)--(76.9) apply when $A>44$. For a lower-margin target first put $F=I_4-E$. Then $F$ has the required strict upper margin, even if $\|E\|_{\rm op}=1$. The original binary menu and $|\operatorname{Tr}H-1|\le9\epsilon$ give

$$
|e(E)+e(F)|\le10\epsilon.
\tag{76.11}
$$

Thus complementing before extraction avoids any claim that a subatom inherits a lower margin. The remaining coarse dyadic scales $N<2048$ have $N\le1024$; the reused bound $\|H\|_{\rm op}\le8$ gives $|e(E)|\le33\le33792/N$.

Equation (76.9) bounds a difference of errors. It supplies no absolute bound on $e(G/N)$. In fact, if $G$ is an atom and $j<t$, the legal decomposition $NY_j=G+jqq^*$ already has $G$ as its residual in Theorem 57.3. The multiplicity can therefore grow while that residual stays unchanged. The determinant confinement and its finite-table consequences here are repo-derived applications of the credited coefficient and Hermite tools; no classification of Gaussian forms or general covariance of table values is used. $\square$

## 77. Two exceptional effects cannot refute the quadratic-margin event

**定理 77.1（Noisy two-effect support certificate with the original tomography）。** For each $m\ge1$, let $N=2^m$ and let $p$ satisfy exactly Definition 76.1. Suppose there exists a density matrix $\rho\succeq0$, $\operatorname{Tr}\rho=1$, such that

$$
\#\{X\in K_{4,m}:p(X)\ne\operatorname{Tr}(\rho X)\}\le2.
\tag{77.1}
$$

The exceptional effects are arbitrary: they may be singular, complementary, endpoints, or a single self-complementary effect. Their deviations need not be opposite. Then, using the original $H$ pinned by $p$, every target in the unchanged spectral disjunction with $A=45$ satisfies

$$
\lambda_{\max}(E)\le1-\frac{45}{N^2}
\quad\text{or}\quad
\lambda_{\min}(E)\ge\frac{45}{N^2}
\quad\Longrightarrow\quad
|p(E)-\operatorname{Tr}(HE)|\le264(\epsilon+N^{-1}).
\tag{77.2}
$$

For $N\ge16$ the sharper bound $106\epsilon$ holds. Thus (77.1) defines a whole class satisfying the original event with $A=45,C=264$, including every two-point perturbation of the trace table used in the companion volume's §32.

Proof. Put $q_\rho(X)=\operatorname{Tr}(\rho X)$, $\delta(X)=p(X)-q_\rho(X)$, and $S=\{X:\delta(X)\ne0\}$. Every original menu has $q_\rho$-sum one, so its $\delta$-sum has absolute value at most $\epsilon$. Assume first $N\ge16$.

If $|\delta(X)|\le2\epsilon$ for every effect, let $L=H-\rho$. On every original tomography projection $Q$,

$$
|\operatorname{Tr}(LQ)|=|\delta(Q)|\le2\epsilon.
$$

The coefficient expansion (16.6)--(16.7) of the companion volume, with $d=4$ and $\|E\|_{\rm op}\le1$, has total absolute coefficient sum at most $52$. Hence

$$
|\operatorname{Tr}(LE)|\le104\epsilon,\qquad
|e(E)|\le|\delta(E)|+|\operatorname{Tr}(LE)|\le106\epsilon
\tag{77.3}
$$

for every effect, without a spectral restriction.

If $S\subseteq\{0,I_4\}$, the menus $(0,I_4)$ and $(0,0,I_4)$ give

$$
|\delta(0)+\delta(I_4)|\le\epsilon,\qquad
|2\delta(0)+\delta(I_4)|\le\epsilon.
$$

Thus $|\delta(0)|\le2\epsilon$ and $|\delta(I_4)|\le3\epsilon$. All tomography projections lie outside these endpoints, so $H=\rho$ and every error is at most $3\epsilon$.

It remains to treat $S\not\subseteq\{0,I_4\}$ and $|\delta(U)|>2\epsilon$ for some $U$. Such a $U$ cannot be an endpoint. Indeed, the binary menu for an endpoint and its complement would force the other endpoint into $S$; since $\#S\le2$, that would imply $S\subseteq\{0,I_4\}$. Put $V=I_4-U$. The binary menu $(U,V)$ forces $V\in S$, because otherwise $|\delta(U)|\le\epsilon$. Also $V\ne U$, since the allowed repeated menu $(U,U)$ would give $2|\delta(U)|\le\epsilon$ if $V=U$. Consequently

$$
S=\{U,V\},\qquad
|\delta(V)|\ge|\delta(U)|-\epsilon>\epsilon.
\tag{77.4}
$$

Both $U,V$ are nonzero and distinct from $I_4$.

Suppose $V=X+Y$ is a proper original-grid decomposition with $X,Y\ne0$ and $X,Y\succeq0$. Neither summand equals $V$. In the permitted menu $(U,X,Y)$ the only possible exceptional entries are therefore copies of $U$. Its deviation is $(1+n)\delta(U)$, where $n\in\{0,1,2\}$ counts the summands equal to $U$. Its absolute value exceeds $\epsilon$, a contradiction. Thus $V$ is a grid interval atom. Applying the identical argument to a proper decomposition of $U$, using the menu containing $V$ and $|\delta(V)|>\epsilon$, shows that $U$ is also a grid interval atom. This argument uses the noisy menu inequalities directly and keeps all labels and repetitions.

Let $G=NU$ and $B=NV$. Scaling by $N$ makes them integral interval atoms with $G+B=NI_4$. They must both be positive definite. To see this, suppose $G$ is singular. The rank-at-most-three extraction in the proof of the companion volume's Theorem 57.3 supplies $0\ne v\in R^4$ with $vv^*\preceq G$. Atomicity forces $G=vv^*$. Put $s=\|v\|^2$, a positive integer with $s\le N$. If $s=N$, then $B=NI_4-vv^*$ has rank three. The same extraction and atomicity would force $B$ to have rank one, a contradiction. If $s<N$, then $B$ is positive definite and

$$
\det B=N^3(N-s)\ge N^3>11,
$$

contradicting the determinant bound for positive-definite integral interval atoms. This proves $G\succ0$; interchanging $G,B$ proves $B\succ0$.

Theorem 76.2 now gives (76.7) for both $U$ and $V$. In particular each exceptional effect obeys

$$
\lambda_{\min}(X)\le\frac{44}{N^2},\qquad
1-\lambda_{\max}(X)\le\frac{44}{N^2},
\qquad X\in\{U,V\}.
\tag{77.5}
$$

Neither exceptional effect satisfies either branch of (77.2). Since $U,V$ have rank four, every rank-one tomography projection is outside $S$, and $H=\rho$ exactly. Every eligible target consequently has zero error in this case. Together with (77.3) and the endpoint case this proves the $106\epsilon$ bound for $N\ge16$.

For the remaining dyadic scales $N\le8$, the original table bounds from Theorem 16.2 of the companion volume give

$$
|e(E)|\le p(E)+|\operatorname{Tr}(HE)|
\le1+\|H\|_{\rm op}\operatorname{Tr}(E)
\le33\le264/N.
$$

Combining the two regimes proves (77.2). The coefficient expansion and rank-one extraction are reused intermediate tools. The repo-derived conclusion is a uniform certificate for all tables with at most two exceptional effects, for every density baseline, with approximate menus and the actual pinned tomography retained.

For unrestricted original tables, (77.1) is not supplied. The remaining upper-margin atom estimate is still

$$
|e(G/N)|\le C_{\rm atom}(\epsilon+N^{-1})
\tag{77.6}
$$

with one finite constant independent of $N,p,\epsilon$, for all positive-definite integral interval atoms of determinant at most $11$ satisfying an upper margin $A/N^2$ for some fixed $A>44$. Equations (76.8)--(76.9) do not prove (77.6). Nor does (76.7) apply to residual pairs satisfying only $G+G'\preceq NI_4$: its coefficient divisibility used exact complementarity. The original unrestricted existential event is therefore neither proved nor refuted by these results. $\square$

## 追加锚（本行以下为增补区）
