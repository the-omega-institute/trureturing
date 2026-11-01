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

## 76. Reused aligned sectors and actual calibrated local services

**定义 76.1（Nonzero local factors, fixed charts and the aligned sector）。** Let $n\ge2$, let each $d_i\ge1$ be an integer, and let $(V_i,g_i)$ be a real inner-product space of dimension $2d_i$ with an orthogonal complex structure

$$
J_i^*=-J_i,\qquad J_i^2=-I.
\tag{76.1}
$$

On the supplied real tensor interface $W=V_1\otimes_{\mathbb R}\cdots\otimes_{\mathbb R}V_n$, use $J_i$ also for its local extension. The different $J_i$ commute. Reuse the aligned-sector structure of [V53, Theorem 7.2 and Corollary 7.5](https://github.com/the-omega-institute/trureturing/blob/aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e/docs/develop/theory/AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md):

$$
P_{\rm al}=\prod_{j=2}^n\frac{I-J_1J_j}{2},\qquad
S=\operatorname{Ran}P_{\rm al},\qquad
\dim_{\mathbb R}S=2\prod_i d_i.
\tag{76.2}
$$

All $J_i$ agree on $S$. Choose fixed local complex charts, with standard realifications $\mathscr R_i$. For complex density matrices $\rho_i$, the independent realification and its aligned weight are

$$
\eta_n=\bigotimes_{i=1}^n\frac{\mathscr R_i(\rho_i)}2,\qquad
\operatorname{Tr}_{\mathbb R}(P_{\rm al}\eta_n)=2^{-(n-1)}.
\tag{76.3}
$$

This reuses V53's sector and trace identities, including Theorem 7.4, rather than supplying a new sector decomposition. The normalized real factors have trace one because realification doubles complex trace. The tensor interface, independent input family and charts are premises; these formulas install neither physical source independence, free preparations, a projector command nor an outcome rule.

**假设 76.2（Calibrated controlled references and clean ready work）。** On each factor supply the actual calibrated reference

$$
Q_i=\cos\theta_iI+\sin\theta_iJ_i,\qquad
0<\theta_i\le\pi/2,\qquad
\nu_i=\left\lceil\frac\pi{2\theta_i}\right\rceil,
\tag{76.4}
$$

its actual coherent controlled queries, known real orthogonal controller maps, and input-independent ready work. Under this contract the [companion volume, Theorem 51.1 with Definitions 48.1–48.2](https://github.com/the-omega-institute/trureturing/blob/ddcf91008d0d847190eca49c04686ef709e3ee40/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md) supplies a clean controlled-$J_i$ using $\nu_i$ forward calls to $Q_i$. All intermediate synthesis work returns to ready, also on arbitrary coherent outer-flag/source inputs. A source-only channel or comparison complex structure does not supply this service. Controller readout instruments and orientation-reversing source conjugations are additional resources only where separately granted below.

## 77. Coherent acquisition of the complete orientation syndrome

**定理 77.1（A counted tree-syndrome isometry）。** For an edge $e=\{i,j\}$ define the real symmetric involution $K_e=J_iJ_j$ and $P_{e,\pm}=(I\pm K_e)/2$. A controller Hadamard, controlled-$K_e$, and another Hadamard give

$$
|0\rangle\psi\longmapsto
|0\rangle P_{e,+}\psi+|1\rangle P_{e,-}\psi
\tag{77.1}
$$

with $\nu_i+\nu_j$ reference calls. For any spanning tree $T$, using one syndrome bit per edge gives the coherent isometry

$$
\psi\longmapsto\sum_{s\in\{+1,-1\}^{E(T)}}|s\rangle P_s\psi,
\qquad
P_s=\prod_{e\in E(T)}\frac{I+s_eK_e}{2}.
\tag{77.2}
$$

Here bit $0$ records eigenvalue $+1$, and bit $1$ records $-1$. Every $P_s$ is nonzero, has rank $2\prod_i d_i$, and the all-minus label is $P_{\rm al}$. All work other than the displayed syndrome record is ready. The additive service count is

$$
C(T)=\sum_{\{i,j\}\in E(T)}(\nu_i+\nu_j)
=\sum_i\deg_T(i)\nu_i,
\qquad
\min_T C(T)=\sum_i\nu_i+(n-2)\min_i\nu_i.
\tag{77.3}
$$

The minimum is attained by a star centered at a least-cost reference. It optimizes this tree construction's additive service count, rather than all possible joint syndrome algorithms.

Proof. The different $J_i$ commute, so $K_e^*=K_e$ and $K_e^2=I$. Controlled-$K_e$ is the product of controlled-$J_i$ and controlled-$J_j$ with the same flag. The supplied clean services therefore use exactly the stated calls and leave their own work ready. The two rows of the Hadamard conjugation are $(I+K_e)/2$ and $(I-K_e)/2$, proving (77.1).

All $K_e$ commute. Repeating the construction with independent controller bits thus gives the product projectors in (77.2), which are orthogonal and sum to $I_W$. On $\operatorname{Ran}P_s$, each edge imposes $J_j=-s_eJ_i$. Unique paths from root $1$ determine every relative orientation. The all-minus assignment makes all $J_j$ agree with $J_1$, hence gives precisely (76.2).

For the rank count, mathematical local orthogonal conjugations reversing selected $J_i$ toggle the labels on their incident edges. On a tree every label assignment is reachable from any other by such vertex toggles, so all projectors have the same rank. This comparison argument does not grant those conjugations to the operation menu. There are $2^{n-1}$ labels and $\dim_{\mathbb R}W=2^n\prod_i d_i$, proving their common positive rank. Orthogonality of the projectors proves that the displayed map is an isometry.

For a spanning tree, every degree is at least one and $\sum_i(\deg_T(i)-1)=n-2$. Charging each excess degree at $\min_i\nu_i$ gives the lower bound in (77.3), and the stated star attains it. This does not assert that native joint services must decompose into separate edge calls.

If a controller Born instrument is separately supplied, reading the syndrome realizes the joint projector instrument with branch weight $\operatorname{Tr}_{\mathbb R}(P_s\eta)$. Without that additional instrument contract, (77.2) states a coherent joint vector and its squared component norms, rather than an outcome probability law. $\square$

## 78. Intertwining menus conserve orientation weight

**定理 78.1（Sector conservation and the heralded alignment bound）。** Suppose every allowed source operation and controller-source interaction intertwines each individual $J_i$, with controller preparations and outcome operations acting only on the controller. This includes the controlled references of Assumption 76.2. Under a separately supplied controller instrument, let $A_b$ be the resulting source branch Kraus maps. With a retained output record $E_b$, use the output action $J_i\otimes I_{E_b}$. Then

$$
A_bJ_i=(J_i\otimes I_{E_b})A_b,\qquad
A_bP_s=(P_s\otimes I_{E_b})A_b.
\tag{78.1}
$$

If a trace-nonincreasing heralded success branch must leave its source in $S$ for every input state, its effect satisfies

$$
E_{\rm succ}=\sum_{b\in\rm succ}A_b^*A_b\preceq P_{\rm al},\qquad
\operatorname{Tr}(E_{\rm succ}\eta)
\le\operatorname{Tr}(P_{\rm al}\eta).
\tag{78.2}
$$

Consequently its success weight on (76.3) is at most $2^{-(n-1)}$. The all-minus outcome of (77.2) attains that weight when the extra instrument and selection contract permits it. Nonselective intertwining instruments conserve every sector weight.

Proof. Commute each $J_i$ through the source and interaction factors and take controller matrix elements. Controller-only preparation and outcome factors commute with its source action, giving the first relation in (78.1); products then give the projector relation. The same calculation applies to retained records with the displayed output action.

If every successful output is supported on $S$, each successful Kraus map has $(P_{\rm al}\otimes I_{E_b})A_b=A_b$: on a pure input, the sum of squared output norms outside that subspace is zero, so each summand vanishes. Equation (78.1) gives $A_b=A_bP_{\rm al}$. Hence $E_{\rm succ}=P_{\rm al}E_{\rm succ}P_{\rm al}$. Trace nonincrease gives $E_{\rm succ}\preceq I$, which proves (78.2), including retained-record outputs. Formula (76.3) then gives the independent-input bound; the syndrome projector realizes equality under the stated outcome contract.

For a nonselective instrument, $\sum_bA_b^*A_b=I$, so

$$
\sum_b\operatorname{Tr}\!\left((P_s\otimes I_{E_b})A_b\eta A_b^*\right)
=\operatorname{Tr}\!\left(P_s\sum_bA_b^*A_b\eta\right)
=\operatorname{Tr}(P_s\eta).
\tag{78.3}
$$

Conditional normalization can raise a selected branch's sector fraction by discarding other weight, without violating (78.2). Reading more flags or making more queries in this intertwining menu does not transfer weight between sectors. The branch and success probabilities have an operational interpretation only under the supplied instrument contract. $\square$

## 79. Granted orientation flips align the source while retaining its sector record

**定理 79.1（Coherent alignment with the minimum reversible record dimension）。** Enlarge the menu by actually granting coherently controlled local real orthogonal conjugations $C_j$ in fixed complex charts, with

$$
C_j^2=I,\qquad C_jJ_jC_j^*=-J_j.
\tag{79.1}
$$

For a tree syndrome $s$, write $J_j=\sigma_jJ_1$ on $\operatorname{Ran}P_s$, where $\sigma_1=1$ and the other $\sigma_j\in\{+1,-1\}$ are determined by the tree paths. Then

$$
R_s=\prod_{j>1:\,\sigma_j=-1}C_j
\tag{79.2}
$$

maps $\operatorname{Ran}P_s$ isometrically onto $S$. The corrected syndrome map is

$$
V\psi=\sum_s|s\rangle R_sP_s\psi
\in\mathbb R^{2^{n-1}}\otimes S,\qquad V^*V=I_W.
\tag{79.3}
$$

For an isometry preserving arbitrary input vectors from all of $W$ into $S\otimes_{\mathbb R}E$ with fixed ready ancillary input,

$$
\dim_{\mathbb R}E\ge\frac{\dim_{\mathbb R}W}{\dim_{\mathbb R}S}
=2^{n-1}.
\tag{79.4}
$$

Proof. Reversible controller logic computes the path signs from the recorded labels. Conjugating by $C_j$ reverses $J_j$ and leaves other local structures unchanged, so the chosen flips make every orientation agree with the unchanged root orientation. Thus $R_s\operatorname{Ran}P_s\subseteq S$; orthogonality and equal dimensions make it an isometric onto map. Orthogonality of the record labels and of the $P_s$ gives $V^*V=\sum_sP_s=I_W$. Counting the dimensions of the domain and codomain of any proposed isometry gives (79.4), whose denominator is positive because every $d_i\ge1$.

The $C_j$ are real linear and complex antilinear. Their existence as comparison maps does not supply their controlled physical action, and they are not generated by repeatedly querying the commuting $Q_j$ menu. An environment receiving discarded information counts as $E$ when reversibility of the full input is preserved. The bound concerns the full real input space, not a restricted known family or thermodynamic cost. The source in (79.3) is aligned, while the record retains its former sector. This need not preserve local complex data in the original fixed charts. $\square$

## 80. Fixed-chart blocks of independently realified product inputs

**定义 80.1（Two sectors and normalized chart embeddings）。** Take two fixed local complex charts with dimensions $d,e\ge2$. Let $\mathcal H=\mathbb C^d\otimes_{\mathbb C}\mathbb C^e$, $W=V_A\otimes_{\mathbb R}V_B$, and

$$
K=J_AJ_B,\qquad S_-=\operatorname{Ran}\frac{I-K}{2},\qquad
S_+=\operatorname{Ran}\frac{I+K}{2}.
\tag{80.1}
$$

The aligned sector is $S_-$. Reuse V53 Theorem 7.2's real isometry from the underlying real space of $\mathcal H$,

$$
\Phi(x\otimes_{\mathbb C}y)
=\frac{x\otimes_{\mathbb R}y-J_Ax\otimes_{\mathbb R}J_By}{\sqrt2}.
\tag{80.2}
$$

For Hermitian $X$ on $\mathcal H$, put

$$
\iota_-(X)=\tfrac12\Phi\mathscr R_{\mathcal H}(X)\Phi^*,\qquad
U=I\otimes_{\mathbb R}C_B,\qquad
\iota_+(X)=U\iota_-(X)U^*,
\tag{80.3}
$$

where $C_B$ is conjugation in Bob's fixed chart. These are comparison embeddings; $C_B$ is an operation only when the enlarged menu of §79 is granted. The common complex structure on $S_-$ is $J=J_A|_{S_-}$, and the $S_+$ chart uses Alice's $J_A$ as well.

**定理 80.2（Normalized product blocks and the state change under alignment）。** The map $\iota_-$ is a positive trace-preserving real-linear order isomorphism from complex Hermitian matrices onto real symmetric operators on $S_-$ commuting with $J$. It preserves trace norm. The map $\iota_+$ is another positive trace-preserving embedding. For every complex density pair $(\rho,\sigma)$ in the fixed charts,

$$
\begin{aligned}
\eta(\rho,\sigma)
&=\frac{\mathscr R_A(\rho)\otimes_{\mathbb R}\mathscr R_B(\sigma)}4\\
&=\tfrac12\iota_-(\rho\otimes\sigma)
 +\tfrac12\iota_+(\rho\otimes\sigma^{\mathsf T}),
\end{aligned}
\tag{80.4}
$$

where $T_B$ denotes partial transpose in that fixed Bob chart. Applying §79's correction using only $C_B$ on the wrong sector and then discarding its record gives

$$
\eta(\rho,\sigma)\longmapsto
\iota_-\!\left(\rho\otimes\frac{\sigma+\sigma^{\mathsf T}}2\right).
\tag{80.5}
$$

Proof. Realification of a Hermitian matrix repeats each eigenvalue twice. The factor $1/2$ in (80.3) cancels this multiplicity for both trace and trace norm. Under the isometry $\Phi$, realification identifies complex Hermitian matrices exactly with the real symmetric matrices commuting with $J$, preserving positivity in both directions. Conjugation by the orthogonal $U$ proves the corresponding positivity and trace properties of $\iota_+$. It has $U^2=I$ and $UKU^*=-K$.

Write $A=\mathscr R_A(\rho)$ and $B=\mathscr R_B(\sigma)$. Restriction of $A\otimes B$ to $S_-$ through $\Phi$ is $\mathscr R_{\mathcal H}(\rho\otimes\sigma)$. Its contribution to $\eta$ is therefore $\iota_-(\rho\otimes\sigma)/2$. Conjugation by $U$ changes $B$ to $\mathscr R_B(\overline\sigma)=\mathscr R_B(\sigma^{\mathsf T})$, since $\sigma$ is Hermitian. Restricting in the same chart gives the second term. The two source blocks are orthogonal, each has trace $1/2$, and they exhaust $\eta$ because $A\otimes B$ commutes with $K$. This proves (80.4), including its normalization and chart choice.

On the $S_+$ term, the wrong-sector correction $U$ maps $\iota_+(X)$ to $\iota_-(X)$, while the aligned term is unchanged. Discarding the syndrome record adds those two terms and gives (80.5). For a coordinate qubit positive $Y$ eigenstate of Bob, transposition reverses its $Y$ sign, so his resulting qubit density is $I_2/2$. Orientation alignment has changed his fixed-chart state.

Formula (80.4) is a product-input statement. Its real-linear extension in $X$ has the expression $[\iota_-(X)+\iota_+(T_BX)]/2$, without asserting positivity on arbitrary entangled $X$. Both $\iota_\pm$ individually are positive on every positive Hermitian $X$. These facts have different domains and must not be conflated. $\square$

## 81. A full-cone positive decoder cannot preserve all fixed product labels

**定理 81.1（Fixed-chart deterministic decoder obstruction）。** There is no single fixed real-linear map

$$
L:\operatorname{Sym}_{\mathbb R}(W)\longrightarrow
\operatorname{Sym}_{\mathbb R}(S_-)
\tag{81.1}
$$

which is positive on the full real positive cone, trace preserving, and satisfies

$$
L(\eta(\rho,\sigma))=\iota_-(\rho\otimes\sigma)
\quad\text{for every complex density pair }(\rho,\sigma)
\tag{81.2}
$$

in the same fixed local charts and output labels. This excludes positive maps, a class containing the real completely positive trace-preserving maps. Input-independent ancillas and discarded records do not evade it when their effective source map obeys these positivity, trace and fixed-label conditions.

Proof. On the output $S_-$ define the real twirl

$$
\operatorname{Tw}_J(Y)=\tfrac12(Y+JYJ^*).
\tag{81.3}
$$

It is positive and trace preserving, its range commutes with $J$, and it fixes every $\iota_-(X)$. Consequently

$$
\mathcal A=\iota_-^{-1}\operatorname{Tw}_JL\iota_-,\qquad
\mathcal B=\iota_-^{-1}\operatorname{Tw}_JL\iota_+
\tag{81.4}
$$

are positive trace-preserving real-linear maps on the full complex Hermitian space. For each product $X=\rho\otimes\sigma$, (80.4) and (81.2) imply

$$
\tfrac12\mathcal A(X)+\tfrac12\mathcal B(T_BX)=X.
\tag{81.5}
$$

If both local states are pure, $X$ has rank one. The two matrices before their $1/2$ factors on the left are positive and have trace one. Evaluating their average on the orthogonal complement of $X$ forces both to be supported in its one-dimensional range; their trace then makes both equal to $X$. Thus

$$
\mathcal A(X)=X,\qquad\mathcal B(T_BX)=X
\quad\text{for every pure product }X.
\tag{81.6}
$$

Local rank-one projectors span the local Hermitian spaces over $\mathbb R$: diagonal matrix units and real or imaginary off-diagonal parts are obtained from coordinate vectors and their real or imaginary pairwise sums. Their products therefore span $\operatorname{Herm}_{de}(\mathbb C)$. Real linearity and $T_B^2=I$ force $\mathcal A=\mathrm{id}$ and $\mathcal B=T_B$ on that entire space.

Choose two coordinate basis vectors in each local chart, their conjugation-invariant qubit faces, and

$$
\begin{gathered}
|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2,\qquad
\Omega=|\Phi^+\rangle\langle\Phi^+|,\\
T_B\Omega=\tfrac12F,\qquad
\langle\Psi^-|T_B\Omega|\Psi^-\rangle=-\tfrac12,\qquad
|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2,
\end{gathered}
\tag{81.7}
$$

where $F$ swaps the two chosen qubit faces and is zero outside their tensor product. The negative expectation contradicts positivity of $\mathcal B$ on $\Omega$. This is the standard Bell partial-transpose witness; see J. Watrous, [The Theory of Quantum Information, Chapter 2, “The transpose map”, equations (2.156)–(2.159)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). It is an intermediate positive-map fact used here against the particular fixed decoder (81.2).

No positivity of the product embedding's extension to entangled $X$ was used. Instead, full-cone positivity of $L$ requires positivity on the actual real state $\iota_+(\Omega)$ in its actual $S_+$ input sector. A model admitting only a restricted state domain does not acquire that full-cone condition from reference queries or finitely many test preparations.

For $n$ factors, any two local complex dimensions at least two give the same obstruction to a full-cone positive trace-preserving decoder preserving every fixed $n$-fold product label. Fix all other complex product states at the input. Twirl the aligned output by its common $J$, identify its complex tensor representation, and take the ordinary complex marginal over the fixed additional factors. These mathematical compositions are positive and trace preserving and would yield a forbidden two-factor map of the form (81.1)–(81.2). This reduction claims no extra physical marginal operation in the native menu. $\square$

## 82. A finite ten-probe lower bound for the same decoder contract

**定理 82.1（A nonzero error floor on fixed coordinate qubit faces）。** Retain the full-cone positive trace-preserving $L$ in (81.1), without requiring exact decoding. Choose coordinate qubit faces in the fixed local charts, invariant under their coordinate conjugations. On each face let $\sigma_x,\sigma_y,\sigma_z$ be the Pauli matrices and $\rho_{a,u}=(I_2+u\sigma_a)/2$, extended by zero outside that face. Put $P_{a,uv}=\rho_{a,u}\otimes\rho_{a,v}$ and the ten pure products

$$
\mathcal P=\{P_{x,++},P_{x,--}\}
\ \cup\ \{P_{y,uv}:u,v=\pm1\}
\ \cup\ \{P_{z,uv}:u,v=\pm1\}.
\tag{82.1}
$$

With $D(X,Y)=\|X-Y\|_1/2$, define on these product probes

$$
F(P)=\iota_-^{-1}\operatorname{Tw}_JL(\eta(P))
=\tfrac12\mathcal A(P)+\tfrac12\mathcal B(T_BP),
\tag{82.2}
$$

where $\eta(P)$ means independent realification of that pure product, rather than a positive embedding of arbitrary entangled matrices. If $D(F(P),P)\le\epsilon$ for all $P\in\mathcal P$, then

$$
\epsilon\ge\frac1{72}.
\tag{82.3}
$$

The same bound holds when the original real decoder outputs all have real half trace-norm error at most $\epsilon$ relative to $\iota_-(P)$, or when a retained-record decoder has such a correct source marginal.

Proof. The rank-one effect $P$ and the variational characterization of half trace norm give $\operatorname{Tr}(PF(P))\ge1-\epsilon$. Each of $\mathcal A(P)$ and $\mathcal B(T_BP)$ is a density matrix and has overlap at most one with $P$, so

$$
\operatorname{Tr}\bigl(P\mathcal B(T_BP)\bigr)\ge1-2\epsilon.
\tag{82.4}
$$

For any density $Y$ and pure projector $P$,

$$
D(Y,P)\le\sqrt{1-\operatorname{Tr}(PY)}.
\tag{82.5}
$$

Indeed spectrally decompose $Y$, use the pure-pair identity $D(|v\rangle\langle v|,P)=\sqrt{1-\langle v|P|v\rangle}$, apply trace-norm convexity, then Cauchy–Schwarz to the weighted square roots. Thus (82.4) gives $D(\mathcal B(T_BP),P)\le\sqrt{2\epsilon}$.

The probe set is closed under $T_B$: the $x,z$ eigenprojectors are fixed, while Bob's $y$ sign reverses. Apply the last inequality to $T_BP$ to obtain

$$
D(\mathcal B(P),T_BP)\le\sqrt{2\epsilon}
\quad(P\in\mathcal P).
\tag{82.6}
$$

The Bell density on these coordinate faces has the exact signed decomposition

$$
\begin{aligned}
\Omega
&=\tfrac14(I\otimes I+\sigma_x\otimes\sigma_x
-\sigma_y\otimes\sigma_y+\sigma_z\otimes\sigma_z)\\
&=\tfrac12(P_{x,++}+P_{x,--})
-\tfrac14\sum_{u,v=\pm1}uv\,P_{y,uv}
+\tfrac14\sum_{u,v=\pm1}uv\,P_{z,uv}.
\end{aligned}
\tag{82.7}
$$

The absolute coefficients sum to $3$. Real linearity, (82.6) and the trace-norm triangle inequality therefore yield

$$
\tfrac12\|\mathcal B(\Omega)-T_B\Omega\|_1
\le3\sqrt{2\epsilon}.
\tag{82.8}
$$

The first matrix $\mathcal B(\Omega)$ is positive with trace one. The second has antisymmetric expectation $-1/2$ by (81.7), and their difference is Hermitian with trace zero. Using the effect $|\Psi^-\rangle\langle\Psi^-|$ in the variational characterization of half trace norm gives a lower bound $1/2$ for the left side of (82.8). Hence $3\sqrt{2\epsilon}\ge1/2$, proving (82.3). Output outside the selected faces does not change this argument; that antisymmetric projector remains an effect on the full output space.

Twirling contracts real trace norm on Hermitian matrices by convexity and orthogonal invariance, and $\iota_-$ preserves trace norm. Thus original real output error at most $\epsilon$ implies the bound assumed for $F(P)$. A retained record with the stated source marginal gives the same effective positive trace-preserving source map after discard. The constant $1/72$ is this proof's lower bound, with no sharpness claim. This is a mathematical test family; neither the ten preparations nor the tomographic effects are thereby free native reference resources. $\square$

## 83. Operation, record and fixed-chart boundaries

**定义 83.1（Distinct alignment and decoding contracts）。** Calibrated controlled references give the coherent syndrome isometry of §77 under the supplied real tensor and ready-controller interfaces. Actual Born readout and heralded selection need the additional instrument contract. The intertwining menu conserves sector mass; coherently granted orientation-reversing conjugations enlarge that menu and permit alignment with a retained sector record. Reversible full-input preservation requires the record dimension in (79.4). None of these facts alone supplies a deterministic fixed-chart state decoder of (81.2).

The sector decomposition, tensor isometry, equal local statistics and independent-input weight are reused from V53 §§7–7.1, and the clean controlled-$J_i$ service from the companion volume's Theorem 51.1. Real simulation with shared phase encoding is established background: M. McKague–M. Mosca–N. Gisin, [Simulating Quantum Systems Using Real Hilbert Spaces](https://arxiv.org/pdf/0810.1923), Phys. Rev. Lett. 102, 020505. That shared encoding does not grant a decoder from the independent realification (80.4). The projector Hadamard construction, density-matrix extremality, partial-transpose witness and trace-norm inequalities are credited intermediate tools inside these conditional operational applications, without a literature-priority claim.

A different shared initial encoding, restriction to real local density matrices, a restricted state cone, or a change of fixed labels or readout convention changes the decoder contract and is outside the no-go conclusion. Existence of these mathematical alternatives does not install them physically. No Born law, source independence, preparation principle or arbitrary source operation is derived from the controlled reference services. A retained orientation record, a source aligned into $S$, and preservation of fixed-chart complex states are separate deliverables.

## 追加锚（本行以下为增补区）

## 84. Positive heralded maps and the fixed-chart success contract

**定义 84.1（Subnormalized compatible output and zero success）。** Use the fixed two-factor charts, independent encoding $\eta$, aligned sector $S_-$, embeddings $\iota_\pm$ and Bob transpose $T_B$ of §§80–81, with $d,e\ge2$. Thus for a complex product density $P=\rho\otimes\sigma$,

$$
\eta(P)=\tfrac12\iota_-(P)+\tfrac12\iota_+(T_BP).
\tag{84.1}
$$

The embeddings individually are positive, trace preserving and trace-norm preserving. Formula (84.1) is a product-input identity; no positive extension of $\eta$ to all entangled complex matrices is assumed.

Let $L:\operatorname{Sym}_{\mathbb R}(W)\to\operatorname{Sym}_{\mathbb R}(S_-)$ be one fixed real-linear map positive on the entire real positive cone and trace nonincreasing. Input-independent ancillas and discarded success records are permitted when their effective source map has these properties. Reuse the twirl $\operatorname{Tw}_J$ of (81.3) and define

$$
E(P)=\iota_-^{-1}\operatorname{Tw}_JL(\eta(P)),\qquad
p(P)=\operatorname{Tr}E(P).
\tag{84.2}
$$

The inverse is taken only on the $J$-compatible range of the twirl, where it is a positive trace-preserving order isomorphism. The exact fixed-label contract is $E(P)=p(P)P$. For $\epsilon\ge0$ the conditional error contract is written without division by zero as

$$
\tfrac12\|E(P)-p(P)P\|_1\le\epsilon p(P).
\tag{84.3}
$$

For $p(P)>0$ this is $D(E(P)/p(P),P)\le\epsilon$, where $D$ is half trace norm. For $p(P)=0$ it is vacuous, and that input supplies no positive guaranteed success. The trace weight is a probability only under a separately supplied instrument contract.

Every fixed-chart compatible effect has the same pairing with a real output $Y$ and with $\operatorname{Tw}_J(Y)$, so hidden real components outside that effect space do not evade the compatible-output bounds. General-map accuracy in (84.3) concerns this twirled output; it need not imply equal accuracy of the original real state. For $p(P)>0$, original real normalized-output half trace-norm error at most $\epsilon$ relative to $\iota_-(P)$ implies (84.3), by trace preservation and trace-norm contraction of the twirl together with trace-norm preservation of $\iota_-$. Theorem 78.1 bounded an intertwining menu's alignment weight. Here exact fixed-label correctness is imposed on a larger positive-map class without that intertwining premise.

## 85. Optimal exact heralding without a sector-intertwining hypothesis

**定理 85.1（The exact fixed-product success weight is at most the aligned fraction）。** Let $n\ge2$ and every local complex dimension $d_i\ge2$. In the fixed charts of §76 let $L$ be a full-cone positive trace-nonincreasing real-linear map into the aligned output. Require its twirled compatible output on every pure complex product $P$ to equal $p(P)P$. No individual-$J_i$ intertwining assumption is made. Then there is one constant $c\in[0,1]$ such that

$$
p(P)=\frac{c}{2^{n-1}}\le2^{-(n-1)}
\tag{85.1}
$$

for all pure products, and the same fixed weight and correct output extend to all mixed product densities. Projection onto the aligned sector attains $c=1$ as an abstract real completely positive success map. Thus (85.1) is the optimal exact weight in the stated full positive-map class.

Proof. Put $\mathcal H=\mathbb C^{d_1}\otimes_{\mathbb C}\cdots\otimes_{\mathbb C}\mathbb C^{d_n}$ and $m=2^{n-1}$. Fix factor $1$ as orientation anchor. Index the $m$ sectors by subsets $R\subseteq\{2,\ldots,n\}$. Let $\iota_0$ be normalized realification into the aligned sector, let $U_R$ be the mathematical product of coordinate conjugations on $R$, and put $\iota_R(X)=U_R\iota_0(X)U_R^*$. Write $T_R$ for partial transpose on precisely those local fixed charts. Repeated use of (80.4) gives for product densities $X$

$$
\eta_n(X)=\frac1m\sum_{R\subseteq\{2,\ldots,n\}}\iota_R(T_RX).
\tag{85.2}
$$

Each block has trace $1/m$, their supports are orthogonal, and they exhaust $W$. To check the fixed-chart formula, local conjugation changes $\mathscr R_i(\rho_i)$ to $\mathscr R_i(\rho_i^{\mathsf T})$; restriction to the aligned chart then takes the ordinary complex tensor product. This also checks normalization via (76.3). The chart labels and $U_R$ in this argument are comparison data rather than supplied operations.

Let $J$ be the common aligned structure. Each full-Hermitian restriction

$$
A_R=\iota_0^{-1}\operatorname{Tw}_JL\iota_R
\tag{85.3}
$$

is positive and trace nonincreasing. The exact contract states

$$
\frac1m\sum_R A_R(T_RP)=p(P)P.
\tag{85.4}
$$

Each summand is positive because $T_RP$ is a pure product. A rank-at-most-one positive sum has every summand supported on the same rank-one range, including when the sum is zero. Therefore

$$
A_R(T_RP)=c_R(P)P,\qquad c_R(P)\ge0.
\tag{85.5}
$$

For each fixed $R$, the real-linear endomorphism $F_R=A_RT_R$ of $\operatorname{Herm}(\mathcal H)$ has every pure product projector as an eigenvector, with eigenvalue $c_R(P)=\operatorname{Tr}(F_R(P))$. The pure product projectors form a connected set, as the continuous image of a product of connected complex unit spheres. Their eigenvalue function is continuous and takes values in the finite set of real eigenvalues of $F_R$, so it is constant, denoted $c_R$. Pure product projectors span the full Hermitian space over $\mathbb R$, as used in the proof of Theorem 81.1. Thus

$$
F_R=c_R\mathrm{id},\qquad A_R=c_RT_R.
\tag{85.6}
$$

For a nonempty $R$, the anchor lies in its nonempty complement. Choose a qubit face in a factor of $R$ and one in its complement, and a Bell density between them, tensored with real coordinate pure states in every remaining factor. Its partial transpose on $R$ has the antisymmetric Bell eigenvalue $-1/2$, by (81.7). Since every $d_i\ge2$, those faces exist. Positivity of $A_R=c_RT_R$ and $c_R\ge0$ therefore force $c_R=0$ for every nonempty $R$. For $R=\varnothing$, trace nonincrease gives $0\le c_\varnothing\le1$. Substitution in (85.4) proves (85.1) with $c=c_\varnothing$. These are restrictions of the twirled compatible output; no further claim about untwirled sector blocks is needed.

Mixed product densities are convex combinations of pure products, so linearity extends the same constant and correct output to them. The success map $Y\mapsto P_{\rm al}YP_{\rm al}$ has the single real Kraus operator $P_{\rm al}$ and, on (85.2), retains exactly $\iota_0(P)/m$. It attains the bound.

The proof applies positivity to actual entangled states inside each real orientation sector through $\iota_R$, not to an assumed positive entangled-input extension of $\eta_n$. The dimension assumption cannot be dropped from this argument: if some $d_i=1$, the required partial-transpose obstruction can be vacuous, and (85.1) is not asserted. The claim concerns fixed product-state labels. Alignment alone can instead be deterministic under the enlarged conjugation and retained-record contract of Theorem 79.1. $\square$

## 86. A finite qubit success-error frontier with input-dependent weights

**定理 86.1（The 36-probe mean and guaranteed-success bound）。** Let $d=e=2$ in Definition 84.1 and use the fixed coordinate Pauli pure states

$$
\rho_{a,u}=\frac{I_2+u\sigma_a}{2},\qquad
\mathcal P_{36}=
\{\rho_{a,u}\otimes\rho_{b,v}:a,b\in\{x,y,z\},\ u,v\in\{+1,-1\}\}.
\tag{86.1}
$$

Suppose the positive trace-nonincreasing $L$ satisfies (84.3) on all 36 probes, and let $\bar p$ be the arithmetic mean of their success weights. For $\bar p>0$,

$$
\epsilon\ge\frac{\max\{0,2\bar p-1\}}{6\bar p}.
\tag{86.2}
$$

The same necessary bound holds with any strictly positive guaranteed success $p_{\min}$ on that probe family in place of $\bar p$. In particular deterministic decoding on these probes has $\epsilon\ge1/6$. For $0\le\epsilon\le1/6$, (86.2) is equivalent to

$$
\bar p\le\frac1{2-6\epsilon}.
\tag{86.3}
$$

If $\bar p=0$, all nonnegative probe weights vanish and no conditional error assertion produces positive guaranteed success.

Proof. Define the positive trace-nonincreasing restrictions

$$
A=\iota_-^{-1}\operatorname{Tw}_JL\iota_-,\qquad
B=\iota_-^{-1}\operatorname{Tw}_JL\iota_+,\qquad
E=\tfrac12(A+BT_B)
\tag{86.4}
$$

as real-linear maps on complex Hermitian matrices, using the last formula on products for the compatible output.

For an explicit finite averaging group, let $G$ be the single-qubit Clifford conjugation group generated by the Hadamard $H=(\sigma_x+\sigma_z)/\sqrt2$ and $S=\operatorname{diag}(1,i)$, modulo global phases. Their actions on Pauli axes are

$$
\begin{aligned}
H:&\quad \sigma_x\mapsto\sigma_z,\quad
\sigma_y\mapsto-\sigma_y,\quad\sigma_z\mapsto\sigma_x,\\
S:&\quad \sigma_x\mapsto\sigma_y,\quad
\sigma_y\mapsto-\sigma_x,\quad\sigma_z\mapsto\sigma_z.
\end{aligned}
\tag{86.5}
$$

These are orientation-preserving signed permutations, of which there are $3!\cdot4=24$. The generated action is transitive on the six signed Pauli axes, and the stabilizer of $+\sigma_z$ contains the four powers of $S$. It therefore has at least $6\cdot4=24$ elements and hence exactly 24. Conjugation on the Pauli basis determines conjugation on all matrices, so this defines a finite 24-element group of conjugation maps. Its orbit of $|0\rangle\langle0|$ is precisely the six Pauli pure states.

Average independently over $g=(g_A,g_B)\in G\times G$. Choose representatives $U_A,U_B$ and set $C_g=\operatorname{Ad}(U_A\otimes U_B)$, $\widetilde C_g=\operatorname{Ad}(U_A\otimes\overline{U_B})$. Fixed-chart partial transpose gives $T_BC_g=\widetilde C_gT_B$. Put

$$
\overline A=\frac1{24^2}\sum_g C_g^{-1}AC_g,\qquad
\overline B=\frac1{24^2}\sum_g C_g^{-1}B\widetilde C_g,\qquad
F=\overline BT_B,\qquad
\overline E=\tfrac12(\overline A+F).
\tag{86.6}
$$

Both averaged restrictions are positive and trace nonincreasing, being averages of unitary pre- and post-compositions. The maps $\overline A$ and $F$ are covariant under ordinary local Clifford conjugations; indeed $F$ is the ordinary conjugation average of $BT_B$. For $P_0=|00\rangle\langle00|$, its orbit is $\mathcal P_{36}$ with equal group multiplicities. Thus

$$
\operatorname{Tr}\overline E(P_0)=\bar p,\qquad
\tfrac12\|\overline E(P_0)-\bar pP_0\|_1\le\epsilon\bar p.
\tag{86.7}
$$

For the error estimate, write $\overline E(P_0)-\bar pP_0$ as the average of
$C_g^{-1}(E(C_gP_0)-p(C_gP_0)C_gP_0)$ and use unitary invariance and the triangle inequality in (84.3). The average is weighted by the actual $p(C_gP_0)$; the original success weights need not agree. This averaging is a proof device rather than a free native source operation.

The Pauli-basis consequence of covariance can be checked directly. The Pauli conjugations lie in $G$, since $S^2$ gives the $\sigma_z$ conjugation and $HS^2H$ gives the $\sigma_x$ conjugation. Under the four Pauli conjugations, $I,\sigma_x,\sigma_y,\sigma_z$ have distinct sign characters. The product characters on the sixteen two-qubit basis elements are also distinct, so covariance kills all coefficients between different basis elements. Clifford permutations of the three axes then give scalar coefficients on the left-local, right-local and correlation blocks. Accordingly there are real $\alpha,\beta,x,y,z$ with

$$
\begin{gathered}
\overline A(I_4)=\alpha I_4,\qquad F(I_4)=\beta I_4,\\
F(\sigma_a\otimes I)=x\sigma_a\otimes I,\qquad
F(I\otimes\sigma_b)=yI\otimes\sigma_b,\\
F(\sigma_a\otimes\sigma_b)=z\sigma_a\otimes\sigma_b.
\end{gathered}
\tag{86.8}
$$

The trace functionals are invariant under the same conjugations, hence vanish on every traceless Pauli basis element. Since $T_B$ preserves trace, this gives

$$
\operatorname{Tr}\overline A(X)=\alpha\operatorname{Tr}X,\qquad
\operatorname{Tr}\overline B(X)=\beta\operatorname{Tr}X,\qquad
0\le\alpha,\beta\le1,\qquad
\bar p=(\alpha+\beta)/2.
\tag{86.9}
$$

The inequalities follow from positivity and trace nonincrease of the averaged restrictions.

Use the Bell density $\Omega$ and antisymmetric vector of (81.7). Since $\overline B=FT_B$ and
$T_B\Omega=(I\otimes I+\sum_a\sigma_a\otimes\sigma_a)/4$, positivity on $\Omega$ gives

$$
0\le\langle\Psi^-|\overline B(\Omega)|\Psi^-\rangle
=\frac{\beta-3z}{4},\qquad z\le\beta/3.
\tag{86.10}
$$

Also $T_BP_0=P_0$. Positivity of $\overline B(P_0)$ on $|11\rangle$ gives

$$
0\le\frac{\beta-x-y+z}{4}.
\tag{86.11}
$$

Its target survival weight therefore obeys

$$
\langle00|\overline B(P_0)|00\rangle
=\frac{\beta+x+y+z}{4}
\le\frac{\beta+z}{2}\le\frac{2\beta}{3}.
\tag{86.12}
$$

The positive aligned restriction has overlap at most its trace $\alpha$, so

$$
\operatorname{Tr}(P_0\overline E(P_0))
\le\alpha/2+\beta/3=\bar p-\beta/6.
\tag{86.13}
$$

The pure effect $P_0$ and (86.7) give the opposite lower bound $\bar p(1-\epsilon)$. Thus $\epsilon\ge\beta/(6\bar p)$. Finally $\alpha\le1$ and $\beta\ge0$ imply $\beta\ge\max\{0,2\bar p-1\}$, proving (86.2). Only full-cone positivity of the restrictions was used, without covariance or complete positivity of the original map. The function $p\mapsto\max\{0,2p-1\}/(6p)$ is nondecreasing for $p>0$, and $\bar p\ge p_{\min}$, proving the guaranteed-success version. Rearranging on $0\le\epsilon\le1/6$ gives (86.3). $\square$

## 87. Explicit real completely positive maps attain the qubit frontier

**定理 87.1（Uniform-success attainment on all complex product densities）。** For any $0<p\le1$ there is a real completely positive trace-nonincreasing map with success weight exactly $p$ on every two-qubit product density, whose conditional half trace-norm error is zero for $p\le1/2$ and at most

$$
\frac{2p-1}{6p}\quad(p\ge1/2).
\tag{87.1}
$$

Equality holds for every pure Bob density in the latter range, with Alice arbitrary. Thus for $0\le\epsilon\le1/6$ the maximum worst guaranteed success is $1/(2-6\epsilon)$, both for the 36-probe family and for all complex product densities under the fixed-label contract. These maps attain the bound at the actual real-state level, as well as on compatible effects.

Proof. Use the established qubit approximate-transpose channel

$$
\Theta(Y)=\frac{Y+\sigma_xY\sigma_x+\sigma_zY\sigma_z}{3}
=\frac{\operatorname{Tr}(Y)I_2+Y^{\mathsf T}}3.
\tag{87.2}
$$

Its first formula gives the Kraus operators $I/\sqrt3,\sigma_x/\sqrt3,\sigma_z/\sqrt3$, and their squared sum is $I$. The second follows by expansion in $I,\sigma_x,\sigma_y,\sigma_z$. This is the $d=2$ case of F. Buscemi–G. M. D’Ariano–P. Perinotti–M. F. Sacchi, [Optimal realization of the transposition maps, §2, equation (15)](https://arxiv.org/pdf/quant-ph/0304175v1). That known channel is an intermediate ingredient rather than a new general transpose-approximation claim. In particular, for a qubit density $\sigma$, $\Theta(\sigma^{\mathsf T})=(I_2+\sigma)/3$.

For $k\in\{0,x,z\}$, let $O_k$ be the real orthogonal action on $S_-$ corresponding through $\Phi$ to $I_A\otimes\sigma_k$, with $\sigma_0=I$. Put

$$
c_0=\min\{1,2p\},\qquad c_1=\max\{0,2p-1\}.
\tag{87.3}
$$

With projections viewed as maps into their stated output spaces, define

$$
L_p(Y)=c_0P_-YP_-
+\frac{c_1}{3}\sum_{k\in\{0,x,z\}}O_kUP_+YP_+U^*O_k^*.
\tag{87.4}
$$

Its explicit real Kraus operators are $\sqrt{c_0}P_-$ and $\sqrt{c_1/3}O_kUP_+$, with

$$
\sum_jK_j^*K_j=c_0P_-+c_1P_+\preceq I_W.
\tag{87.5}
$$

Thus it is real completely positive and trace nonincreasing on the entire real cone. Formula (80.4) gives

$$
E_p(\rho\otimes\sigma)=\iota_-^{-1}L_p(\eta(\rho,\sigma))
=\frac{c_0}{2}\rho\otimes\sigma
+\frac{c_1}{2}\rho\otimes\frac{I_2+\sigma}{3}.
\tag{87.6}
$$

These outputs already commute with $J$, so twirling does not change them. Their trace is $(c_0+c_1)/2=p$ for every product density. If $p\le1/2$ the wrong-sector coefficient vanishes and the conditional output is exact. If $p\ge1/2$, subtraction gives

$$
D\!\left(\frac{E_p(\rho\otimes\sigma)}p,\rho\otimes\sigma\right)
=\frac{c_1}{3p}D(\sigma,I_2/2)
\le\frac{2p-1}{6p}.
\tag{87.7}
$$

Tensoring a Hermitian difference with positive trace-one $\rho$ preserves its trace norm, and $D(\sigma,I_2/2)\le1/2$, with equality for pure $\sigma$. Hence equality holds on every probe in $\mathcal P_{36}$. Trace-norm preservation of $\iota_-$ gives the same conditional error for the actual real outputs, proving the asserted stronger form of attainment. At $p=1$, the output is $\rho\otimes((2/3)\sigma+I_2/6)$ with worst error exactly $1/6$. At $p=1/2$, $L_p$ is projection onto the aligned sector. The zero map supplies $p=0$, for which no normalized conditional output is claimed.

Theorem 86.1 bounds every positive trace-nonincreasing decoder's guaranteed success on the 36 probes, hence on the full product family; the uniform attaining maps prove the stated optimal values. Implementing them requires the source sector instrument, coordinate conjugation $U$, local Pauli source actions or an equivalent real completely positive dilation as actual extra resources. The controlled-$J$ service of §76 supplies none of those arbitrary source actions by itself. These are mathematical attaining maps under an enlarged operation contract. $\square$

## 88. Success weights, real outputs and native implementation boundaries

**定义 88.1（The fixed-chart heralding scope）。** Theorem 85.1 removes Theorem 78.1's intertwining premise from the exact fixed-product-label success bound, while retaining full-cone positivity, fixed charts and the independent encoding. Its proved restrictions are $A_R=c_RT_R$ with $c_R=0$ for nonempty $R$; no additional assertion about an untwirled map's sector blocks is needed. Theorems 86.1–87.1 give the sharp two-qubit mean-success obstruction and uniform guaranteed-success attainment. A zero-success case remains distinct from any positive guaranteed rate, and variable original success weights were retained throughout the averaging argument.

The general lower bound tests all fixed-chart compatible effects through $\operatorname{Tw}_J$. It also constrains any stronger original-real-state accuracy requirement, since twirling contracts trace norm. Conversely, compatible-effect correctness alone need not establish that stronger real-state statement for an arbitrary map. The explicit attaining maps have $J$-compatible product outputs and attain the frontier in both senses. Success trace weights have a physical probability interpretation only under a separately supplied instrument contract. A proof average over a finite Clifford group does not grant that group as a native control menu.

The normalized sector embeddings and chart identities are the reused V53 structure in §§76,80; the actual controlled quarter-turn service is the companion volume's Theorem 51.1. Shared-phase real simulation is established background as cited in §83, and the Bell transpose witness, finite Clifford action, Pauli sign characters and Kraus-channel facts are credited intermediate tools. The specific approximate-transpose ingredient is attributed in (87.2). These conditional encoding-and-success applications make no literature-priority claim. The ten-probe $1/72$ bound in Theorem 82.1 remains a valid weaker bound on a smaller test family.

Alignment without fixed-label state preservation, a different shared initial encoding, restrictions to real local states or to a smaller input cone, and changed chart/readout conventions give different contracts. Multiple independently prepared copies of each unknown local state also fall outside this single-copy real-linear argument. Neither the finite probes nor the averaging group supplies native preparation, tomography, a Born law, source independence or arbitrary source control. The attaining real completely positive operations retain their stated acquisition and implementation obligations.

## 追加锚（本行以下为增补区）

## 89. The fixed-chart success contract in arbitrary local dimensions

**定义 89.1（Rectangular dimensions and compatible conditional error）。** Use the two-sector encoding and fixed local charts of §§80,84 for arbitrary complex dimensions $d,e\ge2$, and put

$$
\mathcal H=\mathbb C^d\otimes_{\mathbb C}\mathbb C^e,\qquad
r=\min(d,e),\qquad \kappa_r=\frac{r-1}{r+1}.
\tag{89.1}
$$

The real source is $W=V_A\otimes_{\mathbb R}V_B$, its sector projections are $P_\pm=(I\pm J_AJ_B)/2$, and the aligned output is $S_-$. Reuse $\Phi$, the normalized embeddings $\iota_\pm$, and $U_B=I\otimes_{\mathbb R}C_B$ from (80.2)–(80.4). For product densities,

$$
\eta(\rho,\sigma)=\tfrac12\iota_-(\rho\otimes\sigma)
+\tfrac12\iota_+(T_B(\rho\otimes\sigma)).
\tag{89.2}
$$

The individual embeddings are positive, trace preserving and trace-norm preserving. Formula (89.2) assumes no positive extension of the independent encoding to entangled complex inputs.

Let $L:\operatorname{Sym}_{\mathbb R}(W)\to\operatorname{Sym}_{\mathbb R}(S_-)$ be a single fixed real-linear success map positive on the full real cone and trace nonincreasing. Define

$$
\begin{gathered}
A=\iota_-^{-1}\operatorname{Tw}_JL\iota_-,\qquad
B=\iota_-^{-1}\operatorname{Tw}_JL\iota_+,\\
E(P)=\tfrac12(A(P)+B(T_BP)),\qquad p(P)=\operatorname{Tr}E(P).
\end{gathered}
\tag{89.3}
$$

The restrictions $A,B$ are positive trace-nonincreasing maps on the full complex Hermitian cone. Conditional accuracy is the subnormalized requirement

$$
\tfrac12\|E(P)-p(P)P\|_1\le\epsilon p(P).
\tag{89.4}
$$

For positive success weight it is half trace distance after normalization. At zero success it assigns no conditional state and gives no positive guaranteed rate. As in §84, it tests the twirled output against all fixed $J$-compatible effects. Original real normalized-output accuracy implies this requirement by twirl contraction, while the converse is not asserted. The trace weight becomes a success probability only under an additional instrument and Born contract. The inputs are single independently realified local states with fixed labels.

## 90. A finite weighted family of local state probes

**定义 90.1（Coordinate and fourth-root phase tests）。** In a local dimension $s\ge2$, take the $s$ coordinate pure projectors with individual weight $1/[s(s+1)]$. Also take every flat phase projector $|\phi_z\rangle\langle\phi_z|$, where

$$
|\phi_z\rangle=\frac1{\sqrt s}\sum_{j=0}^{s-1}z_j|j\rangle,
\qquad z_0=1,\qquad z_j\in\{1,i,-1,-i\}\quad(j>0),
\tag{90.1}
$$

with individual weight $s/[(s+1)4^{s-1}]$. Denote this weighted family by $\mathcal D_s$ and its weights by $w_Q$. They sum to one and have support size

$$
N_s=s+4^{s-1}.
\tag{90.2}
$$

The joint fixed-chart test is $\mathcal D_d\times\mathcal D_e$, with product weights and $N_dN_e$ pure product probes. For $s=2$ the local family is exactly the six Pauli pure states, all with weight $1/6$, recovering (86.1). For $s=3$ it has nineteen states: three coordinate states of weight $1/12$ and sixteen flat states of weight $3/64$, giving $361$ weighted product probes for $d=e=3$. These are mathematical test families; available preparations, tomographic effects and sampling resources are separate premises.

## 91. A sharp dimension-dependent frontier from the finite state moments

**定理 91.1（Weighted finite-probe mean and guaranteed-success bound）。** Suppose (89.4) holds on $\mathcal D_d\times\mathcal D_e$, and let $\bar p$ be the weighted average of $p(P)$ over that family. If $\bar p>0$, then

$$
\epsilon\ge\kappa_r\frac{\max\{0,2\bar p-1\}}{2\bar p}.
\tag{91.1}
$$

The same necessary bound holds with any strictly positive guaranteed success $p_{\min}$ on that family in place of $\bar p$. A positive mean alone does not imply a positive guarantee on each probe. For $0\le\epsilon\le\kappa_r/2$, the mean bound is equivalently

$$
\bar p\le\frac{\kappa_r}{2(\kappa_r-\epsilon)}.
\tag{91.2}
$$

Exact compatible decoding therefore has weighted mean success at most $1/2$. A deterministic decoder has worst conditional half trace-norm error at least

$$
\frac{r-1}{2(r+1)},
\tag{91.3}
$$

which is $1/6$ for $r=2$ and $1/4$ for $r=3$. These coefficients depend on the smaller local dimension. Theorem 92.1 has uniform success on all product densities and attains the worst conditional-error bounds, so they give the optimal guaranteed-success frontier for both this finite family and the entire product-state family in the stated positive-map class. When $\bar p=0$, every finite probe has zero weight of success and no normalized conditional state is claimed.

Proof. First verify the precise state moments used by this finite test. Let $F_s$ swap two copies of $\mathbb C^s$ and $D_s^{\rm diag}=\sum_j|jj\rangle\langle jj|$. Uniformly averaging the flat-family fourth-root phases gives

$$
M_{\rm flat}=\frac{I+F_s-D_s^{\rm diag}}{s^2}.
\tag{91.4}
$$

A phase expectation survives exactly when the two ket indices and two bra indices have equal multisets. The two pairings give $I+F_s$; subtracting $D_s^{\rm diag}$ corrects their double count when all indices coincide. Fixing $z_0=1$ only removes a common phase and does not change this projector moment. The coordinate family's second moment is $D_s^{\rm diag}/s$. Its total mixture weight is $1/(s+1)$ and the flat family's is $s/(s+1)$, so

$$
\sum_{Q\in\mathcal D_s}w_QQ=I_s/s,\qquad
\sum_{Q\in\mathcal D_s}w_QQ^{\otimes2}
=\frac{I+F_s}{s(s+1)}.
\tag{91.5}
$$

Each family's first moment already is $I_s/s$. The same second moment holds for a Haar-distributed pure density. For an elementary check, coordinate phase invariance leaves only the same two pairings. If $u$ is a Haar unit vector, coordinate symmetry makes $A_s=\mathbb E|u_j|^4$ and $B_s=\mathbb E(|u_j|^2|u_k|^2)$ independent of distinct $j,k$. Mixing two coordinates by a Hadamard and averaging their phases gives $A_s=A_s/2+B_s$, hence $A_s=2B_s$. Expanding $(\sum_j|u_j|^2)^2=1$ then gives $B_s=1/[s(s+1)]$, proving (91.5) for Haar pure states too. Thus $\mathcal D_s$ is a finite weighted complex projective state $2$-design. Only its state moments are used; no unitary-design hypothesis enters.

Now take independent normalized Haar local unitaries $g=(U_A,U_B)\in U(d)\times U(e)$ as a mathematical proof device. Set $C_g=\operatorname{Ad}(U_A\otimes U_B)$ and $\widetilde C_g=\operatorname{Ad}(U_A\otimes\overline{U_B})$. Because $T_BC_g=\widetilde C_gT_B$, the averages

$$
\overline A=\int C_g^{-1}AC_g\,dg,\qquad
\overline B=\int C_g^{-1}B\widetilde C_g\,dg,\qquad
F=\overline BT_B
\tag{91.6}
$$

leave both restrictions positive and trace nonincreasing. The maps $\overline A,F$ are covariant under ordinary local unitary conjugations, with $F$ the ordinary conjugation average of $BT_B$.

Let $P_0=|0_A0_B\rangle\langle0_A0_B|$ and $f(P)=\operatorname{Tr}(PE(P))$. The Haar mean of $p(P)$ equals $\operatorname{Tr}((\overline A(P_0)+F(P_0))/2)$; the Haar mean of $f(P)$ equals its expectation in $P_0$. These means equal the corresponding weighted means on $\mathcal D_d\times\mathcal D_e$. In fact $p(P)$ is linear in each local density, and $f(P)$ is quadratic in each, so their means use respectively the first and second state moments (91.5). The $T_B$ term is covered by applying its linear transpose to the relevant moment tensor. This uses no positive extension of the joint complex-input map.

For every tested pure product, (89.4) and the pure effect $P$ give $f(P)\ge(1-\epsilon)p(P)$. Taking only these finite weighted means, then identifying them with the Haar means, gives

$$
\bar f\ge(1-\epsilon)\bar p.
\tag{91.7}
$$

No conditional-error assumption is made on pure states outside the finite family. The input-dependent weights remain inside $p(P)$. The unitary integrals are not native source commands or implemented random operations.

Local covariance makes the trace functionals scalar. Write $\operatorname{Tr}\overline A(X)=\alpha\operatorname{Tr}X$ and $\operatorname{Tr}\overline B(X)=\beta\operatorname{Tr}X$. Positivity and trace nonincrease give $0\le\alpha,\beta\le1$, and

$$
\bar p=(\alpha+\beta)/2.
\tag{91.8}
$$

The ordinary local covariance of $F$ has the four-block form

$$
\begin{gathered}
F(X)=aX+b\operatorname{Tr}_B(X)\otimes I_e
+cI_d\otimes\operatorname{Tr}_A(X)
+t\operatorname{Tr}(X)I_{de},\\
\beta=a+eb+dc+de\,t,
\end{gathered}
\tag{91.9}
$$

where $a,b,c,t$ are real. To obtain this standard conjugation-commutant form, split each local Hermitian space into scalar and traceless parts. Unitary conjugation on the traceless part has scalar commutant; the independent product action gives four inequivalent scalar/traceless blocks. The displayed maps span the scalar actions on those blocks. The local assertion can also be checked using diagonal phases, coordinate permutations and two-coordinate unitary rotations. This is a covariance calculation, without any positivity assumption on $F$ itself. The coefficients $b,c$ need not be nonnegative; positivity is retained for $\overline B$ before composing with $T_B$.

Since $T_BP_0=P_0$, positivity of $\overline B(P_0)=F(P_0)$ on the coordinate vectors $|1_A1_B\rangle$, $|0_A1_B\rangle$ and $|1_A0_B\rangle$ gives

$$
t\ge0,\qquad v:=b+t\ge0,\qquad w:=c+t\ge0.
\tag{91.10}
$$

Let $\Omega_2$ be the rank-two coordinate Bell density on the first two basis vectors of each factor. Its partial transpose has antisymmetric expectation $-1/2$, and its reduced densities are the corresponding rank-two projections divided by two. Evaluating the positive $\overline B(\Omega_2)=F(T_B\Omega_2)$ on that vector gives

$$
0\le\frac{-a+b+c}{2}+t,\qquad a\le v+w.
\tag{91.11}
$$

Put $f_B=\operatorname{Tr}(P_0F(P_0))$. Replacing $b,c$ by $v-t,w-t$ yields

$$
f_B=a+v+w-t,\qquad
\beta=a+ev+dw+(de-d-e)t.
\tag{91.12}
$$

For $r=\min(d,e)$, the required rectangular coefficient bound follows from

$$
\begin{aligned}
2\beta-(r+1)f_B
&=(1-r)a+(2e-r-1)v+(2d-r-1)w\\
&\quad+[2(de-d-e)+r+1]t\\
&\ge2(e-r)v+2(d-r)w+[2(de-d-e)+r+1]t\ge0.
\end{aligned}
\tag{91.13}
$$

The first inequality uses $a\le v+w$ and $1-r<0$. The last uses (91.10), $d,e\ge2$ and $de-d-e\ge0$. Thus $f_B\le2\beta/(r+1)$ even when $b$ or $c$ is negative. The aligned positive restriction has survival overlap at most its trace $\alpha$, so

$$
\bar f\le\alpha/2+\beta/(r+1)
=\bar p-\kappa_r\beta/2.
\tag{91.14}
$$

Combining this with (91.7) gives $\epsilon\ge\kappa_r\beta/(2\bar p)$. Finally $\alpha\le1$ and (91.8) imply $\beta\ge\max\{0,2\bar p-1\}$, proving (91.1). The right side is nondecreasing in positive $\bar p$, so $\bar p\ge p_{\min}>0$ proves the guaranteed-success version. Algebraic rearrangement on the stated error interval gives (91.2), and deterministic success gives (91.3). Full-cone positivity was used on the actual sector-embedded Bell and product densities, independently of which finite preparations are tested. $\square$

## 92. Real Kraus attainment by correcting the smaller factor

**定理 92.1（The rectangular frontier is attained with uniform success）。** Under Definition 89.1, for any $0<p\le1$ there is a real completely positive trace-nonincreasing success map with weight exactly $p$ on every product density and conditional error at most

$$
\kappa_r\frac{\max\{0,2p-1\}}{2p}.
\tag{92.1}
$$

The bound is attained whenever the chosen smaller factor has a pure density. In particular all finite-design probes attain it. The outputs are $J$ compatible on this input family, so the same frontier is attained for the actual normalized real-output half trace norm. For $0\le\epsilon\le\kappa_r/2$, the optimal worst guaranteed success is $\kappa_r/[2(\kappa_r-\epsilon)]$ on both the finite test family and the entire product family.

Proof. The standard approximate-transpose channel on dimension $r$ is

$$
\Theta_r(Y)=\frac{\operatorname{Tr}(Y)I_r+Y^{\mathsf T}}{r+1}.
\tag{92.2}
$$

Use its explicit real matrix Kraus operators

$$
K_{ii}=\sqrt{\frac2{r+1}}|i\rangle\langle i|,\qquad
K_{ij}=\frac{|i\rangle\langle j|+|j\rangle\langle i|}{\sqrt{r+1}}
\quad(i<j).
\tag{92.3}
$$

For each coordinate $i$, the squared Kraus sum has coefficient $[2+(r-1)]/(r+1)=1$. Their action on a matrix has diagonal entries $(\operatorname{Tr}Y+Y_{ii})/(r+1)$ and off-diagonal entries $Y_{ji}/(r+1)$, verifying (92.2). Thus $\Theta_r$ is complex completely positive and trace preserving, and realification of its Kraus operators gives a real completely positive lift. This is the established transpose-approximation ingredient of Buscemi–D’Ariano–Perinotti–Sacchi, [Optimal realization of the transposition maps, §2, equations (15), (17)–(18)](https://arxiv.org/pdf/quant-ph/0304175v1); merging the repeated off-diagonal Kraus terms gives (92.3). It is used as an intermediate channel rather than a new general construction.

Choose a factor $j$ of complex dimension $r$, and let $U_j$ be its real coordinate conjugation on $W$, exchanging $S_+$ and $S_-$. The fixed chart matters when $j=A$. For product $X=\rho\otimes\sigma$,

$$
\begin{aligned}
U_B\iota_+(T_BX)U_B^*&=\iota_-(T_BX),\\
U_A\iota_+(T_BX)U_A^*&=\iota_-(T_AX).
\end{aligned}
\tag{92.4}
$$

The first identity follows from $U_B^2=I$. For the second, $U_AU_B$ acts as full coordinate conjugation on the aligned complex tensor chart, so conjugating $\iota_-(T_BX)$ applies the full transpose and leaves $T_AX$. Thus either choice transposes precisely the factor subsequently corrected by $\Theta_r$.

Let $O_\ell$ be the real lift on $S_-$ of the local Kraus operators (92.3) on that factor, so $\sum_\ell O_\ell^*O_\ell=I_{S_-}$. These Kraus lifts need not be orthogonal individually. Put $c_0=\min(1,2p)$ and $c_1=\max(0,2p-1)$, and define

$$
L_p(Y)=c_0P_-YP_-
+c_1\sum_\ell O_\ell U_jP_+YP_+U_j^*O_\ell^*.
\tag{92.5}
$$

Its real Kraus operators are $\sqrt{c_0}P_-$ and $\sqrt{c_1}O_\ell U_jP_+$, with squared sum $c_0P_-+c_1P_+\preceq I_W$. This proves complete positivity and trace nonincrease on the whole real input cone.

For product $X$ whose chosen factor has density $\rho_j$, let $X_j^{\rm noisy}$ replace only that density by $(I_r+\rho_j)/(r+1)$. The chart identities and $\Theta_r(\rho_j^{\mathsf T})=(I_r+\rho_j)/(r+1)$ give the already compatible output

$$
E_p(X)=\iota_-^{-1}L_p(\eta(X))
=\tfrac{c_0}{2}X+\tfrac{c_1}{2}X_j^{\rm noisy},\qquad
\operatorname{Tr}E_p(X)=(c_0+c_1)/2=p.
\tag{92.6}
$$

Its conditional error is

$$
\begin{aligned}
D(E_p(X)/p,X)
&=\frac{c_1}{2p}\frac r{r+1}D(\rho_j,I_r/r)\\
&\le\frac{c_1}{2p}\frac{r-1}{r+1}.
\end{aligned}
\tag{92.7}
$$

Tensoring with the other positive trace-one density preserves the Hermitian trace norm. Convexity gives $D(\rho_j,I_r/r)\le1-1/r$, with equality for a pure density by its eigenvalues. This proves (92.1) and equality on the finite family. For $p\le1/2$ only aligned weight is accepted and error is zero; for $p\ge1/2$ all aligned weight is kept while wrong-sector weight is accepted with coefficient $2p-1$. These statements hold also for mixed product inputs. Since the output is compatible, trace-norm preservation of $\iota_-$ gives the same actual real-state distance. The zero map supplies $p=0$ without a normalized conditional output.

Theorem 91.1 supplies the corresponding necessary guaranteed-success bound, while the uniform maps attain it. For example, $d=2$ with arbitrary $e\ge2$ admits deterministic worst error $1/6$ by correcting Alice's qubit when it is the smaller factor. This does not declare complex partial transpose completely positive. The whole map (92.5) is real completely positive because the conjugation is real orthogonal and the following real Kraus lift is explicit. Physical implementation requires the sector instrument, $U_j$ and the local Kraus dilation as additional resources. The controlled-reference service of §76 can construct the syndrome with an instrument, but grants neither conjugation nor an arbitrary local source dilation. Any retained success record or discarded dilation environment belongs to that implementation. $\square$

## 93. Finite-test, state-space and implementation boundaries

**定义 93.1（The arbitrary-dimension decoder scope）。** The dimension-sensitive coefficient inequality (91.13), finite weighted input tests and smaller-factor attaining operation apply to two independently realified factors under the fixed-label full-positive-cone contract. They extend the qubit frontier of §§86–87 and recover its exact 36-probe family at $d=e=2$. They do not supply the approximate $n$-factor frontier. Exact $n$-factor success remains the separate statement of Theorem 85.1.

The finite design is a weighted family of pure states. Its first moment matches the average success weight, and its second moment matches the average target overlap. No nonlinear error estimate is transferred by an unproved design property, and no finite-probe hypothesis is strengthened into an assumption on untested Haar states. Haar conjugations, the four-block conjugation commutant, phase-moment cancellation, Bell positivity and the approximate-transpose Kraus channel are credited intermediate proof tools. The Haar integrals and test families grant no native preparation, random source unitary, tomography or measurement resource. No literature-priority claim is made for these conditional encoding-and-frontier applications.

The general lower bounds concern the compatible twirled output and also constrain the stronger real-output requirement by twirl contraction. The attaining maps have compatible product outputs and attain both forms. Trace weights require an extra instrument/Born interpretation; tensor independence, full-cone physical applicability and the source operations used by (92.5) are distinct premises. Multiple independent copies of each unknown input, restricted state cones, different shared encodings, changed fixed charts or alignment without preserving labels change the problem. A discarded dilation environment is not an unaccounted reset or an information-erasure conclusion.

## 追加锚（本行以下为增补区）

## 94. Supplied copies and two distinct joint preparation contracts

**定义 94.1（Independent-copy and internally aligned inputs）。** Let $d,e\ge2$, $k,l\ge1$ and $N=k+l$. The fixed realifications $V_A,V_B$ carry orthogonal complex structures $J_A,J_B$. Supply $k$ preparations of an unknown complex density $\rho$ on $\mathbb C^d$ and $l$ preparations of an unknown density $\sigma$ on $\mathbb C^e$. Every copy is a distinct physical factor in

$$
W=V_A^{\otimes_{\mathbb R}k}\otimes_{\mathbb R}V_B^{\otimes_{\mathbb R}l}.
\tag{94.1}
$$

The required output is one A/B pair in the fixed aligned encoding $\iota_{\rm out}(\rho\otimes_{\mathbb C}\sigma)$. The maps considered below are fixed real completely positive trace-nonincreasing maps on the full real input cone. The extra copies are supplied preparations; no operation that clones an unknown state is inferred.

Under independent realification and real tensor independence of every copy, the joint density is

$$
\eta_{\rm ind}(\rho,\sigma)=
\left(\frac{\mathscr R_A(\rho)}2\right)^{\otimes_{\mathbb R}k}
\otimes_{\mathbb R}
\left(\frac{\mathscr R_B(\sigma)}2\right)^{\otimes_{\mathbb R}l}.
\tag{94.2}
$$

A different contract first aligns the copies within each party. Let $\iota_{A,k}$ and $\iota_{B,l}$ be normalized realification into the internal aligned sectors of the two groups, as in V53 Corollary 7.5, and set

$$
\eta_{\rm grp}(\rho,\sigma)=
\iota_{A,k}(\rho^{\otimes_{\mathbb C}k})
\otimes_{\mathbb R}
\iota_{B,l}(\sigma^{\otimes_{\mathbb C}l}).
\tag{94.3}
$$

Embed this density into the same $W$ through the internal sector inclusions. It has independence between the two groups and shared orientation within each group. Theorem 99.1 shows that (94.2) and (94.3) have equal one-copy marginals and equal readings for all products of real symmetric effects, with one effect on each individual copy, while their optimal exact success weights differ when $N>2$. Local densities and copy counts alone therefore do not specify this decoding resource. The copy contracts of this section are distinct from the single-copy contracts of §§84–93.

## 95. Matching equal orientations and taking an ordinary real marginal

**定义 95.1（Relative sectors and the unmatched sign pattern）。** Number the copies with an A copy first, let $J_i$ denote the local complex structure on the $i$th factor of $W$, and let $\eta_i$ denote its normalized real density. Put $s_1=+1$, take $s_j\in\{+1,-1\}$ for $j>1$, and define

$$
P_s=\prod_{j=2}^N\frac{I-s_jJ_1J_j}{2},
\qquad m=2^{N-1}.
\tag{95.1}
$$

These are orthogonal projections with sum $I_W$, and $J_j=s_jJ_1$ on $\operatorname{Ran}P_s$. The independent density commutes with every $J_i$ and $P_s$. Its sector weights and normalized conditional densities are

$$
\operatorname{Tr}(P_s\eta_{\rm ind})=\frac1m,
\qquad
\tau_s=mP_s\eta_{\rm ind}P_s=mP_s\eta_{\rm ind}.
\tag{95.2}
$$

The projectors and uniform weights reuse the V53 orientation algebra. In an expansion of (95.1), every nonconstant term has a local factor $J_i\eta_i$ with zero trace, which gives the displayed weight.

**定理 95.2（Matching-sector construction with unchanged labels）。** There is a real completely positive trace-nonincreasing success map satisfying, for all local densities,

$$
L_{\rm match}(\eta_{\rm ind}(\rho,\sigma))
=\left(1-2^{-(N-1)}\right)
\iota_{\rm out}(\rho\otimes_{\mathbb C}\sigma).
\tag{95.3}
$$

It uses the orientation syndrome to select an A copy and a B copy of equal sign, routes them by within-type real swaps and takes an ordinary real partial trace over every other copy.

Proof. For any selected distinct copies $i,j$, partial trace of (95.2) over all remaining real factors gives

$$
\operatorname{Tr}_{\widehat{i,j}}\tau_s
=\eta_i\otimes_{\mathbb R}\eta_j
-s_is_j(J_i\eta_i)\otimes_{\mathbb R}(J_j\eta_j).
\tag{95.4}
$$

To verify this formula, expand the star projector in (95.1); the factor $m$ cancels its denominator. When one selected copy is the anchor, only the constant term and the edge joining the other selected copy to the anchor survive the partial trace. Their coefficients are $1$ and $-s_is_j$. Every other term has a traced leaf factor $J_h\eta_h$ of trace zero. When neither selected copy is the anchor, only the constant term and the product of their two anchor edges survive. That product has coefficient $s_is_j$ and contains $J_1^2=-I$, giving the same minus sign. All other terms again have a traced leaf factor with zero trace. Thus (95.4) is an ordinary real marginal and has trace one.

If $i$ is A, $j$ is B and $s_i=s_j$, then (95.4) is

$$
\frac{
\mathscr R_A(\rho)\otimes_{\mathbb R}\mathscr R_B(\sigma)
-J_A\mathscr R_A(\rho)\otimes_{\mathbb R}J_B\mathscr R_B(\sigma)
}{4}
=\iota_{\rm out}(\rho\otimes_{\mathbb C}\sigma).
\tag{95.5}
$$

This formula uses the actual selected factors' fixed local output charts. In particular, when both selected signs are negative relative to copy 1, their product is still $+1$ and (95.5) still contains $\rho,\sigma$ with their original labels. No coordinate conjugation of either selected density is required.

There is no equal-sign A/B pair precisely when all A signs are equal and all B signs have the opposite value. Since the anchor is A with sign $+1$, there is exactly one unmatched sector,

$$
s_i=+1\quad(i\in A),\qquad s_j=-1\quad(j\in B).
\tag{95.6}
$$

For every other syndrome, choose a matching pair by a fixed rule and use swaps between copies of the same type to route it into designated A/B output slots. Measuring the orthogonal $P_s$, accepting all but (95.6), applying the controlled real permutation and discarding the other factors defines a real completely positive trace-nonincreasing map. Each accepted conditional input has output (95.5), and each sector has weight $1/m$. Summing them proves (95.3).

The procedure estimates no unknown state label. All accepted syndromes give the same displayed output marginal, so discarding their records leaves that marginal unchanged. This equality neither proves decoupling from a source environment nor asserts preservation of correlations with arbitrary external references. Physical use of the sector instrument and routing operations is an additional premise. $\square$

## 96. Restricting real Kraus maps to a complex sector

**引理 96.1（The full-transpose restriction formula）。** Let a real completely positive map between two realified complex spaces have real Kraus matrices $R_h$. In fixed complex coordinates, write each underlying real-linear map uniquely as

$$
R_hv=M_hv+N_h\overline v,
\tag{96.1}
$$

with complex matrices $M_h,N_h$. Feed normalized realification $\iota_{\rm in}(X)$ and apply the compatible output twirl $\operatorname{Tw}_J(Y)=(Y+JYJ^*)/2$. Its induced complex Hermitian map is

$$
B(X)=\iota_{\rm out}^{-1}\operatorname{Tw}_J
\left(\sum_hR_h\iota_{\rm in}(X)R_h^*\right)
=\sum_hM_hXM_h^*+\sum_hN_hX^{\mathsf T}N_h^*.
\tag{96.2}
$$

Here $X^{\mathsf T}$ is the full transpose of the entire complex input sector.

Proof. For a unit vector $v$, normalized realification of $|v\rangle\langle v|$ is the half mixture of the two unit real vectors represented by $v$ and $iv$. For one Kraus matrix, their images are

$$
M_hv+N_h\overline v,\qquad
i(M_hv-N_h\overline v).
\tag{96.3}
$$

After output twirling and identification with a complex Hermitian matrix, the half sum of their projectors is

$$
\frac12\left(
|M_hv+N_h\overline v\rangle\langle M_hv+N_h\overline v|
+
|M_hv-N_h\overline v\rangle\langle M_hv-N_h\overline v|
\right)
=
|M_hv\rangle\langle M_hv|
+|N_h\overline v\rangle\langle N_h\overline v|.
\tag{96.4}
$$

The input half mixture and the inverse normalized output realification therefore introduce no extra coefficient in (96.2). Summing over $h$ proves it on rank-one projectors, which span the Hermitian input space. Real linearity proves the formula for every Hermitian $X$. $\square$

Thus the induced complex map is the sum of a completely positive map and a completely positive map after full transpose. The transpose is not assumed to be a complex completely positive operation. This decomposition uses the real Kraus representation; it does not hold for every positive real map by the argument given here. Restricting a real completely positive map to a sector inclusion again gives a real Kraus map. Input-independent real ancillas and discarded records can be included in that effective map.

## 97. A polynomial obstruction to finite-power conjugation

**引理 97.1（Vanishing on coherent powers under a conjugate-ray constraint）。** Let $q\ge2$ and let $t$ be a finite positive integer. Suppose a complex-linear map on the symmetric $t$-fold tensor power has output

$$
H(z)=T(z^{\otimes t})\in
\operatorname{span}_{\mathbb C}\{\overline z\}
\qquad(z\in\mathbb C^q).
\tag{97.1}
$$

Then $H(z)=0$ for every $z$. The same conclusion holds for a homogeneous complex polynomial vector map of finite positive degree obeying this ray constraint.

Proof. Homogeneity extends a ray constraint given on unit vectors to all nonzero inputs. In the affine patch $z=(1,u_1,\ldots,u_{q-1})$, let the polynomial coordinates of $H$ be $P_0,\ldots,P_{q-1}$. The constraint gives

$$
P_j(u_1,\ldots,u_{q-1})
=\overline{u_j}P_0(u_1,\ldots,u_{q-1}).
\tag{97.2}
$$

Fix all variables except $u_1=u$. Two one-variable complex polynomials $Q,P$ then satisfy $Q(u)=\overline uP(u)$ for every complex $u$. On the real line this implies $Q(u)=uP(u)$, hence the latter is a polynomial identity on $\mathbb C$. On the imaginary axis the original relation instead gives $Q(u)=-uP(u)$. Consequently $P$ vanishes on the nonzero imaginary axis and is identically zero. Since all the other fixed variables were arbitrary, $P_0$ vanishes throughout the affine patch, and (97.2) kills every coordinate there. Homogeneity gives vanishing whenever the first coordinate is nonzero; continuity gives it on the remaining inputs. $\square$

The lemma concerns finite powers of a universally varying unknown vector. It does not prohibit real coordinate conjugation when that operation is supplied. Such a real operation conjugates the entire complex input, including all other unknown labels. The upper bound below requires a linear or antilinear component to conjugate only one of two independent unknown labels, which is the constraint detected by this lemma.

## 98. The exact copy-count frontier for independent realification

**定理 98.1（Pointwise pure-state upper bound and uniform attainment）。** Let $L$ be any fixed real completely positive trace-nonincreasing map from $W$ to the output pair. Suppose that for every pure local pair $\rho=|a\rangle\langle a|$, $\sigma=|b\rangle\langle b|$, it decodes the independently realified input (94.2) exactly after output twirling, with an input-dependent success weight $p(a,b)$. Then

$$
p(a,b)\le1-2^{-(k+l-1)}
\qquad\text{for every pure local pair}.
\tag{98.1}
$$

The map of Theorem 95.2 attains this value uniformly for all local densities, including mixed densities, with an already compatible output. It is the optimal guaranteed exact success in the real completely positive class both for the pure family and for the entire family of local densities. The pointwise upper bound here is on pure inputs; no pointwise upper bound for every mixed repeated-state input is inferred.

Proof. The input is a positive mixture of the $m$ normalized orientation-sector densities. Every sector's twirled complex output contribution is positive. For pure local inputs the intended complex output is the rank-one projector

$$
P_{ab}=|a\otimes b\rangle\langle a\otimes b|.
\tag{98.2}
$$

A positive sum supported in this ray has each summand supported in the same ray: its expectation on any orthogonal vector is a sum of nonnegative numbers and must be zero. The conclusion also holds when the total success weight is zero.

In the unmatched sector (95.6), the conditional complex input in the anchor chart is the pure density of

$$
v(a,b)=a^{\otimes k}\otimes\overline b^{\otimes l}.
\tag{98.3}
$$

Apply Lemma 96.1 to the restriction of $L$ to this sector. Each individual positive rank-one output term must lie in the target ray. Thus, for every Kraus index and every pure local pair,

$$
\begin{aligned}
M_h(a^{\otimes k}\otimes\overline b^{\otimes l})
&\in\operatorname{span}_{\mathbb C}\{a\otimes b\},\\
N_h(\overline a^{\otimes k}\otimes b^{\otimes l})
&\in\operatorname{span}_{\mathbb C}\{a\otimes b\}.
\end{aligned}
\tag{98.4}
$$

For the first line, fix a unit $a$ and apply its bra to the Alice output. As a function of $z=\overline b$, the resulting Bob output is a homogeneous complex polynomial of degree $l$ in $z$, in the ray of $\overline z$. Lemma 97.1 makes it zero for every $b$. The full output was already in the Alice ray, so the entire first vector is zero. For the second line, fix a unit $b$ and apply its bra to the Bob output. Varying $z=\overline a$ gives the same conjugate-ray constraint of degree $k$ and kills the second vector. This argument applies to every Kraus index.

The unmatched sector therefore contributes zero for every pure local pair. Trace nonincrease bounds the success weight from each of the other normalized sectors by one. Their input weights are all $1/m$, giving

$$
p(a,b)\le\frac{m-1}{m},
\tag{98.5}
$$

which is (98.1). No input-independent success hypothesis was used. Theorem 95.2 attains that value uniformly and without output twirling, including on mixed local densities. Pure states belong to the entire local-density family, so (98.1) bounds that family's guaranteed success too; this proves the stated optimum without extending the pointwise upper bound to all mixed repeated-state inputs. $\square$

No deterministic exact decoder exists for finite $k,l$ under this universal real completely positive contract. The achievable weight tends to one as the number of supplied copies grows but is strictly below one at every finite count. It is $1/2$ for $k=l=1$, $3/4$ for $(k,l)=(2,1)$ and $7/8$ for $k=l=2$. For a target failure $\delta\in(0,1)$, it suffices to supply at least one copy of each label and

$$
N-1\ge\left\lceil\log_2(1/\delta)\right\rceil.
\tag{98.6}
$$

This is a statement about supplied copy resources, without a native preparation or cloning grant.

## 99. Internally aligned groups retain the one-half ceiling

**定理 99.1（Equal product-effect readings and different exact success）。** For the grouped contract (94.3), every fixed real completely positive trace-nonincreasing decoder that is exact after output twirling on all pure local pairs has

$$
p_{\rm grp}(a,b)\le\frac12
\qquad\text{for every pure local pair}.
\tag{99.1}
$$

This is attained uniformly on all local densities by selecting the common-orientation sector and keeping one A/B pair. Nevertheless, $\eta_{\rm grp}$ and $\eta_{\rm ind}$ have equal one-copy marginals and equal readings for all products of real symmetric effects, with one effect on each individual copy. For $N>2$, their optimal guaranteed exact success weights differ.

Proof. Internal alignment fixes all A signs equal and all B signs equal. Only two relative sectors remain: all copies have common orientation, or all A copies oppose all B copies. Applying V53 Theorem 7.4 to the two grouped complex systems of dimensions $d^k,e^l$ gives weight $1/2$ in each. On pure inputs the opposite sector again has the coherent input (98.3). The real Kraus decomposition and polynomial argument in the proof of Theorem 98.1 give zero exact universal success from that sector. Trace nonincrease bounds the common sector's contribution by its input weight $1/2$, proving (99.1). Selecting that sector and tracing out all but one copy of each type gives the exact aligned output with weight $1/2$, also for mixed densities.

To prove equality of the stated observations, examine either group with $t\ge1$ copies. Its internally aligned normalized state is $2^{t-1}$ times its independent-copy density multiplied by its alignment projector. Expand the projector as in (95.1). Its constant term, after this normalization, contributes the independent-copy density. Every nonconstant term contains a factor $J_i\eta_i$ on at least one local copy. This is real antisymmetric because $\eta_i$ is symmetric and commutes with the skew-symmetric $J_i$. Its trace pairing with a real symmetric local effect is zero. For a product of such effects, the trace factors over copies, so every nonconstant projector term vanishes. Apply this argument separately to both groups. It proves equality of all $N$-fold local product readings; choosing identity effects on all but one factor proves equality of the one-copy marginals.

The independent contract has optimum $1-2^{-(N-1)}$ by Theorems 95.2 and 98.1, while the grouped contract has optimum $1/2$. For $N=2$ they coincide, and for $N>2$ they differ. Independent orientations in (94.2) and within-group shared orientations in (94.3) are actual joint-state premises. Repeated local tomography and the stated product effects do not distinguish those two premises. $\square$

The compared effects have one real symmetric factor on each individual copy. No equality is asserted for collective effects within either party or for general joint real effects. Collective operations within either party lie outside this observation class, and the theorem does not assert agreement of all statistics available to each party. General joint real effects can access the orientation relations used by the decoders.

## 100. Optional reference services and the routing resource

**定义 100.1（A counted implementation interface）。** Suppose each copy has a calibrated actual reference $Q_i$ providing a clean controlled-$J_i$ service with forward cost $\nu_i=\lceil\pi/(2\theta_i)\rceil$. The tree construction of §§76–78 obtains all $N-1$ relative signs with forward reference-call count

$$
\sum_i\deg_T(i)\nu_i
\tag{100.1}
$$

for a selected spanning tree $T$. Within that edge-service construction, the least star cost is

$$
\sum_i\nu_i+(N-2)\min_i\nu_i.
\tag{100.2}
$$

These reuse the controlled-reference service and additive tree optimization; they are not global lower bounds for every multi-copy protocol. A supplied projector instrument is additionally needed to read the controller flags.

The matching map also requires syndrome-controlled swaps between copies of the same type, or an equivalent output-routing interface. A controlled-$Q_i$ reference service does not grant those source swaps. The unused copies, synthesis work, orientation records and routing controls must be retained or discarded according to the supplied operation contract. None is claimed to reset for free. The success map specifies the output marginal and trace weight; it does not specify a clean reversible compression of all input data or arbitrary reference-preserving transfer.

When internal alignment is genuinely supplied, the grouped contract can use a single intergroup orientation test. That interface reduction leaves two relative sectors and does not create the $2^{N-1}$ uniform sectors of the different independent-copy input.

## 101. Reused ingredients and the multi-copy boundary

**定义 101.1（The exact real-channel scope）。** The orientation projectors, independent-sector weights and aligned encoding reuse [V53 §7](https://github.com/the-omega-institute/trureturing/blob/7a42e9d2ad9a60c9d9d4783328946e728b0e9eee/docs/develop/theory/AURIC_SHARP_THREE_AXIS_READOUTS_ENDOGENOUS_COMPLEX_STRUCTURE_AND_COMMON_PHASE_COMPATIBILITY_V53.md). The controlled-$J$ ingredient is the calibrated service of [the atlas §§48–52](https://github.com/the-omega-institute/trureturing/blob/7a42e9d2ad9a60c9d9d4783328946e728b0e9eee/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES.md), with reference return, source return and operation grants kept distinct as in §§76–79.

Shared-phase real simulation is established background, including M. McKague, M. Mosca and N. Gisin, [Simulating Quantum Systems Using Real Hilbert Spaces](https://arxiv.org/pdf/0810.1923), *Phys. Rev. Lett.* **102**, 020505. Kraus representations, realification and transpose positivity are standard ingredients; see J. Watrous, [The Theory of Quantum Information, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). The real-Kraus restriction and finite-power conjugate-ray obstruction are proved explicitly here to expose their use in the exact copy-count frontier. The frontier and the contrast between the two joint copy contracts are conditional applications of those ingredients. No literature-priority claim is made for these applications or for finite-copy universal conjugation impossibility.

The upper bound uses real complete positivity. Whether an arbitrary positive map on the full real cone can improve the repeated-state task remains unresolved: Lemma 96.1 supplies no decomposition for that larger class. The earlier single-copy positive-map bounds retain their original contract. Restricted catalogs, real-only local densities, approximate decoding, dependent repeated preparations, other shared encodings and extra unknown-input copies change the problem.

All displayed trace weights require an additional instrument and Born contract to represent operational success probabilities. No external-reference preservation, cloning, state estimation, source independence, native instrument or general quantum-origin conclusion follows from these output-product identities. In particular the attaining map is exact on the prescribed marginal family; this condition does not establish an identity channel on arbitrary correlated extensions.

## 追加锚（本行以下为增补区）

## 102. Pure repeated inputs and a conditional approximation contract

**定义 102.1（Two pure-copy preparations and the remaining sector weight）。** Let $d,e\ge2$, $k,l\ge1$, $\rho_a=|a\rangle\langle a|$, $\sigma_b=|b\rangle\langle b|$ and $P_{ab}=\rho_a\otimes_{\mathbb C}\sigma_b$. The supplied inputs are either of the two contracts in Definition 94.1, restricted to pure local labels:

$$
\begin{aligned}
\eta_{\rm ind}(a,b)
&=(\mathscr R_A(\rho_a)/2)^{\otimes_{\mathbb R}k}
\otimes_{\mathbb R}(\mathscr R_B(\sigma_b)/2)^{\otimes_{\mathbb R}l},\\
\eta_{\rm grp}(a,b)
&=\iota_{A,k}(\rho_a^{\otimes_{\mathbb C}k})
\otimes_{\mathbb R}\iota_{B,l}(\sigma_b^{\otimes_{\mathbb C}l}).
\end{aligned}
\tag{102.1}
$$

In the first contract, every copy is independently realified and real tensor independent. In the second, each party's copies already share an internal orientation before the two groups are independently combined. They embed in the same real copy space. Their one-copy marginals and readings for products of real symmetric effects, with one effect on each individual copy, agree by Theorem 99.1. No equality of collective effects within a party or general joint real effects is assumed.

Let $M$ be the number of populated equal-weight orientation sectors and $p_0$ the total weight of the sectors admitting exact matching:

$$
M_{\rm ind}=2^{k+l-1},\qquad M_{\rm grp}=2,\qquad
p_0=1-\frac1M.
\tag{102.2}
$$

In either contract there is exactly one populated unmatched sector. Its conditional complex input vector is

$$
v(a,b)=a^{\otimes k}\otimes\overline b^{\otimes l}.
\tag{102.3}
$$

Each other populated sector admits the exact fixed-label output $\iota_{\rm out}(P_{ab})$ by matching, within-type routing and ordinary real partial trace as in Theorem 95.2. This includes equal negative signs relative to the anchor, without conjugating either selected label.

Let $L$ be one fixed real completely positive trace-nonincreasing success map on the full real input space, with output one aligned A/B pair. Set

$$
E(a,b)=\iota_{\rm out}^{-1}\operatorname{Tw}_J L(\eta(a,b)),
\qquad p(a,b)=\operatorname{Tr}E(a,b).
\tag{102.4}
$$

The required worst conditional half trace-norm error is the subnormalized inequality

$$
\frac12\|E(a,b)-p(a,b)P_{ab}\|_1\le\epsilon p(a,b).
\tag{102.5}
$$

At zero success, it assigns no normalized conditional state. Accuracy of the original normalized real output implies (102.5) by twirl contraction; the converse is not assumed. Define the dimension- and copy-dependent loss

$$
\delta=\delta_{k,l;d,e}
=\min\left\{\frac{d-1}{k+d},\frac{e-1}{l+e}\right\}>0.
\tag{102.6}
$$

The mean $\bar p$ below is the normalized Haar mean over independent pure $a,b$, or the exactly equal weighted finite-design mean under the moments specified in §108. A positive guaranteed success $p_{\min}$ means a lower bound on every tested input's success weight. A mean alone does not supply such a guarantee. The targets keep the original fixed complex labels, and the extra copies are supplied preparations. Mixed tensor powers and unknown states correlated with external references are outside this pure-input contract.

## 103. Symmetric-power moments and Choi normalization

**定义 103.1（Coherent-power input spaces）。** For complex dimension $q$ and a positive integer $t$, write

$$
H_{q,t}=\operatorname{Sym}^t(\mathbb C^q),\qquad
D_{q,t}=\dim H_{q,t}=\binom{q+t-1}{t},
\tag{103.1}
$$

and let $\Pi_{q,t}$ be its orthogonal projector in $(\mathbb C^q)^{\otimes t}$. With normalized Haar pure-state measure,

$$
\int\rho_z^{\otimes t}\,dz=\frac{\Pi_{q,t}}{D_{q,t}}.
\tag{103.2}
$$

For a normalization check, use the occupation basis indexed by $n_1+\cdots+n_q=t$. Independent coordinate phases kill every off-diagonal entry. The squared normalized occupation amplitude has coefficient $t!/\prod_i n_i!$, while the Haar amplitude moment is $(q-1)!\prod_i n_i!/(q+t-1)!$. Their product is $t!(q-1)!/(q+t-1)!=1/D_{q,t}$ on every diagonal entry, proving (103.2).

Use an orthonormal occupation basis for the input-first Choi convention

$$
J_C=\sum_{u,v}|u\rangle\langle v|\otimes C(|u\rangle\langle v|),
\qquad
\operatorname{Tr}(QC(X))
=\operatorname{Tr}\bigl(J_C(X^{\mathsf T}\otimes Q)\bigr).
\tag{103.3}
$$

A complex completely positive map has $J_C\succeq0$. Its Haar mean output trace on the coherent-power family is $\operatorname{Tr}J_C/D_{q,t}$. Coordinate conjugation preserves the symmetric space, so transposing the input moment does not change its identity there. Choi positivity and (103.2) will be used on subnormalized outputs, retaining all input-dependent success weights.

## 104. A finite-copy conjugation bound and its attaining channel

**定理 104.1（Mean conjugate-target overlap on coherent powers）。** Let $C$ be any complex completely positive map from $H_{q,t}$ to $\mathbb C^q$, with target $\rho_z^{\mathsf T}$ on input $\rho_z^{\otimes t}$. Let $\bar p_C$ be its Haar mean output trace and $\bar f_C$ its Haar mean target overlap. Without assuming constant success or trace preservation,

$$
\begin{aligned}
\bar f_C
&=\int\operatorname{Tr}\bigl(\rho_z^{\mathsf T}C(\rho_z^{\otimes t})\bigr)\,dz\\
&=\operatorname{Tr}\left(J_C\frac{\Pi_{q,t+1}}{D_{q,t+1}}\right)
\le\frac{\operatorname{Tr}J_C}{D_{q,t+1}}
=\frac{t+1}{t+q}\bar p_C.
\end{aligned}
\tag{104.1}
$$

A trace-preserving channel on $H_{q,t}$ attains this ratio and has

$$
J_{C_{t,q}}=\frac{D_{q,t}}{D_{q,t+1}}\Pi_{q,t+1},
\qquad
C_{t,q}(\rho_z^{\otimes t})
=\frac{I_q+t\rho_z^{\mathsf T}}{t+q}.
\tag{104.2}
$$

The projector $\Pi_{q,t+1}$ is embedded in $H_{q,t}\otimes\mathbb C^q$.

Proof. In (103.3), input transpose and the conjugated target give the same vector $\overline z$ in all $t+1$ slots. Their Haar moment is the projector in (104.1). Since $0\preceq\Pi_{q,t+1}\preceq I$ and $J_C\succeq0$, taking its trace pairing gives the inequality. The ratio $D_{q,t}/D_{q,t+1}=(t+1)/(t+q)$ and the mean-trace identity in §103 give the last equality. This uses the mean success before any normalization of individual outputs.

For attainment, define on $H_{q,t}$

$$
C_{t,q}(X)=D_{q,t}\int
\langle\overline u^{\otimes t}|X|\overline u^{\otimes t}\rangle
|u\rangle\langle u|\,du.
\tag{104.3}
$$

Each integrand is completely positive. The resolution (103.2) gives $\operatorname{Tr}C_{t,q}(X)=\operatorname{Tr}X$. The input-first Choi operator of (104.3) is

$$
D_{q,t}\int\rho_u^{\otimes(t+1)}\,du
=\frac{D_{q,t}}{D_{q,t+1}}\Pi_{q,t+1},
\tag{104.4}
$$

because transposing its input bra-projector removes the coordinate conjugation. This proves the claimed Choi normalization.

For a coherent input, Haar invariance makes the output scalar on the target ray of $\overline z$ and on its orthogonal complement. Its target overlap from (104.3) is
$D_{q,t}\int|\langle\overline u,z\rangle|^{2(t+1)}du
=D_{q,t}/D_{q,t+1}$ by (103.2) at order $t+1$. Trace one fixes the remaining $q-1$ eigenvalues to $1/(t+q)$, proving the output formula in (104.2). $\square$

The integral describes a finite-dimensional channel. Its positive Choi matrix has a finite Kraus decomposition; a physical continuum of measurement outcomes is not required by the mathematical construction. If a channel on the whole tensor input space is needed, choose a fixed output density $\omega$ and extend it by

$$
C^{\rm ext}_{t,q}(X)
=C_{t,q}(\Pi_{q,t}X\Pi_{q,t})
+\operatorname{Tr}((I-\Pi_{q,t})X)\,\omega.
\tag{104.5}
$$

This discards the off-diagonal blocks and replaces the complementary block. Both terms are completely positive and their traces sum to $\operatorname{Tr}X$, so the extension is trace preserving. It agrees on the coherent pure powers. General mixed tensor powers can have support outside $H_{q,t}$, and this extension supplies no stated approximation guarantee for them.

The pure-copy conjugation channel (104.2)–(104.3), its coefficient $(t+1)/(t+q)$ and the full-space extension (104.5) are established results: V. Brzić, D. Grinko, M. Studziński and M. T. Quintino, [Optimal physical approximations of pure-state cloning and transposition are complementary channels, Theorem 1 and equations (1)–(7)](https://arxiv.org/pdf/2603.23628v3). The parameter correspondence is $N=t$, $d=q$, $K=1$. That theorem optimizes completely positive trace-preserving maps. The direct Choi argument above retains arbitrary input-dependent subnormalized success weights for the mean inequality needed here. The same value is the established optimal pure-copy estimation fidelity of D. Bruß and C. Macchiavello, [Optimal state estimation for d-dimensional quantum systems, equation (16)](https://arxiv.org/pdf/quant-ph/9812016). For $t=1$, (104.2) is the approximate-transpose channel of Buscemi–D’Ariano–Perinotti–Sacchi used in §92, [§2, equations (15), (17)–(18)](https://arxiv.org/pdf/quant-ph/0304175v1).

## 105. Joint processing cannot remove the unmatched-sector mean loss

**引理 105.1（The bad-sector overlap bound with both unknown labels）。** For the normalized unmatched-sector input (102.3), let $\beta_{\rm bad}$ be the Haar mean output trace of the restricted real success map and let $\bar f_{\rm bad}$ be its mean target overlap. Then

$$
\bar f_{\rm bad}\le(1-\delta)\beta_{\rm bad},
\qquad 0\le\beta_{\rm bad}\le1.
\tag{105.1}
$$

The restriction may process all Alice and Bob copies jointly and may have input-dependent success.

Proof. Lemma 96.1 gives the compatible complex restriction of a real Kraus map as

$$
B(X)=\sum_hM_hXM_h^*+\sum_hN_hX^{\mathsf T}N_h^*.
\tag{105.2}
$$

The second term uses full transpose of the entire complex sector. The formula follows from $R_hv=M_hv+N_h\overline v$ and the normalized half mixture of $v,iv$, with no extra coefficient. Arbitrary positive maps are not presumed to have this decomposition.

For the first completely positive component, the actual input is $\rho_a^{\otimes k}\otimes(\sigma_b^{\mathsf T})^{\otimes l}$. Restrict its Choi operator to $H_{d,k}\otimes H_{e,l}$ and denote it by $J\succeq0$. After reordering input/output slots, its mean pure-target tester factors as $R_A\otimes R_B$, where

$$
\begin{aligned}
R_A
&=\int(\rho_a^{\mathsf T})^{\otimes k}\otimes\rho_a\,da
\preceq \frac{I_{H_{d,k}}\otimes I_A}{D_{d,k}},\\
R_B
&=\int\sigma_b^{\otimes(l+1)}\,db
=\frac{\Pi_{e,l+1}}{D_{e,l+1}}
\preceq \frac{I_{H_{e,l}}\otimes I_B}{D_{e,l+1}}.
\end{aligned}
\tag{105.3}
$$

The first inequality uses $\rho_a\preceq I_A$ and the order-$k$ moment. The second is the order-$l+1$ moment. Since both factors are positive, their tensor inequalities combine. If $\beta_M$ is this component's actual mean success trace, its input moment gives $\beta_M=\operatorname{Tr}J/(D_{d,k}D_{e,l})$. Therefore

$$
\bar f_M
\le\frac{\operatorname{Tr}J}{D_{d,k}D_{e,l+1}}
=\frac{l+1}{l+e}\beta_M.
\tag{105.4}
$$

No factorization of the map or its Choi operator was imposed. Thus Alice's unknown copies can be processed as part of a joint input without evading this positive-tester bound.

For the second component of (105.2), the full input transpose changes the vector to $\overline a^{\otimes k}\otimes b^{\otimes l}$. Interchanging the two roles in the same argument gives

$$
\bar f_N\le\frac{k+1}{k+d}\beta_N.
\tag{105.5}
$$

The two nonnegative mean traces obey $\beta_M+\beta_N=\beta_{\rm bad}$, so (105.4)–(105.5) give (105.1) with the minimum loss in (102.6). Separate trace preservation, constant success and independence of the two processing components were not used. Trace nonincrease of the full real map on the normalized sector states gives $\beta_{\rm bad}\le1$. $\square$

## 106. The sharp conditional-error frontier

**定理 106.1（Mean and guaranteed-success necessity）。** If (102.5) holds for every pure local pair, let $\bar p$ be the Haar mean of its actual success weights. For $\bar p>0$,

$$
\epsilon\ge\delta\frac{\max\{0,\bar p-p_0\}}{\bar p}.
\tag{106.1}
$$

The same necessary bound holds with any positive guaranteed success $p_{\min}$ in place of $\bar p$. Under the finite tested moment conditions of §108, it instead holds for that test family's weighted mean and guaranteed success, without assuming correctness on untested states. The maps in Theorem 107.1 attain this frontier with uniform success on all pure local inputs. Thus the optimal deterministic worst conditional error is

$$
\epsilon_{\rm det}^*=\frac{\delta}{M}.
\tag{106.2}
$$

For $k=l=1$, this recovers the single-copy arbitrary-dimension real completely positive attainment and its bound. The positive-map necessity proved in §91 also applies to that single-copy case; the multi-copy theorem here uses real complete positivity.

Proof. For each normalized populated sector $s$, let $\beta_s$ be its Haar mean success trace and $\bar f_s$ its mean target overlap. Positivity gives $\bar f_s\le\beta_s$ and trace nonincrease gives $0\le\beta_s\le1$. There are $M-1$ good sectors and one bad sector, each with input weight $1/M$. Consequently

$$
\bar p=\frac1M\sum_s\beta_s,\qquad
\beta_{\rm bad}\ge\max\{0,M\bar p-(M-1)\}.
\tag{106.3}
$$

Applying Lemma 105.1 on the bad sector and the overlap bound on each other sector yields

$$
\bar f=\frac1M\sum_s\bar f_s
\le\bar p-\frac{\delta}{M}\beta_{\rm bad}.
\tag{106.4}
$$

For any tested pure target, $p(a,b)P_{ab}-E(a,b)$ has trace zero. Its expectation in the pure effect $P_{ab}$ has magnitude at most half its trace norm. Hence (102.5) gives

$$
f(a,b):=\operatorname{Tr}(P_{ab}E(a,b))
\ge(1-\epsilon)p(a,b),
\qquad
\bar f\ge(1-\epsilon)\bar p.
\tag{106.5}
$$

Combining (106.3)–(106.5) proves (106.1). The function $\max(0,p-p_0)/p$ is nondecreasing for $p>0$, so $\bar p\ge p_{\min}>0$ gives the guaranteed-success version. This compares actual subnormalized success means throughout; it never adds separately normalized branch fidelities.

Theorem 107.1 attains equality on all pure labels with success independent of the labels. At $\bar p=1$, necessity and attainment give (106.2). The finite-family form follows from the exact success and overlap moment identities established in §108. $\square$

Exact decoding has mean success at most $p_0$. A positive mean permits zero success on some tested inputs and supplies no per-input guarantee. Zero success assigns no conditional state; the zero map supplies it. For the entire pure family, the pointwise inequality $f\le p$ and the mean argument above need no claim that every sector has state-independent success.

## 107. Explicit real-channel attainment on the pure-copy family

**定理 107.1（Uniform success and exact conditional-error attainment）。** Under either preparation contract in Definition 102.1, for every $0<p\le1$ there is a real completely positive trace-nonincreasing success map with trace exactly $p$ on every supplied pure pair and conditional half trace-norm error exactly

$$
\delta\frac{\max\{0,p-p_0\}}p.
\tag{107.1}
$$

Its outputs on that family are already compatible, so it also attains the same error for the actual normalized real output.

Proof. Use the exact matching map on each good sector. In the bad sector choose the better of the following two channels. One keeps an Alice copy and applies $C_{l,e}$ to Bob's conjugated coherent copies. The other applies full real coordinate conjugation of the whole sector, applies $C_{k,d}$ to Alice's now conjugated copies, and keeps one Bob copy. Their compatible conditional outputs are respectively

$$
\rho_a\otimes\frac{I_e+l\sigma_b}{l+e},
\qquad
\frac{I_d+k\rho_a}{k+d}\otimes\sigma_b.
\tag{107.2}
$$

Both are real completely positive operations: use real lifts of the finite complex Kraus channels from §104, and in the second case the real orthogonal full conjugation. The sector chart isometries, routing, conjugation and local channel dilation are supplied operations for this attaining interface.

For a pure $q$-dimensional target, $(I_q+t\rho)/(t+q)$ has target eigenvalue $(t+1)/(t+q)$ and $q-1$ orthogonal eigenvalues $1/(t+q)$. Its half trace distance from $\rho$ is $(q-1)/(t+q)$. Tensoring with the other pure target density preserves this distance. Thus the two bad outputs in (107.2) have errors $(e-1)/(l+e)$ and $(d-1)/(k+d)$, and selecting the smaller gives $\delta$. The selected output commutes with $P_{ab}$, with target-ray weight $1-\delta$.

For $0<p\le p_0$, reject the bad sector and scale each good success map by $p/p_0$. Its real success effect is $(p/p_0)P_{\rm good}\preceq I$, its output trace is $p$, and its normalized output is exact. For $p_0\le p\le1$, keep all good sectors and accept the bad channel with factor

$$
c=M(p-p_0)\in[0,1].
\tag{107.3}
$$

The direct-sum sector map has success effect $P_{\rm good}+cP_{\rm bad}\preceq I$ on the populated subspace; reject any unpopulated sector. Hence it is real completely positive and trace nonincreasing on the whole input space. Every supplied pure input has total trace $p_0+c/M=p$. Its subnormalized compatible output is $p_0P_{ab}+(c/M)Q_{ab}$, where $Q_{ab}$ is the chosen bad output. Therefore

$$
D\left(\frac{p_0P_{ab}+(c/M)Q_{ab}}p,P_{ab}\right)
=\frac{c}{Mp}D(Q_{ab},P_{ab})
=\delta\frac{p-p_0}p.
\tag{107.4}
$$

This is half trace distance itself. The bad output's eigenvalues also verify directly that the pure-effect overlap loss equals this distance. The output is compatible, so trace-norm preservation of normalized realification gives the same actual real-output distance. This proves (107.1), including zero error on the lower-success interval. $\square$

The channel can discard unselected copies, dilation environments and measurement or routing records. Equality of its output marginal does not assert a clean ready return, free erasure or reference-preserving transfer. Controlled-reference acquisition alone grants neither the sector instrument nor these source operations.

## 108. Finite witnesses and the exact moment order

**定理 108.1（Higher state moments give a finite tested frontier）。** Suppose finite weighted families $\mathcal D_A,\mathcal D_B$ of pure local densities have nonnegative normalized weights and exact moments

$$
\begin{aligned}
\sum_{Q\in\mathcal D_A}w_QQ^{\otimes(k+1)}
&=\frac{\Pi_{d,k+1}}{D_{d,k+1}},\\
\sum_{R\in\mathcal D_B}v_RR^{\otimes(l+1)}
&=\frac{\Pi_{e,l+1}}{D_{e,l+1}}.
\end{aligned}
\tag{108.1}
$$

If (102.5) holds only on their product labels, Theorem 106.1 holds for the product-weighted mean success and for any positive guarantee on this finite family. No conditional-error hypothesis on the untested Haar family is required. Such exact finite families exist, with a product-probe count at most

$$
D_{d,k+1}^{\,2}D_{e,l+1}^{\,2}.
\tag{108.2}
$$

Proof. In either preparation contract, $\eta(a,b)$ has degree $k$ in the entries of $\rho_a$ and degree $l$ in those of $\sigma_b$. Realification and transpose are real-linear and do not increase these degrees. The output trace $p(a,b)$ has those degrees, while the target overlap $f(a,b)$ has degrees $k+1,l+1$. Partial trace of (108.1) gives all lower moments, so the two weighted means of $p,f$ agree exactly with their Haar means. This includes the transposed entries by applying their fixed linear maps to the moment tensor.

On each tested pure pair, (102.5) implies the pure-effect inequality (106.5). Averaging it on the finite product family and replacing only the two means by their Haar values gives $\bar f\ge(1-\epsilon)\bar p$. The Haar mean sector bound (106.4), which holds for every real completely positive map under the copy contract, then proves (106.1) for that finite mean. No nonlinear trace-norm error has been transferred using a design identity. These are complex projective state designs, without a unitary-design assumption or a native unitary command.

For existence in dimension $q$ and degree $t$, the Haar moment $\Pi_{q,t}/D_{q,t}$ lies in the convex hull of the coherent projectors $\rho_z^{\otimes t}$ on $H_{q,t}$. These projectors form a compact set. The trace-one Hermitian affine space on $H_{q,t}$ has real dimension $D_{q,t}^2-1$. Carathéodory's theorem gives a convex combination of at most $D_{q,t}^2$ of these projectors equal to that Haar moment. This is an exact finite weighted state design. Apply it separately at degrees $k+1,l+1$ to prove (108.2). The count is an existence bound, not an optimal catalog, explicit preparation schedule or native resource estimate. $\square$

**推论 108.2（Two qubit copies and the six-state third moment）。** For $d=e=2$ and $k=l=2$, the six equally weighted Pauli pure states on each party give the required moments. Thus $36$ product labels, each with two actual copies per party, suffice to test the sharp frontier. Here

$$
\delta=\frac14,\qquad
p_{0,\rm ind}=\frac78,\qquad p_{0,\rm grp}=\frac12,
\qquad
\epsilon_{\rm det,ind}^*=\frac1{32},\qquad
\epsilon_{\rm det,grp}^*=\frac18.
\tag{108.3}
$$

Proof. In Bloch coordinates, the six states have vectors $\pm e_x,\pm e_y,\pm e_z$. Their first and third moments vanish, and their second moment is $\mathbb E(r_ir_j)=\delta_{ij}/3$. The normalized Haar Bloch sphere has the same moments through degree three. Since $\rho_r=(I+r\cdot\sigma)/2$, its tensor powers through order three are polynomials of that degree in $r$. These moment equalities prove that the six states form a complex projective state $3$-design. Theorem 108.1 applies at $k+1=l+1=3$. Substitution in (102.2), (102.6) and (106.2) gives (108.3). $\square$

This finite family is not a state $4$-design: the six vectors give $\mathbb E r_x^4=1/3$, while the Haar sphere gives $\int_{-1}^1x^4dx/2=1/5$. It cannot be used as a matching higher-moment design for arbitrary larger copy counts. The same $36$ labels appear in the single-copy test, but the present protocol supplies two copies per party at each label. Those label sets specify different physical preparations.

## 109. The two joint-copy contracts have different asymptotic errors

**推论 109.1（Equal qubit counts）。** For $d=e=2$ and $k=l=t\ge1$, the optimal deterministic worst errors in the stated real completely positive pure-input classes are

$$
\epsilon_{\rm det,ind}^*=\frac1{(t+2)2^{2t-1}},
\qquad
\epsilon_{\rm det,grp}^*=\frac1{2(t+2)}.
\tag{109.1}
$$

Proof. The loss in (102.6) is $1/(t+2)$. The independent and grouped sector counts are respectively $2^{2t-1}$ and $2$. Apply (106.2). $\square$

Both errors tend to zero as the supplied copy count grows. At each finite count, $\delta>0$ and $M$ is finite, so deterministic exact universal decoding remains excluded. The independent contract's exponential factor comes from the smaller unmatched-sector weight. It does not improve the universal conjugation channel itself. The internally aligned contract has two relative sectors at every copy count and retains unmatched weight $1/2$.

This distinction is compatible with the equality of one-copy marginals and products having one real symmetric effect on each individual copy. Collective effects within a party and general joint real effects remain outside that compared observation class.

## 110. Attribution and limits of the pure-copy approximation result

**定义 110.1（The approximate multi-copy scope）。** The projectors and sector weights reuse V53 §7, with the exact preparation, matching and chart statements of §§94–99. The real-Kraus restriction is Lemma 96.1. The calibrated controlled-reference ingredient remains the atlas service cited in §101; it does not supply arbitrary source control.

Symmetric-power Haar resolution, the Choi/Kraus framework, finite weighted design existence and the Carathéodory argument are established ingredients. The optimal completely positive trace-preserving pure-copy conjugation channel and its coefficient are reused from Brzić–Grinko–Studziński–Quintino, Theorem 1 and equations (1)–(7), at $N=t$, $d=q$, $K=1$. Their normalization and the required subnormalized-success inequalities are displayed in §§103–108. The pure-copy estimation fidelity is credited to Bruß–Macchiavello equation (16), and the single-copy transpose channel to Buscemi–D’Ariano–Perinotti–Sacchi §2. General Choi/Kraus background is J. Watrous, [The Theory of Quantum Information, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). Shared-phase real simulation is established background, including M. McKague, M. Mosca and N. Gisin, [Simulating Quantum Systems Using Real Hilbert Spaces](https://arxiv.org/pdf/0810.1923), *Phys. Rev. Lett.* **102**, 020505. The application in §§105–109 is the orientation-weighted decoder frontier and its finite-moment test under the stated real input contracts. No priority claim is made for these ingredients or for that conditional application.

The sharp frontier combines the finite-copy conjugation loss with the actual weights of populated orientation sectors. It applies to real completely positive trace-nonincreasing maps, fixed complex labels and supplied pure repeated-state inputs. Arbitrary positive maps, arbitrary mixed tensor powers and arbitrary externally entangled extensions are not covered by the proof. An extension of a channel outside the symmetric subspace does not establish the mixed-input approximation bound.

Implementing an attaining map requires the joint preparation contract, sector instrument, routing, chart operations, any chosen conjugation and the channel dilation. Integrals and finite designs are mathematical descriptions and test conditions; they grant no native state preparation, measurement or random-unitary interface. Trace weights require an additional instrument and Born interpretation to become operational probabilities. No cloning, source-independence law, reference-preserving identity channel or general quantum-origin conclusion follows from this marginal output task.

## 追加锚（本行以下为增补区）

## 111. A full tensor-space formula for repeated mixed densities

**定义 111.1（The marginal-transpose extension）。** The pure-copy channel of §104 has coherent-input action

$$
C_{t,q}(\rho_z^{\otimes t})
=\frac{I_q+t\rho_z^{\mathsf T}}{t+q}.
\tag{111.1}
$$

A mixed density's tensor power can have support outside $\operatorname{Sym}^t(\mathbb C^q)$, so this pure-input formula does not determine its image. For $q\ge2$ and $t\ge1$, define on the entire complex tensor input space

$$
Q_{t,q}(X)=
\frac{\operatorname{Tr}(X)I_q+
\sum_{j=1}^t(\operatorname{Tr}_{\widehat j}X)^{\mathsf T}}{t+q},
\qquad
X\in\operatorname{Herm}((\mathbb C^q)^{\otimes t}).
\tag{111.2}
$$

The partial trace retains only input copy $j$, and transpose is in the fixed local coordinate basis. This map is positive and trace preserving for every $q,t$: a positive input has positive marginal transposes, and the output trace numerator is $(q+t)\operatorname{Tr}X$. On every density $\tau$,

$$
Q_{t,q}(\tau^{\otimes t})
=\frac{I_q+t\tau^{\mathsf T}}{t+q}.
\tag{111.3}
$$

Theorem 112.1 proves that $Q_{t,2}$ is complex completely positive on the whole tensor space for every finite $t$. Theorem 114.1 shows that $Q_{2,q}$ fails complex complete positivity when $q\ge3$. Positivity on the standalone input and a repeated-density formula do not by themselves supply a local channel compatible with an untouched complex reference.

## 112. An elementary full-space qubit Choi proof

**定理 112.1（Complete positivity for every qubit copy count）。** For every $t\ge1$, the map $Q_{t,2}$ is complex completely positive and trace preserving on $(\mathbb C^2)^{\otimes t}$. It therefore has a finite Kraus representation and a real completely positive lift.

Proof. In the input-first Choi convention of §103, let $F_{j,o}$ swap input copy $j$ with the output slot. The Choi matrix of (111.2) is

$$
J_{t,q}=\frac{I+\sum_{j=1}^tF_{j,o}}{t+q}.
\tag{112.1}
$$

The identity term is the Choi matrix of $X\mapsto\operatorname{Tr}(X)I_q$. Each marginal transpose contributes a swap on its input/output pair and identity on every other input. Tracing over the output gives $(q+t)I/(q+t)=I$.

For qubits, use Pauli matrices and put

$$
S_a=\frac12\sum_{j=1}^t\sigma_a^{(j)},\qquad
S^2=\sum_{a=x,y,z}S_a^2,\qquad
A=\sum_{a=x,y,z}S_a\otimes\sigma_a^{(o)}.
\tag{112.2}
$$

These are finite-dimensional matrix definitions. Pauli multiplication and
$[S_a,S_b]=i\sum_c\varepsilon_{abc}S_c$ give

$$
A^2+A=S^2\otimes I_o.
\tag{112.3}
$$

Indeed, the diagonal Pauli products in $A^2$ give $S^2\otimes I_o$. In the cross terms, for each $c$,

$$
i\sum_{a,b}\varepsilon_{abc}S_aS_b
=\frac i2\sum_{a,b}\varepsilon_{abc}[S_a,S_b]
=-S_c,
\tag{112.4}
$$

which supplies $-A$. Also,

$$
\begin{aligned}
S^2
&=\frac{3t}{4}I+\frac12\sum_{i<j}\sum_a
\sigma_a^{(i)}\sigma_a^{(j)}\\
&\preceq\frac{3t}{4}I+\frac{t(t-1)}4I
=\frac{t(t+2)}4I.
\end{aligned}
\tag{112.5}
$$

The inequality uses $\sum_a\sigma_a^{(i)}\sigma_a^{(j)}=2F_{i,j}-I\preceq I$. Thus (112.3) implies

$$
(A+I/2)^2\preceq\frac{(t+1)^2}{4}I,
\qquad
A\succeq-\frac{t+2}{2}I.
\tag{112.6}
$$

The second statement follows by applying the first to each real eigenvalue of the Hermitian matrix $A$. The qubit swap identity now gives

$$
I+\sum_jF_{j,o}=\frac{t+2}{2}I+A\succeq0.
\tag{112.7}
$$

Consequently $J_{t,2}\succeq0$. Along with its output partial trace, this proves complex complete positivity and trace preservation on all input matrices. A finite positive Choi matrix has a finite Kraus decomposition, whose ordinary realification gives the real completely positive lift. $\square$

This establishes the property on the full tensor domain without restricting the input to a symmetric subspace or computing a numerical spectrum. The existence and optimal repeated-mixed-state transpose coefficient are established literature results, as credited in §116. Finite Kraus existence does not supply a gate count, a dilation resource or a native channel command.

## 113. The sharp frontier for arbitrary mixed qubit labels

**定理 113.1（Mixed-qubit worst error with guaranteed success）。** Let $\rho,\sigma$ range over all qubit density matrices, with $k,l\ge1$ supplied copies. Use either preparation contract of Definition 94.1,

$$
\begin{aligned}
\eta_{\rm ind}(\rho,\sigma)
&=(\mathscr R_A(\rho)/2)^{\otimes_{\mathbb R}k}
\otimes_{\mathbb R}(\mathscr R_B(\sigma)/2)^{\otimes_{\mathbb R}l},\\
\eta_{\rm grp}(\rho,\sigma)
&=\iota_{A,k}(\rho^{\otimes_{\mathbb C}k})
\otimes_{\mathbb R}\iota_{B,l}(\sigma^{\otimes_{\mathbb C}l}).
\end{aligned}
\tag{113.1}
$$

Put

$$
h=\max(k,l),\qquad
M_{\rm ind}=2^{k+l-1},\quad M_{\rm grp}=2,\qquad
p_0=1-\frac1M.
\tag{113.2}
$$

The target is the fixed-label aligned density $\iota_{\rm out}(\rho\otimes_{\mathbb C}\sigma)$. For $0<p\le1$, take the infimum over fixed real completely positive trace-nonincreasing maps on the full real copy space whose success weight is at least $p$ on every density pair. Let their error be the supremum, over all these pairs, of the compatible normalized-output half trace distance from $\rho\otimes_{\mathbb C}\sigma$. Then

$$
\epsilon^*_{\rm qubit,mixed}(p)
=\frac1{h+2}\frac{\max\{0,p-p_0\}}p.
\tag{113.3}
$$

The same optimum holds for the stronger requirement on the actual normalized real output. A fixed attaining map has uniform success exactly $p$ on every pair, but its individual mixed-input error can be smaller than the worst value in (113.3).

Proof. The good sectors have exact matching and routing outputs for arbitrary mixed densities by Theorem 95.2 and its grouped counterpart. In the bad sector the complex density is
$\rho^{\otimes k}\otimes(\sigma^{\mathsf T})^{\otimes l}$.

If $l\ge k$, retain one Alice copy and apply $Q_{l,2}$ to Bob's transposed copies. If $k>l$, first apply full real coordinate conjugation on the entire bad complex sector, then apply $Q_{k,2}$ to Alice's now transposed copies and retain one Bob copy. Their conditional bad outputs are respectively

$$
\rho\otimes\frac{I_2+l\sigma}{l+2},
\qquad
\frac{I_2+k\rho}{k+2}\otimes\sigma.
\tag{113.4}
$$

These operations are defined on the full bad real input sector. Theorem 112.1 makes $Q_{t,2}$ complex completely positive on its whole tensor domain, so it can act with the other complex factor untouched before taking the real lift. Full coordinate conjugation, when used, is real orthogonal. No pure-subspace approximation guarantee is used for mixed inputs.

Let $\tau$ be the selected density undergoing approximate conjugation and let

$$
R_\tau=2D(\tau,I_2/2)\in[0,1]
\tag{113.5}
$$

be its Bloch radius, where $D(X,Y)=\|X-Y\|_1/2$ for densities. Tensoring a Hermitian difference with a positive trace-one density preserves trace norm. The bad-output error is therefore exactly

$$
D_{\rm bad}
=\frac2{h+2}D(\tau,I_2/2)
=\frac{R_\tau}{h+2}.
\tag{113.6}
$$

For $0<p\le p_0$, scale the exact good-sector map by $p/p_0$ and reject the bad sector. For $p_0\le p\le1$, retain every good sector and accept the bad channel with factor $c=M(p-p_0)\in[0,1]$. These are the direct sector success maps used in Theorem 107.1, now with the full-domain qubit channel. Their real success effects are respectively $(p/p_0)P_{\rm good}$ and $P_{\rm good}+cP_{\rm bad}$, bounded by the identity; unpopulated sectors are rejected. Their trace on every mixed input is $p$. The normalized output difference is the bad-output difference multiplied by its accepted weight divided by $p$, giving

$$
D_{\rm out}(\rho,\sigma;p)
=\frac{R_\tau}{h+2}\frac{\max\{0,p-p_0\}}p.
\tag{113.7}
$$

This is an exact error identity for this fixed map. Its outputs are already compatible. Since $R_\tau\le1$, it supplies the upper bound in (113.3), and equality in its worst error occurs when the selected local density is pure.

For necessity, every real completely positive map with success at least $p$ on all local densities also has that success on the pure subfamily. Its Haar mean success on that subfamily is at least $p$. Theorem 106.1 and monotonicity of $\max(0,x-p_0)/x$ imply the lower bound in (113.3), because the qubit pure-copy loss is
$\min\{1/(k+2),1/(l+2)\}=1/(h+2)$. This permits input-dependent success in the competing maps and establishes the optimum over the whole mixed family.

For actual normalized real outputs, compatible twirling fixes the target and contracts the trace norm. Thus the same lower bound applies, and the already compatible attainer has exactly the same real and complex error by trace-norm preservation of normalized realification. This proves both stated optima. $\square$

At $p=1$, the worst errors are $1/[(h+2)2^{k+l-1}]$ for independent realification and $1/[2(h+2)]$ for internally aligned groups. For $k=l=2$ they are $1/32$ and $1/8$. If the selected factor is maximally mixed, $R_\tau=0$ and this map has zero error even at $p=1$. This does not assert pointwise optimality for every mixed pair and does not change the guaranteed worst error.

For an internally aligned grouped input embedded in the larger real copy space, the map may reject the orthogonal unpopulated support. If a trace-preserving channel on that larger space is desired at $p=1$, replace that support by a fixed output density after discarding off-diagonal blocks. This completes the channel without changing its action on the stated inputs.

The finite pure-state designs of §108 remain lower-bound witnesses for this larger mixed-input task. Their readings alone do not certify a map's behavior on all mixed inputs. The mixed upper guarantee is supplied by Theorem 112.1 and the exact identity (113.7), while the lower guarantee uses the pure subfamily.

## 114. A qutrit reference detects failure of the same local formula

**定理 114.1（Two-copy higher-dimensional complex reference obstruction）。** For $q\ge3$, the positive trace-preserving map $Q_{2,q}$ of (111.2) is not complex completely positive. A three-dimensional reference and an explicit valid encoded input give a negative output effect reading.

Proof. Choose a unit vector in $\bigwedge^3(\mathbb C^3)$, embedded in the two-input-plus-output space $(\mathbb C^q)^{\otimes3}$. Both input/output swaps in (112.1) act as $-I$, so

$$
\langle\omega|J_{2,q}|\omega\rangle
=-\frac1{q+2}<0.
\tag{114.1}
$$

For a direct reference witness, define the real-coordinate isometry from $\mathbb C^3$ to the first three coordinates of two input copies by

$$
\begin{aligned}
V|0\rangle&=(|12\rangle-|21\rangle)/\sqrt2,\\
V|1\rangle&=(|20\rangle-|02\rangle)/\sqrt2,\\
V|2\rangle&=(|01\rangle-|10\rangle)/\sqrt2.
\end{aligned}
\tag{114.2}
$$

Let $\Pi_3$ project onto those three local coordinates. For every $3$-by-$3$ matrix $X$, both ordinary complex marginals satisfy

$$
\operatorname{Tr}_1(VXV^*)=\operatorname{Tr}_2(VXV^*)
=\frac{\operatorname{Tr}(X)\Pi_3-X^{\mathsf T}}2.
\tag{114.3}
$$

To verify the entries, write $V_{ij,r}=\varepsilon_{rij}/\sqrt2$ and use
$\sum_j\varepsilon_{rij}\varepsilon_{skj}
=\delta_{rs}\delta_{ik}-\delta_{rk}\delta_{is}$.
The resulting marginal entry is
$(\operatorname{Tr}(X)\delta_{ik}-X_{ki})/2$ on the three-coordinate subspace, and zero elsewhere. The second marginal agrees because the encoded support is antisymmetric. Substituting these two marginal transposes into (111.2) yields

$$
Q_{2,q}(VXV^*)
=\frac{\operatorname{Tr}(X)(I_q+\Pi_3)-X}{q+2},
\tag{114.4}
$$

where $X$ in the output is embedded in that same three-dimensional subspace.

Let $\Omega_3$ be the normalized maximally entangled density between an actual reference $\mathbb C^3_R$ and this three-dimensional input, and put
$Z=(I_R\otimes V)\Omega_3(I_R\otimes V^*)$.
It is a positive trace-one joint input. Equation (114.4) gives

$$
\begin{aligned}
(\operatorname{id}_R\otimes Q_{2,q})(Z)
&=\frac{(I_R/3)\otimes(I_q+\Pi_3)-\Omega_3}{q+2},\\
\operatorname{Tr}\!\left[
\Omega_3(\operatorname{id}_R\otimes Q_{2,q})(Z)
\right]
&=-\frac1{3(q+2)}.
\end{aligned}
\tag{114.5}
$$

Here the output occurrence of $\Omega_3$ uses the reference and the three-coordinate output subspace. Its expectation in the first numerator term is $2/3$, while its expectation in itself is $1$, giving the negative value. Thus the proposed local action fails positivity with that reference. At $q=3$ the reading is $-1/15$. $\square$

The witness is a full-domain test with an antisymmetric encoded input. It is not a counterexample within the restricted preparation family $\tau\otimes\tau$. It rules out the specified local complex channel correspondence, while the map remains positive and trace preserving on its standalone input.

## 115. A standalone real lift does not install a fixed-chart local action

**命题 115.1（Real lift of the marginal-transpose mixture）。** For every $q,t$, $Q_{t,q}$ admits a real completely positive trace-preserving lift between the standalone realifications of its entire complex input and output, even when $Q_{t,q}$ is not complex completely positive.

Proof. Define the average marginal channel and the replacement channel by

$$
\mathcal M_t(X)=\frac1t\sum_j\operatorname{Tr}_{\widehat j}X,
\qquad
\mathcal R_{I_q/q}(X)=\operatorname{Tr}(X)I_q/q.
\tag{115.1}
$$

Both are complex completely positive and trace preserving, and

$$
Q_{t,q}
=\frac q{t+q}\mathcal R_{I_q/q}
+\frac t{t+q}\,T\circ\mathcal M_t.
\tag{115.2}
$$

In the fixed coordinate bases, partial-trace Kraus matrices can be chosen real, and
$T\circ\mathcal M_t=\mathcal M_t\circ T_{\rm all}$, where $T_{\rm all}$ is full input transpose. Thus the second term is completely positive after full transpose of the entire complex input.

Realify the replacement Kraus matrices for the first term. For the second, realify the marginal Kraus matrices and precede them by full real coordinate conjugation on the input. That conjugation is a real orthogonal map and implements $T_{\rm all}$ on compatible realified densities. Each unweighted Kraus family has squared sum equal to the real input identity. Multiplying them by the square roots of the two nonnegative weights in (115.2) makes their combined squared sum
$[q/(t+q)+t/(t+q)]I=I$.
This gives a real completely positive trace-preserving lift and its stated compatible action on standalone realified inputs. $\square$

For $q\ge3$, this standalone lift does not supply $\operatorname{id}_R\otimes Q_{2,q}$ on a preselected aligned complex joint carrier while preserving the reference. Equation (114.5) forbids that correspondence as a positive map on the full complex joint cone. Tensoring a standalone real lift with a real identity remains a real completely positive operation, but separate realification and restriction to a fixed common complex tensor chart are distinct constructions. Their correspondence is an additional condition and fails for the asserted local action in Theorem 114.1.

For qubits, Theorem 112.1 supplies the stronger complex complete positivity used in Theorem 113.1. It permits the qubit channel to act with the other complex factor untouched before realification. The higher-dimensional witness does not exclude a different full-space extension of the symmetric pure-copy channel with a different mixed-input action, a different joint real decoder on repeated-state inputs or a mixed-state frontier proved by another method. The joint decoder questions in those larger classes remain unresolved by this argument.

## 116. The established mixed-state transpose ingredient

**定义 116.1（Literature scope and the parameter correspondence）。** The existence and maximal mixed-state transpose visibility are established in V. Brzić, D. Grinko, M. Studziński and M. T. Quintino, [Optimal physical approximations of pure-state cloning and transposition are complementary channels, Theorem 3, equations (16)–(18), and Appendix D](https://arxiv.org/pdf/2603.23628v3). In their notation $N=t$ and $d=q$. For a complex completely positive trace-preserving channel required to have

$$
C_t(\tau^{\otimes t})
=\eta\tau^{\mathsf T}+(1-\eta)I_q/q
\quad\text{for every density }\tau,
\tag{116.1}
$$

their maximal visibility is

$$
\eta_{\max}=
\begin{cases}
1/(q+1),&t\le q-1,\\
t/[q(q-1)+t],&t\ge q-1.
\end{cases}
\tag{116.2}
$$

The two expressions agree at the common endpoint. At $q=2$, this is $\eta_{\max}=t/(t+2)$, and (111.3) is precisely that repeated-state output. Appendix D constructs the averaged swap Choi operator for the noisy transpose and derives its permitted visibility from the spectrum of the swap sum. The elementary qubit calculation in §112 proves directly the full-space complete positivity needed for the decoder.

The literature theorem concerns existence and optimal visibility within the prescribed local repeated-density transpose form. It does not by itself optimize arbitrary joint real success decoders with input-dependent success. The worst-error optimum in Theorem 113.1 uses the full-domain channel for attainment and the separate pure-subfamily lower bound of Theorem 106.1. No priority claim is made for the channel, its qubit coefficient or the standard Pauli, swap, transpose and Choi ingredients.

The orientation algebra and input contracts reuse §§94–99, ultimately V53 §7. The pure-copy lower frontier and its primary attribution are §§104–110. General Choi/Kraus and transpose/swap facts are described in J. Watrous, [The Theory of Quantum Information, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). Shared-phase real simulation is established background, including M. McKague, M. Mosca and N. Gisin, [Simulating Quantum Systems Using Real Hilbert Spaces](https://arxiv.org/pdf/0810.1923), *Phys. Rev. Lett.* **102**, 020505. The displayed arguments expose the use of these ingredients in the mixed-qubit decoder and the stated reference-interface obstruction.

## 117. Preparation and implementation limits for mixed-copy decoding

**定义 117.1（The mixed-copy and reference-interface boundary）。** The sharp mixed-state frontier here is for qubit local densities, supplied finite copies, fixed complex labels, one selected output per party and fixed real completely positive trace-nonincreasing maps on the full real copy space. Its two preparation contracts carry the populated sector weights in (113.2). Equality of their local observations is the per-individual-copy product-effect statement of Theorem 99.1; it asserts no equality for collective effects within either party or general joint real effects.

Implementing the attaining decoder requires the stated joint preparation, sector instrument, within-type routing, any chosen full coordinate conjugation and the local channel dilation. These operations are not consequences of the calibrated controlled-reference menu. Unselected copies, dilation environments and routing or syndrome records are retained or discarded according to that supplied interface. The specified output density does not imply a clean ready return or free erasure.

The qutrit witness tests a different, explicit joint-reference interface on the full complex cone. It does not convert positivity of a standalone real lift into the required fixed-chart local correspondence and does not disprove every higher-dimensional mixed-state joint decoder. Neither the mixed-qubit attaining decoder nor its output formula asserts preservation of arbitrary external-reference correlations.

Finite copies are supplied resources, without a cloning operation. Trace weights become operational success probabilities only under an additional instrument and Born contract. The results supply no source-independence law or general quantum-origin conclusion.

## 追加锚（本行以下为增补区）

## 118. Choosing the nonsymmetric block of a two-copy channel

**定义 118.1（Symmetric and exterior-square input blocks）。** Let $H=\mathbb C^q$ with $q\ge3$. Let $F$ swap the two input copies, put $P_\pm=(I\pm F)/2$, and write $X_\pm=P_\pm XP_\pm$ for an arbitrary matrix on $H\otimes_{\mathbb C}H$. All transposes below use fixed coordinate bases. Define

$$
\begin{aligned}
\mathcal S_q(Y)
&=\frac{\operatorname{Tr}(Y)I_q+
(\operatorname{Tr}_1Y)^{\mathsf T}
+(\operatorname{Tr}_2Y)^{\mathsf T}}{q+2},
&&Y=P_+YP_+,\\
\mathcal A_q(Y)
&=\frac{\operatorname{Tr}(Y)I_q-
(\operatorname{Tr}_1Y)^{\mathsf T}
-(\operatorname{Tr}_2Y)^{\mathsf T}}{q-2},
&&Y=P_-YP_-,\\
\widehat C_{2,q}(X)&=\mathcal S_q(X_+)+\mathcal A_q(X_-).
\end{aligned}
\tag{118.1}
$$

The symmetric input block is $\operatorname{Sym}^2H$ and the antisymmetric block is $\bigwedge^2H$. Theorem 119.1 proves complex complete positivity and trace preservation on the two blocks and hence on the entire input tensor space. Discarding cross-block coherences is part of this linear channel.

On a pure power the antisymmetric block vanishes, giving

$$
\widehat C_{2,q}(\rho_z^{\otimes2})
=\frac{I_q+2\rho_z^{\mathsf T}}{q+2}.
\tag{118.2}
$$

This is the established pure-power conjugation action of §104 at $t=2$. The new full-space formula has a different nonsymmetric action from $Q_{2,q}$ in §111. The reference obstruction to that particular $Q_{2,q}$ remains valid and does not apply to the different channel (118.1).

## 119. Positive Choi projectors and finite antisymmetric Kraus operators

**定理 119.1（The two-block map is a full complex channel）。** For $q\ge3$, $\mathcal S_q$ and $\mathcal A_q$ are complex completely positive and trace preserving on their respective input blocks. Thus $\widehat C_{2,q}$ is complex completely positive and trace preserving on all $H\otimes H$, including with untouched complex references.

Proof. Let $\Pi_{{\rm sym},3}$ and $\Pi_{{\rm alt},3}$ project onto $\operatorname{Sym}^3H$ and $\bigwedge^3H$ in the two-input/output triple tensor product. In the input-first Choi convention,

$$
J_{\mathcal S_q}=\frac3{q+2}\Pi_{{\rm sym},3},
\qquad
J_{\mathcal A_q}=\frac3{q-2}\Pi_{{\rm alt},3}.
\tag{119.1}
$$

The block embeddings and projectors are real in the coordinate bases. Thus their input transposes introduce no different embedding. To check the identities, let $F_{13},F_{23}$ swap each input with the output. The swap Choi identity gives the block compressions of $I+F_{13}+F_{23}$ and $I-F_{13}-F_{23}$. The six permutations of three tensor slots yield

$$
\begin{aligned}
(P_+\otimes I)(I+F_{13}+F_{23})(P_+\otimes I)
&=3\Pi_{{\rm sym},3},\\
(P_-\otimes I)(I-F_{13}-F_{23})(P_-\otimes I)
&=3\Pi_{{\rm alt},3}.
\end{aligned}
\tag{119.2}
$$

Indeed, $F_{13}+F_{23}$ commutes with the input swap $F_{12}$, so the two block projections can be combined. Expanding the first compression gives half the sum of the identity, the three transpositions and the two three-cycles. Expanding the second gives half their alternating sum. These are three times the corresponding permutation projectors, proving (119.1).

Tracing over the output in (119.2), each swap has output trace $I$ and the identity has output trace $qI$. Consequently

$$
\operatorname{Tr}_o\Pi_{{\rm sym},3}
=\frac{q+2}{3}P_+,
\qquad
\operatorname{Tr}_o\Pi_{{\rm alt},3}
=\frac{q-2}{3}P_-.
\tag{119.3}
$$

The positive Choi matrices in (119.1) therefore have output traces $P_+,P_-$, proving block trace preservation. Their sum has output trace $I$ on the full two-copy space. The compressed-input construction discards cross-block terms and is completely positive, so it defines the stated full channel. $\square$

**命题 119.2（Explicit exterior-square Kraus family）。** Write $|i\wedge j\rangle=(|ij\rangle-|ji\rangle)/\sqrt2$ for $i<j$. For each $i<j<k$, define

$$
K_{ijk}=
\frac{
|i\rangle\langle j\wedge k|
-|j\rangle\langle i\wedge k|
+|k\rangle\langle i\wedge j|
}{\sqrt{q-2}}.
\tag{119.4}
$$

Then

$$
\sum_{i<j<k}K_{ijk}^*K_{ijk}=I_{\wedge^2H},
\qquad
\mathcal A_q(Y)=\sum_{i<j<k}K_{ijk}YK_{ijk}^*.
\tag{119.5}
$$

Proof. Within each triple the three output vectors in (119.4) are orthogonal, so its squared Kraus operator is the sum of the three input wedge-pair projectors divided by $q-2$. Each wedge pair occurs in exactly $q-2$ triples. Summing gives the first equality.

For the second, the input-first Choi vector of $K_{ijk}$ is $\sqrt{3/(q-2)}$ times the normalized alternating three-slot vector on coordinates $i,j,k$. These alternating vectors are orthonormal as the triple varies, so the Kraus Choi matrix is $3\Pi_{{\rm alt},3}/(q-2)$, equal to (119.1). Thus it is the same channel. $\square$

In particular, an input coordinate wedge pair is sent uniformly to the $q-2$ coordinate directions outside that pair. The complete positivity statement is on the whole block, rather than a positivity test restricted to repeated-state inputs.

The symmetric block is the established optimal pure-copy transpose channel in Brzić–Grinko–Studziński–Quintino, [Theorem 1 and equations (1)–(7)](https://arxiv.org/pdf/2603.23628v3), at $N=2$, $d=q$, $K=1$, as credited in §104. Its Choi coefficient is $D_{q,2}/D_{q,3}=3/(q+2)$. The displayed permutation and Kraus calculations specify the additional antisymmetric block used here.

## 120. The exact output on a repeated mixed density

**命题 120.1（Quadratic repeated-state action）。** Let $\tau$ be any density on $\mathbb C^q$, $q\ge3$, with eigenvalues $\lambda_i$, and put $P=\operatorname{Tr}(\tau^2)$. Define

$$
s=\operatorname{Tr}(P_+\tau^{\otimes2})=\frac{1+P}{2},
\qquad
a=\operatorname{Tr}(P_-\tau^{\otimes2})=\frac{1-P}{2}.
\tag{120.1}
$$

Then

$$
\widehat C_{2,q}(\tau^{\otimes2})
=\frac{sI_q+(\tau+\tau^2)^{\mathsf T}}{q+2}
+\frac{aI_q-(\tau-\tau^2)^{\mathsf T}}{q-2}.
\tag{120.2}
$$

It commutes with the target $\tau^{\mathsf T}$, and its eigenvalues in a common eigenbasis are

$$
y_i=\frac{q-2P-4\lambda_i+2q\lambda_i^2}{q^2-4}.
\tag{120.3}
$$

Proof. The repeated input commutes with the swap. The swap trace identities give $\operatorname{Tr}(F\tau^{\otimes2})=\operatorname{Tr}(\tau^2)$ and, for either retained factor,
$\operatorname{Tr}_{\widehat j}(F\tau^{\otimes2})=\tau^2$.
Hence the block traces are (120.1), and both marginals of the symmetric and antisymmetric blocks are respectively $(\tau+\tau^2)/2$ and $(\tau-\tau^2)/2$. Substituting into (118.1) gives (120.2). Combining its scalar, linear and quadratic eigenvalue terms over the denominator $q^2-4$ gives (120.3).

The eigenvalues sum to one by trace preservation. Positivity follows from Theorem 119.1; for the antisymmetric contribution it is also explicit:

$$
a-\lambda_i+\lambda_i^2
=\sum_{\substack{j<k\\j,k\ne i}}\lambda_j\lambda_k\ge0.
\tag{120.4}
$$

The symmetric contribution is nonnegative term by term. $\square$

For a pure density (120.2) reduces to (118.2). For a mixed density it generally differs from $(I_q+2\tau^{\mathsf T})/(q+2)$. The quadratic terms are part of the repeated-state action of a channel linear in the full tensor input $X$. They do not postulate a nonlinear quantum channel.

## 121. The all-mixed worst error and rank-two equality cases

**定理 121.1（Two-copy mixed minimax value for $q\ge3$）。** For the channel (118.1),

$$
\sup_\tau D\bigl(\widehat C_{2,q}(\tau^{\otimes2}),\tau^{\mathsf T}\bigr)
=\frac{q-1}{q+2},
\qquad D(U,V)=\frac12\|U-V\|_1.
\tag{121.1}
$$

This is also the minimum possible worst error among full-space complex completely positive trace-preserving channels with the same repeated-density target. Every pure density attains the displayed error. For $q\ge3$, every density uniform on a two-dimensional subspace also attains it.

Proof. Since output and target commute, their trace distance is the maximum eigenvalue-mass deficit $\sum_{i\in S}(\lambda_i-y_i)$ over all subsets $S$. The empty and full subsets have zero deficit. For a nonempty proper subset, set

$$
r=|S|,\qquad w=\sum_{i\in S}\lambda_i,\qquad
U=\sum_{i\in S}\lambda_i^2,\qquad
V=\sum_{i\notin S}\lambda_i^2.
\tag{121.2}
$$

Here $1\le r\le q-1$ and $0\le w\le1$. Summing (120.3), with $P=U+V$, gives

$$
\sum_{i\in S}(\lambda_i-y_i)
=\frac{q^2w-rq-2(q-r)U+2rV}{q^2-4}.
\tag{121.3}
$$

Cauchy–Schwarz gives $U\ge w^2/r$, while nonnegative eigenvalues give $V\le(1-w)^2$. The numerator is therefore bounded above by

$$
F_r(w)=q^2w-rq-\frac{2(q-r)}r w^2+2r(1-w)^2.
\tag{121.4}
$$

Its derivative is affine in $w$, with endpoint values

$$
F_r'(0)=q^2-4r\ge(q-2)^2,
\qquad
F_r'(1)=q^2+4-\frac{4q}{r}\ge(q-2)^2.
\tag{121.5}
$$

These use $r\le q-1$ and $r\ge1$, respectively. Thus $F_r$ is increasing on $[0,1]$. Consequently

$$
F_r(w)\le F_r(1)
=(q-r)\left(q-\frac2r\right)
\le(q-1)(q-2).
\tag{121.6}
$$

The difference in the last inequality is $q(r-1)(r-2)/r\ge0$, because $r$ is an integer at least one. It vanishes at $r=1,2$. Dividing by $q^2-4$ and taking the maximum over subsets gives the upper bound in (121.1).

The pure-state formula (118.2) attains the bound. If $\tau=(|i\rangle\langle i|+|j\rangle\langle j|)/2$ with $i\ne j$, then (120.3) gives

$$
y_i=y_j=\frac3{2(q+2)},\qquad
y_h=\frac{q-1}{q^2-4}\quad(h\notin\{i,j\}).
\tag{121.7}
$$

Since $q\ge3$, its two-element support is a proper subset. Its mass deficit is $1-3/(q+2)=(q-1)/(q+2)$, proving the claimed mixed equality cases. The argument depends only on eigenvalues, so it applies to every uniform rank-two density.

For any competing complex completely positive trace-preserving channel, restriction to pure powers allows Theorem 104.1 at $t=2$. The mean target overlap is at most $3/(q+2)$. Half trace distance to a pure target is at least one minus that overlap, so the worst error on pure powers is at least $(q-1)/(q+2)$. Pure powers belong to the full mixed family. This proves the same lower bound for that family and establishes the minimax claim. $\square$

Mixed inputs therefore need not have strictly smaller error than the pure worst case. The rank-two equality statement is for $q\ge3$; it is not a qubit mixed-state equality assertion.

## 122. The qubit and one-copy cases

**命题 122.1（Full channels for one or two copies in every dimension）。** For every $q\ge2$ and $t\in\{1,2\}$, there is a full-space complex completely positive trace-preserving channel with

$$
\sup_\tau D\bigl(\widehat C_{t,q}(\tau^{\otimes t}),\tau^{\mathsf T}\bigr)
=\frac{q-1}{t+q}.
\tag{122.1}
$$

Proof. For $t=2$ and $q\ge3$, use Theorem 121.1. For $q=2$, use the full-space channel of Theorem 112.1 at $t=2$,

$$
\widehat C_{2,2}(X)
=\frac{\operatorname{Tr}(X)I_2+
(\operatorname{Tr}_1X)^{\mathsf T}
+(\operatorname{Tr}_2X)^{\mathsf T}}4.
\tag{122.2}
$$

Its action on repeated densities is $(I_2+2\tau^{\mathsf T})/4$.

There is also a direct two-block construction for that repeated-input action: use the symmetric formula $\mathcal S_2$ from the first line of (118.1) at $q=2$ and replace the one-dimensional antisymmetric block by its trace times $I_2/2$. Both branches are complex completely positive and trace preserving on their blocks. For a trace-one qubit density, Cayley–Hamilton gives $\tau^2=\tau-\det(\tau)I_2$. The symmetric block has trace $s=1-\det(\tau)$ and the antisymmetric block has trace $a=\det(\tau)$. Its repeated output is

$$
\frac{sI_2+(\tau+\tau^2)^{\mathsf T}}4
+aI_2/2
=\frac{I_2+2\tau^{\mathsf T}}4.
\tag{122.3}
$$

Thus this block route supplies the same repeated-density guarantee. Its distance to $\tau^{\mathsf T}$ is $D(\tau,I_2/2)/2\le1/4$, with equality for pure $\tau$.

For $t=1$ and any $q\ge2$, use the standard approximate-transpose channel

$$
\widehat C_{1,q}(X)
=\frac{\operatorname{Tr}(X)I_q+X^{\mathsf T}}{q+1}.
\tag{122.4}
$$

Its Choi matrix is $(I+F)/(q+1)\succeq0$, and its output trace is $\operatorname{Tr}X$. Its error on a density is $qD(\tau,I_q/q)/(q+1)$. Convexity and pure-state eigenvalues give $D(\tau,I_q/q)\le1-1/q$, with equality for pure densities. This proves (122.1) in the remaining case. $\square$

The one-copy channel is the Buscemi–D’Ariano–Perinotti–Sacchi ingredient cited in §92, and the qubit repeated-state coefficient is the established mixed-transpose value cited in §116.

## 123. A sharp all-mixed real decoder when each party supplies one or two copies

**定理 123.1（Arbitrary local dimensions with $k,l\in\{1,2\}$）。** Let $d,e\ge2$ and let $k,l$ each be one or two. Supply either of the independent-copy or internally aligned preparation contracts of Definition 94.1 for arbitrary local densities $\rho,\sigma$. Put

$$
M_{\rm ind}=2^{k+l-1},\qquad M_{\rm grp}=2,\qquad
p_0=1-\frac1M,\qquad
\delta=\min\left\{\frac{d-1}{k+d},\frac{e-1}{l+e}\right\}.
\tag{123.1}
$$

For $0<p\le1$, consider all fixed real completely positive trace-nonincreasing maps on the full real input cone with success weight at least $p$ on every supplied density pair. Their minimum worst conditional half trace-norm error, for the fixed-label output $\rho\otimes_{\mathbb C}\sigma$, is

$$
\epsilon^*_{\rm mixed}(p)
=\delta\frac{\max\{0,p-p_0\}}p.
\tag{123.2}
$$

The statement holds for compatible output error and for actual normalized real-output error. It is a worst-case optimum over the full stated real success-map class; it does not assert pointwise optimality for each mixed pair.

Proof. Every good populated sector has an exact matching-and-routing output for mixed densities. In the unique bad sector the complex input is
$\rho^{\otimes k}\otimes(\sigma^{\mathsf T})^{\otimes l}$.
One may retain an Alice copy and apply $\widehat C_{l,e}$ to Bob's conjugated copies. Alternatively, apply full real coordinate conjugation of the entire sector, use $\widehat C_{k,d}$ on Alice's now conjugated copies and retain one Bob copy. Choose the side giving the smaller term in (123.1).

The local maps in Proposition 122.1 are complex completely positive on their full tensor domains, so they act with the retained complex factor untouched. Their real lifts are real completely positive, and the optional full coordinate conjugation is real orthogonal. The bound on the selected transposed density is unchanged by transposing its label. Tensoring the output difference with the other positive trace-one density preserves its trace norm. Thus the bad conditional output has error at most $\delta$ for every mixed pair and exactly $\delta$ for every pure pair.

For $0<p\le p_0$, reject the bad sector and scale the exact good-sector map by $p/p_0$. For $p_0\le p\le1$, keep every good sector and accept the bad channel with factor $c=M(p-p_0)\in[0,1]$. These direct sector maps have real success effects $(p/p_0)P_{\rm good}$ and $P_{\rm good}+cP_{\rm bad}$, respectively; unpopulated sectors can be rejected. Hence they are real completely positive and trace nonincreasing on the whole real cone. Their trace on every density pair is exactly $p$.

In the upper-success interval the compatible subnormalized output is $p_0(\rho\otimes\sigma)+(c/M)Q_{\rho,\sigma}$, where $Q_{\rho,\sigma}$ is the normalized bad output. Consequently its normalized error is

$$
D_{\rm out}(\rho,\sigma;p)
=\frac{\max\{0,p-p_0\}}p
D(Q_{\rho,\sigma},\rho\otimes\sigma)
\le\delta\frac{\max\{0,p-p_0\}}p.
\tag{123.3}
$$

The lower-success interval has zero error. Pure pairs attain the displayed worst bound, proving attainment with uniform success.

For necessity, a competing map with guaranteed success $p$ and worst error $\epsilon$ on all densities has the same guarantees on pure pairs. Its Haar mean pure-input success is at least $p$. Theorem 106.1, including both complex-linear and complex-antilinear real Kraus components, and monotonicity of $\max(0,u-p_0)/u$ give the lower bound in (123.2). This allows input-dependent success in every competing map. Twirl contraction gives the same lower bound for actual normalized real outputs, and the compatible attaining maps have identical real and complex distances. $\square$

For $k=l=2$, deterministic independent-copy error is
$\min\{(d-1)/(d+2),(e-1)/(e+2)\}/8$,
and grouped error is the same minimum divided by two. At $d=e=3$ these values are $1/20$ and $1/5$. At $d=e=2$ they are $1/32$ and $1/8$, agreeing with §113.

For larger copy counts, discarding surplus copies inside the branches after the orientation-sector step supplies an upper bound using $\min(k,2)$ and $\min(l,2)$ in the local loss terms while keeping the original sector count $M$. This does not in general match the larger-copy pure lower bound. Theorem 113.1 already treats all qubit copy counts; no sharp arbitrary-copy mixed frontier in nonqubit dimensions is inferred here.

## 124. The qutrit antisymmetric reference block is transmitted exactly

**命题 124.1（The changed qutrit block preserves its encoded reference）。** At $q=3$, take the same coordinate isometry as in (114.2), written in wedge notation:

$$
V|0\rangle=|1\wedge2\rangle,\qquad
V|1\rangle=-|0\wedge2\rangle,\qquad
V|2\rangle=|0\wedge1\rangle.
\tag{124.1}
$$

Then, for every matrix $X$ on $\mathbb C^3$,

$$
\mathcal A_3(VXV^*)=X.
\tag{124.2}
$$

Proof. The only triple in (119.4) is $0,1,2$, and $q-2=1$. Its Kraus matrix is exactly $K_{012}=V^*$. Since $V^*V=I_3$, equation (119.5) gives
$\mathcal A_3(VXV^*)=V^*VXV^*V=X$. $\square$

Tensoring this identity with the identity on an arbitrary complex reference transmits every state encoded in this antisymmetric block. In particular the maximally entangled reference input of Theorem 114.1 is transmitted exactly. The former map $Q_{2,3}$ had a negative output effect reading on that input. The present channel agrees with its symmetric action and changes the antisymmetric action, so those two conclusions concern different full-space maps.

Complex complete positivity permits this local channel to act with untouched complex references. The entire orientation decoder additionally measures sectors, selects and discards copies, handles records and may use full real conjugation. It does not inherit an identity action on arbitrary external-reference extensions from this one block identity.

## 125. Pure-copy reuse and the fixed-SPA distinction

**定义 125.1（Which literature optimum is reused）。** The symmetric block and its pure-copy coefficient are the $N=2$, $d=q$, $K=1$ case of Brzić–Grinko–Studziński–Quintino, [Theorem 1 and equations (1)–(7)](https://arxiv.org/pdf/2603.23628v3). Their mixed-state result, Theorem 3 and Appendix D, optimizes the fixed affine repeated-density action
$\tau^{\otimes t}\mapsto\eta\tau^{\mathsf T}+(1-\eta)I_q/q$
described in §116.

For $q\ge3$, (120.2) generally contains both $\tau^2$ and $\operatorname{Tr}(\tau^2)$ and does not have that fixed affine form on mixed states. It is still a linear completely positive map of the full input $X$. Thus its pure-copy coefficient $2/(q+2)$ and its mixed trace-distance guarantee do not contradict the fixed-SPA visibility maximum in (116.2). For example at $q=3$, a uniform rank-two input has output eigenvalues $(3/10,3/10,2/5)$, while the direct affine formula $(I_3+2\tau^{\mathsf T})/5$ gives $(2/5,2/5,1/5)$ in the same eigenbasis.

The pure-copy overlap lower bound in §104 gives the local minimax necessity in Theorem 121.1. The real joint decoder necessity in Theorem 123.1 uses the stronger orientation-weighted pure-family argument of §§105–106, with its real-Kraus decomposition and actual success means. Neither conclusion follows solely from the literature's fixed-affine mixed-SPA optimum.

The Choi criterion, exterior powers, permutation projectors and conjugate-representation channels are standard ingredients. Choi/Kraus and transpose/swap background is J. Watrous, [The Theory of Quantum Information, Chapter 2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf). The block and trace-distance calculations required here are displayed explicitly. No priority claim is made for the ingredients or for the conditional mixed-copy decoding application.

## 126. The settled copy range and its implementation boundary

**定义 126.1（Two-copy mixed decoding scope）。** The all-mixed sharp real-decoder statement of Theorem 123.1 has $k,l\in\{1,2\}$ and arbitrary $d,e\ge2$. The exterior-block construction and uniform rank-two equality cases in §§118–121 have $q\ge3$. The qubit route is the separate channel of §122, with the broader all-count qubit result in §113. Higher nonqubit copy counts are not settled by the two-copy construction.

The preparation contracts, normalized real tensor charts and matching operations reuse §§94–99, ultimately V53 §7. Their equality of local observations concerns products with one real symmetric effect on each individual copy, without an equality assertion for collective effects within a party or general joint real effects. The relative-sector weights are joint-input assumptions and do not follow from local tomography.

Implementation requires the stated copies, sector instruments, within-type routing, chart operations, any chosen real conjugation and the local channel dilations. The controlled-reference service cited in §101 grants only its specified interface. Unselected copies, environments and controller or syndrome records are retained or discarded according to the supplied operations; no clean ready return or free reset is inferred.

The corrected complex channel acts with arbitrary untouched complex references on its own full tensor domain. The real decoder's stated task is its fixed-label output marginal on the supplied family, with no assertion that it preserves arbitrary source-reference relations. Unknown preparation weights, native source-control availability and reference-return costs remain separate questions. The results derive no cloning operation, Born rule, source-independence law or general quantum-origin conclusion.

## 追加锚（本行以下为增补区）
