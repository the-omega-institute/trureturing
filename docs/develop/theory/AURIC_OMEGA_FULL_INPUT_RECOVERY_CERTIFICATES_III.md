# AURIC Ω full-input recovery certificates III

## 109. Common-boundary variables and the original recovery assertion

**Definition 109.1 (domain and conventions).** Continue the common-boundary mathematics of [volume II, Sections 85–101](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II.md#85-the-three-environment-family-and-one-common-auxiliary-density). All matrices below are finite dimensional. Positive square roots include singular positive semidefinite matrices. The nuclear or trace norm is $\|A\|_*=\operatorname{Tr}\sqrt{A^*A}$; it is distinct from the operator norm. Put

$$
\begin{gathered}
c=\frac{2+\sqrt2}{4},\qquad r=\sqrt c,\qquad \lambda_0=\frac c2,\\
P=\operatorname{diag}(p,q),\qquad \frac12\leq p\leq1,\qquad q=1-p,\qquad
a=\sqrt p,\quad b=\sqrt q,\\
V=\begin{pmatrix}V_0\\V_1\end{pmatrix}\in\mathbb R^{4\times2},\qquad
V_i\in\mathbb R^{2\times2},\qquad G=V^TV\preceq I_2,\qquad K=I_2-G,\\
D=\operatorname{diag}(a,b,a,b),\qquad
F=D(I_4-VV^T)D,\qquad B=\sqrt P K\sqrt P,\\
\tau=\frac12\sum_{i=0}^1\bigl(\operatorname{Tr}(V_i\sqrt P)\bigr)^2,\qquad
N=\frac{\operatorname{Tr}\sqrt F}{4\sqrt2},\\
R=1-\lambda_{\min}(B)-\tau,\qquad
\Theta=N+\frac{\sqrt R}{2},\qquad
\mathcal S=N^2+\frac R4.
\end{gathered}
\tag{U.1}
$$

Each occurrence of $N,R,\tau,G,B$ refers to this same feasible pair $P,V$. In particular both squared traces are included in $\tau$. The scalar $q$ is the smaller eigenvalue of $P$, not a residual objective. The number $\lambda_0$ is the fixed squared-bound constant; a subscript on a residual eigenvalue below denotes a different quantity. The results here are ordinary mathematical statements with proofs, without an assertion of Lean kernel certification.

**Definition 109.2 (physical family and source correspondence).** In a real output orthonormal frame $(b_1,g_1,b_2,g_2,h)$ set

$$
\begin{gathered}
E_0=\frac1{\sqrt2}[b_1,b_2,0],\qquad E_1=\frac1{\sqrt2}[g_1,g_2,0],\\
\mathcal T=\{T\in\mathbb R^{5\times3}:\|T\|_F=1,
\ \langle E_0,T\rangle_F=\langle E_1,T\rangle_F=0\},\\
\mathcal T_3=\{T\in\mathcal T:Te_2\ne0\},\qquad
\mathcal T_\partial=\{T\in\mathcal T:Te_2=0\},\qquad
\rho_\star=\operatorname{diag}(1/4,1/4,1/2),\\
f_T(X)=\left\|[E_0\sqrt X/4\mid E_1\sqrt X/4\mid T\sqrt X/2]\right\|_*\qquad
(X\in\mathsf D(\mathbb C^3)).
\end{gathered}
\tag{U.2}
$$

Here $\mathsf D(\mathbb C^d)$ denotes PSD trace-one matrices. The actual encoder has Kraus matrices $K_\alpha=[(E_0)_\alpha,(E_1)_\alpha,t_\alpha]$ for $T=[t_0,t_1,t_2]$. Volume II, Proposition 85.2 proves CPTP, the actual phase-difference spectrum $(1/2,1/2,0,-1/2,-1/2)$, and actual minimal Kraus rank three exactly when $Te_2\ne0$. This is the half-beta, $\lambda=1$ family specified there. Neither $\operatorname{rank}T$ nor $\operatorname{rank}V$ is that actual Kraus rank.

The boundary auxiliary density of volume II, (S.242), is $X=P$ after simultaneous symmetry. Its common block is

$$
M=V^T=[V_0^T\ V_1^T],\qquad
p_{\mathrm{(S.242)}}=\tau,\qquad
\ell_{\mathrm{(S.242)}}=4N,\qquad q_{\mathrm{(S.242)}}=R.
\tag{U.3}
$$

Indeed $\sqrt{A_{\mathrm{(S.242)}}}=D/\sqrt2$ and $M^TM=VV^T$. Transposition preserves each trace against symmetric $\sqrt P$, giving both terms of $\tau$. The auxiliary $P$, and the full complex $X$ in (U.2), act on an environment; neither is the physical $\rho_\star$.

**Proposition 109.3 (nonnegative residual and the exact uniform obligation).** On the domain (U.1), $R\geq0$. The assertion

$$
\Theta(P,V)\leq r\quad\text{for every feasible }P,V
\tag{U.4}
$$

is equivalent to

$$
f_T(X)^2\leq c\quad
\text{for every }T\in\mathcal T_3\text{ and every }X\in\mathsf D(\mathbb C^3).
\tag{U.5}
$$

The fixed-input recovery normalization is

$$
\max_{\mathcal R:M_5\to M_3\ \mathrm{CPTP}}
F_e(\rho_\star,\mathcal R N_T)
=\max_{X\in\mathsf D(\mathbb C^3)} f_T(X)^2.
\tag{U.6}
$$

Proof. The normalization and exact optimized equivalences are those of volume II, Propositions 85.3, 86.1–86.2, 90.2 and 91.2–91.3. Their common-variable content can be seen directly in the residual. Reorder the output as $(b_1,b_2,g_1,g_2,h)$ and write a common dual block as

$$
\mathscr B=\begin{pmatrix}V_0\\V_1\\w\end{pmatrix},\qquad
w\in\mathbb R^{1\times2},\qquad w^Tw\preceq K.
$$

The squared Frobenius norm after projection onto the two zero-overlap constraints is

$$
\|\Pi_2(\mathscr B\sqrt P)\|_F^2
=\operatorname{Tr}(PG)+wPw^T-\tau.
\tag{U.7}
$$

The two normalized constraint vectors are $[I_2;0;0]/\sqrt2$ and $[0;I_2;0]/\sqrt2$, so their squared projection coefficients are exactly the two halves of the squared traces in (U.1). For singular $K$, $w^Tw\preceq K$ forces $w^T$ into its range and is equivalent to $w^T=\sqrt K z$, $\|z\|\leq1$. Hence the maximum of $wPw^T$ is $\lambda_{\max}(\sqrt K P\sqrt K)$, attained by a top eigenvector, including a zero maximum. The matrices $\sqrt K P\sqrt K$ and $B$ have the same spectrum as the two Grams of $\sqrt K\sqrt P$. Thus

$$
\max_w\|\Pi_2(\mathscr B\sqrt P)\|_F^2
=\operatorname{Tr}(PG)+\operatorname{Tr}(PK)-\lambda_{\min}(B)-\tau=R\geq0.
$$

There is exactly one row $w$. Its contribution cannot be replaced by $\operatorname{Tr}(PK)$, which would allow a residual of larger rank. For the same $\mathscr B$, common code-row polar maximization gives $\ell/4=N$ as in (S.244)–(S.245). Support factorization and polar completion attain that maximum even when the residual has a kernel. Maximizing the boundary vector gives the projection norm in (U.7); if it vanishes, any unit vector in the eight-dimensional zero-overlap space is allowed. Consequently

$$
\max_{P,V}\Theta(P,V)
=\max_{T\in\mathcal T_\partial,\ X\in\mathsf D(\mathbb C^3)}f_T(X)
=\sup_{T\in\mathcal T_3,\ X\in\mathsf D(\mathbb C^3)}f_T(X).
\tag{U.8}
$$

For the middle expression, projection onto the first two environment coordinates and normalization retains the full auxiliary $2\times2$ block. Concavity and complex-conjugation symmetry permit real averaging. Ordered diagonal $P$ then follows from the joint transformation of density, channel and common blocks in (S.246), not from removing offdiagonals at a fixed channel. Equality with the last supremum uses the full-sphere comparison (S.208) and legal lifting (S.215). More explicitly, for $T_0\in\mathcal T_\partial$,

$$
T_\varepsilon=\frac{T_0+\varepsilon he_2^T}{\sqrt{1+\varepsilon^2}}\in\mathcal T_3,\qquad
|f_T(X)-f_{T'}(X)|\leq\frac12\|T-T'\|_F.
\tag{U.9}
$$

The inequality follows from $\|(T-T')\sqrt X\|_*\leq\|T-T'\|_F\|\sqrt X\|_F$ and holds for every complex density. It preserves a strict boundary gap at that same $X$ for sufficiently small $\varepsilon$. The full-sphere comparison is an optimized statement; it asserts no pointwise improvement by deleting a third column. Compact boundary maxima and (U.8) prove the equivalence of (U.4) and (U.5).

Finally the actual purification Gram is $L^TL$ for $L=[E_0/2\mid E_1/2\mid T/\sqrt2]$. Sandwiching by $\sqrt{\rho_\star}\otimes\sqrt X$ gives the right Gram of the rectangular matrix in (U.2). This explains its coefficients $1/4,1/4,1/2$ and gives its root fidelity. [Bény–Oreshkov, arXiv:1103.0649v3, Section IV, (133), with Corollary 5](https://arxiv.org/html/1103.0649v3) identifies its maximum with the square root of the unrestricted fixed-input entanglement fidelity. Squaring gives (U.6). Their (132) alone retains a Kraus-number restriction and is not the interface being used. $\square$

## 110. Joint singular-value and residual-loss bounds

**Theorem 110.1 (all directions with the actual residual loss).** Let $s_1\geq s_2\geq0$ be the singular values of the same $V$ in (U.1), and define

$$
\eta_j=\sqrt{1-s_j^2},\qquad
\zeta=\lambda_{\min}(B)-q\eta_1^2,\qquad \mu=\tau+\zeta.
\tag{U.10}
$$

Then $\zeta\geq0$, $0\leq\mu\leq1$, and

$$
R=1-\mu-q\eta_1^2,
\qquad 4\sqrt2 N\leq2a+b(\eta_1+\eta_2).
\tag{U.11}
$$

The following bounds hold simultaneously at this same point:

$$
\begin{aligned}
4\sqrt2\Theta
&\leq2a+b(\eta_1+\eta_2)
 +2\sqrt2\sqrt{1-\mu-q\eta_1^2}\\
&\leq2a+b\eta_2+3\sqrt{1-\mu}\\
&\leq\sqrt{5-s_2^2}+3\sqrt{1-\mu}.
\end{aligned}
\tag{U.12}
$$

Proof. Since $K\succeq\eta_1^2I_2$ and $P\succeq qI_2$, congruence gives $B\succeq\eta_1^2P\succeq q\eta_1^2I_2$. This proves $\zeta\geq0$. Its definition gives the first equality of (U.11). Nonnegativity of $R$, $\tau$ and $\zeta$ then gives $0\leq\mu\leq1$ and legitimates all roots.

Put $C=I_4-VV^T\succeq0$. Then $\operatorname{Tr}\sqrt{DCD}=\|D\sqrt C\|_*$. The singular values of $D$ are $a,a,b,b$; those of $\sqrt C$ are $1,1,\eta_2,\eta_1$. Trace-norm duality and the finite-dimensional singular-value pairing inequality give

$$
\|D\sqrt C\|_*\leq2a+b(\eta_1+\eta_2).
$$

This standard pairing is also supplied by [Miszczak–Puchała–Horodecki–Uhlmann–Życzkowski, arXiv:0805.2037v2, (9)](https://arxiv.org/html/0805.2037v2). Its density normalization here is $\rho_1=D^2/2$, $\rho_2=C/\operatorname{Tr}C$, where $\operatorname{Tr}C=4-s_1^2-s_2^2\geq2$. The paper uses squared fidelity: its $F(\rho_1,\rho_2)$ equals $(\operatorname{Tr}\sqrt{DCD})^2/(2\operatorname{Tr}C)$. Take the nonnegative square root of (9) and multiply by $\sqrt{2\operatorname{Tr}C}$ to obtain exactly this pairing, including singular densities. It is only an upper bound and asserts no jointly attainable equality configuration.

Now set $k=b\eta_1$. Equation (U.11) yields $k^2+R=1-\mu$. Cauchy–Schwarz against $(1,2\sqrt2)$ gives $k+2\sqrt2\sqrt R\leq3\sqrt{1-\mu}$. A second Cauchy–Schwarz inequality, using $a^2+b^2=1$, gives $2a+b\eta_2\leq\sqrt{4+\eta_2^2}=\sqrt{5-s_2^2}$. These prove (U.12). No inverse, division by a residual eigenvalue, or choice of independent spectra occurs. $\square$

**Corollary 110.2 (necessary localization and the singular contraction endpoint).** Define the starred localization constants

$$
\begin{gathered}
L=4\sqrt2 r=2\sqrt{4+2\sqrt2},\qquad k_*=L-3,\\
\delta_*=5-k_*^2,\qquad
\varepsilon_*=1-\left(\frac{L-\sqrt5}{3}\right)^2,\qquad
p_\pm=\left(\frac{2k_*\pm\sqrt{\delta_*}}5\right)^2.
\end{gathered}
\tag{U.13}
$$

Every feasible point with $\Theta>r$ satisfies

$$
p_-<p<p_+,\qquad s_2^2<\delta_*,\qquad
\tau+\zeta<\varepsilon_*,\qquad s_1<1,\qquad p<9/10.
\tag{U.14}
$$

In particular the joint inequality

$$
\sqrt{5-s_2^2}+3\sqrt{1-\tau-\zeta}\leq L
\tag{U.15}
$$

is sufficient for $\Theta\leq r$.

Proof. A strict violation and (U.12) imply each of

$$
2\sqrt p+\sqrt{1-p}>k_*,\qquad
\sqrt{5-s_2^2}+3>L,\qquad
\sqrt5+3\sqrt{1-\mu}>L.
$$

The function $2\sqrt p+\sqrt{1-p}$ increases up to $p=4/5$ and decreases thereafter. Its intersections with $k_*$ on the unit quarter circle $a^2+b^2=1$ solve $2a+b=k_*$, giving $a=(2k_*\pm\sqrt{5-k_*^2})/5$ and hence exactly $p_\pm$. These intersections are in $[1/2,1]$, with the strict superlevel interval between them; this also follows directly from $3/\sqrt2<k_*<\sqrt5$ and $2<k_*$. Squaring the other two positive comparisons gives the stated strict bounds on $s_2^2$ and $\mu$.

If $s_1=1$, then $\eta_1=0$, $R\leq1$, and the first line of (U.12) gives

$$
\Theta\leq\frac{\sqrt5}{4\sqrt2}+\frac12<\frac9{10}<r.
\tag{U.16}
$$

For the first strict comparison, $5<(8\sqrt2/5)^2=128/25$; for the second, $c>81/100$. Thus $I_2-G$ cannot be singular at a strict violation. If $p\geq9/10$, monotonicity on $[4/5,1]$ gives $2\sqrt p+\sqrt{1-p}\leq7/\sqrt{10}<k_*$. One exact verification of the last comparison uses $\sqrt2>7/5$: then $L>1043/200$, while $7/\sqrt{10}<443/200$, as is checked by squaring positive quantities. This excludes that interval. Equation (U.15) is the direct contrapositive of the last bound in (U.12). $\square$

## 111. The commuting case over the entire auxiliary spectrum

**Theorem 111.1 (full-spectrum commuting squared bound).** For every pair (U.1) with $[P,G]=0$,

$$
\mathcal S\leq\lambda_0,\qquad \Theta^2\leq c.
\tag{U.17}
$$

Proof. Write $\chi=2a+b$. First, in the whole domain, not yet assuming commutation, (U.11), $\eta_2\leq1$ and $\zeta\geq0$ give

$$
\begin{aligned}
\mathcal S
&\leq\frac{(\chi+b\eta_1)^2}{32}
+\frac{1-\tau-b^2\eta_1^2}{4}\\
&=\frac{1-\tau}{4}+\frac{\chi^2}{28}
-\frac7{32}\left(b\eta_1-\frac\chi7\right)^2
\leq\frac14+\frac{\chi^2}{28}.
\end{aligned}
\tag{U.18}
$$

For $1/2\leq p\leq71/100$, $\chi$ is increasing, since this interval lies below $4/5$. At its upper endpoint $pq=2059/10000<(227/500)^2$, so

$$
\chi^2=1+3p+4\sqrt{pq}<\frac{2473}{500}<\frac{7\sqrt2}{2}.
$$

The last inequality follows from $\sqrt2>707/500$. Therefore (U.18) gives $\mathcal S<1/4+\sqrt2/8=\lambda_0$. This covers every residual eigendirection, including $p=q=1/2$, where commutation with $P$ puts no restriction on $G$.

At $q=0$, $F\preceq D^2$ gives $\operatorname{Tr}\sqrt F\leq\operatorname{Tr}D=2$, while $R\leq1$. Thus $N\leq1/(2\sqrt2)$ and $\mathcal S\leq3/8<\lambda_0$. This endpoint needs no column-orthogonality assumption or division by $q$.

It remains to take $1/2<p<1$, where $[P,G]=0$ implies $G=\operatorname{diag}(g_1,g_2)$. Consequently $B=\operatorname{diag}(p(1-g_1),q(1-g_2))$. Split according to a top residual eigendirection; in a tie either branch is legitimate. Write

$$
V_i=\begin{pmatrix}a_i&b_i\\c_i&d_i\end{pmatrix}.
$$

Suppose first that $e_1$ is a top residual eigenvector. The exact expression for $R$ is

$$
R=p+q\sum_i(b_i^2+d_i^2)
-\frac12\sum_i(aa_i+bd_i)^2.
\tag{U.19}
$$

For $71/100\leq p\leq3/4$, take $W=\operatorname{diag}(2,1,2,1)$. The Hilbert–Schmidt inequality

$$
(\operatorname{Tr}\sqrt F)^2
\leq\operatorname{Tr}(W)\operatorname{Tr}(W^{-1}F)
\tag{U.20}
$$

holds for every $F\succeq0$: apply Cauchy–Schwarz to $W^{1/2}$ and $W^{-1/2}\sqrt F$ and use trace cyclicity. Only $W$ is inverted. Its trace is six, and expansion gives

$$
\operatorname{Tr}(W^{-1}F)
=p+2q-\sum_i\left[\frac p2(a_i^2+b_i^2)+q(c_i^2+d_i^2)\right].
$$

Multiplying $\mathcal S$ by sixteen and using (U.19) yields

$$
16\mathcal S\leq6+p+\sum_i\left[
-\frac72pa_i^2+\left(4q-\frac32p\right)b_i^2
-3qc_i^2-qd_i^2-4\sqrt{pq}\,a_id_i\right].
\tag{U.21}
$$

Both penalties occur in this sum. Complete the square in each pair $a_i,d_i$:

$$
-\frac72pa_i^2-4\sqrt{pq}\,a_id_i-qd_i^2
=-\frac72p\left(a_i+\frac{4\sqrt q}{7\sqrt p}d_i\right)^2+\frac q7d_i^2.
$$

Drop the negative squares and $-3qc_i^2$, and use the common budget $\sum_i(b_i^2+d_i^2)=g_2\leq1$. It follows that

$$
16\mathcal S\leq6+p+
\max\left\{\frac{8-11p}{2},\frac q7\right\}.
\tag{U.22}
$$

The two entries cross at $p=18/25$. Below that point the right side is $10-9p/2$, whose maximum on the specified interval is $1361/200$. Above it the right side is $(43+6p)/7$, whose maximum is $95/14<1361/200$. Hence

$$
\mathcal S\leq\frac{1361}{3200}<\lambda_0.
\tag{U.23}
$$

The last comparison follows, for example, from $\sqrt2>707/500$.

For completeness, the aligned high-spectrum estimate of [volume II, Theorem 98.1](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II.md#98-a-restricted-high-spectrum-estimate-with-aligned-residual-direction) applies with both hypotheses $p\geq p_0=4/(4+\sqrt2)$ and $e_1$ top for $B$. Its full quadratic argument here is short. Put $w=1+\sqrt2$ and $W=\operatorname{diag}(w,1,w,1)$ in (U.20). Then

$$
N^2\leq\frac{w+1}{8}(p/w+q)
-\frac{w+1}{16}\sum_i\left[\frac p w(a_i^2+b_i^2)+q(c_i^2+d_i^2)\right].
$$

Since $(w+1)/w=\sqrt2$, adding $R/4$ makes the constant part exactly $\lambda_0$. The rest is

$$
\begin{aligned}
16(\mathcal S-\lambda_0)\leq\sum_i\bigl[
&-(2+\sqrt2)pa_i^2+(4q-\sqrt2p)b_i^2\\
&-(2+\sqrt2)qc_i^2-\sqrt2qd_i^2
-4\sqrt{pq}\,a_id_i\bigr].
\end{aligned}
\tag{U.24}
$$

The $b_i^2$ coefficient is nonpositive for $p\geq p_0$, and the $c_i^2$ coefficient is nonpositive. The negative of the remaining quadratic has matrix

$$
\begin{pmatrix}(2+\sqrt2)p&2\sqrt{pq}\\2\sqrt{pq}&\sqrt2q\end{pmatrix},
\qquad \det=2pq(\sqrt2-1)\geq0.
\tag{U.25}
$$

Its diagonal entries are nonnegative, so it is PSD. This proves $\mathcal S\leq\lambda_0$ under both high-spectrum alignment hypotheses. In particular it covers the remaining $p\geq3/4$ branch, since $p_0<3/4$ is equivalent to $4<3\sqrt2$. The endpoint $p=p_0$ merely sets one coefficient to zero. No alignment is inferred from feasibility alone.

Finally suppose that $e_2$ is a top eigenvector of $B$. Then

$$
p(1-g_1)\leq q(1-g_2),\qquad g_1\geq g_2.
$$

For the second implication, divide by positive $p$ and use $(q/p)(1-g_2)\leq1-g_2$. Thus $s_1^2=g_1$ and

$$
R=q+pg_1-\tau=1-p\eta_1^2-\tau.
$$

Combining this exact identity with the code bound of (U.11), again using $\eta_2\leq1$, and completing the same $\eta_1$ square gives

$$
\begin{aligned}
\mathcal S
&\leq\frac{1-\tau}{4}+\frac{\chi^2}{32}
+\frac{\chi b}{16}\eta_1-\frac{9p-1}{32}\eta_1^2\\
&\leq\frac{1-\tau}{4}+\frac{p\chi^2}{4(9p-1)}.
\end{aligned}
\tag{U.26}
$$

Here $9p-1>0$. For $1/2\leq p\leq3/5$, $\chi^2\leq24/5$ and $p/(9p-1)\leq1/7$, giving $\mathcal S\leq59/140$. For $3/5\leq p\leq1$, $\chi^2\leq5$ and $p/(9p-1)\leq3/22$, giving $\mathcal S\leq37/88\leq59/140<\lambda_0$. To justify the first bound on $\chi^2$, its maximum on the first interval is at $3/5$, where $\chi^2=(14+4\sqrt6)/5<24/5$; the global bound five is Cauchy–Schwarz. The function $p/(9p-1)$ decreases. The comparison with $\lambda_0$ follows from $\sqrt2>48/35$.

The low-spectrum, aligned middle-spectrum, aligned high-spectrum and switched-top branches exhaust the commuting domain. The preceding direct arguments include $p=q$, $q=0$, repeated residual eigenvalues, zero singular values and $s_1=1$. Finally

$$
\Theta^2=2\mathcal S-\left(N-\frac{\sqrt R}{2}\right)^2\leq2\lambda_0=c,
\tag{U.27}
$$

which proves the theorem. $\square$

## 112. Necessary violation region and the directional deficit

**Corollary 112.1 (common-variable exclusions).** A feasible pair with $\Theta>r$ must satisfy simultaneously

$$
\begin{gathered}
p_-<p<p_+,\qquad [P,V^TV]\ne0,\qquad 0<s_1<1,\\
s_2^2<\delta_*,\qquad \tau+\zeta<\varepsilon_*,\qquad
\|V\|_F>1/100,\\
p\in[21/25,7/8]\ \Longrightarrow\ \|V\|_F>1/10.
\end{gathered}
\tag{U.28}
$$

Proof. Corollary 110.2 gives the spectral and residual restrictions. Theorem 111.1 excludes commutation, and in particular $V=0$. For the radii apply [volume II, Theorems 93.1 and 93.3](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES_II.md#93-rational-spectral-band-and-all-spectrum-exclusion-radii), with the exact map $M=V^T$ and $\|M\|_F=\|V\|_F$. Their conclusions are respectively $\Theta\leq F_0(p)-\|V\|_F^2/4000$ in the stated spectral band at radius $1/10$, and $\Theta\leq r-\|V\|_F^2/4000$ at radius $1/100$ over the whole spectrum. The calibration $F_0(p)\leq r$ is (S.264). Taking contrapositives gives the two strict exclusions. These are radii and singular values of the common dual contraction, not of the physical Kraus list or the matrix $T$. $\square$

**Proposition 112.2 (exact remaining directional inequality).** Let

$$
S_0=2a+b(\eta_1+\eta_2),\qquad
\nu=S_0-4\sqrt2N\geq0.
$$

Then the exact target and its strict failure have the respective equivalent forms

$$
\begin{aligned}
\Theta\leq r
&\quad\Longleftrightarrow\quad
\nu\geq S_0+2\sqrt2\sqrt R-L,\\
\Theta>r
&\quad\Longleftrightarrow\quad
\nu<S_0+2\sqrt2\sqrt R-L.
\end{aligned}
\tag{U.29}
$$

Proof. Substitute the definition of $\nu$ into $4\sqrt2\Theta=S_0-\nu+2\sqrt2\sqrt R$ and rearrange, preserving the direction of the inequality. The nonnegativity of $\nu$ is (U.11). Where the right side in (U.29) is nonpositive, $\nu\geq0$ already proves the target. Thus only its positive part needs an additional lower bound. That lower bound must refer to the singular directions and both trace penalties of the actual same $V$; (U.29) does not supply it. $\square$

## 113. Rank-one zero-penalty geometry and shared roots

**Theorem 113.1 (same-direction parameterization).** Suppose $q>0$ and $V=s\ell u^T$ with $0<s\leq1$ and $\|\ell\|=\|u\|=1$. Split $\ell=(\ell_0;\ell_1)$ into two real two-vectors and put

$$
t=s^2,\qquad \eta=\sqrt{1-t},\qquad m=u^TPu\in[q,p],\qquad
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

Then $\tau=0$ if and only if

$$
\ell_i=\kappa_i v,\qquad
v=\frac{J\sqrt P u}{\sqrt m},\qquad
\kappa_0^2+\kappa_1^2=1.
\tag{U.30}
$$

Every $m\in[q,p]$ is attained by a unit $u$. A rotation between the two copies makes $\ell=(v;0)$ without changing $P,u,m,N,\tau,R$.

Proof. Directly,

$$
\operatorname{Tr}(V_i\sqrt P)=s(\sqrt P u)^T\ell_i.
$$

Since $s>0$ and $\tau$ is a sum of two squares, zero penalty is equivalent to each $\ell_i$ being perpendicular to nonzero $\sqrt P u$. Its orthogonal complement is the line through $v$, and $\|v\|=1$. Normalizing $\ell$ gives exactly (U.30), including vanishing individual copies. If $p>q$, choose $u_1^2=(m-q)/(p-q)$, $u_2^2=(p-m)/(p-q)$. If $p=q=1/2$, the interval consists only of $m=1/2$ and every unit $u$ attains it.

Choose $O\in O(2)$ with $O(\kappa_0,\kappa_1)^T=(1,0)^T$, and let $Q=O\otimes I_2$. It commutes with $D$, while $(QV)^T(QV)=V^TV$. The two-trace vector is multiplied by $O$, so its squared norm and $\tau$ are unchanged. Also

$$
D(I_4-QVV^TQ^T)D=QFQ^T.
$$

Thus $N$ is unchanged; $G$ and $P$ remain the same, so $R$ is unchanged as well. This is one lawful left rotation, with no independent choice of a right direction or residual spectrum. $\square$

**Theorem 113.2 (common determinant and exact root formulas).** Under the hypotheses of Theorem 113.1 and $\tau=0$, set $h=a+b$ and

$$
f=\sqrt{1-tpq/m+2ab\eta},\qquad
\Delta=\sqrt{(1-tm)^2-4pq\eta^2}.
$$

Then

$$
N=\frac{h+f}{4\sqrt2},\qquad R=\frac{1+tm+\Delta}{2}.
\tag{U.31}
$$

Proof. Use the copy rotation just proved. The full four-dimensional code Gram splits as $A\oplus P$, where

$$
A=P-\frac{tpq}{m}Juu^TJ^T,\qquad
B=\sqrt P(I_2-tuu^T)\sqrt P.
\tag{U.32}
$$

Indeed $\sqrt P J\sqrt P=\sqrt{pq}J$. Both are PSD by their original contraction-Gram expressions. Their traces and determinants are

$$
\operatorname{Tr}A=1-tpq/m,\quad
\operatorname{Tr}B=1-tm,\quad
\det A=\det B=pq\eta^2.
\tag{U.33}
$$

For the determinant of $A$, the rank-one determinant identity gives $\det A=pq[1-(tpq/m)(Ju)^TP^{-1}(Ju)]$ and $(Ju)^TP^{-1}(Ju)=m/(pq)$. For $B$ it gives $\det B=pq\det(I_2-tuu^T)=pq(1-t)$. Here $q,m>0$ justify these inverses; no inverse of a residual is used.

For any $2\times2$ PSD matrix with eigenvalues $x,y\geq0$, $(\operatorname{Tr}\sqrt C)^2=(\sqrt x+\sqrt y)^2=\operatorname{Tr}C+2\sqrt{\det C}$. Apply this elementary identity to $A$, and $\operatorname{Tr}\sqrt P=h$, to obtain $N$. The smaller eigenvalue of $B$ is $(1-tm-\Delta)/2$. Since $\tau=0$, subtracting it from one yields $R$. Positivity of $A,B$ proves that all roots used are real. Both expressions retain the same $m$ and the same determinant; these parameters cannot be optimized separately. $\square$

## 114. An all-direction rank-one gap

**Theorem 114.1 (quantitative squared bound).** For every feasible rank-one zero-penalty pair with $q>0$ and $s>0$, using Theorem 113.2's $h,f$,

$$
\begin{aligned}
\mathcal S&\leq\frac c2-\frac{s^2}{2880}-\frac{(h-f)^2}{32},\\
\Theta^2&\leq c-\frac{s^2}{1440}-\frac{(h-f)^2}{16}.
\end{aligned}
\tag{U.34}
$$

No commutation or alignment condition is imposed.

Proof. Set

$$
n=\frac{pq}{m},\qquad
\gamma^2=1-m-n=\frac{(p-m)(m-q)}m\geq0,\qquad
x=(\sqrt m,\sqrt n,\gamma)^T.
$$

Choose $\gamma\geq0$, so $\|x\|=1$ and $ab=\sqrt{mn}$. Since $1-tm=\eta^2m+n+\gamma^2$, the discriminant in (U.31) has the decomposition

$$
\Delta^2=(\eta^2m-n-\gamma^2)^2+4\eta^2m\gamma^2.
\tag{U.35}
$$

Using $(h+f)^2=2(h^2+f^2)-(h-f)^2$, $h^2=1+2ab$ and $f^2=1-tn+2ab\eta$, the exact formula for $\mathcal S$ becomes

$$
\mathcal S=\frac14+\frac\Phi8-\frac{(h-f)^2}{32},\qquad
\Phi=t(m-n/2)+(1+\eta)\sqrt{mn}+\Delta.
\tag{U.36}
$$

To bound this expression in every direction, use the support function of the two-vector in (U.35). Its second coordinate $2\eta\sqrt m\gamma$ is nonnegative, hence

$$
\Delta=\max_{-1\leq\xi\leq1}
\left[\xi(\eta^2m-n-\gamma^2)
+2\eta\sqrt{1-\xi^2}\sqrt m\gamma\right].
$$

This formula includes a zero second coordinate. Consequently

$$
\begin{gathered}
\Phi=\max_{-1\leq\xi\leq1}x^TM_\eta(\xi)x,\\
M_\eta(\xi)=
\begin{pmatrix}
t+\eta^2\xi&(1+\eta)/2&\eta\sqrt{1-\xi^2}\\
(1+\eta)/2&-t/2-\xi&0\\
\eta\sqrt{1-\xi^2}&0&-\xi
\end{pmatrix}.
\end{gathered}
\tag{U.37}
$$

We prove the uniform matrix bound

$$
M_\eta(\xi)\preceq\left(\sqrt2-\frac t{360}\right)I_3
\quad(0\leq\eta\leq1,\ t=1-\eta^2,\ -1\leq\xi\leq1).
\tag{U.38}
$$

Put $\kappa=\sqrt2$, $d=\kappa-1$, $z=\kappa+\xi\in[d,1/d]$, and $\mathsf K=\kappa I_3-M_\eta(\xi)$. The lower $2\times2$ block is $\operatorname{diag}(z+t/2,z)\succ0$, including $t=0$ and $\eta=0$. Its Schur complement is

$$
\begin{aligned}
\mathsf{Schur}
&=\kappa-t-\eta^2\xi
-\frac{(1+\eta)^2}{4(z+t/2)}
-\frac{\eta^2(1-\xi^2)}z\\
&=\frac{tH}{4(z+t/2)},\\
H&=\frac{2\eta^2}{z}+4dz+2d(1-\eta^2)-\frac{3\eta+1}{1+\eta}.
\end{aligned}
\tag{U.39}
$$

The identity follows by putting the first line over $4z(z+t/2)$, substituting $\xi=z-\kappa$, $t=1-\eta^2$, $\kappa^2=2$, and using $t/(1+\eta)=1-\eta$. It introduces no division by $t$, so it holds at $t=0$ as well.

We next prove $H\geq1/4$ on its entire rectangle. For $0\leq\eta\leq1/3$, the function $2\eta^2/z+4dz$ is increasing on $z\geq d$, because its derivative is $4d-2\eta^2/z^2>0$. Indeed $\eta^2\leq1/9<2d^3$, the latter following from $d>2/5$ and $1/9<16/125$. Evaluate at $z=d$ and use $1/d=\kappa+1$ to obtain

$$
\begin{aligned}
H&\geq4\eta^2+10-6\sqrt2-\frac{3\eta+1}{1+\eta}\\
&\geq4\eta^2-2\eta+9-6\sqrt2\\
&\geq\frac{35}{4}-6\sqrt2>\frac14.
\end{aligned}
\tag{U.40}
$$

The second line uses $(3\eta+1)/(1+\eta)=1+2\eta/(1+\eta)\leq1+2\eta$; the third completes $4(\eta-1/4)^2$. The final strict comparison is $\sqrt2<17/12$, verified by squaring.

For $1/3\leq\eta\leq1$, AM–GM gives $2\eta^2/z+4dz\geq4\eta\sqrt{2d}\geq16\eta/5$, since $d>2/5$ implies $\sqrt{2d}>4/5$. Also $2d(1-\eta^2)\geq4(1-\eta^2)/5$. Hence

$$
\begin{gathered}
H\geq F_1(\eta):=\frac{16\eta}{5}+\frac{4(1-\eta^2)}5-\frac{3\eta+1}{1+\eta},\\
F_1'(\eta)=\frac{16}{5}-\frac{8\eta}{5}-\frac2{(1+\eta)^2}
\geq\frac85-\frac98=\frac{19}{40}>0,\\
F_1(1/3)=\frac5{18}>\frac14.
\end{gathered}
\tag{U.41}
$$

This proves the required lower bound on $H$ without restricting the direction parameter $z$.

The Schur complement now gives $\mathsf K\succeq0$, and $\mathsf K\succ0$ if $t>0$. Moreover

$$
\det\mathsf K=\frac{tzH}{4}\geq\frac{tz}{16},\qquad
\operatorname{Tr}\mathsf K=3\sqrt2-\frac t2+(1+t)\xi
\leq3\sqrt2+\frac32<6.
\tag{U.42}
$$

If $t>0$, the product of the two largest eigenvalues is at most $(\operatorname{Tr}\mathsf K)^2/4<9$. Therefore

$$
\lambda_{\min}(\mathsf K)
\geq\frac{\det\mathsf K}{9}
\geq\frac{td}{144}\geq\frac t{360}.
$$

For $t=0$, PSD alone gives the same non-strict bound. This proves (U.38). The unit-vector representation (U.37) yields $\Phi\leq\sqrt2-t/360$, and substitution in (U.36) proves the first line of (U.34), since $1/4+\sqrt2/8=c/2$. Identity (U.27) proves the second line. All steps retain the same $m,n,\gamma$; the matrix estimate dominates the whole actual directional family rather than selecting independent eigenvalue optima. $\square$

## 115. Degenerate parameters and equality

**Theorem 115.1 (endpoints and exact equality set).** Over the entire feasible family $\operatorname{rank}V\leq1$, $\tau=0$,

$$
\mathcal S\leq\frac c2-\frac{s_1^2}{2880},\qquad
\Theta\leq\sqrt{c-\frac{s_1^2}{1440}}\leq r.
\tag{U.43}
$$

Equality $\Theta=r$ holds if and only if $V=0$ and $p=c$. For $q>0$, $s_1>0$, the stronger refinement (U.34) applies. For $q=0$ the direct endpoint estimates are

$$
N\leq\frac1{2\sqrt2},\qquad R\leq1,\qquad
\mathcal S\leq\frac38,\qquad \Theta\leq c<r.
\tag{U.44}
$$

Proof. Theorem 114.1 covers $q>0$, $s_1>0$. At $s_1=1$, $\eta=0$ and its proof still applies: the lower Schur block is positive and no division by $\eta$ or residual eigenvalue difference occurs. Direction endpoints $m=q,p$ have $\gamma=0$ and are included. At $q=0$, $F\preceq D^2$ gives $\operatorname{Tr}\sqrt F\leq2$ as in Theorem 111.1. Together with $R\leq1$ this proves (U.44). Since

$$
\frac c2-\frac38=\frac{\sqrt2-1}{8}>\frac1{2880},
$$

it also proves the unrefined squared gap in (U.43) for $s_1\leq1$, and (U.27) proves its root bound. No expression $pq/m$ or refinement involving $h-f$ is evaluated at $m=0$.

For $s_1=0$, $V=0$, with no need to choose $u$ or $m$. Directly $N=(a+b)/(2\sqrt2)$, $R=p$, and

$$
\Theta=c\sqrt p+\frac{\sqrt2}{4}\sqrt q\leq r,
\tag{U.45}
$$

because $c^2+1/8=c$. Cauchy–Schwarz equality requires $(\sqrt p,\sqrt q)$ to be the normalized vector $(c,\sqrt2/4)$, giving exactly $p=c$. To check also $\mathcal S\leq c/2$ on this slice, use

$$
\mathcal S=\frac{1+2p+2\sqrt{pq}}8\leq\frac{2+\sqrt2}{8}.
$$

Indeed with $x=2p-1$ and $y=2\sqrt{pq}$, $x^2+y^2=1$ and $2p+2\sqrt{pq}=1+x+y\leq1+\sqrt2$. For $q>0$, $s_1>0$, (U.34) is strict below $c$; for $q=0$, (U.44) is strict below $r$. This proves the equality characterization. $\square$

**Proposition 115.2 (balanced spectrum calibration).** If $p=q=1/2$ in the rank-one zero-penalty family, then for $\eta=\sqrt{1-s_1^2}$,

$$
N=\frac{3+\eta}{8},\qquad R=1-\frac{\eta^2}{2},
\qquad
\max\Theta=\frac{3(1+\sqrt2)}8,\qquad
\max\mathcal S=\frac{23}{56}.
\tag{U.46}
$$

The maximizing $\eta$ values are respectively $\sqrt2/3$ and $3/7$; both maxima are strictly below the corresponding $r,c/2$.

Proof. Here $m=n=1/2$, $h=\sqrt2$, $f=(1+\eta)/\sqrt2$ and $\Delta=t/2$, giving the formulas from (U.31), with continuity at $s_1=0$. Thus $\Theta=(3+\eta)/8+\sqrt{1-\eta^2/2}/2$. Its derivative on $[0,1]$ vanishes exactly when $\sqrt{1-\eta^2/2}=2\eta$, namely at $\eta=\sqrt2/3$, with positive derivative before and negative derivative after. At that point $\sqrt{1-\eta^2/2}=2\sqrt2/3$, giving the displayed maximum. Its square is $(27+18\sqrt2)/64<c=(32+16\sqrt2)/64$, since $2\sqrt2<5$. Also

$$
\mathcal S=\frac{25+6\eta-7\eta^2}{64}
=\frac{23}{56}-\frac7{64}(\eta-3/7)^2.
$$

Finally $23/56<c/2$ is equivalent to $9<7\sqrt2$, verified by squaring. $\square$

## 116. The actual SVD angle, trace cancellation and residual decrement

**Theorem 116.1 (same-realization directional data).** Suppose $q>0$ and $s=s_1>0$. Choose an actual SVD

$$
V=s\ell u^T+\sigma k u_\perp^T,\qquad
\sigma=s_2\leq s\leq1,
\tag{U.47}
$$

with $\ell,k\in\mathbb R^4$ orthonormal and $u,u_\perp\in\mathbb R^2$ orthonormal. Repeated and zero singular values are allowed; fix one such actual choice. Split left vectors into their two copies, and put

$$
\eta=\sqrt{1-s^2},\qquad m=u^TPu,\qquad g=\sqrt P u,\qquad
\alpha^2=\frac{\sum_i(g^T\ell_i)^2}{m}.
\tag{U.48}
$$

Then $0\leq\alpha\leq1$ and

$$
s\sqrt m\,\alpha\leq\sqrt{2\tau}+\sigma\sqrt{1-m},\qquad
\alpha\leq\min\left\{1,\frac{\sqrt{2\tau}+\sigma\sqrt{1-m}}{s\sqrt m}\right\}.
\tag{U.49}
$$

Define actual residual eigenvalues and their decrement by

$$
\begin{gathered}
\lambda=\lambda_{\min}\bigl(\sqrt P(I_2-V^TV)\sqrt P\bigr),\qquad
\lambda_{\mathrm{top}}=\lambda_{\min}\bigl(\sqrt P(I_2-s^2uu^T)\sqrt P\bigr),\\
\delta=\lambda_{\mathrm{top}}-\lambda,\qquad
\zeta=\lambda-q\eta^2.
\end{gathered}
\tag{U.50}
$$

These quantities satisfy

$$
0\leq\delta\leq\sigma^2(1-m),\qquad \zeta\geq0,\qquad
R=1-q\eta^2-\zeta-\tau.
\tag{U.51}
$$

In particular $\delta$ in (U.50) is not the starred constant $\delta_*$ in (U.13). Full closed expressions are

$$
\begin{gathered}
T_B=1-s^2m-\sigma^2(1-m),\\
\lambda=\frac{T_B-\sqrt{T_B^2-4pq\eta^2(1-\sigma^2)}}2,\\
\lambda_{\mathrm{top}}
=\frac{1-s^2m-\sqrt{(1-s^2m)^2-4pq\eta^2}}2.
\end{gathered}
\tag{U.52}
$$

Proof. Define the two-component real vectors $A_i=g^T\ell_i$ and $C_i=(\sqrt P u_\perp)^Tk_i$. Orthogonal projection and $\|\ell\|=1$ give $\|A\|^2=m\alpha^2\leq m$. Similarly $\|C\|\leq\sqrt{u_\perp^TPu_\perp}=\sqrt{1-m}$. The actual trace vector is $sA+\sigma C$, so $\|sA+\sigma C\|=\sqrt{2\tau}$. The triangle inequality $s\|A\|\leq\|sA+\sigma C\|+\sigma\|C\|$ proves (U.49). Thus small total $\tau$ permits cancellation between the two singular contributions; it does not imply small individual traces.

Write $W=s\ell u^T$. Its residual satisfies

$$
B(V)=B(W)-\sigma^2\sqrt P u_\perp u_\perp^T\sqrt P.
$$

The removed PSD term has operator norm $\sigma^2(1-m)$. The variational characterization of the smallest eigenvalue gives the two bounds on $\delta$. Also $I_2-V^TV\succeq\eta^2I_2$, proving $\zeta\geq0$ by the same congruence as in Theorem 110.1. Substitution yields the identity for $R$.

In the actual right singular basis, $I_2-V^TV$ has eigenvalues $\eta^2,1-\sigma^2$. Its congruence by $\sqrt P$ has determinant $pq\eta^2(1-\sigma^2)$ and trace $T_B$. The quadratic eigenvalue formula gives $\lambda$; setting $\sigma=0$ gives $\lambda_{\mathrm{top}}$. Positivity ensures nonnegative discriminants, even at repeated or zero residual eigenvalues. These are identities at the chosen common direction, not bounds obtained by varying that direction independently. $\square$

## 117. An angle-aware common-root certificate

**Theorem 117.1 (comparison with the zero-penalty core).** With the actual SVD data of Theorem 116.1, define

$$
\begin{gathered}
N_0=\frac{a+b+\sqrt{1-s^2pq/m+2ab\eta}}{4\sqrt2},\qquad
R_0=1-\lambda_{\mathrm{top}}=1-q\eta^2-\zeta-\delta,\\
E=\frac{a(1-\eta)\alpha}{2\sqrt2}.
\end{gathered}
\tag{U.53}
$$

Then $R_0\geq p>0$, and

$$
\begin{aligned}
\Theta(P,V)
&\leq N_0+E+\frac12\sqrt{1-q\eta^2-\zeta-\tau},\\
\Theta(P,V)
&\leq\sqrt{c-\frac{s^2}{1440}}+E\\
&\hspace{8mm}+\frac12\left[
\sqrt{1-q\eta^2-\zeta-\tau}
-\sqrt{1-q\eta^2-\zeta-\delta}\right].
\end{aligned}
\tag{U.54}
$$

In particular the sufficient certificate

$$
E+\frac12\left[
\sqrt{1-q\eta^2-\zeta-\tau}
-\sqrt{1-q\eta^2-\zeta-\delta}\right]
\leq r-\sqrt{c-\frac{s^2}{1440}}
\tag{U.55}
$$

implies the target $\Theta(P,V)\leq r$. If $\delta<\tau$, the difference of roots in this certificate is negative.

Proof. Project $\ell$ in each copy onto $g^\perp$. The combined projection has squared norm $1-\alpha^2$. If $\alpha<1$, normalize this projection to obtain $\widehat\ell$. If $\alpha=1$, take any unit vector in the two-dimensional space $g^\perp\oplus g^\perp$; it is orthogonal to $\ell$. Thus in all cases

$$
\ell^T\widehat\ell=\sqrt{1-\alpha^2},\qquad
g^T\widehat\ell_i=0.
$$

The comparison matrix $U=s\widehat\ell u^T$ is a contraction with $\tau(U)=0$ and $U^TU=s^2uu^T=W^TW$. Theorems 113.1–113.2 give $N(U)=N_0$ and $R(U)=R_0$. Since $B(W)\preceq P$, $\lambda_{\mathrm{top}}\leq\lambda_{\min}(P)=q$, so $R_0\geq p$.

The equality $VV^T=WW^T+\sigma^2kk^T$ implies $F(V)\preceq F(W)$, hence $N(V)\leq N(W)$ by eigenvalue monotonicity and the increasing scalar square root. For a unit vector $v\in\mathbb R^4$ put

$$
Q_v=I_4-(1-\eta)vv^T,\qquad Q_v^2=I_4-s^2vv^T.
$$

Then, with the nuclear norm throughout,

$$
4\sqrt2 N(svu^T)=\|Q_vD\|_*.
$$

Indeed $D Q_v^2 D$ is the right Gram of $Q_vD$. The triangle inequality yields

$$
\begin{aligned}
4\sqrt2\,[N(W)-N(U)]
&\leq(1-\eta)\|[\ell\ell^T-\widehat\ell\widehat\ell^T]D\|_*\\
&\leq2a(1-\eta)\alpha.
\end{aligned}
\tag{U.56}
$$

For the last step, two unit-vector projections with inner product $\sqrt{1-\alpha^2}$ have difference with nonzero eigenvalues $\alpha,-\alpha$. This follows by restricting to their at-most-two-dimensional span, where its trace is zero and its squared trace is $2\alpha^2$. Its trace norm is therefore $2\alpha$, including $\alpha=0,1$. Apply $\|HD\|_*\leq\|H\|_*\|D\|_{\mathrm{op}}$ and $\|D\|_{\mathrm{op}}=a$.

Thus $N(V)\leq N_0+E$. Combining this with the actual identity for $R(V)$ in (U.51) gives the first inequality of (U.54). The core theorem applied to $U$ gives $N_0+\sqrt{R_0}/2\leq\sqrt{c-s^2/1440}$. Subtract and add precisely this $\sqrt{R_0}/2$ to obtain the second inequality. Both root arguments are their actual nonnegative residuals; $R_0$ is even bounded below by $p$. Their difference has sign equal to that of $R-R_0=\delta-\tau$, proving the final statement and the sufficient implication.

Only the code term was bounded after removing the second singular component, and an explicit angle error was paid in comparing $W$ with $U$. The actual $P,V,\tau,\zeta,R$ remain the inputs to the target. The construction is not removal of trace parts from the original channel and does not assert feasibility or objective monotonicity of such a removal. $\square$

## 118. A scaled neighborhood of the rank-one core

**Corollary 118.1 (explicit constants).** Every feasible pair with

$$
\frac12\leq p\leq\frac9{10},\qquad
\chi_{\mathrm{err}}:=s_2+\sqrt{2\tau}\leq\frac{s_1}{5000}
\tag{U.57}
$$

satisfies

$$
\Theta(P,V)\leq r-\frac{s_1^2}{10000}.
\tag{U.58}
$$

Proof. For $s=s_1>0$ we have $q\geq1/10$, $m\geq q$, $1-\eta\leq s^2$, and (U.49). Hence

$$
E\leq\frac{\sqrt{p/q}}{2\sqrt2}s\chi_{\mathrm{err}}
\leq\frac98s\chi_{\mathrm{err}}.
$$

The last comparison uses $p/q\leq9$ and $3/(2\sqrt2)<9/8$. Concavity of the square root at $R_0\geq p>0$ gives

$$
\frac{\sqrt R-\sqrt{R_0}}2
\leq\frac{\delta-\tau}{4\sqrt{R_0}}
\leq\frac{\sigma^2}{2},\qquad \sigma=s_2.
$$

Here (U.51) and $R_0\geq1/2$ justify the coarser final constant, regardless of the sign of the root difference. Also, since $r<1$,

$$
\sqrt{c-s^2/1440}\leq r-\frac{s^2}{2880}.
$$

This follows either from the supporting line at $c$ or from rationalizing the difference, whose denominator is at most $2r<2$. Applying (U.54), and then (U.57) and $\sigma\leq\chi_{\mathrm{err}}$, gives

$$
\Theta\leq r-\frac{s^2}{2880}
+\frac98s\chi_{\mathrm{err}}+\frac{\sigma^2}{2}
\leq r-s^2\left(\frac1{2880}-\frac9{40000}-\frac1{50000000}\right).
$$

The excess of the parenthesized coefficient over $1/10000$ is exactly $9991/450000000>0$. If $s_1=0$, feasibility forces $V=0$ and (U.45) gives (U.58) directly, without dividing by $s_1$. The neighborhood and its margin both scale with $s_1$; no fixed positive gap is asserted near the equality point $V=0,p=c$. $\square$

## 119. Exact failure of the sufficient angle certificate

**Proposition 119.1 (feasible cancellation with a true target bound).** Consider the exact feasible point

$$
P=\operatorname{diag}(c,1-c),\qquad s=\frac25,\qquad
\sigma=(\sqrt2-1)s,\qquad
V_0=\operatorname{diag}(\sigma,-s),\qquad V_1=0.
\tag{U.59}
$$

It satisfies the strict scalar localization $p\in(p_-,p_+)$, $s_2^2<\delta_*$, $\tau+\zeta<\varepsilon_*$, and $0<s_1<1$. It fails both the scaled-neighborhood hypothesis (U.57) and the sufficient angle certificate (U.55), whereas $\mathcal S<c/2$ and $\Theta<r$ hold.

Proof. Its Gram is $G=\operatorname{diag}(\sigma^2,s^2)\preceq I_2$. Use the actual SVD with top $u=e_2$, $\ell=-e_2$ in the first copy, and second $u_\perp=e_1$, $k=e_1$ in that copy. Since $a/b=1+\sqrt2$, $a\sigma-bs=0$, so $\tau=0$. The separate top and second singular-component traces are $-bs$ and $a\sigma$, both nonzero; their cancellation is exact. Also $m=q$ and $\alpha=1$.

The actual residual and the top-only residual have the same smaller eigenvalue $q(1-s^2)$. Indeed their first diagonal entries are respectively $p(1-\sigma^2)$ and $p$, both strictly above $q(1-s^2)$, since $p>q$ and $\sigma<s$. Thus

$$
\lambda=\lambda_{\mathrm{top}}=q\eta^2,\qquad
\delta=\zeta=\mu=0,\qquad \eta=\frac{\sqrt{21}}5.
\tag{U.60}
$$

The scalar localization is strict. At $p=c$, (U.45) gives $L=2a+2b+2\sqrt2a$, so $2a+b-k_*=3-b-2\sqrt2a>0$: indeed $ab=1/(2\sqrt2)$ and $(b+2\sqrt2a)^2=3+7c=(26+7\sqrt2)/4<9$, since $7\sqrt2<10$. Hence $p_-<c<p_+$. Also

$$
\sigma^2=\frac{4(3-2\sqrt2)}{25}<\frac7{250}<\frac1{25}<\delta_*.
$$

For a direct rational verification of the final comparison, $\sqrt2<141422/100000$ implies $L<52263/10000$, hence $k_*<22263/10000$ and $\delta_*>5-(22263/10000)^2>1/25$; all these positive comparisons are checked by squaring. The first comparison follows from $\sqrt2>707/500$. Furthermore $\varepsilon_*>0$ follows from $L<3+\sqrt5$, so $\mu=0<\varepsilon_*$. The neighborhood fails because $\chi_{\mathrm{err}}=\sigma=(\sqrt2-1)s>s/5000$.

The root difference in (U.55) is zero, while

$$
E=\frac{a(1-\sqrt{21}/5)}{2\sqrt2}>\frac3{125},\qquad
r-\sqrt{c-1/9000}<\frac1{10000}.
\tag{U.61}
$$

For the first strict bound, $a>9/10$ and $\sqrt{21}/5<23/25$ give $E>9/(250\sqrt2)>3/125$. For the second, rationalize the difference; $c>17/20$ ensures both roots exceed $9/10$, so their sum exceeds $9/5$ and the difference is less than $1/16200$. Since $s^2/1440=1/9000$, (U.61) proves strict failure of the sufficient certificate.

Nevertheless $G$ commutes with $P$, and the residual has top eigenvector $e_1$. Moreover $p=c>4/(4+\sqrt2)$, as follows by multiplying by the positive denominator. Thus the high-spectrum calculation (U.24) applies. Its matrix (U.25) is positive definite because $pq>0$ and its determinant is $2pq(\sqrt2-1)>0$. The pair $(a_0,d_0)=(\sigma,-s)$ is nonzero, so that part of the negative quadratic is strictly negative; all other parts here vanish. Consequently $16(\mathcal S-\lambda_0)<0$, and (U.27) gives $\Theta<r$.

For completeness the actual root value, without the comparison error, is

$$
\Theta=\frac{a\bigl(1+\sqrt{1-\sigma^2}\bigr)+b(1+\eta)}{4\sqrt2}
+\frac12\sqrt{1-q\eta^2}.
$$

The preceding strict quadratic proof bounds this expression; no numerical approximation is needed. This point is excluded by the commuting theorem and is not a point satisfying the noncommutation condition of (U.28). It proves that the scalar localization alone does not force the angle certificate. It supplies no counterexample to (U.4), (U.5), or a physical recovery target. $\square$

## 120. Literature interfaces, admissible transfers and the remaining assertion

**Definition 120.1 (attributed tools and conventions).** The family-specific coupled estimates (U.11)–(U.61) are repo-derived consequences in the domain (U.1), with the source correspondence (U.3). No literature-priority assertion is attached to them. The general tools used inside their proofs are literature-attested at the following primary locators, with the stated boundaries.

The rectangular norm duality and singular-compatible block factorization are [Watrous, *Simpler semidefinite programs for completely bounded norms*, arXiv:1207.5726v2, Section 1 and Section 2.1, Lemma 2](https://arxiv.org/html/1207.5726v2), also identified in the [repository literature note](../../../Library/QuantumChannels/watrous2012simpler.md). Equation (6) is an infimum over positive definite test matrices; it gives no attaining inverse on a singular kernel. Its root fidelity is unsquared. The direct Hilbert–Schmidt proof (U.20) requires only the chosen weight to be positive definite, so it applies to singular code matrices without such an inverse.

The fixed-physical-input recovery interface is [Bény–Oreshkov, *Approximate simulation of quantum channels*, arXiv:1103.0649v3, Section IV, (132)–(133), and Corollary 5, (64)–(66)](https://arxiv.org/html/1103.0649v3), with the purification contractions in (54)–(55); see also the [repository literature note](../../../Library/QuantumChannels/beny2011simulation.md). The unrestricted CPTP completion and the fixed-state equation (133), rather than the Kraus-bounded (132) or a worst-case-input theorem, are the interfaces for (U.6). Its fixed-state root quantity is the square root of entanglement fidelity at the identity target. It does not supply the constant $c$.

The eigenvalue-pairing comparison is [Miszczak, Puchała, Horodecki, Uhlmann and Życzkowski, *Sub– and super–fidelity as bounds for quantum fidelity*, arXiv:0805.2037v2, (4), (9), Theorem 1 and the following two-dimensional equality discussion](https://arxiv.org/html/0805.2037v2), *Quantum Information and Computation* 9 (2009), 103–130. Its $F$ is squared fidelity, and the conversion in Theorem 110.1 takes a nonnegative square root. The $2\times2$ trace–determinant step in Theorem 113.2 is explicitly proved there from nonnegative eigenvalues; it is not a new general fidelity identity. Super-fidelity alone loses the sharp constant, as quantified below.

The positive-definite variational reference is [Bhatia–Jain–Lim, *On the Bures–Wasserstein distance between positive definite matrices*, arXiv:1712.01504v1, Section 2, Theorem 2(i)–(iii)](https://arxiv.org/html/1712.01504v1). Its hypotheses require positive definite $A,B$. The direct fixed-weight inequality (U.20) is valid without that restriction on $F$; no singular minimizer is imported from the reference.

The symmetry-projection reference is [Brahmachari–Rubboli–Tomamichel, *A fixed-point algorithm for matrix projections with applications in quantum information*, arXiv:2312.14615v3, Theorem 1 and Appendix B](https://arxiv.org/html/2312.14615v3). Theorem 1 assumes positive definite input $R$. Its fixed-point convergence result is not a theorem for the singular rank-constrained residual family here. A covariance or convex-average construction must still preserve the actual factor rank.

The finite-dimensional trace inequality has the additional bibliographic locator Rolf Dieter Grigorieff, *A Note on von Neumann's Trace Inequality*, *Mathematische Nachrichten* 151 (1991), 327–328, [DOI 10.1002/mana.19911510122](https://doi.org/10.1002/mana.19911510122). Its primary full text is not authenticated here; the available authenticated record is metadata. No unread theorem text or equality condition is a proof dependency, since the applicable pairing is supplied by the primary (9) above. Likewise Marcus Carlsson, *von Neumann's trace inequality for Hilbert–Schmidt operators*, *Expositiones Mathematicae* 39 (2021), 149–157, [DOI 10.1016/j.exmath.2020.05.001](https://doi.org/10.1016/j.exmath.2020.05.001), has an authenticated [institutional abstract and metadata record](https://lup.lub.lu.se/record/e477f327-ed31-4e35-a2c7-5a130e0415e8); its full theorem text remains unverified and contributes no additional equality or realizability assertion. Ky Fan's *On a Theorem of Weyl Concerning Eigenvalues of Linear Transformations I*, *PNAS* 35 (1949), 652–655, [DOI 10.1073/pnas.35.11.652](https://doi.org/10.1073/pnas.35.11.652), is a metadata-authenticated locator for the projection-eigenvalue background, with primary full text unavailable here. The new estimates use directly stated finite-dimensional variational and eigenvalue arguments, not an unchecked strengthening of that source. No Powers–Størmer theorem is used.

**Proposition 120.2 (two explicit limits of generic substitutes).** Super-fidelity need not certify the required sharp constant even on the zero-contraction calibration. Convex averaging of rank-two residual factors need not stay within the allowed residual-factor family.

Proof. For $\rho=I_4/4$ and $\sigma=\operatorname{diag}(P,P)/2$ with $p=c$, the squared-fidelity convention of Miszczak et al. gives

$$
F(\rho,\sigma)=\frac{(a+b)^2}{2}=c,
$$

since $pq=c(1-c)=1/8$. In Theorem 1 of that reference the upper bound is

$$
\operatorname{Tr}(\rho\sigma)
+\sqrt{(1-\operatorname{Tr}\rho^2)(1-\operatorname{Tr}\sigma^2)}
=\frac14+\frac{\sqrt{30}}8>c.
$$

Here $\operatorname{Tr}\rho^2=1/4$ and $\operatorname{Tr}\sigma^2=(p^2+q^2)/2=3/8$. The strict comparison is $\sqrt{30}>2+2\sqrt2$, whose positive sides square to $30>12+8\sqrt2$. This demonstrates slack in that substitute, not a failure of the target.

For the rank issue take four actual contractions $V^{(j)}=e_j e_1^T\in\mathbb R^{4\times2}$, $j=1,2,3,4$. Each has rank one and $(V^{(j)})^TV^{(j)}\preceq I_2$, but

$$
\frac14\sum_{j=1}^4V^{(j)}(V^{(j)})^T=I_4/4
$$

has rank four, whereas any $VV^T$ for a real $4\times2$ matrix has rank at most two. Thus averaging the positive matrices does not provide a common feasible factor of the required size. It supplies no convexity or simultaneous-realization shortcut for (U.1). $\square$

**Definition 120.3 (remaining universal tradeoff).** The universal assertion (U.4), equivalently the original half-beta $\lambda=1$ actual-minimal-Kraus-rank-three assertion (U.5) with every complex auxiliary density, remains unresolved. The commuting family, the all-direction rank-one zero-penalty family and the scaled neighborhood have the bounds proved above. Outside their union, (U.29) isolates the missing directional deficit; (U.55) is a sufficient common-root test, and Proposition 119.1 shows that it is not implied merely by the scalar localization. A universal proof must control the second singular direction, trace cancellation, actual residual and code loss jointly, or provide a different valid comparison. None of the separate upper bounds asserts a jointly attainable extremizer. The stronger universal squared inequality $\mathcal S\leq c/2$, equivalent to the uniform multiplier choice in volume II, Proposition 99.1, also remains unresolved outside the proved sectors.

The separate broader target is [volume I, Definition 47.2, (R.243)](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#47-applicability-and-the-remaining-recovery-problem):

$$
\delta_N:=\inf_{\mathcal R}\|\mathcal R N-\mathrm{id}_3\|_\diamond
\geq1-\sqrt{1-\beta}
$$

for every stipulated original-real actual encoder $N$ with arbitrary $0<\beta\leq1/2$, arbitrary admissible third columns and actual ranks up to nine, against all whole-output complex CPTP recoveries and all finite complex references, using the unhalved diamond norm. It remains unresolved separately from (U.5). Failure of a sufficient scalar or angle certificate is not a target counterexample; even a strict fixed-input witness failure would not by itself exhibit a recovery improving this full-reference diamond bound. The exact bridges in Section 109 retain their stated common-realization and physical-input conditions.

## 追加锚（本行以下为增补区）
