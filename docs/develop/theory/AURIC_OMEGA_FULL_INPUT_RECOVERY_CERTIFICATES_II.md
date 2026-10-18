# AURIC Ω full-input recovery certificates II

## 52. Actual channels, center supports and common contractions

**Definition 52.1 (the original-real class and the full-reference objective).** Let $N:M_3\to M_5$ be an actual original-real CPTP encoder of [Definition 1.1 and Theorems 1.2–1.3 of the first volume](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#1-the-complete-actual-real-frame-domain). Its Kraus matrices are real in the fixed original input and output bases, its actual phase-difference spectrum is $(a,\beta,0,-\beta,-a)$, and

$$
0<\beta\leq\frac12,\qquad a=1-\beta,\qquad
\chi_\pm=\frac{|0\rangle\pm i|1\rangle}{\sqrt2},\qquad
\mathcal C=\operatorname{span}\{|0\rangle,|1\rangle\}.
\tag{S.1}
$$

Choose a real Kraus compression of actual rank $r\leq9$ as in Theorem 1.3, and fix its Stinespring isometry and complement

$$
V:\mathbb C^3\longrightarrow\mathbb C^5_B\otimes E,
\qquad E=\mathbb C^r,\qquad
\Gamma(X)=\operatorname{Tr}_B(VXV^\dagger).
\tag{S.2}
$$

All admissible third columns remain in this class; no component in the active output space is removed. For positive semidefinite, possibly subnormalized operators write $f(Q,M)=\|\sqrt Q\sqrt M\|_1$. For an actual input density $\rho$ and any of its purifications, let $F_\rho(\Lambda_1,\Lambda_2)$ be root fidelity of the purified channel outputs. Put

$$
\begin{aligned}
F(\Lambda_1,\Lambda_2)&=\min_{\rho\in\mathsf D(\mathbb C^3)}F_\rho(\Lambda_1,\Lambda_2),\\
g_N&=\max_{R:M_5\to M_3\ {\rm CPTP}}F(RN,\mathrm{id}_3),\\
\delta_N&=\inf_{R:M_5\to M_3\ {\rm CPTP}}\|RN-\mathrm{id}_3\|_\diamond,\\
T&=\frac{1+\sqrt a}{2},\qquad v=\sqrt T,\qquad d=1-T.
\end{aligned}
\tag{S.3}
$$

Recoveries are all complex CPTP maps on the whole five-dimensional output. The diamond norm is unhalved and allows every finite complex reference. Dimension at most three suffices for an input-purification witness below; it does not narrow that supremum.

**Definition 52.2 (one supported center and transported reality).** Fix a density $\omega\in\mathsf D(E)$, let $S=\operatorname{supp}\omega$ and $k=\dim S$, and choose an eigenbasis on $S$ with

$$
\omega|_S=\operatorname{diag}(\lambda_1,\ldots,\lambda_k)>0,
\qquad \sum_i\lambda_i=1.
$$

With $F=\mathbb C^k$ define

$$
|\omega\rangle_{FE}=\sum_{i=1}^k\sqrt{\lambda_i}|i\rangle_F|i\rangle_E,
\qquad V_\omega\psi=\psi\otimes|\omega\rangle,
\qquad \mathcal C_\omega(X)=\operatorname{Tr}(X)\omega.
\tag{S.4}
$$

Only the center is represented on $S$; the encoder and its complement still use the actual environment $E$. Original environmental conjugation is the real-basis antiunitary $J_E$. A coordinate unitary $T_E$ transports it to $T_EJ_ET_E^\dagger$, which need not be entrywise conjugation in the new basis. The original input basis is unchanged. In phase coordinates its real structure remains the swapped conjugation (R.33) of the first volume, rather than entrywise reality of phase coordinates.

For one contraction $U:\mathbb C^5\to\mathbb C^3\otimes F$, $U^\dagger U\preceq I_5$, put

$$
\begin{aligned}
A_{\omega,U}&=V_\omega^\dagger(U\otimes I_E)V,\\
t_\psi&=V_\omega\psi,
&x_\psi&=(U\otimes\Pi_S)V\psi,
&r_\psi&=\operatorname{Re}\langle t_\psi,x_\psi\rangle
=\operatorname{Re}\langle\psi,A_{\omega,U}\psi\rangle.
\end{aligned}
\tag{S.5}
$$

The existing unequal-dimension Uhlmann interface (R.223) gives

$$
F_\rho(\Gamma,\mathcal C_\omega)
=\max_{U^\dagger U\preceq I_5}\operatorname{Re}\operatorname{Tr}(\rho A_{\omega,U}).
\tag{S.6}
$$

[Bény–Oreshkov, *Approximate simulation of quantum channels*, arXiv:1103.0649v3, (54)–(56)](https://arxiv.org/pdf/1103.0649v3) allows rectangular norm-one contractions and uses root fidelity. Its Corollary 5, (64)–(66), supplies the unrestricted CPTP recovery/complement identity

$$
g_N=\max_\omega\min_\rho F_\rho(\Gamma,\mathcal C_\omega).
\tag{S.7}
$$

The Kraus-bounded trace-nonincreasing optimization alone does not justify (S.7). The contraction in (S.6) is a purification variable, not a physical recovery with a Kraus bound.

**Theorem 52.3 (phase marginal, support compression and a single projection).** For every complex unit $\psi\in\mathcal C$, the environmental marginal $Q_\psi$ of $x_\psi$ satisfies

$$
0\preceq Q_\psi\preceq\Pi_S\Gamma(|\psi\rangle\langle\psi|)\Pi_S
\preceq aI_S,\qquad \operatorname{Tr}Q_\psi\leq1.
\tag{S.8}
$$

For $k=1$, every such direction satisfies $r_\psi\leq\sqrt a<v$. For $k\geq2$, choose one rank-five orthogonal projection $P$ on $\mathbb C^3\otimes F$ with $PU=U$, set $D=I-P$ and write

$$
H_\psi=(\langle\psi|\otimes I_F)P(|\psi\rangle\otimes I_F),
\qquad D_\psi=(\langle\psi|\otimes I_F)D(|\psi\rangle\otimes I_F).
\tag{S.9}
$$

The environmental marginal of $y_\psi=(P\otimes I_E)t_\psi$ is exactly

$$
M_\psi=\sqrt\omega H_\psi^T\sqrt\omega
=\omega-\sqrt\omega D_\psi^T\sqrt\omega,
\qquad 0\preceq M_\psi\preceq\omega,
\tag{S.10}
$$

and $\langle t_\psi,x_\psi\rangle=\langle y_\psi,x_\psi\rangle$. The transpose is the full transpose of the $F$ matrix in the paired eigenbases of (S.4).

Proof. By (R.3), $\Gamma(|\chi_+\rangle\langle\chi_-|)=0$ and the two phase marginals $\tau,\bar\tau$ have nonzero eigenvalues $a,\beta$. In the original real environment basis, writing $\psi=p\chi_++q\chi_-$ gives

$$
\Gamma(|\psi\rangle\langle\psi|)=|p|^2\tau+|q|^2\bar\tau\preceq aI_E,
\qquad |p|^2+|q|^2=1.
\tag{S.11}
$$

Changing environment coordinates transports both states and their conjugation together; the operator inequality survives without a new entrywise-bar hypothesis. For any environment ket $e$, the marginal quadratic form after applying $U$ is bounded by the one before applying $U$, since $I_5-U^\dagger U\succeq0$. Compressing this inequality to $S$ proves (S.8). It leaves (S.5) unchanged because $t_\psi$ is supported on $S$, and does not replace the actual encoder by a truncated channel.

For $k=1$, (S.8) gives $\|x_\psi\|^2\leq a$ and $\|t_\psi\|=1$, hence $r_\psi\leq\sqrt a$. To see $a<T$, put $u=\sqrt a\in[1/\sqrt2,1)$ and use $1+u-2u^2=(1-u)(2u+1)>0$. No rank-five padding is used in dimension three.

For $k\geq2$, $3k\geq6$ and $\operatorname{rank}U\leq5$, so complete its range to a five-dimensional subspace and take $P$. This one projection works for all inputs; equality $P=UU^\dagger$ is unnecessary. In tensor coordinates $(m,i)$, the $(i,j)$ entry of the environmental marginal of $y_\psi$ is

$$
\sqrt{\lambda_i\lambda_j}\sum_{m,l}\bar\psi_m\psi_lP_{(m,j),(l,i)}
=\sqrt{\lambda_i\lambda_j}(H_\psi)_{ji}.
\tag{S.12}
$$

Here $P^\dagger P=P$ was used in the partial trace. This proves the full transpose with the same complex input $\psi$. It is neither a conjugation of $\psi$ nor the reference-density transpose $q^T$ of (R.27). Since $0\preceq H_\psi\preceq I_F$, (S.10) is positive and bounded by $\omega$. Finally $PU=U$ fixes $x_\psi$ and proves the overlap identity. $\square$

## 53. A sufficient five-output spectral budget

**Theorem 53.1 (common-center variational and Ky Fan certificate).** Fix Section 52 with $k\geq2$. Let $X>0$ commute with $\omega$ on $S$. In a common eigenbasis write $X=\operatorname{diag}(x_i)$ and let $x_{(1)}\geq x_{(2)}$ be its largest two eigenvalues. Define

$$
A=\omega X^{-1},\qquad m_X=ax_{(1)}+\beta x_{(2)},\qquad
K_c=\operatorname{diag}(A,A,c\omega),\qquad c\geq0.
\tag{S.13}
$$

For a Hermitian matrix of order at least five let $S_5$ denote its five largest eigenvalues' sum, with multiplicities. If

$$
S_5(K_c)+2m_X\leq4v+cT,
\tag{S.14}
$$

then, for every contraction $U$, with the same actual $V$ and center $\omega$,

$$
\min\left\{\min_{\substack{\psi\in\mathcal C\\\|\psi\|=1}}r_\psi,\ r_{|2\rangle}\right\}\leq v.
\tag{S.15}
$$

Proof. For positive semidefinite operands and a positive definite weight, the variational-fidelity inequality is

$$
f(Q,M)\leq\frac12\bigl(\operatorname{Tr}(QX)+\operatorname{Tr}(MX^{-1})\bigr).
\tag{S.16}
$$

This is the upper direction of [Watrous, *The Theory of Quantum Information*, Theorem 3.19, (3.115)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf), including singular operands. Directly, write $f(Q,M)=\max_{W\ {\rm unitary}}|\operatorname{Tr}(\sqrt Q\sqrt M W)|$ and apply Hilbert–Schmidt Cauchy–Schwarz to $X^{1/2}\sqrt Q$ and $X^{-1/2}\sqrt M W$, followed by $2ab\leq a^2+b^2$. Their squared norms are $\operatorname{Tr}(QX)$ and $\operatorname{Tr}(MX^{-1})$. Neither $Q$ nor $M$ is inverted. Purification overlap is at most root fidelity, including subnormalized marginals.

In an ordered eigenbasis of $X$, the diagonal entries $q_i$ of $Q_\psi$ satisfy $0\leq q_i\leq a$ and $\sum_iq_i\leq1$. Therefore

$$
\begin{aligned}
\operatorname{Tr}(Q_\psi X)
&\leq x_{(1)}q_1+x_{(2)}\sum_{i\geq2}q_i\\
&\leq x_{(2)}+(x_{(1)}-x_{(2)})q_1
\leq ax_{(1)}+\beta x_{(2)}=m_X.
\end{aligned}
\tag{S.17}
$$

This relaxed maximum is attained at $q_1=a,q_2=\beta$, all others zero, since $\beta\leq a$. In the common diagonal basis, (S.10) gives

$$
\operatorname{Tr}(M_\psi X^{-1})
=\operatorname{Tr}(AH_\psi^T)=\operatorname{Tr}(AH_\psi)
=\operatorname{Tr}A-\operatorname{Tr}(AD_\psi).
\tag{S.18}
$$

Combining these inequalities yields, for every complex phase direction,

$$
2r_\psi\leq m_X+\operatorname{Tr}A-\operatorname{Tr}(AD_\psi).
\tag{S.19}
$$

Suppose all overlaps in (S.15) exceed $v$. Let $D_{ij}=(\langle i|\otimes I)D(|j\rangle\otimes I)$ in the original input basis. Testing $|0\rangle,|1\rangle$ gives

$$
\operatorname{Tr}[A(D_{00}+D_{11})]
<2(m_X+\operatorname{Tr}A-2v).
\tag{S.20}
$$

The actual contracted third-input vector has norm at most one. Its projected target has squared norm $1-\operatorname{Tr}(\omega D_{22})$, so Cauchy–Schwarz and $r_2>v$ imply

$$
q_2:=\operatorname{Tr}(\omega D_{22})<1-v^2=d.
\tag{S.21}
$$

These inequalities concern the same $V,\omega,U,P$.

The standard Ky Fan eigenvalue-sum principle ([Fan, *On a Theorem of Weyl Concerning Eigenvalues of Linear Transformations I*, PNAS 35, 652–655](https://doi.org/10.1073/pnas.35.11.652)) has the exact projection form needed here:

$$
S_5(K)=\max_{\substack{P'=P'^\dagger=P'^2\\\operatorname{rank}P'=5}}\operatorname{Tr}(KP').
\tag{S.22}
$$

For the needed finite-dimensional proof, diagonalize $K$ with $\kappa_1\geq\cdots\geq\kappa_{3k}$. The diagonal entries $p_j$ of a rank-five projection lie in $[0,1]$ and sum to five. Hence $\sum_j\kappa_jp_j\leq\sum_{j=1}^5\kappa_j$, attained by the top-five eigenspace. Thus this step retains rank five exactly. Applying it to our one $P$ gives

$$
\operatorname{Tr}(K_cD)
=2\operatorname{Tr}A+c-\operatorname{Tr}(K_cP)
\geq2\operatorname{Tr}A+c-S_5(K_c).
\tag{S.23}
$$

But (S.20)–(S.21) also give

$$
\operatorname{Tr}(K_cD)<2(m_X+\operatorname{Tr}A-2v)+cd.
\tag{S.24}
$$

Strictness persists at $c=0$ because (S.20) is strict. Comparing the bounds gives $S_5(K_c)+2m_X>4v+c(1-d)=4v+cT$, contradicting (S.14). Singular $K_c$ and $c=0$ are fully included. $\square$

**Theorem 53.2 (the sufficient full-reference implication).** For an actual channel of Definition 52.1, suppose every center of rank $k\geq2$ admits (S.14). Then

$$
g_N^2\leq T,\qquad \delta_N\geq2(1-T)=1-\sqrt{1-\beta}.
\tag{S.25}
$$

Proof. For a fixed center let $f_\omega(\rho)=F_\rho(\Gamma,\mathcal C_\omega)$. The input densities and rectangular-contraction ball are nonempty compact convex sets over their finite-dimensional real coordinates, and the pairing in (S.6) is continuous and real affine in each variable. The continuous convex-concave minimax theorem in [Watrous, Theorem 1.12](https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf) therefore gives

$$
\min_\rho f_\omega(\rho)
=\max_{U^\dagger U\preceq I_5}\min_\rho\operatorname{Re}\operatorname{Tr}(\rho A_{\omega,U})
=\max_{U^\dagger U\preceq I_5}\lambda_{\min}(\operatorname{Herm}A_{\omega,U}).
\tag{S.26}
$$

The least eigenvalue is at most the restricted test minimum in (S.15). Theorem 53.1 bounds that minimum by $v$ for each $U$; rank-one centers are covered by Theorem 52.3. Thus every center has $\min_\rho f_\omega(\rho)\leq v$, and (S.7) yields $g_N\leq v$.

For any allowed recovery $R$ and actual density $\rho$, let $|\Psi_\rho\rangle$ purify $\rho$ and put

$$
F_e(\rho,RN)=\langle\Psi_\rho|(RN\otimes\mathrm{id})(|\Psi_\rho\rangle\langle\Psi_\rho|)|\Psi_\rho\rangle.
$$

The binary measurement onto this pure target gives unhalved trace distance at least $2(1-F_e(\rho,RN))$. Consequently

$$
\|RN-\mathrm{id}_3\|_\diamond
\geq2\left(1-\min_\rho F_e(\rho,RN)\right)
=2\left(1-F(RN,\mathrm{id}_3)^2\right).
\tag{S.27}
$$

Taking the infimum over all complex whole-output recoveries gives $\delta_N\geq2(1-g_N^2)$, the direct lower interface of Theorem 7.4 in the first volume, proving (S.25). No equality involving the optimized diamond norm is required. The all-center assumption is only sufficient; Section 55 shows that this scalar assumption does not hold for all centers. $\square$

## 54. Individual centers with a spread spectrum

**Theorem 54.1 (a higher-rank center criterion).** Let $\omega$ have rank $3\leq k\leq r\leq9$ and ordered positive eigenvalues $\lambda_1\geq\cdots\geq\lambda_k$. If

$$
b_5:=2\lambda_1+2\lambda_2+\lambda_3\leq1+\sqrt{1-\beta}=2T,
\tag{S.28}
$$

then (S.15) holds at this center for every contraction and every actual encoder of Definition 52.1. In particular it holds at every uniform center $\omega=I_S/k$, $k\geq3$, for all $0<\beta\leq1/2$.

Proof. Choose $X=xI_S$ and $c=0$. Then $m_X=x$. The top five eigenvalues of $\operatorname{diag}(\omega/x,\omega/x,0)$ are $\lambda_1/x$ twice, $\lambda_2/x$ twice and $\lambda_3/x$ once. Hence

$$
S_5(K_0)+2m_X=\frac{b_5}{x}+2x\geq2\sqrt{2b_5},
\qquad x=\sqrt{b_5/2}\text{ attains equality}.
\tag{S.29}
$$

This scalar arithmetic-geometric mean step is only an intermediate. Condition (S.28) gives $2\sqrt{2b_5}\leq4\sqrt T=4v$, so these weights satisfy (S.14). For uniform centers $b_5=5/k\leq5/3$, and

$$
\frac53<1+\frac1{\sqrt2}\leq1+\sqrt a.
\tag{S.30}
$$

The strict comparison is equivalent to the positive-root comparison $2/3<1/\sqrt2$, proved by $4/9<1/2$. The last inequality uses $a\geq1/2$. $\square$

**Definition 54.2 (the center quantifier).** Condition (S.28) concerns one center. The optimization (S.7) still includes all other centers, including concentrated spectra. Theorem 54.1 does not locate a maximizing center in its subclass, and certification of uniform centers does not give the all-center hypothesis of Theorem 53.2.

## 55. Exact global calibration of the scalar certificate

**Theorem 55.1 (all commuting weights and both order cones).** At

$$
\beta=\frac12,\quad \omega=\operatorname{diag}(s,t),\quad
s=\frac7{10},\quad t=\frac3{10},\quad
h=\frac1{\sqrt2},\quad T=\frac{1+h}{2},\quad d=\frac{1-h}{2},
\tag{S.31}
$$

the global minimum over every positive definite $X$ commuting with $\omega$ and every $c\geq0$ is

$$
\begin{aligned}
\min_{X>0,\ [X,\omega]=0,\ c\geq0}
\left[S_5\!\left(\operatorname{diag}(\omega X^{-1},\omega X^{-1},c\omega)\right)+2m_X-cT\right]
&=2\sqrt{\frac75}+2\sqrt{\frac45-\frac1{2\sqrt2}}\\
&=:G_1.
\end{aligned}
\tag{S.32}
$$

It is attained uniquely at

$$
X_* =\operatorname{diag}\!\left(\sqrt{\frac75},\sqrt{\frac45-\frac1{2\sqrt2}}\right),
\qquad c_* =\left(\frac45-\frac1{2\sqrt2}\right)^{-1/2}.
\tag{S.33}
$$

Proof. The center has distinct eigenvalues, so every commuting positive weight is $X=\operatorname{diag}(x_1,x_2)$ with $x_i>0$. The substitution

$$
u=\frac{s}{x_1}>0,\qquad z=\frac{t}{x_2}>0
\tag{S.34}
$$

is a bijection of the positive quadrant. At half beta, $2m_X=x_1+x_2=s/u+t/z$, regardless of the ordering of the $x_i$. The six eigenvalues in the Ky Fan term are $u,u,z,z,cs,ct$. Since $s\geq t$, their smallest is $\min(u,z,ct)$, and the complete objective is

$$
\Phi(u,z,c)=\frac{s}{u}+\frac{t}{z}+2u+2z+cd-\min(u,z,ct).
\tag{S.35}
$$

No ordering of the other five eigenvalues is omitted. For $q=\min(u,z)>0$, its $c$-dependent term is

$$
cd-\min(q,ct)=
\begin{cases}
c(d-t),&0\leq c\leq q/t,\\
cd-q,&c\geq q/t.
\end{cases}
\tag{S.36}
$$

Here $0<d<t$: $h>2/5$ follows by squaring positive sides, since $1/2>4/25$. Thus the slopes are strictly negative before $q/t$ and strictly positive after it. The unique minimizing multiplier is $c=q/t$; this includes the search endpoint $c=0$ and the breakpoint. The reduced objective is

$$
\Phi_0(u,z)=\frac{s}{u}+\frac{t}{z}+2u+2z-
\left(1-\frac dt\right)\min(u,z).
\tag{S.37}
$$

Put $\mu=1+d/t=(t+d)/t>0$. On the entire closed order cone $u\geq z>0$,

$$
\Phi_0=\frac{s}{u}+2u+\frac{t}{z}+\mu z
\geq2\sqrt{2s}+2\sqrt{\mu t}=G_1.
\tag{S.38}
$$

The unique simultaneous equality point is

$$
u_0=\sqrt{s/2},\qquad z_0=\frac{t}{\sqrt{t+d}}.
$$

It lies strictly inside the cone because

$$
u_0^2-z_0^2=\frac{s(t+d)-2t^2}{2(t+d)}>0,
\qquad s(t+d)-2t^2=\frac3{100}+\frac7{10}d>0.
\tag{S.39}
$$

On the other closed cone $0<u\leq z$,

$$
\Phi_0=\frac{s}{u}+\mu u+\frac{t}{z}+2z.
\tag{S.40}
$$

It is strictly convex, with Hessian $\operatorname{diag}(2s/u^3,2t/z^3)>0$. Its unconstrained critical point has $u_1^2=s/\mu$ and $z_1^2=t/2$, so

$$
u_1^2-z_1^2=\frac{t(2s-t-d)}{2(t+d)}>0.
\tag{S.41}
$$

Indeed $2s-t=11/10>d$. The critical point is outside this second cone. Reciprocal terms keep bounded sublevels away from zero and positive linear terms keep them away from infinity. A constrained minimum exists. An interior minimum would be that inadmissible critical point, so the minimum lies on the shared boundary $u=z=w>0$. There

$$
\Phi_0(w,w)=\frac1w+\left(3+\frac dt\right)w
\geq2\sqrt{3+\frac dt}=:G_2,
\tag{S.42}
$$

with equality uniquely at $w=(3+d/t)^{-1/2}$. Thus the full opposite cone and common boundary have been included. Moreover

$$
\left(\frac{G_2}{2}\right)^2-\left(\frac{G_1}{2}\right)^2
=\left(\sqrt{\mu s}-\sqrt{2t}\right)^2>0.
\tag{S.43}
$$

Strictness is $\mu s>2t$, proved in (S.39). Both $G_i$ are positive; hence $G_2>G_1$ and (S.38) is the global minimum. Substituting $s,t,d$ gives (S.32), and converting $u_0,z_0,c=z_0/t$ back to the weights gives (S.33).

Finally (S.36) is a global lower bound in $c$ for every $u,z$. The reduced objectives have compact bounded sublevels, so no sequence with $u$ or $z$ approaching zero or infinity can improve the minimum. With $u,z$ bounded, $cd-q$ tends to infinity with $c$. These facts include all boundary limits in the original positive-weight domain as well as $c=0$. $\square$

**Theorem 55.2 (the exact strict gap).** At (S.31), $G_1>4v$. Thus no positive commuting $X$ and $c\geq0$ satisfy (S.14) there.

Proof. Put

$$
L=\sqrt{\frac75}+\sqrt{\frac45-\frac h2},\qquad
A_0=\frac{28}{25}-\frac{7h}{10},\qquad B_0=\frac{5h}{2}-\frac15.
\tag{S.44}
$$

All square roots and both $A_0,B_0$ are positive: $0<h<1$ proves positivity of $A_0$, and $h>2/5$ proves positivity of $B_0$. Direct expansion with $v^2=(1+h)/2$ gives

$$
L^2-(2v)^2=2\sqrt{A_0}-B_0,
\qquad 4A_0-B_0^2=\frac{263-360h}{200}.
\tag{S.45}
$$

Both $263$ and $360h$ are positive and

$$
263^2-(360h)^2=263^2-\frac{360^2}{2}=4369>0.
\tag{S.46}
$$

Therefore $263>360h$, then $2\sqrt{A_0}>B_0$, then $L>2v$ and $G_1=2L>4v$. Every squaring used positive sides. The sign follows from the positive integer (S.46), without a numerical minimum or approximate sign test. $\square$

## 56. Pinching the specified natural matrix extension

**Theorem 56.1 (noncommuting weights in the same certificate).** Fix a supported diagonal center of rank $k\geq2$ as in Section 52, but now allow every Hermitian $X>0$. Define precisely

$$
\begin{aligned}
B_X&=(\sqrt\omega X^{-1}\sqrt\omega)^T,\\
m_X&=a\lambda_1(X)+\beta\lambda_2(X),\\
J_c(X)&=S_5\!\left(\operatorname{diag}(B_X,B_X,c\omega)\right)+2m_X-cT,
\qquad c\geq0.
\end{aligned}
\tag{S.47}
$$

The eigenvalues in $m_X$ are decreasingly ordered. The sufficient certificate remains $J_c(X)\leq4v$. If $\mathcal E$ is diagonal pinching in this chosen eigenbasis of the center, then

$$
J_c(\mathcal E X)\leq J_c(X)
\quad\text{for every }X>0,\ c\geq0.
\tag{S.48}
$$

In particular the global minimum of Section 55 is also the infimum over all positive $X$ in this specified extension.

Proof. For general $X$ the trace identity is

$$
\operatorname{Tr}(M_\psi X^{-1})
=\operatorname{Tr}(\sqrt\omega X^{-1}\sqrt\omega H_\psi^T)
=\operatorname{Tr}(B_XH_\psi).
\tag{S.49}
$$

The full transpose is essential. The product $\omega X^{-1}$ is generally non-Hermitian and cannot replace $B_X$. The budget (S.17) still holds in the eigenbasis of $X$. Repeating (S.19)–(S.24) with $B_X$ in place of $A$ proves the same sufficient implication. Thus (S.47) specifies the extension being considered.

Let $X_0=\mathcal E X>0$. The inverse Jensen/pinching inequality is

$$
X_0^{-1}\preceq\mathcal E(X^{-1}).
\tag{S.50}
$$

It is the inverse-function instance of the operator Jensen mechanism in [Hansen–Pedersen, *Jensen's operator inequality*, arXiv:math/0204049, Theorem 2.1(ii)](https://arxiv.org/pdf/math/0204049). For this finite pinching there is a direct proof: the block matrix

$$
\begin{pmatrix}X&I\\I&X^{-1}\end{pmatrix}
=\begin{pmatrix}X^{1/2}\\X^{-1/2}\end{pmatrix}
\begin{pmatrix}X^{1/2}&X^{-1/2}\end{pmatrix}\succeq0
$$

is positive. Average its simultaneous block conjugations by all diagonal sign unitaries to obtain

$$
\begin{pmatrix}\mathcal EX&I\\I&\mathcal E(X^{-1})\end{pmatrix}\succeq0.
$$

Its Schur complement is (S.50). No singular matrix is inverted. Multiplication by $\sqrt\omega$ and full transposition preserve the positive order here, and pinching commutes with both operations, so

$$
B_{X_0}\preceq\mathcal E(B_X).
\tag{S.51}
$$

By (S.22), $S_5$ is convex, unitarily invariant and monotone in positive order. Simultaneous sign conjugation on the first two blocks, leaving $c\omega$ fixed, and averaging give

$$
\begin{aligned}
S_5\!\left(\operatorname{diag}(B_{X_0},B_{X_0},c\omega)\right)
&\leq S_5\!\left(\operatorname{diag}(\mathcal EB_X,\mathcal EB_X,c\omega)\right)\\
&\leq S_5\!\left(\operatorname{diag}(B_X,B_X,c\omega)\right).
\end{aligned}
\tag{S.52}
$$

Also, with $S_2(X)=\lambda_1(X)+\lambda_2(X)$,

$$
m_X=(a-\beta)\lambda_1(X)+\beta S_2(X).
\tag{S.53}
$$

Both coefficients are nonnegative. The rank-one and rank-two versions of the diagonal proof of (S.22) make $\lambda_1$ and $S_2$ convex and unitarily invariant. Therefore $m_{\mathcal EX}\leq m_X$, proving (S.48). The pinched weight commutes with $\omega$, and commuting weights form a subset of all weights. At (S.31) the two infima therefore agree with $G_1$, attained by (S.33). This excludes improvement by this precise extension. Direction-dependent weights and other matrix methods are outside (S.47). $\square$

## 57. The common-defect nonlinear directional interface

**Theorem 57.1 (all directions before taking their trace).** Fix one $V,\omega,U,P$ as in Section 52 with $k\geq2$. Let $X>0$ and use $B_X,m_X$ of (S.47). If every phase-plane real overlap exceeds $v$, the Hermitian $2\times2$ matrix

$$
(\mathcal K_X)_{ij}=\operatorname{Tr}(B_XD_{ij}),\qquad i,j\in\{0,1\},
$$

satisfies

$$
\mathcal K_X\prec(m_X+\operatorname{Tr}B_X-2v)I_{\mathcal C}.
\tag{S.54}
$$

For commuting diagonal weights this is the matrix relation whose trace is (S.20).

Proof. Since $D_{ji}=D_{ij}^\dagger$ and $B_X$ is Hermitian, $\mathcal K_X$ is Hermitian. By (S.16), (S.17) and (S.49), every complex unit $\psi\in\mathcal C$ satisfies

$$
\psi^\dagger\mathcal K_X\psi
=\operatorname{Tr}(B_XD_\psi)
\leq m_X+\operatorname{Tr}B_X-2r_\psi
<m_X+\operatorname{Tr}B_X-2v.
$$

Every unit eigenvector of $\mathcal K_X$ is one of these directions, so its largest eigenvalue is strictly below the displayed scalar. Taking the trace retains only one consequence of the full directional family. $\square$

**Theorem 57.2 (a nonlinear common-projection necessary system).** Fix one $V,\omega,U,P$ of Theorem 52.3 with $k\geq2$, and set $n=3k-5$. Factor the same defect projection as $D=WW^\dagger$, $W^\dagger W=I_n$, write $W_i:\mathbb C^n\to F$ for its three $k\times n$ block rows, and put $Z_i=\overline{W_i}$ in the paired center coordinates. Then

$$
\sum_{i=0}^2Z_i^\dagger Z_i=I_n,
\qquad \operatorname{rank}D=n,
\qquad \sum_{j=0}^2D_{ij}D_{jl}=D_{il}.
\tag{S.55}
$$

For every complex unit $\psi=(\psi_0,\psi_1)\in\mathcal C$ define

$$
\begin{aligned}
Z_\psi&=\psi_0Z_0+\psi_1Z_1,\\
M_\psi&=\omega-\sqrt\omega Z_\psi Z_\psi^\dagger\sqrt\omega,
& q_2&=\operatorname{Tr}(\omega Z_2Z_2^\dagger).
\end{aligned}
\tag{S.56}
$$

These are the marginal and charge of the same $P$ in (S.10) and (S.21). For $M\succeq0$ on $S$, let $b=\operatorname{Tr}M$, $\ell=\lambda_{\max}(M)$ and define

$$
H_a(M)=
\begin{cases}
0,&b=0,\\
\sqrt b,&b>0,\ \ell\leq ab,\\
\sqrt{a\ell}+\sqrt{\beta(b-\ell)},&b>0,\ \ell>ab.
\end{cases}
\tag{S.57}
$$

For $k\geq2$ this is the exact relaxed marginal maximum

$$
H_a(M)=\max_{\substack{0\preceq Q\preceq aI_S\\\operatorname{Tr}Q\leq1}}f(Q,M).
\tag{S.58}
$$

If all real overlaps in (S.15) exceed $v$, the following joint system is necessary:

$$
\begin{gathered}
\sum_{i=0}^2Z_i^\dagger Z_i=I_{3k-5},\qquad
0\preceq M_\psi\preceq\omega,\\
H_a(M_\psi)>v
\quad\text{for every complex unit }\psi\in\mathcal C,\\
\operatorname{Tr}(\omega Z_2Z_2^\dagger)<d.
\end{gathered}
\tag{S.59}
$$

The same three $Z_i$ occur in every direction, including every relative complex phase.

Proof. Isometric factorization of a rank-$n$ projection gives $W$. Conjugating $W^\dagger W=I_n$ proves the first identity of (S.55); rank and idempotence give the other two. Also

$$
D_\psi=\sum_{i,j=0}^1\bar\psi_i\psi_jW_iW_j^\dagger,
\qquad
D_\psi^T=\sum_{i,j=0}^1\bar\psi_i\psi_j\overline{W_j}W_i^T
=Z_\psi Z_\psi^\dagger.
\tag{S.60}
$$

Substitution in (S.10) proves (S.56). The third-input identity is $D_{22}^T=Z_2Z_2^\dagger$, and the diagonal real $\omega$ gives $\operatorname{Tr}(\omega D_{22})=\operatorname{Tr}(\omega Z_2Z_2^\dagger)$. Compressing $0\preceq D\preceq I$ also proves $0\preceq M_\psi\preceq\omega$.

To evaluate (S.58), pinch $Q$ in an eigenbasis of $M$. This preserves the operator and trace constraints. Fidelity concavity in $Q$ and invariance under the diagonal sign unitaries fixing $M$ show that pinching cannot decrease its value. The required PSD concavity follows from [Watrous, Chapter 3, Theorem 3.25, (3.165)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf) and homogeneity; its normalized-state version is Corollary 3.26. Thus the maximum is

$$
\max\left\{\sum_{i=1}^k\sqrt{\mu_iq_i}:
0\leq q_i\leq a,\ \sum_iq_i\leq1\right\},
\quad \mu_1=\ell\geq\cdots\geq\mu_k\geq0,
\quad \sum_i\mu_i=b.
\tag{S.61}
$$

For $b=0$ the value is zero. For $b>0$ and $\ell\leq ab$, Cauchy–Schwarz bounds the sum by $\sqrt b$, attained by $q_i=\mu_i/b\leq a$. This includes the branch boundary $\ell=ab$.

If $\ell>ab$ and $b>\ell$, then, for fixed $q_1\leq a$, Cauchy–Schwarz on the remaining coordinates gives

$$
\sum_i\sqrt{\mu_iq_i}
\leq\sqrt{\ell q_1}+\sqrt{(b-\ell)(1-q_1)}.
\tag{S.62}
$$

The right side is increasing on $0\leq q_1\leq a$: its unconstrained maximum is at $q_1=\ell/b>a$, and its derivative is positive for $0<q_1<\ell/b$, by squaring the positive comparison of its derivative terms. Its value at $a$ is the third branch of (S.57), attained by

$$
q_1=a,\qquad q_i=\frac{\beta\mu_i}{b-\ell}\quad(i\geq2).
\tag{S.63}
$$

These remaining entries sum to $\beta$ and each is at most $\beta\leq a$. If $b=\ell>0$, $M$ has rank one and $q_1=a$, all other entries zero, attains $\sqrt{a\ell}$; unused trace is allowed. The two nonzero branches agree at $\ell=ab$, since $\sqrt{a^2b}+\sqrt{\beta^2b}=\sqrt b$. This proves (S.58), including all singular ranks and boundaries.

Finally, for the actual marginals, $r_\psi\leq f(Q_\psi,M_\psi)\leq H_a(M_\psi)$ by (S.8) and the purification overlap bound. Thus $r_\psi>v$ forces the full complex-direction family in (S.59). Its last inequality is (S.21). The maximization (S.58) relaxes actual marginals from one $V,\omega,U,P$; it does not select a different actual channel for each direction. $\square$

## 58. Actual lifting, attribution and the remaining all-class statement

**Definition 58.1 (what the scalar obstruction leaves unspecified).** The Ky Fan extremum (S.22) uses genuine rank-five projections and is exact. The passage from actual common objects to (S.14) instead relaxes joint information at several places: actual directional $Q_\psi$ are bounded only by $Q\preceq aI$ and $\operatorname{Tr}Q\leq1$; one weight replaces nonlinear fidelity; all directional inequalities are reduced to two basis tests and then their trace; and the resulting traces are optimized without complete common directional and block relations. The scalar obstruction does not identify a unique one of these losses as its sole cause.

Conversely the first equation of (S.55) reconstructs an isometry $W$ by conjugating and stacking the $Z_i$, and hence a genuine defect projection $WW^\dagger$ with a rank-five complement. This reconstructs the projection geometry, not an actual encoder or the contraction overlaps in (S.5). A relaxed solution of (S.59) would still need a common actual $V$, a common $U$ with $U^\dagger U\preceq I_5$ and $PU=U$, and the same center $\omega$ whose actual contracted marginals and overlaps meet the required inequalities. Separate saturation of (S.58) in each direction does not supply these data.

In particular the complementary channel must satisfy the complete phase-Choi conditions (R.3)–(R.5) of the first volume. In the original real environment frame these require

$$
J_p=\begin{pmatrix}
\tau&0&C\\0&\bar\tau&\bar C\\C^\dagger&C^T&\sigma
\end{pmatrix},\qquad
\tau\succeq0,\quad\operatorname{spec}_{>0}\tau=(a,\beta),\quad
\sigma=\bar\sigma=\sigma^T,\quad
\operatorname{Tr}\tau=\operatorname{Tr}\sigma=1,\quad\operatorname{Tr}C=0,
\tag{S.64}
$$

$$
\operatorname{ran}C\subseteq\operatorname{ran}\tau,\qquad
S_{\rm res}=\sigma-C^\dagger\tau^+C-
\overline{C^\dagger\tau^+C}\succeq0,\qquad
\operatorname{rank}S_{\rm res}\leq1.
\tag{S.65}
$$

The inverse $\tau^+$ acts only on its actual support. In diagonal-center coordinates all these blocks and real structures must be transported together. Conditions (S.64)–(S.65) are not consequences of (S.59); they retain the original range, reality, rank and third-column requirements.

**Definition 58.2 (the remaining uniform problem).** The original problem keeps every actual channel of Definition 52.1, all $0<\beta\leq1/2$, every actual rank $r\leq9$, all admissible third columns, all complex whole-output CPTP recoveries and every finite complex reference. Its lower-bound target is

$$
\inf_{N\in\mathcal R_\beta}\ \inf_{R:M_5\to M_3\ {\rm CPTP}}
\|RN-\mathrm{id}_3\|_\diamond\geq1-\sqrt{1-\beta},
\tag{S.66}
$$

where $\mathcal R_\beta$ is the actual original-real passive class. Together with the existing matching upper construction this is the equality target of Definition 10.2 of the first volume. The complete half-beta actual-rank-two proof is already Theorems 44.2–45.1 there, and is not repeated here.

Theorem 54.1 proves (S.15) only at its individual center subclass. Section 55 rules out an all-center proof by (S.14); Section 56 extends that method obstruction precisely to (S.47). Neither obstruction is an actual encoder counterexample to (S.66). They do not exclude direction-dependent weights or other matrix methods. No theorem locating all actual maximizing centers in the spread subclass is supplied.

Uniform infeasibility of (S.59) at the remaining centers would suffice for (S.15). Its truth over the full remaining domain is unresolved. A feasible point of that relaxation requires the actual lifting of Definition 58.1 before it can challenge the common-contraction bound, and still does not supply a recovery with an improving full-reference diamond upper certificate. No such actual improving encoder/recovery pair or uniform joint infeasibility is supplied here. The arbitrary-rank target (S.66) remains unchanged.

**Definition 58.3 (mathematical attribution and scope).** The recovery/complement and rectangular-contraction interfaces (S.6)–(S.7) are `literature-attested` in Bény–Oreshkov, *Approximate simulation of quantum channels*, arXiv:1103.0649v3, (54)–(56), Corollary 5, (64)–(66); their fixed-input counterparts are (132)–(133). They concern root fidelity and unrestricted complex CPTP channels. The conventions and lower diamond interface agree with Definitions 1.1 and 10.1, Theorems 6.1 and 7.4, and Sections 44–45 of the first volume. The only fidelity-to-diamond implication used here is (S.27).

Variational fidelity, fidelity concavity, compact convex-concave minimax, inverse Jensen/pinching and scalar arithmetic-geometric mean are established intermediates. Their applications above retain singular operands, positive definite weights, compact finite-dimensional optimization sets and nonnegative coefficients where required. Watrous, *The Theory of Quantum Information*, Chapter 3, Theorems 3.19 and 3.25, and Chapter 1, Theorem 1.12, give the stated fidelity and minimax forms. Hansen–Pedersen, *Jensen's operator inequality*, Theorem 2.1, gives the operator Jensen form; its finite inverse-pinching case is also proved in (S.50). The Ky Fan eigenvalue-sum step is the standard exact projection extremum, with the needed finite-dimensional proof in (S.22), not a new variational theorem.

The source-specific compositions in Theorems 52.3, 53.1–53.2, 54.1, 55.1–55.2, 56.1 and 57.1–57.2 are `repo-derived` ordinary finite-dimensional arguments using these intermediates and the actual phase-class domain. This attribution identifies the displayed derivations, not global novelty, priority, physical realization or a theorem for arbitrary complex encoders. Original-real assumptions enter through (S.11) and the actual lifting conditions; they do not restrict complex recoveries or references.

## 追加锚（本行以下为增补区）

## 59. One common defect vector on the two leading center coordinates

**Definition 59.1 (supported normal form and parameters).** Work in the paired center coordinates of (S.55)–(S.59), with one supported positive center and one common triple of matrices. Write

$$
\begin{gathered}
3\leq k\leq9,\qquad n=3k-5,\qquad
\omega=\operatorname{diag}(s,t,\lambda_3,\ldots,\lambda_k)>0,\\
s\geq t\geq\lambda_3\geq\cdots\geq\lambda_k>0,\qquad
\operatorname{Tr}\omega=1,\qquad \epsilon=1-s-t>0,\\
\Omega_2=\operatorname{diag}(s,t),\qquad
\omega_{\rm tail}=\operatorname{diag}(\lambda_3,\ldots,\lambda_k),\\
T_a=\frac{1+\sqrt a}{2},\qquad d_a=\frac{1-\sqrt a}{2},\qquad
v_a=\sqrt{T_a},\qquad a=1-\beta,\quad0<\beta\leq\frac12.
\end{gathered}
\tag{S.67}
$$

The symbols $T_a,d_a,v_a$ are the $T,d,v$ of (S.3). Relaxed feasibility means precisely (S.59), with $H_a$ given by (S.57)–(S.58). The support is fixed before forming the normalized matrices; no arbitrary compression of a larger projection is asserted to preserve its rank. Center eigenvalue degeneracies are allowed.

**Theorem 59.2 (one vector for every complex direction).** For every normalized triple in (S.55), there is one unit vector $\eta$ supported on $\mathbb C^3\otimes K_2$, where $K_2$ is a two-dimensional span of selected leading eigenvectors of $\omega$, and one complex $2\times2$ matrix $L$, such that, simultaneously for every complex unit $\psi=(\psi_0,\psi_1)$,

$$
\begin{gathered}
\eta=(\ell_0,\ell_1,b_{\rm vec}),\qquad
L=[\ell_0,\ell_1],\qquad G=LL^\dagger,\qquad
\operatorname{Tr}G+\|b_{\rm vec}\|^2=1,\\
z=L\psi,\qquad \kappa=\|z\|^2\leq1,\qquad q=z^\dagger\Omega_2z,\\
0\preceq M_\psi\preceq B_\psi:=A_\psi\oplus\omega_{\rm tail},\qquad
A_\psi=\Omega_2-\sqrt{\Omega_2}zz^\dagger\sqrt{\Omega_2}\succeq0,\\
H_a(M_\psi)\leq H_a(B_\psi),\qquad
q_2\geq b_{\rm vec}^\dagger\Omega_2b_{\rm vec}
\geq t(1-\operatorname{Tr}G).
\end{gathered}
\tag{S.68}
$$

Here $\ell_0,\ell_1,b_{\rm vec}$ are expressed in $K_2$. The exact reduced test uses

$$
\begin{aligned}
\operatorname{Tr}A_\psi&=s+t-q,&\det A_\psi&=st(1-\kappa),\\
\mu_\psi&=\frac{s+t-q+\sqrt{(s+t-q)^2-4st(1-\kappa)}}2,\\
b_\psi:=\operatorname{Tr}B_\psi&=1-q,&
\ell_\psi:=\lambda_{\max}(B_\psi)&=\max\{\mu_\psi,\lambda_3\}.
\end{aligned}
\tag{S.69}
$$

Thus (S.57), evaluated at $(b_\psi,\ell_\psi)$, gives $H_a(B_\psi)$ exactly, and feasibility requires $H_a(B_\psi)>v_a$ for every complex unit $\psi$, as well as $t(1-\operatorname{Tr}G)<d_a$. The same $\eta$ and $L$ serve the entire sphere and every permitted $\beta$ at the specified center and projection. Singular $L$, $A_\psi$ and $M_\psi$ are included.

Proof. Stack the three $Z_i$ of (S.55) into $Z$. Its columns are orthonormal, so

$$
E_Z=ZZ^\dagger=\overline D,
\qquad E_Z^\dagger=E_Z^2=E_Z,\qquad \operatorname{rank}E_Z=n.
$$

This is the conjugated defect projection, rather than $D$ with its conjugation suppressed. For subspaces $A,B$ of a space of dimension $3k$, the identity $\dim(A+B)=\dim A+\dim B-\dim(A\cap B)\leq3k$ gives, in this instance,

$$
\dim\bigl(\operatorname{ran}E_Z\cap(\mathbb C^3\otimes K_2)\bigr)
\geq(3k-5)+6-3k=1.
\tag{S.70}
$$

Choose one unit $\eta$ in that intersection. Its three blocks give $L,G,b_{\rm vec}$ in (S.68). Since $E_Z\eta=\eta$, the restriction of $E_Z$ to $\eta^\perp$ is a projection, and hence $E_Z\succeq\eta\eta^\dagger$.

For the same complex $\psi$ as in (S.56), set $C_\psi=(\psi_0,\psi_1,0)\otimes I_k$. This is the transpose row $\psi^T$ on the phase plane, not the adjoint row $\psi^\dagger$. It satisfies $C_\psi C_\psi^\dagger=I_k$, $C_\psi Z=Z_\psi$ and $C_\psi\eta=L\psi$, with the latter embedded in $K_2$. Positive compression therefore gives

$$
0\preceq zz^\dagger\preceq C_\psi E_ZC_\psi^\dagger
=Z_\psi Z_\psi^\dagger\preceq I_k.
\tag{S.71}
$$

Congruence by $\sqrt\omega$ proves $0\preceq M_\psi\preceq B_\psi$. Also $\kappa\leq\|L\|_{\rm op}^2\leq\operatorname{Tr}G\leq1$, so $A_\psi=\sqrt{\Omega_2}(I_2-zz^\dagger)\sqrt{\Omega_2}\succeq0$, including $\kappa=1$. Compressing $E_Z\succeq\eta\eta^\dagger$ to the third block and taking its $\omega$-weighted trace proves the two lower bounds for $q_2$ in (S.68).

For any fixed feasible $Q$ in (S.58), positive order of $M\preceq B$ gives positive order of $\sqrt Q M\sqrt Q\preceq\sqrt Q B\sqrt Q$. Ordered eigenvalues, and their scalar square roots, increase under this order. Consequently

$$
f(Q,M)=\operatorname{Tr}\sqrt{\sqrt Q M\sqrt Q}
\leq\operatorname{Tr}\sqrt{\sqrt Q B\sqrt Q}=f(Q,B).
$$

Taking the maximum over the same feasible set proves the $H_a$ comparison. This uses no inverse of $Q$ or $M$, and does not assert that the maximizing $Q$ in different directions comes from one channel.

Finally, writing $z=(z_1,z_2)^T$ gives

$$
A_\psi=\begin{pmatrix}
s(1-|z_1|^2)&-\sqrt{st}z_1\bar z_2\\
-\sqrt{st}\bar z_1z_2&t(1-|z_2|^2)
\end{pmatrix},\qquad
\det A_\psi=st\bigl[(1-|z_1|^2)(1-|z_2|^2)-|z_1|^2|z_2|^2\bigr].
$$

This proves the trace and determinant in (S.69); the quadratic eigenvalue formula and the direct sum give the rest. The discriminant is nonnegative because $A_\psi$ is Hermitian. This reduces the test through the tail mass and its largest eigenvalue, while discarding the other defect directions. $\square$

## 60. Half-beta nonlinear and scalar necessities

**Theorem 60.1 (a stronger pencil bound and its scalar consequence).** Specialize to $\beta=1/2$ and set

$$
h=\frac1{\sqrt2},\qquad T=\frac{1+h}{2},\qquad d=\frac{1-h}{2},\qquad
\Delta=4s(1-s)-\frac12.
\tag{S.72}
$$

For $s\geq1/2$, every pencil of Theorem 59.2 satisfies the upper bound

$$
H_{1/2}(B_\psi)^2
\leq\frac{1-q}{2}+\sqrt{st(1-\kappa)+s\epsilon}.
\tag{S.73}
$$

If (S.59) is feasible, its one common $L$ must then satisfy, for every complex unit $\psi$,

$$
\begin{gathered}
4st\kappa+2hq+q^2<\Delta,\qquad \Delta>0,\\
B_0:=4stI_2+2h\Omega_2\succ0,\qquad
L^\dagger B_0L\prec\Delta I_2,\qquad
G\prec\Delta B_0^{-1}.
\end{gathered}
\tag{S.74}
$$

In particular the scalar necessary condition is

$$
q_2>f(s,t):=t-\Delta\left[\frac1{4s+2h}
+\frac{t}{s(4t+2h)}\right],\qquad f(s,t)<d.
\tag{S.75}
$$

The notation $f(s,t)$ in this section is this scalar function; the two-operator root fidelity remains $f(Q,M)$.

Proof. Put $b=1-q$ and let $\mu\geq\nu\geq0$ be the eigenvalues of $A_\psi$. Positive order $A_\psi\preceq\Omega_2$ gives $\mu\leq s$, while

$$
\mu+\nu=b-\epsilon,\qquad \mu\nu=st(1-\kappa),\qquad0\leq b\leq1.
$$

If $\mu\geq b/2$, every other eigenvalue of $B_\psi$ is at most the sum of those other eigenvalues, $b-\mu\leq\mu$. Formula (S.57), including its branch boundary, gives

$$
H_{1/2}(B_\psi)^2=\frac b2+\sqrt{\mu(\nu+\epsilon)}
\leq\frac b2+\sqrt{\mu\nu+s\epsilon}.
$$

If $\mu\leq b/2$, then $\mu\in[(b-\epsilon)/2,b/2]$. The polynomial $x(b-\epsilon-x)$ decreases on this interval, because its derivative is $b-\epsilon-2x\leq0$. Thus

$$
\mu\nu\geq\frac{b^2}{4}-\frac{b\epsilon}{2},\qquad
\mu\nu+s\epsilon\geq\frac{b^2}{4},
$$

where the second inequality uses $s\geq1/2\geq b/2$. For every $B\succeq0$, (S.58) and trace Cauchy–Schwarz give $H_a(B)^2\leq\operatorname{Tr}B=b$. Hence in this second case $H_{1/2}(B_\psi)^2\leq b\leq b/2+\sqrt{\mu\nu+s\epsilon}$. The case $b=0$ also satisfies the inequality. This proves (S.73) without selecting a cap branch on the basis of the tail spectrum, and permits singular pencils.

Feasibility and (S.68) force the right side of (S.73) to exceed $T$. Therefore

$$
2\sqrt{st(1-\kappa)+s\epsilon}>h+q>0.
$$

Both sides are positive, so squaring preserves the strict inequality. Since $t+\epsilon=1-s$ and $h^2=1/2$, its rearrangement is the first inequality of (S.74). Its left side is nonnegative, proving $\Delta>0$.

Drop only the nonnegative term $q^2$. The resulting inequality is $\psi^\dagger L^\dagger B_0L\psi<\Delta$ for every complex unit $\psi$. A largest-eigenvalue unit eigenvector is among these directions, so $L^\dagger B_0L\prec\Delta I_2$. In particular testing only two basis directions or only real directions would not justify this conclusion for a general complex $L$.

Let $K=B_0^{1/2}L$. The equality $\|K\|_{\rm op}=\|K^\dagger\|_{\rm op}$ gives $KK^\dagger\prec\Delta I_2$ from $K^\dagger K\prec\Delta I_2$. Congruence by $B_0^{-1/2}$ now proves $G\prec\Delta B_0^{-1}$, without requiring $L$ to be invertible. Here

$$
B_0=\operatorname{diag}\bigl(s(4t+2h),t(4s+2h)\bigr),\qquad
\operatorname{Tr}G<\Delta\left[\frac1{t(4s+2h)}+\frac1{s(4t+2h)}\right].
$$

All denominators are positive because $s,t,h>0$. Multiplying the strict trace bound by $t>0$ and using (S.68) gives $q_2\geq t(1-\operatorname{Tr}G)>f(s,t)$. Combining this with $q_2<d$ proves (S.75). The only inverse is of the positive definite $B_0$; neither $L$, $M_\psi$ nor $A_\psi$ is inverted. $\square$

**Proposition 60.2 (monotonicity and positive tails from a fixed boundary).** For $1/2\leq s<T$ and $t>0$, $f(s,t)$ increases strictly with $t$. For each such fixed $s$, a nonzero interval immediately below $t_0=1-s$ is excluded by (S.75), and therefore excludes positive-tail centers in that interval.

Proof. The roots of $\Delta$ are $d,T$, so $0<\Delta\leq1/2$ in this range. Differentiating only in $t$ gives

$$
\partial_t f=1-\frac{2h\Delta}{s(4t+2h)^2}\geq1-h>0.
\tag{S.76}
$$

Indeed $s(4t+2h)^2\geq(1/2)(2h)^2=1$ and $2h\Delta\leq h$. The scalar expression is defined for every $t>0$, whether or not that $t$ is the second eigenvalue of an ordered center.

At $t=t_0=1-s$, one has $d<t_0\leq1/2$ and $\Delta=4(t_0-d)(T-t_0)$. Put $C(s,t)=1/(4s+2h)+t/[s(4t+2h)]$. Then

$$
f(s,t_0)-d=(t_0-d)\bigl[1-4(T-t_0)C(s,t_0)\bigr].
$$

Clearing the positive denominator $s(4s+2h)(4t_0+2h)$ shows that the bracket has the sign of

$$
\begin{aligned}
D_0&=s(4st_0+2h+h^2)-2(T-t_0)(4st_0+h)\\
&=h-h^2t_0-4st_0(h-t_0)\\
&\geq h-h^2t_0-(h-t_0)=\frac{t_0}{2}>0.
\end{aligned}
\tag{S.77}
$$

The last step uses $s+t_0=1$, $4st_0\leq1$ and $h>t_0$. This is the boundary comparison already used in (R.228)–(R.229) of Theorem 44.2 of the first volume, with $c=h$; it is not a new rank-two result. Its use here is continuity of the explicit scalar function: since $f(s,t_0)>d$, there is $\varepsilon_s\in(0,t_0)$ such that $f(s,t)>d$ whenever $t_0-\varepsilon_s<t\leq t_0$. The part $t<t_0$ has $0<\epsilon=1-s-t<\varepsilon_s$, and so gives genuinely positive-tail exclusions in ranks $3$ through $9$ whenever the spectrum is ordered. Section 62 gives explicit rational widths and margins. $\square$

## 61. A common trace constraint and an exact quartic exclusion

**Theorem 61.1 (trace necessity and excluded leading eigenvalues).** At half beta, every feasible system (S.59) with positive support $3\leq k\leq9$ obeys

$$
3s+2t>3T,\qquad t>t_*(s):=\frac32(T-s),\qquad
\frac{31}{50}<s<T.
\tag{S.78}
$$

Proof. As used in Theorem 60.1, $H_a(M)^2\leq\operatorname{Tr}M$. The phase basis tests in (S.59) therefore give $\operatorname{Tr}(\omega Z_iZ_i^\dagger)<d$ for $i=0,1$; the same inequality for $i=2$ is $q_2<d$. For $E_Z$ of Theorem 59.2 and its rank-five complement $\widehat P=I-E_Z=\overline P$, it follows that

$$
\operatorname{Tr}((I_3\otimes\omega)E_Z)<3d,\qquad
\operatorname{Tr}((I_3\otimes\omega)\widehat P)>3-3d=3T.
$$

The eigenvalues of $I_3\otimes\omega$ repeat each center eigenvalue three times. The diagonal entries of a rank-five projection lie in $[0,1]$ and sum to five, so the weighted allocation argument of (S.22) bounds its trace by its five largest eigenvalues, $3s+2t$. This proves the first two inequalities of (S.78), with the same projection in all three tests.

If $s\leq1/2$, ordering implies $3s+2t\leq5s\leq5/2<3T$. To justify the strict last comparison, $h>7/10$ follows from $1/2>49/100$, and hence $3T>51/20>5/2$. This excludes that entire branch without using Theorem 60.1 there.

Consider next $1/2\leq s\leq31/50$. This closed interval is contained in $[1/2,T)$ because $T>17/20$, so $\Delta>0$ and $t_*(s)>0$. Clear the positive denominator in (S.75):

$$
\begin{aligned}
2s(2s+h)(2t+h)(f(s,t)-d)
&=N(s,t),\\
N(s,t)&=2s(2s+h)(2t+h)(t-d)
-\Delta\,[4st+h(s+t)].
\end{aligned}
\tag{S.79}
$$

Substitution of $t=t_*(s)=3(1+h-2s)/4$ and reduction by $h^2=1/2$ yields every coefficient of the quartic

$$
\begin{aligned}
N_*(s):=N(s,t_*(s))
={}&\frac3{16}+\frac{3h}{8}
+\left(\frac52+\frac{17h}{8}\right)s
+\left(-\frac{53}{4}-3h\right)s^2\\
&+(24-11h)s^3-6s^4.
\end{aligned}
\tag{S.80}
$$

For an exact sign on the entire interval, put $s=1/2+3u/25$, $0\leq u\leq1$. The power coefficients $a_i$ in $N_*(1/2+3u/25)=\sum_{i=0}^4a_iu^i$ are

$$
\begin{aligned}
a_0&=\frac34-\frac{11h}{16},&
a_1&=\frac{51}{100}-\frac{219h}{200},&
a_2&=\frac{99}{500}-\frac{351h}{1250},\\
a_3&=\frac{324-297h}{15625},&
a_4&=-\frac{486}{390625}.
\end{aligned}
$$

Using $u^i=\sum_{j=i}^4[\binom ji/\binom4i]\binom4j u^j(1-u)^{4-j}$ gives the consumed degree-four Bernstein representation

$$
N_*(1/2+3u/25)=\sum_{j=0}^4b_j\binom4j u^j(1-u)^{4-j},\qquad
b_j=\sum_{i=0}^j a_i\frac{\binom ji}{\binom4i}.
\tag{S.81}
$$

The identity for $u^i$ follows by $\binom4j\binom ji=\binom4i\binom{4-i}{j-i}$ and the binomial theorem. The complete coefficient list and strictly positive lower bounds are

| $j$ | $b_j$ | strict rational lower bound |
| --- | --- | --- |
| $0$ | $3/4-11h/16$ | $1319/5000$ |
| $1$ | $351/400-769h/800$ | $24713/125000$ |
| $2$ | $519/500-6409h/5000$ | $102743/781250$ |
| $3$ | $309171/250000-826951h/500000$ | $1309463/19531250$ |
| $4$ | $2308581/1562500-520577h/250000$ | $381533/78125000$ |

For these bounds use

$$
0<h<\frac{442}{625},\qquad 2\cdot442^2-625^2=103>0.
\tag{S.82}
$$

Both compared numbers are positive; the integer comparison proves $(442/625)^2>1/2=h^2$. Every coefficient of $h$ in the table is negative, so substituting this strict upper bound gives exactly the displayed lower bounds. Each Bernstein weight is nonnegative on $[0,1]$ and their sum is one. All five coefficients are strictly positive, proving $N_*(s)>0$ on $[1/2,31/50]$, including both endpoints.

Since the denominator of (S.79) is positive at $t_*(s)>0$, this proves $f(s,t_*(s))>d$. The trace necessity gives $t>t_*(s)$ and (S.76) gives $f(s,t)>f(s,t_*(s))>d$, contradicting (S.75). This argument does not require $t_*(s)$ itself to be an admissible ordered eigenvalue.

Finally $s<1$ on positive support. The exact factorization $\Delta=4(s-d)(T-s)$ implies $\Delta\leq0$ for $s\geq T$, contradicting (S.74). Thus $s=T$ is excluded as well, leaving exactly the asserted open leading-eigenvalue interval as a necessary condition. $\square$

## 62. Explicit positive-tail regions and center consumers

**Theorem 62.1 (a fixed leading eigenvalue and a full rectangle).** At half beta, (S.59) is infeasible at every ordered positive center of ranks $3$ through $9$ in either of the following regions:

$$
s=\frac7{10},\quad \frac{29}{100}\leq t<\frac3{10};
\qquad
\frac{699}{1000}\leq s\leq\frac{701}{1000},\quad
0<\epsilon=1-s-t\leq\frac1{100}.
\tag{S.83}
$$

Proof. In the fixed-$s$ band, $\Delta=17/50$ and $0<\epsilon\leq1/100$. The function $t/(4t+2h)$ increases with $t$, with derivative $2h/(4t+2h)^2>0$. Using $h>7/10$ and $t\leq3/10$ in the positive denominators gives

$$
C(s,t)\leq\frac5{21}+\frac{15}{91}=\frac{110}{273}.
$$

Consequently the exact rational margin is

$$
f(s,t)\geq\frac{29}{100}-\frac{17}{50}\frac{110}{273}
=\frac{4177}{27300}=\frac3{20}+\frac{41}{13650}>d,
\tag{S.84}
$$

where $d<3/20$ follows from $h>7/10$. This contradicts (S.75), including the $t=29/100$ endpoint. The upper endpoint $t=3/10$ is the zero-tail boundary, used only for the upper estimate of $C$.

In the rectangle, $289/1000\leq t\leq301/1000$, and $\Delta>0$. Since $\Delta$ decreases with $s>1/2$, it obeys $\Delta\leq85399/250000$, its value at $s=699/1000$. Each summand of $C(s,t)$ decreases with $s$ and with $h$, while the second increases with $t$. Thus

$$
\begin{aligned}
C(s,t)&\leq\frac1{4(699/1000)+7/5}
+\frac{301/1000}{(699/1000)(4(301/1000)+7/5)}\\
&=\frac{27528500}{68192343}.
\end{aligned}
$$

All factors used to clear denominators are positive. Because $C\geq0$ and $\Delta>0$, simultaneous upper bounds on these two factors give

$$
\begin{aligned}
f(s,t)&\geq\frac{289}{1000}
-\frac{85399}{250000}\frac{27528500}{68192343}\\
&=\frac{10303961641}{68192343000}
=\frac3{20}+\frac{75110191}{68192343000}>d.
\end{aligned}
\tag{S.85}
$$

This contradicts (S.75) on the full closed $s$ interval and at $\epsilon=1/100$, with $\epsilon=0$ excluded from the asserted positive-support region. These are rational inequalities for the whole rectangle, not sampled sign tests. $\square$

**Corollary 62.2 (individual centers beyond the spread criterion).** For each $k\in\{3,4,5,6,7,8,9\}$, the center spectrum

$$
\left(\frac7{10},\frac{29}{100},
\underbrace{\frac1{100(k-2)},\ldots,\frac1{100(k-2)}}_{k-2\text{ entries}}\right)
\tag{S.86}
$$

is excluded by Theorem 62.1, but does not meet the existing sufficient criterion (S.28).

Proof. The entries are strictly positive, ordered and sum to $7/10+29/100+1/100=1$. Their tail mass is $1/100$, so they lie in the rectangle (S.83). Their spread is

$$
2s+2t+\lambda_3=\frac{198}{100}+\frac1{100(k-2)}>1+h=2T,
$$

because $h<71/100<98/100$, where $h<71/100$ follows by squaring positive numbers, $1/2<5041/10000$. Thus (S.28) does not exclude these centers. Similarly $(3/5,39/100,1/100)$ is excluded by Theorem 61.1 and has spread $199/100>1+h$.

Within ordered positive spectra, the region $699/1000<s<701/1000$, $0<\epsilon<1/100$ is relatively open by continuity of these strict inequalities. It is nonempty in every stated rank: distribute $\epsilon$ equally among the $k-2$ tail entries. Then $t=1-s-\epsilon>289/1000$ exceeds each tail entry, so strict positivity and ordering hold for every $k=3,\ldots,9$. The rectangle exclusions therefore include positive tails in every stated rank.

By Theorem 57.2, infeasibility of (S.59) implies (S.15) at each excluded center, for every allowed actual $V$ and common contraction $U$ at that center. These are individual center examples consumed by that necessary-system exclusion, not actual encoder constructions or a statement about the location of any optimizer. $\square$

## 63. Residual necessary range, actual lifting and attribution

**Proposition 63.1 (the exact remaining certificate gap).** At half beta any feasible (S.59) with ordered positive spectrum and $3\leq k\leq9$ must satisfy all of

$$
\frac{31}{50}<s<T,\qquad
 t>\frac32(T-s),\qquad f(s,t)<d,\qquad
2s+2t+\lambda_3>2T.
\tag{S.87}
$$

These are necessary conditions, not a characterization of feasible centers. The exclusions of Section 62 are already enforced by $f(s,t)<d$.

Proof. The first three conditions are (S.75) and (S.78). For the last one, the two phase basis tests give $\operatorname{Tr}M_0+\operatorname{Tr}M_1>2T$. In the conjugated defect coordinates this sum equals $\operatorname{Tr}(\operatorname{diag}(\omega,\omega,0)\widehat P)$. The rank-five allocation in (S.22) bounds it by $2s+2t+\lambda_3$. This is exactly failure of the spread exclusion (S.28), reused within the nonlinear relaxation.

The rank-three spectrum $(7/10,1/4,1/20)$ is inconclusive for these conditions. It has $31/50<s<T$ and

$$
3s+2t=\frac{13}{5}>3T,\qquad
2s+2t+\lambda_3=\frac{39}{20}>2T.
$$

Indeed $h<71/100$ gives $3T<513/200<13/5$ and $2T<171/100<39/20$. Its $\Delta=17/50$ is independent of $h$; $C(s,t)$ decreases with $h$, so

$$
\begin{aligned}
f(7/10,1/4)
&<\frac14-\frac{17}{50}\left[
\frac1{4(7/10)+2(71/100)}
+\frac{1/4}{(7/10)(4(1/4)+2(71/100))}\right]\\
&=\frac{85251}{714868}<\frac3{25}<\frac{29}{200}<d.
\end{aligned}
\tag{S.88}
$$

The last inequality also uses $h<71/100$. Thus none of the displayed certificates excludes it. No common $Z$, strict all-direction relaxed point, or actual channel is supplied by this scalar calculation. $\square$

**Definition 63.2 (what remains to prove).** The one-vector reduction keeps one rank-one part of a rank-$(3k-5)$ defect. It drops the other defect directions and their orthogonality and coupling. The passage to (S.73) also bounds the exact nonlinear $H_a$ pencil, and (S.74) drops $q^2$ before taking a trace. Passing $f(s,t)<d$ therefore does not establish even the stronger one-vector directional inequalities, much less feasibility of (S.59). No strict relaxed feasible point or actual counterexample is established here.

The remaining analytic question is joint infeasibility of (S.59) on all surviving ordered positive centers, with the same normalized projection for the entire complex unit sphere. A proposed relaxed point would instead need a strict continuum verification, not separate directionwise optimizing marginals. For $0<\beta<1/2$, Theorem 59.2 supplies the all-complex common-vector reduction, but the numerical thresholds and regions of Sections 60–62 are asserted only at $\beta=1/2$.

Actual lifting still requires Definition 58.1: one allowed original-real Stinespring isometry $V$, one common rectangular contraction $U$, the same projection, and actual marginals and overlaps arising jointly, including phase/third superpositions. The actual phase family is the mixture (S.11) of $\tau$ and its conjugate in the original real frame; those mixtures need not have rank two. Their contracted marginals must obey the actual domination in (S.8), beyond the relaxed cap. The full phase-Choi range, trace, reality, Schur-residual and rank conditions (S.64)–(S.65) remain required. Diagonalizing the center transports the antiunitary with every actual block; it does not make those blocks jointly real or commuting.

Even actual common-contraction threshold failure would not by itself be a counterexample to (S.66). A counterexample requires an allowed actual encoder and a complex whole-output recovery with an unhalved diamond upper certificate strictly below $1-\sqrt{1-\beta}$ for all finite complex references. The original target retains all positive $\beta\leq1/2$, all admissible third columns and all actual ranks at most nine, as well as all those recoveries and references. That target remains unresolved.

**Definition 63.3 (reuse and mathematical scope).** Sections 59–63 are source-specific analytic compositions of (S.55)–(S.59), the marginal comparison in Section 52 and the rank-five trace allocation (S.22). The spread interface (S.28), the scalar-method limitation of Sections 55–56, and the half-beta actual-rank-two result in Sections 44–45 of the first volume remain their respective existing results. In particular (S.77) consumes the boundary comparison (R.228)–(R.229) to extend to positive tails; it does not recount that boundary calculation as a new rank-two theorem.

Dimension intersection, positive compression and fidelity monotonicity, the $2\times2$ determinant identity, equality of the operator norms of a matrix and its adjoint, and the Bernstein representation are established intermediates used at the displayed steps. The coefficient and rational-margin calculations are part of the concrete center exclusions, not new generic dimension, spectral-norm or Bernstein theorems. The derivations are `repo-derived` analytic mathematics; no kernel verification, global novelty, priority or literature-completeness claim is made. Excluding these individual center regions does not prove all-center infeasibility, locate an actual optimizer or construct an encoder.

## 追加锚（本行以下为增补区）

## 64. Overlapping certificates exclude every half-beta common projection

**Definition 64.1 (the common system and its spectral consumer).** Use the supported center, $T_a,d_a,v_a$, and $H_a$ of (S.57)–(S.59) and (S.67). For $k\geq2$, stack the same normalized matrices as $Z=(Z_0;Z_1;Z_2)$, so that

$$
E_Z=ZZ^\dagger=\overline D,\qquad Z^\dagger Z=I_{3k-5},\qquad
\widehat P=I-E_Z,\qquad\operatorname{rank}\widehat P=5.
\tag{S.89}
$$

Here $E_Z$ is the conjugated defect projection. The input compression remains $C_\psi=(\psi_0,\psi_1,0)\otimes I_k$, with the transpose row $\psi^T$, as in (S.71). Thus $C_\psi E_ZC_\psi^\dagger=Z_\psi Z_\psi^\dagger$ uses the same complex $\psi$ as (S.56). A strict solution means one center and one triple satisfying $H_a(M_\psi)>v_a$ for every complex unit phase direction simultaneously, together with $q_2<d_a$.

For diagonal $X>0$ in this center basis and $c\geq0$, retain the spectral quantities of (S.13):

$$
A=\omega X^{-1},\qquad m_X=a\lambda_1(X)+\beta\lambda_2(X),\qquad
K_c=\operatorname{diag}(A,A,c\omega),\qquad
J_c(X)=S_5(K_c)+2m_X-cT_a.
\tag{S.90}
$$

The two eigenvalues of $X$ in $m_X$ are decreasingly ordered. The variational and rank-five argument (S.16)–(S.24) applies directly to the relaxed maximum (S.58): for every feasible $Q$ there, $\operatorname{Tr}(QX)\leq m_X$, so $H_a(M)\leq[m_X+\operatorname{Tr}(MX^{-1})]/2$. Consequently a strict solution obeys

$$
\begin{aligned}
\operatorname{Tr}[A((E_Z)_{00}+(E_Z)_{11})]
&<2(m_X+\operatorname{Tr}A-2v_a),\\
2\operatorname{Tr}A+c-S_5(K_c)
&\leq\operatorname{Tr}(K_cE_Z)
<2(m_X+\operatorname{Tr}A-2v_a)+cd_a,\\
J_c(X)&>4v_a.
\end{aligned}
\tag{S.91}
$$

The lower bound uses this same $\widehat P$ in (S.22); the upper bound uses $q_2<d_a$. At $c=0$ the strict basis inequalities still supply strictness. Thus $J_c(X)\leq4v_a$ excludes the strict relaxation itself. This is an application of the existing spectral-budget argument, without an actual lifting or optimizer-location premise.

**Theorem 64.2 (complete half-beta exclusion on positive supports of ranks three through nine).** At $\beta=1/2$, no ordered positive trace-one center of rank $3\leq k\leq9$ and no single common rank-$(3k-5)$ projection satisfy the strict system (S.59) for the whole complex unit phase sphere.

Proof. Set $h=1/\sqrt2$, $T=(1+h)/2$, $d=(1-h)/2$, and reuse the scalar function of (S.75):

$$
\Delta=4s(1-s)-\frac12=4(T-s)(s-d),\qquad
C(s,t)=\frac1{4s+2h}+\frac{t}{s(4t+2h)},\qquad
f(s,t)=t-\Delta C(s,t).
\tag{S.92}
$$

By Theorems 59.2, 60.1 and 61.1, a putative strict solution has

$$
\frac{31}{50}<s<T,\qquad
t_*(s)=\frac32(T-s)<t\leq1-s,\qquad f(s,t)<d.
\tag{S.93}
$$

In particular $s>1/2$, $\Delta>0$, and all denominators in (S.92) are positive. These necessities come from one fixed $\eta,L,G$ on the whole complex sphere: (S.73)–(S.75) include both cap branches and singular pencils, while (S.78) uses the exact rank-five trace allocation. Their proofs, including the quartic exclusion in (S.79)–(S.82), are reused without replacement.

Choose

$$
\xi=2t+s-T,\qquad x=\sqrt{2s},\qquad y=\sqrt\xi,\qquad
X=\operatorname{diag}(x,y,\ldots,y),\qquad c=\frac1y.
\tag{S.94}
$$

The trace necessity gives $\xi>2(T-s)>0$. Also $\xi<2s$, because $t\leq s<T$, so $0<y<x$. To establish the other needed ordering, positive-side squaring shows

$$
\frac{s}{x}\geq\frac{t}{y}
\quad\Longleftrightarrow\quad
F_s(t):=s(2t+s-T)-2t^2\geq0.
\tag{S.95}
$$

This polynomial is concave in $t$. Its endpoint values on $[t_*(s),1-s]$ are

$$
F_s(t_*)=\frac{(T-s)(13s-9T)}2,\qquad
F_s(1-s)=-3s^2+(6-T)s-2.
\tag{S.96}
$$

The bounds $7/10<h<71/100$ follow by squaring positive rational numbers; in particular $T<43/50$. Hence $13s-9T>13(31/50)-9(43/50)=8/25>0$. The second polynomial in (S.96) is concave in $s$ on $[31/50,T]$. At $s=31/50$ its value is greater than $21/625$, by $T<43/50$, and at $s=T$ it equals $2dh>0$. Both endpoint values in (S.96) are therefore positive throughout the required interval, proving (S.95).

The eigenvalues of $K_c$ are $s/y$ once, $s/x$ twice, and $\lambda_j/y$ three times for each $j\geq2$. Since every $\lambda_j\leq t$, the five largest, with multiplicities and any ties, are

$$
\frac{s}{y},\quad\frac{s}{x},\quad\frac{s}{x},\quad
\frac{t}{y},\quad\frac{t}{y}.
\tag{S.97}
$$

Thus this entire ordering cone, including every ordered positive tail, gives

$$
\begin{aligned}
J_c(X)&=\frac{2s}{x}+x+\frac{s+2t-T}{y}+y
=2\sqrt{2s}+2\sqrt{2t+s-T},\\
g(s)&=\frac{5T+s-4\sqrt{2sT}}2,\\
J_c(X)\leq4\sqrt T&\quad\Longleftrightarrow\quad t\leq g(s).
\end{aligned}
\tag{S.98}
$$

Indeed $2\sqrt T-\sqrt{2s}>0$, so squaring that positive comparison with $\sqrt\xi$ proves the equivalence. Necessity (S.91) now forces $t>g(s)$.

For the opposite consequence, $C(s,t)$ increases with $t$, its second summand having derivative $2h/[s(4t+2h)^2]>0$. Hence $C(s,t)\leq C(s,1-s)$. Put $Q=s(2s+h)(2-2s+h)>0$. Expansion using $h^2=1/2$ gives the exact identity

$$
\begin{aligned}
\frac9{10}-4(s-d)C(s,1-s)&=\frac{P_h(s)}{10Q},\\
P_h(s)&=44s^3+(-84+40h)s^2
+\left(\frac{89}{2}-42h\right)s+10h-5.
\end{aligned}
\tag{S.99}
$$

Here is a complete sign certificate. For $s=31/50+(6/25)u$, $0\leq u\leq1$, write

$$
P_b\!\left(\frac{31}{50}+\frac6{25}u\right)
=\sum_{j=0}^3 p_j(b)\binom3j u^j(1-u)^{3-j}.
\tag{S.100}
$$

All eight endpoint coefficients are

| $j$ | $p_j(7/10)$ | $p_j(71/100)$ |
| --- | --- | --- |
| $0$ | $20127/62500$ | $4928/15625$ |
| $1$ | $2131/62500$ | $524/15625$ |
| $2$ | $15143/62500$ | $3992/15625$ |
| $3$ | $97179/62500$ | $24836/15625$ |

These are all strictly positive. The Bernstein weights are nonnegative and sum to one, so both endpoint polynomials are strictly positive on the full interval $[31/50,43/50]$, including its endpoints. Since $P_h$ is affine in $h$ and $7/10<h<71/100$, it is a convex combination of those two positive polynomials. In particular (S.99) proves $4(s-d)C(s,1-s)<9/10$ on $[31/50,T]$.

For $s<T$, put $z=\sqrt{s/T}<1$. Direct factorization and $\sqrt2>7/5$ give

$$
\begin{aligned}
g(s)-d&=(T-s)\left(\frac{2\sqrt2}{1+z}-\frac12\right)
>(T-s)\left(\sqrt2-\frac12\right)
>\frac9{10}(T-s),\\
f(s,t)&>t-\frac9{10}(T-s).
\end{aligned}
\tag{S.101}
$$

The second line uses $\Delta=4(T-s)(s-d)>0$, $C(s,t)\leq C(s,1-s)$ and the strict bound just proved. Thus $t\geq g(s)$ would imply $f(s,t)>d$, contradicting (S.93). Strict feasibility requires $t<g(s)$ as well as $t>g(s)$, an impossibility; $t=g(s)$ is excluded too. Theorem 61.1 already excludes the complementary leading-eigenvalue bands, including $s=31/50$ and $s=T$. This proves the assertion for every stated support and every ordered positive tail. $\square$

## 65. Fixed weights for an all-positive-beta region

**Theorem 65.1 (a uniform spectral region).** For every $0<\beta\leq1/2$ and $3\leq k\leq9$, the strict system (S.59) is infeasible at every ordered positive trace-one center with

$$
s\geq2t,\qquad s+t\leq\frac{49}{50}.
\tag{S.102}
$$

Proof. Take fixed weights

$$
X=\operatorname{diag}\left(\frac65,\frac35,\ldots,\frac35\right),\qquad c=\frac53.
\tag{S.103}
$$

In this ordering cone the five largest eigenvalues of $K_c$ are

$$
\frac{5s}{3},\quad\frac{5s}{6},\quad\frac{5s}{6},\quad
\frac{5t}{3},\quad\frac{5t}{3},\qquad
S_5(K_c)=\frac{10}{3}(s+t).
\tag{S.104}
$$

Indeed the leading center coordinate contributes $5s/3$ once and $5s/6$ twice; every other coordinate contributes $5\lambda_j/3$ three times. Ordering $\lambda_j\leq t$ and $s\geq2t$ proves the list, including $s=2t$, repeated center eigenvalues and all tail ties. Therefore

$$
\begin{aligned}
J_c(X)&=\frac{10}{3}(s+t)+\frac{12}{5}-\frac65\beta-\frac53T_a\\
&=\frac{10}{3}(s+t)+\frac{11}{30}+\frac65u^2-\frac56u,\qquad
u:=\sqrt{1-\beta}\in\left[\frac1{\sqrt2},1\right).
\end{aligned}
\tag{S.105}
$$

Both sides in $v_a\geq(7+3u)/10$ are positive, and their squared difference is

$$
\frac{1+u}{2}-\left(\frac{7+3u}{10}\right)^2
=\frac{(1-u)(9u+1)}{100}\geq0.
\tag{S.106}
$$

Substitution into (S.105) gives the factorized lower margin

$$
4v_a-J_c(X)\geq
\frac{10}{3}\left(\frac{49}{50}-s-t\right)
+\frac{(1-u)(36u-25)}{30}>0.
\tag{S.107}
$$

The first term is nonnegative by (S.102). The second is strictly positive because $u<1$ and $u\geq1/\sqrt2>25/36$; the latter positive-root comparison follows from $1/2>625/1296$. This includes $\beta=1/2$ and both spectral boundaries in (S.102). Necessity (S.91) yields the contradiction for the entire allowed beta interval. $\square$

**Corollary 65.2 (positive-tail consumers with a uniform margin).** For every $k=3,\ldots,9$, every ordered positive tail with total mass $1/20$ at $s=7/10,t=1/4$ is excluded for all $0<\beta\leq1/2$, with

$$
4v_a-J_c(X)\geq\frac1{10}.
\tag{S.108}
$$

Within the space of ordered positive trace-one spectra in each rank, the region $s>2t$, $s+t<49/50$ is a relative open neighborhood of each of these centers and is excluded by Theorem 65.1.

Proof. These leading eigenvalues have $s>2t$ and $s+t=19/20<49/50$. Every positive tail of total $1/20$ has each entry at most $1/20<t$. Such tails exist in every stated rank, for example by equal distribution among $k-2$ entries. The first term of (S.107) is exactly $(10/3)(49/50-19/20)=1/10$, while its second term is positive for each allowed beta. This proves the uniform margin independently of how that mass is distributed. The neighborhood assertion follows from the strict spectral inequalities and continuity. In particular the rank-three center $(7/10,1/4,1/20)$ of Proposition 63.1 is covered. The necessary scalar conditions in (S.87) alone remain insufficient; the additional spectral certificate (S.103) supplies its exclusion, while Theorem 64.2 closes the entire half-beta residual by overlap. $\square$

## 66. The rank-two supported boundary and a conditional actual-channel consequence

**Proposition 66.1 (rank-two centers at half beta).** For every positive trace-one center of support rank $k=2$, the strict system (S.59) at $\beta=1/2$ is infeasible, independently of the ambient actual Kraus rank.

Proof. Here $E_Z$ has rank one in dimension six, so its unit range vector is already supported on $\mathbb C^3\otimes K_2$, with $K_2$ the whole center support. No dimension-intersection premise requiring $k\geq3$ is used. The construction (S.68)–(S.71) and the branch-complete proof (S.73)–(S.75) apply with $\epsilon=0$, $t=1-s>0$ and $s\geq1/2$. Thus strict feasibility requires $\Delta>0$ and $f(s,t)<d$. If $s\geq T$, then $\Delta\leq0$, a contradiction. Otherwise $1/2\leq s<T$ and $d<t\leq1/2$.

Use precisely the boundary comparison (S.77), inherited from (R.228)–(R.229) of Theorem 44.2 of the first volume. Its full denominator and sign are

$$
\begin{aligned}
\Delta&=4(t-d)(T-t),\\
f(s,t)-d&=(t-d)\bigl[1-4(T-t)C(s,t)\bigr],\\
1-4(T-t)C(s,t)&=\frac{4D_0}{s(4s+2h)(4t+2h)},\\
D_0&=s(4st+2h+h^2)-2(T-t)(4st+h)\\
&=h-h^2t-4st(h-t)\geq t(1-h^2)=\frac t2>0.
\end{aligned}
\tag{S.109}
$$

All denominator factors are positive. The lower bound uses $s+t=1$, $4st\leq1$ and $h>t$. Hence $f(s,t)>d$, contradicting necessity, including $s=t=1/2$. Singular $L$, directional marginals and $\kappa=1$ remain within the reused argument; only the positive definite matrix $B_0$ of (S.74) is inverted. Ambient zero eigenvalues are removed by taking the exact center support before this construction. Rank-one centers are treated by the actual overlap bound of Theorem 52.3, without rank-five padding. $\square$

**Theorem 66.2 (actual half-beta lower bound through the inherited interfaces).** Assume the actual phase-marginal and supported common-projection interfaces (S.8)–(S.12), (S.55)–(S.60), the rectangular-contraction identity (S.6), compact affine minimax (S.26), unrestricted CPTP recovery/complement identity (S.7), and pure-target diamond lower bound (S.27), with their stated domains and conventions. Then every actual original-real CPTP $N:M_3(\mathbb C)\to M_5(\mathbb C)$ of Definition 52.1 with phase-difference spectrum $(1/2,1/2,0,-1/2,-1/2)$ and actual minimal Kraus rank $r\leq9$ satisfies

$$
g_N^2\leq T,\qquad
\inf_{R:M_5\to M_3\ {\rm CPTP}}\|RN-\mathrm{id}_3\|_\diamond
=\delta_N\geq1-\frac1{\sqrt2}.
\tag{S.110}
$$

All admissible third columns, all complex CPTP recoveries on the whole output, and every finite complex reference are retained; the diamond norm is unhalved.

Proof. Fix one actual $V$ and then any center $\omega$ on its environment and any single rectangular contraction $U$ of (S.5). The center has support rank $1\leq k\leq r$, which is not the actual Kraus rank. If $k=1$, (S.8) and Cauchy–Schwarz give $r_\psi\leq\sqrt a<v_a$, as proved in Theorem 52.3. In particular no projection of rank five is required on a three-dimensional space.

For $k\geq2$, restrict the center and contracted vector to the exact center support as in Section 52, leaving the actual encoder and its environment intact. Complete the range of this supported $U$ to one five-dimensional subspace, and choose its projection $P$ before testing directions. This step is valid because $3k\geq6$ and $\operatorname{rank}U\leq5$; it does not compress an existing rank-five projection and presume its rank unchanged. By Theorem 57.2, if every phase-direction real overlap and the third-basis overlap exceeded $v=\sqrt T$, this one common $V,\omega,U,P$ would yield the strict system (S.59). Proposition 66.1 excludes $k=2$ and Theorem 64.2 excludes $3\leq k\leq9$. Therefore for each fixed $V,\omega,U$ the restricted minimum in (S.15) is at most $v$; its witnessing direction may depend on $\omega$ and $U$.

The least eigenvalue of $\operatorname{Herm}A_{\omega,U}$ is at most that restricted minimum. The assumed compact-affine minimax identity (S.26) consequently gives, for every center,

$$
\min_\rho F_\rho(\Gamma,\mathcal C_\omega)
=\max_{U^\dagger U\preceq I_5}\lambda_{\min}(\operatorname{Herm}A_{\omega,U})
\leq v.
\tag{S.111}
$$

Only now maximize over centers in (S.7), obtaining $g_N\leq v$. For every unrestricted recovery, (S.27) uses an input purification and the binary measurement onto the pure identity target to bound its full diamond norm. Taking the recovery infimum gives $\delta_N\geq2(1-g_N^2)\geq2(1-T)=1-1/\sqrt2$. Phase-plane and third-basis tests are a subset used to bound the least eigenvalue; they impose no restriction on recoveries or on the finite-reference supremum.

The complete actual-rank-two theorem is already Theorems 44.2–45.1 of the first volume. Proposition 66.1 extends its supported boundary calculation to rank-two centers inside any allowed actual environment; it does not identify center rank with actual Kraus rank or claim that earlier theorem anew. The present consequence uses the inherited interfaces explicitly stated in the hypothesis. $\square$

## 67. Actual-domain premises, attribution and the general-beta boundary

**Definition 67.1 (scope of the projection exclusions and actual consequence).** Theorems 64.2 and 65.1 are analytic exclusions of the strict common-projection relaxation itself. They require one normalized projection and one center across every complex unit phase direction; they supply neither a strict relaxed feasible point nor an actual encoder or physical recovery. Theorem 66.2 additionally consumes the named actual-channel and fidelity interfaces. Their primary-source status is the inherited `literature-attested` attribution in Definition 58.3, not a new authentication of those papers or a newly verified physical realization. The projection exclusions do not depend on that external authentication; the actual-channel conclusion is conditional on the stated interfaces.

The actual domain still requires one original-real $V$, one common $U$, actual domination (S.8), and the complete phase-Choi range, trace, reality, residual positivity and residual-rank premises (S.64)–(S.65), including every admissible $C$ and $\sigma$. The phase states are the mixtures (S.11), which need not have rank two. Diagonalizing a center transports the environmental antiunitary and all actual blocks together; it does not make the blocks jointly entrywise real or commuting. The normalized $Z_i$ equations reconstruct only projection geometry. They neither discharge those actual conditions nor provide a common family of attaining $Q_\psi$ or a converse lifting theorem.

The source-specific overlap, fixed-weight region and supported-center application are `repo-derived`. Their intermediates are the existing common-vector/pencil and scalar results of Sections 59–63, variational fidelity and exact rank-five allocation in Section 53, concavity of quadratic polynomials, the Bernstein representation (S.81), and the inherited supported boundary (S.77). The scalar-method obstruction of Sections 55–56, including both weight-order cones in Theorem 55.1 and the pinching theorem, retains its exact scope: it does not preclude the nonlinear-plus-spectral overlap. These applications assert no new generic spectral, minimax or Bernstein theorem, kernel verification, global novelty or literature completeness.

The necessary scalar conditions of Proposition 63.1 remain valid and insufficient by themselves. Their residual half-beta region is excluded by the additional certificate and overlap in Section 64, with the displayed center and all its positive-tail counterparts also consumed by Section 65. For $0<\beta<1/2$, the fixed-weight theorem covers only (S.102); the spread criterion (S.28), common-vector reduction of Section 59 and earlier results retain their respective ranges. An all-center general-beta analogue of the overlap, or an additional obstruction using four common orthogonal top-three-supported defect vectors, is not established here. No strict feasible relaxation or counterexample outside the certified regions is inferred.

The original target (S.66) remains the uniform statement for every $0<\beta\leq1/2$, every allowed original-real actual encoder with actual rank at most nine, all admissible third columns, all complex whole-output CPTP recoveries, every finite complex reference and the unhalved diamond norm. Its general-beta part remains unresolved. Theorem 66.2 is a conditional half-beta consequence toward that unchanged target. An actual counterexample would still require an allowed common implementation and a full-reference diamond upper certificate below $1-\sqrt{1-\beta}$; passing an individual necessary scalar test cannot supply either.

## 追加锚（本行以下为增补区）
