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
