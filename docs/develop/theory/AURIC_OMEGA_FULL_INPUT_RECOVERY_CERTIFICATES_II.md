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

## 68. An actual half-beta family separating subcode and full-input recovery

**Definition 68.1 (the reused base and the allowed perturbations).** Use the original-real class of Definition 52.1 and the unhalved full-reference norm of (S.3). Fix $a=\beta=1/2$ and a real output orthonormal frame $(b_1,g_1,b_2,g_2,h)$. The following base encoder is exactly Definition 48.1, (R.244), of the [first volume](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#48-an-explicit-half-beta-encoder-with-two-complementary-certificates), under $(b_1,g_1,b_2,g_2,h)=(e_0,e_1,e_2,e_3,e_4)$ and $K_1^0=K_0$, $K_2^0=K_1$ there:

$$
\begin{aligned}
t_1&=\frac{b_1+g_2+2h}{2\sqrt2},&
t_2&=\frac{g_1-b_2}{2\sqrt2},\\
K_1^0&=[b_1/\sqrt2,g_1/\sqrt2,t_1],&
K_2^0&=[b_2/\sqrt2,g_2/\sqrt2,t_2],\\
N_0(X)&=\sum_{\alpha=1}^2K_\alpha^0X(K_\alpha^0)^\dagger.
\end{aligned}
\tag{S.112}
$$

Let $Q\in M_5(\mathbb R)$ be any real symmetric density, including singular densities. Choose its real spectral factorization $Q=\sum_{\ell=1}^s q_\ell q_\ell^T$ with linearly independent $q_\ell$ and $s=\operatorname{rank}Q\in\{1,2,3,4,5\}$. Set

$$
\begin{gathered}
0<\epsilon\leq\frac1{128},\qquad d_\epsilon=\sqrt{1-\epsilon},\\
K_1^{\epsilon,Q}=[b_1/\sqrt2,g_1/\sqrt2,d_\epsilon t_1],\qquad
K_2^{\epsilon,Q}=[b_2/\sqrt2,g_2/\sqrt2,d_\epsilon t_2],\\
K_{2+\ell}^{\epsilon,Q}=[0,0,\sqrt\epsilon q_\ell],\qquad
N_{\epsilon,Q}(X)=\sum_{\alpha=1}^{2+s}K_\alpha^{\epsilon,Q}X(K_\alpha^{\epsilon,Q})^\dagger.
\end{gathered}
\tag{S.113}
$$

The symbol $d_\epsilon$ is unrelated to the threshold defect $d=1-T$ of (S.3). The parameter $\epsilon$ here is a channel perturbation, not the center tail mass of Section 59. The base $\epsilon=0$ is used only for comparison and is outside the asserted rank-three-through-seven family.

**Proposition 68.2 (actual class membership and minimal rank).** Every (S.113) is an actual original-real CPTP map on complex $M_3$, has $\lambda=f(\tau,\bar\tau)=1$, the prescribed half-beta phase-difference spectrum, and minimal encoder Kraus rank $2+\operatorname{rank}Q$.

Proof. Proposition 48.2 already supplies the base realization. To check the changed third columns against the same first two columns, use

$$
\begin{gathered}
\|t_1\|^2=\frac34,\quad\|t_2\|^2=\frac14,\qquad
\frac{\langle b_1,t_1\rangle+\langle b_2,t_2\rangle}{\sqrt2}
=\frac14-\frac14=0,\\
\frac{\langle g_1,t_1\rangle+\langle g_2,t_2\rangle}{\sqrt2}=0,\qquad
\sum_\alpha\|K_\alpha^{\epsilon,Q}|2\rangle\|^2
=d_\epsilon^2+\epsilon\operatorname{Tr}Q=1.
\end{gathered}
\tag{S.114}
$$

Thus the third-to-code TP sums still vanish, while the code-column Gram sums are unchanged. Hence $\sum_\alpha(K_\alpha^{\epsilon,Q})^\dagger K_\alpha^{\epsilon,Q}=I_3$. These real matrices have the form $(x,Jx,t)$ in (R.8)–(R.9), with every third-column component retained. Their Kraus sum is CP on all complex matrices, so this verifies the actual class rather than a complementary relaxation.

For $f_j^\pm=(b_j\pm ig_j)/\sqrt2$, the only nonzero phase Kraus vectors are $K_j^{\epsilon,Q}\chi_\pm=f_j^\pm/\sqrt2$, $j=1,2$. The four $f_j^\pm$ are orthonormal. The actual phase outputs and their environment data therefore satisfy

$$
\operatorname{spec}(N_{\epsilon,Q}(\chi_+)-N_{\epsilon,Q}(\chi_-))
=(1/2,1/2,0,-1/2,-1/2),\qquad
\tau=\bar\tau=\operatorname{diag}(1/2,1/2,0,\ldots,0),\qquad\lambda=1.
\tag{S.115}
$$

Here $N(\chi_\pm)$ denotes the output on the phase projector, as in the first volume. In a complex linear relation among the Kraus matrices, their first columns force the coefficients of $K_1^{\epsilon,Q},K_2^{\epsilon,Q}$ to vanish. The remaining coefficients vanish because $\epsilon>0$ and the real independent $q_\ell$ are also complex independent. Thus the vectorized Kraus matrices are independent and the encoder Choi rank is exactly $2+s$, equal to the minimal Kraus number. Choosing $Q=\Pi_s/s$ for any real rank-$s$ orthogonal projection realizes each rank $3,4,5,6,7$. The unchanged code columns and $d_\epsilon t_1$ also span all five output directions, so retained-output support is five-dimensional. $\square$

**Proposition 68.3 (the residual belongs to the same dilation).** The actual support-aware Schur residual of (S.65) for (S.113) is

$$
S_{\rm res}=v_{\epsilon,Q}v_{\epsilon,Q}^T,\qquad
v_{\epsilon,Q}=(d_\epsilon/\sqrt2,0,\sqrt\epsilon\langle h,q_1\rangle,\ldots,
\sqrt\epsilon\langle h,q_s\rangle)^T,
\qquad
w=\frac{1-\epsilon}{2}+\epsilon\langle h,Qh\rangle.
\tag{S.116}
$$

Proof. Apply the same-dilation identity of Theorem 2.1 in the first volume: the residual is the Gram outer product of the actual third-input components along the one outside-phase output direction $h$. Their list is precisely $v_{\epsilon,Q}$, which is nonzero since $d_\epsilon>0$. Thus the residual has rank one and trace $w$. Its phase-Choi rank is $2\operatorname{rank}\tau+1=5$ by (R.5); this is distinct from the encoder Kraus rank $2+s$.

For example, $Q=hh^T$ gives the actual third-input environment state and residual

$$
\sigma=\begin{pmatrix}
3d_\epsilon^2/4&0&d_\epsilon\sqrt{\epsilon/2}\\
0&d_\epsilon^2/4&0\\
d_\epsilon\sqrt{\epsilon/2}&0&\epsilon
\end{pmatrix},\qquad
S_{\rm res}=\begin{pmatrix}d_\epsilon/\sqrt2\\0\\\sqrt\epsilon\end{pmatrix}
\begin{pmatrix}d_\epsilon/\sqrt2&0&\sqrt\epsilon\end{pmatrix},\qquad
w=\frac{1+\epsilon}{2}.
\tag{S.117}
$$

The inverse of $\tau$ in the Schur calculation is its support inverse, zero on the remaining environment coordinates. No independently chosen residual or discarded active-space third column enters these identities. $\square$

## 69. A sharper rational full-input dual for the reused base

**Definition 69.1 (recovery-shaped vectorization and transport).** For every $3\times5$ recovery-shaped matrix $A$ use logical-first row vectorization

$$
\operatorname{vec}_{3,5}(A)=\sum_{i=0}^2\sum_{y=0}^4A_{iy}|i\rangle_3|y\rangle_5,\qquad
C_{\rho,N}=\sum_\alpha|\operatorname{vec}_{3,5}(\rho K_\alpha^\dagger)\rangle
\langle\operatorname{vec}_{3,5}(\rho K_\alpha^\dagger)|.
\tag{S.118}
$$

For a complex whole-output recovery with Kraus matrices $R_k$, put $J=\sum_k|\operatorname{vec}_{3,5}(R_k)\rangle\langle\operatorname{vec}_{3,5}(R_k)|$. Then $J\succeq0$, $\operatorname{Tr}_3J=(\sum_kR_k^\dagger R_k)^T=I_5$, and, for every complex Hermitian density $\rho$,

$$
\langle\operatorname{vec}_{3,5}(\rho K_\alpha^\dagger),\operatorname{vec}_{3,5}(R_k)\rangle
=\operatorname{Tr}(\rho R_kK_\alpha),\qquad
F_e(\rho,RN)=\operatorname{Tr}(C_{\rho,N}J).
\tag{S.119}
$$

This is the same SDP as Theorem 7.1 of the first volume, in a transported convention. Explicitly, let $\mathsf S(|y\rangle_5|i\rangle_3)=|i\rangle_3|y\rangle_5$, and let $M_\rho=D_\rho D_\rho^\dagger$ be (R.29). Then

$$
C_{\rho,N}=\mathsf S\overline{M_\rho}\mathsf S^\dagger,\qquad
X_{\rm out}=\mathsf S^\dagger\bar J\mathsf S,\qquad
Y_{\rm out}=Y^T,\qquad
C_{\rho,N}\preceq I_3\otimes Y
\ \Longleftrightarrow\ M_\rho\preceq Y^T\otimes I_3.
\tag{S.120}
$$

Indeed $\operatorname{vec}_{3,5}(\rho K_\alpha^\dagger)=\mathsf S\overline{\operatorname{vec}_{5,3}(K_\alpha\rho)}$. These are a whole tensor swap and full conjugation, equivalently full transpose of Hermitian matrices, together with transpose of the output dual. They are not a partial transpose. The real numerical certificate below is unchanged by the output transpose, but the general complex convention still requires it.

The reused weak-dual and pure-target interfaces now read

$$
\begin{gathered}
C_{\rho,N}\preceq I_3\otimes Y\quad\Longrightarrow\quad
F_e(\rho,RN)\leq\operatorname{Tr}Y\quad\hbox{for every complex whole-output CPTP }R,\\
\|(\mathrm{id}\otimes RN)(\Phi_\rho)-\Phi_\rho\|_1
\geq2(1-F_e(\rho,RN)),
\end{gathered}
\tag{S.121}
$$

where $\Phi_\rho$ is any pure purification projector. The first implication follows by tracing against $J$; the second is the binary measurement onto $\Phi_\rho$. Both reuse Theorems 7.1 and 7.4, with the unhalved norm.

**Theorem 69.2 (improved base certificate).** For $N_0$ of (S.112), the same full-input witness $\rho_\star$ as (R.260) and the following new rational dual satisfy

$$
\rho_\star=\operatorname{diag}(1/4,1/4,1/2),\qquad
Y=\frac{M}{64},\qquad
M=\begin{pmatrix}
11&0&0&2&5\\
0&10&-2&0&0\\
0&-2&8&0&0\\
2&0&0&8&6\\
5&0&0&6&15
\end{pmatrix},\qquad
Y\succ0,\quad\operatorname{Tr}Y=\frac{13}{16}.
\tag{S.122}
$$

Consequently every complex whole-output recovery obeys $F_e(\rho_\star,RN_0)\leq13/16$ and $\delta_{N_0}\geq3/8$.

Proof. In the order $(b_1,g_2,h)\oplus(g_1,b_2)$ the matrix $M$ is $A\oplus B$, where

$$
\begin{gathered}
A=\begin{pmatrix}11&2&5\\2&8&6\\5&6&15\end{pmatrix},\quad
B=\begin{pmatrix}10&-2\\-2&8\end{pmatrix},\\
A^{-1}=\frac1{28}\begin{pmatrix}3&0&-1\\0&5&-2\\-1&-2&3\end{pmatrix},\qquad
B^{-1}=\frac1{76}\begin{pmatrix}8&2\\2&10\end{pmatrix}.
\end{gathered}
\tag{S.123}
$$

Their leading principal minors are $(11,84,784)$ and $(10,76)$, respectively. Sylvester's criterion proves positivity, and multiplication verifies the displayed inverses. Let

$$
\begin{aligned}
w_1&=|0\rangle b_1+|1\rangle g_1+|2\rangle(b_1+g_2+2h),\\
w_2&=|0\rangle b_2+|1\rangle g_2+|2\rangle(g_1-b_2),\qquad
W=[w_1,w_2]/\sqrt{32}.
\end{aligned}
\tag{S.124}
$$

Tensor products in this formula have the logical factor first. Directly from (S.112), $C_{\rho_\star,N_0}=WW^\dagger$. For transparency the two diagonal contractions, including the factor $64/32=2$, are

$$
\begin{aligned}
[W^\dagger(I_3\otimes Y^{-1})W]_{11}
&=2\left(\frac3{28}+\frac8{76}+\frac8{28}\right)=\frac{265}{266},\\
[W^\dagger(I_3\otimes Y^{-1})W]_{22}
&=2\left(\frac{10}{76}+\frac5{28}+\frac{14}{76}\right)=\frac{263}{266},\\
W^\dagger(I_3\otimes Y^{-1})W
&=\operatorname{diag}(265/266,263/266),\\
I_2-W^\dagger(I_3\otimes Y^{-1})W
&=\operatorname{diag}(1/266,3/266)\succ0.
\end{aligned}
\tag{S.125}
$$

The off-diagonal contraction vanishes because corresponding vectors belong to different blocks of (S.123). In the first contraction, $(1,1,2)A^{-1}(1,1,2)^T=8/28$; in the second, $(1,-1)B^{-1}(1,-1)^T=14/76$.

Taking both Schur complements of the same block matrix proves the full inequality:

$$
\begin{pmatrix}I_3\otimes Y&W\\W^\dagger&I_2\end{pmatrix}\succ0
\ \Longleftrightarrow\ I_2-W^\dagger(I_3\otimes Y^{-1})W\succ0
\ \Longleftrightarrow\ I_3\otimes Y-WW^\dagger\succ0.
\tag{S.126}
$$

Thus this is a strict fifteen-dimensional certificate, not a test on selected recovery columns. Apply (S.121) at the fixed purification $\frac12|00\rangle+\frac12|11\rangle+\frac1{\sqrt2}|22\rangle$ to obtain

$$
F_e(\rho_\star,RN_0)\leq\frac{13}{16},\qquad
\|RN_0-\mathrm{id}_3\|_\diamond\geq\frac38,\qquad
\delta_{N_0}\geq\frac38.
\tag{S.127}
$$

The witness and the encoder are reused from Sections 48–50 of the first volume. Relative to its $83/100$ fidelity upper bound and $17/50$ norm lower bound, the improvements are $7/400$ and $7/200$. Neither the displayed dual nor the witness is asserted optimal. $\square$

## 70. Every complex code direction has a completed transpose recovery

**Definition 70.1 (one recovery for a whole complex plane).** For any $u,v\in\mathbb C$ with $|u|^2+|v|^2=1$, put $\xi=u|0\rangle+v|1\rangle$, $V_\xi=[\xi,|2\rangle]$, and $\iota_\xi(X)=V_\xi XV_\xi^\dagger$. Define

$$
N_\xi=N_0\iota_\xi,\quad L_\alpha=K_\alpha^0V_\xi,\quad
S_\xi=\sum_{\alpha=1}^2L_\alpha L_\alpha^\dagger,\quad
P_\xi=\operatorname{supp}S_\xi,\quad H_\xi=S_\xi^{-1/2},
\tag{S.128}
$$

where $H_\xi$ is zero on $\ker S_\xi$. Reuse the supported transpose recovery and whole-output completion of Section 49 in the first volume, now at this complex direction:

$$
\begin{aligned}
D_\xi(X)&=\sum_{\alpha=1}^2L_\alpha^\dagger H_\xi XH_\xi L_\alpha
+\operatorname{Tr}((I_5-P_\xi)X)|0\rangle\langle0|,\\
R_\xi&=\iota_\xi D_\xi:M_5\longrightarrow M_3.
\end{aligned}
\tag{S.129}
$$

The supported core has Kraus completeness $H_\xi S_\xi H_\xi=P_\xi$. Choosing an orthonormal basis $n_j$ of $\ker S_\xi$, the reset branch has Kraus matrices $|0\rangle\langle n_j|$, with completeness $I_5-P_\xi$. Thus $D_\xi$ and $R_\xi$ are complex CPTP maps on all of $M_5$. The completion acts also on later perturbation output outside the old support; it is not discarded when $Q$ changes.

**Theorem 70.2 (uniform complex Gram bound).** Arrange the four vectors $L_\alpha|i\rangle$ in logical-first order $(i,\alpha)=(0,1),(0,2),(1,1),(1,2)$. Their Gram matrix is

$$
G_\xi=\begin{pmatrix}I_2/2&U_\xi/4\\U_\xi^\dagger/4&\operatorname{diag}(3/4,1/4)\end{pmatrix},\qquad
U_\xi=\bar u Z+\bar v X,\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{S.130}
$$

It satisfies $G_\xi\succeq(2-\sqrt3)I_4/4\succ0$ and $\operatorname{Tr}\sqrt{G_\xi}\geq\sqrt2+\sqrt{3/2}$ for every complex unit direction.

Proof. Formula (S.130) follows by contracting the actual columns; its conjugates cannot be dropped. With $\sigma_y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$ and $\kappa=2\operatorname{Im}(\bar u v)$,

$$
B_\xi:=4G_\xi-2I_4=\begin{pmatrix}0&U_\xi\\U_\xi^\dagger&Z\end{pmatrix},\quad
U_\xi^\dagger U_\xi=I_2+\kappa\sigma_y,\quad |\kappa|\leq1,\quad
\operatorname{Tr}B_\xi=\operatorname{Tr}B_\xi^3=0,\quad\operatorname{Tr}B_\xi^2=6.
\tag{S.131}
$$

For the cubic trace use $\operatorname{Tr}B_\xi^3=3\operatorname{Tr}(ZU_\xi^\dagger U_\xi)+\operatorname{Tr}Z^3=0$. Equivalently, a Schur computation for $t\ne0$, then polynomial continuation to $t=0$, gives

$$
\det(tI_4-B_\xi)=\det((t^2-1)I_2-tZ-\kappa\sigma_y)
=t^4-3t^2+1-\kappa^2.
\tag{S.132}
$$

Hermiticity and the even polynomial give eigenvalues $s_1,-s_1,s_2,-s_2$ with $s_j\geq0$ and $s_1^2+s_2^2=3$. This includes a zero pair at $|\kappa|=1$. Consequently the eigenvalues of $G_\xi$ are $1/2\pm s_j/4$, all at least $(2-\sqrt3)/4>0$. The four actual output columns are independent, so $\operatorname{rank}S_\xi=4$ for real, circular, zero-coordinate and all other complex directions.

Put $z_j=s_j^2/16$, so $z_1+z_2=3/16$. On $[0,3/16]$ define

$$
g(z)=\sqrt{1/2+\sqrt z}+\sqrt{1/2-\sqrt z}
=\sqrt{1+\sqrt{1-4z}}.
\tag{S.133}
$$

With $r=\sqrt{1-4z}\geq1/2$ and $g=\sqrt{1+r}$, differentiation gives $g''=-2/(r^3g)-1/(r^2g^3)<0$, including finite endpoint limits. Hence each $g(z)$ lies above its chord between $0$ and $3/16$. Adding the two chord bounds yields

$$
\operatorname{Tr}\sqrt{G_\xi}=g(z_1)+g(z_2)
\geq g(0)+g(3/16)=\sqrt2+\sqrt{3/2}.
\tag{S.134}
$$

No step assumes $u,v$ real. $\square$

**Proposition 70.3 (midpoint fidelity with the tensor shuffle).** Let $\Lambda_\xi=D_\xi N_\xi$. Then

$$
F_e(I_2/2,\Lambda_\xi)
=\frac14\|\operatorname{Tr}_{\rm logical}\sqrt{G_\xi}\|_{\rm HS}^2
\geq\frac{(\operatorname{Tr}\sqrt{G_\xi})^2}{8}
\geq\frac{7+4\sqrt3}{16}.
\tag{S.135}
$$

Proof. Concatenate $F_\xi=[L_1,L_2]$ in Kraus-first order $(\alpha,i)$ and put $G_{\rm KF}=F_\xi^\dagger F_\xi$. Let $\Pi$ be the coordinate shuffle with zero-based order $(0,2,1,3)$, taking Kraus-first to logical-first order. Then

$$
G_\xi=\Pi G_{\rm KF}\Pi^\dagger,\qquad
\sqrt{G_\xi}=\Pi\sqrt{G_{\rm KF}}\Pi^\dagger,\qquad
F_\xi^\dagger H_\xi F_\xi=\sqrt{G_{\rm KF}}.
\tag{S.136}
$$

The last identity is the singular-value/polar identity with the support inverse. Its $(\alpha,\gamma)$ block is the composite Kraus matrix $L_\alpha^\dagger H_\xi L_\gamma$. Reset Kraus products vanish since $n_j^\dagger L_\gamma=0$. Taking the logical trace of those blocks therefore produces the two-by-two environment matrix whose squared Hilbert–Schmidt norm divided by four is the midpoint fidelity. In logical-first order this is exactly $\operatorname{Tr}_{\rm logical}\sqrt{G_\xi}$. The shuffle preserves the total trace and makes this partial-trace identification explicit. Cauchy–Schwarz against $I_2$ gives its squared norm at least half its trace squared; (S.134) proves (S.135). The polar and midpoint identities reuse (R.258)–(R.259); their complex-direction estimate here is the extension. $\square$

## 71. Full-reference error from the self-adjoint unital qubit composite

**Theorem 71.1 (the restricted Pauli norm identity and the base subcode bound).** For each complex unit $\xi$, the particular channel $\Lambda_\xi$ is Hilbert–Schmidt self-adjoint, TP and unital, and

$$
\|\Lambda_\xi-\mathrm{id}_2\|_\diamond
=2(1-F_e(I_2/2,\Lambda_\xi)),\qquad
\|R_\xi N_0\iota_\xi-\iota_\xi\|_\diamond
\leq\frac{9-4\sqrt3}{8}.
\tag{S.137}
$$

Proof. Every $N_\xi(X)$ is supported on $P_\xi$, also for off-diagonal matrix units. Thus the completion branch vanishes in the composite, which is

$$
\Lambda_\xi=N_\xi^\dagger\circ[X\mapsto H_\xi XH_\xi]\circ N_\xi,\qquad
\Lambda_\xi(I_2)=\sum_\alpha L_\alpha^\dagger P_\xi L_\alpha=I_2.
\tag{S.138}
$$

The sandwich is self-adjoint for the Hilbert–Schmidt inner product, hence so is this composite. TP follows from composition of CPTP maps. For a TP unital Hermiticity-preserving qubit channel write $T_{ij}=\operatorname{Tr}(\sigma_i\Lambda(\sigma_j))/2$ on the three Pauli matrices. The Bloch matrix $T$ is real; Hilbert–Schmidt self-adjointness makes it symmetric. The real spectral theorem supplies a diagonalizing orthogonal eigenbasis, including degeneracies. Flip one eigenvector if needed to choose a rotation in $SO(3)$. Lift that rotation to a qubit unitary $U$. Thus the simultaneous conjugation $\Lambda'=\operatorname{Ad}_{U^\dagger}\Lambda\operatorname{Ad}_U$ is Pauli diagonal. The same unitary is used on both sides, so the identity target is preserved.

If its three eigenvalues are $\mu_1,\mu_2,\mu_3$, set

$$
\begin{aligned}
p_0&=(1+\mu_1+\mu_2+\mu_3)/4,&p_1&=(1+\mu_1-\mu_2-\mu_3)/4,\\
p_2&=(1-\mu_1+\mu_2-\mu_3)/4,&p_3&=(1-\mu_1-\mu_2+\mu_3)/4.
\end{aligned}
\tag{S.139}
$$

The normalized Choi matrix is diagonal in the Bell basis with these entries. CP makes every $p_j\geq0$ and TP gives $\sum_jp_j=1$, so $\Lambda'(X)=\sum_{j=0}^3p_j\sigma_jX\sigma_j$, with $\sigma_0=I_2$. The Kraus-trace formula gives $p_0=F_e(I_2/2,\Lambda')=F_e(I_2/2,\Lambda)$; simultaneous unitary conjugation preserves this fidelity.

For every finite complex reference and every trace-class operator, unitary conjugation preserves its trace norm. Writing $\Lambda'-\mathrm{id}=\sum_{j>0}p_j(\operatorname{Ad}_{\sigma_j}-\mathrm{id})$ gives the diamond upper bound $2\sum_{j>0}p_j$. On a normalized Bell input the four Pauli branches are orthogonal Bell projectors, so the difference has eigenvalues $p_0-1,p_1,p_2,p_3$ and trace norm exactly $2(1-p_0)$. Unitary invariance of the diamond norm proves the first identity of (S.137). This argument applies to self-adjoint unital CPTP qubit channels; it supplies no fidelity–diamond equality for arbitrary channels or for optimized qutrit recoveries.

Finally $R_\xi N_0\iota_\xi-\iota_\xi=\iota_\xi(\Lambda_\xi-\mathrm{id}_2)$. Output isometries preserve trace norm with any finite reference. Combining (S.135) with the first identity proves the second bound. $\square$

## 72. Uniform continuation through every real residual density

**Theorem 72.1 (actual-channel perturbation estimate).** Put $P_2=|2\rangle\langle2|$, $P_{\mathcal C}=I_3-P_2$, $Z_0=P_{\mathcal C}-P_2$ and $Q_0=N_0(P_2)=t_1t_1^T+t_2t_2^T$. For every allowed $\epsilon,Q$,

$$
\begin{aligned}
\mathcal D_{d_\epsilon}(X)
&=P_{\mathcal C}XP_{\mathcal C}+P_2XP_2
+d_\epsilon(P_{\mathcal C}XP_2+P_2XP_{\mathcal C})\\
&=\frac{1+d_\epsilon}{2}X+\frac{1-d_\epsilon}{2}Z_0XZ_0,\\
N_{\epsilon,Q}(X)&=N_0\mathcal D_{d_\epsilon}(X)
+\epsilon\langle2|X|2\rangle(Q-Q_0),\\
\|N_{\epsilon,Q}-N_0\|_\diamond
&\leq1-\sqrt{1-\epsilon}+\epsilon\|Q-Q_0\|_1
\leq\eta_\epsilon:=1-\sqrt{1-\epsilon}+2\epsilon
\leq\frac83\epsilon\leq\frac1{48}.
\end{aligned}
\tag{S.140}
$$

Proof. The channel identity follows on all four input blocks: the code block is unchanged, the two cross blocks acquire $d_\epsilon$, and the third diagonal output becomes $d_\epsilon^2Q_0+\epsilon Q$. It therefore holds on every complex input and after tensoring with any reference.

The dephasing mixture gives $\|\mathcal D_{d_\epsilon}-\mathrm{id}\|_\diamond\leq1-d_\epsilon$. A balanced superposition of one code vector and $|2\rangle$ has its two cross entries reduced by $d_\epsilon$, and the resulting difference has eigenvalues $\pm(1-d_\epsilon)/2$. This attains $1-d_\epsilon$. For any fixed $A\in M_5$, the map $X\mapsto\langle2|X|2\rangle A$ has diamond norm $\|A\|_1$: after any finite reference it is the reference compression of $X$ tensored with $A$. Compression has induced trace norm at most one, tensor-product trace norms multiply, and $P_2$ attains equality. Apply this with $A=Q-Q_0$. Since $Q,Q_0$ are densities, their trace distance is at most two. CPTP postprocessing by $N_0$ is contractive. Finally $d_\epsilon\geq1/2$, so $1-d_\epsilon=\epsilon/(1+d_\epsilon)\leq2\epsilon/3$. These prove every bound in (S.140), uniformly in the entire real-density continuum. $\square$

**Theorem 72.2 (strict subcode/full-code separation).** For every fixed actual $N_{\epsilon,Q}$ of (S.113), every complex unit $\xi$ has the whole-output recovery (S.129), independent of $\epsilon,Q$, satisfying

$$
\|R_\xi N_{\epsilon,Q}\iota_\xi-\iota_\xi\|_\diamond
\leq b:=\frac{55-24\sqrt3}{48},\qquad
\delta_{N_{\epsilon,Q}}\geq\frac{17}{48}.
\tag{S.141}
$$

In particular, with all recovery infima over complex CPTP maps $M_5\to M_3$,

$$
\sup_{\substack{\xi\in\mathcal C\\\|\xi\|=1}}
\inf_R\|RN_{\epsilon,Q}\iota_\xi-\iota_\xi\|_\diamond
\leq b<\frac9{32}<1-\frac1{\sqrt2}<\frac{17}{48}
\leq\inf_R\|RN_{\epsilon,Q}-\mathrm{id}_3\|_\diamond.
\tag{S.142}
$$

Proof. Fix the same arbitrary recovery $R$ when comparing the purified outputs at $N_0$ and $N_{\epsilon,Q}$ for the same $\rho_\star$. Their trace-norm difference is at most $\eta_\epsilon$ by (S.140) and CPTP contraction. Their difference is Hermitian and traceless, so any effect probability differs by at most $\eta_\epsilon/2$: its positive and negative parts each have trace half its trace norm. Using the pure target effect and (S.127) gives, simultaneously for every $R$,

$$
F_e(\rho_\star,RN_{\epsilon,Q})
\leq\frac{13}{16}+\frac{\eta_\epsilon}{2}\leq\frac{79}{96},\qquad
\|RN_{\epsilon,Q}-\mathrm{id}_3\|_\diamond
\geq2(1-79/96)=\frac{17}{48}.
\tag{S.143}
$$

This is one fixed three-dimensional purification witnessing a lower bound for all unrestricted recoveries. For each $\xi$, use its fixed base recovery $R_\xi$ on the entire perturbed output, including the reset branch outside $P_\xi$. Input isometries and CPTP postprocessing do not increase diamond norm, so

$$
\|R_\xi N_{\epsilon,Q}\iota_\xi-\iota_\xi\|_\diamond
\leq\frac{9-4\sqrt3}{8}+\eta_\epsilon
\leq\frac{55-24\sqrt3}{48}.
\tag{S.144}
$$

The three strict comparisons in (S.142) reduce, by squaring positive sides, to

$$
48\sqrt3>83\quad(6912>6889),\qquad
\frac1{\sqrt2}<\frac{23}{32}\quad(512<529),\qquad
\frac{31}{48}<\frac1{\sqrt2}\quad(961<1152).
\tag{S.145}
$$

The uniform separation between the displayed full-code lower bound and the subcode upper bound is $17/48-b=(12\sqrt3-19)/24>0$, since $432>361$. Every upper estimate holds after every finite complex reference. Taking a separate recovery infimum for each direction and then the direction supremum is therefore legitimate. It does not place a single recovery before that supremum. $\square$

## 73. The exact fixed-input witness exclusion and its quantifiers

**Corollary 73.1 (code-compression rank at most one cannot witness the threshold).** For each fixed $N_{\epsilon,Q}$ and each complex unit $\xi$, the same $R_\xi$ works simultaneously for every density $\rho$ supported on $\operatorname{span}\{\xi,|2\rangle\}$, with arbitrary complex coherences, weights and rank, and every purification. In particular

$$
F_e(\rho,R_\xi N_{\epsilon,Q})\geq1-b/2>
\frac{55}{64}>T_{1/2}:=\frac{1+1/\sqrt2}{2}.
\tag{S.146}
$$

For this actual family, no density with $\operatorname{rank}(P_{\mathcal C}\rho P_{\mathcal C})\leq1$ can be a fixed-input witness satisfying $\max_R F_e(\rho,RN_{\epsilon,Q})\leq T_{1/2}$, or admit a threshold dual of (S.121).

Proof. A supported density is $V_\xi\sigma V_\xi^\dagger$ for a qubit density, including singular endpoints. Any purification lies on that plane tensored with its reference. Thus (S.141) bounds its recovered trace error by $b$. Combining with the binary lower inequality (S.121) gives (S.146); $55/64>T_{1/2}$ is equivalent to the middle comparison of (S.145).

If a code vector $z$ is in the kernel of $P_{\mathcal C}\rho P_{\mathcal C}$, then $0=\langle z,\rho z\rangle=\|\rho^{1/2}z\|^2$, so $\rho z=0$. With code-compression rank one this confines the support to the orthogonal complement of its zero code direction, namely one plane $\operatorname{span}\{\xi,|2\rangle\}$. With code-compression rank zero both code directions vanish, and any unit $\xi$ supplies such a plane. The preceding recovery contradicts a uniform upper fidelity threshold at that input. Weak duality gives the same exclusion for a threshold dual. $\square$

**Definition 73.2 (the common-object distinction).** The demonstrated quantifier order is one actual encoder, then every complex direction, then one recovery for the whole plane, then every density and finite reference on that plane. In fact $R_\xi$ depends only on $N_0$ and $\xi$ and works for all the allowed $\epsilon,Q$. On the other side, one actual encoder and the same $\rho_\star$ precede every unrestricted recovery in (S.143). The construction never exchanges $\forall\xi\,\exists R_\xi$ with a common qutrit recovery serving every input. The strict gap concerns these distinct operational optimizations for the same channel.

The exclusion is exactly $\operatorname{rank}(P_{\mathcal C}\rho P_{\mathcal C})\leq1$, not every total-rank-two input or every complex two-dimensional subspace. An input of total rank two can have code-compression rank two. The witness $\rho_\star$ has total rank three and code-compression rank two and is sufficient for (S.143); necessity of total rank three among unrestricted threshold witnesses is not proved. Sections 48–51 of the first volume already supply the real-direction plane obstruction for the reused base; the all-complex-direction, referenced norm and perturbed-family conclusions here extend that scope.

## 74. Exact matrix interfaces for the remaining arbitrary third columns

**Definition 74.1 (the full lambda-one normal form).** In this section return to arbitrary $0<\beta\leq1/2$, $a=1-\beta$, and every original-real actual encoder of Definition 52.1 with $\lambda=f(\tau,\bar\tau)=1$. Unit-trace fidelity one gives $\tau=\bar\tau$. It is real symmetric, so a real orthogonal environment change diagonalizes it to $\operatorname{diag}(a,\beta,0,\ldots,0)$. The real and imaginary parts of the two nonzero orthogonal phase Kraus vectors, together with their orthogonal conjugate partners, then give a real output frame as in (R.7). In those coordinates the first two column lists and all third columns are

$$
\begin{gathered}
E_0=[\sqrt a\,b_1,\sqrt\beta\,b_2,0,\ldots,0],\qquad
E_1=[\sqrt a\,g_1,\sqrt\beta\,g_2,0,\ldots,0],\qquad
\mathsf T=[t_1,\ldots,t_r],\\
K_\alpha=[(E_0)_\alpha,(E_1)_\alpha,t_\alpha],\qquad
\|\mathsf T\|_{\rm HS}^2=1,\qquad
\operatorname{Tr}(E_0^\dagger\mathsf T)=\operatorname{Tr}(E_1^\dagger\mathsf T)=0.
\end{gathered}
\tag{S.147}
$$

This uses coordinate changes of the same actual channel, retaining $r\leq9$ and every admissible real third column, including columns at indices greater than two. It is not a two-Kraus restriction. Environmental conjugation and all actual blocks transform with the coordinates as required in Definition 58.1. No normal form for $\sqrt a<\lambda<1$ is inferred here.

**Proposition 74.2 (real-direction diagonal weighted-input interface).** For real $\theta$ and $p\in[0,1]$, set $\xi=\cos\theta|0\rangle+\sin\theta|1\rangle$, $P_\xi^{\rm in}=|\xi\rangle\langle\xi|$ on the input, $\rho_{\theta,p}=pP_\xi^{\rm in}+(1-p)P_2$, and

$$
\begin{gathered}
e_j(\theta)=\cos\theta b_j+\sin\theta g_j,\quad
D_\theta=a e_1e_1^\dagger+\beta e_2e_2^\dagger=N(P_\xi^{\rm in}),\\
Q_N=\mathsf T\mathsf T^\dagger=N(P_2),\qquad
X_\theta=\sqrt a\,e_1t_1^\dagger+\sqrt\beta\,e_2t_2^\dagger=N(|\xi\rangle\langle2|).
\end{gathered}
\tag{S.148}
$$

Then the exact optimum over all complex whole-output recoveries is

$$
\begin{aligned}
\max_R F_e(\rho_{\theta,p},RN)
=\max_{0\preceq P\preceq I_5}\Bigl\{&p^2(1-\operatorname{Tr}(PD_\theta))
+(1-p)^2\operatorname{Tr}(PQ_N)\\
&+2p(1-p)\|\sqrt{I_5-P}\,X_\theta\sqrt P\|_1\Bigr\}.
\end{aligned}
\tag{S.149}
$$

Proof. Restricting recovery output to the target plane loses nothing: postcompose any qutrit recovery with the channel that compresses to the plane and returns leakage to one fixed vector in it. In the Kraus-trace formula the compressed branch preserves the original overlap with the supported $\rho_{\theta,p}$; added reset branches contribute nonnegative squared overlaps. Thus code-valued recoveries attain the unrestricted optimum.

For their unital CP adjoints put $P=R^\dagger(P_2)$, $B=R^\dagger(|\xi\rangle\langle2|)$. Complete positivity and unitality are exactly

$$
\begin{pmatrix}I_5-P&B\\B^\dagger&P\end{pmatrix}\succeq0
\quad\Longleftrightarrow\quad
B=\sqrt{I_5-P}\,C\sqrt P,\quad\|C\|_\infty\leq1.
\tag{S.150}
$$

This block contraction factorization includes singular $P$ and $I_5-P$. The objective before optimizing $B$ is

$$
p^2\operatorname{Tr}((I_5-P)D_\theta)+(1-p)^2\operatorname{Tr}(PQ_N)
+2p(1-p)\operatorname{Re}\operatorname{Tr}(B^\dagger X_\theta).
\tag{S.151}
$$

Substituting (S.150), cyclicity gives $\operatorname{Re}\operatorname{Tr}(C^\dagger\sqrt{I_5-P}X_\theta\sqrt P)$. Optimizing this one common contraction $C$ yields exactly the trace norm in (S.149). Conversely every such positive block defines a unital CP adjoint and a whole-output CPTP recovery, so this is equality. At $p=0$ choose $P=I_5$; at $p=1$ choose $P=0$. Both optima are one, as required for a pure known input. No inverse is used at a singular effect or endpoint. The displayed input is diagonal in the real-direction code basis; (S.149) is not asserted as a formula for arbitrary input coherences or all complex directions. $\square$

**Proposition 74.3 (common full-input Schur interface).** For the same real data (S.147), the fixed input $\rho_\star$ and a real symmetric $Y\succ0$, the full dual inequality (S.121) is equivalent to

$$
\frac1{16}(E_0^\dagger Y^{-1}E_0+E_1^\dagger Y^{-1}E_1)
+\frac14\mathsf T^\dagger Y^{-1}\mathsf T\preceq I_r.
\tag{S.152}
$$

Proof. The $\alpha$th vector of (S.118) is the stacked real vector $((E_0)_\alpha/4,(E_1)_\alpha/4,t_\alpha/2)$. Collect these as columns of $W$. The positive-definite Schur criterion $WW^\dagger\preceq I_3\otimes Y$ iff $W^\dagger(I_3\otimes Y^{-1})W\preceq I_r$ gives exactly (S.152). It retains every off-diagonal Kraus-index term and the same $Y$ across all three input blocks. For singular Hermitian $Y$, use the full inequality $C_{\rho_\star,N}\preceq I_3\otimes Y$ directly. Merely substituting a pseudoinverse into (S.152) without a range condition is not an equivalent singular formulation. $\square$

**Proposition 74.4 (fixed-input exact SDP and sufficient uniform obligations).** For every actual $N$ and every complex density $\rho$, including singular inputs, Theorem 7.1 transports to

$$
\max_{R\ {\rm CPTP}}F_e(\rho,RN)
=\max_{J\succeq0,\ \operatorname{Tr}_3J=I_5}\operatorname{Tr}(C_{\rho,N}J)
=\min_{Y=Y^\dagger,\ I_3\otimes Y\succeq C_{\rho,N}}\operatorname{Tr}Y.
\tag{S.153}
$$

Both optima are attained. Indeed $J_0=I_3\otimes I_5/3$ is strictly primal feasible, and $Y=cI_5$, $c>\|C_{\rho,N}\|_\infty$, is strictly dual feasible. The primal is compact with trace five. Dual feasible $Y$ is PSD, so its bounded-trace sublevels are compact too. Finite-dimensional Slater duality gives the claimed equality and attainment, independent of singularity of $\rho$. Singular dual optima are permitted by the full inequality.

For the arbitrary-third-column $\lambda=1$ branch, a sufficient fixed-$\rho_\star$ programme would construct, for each actual $N$, one real $Y_N\succ0$ satisfying (S.152) and

$$
\operatorname{Tr}Y_N\leq\frac{1+\sqrt a}{2}.
\tag{S.154}
$$

The more general sufficient programme, allowing an actual density to depend on that encoder, is

$$
\forall N\ \exists\rho_N\in\mathsf D(\mathbb C^3)\ \exists Y_N=Y_N^\dagger:
\quad C_{\rho_N,N}\preceq I_3\otimes Y_N,\qquad
\operatorname{Tr}Y_N\leq\frac{1+\sqrt a}{2}.
\tag{S.155}
$$

For each successful certificate, $\rho_N,Y_N$ precede every recovery of that same encoder, and (S.121) gives $\delta_N\geq1-\sqrt a$. One $Y_N$ must constrain the complete Kraus list; different matrices for separate columns or input branches do not supply it. The matrix may depend on $N$; no common matrix across different encoders is required.

Uniform feasibility of (S.152)–(S.154) for arbitrary admissible third columns is not proved here. Neither is feasibility of (S.155) for that entire branch or the original all-beta class. These are sufficient witness routes, not asserted necessary conditions for the original diamond target: failure of such a route does not exhibit a full-reference recovery below the target. The exact fixed-input equality (S.153) is reused SDP theory; it does not establish the missing all-channel existence statement.

## 75. Attribution, preserved target and analytic limits

**Definition 75.1 (reuse and primary-source conditions).** The base $N_0$, $\rho_\star$, actual class and residual identities, real-direction plane obstruction, supported transpose completion, polar/midpoint identities and exact recovery SDP reuse Sections 1–2, 7 and 48–51 of the first volume. The existing declarations `SpectralTransposeRecovery.spectral_transpose_candidate` and `ReferencePetzChannel.completed_reference_petz_channel`, cited there, supply the corresponding general support-completion structures; no new general Petz construction is claimed here. The additional source-specific analytic consequences are the sharper rational dual, the all-complex-direction full-reference bound and its uniform arbitrary-real-$Q$ continuation through actual encoder ranks three through seven. These are `repo-derived` compositions, with no global priority or novelty assertion.

The standard methods have the following bounded primary-source scope. Bény–Oreshkov, [arXiv:0907.5391v4](https://arxiv.org/html/0907.5391v4), Theorem 1 and (1)–(3), uses root fidelity and all appropriately dimensioned channels. Their [arXiv:1103.0649v3](https://arxiv.org/html/1103.0649v3), Corollary 5 and (64), gives the unrestricted-channel identity; fixed-input (132) is Kraus bounded whereas (133) is unrestricted. Neither supplies an unrestricted fidelity–diamond equality or the missing arbitrary-third-column threshold. The separation proof above uses the direct fixed-input dual and independently proved Pauli norm identity, without those optimized-channel equalities.

Barnum–Knill, [arXiv:quant-ph/0004088v2](https://arxiv.org/html/quant-ph/0004088v2), (12), gives the transpose formula on the supported noise output; its ensemble performance Theorem 3 requires commuting density matrices. Ng–Mandayam, [arXiv:0909.0931v2](https://arxiv.org/html/0909.0931v2), (4) and Section III.A, likewise takes the inverse on output support. Here only that construction is reused, with the explicit whole-output completion (S.129); their performance estimates are not imported as full-reference diamond bounds. Fletcher–Shor–Win, [arXiv:quant-ph/0606035](https://arxiv.org/html/quant-ph/0606035), (20)–(22), gives the fixed-input recovery SDP with objective $\operatorname{Tr}(JC)$ and TP marginal, agreeing with (S.118)–(S.121) and (S.153) under the stated conventions.

Watrous, [arXiv:0901.4709v2](https://arxiv.org/html/0901.4709v2), Section 4, gives a channel-difference SDP value equal to one half of the diamond norm; all norms here remain unhalved. Watrous, [arXiv:1207.5726v2](https://arxiv.org/html/1207.5726v2), Section 2.1 and Lemma 2, (5), permits arbitrary PSD operands and the singular-valid block contraction factorization used in (S.150). The fixed-input recovery SDP has its own strict feasible points in (S.153); it does not assume strict feasibility of a singular-operand fidelity SDP. These seven primary interfaces are used only with these conditions, not as an exhaustive literature survey or a new authentication claim by this source author.

**Definition 75.2 (unchanged programme and unresolved boundaries).** The family in (S.113) stays exactly at $\beta=1/2$ and $\lambda=1$. It satisfies a stronger full-qutrit lower bound than the original target while obstructing fixed-input witnesses with code-compression rank at most one. It is progress within the same programme, not a counterexample to (S.66), and gives no full-qutrit recovery improving that benchmark. Neither side of (S.142) is asserted to equal the displayed bound.

The original domain remains all actual original-real CPTP encoders $M_3\to M_5$, every $0<\beta\leq1/2$, the original phase-difference spectrum, all admissible third columns, actual minimal Kraus ranks at most nine, every complex CPTP recovery on the whole output, every finite complex reference, and the unhalved diamond norm. The arbitrary-third-column witness obligations (S.154)–(S.155) and the $\sqrt a<\lambda<1$ bridge remain unproved by this increment. The estimate (S.140) measures the actual perturbation of $N_0$ and does not supply a distance estimate from $1-\lambda$. The preceding conditional interfaces, including Theorem 66.2, retain their stated hypotheses; this separate explicit-family proof does not strengthen their evidence status.

All claims above are finite-dimensional analytic mathematics. The proofs include arbitrary complex input densities and references where stated, support inverses zero on kernels, singular density and effect endpoints, and the full convention transport. They assert no empirical physical realization, native recovery-control capability, Lean/kernel verification, exhaustive literature result, global novelty or completion of the original all-class target.

## 追加锚（本行以下为增补区）

## 76. The all-positive-beta common-projection statement

**Definition 76.1 (one supported center and one conjugated defect).** Retain the capped root-fidelity maximum $H_a$ of (S.57)–(S.58), the common-projection system (S.59), and the spectral consumer (S.90)–(S.91). Set

$$
h=\frac1{\sqrt2},\qquad u=\sqrt a=\sqrt{1-\beta},\qquad
T=\frac{1+u}{2},\qquad d=\frac{1-u}{2},\qquad v=\sqrt T,
\qquad \beta=4dT,
\qquad 0<\beta\leq\frac12.
\tag{S.156}
$$

Thus $h\leq u<1$. Let $k\geq2$ be any fixed finite integer, and work on the exact center support:

$$
\begin{gathered}
\omega=\operatorname{diag}(s,t,\lambda_3,\ldots,\lambda_k)>0,
\quad s\geq t\geq\lambda_3\geq\cdots\geq\lambda_k>0,
\quad\operatorname{Tr}\omega=1,\\
Z=\begin{pmatrix}Z_0\\Z_1\\Z_2\end{pmatrix},\qquad
Z_i:\mathbb C^{3k-5}\to\mathbb C^k,\qquad
Z^\dagger Z=I_{3k-5},\\
E=ZZ^\dagger,\qquad \widehat P=I-E,\qquad
\operatorname{rank}E=3k-5,\qquad\operatorname{rank}\widehat P=5.
\tag{S.157}
\end{gathered}
$$

For $k=2$ there is no tail. In an actual application $E=\overline D$ is the conjugated defect of (S.55)–(S.60), not the unconjugated $D$. For each complex unit $\psi=(\psi_0,\psi_1)$ define

$$
\begin{gathered}
Z_\psi=\psi_0Z_0+\psi_1Z_1,\qquad
M_\psi=\omega-\sqrt\omega Z_\psi Z_\psi^\dagger\sqrt\omega,
\qquad q_i=\operatorname{Tr}(\omega Z_iZ_i^\dagger),\\
H_a(M_\psi)>v\quad\text{for every complex unit }\psi,
\qquad q_2<d.
\tag{S.158}
\end{gathered}
$$

The last line is the hypothetical strict system to be excluded. The center, $E$, and its three blocks precede the entire sphere of tests. All statements below concern this one implementation of the projection geometry. The symbol $\varepsilon=T-s$ used below is a leading-eigenvalue deficit, distinct from the tail mass $1-s-t$ and from earlier family perturbation parameters.

**Theorem 76.2 (all-positive-beta infeasibility).** For every $0<\beta\leq1/2$ and every fixed finite positive center rank $k\geq2$, no data of Definition 76.1 satisfy (S.158). Singular directional marginals, a singular common matrix $L$ in the reduction below, and singular leading two-by-two blocks are included. This is an exclusion of the strict relaxation itself. Its proof occupies Sections 77–79; the actual-channel consequence in Section 80 additionally assumes each named inherited interface.

## 77. A trace band and a branch-complete common-vector bound

**Proposition 77.1 (the supported trace band).** Under hypothetical feasibility (S.158),

$$
3T<\operatorname{Tr}[(I_3\otimes\omega)\widehat P]
\leq3s+2t,\qquad
s>3T-2>a.
\tag{S.159}
$$

Moreover $s<T$, and therefore

$$
0<\varepsilon:=T-s<2d,\qquad
\frac32\varepsilon<t\leq1-s=d+\varepsilon,\qquad s>a.
\tag{S.160}
$$

Proof. By (S.57), $H_a(M)^2\leq\operatorname{Tr}M$. The two basis directions in (S.158) give $q_0,q_1<d$; the third budget already gives $q_2<d$. Since $\operatorname{Tr}[(I_3\otimes\omega)\widehat P]=3-q_0-q_1-q_2$, its value is greater than $3T$. The five leading eigenvalues of $I_3\otimes\omega$ are $s,s,s,t,t$, with multiplicities, so the exact rank-five allocation (S.22) proves the upper bound. Using $t\leq1-s$ gives $s>3T-2$. Finally

$$
3T-2-a=d(2u-1)>0.
$$

For $s<T$, use the existing positive-weight fidelity inequality (S.16) and capped trace maximum (S.17), directly in (S.58): for every $X>0$,

$$
H_a(M)\leq\frac12\bigl(m_X+\operatorname{Tr}(MX^{-1})\bigr),
\qquad m_X=a\lambda_1(X)+\beta\lambda_2(X),
\tag{S.161}
$$

where the two eigenvalues are decreasingly ordered. Choose $X=\operatorname{diag}(v/u,1/(2v),\ldots,1/(2v))$. These positive entries are in the displayed order since $2T/u=(1+u)/u>1$. They give $m_X=uv+\beta/(2v)=v$, and hence

$$
H_a(\omega)\leq\frac{3T-s}{2v}.
$$

The order monotonicity proved in (S.68)–(S.71) and $M_\psi\preceq\omega$ give $H_a(\omega)>v$, forcing $s<T$. Now (S.159) gives $t>3\varepsilon/2$ and $\varepsilon<T-(3T-2)=2d$. This proves (S.160). No actual marginal or positive semidefinite operand has been inverted. $\square$

**Proposition 77.2 (one common vector and both cap branches).** Let $K_2$ be the span of two selected leading eigenvectors of the supported center. The common-vector construction (S.68)–(S.71) gives one unit vector and one complex matrix

$$
\begin{gathered}
\eta=(\ell_0,\ell_1,b_{\rm vec})
\in\operatorname{ran}E\cap(\mathbb C^3\otimes K_2),\qquad
L=[\ell_0,\ell_1],\quad G=LL^\dagger,\quad\Omega=\operatorname{diag}(s,t),\\
\operatorname{Tr}G+\|b_{\rm vec}\|^2=1,\qquad
q_2\geq t(1-\operatorname{Tr}G),\\
z=L\psi,\qquad\kappa=\|z\|^2\leq1,\qquad q=z^\dagger\Omega z,\\
0\preceq M_\psi\preceq B_\psi
:=\bigl(\Omega-\sqrt\Omega zz^\dagger\sqrt\Omega\bigr)
\oplus\omega_{\rm tail}.
\tag{S.162}
\end{gathered}
$$

The same $\eta,L$ apply to every complex direction. If $r_{\rm tail}=1-s-t$ and $b=\operatorname{Tr}B_\psi=1-q$, then throughout (S.160),

$$
H_a(B_\psi)^2\leq
\beta b+(a-\beta)s+
2\sqrt{a\beta}\sqrt{st(1-\kappa)+sr_{\rm tail}}.
\tag{S.163}
$$

Proof. The intersection dimension is at least $(3k-5)+6-3k=1$. Choose $\eta$ once in this intersection. The proof of (S.71) uses the transpose-row compression $C_\psi=(\psi_0,\psi_1,0)\otimes I_k$, so that $C_\psi\eta=L\psi$ and $C_\psi EC_\psi^\dagger=Z_\psi Z_\psi^\dagger$. In particular the complex direction is not replaced by its conjugate. The row satisfies $C_\psi C_\psi^\dagger=I_k$, so $0\preceq C_\psi EC_\psi^\dagger\preceq I_k$. Since $E\succeq\eta\eta^\dagger$, positive compression and congruence give (S.162); the third compression gives its budget. For $k=2$, $\mathbb C^3\otimes K_2$ is the full six-dimensional supported space and $E$ has rank one. This proves the same construction on that boundary without compressing an unrelated larger projection. Positivity of the leading block follows from $\kappa\leq\operatorname{Tr}G\leq1$.

Let $\mu\geq\nu\geq0$ be its two eigenvalues. The already computed trace and determinant in (S.69) give

$$
\mu+\nu=b-r_{\rm tail},\qquad
\mu\nu=st(1-\kappa),\qquad \mu\leq s.
$$

Here $0\leq b\leq1$. If $b=0$, the left side of (S.163) is zero and its right side is nonnegative. Suppose $b>0$ and first $\mu\geq ab$. Since $a\geq1/2$, $\mu\geq b/2$; every tail eigenvalue is at most $r_{\rm tail}\leq b-\mu\leq\mu$. Thus $\mu$ is a largest eigenvalue of the whole $B_\psi$. The capped formula, including the equality boundary, reads

$$
H_a(B_\psi)^2
=\beta b+(a-\beta)\mu+
2\sqrt{a\beta}\sqrt{\mu(\nu+r_{\rm tail})}.
$$

Use $a-\beta\geq0$, $\mu\leq s$ and $\mu\nu=st(1-\kappa)$ to obtain (S.163).

In the other case $\mu\leq ab$, the polynomial $x(b-r_{\rm tail}-x)$ is decreasing for $x\geq(b-r_{\rm tail})/2$. Both $\mu$ and $ab$ lie in this interval, in the stated order. Consequently

$$
\begin{aligned}
\mu\nu&\geq ab(b-r_{\rm tail}-ab)
=a\beta b^2-ab r_{\rm tail},\\
\mu\nu+sr_{\rm tail}&\geq a\beta b^2+r_{\rm tail}(s-ab)
\geq a\beta b^2.
\end{aligned}
$$

The last sign uses $s\geq a$ and $b\leq1$. Thus the right side of (S.163) is at least

$$
\beta b+(a-\beta)s+2a\beta b
=b+(a-\beta)(s-ab)\geq b\geq H_a(B_\psi)^2.
$$

This branch does not presume that the leading block contains the largest eigenvalue of $B_\psi$. The proof includes $a=\beta=1/2$, absent tails, $\kappa=1$, rank-one or zero leading blocks and the cap-branch equality. $\square$

**Proposition 77.3 (the full complex sphere yields a strict matrix bound).** Under (S.158), define

$$
\begin{aligned}
C_0&=T-\beta-(a-\beta)s
=\beta u+(a-\beta)\varepsilon>0,\\
\Delta&=4a\beta s(1-s)-C_0^2
=(T-s)\bigl(s-T(2u-1)^2\bigr)
=\varepsilon(2\beta u-\varepsilon).
\end{aligned}
\tag{S.164}
$$

Then $\Delta>0$ and

$$
q_2>f_\beta(s,t):=
 t-\frac{\Delta}{2\beta}
\left[\frac1{2as+C_0}+\frac{t}{s(2at+C_0)}\right].
\tag{S.165}
$$

Proof. By monotonicity, (S.158) and (S.163),

$$
2\sqrt{a\beta}\sqrt{s(1-s)-st\kappa}>C_0+\beta q>0.
$$

Both sides are positive, so squaring and collecting terms is valid and gives

$$
4a\beta st\kappa+2\beta C_0q+\beta^2q^2<\Delta.
\tag{S.166}
$$

In particular $\Delta>0$. Drop the nonnegative last term. Since the inequality holds for every complex unit $\psi$ for this one $L$, it is the Hermitian inequality

$$
\begin{gathered}
L^\dagger\mathcal D L\prec\Delta I_2,\qquad
\mathcal D=4a\beta st I_2+2\beta C_0\Omega\succ0,\\
G\prec\Delta\mathcal D^{-1},\qquad
\mathcal D=\operatorname{diag}
\bigl(2\beta s(2at+C_0),\ 2\beta t(2as+C_0)\bigr).
\tag{S.167}
\end{gathered}
$$

Indeed, for $K=\mathcal D^{1/2}L$, the first inequality says $\|K\|_{\rm op}^2<\Delta$. Equality of the operator norms of $K$ and its adjoint gives $KK^\dagger\prec\Delta I_2$; congruence by $\mathcal D^{-1/2}$ proves the second. This argument needs no inverse of $L$. Every entry of $\mathcal D$ is strictly positive since $\beta,s,t,C_0>0$.

Taking traces and using the same third budget in (S.162) gives

$$
\begin{aligned}
q_2&\geq t(1-\operatorname{Tr}G)\\
&>t-\frac{\Delta}{2\beta}
\left[\frac{t}{s(2at+C_0)}+\frac1{2as+C_0}\right].
\end{aligned}
$$

This proves (S.165), with its strict direction, also when $G$ is singular. $\square$

## 78. A uniform coefficient inequality on the complete beta interval

**Lemma 78.1 (the all-beta coefficient bound).** Throughout the hypothetical-feasibility region (S.160), (S.164), set

$$
A_u=\frac12+\frac{u}{1+u}.
$$

Then

$$
f_\beta(s,t)>t-A_u\varepsilon.
\tag{S.168}
$$

Proof. Equations (S.164)–(S.165) give the exact expression

$$
\begin{aligned}
f_\beta(s,t)&=t-\varepsilon\mathcal F,\\
\mathcal F&=\left(u-\frac{\varepsilon}{2\beta}\right)
\left[\frac1{u(1+u)-\varepsilon}
+\frac{t}{s(2at+C_0)}\right].
\end{aligned}
\tag{S.169}
$$

The prefactor is positive because $\Delta>0$. The first denominator equals $2as+C_0>0$. At fixed $s,u$, the derivative of the second summand in brackets with respect to $t$ is $C_0/[s(2at+C_0)^2]>0$. Replacing $t$ by its upper bound $1-s=d+\varepsilon$ is therefore an upper bound for $\mathcal F$.

Normalize only at $\beta>0$, so $u<1$, and put

$$
\begin{gathered}
\xi=\frac{\varepsilon}{1-u}\in(0,1),\qquad p=u(1+u),\qquad e=1-u,\\
A=p-e\xi,\qquad
B=(1+u-2e\xi)(2u+1)\bigl(u+(2u-1)\xi\bigr),\qquad
C=2p-\xi.
\tag{S.170}
\end{gathered}
$$

All three are strictly positive on the larger closed rectangle $h\leq u\leq1$, $0\leq\xi\leq1$. In fact $A\geq u^2+2u-1>0$, the three factors of $B$ are respectively at least $3u-1>0$, $2u+1>0$ and $u>0$, and $C\geq2u>0$. Substitution of $s=T-(1-u)\xi$, $\beta=(1-u)(1+u)$ in the upper replacement gives

$$
\begin{aligned}
\mathcal F&\leq\widehat F(u,\xi)
=\frac{C}{2(1+u)}\left(\frac1A+\frac{1+2\xi}{B}\right),\\
A_u-\widehat F(u,\xi)
&=\frac{\mathscr D_u(\xi)}{2(1+u)AB},\\
\mathscr D_u(\xi)&=(1+3u)AB-C\bigl[B+A(1+2\xi)\bigr].
\end{aligned}
\tag{S.171}
$$

Every denominator cleared here is positive. The numerator is a cubic in $\xi$, with the complete exact Bernstein expansion

$$
\begin{aligned}
\mathscr D_u(\xi)
&=\sum_{j=0}^3 b_j(u)\binom3j\xi^j(1-\xi)^{3-j},\\
b_0&=(6u^2+u-3)p^2,\qquad
b_1=\frac p3\pi_1(u),\qquad
b_2=\frac13\pi_2(u),\qquad b_3=\pi_3(u),\\
\pi_1(u)&=42u^4+25u^3-22u^2-17u+4,\\
\pi_2(u)&=90u^6+111u^5-49u^4-70u^3-6u^2+15u-1,\\
\pi_3(u)&=54u^6+81u^5-87u^4-26u^3+14u^2+9u-3.
\end{aligned}
\tag{S.172}
$$

The identity follows by expanding (S.171) in powers of $\xi$; the four power coefficients are $b_0$, $3(b_1-b_0)$, $3(b_0-2b_1+b_2)$ and $-b_0+3b_1-3b_2+b_3$, respectively. The signs of all four Bernstein coefficients admit the following exact proof over the whole rectangle.

For $b_0$, $6u^2+u-3\geq u>0$. For the first two polynomials,

$$
\begin{aligned}
\pi_1(h)&=\frac{7-9h}{2}>0,\\
\pi_1'(u)&=u(168u^2-44)+75u^2-17
\geq40u+\frac{41}{2}>0,\\
\pi_2(h)&=\frac{31h-20}{4}>0,\\
\pi_2'(u)&=u^3(540u^2-196)+u^2(555u^2-210)+15-12u\\
&\geq74u^3+\frac{135}{2}u^2+3>0.
\end{aligned}
\tag{S.173}
$$

For the remaining polynomial,

$$
\begin{aligned}
\pi_3(h)&=\frac{65h-44}{4}>0,\qquad
\pi_3'(h)=\frac{285-260h}{4}>0,\\
\pi_3''(h)&=654h-89>0,\\
\pi_3^{(3)}(u)&=u(6480u^2-2088)+4860u^2-156
\geq1152u+2274>0.
\end{aligned}
\tag{S.174}
$$

The derivative lower bounds use only $u^2\geq1/2$ and $u\leq1$. Every endpoint sign follows from $h^2=1/2$ and the positive-root comparisons $7/10<h<3/4$: for example $7-9h>1/4$, $31h-20>17/10$, $65h-44>3/2$, $285-260h>90$, and $654h-89>1844/5$. Thus $\pi_1,\pi_2$ stay positive; successively $\pi_3''$, $\pi_3'$ and $\pi_3$ stay positive too. Since $p>0$, every $b_j$ is strictly positive on $[h,1]$.

The Bernstein basis functions are nonnegative on $[0,1]$ and sum to one. Equation (S.172) therefore proves $\mathscr D_u(\xi)>0$ throughout the closed rectangle, including its edges. Equation (S.171) gives $\mathcal F\leq\widehat F<A_u$. Since $\varepsilon>0$, (S.169) proves (S.168). This is a universal polynomial sign proof, without sampled signs. The polynomial statement includes $u=1$; the normalization and every application containing $1/\beta$ or $1/(1-u)$ use $\beta>0$. $\square$

**Corollary 78.2 (the refined spectral interval).** Hypothetical feasibility requires

$$
\begin{gathered}
t<d+A_u\varepsilon,\qquad
\varepsilon<d(1+u)=\frac\beta2,\qquad
uT<s<T.
\tag{S.175}
\end{gathered}
$$

Proof. Combine $q_2<d$, (S.165) and (S.168) to get the first inequality. Since $t>3\varepsilon/2$, it follows that $(3/2-A_u)\varepsilon<d$. The exact identity $3/2-A_u=1/(1+u)>0$ gives $\varepsilon<d(1+u)=\beta/2$. Subtracting this from $T$ gives $s>T-\beta/2=uT$, while $s<T$ is already known. $\square$

## 79. Ordered spectral weights and the strict overlap contradiction

**Proposition 79.1 (the exact five largest weights).** In the refined region (S.160), (S.175), define

$$
D_s=s+2t-T=2t-\varepsilon>0,\qquad
x_{\rm w}=\sqrt{\frac{s}{a}},\qquad
y_{\rm w}=\sqrt{\frac{D_s}{2\beta}},\qquad
X=\operatorname{diag}(x_{\rm w},y_{\rm w},\ldots,y_{\rm w}),\qquad
c=\frac1{y_{\rm w}}.
\tag{S.176}
$$

Then $x_{\rm w}>y_{\rm w}>0$ and $s/x_{\rm w}>t/y_{\rm w}$. The five largest eigenvalues of $K_c=\operatorname{diag}(\omega X^{-1},\omega X^{-1},c\omega)$, with multiplicities, are exactly

$$
\frac{s}{y_{\rm w}},\quad
\frac{s}{x_{\rm w}},\quad\frac{s}{x_{\rm w}},\quad
\frac{t}{y_{\rm w}},\quad\frac{t}{y_{\rm w}}.
\tag{S.177}
$$

Proof. First $t>3\varepsilon/2$ gives $D_s>2\varepsilon>0$. For the first ordering, use $t\leq1-s$ and $s>3T-2$ to obtain

$$
\begin{aligned}
2\beta s-aD_s
&\geq(2-a)s+aT-2a\\
&>(2-a)(3T-2)+aT-2a\\
&=(1-u)(u^2+2u-1)>0.
\end{aligned}
\tag{S.178}
$$

All factors are positive at $h\leq u<1$. Since $a,\beta>0$, this is exactly $x_{\rm w}>y_{\rm w}$ after squaring positive quantities.

For the second ordering, positive-side squaring reduces it to

$$
\Phi_s(t):=as(2t-\varepsilon)-2\beta t^2>0.
\tag{S.179}
$$

This is concave in $t$. The allowed $t$ lies between $3\varepsilon/2$ and $1-s$. At the lower endpoint,

$$
\Phi_s(3\varepsilon/2)
=\varepsilon\left[2aT-\frac{9-5a}{2}\varepsilon\right]>0.
\tag{S.180}
$$

Indeed $\varepsilon<\beta/2$, and $\beta(9-5a)<8aT$. To prove this last comparison, divide its difference by $1+u>0$: it is equivalent to $q_*(u)=9-9u-9u^2+5u^3<0$. Its value at $h$ is $(9-13h)/2<0$, and $q_*'(u)=15u^2-18u-9\leq-9-3u<0$ on $[h,1]$. This proves the strict sign in (S.180).

At the upper endpoint put

$$
\begin{aligned}
\Phi_{\rm top}(s)&:=\Phi_s(1-s)
=as(2-s-T)-2\beta(1-s)^2,\\
\Phi_{\rm top}(T)&=2dT(2u-1)>0,\\
\Phi_{\rm top}(uT)&=dTQ(u),\qquad
Q(u)=-u^4-u^3+6u^2+8u-8.
\end{aligned}
\tag{S.181}
$$

The function $\Phi_{\rm top}$ is concave in $s$, and (S.175) confines $s$ between $uT$ and $T$. Both endpoints are positive: $Q(h)=3(10h-7)/4>0$, and

$$
Q'(u)-(5u+8)=u(1-u)(4u+7)\geq0.
$$

Hence $Q>0$ on $[h,1]$. Concavity first in $s$ and then in $t$ proves (S.179) on the full required interval. There is no assumption on the tail beyond positivity and ordering.

The leading center coordinate contributes $s/y_{\rm w}$ once and $s/x_{\rm w}$ twice to $K_c$. Each other coordinate contributes three copies of $\lambda_j/y_{\rm w}\leq t/y_{\rm w}$. The established strict comparisons put the first three above these; two copies belonging to $t$ complete the top five. Ties among the remaining coordinates are harmless. For $k=2$ this is a list of five among six eigenvalues, with the third copy of $t/y_{\rm w}$ outside the chosen five. This proves (S.177) also on the full-support rank-two boundary. $\square$

**Theorem 79.2 (the two necessary inequalities have no overlap).** The strict system (S.158) is impossible for every parameter and center in Theorem 76.2.

Proof. Reuse (S.91) directly for the relaxed capped fidelities. For completeness, the two basis tests and (S.161), with $A_\omega=\omega X^{-1}$, give

$$
\begin{aligned}
\operatorname{Tr}[A_\omega(E_{00}+E_{11})]
&<2(m_X+\operatorname{Tr}A_\omega-2v),\\
2\operatorname{Tr}A_\omega+c-S_5(K_c)
&\leq\operatorname{Tr}(K_cE)\\
&<2(m_X+\operatorname{Tr}A_\omega-2v)+cd,\\
J_c(X):=S_5(K_c)+2m_X-cT&>4v.
\end{aligned}
\tag{S.182}
$$

The lower bound is the exact rank-five allocation to this same $\widehat P=I-E$; the upper bound uses the same $q_2<d$. All these inequalities hold for one center and one conjugated defect. No separately attainable directionwise marginal is inserted into an actual implementation.

At the positive weights of (S.176), the ordered list (S.177) gives $m_X=ax_{\rm w}+\beta y_{\rm w}$ and

$$
\begin{aligned}
J_c(X)
&=\frac{2s}{x_{\rm w}}+2ax_{\rm w}
+\frac{D_s}{y_{\rm w}}+2\beta y_{\rm w}\\
&=4\sqrt{as}+2\sqrt{2\beta D_s}>4\sqrt T,\\
t&>g_\beta(s):=\frac{T-s}{2}
+\frac{(\sqrt T-\sqrt{as})^2}{\beta}.
\end{aligned}
\tag{S.183}
$$

To obtain the last inequality, $s<T$ and $a\leq1$ give $as<T$. Thus the preceding strict comparison is $\sqrt{2\beta D_s}>2(\sqrt T-\sqrt{as})$, with both sides positive. Squaring and using $D_s=2t-\varepsilon$ proves exactly the stated bound; the reverse manipulations are valid as well.

For the opposite comparison put $z=\sqrt{s/T}\in(0,1)$. Since $\varepsilon=T(1-z^2)>0$ and $d/T=(1-u)^2/\beta$, exact subtraction and cancellation of the positive $1-z$ give

$$
\begin{aligned}
\frac{g_\beta(s)-d}{T-s}
&=\frac12+\frac{(1-uz)^2-(1-u)^2}{\beta(1-z^2)}\\
&=\frac12+\frac{u[2-u(1+z)]}{\beta(1+z)}\\
&=A_u+\frac{u(1-z)}{\beta(1+z)}>A_u.
\end{aligned}
\tag{S.184}
$$

But (S.175) requires $t<d+A_u(T-s)$, whereas (S.183)–(S.184) require $t>g_\beta(s)>d+A_u(T-s)$. This contradiction proves Theorem 76.2.

Every inversion was of an explicitly positive weight or the positive matrix $\mathcal D$; no inverse of $L$, a leading block or a marginal was used. All squarings compared positive sides, and all denominator clearings used the positive factors displayed above. The proof includes $\beta=1/2$ and applies separately to every arbitrarily small positive $\beta$, with no positive lower cutoff and no claimed uniform positive margin as $\beta\downarrow0$. The endpoint $u=1$ belongs to the polynomial lemma alone. The support dimension can be any fixed finite $k\geq2$; no limiting-rank argument is needed. $\square$

## 80. The original actual-channel bound under every inherited interface

**Definition 80.1 (the retained actual premises).** Let $N:M_3(\mathbb C)\to M_5(\mathbb C)$ be an actual original-real CPTP encoder of Definition 52.1, with actual phase-difference spectrum $(a,\beta,0,-\beta,-a)$ and $0<\beta\leq1/2$. Fix one actual real Kraus compression of minimal rank $r\leq9$, its isometry $V$ and its complement $\Gamma$ as in (S.2). Center support rank $k\leq r$ is a separate variable. The complete actual complementary-domain premises are those of (S.64)–(S.65), or equivalently (R.3)–(R.5) of [the first volume at the fixed published snapshot](https://github.com/the-omega-institute/trureturing/blob/40f9e7b52526d6fab4e139bb95e7bdbdda64f78c/docs/develop/theory/AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#1-the-complete-actual-real-frame-domain):

$$
\begin{gathered}
J_p=\begin{pmatrix}
\tau&0&C\\0&\bar\tau&\bar C\\C^\dagger&C^T&\sigma
\end{pmatrix}\succeq0,\qquad
\tau\succeq0,\quad\operatorname{spec}_{>0}\tau=(a,\beta),\\
\sigma=\bar\sigma=\sigma^T,\qquad
\operatorname{Tr}\tau=\operatorname{Tr}\sigma=1,\qquad\operatorname{Tr}C=0,\\
\operatorname{ran}C\subseteq\operatorname{ran}\tau,\qquad
S_{\rm res}=\sigma-C^\dagger\tau^+C-
\overline{C^\dagger\tau^+C}\succeq0,\qquad
\operatorname{rank}S_{\rm res}\leq1,\qquad\operatorname{rank}J_p\leq5.
\tag{S.185}
\end{gathered}
$$

Here $\tau^+$ acts on its actual support; singular $\tau$ requires the range condition. The bars refer to the fixed original real environment frame. A center-diagonalizing unitary transports every block and the original antiunitary together, as in Definition 52.2. It does not make these blocks jointly entrywise real, commuting, or supported on the same two-dimensional subspace. In particular (S.11) is a mixture of the two transported phase marginals for every complex phase-plane direction; that mixture need not have rank two. Every admissible third column remains present, including its active-output components and the full $C,\bar C,\sigma$ data.

The conditional application assumes, with exactly their stated domains and conventions: the actual phase and supported common-projection interfaces (S.8)–(S.12), (S.55)–(S.60); the rectangular-contraction identity (S.6); the fixed-center compact-affine minimax identity (S.26); the unrestricted CPTP recovery/complement identity (S.7); and the pure-target unhalved-diamond lower interface (S.27). These premises include the actual domination of singular contracted marginals, the full paired-basis transpose, and one common range completion. The standard literature formulas cited below do not by themselves verify these repository-specific actual reductions.

**Theorem 80.2 (conditional all-positive-beta actual consequence).** Under all the premises of Definition 80.1, every such actual $N$, with all admissible third columns and every actual minimal Kraus rank $r\leq9$, satisfies

$$
\begin{gathered}
g_N=\max_{R:M_5\to M_3\ {\rm CPTP}}F(RN,\mathrm{id}_3),
\qquad g_N^2\leq T,\\
\delta_N=\inf_{R:M_5\to M_3\ {\rm CPTP}}
\|RN-\mathrm{id}_3\|_\diamond
\geq1-\sqrt{1-\beta}.
\tag{S.186}
\end{gathered}
$$

The recovery optimization is over all complex CPTP maps on the whole five-dimensional output. The norm is unhalved, with every finite complex reference allowed.

Proof. Keep the actual $V$ fixed. For any center $\omega$ on its actual environment, take its exact support $S$ of rank $k$ and then any one complex rectangular contraction $U:\mathbb C^5\to\mathbb C^3\otimes\mathbb C^k$. Use $A_{\omega,U}$ and $r_\psi$ of (S.5).

For $k=1$, actual domination (S.8) gives $\|x_\psi\|^2\leq a$ for each complex unit $\psi\in\mathcal C$, so $r_\psi\leq\sqrt a<v$. The strict last comparison follows from $T-a=(1-u)(2u+1)/2>0$. No rank-five projection is inserted into the three-dimensional supported target.

For $k\geq2$, $3k\geq6$ and $\operatorname{rank}U\leq5$. Complete its range to one five-dimensional subspace and choose its projection $P$ with $PU=U$. This is a completion after taking the center support, not a compression of a previously chosen larger projection presumed to retain its rank; $P=UU^\dagger$ is not required. Fix $D=I-P$ and its conjugated defect $E=\overline D$. The transpose identities (S.10), (S.12), (S.60) and actual cap domination give the same $M_\psi$ with

$$
r_\psi\leq f(Q_\psi,M_\psi)\leq H_a(M_\psi)
\quad(\psi\in\mathcal C,\ \|\psi\|=1).
$$

For the same $V,\omega,U,P$, the third-input overlap $r_2>v$ would imply $q_2<d$ by (S.21). Hence simultaneous strict inequalities $r_\psi>v$ for every complex phase direction and $r_2>v$ would produce precisely (S.158). Theorem 76.2 excludes it for each $k\geq2$, including the full-support $k=2$ construction. Consequently

$$
\forall\omega\ \forall U:\quad
\min\left\{\min_{\substack{\psi\in\mathcal C\\\|\psi\|=1}}r_\psi,\ r_2\right\}
\leq v.
\tag{S.187}
$$

The center and contraction, then the projection and common $\eta,L$, precede the directional tests. A direction witnessing (S.187) may depend on the center and contraction. This order does not supply a common input witness before $U$, nor exchange a direction-dependent contraction for a common recovery.

For each fixed center, input densities and the complex rectangular-contraction ball are nonempty compact convex sets in finite real coordinates. The pairing $\operatorname{Re}\operatorname{Tr}(\rho A_{\omega,U})$ is continuous and affine in each variable. Apply exactly (S.6) and (S.26), with the center held fixed:

$$
\begin{aligned}
\min_\rho F_\rho(\Gamma,\mathcal C_\omega)
&=\min_\rho\max_U\operatorname{Re}\operatorname{Tr}(\rho A_{\omega,U})\\
&=\max_U\min_\rho\operatorname{Re}\operatorname{Tr}(\rho A_{\omega,U})\\
&=\max_U\lambda_{\min}(\operatorname{Herm}A_{\omega,U})\leq v.
\end{aligned}
\tag{S.188}
$$

The last step uses (S.187): a least eigenvalue is at most that restricted test minimum. Only after this per-center conclusion take the center maximum in (S.7), obtaining $g_N\leq v$. There is no exchange of the center maximum with an input minimum. The Uhlmann contraction and the center rank impose no Kraus-number restriction on the physical recovery.

Finally, for each allowed recovery $R$ and qutrit density $\rho$, choose a purification $|\Psi_\rho\rangle$ and measure the output against its pure identity target. The probability deficit yields trace distance at least $2(1-F_e(\rho,RN))$. This purification supplies a witness inside the original supremum over all finite complex references. The assumed interface (S.27) and the recovery infimum give

$$
\begin{aligned}
\|RN-\mathrm{id}_3\|_\diamond
&\geq2\left(1-\min_\rho F_e(\rho,RN)\right)
=2\left(1-F(RN,\mathrm{id}_3)^2\right),\\
\delta_N&\geq2(1-g_N^2)\geq2(1-T)=1-\sqrt{1-\beta}.
\end{aligned}
\tag{S.189}
$$

This uses a one-sided pure-target lower bound, not an equality between optimized diamond and fidelity objectives. The subset of input tests used in (S.187) restricts neither the recovery class nor the reference supremum. All actual-domain conclusions remain conditional on every interface in Definition 80.1. $\square$

## 81. Bounded literature attribution and transfer conditions

**Definition 81.1 (reused intermediates and the source-specific composition).** The cap maximization and order comparison are reused from (S.57)–(S.63), (S.68)–(S.71); the exact rank-five and positive-weight consumer is (S.90)–(S.91). The new source-specific analytic content is the general-beta branch-complete estimate (S.163), its scalar necessity (S.165), the uniform coefficient inequality (S.168)–(S.174), and their exact ordered spectral overlap (S.175)–(S.184). This is a `repo-derived` composition extending the half-beta exclusion of Sections 64 and 66 to every $0<\beta\leq1/2$ and every fixed finite $k\geq2$. It asserts no new generic fidelity variational theorem, dimension-intersection principle, Ky Fan theorem, compact minimax theorem or Bernstein representation theorem.

The following primary-source attributions are `literature-attested` only within their stated versions, formula conventions and hypotheses. They identify reused interfaces or alternative methods; no alternative row supplies a missing actual-class implication.

| Primary source and exact locator | Formula conditions and transfer boundary |
| --- | --- |
| Watrous, *The Theory of Quantum Information*, Chapter 3 PDF, Theorem 3.19, (3.115), printed p. 148, [chapter](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf); PDF SHA256 `e91c1a2112676c0f0f6070f97a35099d5e6f392c5d971f7f9054b38c6dd6fe46`. | For arbitrary finite-dimensional PSD operands, root fidelity is the infimum of $[\operatorname{Tr}(QX)+\operatorname{Tr}(MX^{-1})]/2$ over $X\succ0$. Every such weight gives (S.161); operands may be singular. Only $X$ is inverted. |
| Bény–Oreshkov, *Approximate simulation of quantum channels*, [arXiv:1103.0649v3](https://arxiv.org/html/1103.0649v3), (54)–(56), Corollary 5, (64)–(66); fixed-input (132)–(133). | The fidelity is root fidelity minimized over purified inputs, rectangular contractions allow unequal purification spaces, and Corollary 5 is unrestricted CPTP. Its (65)–(66) complete trace-nonincreasing maps without decreasing fidelity; the Kraus-bounded Theorem 3 alone is insufficient. For target $\mathrm{id}_3$, the scalar-trace complement has postprocessings exactly the constant environment densities. The fixed-input identity is a distinct interface and is not substituted for (S.7). |
| Braunstein–Pati, *Quantum information cannot be completely hidden in correlations: implications for the black-hole information paradox*, [arXiv:gr-qc/0603046v1](https://arxiv.org/html/gr-qc/0603046v1), (2)–(4), (6)–(9). | The exact no-hiding construction has $Kd$ orthogonal complementary vectors. An exactly reversible qutrit with a fixed rank-two environment marginal therefore needs six output dimensions. The approximate premise is reference-inclusive decoupling; the sharp weighted five-dimensional obstruction does not follow from that statement alone. |
| Ng–Mandayam, *A simple approach to approximate quantum error correction based on the transpose channel*, [arXiv:0909.0931v2](https://arxiv.org/html/0909.0931v2), Theorem 3 and Corollary 4, (8)–(10). | The comparison is dimension dependent and concerns optimal worst-case pure-code-state squared fidelity and transpose recovery. A sharp transfer here needs a quantitative transpose-loss estimate and a bridge to the reference-entangled worst-case convention. Neither is inferred from the comparison. |
| Mandayam–Ng, *Towards a Unified Framework for Approximate Quantum Error Correction*, [arXiv:1202.5139v2](https://arxiv.org/html/1202.5139v2), Section II, (1)–(2), Theorem 2, (12)–(14). | A subsystem subspace $\mathcal H_A\otimes\mathcal H_B$ is already specified, and the theorem gives sufficient perturbative recovery conditions. A protected dimension-three factor and dimension-two gauge factor require six dimensions exactly; applying an approximate version inside dimension five needs a quantitative approximate-embedding argument and a converse. |
| Renes, *Better bounds on optimal measurement and entanglement recovery, with applications to uncertainty and monogamy relations*, [arXiv:1707.01114v1](https://arxiv.org/html/1707.01114v1), Proposition 1, (9), and (13); Zheng–He–Lee–Jiang, *The Near-optimal Performance of Quantum Error Correction Codes*, [arXiv:2401.02022v2](https://arxiv.org/html/2401.02022v2), Theorem 1, (4)–(5). | Renes uses normalized $\sigma_B$ and Rényi parameter at least $1/2$ in (9), with squared maximally-entangled-target recovery fidelity. The second source gives $\widetilde F=d_L^{-2}\|\operatorname{Tr}_L\sqrt M\|_F^2$ and $(1-\widetilde F)/2\leq1-F_{\rm opt}\leq1-\widetilde F$ for maximally-mixed-input entanglement fidelity. These fixed-state methods require an additional inequality on the full actual QEC matrix retaining $C,\bar C,\sigma$ and rank five before a sharp application here. |
| Wu–Grossi–Kürkçüoğlu–Zorzetti, *Universal Optimization and Tighter Fidelity Bounds for Approximate Quantum Error Correction*, [arXiv:2607.24968v2](https://arxiv.org/html/2607.24968v2), Theorem 1, (6), Corollary 2, (8). | Theorem 1 is an exact dual representation for optimal maximally-mixed-input entanglement fidelity. Corollary 2 requires $\langle i|E_k^\dagger E_l|j\rangle=0$ for every distinct logical $i,j$ and all Kraus indices $k,l$. The actual class permits nonzero third-column blocks $C,\bar C$, so that corollary has no automatic all-class application. |
| Elimelech–Albert–Barg, *Universal recovery in approximate quantum error correction*, [arXiv:2608.28962v2](https://arxiv.org/html/2608.28962v2), Definition 2 and Theorem 4. | The family is controlled by a specified error set: Kraus expansions $A_m=\sum_k c_{mk}E_k$ have coefficient-matrix operator norm at most one. A common recovery guarantee for that family requires this control hypothesis. A converse from its leakage functional to the present five-output defect is an additional obligation. |

Authentication of a standard formula or a bounded locator does not prove the repository-specific phase, support, transpose, domination or common-implementation premises in Definition 80.1. The listed attributions do not constitute an exhaustive literature survey or an independent proof of the alternative theorems and imply no global novelty claim. No new authentication of those primary sources is asserted by this exposition.

## 82. Scope of the extension and the separate witness programmes

**Definition 82.1 (consequences and remaining distinctions).** Theorem 76.2 supplies the all-center general-beta common-projection exclusion left unspecified in Section 67. Theorem 80.2 extends the conditional half-beta actual consequence of Theorem 66.2 over the full original positive-beta interval, under the explicitly retained interfaces. The scalar-only and specified matrix-extension obstructions of Sections 55–56 retain their exact scope: the present contradiction uses the full common-vector inequality as well as the spectral budget and does not assert an all-center standalone certificate (S.14).

The normalized $Z_i$ equations reconstruct projection geometry only. This proof constructs neither an actual encoder from arbitrary relaxed data nor a common attaining family of directionwise maximizing marginals. It imposes no extra normal form, reality or commutativity on actual third columns, no bound on recovery Kraus number, no restriction of complex directions or references, and no center/input quantifier exchange. Rank-one actual centers are covered separately; center support rank two is covered in its own full six-dimensional supported geometry; every higher finite positive support is included without a tail-rank restriction.

Sections 68–75 and their fixed-input sufficient routes (S.154)–(S.155) retain their stated mathematical boundaries. The all-beta projection contradiction does not construct a fixed-$\rho_\star$ dual $Y_N$, a density $\rho_N$ and dual meeting (S.155) for every encoder, or the separate $\sqrt a<\lambda<1$ constructive witness bridge. Uniform feasibility of those routes remains unproved here. In particular the per-center, per-contraction directional witness of (S.187) cannot be promoted to an input chosen before every recovery. A diamond lower bound alone does not establish either stronger sufficient witness programme or converse lifting.

The actual conclusion is exactly the unchanged original-domain lower target: all original-real CPTP $M_3(\mathbb C)\to M_5(\mathbb C)$ with the stated spectrum, every $0<\beta\leq1/2$, all admissible third columns, actual minimal Kraus rank at most nine, all complex whole-output CPTP recoveries, all finite complex references, and the unhalved diamond norm, conditional on Definition 80.1. The analytic projection theorem has the larger finite-center-rank scope stated in Theorem 76.2. Neither result asserts a new matching construction, physical realization, kernel verification, exhaustive novelty or completion of the continuing research programme.

## 追加锚（本行以下为增补区）

## 83. Conditional closure of the encoder-dependent witness route

**Definition 83.1 (the scalar premise and inherited scope).** Keep the actual original-real channel class, the phase spectrum, all admissible third columns, and every complex whole-output CPTP recovery from Definition 80.1. For a fixed actual channel $N$, write

$$
T_\beta=\frac{1+\sqrt{1-\beta}}2,
\qquad
p_N(\rho)=\max_{R\ {\rm CPTP}}F_e(\rho,RN),
\qquad
h_N(\rho)=p_N(\rho).
\tag{S.190}
$$

The existing fixed-input and channel minimax interfaces identify

$$
 g_N^2=\min_{\rho\in\mathsf D(\mathbb C^3)}h_N(\rho),
\qquad
 h_N(\rho)=
 \min_{Y=Y^\dagger}
 \left\{\operatorname{Tr}Y:
 I_3\otimes Y\succeq C_{\rho,N}\right\},
\tag{S.191}
$$

with both minima attained, including singular input densities and singular dual optima. Equation (S.191) is the previously established result of Sections 7 and 53 transported in the conventions of (S.153); it is not a new minimax theorem here.

**Proposition 83.2 (conditional S.155 certificate).** Under the inherited interfaces of Definition 80.1, suppose for one fixed actual $N$ that

$$
 g_N^2\leq T_\beta.
\tag{S.192}
$$

Then there are a density $\rho_N$ and a Hermitian positive semidefinite $Y_N$ such that

$$
 C_{\rho_N,N}\preceq I_3\otimes Y_N,
\qquad
 \operatorname{Tr}Y_N=g_N^2\leq T_\beta.
\tag{S.193}
$$

If the channel and its Kraus frame are real in the original frame, the pair may be chosen with $\rho_N=\overline{\rho_N}=\rho_N^T$ and $Y_N=\overline{Y_N}=Y_N^T$. The selected pair is fixed before the recovery is chosen and therefore constrains every complex CPTP recovery on the whole five-dimensional output.

Proof. Choose an attaining minimizer $\rho_N$ in the first equality of (S.191), then choose an attaining dual minimizer $Y_N$ in the second equality. This gives (S.193) and (S.192). For original-real data, simultaneous conjugation sends $(\rho,Y)$ to $(\bar\rho,\bar Y)$ and preserves feasibility and trace. The convexity of the squared fixed-input fidelity in the input density gives the standard conjugation average without restricting the recovery set; hence the minimizing pair can be taken real symmetric. This is exactly the previously established real-pair interface, applied at the selected $N$.

For any complex recovery $R$, weak duality in the fixed-input SDP gives

$$
F_e(\rho_N,RN)\leq\operatorname{Tr}Y_N=g_N^2.
\tag{S.194}
$$

Purify $\rho_N$ in a finite complex reference and apply the pure-target trace-distance inequality. Taking the infimum over all recoveries gives

$$
\delta_N
\geq2(1-g_N^2)
\geq2(1-T_\beta)
=1-\sqrt{1-\beta}.
\tag{S.195}
$$

This is a one-sided unhalved diamond lower bound. It does not identify the diamond optimum with a fidelity optimum. $\square$

**Corollary 83.3 (what the all-beta projection theorem supplies).** Theorem 80.2 supplies (S.192), still under every actual phase, support, projection, rectangular-contraction, fixed-center minimax, unrestricted recovery/complement, and pure-target interface listed in Definition 80.1. Consequently, within exactly those inherited premises, Proposition 83.2 conditionally closes the encoder-dependent existential route (S.155) for every $0<\beta\leq1/2$ and every admissible third column.

The quantifiers are

$$
\forall N\quad
\bigl[\text{Definition 80.1 premises}\ \wedge\ g_N^2\leq T_\beta\bigr]
\Longrightarrow
\exists(\rho_N,Y_N)\quad
\forall R.
\tag{S.196}
$$

The witness depends on $N$ and is selected before $R$. The direction-dependent witnesses in (S.187) are not reused as a common input, and no exchange of the center maximum with an input minimum is made.

The earlier Section 74 sentence that recorded (S.155) as unproved described the proof boundary before this conditional composition. It remains correct for an unconditional proof of (S.155) over arbitrary actual channels: that proof still requires the scalar premise and all Definition 80.1 interfaces. The composition here does not close the fixed-input route (S.154), because $\rho_N$ need not equal $\rho_\star$.

**Proposition 83.4 (support boundary for the selected dual).** For any fixed density $\rho$ and any trace-optimal dual $Y$ in (S.191), including singular cases,

$$
\operatorname{ran}Y
=\operatorname{ran}\!\left(\mathcal N(\rho^2)^T\right)
=\operatorname{ran}\!\left(\mathcal N(\rho)^T\right).
\tag{S.197}
$$

Consequently,

$$
\operatorname{rank}Y
=\dim\operatorname{span}_\alpha K_\alpha\operatorname{ran}\rho.
\tag{S.198}
$$

Proof. The row-vectorization convention gives

$$
\operatorname{Tr}_3 C_{\rho,N}=\mathcal N(\rho^2)^T=:B.
\tag{S.199}
$$

Every feasible dual satisfies $3Y\succeq B$. Let $\Pi$ be the support projection of $B$. Positivity of $C_{\rho,N}$ and the vanishing partial trace on $\ker B$ imply $C_{\rho,N}=(I_3\otimes\Pi)C_{\rho,N}(I_3\otimes\Pi)$. Compressing $Y$ to $\Pi$ preserves feasibility and cannot increase its trace. At optimum, positivity removes the exterior and cross blocks, so $\operatorname{ran}Y=\operatorname{ran}B$. Since $\rho$ and $\rho^2$ have the same support, $\mathcal N(\rho)$ and $\mathcal N(\rho^2)$ have the same output support, proving (S.197)–(S.198). $\square$

**Definition 83.5 (the strict-positive dual boundary).** Let $u=h_N(\rho)$. A positive-definite dual with trace at most $T_\beta$ exists exactly when

$$
 u<T_\beta
 \quad\text{or}\quad
 \bigl[u=T_\beta\ \text{and}\ \mathcal N(\rho)\succ0\bigr].
\tag{S.200}
$$

A strict trace gap permits adding a sufficiently small positive multiple of $I_5$ to an optimal dual. At equality, (S.197) prevents such a perturbation when the channel output has deficient support. Therefore (S.200) is a boundary condition for an SPD version of a fixed-input certificate, not a proof of (S.154). In particular, for $\rho_\star=\operatorname{diag}(1/4,1/4,1/2)$, the missing requirement remains the actual estimate $h_N(\rho_\star)\leq T_\beta$, together with the full-output support condition at equality.

**Definition 83.6 (scope and remaining gap).** Proposition 83.2 and Corollary 83.3 are a conditional reuse composition, not a new generic minimax, SDP, or real-symmetry theorem. They do not construct an explicit closed formula for $(\rho_N,Y_N)$, prove S.154, justify code/third pinching, provide a relaxed-data-to-actual converse, or establish a fidelity–diamond equality. The original all-class target remains conditional on Definition 80.1, and the fixed-$\rho_\star$ and $\sqrt a<\lambda<1$ witness programmes remain open.

## 追加锚（本行以下为增补区）

## 84. Reading the retained S.155 boundary with the conditional composition

**Definition 84.1 (scope reconciliation).** The sentence in Section 82 that leaves S.155 unproved is retained as the status of an unconditional, premise-free all-class proof and of any proof that does not establish the scalar premise. Sections 83.2–83.3 add a different statement: after Definition 80.1 is assumed and Theorem 80.2 supplies $g_N^2\leq T_\beta$, the already established attained minimax and fixed-input SDP yield the encoder-dependent pair $(\rho_N,Y_N)$. Thus the current boundary is

$$
\text{unconditional S.155 over the raw actual class: open},
\qquad
\text{S.155 under Definition 80.1 and Theorem 80.2: conditional consequence}.
\tag{S.201}
$$

This reconciliation does not promote the conditional statement to S.154, does not remove any inherited premise, and does not turn the direction-dependent projection witness into a common input. $\square$

## 追加锚（本行以下为增补区）

## 85. The three-environment family and one common auxiliary density

**Definition 85.1 (fixed physical input and the complete third-column sphere).** Specialize (S.147) to $a=\beta=1/2$ and three environment coordinates $e_0,e_1,e_2$. In the original real output frame $(b_1,g_1,b_2,g_2,h)$ put $T=\mathsf T$ and

$$
\begin{gathered}
E_0=\frac1{\sqrt2}[b_1,b_2,0],\qquad
E_1=\frac1{\sqrt2}[g_1,g_2,0],\\
\mathcal L=\{T\in\mathbb R^{5\times3}:
\langle E_0,T\rangle_F=\langle E_1,T\rangle_F=0\},\qquad
\mathcal T=\{T\in\mathcal L:\|T\|_F=1\},\\
\mathcal T_3=\{T\in\mathcal T:T e_2\ne0\},\qquad
\mathcal T_\partial=\{T\in\mathcal T:T e_2=0\},\\
\rho_\star=\operatorname{diag}(1/4,1/4,1/2),\qquad
c=\frac{1+1/\sqrt2}{2},\qquad r=\sqrt c=\cos(\pi/8).
\end{gathered}
\tag{S.202}
$$

Here $\langle A,B\rangle_F=\operatorname{Tr}(A^TB)$ on real matrices. The two $E_i$ are Frobenius orthonormal. For an arbitrary complex auxiliary density $X\in\mathsf D(\mathbb C^3)$ define

$$
\begin{gathered}
\mathcal K_T(X)=
[E_0\sqrt X/4\mid E_1\sqrt X/4\mid T\sqrt X/2],\qquad
f_T(X)=\|\mathcal K_T(X)\|_*,\\
\Phi_T(X)=\frac1{16}(E_0XE_0^T+E_1XE_1^T)+\frac14TXT^T,\qquad
f_T(X)=\operatorname{Tr}\sqrt{\Phi_T(X)},\\
v_T=\max_{X\in\mathsf D(\mathbb C^3)}f_T(X),\qquad
V_{\rm all}=\max_{T\in\mathcal T}v_T^2,\qquad
V_\partial=\max_{T\in\mathcal T_\partial}v_T^2.
\end{gathered}
\tag{S.203}
$$

The nuclear norm is denoted by $\|\cdot\|_*$. The density $X$ acts on the environment and is independent of the fixed physical input $\rho_\star$. The family is the three-environment part of the real $\lambda=1$, half-beta branch of (S.147); it is not a parameterization of all other branches of Definition 52.1. The family-specific reductions and comparisons below are repo-derived; their cited norm, fidelity and quadratic-alternative results are literature-attested intermediate steps.

**Proposition 85.2 (actual channel and exact Kraus-rank condition).** For every $T=[t_0,t_1,t_2]\in\mathcal T$, the actual matrices

$$
K_\alpha=[(E_0)_\alpha,(E_1)_\alpha,t_\alpha],
\qquad \alpha=0,1,2,
\tag{S.204}
$$

define a real-Kraus CPTP encoder $N_T:M_3(\mathbb C)\to M_5(\mathbb C)$ with phase-difference spectrum $(1/2,1/2,0,-1/2,-1/2)$. Its minimal Kraus rank is three exactly for $T\in\mathcal T_3$, and is two on $\mathcal T_\partial$.

Proof. The diagonal of $\sum_\alpha K_\alpha^TK_\alpha$ is $(1,1,\|T\|_F^2)=(1,1,1)$. The $01$ entry vanishes by orthogonality of the $b$ and $g$ directions. Its $02$ and $12$ entries are precisely $\langle E_0,T\rangle_F$ and $\langle E_1,T\rangle_F$. Thus its sum is $I_3$, and the Kraus formula gives complete positivity on complex matrices. These are exactly the sufficient conditions (R.8)–(R.9) of the first volume, with both coefficient rows real.

For $f_j^\pm=(b_j\pm ig_j)/\sqrt2$, the phase outputs are $\frac12\sum_{j=1}^2|f_j^\pm\rangle\langle f_j^\pm|$. Their supports are orthogonal, so their difference has the stated spectrum, independently of $T$. In a complex linear relation $\sum_\alpha z_\alpha K_\alpha=0$, the first physical column is $(z_0b_1+z_1b_2)/\sqrt2$. Consequently $z_0=z_1=0$. The remaining relation is $z_2t_2=0$. Thus the vectorized Kraus matrices are independent exactly when $t_2\ne0$; otherwise $K_2=0$ and the other two remain independent. Choi rank equals minimal Kraus number. Matrix rank of the $5\times3$ matrix $T$ is a different quantity and need not be three. $\square$

**Proposition 85.3 (common-density recovery normalization and the real factor formula).** For this family the unrestricted fixed-input recovery value and the squared real dual formula are

$$
\max_{R:M_5\to M_3\ {\rm CPTP}}F_e(\rho_\star,RN_T)=v_T^2
=\max_{\substack{Q_i\in\mathbb R^{5\times3}\\
\sum_{i=0}^2Q_iQ_i^T\preceq I_5}}
\left\|\frac{E_0^TQ_0+E_1^TQ_1}{4}
+\frac{T^TQ_2}{2}\right\|_F^2.
\tag{S.205}
$$

The auxiliary maximization in (S.203) can be attained by a real symmetric density, including real offdiagonal entries.

Proof. Purify $\rho_\star$ in input-first reference coordinates and apply the actual isometry of (S.2). With $p=(1/4,1/4,1/2)$, its reference-environment marginal is

$$
L=[E_0/2\mid E_1/2\mid T/\sqrt2],\qquad
\sigma_{RE}=L^TL,\qquad
f(\sigma_{RE},\rho_\star\otimes X)
=\|L(\sqrt{\rho_\star}\otimes\sqrt X)\|_*
=f_T(X).
\tag{S.206}
$$

Indeed the $(i\alpha,j\gamma)$ Gram entry is
$\sqrt{p_ip_j}\sum_b(E_i)_{b\alpha}(E_j)_{b\gamma}$, with $E_2=T$ in this sentence. For complex $X$, the positive sandwich of $L^TL$ by $\sqrt{\rho_\star}\otimes\sqrt X$ is still the right Gram matrix of the displayed rectangular product. Its square-root trace is therefore the fidelity. No inverse or full-support condition is used. The second physical square-root factor gives the coefficients $p_i$ in $\mathcal K_T$, rather than $\sqrt{p_i}$.

Apply [Bény–Oreshkov, arXiv:1103.0649v3, Section IV, (133)](../../../Library/QuantumChannels/beny2011simulation.md) to the fixed physical input and identity target. The identity complement is the scalar trace, and a CPTP map from that scalar output prepares an arbitrary density $X$. Equation (133), with the CPTP completion of Corollary 5, gives $\max_R\sqrt{F_e(\rho_\star,RN_T)}=\max_X f_T(X)$. Their $F_\rho$ is root fidelity, the square root of Schumacher entanglement fidelity at the identity target. Equation (132) alone has a Kraus-number restriction and is not the unrestricted interface used here. The worst-case-input theorem of arXiv:0907.5391v4 is a different optimization and is not substituted for this fixed-input identity.

For real $T$, $\Phi_T(\bar X)=\overline{\Phi_T(X)}$. Concavity of the trace square root and invariance under conjugation give
$f_T((X+\bar X)/2)\geq f_T(X)$. The average is a real symmetric PSD trace-one matrix; it need not be diagonal. This argument concerns an objective symmetry, not a physical operation taking real parts.

For a real density replace $\sqrt X$ by any real $Z\in\mathbb R^{3\times3}$ with $ZZ^T=X$. The horizontal matrices formed with $Z$ and with $\sqrt X$ have the same left Gram matrix $\Phi_T(X)$ and hence the same nuclear norm. Conversely every real $Z$ with $\|Z\|_F=1$ determines such an $X$. Real rectangular nuclear/operator duality, followed by Frobenius self-duality, now gives

$$
\begin{aligned}
v_T
&=\max_Q\max_{\|Z\|_F=1}
\left\langle
\frac{E_0^TQ_0+E_1^TQ_1}{4}+\frac{T^TQ_2}{2},Z
\right\rangle_F\\
&=\max_Q\left\|
\frac{E_0^TQ_0+E_1^TQ_1}{4}+\frac{T^TQ_2}{2}
\right\|_F,\qquad
Q=[Q_0\mid Q_1\mid Q_2],\quad QQ^T\preceq I_5.
\end{aligned}
\tag{S.207}
$$

The pairing follows from $\langle Q_i,E_iZ\rangle_F=\langle E_i^TQ_i,Z\rangle_F$. These are maxima over independent compact sets, so their order can be interchanged; no minimax exchange is required. Squaring proves (S.205). The norm identities are established intermediates in [Watrous, arXiv:1207.5726v2, Section 1](../../../Library/QuantumChannels/watrous2012simpler.md). They do not provide the numerical bound $c$. $\square$

## 86. Joint boundary equivalence and legal rank-three lifting

**Proposition 86.1 (the optimized full sphere equals the two-column boundary).** With every third-column component retained in (S.202),

$$
V_{\rm all}\leq\max\{3/4,V_\partial\},
\qquad V_\partial\geq c>3/4,\qquad
V_{\rm all}=V_\partial.
\tag{S.208}
$$

Proof. Fix one feasible common $Q$ in (S.205), and put

$$
C=\frac{E_0^TQ_0+E_1^TQ_1}{4},\qquad B=Q_2,\qquad
A=\|C\|_F^2.
\tag{S.209}
$$

Here $C$ is $3\times3$ and its last row is zero. The first two rows are
$(b_j^TQ_0+g_j^TQ_1)/(4\sqrt2)$. Consequently

$$
A\leq\frac1{16}\sum_{j=1}^2
\bigl(\|b_j^TQ_0\|^2+\|g_j^TQ_1\|^2\bigr)
\leq\frac14.
\tag{S.210}
$$

The last inequality uses each of the four unit-vector tests of
$\sum_iQ_iQ_i^T\preceq I_5$; the same $Q$ is used throughout. In particular $\|B\|_{\rm op}\leq1$.

Write $s=\|[t_0,t_1]\|_F$. For $0<s<1$ set
$T=[sS,\sqrt{1-s^2}\,w]$, where $S\in\mathbb R^{5\times2}$ and $w\in\mathbb R^5$ have unit Frobenius and Euclidean norm respectively. The two overlaps of $[S,0]$ with $E_i$ vanish because the last columns of $E_i$ are zero. If $C_{\rm top}$ is the first two rows of $C$, the entire objective is

$$
\begin{aligned}
\|C+T^TB/2\|_F^2&=A+bs^2+Ds+e(1-s^2),\\
b&=\frac14\|S^TB\|_F^2,\qquad
e=\frac14\|w^TB\|^2,\qquad
D=\langle C_{\rm top},S^TB\rangle_F,\qquad
0\leq b,e\leq\frac14.
\end{aligned}
\tag{S.211}
$$

The last row of $T^TB$ is separate from its first two rows, so there is no missing mixed $S,w$ term. All active-output and outside-output parts of $w$ occur in $e$.

For an upper bound replace $D$ by $|D|$. At $s=1$, the value $A+b+|D|$ is realized by this same $Q$ and either $[S,0]$ or $[-S,0]$. It is therefore at most $V_\partial$. The $s=0$ endpoint is $A+e\leq1/2$. If $b\geq e$, the polynomial in (S.211) with $|D|$ is convex and is bounded by these endpoints. If $u=e-b>0$, it becomes $A+e+|D|s-us^2$. For $|D|\geq2u$ it is increasing on $[0,1]$ and is again bounded by the $s=1$ endpoint. For $|D|<2u$, its vertex value satisfies

$$
A+e+\frac{|D|^2}{4u}
\leq A+e+u=A+2e-b\leq\frac34.
\tag{S.212}
$$

When $s=0$, the original $T=[0,0,w]$ already gives $A+e\leq1/2$, without normalizing a zero two-column block. When $s=1$, $T$ is already on the boundary and no $w$ is needed. This proves the first inequality of (S.208).

For the lower comparison use the familiar endpoint $T_0=[h,0,0]$ and the single feasible triple

$$
Q_0=[b_1,b_2,0],\qquad Q_1=[g_1,g_2,0],\qquad
Q_2=[h,0,0],\qquad \sum_iQ_iQ_i^T=I_5.
\tag{S.213}
$$

Here $C=\operatorname{diag}(1/(2\sqrt2),1/(2\sqrt2),0)$ and
$T_0^TQ_2/2=\operatorname{diag}(1/2,0,0)$. Their squared Frobenius norm is
$(1/2+1/(2\sqrt2))^2+1/8=c$. Thus $V_\partial\geq c>3/4$; the first inequality and $V_\partial\leq V_{\rm all}$ yield equality. The endpoint channel is the existing one identified in Definition 56.5 of the first volume. Its trial value here finishes the optimized comparison; it does not give an upper bound for all boundary matrices.

The sign comparison and the choices of maximizing factor and $Q$ occur after joint optimization. They imply no pointwise inequality obtained by deleting a nonzero third environment column at a fixed $T,X$. $\square$

**Proposition 86.2 (uniform continuity, the exact legal supremum and strict lifting).** For all complex auxiliary densities and every pair of real $5\times3$ matrices,

$$
|f_T(X)-f_{T'}(X)|\leq\frac12\|T-T'\|_F.
\tag{S.214}
$$

For $T_0\in\mathcal T_\partial$ and $\varepsilon>0$, the perturbations

$$
T_\varepsilon=\frac{T_0+\varepsilon h e_2^T}{\sqrt{1+\varepsilon^2}}
\in\mathcal T_3,\qquad
\|T_\varepsilon-T_0\|_F^2
=2-\frac2{\sqrt{1+\varepsilon^2}}
\tag{S.215}
$$

give

$$
\sup_{T\in\mathcal T_3}v_T^2=V_{\rm all}=V_\partial.
\tag{S.216}
$$

A strict boundary violation $f_{T_0}(X)^2>c$ lifts to a strict violation in the actual minimal-Kraus-rank-three family at that same complex $X$.

Proof. The reverse triangle inequality, invariance of the nuclear norm under zero padding, and Schatten Hölder with exponents $2,2,1$ give

$$
|f_T(X)-f_{T'}(X)|
\leq\frac12\|(T-T')\sqrt X\|_*
\leq\frac12\|T-T'\|_F\|\sqrt X\|_F
=\frac12\|T-T'\|_F.
\tag{S.217}
$$

This estimate needs no reality, diagonality or support restriction on $X$. It also bounds $|v_T-v_{T'}|$ by the same quantity.

The added column $h e_2^T$ is Frobenius orthogonal to $T_0$, since the latter has zero third environment column. It has norm one and is orthogonal to both $E_i$. Thus (S.215) preserves both overlaps and unit norm and has nonzero third column. Proposition 85.2 supplies actual TP, the phase spectrum and minimal Kraus rank three. The stated distance follows by expanding the squared norm. Every point excluded from $\mathcal T_3$ has this approximation, so $\mathcal T_3$ is dense in the compact sphere $\mathcal T$. Continuity proves (S.216); a supremum on the nonclosed rank-three subset is not asserted to be attained. For a strict violation set $\delta=f_{T_0}(X)-r>0$ and choose $\varepsilon$ with $\|T_\varepsilon-T_0\|_F<2\delta$. Equation (S.214) preserves the strict root gap and hence the squared gap. $\square$

## 87. The exact common-block quadratic certificate on the boundary

**Proposition 87.1 (auxiliary support and the eight-dimensional boundary space).** On $\mathcal T_\partial$ the maximizing auxiliary density may be supported on the first two environment coordinates, with its full real symmetric $2\times2$ block retained. Let $\widehat E_i\in\mathbb R^{5\times2}$ be the first two columns of $E_i$ and define

$$
\begin{gathered}
\mathcal L_2=\{S\in\mathbb R^{5\times2}:
\langle\widehat E_0,S\rangle_F
=\langle\widehat E_1,S\rangle_F=0\},\qquad \dim\mathcal L_2=8,\\
V_\partial=
\max_{\substack{S\in\mathcal L_2,\ \|S\|_F=1\\
Q_i\in\mathbb R^{5\times2},\ \sum_iQ_iQ_i^T\preceq I_5}}
\left\|\frac{\widehat E_0^TQ_0+\widehat E_1^TQ_1}{4}
+\frac{S^TQ_2}{2}\right\|_F^2.
\end{gathered}
\tag{S.218}
$$

Proof. Put $P_E=\operatorname{diag}(1,1,0)$ in the auxiliary environment. Each of $E_0,E_1,T$ annihilates $I-P_E$, so $\Phi_T(X)=\Phi_T(P_EXP_E)$. If $t=\operatorname{Tr}(P_EX)$ is zero, this objective is zero. If $t>0$, homogeneity gives
$f_T(X)=\sqrt t\,f_T(P_EXP_E/t)\leq f_T(P_EXP_E/t)$, since $t\leq1$. This proves the support restriction for the maximum, including singular $X$. Conjugation averaging then gives a real maximizing block, with no removal of its offdiagonals. Applying exactly the real-factor argument of Proposition 85.3 in dimension two gives (S.218). The two $\widehat E_i$ remain orthonormal in a ten-dimensional Frobenius space, so their common orthogonal complement has dimension eight. $\square$

**Definition 87.2 (one feasible triple and its quadratic).** Fix one common feasible triple $Q_i\in\mathbb R^{5\times2}$ in (S.218). Write $\Pi_2$ for the orthogonal projection onto $\mathcal L_2$ and put

$$
\begin{gathered}
C=\frac{\widehat E_0^TQ_0+\widehat E_1^TQ_1}{4}
\in\mathbb R^{2\times2},\quad B=Q_2,\quad A=\|C\|_F^2,\\
d=\Pi_2(BC^T)\in\mathcal L_2,\qquad
H(S)=\frac14\Pi_2(BB^TS)\quad(S\in\mathcal L_2),\\
g_Q(S)=A+\langle d,S\rangle_F+\langle S,H(S)\rangle_F
=\|C+S^TB/2\|_F^2.
\end{gathered}
\tag{S.219}
$$

**Proposition 87.3 (exact S-lemma certificate, including singular multipliers).** The operator $H$ is self-adjoint on $\mathcal L_2$ and $0\preceq H\preceq I_{\mathcal L_2}/4$. For each fixed common $Q$, the following three conditions are equivalent:

$$
\begin{gathered}
g_Q(S)\leq c\quad\text{for every }\|S\|_F=1,\\
g_Q(S)\leq c\quad\text{for every }\|S\|_F\leq1,\\
\exists\lambda\geq0:\quad
\begin{pmatrix}
\lambda I_{\mathcal L_2}-H&-d/2\\
-d^T/2&c-A-\lambda
\end{pmatrix}\succeq0.
\end{gathered}
\tag{S.220}
$$

The block matrix is $9\times9$ in any orthonormal basis of $\mathcal L_2$. Its singular-safe form, with $W=\lambda I_{\mathcal L_2}-H$, is

$$
W\succeq0,\qquad d\in\operatorname{ran}W,\qquad
c-A-\lambda\geq\frac14\langle d,W^+d\rangle_F.
\tag{S.221}
$$

Proof. For $S,S'\in\mathcal L_2$, the projection disappears when paired with $S'$, and
$\langle S',H(S)\rangle_F=\langle B^TS',B^TS\rangle_F/4$.
This proves self-adjointness, positivity and the upper bound because $\|B\|_{\rm op}\leq1$. Expanding the square in (S.219) proves its last identity, since
$\langle C,S^TB\rangle_F=\langle BC^T,S\rangle_F$ and
$\|S^TB\|_F^2=\langle S,BB^TS\rangle_F$.

The function $g_Q$ is convex. Every interior point of the unit ball is a convex combination of two antipodal unit vectors: for $S=tU$ with $0\leq t<1$, take weights $(1+t)/2,(1-t)/2$ on $U,-U$, choosing any unit $U$ when $S=0$. Thus the sphere bound is equivalent to the ball bound.

Apply the one-constraint S-lemma in [Boyd–Vandenberghe, Appendix B.2, p. 655, (B.6)–(B.7)](../../../Library/QuadraticForms/boydvandenberghe2004convex.md) to
$\|S\|_F^2-1\leq0$ implying
$\langle S,HS\rangle_F+\langle d,S\rangle_F+A-c\leq0$.
The ball has the strictly feasible point $S=0$. The lemma gives exactly a $\lambda\geq0$ such that
$c-g_Q(S)-\lambda(1-\|S\|_F^2)$ is nonnegative on the entire eight-dimensional space. Its coefficient matrix is the last matrix in (S.220). Conversely that PSD matrix gives the ball bound directly. This is an application of the established S-lemma to this common triple, not a proof of its uniform feasibility.

For completeness, PSD of that matrix forces $W\succeq0$. A nonzero component of $d$ in $\ker W$ would give a negative quadratic value by varying the corresponding top coordinate with bottom coordinate one. Hence $d\perp\ker W=\operatorname{ran}(W)^\perp$. Under this range condition the quadratic form on $(S,t)$ completes to

$$
\left\langle S-\frac t2W^+d,\,
W\left(S-\frac t2W^+d\right)\right\rangle_F
+t^2\left(c-A-\lambda-\frac14\langle d,W^+d\rangle_F\right).
\tag{S.222}
$$

This proves (S.221) in both directions without requiring $W$ to be invertible. Neither the S-lemma nor the range condition supplies a multiplier for every feasible common $Q$; that uniform assertion is the remaining numerical inequality. $\square$

## 88. Exact common-isometry elimination with one outside-output column

**Definition 88.1 (the contraction variables).** In this section only, reorder the same output basis as $(b_1,b_2,g_1,g_2,h)$. Let $J:\mathbb R^2\to\mathbb R^3$ include the first two environment coordinates. For a real symmetric density $X$ and a real $M=[M_0\ M_1]\in\mathbb R^{3\times4}$ define

$$
\begin{gathered}
S=\sqrt X,\quad R=J^TXJ,\quad
A=\tfrac12\operatorname{diag}(R,R)\in\mathbb R^{4\times4},\\
M_i\in\mathbb R^{3\times2},\quad MM^T\preceq I_3,\quad
H=I_3-MM^T,\quad
\eta_i=\frac1{\sqrt2}\operatorname{Tr}(J^TSM_i),\\
\ell(X,M)=\operatorname{Tr}
\sqrt{\sqrt A(I_4-M^TM)\sqrt A},\\
q(X,M)=\operatorname{Tr}(XMM^T)
+\lambda_{\max}(\sqrt H X\sqrt H)-\eta_0^2-\eta_1^2,\\
\Theta(X,M)=\frac{\ell(X,M)}4+\frac{\sqrt{q(X,M)}}2.
\end{gathered}
\tag{S.223}
$$

The letters $S,A,H$ here have the displayed types, independently of their local uses in Section 87. The condition on $M$ also implies $M^TM\preceq I_4$.

**Proposition 88.2 (exact original-family supremum).** The quantity $q$ in (S.223) is nonnegative throughout its domain, and

$$
\sup_{T\in\mathcal T_3}\ \max_{X\in\mathsf D(\mathbb C^3)} f_T(X)
=\max_{\substack{X\in\mathsf D(\mathbb R^3)\\
M\in\mathbb R^{3\times4},\ MM^T\preceq I_3}}\Theta(X,M).
\tag{S.224}
$$

All closed-domain maxima on the right exist. A strict value $\Theta(X,M)>r$ constructs a strict violation for an actual $T\in\mathcal T_3$ without changing that $X$.

Proof. By Proposition 85.3, real $X$ suffices for each $T$. For the real $5\times9$ matrix $\mathcal K_T(X)$ the nuclear-dual optimum can be attained by a real $9\times5$ isometry $U$. To see the extra isometry condition, take its rectangular SVD and extend the polar singular-vector pairing over any zero singular values. There are nine rows for five orthonormal columns. This is an isometric completion of the same attained rectangular duality, including deficient rank.

Write the three $3\times5$ row blocks as $U_0,U_1,C$, and put $D=(U_0;U_1)\in\mathbb R^{6\times5}$. One common isometry gives exactly

$$
\begin{gathered}
U^TU=I_5,\qquad D^TD+C^TC=I_5,\\
\operatorname{Tr}(U\mathcal K_T(X))
=\frac14\operatorname{Tr}\bigl(S(U_0E_0+U_1E_1)\bigr)
+\frac12\langle T,C^TS\rangle_F.
\end{gathered}
\tag{S.225}
$$

For fixed $C,X$, maximize over the unit sphere of $\mathcal L$. Its support function is $\|\Pi_{\mathcal L}(C^TS)\|_F$, even when that projection vanishes. Orthonormality of the two $E_i$ gives

$$
\|\Pi_{\mathcal L}(C^TS)\|_F^2
=\operatorname{Tr}(XCC^T)
-\bigl(\operatorname{Tr}(SCE_0)\bigr)^2
-\bigl(\operatorname{Tr}(SCE_1)\bigr)^2.
\tag{S.226}
$$

Both overlap penalties therefore belong to the same $C$ and $X$.

For this fixed $C$, feasibility is $C^TC\preceq I_5$, equivalently $CC^T\preceq I_3$. Put $P=I_5-C^TC$ and $W=[E_0S\mid E_1S]\in\mathbb R^{5\times6}$. Every $D$ with $D^TD=P$ can be written $D=V\sqrt P$, where $V\in\mathbb R^{6\times5}$ is an isometry. Indeed the equality of Grams defines an isometry on $\operatorname{ran}\sqrt P$ and it extends to all five columns in six dimensions. Conversely this representation always gives $D^TD=P$. Rectangular Procrustes maximization, or the same SVD pairing, gives

$$
\begin{aligned}
\max_{D^TD=P}\operatorname{Tr}(DW)
&=\|\sqrt P\,W\|_*\\
&=\operatorname{Tr}\sqrt{\sqrt{A_5}P\sqrt{A_5}},\\
A_5=WW^T&=E_0XE_0^T+E_1XE_1^T
=\operatorname{diag}(A,0).
\end{aligned}
\tag{S.227}
$$

For the second equality, the two positive products
$\sqrt P A_5\sqrt P$ and $\sqrt{A_5}P\sqrt{A_5}$ have identical nonzero spectra: they are the left and right Grams of $\sqrt P\sqrt{A_5}$. The SVD maximizing $V$ exists with six rows, including when $P$ or $A_5$ is singular. Thus this step uses neither an inverse nor separate choices for the two code blocks.

Write $C=[M_0\ M_1\ u]$ in the reordered output basis, with one vector $u\in\mathbb R^3$. Since $CE_i=M_iJ^T/\sqrt2$, the two traces in (S.226) are precisely $\eta_i$. The zero last row and column of $\sqrt{A_5}$ remove $u$ and its cross terms from (S.227), leaving exactly $\ell(X,M)$. The remaining feasibility and projected norm are

$$
uu^T\preceq H=I_3-MM^T,\qquad
\|\Pi_{\mathcal L}(C^TS)\|_F^2
=\operatorname{Tr}(XMM^T)+u^TXu-\eta_0^2-\eta_1^2.
\tag{S.228}
$$

For arbitrary singular $H\succeq0$, $uu^T\preceq H$ is equivalent to
$u=\sqrt H z$ for a vector with $\|z\|\leq1$. The inequality first forces $u\in\operatorname{ran}H$; on this range it gives $\|H^{+/2}u\|\leq1$. Conversely $zz^T\preceq I_3$ gives the original inequality by congruence. It follows that

$$
\max_{uu^T\preceq H}u^TXu
=\max_{\|z\|\leq1}z^T\sqrt H X\sqrt H z
=\lambda_{\max}(\sqrt H X\sqrt H).
\tag{S.229}
$$

A unit top eigenvector attains this even when the top eigenvalue is zero. This is the exact contribution of the single physical output direction $h$, as in the same-dilation geometry (R.10). Replacing it by $\operatorname{Tr}(XH)$ would permit a higher-rank residual and would change this optimization. No active-output component of $T$ has been discarded.

At an attaining $u$, the last side of (S.228) equals $q$, proving $q\geq0$. The code optimum and $\eta_i$ depend only on $X,M$, so choosing this $u$, then an attaining $D$, then an attaining $T$ gives $\Theta$ with one common $U$. Conversely every original triple has these constraints and is bounded by the same expression. The maxima over $T,X,U$ commute as maxima over their compact product before the conditional eliminations; the conditional choices just described show attainment at every elimination. There is no interchange of a minimum with a maximum. Densities and the row-contraction ball for $M$ are compact. Square roots, largest eigenvalues and all expressions in (S.223) are continuous, including their singular endpoints. This proves the closed-domain identity; Proposition 86.2 replaces its $T$ maximum by the legal supremum, giving (S.224).

For the strict-violation construction, first choose $u=\sqrt H z$ using a unit top eigenvector in (S.229), and then choose the single $D$ attaining (S.227). Since

$$
\ell(X,M)\leq\operatorname{Tr}\sqrt A
=\sqrt2\operatorname{Tr}\sqrt R
\leq2\sqrt{\operatorname{Tr}R}\leq2,
\tag{S.230}
$$

a strict $\Theta>r>1/2$ has $q>0$. The first inequality follows from
$0\preceq I_4-M^TM\preceq I_4$ and monotonicity of the positive square root; the middle one is Cauchy–Schwarz on the two eigenvalues of $R$. Define
$T=\Pi_{\mathcal L}(C^TS)/\sqrt q$. It has unit norm and both zero overlaps. The common-isometry pairing in (S.225) is then $\Theta$, so $f_T(X)\geq\Theta>r$. If $T e_2=0$, apply (S.215) with a sufficiently small parameter and use (S.214) at the same $X$. Proposition 85.2 supplies the required actual rank-three encoder. $\square$

## 89. Exact product and offdiagonal calibrations

**Proposition 89.1 (sharp zero-$M$ calibration).** On the $M=0$ slice of (S.223),

$$
\max_{X\in\mathsf D(\mathbb R^3)}\Theta(X,0)=r,
\qquad X_\star=\operatorname{diag}(c,1-c,0)
\ \text{attains equality}.
\tag{S.231}
$$

Proof. Here $H=I_3$, $\eta_i=0$ and
$\ell=\sqrt2\operatorname{Tr}\sqrt{J^TXJ}$, so

$$
\Theta(X,0)=
\frac{\operatorname{Tr}\sqrt{J^TXJ}}{2\sqrt2}
+\frac{\sqrt{\lambda_{\max}(X)}}2.
\tag{S.232}
$$

Let the eigenvalues of $X$ be $\lambda_1\geq\lambda_2\geq\lambda_3\geq0$. Compression interlacing, by the Rayleigh min-max principle, bounds the two eigenvalues of $J^TXJ$ by $\lambda_1,\lambda_2$. Thus
$\operatorname{Tr}\sqrt{J^TXJ}\leq\sqrt{\lambda_1}+\sqrt{\lambda_2}
\leq\sqrt{\lambda_1}+\sqrt{1-\lambda_1}$.
Put $b=1/(2\sqrt2)$. Since $1/2+b=c$ and $c^2+b^2=c$, Cauchy–Schwarz gives
$\Theta(X,0)\leq c\sqrt{\lambda_1}+b\sqrt{1-\lambda_1}\leq\sqrt c$.
At $X_\star$ the two compression inequalities are equalities and
$\lambda_1=c=c^2/(c^2+b^2)$ gives equality in the last step. The associated outside column can be $u=e_0$, and (S.226) then selects $T=h e_0^T$. Directly
$f_{h e_0^T}(X_\star)=c\sqrt c+b\sqrt{1-c}=\sqrt c$.
This calibrates one slice and one boundary channel; it gives no bound for nonzero $M$. $\square$

**Proposition 89.2 (the legal product family has an exact common-density optimum).** For $0<\epsilon\leq1$ put

$$
u_\epsilon=\sqrt{1-\epsilon}\,e_0+\sqrt\epsilon\,e_2,\qquad
T^{\rm prod}_\epsilon=h u_\epsilon^T.
\tag{S.233}
$$

This is an actual minimal-Kraus-rank-three family, although
$\operatorname{rank}T^{\rm prod}_\epsilon=1$, and

$$
\max_{X\in\mathsf D(\mathbb C^3)}
f_{T^{\rm prod}_\epsilon}(X)^2
=\frac{1+\sqrt{(1-\epsilon)/2}}2<c.
\tag{S.234}
$$

These values tend to $c$ as $\epsilon\downarrow0$.

Proof. The product outside-output structure is the branch with vanishing phase-Choi cross block (R.3), already present in Theorem 4.3 of the first volume. Here its environment vector is chosen for an exact calibration. In the notation of (S.204) the three actual Kraus matrices are

$$
\begin{aligned}
K_0&=[b_1/\sqrt2,g_1/\sqrt2,\sqrt{1-\epsilon}\,h],\\
K_1&=[b_2/\sqrt2,g_2/\sqrt2,0],\\
K_2&=[0,0,\sqrt\epsilon\,h].
\end{aligned}
\tag{S.235}
$$

Their TP sum has diagonal $(1,1,1-\epsilon+\epsilon)$ and all offdiagonals zero. The two overlaps vanish because $h$ is perpendicular to the four code directions. The first columns force the coefficients of $K_0,K_1$ in any complex linear relation to vanish, and $\epsilon>0$ then forces that of $K_2$ to vanish. The phase outputs are those of Proposition 85.2. This includes $\epsilon=1$ and proves actual rank three without imposing matrix rank three on $T$.

Let $\omega=\operatorname{diag}(1/2,1/2,0)$ and
$\nu_\epsilon=|u_\epsilon\rangle\langle u_\epsilon|$. Orthogonality of the active output space and $h$ gives, for every complex density,

$$
f_{T^{\rm prod}_\epsilon}(X)
=\frac{\operatorname{Tr}\sqrt{J^TXJ}}{2\sqrt2}
+\frac{\sqrt{u_\epsilon^TXu_\epsilon}}2
=\frac{f(\omega,X)+f(\nu_\epsilon,X)}2.
\tag{S.236}
$$

Both terms must use this same $X$. Use the two-state Uhlmann midpoint identity as an intermediate consequence of the purification formula [Bény–Oreshkov, (54)–(56)](../../../Library/QuantumChannels/beny2011simulation.md). Its required form and applicability to singular states can be seen directly inside this calculation. For normalized states $A,B$, fix a purification $x$ of a candidate $X$, on a sufficiently large common ancilla. Choose purifications $a,b$ realizing the positive overlaps $f(A,X),f(B,X)$ with that one $x$. Uhlmann gives $\operatorname{Re}\langle a,b\rangle\leq f(A,B)$, so
$(f(A,X)+f(B,X))/2\leq\|a+b\|/2\leq\sqrt{(1+f(A,B))/2}$.
Conversely choose Uhlmann-aligned $a,b$ with
$\langle a,b\rangle=f(A,B)\geq0$ and take
$x=(a+b)/\sqrt{2+2f(A,B)}$. Its single reduced density $X$ gives each fidelity at least the corresponding overlap, attaining the upper bound on their average. This uses no inverse or strict positivity.

Apply this cited purification identity to the two states in (S.236). Their root fidelity is
$f(\omega,\nu_\epsilon)=\sqrt{u_\epsilon^T\omega u_\epsilon}
=\sqrt{(1-\epsilon)/2}$. Squaring the midpoint value proves (S.234). For positive $\epsilon$ that inner root is strictly below $1/\sqrt2$, and its limit at zero is $1/\sqrt2$. Thus the proposed constant could not be decreased if a uniform bound for all $T$ were established; this family alone does not establish that bound. $\square$

**Proposition 89.3 (a legal offdiagonal optimizer and the exact diagonal loss).** For $\epsilon=1/2$ in (S.233), the density

$$
X_{\rm off}=
\begin{pmatrix}
2/3&0&1/3\\
0&1/6&0\\
1/3&0&1/6
\end{pmatrix}
\tag{S.237}
$$

is an unrestricted optimizer, with

$$
\max_{X\in\mathsf D(\mathbb C^3)}f_{T^{\rm prod}_{1/2}}(X)^2
=\frac34,\qquad
\max_{\substack{X\in\mathsf D(\mathbb C^3)\\X\ {\rm diagonal}}}
f_{T^{\rm prod}_{1/2}}(X)^2=\frac58.
\tag{S.238}
$$

Proof. The $(e_0,e_2)$ block of $X_{\rm off}$ is
$\left(\begin{smallmatrix}4&2\\2&1\end{smallmatrix}\right)/6$, a PSD rank-one block with nonzero eigenvalue $5/6$. The other eigenvalue is $1/6$ on $e_1$. Thus the full spectrum is $(5/6,1/6,0)$ and the trace is one. For $u=(e_0+e_2)/\sqrt2$,
$u^TX_{\rm off}u=3/4$ and $J^TX_{\rm off}J=\operatorname{diag}(2/3,1/6)$. Consequently
$f(\omega,X_{\rm off})=(\sqrt{2/3}+\sqrt{1/6})/\sqrt2=\sqrt3/2$ and
$f(|u\rangle\langle u|,X_{\rm off})=\sqrt3/2$.
Each weighted output sector in (S.236) contributes $\sqrt3/4$; their sum has square $3/4$. Equation (S.234) proves unrestricted optimality.

For $X=\operatorname{diag}(x,y,z)$, $x+y+z=1$, (S.236) gives
$f_T(X)=(\sqrt x+\sqrt y+\sqrt{x+z})/(2\sqrt2)$.
Since $x+z=1-y$ and $x\leq1-y$, it is at most
$(2\sqrt{1-y}+\sqrt y)/(2\sqrt2)\leq\sqrt{5/8}$.
The last inequality is Cauchy–Schwarz with coefficient vector $(2,1)$.
Both inequalities attain equality at $(x,y,z)=(4/5,1/5,0)$.
Thus (S.238) is exact. It disproves a diagonal-auxiliary-density restriction within this actual rank-three product family. Since $3/4<c$, it does not violate the proposed uniform constant. $\square$

## 90. The unchanged sharp inequality in equivalent common-variable forms

**Definition 90.1 (the remaining uniform assertion).** The sharp fixed-input assertion for the family of Definition 85.1 is

$$
\forall T\in\mathcal T_3\ \forall X\in\mathsf D(\mathbb C^3):
\qquad f_T(X)^2\leq c.
\tag{S.239}
$$

**Proposition 90.2 (exact equivalent obligations).** Equation (S.239) is equivalent to each of the following common-variable assertions: $V_\partial\leq c$; the sphere inequality of (S.220) for every feasible triple in (S.218); existence, for each such triple separately, of a multiplier satisfying the $9\times9$ PSD certificate of (S.220); and

$$
\ell(X,M)+2\sqrt{q(X,M)}\leq4\cos(\pi/8)
\quad\text{for every }X\in\mathsf D(\mathbb R^3),\
M\in\mathbb R^{3\times4},\ MM^T\preceq I_3.
\tag{S.240}
$$

Proof. The legal supremum equals $V_\partial$ by (S.216). Equation (S.218) and the expansion (S.219) express the boundary maximum using a single common feasible triple and one unit $S$. Proposition 87.3 gives the multiplier equivalence for each fixed triple, allowing $\lambda$ to depend on it. Proposition 88.2 gives the exact alternative supremum $\max\Theta$, and $r=\sqrt c$ converts its upper bound to (S.240). These are equivalences of full optimized values and of uniform statements on the displayed domains. A strict failure of either exact formulation yields a strict legal fixed-input failure by Proposition 86.2 or the construction in Proposition 88.2. $\square$

**Definition 90.3 (unproved quantitative boundary and distinct supports).** Uniform validity of (S.239), or equivalently (S.240) for general nonzero common $M$ or (S.220) for every common $Q$, remains unproved. The code loss $\ell$ and residual gain $q$ must be estimated at the same $X,M$, with both $\eta_i$ penalties retained. The $M=0$ calibration and the exact product family give equality on the closure and approach it in the legal class; they do not bound the other common-variable choices.

The auxiliary support projection $P_E$ of Proposition 87.1 acts in the three-dimensional environment. The physical-output optimal-dual support is the separate equality (S.197) of Proposition 83.4, acting in the five-dimensional output. No identification of these supports, or positive-definite dual conclusion without (S.200), is part of the reductions. A fixed-input violation would disprove this sufficient witness assertion, and would not by itself construct a full-reference recovery beating the original diamond lower target. The broader branches, the conditional consequences and the encoder-dependent input assertions of Sections 80–84 retain their respective hypotheses and conclusions.

## 追加锚（本行以下为增补区）

## 91. The boundary specialization and simultaneous orthogonal symmetry

**Definition 91.1 (the same boundary family in two environment coordinates).** Retain $E_i,\mathcal T_\partial,\mathcal T_3,\rho_\star,c,r$ from (S.202), so $r=\sqrt c=\cos(\pi/8)$. Use the reordered output frame $(b_1,b_2,g_1,g_2,h)$ of Section 88. Write $T=[Z,0]\in\mathcal T_\partial$ and

$$
\begin{gathered}
\widehat E_0=\frac1{\sqrt2}\begin{pmatrix}I_2\\0_2\\0_{1\times2}\end{pmatrix},\qquad
\widehat E_1=\frac1{\sqrt2}\begin{pmatrix}0_2\\I_2\\0_{1\times2}\end{pmatrix},\\
Z=\begin{pmatrix}Z_0\\Z_1\\v^T\end{pmatrix}\in\mathbb R^{5\times2},\qquad
\operatorname{Tr}Z_0=\operatorname{Tr}Z_1=0,\qquad \|Z\|_F=1,\\
X\in\mathsf D(\mathbb R^2),\qquad
f_\partial(X,Z)=f_{[Z,0]}(JXJ^T)
=\left\|[\widehat E_0\sqrt X/4\mid\widehat E_1\sqrt X/4\mid Z\sqrt X/2]\right\|_*.
\end{gathered}
\tag{S.241}
$$

Here $J$ is the inclusion used in (S.223). The two zero traces are exactly the two Frobenius constraints of (S.202); the row $v^T$ is the single outside-output direction. The environmental density $X$ is separate from the physical qutrit density $\rho_\star=\operatorname{diag}(1/4,1/4,1/2)$.

For one common real matrix $M=[M_0\ M_1]\in\mathbb R^{2\times4}$ define

$$
\begin{gathered}
MM^T\preceq I_2,\qquad G=MM^T=(g_{ij}),\qquad H=I_2-G,\qquad
A=\tfrac12\operatorname{diag}(X,X),\\
p=\tfrac12\sum_{i=0}^1\bigl(\operatorname{Tr}(\sqrt X\,M_i)\bigr)^2,\qquad
\ell=\operatorname{Tr}\sqrt{\sqrt A(I_4-M^TM)\sqrt A},\\
q=1-\lambda_{\min}(\sqrt XH\sqrt X)-p,\qquad
\Theta(X,M)=\ell/4+\sqrt q/2.
\end{gathered}
\tag{S.242}
$$

The letters in (S.242) have these boundary dimensions. They specialize the common variables of Definition 88.1; they do not replace its three-dimensional domain.

**Proposition 91.2 (support-safe exact boundary specialization).** The quantity $q$ in (S.242) is nonnegative, and

$$
\max_{\substack{X\in\mathsf D(\mathbb R^2)\\M\in\mathbb R^{2\times4},\ MM^T\preceq I_2}}\Theta(X,M)
=\max_{\substack{X\in\mathsf D(\mathbb R^2)\\Z\in\mathcal L_2,\ \|Z\|_F=1}} f_\partial(X,Z)
=\sqrt{V_\partial}.
\tag{S.243}
$$

All displayed maxima include singular densities and singular $H$.

Proof. Proposition 87.1 supplies the environmental support restriction: since $E_0,E_1,T$ annihilate $I-P_E$, only $P_EXP_E$ enters $\Phi_T(X)$. If its trace is $s>0$, normalization multiplies the root objective by $1/\sqrt s\geq1$; if $s=0$, the objective is zero. Proposition 85.3 then permits real symmetric $X$ by conjugation averaging. Neither operation removes real offdiagonal entries.

Apply the rectangular trace/spectral duality used in (S.207) to (S.241). For fixed $X$, write the common dual matrix as $Q=[Q_0\ Q_1\ B]\in\mathbb R^{5\times6}$, with $QQ^T\preceq I_5$, and put $W=[\widehat E_0\sqrt X\mid\widehat E_1\sqrt X]$. At a fixed $B$, the maximum of the two code pairings is $\|(I_5-BB^T)^{1/2}W\|_*$. Indeed every code block $Q_c=[Q_0\ Q_1]$ satisfying $Q_cQ_c^T\preceq I_5-BB^T$ factors as $(I_5-BB^T)^{1/2}R$ for a contraction $R$ on the support; rectangular polar pairing attains its nuclear norm. This factorization and attainment remain valid with a kernel, as in the Watrous interface used in (S.227). Maximization over the unit sphere in $\mathcal L_2$ gives the support function $\|\Pi_2(B\sqrt X)\|_F$, including a zero projection. Thus, before eliminating $B$, the common-variable objective is

$$
\frac14\|(I_5-BB^T)^{1/2}W\|_*
+\frac12\|\Pi_2(B\sqrt X)\|_F,
\qquad B^TB\preceq I_2.
\tag{S.244}
$$

Write $B=[M^T;w^T]$, with $w\in\mathbb R^2$. Then $B^TB=G+ww^T$, so feasibility is exactly $ww^T\preceq H$. Since $W=[\sqrt A;0_{1\times4}]$, its Gram after multiplication by $(I_5-BB^T)^{1/2}$ is $\sqrt A(I_4-M^TM)\sqrt A$. The first term of (S.244) is therefore $\ell/4$, independent of $w$. Orthonormality of $\widehat E_0,\widehat E_1$ gives the two distinct projection penalties:

$$
\begin{aligned}
\|\Pi_2(B\sqrt X)\|_F^2
&=\operatorname{Tr}(XG)+w^TXw
-\tfrac12\bigl(\operatorname{Tr}(\sqrt X M_0)\bigr)^2
-\tfrac12\bigl(\operatorname{Tr}(\sqrt X M_1)\bigr)^2,\\
\max_{ww^T\preceq H}w^TXw
&=\lambda_{\max}(\sqrt H X\sqrt H).
\end{aligned}
\tag{S.245}
$$

For singular $H$, the constraint forces $w$ into $\operatorname{ran}H$. Inverting $\sqrt H$ only on that range shows it is equivalent to $w=\sqrt H u$ with $\|u\|\leq1$. Conversely $uu^T\preceq I_2$ implies $ww^T\preceq H$. A unit top eigenvector of $\sqrt H X\sqrt H$ attains (S.245), even if the eigenvalue is zero. This is the contribution of one row; a trace in its place would change the allowed rank of the outside contribution.

The matrices $\sqrt H X\sqrt H$ and $\sqrt XH\sqrt X$ have identical spectra, as the two Grams of $\sqrt H\sqrt X$. In dimension two their largest eigenvalue is $\operatorname{Tr}(XH)-\lambda_{\min}(\sqrt XH\sqrt X)$. Since $\operatorname{Tr}(X(G+H))=1$, (S.245) becomes exactly $q$ in (S.242). Its projected-norm interpretation proves $q\geq0$. For each $X,M$, choose the attaining $w$, the attaining common code block, and then the attaining $Z$ in the projection direction. Those choices realize (S.244) simultaneously. Compactness and continuity supply all maxima, without inverses on null spaces. This proves (S.243). The norm duality and singular-compatible contraction factorization are the literature-attested intermediate tools of [Watrous, Section 1 and Section 2.1, Lemma 2](../../../Library/QuantumChannels/watrous2012simpler.md); the specialization is a consequence of the existing family-specific reduction. $\square$

**Proposition 91.3 (ordered spectrum by joint symmetry).** For $O\in O(2)$ and $D=\operatorname{diag}(O,O,1)$, the transformations

$$
(X,Z)\longmapsto(OXO^T,DZO^T),\qquad
M_i\longmapsto OM_iO^T
\tag{S.246}
$$

preserve the respective objectives, constraints and $\|M\|_F$. Consequently the joint maxima in (S.243) may be expressed with

$$
X=\operatorname{diag}(x,y),\qquad x+y=1,\qquad x\geq y\geq0,\qquad
\alpha=\sqrt x,\quad\beta=\sqrt y.
\tag{S.247}
$$

Proof. The identities $D\widehat E_iO^T=\widehat E_i$ imply that each block of the matrix defining $f_\partial$ is transformed by the same left orthogonal $D$ and a right orthogonal $O^T$. Its nuclear norm is unchanged. Conjugation sends $Z_i$ to $OZ_iO^T$, preserving both zero traces, and preserves the full Frobenius norm of $Z$. For $\mathcal O=\operatorname{diag}(O,O)$, the transformed common matrix is $OM\mathcal O^T$; hence $G,H$ are conjugated by $O$, $A$ and $M^TM$ by $\mathcal O$, and both traces in $p$ are unchanged. These transformations preserve $\ell,q,\Theta$ and the contraction condition. The real spectral theorem, followed by a simultaneous interchange of the two coordinates if necessary, gives (S.247). The transformation also changes $Z$; it does not justify diagonalizing $X$ while holding a channel fixed. $\square$

## 92. A weighted loss and the common eigenvalue-switch gain

**Definition 92.1 (weighted energy and exact spectral correction).** In the ordered coordinates (S.247), for the same $X,M$ as in (S.242), put

$$
\begin{gathered}
t=\|M\|_F^2=\operatorname{Tr}G,\qquad
\mathcal J=\sum_{i=0}^1\operatorname{Tr}(\sqrt X\,M_i^TM_i),\\
\kappa(x)=\max\left\{\frac y\alpha,
\frac{\beta-\alpha+\sqrt{1+6\alpha\beta}}4\right\},\\
\Delta=x(1-g_{11})-y(1-g_{22}),\qquad
\omega=\frac{\sqrt{\Delta^2+4xyg_{12}^2}-\Delta}{2},\\
F_0(x)=\frac{(2+\sqrt2)\sqrt x+\sqrt2\sqrt{1-x}}4
=c\sqrt x+\frac{\sqrt{1-x}}{2\sqrt2}.
\end{gathered}
\tag{S.248}
$$

The correction $\omega\geq0$ includes eigenvalue switching when $\Delta\leq0$. The parameter $t$ is the square of the Frobenius radius of the dual contraction.

**Proposition 92.2 (support-safe code loss).** Throughout (S.242),

$$
\ell\leq\sqrt2(\alpha+\beta)-\frac{\mathcal J}{2\sqrt2}.
\tag{S.249}
$$

Proof. Set $L=\sqrt A(I_4-M^TM)\sqrt A$. Its support is contained in $\operatorname{supp}A$. On that support $Y=\sqrt A$ is positive definite. Use the fidelity variational formula of [Watrous, Section 2.1, (6) and Theorem 3](../../../Library/QuantumChannels/watrous2012simpler.md) with operands $I$ and $L$, restricted to this support, and this particular test matrix $Y$:

$$
\begin{aligned}
\operatorname{Tr}\sqrt L
&\leq\tfrac12\operatorname{Tr}(Y+Y^{-1}L)\\
&=\operatorname{Tr}\sqrt A-\tfrac12\operatorname{Tr}(\sqrt A M^TM)\\
&=\sqrt2(\alpha+\beta)-\frac1{2\sqrt2}
\sum_i\operatorname{Tr}(\sqrt X M_i^TM_i).
\end{aligned}
\tag{S.250}
$$

All traces in the first line are on the support. In the second line, cyclicity and $A^{1/2}Y^{-1}A^{1/2}=\sqrt A$ on that support justify the equality; extending by zero gives the full-space expression. No commutation between $A$ and $M^TM$ is assumed. The result holds directly when $A$ is singular and uses a variational upper bound, not an asserted attaining inverse on its kernel. $\square$

**Proposition 92.3 (both trace losses and the exact eigenvalue switch).** For every feasible common pair,

$$
yg_{22}-p\leq\kappa(x)\mathcal J,\qquad
\lambda_{\min}(\sqrt XH\sqrt X)=y(1-g_{22})-\omega,
\qquad q=x+yg_{22}-p+\omega.
\tag{S.251}
$$

Proof. Write $M_i=\left(\begin{smallmatrix}a_i&b_i\\d_i&e_i\end{smallmatrix}\right)$. Directly from the two squared traces in $p$,

$$
\begin{aligned}
yg_{22}-p
&=\sum_i\left[-\tfrac x2a_i^2+yd_i^2+\tfrac y2e_i^2-\alpha\beta a_ie_i\right],\\
\mathcal J&=\sum_i\left[\alpha(a_i^2+d_i^2)+\beta(b_i^2+e_i^2)\right].
\end{aligned}
\tag{S.252}
$$

When $\beta>0$, the $d_i$ term has quotient $y/\alpha$, and the $b_i$ term has quotient zero. Rescale the pair $(a_i,e_i)$ to $(\sqrt\alpha a_i,\sqrt\beta e_i)$. Its symmetric quadratic matrix and larger eigenvalue are

$$
\frac12\begin{pmatrix}-\alpha&-\sqrt{\alpha\beta}\\-\sqrt{\alpha\beta}&\beta\end{pmatrix},\qquad
\frac{\beta-\alpha+\sqrt{(\alpha+\beta)^2+4\alpha\beta}}4
=\frac{\beta-\alpha+\sqrt{1+6\alpha\beta}}4.
\tag{S.253}
$$

This eigenvalue is nonnegative, since the determinant is $-\alpha\beta/2<0$. Taking the maximum of the two nonzero quotients proves the first inequality of (S.251), for each block and then their sum. At $y=0$, $\alpha=1,\beta=0,\kappa=0$ and the inequality is simply $-p\leq0$, with no rescaling by zero.

The matrix $\sqrt XH\sqrt X$ has diagonal entries $x(1-g_{11})$, $y(1-g_{22})$ and offdiagonal $-\sqrt{xy}\,g_{12}$. Its smaller eigenvalue is the second diagonal entry minus $(\sqrt{\Delta^2+4xyg_{12}^2}-\Delta)/2$. This proves the exact identity for every sign of $\Delta$, including $x=y$ and repeated eigenvalues. Substitution into (S.242) gives the last identity. $\square$

**Theorem 92.4 (gain-loss inequality on the common contraction).** For every pair in (S.242), expressed by the joint symmetry in ordered coordinates,

$$
\Theta(X,M)\leq F_0(x)
-\left(\frac1{8\sqrt2}-\frac{\kappa(x)}{4\sqrt x}\right)\mathcal J
+\frac{\omega}{4\sqrt x}.
\tag{S.254}
$$

If $\Delta>0$, there is the additional upper bound

$$
\Theta(X,M)\leq F_0(x)
-\left(\frac1{8\sqrt2}-\frac{\kappa(x)}{4\sqrt x}\right)\mathcal J
+\frac{\sqrt x\,y}{4\Delta}g_{12}^2.
\tag{S.255}
$$

Proof. Since $q\geq0$ and $x\geq1/2$, the supporting line to the square root at $x$ gives $\sqrt q\leq\alpha+(q-x)/(2\alpha)$. Combine this with (S.249) and (S.251): the code loss in $\ell/4$ is $\mathcal J/(8\sqrt2)$, while the residual term contributes at most $(\kappa\mathcal J+\omega)/(4\alpha)$. The remaining terms are $F_0(x)$, proving (S.254). When $\Delta>0$, rationalization gives

$$
\omega=\frac{2xyg_{12}^2}{\sqrt{\Delta^2+4xyg_{12}^2}+\Delta}
\leq\frac{xyg_{12}^2}{\Delta},
\tag{S.256}
$$

which proves (S.255). The hypothesis $\Delta>0$ is required for this denominator bound. At $x=1$, feasibility gives $\Delta=1-g_{11}\geq0$ and $\omega=0$, so (S.254) still holds even if $\Delta=0$. All terms in the first bound are defined at $x=1/2$. These are one-sided estimates of the exact objective (S.242), with $\mathcal J$ and $\omega$ evaluated at the same $M$. $\square$

## 93. Rational spectral-band and all-spectrum exclusion radii

**Theorem 93.1 (the spectral-band estimate).** If the boundary pair satisfies

$$
\frac{21}{25}\leq\lambda_{\max}(X)=x\leq\frac78,
\qquad \|M\|_F\leq\frac1{10},
\tag{S.257}
$$

then

$$
\Theta(X,M)\leq F_0(x)-\frac{\mathcal J}{1280}
\leq F_0(x)-\frac{\|M\|_F^2}{4000}.
\tag{S.258}
$$

Proof. By Proposition 91.3 it suffices to use (S.247), and the norm assumption is $t\leq1/100$. The following estimates use only rational comparisons:

$$
\alpha\geq\frac{229}{250},\qquad
\frac{353}{1000}\leq\beta\leq\frac25,\qquad
\alpha\beta\leq\frac{367}{1000}.
\tag{S.259}
$$

Indeed $(229/250)^2<21/25$, $(353/1000)^2<1/8\leq y$, and $y\leq4/25$. Also $xy\leq84/625<(367/1000)^2$, because $x(1-x)$ decreases for $x\geq1/2$ and $x\geq21/25$. Consequently
$y/\alpha\leq40/229<637/2000$ and
$\sqrt{1+6\alpha\beta}\leq179/100$, the latter since
$1+6(367/1000)=1601/500<(179/100)^2$. Thus

$$
\kappa(x)\leq\frac{(2/5)-(229/250)+(179/100)}4
=\frac{637}{2000}.
\tag{S.260}
$$

Here the displayed value bounds both entries of the maximum defining $\kappa$. Since $G\succeq0$, $g_{11},g_{22}\geq0$ and $g_{11}+g_{22}=t$, whence

$$
\begin{gathered}
\Delta=(2x-1)-xg_{11}+yg_{22}
\geq\frac{17}{25}-\frac78\frac1{100}
=\frac{537}{800}>\frac{67}{100},\\
g_{12}^2\leq g_{11}g_{22}\leq\frac{t^2}{4},\qquad
\mathcal J\geq\beta t\geq\frac{353}{1000}t.
\end{gathered}
\tag{S.261}
$$

The first inequality for $\mathcal J$ uses $\alpha\geq\beta$ in (S.252). Since $xy\leq84/625<27/200$, (S.256) yields

$$
\omega\leq\frac{27}{536}t^2
\leq\frac{27}{53600}t
\leq\frac{1059}{2000000}t
\leq\frac3{2000}\mathcal J.
\tag{S.262}
$$

The middle scalar comparison is strict before multiplication by $t$, because $27\cdot2000000<1059\cdot53600$; it remains a non-strict inequality when $t=0$. Equations (S.251), (S.260) and (S.262) give $q\leq x+(8/25)\mathcal J$. Use this sharper bound in the square-root supporting line and retain (S.249). Then

$$
\begin{aligned}
\Theta&\leq F_0(x)-\frac{\mathcal J}4
\left(\frac1{2\sqrt2}-\frac8{25\alpha}\right),\\
\frac1{2\sqrt2}-\frac8{25\alpha}
&\geq\frac{353}{1000}-\frac{80}{229}
=\frac1{320}+\frac{971}{1832000}>\frac1{320}.
\end{aligned}
\tag{S.263}
$$

The first lower bound follows again from $(353/1000)^2<1/8$ and $\alpha\geq229/250$. Thus $\Theta\leq F_0-\mathcal J/1280$. Finally
$\mathcal J/1280\geq353t/1280000\geq t/4000$, since $353>320$. This proves both parts of (S.258), including $M=0$. $\square$

**Proposition 93.2 (exact zero-contraction gap and a global coarse estimate).** For $x\in[1/2,1]$,

$$
\begin{aligned}
r-F_0(x)
&=\frac r2\left[(\sqrt x-\sqrt c)^2+
(\sqrt{1-x}-\sqrt{1-c})^2\right]\\
&\geq\frac r4(x-c)^2.
\end{aligned}
\tag{S.264}
$$

In particular $F_0(x)\leq r$, with equality exactly at $x=c$. For every feasible pair with $t\leq1$,

$$
q\leq x+yt,\qquad \Theta(X,M)\leq F_0(x)+t/4.
\tag{S.265}
$$

Proof. The coefficient identities $c^2+1/8=c$ and $c(1-c)=1/8$ give
$F_0(x)=r(\sqrt c\sqrt x+\sqrt{1-c}\sqrt{1-x})$. The two vectors inside the inner product are unit vectors. Expanding their squared distance proves the equality in (S.264) and its equality condition. Each squared difference is at least $(x-c)^2/4$, by factoring the difference of squares and bounding the sum of the two nonnegative roots by $2$. Adding the two bounds proves the last inequality, including the endpoints.

For (S.265), positivity and $\operatorname{Tr}G=t$ imply $G\preceq tI_2$, hence $H\succeq(1-t)I_2$. Congruence by $\sqrt X$ and the minimum-eigenvalue bound yield
$\lambda_{\min}(\sqrt XH\sqrt X)\geq(1-t)y$. As $p\geq0$, this gives $q\leq x+yt$. Also $\ell\leq\operatorname{Tr}\sqrt A=\sqrt2(\alpha+\beta)$ by positive-square-root monotonicity. The supporting line at $x$ therefore gives
$\Theta\leq F_0(x)+yt/(4\alpha)\leq F_0(x)+t/4$, because $y\leq\alpha$ on $[1/2,1]$. Every comparison uses the same pair $X,M$. $\square$

**Theorem 93.3 (a uniform radius over all boundary auxiliary densities).** For every $X\in\mathsf D(\mathbb R^2)$, including singular $X$, and every common feasible $M$,

$$
\|M\|_F\leq\frac1{100}
\quad\Longrightarrow\quad
\Theta(X,M)\leq r-\frac{\|M\|_F^2}{4000}.
\tag{S.266}
$$

Proof. By joint symmetry order the spectrum as in (S.247), and put $t=\|M\|_F^2\leq1/10000$. Inside $[21/25,7/8]$, Theorem 93.1 and $F_0\leq r$ prove the assertion. Outside that interval the following strict rational margins apply. Since
$(353/250)^2<2<(181/125)^2$, the formula $c=(2+\sqrt2)/4$ gives
$c>853/1000$ and $c<431/500$. Therefore both $c-21/25$ and $7/8-c$ exceed $13/1000$. Moreover $c>21/25>81/100$, so $r>9/10$. Equation (S.264) then gives

$$
r-F_0(x)>\frac9{40}\left(\frac{13}{1000}\right)^2
=\frac{1521}{40000000},\qquad
\frac t4+\frac t{4000}\leq\frac{1001}{40000000}
<\frac{1521}{40000000}.
\tag{S.267}
$$

Combining (S.265) with this strict gap proves (S.266) outside the band as well. The included singular endpoint $x=1$ uses (S.265) directly and needs no strictly positive $X$. The radii $1/100$ here and $1/10$ in Theorem 93.1 correspond respectively to $t\leq1/10000$ and $t\leq1/100$. $\square$

## 94. An exact overlap cost in the original boundary variables

**Proposition 94.1 (traceless-block weighted overlap identity).** For the boundary variables of (S.241), without any diagonal assumption on $X$, set

$$
D_0=\tfrac12\operatorname{diag}(X,X,0),\qquad W=ZXZ^T.
\tag{S.268}
$$

Then

$$
\operatorname{Tr}(D_0W)
=\frac12\left[\det(X)\sum_{i=0}^1\|Z_i\|_F^2
+\sum_{i=0}^1\bigl(\operatorname{Tr}(XZ_i)\bigr)^2\right].
\tag{S.269}
$$

Proof. The block trace gives
$\operatorname{Tr}(D_0W)=\tfrac12\sum_i\operatorname{Tr}(XZ_iXZ_i^T)$; the outside row $v^T$ contributes zero to this trace. In a basis with $X=\operatorname{diag}(x,y)$, any real traceless block is $Z_i=\left(\begin{smallmatrix}a&b\\d&-a\end{smallmatrix}\right)$, and

$$
\begin{aligned}
\operatorname{Tr}(XZ_iXZ_i^T)
&=(x^2+y^2)a^2+xy(b^2+d^2)\\
&=xy(2a^2+b^2+d^2)+(x-y)^2a^2\\
&=\det(X)\|Z_i\|_F^2+\bigl(\operatorname{Tr}(XZ_i)\bigr)^2.
\end{aligned}
\tag{S.270}
$$

Both sides are invariant under the simultaneous conjugation $X\mapsto OXO^T$, $Z_i\mapsto OZ_iO^T$ of Proposition 91.3, so the identity holds for every real symmetric density. The calculation is polynomial and includes $y=0$ and $x=y$. Summing over the two blocks proves (S.269). This is an identity for a common $X,Z$, rather than separately optimized bounds on the two summands. $\square$

## 95. Interpretation in the original actual family and the remaining contraction inequality

**Corollary 95.1 (necessary dual radii for a strict violation).** Any boundary common pair with $\Theta(X,M)>r$ must satisfy

$$
\|M\|_F>\frac1{100};\qquad
\lambda_{\max}(X)\in[21/25,7/8]
\ \Longrightarrow\ \|M\|_F>\frac1{10}.
\tag{S.271}
$$

The same necessary conditions hold for every maximizing common pair associated with a strict boundary violation through (S.243).

Proof. The first implication is the contrapositive of Theorem 93.3. In the stated band, Theorem 93.1 and $F_0\leq r$ give the second. A strict boundary value is bounded by the jointly maximized common formulation, whose maximum is attained by Proposition 91.2; any such maximizing value above $r$ obeys these implications. The constraints are on a dual $2\times4$ contraction. They impose neither a radius on an active channel column nor a condition on the matrix rank of $T$ or its physical Kraus rank. $\square$

**Definition 95.2 (the residual uniform obligation and its exact original-family meaning).** The remaining boundary assertion is

$$
\Theta(X,M)\leq r\qquad
\text{for all }X\in\mathsf D(\mathbb R^2),\quad
M\in\mathbb R^{2\times4},\quad MM^T\preceq I_2.
\tag{S.272}
$$

Proposition 91.2 identifies this assertion with $V_\partial\leq c$; Propositions 86.1–86.2 and 90.2 identify it with (S.239), with every complex $3\times3$ environmental density retained and actual minimal Kraus rank three. The calibration of Proposition 89.1 provides a feasible value $r$ at $M=0$, and (S.213) provides a boundary feasible squared value $c$. These are lower calibrations for the full maximum; neither supplies its general upper bound.

Theorems 92.4, 93.1 and 93.3 give upper estimates and the two exclusion neighborhoods, while (S.245), (S.251)'s eigenvalue formulas, (S.264)'s first equality and (S.269) are exact identities. For general $M$ outside those neighborhoods, sufficient control of the common $\omega$ against the weighted loss and $r-F_0(x)$ remains unproved. In particular (S.255) requires $\Delta>0$ and does not control the whole eigenvalue-switch regime. Neither (S.272) nor a uniform multiplier construction for (S.220) follows from the local estimates.

For the original physical interpretation, Proposition 85.2 retains the full matrices $K_\alpha=[(E_0)_\alpha,(E_1)_\alpha,t_\alpha]$ and both TP trace constraints. Their actual minimal Kraus rank is three exactly when $Te_2\ne0$, independently of $\operatorname{rank}T$. If a strict boundary value were found, the perturbation $( [Z,0]+\varepsilon he_2^T)/\sqrt{1+\varepsilon^2}$ of (S.215), together with (S.214), would transfer its strict gap at the same auxiliary density to that actual rank-three class. The local bounds construct no such violation. The fixed physical input remains $\rho_\star$, the recovery ranges over all complex CPTP maps, and the Bény–Oreshkov fixed-state root-fidelity identity (133), with its unrestricted completion, is precisely the interface already used in (S.205)–(S.206) [Bény–Oreshkov, Section IV](../../../Library/QuantumChannels/beny2011simulation.md). No change of physical dimension or restriction of recovery Kraus number is implicit in the two-dimensional auxiliary boundary.

The weighted quadratic comparison, eigenvalue correction, rational exclusions and overlap identity in Sections 92–94 are repo-derived consequences within this family. The norm duality, support-compatible contraction factorization and fidelity test-matrix inequality are literature-attested intermediate tools, with the exact Watrous citations attached to their uses above. The existing full-family reductions of Sections 85–90 retain their original domains and proofs; the estimates here do not assert a uniform fixed-input certificate or the broader full-reference target.

## 追加锚（本行以下为增补区）

## 96. Common-matrix coordinates for the boundary budgets

**Definition 96.1 (the common contraction and its active rows).** Use the boundary space and the quadratic of Definitions 87.2 and 91.1, in the reordered output frame $(b_1,b_2,g_1,g_2,h)$. Write $J_0=[b_1,b_2]$, $J_1=[g_1,g_2]$, so $\widehat E_i=J_i/\sqrt2$ and $J_i^TJ_j=\delta_{ij}I_2$. In these coordinates,

$$
\begin{gathered}
\mathcal L_2=\{S\in\mathbb R^{5\times2}:\operatorname{Tr}(J_0^TS)=\operatorname{Tr}(J_1^TS)=0\},\\
\Pi_2(Z)=Z-\frac12\sum_{i=0}^1J_i\operatorname{Tr}(J_i^TZ),\\
Q=[Q_0\mid Q_1\mid B]\in\mathbb R^{5\times6},\qquad QQ^T\preceq I_5,\qquad
C=\frac{J_0^TQ_0+J_1^TQ_1}{4\sqrt2},\qquad A=\|C\|_F^2,\\
d=\Pi_2(BC^T),\qquad H(S)=\frac14\Pi_2(BB^TS),\qquad
g_Q(S)=\|C+S^TB/2\|_F^2.
\end{gathered}
\tag{S.273}
$$

Thus $C$ is $2\times2$, $d\in\mathcal L_2$, and $H$ acts on the eight-dimensional space $\mathcal L_2$. The factor $1/2$ in the projection follows from $\|J_i\|_F^2=2$. Decompose the same $B$ as

$$
\begin{gathered}
B=J_0V_0+J_1V_1+hw,\qquad
V_i=J_i^TB\in\mathbb R^{2\times2},\quad w=h^TB\in\mathbb R^{1\times2},\\
V=\begin{pmatrix}V_0\\V_1\end{pmatrix}\in\mathbb R^{4\times2},\qquad
B^TB=V^TV+w^Tw\preceq I_2,\qquad K=I_2-V^TV\succeq0,\\
\alpha=\frac1{2\sqrt2},\qquad
\lambda_0=\frac c2=\frac{2+\sqrt2}{8}.
\end{gathered}
\tag{S.274}
$$

The physical output direction $h$ contributes exactly one row $w$. It is distinct from the third environment coordinate $e_2$ used in (S.215).

**Definition 96.2 (notation for the existing ordered boundary formula).** Apply the joint symmetry of Proposition 91.3 and write

$$
\begin{gathered}
P=\operatorname{diag}(p,q),\qquad \frac12\leq p\leq1,\quad q=1-p,\qquad
D_p=\operatorname{diag}(\sqrt p,\sqrt q,\sqrt p,\sqrt q),\\
F_{P,V}=D_p(I_4-VV^T)D_p\succeq0,\qquad
\tau(P,V)=\frac12\sum_{i=0}^1\bigl(\operatorname{Tr}(V_i\sqrt P)\bigr)^2,\\
N(P,V)=\frac1{4\sqrt2}\operatorname{Tr}\sqrt{F_{P,V}},\\
R(P,V)=\operatorname{Tr}(PV^TV)
+\lambda_{\max}(\sqrt K P\sqrt K)-\tau(P,V)
=1-\lambda_{\min}(\sqrt P K\sqrt P)-\tau(P,V).
\end{gathered}
\tag{S.275}
$$

Here $p$ is an eigenvalue of $P$; it is not the trace-penalty variable called $p$ in (S.242). The parameter correspondence to that formula is exactly

$$
X_{\rm( S.242)}=P,\qquad M=V^T=[V_0^T\ V_1^T],\qquad
p_{\rm( S.242)}=\tau,\qquad
\ell=4N,\qquad q_{\rm( S.242)}=R,\qquad
\Theta=N+\frac{\sqrt R}{2}.
\tag{S.276}
$$

Indeed $\sqrt{A_{\rm( S.242)}}=D_p/\sqrt2$, and $M^TM=VV^T$. Transposition preserves each trace against the symmetric matrix $\sqrt P$, so both penalties are retained. The two products $\sqrt K P\sqrt K$ and $\sqrt P K\sqrt P$ have the same spectrum, including zero eigenvalues. Together with $\operatorname{Tr}(P(V^TV+K))=1$, this gives the last equality of (S.275). These identities identify (S.275) with the common-variable boundary formula (S.242)–(S.245); they do not constitute a second boundary reduction. In particular Proposition 91.2 already supplies $R\geq0$ and equality of the optimized maxima, with both trace constraints and the full $4\times4$ code square root.

All support and attainment conventions are inherited from that proposition. When $K$ is singular, $w^Tw\preceq K$ means $w^T=\sqrt K z$ for some $\|z\|\leq1$ on its support. The largest eigenvalue in (S.275) is the attainable maximum of $wPw^T$ over this single row, including a zero maximum; replacing it by $\operatorname{Tr}(PK)$ changes the allowed residual rank. The code-row residual $I_5-BB^T$ is also allowed to be singular. Its factorization uses its range, as in the proof of (S.244), and not an inverse on its kernel. If the projected norm is zero, the maximizing unit boundary vector can be any unit vector in $\mathcal L_2$. The spectral ordering of $P$ is a symmetry of the joint optimization, and does not permit diagonalizing an auxiliary density at a fixed channel.

## 97. An operator bound and a necessary common matrix budget

**Proposition 97.1 (sharp operator bound for the common code matrix).** Every common feasible $Q$ of (S.273) satisfies

$$
\|C\|_{\rm op}\leq\alpha=\frac1{2\sqrt2}.
\tag{S.277}
$$

Proof. For arbitrary unit vectors $u,v\in\mathbb R^2$ form the $5\times6$ test matrix

$$
T_{u,v}=\frac1{4\sqrt2}[J_0uv^T\mid J_1uv^T\mid0],\qquad
\langle Q,T_{u,v}\rangle_F=u^TCv,\qquad
\|T_{u,v}\|_*=\frac2{4\sqrt2}=\alpha.
\tag{S.278}
$$

Its two left vectors $J_0u,J_1u$ are orthonormal. Its two unit right vectors have disjoint block supports. Consequently its two nonzero singular values are both $1/(4\sqrt2)$. Rectangular trace/spectral duality, in the convention of [Watrous, Section 1](../../../Library/QuantumChannels/watrous2012simpler.md), gives $|u^TCv|\leq\|Q\|_{\rm op}\|T_{u,v}\|_*\leq\alpha$. Taking the supremum over $u,v$ proves (S.277). The same feasible choice $Q_0=J_0$, $Q_1=J_1$, $B=he_1^T$, where $e_1$ is the first coordinate vector of $\mathbb R^2$, has $QQ^T=I_5$ and $C=\alpha I_2$, so the constant is attained. $\square$

**Proposition 97.2 (necessary matrix budget and its trace).** For the same common $Q$, with $V_i$ taken from its actual block $B$ in (S.274),

$$
16CC^T+V_0V_0^T+V_1V_1^T\preceq2I_2,
\qquad 16A+\|V\|_F^2\leq4,
\qquad A\leq\frac14-\frac{\|V\|_F^2}{16}.
\tag{S.279}
$$

Proof. For every $u\in\mathbb R^2$, the two code terms and the same row-contraction constraint give

$$
\begin{aligned}
16\|C^Tu\|^2
&=\frac12\|Q_0^TJ_0u+Q_1^TJ_1u\|^2\\
&\leq\sum_{i=0}^1\|Q_i^TJ_iu\|^2\\
&\leq\sum_{i=0}^1u^TJ_i^T(I_5-BB^T)J_iu\\
&=2\|u\|^2-u^T(V_0V_0^T+V_1V_1^T)u.
\end{aligned}
\tag{S.280}
$$

The first inequality is $\|x+y\|^2\leq2\|x\|^2+2\|y\|^2$. The second uses $Q_iQ_i^T\preceq I_5-BB^T$, which follows by dropping only the other positive code block from $QQ^T\preceq I_5$. Finally $J_i^TB=V_i$ and $J_i^TJ_i=I_2$ give the last line. This proves the matrix inequality by its quadratic forms. Taking its two-dimensional trace gives $16\|C\|_F^2+\sum_i\|V_i\|_F^2\leq4$, proving the remaining assertions. $\square$

The budgets (S.277) and (S.279) are necessary conditions on data extracted from one feasible common $Q$. They assert no converse realizing arbitrary matrices $C,V$ that satisfy them. Neither budget alone supplies the target bound for $g_Q$ or replaces the directional certificate (S.220)–(S.221).

## 98. A restricted high-spectrum estimate with aligned residual direction

**Theorem 98.1 (weighted estimate in the aligned high-$p$ sector).** Let $P,V$ have the common feasible domain of (S.275). In addition assume both

$$
p\geq p_0:=\frac4{4+\sqrt2},\qquad
e_1\text{ is a top eigenvector of }\sqrt P(I_2-V^TV)\sqrt P,
\tag{S.281}
$$

where $Pe_1=pe_1$. A repeated top eigenvalue is allowed. Then

$$
N(P,V)^2+\frac{R(P,V)}4\leq\lambda_0,
\qquad
\left(N(P,V)+\frac{\sqrt{R(P,V)}}2\right)^2\leq c.
\tag{S.282}
$$

Proof. Write $V_i=\left(\begin{smallmatrix}a_i&b_i\\c_i&d_i\end{smallmatrix}\right)$ and set $s_j=\|Ve_j\|^2$, $\gamma=(Ve_1)^T(Ve_2)$. The residual matrix is

$$
\sqrt P K\sqrt P=
\begin{pmatrix}
p(1-s_1)&-\sqrt{pq}\,\gamma\\
-\sqrt{pq}\,\gamma&q(1-s_2)
\end{pmatrix}.
\tag{S.283}
$$

For $p,q>0$, the eigenvector condition in (S.281) is equivalent to $\gamma=0$ and $p(1-s_1)\geq q(1-s_2)$. For $q=0$ the matrix condition itself applies; it imposes no division by $q$ and no orthogonality condition on the two columns of $V$. Under (S.281) the largest eigenvalue is $p(1-s_1)$, even when the two eigenvalues coincide. Thus the exact residual in (S.275) is

$$
R=p+q\sum_{i=0}^1(b_i^2+d_i^2)
-\frac12\sum_{i=0}^1(\sqrt p\,a_i+\sqrt q\,d_i)^2.
\tag{S.284}
$$

Use $t=1+\sqrt2$ and the positive definite weight $W=\operatorname{diag}(t,1,t,1)$. For $F=F_{P,V}\succeq0$, Hilbert–Schmidt Cauchy–Schwarz gives

$$
\begin{aligned}
(\operatorname{Tr}\sqrt F)^2
&=\langle W^{1/2},W^{-1/2}\sqrt F\rangle_F^2\\
&\leq\operatorname{Tr}(W)\,
\operatorname{Tr}(\sqrt F W^{-1}\sqrt F)
=\operatorname{Tr}(W)\operatorname{Tr}(W^{-1}F).
\end{aligned}
\tag{S.285}
$$

Only $W$ is inverted. The last equality is cyclicity of the trace, requiring no commutation of $W$ with $F$ and no invertibility of $F$, $P$, or $I_4-VV^T$. Expanding the diagonal trace and using $N^2=(\operatorname{Tr}\sqrt F)^2/32$ yields

$$
\begin{aligned}
\operatorname{Tr}(W^{-1}F)
&=2(p/t+q)-\sum_{i=0}^1
\left[\frac pt(a_i^2+b_i^2)+q(c_i^2+d_i^2)\right],\\
N^2&\leq\frac{t+1}{8}(p/t+q)
-\frac{t+1}{16}\sum_{i=0}^1
\left[\frac pt(a_i^2+b_i^2)+q(c_i^2+d_i^2)\right].
\end{aligned}
\tag{S.286}
$$

Since $(t+1)/t=\sqrt2$, the constant part after adding $R/4$ from (S.284) is exactly

$$
\frac{t+1}{8}(p/t+q)+\frac p4
=\frac{(2+\sqrt2)(p+q)}8=\lambda_0.
\tag{S.287}
$$

The complete remaining quadratic, with both trace penalties expanded, is

$$
\begin{aligned}
16\left(N^2+\frac R4-\lambda_0\right)
\leq\sum_{i=0}^1\bigl[
&-(2+\sqrt2)p a_i^2+(4q-\sqrt2 p)b_i^2\\
&-(2+\sqrt2)q c_i^2-\sqrt2 q d_i^2
-4\sqrt{pq}\,a_id_i\bigr].
\end{aligned}
\tag{S.288}
$$

The $b_i^2$ coefficient is nonpositive exactly when $p\geq p_0$. The $c_i^2$ coefficient is nonpositive. The opposite of the $(a_i,d_i)$ quadratic has matrix

$$
G_{p,q}=\begin{pmatrix}
(2+\sqrt2)p&2\sqrt{pq}\\
2\sqrt{pq}&\sqrt2 q
\end{pmatrix},\qquad
\det G_{p,q}=2pq(\sqrt2-1)\geq0.
\tag{S.289}
$$

Its diagonal entries are nonnegative, so it is PSD, including when $q=0$. Every summand on the right of (S.288) is therefore nonpositive. This proves the first inequality of (S.282). Both $N$ and $R$ are nonnegative, and $(a+b)^2\leq2(a^2+b^2)$ with $a=N$, $b=\sqrt R/2$ proves the second because $2\lambda_0=c$.

At $p=p_0$ the $b_i^2$ coefficient vanishes without affecting the conclusion. At $q=0$ the residual matrix, the weight, and all displayed quadratics remain defined, and the same proof applies. Repeated residual eigenvalues are included by the non-strict eigenvalue comparison preceding (S.284). No positive-definiteness assumption on the feasible residuals has entered the argument. $\square$

The two conditions in (S.281) are additional hypotheses. Feasibility of $V$ does not imply them, and no reduction of a global optimizer to their sector is established. The conclusion concerns the joint variables $P,V$; it does not certify all auxiliary directions of an arbitrary fixed common $Q$.

## 99. The stronger squared inequality and the fixed-multiplier route

**Proposition 99.1 (equivalence of a universal squared lemma and a uniform multiplier).** The following proposed stronger inequality over the whole boundary domain,

$$
N(P,V)^2+R(P,V)/4\leq\lambda_0
\quad\text{for all }p\in[1/2,1],\quad V^TV\preceq I_2,
\tag{S.290}
$$

is equivalent to validity of (S.220) with the single choice $\lambda=\lambda_0$ for every common feasible $Q$. This equivalence does not assert either universal inequality.

Proof. For fixed $Q$, define $K_B:\mathcal L_2\to\mathbb R^{2\times2}$ and $L_Q:\mathbb R\oplus\mathcal L_2\to\mathbb R^{2\times2}$ by

$$
\begin{gathered}
K_B(S)=S^TB/2,\qquad L_Q(t,S)=tC+K_B(S),\\
K_B^*(Y)=\Pi_2(BY^T)/2,\qquad
K_B^*K_B=H,\qquad K_B^*(C)=d/2,\\
L_Q^*L_Q=
\begin{pmatrix}A&d^T/2\\d/2&H\end{pmatrix}
\quad\text{on }\mathbb R\oplus\mathcal L_2.
\end{gathered}
\tag{S.291}
$$

The adjoint follows by the Frobenius pairing, with $\Pi_2$ because the domain is $\mathcal L_2$; the two remaining identities follow by substitution into (S.273). Equality of the operator norms of $L_Q$ and $L_Q^*$ gives

$$
\begin{aligned}
\|L_Q\|_{\rm op}^2\leq\lambda_0
&\ \Longleftrightarrow\quad
\langle C,Y\rangle_F^2+\tfrac14\|\Pi_2(BY^T)\|_F^2
\leq\lambda_0\|Y\|_F^2\quad(\forall Y),\\
&\ \Longleftrightarrow\quad
\begin{pmatrix}
\lambda_0 I_{\mathcal L_2}-H&-d/2\\
-d^T/2&c-A-\lambda_0
\end{pmatrix}\succeq0.
\end{aligned}
\tag{S.292}
$$

For the last equivalence reorder the scalar coordinate in $\lambda_0 I-L_Q^*L_Q$ and use $c=2\lambda_0$.

It remains to match the universal auxiliary-direction inequality in (S.292) to (S.290). Homogeneity permits $\|Y\|_F=1$. At fixed $B,Y$, put

$$
\begin{gathered}
\mathcal A_Y=\frac1{4\sqrt2}[J_0Y\mid J_1Y],\qquad
\mathcal D=I_5-BB^T,\qquad
n_B(Y)=\|\mathcal D^{1/2}\mathcal A_Y\|_*,\\
\max_{[Q_0\mid Q_1][Q_0\mid Q_1]^T\preceq\mathcal D}
\langle C,Y\rangle_F^2=n_B(Y)^2.
\end{gathered}
\tag{S.293}
$$

This is the exact code-row elimination already used in (S.244), with its factor $1/4$ included in $\mathcal A_Y$. The feasible code-row set is symmetric, so its maximal squared pairing is the square of its maximal pairing. If $\mathcal D$ is singular, the row constraint forces the code block into its range, and the support factorization $[Q_0\mid Q_1]=\mathcal D^{1/2}Z$ uses a contraction $Z$; the polar pairing still attains $n_B(Y)$. No row outside that range is allowed.

Write $P_Y=YY^T$ and extend the polar factor in $Y=\sqrt{P_Y}U$ to an orthogonal $U$ even at deficient rank. The simultaneous transformation $(Y,B)\mapsto(YU^T,BU^T)$ makes $Y=\sqrt{P_Y}$ and leaves $BY^T$ unchanged. It also preserves $BB^T$ and right-rotates the two blocks of $\mathcal A_Y$, preserving $n_B(Y)$. The joint orthogonal symmetry of Proposition 91.3 then gives the ordered density $P$ of (S.275). Both transformations act on the common variables and preserve both trace penalties. For this $Y=\sqrt P$ and $B$ as in (S.274), the code Gram is $F_{P,V}/32$, hence $n_B(\sqrt P)=N(P,V)$, independently of $w$. Moreover (S.245), with the parameter map (S.276), gives

$$
\begin{aligned}
\|\Pi_2(B\sqrt P)\|_F^2
&=\operatorname{Tr}(PV^TV)+wPw^T-\tau(P,V),\\
\max_{w^Tw\preceq K}
\left[n_B(\sqrt P)^2+\tfrac14\|\Pi_2(B\sqrt P)\|_F^2\right]
&=N(P,V)^2+R(P,V)/4.
\end{aligned}
\tag{S.294}
$$

The maximizing row is obtained from a top eigenvector of $\sqrt K P\sqrt K$ on the support, as in (S.245). The same $B$ permits an attaining code polar factor in (S.293). If either maximum is zero, a zero code block or a zero outside row is admissible; a zero projected norm needs no normalization. Thus the conditional maxima are attained with common variables, including singular $K$ and $\mathcal D$. Maximizing over compact unit $Y$ and feasible $Q$ can be done in either order. Equations (S.293)–(S.294) therefore identify the universal left side of (S.292) with the maximum in (S.290), proving the equivalence. $\square$

The exact residual target of Definition 95.2 and the stronger route (S.290) have different logical force. The latter would imply the former by

$$
\left(N+\frac{\sqrt R}{2}\right)^2
\leq2\left(N^2+\frac R4\right)\leq2\lambda_0=c.
\tag{S.295}
$$

The exact certificate (S.220) allows $\lambda$ to depend on $Q$. Consequently a failure of (S.290) would rule out the uniform choice $\lambda_0$ without itself refuting (S.272) or (S.239). Theorem 98.1 proves (S.290) only under both extra conditions (S.281).

**Definition 99.2 (the coarse scalar sufficient helper).** For each common feasible $Q$, Proposition 87.3 gives $0\preceq H\preceq I/4$. Thus $L_0=\lambda_0 I-H\succeq(\sqrt2/8)I\succ0$ and

$$
\frac14\langle d,L_0^{-1}d\rangle_F\leq\sqrt2\|d\|_F^2.
\qquad
\|d\|_F^2\leq\frac{\lambda_0-A}{\sqrt2}
\ \Longrightarrow\quad
\frac14\langle d,L_0^{-1}d\rangle_F\leq c-A-\lambda_0.
\tag{S.296}
$$

The implication is a sufficient scalar replacement for the directional Schur condition, since $c-A-\lambda_0=\lambda_0-A$. Its scalar premise is not a universal inequality: the next proposition disproves it using actual common blocks. This coarse premise, the universal squared lemma (S.290), and the exact residual target (S.272) are three distinct assertions.

## 100. An exact coarse-helper counterexample with a positive full certificate

**Proposition 100.1 (failure of the scalar premise on a common feasible contraction).** In the frame of Definition 96.1 take

$$
\begin{gathered}
Q_0=[b_1/2,b_2],\qquad Q_1=[g_1,g_2],\qquad
B=[h,(\sqrt3/2)b_1],\\
Q_0Q_0^T+Q_1Q_1^T+BB^T
=\left(\tfrac14+\tfrac34\right)b_1b_1^T
+b_2b_2^T+g_1g_1^T+g_2g_2^T+hh^T=I_5.
\end{gathered}
\tag{S.297}
$$

The scalar premise in (S.296) fails strictly for this same $Q$.

Proof. Equation (S.297) proves feasibility of all three blocks jointly. Direct substitution gives

$$
\begin{gathered}
C=\operatorname{diag}\left(\frac3{8\sqrt2},\frac1{2\sqrt2}\right),\qquad
A=\frac9{128}+\frac18=\frac{25}{128},\\
BC^T=\frac3{8\sqrt2}he_1^T+\frac{\sqrt3}{4\sqrt2}b_1e_2^T,\qquad
d=BC^T,\qquad \|d\|_F^2=\frac9{128}+\frac3{32}=\frac{21}{128}.
\end{gathered}
\tag{S.298}
$$

Here $e_1,e_2$ are the coordinate vectors of the two-dimensional boundary space. Each of $he_1^T$ and $b_1e_2^T$ has both traces against $J_0,J_1$ zero, so the projection defining $d$ removes neither term. The two matrices are Frobenius orthonormal, giving the displayed squared norm. Since $\lambda_0-A=(7+16\sqrt2)/128$,

$$
\|d\|_F^2-\frac{\lambda_0-A}{\sqrt2}
=\frac{5-7/\sqrt2}{128}>0.
\tag{S.299}
$$

The strict sign follows from $5\sqrt2>7$, whose positive sides have squares $50>49$. Thus the coarse sufficient scalar premise fails on the actual common-contraction domain, without using a tuple satisfying only the necessary budgets. $\square$

**Proposition 100.2 (the full directional certificate for the same contraction).** The $Q$ in (S.297) satisfies the full $9\times9$ certificate (S.220) strictly at $\lambda=\lambda_0$. In particular $g_Q(S)<c$ for every unit $S\in\mathcal L_2$.

Proof. For exactly the same $B$ as in (S.297), $BB^T=hh^T+(3/4)b_1b_1^T$. The two directions occupied by $d$ are therefore eigenvectors of $H$:

$$
u_1=he_1^T,\quad u_2=b_1e_2^T,\qquad
H(u_1)=\frac14u_1,\quad H(u_2)=\frac3{16}u_2,\qquad
d=\frac3{8\sqrt2}u_1+\frac{\sqrt3}{4\sqrt2}u_2.
\tag{S.300}
$$

Both eigenvector identities hold after projection because $u_1,u_2\in\mathcal L_2$. On the rest of that space the general bound $H\preceq I/4$ still holds. Hence $L_0\succeq(\sqrt2/8)I\succ0$, and the resolvent on $d$ is exactly

$$
\begin{aligned}
\langle d,L_0^{-1}d\rangle_F
&=\frac{9/128}{\lambda_0-1/4}
+\frac{3/32}{\lambda_0-3/16}\\
&=\frac{9\sqrt2}{32}+\frac3{2(1+2\sqrt2)}.
\end{aligned}
\tag{S.301}
$$

The available scalar term has four times its value equal to

$$
\begin{aligned}
4(c-A-\lambda_0)&=\frac7{32}+\frac1{\sqrt2},\\
4(c-A-\lambda_0)-\langle d,L_0^{-1}d\rangle_F
&=\frac{21\sqrt2-13}{32(1+2\sqrt2)}>0.
\end{aligned}
\tag{S.302}
$$

Thus the actual scalar Schur margin is

$$
c-A-\lambda_0-\frac14\langle d,L_0^{-1}d\rangle_F
=\frac{21\sqrt2-13}{128(1+2\sqrt2)}>0.
\tag{S.303}
$$

Both denominator and numerator are positive. Positive definiteness of $L_0$ and the strict Schur margin prove positive definiteness of the entire matrix in (S.220). Pairing it with $(S,1)$ for $\|S\|_F=1$ gives $c-g_Q(S)>0$. This proves the asserted certificate and strict bound. $\square$

This contraction refutes only the scalar premise of (S.296). Its valid full certificate shows why that failure is compatible with the proposed original bound. The resolvent charges the two nonzero components of $d$ at different eigenvalues, $1/4$ and $3/16$; the coarse estimate charges both at the first value and loses precisely that directional information. For a general multiplier in (S.220), possible singularity still requires all three conditions (S.221): nonnegativity of $\lambda I-H$, membership of $d$ in its range, and the pseudoinverse Schur inequality. The ordinary inverse in (S.301) is justified by $\lambda_0>1/4$, and supplies no permission to drop those conditions elsewhere.

## 101. Uniform obligations and applicability of the common-budget estimates

**Definition 101.1 (the remaining sectors and original-family boundaries).** The exact common-variable assertion still required is (S.272), or, by the notation map (S.276),

$$
\left(N(P,V)+\frac{\sqrt{R(P,V)}}2\right)^2\leq c
\quad\text{for every }p\in[1/2,1],\quad V\in\mathbb R^{4\times2},\quad V^TV\preceq I_2.
\tag{S.304}
$$

Theorem 98.1 controls only $p\geq p_0$ with the larger-$P$ direction a top residual eigendirection. It leaves the sector $p<p_0$ and the sectors in which that alignment fails. For $p,q>0$, a nonzero column inner product $(Ve_1)^T(Ve_2)$ rotates the residual eigendirections; even when it is zero, the larger residual eigenvalue can occur on the other axis. Repeated residual eigenvalues meet the alignment condition, while a singular endpoint must be interpreted through (S.283). The small-contraction results of Theorems 93.1 and 93.3 apply independently under their own hypotheses and exclude the neighborhoods in (S.271). There is no established argument placing a global optimizer in the union of those neighborhoods and the sector (S.281).

The unproved joint tradeoff is between the full code square-root trace $\operatorname{Tr}\sqrt{D_p(I_4-VV^T)D_p}$, the attainable gain of one outside row, and the two squared traces in $\tau$. The necessary common matrix budget (S.279) does not realize arbitrary data or control this tradeoff by itself. A universal proof of the stronger (S.290) would suffice by Proposition 99.1 and (S.295), but its validity outside the stated restricted sector is not established. The per-$Q$ multiplier alternative of Proposition 87.3 remains the exact certificate route and permits a multiplier depending on the common contraction.

Propositions 85.2–85.3, 86.1–86.2 and 90.2 retain the original-family interpretation of (S.304): the half-beta, $\lambda=1$ mixed-Gram bound (S.239), with fixed physical $\rho_\star$, every complex $3\times3$ auxiliary density, and actual minimal Kraus rank three characterized by $Te_2\ne0$. The matrix rank of $T$ is not substituted for Kraus rank. A strict failure of (S.304) would require the common attaining blocks and one auxiliary density supplied by (S.243)–(S.245), followed by (S.215) and its all-complex-density continuity bound (S.214) to enter the actual rank-three class. Proposition 100.1 supplies no such strict failure, because Proposition 100.2 bounds its entire boundary sphere.

The universal half-beta rank-three mixed-Gram estimate remains unproved here, as does the associated uniform fixed-input witness programme (S.154), with the support and positive-definite-dual qualifications of Sections 83–84 retained. The separate broader target of [volume I, Definition 47.2](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#47-applicability-and-the-remaining-recovery-problem) ranges over arbitrary $0<\beta\leq1/2$, actual ranks up to nine, and whole-output complex CPTP recoveries with a full complex reference and the unhalved diamond norm. It also remains open. A counterexample to a sufficient scalar helper is not a counterexample to either of these targets; even a fixed-input witness failure would not itself provide an improving full-reference recovery certificate.

The operator and matrix budgets, the restricted coefficient comparison, and the common-contraction counterexample with its full directional certificate are repo-derived mathematics for this family. The boundary normal form is reused from Sections 85–95, with the exact correspondence (S.276), rather than claimed as an additional reduction. Rectangular trace/spectral duality and the support-compatible contraction factorization are attributed to the interfaces in [Watrous, Section 1 and Section 2.1, Lemma 2](../../../Library/QuantumChannels/watrous2012simpler.md); Hilbert–Schmidt Cauchy–Schwarz is used inside (S.285). The exact one-constraint alternative is the [Boyd–Vandenberghe Appendix B.2 interface](../../../Library/QuadraticForms/boydvandenberghe2004convex.md) applied in Proposition 87.3. The physical normalization continues to use [Bény–Oreshkov, Section IV, (133), with Corollary 5](../../../Library/QuantumChannels/beny2011simulation.md), as in Proposition 85.3. These attributed general tools do not state the family-specific constant or settle the remaining universal tradeoff. No literature-priority claim is attached to the new family-specific consequences.

## 追加锚（本行以下为增补区）
