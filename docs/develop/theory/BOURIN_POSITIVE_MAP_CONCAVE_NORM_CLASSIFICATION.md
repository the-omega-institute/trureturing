# Bourin's positive-map concave norm problem: trace, projections and maximal rank

## 1. Original problem, domain and notation

**Definition 1.1 (The problem and its quantifiers).** Bourin, *A matrix subadditivity inequality for symmetric norms*, [arXiv:0906.1447v1](https://arxiv.org/pdf/0906.1447v1), p. 10, immediately after Theorem 3.3, asks for a characterization of positive linear maps $\Phi$ such that

$$
\|f(|\Phi(N)|)\|\leq\|\Phi(f(|N|))\|
\tag{1.1}
$$

for all normal operators $N$, all nonnegative concave functions and all symmetric norms. The preceding Theorem 3.3 treats sums of expansive congruences of normal matrices. The characterization below concerns every complex-linear positive map

$$
\Phi:M_n(\mathbb C)\longrightarrow M_k(\mathbb C),
\qquad n,k\geq1,
\tag{1.2}
$$

with no restriction to such a presentation by expansive congruences. For each fixed map, the quantifiers in (1.1) range over every normal $N\in M_n(\mathbb C)$, every finite-valued concave $f:[0,\infty)\to[0,\infty)$, and every unitarily invariant norm on $M_k(\mathbb C)$. Positivity means that $X\geq0$ implies $\Phi(X)\geq0$. No unitality or complete positivity is assumed.

**Definition 1.2 (Modulus, calculus and traces).** Adjoint is denoted by a superscript $*$, and throughout the modulus is the right modulus

$$
|X|=(X^*X)^{1/2}.
\tag{1.3}
$$

All traces are unnormalized. For a positive matrix $H=\sum_j t_jP_j$, spectral functional calculus means $f(H)=\sum_j f(t_j)P_j$, including the actual value $f(0)$ on the kernel. In particular, $f(0_{k\times k})=f(0)I_k$. A symmetric norm satisfies $\|UXV\|=\|X\|$ for all unitary $U,V$ of the appropriate size. The trace norm is $\|X\|_1=\operatorname{Tr}|X|$; thus both norms in (1.1) become ordinary traces when the trace norm is selected, since both arguments are positive.

For a positive $H\in M_k(\mathbb C)$ write

$$
F_q(H)=\sum_{j=1}^q\lambda_j(H),
\qquad 1\leq q\leq k,
\tag{1.4}
$$

with eigenvalues in decreasing order and repeated with multiplicity. For positive $H,J$, write $H\prec_w J$ when $F_q(H)\leq F_q(J)$ for every $q$. The Ky Fan dominance principle, recalled in Bourin's cited paper, p. 5, identifies this relation with domination for every symmetric norm. We use that principle directly. We also use the usual spectral variational formula

$$
F_q(H)=\max_{Q=Q^*=Q^2,\ \operatorname{rank}Q=q}\operatorname{Tr}(QH).
\tag{1.5}
$$

Indeed, in an eigenbasis of $H$, the diagonal entries of $Q$ lie in $[0,1]$ and sum to $q$; their weighted sum against decreasing eigenvalues is at most the sum of the first $q$. Projection onto the first $q$ eigenvectors attains it. Consequently positive Loewner order implies $\prec_w$ and hence symmetric-norm domination. These are classical spectral facts used as intermediates, not additional characterization claims.

**Definition 1.3 (The adjoint and the rank parameter).** Equip each matrix algebra with the Hilbert–Schmidt inner product $\langle X,Y\rangle=\operatorname{Tr}(X^*Y)$. Put

$$
T=\Phi^*(I_k),\qquad S=\Phi(I_n),\qquad
r_\Phi=\max_{\|u\|_2=1}\operatorname{rank}\Phi(uu^*).
\tag{1.6}
$$

Here $\Phi^*$ is the Hilbert–Schmidt adjoint of the same map (1.2). The maximum exists because the ranks form a nonempty subset of the finite set $\{0,\ldots,k\}$. For every vector $u$, the adjoint identity and positivity give

$$
u^*Tu=\operatorname{Tr}\Phi(uu^*)\geq0.
$$

In particular $T$ is Hermitian positive semidefinite. The adjoint identity, followed by conjugation, then yields

$$
\operatorname{Tr}\Phi(X)=\operatorname{Tr}(TX),\qquad
\operatorname{Tr}S=\operatorname{Tr}T
\tag{1.7}
$$

for all complex matrices $X$. For clarity, before using Hermiticity of $T$ the adjoint identity reads $\overline{\operatorname{Tr}\Phi(X)}=\operatorname{Tr}(X^*T)$; its specialization to $uu^*$ proves the assertion about $T$ and justifies (1.7).

**Convention 1.4 (Concavity at the endpoint).** Concavity is the scalar inequality on the closed half-line, with the given value at zero. A finite nonnegative concave function on this unbounded interval is nondecreasing: if one secant slope were negative, concavity would bound subsequent secant slopes by that negative number and force negative values sufficiently far to the right. Thus, for

$$
c=f(0),\qquad g(t)=f(t)-c,
\tag{1.8}
$$

$g$ is nonnegative and concave and satisfies $g(0)=0$. No continuity at zero follows or is imposed. In particular, for $a\geq1$ and $t\geq0$, concavity applied to $t=a^{-1}(at)+(1-a^{-1})0$ gives

$$
g(at)\leq a g(t).
\tag{1.9}
$$

The endpoint value in this formula is the assigned value $g(0)=0$, not a right-hand limit. The arguments below retain that distinction.

## 2. Projection traces and a uniform rank bound

**Lemma 2.1 (Projection condition and adjoint condition).** For the map (1.2), the following conditions are equivalent:

$$
\operatorname{Tr}\Phi(P)\geq\operatorname{rank}\Phi(P)
\quad\hbox{for every orthogonal projection }P\in M_n(\mathbb C);
\tag{2.1}
$$

$$
T\geq r_\Phi I_n.
\tag{2.2}
$$

It is enough to assume (2.1) for rank-one projections in order to deduce (2.2).

*Proof.* Suppose first that (2.2) holds. If $P$ has rank $m$, choose orthonormal vectors $u_1,\ldots,u_m$ spanning its range. Positivity and linearity give

$$
\Phi(P)=\sum_{i=1}^m\Phi(u_iu_i^*),\qquad
\operatorname{rank}\Phi(P)\leq\sum_{i=1}^m
\operatorname{rank}\Phi(u_iu_i^*)\leq m r_\Phi.
\tag{2.3}
$$

The rank inequality follows because the range of a sum is contained in the sum of the ranges. On the other hand, (1.7) and (2.2) give

$$
\operatorname{Tr}\Phi(P)=\sum_{i=1}^m u_i^*Tu_i\geq m r_\Phi.
\tag{2.4}
$$

These prove (2.1), including $P=0$ and every zero projection image.

Conversely assume (2.1) for rank-one projections and write $r=r_\Phi$. If $r=0$, (2.2) follows from $T\geq0$. Suppose $r>0$. Choose a unit vector $u_0$ such that $B_0=\Phi(u_0u_0^*)$ has rank $r$, and let $R=\operatorname{ran}B_0$. The restriction of $B_0$ to $R$ is positive definite. Fix any unit vector $v\in\mathbb C^n$. For real $t$, form the compression to this fixed $R$ of

$$
\Phi\bigl((v+tu_0)(v+tu_0)^*\bigr).
\tag{2.5}
$$

In an orthonormal basis of $R$, its determinant is a polynomial in $t$ of degree $2r$. Its leading coefficient is $\det(B_0|_R)>0$, since the coefficient of $t^2$ in the compressed matrix is $B_0|_R$. This polynomial is nonzero and has only finitely many real roots. For all sufficiently small $t$, $v+tu_0\ne0$. Except for those finitely many roots, (2.5) has rank at least $r$. With

$$
w_t=\frac{v+tu_0}{\|v+tu_0\|_2},
$$

normalization does not change the rank, and maximality of $r$ gives $\operatorname{rank}\Phi(w_tw_t^*)=r$. Along a sequence of such real $t$ tending to zero, the assumed rank-one case of (2.1) yields

$$
\operatorname{Tr}\Phi(w_tw_t^*)\geq r.
$$

A linear map between these finite-dimensional spaces is continuous. Taking the limit gives $v^*Tv=\operatorname{Tr}\Phi(vv^*)\geq r$. Since $v$ was arbitrary, (2.2) follows. The argument uses maximal-rank inputs approaching each actual $v$; it does not replace the map or treat rank as continuous. $\square$

## 3. Normal sums with the zero-origin function class

**Lemma 3.1 (Lifting a spectral family).** Let $E_1,\ldots,E_m\in M_k(\mathbb C)$ be positive and satisfy

$$
\operatorname{Tr}E_i\geq\operatorname{rank}E_i
\quad(1\leq i\leq m).
\tag{3.1}
$$

For arbitrary complex $z_1,\ldots,z_m$ and every finite nonnegative concave $g$ with $g(0)=0$,

$$
g\left(\left|\sum_{i=1}^m z_iE_i\right|\right)
\prec_w\sum_{i=1}^m g(|z_i|)E_i.
\tag{3.2}
$$

The sum on the left need not be normal.

*Proof.* We first give the rank-one decompositions used in this application. Discard an $E_i=0$, whose contributions to both sums are zero. Write the remaining $E_i$ in its positive spectral decomposition

$$
E_i=\sum_{j=0}^{d_i-1}\alpha_{ij}e_{ij}e_{ij}^*,
\qquad d_i=\operatorname{rank}E_i\geq1,\quad\alpha_{ij}>0,
$$

with the $e_{ij}$ orthonormal. If $d_i>1$, put $\omega_i=\exp(2\pi\mathrm i/d_i)$; if $d_i=1$, put $\omega_i=1$. Define

$$
v_{i\ell}=\frac1{\sqrt{d_i}}\sum_{j=0}^{d_i-1}
\sqrt{\alpha_{ij}}\,\omega_i^{j\ell}e_{ij},
\qquad 0\leq\ell<d_i.
\tag{3.3}
$$

Orthogonality and the finite geometric-sum identity give

$$
\sum_{\ell=0}^{d_i-1}v_{i\ell}v_{i\ell}^*=E_i,
\qquad
\|v_{i\ell}\|_2^2=\frac{\operatorname{Tr}E_i}{d_i}=:a_i\geq1.
\tag{3.4}
$$

This is the classical equal-diagonal Fourier change of basis applied to a spectral square root. Explicitly, the coefficient of $e_{ij}e_{ih}^*$ in the first sum is
$\sqrt{\alpha_{ij}\alpha_{ih}}d_i^{-1}\sum_\ell\omega_i^{(j-h)\ell}$, which equals $\alpha_{ij}$ for $j=h$ and zero otherwise. Thus (3.4) is an identity for the given $E_i$, not a substitute with the same eigenvalues.

Set $P_{i\ell}=a_i^{-1}v_{i\ell}v_{i\ell}^*$, a rank-one orthogonal projection. Every summand

$$
X_{i\ell}=z_i v_{i\ell}v_{i\ell}^*=z_i a_iP_{i\ell}
$$

is normal, and its right modulus is $|z_i|a_iP_{i\ell}$. Because $g(0)=0$, spectral calculus and (1.9) give the positive-matrix inequality

$$
g(|X_{i\ell}|)=g(|z_i|a_i)P_{i\ell}
\leq a_i g(|z_i|)P_{i\ell}.
\tag{3.5}
$$

We now directly reuse Bourin's normal-sum inequality, arXiv:0906.1447v1, Theorem 2.1 and its finite-family statement on p. 7:

$$
\left\|g\left(\left|\sum_{i,\ell}X_{i\ell}\right|\right)\right\|
\leq\left\|\sum_{i,\ell}g(|X_{i\ell}|)\right\|
\tag{3.6}
$$

for every symmetric norm. Its hypotheses apply to the individually normal summands $X_{i\ell}$, all in the same $M_k(\mathbb C)$; normality of their sum is not a hypothesis. The finite-family assertion is used directly, rather than iterating a two-summand result through nonnormal partial sums.

There is also an exact finite-spectral way to accommodate a discontinuity of $g$ at zero in this invocation. Take the finite set of positive spectral values of all $|X_{i\ell}|$ and of $|\sum_{i,\ell}X_{i\ell}|$. If it is nonempty, join the points $(0,0)$ and $(t,g(t))$ at these distinct increasing values by line segments, and extend constantly after the last point. Concavity of $g$ makes the successive slopes nonincreasing; nondecreasingness makes them nonnegative. The resulting function is continuous, concave and nonnegative on the whole half-line, and agrees with $g$ on every spectrum involved in (3.6). If the set is empty, all these matrices are zero and (3.6) is immediate. Thus even a continuous-endpoint formulation of the published supplier would give exactly (3.6), without changing any spectral-calculus value or using a limiting value at zero. This interpolation is only a proof of exact applicability of the supplier.

Summing (3.5) gives

$$
\sum_{i,\ell}g(|X_{i\ell}|)
\leq\sum_i g(|z_i|)E_i.
\tag{3.7}
$$

Apply (3.6) to each Ky Fan norm and then apply positive order monotonicity to (3.7). By (3.4), $\sum_{i,\ell}X_{i\ell}=\sum_i z_iE_i$, so this proves (3.2). If every $E_i$ was discarded, both sides of (3.2) are zero. No division by a zero rank or a zero eigenvalue was made. $\square$

## 4. Restoring constants in the actual output dimension

**Lemma 4.1 (A maximizing projection with a trace lower bound).** Let $v_1,\ldots,v_M\in\mathbb C^k$ satisfy $\|v_\ell\|_2^2\geq1$, and put

$$
S=\sum_{\ell=1}^M v_\ell v_\ell^*,\qquad
A=\sum_{\ell=1}^M b_\ell v_\ell v_\ell^*,\qquad b_\ell\geq0.
\tag{4.1}
$$

If $\operatorname{Tr}S\geq k$, then for each $1\leq q\leq k$ there is a rank-$q$ orthogonal projection $Q$ such that

$$
\operatorname{Tr}(QA)=F_q(A),\qquad \operatorname{Tr}(QS)\geq q.
\tag{4.2}
$$

Consequently, for every $c\geq0$,

$$
F_q(A+cS)\geq F_q(A)+cq.
\tag{4.3}
$$

Neither $A$ nor $S$ is required to be invertible.

*Proof.* Let $R=\operatorname{ran}A$, let $d=\dim R$, and choose an orthonormal eigenbasis $e_1,\ldots,e_d$ on $R$ with eigenvalues $\lambda_1\geq\cdots\geq\lambda_d>0$. A vector $v_\ell$ with $b_\ell>0$ belongs to $R$: if $x\in\ker A$, then

$$
0=x^*Ax=\sum_\ell b_\ell|v_\ell^*x|^2
$$

forces $v_\ell^*x=0$ for every such index. For these active indices define, only on $R$,

$$
w_\ell=\sqrt{b_\ell}\,(A|_R)^{-1/2}v_\ell.
\tag{4.4}
$$

Then

$$
\sum_{b_\ell>0}w_\ell w_\ell^*=I_R,
\qquad
0< h_\ell:=\|w_\ell\|_2^2\leq1.
\tag{4.5}
$$

The upper bound follows from $w_\ell w_\ell^*\leq I_R$. All inverses in (4.4) concern the positive definite restriction $A|_R$ only.

Suppose first that $1\leq q\leq d$, and let $Q$ be projection onto $e_1,\ldots,e_q$. Write $w_{j\ell}=e_j^*w_\ell$ and set

$$
\alpha_\ell=\sum_{j=1}^d\lambda_j|w_{j\ell}|^2
=b_\ell\|v_\ell\|_2^2\geq b_\ell>0,
\qquad
\beta_\ell=\sum_{j=1}^q\lambda_j|w_{j\ell}|^2,
\qquad
p_\ell=\sum_{j=1}^q|w_{j\ell}|^2.
\tag{4.6}
$$

The ordering of the eigenvalues yields

$$
\begin{aligned}
\beta_\ell h_\ell-\alpha_\ell p_\ell
&=\sum_{j\leq q<h\leq d}
(\lambda_j-\lambda_h)|w_{j\ell}|^2|w_{h\ell}|^2\geq0,\\
\frac{\beta_\ell}{\alpha_\ell}
&\geq\frac{p_\ell}{h_\ell}\geq p_\ell.
\end{aligned}
\tag{4.7}
$$

For $q=d$ the double sum is empty and the same assertions hold. Equation (4.4) gives $\operatorname{Tr}(Qv_\ell v_\ell^*)=\beta_\ell/b_\ell$ for active indices. Since $\alpha_\ell\geq b_\ell$, (4.5)–(4.7) imply

$$
\begin{aligned}
\operatorname{Tr}(QS)
&\geq\sum_{b_\ell>0}\frac{\beta_\ell}{b_\ell}
\geq\sum_{b_\ell>0}\frac{\beta_\ell}{\alpha_\ell}
\geq\sum_{b_\ell>0}p_\ell
=q.
\end{aligned}
\tag{4.8}
$$

The first inequality merely retains the nonnegative contributions of active indices. The last equality follows by tracing (4.5) against $Q$. This $Q$ maximizes the trace against $A$, so (4.2) follows for $q\leq d$. Ties among the eigenvalues cause no difficulty, since every difference in (4.7) is still nonnegative.

It remains to treat $q>d$, including $d=0$. Let $Q_R$ project onto $R$, and put

$$
a=\operatorname{Tr}(Q_RS),\qquad
b=\operatorname{Tr}((I_k-Q_R)S).
$$

We have $a\geq d$: for $d>0$ this is (4.8) with $q=d$, and for $d=0$ it says $0\geq0$. Also $a+b=\operatorname{Tr}S\geq k$. The positive compression of $S$ to $R^\perp$ has dimension $k-d>0$ and trace $b$. Its largest $q-d$ eigenvalues have sum at least $(q-d)b/(k-d)$, because the mean of an initial segment of a decreasing nonnegative list is at least the mean of the whole list. Choose their eigenprojection $Q_0$ inside $R^\perp$ and put $Q=Q_R+Q_0$. This is a rank-$q$ projection and maximizes the trace against $A$, whose nonzero spectrum lies on $R$. With $\theta=(q-d)/(k-d)$,

$$
\operatorname{Tr}(QS)\geq a+\theta b
=(1-\theta)a+\theta(a+b)
\geq(1-\theta)d+\theta k=q.
\tag{4.9}
$$

This proves (4.2) in every remaining case, in the full ambient dimension $k$. In particular, it includes projections extending beyond $\operatorname{ran}S$. Finally (1.5) gives

$$
F_q(A+cS)\geq\operatorname{Tr}(Q(A+cS))
\geq F_q(A)+cq,
$$

which is (4.3). $\square$
