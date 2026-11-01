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

## 5. The two exact characterizations

**Theorem 5.1 (The full function class).** For every pair of positive integers $n,k$ and each complex-linear positive $\Phi:M_n(\mathbb C)\to M_k(\mathbb C)$, the following four conditions on that same map are equivalent.

(A) For every normal $N\in M_n(\mathbb C)$, every finite nonnegative concave $f:[0,\infty)\to[0,\infty)$, and every symmetric norm on $M_k(\mathbb C)$,

$$
\|f(|\Phi(N)|)\|\leq\|\Phi(f(|N|))\|.
\tag{5.1}
$$

(B) For every such $N,f$, the trace-norm inequality holds, equivalently

$$
\operatorname{Tr}f(|\Phi(N)|)\leq
\operatorname{Tr}\Phi(f(|N|)).
\tag{5.2}
$$

(C) Both of the following inequalities hold:

$$
\operatorname{Tr}\Phi(I_n)\geq k,\qquad
\operatorname{Tr}\Phi(P)\geq\operatorname{rank}\Phi(P)
\quad\hbox{for every orthogonal projection }P.
\tag{5.3}
$$

(D) With precisely the adjoint and rank parameter (1.6),

$$
T\geq r_\Phi I_n,\qquad \operatorname{Tr}T\geq k.
\tag{5.4}
$$

*Proof.* (A) implies (B) because the trace norm is a symmetric norm. To prove (B) implies (C), first use $N=0$ and the constant function $f(t)=1$. Its two spectral-calculus values are $I_k$ and $\Phi(I_n)$, so (5.2) gives the first inequality of (5.3).

Fix an arbitrary orthogonal projection $P$. If $\Phi(P)=0$, its required inequality is $0\geq0$. Otherwise let $\mu>0$ be the smallest positive eigenvalue of $\Phi(P)$, and choose a real $a\geq\max\{1,\mu^{-1}\}$. Use the normal positive matrix $N=aP$ and the nonnegative concave function $f(t)=\min\{t,1\}$, which has $f(0)=0$. Then

$$
f(|N|)=P,\qquad
f(|\Phi(N)|)=f(a\Phi(P))
=\operatorname{supp}\Phi(P).
\tag{5.5}
$$

The second equality follows eigenvalue by eigenvalue: every positive eigenvalue of $a\Phi(P)$ is at least one, and every zero eigenvalue remains zero. Thus (5.2) is exactly $\operatorname{rank}\Phi(P)\leq\operatorname{Tr}\Phi(P)$. This proves (C) for every $P$, without requiring an invertible image.

Lemma 2.1 and (1.7) prove (C) if and only if (D), including both trace requirements.

To finish, assume (C) and prove (A). Fix the actual normal input $N$, and choose an orthonormal eigenbasis, including its zero eigenspace:

$$
N=\sum_{i=1}^n z_i p_i,\qquad p_i=u_iu_i^*,\qquad
\sum_i p_i=I_n.
\tag{5.6}
$$

Normal spectral calculus, positivity and complex linearity give

$$
E_i:=\Phi(p_i)\geq0,\qquad
X:=\Phi(N)=\sum_i z_iE_i,\qquad
S=\sum_i E_i=\Phi(I_n).
\tag{5.7}
$$

The projection part of (C) gives $\operatorname{Tr}E_i\geq\operatorname{rank}E_i$. Let $c=f(0)$ and $g=f-c$ as in (1.8), and put

$$
G=\sum_i g(|z_i|)E_i=\Phi(g(|N|)).
\tag{5.8}
$$

Lemma 3.1 gives

$$
F_q(g(|X|))\leq F_q(G)\qquad(1\leq q\leq k).
\tag{5.9}
$$

For every nonzero $E_i$ use its decomposition (3.3)–(3.4). Retain these vectors also when $z_i=0$ or $g(|z_i|)=0$. Taken together, these vectors have squared norms at least one and satisfy

$$
S=\sum_{i,\ell}v_{i\ell}v_{i\ell}^*,\qquad
G=\sum_{i,\ell}g(|z_i|)v_{i\ell}v_{i\ell}^*.
\tag{5.10}
$$

Zero $E_i$ contribute nothing. The ambient condition in (C) says $\operatorname{Tr}S\geq k$, so Lemma 4.1 applies to (5.10) with $A=G$. Consequently

$$
\begin{aligned}
F_q(f(|X|))
&=cq+F_q(g(|X|))\\
&\leq cq+F_q(G)\\
&\leq F_q(G+cS)\\
&=F_q(\Phi(f(|N|))).
\end{aligned}
\tag{5.11}
$$

The first identity holds because adding $cI_k$ shifts each eigenvalue by $c$. The last identity uses $f(|N|)=g(|N|)+cI_n$ and linearity of the same $\Phi$. All matrices to which $F_q$ is applied are positive. Ky Fan dominance now gives (5.1) for every symmetric norm. No assertion of normality for $X=\Phi(N)$ was used. We have proved (C) implies (A), completing all four equivalences. $\square$

**Theorem 5.2 (Exactly the zero-origin function class).** For the same full range of dimensions and positive maps, the following are equivalent:

(A$_0$) Inequality (5.1) holds for every normal $N$, every finite nonnegative concave $f$ satisfying $f(0)=0$, and every symmetric norm.

(B$_0$) Inequality (5.2) holds for every normal $N$ and every function in precisely that restricted class.

(C$_0$) For every orthogonal projection $P$,

$$
\operatorname{Tr}\Phi(P)\geq\operatorname{rank}\Phi(P).
\tag{5.12}
$$

(D$_0$) The adjoint satisfies

$$
T\geq r_\Phi I_n.
\tag{5.13}
$$

There is no additional condition on $\operatorname{Tr}\Phi(I_n)$ or $\operatorname{Tr}T$.

*Proof.* (A$_0$) implies (B$_0$) by selecting the trace norm. The function and inputs in (5.5) belong to the zero-origin class, so the projection argument proving (B) implies (C) also proves (B$_0$) implies (C$_0$), including zero images. Lemma 2.1 proves (C$_0$) if and only if (D$_0$). Conversely, under (C$_0$), use (5.6)–(5.7) and apply Lemma 3.1 directly with $g=f$. It gives

$$
f(|\Phi(N)|)\prec_w\sum_i f(|z_i|)E_i
=\Phi(f(|N|)),
\tag{5.14}
$$

which is (A$_0$) by Ky Fan dominance. This direction needs neither Lemma 4.1 nor an ambient trace bound. It also covers an empty family after zero $E_i$ are discarded, when both sides of (5.14) are zero. Thus all four conditions are equivalent with no hidden trace requirement. $\square$

Theorems 5.1–5.2 in particular show that a trace-norm test over the entire prescribed function and normal-input class characterizes the all-norm property. They do not identify a fixed finite collection of sampled inputs as a decision procedure. The separate ambient trace condition in Theorem 5.1 is exactly the condition needed to pass from the zero-origin function class to the full function class.

## 6. Singular, scalar and endpoint boundaries

**Corollary 6.1 (Zero maps and singular ambient output).** The zero map satisfies Theorem 5.2 and fails Theorem 5.1. More generally, let $R=\operatorname{ran}\Phi(I_n)$ and $s=\dim R$. Every output of $\Phi$ is supported on this same $R$, and in the orthogonal decomposition $\mathbb C^k=R\oplus R^\perp$,

$$
f(|\Phi(N)|)=f(|\Phi(N)|\big|_R)\oplus f(0)I_{k-s},
\qquad
\Phi(f(|N|))=\Phi(f(|N|))\big|_R\oplus0_{k-s}.
\tag{6.1}
$$

The dimension in Theorem 5.1 is still $k$, including when $s<k$. For $k\geq2$ and a rank-one projection $P\in M_k(\mathbb C)$, the map $\Phi(z)=zP$ satisfies the zero-origin property with equality for every allowed input and norm but fails the full property. The map $\Psi(z)=kzP$ satisfies the full property despite its singular output support.

*Proof.* If $r_\Phi=0$, all rank-one positive matrices have zero image. Spectral decompositions of Hermitian matrices and complex linearity imply $\Phi=0$. Its adjoint is zero, so (5.13) holds, whereas $\operatorname{Tr}T=0<k$. Directly, every zero-origin function gives zero on both sides, and the constant function one gives trace values $k$ and zero.

For the support assertion, every orthogonal projection $p$ satisfies $0\leq\Phi(p)\leq S=\Phi(I_n)$. If $x\in\ker S$, then $0\leq x^*\Phi(p)x\leq x^*Sx=0$, whence $\Phi(p)x=0$ by its positive square root. Hermiticity also annihilates the corresponding rows. Spectral decomposition therefore puts every image of a Hermitian matrix on $R$, and decomposition into real and imaginary Hermitian parts does so for every complex input. Its right modulus has the same zero block, and spectral calculus proves (6.1), retaining the actual endpoint value even on the ambient complement. If $s=0$, this is simply $f(0)I_k$ on the left and zero on the right.

For $\Phi(z)=zP$, $T=1$ and $r_\Phi=1$, while $\operatorname{Tr}S=1<k$. For $f(0)=0$, spectral calculus gives $f(|\Phi(z)|)=f(|z|)P=\Phi(f(|z|))$ exactly. The constant function one detects failure of the full property. For $\Psi(z)=kzP$, $T=k$, $r_\Psi=1$ and $\operatorname{Tr}\Psi(1)=k$, so Theorem 5.1 applies. These maps exhibit both sides of the ambient trace boundary on the actual singular output space. $\square$

**Corollary 6.2 (Scalar dimensions, identity and transpose).** If $n=1$, write $\Phi(z)=zH$ with $H\geq0$ in $M_k(\mathbb C)$. Its zero-origin property is equivalent to

$$
\operatorname{Tr}H\geq\operatorname{rank}H,
\tag{6.2}
$$

and its full property is equivalent to

$$
\operatorname{Tr}H\geq k.
\tag{6.3}
$$

If $k=1$, every nonzero positive map has the form $\Phi(X)=\operatorname{Tr}(TX)$ with $T\geq0$, and each of the two properties is equivalent to $T\geq I_n$. The zero map remains the additional zero-origin case. The identity and transpose maps on every $M_n(\mathbb C)$ satisfy the full property; for normal inputs their two spectral-calculus matrices agree exactly.

*Proof.* For scalar input, $r_\Phi=\operatorname{rank}H$ and $T$ is the scalar $\operatorname{Tr}H$. Theorems 5.1–5.2 give (6.2) and, since $\operatorname{rank}H\leq k$, (6.3). For scalar output, a nonzero positive functional has $r_\Phi=1$: its rank-one values are scalars and at least one is nonzero. Thus (5.13) becomes $T\geq I_n$. Its trace is then at least $n\geq1$, so the extra ambient inequality for the full property is automatic.

For identity and transpose, $T=I_n$, $r_\Phi=1$, and $k=n$. Positivity of transpose follows, for example, by transposing a positive spectral decomposition: $(uu^*)^{\mathsf T}=\overline u\,\overline u^{\,*}$. Theorem 5.1 applies. If $N=U\operatorname{diag}(z_i)U^*$ is normal, then

$$
N^{\mathsf T}=\overline U\operatorname{diag}(z_i)U^{\mathsf T},\qquad
|N^{\mathsf T}|=\overline U\operatorname{diag}(|z_i|)U^{\mathsf T}
=|N|^{\mathsf T}.
\tag{6.4}
$$

Consequently $f(|N^{\mathsf T}|)=f(|N|)^{\mathsf T}$ for every function in the domain, including its value at zero. Identity gives the same equality without transposes. These calculations use only positivity, rather than an assumption of complete positivity. $\square$

**Corollary 6.3 (Endpoint freedom and zero eigenvalues).** The two characterizations apply to functions discontinuous at zero, including

$$
f(0)=c,\qquad f(t)=c+d\quad(t>0),\qquad c,d\geq0.
\tag{6.5}
$$

More generally, a finite nonnegative concave function on $(0,\infty)$ has a finite right limit $L$ at zero and admits exactly the nonnegative concave endpoint assignments $f(0)=c$ with $0\leq c\leq L$. In Theorem 5.2, the restriction is the assigned value $c=0$, and does not require $L=0$.

*Proof.* The nondecreasingness argument in Convention 1.4 also applies on the open half-line. Hence $L$ exists and is finite, with $0\leq L\leq f(1)$. If $f$ is extended concavely to zero with a nonnegative value $c$, the same monotonicity gives $c\leq L$. Conversely suppose $0\leq c\leq L$. The usual interior continuity of a finite concave function and its concavity, applied between $\varepsilon>0$ and $t>0$ and then letting $\varepsilon\downarrow0$, yield, for $0<\theta<1$,

$$
f(\theta t)\geq(1-\theta)L+\theta f(t)
\geq(1-\theta)c+\theta f(t).
\tag{6.6}
$$

Thus the extension with value $c$ is concave across the endpoint as well; all other pairs were already in its domain. Formula (6.5) is this construction for a constant interior function. These scalar facts are standard concavity facts, here used to specify exactly the endpoint domain of Theorems 5.1–5.2.

In their sufficiency proofs, $g=f-f(0)$ has its assigned value zero at zero, even if its right limit is positive. Lemma 3.1 applies to this $g$ exactly, as the finite-spectral explanation following (3.6) also shows. In (5.6), all zero eigenvalues $z_i=0$ remain in the spectral decomposition. Their $g$-coefficients vanish, but their $E_i$ remain in $S$ in (5.10), and their $f$-coefficients equal $c$. Lemma 4.1 treats the resulting zero coefficients and singular matrices explicitly. Therefore neither a zero input eigenvalue nor a zero output eigenvalue has been replaced by a positive one or by a right-hand-limit convention. $\square$

## 7. Source correspondence and the older questions

**Corollary 7.1 (Relationship to the old Question 1 witness).** Bourin's Question 1 in [arXiv:0805.1954v1](https://arxiv.org/pdf/0805.1954v1), p. 3, concerns positive inputs $M$ and asks whether reflection of positive contractions,

$$
\Phi^{-1}(F_k)\subseteq F_n,\qquad
F_j=\{X\in M_j(\mathbb C):0\leq X\leq I_j\},
\tag{7.1}
$$

implies the concave symmetric-norm inequality. That hypothesis does not imply either property of Theorems 5.1–5.2. The previously supplied witness

$$
\Phi(z)=\operatorname{diag}(z,z/4),\qquad M=1,\qquad f(t)=\sqrt t
\tag{7.2}
$$

fails both properties, already with the zero-origin function in (7.2).

*Proof.* The witness and its contraction-reflection argument are the existing result of the repository sources cited below, and are reused here. If $\Phi(z)$ is a positive contraction, its first diagonal entry gives that $z$ is real and $0\leq z\leq1$. Conversely those scalar inequalities make both entries positive contractions, so $\Phi^{-1}(F_2)=F_1$, with the inverse image taken in the entire complex scalar algebra. Its functional-calculus values are

$$
f(\Phi(1))=\operatorname{diag}(1,1/2),\qquad
\Phi(f(1))=\operatorname{diag}(1,1/4).
\tag{7.3}
$$

Their trace norms are $3/2>5/4$, and their squared Frobenius norms are $5/4>17/16$. Thus the old witness already uses $f(0)=0$. In the present characterization, $r_\Phi=2$ and $T=5/4$, so $T\not\geq r_\Phi I_1$; also $\operatorname{Tr}T=5/4<k=2$. This locates its failure in both exact criteria. Its operator norms in (7.3) are equal to one, a fact about this particular witness, not a universal operator-norm assertion. Theorem 5.1 characterizes all maps for normal inputs, while (7.1) was a proposed sufficient hypothesis even for positive inputs. The extra ambient condition separating Theorems 5.1 and 5.2 is instead witnessed independently by Corollary 6.1. $\square$

**Citation convention 7.2 (Load-bearing supplier and correspondence).** The normal-sum inequality (3.6) is Bourin's published theorem, not a new result of this volume. Its precise supplier is *A matrix subadditivity inequality for symmetric norms*, arXiv:0906.1447v1, Theorem 2.1, pp. 3 and 6–7, with the finite-family statement on p. 7. Its variables are the actual $X_{i\ell}=z_iv_{i\ell}v_{i\ell}^*$, its dimension is $k$, and its scalar function is $g=f-f(0)$ (or $f$ itself in the zero-origin case). The same paper, p. 5, supplies the Ky Fan dominance principle used to turn the resulting eigenvalue-sum inequalities into all-norm inequalities. Its proofs, positive-matrix intermediates, and references to Bourin–Uchiyama, Bourin–Lee, Ando–Zhan, Kosem and Rotfel'd are part of the established subadditivity background. They are not reattributed to the characterization.

The spectral theorem, positive square roots, spectral variational principle, finite Fourier orthogonality, polynomial zero-set fact and elementary scalar concavity are classical intermediate facts. The mathematical contribution asserted here is the characterization in Theorems 5.1–5.2 and its derivation through the projection/adjoint argument, the application to the actual spectral family, and the maximizing-projection argument restoring constants. The attribution is relative to the explicitly identified sources; it is not an assertion of worldwide priority or exhaustive absence of an equivalent theorem elsewhere.

**Citation convention 7.3 (Adjacent external originals).** The following distinctions fix the scope of the cited public originals and of the target.

Bourin, *Matrix Subadditivity Inequalities and Block-Matrices*, [arXiv:0805.1954v1](https://arxiv.org/pdf/0805.1954v1), p. 3, Question 1, is (7.1). Its p. 6, Question 3, instead concerns products and sums of positive powers, including

$$
\|A^{p+q}+B^{p+q}\|\leq\|(A^p+B^p)(A^q+B^q)\|.
\tag{7.4}
$$

Hayajneh–Hayajneh–Kittaneh, *Remarks on some norm inequalities for positive semidefinite matrices and questions of Bourin*, [Mathematical Inequalities & Applications 20 (2017), 225–232](https://files.ele-math.com/articles/mia-20-16.pdf), DOI [10.7153/mia-20-16](https://doi.org/10.7153/mia-20-16), Theorem 2, Corollary 1 and the application on p. 232, give the commuting-positive-pair product comparison and the stated application to Question 3, including the sandwich refinement of (7.4). Those are supplied results, not the normal-input positive-map characterization. Question 4 on p. 6 of arXiv:0805.1954v1 has the crossed products $A^pB^q+B^pA^q$ on the left; it is a separate question and is not a conclusion of Theorems 5.1–5.2.

Bourin–Lee, *Positive linear maps on normal matrices*, [arXiv:2006.09692v1](https://arxiv.org/pdf/2006.09692v1), Proposition 2.1 and Theorem 2.2, compare $|\Phi(N)|$ to unitary-orbit expressions involving $\Phi(|N|)$, notably

$$
|\Phi(N)|\leq\beta\Phi(|N|)
+\frac1{4\beta}V\Phi(|N|)V^*,\qquad\beta>0.
\tag{7.5}
$$

Theorem 2.2 is stated there for $n,m\ne1$; its sharpness assertion has $\beta\geq1/2$. Corollary 2.3 includes weak log-majorization. The proof restricts the given map to the commutative algebra of the spectral projections of the given normal matrix. This restriction and its rank-one congruence representation concern the same map, but are not an assumption that the whole map is completely positive. These unitary-orbit and log-majorization conclusions are different from (5.1). In particular, arbitrary nonnegative scalar concavity does not turn weak log-majorization into the required weak majorization; the difficulty without e-convexity is already exhibited on pp. 3–4 of arXiv:0906.1447v1. No such implication is used here.

Bourin–Shao, *Positive linear maps on Hilbert space operators and noncommutative $L^p$ spaces*, [arXiv:2004.10751v1](https://arxiv.org/pdf/2004.10751v1), §1 and Theorem 2.1, treats related unitary-orbit/geometric-mean estimates and their operator-algebra extensions. Its Hilbert-space and measurable-operator domains are distinct from the finite-matrix characterization here. No infinite-dimensional extension is inferred.

Bourin–Lee, *Unitary orbits of Hermitian operators with convex or concave functions*, [arXiv:1109.2384v1](https://arxiv.org/pdf/1109.2384v1), Theorem 2.1, gives Jensen inequalities with unitary orbits for a unital positive map and Hermitian input with spectrum in an interval; its concave direction is the reverse of its convex direction. Its Theorem 3.1 concerns subadditivity via unitary orbits. Bourin–Hiai, *Jensen and Minkowski inequalities for operator means and anti-norms*, [arXiv:1106.2213v3](https://arxiv.org/pdf/1106.2213v3), Theorem 1.1, similarly gives a concave Jensen lower bound by a mean of two unitary conjugates for a unital positive map; the paper's further targets involve operator means and anti-norms. Neither displayed Jensen theorem is (5.1), and unitality is not imported from them.

Sheybani–Erfanian Omidvar–Moradi, *New inequalities for operator concave functions involving positive linear maps*, [arXiv:1711.04957v2](https://arxiv.org/pdf/1711.04957v2), §2, uses normalized positive maps, strictly positive bounded-interval hypotheses and operator monotonicity or operator concavity in its inequalities. These hypotheses and targets differ from the arbitrary scalar-concave, possibly singular normal-input property (5.1).

Bourin's thesis, *A journey into Matrix Analysis*, [arXiv:2307.03064v1](https://arxiv.org/pdf/2307.03064v1), Chapter 1 §1.2, Chapter 2 and Chapter 3, contains the subadditivity, log-majorization and unitary-orbit Jensen background. These are local correspondences to those topics. Availability of the full thesis does not make these locators an exhaustive classification of its contents or of the literature.

All arXiv references in this volume denote the specified versions. The target is the paragraph after Theorem 3.3 of arXiv:0906.1447v1, not an assertion that an author-version body is byte-identical to a journal version. The attribution makes no assertion about present worldwide openness or exhaustive literature coverage.

**Citation convention 7.4 (Published repository originals).** The repository comparisons and the old witness refer to the following complete published originals at revision `fccba7db52358bbf30bf30a86994ace3b29d9a1b`.

The source of (7.2)–(7.3) is [BourinQuestionOneRefutation.lean](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.lean), with its [Blueprint](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/Blueprint/D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.md), [Scribe source](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/Blueprint/D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.scribe.cs), [Question 1 statement](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/Problems/bourin-2008-matrix-subadditivity-question-1.md), and [Bourin source note](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/Library/QuantumContext/bourin2008matrixsubadditivity.md). The positive-contraction reflection and square-root/Frobenius refutation belong to these suppliers. Their witness is credited and reused, not presented as a new counterexample.

[PositiveMapJensen.lean](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/D5/S3/Quantum/Lieb/PositiveMapJensen.lean), its [Blueprint](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/Blueprint/D5/S3/Quantum/Lieb/PositiveMapJensen.md), and its [Scribe source](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/Blueprint/D5/S3/Quantum/Lieb/PositiveMapJensen.scribe.cs) concern operator-convex continuous functions, positive unital maps and positive inputs, with a Loewner-order conclusion. Their analytic attribution includes the Physlib supplier by Kei Tsukamoto, Kento Mori and Hayata Yamasaki at revision `b9043cc548ef6d63a28454cf3a57fb12a0c2e142`; their spectral-effect and rectangular-dilation intermediates are classical. Neither their public theorem nor their proof-local helpers supply the scalar-concave normal-input characterization, and none is reproved here as new content.

[Exact normal-modulus coefficients and rigidity for rank-one pairs](https://github.com/the-omega-institute/trureturing/blob/fccba7db52358bbf30bf30a86994ace3b29d9a1b/docs/develop/theory/NORMAL_MODULUS_RANK_ONE_RIGIDITY.md) concerns the least $c$ in $|A+B|\leq D+cUDU^*$ for a fixed pair of nonzero rank-one normal matrices, where $D=|A|+|B|$. Its coefficient, extremality and stability retain that fixed-pair domain. They are not a classification of positive maps satisfying (5.1), and the present proof uses no fixed-pair coefficient or rigidity assertion.

## 追加锚（本行以下为增补区）
