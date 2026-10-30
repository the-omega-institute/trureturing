# Entrywise Loewner monotonicity on positive-parameter Green matrices

## 1. Definitions and cited premises

Fix an integer $n\ge 1$. For vectors $p,q\in(0,\infty)^n$, define the Green matrix

$$
G(p,q)_{ij}=p_{\min(i,j)}q_{\max(i,j)}\qquad(1\le i,j\le n).
$$

Write $r_i=p_i/q_i$. The matrix is called positive-semidefinite admissible when

$$
0<r_1\le r_2\le\cdots\le r_n,
$$

and strict when all these inequalities are strict. For a real function $h$ on $(0,\infty)$, $h[G]$ denotes entrywise application, and $X\succeq Y$ means that $X-Y$ is positive semidefinite.

The following results are used as cited premises. If $D_q=\operatorname{diag}(q_1,\ldots,q_n)$, $L_{ij}=1$ for $i\ge j$ and $L_{ij}=0$ otherwise, and $\Delta_i=r_i-r_{i-1}$ with $r_0=0$, then Xie, Proposition 2.3, gives

$$
G(p,q)=D_qL\operatorname{diag}(\Delta_1,\ldots,\Delta_n)L^{\mathsf T}D_q.
$$

Xie, Corollary 2.4, gives the displayed weak-ratio criterion for positive semidefiniteness and says that strict ratios are equivalent to positive definiteness. Xie, Theorem 3.1, says that a function

$$
g(t)=\int_{[0,\infty)}t^\alpha\,d\mu(\alpha)
$$

with finite positive Borel $\mu$ and finite integral for every $t>0$ preserves positive semidefiniteness entrywise on this Green class in every order; the zero function is included by taking $\mu=0$. Xie, Theorem 4.1, classifies entrywise Loewner monotonicity when the two matrices have the same $q$ vector.

## 2. Exact classification with unrelated parameter vectors

**Theorem 2.1 (finite-Green companion to the fixed-parameter classification).** Let $f\in C^1((0,\infty);\mathbb R)$. The following are equivalent.

1. For every $n\ge1$, every $p_A,q_A,p_B,q_B\in(0,\infty)^n$ satisfying

   $$
   0<\frac{(p_A)_1}{(q_A)_1}\le\cdots\le\frac{(p_A)_n}{(q_A)_n},\qquad
   0<\frac{(p_B)_1}{(q_B)_1}\le\cdots\le\frac{(p_B)_n}{(q_B)_n},
   $$

   and $A=G(p_A,q_A)$, $B=G(p_B,q_B)$ with $A\succeq B$, one has $f[A]\succeq f[B]$.

2. There are $c\in\mathbb R$ and a finite positive Borel measure $\mu$ on $[0,\infty)$, possibly the zero measure and with no bounded-support assumption, such that

   $$
   f(t)=c+\int_{[0,\infty)}\frac{t^{\alpha+1}-1}{\alpha+1}\,d\mu(\alpha)\qquad(t>0),
   $$

   and the integral is finite for every $t>0$.

The assertion in 1 includes every $n\ge1$, arbitrary unrelated positive $q_A,q_B$, and singular Green matrices arising from weak ratio equalities.

The fixed-$q$ classification, the Green factorization and ratio criterion, the all-orders positive-semidefinite preserver theorem, and the Schur product theorem are cited premises. The varying-$q$ implication is obtained here by the reciprocal interpolation in Sections 2.2–2.4; the common Schur regularizer in Section 2.5 extends it to every singular endpoint. The result is restricted to finite Green matrices with strictly positive parameters, all finite orders, real $C^1$ functions on $(0,\infty)$, and the exact antiderivative representation displayed in Theorem 2.1.

### Proof

#### 2.1. The representation supplies a positive derivative

Assume 2 and put

$$
H_t(\alpha)=\frac{t^{\alpha+1}-1}{\alpha+1}=\int_1^t u^\alpha\,du.
$$

For $T\ge1$ and $\alpha\ge0$,

$$
0\le T^\alpha\le\int_T^{T+1}u^\alpha\,du\le H_{T+1}(\alpha).
$$

Thus finiteness of the assumed integral at $T+1$ implies $\int T^\alpha\,d\mu(\alpha)<\infty$. On a compact interval $[a,b]\subset(0,\infty)$ choose $T\ge\max(1,b+1)$. For $t$ and a sufficiently small increment $h$, the scalar mean-value theorem bounds

$$
\left|\frac{H_{t+h}(\alpha)-H_t(\alpha)}h\right|\le T^\alpha.
$$

Dominated convergence therefore gives

$$
f'(t)=g(t):=\int_{[0,\infty)}t^\alpha\,d\mu(\alpha).
$$

The same domination, applied to $t_k\to t$, proves that $g$ is continuous. When $t<1$, $|H_t(\alpha)|\le1$ because $0\le u^\alpha\le1$ on $[t,1]$; hence no signed-integral issue is hidden in the representation. Xie, Theorem 3.1, now yields

$$
g[C]\succeq0
$$

for every positive-semidefinite positive-parameter Green matrix $C$ of every order, including $g=0$ when $\mu=0$.

#### 2.2. A reciprocal structural lemma

**Lemma 2.2.** Let $K$ be a real symmetric positive-definite tridiagonal matrix with $K_{i,i+1}<0$ for every $i<n$. Then $K^{-1}$ is a strict positive-parameter Green matrix.

**Proof.** Choose $s>\lambda_{\max}(K)$ and set $N=sI-K$. Positive definiteness gives $0<s-\lambda_i(K)<s$ for every eigenvalue, while the hypotheses give $N_{ij}\ge0$ entrywise. Hence

$$
K^{-1}=\sum_{m=0}^{\infty}\frac{N^m}{s^{m+1}}.
$$

Every entry of this sum is strictly positive: for $i\ne j$, the term $m=|i-j|$ contains the product of the strictly positive adjacent entries along the path from $i$ to $j$, and for $i=j$ the term $m=0$ is positive.

Write $C=K^{-1}$ and let $c^{(j)}$ be its $j$th column. For $k<j$, the equation $(Kc^{(j)})_k=0$ is the same second-order homogeneous recurrence for every column, with the coefficient of the next entry equal to $K_{k,k+1}\ne0$. Let $y_i=C_{i,n}$ be the last column. It satisfies this recurrence through row $n-1$. Since $C_{1,n}>0$, define $u_i=y_i/C_{1,n}$ and $v_j=C_{1,j}$. Induction on the recurrence gives $C_{i,j}=u_i v_j$ whenever $i\le j$; symmetry gives the same formula with the indices interchanged. Consequently

$$
C_{ij}=u_{\min(i,j)}v_{\max(i,j)},
$$

with all $u_i,v_i>0$. Thus $C$ is a positive-parameter Green matrix. Since $C$ is positive definite, Xie's ratio criterion makes its ratios $u_i/v_i$ strict. The argument is also valid for $n=1$, where the recurrence is empty. $\square$

#### 2.3. Ordered interpolation for positive-definite endpoints

Let $A\succeq B$ be positive-definite Green matrices, with no common-$q$ assumption. Congruence by $B^{-1/2}$ gives

$$
S=B^{-1/2}AB^{-1/2}\succeq I.
$$

The spectral theorem gives $S^{-1}\preceq I$, hence $A^{-1}\preceq B^{-1}$. Put

$$
D=B^{-1}-A^{-1}\succeq0,\qquad K(t)=(1-t)B^{-1}+tA^{-1},\qquad C(t)=K(t)^{-1}\quad(0\le t\le1).
$$

For a strict Green matrix, every $\Delta_i$ is positive. If $E=L^{-1}$, then $E$ is lower bidiagonal with diagonal entries $1$ and subdiagonal entries $-1$, so Xie's factorization gives

$$
G(p,q)^{-1}=D_q^{-1}E^{\mathsf T}\operatorname{diag}(\Delta_1^{-1},\ldots,\Delta_n^{-1})E D_q^{-1}.
$$

Thus the inverse is tridiagonal and

$$
\bigl(G(p,q)^{-1}\bigr)_{i,i+1}=-\frac{1}{q_iq_{i+1}\Delta_{i+1}}<0.
$$

Both endpoint inverses therefore have strictly negative adjacent entries, and the same is true of their convex combination $K(t)$. Lemma 2.2 says that every $C(t)$ is a strict positive-parameter Green matrix, and $C(0)=B$, $C(1)=A$. Differentiating $K(t)C(t)=I$ gives

$$
C'(t)=-C(t)K'(t)C(t)=C(t)DC(t)\succeq0.
$$

This is the required increasing path inside the strict Green class; its parameter vectors may vary with $t$.

#### 2.4. Entrywise differentiation along the path

The finitely many entries of $C(t)$ are positive and continuous on $[0,1]$, so they lie in a compact subinterval of $(0,\infty)$. Entrywise differentiation gives

$$
\frac{d}{dt}f[C(t)]=g[C(t)]\circ C'(t),
$$

where $\circ$ denotes the Hadamard product. The first factor is positive semidefinite by Section 2.1, the second by Section 2.3, and the Schur product theorem gives

$$
\frac{d}{dt}f[C(t)]\succeq0.
$$

For every $x\in\mathbb R^n$, continuity permits entrywise integration and yields

$$
x^{\mathsf T}(f[A]-f[B])x
=\int_0^1x^{\mathsf T}\bigl(g[C(t)]\circ C'(t)\bigr)x\,dt\ge0.
$$

Thus $f[A]\succeq f[B]$ for positive-definite endpoints. The constant-entry matrix contributed by $c$ cancels between the two endpoints.

#### 2.5. Singular endpoints

Let now $A\succeq B$ be arbitrary admissible Green matrices, allowing weak ratio equalities. Fix $\varepsilon>0$, set $\rho=e^{-\varepsilon}\in(0,1)$, and define

$$
R_{\varepsilon,ij}=\rho^{|i-j|}.
$$

This is $G(p,q)$ with $p_i=\rho^{-i}$ and $q_i=\rho^i$; its ratios are $\rho^{-2i}$, so it is positive definite. If $G=G(p,q)$ is any admissible Green matrix, then

$$
G_\varepsilon:=G\circ R_\varepsilon
$$

is the Green matrix with parameters $p_i\rho^{-i}$ and $q_i\rho^i$. Its ratios $r_i\rho^{-2i}$ are strict because $r_{i+1}\ge r_i>0$ and $\rho^{-2}>1$. Hence $A_\varepsilon$ and $B_\varepsilon$ are positive definite. The Schur product theorem gives

$$
A_\varepsilon-B_\varepsilon=(A-B)\circ R_\varepsilon\succeq0.
$$

Section 2.4 therefore gives $f[A_\varepsilon]-f[B_\varepsilon]\succeq0$. As $\varepsilon\downarrow0$, $R_\varepsilon$ converges entrywise to the all-ones matrix, so $A_\varepsilon\to A$ and $B_\varepsilon\to B$ entrywise. Continuity of $f$ gives convergence of the corresponding entrywise images. Taking the limit of the nonnegative quadratic form for each fixed $x$ proves

$$
f[A]-f[B]\succeq0.
$$

This proves 1 from 2 for every order, every pair of positive parameter vectors, and every singular endpoint.

#### 2.6. Necessity

Assume 1. Fix $n$ and a single $q\in(0,\infty)^n$, and restrict 1 to pairs $A,B$ in that common-$q$ Green family. Xie, Theorem 4.1, applies with exactly the hypothesis $f\in C^1((0,\infty))$ and all finite orders, and supplies the representation in 2, with arbitrary real $c$, a finite positive measure on $[0,\infty)$ (possibly zero), and finiteness of the integral at every $t>0$.

Both implications are proved. The one-dimensional case is included: the adjacency conditions in Lemma 2.2 are empty and the same regularization has a single positive ratio. $\square$

## References

Wei Xie, *Entrywise Positivity Preservers on Green Matrices*, arXiv:2608.18491v1, Proposition 2.3, Corollary 2.4, and Theorems 3.1 and 4.1. The source's Theorem 4.1 is used only for the common-$q$ necessity direction; the unrelated-$q$ monotonicity implication is established above. The Schur product theorem and the spectral theorem are used in their standard finite-dimensional real-symmetric forms.

## 追加锚（本行以下为增补区）
