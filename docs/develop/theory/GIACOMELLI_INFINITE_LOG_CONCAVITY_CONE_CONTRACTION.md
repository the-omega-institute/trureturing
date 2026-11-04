# Giacomelli's full cone of infinitely log-concave initial data

## 1. Recurrence, iterates and topology

**Definition 1.1 (Initial-data recurrence).** Write $\mathbb N=\{0,1,2,\ldots\}$.
Let $d\ge3$ be an integer and let
$p=(p_0,\ldots,p_{d-1})$ and $q=(q_0,\ldots,q_{d-1})$ be arbitrary vectors
in $\mathbb R^d$. For each initial vector $x=(x_0,\ldots,x_{d-1})\in\mathbb R^d$,
let $a^x$ be the real sequence with
$a^x_j=x_j$ for $0\le j<d$ and

$$
a^x_{n+1}=\sum_{k=0}^{d-1}(p_k n+q_k)a^x_{n-k}
\qquad(n\ge d-1).                                      \tag{1}
$$

All terms are determined uniquely by forward induction: every index $n-k$
on the right-hand side lies between $0$ and $n$. No sign, nonvanishing or
invertibility condition is imposed on the coefficients or the initial data.

**Definition 1.2 (Complete-window iterates and full cone).** For $n\ge0$, put
$A^0_n(x)=a^x_n$. For every $i\in\mathbb N$, define the next level by

$$
A^{i+1}_n(x)
   =A^i_n(x)^2-A^i_{n+1}(x)A^i_{n-1}(x)
\qquad(n\ge i+1).                                     \tag{2}
$$

Thus the domain of level $i$ is $n\ge i$. At level $i+1$ the least
predecessor index is $n-1\ge i$, so every term in (2) belongs to the preceding
level's domain. Define the full initial-data cone by

$$
C_\infty(p,q)
 =\left\{x\in\mathbb R^d:
      A^i_n(x)\ge0\ \text{for every }i\in\mathbb N
                       \text{ and every }n\ge i\right\}.             \tag{3}
$$

Iteration zero is included, so (3) requires the original sequence to be
nonnegative. The set is taken in the initial-data space $\mathbb R^d$ itself,
including the zero vector; no nonzero-data restriction, normalization or
quotient is part of the definition.

The recurrence (1) is equation (3), and the square-minus-product operator
in (2) is Definition 2.1, of P. Giacomelli,
[*Log-Concavity and Infinite Log-Concavity of Linear Recurrent Sequences with
Linear Coefficients via Companion Matrix Methods*, arXiv:2604.14391v1](https://arxiv.org/html/2604.14391v1),
printed pages 2 and 3. The parameter correspondence is literal:
$x=(a_0,\ldots,a_{d-1})$, the coefficients are the same real $p_k,q_k$,
and the recurrence index is the same $n\ge d-1$. Section 7 (1), printed
page 13, writes $C_\infty=\{v_0:L^i(a_n)\ge0\ \forall n,i\}$ and asks
whether it is convex and simply connected for $d\ge3$. That notation leaves
the endpoint convention implicit; (2)–(3) fix its complete-window
interpretation here, including $i=0$. No value at $n<i$ is assigned, and
this choice is not asserted to be the source's uniquely intended endpoint
convention.

**Definition 1.3 (Topology and simple connectedness).** Give $C_\infty(p,q)$
the subspace topology inherited from Euclidean $\mathbb R^d$. A space is
simply connected if it is nonempty and path connected and every loop in it
is null-homotopic. For a subspace $B\subset X$, a strong deformation
retraction of $X$ onto $B$ is a continuous map
$H:X\times[0,1]\to X$ such that $H(x,0)=x$, $H(x,1)\in B$, and
$H(b,t)=b$ for every $b\in B$ and $t\in[0,1]$.
The deformation-retraction and contractibility terminology is as in
Allen Hatcher, [*Algebraic Topology*, Cambridge University Press, 2002,
Chapter 0, p. 4](https://pi.math.cornell.edu/~hatcher/AT/ATch0.pdf).

## 2. Uniform contraction of the full cone

**Theorem 2.1 (Strong deformation retraction and simple connectedness).**
For every integer $d\ge3$ and every $p,q\in\mathbb R^d$, the full set
$C_\infty(p,q)$ in Definition 1.2, with the Euclidean subspace topology,
strongly deformation retracts onto $\{0\}$. In particular it is nonempty,
contractible, path connected and simply connected.

Proof. Fix arbitrary $d,p,q$ as in Definition 1.1. For every
$x\in\mathbb R^d$, every real $\lambda$ and every $n\ge0$, the recurrence
satisfies

$$
a^{\lambda x}_n=\lambda a^x_n.                         \tag{4}
$$

Indeed, (4) holds at each initial index $0\le n<d$. If it holds at all
indices up to $n$, where $n\ge d-1$, then every $n-k$ in (1) is such an
index, and

$$
\begin{aligned}
a^{\lambda x}_{n+1}
 &=\sum_{k=0}^{d-1}(p_k n+q_k)a^{\lambda x}_{n-k}\\
 &=\sum_{k=0}^{d-1}(p_k n+q_k)\lambda a^x_{n-k}\\
 &=\lambda a^x_{n+1}.
\end{aligned}
$$

Forward induction proves (4) for every $n\ge0$; it uses only the homogeneity
of (1), without division or a coefficient sign assumption.

For every $i\in\mathbb N$, every $n\ge i$ and every real $\lambda$, we have

$$
A^i_n(\lambda x)=\lambda^{2^i}A^i_n(x).                 \tag{5}
$$

We prove this simultaneously for all admissible $n$ by induction on $i$.
At $i=0$, it is (4), since $2^0=1$. Suppose (5) holds at level $i$ for all
$n\ge i$. If $n\ge i+1$, the three indices $n-1,n,n+1$ are all at least
$i$. Substituting the induction hypothesis into (2) therefore gives

$$
\begin{aligned}
A^{i+1}_n(\lambda x)
 &=\bigl(\lambda^{2^i}A^i_n(x)\bigr)^2
   -\bigl(\lambda^{2^i}A^i_{n+1}(x)\bigr)
    \bigl(\lambda^{2^i}A^i_{n-1}(x)\bigr)\\
 &=\lambda^{2^{i+1}}
     \bigl(A^i_n(x)^2-A^i_{n+1}(x)A^i_{n-1}(x)\bigr)\\
 &=\lambda^{2^{i+1}}A^{i+1}_n(x).
\end{aligned}
$$

This proves (5) at every level, including the smallest admissible index
$n=i$ at that level. No value below a level's domain has been used. Every
exponent $2^i$ is positive, including the exponent at iteration zero.

The zero initial vector generates the zero sequence by (1); induction in
(2) then gives zero at every admissible iterate. Hence $0\in C_\infty(p,q)$.
If $x\in C_\infty(p,q)$ and $\lambda\ge0$, (5) gives
$A^i_n(\lambda x)\ge0$ for every $i\in\mathbb N$ and $n\ge i$. Thus
$\lambda x\in C_\infty(p,q)$. In particular, the full segment from $0$ to
each $x$ lies in the set: it is star shaped at $0$.

Put $C=C_\infty(p,q)$ and define

$$
H:C\times[0,1]\longrightarrow C,
\qquad H(x,t)=(1-t)x.                                  \tag{6}
$$

The nonnegative-scaling property makes (6) well defined. It is continuous:
$(x,t)\mapsto(1-t)x$ is the restriction of continuous scalar multiplication
in $\mathbb R^d$, its image is contained in $C$, and $C$ has the subspace
topology. Moreover

$$
H(x,0)=x,\qquad H(x,1)=0,\qquad H(0,t)=0.
$$

Consequently (6) is a strong deformation retraction onto $\{0\}$ and a
contraction of $C$. Each path $t\mapsto H(x,t)$ joins $x$ to $0$;
concatenating one such path with the reverse of another joins any two
points of $C$. Thus $C$ is nonempty and path connected.

For the fundamental group, apply the classical deformation-retraction
isomorphism in Hatcher, *Algebraic Topology*,
[Chapter 1, Proposition 1.17, p. 36](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf),
with $X=C$, $A=\{0\}$ and basepoint $0$. The homotopy is precisely (6),
with its endpoint and fixed-point properties displayed above. The theorem
requires no manifold, local-connectivity or CW-complex hypothesis. It gives

$$
\pi_1(C,0)\cong\pi_1(\{0\},0)=0.
$$

Since $C$ is path connected, change of basepoint along a path, as in
Hatcher, Chapter 1, Proposition 1.5, p. 28, gives the same trivial
fundamental group at every basepoint. Every loop is therefore
null-homotopic, so $C$ is simply connected. The contraction and the
fundamental-group consequences used here are classical topology applied
to the explicitly defined full cone. Since $d,p,q$ were arbitrary, the
conclusion holds for every coefficient pair and every integer $d\ge3$.
$\square$

## 追加锚（本行以下为增补区）
