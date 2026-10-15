# Finite renewal phase channels: full Jordan structure and stationary identification

## 1. Scope, source credit and the structural question

The averaged channel of every finite-gap phase instrument considered here admits an explicit splitting into a nilpotent off-diagonal restriction and an invertible diagonal quotient. This splitting gives its complete complex Jordan basis, including repeated nonzero roots. The entire similarity type is independent of the reset phases. Consequently the complete stationary binary law, even supplemented by the full channel Jordan form and the minimum exact homogeneous memory dimension, does not determine stationary purity.

The owning source is [Real renewal instruments and detector rank II: phase fibers and stationary identification](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_II.md), abbreviated **Source**. Definition 23.1 supplies the exact family. Theorem 23.2 supplies its stationary states, complete classical laws, diagonal quotient and characteristic polynomial; Proposition 23.3 supplies the stationary purity pair; Theorem 23.4 supplies its minimum-memory and unitary-nonequivalence conclusions. These are credited premises, not new results of this volume. Source Section 24 separately supplies a coherent-output identification theorem under stronger, explicitly specified access. Section 10 states that complementary result with its access boundary.

The source-relative contribution is the removal of the actual phase-dependent extension block, the complete lifted Jordan basis and filtrations, the positivity boundary of the constructed intertwiner, and the resulting strengthening of stationary-purity nonidentification. Finite Sylvester equations and cyclic polynomial modules are classical linear-algebra tools; the proofs below give their required forms and their exact application to this family. No worldwide originality or literature-completeness claim is made.

All proofs here are ordinary handwritten mathematics on finite-dimensional complex spaces, not Lean kernel certificates. Source's linked literature and preceding manuscripts are not independently audited here. In particular its minimum-memory theorem is used with its printed hypotheses and conclusion; the external nilpotent-CP bound in its proof is an inherited dependency, not a newly verified theorem. The exposition below supplies the complete interface needed for the new proofs without requiring those nested sources.

## 2. The exact instrument and its credited stationary interface

**Definition 2.1 (The full finite-gap phase family, from Source Definition 23.1).** Let $H\ge1$ be an integer, $d=H+1$, and $K\subseteq\{1,\ldots,H\}$ contain $H$. Choose $p_k>0$ for $k\in K$, with $\sum_{k\in K}p_k=1$, and set $p_k=0$ for every nonnegative integer outside $K$, in particular $p_0=0$. For integers $a\ge0$ put

$$
t(a)=\sum_{k\ge a}p_k,\qquad
\mu=\sum_{k\ge0}(k+1)p_k=\sum_{a=0}^H t(a).
$$

Let $e_0,\ldots,e_H$ be the standard orthonormal basis of $\mathbb C^d$ and $E_{ij}=e_ie_j^*$. For arbitrary phases $\theta_k\in\mathbb R/(2\pi\mathbb Z)$, $k\in K$, define

$$
Se_j=e_{j+1}\quad(j<H),\qquad Se_H=0,\qquad
x_\theta=\sum_{k\in K}\sqrt{p_k}e^{i\theta_k}e_{H-k},\qquad
J_\theta=x_\theta e_H^*.
$$

The outcome-labeled CP instrument and its averaged channel act on the **full complex matrix algebra** $M_d(\mathbb C)$:

$$
\mathcal C_0(A)=SAS^*,\qquad
\mathcal C_{1,\theta}(A)=J_\theta A J_\theta^*
=A_{HH}x_\theta x_\theta^*,\qquad
\mathcal E_\theta=\mathcal C_0+\mathcal C_{1,\theta}.
$$

A density is a positive semidefinite matrix of trace one. For a chronological word $w=b_1\cdots b_n$ and initial density $\sigma$, its probability is

$$
\mathbb P_{\theta,\sigma}(w)
=\operatorname{Tr}\bigl(\mathcal C_{b_n,\theta}\cdots
\mathcal C_{b_1,\theta}(\sigma)\bigr),\qquad
\mathcal C_{0,\theta}=\mathcal C_0,
$$

and the empty word has probability one. A complete stationary binary law consists of all these finite-word probabilities with a stationary initial density. All linear-algebraic dimensions and ranks below are over $\mathbb C$; the operator space has dimension $d^2$.

**Source interface 2.2 (Credited Theorem 23.2).** For Definition 2.1 the averaged channel is trace preserving, and its unique faithful mixed stationary density is

$$
R_\theta=\sum_{j=0}^H S^j x_\theta x_\theta^*(S^*)^j,
\qquad \rho_\theta=R_\theta/\mu,
\qquad (\rho_\theta)_{ii}=t(H-i)/\mu.
$$

The stronger full-complex fixed-space identity, Source (23.13), is part of the premise:

$$
\mathcal E_\theta(A)=A
\quad\Longrightarrow\quad
A=A_{HH}R_\theta\qquad(A\in M_d(\mathbb C)),
\qquad \operatorname{Tr}R_\theta=\mu.
\tag{2.1}
$$

Every word effect is diagonal and independent of $\theta$. For initial densities $\sigma,\omega$ and phases $\theta,\eta$ with the same $H,K,p$, equality of all word probabilities is equivalent to $\sigma_{ii}=\omega_{ii}$ for all $i$. In stationarity the common law is $\mathbb P_p$, with, for an integer $m\ge1$ and nonnegative integers $a,b,g_1,\ldots,g_{m-1},N,k$,

$$
\begin{aligned}
\mathbb P_p(0^a1\,0^{g_1}1\cdots0^{g_{m-1}}1\,0^b)
&=\frac{t(a)t(b)}{\mu}\prod_{j=1}^{m-1}p_{g_j},\\
\mathbb P_p(0^N)&=\frac1\mu\sum_{k\ge N}(k-N+1)p_k\quad(N\ge0),\\
\mathbb P_p(1)&=\mu^{-1},\qquad
p_k=\frac{\mathbb P_p(10^k1)}{\mathbb P_p(1)}\quad(k\ge0).
\end{aligned}
\tag{2.2}
$$

The empty product in the first line is one. The second line includes the empty word. Source also gives

$$
\chi_{\mathcal E_\theta}(z)=z^{d^2-d}f(z),\qquad
f(z)=z^{H+1}-\sum_{k=1}^H p_k z^{H-k}.
\tag{2.3}
$$

These stationary and characteristic-polynomial assertions are reused from Source, not reproved as new claims. A characteristic polynomial specifies eigenvalues and algebraic multiplicities; it does not in general specify Jordan block sizes. Sections 3–5 supply the missing structural proof for the actual operators of Definition 2.1.

## 3. Splitting the actual nilpotent restriction and invertible quotient

**Definition 3.1 (Diagonal coordinates and the extension block).** For Definition 2.1 set $V=\mathbb C^d$ and define complex-linear maps

$$
D:M_d(\mathbb C)\longrightarrow V,\quad
D(A)=(A_{00},\ldots,A_{HH})^{\mathsf T},\qquad
\Delta:V\longrightarrow M_d(\mathbb C),\quad
\Delta(v)=\operatorname{diag}(v).
$$

Put $\mathcal N=\ker D$ and $q_i=p_{H-i}$ for $0\le i\le H$. Define

$$
\begin{aligned}
T:\mathcal N&\longrightarrow\mathcal N,& T(n)&=SnS^*,\\
P:V&\longrightarrow V,& Pe_j&=e_{j+1}\ (j<H),\quad Pe_H=q,\\
u_\theta&=x_\theta x_\theta^*-\Delta(q),&
B_\theta:V&\longrightarrow\mathcal N,\quad B_\theta(v)=v_Hu_\theta.
\end{aligned}
$$

Here $u_\theta\in\mathcal N$ because $|(x_\theta)_i|^2=q_i$. Each $A$ has the unique decomposition $A=n+\Delta(v)$, with $v=D(A)$ and $n=A-\Delta D(A)$.

**Lemma 3.2 (Actual block form, exact nilpotence and quotient inverse).** For every parameter choice of Definition 2.1, the decomposition in Definition 3.1 gives

$$
\mathcal E_\theta(n+\Delta v)=Tn+B_\theta v+\Delta(Pv),
\qquad D\mathcal E_\theta=PD.
\tag{3.1}
$$

The nilpotency order of $T$ is exactly $H$. The map $P$ is invertible, with inverse specified for $w\in V$ by

$$
(P^{-1}w)_H=\frac{w_0}{q_0},\qquad
(P^{-1}w)_{i-1}=w_i-\frac{q_i}{q_0}w_0\quad(1\le i\le H),
\qquad q_0=p_H>0.
\tag{3.2}
$$

Proof. The tick branch vanishes on $\mathcal N$. For $i\ne j$,

$$
T(E_{ij})=
\begin{cases}E_{i+1,j+1},&i,j<H,\\0,&\max(i,j)=H.\end{cases}
$$

Every off-diagonal pair has $\max(i,j)\ge1$, so $T^H=0$. On the other hand $T^{H-1}E_{01}=E_{H-1,H}\ne0$, including $H=1$ where the exponent is zero. Thus the order is exactly $H$. This restriction must be distinguished from the no-tick map on the whole algebra: if $\mathcal L(A)=SAS^*$, then $\mathcal L^{H+1}=0$ while $\mathcal L^H(E_{00})=E_{HH}\ne0$.

For arbitrary $A$, the zeroth diagonal entry of $\mathcal E_\theta(A)$ is $q_0A_{HH}$, and its $i$th diagonal entry for $1\le i\le H$ is $A_{i-1,i-1}+q_iA_{HH}$. These are precisely the coordinates of $PD(A)$. For diagonal input $\Delta(v)$ the off-diagonal output is $v_Hu_\theta$. This proves (3.1), also rechecking the block form credited to Source (23.17)–(23.18). In particular diagonal matrices need not be an invariant subspace.

Solving $Pv=w$ first gives $q_0v_H=w_0$ and then $v_{i-1}+q_iv_H=w_i$. Since $q_0>0$, these equations force exactly (3.2). Substituting (3.2) back gives every coordinate of $Pv=w$, so it is both a right and a left inverse. No other $q_i$ is required to be nonzero; $q_H=p_0=0$ presents no obstruction. $\square$

**Lemma 3.3 (Finite Sylvester equation).** Let $U,V$ be complex vector spaces, let $T:U\to U$ satisfy $T^H=0$ for an integer $H\ge1$, let $P:V\to V$ be invertible, and let $B:V\to U$ be linear. There is exactly one linear map $X:V\to U$ satisfying $XP-TX=B$, namely

$$
X=\sum_{j=0}^{H-1}T^jBP^{-j-1}.
\tag{3.3}
$$

Proof. Every summand has domain $V$ and codomain $U$. Direct multiplication gives

$$
XP=\sum_{j=0}^{H-1}T^jBP^{-j},\qquad
TX=\sum_{j=1}^{H}T^jBP^{-j}.
$$

Their difference is $B-T^HBP^{-H}=B$. If two solutions exist, their difference $Y$ satisfies $YP-TY=0$, hence $Y=TYP^{-1}$. Iterating this identity $H$ times gives $Y=T^HYP^{-H}=0$. The sum is finite and requires neither convergence nor diagonalizability. $\square$

**Theorem 3.4 (Constructed similarity and unique invariant graph).** For every instrument of Definition 2.1 let

$$
X_\theta=\sum_{j=0}^{H-1}T^jB_\theta P^{-j-1}:V\longrightarrow\mathcal N,
\qquad
\iota_\theta(v)=\Delta(v)+X_\theta v,
\qquad W_\theta=\iota_\theta(V).
\tag{3.4}
$$

The map

$$
G_\theta:\mathcal N\oplus V\longrightarrow M_d(\mathbb C),
\qquad G_\theta(n,v)=n+\iota_\theta(v)
$$

is invertible and satisfies

$$
G_\theta^{-1}\mathcal E_\theta G_\theta=T\oplus P.
\tag{3.5}
$$

The space $W_\theta$ is the unique $\mathcal E_\theta$-invariant vector-space complement of $\mathcal N$. For two phases with the same $H,K,p$, the actual operator-space map

$$
L_{\eta,\theta}=I+(X_\eta-X_\theta)D
$$

has inverse $L_{\theta,\eta}$ and intertwines the averaged channels:

$$
\mathcal E_\eta L_{\eta,\theta}=L_{\eta,\theta}\mathcal E_\theta.
\tag{3.6}
$$

Proof. Lemmas 3.2–3.3 give $X_\theta P-TX_\theta=B_\theta$. Since $DX_\theta=0$ and $D\Delta=I_V$, the inverse of $G_\theta$ is

$$
G_\theta^{-1}(A)=\bigl(A-\Delta D(A)-X_\theta D(A),\ D(A)\bigr).
$$

The first component belongs to $\mathcal N$, and substitution in both directions gives the identity. Using (3.1),

$$
\begin{aligned}
\mathcal E_\theta G_\theta(n,v)
&=Tn+TX_\theta v+B_\theta v+\Delta(Pv)\\
&=Tn+X_\theta Pv+\Delta(Pv)=G_\theta(Tn,Pv).
\end{aligned}
$$

This proves (3.5) and invariance of the graph. Equivalently, the shear on actual matrices is $F_\theta=I+X_\theta D$, with inverse $I-X_\theta D$; conjugating by it removes the upper-right block in (3.1).

For any vector-space complement $W$ to $\mathcal N$, $D|_W$ is an isomorphism onto $V$. Injectivity follows from $W\cap\mathcal N=0$; surjectivity follows by decomposing $\Delta(v)$ in $\mathcal N\oplus W$. Consequently $W$ is the graph of a unique $Y:V\to\mathcal N$. If it is invariant, (3.1) applied to $\Delta(v)+Yv$ gives $TY+B_\theta=YP$. Lemma 3.3 forces $Y=X_\theta$, proving uniqueness.

Finally $G_\eta G_\theta^{-1}(A)=A+(X_\eta-X_\theta)D(A)$, giving (3.6) by (3.5). Its inverse is obtained by exchanging $\theta,\eta$, either from the two $G$ maps or because $D(X_\eta-X_\theta)=0$. This constructs similarity of the actual channels, without inferring it from their characteristic polynomials. $\square$

**Proposition 3.5 (Independent column formula and polynomial inverse).** Under Definition 2.1 put

$$
Q(T)=\sum_{i=0}^H q_iT^i,\qquad
R=q_0^{-1}\sum_{i=1}^H q_iT^i\quad\text{on }\mathcal N.
$$

Then

$$
Q(T)^{-1}=q_0^{-1}\sum_{a=0}^{H-1}(-R)^a,
\qquad
X_\theta e_j=T^jQ(T)^{-1}u_\theta\quad(0\le j\le H).
\tag{3.7}
$$

In particular $X_\theta e_H=0$.

Proof. The polynomial $R$ has zero constant term, so it has the form $T$ times a polynomial in $T$. The factors commute and $T^H=0$, hence $R^H=0$. Multiplication of the finite sum by $I+R$ on either side gives $I-(-R)^H=I$. Since $Q(T)=q_0(I+R)$ and $q_0>0$, this proves the inverse formula.

Independently solve the columns of $XP-TX=B_\theta$. On $e_j$ for $j<H$, $B_\theta e_j=0$, and the equation is $Xe_{j+1}=TXe_j$. Writing $c=Xe_0$, this forces $Xe_j=T^jc$ for all $0\le j\le H$, so $Xe_H=0$. On the last column the equation becomes

$$
\sum_{i=0}^H q_iXe_i-TXe_H=u_\theta,
\quad\text{that is,}\quad Q(T)c=u_\theta.
$$

The inverse just proved gives $c=Q(T)^{-1}u_\theta$. Conversely these columns satisfy all the equations, including the last one. Uniqueness in Lemma 3.3 identifies them with (3.4). This second construction again divides only by $p_H$. $\square$

## 4. Every Jordan chain on the full complex matrix algebra

**Definition 4.1 (Jordan convention and root multiplicities).** For an integer $m\ge1$, the block $J_m(\lambda)$ has $\lambda$ on its diagonal, ones immediately above the diagonal and zeros elsewhere. A linearly independent list $a_0,\ldots,a_{m-1}$ satisfying $(A-\lambda I)a_j=a_{j+1}$ for $j<m-1$ and $(A-\lambda I)a_{m-1}=0$ gives this block when ordered as $a_{m-1},\ldots,a_0$. For the polynomial $f$ in (2.3), factor over $\mathbb C$ as

$$
f(z)=\prod_{\lambda\in\Lambda}(z-\lambda)^{m_\lambda},
\qquad m_\lambda\ge1,
\qquad \sum_{\lambda\in\Lambda}m_\lambda=d,
$$

where $\Lambda$ consists of distinct roots. Complex polynomial factorization and polynomial division are used in their ordinary algebraic senses.

**Lemma 4.2 (All off-diagonal band chains).** For Definition 2.1, $T$ has exactly two Jordan blocks $J_m(0)$ for each $1\le m\le H$. An explicit basis consists, for each $1\le r\le H$, of the two lists

$$
E_{0,r},E_{1,1+r},\ldots,E_{H-r,H},
\qquad
E_{r,0},E_{1+r,1},\ldots,E_{H,H-r},
\tag{4.1}
$$

reversed within each list. The zero generalized eigenspace of the full channel $\mathcal E_\theta$ is exactly $\mathcal N$.

Proof. Within each list, $T$ sends a unit to the next and kills the last by Lemma 3.2. Each list has $H-r+1$ independent units. Its span is invariant and its reversed order is a single block $J_{H-r+1}(0)$. Every off-diagonal unit belongs to exactly one of these lists: its offset $|i-j|$ gives $r$, and the order of its indices gives the list. The lists therefore constitute a basis of $\mathcal N$. As $r$ ranges from $1$ to $H$, their lengths range from $H$ to $1$, once for each of the two orientations. This proves all block multiplicities by an actual basis, with total dimension $H(H+1)=d^2-d$.

If $\mathcal E_\theta^n A=0$ for some $n\ge1$, (3.1) gives $P^nD(A)=0$. Since $P$ is invertible, $D(A)=0$. Conversely every element of $\mathcal N$ is killed by $\mathcal E_\theta^H=T^H$ on that subspace. Thus the zero generalized eigenspace is precisely $\mathcal N$; no extra zero chains arise from the quotient. $\square$

**Lemma 4.3 (Cyclicity and the minimal polynomial of the quotient).** For Definition 2.1 the vector $e_0$ is cyclic for $P$, the minimal polynomial of $P$ is $f$, and

$$
\mathbb C[z]/(f)\longrightarrow V,\qquad
[h]\longmapsto h(P)e_0
\tag{4.2}
$$

is a linear isomorphism intertwining multiplication by $z$ with $P$. Every root of $f$ is nonzero.

Proof. The shift columns give $P^je_0=e_j$ for $0\le j\le H$, so these iterates form a basis. Also

$$
P^de_0=Pe_H=q=\sum_{i=0}^H q_iP^ie_0,
\qquad f(z)=z^d-\sum_{i=0}^H q_i z^i.
$$

Thus $f(P)e_0=0$. Since $f(P)$ commutes with $P$, it annihilates each $P^je_0$, hence $f(P)=0$ on $V$. If $r$ has degree less than $d$, the equality $r(P)e_0=0$ is a relation among the basis $e_0,\ldots,e_H$ and forces all coefficients of $r$ to be zero. Dividing any polynomial $h$ by the monic polynomial $f$ now shows

$$
h(P)e_0=0\quad\Longleftrightarrow\quad f\text{ divides }h.
$$

This proves that (4.2) is well-defined and injective; the basis iterates prove surjectivity. Multiplying a polynomial representative by $z$ corresponds exactly to applying $P$. In particular every annihilating polynomial of $P$ is divisible by $f$, while $f$ itself annihilates $P$, proving minimality. Finally $f(0)=-q_0=-p_H\ne0$, excluding zero roots. $\square$

**Lemma 4.4 (Explicit primary chains, including every repeated root).** For Definition 2.1 and the factorization in Definition 4.1 set

$$
g_\lambda(z)=\frac{f(z)}{(z-\lambda)^{m_\lambda}},\qquad
v_{\lambda,j}=(P-\lambda I)^j g_\lambda(P)e_0
\quad(0\le j<m_\lambda).
\tag{4.3}
$$

All the vectors in (4.3), over all $\lambda\in\Lambda$, form a basis of $V$. For each root they give one chain of length exactly $m_\lambda$. Consequently $P$ has exactly one block $J_{m_\lambda}(\lambda)$ at that root.

Proof. Applying $P-\lambda I$ sends $v_{\lambda,j}$ to $v_{\lambda,j+1}$ until the last, and kills the last because $(P-\lambda I)^{m_\lambda}g_\lambda(P)=f(P)=0$.

To prove independence, suppose a relation among all the displayed vectors holds. For each root form

$$
a_\lambda(z)=\sum_{j=0}^{m_\lambda-1}c_{\lambda,j}(z-\lambda)^j
$$

from its coefficients. Lemma 4.3 says that $f$ divides $\sum_\lambda a_\lambda g_\lambda$. Fix one root $\lambda$. Each summand indexed by a different root is divisible by $(z-\lambda)^{m_\lambda}$, as is the total sum. Hence this power divides $a_\lambda g_\lambda$. But $g_\lambda(\lambda)\ne0$, so $g_\lambda$ contains no factor $z-\lambda$; the entire power must divide $a_\lambda$. Since $\deg a_\lambda<m_\lambda$ unless it is zero, $a_\lambda=0$. This holds for every root, so all coefficients vanish.

There are $\sum_\lambda m_\lambda=d$ independent vectors, giving a basis. In particular the last vector of each list is nonzero, and the chain has its asserted exact length. Reversing each list gives the specified Jordan convention. No simplicity of the roots has been assumed. $\square$

**Theorem 4.5 (Complete actual Jordan basis and minimal polynomial).** For every $H,K,p$ and every phase choice of Definition 2.1,

$$
\mathcal E_\theta\ \sim_{\mathbb C}\quad
\left[\bigoplus_{m=1}^H\bigl(J_m(0)\oplus J_m(0)\bigr)\right]
\oplus
\left[\bigoplus_{\lambda\in\Lambda}J_{m_\lambda}(\lambda)\right],
\qquad
m_{\mathcal E_\theta}(z)=z^Hf(z).
\tag{4.4}
$$

An actual Jordan basis in $M_d(\mathbb C)$ consists of the reversed band lists (4.1), together with, for each $\lambda$, the reversed lifted list

$$
w_{\lambda,j}^{\theta}
=\iota_\theta(v_{\lambda,j})
=\Delta(v_{\lambda,j})+X_\theta v_{\lambda,j},
\qquad 0\le j<m_\lambda.
\tag{4.5}
$$

Proof. Theorem 3.4 identifies the channel with $T\oplus P$ through the explicit isomorphism $G_\theta$. Lemma 4.2 supplies a basis for the first summand and Lemma 4.4 supplies a basis for the second. Their images under $G_\theta$ are exactly the displayed matrices. In particular

$$
(\mathcal E_\theta-\lambda I)w_{\lambda,j}^{\theta}
=w_{\lambda,j+1}^{\theta}\quad(j<m_\lambda-1),
\qquad
(\mathcal E_\theta-\lambda I)w_{\lambda,m_\lambda-1}^{\theta}=0.
$$

This proves the complete block list on the whole algebra.

For minimality, a length-$H$ nilpotent chain has minimal polynomial $z^H$: if $r(T)$ kills its initial chain vector, the independent successive vectors force the coefficients of $z^0,\ldots,z^{H-1}$ in $r$ to vanish. Thus any polynomial annihilating the channel must be divisible by $z^H$ from its restriction to $\mathcal N$, and by $f$ from its action on $W_\theta\cong V$. The factors are coprime because $f(0)\ne0$, so their product divides every annihilating polynomial. Conversely $z^Hf(z)$ kills both summands. This proves the second assertion of (4.4). The characteristic polynomial (2.3) is consistent with the blocks, but was not used as a substitute for the basis construction. $\square$

## 5. Exact powers, images and generalized-eigenvalue filtrations

**Theorem 5.1 (All power kernels, images and ranks).** For Definition 2.1 and every integer $n\ge0$, put $a_n=\max(H-n,0)$. With empty spans interpreted as zero,

$$
\begin{aligned}
\ker\mathcal E_\theta^n
&=\operatorname{span}\{E_{ij}:0\le i,j\le H,\ i\ne j,\ \max(i,j)+n>H\},\\
T^n(\mathcal N)
&=\operatorname{span}\{E_{ij}:0\le i,j\le H,\ i\ne j,\ \min(i,j)\ge n\},\\
\operatorname{im}\mathcal E_\theta^n
&=T^n(\mathcal N)\oplus W_\theta,\\
\operatorname{rank}\mathcal E_\theta^n&=d+a_n(a_n+1),\\
\dim\ker\mathcal E_\theta^n&=H(H+1)-a_n(a_n+1).
\end{aligned}
\tag{5.1}
$$

In particular $\ker\mathcal E_\theta^H=\mathcal N$ and $\operatorname{im}\mathcal E_\theta^H=W_\theta$, and these kernels and images stabilize for $n\ge H$. The zero-eigenvalue kernel filtration is literally the same family of subspaces for every phase; the image complement $W_\theta$ need not be.

Proof. From $D\mathcal E_\theta^n=P^nD$, a matrix in the kernel must have zero diagonal because $P^n$ is invertible. On $\mathcal N$, the power is $T^n$. A matrix unit $E_{ij}$ with $i\ne j$ survives precisely when $\max(i,j)+n\le H$, and then its image is $E_{i+n,j+n}$. Distinct surviving units have distinct images, so no cancellation can enlarge the kernel. This proves its asserted span and, by listing the resulting indices, the asserted image of $T^n$.

The direct-sum conjugacy of Theorem 3.4 gives

$$
\operatorname{im}\mathcal E_\theta^n
=G_\theta\bigl(T^n(\mathcal N)\oplus P^n(V)\bigr)
=T^n(\mathcal N)\oplus W_\theta,
$$

where directness follows from $W_\theta\cap\mathcal N=0$. For $0\le n\le H$ there are $H-n+1$ possible surviving indices in each coordinate and the equal pairs must be removed. Their number is $(H-n+1)^2-(H-n+1)=a_n(a_n+1)$. For $n>H$ there are none, again giving $a_n(a_n+1)=0$. Adding the invertible summand of dimension $d$ proves the rank formula; subtracting from $d^2$ proves the kernel dimension. These arguments include $n=0$, giving kernel zero and full image. For $n\ge H$, $T^n=0$, proving stabilization. $\square$

**Theorem 5.2 (Nonzero-root kernel and image filtrations).** For Definition 2.1 fix $\lambda\in\Lambda$ and an integer $n\ge0$. Use the basis (4.5) and put $W_{\theta,\nu}=\operatorname{span}\{w_{\nu,j}^{\theta}:0\le j<m_\nu\}$. Then

$$
\begin{aligned}
\ker(\mathcal E_\theta-\lambda I)^n
&=\operatorname{span}\{w_{\lambda,j}^{\theta}:\max(m_\lambda-n,0)\le j<m_\lambda\},\\
\operatorname{im}(\mathcal E_\theta-\lambda I)^n
&=\mathcal N\oplus\bigoplus_{\nu\in\Lambda\setminus\{\lambda\}}W_{\theta,\nu}
\oplus\operatorname{span}\{w_{\lambda,j}^{\theta}:n\le j<m_\lambda\},\\
\dim\ker(\mathcal E_\theta-\lambda I)^n&=\min(n,m_\lambda),\\
\operatorname{rank}(\mathcal E_\theta-\lambda I)^n&=d^2-\min(n,m_\lambda).
\end{aligned}
\tag{5.2}
$$

For a complex number $\lambda$ outside $\{0\}\cup\Lambda$, all these powers are invertible, with kernel zero and image $M_d(\mathbb C)$.

Proof. Since $\lambda\ne0$, the restriction $T-\lambda I$ is invertible with inverse

$$
-\sum_{j=0}^{H-1}\frac{T^j}{\lambda^{j+1}}.
$$

Indeed multiplying the latter sum by $T-\lambda I$ telescopes to $I-T^H/\lambda^H=I$ on either side. On $W_{\theta,\nu}$ with $\nu\ne\lambda$, the operator is $(\nu-\lambda)I+N_\nu$ with $N_\nu^{m_\nu}=0$, and its inverse is

$$
\sum_{j=0}^{m_\nu-1}\frac{(-1)^jN_\nu^j}{(\nu-\lambda)^{j+1}}.
$$

Multiplication gives $I$ by the same finite geometric identity. Thus those summands contribute their whole spaces to the image and nothing to the kernel for every power.

On $W_{\theta,\lambda}$, the $n$th power sends $w_{\lambda,j}^{\theta}$ to $w_{\lambda,j+n}^{\theta}$ if $j+n<m_\lambda$, and to zero otherwise. The surviving vectors are independent. The killed vectors and the surviving image vectors are exactly the two spans in (5.2). Their dimensions give the formulas. If $\lambda$ is outside the spectrum, the same inverse argument applies to every summand, proving the last assertion. $\square$

## 6. Small horizon, missing gaps and repeated nonzero roots

**Proposition 6.1 (The $H=1$ and singleton-support cases).** When $H=1$, the full Jordan form is $J_1(0)\oplus J_1(0)\oplus J_1(1)\oplus J_1(-1)$. More generally, when $K=\{H\}$, the reset projector is $E_{00}$, $X_\theta=0$, and the nonzero blocks are the scalar blocks at the distinct $(H+1)$st roots of unity; the zero blocks remain the two copies of each size $1,\ldots,H$. Every statement of Sections 3–5 also applies to arbitrary sparse $K$ without alteration.

Proof. At $H=1$, the constraints force $K=\{1\}$ and $p_1=1$. Thus $q=(1,0)^{\mathsf T}$, $x_\theta x_\theta^*=E_{00}$ and $u_\theta=0$, so $B_\theta=X_\theta=0$. The restriction $T$ is zero on the independent units $E_{01},E_{10}$. The quotient exchanges $e_0$ and $e_1$, with eigenvectors $e_0+e_1$ and $e_0-e_1$ at $1$ and $-1$. This yields the stated basis and blocks.

For $K=\{H\}$, $p_H=1$, $x_\theta$ is a scalar phase times $e_0$, and again $u_\theta=0$. Here $f(z)=z^{H+1}-1$. A root $\zeta$ is nonzero and its derivative value $(H+1)\zeta^H$ is nonzero, so all roots are distinct. Theorem 4.5 gives the asserted scalar nonzero blocks and all zero blocks. For general sparse support the spaces $\mathcal N$ and $T$ are unchanged, while the two inverse formulas (3.2) and (3.7) use only $p_H>0$. The proofs impose no positivity on a missing $p_k$, so they cover every such support; neither $H$ nor the number of bands is replaced by $|K|$. $\square$

**Proposition 6.2 (An allowed repeated-root quotient).** Take $H=2$, $K=\{1,2\}$, $p_1=3/4$ and $p_2=1/4$, with arbitrary phases. The nonzero Jordan blocks of $\mathcal E_\theta$ are $J_1(1)$ and $J_2(-1/2)$; its zero blocks are two copies each of $J_1(0)$ and $J_2(0)$.

Proof. The probabilities are strictly positive and sum to one. Hand multiplication gives

$$
\begin{aligned}
(z-1)(z+\tfrac12)^2
&=(z-1)(z^2+z+\tfrac14)\\
&=z^3-\tfrac34 z-\tfrac14=f(z).
\end{aligned}
$$

Thus $-1/2$ has multiplicity two and $1$ has multiplicity one. Lemma 4.4 makes the double root one chain of length two, rather than two length-one chains. Lemma 4.2 gives both zero blocks of each required size. The construction is valid for every phase; no numerical approximation or matrix enumeration enters the conclusion. $\square$

## 7. The actual Jordan data of the published four-dimensional pair

**Theorem 7.1 (Equal-probability specialization on $M_4(\mathbb C)$).** Take $H=3$, $K=\{1,2,3\}$ and $p_1=p_2=p_3=1/3$ in Definition 2.1. Let $\alpha_1,\alpha_2,\alpha_3$ be the roots of $g(z)=3z^3+3z^2+2z+1$. These roots are distinct, nonzero and different from $1$. For every phase choice, in particular for the actual Source Proposition 23.3 pair

$$
\theta^+=(0,0,0),\qquad\theta^-=(\pi,0,0),\qquad
x_+=\frac{e_0+e_1+e_2}{\sqrt3},\qquad
x_-=\frac{e_0+e_1-e_2}{\sqrt3},
$$

the full channel Jordan form is

$$
\begin{aligned}
&J_3(0)\oplus J_3(0)\oplus J_2(0)\oplus J_2(0)
\oplus J_1(0)\oplus J_1(0)\\
&\hspace{2em}\oplus J_1(1)\oplus J_1(\alpha_1)
\oplus J_1(\alpha_2)\oplus J_1(\alpha_3).
\end{aligned}
\tag{7.1}
$$

Its minimal polynomial and all power ranks are

$$
m_{\mathcal E_\theta}(z)=z^3\left(z^4-\frac{z^2+z+1}{3}\right),\qquad
\operatorname{rank}\mathcal E_\theta^n=
\begin{cases}16,&n=0,\\10,&n=1,\\6,&n=2,\\4,&n\ge3.\end{cases}
\tag{7.2}
$$

Proof. The actual quotient and its polynomial are

$$
P=\begin{pmatrix}
0&0&0&1/3\\1&0&0&1/3\\0&1&0&1/3\\0&0&1&0
\end{pmatrix},\qquad
f(z)=z^4-\frac{z^2+z+1}{3}=\frac{(z-1)g(z)}3.
$$

The factorization follows by multiplication: $(z-1)g(z)=3z^4-z^2-z-1$. Since $g(1)=9$ and $g(0)=1$, its roots are neither $1$ nor zero. To exclude a repeated root, suppose $g(\alpha)=g'(\alpha)=0$, where $g'(z)=9z^2+6z+2$. Then

$$
3g(\alpha)-\alpha g'(\alpha)=3\alpha^2+4\alpha+3=0.
$$

Subtracting three times this quadratic from $g'(\alpha)=0$ gives $-6\alpha-7=0$, so $\alpha=-7/6$. But

$$
g'(-7/6)=\frac{49}{4}-7+2=\frac{29}{4}\ne0,
$$

a contradiction. Thus all four roots of $f$ are simple. Theorem 4.5 applies to these actual channels, giving all the zero blocks, the four scalar nonzero blocks and the minimal polynomial. Substitution of $H=3,d=4$ in (5.1) gives ranks $4+3\cdot4=16$, $4+2\cdot3=10$, $4+1\cdot2=6$, and $4$ thereafter. This proves (7.1)–(7.2) from the full-family splitting and bases, without treating Source's characteristic-polynomial equality as Jordan equality. $\square$

**Source interface 7.2 (Credited purity and minimum memory of this pair).** In the family of Theorem 7.1, Source Proposition 23.3 gives $\mu=3$, stationary diagonal $(1,2,3,3)/9$, and

$$
\operatorname{Tr}(\rho_\theta^2)=\frac{37+8\cos\delta}{81},
\qquad \delta=\theta_1-2\theta_2+\theta_3.
\tag{7.3}
$$

Its actual stationary pair is

$$
9\rho_+=\begin{pmatrix}
1&1&1&0\\1&2&2&1\\1&2&3&2\\0&1&2&3
\end{pmatrix},\qquad
9\rho_-=\begin{pmatrix}
1&1&-1&0\\1&2&0&-1\\-1&0&3&0\\0&-1&0&3
\end{pmatrix},
$$

with purities $5/9$ and $29/81$, respectively. The range (7.3) over this stationary family is exactly $[29/81,5/9]$. Faithfulness, stationarity and equality of their entire stationary binary laws are inherited from Source Theorem 23.2. Thus these are states and instruments from the same specified shift/reset construction, not independently selected matrices with matching spectral data.

Source Theorem 23.4 gives minimum complex memory dimension **four** for this law among all **exact finite homogeneous binary CP realizations**. The comparison allows arbitrary Kraus counts and mixed initial densities and assumes neither reset nor stationary initialization in a competitor. It counts all persistent classical, quantum and controller registers influencing future outputs and excludes an uncounted external time-dependent controller. Its stated class and dimension bound are the premise used below; no minimum-memory theorem for arbitrary $H$ is asserted here. Source also proves that $\mathcal E_+$ and $\mathcal E_-$ are not related by memory-unitary conjugation and that the outcome-labeled CP instruments are not unitarily equivalent, even allowing scalar phases on Kraus representatives.

## 8. Exactly what the constructed similarity preserves

**Definition 8.1 (Different equivalence requirements).** A complex-linear similarity of averaged channels is an invertible complex-linear $L:M_d(\mathbb C)\to M_d(\mathbb C)$ with $\mathcal E_\eta L=L\mathcal E_\theta$. A positive map sends every positive semidefinite matrix to a positive semidefinite matrix; complete positivity requires this after tensoring with every finite-dimensional identity map. A quantum channel is completely positive and trace preserving. A positive change of coordinates and an inverse which is also positive are additional requirements, separate from invertibility of $L$ as a vector-space map.

Memory-unitary channel equivalence requires $L=\operatorname{Ad}_U$, where $U$ is unitary on $\mathbb C^d$ and $\operatorname{Ad}_U(A)=UAU^*$. Outcome-labeled memory-unitary instrument equivalence requires the corresponding equation for each CP branch with its label fixed. Classical output-law equivalence concerns the probabilities of chronological branch compositions, not a conjugacy of the averaged maps. These definitions distinguish a channel spectrum or Jordan form from the eigenvalues of a stationary density, a Choi matrix or a tomographically specified process.

**Theorem 8.2 (Diagonal, trace and adjoint preservation; precise positivity boundary).** Fix any $H,K,p$ of Definition 2.1 and any phases $\theta,\eta$. For the particular intertwiner of Theorem 3.4, both $L_{\eta,\theta}$ and its inverse preserve every diagonal entry, trace and adjoint:

$$
DL_{\eta,\theta}=D,\qquad
\operatorname{Tr}L_{\eta,\theta}(A)=\operatorname{Tr}A,\qquad
L_{\eta,\theta}(A^*)=L_{\eta,\theta}(A)^*.
\tag{8.1}
$$

For this constructed map the following are equivalent: it is positive; its inverse is positive; the reset projectors are equal, $x_\eta x_\eta^*=x_\theta x_\theta^*$. If the projectors agree, this map is the identity. If they differ, $E_{00}$ is a positive semidefinite input whose image under either map is not positive semidefinite. Explicitly, with

$$
c=Q(T)^{-1}\bigl(x_\eta x_\eta^*-x_\theta x_\theta^*\bigr)\in\mathcal N,
$$

one has $c\ne0$ and

$$
L_{\eta,\theta}(E_{00})=E_{00}+c,\qquad
L_{\eta,\theta}^{-1}(E_{00})=E_{00}-c.
\tag{8.2}
$$

Proof. Write $Y=X_\eta-X_\theta$. Its image lies in $\mathcal N$, so $DY=0$. The map and its inverse are $I+YD$ and $I-YD$, giving $DL=D$ for each. Since trace is the sum of diagonal entries, both preserve trace on all complex matrices. This preservation of diagonal entries does not assert that a diagonal input remains diagonal.

The entries of $P$ and of its inverse (3.2) are real. Since $u_\theta$ is Hermitian, $B_\theta(\overline v)=(B_\theta v)^*$. Also $T(n^*)=(Tn)^*$. Applying these identities to each term in (3.4) yields

$$
X_\theta(\overline v)=(X_\theta v)^*.
$$

The same holds for $X_\eta$ and hence $Y$. As $D(A^*)=\overline{D(A)}$, both $I+YD$ and $I-YD$ commute with taking adjoints, proving (8.1).

Subtracting the Sylvester equations gives

$$
YP-TY=B_\eta-B_\theta.
$$

If the reset projectors are equal, the right side is zero, and uniqueness in Lemma 3.3 gives $Y=0$, so $L$ and its inverse are the identity and are positive. Conversely, if they differ, their difference lies in $\mathcal N$ because their diagonals are both $q$. Proposition 3.5 gives

$$
Ye_0=Q(T)^{-1}(u_\eta-u_\theta)=c\ne0,
$$

where nonzero follows from the invertibility of $Q(T)$. This proves (8.2). Both outputs are Hermitian by (8.1), have diagonal $(1,0,\ldots,0)$, and have a nonzero off-diagonal part.

For a positive semidefinite matrix $A$, its two-coordinate principal restriction is positive semidefinite and therefore

$$
|A_{ij}|^2\le A_{ii}A_{jj}\quad(i\ne j).
\tag{8.3}
$$

For completeness, if the diagonal entries of that restriction are $a,b\ge0$ and its upper-right entry is $z$, positivity of its quadratic form gives $b-|z|^2/a\ge0$ when $a>0$ by taking the first coordinate $-z/a$ and the second $1$. When $a=0$, allowing the first coordinate to vary in magnitude and phase forces $z=0$. These two cases give (8.3). For diagonal $(1,0,\ldots,0)$, every right side in (8.3) is zero, so all off-diagonal entries must vanish. Thus the only positive semidefinite matrix with that diagonal is $E_{00}$. Neither output in (8.2) is positive semidefinite, proving failure of positivity for both maps. This proves all the equivalences. $\square$

**Proposition 8.3 (Stationary-state transport uses the full complex fixed space).** Under the hypotheses of Theorem 8.2,

$$
L_{\eta,\theta}(\rho_\theta)=\rho_\eta.
\tag{8.4}
$$

This assertion uses no positivity assumption on $L_{\eta,\theta}$.

Proof. Put $A=L_{\eta,\theta}(\rho_\theta)$. Intertwining gives $\mathcal E_\eta(A)=A$, while trace preservation gives $\operatorname{Tr}A=1$. Source's full-complex identity (2.1), originally (23.13), now gives $A=A_{HH}R_\eta$ and $1=A_{HH}\mu$. Hence $A=R_\eta/\mu=\rho_\eta$. Uniqueness only among positive densities would not suffice at this step, because $A$ has not been shown positive before the conclusion. The full fixed-space premise supplies exactly what is needed. $\square$

For the pair of Section 7, the $(0,2)$ entries of the reset projectors are $1/3$ and $-1/3$. Their difference is nonzero, so Theorem 8.2 applies to $L_{-,+}$ and its inverse. They intertwine the averaged channels and send the actual stationary states to one another, yet fail positivity at the specific density $E_{00}$. They therefore are not quantum channels. This claim concerns these constructed intertwiners only; it is not a classification of all possible positive similarities between arbitrary phase choices.

The construction intertwines the sums of the branches. It establishes no equation intertwining the two outcome branches separately. The unitary-nonequivalence of the pair remains the credited Source Theorem 23.4 conclusion: a memory unitary intertwining the averages would carry the unique stationary density to the other one and preserve its purity, contradicting (7.3). Branchwise unitary equivalence would imply that averaged identity after summation. Scalar phases on Kraus representatives do not alter their CP maps.

## 9. Common-source nonidentification with full Jordan data

**Theorem 9.1 (The complete classical law already determines this family's Jordan form).** For realizations in Definition 2.1, the complete stationary binary law determines $H$, every $p_k$, and the full complex Jordan form of the averaged channel. In particular adding that Jordan form to this law supplies no information about the phases within this family.

Proof. By (2.2), the positive denominator $\mathbb P_p(1)=1/\mu$ and the cylinders $10^k1$ determine every $p_k$, including zero values. Since support is finite and $p_H>0$, the largest $k$ for which the recovered $p_k$ is positive is exactly $H$. Thus the law determines $d=H+1$ and the polynomial $f$. Theorem 4.5 determines all zero blocks from $H$ and all nonzero blocks from the exact root multiplicities of $f$. Hence the law determines every block. For fixed $H,K,p$, the law is independent of phases by Source Theorem 23.2 and the same is now proved for the Jordan data. This is a statement inside the exact supplied family, not about all CP realizations of a given classical law. $\square$

**Theorem 9.2 (Stationary purity is not identified by law, full Jordan form and minimum dimension).** There is no function of the triple

$$
\bigl(\text{complete stationary binary law},\;
\text{full complex Jordan form of the averaged channel},\;
\text{minimum exact homogeneous complex memory dimension}\bigr)
\tag{9.1}
$$

which returns stationary purity for every realization in the equal-probability $H=3$ phase family of Section 7. The minimum dimension in this statement is taken over exactly the comparison class in Source interface 7.2. Consequently no such function can succeed on any larger class containing these realizations with the same meaning of minimum dimension. On this one fixed triple the actual stationary-family purity range is $[29/81,5/9]$.

Proof. The two realizations are the explicit $S,J_+,J_-$ instruments of Definition 2.1 and Theorem 7.1, initialized in their own stationary densities in Source interface 7.2. Thus the states, branches and outputs are jointly realized by each one device model. Source Theorem 23.2 gives their identical complete stationary law. Theorem 7.1 gives the same actual full Jordan form (7.1) and minimal polynomial, with no unresolved block-size inference. Source Theorem 23.4 gives the common minimum dimension four in the specified comparison class. All three arguments of a putative function are therefore identical for the two realizations.

Source Proposition 23.3 gives purities $5/9=45/81$ and $29/81$, which are different. A function at one input triple cannot have both values, proving the contradiction. More generally all phases in this equal-probability family share the law, the Jordan form by Theorem 4.5, and the minimum dimension by Source Theorem 23.4. The credited formula (7.3), with $\delta$ ranging over the circle, attains exactly the stated interval at this fixed triple. No independent choice of a density with the same diagonal has been substituted for a stationary state of an actual family member. $\square$

The data in (9.1) do not contain the embedding of the generalized eigenvectors (4.5) into the physical matrix algebra, its positive cone or its Hilbert–Schmidt geometry. Similarity alone also does not specify eigenoperators, stationary-density eigenvalues or quantum intervention responses. Full channel or instrument tomography is richer than these data. Equality of stationary-density spectra is neither assumed for the purity pair nor implied: such equality would make the two sums of squared density eigenvalues, and hence their purities, equal. The conclusion is an exact identification obstruction for the stated observations, not a claim about every richer observation scheme, all-$H$ memory minimality, approximation, finite-bit production or a physical memory advantage. In particular the constant-purity singleton case in Proposition 6.1 is compatible with failure of a recovery function on the broader family.

## 10. The credited coherent-output route and its additional access

**Definition 10.1 (Source Section 24 access, restricted to positive $H=3$).** Specialize Definition 2.1 to $H=3$, $K=\{1,2,3\}$ and **fixed known** $p_1,p_2,p_3>0$ with sum one. These probabilities need not be equal. Write

$$
c_k=\sqrt{p_k}e^{i\theta_k},\qquad
x_\theta=(c_3,c_2,c_1,0)^{\mathsf T},\qquad
q_{\mathrm{tail}}=p_2+p_3,\qquad
\delta=\theta_1-2\theta_2+\theta_3.
$$

An actual observed outcome $1$ heralds the tick; its normalized posterior is $x_\theta x_\theta^*$, independent of the conditional input density. After this observed tick, Source Definition 24.1 assumes the additional ability to apply repeatedly the same fixed isometry

$$
V_\theta\psi=S\psi\otimes|0\rangle+J_\theta\psi\otimes|1\rangle.
\tag{10.1}
$$

Its chronological output flags are retained coherently and accessibly. The branch representatives remain stable across uses, and no inaccessible environment retains which-branch records. There are no intermediate memory interventions or terminal memory measurements. A permitted terminal POVM on the $n$ flags has effects commuting with the total count

$$
N_1^{(n)}=\sum_{r=1}^n |1\rangle\langle1|_r.
$$

Arbitrary measurements within a count sector are allowed, including the relative complex control needed there; no external reference breaking the count symmetry is supplied. For $K_0=S$, $K_1=J_\theta$ and chronological $K_w=K_{b_n}\cdots K_{b_1}$, put

$$
\begin{aligned}
|\Psi_{n,\theta}\rangle&=\sum_{w\in\{0,1\}^n}K_wx_\theta\otimes|w\rangle,\\
\Omega_{n,\theta}&=\operatorname{Tr}_{\mathbb C^4}|\Psi_{n,\theta}\rangle\langle\Psi_{n,\theta}|,\\
T_{n,\theta}&=\sum_{m=0}^n P_m^{(n)}\Omega_{n,\theta}P_m^{(n)},
\end{aligned}
$$

where $P_m^{(n)}$ projects onto words with $m$ ticks. This count-sector twirl is the complete output datum in the stated access class. It is unrelated to the symbol $T$ for the off-diagonal restriction in Section 3.

**Source interface 10.2 (Credited Theorem 24.2, not a new orbit classification).** Under exactly Definition 10.1, Source proves that the following five data or equivalence conditions separate the same phase orbits: equality of $T_{3,\theta}$; equality of the complex number

$$
C_\theta=\langle010|\Omega_{3,\theta}|001\rangle
=p_1p_2+p_2\sqrt{p_1p_3}e^{i\delta};
\tag{10.2}
$$

equality of $e^{i\delta}$; memory-unitary equivalence of averaged channels; and memory-unitary equivalence of outcome-labeled instruments. In this supplied family the unitary gauge is precisely an affine phase difference $\theta'_k-\theta_k=a+bk$ modulo $2\pi$ on $k=1,2,3$. This classification is credited to Source, not reproved or extended to all CP realizations here.

For clarity, the complete datum provided there is

$$
\begin{aligned}
T_{3,\theta}
&=p_3|000\rangle\langle000|+p_2|001\rangle\langle001|
+p_1|010\rangle\langle010|\\
&\quad+C_\theta|010\rangle\langle001|
+\overline{C_\theta}|001\rangle\langle010|.
\end{aligned}
\tag{10.3}
$$

The two interfering words have the same count, so their coherence is accessible under the permitted symmetry. With $A=|001\rangle\langle010|$, the count-preserving observables $X=A+A^*$ and $Y=(A-A^*)/i$ have outcomes $(+1,-1,0)$ and the credited distributions

$$
\begin{aligned}
\Pr(X)&=\left(\frac{p_1+p_2}{2}+\operatorname{Re}C_\theta,
\frac{p_1+p_2}{2}-\operatorname{Re}C_\theta,p_3\right),\\
\Pr(Y)&=\left(\frac{p_1+p_2}{2}+\operatorname{Im}C_\theta,
\frac{p_1+p_2}{2}-\operatorname{Im}C_\theta,p_3\right).
\end{aligned}
\tag{10.4}
$$

A fixed random choice of $X$ or $Y$ with probabilities $1/2$, retaining the setting, gives the six-outcome separating distribution of Source Theorem 24.2. At shorter complete post-tick horizons the credited data are

$$
T_{1,\theta}=|0\rangle\langle0|,\qquad
T_{2,\theta}=q_{\mathrm{tail}}|00\rangle\langle00|+p_1|01\rangle\langle01|,
$$

which do not identify the phase orbit. Thus the least complete horizon in **this access class** is three. Source also proves that all $T_{3,\theta}$ have the same support and are strictly positive there. Finite tensor powers retain that common support, so no measurement on finitely many copies perfectly discriminates two distinct orbits. Distributional injectivity is not zero-error recovery of a continuous phase from finitely many samples.

The heralding premise is actual preparation, not a declared reset without observation. Source proves that from every initial density, monitoring reaches a tick in at most four device applications almost surely, including the tick. Three further coherent uses give its separating trial, with at most seven applications. Reheralding is required before each trial. Coherent flag storage, the measurement apparatus, the setting and outcome registers and the preparation controller are additional resources. The minimum generator memory in Source Theorem 23.4 is not a bound on this apparatus, nor are optimal hardware, time or energy costs asserted.

Source Section 24 also supplies a complementary mirror obstruction: phases $(\pi/2,0,0)$ and $(-\pi/2,0,0)$ at fixed positive $p$ have equal stationary-density spectra and equal pairwise trace overlaps of their actual history posteriors, yet belong to different unitary channel orbits. The oriented coherent datum (10.2) separates them. This mirror pair and its invariant calculations are credited source results, distinct from the unequal-purity pair in Section 7.

The additional access in Definition 10.1 cannot be inferred from a classical CP-instrument interface. Source (24.18) explicitly supplies the alternative dilation

$$
\widetilde V\psi=S\psi\otimes|0\rangle\otimes|r_0\rangle
+J_\theta\psi\otimes|1\rangle\otimes|r_1\rangle,
\qquad \langle r_0,r_1\rangle=0,
$$

with a fresh inaccessible record at each use. It gives the same outcome CP maps while loss of those records removes the inter-word coherence, including the $001/010$ entry. Its classical law therefore does not promise access to (10.2). Stable accessible coherent outputs and the stated within-sector measurements are genuine additional assumptions.

Theorems 4.5 and 9.1 show why the law and Jordan data still carry no phase information even in this positive $H=3$ subcase; Source Theorem 24.2 already gives a separating route with the richer access just stated. No unknown-observable-route claim is made for that subcase. The universal Jordan theorem remains valid for every legal $H,K,p$ and phase in Definition 2.1, including cases outside Source Section 24's coherent identification theorem.

## 11. Source-relative content and remaining boundaries

| Mathematical component | Provenance and exact scope |
| --- | --- |
| Definition 2.1 and Source interface 2.2 | Source Definition 23.1 and Theorem 23.2: full complex instrument, stationary fixed space and law, actual block representation and characteristic polynomial. |
| Sections 3–6 | Repo-derived constructive extension: actual splitting, independent column formula, all Jordan chains, minimal polynomial, exact kernel and image filtrations and legal boundary cases. The general Sylvester and cyclic-module methods are classical tools proved in the forms used here. |
| Source interface 7.2 | Source Proposition 23.3 and Theorem 23.4: actual stationary purity pair and interval, minimum four-dimensional homogeneous memory under the specified competitor class, and unitary nonequivalence. |
| Theorem 7.1 and Sections 8–9 | Repo-derived consequences: full Jordan data for the actual pair, the constructed map's exact positivity boundary and stationary transport, and stronger common-source purity nonidentification. |
| Section 10 | Source Definition 24.1 and Theorem 24.2: coherent-output access, positive $H=3$ orbit identification and classification, exact horizon, finite-copy limit and mirror obstruction. These are complementary inherited results. |

The universal statements concern exact finite-dimensional channels with $p_H>0$ and $p_0=0$ as defined here. The construction divides by $p_H$ and makes no assertion for a degenerate endpoint $p_H=0$ with the old carrier held fixed. No assertion of arbitrary-$H$ minimum memory, general positive-similarity classification or branchwise intertwining by $L_{\eta,\theta}$ is supplied. Only the specific constructed map is classified for positivity.

The identification conclusions distinguish an exact observational obstruction from experimental estimation. They provide neither an operational machine-learning benefit nor an ANN impossibility result. A prospective learning application would need to specify its actual generator family, measured data, access to coherent outputs if used, estimation and noise model, and the target property; this volume supplies no empirical accuracy, generalization, sample-complexity, physical-realization or finite-bit-production conclusion. Its proofs and source premises retain their ordinary handwritten status, with no claim that a source citation certifies its unopened external dependencies.

## 追加锚（本行以下为增补区）
