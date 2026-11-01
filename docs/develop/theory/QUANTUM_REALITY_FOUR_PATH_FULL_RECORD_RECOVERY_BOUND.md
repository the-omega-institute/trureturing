# Four-path full-record recovery: a quadratic majorant and a diamond lower bound

## 1. The record, protocol class, and normalization

This volume continues the four-path record problem of [QUANTUM-REALITY, Sections 390, 392, and 395–399](QUANTUM-REALITY.md). It establishes a uniform deterministic recovery lower bound using a quadratic majorant specific to that record. The recovery task concerns the entire unknown four-dimensional input, including its correlations with an untouched reference.

**Definition 1.1 (four-path record).** All vector spaces are finite-dimensional complex Hilbert spaces. Write $M_d(\mathbb C)$ for the $d$-by-$d$ complex matrices, $A^\dagger$ for the adjoint, and $A^{\mathsf T}$ for the ordinary transpose. Fix

$$
R_0=
\begin{pmatrix}
1&0\\
0&1\\
1/\sqrt2&1/\sqrt2\\
1/\sqrt2&i/\sqrt2
\end{pmatrix},
\qquad C_0=R_0R_0^\dagger.
\tag{1.1}
$$

If $r_i\in\mathbb C^2$ is the column vector whose entries are the $i$th row of $R_0$, the record coupling is the isometry

$$
V|i\rangle=|i\rangle\otimes|r_i\rangle,
\qquad i=1,2,3,4.
\tag{1.2}
$$

Each $r_i$ has norm one, and $(C_0)_{ij}=\langle r_j|r_i\rangle$. Thus discarding the record gives the Schur channel $X\mapsto C_0\circ X$, where $(A\circ X)_{ij}=A_{ij}X_{ij}$.

**Definition 1.2 (finite deterministic full-record protocol).** Choose an arbitrary integer $k\ge1$, Hermitian positive semidefinite effects $D_1,\ldots,D_k\in M_2(\mathbb C)$ satisfying

$$
\sum_{y=1}^kD_y=I_2,
\tag{1.3}
$$

and arbitrary feedback unitaries $U_1,\ldots,U_k\in U(4)$. The effects act on the full record space $\mathbb C^2$. The system channel after measuring that record and applying the indicated feedback is

$$
\begin{aligned}
C_y&=R_0D_y^{\mathsf T}R_0^\dagger,\\
\Phi(X)&=\sum_{y=1}^kU_y(C_y\circ X)U_y^\dagger,
\qquad X\in M_4(\mathbb C).
\end{aligned}
\tag{1.4}
$$

Every outcome is included in this sum. There is no postselection, upper bound on the finite outcome count, or diagonal restriction on $U_y$.

The transpose in (1.4) follows from the ket convention (1.2): for any record measurement realizing the effect $D_y$, its coefficient on the system matrix unit $|i\rangle\langle j|$ is

$$
\langle r_j|D_y|r_i\rangle
 =\sum_{a,b}\overline{(R_0)_{ja}}(D_y)_{ab}(R_0)_{ib}
 =(R_0D_y^{\mathsf T}R_0^\dagger)_{ij}.
\tag{1.5}
$$

Consequently (1.4) depends on the effects, rather than on a choice of measurement operators realizing each effect. The ordinary transpose cannot be replaced by the adjoint in this convention.

**Definition 1.3 (norms and Choi normalization).** For a vector $v\in\mathbb C^d$, let $\|v\|_{\ell^1}=\sum_i|v_i|$. For a matrix $X$, let $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$ be its trace norm. For a linear map $\Lambda:M_4(\mathbb C)\to M_4(\mathbb C)$, use the unhalved diamond norm

$$
\|\Lambda\|_\diamond
 =\sup_{n\ge1}\ \sup_{\substack{X\in M_n(\mathbb C)\otimes M_4(\mathbb C)\\X\ne0}}
 \frac{\|(\operatorname{id}_{M_n}\otimes\Lambda)(X)\|_1}{\|X\|_1}.
\tag{1.6}
$$

The reference factor $M_n(\mathbb C)$ is untouched. There is no factor $1/2$ in (1.6). Put

$$
|\omega\rangle=\frac12\sum_{i=1}^4|i\rangle\otimes|i\rangle,
\qquad \Pi=|\omega\rangle\langle\omega|.
\tag{1.7}
$$

Thus $\|\omega\|=1$ and $\operatorname{Tr}\Pi=1$. For a channel $\Phi$, its normalized Choi state is $J_\Phi=(\operatorname{id}_{M_4}\otimes\Phi)(\Pi)$. The quantity used below is the overlap $\langle\omega|J_\Phi|\omega\rangle$, without a square root.

## 2. The source-specific quadratic majorant

Set

$$
c=\cos(\pi/8),\qquad s=\sin(\pi/8).
\tag{2.1}
$$

In particular, $0<s<c$, $c^2+s^2=1$, $cs=1/(2\sqrt2)$, $c+s=\sqrt2c$, and $(c-s)^2=2s^2=1-1/\sqrt2$.

**Lemma 2.1 (two-complex-variable majorant).** For every $\xi,\eta\in\mathbb C$,

$$
\left(
\frac{|\xi+\eta|+|\xi-\eta|}{\sqrt2}
+|c\xi+is\eta|+|c\xi-is\eta|
\right)^2
\le (\sqrt2+2c)^2|\xi|^2+(\sqrt2+2s)^2|\eta|^2.
\tag{2.2}
$$

Proof. Both sides are homogeneous of degree two. The zero pair satisfies (2.2); for a nonzero pair it suffices to divide by its Euclidean norm and assume $|\xi|^2+|\eta|^2=1$. Write

$$
\begin{aligned}
p&=|\xi|^2,&q&=|\eta|^2,&p+q&=1,\\
x&=\operatorname{Re}(\xi\overline\eta),&
y&=\operatorname{Im}(\xi\overline\eta),&x^2+y^2&=pq,\\
a&=\sqrt{c^2p+s^2q},&m&=cp+sq.
\end{aligned}
\tag{2.3}
$$

Here $s\le a\le c$, $s\le m\le a$, and direct expansion gives

$$
a^2-m^2=(c-s)^2pq.
\tag{2.4}
$$

We use the elementary concavity estimate

$$
\sqrt{1+u}+\sqrt{1-u}\le2-\frac{u^2}{4},
\qquad -1\le u\le1.
\tag{2.5}
$$

Indeed, the square of the left side is $2+2\sqrt{1-u^2}\le4-u^2$. Taking square roots and applying the tangent bound for the square root once more gives $\sqrt{4-u^2}\le2-u^2/4$.

Let

$$
A=\frac{|\xi+\eta|+|\xi-\eta|}{\sqrt2},
\qquad B=|c\xi+is\eta|+|c\xi-is\eta|.
$$

Since $|\xi\pm\eta|^2=1\pm2x$, (2.5) with $u=2x$ gives

$$
A\le\sqrt2-\frac{x^2}{\sqrt2}.
\tag{2.6}
$$

Similarly, $|c\xi\pm is\eta|^2=a^2\pm2cs\,y$. The argument $u=2cs\,y/a^2$ lies in $[-1,1]$ because

$$
2cs|y|\le2cs\sqrt{pq}\le c^2p+s^2q=a^2.
$$

As $c^2s^2=1/8$ and $a\ge s>0$, (2.5) therefore yields

$$
B\le2a-\frac{y^2}{8a^3}.
\tag{2.7}
$$

Define

$$
\begin{aligned}
I&=\sqrt2+2a,\\
L&=\sqrt{(\sqrt2+2c)^2p+(\sqrt2+2s)^2q}
  =\sqrt{2+4a^2+4\sqrt2m}.
\end{aligned}
\tag{2.8}
$$

Equations (2.6)–(2.7) and $x^2+y^2=pq$ imply

$$
A+B\le I-pq\min\left\{\frac1{\sqrt2},\frac1{8a^3}\right\}.
\tag{2.9}
$$

Also $\sqrt2+2m\le L\le I$. Using (2.4) to rationalize twice gives the exact identity

$$
I-L
 =\frac{4\sqrt2(a-m)}{I+L}
 =\frac{4\sqrt2(c-s)^2pq}{(a+m)(I+L)}.
\tag{2.10}
$$

All denominators are positive. We bound $N=(a+m)(I+L)$ in two ways.

First, $a,m\ge s$ and $L\ge\sqrt2+2m$ give

$$
N\ge(2s)(2\sqrt2+4s)
 =4\sqrt2s+8s^2
 \ge16s^2=8(c-s)^2,
\tag{2.11}
$$

where the second inequality uses $2s\le\sqrt2$. Substitution into (2.10) proves

$$
I-L\le\frac{pq}{\sqrt2}.
\tag{2.12}
$$

For the second bound, $m=(a^2+cs)/(c+s)$ and the arithmetic-geometric mean inequality show

$$
\frac ma\ge\frac{2\sqrt{cs}}{c+s}
 =\sqrt{2\sqrt2-2}>\frac9{10}.
\tag{2.13}
$$

The strict comparison follows by squaring; for example $\sqrt2>281/200$ because $2>(281/200)^2$. Therefore

$$
\begin{aligned}
N&\ge2(a+m)(\sqrt2+a+m)\\
 &\ge\frac{19}{5}\sqrt2\,a+\frac{361}{50}a^2.
\end{aligned}
\tag{2.14}
$$

To compare (2.14) with a cubic in $a$, consider

$$
F(t)=\frac{19}{5}\sqrt2+\frac{361}{50}t
      -32(\sqrt2-1)t^2.
\tag{2.15}
$$

We have $c<15/16$: the rational inequality $\sqrt2<10/7$ gives $c^2=(2+\sqrt2)/4<6/7<225/256$. The polynomial $F$ is concave. Its values at the endpoints of $[0,15/16]$ are positive, since $F(0)>0$ and

$$
F(15/16)=\frac{5583-3892\sqrt2}{160}
 >\frac{5583-3892(10/7)}{160}
 =\frac{161}{1120}>0.
\tag{2.16}
$$

A concave function is bounded below by its endpoint chord on an interval, so $F(a)>0$. Multiplying this inequality by $a>0$ in (2.14) gives

$$
N\ge32(\sqrt2-1)a^3
 =32\sqrt2(c-s)^2a^3.
\tag{2.17}
$$

Now (2.10) implies

$$
I-L\le\frac{pq}{8a^3}.
\tag{2.18}
$$

Combining (2.12) and (2.18) with (2.9) proves $A+B\le L$. Both sides are nonnegative, so squaring proves (2.2). When $pq=0$, (2.10) simply states $I=L$, and the same argument applies. Rescaling removes the normalization. $\square$

## 3. The universal deterministic recovery lower bound

**Theorem 3.1 (all finite full-record POVMs and all unitary feedback).** For every integer $k\ge1$, every Hermitian positive semidefinite family $D_1,\ldots,D_k\in M_2(\mathbb C)$ with $\sum_yD_y=I_2$, and every family $U_1,\ldots,U_k\in U(4)$, the map (1.4) satisfies

$$
\boxed{\ \|\Phi-\operatorname{id}_{M_4(\mathbb C)}\|_\diamond
          \ge1-\cos(\pi/8).\ }
\tag{3.1}
$$

The norm is exactly (1.6), with its supremum over all finite untouched references. Every original outcome is retained.

Proof. Transpose preserves positivity of a Hermitian positive semidefinite matrix: for any $z$, $z^\dagger D_y^{\mathsf T}z=\overline{\bar z^\dagger D_y\bar z}\ge0$. By the finite-dimensional spectral theorem, choose vectors $b_{y\ell}\in\mathbb C^2$ such that

$$
D_y^{\mathsf T}=\sum_\ell b_{y\ell}b_{y\ell}^\dagger.
\tag{3.2}
$$

Use the finite combined index $j=(y,\ell)$ and set

$$
b_j=b_{y\ell},\qquad v_j=R_0b_j,\qquad
K_j=U_y\operatorname{diag}(v_j).
\tag{3.3}
$$

The POVM completeness relation gives $\sum_jb_jb_j^\dagger=I_2$. Furthermore,

$$
(v_jv_j^\dagger)\circ X
 =\operatorname{diag}(v_j)X\operatorname{diag}(v_j)^\dagger,
\qquad \Phi(X)=\sum_jK_jXK_j^\dagger.
\tag{3.4}
$$

This is a decomposition of the original channel. The added spectral index is used only in the proof; each term still has its original $U_y$. This is the feedback-preserving refinement of QUANTUM-REALITY, Proposition 395.2.

Let $\alpha=e^{-i\pi/4}$ and write each $b_j$ in the unitary coordinates

$$
b_j=T\begin{pmatrix}\xi_j\\\eta_j\end{pmatrix},
\qquad
T=\frac1{\sqrt2}
\begin{pmatrix}1&1\\\alpha&-\alpha\end{pmatrix}.
\tag{3.5}
$$

Indeed, $T^\dagger T=I_2$. Completeness becomes

$$
\sum_j
\begin{pmatrix}\xi_j\\\eta_j\end{pmatrix}
\begin{pmatrix}\overline\xi_j&\overline\eta_j\end{pmatrix}=I_2,
\qquad
\sum_j|\xi_j|^2=\sum_j|\eta_j|^2=1.
\tag{3.6}
$$

For any $\xi,\eta$, multiplication of the rows of $R_0T(\xi,\eta)^{\mathsf T}$ by the respective unit phases $1,e^{i\pi/4},e^{i\pi/8},e^{-i\pi/8}$ gives

$$
\begin{pmatrix}
(\xi+\eta)/\sqrt2\\
(\xi-\eta)/\sqrt2\\
c\xi+is\eta\\
c\xi-is\eta
\end{pmatrix}.
\tag{3.7}
$$

For example $(1+\alpha)/2=e^{-i\pi/8}c$ and $(1-\alpha)/2=ie^{-i\pi/8}s$ give the third row; $i\alpha=e^{i\pi/4}$ gives the fourth. These row phases preserve magnitudes. Lemma 2.1 and (3.6) therefore imply the complete-resolution bound

$$
\begin{aligned}
\sum_j\|R_0b_j\|_{\ell^1}^2
&\le (\sqrt2+2c)^2\sum_j|\xi_j|^2
     +(\sqrt2+2s)^2\sum_j|\eta_j|^2\\
&=(\sqrt2+2c)^2+(\sqrt2+2s)^2\\
&=8+4\sqrt2(c+s)=8+8c.
\end{aligned}
\tag{3.8}
$$

Equivalently, (2.2) and (3.7) give, for every $b\in\mathbb C^2$, the pointwise quadratic certificate

$$
\|R_0b\|_{\ell^1}^2\le b^\dagger H b,
\quad
H=T\begin{pmatrix}(\sqrt2+2c)^2&0\\0&(\sqrt2+2s)^2\end{pmatrix}T^\dagger,
\quad \operatorname{Tr}H=8+8c.
\tag{3.9}
$$

Thus (3.8) holds for every finite resolution $\sum_jb_jb_j^\dagger=I_2$, including those arising from effects of arbitrary rank. It uses the common completeness constraint on all branches.

The map $\Phi$ is completely positive by (3.4), and it is trace preserving because

$$
\begin{aligned}
\sum_jK_j^\dagger K_j
 &=\operatorname{diag}\left(\sum_j|(v_j)_i|^2\right)_{i=1}^4\\
 &=\operatorname{diag}\left(
      \left(R_0\Bigl(\sum_jb_jb_j^\dagger\Bigr)R_0^\dagger\right)_{ii}
    \right)_{i=1}^4
 =I_4.
\end{aligned}
\tag{3.10}
$$

Its normalized Choi matrix $J=J_\Phi$ is consequently positive semidefinite with trace one. Since $\langle\omega|(I\otimes K)|\omega\rangle=\operatorname{Tr}K/4$, its overlap with $\Pi$ is

$$
f=\langle\omega|J|\omega\rangle
 =\frac1{16}\sum_j|\operatorname{Tr}K_j|^2.
\tag{3.11}
$$

For every $j=(y,\ell)$, unitarity gives $|(U_y)_{ii}|\le1$. Hence

$$
|\operatorname{Tr}(U_y\operatorname{diag}(v_j))|
 =\left|\sum_i(U_y)_{ii}(v_j)_i\right|
 \le\sum_i|(v_j)_i|.
\tag{3.12}
$$

This is the diagonal-Kraus specialization of Gregoratti–Werner, *Quantum Lost and Found*, [quant-ph/0209025v1, Proposition 8, equations (15)–(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8). In that proposition the uncorrected Kraus operators here are $t_j=\operatorname{diag}(v_j)$, the input dimension is four, and recovery is $X\mapsto U_yXU_y^\dagger$. Its fixed-decomposition bound is $4^{-2}\sum_j(\operatorname{Tr}|t_j|)^2$; here $\operatorname{Tr}|t_j|=\|v_j\|_{\ell^1}$. In particular, (3.12) applies to every original feedback unitary, regardless of its off-diagonal entries. Combining it with (3.8) gives

$$
f\le\frac1{16}\sum_j\|v_j\|_{\ell^1}^2
 \le\frac{1+c}{2}.
\tag{3.13}
$$

Finally, $Z=J-\Pi$ is Hermitian with trace zero. The two effects $\Pi$ and $I-\Pi$ have signed expectation values $f-1$ and $1-f$. The trace-norm bound for such a test gives

$$
\|Z\|_1\ge|\operatorname{Tr}(\Pi Z)|
                   +|\operatorname{Tr}((I-\Pi)Z)|
 =2(1-f).
\tag{3.14}
$$

For completeness, for any positive effect $E$ and Hermitian $Z$, its spectral decomposition yields $|\operatorname{Tr}(EZ)|\le\operatorname{Tr}(E|Z|)$; summing over the two effects proves the inequality. Positivity and trace one of $J$ ensure $0\le f\le1$.

The input $\Pi$ has trace norm one and its four-dimensional reference is allowed in (1.6). Thus

$$
\begin{aligned}
\|\Phi-\operatorname{id}_{M_4}\|_\diamond
&\ge\|(\operatorname{id}_{M_4}\otimes(\Phi-\operatorname{id}_{M_4}))(\Pi)\|_1\\
&=\|J-\Pi\|_1
 \ge2(1-f)\ge1-c.
\end{aligned}
\tag{3.15}
$$

This is the necessary fidelity-to-diamond implication of QUANTUM-REALITY, Proposition 395.2, with total retained weight one. A single admissible reference input supplies a lower bound on the supremum over all references; no restriction of that supremum has been imposed. Substituting (2.1) proves (3.1). $\square$

## 4. Source and hypothesis correspondence

The record (1.1) is the one in QUANTUM-REALITY, Definition 392.1. Its branch convention and full-record POVM interface are those of Section 390. Proposition 395.2 supplies the feedback-preserving refinement and normalized Choi mechanism used inside the proof. Sections 396–398 give support and auxiliary-effect necessary inequalities. The additional quantitative ingredient here is (2.2), or equivalently the quadratic certificate (3.9), whose completeness sum is (3.8). The fixed-decomposition fidelity estimate alone does not supply that sum.

The distinction between record changes and input extensions is essential. QUANTUM-REALITY, Section 399, treats a joint unknown tensor input and joint feedback. Section 403 instead supplies a phase decomposition for the Hadamard cube $C_0^{\circ3}$. Neither changes the matrix or the protocol quantifiers of Theorem 3.1: it concerns the single record $C_0$ of (1.1).

Buscemi, Chiribella, and D’Ariano, *Inverting Quantum Decoherence by Classical Feedback from the Environment*, [quant-ph/0504195v5, Theorem 2 and equation (9)](https://arxiv.org/html/quant-ph/0504195v5), give the four-dimensional rank-two correlation example and its perfect-correction context. Their equation (9) is the entrywise conjugate of (1.1)'s $C_0$: their $(2,4)$ entry is $i/\sqrt2$ and their $(3,4)$ entry is $(1+i)/2$, while ours are $-i/\sqrt2$ and $(1-i)/2$. This agrees with their Heisenberg convention and the Schrödinger convention (1.2)–(1.5). Their Theorem 2 gives the extremal-rank constraint $r\le\sqrt d$ and random-unitary structure for qubit and qutrit decoherence maps. These qualitative statements do not assert the quantitative bound (3.1).

Gregoratti and Werner's [Proposition 8](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8) fixes a Kraus decomposition and permits arbitrary outcome-conditioned recovery channels. The recovery channels in Theorem 3.1 are its unitary special case; refined labels sharing an original outcome retain the same recovery. Its entanglement-fidelity estimate is used within (3.11)–(3.13), without identifying an entanglement-fidelity optimum with a diamond-norm optimum.

Yu, Duan, and Xu, *Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*, [arXiv:1201.1172v1, Lemma 2 and Theorem 2](https://arxiv.org/html/1201.1172v1), study the distance of an uncorrected channel to mixed-unitary competitors. Lemma 2 assumes its Kraus operator space contains no unitary and bounds that distance by a Kraus-space variational quantity; Theorem 2 preserves the bound under tensoring with a Schur channel. This competitor domain is different from (1.4), where a POVM chooses the branches and the feedback is conditioned on the same outcomes. Those results are not substituted for (3.8). The related [repository mixed-unitary distance result](../../../Library/QuantumChannels/yuduanxu2017unitarydistance.md), on equality of distances to all mixed-unitary and Schur mixed-unitary competitors, likewise concerns that other domain.

Finite spectral refinement, the fixed-decomposition correction estimate, and the normalized Choi trace-norm witness are mature intermediate tools, used inside the derivation. The specific additional mathematical content is the proved quadratic majorant and its full-resolution consequence. This source-relative distinction makes no claim of global literature originality or priority for the majorant.

## 5. Attainability and global-minimum boundaries

Theorem 3.1 is a universal lower bound. It does not establish a protocol attaining $1-\cos(\pi/8)$, a matching upper bound on the full diamond error, an optimizing protocol, or an exact global minimum. These conclusions require additional mathematics beyond the lower-bound proof.

In particular, equality in the fixed-Kraus entanglement-fidelity estimate would not alone establish equality in (3.15). The quadratic estimate, completeness sum, actual-feedback trace estimate, two-effect trace-norm inequality, and diamond supremum all have to support any claimed equality. A small normalized Choi error is not an upper bound on the error for every reference input.

The proof uses the exact record (1.1), all-outcome retention, finite POVMs on its full two-dimensional record space, and arbitrary four-dimensional unitary feedback. It proves the inequality for every finite outcome count, without a uniform bound on that count. It does not assert a result for postselected protocols, a different record, a chosen encoding subspace, or a global optimizer obtained by restricting feedback to an ansatz.

## 追加锚（本行以下为增补区）

## 6. Finite attainment for the original full-record problem

**Definition 6.1 (two-outcome protocol for the fixed record).** Keep exactly $R_0$ and $C_0$ from (1.1), the ordinary transpose in (1.4), and the unhalved norm (1.6). Set

$$
\theta=\pi/8,\qquad c=\cos\theta,\qquad s=\sin\theta,
\qquad h=1/\sqrt2,\qquad \alpha=e^{-i\pi/4}.
\tag{6.1}
$$

Choose $k=2$, with outcomes labelled $+$ and $-$, and define the effects

$$
D_+=\frac12\begin{pmatrix}1&\alpha\\\bar\alpha&1\end{pmatrix},
\qquad
D_-=\frac12\begin{pmatrix}1&-\alpha\\-\bar\alpha&1\end{pmatrix},
\tag{6.2}
$$

and feedback matrices

$$
\begin{aligned}
U_+&=\operatorname{diag}
 (1,e^{i\pi/4},e^{i\theta},e^{-i\theta}),\\
U_-&=\operatorname{diag}
 (1,-e^{i\pi/4},-i e^{i\theta},i e^{-i\theta}).
\end{aligned}
\tag{6.3}
$$

These choices use the two columns of the basis $T$ in (3.5), with the phase correction associated to the diagonal Kraus operators in (3.4); the corresponding general polar-correction construction is Gregoratti–Werner, [Proposition 8, equations (18)–(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8). Their feasibility and their full diamond error are established below.

**Theorem 6.2 (an attained exact minimum).** The effects (6.2) are Hermitian positive semidefinite and sum to $I_2$, and (6.3) belongs to $U(4)^2$. For the channel implemented by these same effects and feedback,

$$
\Phi_*(X)=\sum_{\varepsilon\in\{+,-\}}
 U_\varepsilon\bigl((R_0D_\varepsilon^{\mathsf T}R_0^\dagger)
                  \circ X\bigr)U_\varepsilon^\dagger,
\tag{6.4}
$$

both outcomes are retained and

$$
\boxed{\ \|\Phi_*-\operatorname{id}_{M_4}\|_\diamond=1-\cos(\pi/8).\ }
\tag{6.5}
$$

Consequently, over the entire protocol class of Definition 1.2, including arbitrary finite outcome counts and arbitrary unitary feedback,

$$
\min_{\substack{k\ge1,\ D_y\succeq0,\ \sum_yD_y=I_2\\
                 U_y\in U(4),\ 1\le y\le k}}
\left\|\sum_{y=1}^k
 U_y\bigl((R_0D_y^{\mathsf T}R_0^\dagger)\circ\,·\,\bigr)U_y^\dagger
 -\operatorname{id}_{M_4}\right\|_\diamond
=1-\cos(\pi/8).
\tag{6.6}
$$

The lower comparison in this statement is Theorem 3.1, reused without reproof. The construction specializes (3.5)–(3.7) and the polar-correction formula cited in Definition 6.1; the upper comparison is an estimate on every amplified operator.

Proof. Put

$$
b_+=h\begin{pmatrix}1\\\alpha\end{pmatrix},\qquad
b_-=h\begin{pmatrix}1\\-\alpha\end{pmatrix}.
\tag{6.7}
$$

These are exactly the columns of $T$ in (3.5), so they form an orthonormal basis of $\mathbb C^2$. Their conjugates also form an orthonormal basis, and direct comparison with (6.2) gives

$$
D_\varepsilon=\bar b_\varepsilon\bar b_\varepsilon^\dagger,
\qquad D_\varepsilon^{\mathsf T}=b_\varepsilon b_\varepsilon^\dagger,
\qquad \varepsilon\in\{+,-\}.
\tag{6.8}
$$

Thus the two effects are positive rank-one orthogonal projections and $D_++D_-=I_2$. All entries on the diagonals of (6.3) have modulus one, proving $U_+,U_-\in U(4)$. In particular, the vectors multiplying $R_0$ are $b_\varepsilon$, while the measured effects project onto $\bar b_\varepsilon$; this respects the ordinary transpose in (1.4).

For $v_\varepsilon=R_0b_\varepsilon$, multiplication using the unchanged four rows of (1.1) gives

$$
v_+=\begin{pmatrix}
h\\\alpha h\\e^{-i\theta}c\\e^{i\theta}c
\end{pmatrix},\qquad
v_-=\begin{pmatrix}
h\\-\alpha h\\i e^{-i\theta}s\\-i e^{i\theta}s
\end{pmatrix}.
\tag{6.9}
$$

In detail, the last two rows use

$$
\begin{aligned}
\frac{1+\alpha}{2}&=e^{-i\theta}c,&
\frac{1-\alpha}{2}&=i e^{-i\theta}s,\\
\frac{1+i\alpha}{2}&=e^{i\theta}c,&
\frac{1-i\alpha}{2}&=-i e^{i\theta}s.
\end{aligned}
\tag{6.10}
$$

These are the two coordinate-axis instances of (3.7). The Schur-to-Kraus identity (3.4) and the actual unitaries (6.3) now yield

$$
\begin{aligned}
A_+&=U_+\operatorname{diag}(v_+)
     =\operatorname{diag}(h,h,c,c),\\
A_-&=U_-\operatorname{diag}(v_-)
     =\operatorname{diag}(h,h,s,s),\\
\Phi_*(X)&=A_+XA_+^\dagger+A_-XA_-^\dagger.
\end{aligned}
\tag{6.11}
$$

Both summands are the original measurement outcomes. There is no branch removal or conditioning on a successful outcome. Moreover,

$$
A_+^\dagger A_++A_-^\dagger A_-
=\operatorname{diag}(2h^2,2h^2,c^2+s^2,c^2+s^2)=I_4,
\tag{6.12}
$$

so this channel is trace preserving as well as completely positive.

Define complementary system projections and a unitary

$$
P=\operatorname{diag}(1,1,0,0),\qquad
Q=\operatorname{diag}(0,0,1,1),\qquad Z=P-Q.
\tag{6.13}
$$

Then $P+Q=I_4$, $PQ=0$, and $Z^\dagger Z=I_4$. Since $A_+=hP+cQ$, $A_-=hP+sQ$, and $h(c+s)=c$ by (2.1), expansion of (6.11) gives, for every $X\in M_4(\mathbb C)$,

$$
\begin{aligned}
\Phi_*(X)
 &=PXP+QXQ+c(PXQ+QXP)\\
 &=\frac{1+c}{2}X+\frac{1-c}{2}ZXZ^\dagger.
\end{aligned}
\tag{6.14}
$$

This equality describes the channel of the displayed full-record protocol itself; it does not require an extra randomization step.

Fix any integer $n\ge1$ and any operator $X\in M_n(\mathbb C)\otimes M_4(\mathbb C)$. With $W=I_n\otimes Z$, equation (6.14) gives

$$
(\operatorname{id}_{M_n}\otimes(\Phi_*-\operatorname{id}_{M_4}))(X)
=\frac{1-c}{2}(WXW^\dagger-X).
\tag{6.15}
$$

Unitary conjugation preserves the trace norm: indeed $(WXW^\dagger)^\dagger(WXW^\dagger)=WX^\dagger XW^\dagger$, so the eigenvalues of $X^\dagger X$ and hence the singular values of $X$ are unchanged. The trace-norm triangle inequality therefore implies

$$
\begin{aligned}
\|(\operatorname{id}_{M_n}\otimes(\Phi_*-\operatorname{id}_{M_4}))(X)\|_1
&\le\frac{1-c}{2}\bigl(\|WXW^\dagger\|_1+\|X\|_1\bigr)\\
&=(1-c)\|X\|_1.
\end{aligned}
\tag{6.16}
$$

This estimate holds for every finite untouched reference and every operator $X$, without a Hermiticity or positivity assumption. Taking the suprema in precisely (1.6) proves

$$
\|\Phi_*-\operatorname{id}_{M_4}\|_\diamond\le1-c.
\tag{6.17}
$$

The feasibility established in (6.8) and (6.3) places this same channel in the full class of Theorem 3.1. That theorem gives the reverse inequality, proving (6.5). It also bounds every competitor in (6.6), while (6.2)–(6.4) give a finite attaining competitor; hence the infimum is a minimum with the displayed value. This supplies the attainment and exact-minimum conclusions left undecided in Section 5, while retaining the lower bound (3.1) and its full arbitrary-feedback domain. $\square$

## 7. Correspondence and limits of the attaining application

**Proposition 7.1 (source-specific application and its domain).** Theorem 6.2 concerns exactly the record, branch convention, deterministic outcome retention, unknown system space, and reference-inclusive norm of Definitions 1.1–1.3. Its exact-minimum conclusion follows from a member with diagonal feedback and the universal lower comparison, without imposing a diagonal restriction on competing feedback. The intermediate basis and polar correction are existing ingredients; the source-specific consequence is their concrete $C_0$ application (6.2)–(6.17), together with Theorem 3.1. This consequence asserts neither uniqueness of the optimizer nor an extension to postselection, changed records, uncertain controls, or a procedure for acquiring physical outcome probabilities.

Proof. The basis correspondence is literal: $b_+=T(1,0)^{\mathsf T}$ and $b_-=T(0,1)^{\mathsf T}$ for (3.5). Equation (6.8) enforces the same transpose convention as (1.5), and its common completeness relation is $D_++D_-=I_2$ on the entire original record space. Equations (6.9)–(6.11) retain the original $R_0$, use genuine elements of $U(4)$ on all of $M_4$, and sum both outcomes. The projections $P,Q$ in (6.13) only express the resulting channel; they do not restrict its allowed inputs. The reference quantifier and the unhalved normalization are exactly those of (1.6), as shown by (6.15)–(6.17). The universal comparison uses Theorem 3.1, whose competitors have no diagonal-feedback restriction.

For the external correspondence, set $t_\varepsilon=\operatorname{diag}(v_\varepsilon)$ and write $t_\varepsilon=V_\varepsilon|t_\varepsilon|$ for its polar decomposition. All entries in (6.9) are nonzero, so $V_\varepsilon$ is unitary and (6.3) is precisely $V_\varepsilon^\dagger$. Thus $U_\varepsilon t_\varepsilon=|t_\varepsilon|=A_\varepsilon$. This is the specialization of Gregoratti–Werner, [*Quantum Lost and Found*, Proposition 8, equations (18)–(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8), with input and output dimension four and the fixed two-operator decomposition furnished by (6.7). Their proposition concerns optimal corrected entanglement fidelity for a fixed decomposition. Here the additional full diamond comparison is the concrete operator identity (6.14) and its uniform amplified trace-norm estimate (6.16); it is not inferred from fidelity or Choi-overlap equality.

The rank-two correlation example in Buscemi–Chiribella–D’Ariano, [*Inverting Quantum Decoherence by Classical Feedback from the Environment*, equation (9)](https://arxiv.org/html/quant-ph/0504195v5), is the entrywise conjugate of $C_0$, with the Heisenberg/Schrödinger correspondence specified in Section 4. Their Theorem 2 gives the extremal-rank constraint and the qubit/qutrit random-unitary conclusion; neither supplies (6.16). Yu–Duan–Xu, [*Bounds on the distance between a unital quantum channel and the convex hull of unitary channels*, Lemma 2 and Theorem 2](https://arxiv.org/html/1201.1172v1), compare an uncorrected channel with mixed-unitary competitors, a different optimization domain from (1.4). No such change of competitor domain enters (6.6).

The derivation is therefore a source-specific application of the existing basis, polar correction, and elementary norm inequalities, with the lower bound supplied by Theorem 3.1; it does not assert a new general norm theorem or global literature priority. Every premise used for the exact value is displayed above or in the cited existing lower theorem, and no inaccessible manuscript or unpublished protocol claim is a premise. The construction fixes the record, effects, and feedback exactly and proves a channel identity on arbitrary operators; it supplies no additional premise about uncertain physical implementations or access to measured probabilities. $\square$

## 追加锚（本行以下为增补区）
