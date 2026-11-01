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
