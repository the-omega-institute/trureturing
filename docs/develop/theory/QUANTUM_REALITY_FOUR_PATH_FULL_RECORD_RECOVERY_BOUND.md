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

## 8. A homogeneous equality gap for complete refinements

**Definition 8.1 (certificate coordinates and ray distance).** Let $T$ be the unitary in (3.5). For a finite family $b_j\in\mathbb C^2$, write

$$
b_j=T\begin{pmatrix}\xi_j\\\eta_j\end{pmatrix},
\qquad p_j=|\xi_j|^2,\qquad q_j=|\eta_j|^2,
\qquad w_j=p_j+q_j=\|b_j\|^2.
\tag{8.1}
$$

Let

$$
\mathcal E=T(\mathbb C\times\{0\})\ \cup\ T(\{0\}\times\mathbb C)
\tag{8.2}
$$

be the union of the two extremal complex rays. Since $T$ is unitary, the squared Euclidean distance from $b_j$ to $\mathcal E$ is

$$
d_j^2=\operatorname{dist}(b_j,\mathcal E)^2=\min\{p_j,q_j\}.
\tag{8.3}
$$

For the pointwise certificate of (3.9), put

$$
\delta(b)=b^\dagger H b-\|R_0b\|_{\ell^1}^2.
\tag{8.4}
$$

Whenever $w_j=0$, interpret $p_jq_j/w_j$ as zero. The same convention applies to an individual vector with coordinates $p,q,w$.

**Theorem 8.2 (homogeneous gap and ordinary aggregate distance).** For every nonzero $b=T(\xi,\eta)^{\mathsf T}\in\mathbb C^2$, put $p=|\xi|^2$, $q=|\eta|^2$, and $w=p+q=\|b\|^2$. Then

$$
\delta(b)\ge \frac{pq}{800w}
\ge\frac{\operatorname{dist}(b,\mathcal E)^2}{1600}.
\tag{8.5}
$$

At $b=0$ all three quantities are zero under the stated convention. Equality in the certificate $\delta(b)=0$ holds exactly for $b\in\mathcal E$. For every finite family the first two bounds below hold; if it is a complete resolution $\sum_j b_jb_j^\dagger=I_2$, the third holds as well:

$$
\begin{aligned}
\sum_j\frac{p_jq_j}{w_j}&\le800\sum_j\delta(b_j),\\
\sum_j d_j^2&\le1600\sum_j\delta(b_j),\\
\sum_j p_jq_j&\le800\sum_j\delta(b_j)
\quad\text{if }\sum_jb_jb_j^\dagger=I_2.
\end{aligned}
\tag{8.6}
$$

For a protocol of Definition 1.2, use exactly the refinement (3.2)--(3.4), with the same original $U_y$ on every spectral piece of outcome $y$. If $\varepsilon\in[0,1]$ and
$\|\Phi-\operatorname{id}_{M_4}\|_\diamond\le1-c+\varepsilon$, then

$$
\begin{aligned}
\sum_j d_j^2&\le12800\varepsilon,\\
\sum_j p_jq_j&\le6400\varepsilon,\\
\sum_j d_j^4&\le6400\varepsilon.
\end{aligned}
\tag{8.7}
$$

In particular, the ordinary aggregate squared distance has a constant independent of the finite outcome count. These are estimates for certificate vectors of the actual protocol, rather than estimates in a channel norm.

Proof. The homogeneity of (8.4) allows us to assume $p+q=1$ when $b\ne0$, where $p=|\xi|^2$, $q=|\eta|^2$. Use the notation $x,y,a,m,I,L,A,B$ from (2.3) and (2.8). Equations (2.6) and (2.7) give

$$
A+B\le I-d,
\qquad
d=\frac{x^2}{\sqrt2}+\frac{y^2}{8a^3}
\ge pq\min\left\{\frac1{\sqrt2},\frac1{8a^3}\right\}.
\tag{8.8}
$$

The exact identity (2.10) can be written

$$
I-L=\gamma(a,p,q)\,pq,
\qquad
\gamma(a,p,q)=\frac{4\sqrt2(c-s)^2}{(a+m)(I+L)}.
\tag{8.9}
$$

We first obtain a uniform lower gap between the two coefficients in (8.8) and (8.9). Put $e=(c-s)^2=2s^2$. Since $a,m\ge s$ and $L\ge\sqrt2+2m$, the denominator in (8.9) obeys

$$
(a+m)(I+L)\ge4\sqrt2s+8s^2.
\tag{8.10}
$$

The elementary radical inequality

$$
4\sqrt2s+8s^2\ge8\sqrt2e
\tag{8.11}
$$

follows from $e=2s^2$ and $\sqrt2+2s\ge4\sqrt2s$; after squaring the latter positive inequality it is $17\sqrt2\ge24$, which follows from $2>(24/17)^2$. Hence $\gamma(a,p,q)\le1/2$.

If $a\le3/5$, then $1/(8a^3)\ge125/216$, and $1/\sqrt2\ge125/216$. Therefore

$$
\min\left\{\frac1{\sqrt2},\frac1{8a^3}\right\}-\gamma(a,p,q)
\ge\frac{125}{216}-\frac12>\frac1{800}.
\tag{8.12}
$$

For $a\ge3/5$, the second denominator estimate in the proof of Lemma 2.1 gives

$$
(a+m)(I+L)\ge\frac{19}{5}\sqrt2\,a+\frac{361}{50}a^2.
\tag{8.13}
$$

Let

$$
F(t)=\frac{19}{5}\sqrt2+\frac{361}{50}t
      -\frac{3200}{99}\sqrt2 e\,t^2.
\tag{8.14}
$$

This is concave. On $[3/5,c]$ its endpoint values are positive. To check this without approximation, use

$$
\frac75<\sqrt2<\frac{99}{70},
\qquad \frac9{10}<c<1,
\qquad c^2=\frac{2+\sqrt2}{4}<\frac{239}{280},
\tag{8.15}
$$

which give

$$
F(3/5)>\frac{2413}{250}-\frac{83520}{17325}>0,
\qquad
F(c)>\frac{5909}{500}-\frac{55448}{4851}>0.
\tag{8.16}
$$

Concavity then gives $F(t)>0$ throughout the interval. Combining (8.13)--(8.14) yields

$$
(a+m)(I+L)\ge\frac{3200}{99}\sqrt2 e\,a^3,
\qquad
\gamma(a,p,q)\le\frac{99}{800a^3}.
\tag{8.17}
$$

On this range $8a^3\ge216/125>\sqrt2$, so the minimum below is its second entry. Since $a\le c<1$, (8.17) implies

$$
\min\left\{\frac1{\sqrt2},\frac1{8a^3}\right\}-\gamma(a,p,q)
\ge\frac1{8a^3}-\frac{99}{800a^3}
=\frac1{800a^3}\ge\frac1{800}.
\tag{8.18}
$$

Equations (8.8), (8.9), (8.12), and (8.18) therefore give

$$
L-(A+B)\ge\frac{pq}{800}.
\tag{8.19}
$$

Because $L^2\ge2$, $L+A+B\ge1$, and the defect is

$$
\delta(b)=L^2-(A+B)^2=(L-(A+B))(L+A+B),
$$

we obtain $\delta(b)\ge pq/800$ in the normalized case. For an arbitrary nonzero vector let $\widehat b=b/\sqrt w$. Its squared coordinate magnitudes are $p/w$ and $q/w$, while $\delta(\widehat b)=\delta(b)/w$. Hence

$$
\frac{\delta(b)}w
\ge\frac{pq}{800w^2},
\qquad
\delta(b)\ge\frac{pq}{800w}.
$$

If $p\le q$, then $pq/(p+q)\ge p/2$; the reverse ordering gives $pq/(p+q)\ge q/2$. Together with (8.3), this proves the second inequality in (8.5). On a normalized coordinate axis, the explicit expressions (3.7) give $A=\sqrt2$ and $B=2a$, while (2.10) gives $I=L$. Thus $\delta=0$ on both axes, and degree-two homogeneity gives equality on both entire complex rays and at zero. If $pq>0$, the first lower bound in (8.5) is positive. These are therefore exactly the certificate equality cases.

Summing the two bounds in (8.5) proves the first two lines of (8.6). For a complete resolution, positivity of the other summands gives $b_jb_j^\dagger\preceq I_2$, whence $w_j=\|b_j\|^2\le1$. Consequently $p_jq_j\le p_jq_j/w_j$ whenever $w_j>0$; zero vectors contribute zero to both quantities. This proves the third line of (8.6).

For the asserted protocol consequence, keep the actual $K_j=U_y\operatorname{diag}(R_0b_j)$ of (3.3). Write $f$ for its overlap (3.11), and put

$$
\tau_j=\|R_0b_j\|_{\ell^1}^2-|\operatorname{Tr}K_j|^2\ge0,
\qquad \Delta=\frac{1+c}{2}-f\ge0.
$$

The nonnegativity is (3.12)--(3.13), applied to these same feedback unitaries. Completeness, (3.9), and (3.11) give the identity

$$
\sum_j\delta(b_j)+\sum_j\tau_j
=\operatorname{Tr}H-16f=16\Delta.
$$

The existing lower witness (3.15) and the near-optimality premise imply
$2(1-f)\le1-c+\varepsilon$, hence $\Delta\le\varepsilon/2$. Thus $\sum_j\delta(b_j)\le8\varepsilon$, with no replacement or optimization of the feedback. Equations (8.6) and $d_j^4=\min(p_j,q_j)^2\le p_jq_j$ now prove (8.7). $\square$

**Proposition 8.3 (proportional refinement and the actual defect).** Replace any vector $b$ in a finite family by proportional pieces $t_1b,\ldots,t_rb$, where $r\ge1$, $t_\ell\in\mathbb C$, and $\sum_\ell|t_\ell|^2=1$. This preserves its contribution to completeness and to each of

$$
\sum_j\delta(b_j),\qquad
\sum_j d_j^2,\qquad
\sum_j\frac{p_jq_j}{w_j}.
$$

When this is a refinement of (3.3)--(3.4) retaining the same original outcome and feedback $U_y$ on every piece, it preserves the actual channel and $\sum_j\tau_j$ as well. The contributions to the quartic sums $\sum_jp_jq_j$ and $\sum_jd_j^4$ are instead multiplied by $\sum_\ell|t_\ell|^4\le1$.

Proof. For the pieces, $p_\ell=|t_\ell|^2p$, $q_\ell=|t_\ell|^2q$, and $w_\ell=|t_\ell|^2w$. Degree-two homogeneity of (8.4) gives $\delta(t_\ell b)=|t_\ell|^2\delta(b)$; (8.3) gives the same scaling for squared ray distance. For $t_\ell\ne0$ and $w>0$,

$$
\frac{p_\ell q_\ell}{w_\ell}
=|t_\ell|^2\frac{pq}{w}.
$$

Zero pieces and the zero vector satisfy the same identity under the convention of Definition 8.1. Summation proves the three aggregate conservation statements, while
$\sum_\ell(t_\ell b)(t_\ell b)^\dagger=bb^\dagger$ proves completeness conservation. The corresponding actual Kraus operators are $t_\ell K$, since the original $U_y$ remains common. Hence

$$
\sum_\ell(t_\ell K)X(t_\ell K)^\dagger=KXK^\dagger
$$

for every $X$, and both terms defining $\tau$ scale by $|t_\ell|^2$. This proves the channel and trace-defect assertions. Finally, each quartic contribution scales by $|t_\ell|^4$. The inequality $\sum_\ell|t_\ell|^4\le(\sum_\ell|t_\ell|^2)^2=1$ proves the stated decrease. In particular, $r$ equal pieces $b/\sqrt r$ preserve the actual total defect and the ordinary aggregate squared distance, while dividing the quartic contributions by $r$. The ordinary aggregate bound (8.6) is therefore compatible with arbitrary proportional refinement. $\square$

The coefficient separation (8.12) and (8.18) strengthens the source-specific certificate of Lemma 2.1. Its protocol application uses the actual-feedback trace estimate (3.12), the fixed-decomposition estimate cited there from Gregoratti--Werner, Proposition 8, rather than a new fidelity-to-diamond upper bound. Theorem 3.1 supplies the existing lower witness, and the attaining channel remains the one in Theorem 6.2. No global literature-priority claim is made for this equality-gap argument.

Theorem 8.2 controls the certificate vectors in the actual feedback-preserving refinement, including an ordinary aggregate squared-distance bound. At exact optimality every nonzero refined vector lies on one of the two certificate rays. What remains unproved is the control of the actual corrected Kraus operators, with their common feedback across spectral pieces, that would turn the two defect budgets into a bound on $\|\Phi-\Phi_*\|_\diamond$, uniform over every finite outcome count, arbitrary $U(4)$ feedback, and every finite untouched reference. This section establishes neither implemented-channel uniqueness at $\varepsilon=0$, qualitative channel stability, nor the quantitative square-root rate.

The unresolved assertion is that there exists a finite $K>0$ such that, for every protocol of Definition 1.2 and every $\varepsilon\in[0,1]$,

$$
\|\Phi-\operatorname{id}_{M_4}\|_\diamond\le1-c+\varepsilon
\quad\Longrightarrow\quad
\|\Phi-\Phi_*\|_\diamond\le K\sqrt\varepsilon.
$$

Here $\Phi_*$ is exactly (6.14), $K$ is independent of all effects, feedback and finite outcome counts, and both norms are the unhalved norm (1.6), including every finite untouched reference. The record (1.1) and retention of every original outcome remain fixed.

## 追加锚（本行以下为增补区）

## 9. Optimizer-channel uniqueness and qualitative stability

Keep the exact record $R_0,C_0$ of (1.1), the branch convention (1.4), and the unhalved, reference-inclusive diamond norm (1.6). Throughout this section, put

$$
c=\cos(\pi/8),\qquad q=1-c,
\qquad
\Phi_* (X)=PXP+QXQ+c(PXQ+QXP),
\tag{9.1}
$$

where $P,Q$ are the fixed projections (6.13). Thus $\Phi_*$ is exactly the channel of Theorem 6.2, with no optimization over its choice. Theorems 3.1 and 6.2 supply the lower bound $q$ and its finite attainment. The equality characterization of Theorem 8.2 will supply the additional rigidity needed here; its proof is not repeated.

**Definition 9.1 (normalized effect measures).** Write

$$
\operatorname{Dens}_2
 =\{E\in M_2(\mathbb C):E=E^\dagger,\ E\succeq0,\ \operatorname{Tr}E=1\},
\qquad
\mathcal K=\operatorname{Dens}_2\times U(4).
\tag{9.2}
$$

For an original protocol of Definition 1.2, omit its zero effects and set, for every remaining outcome,

$$
t_y=\operatorname{Tr}D_y>0,\qquad E_y=D_y/t_y,
\qquad
\mu=\sum_{y:D_y\ne0}t_y\,\delta_{(E_y,U_y)}.
\tag{9.3}
$$

Here $\delta_{(E,U)}$ denotes a point mass, distinct from the certificate defect $\delta(b)$ of (8.4). A positive semidefinite effect of trace zero is zero, and its summand in (1.4) is zero for every feedback unitary. Omitting it changes neither the channel nor the completeness relation and imposes no condition on its feedback. All outcomes with nonzero contribution remain present.

Let $\mathcal M$ be the following set of positive finite Borel measures on $\mathcal K$:

$$
\mathcal M
 =\left\{\mu\ge0:\ \mu(\mathcal K)=2,
                    \quad\int_{\mathcal K}E\,d\mu(E,U)=I_2\right\}.
\tag{9.4}
$$

The measure (9.3) belongs to $\mathcal M$, since $\sum_y t_y=\operatorname{Tr}I_2=2$ and $\sum_y t_yE_y=I_2$. The unitary in each atom is the actual original $U_y$, shared by all pieces of that outcome; it is not replaced by feedback optimized after a refinement.

For an atom and a measure define the linear maps

$$
\begin{aligned}
G_{(E,U)}(X)
 &=U\bigl((R_0E^{\mathsf T}R_0^\dagger)\circ X\bigr)U^\dagger,\\
\Phi_\mu(X)
 &=\int_{\mathcal K}G_{(E,U)}(X)\,d\mu(E,U),
 \qquad X\in M_4(\mathbb C).
\end{aligned}
\tag{9.5}
$$

The integrals are entrywise finite-dimensional integrals. For (9.3), homogeneity in the effect gives $\Phi_\mu=\Phi$ exactly.

**Lemma 9.2 (compact parameters and continuity in the full diamond norm).** The space $\mathcal K$ is compact metrizable. The set $\mathcal M$ is weak-* compact, metrizable, and sequentially compact. Every $\Phi_\mu$ for $\mu\in\mathcal M$ is completely positive and trace preserving. Moreover,

$$
\mu_m\longrightarrow\mu\ \text{weak-*}
\quad\Longrightarrow\quad
\|\Phi_{\mu_m}-\Phi_\mu\|_\diamond\longrightarrow0.
\tag{9.6}
$$

Proof. The density matrices form a closed bounded subset of the finite-dimensional real space of Hermitian $2$-by-$2$ matrices. The group $U(4)$ is a closed bounded subset of the finite-dimensional space of complex $4$-by-$4$ matrices. Their product is therefore compact metrizable. Positive measures of mass two form a weak-* compact subset of the dual of $C(\mathcal K)$, by the Riesz representation theorem and weak-* compactness of a bounded dual ball. Positivity and mass are closed conditions. The entries of $E$ are continuous test functions, so the moment condition in (9.4) is also closed. Thus $\mathcal M$ is compact. Since $C(\mathcal K)$ is separable, the weak-* topology on this bounded set is metrizable, and compactness consequently gives sequential compactness. Nonemptiness also follows from the two-outcome protocol (6.2)--(6.3).

For each fixed $X$, the entries of $G_{(E,U)}(X)$ are continuous functions of $E,U$. The matrix $R_0E^{\mathsf T}R_0^\dagger$ is positive semidefinite. The factorization and diagonal-Kraus identity (3.4) therefore show that $G_{(E,U)}$ is completely positive. At every finite reference size, integration of its positive amplified outputs preserves positivity, proving complete positivity of $\Phi_\mu$. Unitary conjugation preserves trace, and the moment condition gives

$$
\begin{aligned}
\operatorname{Tr}\Phi_\mu(X)
 &=\sum_{i=1}^4 X_{ii}
       \left(R_0\left(\int_{\mathcal K}E^{\mathsf T}\,d\mu\right)
                         R_0^\dagger\right)_{ii}\\
 &=\sum_{i=1}^4 X_{ii}(C_0)_{ii}
 =\operatorname{Tr}X.
\end{aligned}
\tag{9.7}
$$

Here $\int E^{\mathsf T}\,d\mu=I_2$ and every diagonal entry of $C_0$ is one. This proves trace preservation without requiring an individual atom map to be trace preserving.

Let $E_{ij}=|i\rangle\langle j|$, $1\le i,j\le4$, denote the sixteen system matrix units. Weak-* convergence and the integrand continuity just proved imply entrywise, hence trace-norm, convergence

$$
\Phi_{\mu_m}(E_{ij})\longrightarrow\Phi_\mu(E_{ij}).
\tag{9.8}
$$

For any linear map $L:M_4(\mathbb C)\to M_4(\mathbb C)$, one has the reference-independent bound

$$
\|L\|_\diamond
 \le\sum_{i,j=1}^4\|L(E_{ij})\|_1
 \le16\max_{1\le i,j\le4}\|L(E_{ij})\|_1.
\tag{9.9}
$$

Indeed, fix any finite $n\ge1$ and any $X\in M_n(\mathbb C)\otimes M_4(\mathbb C)$. Its system blocks satisfy

$$
X=\sum_{i,j=1}^4X_{ij}\otimes E_{ij},\qquad
X_{ij}=(I_n\otimes\langle i|)X(I_n\otimes|j\rangle),
\qquad \|X_{ij}\|_1\le\|X\|_1.
\tag{9.10}
$$

The last inequality is the trace-norm ideal inequality for left and right multiplication by contractions; both block-compression maps have operator norm one. Multiplicativity of the trace norm on tensor products and its triangle inequality now give

$$
\begin{aligned}
\|(\operatorname{id}_{M_n}\otimes L)(X)\|_1
 &\le\sum_{i,j=1}^4\|X_{ij}\|_1\,\|L(E_{ij})\|_1\\
 &\le\|X\|_1\sum_{i,j=1}^4\|L(E_{ij})\|_1.
\end{aligned}
\tag{9.11}
$$

This holds for every finite untouched reference and every operator $X$, without a positivity or Hermiticity restriction. Taking exactly the suprema in (1.6) proves (9.9), with no factor $1/2$. Applying (9.9) to $L=\Phi_{\mu_m}-\Phi_\mu$ and using (9.8) proves (9.6). In particular, both $\|\Phi_\mu-\operatorname{id}_{M_4}\|_\diamond$ and $\|\Phi_\mu-\Phi_*\|_\diamond$ are continuous functions on $\mathcal M$. $\square$

**Lemma 9.3 (continuous actual-feedback defect).** Let $e_1,e_2$ be the standard record basis and use the unique positive square root to define

$$
\begin{aligned}
b_\ell(E)&=(E^{\mathsf T})^{1/2}e_\ell,
 &\quad v_\ell(E)&=R_0b_\ell(E),\\
K_\ell(E,U)&=U\operatorname{diag}(v_\ell(E)),
 &\quad \ell&=1,2,\\
a(E)&=\sum_{\ell=1}^2\delta(b_\ell(E)),\\
\tau(E,U)&=\sum_{\ell=1}^2
 \left(\|v_\ell(E)\|_{\ell^1}^2
                   -|\operatorname{Tr}K_\ell(E,U)|^2\right).
\end{aligned}
\tag{9.12}
$$

These are continuous nonnegative defects on $\mathcal K$. For the normalized Choi state and overlap

$$
J_{\Phi_\mu}=(\operatorname{id}_{M_4}\otimes\Phi_\mu)(\Pi),
\qquad f_\mu=\langle\omega|J_{\Phi_\mu}|\omega\rangle,
\qquad \Delta_\mu=\frac{1+c}{2}-f_\mu,
\tag{9.13}
$$

one has

$$
\int_{\mathcal K}(a(E)+\tau(E,U))\,d\mu
 =\operatorname{Tr}H-16f_\mu=16\Delta_\mu\ge0.
\tag{9.14}
$$

The lower witness (3.15) applies to $\Phi_\mu$ and gives

$$
\|\Phi_\mu-\operatorname{id}_{M_4}\|_\diamond
 \ge2(1-f_\mu)\ge q.
\tag{9.15}
$$

For every $\varepsilon\ge0$, the premise
$\|\Phi_\mu-\operatorname{id}_{M_4}\|_\diamond\le q+\varepsilon$ implies the actual defect budget

$$
0\le\int_{\mathcal K}(a+\tau)\,d\mu\le8\varepsilon.
\tag{9.16}
$$

At exact optimum, $a(E)=\tau(E,U)=0$ at every point of $\operatorname{supp}\mu$.

Proof. The positive square-root map is continuous on positive semidefinite matrices, including at singular matrices. Thus the columns in (9.12) are continuous and require no continuous choice of eigenvectors. They satisfy

$$
\sum_{\ell=1}^2b_\ell(E)b_\ell(E)^\dagger=E^{\mathsf T},
\qquad
G_{(E,U)}(X)=\sum_{\ell=1}^2K_\ell(E,U)XK_\ell(E,U)^\dagger.
\tag{9.17}
$$

Theorem 8.2 gives $\delta(b)\ge0$, with equality exactly on its two rays. Each summand of $\tau$ is nonnegative by (3.12), using the actual same $U$ in both column terms. All expressions in (9.12) are continuous.

The Choi trace formula (3.11), applied to (9.17) and integrated, reads

$$
16f_\mu=\int_{\mathcal K}\sum_{\ell=1}^2
                   |\operatorname{Tr}K_\ell(E,U)|^2\,d\mu.
\tag{9.18}
$$

Also, $\sum_\ell b_\ell^\dagger H b_\ell=\operatorname{Tr}(HE^{\mathsf T})$, whose integral is $\operatorname{Tr}H$ by (9.4). Subtracting (9.18) proves (9.14). This is the actual defect identity of Section 8 with the finite sum replaced by an integral; the feedback has not been changed. Since $\operatorname{Tr}H=8+8c$, (9.14) gives $f_\mu\le(1+c)/2$. Lemma 9.2 allows the existing Choi lower witness (3.15) to be applied, giving (9.15). For finite protocols its lower comparison is exactly Theorem 3.1. The near-optimal premise gives $2(1-f_\mu)\le1-c+\varepsilon$, hence $\Delta_\mu\le\varepsilon/2$, proving (9.16).

At error $q$, (9.16) makes the integral of the continuous nonnegative function $a+\tau$ zero. If that function were positive at a support point, it would have a positive lower bound on a neighborhood with positive measure, a contradiction. Thus it is zero on the support, and nonnegativity gives the two separate equalities there. $\square$

**Theorem 9.4 (exact support rigidity and unique optimizer channel).** Put

$$
E_\sigma=\bar b_\sigma\bar b_\sigma^\dagger=D_\sigma,
\qquad E_\sigma^{\mathsf T}=b_\sigma b_\sigma^\dagger,
\qquad \sigma\in\{+,-\},
\tag{9.19}
$$

using exactly $b_\sigma,D_\sigma,U_\sigma$ from (6.7), (6.2), and (6.3). Define the two disjoint compact sets

$$
\mathcal S_\sigma
 =\{(E_\sigma,e^{i\varphi}U_\sigma):\varphi\in\mathbb R\},
\qquad \mathcal S=\mathcal S_+\cup\mathcal S_-.
\tag{9.20}
$$

For $\mu\in\mathcal M$, the following are equivalent: its error is $q$; its support is contained in $\mathcal S$; and its channel is $\Phi_*$. In the optimizing case $\mu(\mathcal S_+)=\mu(\mathcal S_-)=1$. Consequently the exact optimizer channel is unique in the original finite protocol class, although its implementing measures and instruments need not be unique.

Proof. Suppose the error is $q$ and take $(E,U)\in\operatorname{supp}\mu$. Lemma 9.3 makes every individual nonnegative summand in (9.12) zero. The equality characterization of Theorem 8.2 therefore puts every nonzero column $b_\ell(E)$ on one of the two complex $T$-coordinate rays. Such a column has the form $z b_\sigma$ for some $z\ne0$ and $\sigma\in\{+,-\}$. By (6.9),

$$
R_0b_+=\begin{pmatrix}
h\\\alpha h\\e^{-i\theta}c\\e^{i\theta}c
\end{pmatrix},\qquad
R_0b_-=\begin{pmatrix}
h\\-\alpha h\\i e^{-i\theta}s\\-i e^{i\theta}s
\end{pmatrix},
\qquad h,c,s>0.
\tag{9.21}
$$

Every coordinate of both vectors is nonzero. Thus $v=R_0b_\ell(E)$ also has no zero coordinate. The zero trace defect for this column forces equality throughout

$$
\left|\operatorname{Tr}(U\operatorname{diag}(v))\right|
 =\left|\sum_{i=1}^4U_{ii}v_i\right|
 \le\sum_{i=1}^4|U_{ii}|\,|v_i|
 \le\sum_{i=1}^4|v_i|.
\tag{9.22}
$$

In the last inequality every $|v_i|$ is strictly positive and every $|U_{ii}|\le1$, so equality gives $|U_{ii}|=1$ for every $i$. The norm-one condition on each column of the unitary $U$ then makes every off-diagonal entry zero. Equality in the triangle inequality in (9.22) says that the four nonzero numbers $U_{ii}v_i$ have a common phase. Hence

$$
U=e^{i\psi}\operatorname{diag}
 \left(\frac{\overline{v_i}}{|v_i|}\right)_{i=1}^4
   =e^{i\varphi}U_\sigma
\tag{9.23}
$$

for some phases $\psi,\varphi$; the phase of the scalar $z$ is absorbed into $e^{i\varphi}$. The last equality uses the polar corrections already displayed in (6.3) and (6.9).

One original $U$ cannot satisfy (9.23) for nonzero columns on both rays, because

$$
U_+^\dagger U_-
 =\operatorname{diag}(1,-1,-i,i)
\tag{9.24}
$$

is not scalar. At least one column is nonzero since $\operatorname{Tr}E=1$. All nonzero columns must therefore belong to the same ray. Equation (9.17) and the trace-one normalization imply

$$
E^{\mathsf T}
 =\left(\sum_\ell|z_\ell|^2\right)b_\sigma b_\sigma^\dagger
 =b_\sigma b_\sigma^\dagger,
\qquad E=\bar b_\sigma\bar b_\sigma^\dagger=E_\sigma.
\tag{9.25}
$$

Together with (9.23), this proves $\operatorname{supp}\mu\subseteq\mathcal S$. In particular it keeps the transpose explicit: the normalized measured effect is the projection onto $\bar b_\sigma$, while the vectors acted on by $R_0$ lie on the $b_\sigma$ ray.

Conversely, suppose a feasible measure is supported in $\mathcal S$. Write $m_\sigma=\mu(\mathcal S_\sigma)$. Its moment is

$$
m_+E_++m_-E_-=I_2.
\tag{9.26}
$$

The two $E_\sigma$ are orthogonal rank-one projections summing to $I_2$. Multiplying (9.26) by either projection and taking trace yields $m_+=m_-=1$. Scalar feedback phases cancel from $G_{(E,U)}$, so (6.4) gives

$$
\Phi_\mu
 =m_+G_{(E_+,U_+)}+m_-G_{(E_-,U_-)}
 =\Phi_*.
\tag{9.27}
$$

Theorem 6.2 gives its error $q$, completing all implications. The displayed atoms themselves have zero certificate and trace defects by Theorem 8.2 and (6.11), so $\mathcal S$ is precisely the set of atoms eligible for optimizing support, subject to the moment masses in (9.26).

For a finite original optimizer, every nonzero effect consequently has the form $D_y=t_yE_{\sigma(y)}$, its actual feedback is $e^{i\varphi_y}U_{\sigma(y)}$, and the total $t_y$ for each sign is one. Zero effects remain harmless. Outcomes may be split or relabelled, and scalar phases may vary, giving different measures and instruments with the same channel. The uniqueness assertion concerns the implemented channel, not these presentations or measurement realizations. $\square$

**Proposition 9.5 (finite realization of every compactified channel).** Every $\mu\in\mathcal M$, including every weak-* limiting measure, has the same moment and channel as an original finite protocol with at most $261$ nonzero outcomes and genuine feedback unitaries in $U(4)$.

Proof. For each atom retain the same normalized Choi convention as in Definition 1.3, even though an atom need not preserve trace:

$$
J_{G_{(E,U)}}=(\operatorname{id}_{M_4}\otimes G_{(E,U)})(\Pi).
\tag{9.28}
$$

This is a Hermitian $16$-by-$16$ matrix. The continuous map

$$
F:\mathcal K\longrightarrow
 \operatorname{Herm}_2\oplus\operatorname{Herm}_{16},
\qquad F(E,U)=(E,J_{G_{(E,U)}})
\tag{9.29}
$$

has compact image in a real vector space of dimension at most $4+256=260$. The probability measure $\nu=\mu/2$ has barycenter

$$
\int_{\mathcal K}F\,d\nu
 =\left(\frac{I_2}{2},\frac{J_{\Phi_\mu}}{2}\right).
\tag{9.30}
$$

This barycenter belongs to the convex hull of $F(\mathcal K)$. Indeed, finite weighted samples approximate its integral by compactness and continuity, and the convex hull of a compact set in finite dimensions is closed. Caratheodory's theorem represents each point of that convex hull using at most $261$ points; it also gives its compactness, since the representations are images of a compact product with the closed probability simplex.

Thus there are $1\le r\le261$, atoms $(E_i,U_i)\in\mathcal K$, and positive weights $p_i$ summing to one, after removal of any zero weights, such that

$$
\sum_{i=1}^rp_iE_i=\frac{I_2}{2},\qquad
\sum_{i=1}^rp_iJ_{G_{(E_i,U_i)}}=\frac{J_{\Phi_\mu}}{2}.
\tag{9.31}
$$

Set $D_i=2p_iE_i$ and keep these same $U_i$. These effects are Hermitian positive semidefinite and sum to $I_2$. Linearity in the effect and injectivity of the Choi correspondence yield

$$
\sum_{i=1}^rU_i\bigl((R_0D_i^{\mathsf T}R_0^\dagger)\circ X\bigr)U_i^\dagger
 =2\sum_{i=1}^rp_iG_{(E_i,U_i)}(X)=\Phi_\mu(X)
\tag{9.32}
$$

for every $X$. This is a protocol in exactly Definition 1.2, retaining every outcome. Thus the compact measure description introduces no additional channel obtainable only from diffuse measures. In particular a diffuse optimizing limit cannot evade finite realization. Measures here are an auxiliary compact parameter space, not a claim about physically implementing an infinite-outcome measurement. $\square$

**Theorem 9.6 (qualitative optimizer-channel stability for the original protocol class).** For every $\delta>0$ there exists $\varepsilon_\delta>0$ such that the following holds simultaneously for every finite integer $k\ge1$, every Hermitian positive semidefinite family $D_1,\ldots,D_k\in M_2(\mathbb C)$ with $\sum_{y=1}^kD_y=I_2$, and every family of actual feedback unitaries $U_1,\ldots,U_k\in U(4)$. For the fixed original record and its all-outcome channel

$$
\Phi(X)=\sum_{y=1}^k
 U_y\bigl((R_0D_y^{\mathsf T}R_0^\dagger)\circ X\bigr)U_y^\dagger,
\tag{9.33}
$$

one has

$$
\boxed{
\|\Phi-\operatorname{id}_{M_4}\|_\diamond
 \le1-\cos(\pi/8)+\varepsilon_\delta
\quad\Longrightarrow\quad
\|\Phi-\Phi_*\|_\diamond<\delta.
}
\tag{9.34}
$$

Both norms are exactly the unhalved norm (1.6), with suprema over every finite untouched reference and every nonzero operator on reference and system. In particular the conclusion supplies one number $d=\|\Phi-\Phi_*\|_\diamond<\delta$ such that, for every finite $n\ge1$ and every $X\in M_n(\mathbb C)\otimes M_4(\mathbb C)$,

$$
\|(\operatorname{id}_{M_n}\otimes(\Phi-\Phi_*))(X)\|_1
 \le d\,\|X\|_1.
\tag{9.35}
$$

The tolerance $\varepsilon_\delta$ is independent of the finite outcome count, the effects, and the feedback.

Proof. Fix $\delta>0$ and consider the closed subset of the compact set $\mathcal M$

$$
\mathcal A_\delta
 =\{\mu\in\mathcal M:\|\Phi_\mu-\Phi_*\|_\diamond\ge\delta\}.
\tag{9.36}
$$

Its compactness follows from Lemma 9.2. If it is empty, choose any positive $\varepsilon_\delta$, for example one. Otherwise the continuous nonnegative error excess has a minimum there:

$$
\eta_\delta
 =\min_{\mu\in\mathcal A_\delta}
       \left(\|\Phi_\mu-\operatorname{id}_{M_4}\|_\diamond-q\right).
\tag{9.37}
$$

It is strictly positive. If it were zero, a minimizing measure would have error $q$, so Theorem 9.4 would force its channel to be $\Phi_*$, contradicting membership in $\mathcal A_\delta$. The lower comparison is (9.15), consistent with Theorem 3.1 and the finite realization of Proposition 9.5; Theorem 6.2 supplies the attaining channel. Set

$$
\varepsilon_\delta=\eta_\delta/2>0.
\tag{9.38}
$$

An original protocol satisfying the premise of (9.34) gives a measure (9.3) whose error excess is at most $\eta_\delta/2$. It cannot belong to $\mathcal A_\delta$, on which that excess is at least $\eta_\delta$. Hence its distance to the fixed $\Phi_*$ is strictly less than $\delta$.

Equivalently, a failure of stability would provide original finite protocols with errors tending to $q$ but distances at least a fixed $\delta$. Sequential compactness of their normalized effect measures and (9.6) would give an exact optimizing limit still at distance at least $\delta$, contradicting Theorem 9.4. Proposition 9.5 also gives that limit a finite original realization. Every continuity assertion used here is in the full norm (1.6), so no restriction on the reference or on amplified operators enters either argument. $\square$

The source-specific conclusions of this section are exact optimizer-channel uniqueness and qualitative stability at positive error tolerance, using the equality characterization and actual defect identity of Section 8. Compactness, the continuous positive square root, and Caratheodory's theorem are general ingredients; no literature-priority assertion is made. No quantitative modulus is evaluated or proved, and no $K\sqrt\varepsilon$ rate is established. The square-root assertion at the end of Section 8 remains unresolved. The conclusions concern the original finite full-record protocols only: no extension to postselection, changed records, infinite outcomes, nonunitary feedback, or physical acquisition of outcome probabilities is claimed.

## 追加锚（本行以下为增补区）
## 10. Quantitative square-root transport through actual feedback

The preceding section used compactness to obtain a qualitative modulus. The next estimate keeps the same feedback-preserving refinement as Section 8 and supplies a direct quantitative bridge from its two defect budgets to the implemented channel. No outcome weight is bounded below, and no feedback is re-optimized after spectral refinement.

**Lemma 10.1 (weighted equality remainder).** Let $v\in\mathbb C^4$, $U\in U(4)$, and put

$$
K=U\operatorname{diag}(v),\qquad
 a_i=|v_i|,\qquad L=\sum_{i=1}^4a_i,\qquad
 t=|\operatorname{Tr}K|,\qquad \tau=L^2-t^2.
\tag{10.1}
$$

There is a phase $\lambda\in\mathbb C$ with $|\lambda|=1$ such that

$$
\boxed{\ \|K-\lambda\operatorname{diag}(a_1,a_2,a_3,a_4)\|_{\mathrm{HS}}^2\le2\tau.\ }
\tag{10.2}
$$

**Proof.** Choose $\lambda$ so that $\overline\lambda\operatorname{Tr}K=t$; when $t=0$, choose any unit phase. Set

$$
 r_i=a_i-\operatorname{Re}\bigl(\overline\lambda\,U_{ii}v_i\bigr)\ge0.
$$

The inequalities $|U_{ii}|\le1$ give the nonnegativity, and $\sum_i r_i=L-t$. Direct expansion gives

$$
\begin{aligned}
\|K-\lambda\operatorname{diag}(a_i)\|_{\mathrm{HS}}^2
 &=2\sum_i a_i^2-2\sum_i a_i\operatorname{Re}\bigl(\overline\lambda\,U_{ii}v_i\bigr)\\
 &=2\sum_i a_i r_i
 \le2L(L-t)\le2(L+t)(L-t)=2\tau.
\end{aligned}
$$

The same calculation covers $L=0$ and zero coordinates. $\square$

**Lemma 10.2 (nearest-ray Kraus comparison).** Use the feedback-preserving refinement (3.2)--(3.4) and write

$$
 b_j=T\begin{pmatrix}\xi_j\\\eta_j\end{pmatrix},\qquad
 p_j=|\xi_j|^2,\quad q_j=|\eta_j|^2,\quad
 d_j^2=\min\{p_j,q_j\}.
\tag{10.3}
$$

Put

$$
 S_{\mathrm{cert}}=\sum_j\delta(b_j),\qquad
 S_{\mathrm{tr}}=\sum_j\tau_j,\qquad
 M=\sum_jd_j^2,
\tag{10.4}
$$

where $\tau_j$ is the actual-feedback defect defined in the proof of Theorem 8.2. Assign $j$ to $\sigma_j=+$ when $p_j\ge q_j$ and to $\sigma_j=-$ otherwise, and let

$$
 z_j=\begin{cases}
 \xi_j,&\sigma_j=+,\\
 \eta_j,&\sigma_j=-,
 \end{cases}\qquad
 b_j^0=z_jb_{\sigma_j},\qquad
 A_\sigma=\operatorname{diag}(|R_0b_\sigma|).
\tag{10.5}
$$

For the phase supplied by Lemma 10.1 applied to $K_j=U_y\operatorname{diag}(R_0b_j)$, define

$$
 B_j=\lambda_j|z_j|A_{\sigma_j}.
\tag{10.6}
$$

Then

$$
\boxed{\ \sum_j\|K_j-B_j\|_{\mathrm{HS}}^2
 \le4S_{\mathrm{tr}}+2\|R_0\|_{\mathrm{op}}^2M.\ }
\tag{10.7}
$$

Moreover, with

$$
 m_+=\sum_{\sigma_j=+}p_j,\qquad m_-=\sum_{\sigma_j=-}q_j,
\tag{10.8}
$$

one has $0\le m_\sigma\le1$ and

$$
(1-m_+)+(1-m_-)=M.
\tag{10.9}
$$

**Proof.** The coordinatewise modulus is $1$-Lipschitz, so

$$
\|\operatorname{diag}(|R_0b_j|)-|z_j|A_{\sigma_j}\|_{\mathrm{HS}}^2
 \le\|R_0(b_j-b_j^0)\|_2^2
 \le\|R_0\|_{\mathrm{op}}^2d_j^2.
$$

Combining this with (10.2) and $\|X+Y\|_{\mathrm{HS}}^2\le2\|X\|_{\mathrm{HS}}^2+2\|Y\|_{\mathrm{HS}}^2$ gives (10.7). Completeness in (3.6) gives $\sum_jp_j=\sum_jq_j=1$, hence

$$
1-m_+=\sum_{\sigma_j=-}p_j,\qquad
1-m_-=\sum_{\sigma_j=+}q_j.
$$

Their sum is $\sum_j\min\{p_j,q_j\}=M$. $\square$

**Theorem 10.3 (uniform quantitative square-root stability).** For every protocol of Definition 1.2 and every $\varepsilon\in[0,1]$ satisfying

$$
\|\Phi-\operatorname{id}_{M_4}\|_\diamond\le1-c+\varepsilon,
\tag{10.10}
$$

one has

$$
\boxed{\ \|\Phi-\Phi_*\|_\diamond
 \le480\sqrt2\,\sqrt\varepsilon.\ }
\tag{10.11}
$$

The constant is independent of the finite outcome count, all positive semidefinite effects, all actual feedback unitaries, and every finite untouched reference. The norm is the unhalved norm (1.6), and every original outcome remains in the actual channel.

**Proof.** Let $A_\sigma$ be as in (10.5). By (6.11), $A_\sigma$ are the diagonal Kraus operators of $\Phi_*$ and

$$
A_+^\dagger A_++A_-^\dagger A_-=I_4.
\tag{10.12}
$$

Append two zero operators to the actual list $K_j$. Append to the comparison list

$$
 C_\sigma=\sqrt{1-m_\sigma}\,A_\sigma,\qquad \sigma\in\{+,-\}.
\tag{10.13}
$$

The $B_j$ terms implement $m_+A_+(\cdot)A_+^\dagger+m_-A_-(\cdot)A_-^\dagger$, so the completed comparison list $B_j,C_+,C_-$ implements exactly $\Phi_*$. The appended zeros and $C_\sigma$ are comparison padding only; they are not extra physical outcomes. Both padded lists are trace-preserving Kraus lists. Let $V$ and $W$ be their common-environment column isometries.

Since $\|A_\sigma\|_{\mathrm{op}}\le1$, (10.7), (10.9), and (10.13) give

$$
\begin{aligned}
\|V-W\|_{\mathrm{op}}^2
 &\le \sum_j\|K_j-B_j\|_{\mathrm{HS}}^2
       +\left\|\sum_\sigma C_\sigma^\dagger C_\sigma\right\|_{\mathrm{op}}\\
 &\le4S_{\mathrm{tr}}+(2\|R_0\|_{\mathrm{op}}^2+1)M.
\end{aligned}
\tag{10.14}
$$

Here the first inequality uses the direct-sum form of the column isometries, and the second uses
$\|\sum_\sigma C_\sigma^\dagger C_\sigma\|_{\mathrm{op}}\le(1-m_+)+(1-m_-)=M$.

For completeness, the partial trace over a finite environment is trace-norm contractive for arbitrary operators: by trace duality,

$$
\|\operatorname{Tr}_{\mathrm{env}}Z\|_1
 =\sup_{\|Y\|_{\mathrm{op}}\le1}
   \left|\operatorname{Tr}\bigl[(I_{\mathrm{env}}\otimes Y)Z\bigr]\right|
 \le\|Z\|_1.
\tag{10.15}
$$

For every finite reference $M_n(\mathbb C)$ and every $X\in M_n(\mathbb C)\otimes M_4(\mathbb C)$, expand the difference of the two dilated maps into the two terms containing $V-W$. The trace-norm ideal inequality, (10.15), and $\|V\|_{\mathrm{op}}=\|W\|_{\mathrm{op}}=1$ yield

$$
\| (\operatorname{id}_{M_n}\otimes(\Phi-\Phi_*))(X)\|_1
 \le2\|V-W\|_{\mathrm{op}}\|X\|_1.
\tag{10.16}
$$

This is uniform in the reference dimension and does not assume positivity or Hermiticity of $X$.

Now (8.6) gives $M\le1600S_{\mathrm{cert}}$ and the actual defect identity gives

$$
S_{\mathrm{cert}}+S_{\mathrm{tr}}\le8\varepsilon.
\tag{10.17}
$$

Since $\|R_0\|_{\mathrm{op}}^2\le\|R_0\|_{\mathrm{HS}}^2=4$, (10.14)--(10.17) imply

$$
\begin{aligned}
\|\Phi-\Phi_*\|_\diamond
 &\le2\sqrt{4S_{\mathrm{tr}}+9M}\\
 &\le2\sqrt{4S_{\mathrm{tr}}+14400S_{\mathrm{cert}}}\\
 &\le2\sqrt{14400(S_{\mathrm{cert}}+S_{\mathrm{tr}})}\\
 &\le480\sqrt2\,\sqrt\varepsilon.
\end{aligned}
$$

All comparison phases $\lambda_j$ are Kraus gauges in the auxiliary representation of $\Phi_*$; they do not alter the actual shared feedback $U_y$, add a physical outcome, postselect, or change the record. $\square$

**Proposition 10.4 (the square-root exponent is sharp for this protocol class).** Let $Z=P-Q$ and $W_t=e^{itZ}$. Keep the two effects of (6.2) and replace the actual feedbacks by

$$
U_\sigma(t)=W_tU_\sigma,\qquad \sigma\in\{+,-\}.
\tag{10.18}
$$

The resulting two-outcome channel is $\Phi_t=\operatorname{Ad}(W_t)\circ\Phi_*$. Put

$$
q=1-c,\qquad
\epsilon_t=\|\Phi_t-\operatorname{id}_{M_4}\|_\diamond-q,\qquad
 d_t=\|\Phi_t-\Phi_*\|_\diamond.
\tag{10.19}
$$

Then

$$
\boxed{\ \epsilon_t=\sqrt{q^2+4c\sin^2t}-q,\qquad
 d_t=2c|\sin t|,\qquad
 d_t^2=c(2q\epsilon_t+\epsilon_t^2).\ }
$$

Consequently $d_t/\sqrt{\epsilon_t}\to\sqrt{2cq}>0$ as $t\to0$, so no uniform bound $d_t\le K\epsilon_t^\beta$ can hold for any $\beta>1/2$.

**Proof.** The channel $\Phi_*$ has cross-block coefficient $c$ in (6.14), while conjugation by $W_t$ changes it to $ce^{2it}$. For any $\lambda\in\mathbb C$, the cross-block map

$$
\Gamma_\lambda(X)=\lambda PXQ+\overline\lambda QXP
$$

has full unhalved diamond norm $|\lambda|$: the upper bound follows from
$\Gamma_1=(\operatorname{id}-\operatorname{Ad}Z)/2$ and unitary phase conjugation, while $X=|1\rangle\langle3|$ gives the reverse bound. Therefore

$$
\|\Phi_t-\operatorname{id}\|_\diamond=|1-ce^{2it}|
 =\sqrt{q^2+4c\sin^2t},
$$

and

$$
\|\Phi_t-\Phi_*\|_\diamond=|c(e^{2it}-1)|=2c|\sin t|.
$$

Eliminating $\sin^2t$ gives the final identity. The effects remain complete, each outcome retains one actual unitary, and all outcomes are included, so the family lies in the original protocol class. $\square$

Theorem 10.3 closes the quantitative assertion left open after Section 9, while Proposition 10.4 records that its exponent cannot be improved using the same protocol class. The proof uses the degree-two homogeneous defect budget; the quartic statistics in Proposition 8.3 alone would be presentation-dependent under proportional refinement. The estimate is deliberately conservative and does not claim an optimal constant.

## 追加锚（本行以下为增补区）
## 11. 原始效果与共享反馈的定性刚性

Theorem 10.3 controls the implemented channel in the full reference-inclusive diamond norm.  The next distinction is at the producer level: an original outcome carries one normalized effect and one feedback unitary, and spectral refinement must not replace that shared unitary by separate controls.  This section extracts a uniform qualitative modulus for those original pairs.  Its consumer is a weighted producer certificate: near-optimal implementations can certify clustering of normalized effects and their actual feedback around the two joint optimizer classes, with no claim of uniform control for arbitrarily small-weight outcomes.  It does not assert a power law; the quadratic producer coercivity remains a separate open target.

**定义 11.1（原始对的距离与联合缺陷）。** 保持定义 9.1 的紧空间

$$
\mathcal K=\operatorname{Dens}_2\times U(4)
$$

及定理 9.4 的两个优化集

$$
\mathcal S_\sigma
 =\{(E_\sigma,e^{i\varphi}U_\sigma):\varphi\in\mathbb R\},
\qquad
\mathcal S=\mathcal S_+\cup\mathcal S_-.
$$

在 $\mathcal K$ 上定义

$$
\rho(E,U)
 =\min_{\sigma\in\{+,-\},\ |\lambda|=1}
 \left(\|E-E_\sigma\|_{\mathrm F}^2
       +\|U-\lambda U_\sigma\|_{\mathrm F}^2\right)
$$

以及

$$
g(E,U)=a(E)+\tau(E,U),
$$

其中 $a$ 与 $\tau$ 正是式 (9.12) 的连续缺陷。$\rho$ 对反馈的标量相位取商，保留效果与反馈的共同符号选择；它不把同一原始结果的两个谱向量当成两个可重新控制的结果。

**引理 11.2（单原始对的零集）。** 对所有 $(E,U)\in\mathcal K$，

$$
\boxed{\quad g(E,U)=0\quad\Longleftrightarrow\quad
       \rho(E,U)=0\quad\Longleftrightarrow\quad
       (E,U)\in\mathcal S.\quad}
$$

**证明。** 若 $(E,U)\in\mathcal S_\sigma$，式 (9.12) 中的两个平方根列均位于相同的证书射线上，且 $U$ 只是式 (6.3) 的极坐标修正乘以标量相位；故 $a=\tau=0$，从而 $\rho=0$。

反之，$g=0$ 时，式 (9.12) 的每个非负项都为零。由定理 8.2 的等号刻画，每个非零列

$$
b_\ell(E)=(E^{\mathsf T})^{1/2}e_\ell
$$

位于两个证书复射线之一。其像 $R_0b_\ell(E)$ 的四个坐标均非零，因此 $\tau=0$ 迫使不等式

$$
\left|\operatorname{Tr}\!\left(U\operatorname{diag}(R_0b_\ell(E))\right)\right|
\le\sum_i\left|(R_0b_\ell(E))_i\right|
$$

逐项取等号。于是 $U$ 为相应极坐标修正乘以一个共同标量相位。一个 $U$ 不可能同时修正两个不同的证书射线，因为式 (9.24) 不是标量矩阵；而 $\operatorname{Tr}E=1$ 保证至少一个列非零。所以全部非零列在同一射线上。由

$$
\sum_\ell b_\ell(E)b_\ell(E)^\dagger=E^{\mathsf T}
$$

及迹一归一化，得到 $E=E_\sigma$，并且 $U=e^{i\varphi}U_\sigma$。这正是 $(E,U)\in\mathcal S_\sigma$。$\square$

**定理 11.3（原始对的统一定性模）。** 定义

$$
\omega(r)=\max\{\rho(E,U):(E,U)\in\mathcal K,\ g(E,U)\le r\}
$$

（当集合非空时；对超出 $g$ 的最大值的 $r$ 取同一常数延拓）。则 $\omega$ 有限、单调不减，并且

$$
\boxed{\qquad \lim_{r\downarrow0}\omega(r)=0.\qquad}
$$

令 $R_\rho=\max_{\mathcal K}\rho<\infty$，对 $s\ge0$ 定义

$$
\Omega(s)=\inf_{r>0}\left(2\omega(r)+\frac{R_\rho s}{r}\right).
$$

则对定义 1.2 的任意有限全结果协议，若其效果与实际反馈给出式 (9.3) 的测度 $\mu$，且 $\varepsilon\ge0$ 满足

$$
\|\Phi_\mu-\operatorname{id}_{M_4}\|_\diamond\le q+\varepsilon,
$$

就有

$$
\boxed{
\int_{\mathcal K}\rho(E,U)\,d\mu(E,U)
 \le \Omega(8\varepsilon),
\qquad
\lim_{\varepsilon\downarrow0}\Omega(8\varepsilon)=0.
}
$$

等价地，若原协议写成有限效果族，则

$$
\sum_{y:D_y\ne0}\operatorname{Tr}(D_y)\,
 \rho\!\left(\frac{D_y}{\operatorname{Tr}D_y},U_y\right)
 \le\Omega(8\varepsilon).
$$

**证明。** $\mathcal K$ 紧，且正平方根、$a$、$\tau$ 连续；对有限个符号和紧单位圆取最小值后，$\rho$ 也连续。引理 11.2 说明 $g^{-1}(0)=\mathcal S=\rho^{-1}(0)$。若存在 $\eta>0$、$r_n\downarrow0$ 及 $(E_n,U_n)$ 使 $g(E_n,U_n)\le r_n$ 而 $\rho(E_n,U_n)\ge\eta$，紧性给出收敛子列。连续性使极限点同时满足 $g=0$ 与 $\rho\ge\eta$，矛盾。因此 $\omega(r)\to0$。

对任意 $r>0$，将 $\mathcal K$ 分成 $g\le r$ 与 $g>r$ 两部分。在前一部分 $\rho\le\omega(r)$；在后一部分 $\rho\le R_\rho$ 且 $1\le g/r$。因为 $\mu(\mathcal K)=2$，

$$
\begin{aligned}
\int\rho\,d\mu
&\le2\omega(r)+R_\rho\,\mu\{g>r\}\\
&\le2\omega(r)+\frac{R_\rho}{r}\int g\,d\mu.
\end{aligned}
$$

引理 9.3 的实际缺陷预算给出 $\int g\,d\mu\le8\varepsilon$。先对 $r$ 取下确界即得第一式。给定 $\eta>0$，先取 $r$ 使 $2\omega(r)<\eta/2$，再令 $s$ 足够小使 $R_\rho s/r<\eta/2$，故 $\Omega(s)\to0$。最后将 $d\mu$ 的原子表达式 (9.3) 代回即可。$\square$

这个结果保留了原始结果的反馈共享关系，并且对结果数与最小结果权重不作假设。它只给出存在性的定性模；没有把 $\Omega$ 误称为平方根，也没有由紧性推出任何显式幂次或最佳常数。

**问题 11.4（生产者层的定量缺口）。** 在定理 11.3 的同一距离 $\rho$ 与缺陷 $g$ 下，是否存在仅依赖固定记录的有限常数 $C$，使

$$
\rho(E,U)\le C\,g(E,U)
\quad\text{对所有 }(E,U)\in\mathcal K
$$

成立，或至少使其在积分意义下给出 $\int\rho\,d\mu\le C\varepsilon$？若答案为否，应给出使 $\rho/g$ 发散的合法原始对序列。任何结论都必须保持同一 $U$ 作用于一个原始结果的全部谱列，并允许奇异效果、零列与任意小结果权重。该问题是生产者层的二次 coercivity 问题；定理 10.3 的通道级平方根估计不替代它。

## 追加锚（本行以下为增补区）


## 12. 生产者层的线性 coercivity

问题 11.4 的线性版本可以在同一固定记录上成立。关键是把效果的平方距离与实际共享反馈的相位余量放在同一个局部坐标中；单独对效果做谱分解会丢掉后者。本节只证明存在一个依赖固定记录的常数，不求最佳值。

**引理 12.1（优化圆周附近的共同射线）。** 设 $\sigma\in\{+,-\}$，令
$P_\sigma=b_\sigma b_\sigma^\dagger$，并写

$$
B=(E^{\mathsf T})^{1/2},\qquad b_\ell=Be_\ell,\qquad
t_\sigma(E)=\operatorname{Tr}\bigl((I-P_\sigma)E^{\mathsf T}\bigr).
$$

存在包含 $\mathcal S_\sigma$ 的邻域 $\mathcal N_\sigma$ 及常数 $C_\sigma<\infty$，使 $(E,U)\in\mathcal N_\sigma$ 时，两列都能写成

$$
b_\ell=z_\ell b_\sigma+r_\ell,\qquad r_\ell\perp b_\sigma,\qquad |z_\ell|\ge\tfrac13,
$$

且

$$
\sum_{\ell=1}^2\|r_\ell\|^2=t_\sigma(E),\qquad
\|E-E_\sigma\|_{\mathrm F}^2\le2t_\sigma(E),\qquad
t_\sigma(E)\le1600\,a(E).
$$

此外，

$$
\min_{|\mu|=1}\|U-\mu U_\sigma\|_{\mathrm F}^2
\le C_\sigma\bigl(a(E)+\tau(E,U)\bigr).
$$

**证明。** 在 $\mathcal S_\sigma$ 上，$B$ 的两列分别是 $(b_\sigma)_\ell b_\sigma$，而 (9.21) 给出 $(b_\sigma)_\ell\ne0$ 且 $R_0b_\sigma$ 的四个坐标均非零。正平方根的连续性给出一个邻域，其中 $|z_\ell|\ge1/3$，且每一列的另一坐标严格小于主坐标；这就固定了上述分解。

由 $\sum_\ell b_\ell b_\ell^\dagger=E^{\mathsf T}$，取 $I-P_\sigma$ 的迹得第一式。在基 $(b_\sigma,b_{-\sigma})$ 中，任意 $E$ 可写成

$$
T^\dagger E^{\mathsf T}T
=\begin{pmatrix}1-t&z\\\bar z&t\end{pmatrix},\qquad
0\le t\le1,\quad |z|^2\le t(1-t),
$$

其中 $t=t_\sigma(E)$。因此

$$
\|E-E_\sigma\|_{\mathrm F}^2=2(t^2+|z|^2)\le2t.
$$

在当前邻域中，$d_\ell^2=\operatorname{dist}(b_\ell,\mathcal E)^2=\|r_\ell\|^2$。定理 8.2 的第二个估计给
$\sum_\ell d_\ell^2\le1600\sum_\ell\delta(b_\ell)=1600a(E)$，从而得到第三式。

再取一个使 $|z_\ell|^2\ge(1-t)/2\ge1/4$ 的列，记
$v_\ell=R_0b_\ell$、$v_\sigma=R_0b_\sigma$、
$D_\sigma=\operatorname{diag}(v_\sigma)$、
$A_\sigma=\operatorname{diag}(|v_\sigma|)$ 及
$m_\sigma=\min_i|(v_\sigma)_i|>0$。坐标模长的 1-Lipschitz 性给出

$$
\|\operatorname{diag}(|v_\ell|)-|z_\ell|A_\sigma\|_{\mathrm{HS}}
\le\|R_0\|_{\mathrm{op}}\|r_\ell\|.
$$

对 $K_\ell=U\operatorname{diag}(v_\ell)$ 使用引理 10.1，取其相位 $\lambda$，并令
$\mu=\lambda|z_\ell|/z_\ell$。因为 $U_\sigma D_\sigma=A_\sigma$，三角不等式给出

$$
\|(U-\mu U_\sigma)z_\ell D_\sigma\|_{\mathrm{HS}}
\le\sqrt{2\tau_\ell}+2\|R_0\|_{\mathrm{op}}\|r_\ell\|.
$$

邻域可再缩小，使 $|z_\ell|m_\sigma\ge m_\sigma/2$。除以这个下界并平方，得到

$$
\min_{|\mu|=1}\|U-\mu U_\sigma\|_{\mathrm F}^2
\le\frac{16}{m_\sigma^2}\tau_\ell
  +\frac{32\|R_0\|_{\mathrm{op}}^2}{m_\sigma^2}\|r_\ell\|^2
\le C_\sigma(a+\tau).
$$

这同时处理了 $E$ 的秩一边界；没有对矩阵平方根作可微性假设。$\square$

**定理 12.2（生产者层线性 coercivity）。** 在定义 11.1 的同一 $\rho$ 与 $g$ 下，存在
$C_{\mathrm{prod}}<\infty$，仅依赖固定记录 $R_0,b_\pm,U_\pm$，使得

$$
\boxed{\qquad
\rho(E,U)\le C_{\mathrm{prod}}\,g(E,U)
\qquad((E,U)\in\mathcal K).}
$$

因此定义 1.2 的任意有限全结果协议都满足

$$
\boxed{\qquad
\int_{\mathcal K}\rho(E,U)\,d\mu(E,U)
\le8C_{\mathrm{prod}}\,\varepsilon,\qquad}
$$

只要 $\|\Phi_\mu-\operatorname{id}_{M_4}\|_\diamond\le q+\varepsilon$。

**证明。** 由引理 12.1，在每个 $\mathcal N_\sigma$ 中，以 $\sigma$ 作为定义 11.1
中最小值的候选，得到

$$
\rho(E,U)
\le \|E-E_\sigma\|_{\mathrm F}^2
+\min_{|\mu|=1}\|U-\mu U_\sigma\|_{\mathrm F}^2
\le C'_\sigma g(E,U).
$$

取两个邻域的不交并 $\mathcal N$。引理 11.2 表明
$g^{-1}(0)=\mathcal S\subset\mathcal N$，故紧集
$\mathcal K\setminus\mathcal N$ 上 $g$ 有严格正的最小值 $m$。令
$R_\rho=\max_\mathcal K\rho$，则该补集上
$\rho\le(R_\rho/m)g$。与两个局部常数取最大即得全局
$C_{\mathrm{prod}}$。

最后对协议的测度积分，并使用引理 9.3 的实际缺陷预算
$\int g\,d\mu\le8\varepsilon$，得到第二式。该结论不改变原始结果的反馈共享，也不对结果数或最小结果权重作假设。$\square$

定理 12.2 关闭问题 11.4 的存在性版本。这里的常数来自固定记录的局部非退化下界与紧性，尚未给出显式闭式或最佳值；这两个量化问题仍可单独研究。定理 10.3 的通道距离平方根上界及命题 10.4 的锐性不受影响：生产者距离是平方 Frobenius 距离，而通道范数仍可只呈平方根级稳定。

## 13. 局部常数与全局常数的下界

定理 12.2 中的局部常数可以只用固定记录的显式数值写出。令

$$
\kappa_R=\|R_0\|_{\mathrm{op}}^2=2+\frac1{\sqrt2},
\qquad s=\sin(\pi/8),
$$

则 $m_+=\min_i|(R_0b_+)_i|=1/\sqrt2$，而
$m_-=\min_i|(R_0b_-)_i|=s$。在引理 12.1 的邻域中再缩小使所选主系数满足
$|z_\ell|\ge1/2$，其证明中的同一估计给出

$$
\rho(E,U)
\le \left(3200+\frac{51200\kappa_R}{m_\sigma^2}\right)a(E)
      +\frac{16}{m_\sigma^2}\tau(E,U).
$$

因此可取局部系数

$$
C_{+,\mathrm{loc}}=208000+51200\sqrt2,
\qquad
C_{-,\mathrm{loc}}=515200+307200\sqrt2.
$$

这里使用了
$s^2=(2-\sqrt2)/4$ 及
$\kappa_R/s^2=10+6\sqrt2$。这些数值是显式的局部上界，不是全局最佳常数。

事实上，固定记录还允许把补集上的紧性最小值替换成显式的缺陷下界。对
$F=E^{\mathsf T}$ 在 $(b_\sigma,b_{-\sigma})$ 基中的表示

$$
F=\begin{pmatrix}1-t&z\\\bar z&t\end{pmatrix},
\qquad t=t_\sigma(E),
$$

令 $B=F^{1/2}$，并写每列的两个射线坐标平方为 $p_\ell,q_\ell$。正性和
$\operatorname{Tr}B^2=1$ 给出

$$
\sum_{\ell=1}^2\min\{p_\ell,q_\ell\}=\min\{t,1-t\}.
$$

具体地，在该基中写 $B=\left(\begin{smallmatrix}A&C\\\bar C&D\end{smallmatrix}\right)$；标准基的两个坐标模均为
$1/\sqrt2$，于是

$$
|p_1-q_1|+|p_2-q_2|=|A-D|(A+D)=|A^2-D^2|=|1-2t|.
$$

结合定理 8.2，若 $t\in[\delta,1-\delta]$，则
$a(E)\ge\delta/1600$。
取 $\delta=1/30$，并令
$\mathcal N_\sigma=\{E:t_\sigma(E)<\delta\}\times U(4)$。在 $t\le\delta$ 时，二阶正平方根公式

$$
F^{1/2}=\frac{F+\sqrt{\det F}\,I}{\sqrt{1+2\sqrt{\det F}}}
$$

保证两个主射线坐标的模大于 $\sqrt\delta$，而每个次坐标平方不超过 $\delta$；故引理 12.1 的同一射线分解在整个 $\mathcal N_\sigma$ 上成立，且可选列满足
$|z_\ell|^2\ge(1-\delta)/2$。补集满足 $t\in[\delta,1-\delta]$，并且
$\rho\le10$。因此

$$
\boxed{
C_{\mathrm{prod}}
\le \frac{7\,772\,800+4\,608\,000\sqrt2}{29}
<493\,000.}
$$

这里的上界仍然是保守的，但不再含未计算的紧性最小值。

还可以从合法的共享反馈路径得到全局常数的非平凡下界。令

$$
\xi_t=\cos t,\qquad \eta_t=i\sin t,
\qquad b(t)=T(\xi_t,\eta_t)^{\mathsf T},
$$

取 $E_t=\overline{b(t)}\,\overline{b(t)}^\dagger$，并令

$$
U_t=\operatorname{diag}(e^{-it},e^{it},1,1)U_+.
$$

当 $|t|<\pi/8$ 时，同一个 $U_t$ 作用于该原始结果的全部谱列，且
$\tau(E_t,U_t)=0$。此时

$$
a(E_t)=\delta(b(t))
= (\sqrt2+2c)^2\cos^2t+(\sqrt2+2s)^2\sin^2t
  -(\sqrt2+2c\cos t)^2.
$$

若

$$
\kappa_*=2-\sqrt2+2\sqrt2(2s-c)>0,
$$

则在 $t\to0$ 时直接展开得到

$$
a(E_t)=\kappa_*t^2+O(t^4),\qquad
\rho(E_t,U_t)=4t^2+O(t^4).
$$

其中效果项为 $\|E_t-E_+\|_{\mathrm F}^2=2\sin^2t$，反馈相位商项为
$4(1-\cos t)$。故任何满足定理 12.2 的全局系数都必须满足

$$
\boxed{
C_{\mathrm{prod}}\ge\frac4{\kappa_*}
 =29.1025694938\ldots .}
$$

该路径保留一个原始结果的共享反馈，因而不使用把谱列拆成独立控制的非法反例。它只给出下界；全局最佳常数仍是开放问题。

## 14. 两列加权估计与改进的显式常数

上一节的局部估计只选取一列来控制反馈。把两列的系数平方作为权重相加，可以同时保留共享反馈约束并降低常数。以下计算给出一个替代上一节数值上界的全局显式界。

取

$$
\eta=\frac1{17},\qquad
\mathcal N_\sigma=\{E:t_\sigma(E)<\eta\}\times U(4).
$$

在 $(b_\sigma,b_{-\sigma})$ 基中写

$$
F=E^{\mathsf T}=\begin{pmatrix}1-t&z\\\bar z&t\end{pmatrix},
\qquad |z|^2\le t(1-t).
$$

令 $u=\sqrt{\det F}$。二阶正平方根的恒等式为

$$
B=F^{1/2}=\frac{F+uI}{\sqrt{1+2u}}.
$$

标准基的两个坐标在该基中的模均为 $h=1/\sqrt2$，所以每一列 $b_\ell=Be_\ell$ 的 $b_\sigma$ 坐标满足

$$
|z_\ell|\ge
\frac{h\bigl(1-t-\sqrt{t(1-t)}\bigr)}{\sqrt{1+2\sqrt{t(1-t)}}}.
$$

当 $t<1/17$ 时，$\sqrt{t(1-t)}\le4/17$，从而

$$
|z_\ell|^2\ge\frac{72}{425}>\frac1{17}>|r_\ell|^2,
\qquad
b_\ell=z_\ell b_\sigma+r_\ell,\qquad r_\ell\perp b_\sigma.
$$

这里 $r_\ell$ 是 $b_{-\sigma}$ 方向分量。由完备关系，

$$
\sum_{\ell=1}^2|z_\ell|^2=1-t,
\qquad
\sum_{\ell=1}^2\|r_\ell\|^2=t.
$$

定理 8.2 给出 $t\le1600a(E)$，而二元矩阵的直接展开给出

$$
\|E-E_\sigma\|_{\mathrm F}^2
=2\bigl(t^2+|z|^2\bigr)\le2t\le3200a(E).
$$

对每一列重复引理 10.1 的模长估计。置
$\kappa_R=\|R_0\|_{\mathrm{op}}^2$、
$m_\sigma=\min_i|(R_0b_\sigma)_i|$，并令
$d_U^2=\min_{|\mu|=1}\|U-\mu U_\sigma\|_{\mathrm F}^2$。
存在相位 $\mu_\ell$ 使

$$
|z_\ell|^2m_\sigma^2d_U^2
\le4\tau_\ell+8\kappa_R\|r_\ell\|^2.
$$

两列相加并使用 $t<\eta$，得到

$$
d_U^2\le
\frac{4}{m_\sigma^2(1-\eta)}\tau(E,U)
+\frac{12800\kappa_R}{m_\sigma^2(1-\eta)}a(E).
$$

因此在 $\mathcal N_\sigma$ 内，

$$
\rho(E,U)\le
\left(3200+\frac{12800\kappa_R}{m_\sigma^2(1-\eta)}\right)a(E)
+\frac{4}{m_\sigma^2(1-\eta)}\tau(E,U).
$$

固定记录给出

$$
\kappa_R=2+\frac1{\sqrt2},\qquad
m_+^2=\frac12,
\qquad m_-^2=\sin^2(\pi/8)=\frac{2-\sqrt2}{4}.
$$

故

$$
C_{+,\mathrm{loc}}=57600+13600\sqrt2,
\qquad
C_{-,\mathrm{loc}}=139200+81600\sqrt2.
$$

在两个邻域的补集上，令 $F^{1/2}=\left(\begin{smallmatrix}A&C\\\bar C&D\end{smallmatrix}\right)$，并以标准基计算列坐标平方 $p_\ell,q_\ell$。正性、$B^2=F$ 和 $A+D=\operatorname{Tr}B$ 给出精确恒等式

$$
\sum_{\ell=1}^2\min\{p_\ell,q_\ell\}=\min\{t,1-t\}.
$$

结合定理 8.2，若 $t\in[\eta,1-\eta]$，则

$$
a(E)\ge\frac{\eta}{1600}=\frac1{27200}.
$$

另一方面，取距离定义中的较近投影，效果项至多为 $1$；任意两个四阶酉矩阵的相位商 Frobenius 距离至多为 $8$。所以

$$
\rho(E,U)\le9
$$

在补集上成立。于是补集的系数至多为 $244800$，从而整个紧参数空间满足

$$
\boxed{
C_{\mathrm{prod}}\le139200+81600\sqrt2<254600.}
$$

相应的协议积分界可以取

$$
\boxed{\displaystyle
\int\rho\,d\mu
\le8(139200+81600\sqrt2)\,\varepsilon
<2036800\,\varepsilon.}
$$

该界仍不是最佳值。为提高下界，保留同一共享反馈并令

$$
U_t=\operatorname{diag}(e^{-ixt},e^{ixt},1,1)U_+,
\qquad
x>1,
$$

同时取 $b(t)=T(\cos t,i\sin t)^{\mathsf T}$、
$E_t=\overline{b(t)}\,\overline{b(t)}^\dagger$。在 $t\to0$ 时，取相位商后的反馈偏差和效果偏差满足

$$
\rho(E_t,U_t)=2(1+x^2)t^2+O(t^4),
$$

而共同实际反馈产生的缺陷为

$$
g(E_t,U_t)=\bigl(\kappa_0+A(x-1)^2\bigr)t^2+O(t^4),
$$

其中

$$
\kappa_0=2-\sqrt2+2\sqrt2(2\sin(\pi/8)-\cos(\pi/8)),
\qquad
A=\sqrt2\bigl(\sqrt2+2\cos(\pi/8)\bigr).
$$

令 $x_*$ 为

$$
A(x_*^2-1)=\kappa_0x_*.
$$

则 $x_*=1.01500811195\ldots$，并得到合法共享反馈路径的下界

$$
\boxed{
C_{\mathrm{prod}}\ge
\frac{2(1+x_*^2)}{\kappa_0+A(x_*-1)^2}
=29.3209568043\ldots .}
$$

这里的反馈仍对该原始结果的全部谱列共同作用；可将该归一化效果作为任意正权重的一个原始协议结果，因此没有使用独立拆分反馈或后选择。

## 15. 进一步的交叉项控制

还可以直接控制两列估计中的交叉项。取

$$
\eta=\frac1{10},
\qquad \mathcal N_\sigma=\{E:t_\sigma(E)<\eta\}\times U(4).
$$

此时 $\sqrt{\eta(1-\eta)}=3/10$，正平方根公式给出每列主坐标平方至少为

$$
\frac12\frac{(3/5)^2}{8/5}=\frac9{80}>\eta.
$$

所以两列仍可相对于同一个 $b_\sigma$ 分解。沿用上一节的记号，对每列的估计先不使用平方和不等式，得到

$$
m_\sigma^2(1-t)d_U^2
\le2\tau+4\kappa_Rt+4\sqrt{2\kappa_R\tau t}.
$$

用 $2\sqrt{AB}\le32A+B/32$，其中 $A=\tau$、$B=8\kappa_Rt$，得到

$$
d_U^2\le
\frac{34}{m_\sigma^2(1-\eta)}\tau
+\frac{17\kappa_R}{4m_\sigma^2(1-\eta)}t.
$$

结合 $t\le1600a(E)$ 和 $\|E-E_\sigma\|_{\mathrm F}^2\le3200a(E)$，在 $\mathcal N_\sigma$ 内有

$$
\rho(E,U)\le
\left(3200+\frac{6800\kappa_R}{m_\sigma^2(1-\eta)}\right)a(E)
+\frac{34}{m_\sigma^2(1-\eta)}\tau(E,U).
$$

负分支给出最大的局部系数：

$$
C_{-,\mathrm{loc}}
=\frac{708800+408000\sqrt2}{9}
=142866.570\ldots .
$$

补集上仍有 $a(E)\ge\eta/1600=1/16000$ 及 $\rho\le9$，故其系数至多为 $144000$。因此得到更简洁的全局界

$$
\boxed{\qquad
C_{\mathrm{prod}}\le144000,
\qquad
\int\rho\,d\mu\le1{,}152{,}000\,\varepsilon.
\qquad}
$$

该常数只使用固定记录、共享反馈和完整两列缺陷预算；最佳全局常数仍未确定。前述显式上界均由本界严格改进。

## 16. 局部与补集阈值的再平衡

阈值与交叉项参数还可以共同再平衡。取

$$
\eta=\frac{53}{500},
\qquad \theta=1024
$$

并在交叉项中使用

$$
2\sqrt{AB}\le\theta A+\frac{B}{\theta},
\qquad A=\tau,\quad B=8\kappa_Rt.
$$

有

$$
m_\sigma^2(1-t)d_U^2
\le1026\tau+\frac{513}{128}\kappa_Rt.
$$

阈值仍保证共同主射线。事实上

$$
\sqrt{\eta(1-\eta)}=\frac{\sqrt{23691}}{500}<\frac{77}{250},
$$

故每列主坐标平方至少为

$$
\frac12\frac{(293/500)^2}{202/125}
=\frac{85849}{808000}>\frac{53}{500},
$$

而次坐标平方小于 $t<\eta$。局部负分支的 $a(E)$ 系数为

$$
3200+\frac{1600\,(513/128)(10+6\sqrt2)}{447/500}
=135791.5736\ldots,
$$

其 $\tau$ 系数约为 $7837$，不构成最大项。补集上

$$
a(E)\ge\frac{\eta}{1600},
\qquad
\frac{\rho}{g}\le\frac{14400}{\eta}
=\frac{7200000}{53}=135849.0566\ldots .
$$

因此得到当前显式上界

$$
\boxed{\qquad C_{\mathrm{prod}}<135850.\qquad}
$$

积分形式可取 $\int\rho\,d\mu\le1{,}086{,}800\,\varepsilon$。该阈值只改善常数，不改变共享反馈、奇异效果或任意小结果权重的适用范围。

## 追加锚（本行以下为增补区）
