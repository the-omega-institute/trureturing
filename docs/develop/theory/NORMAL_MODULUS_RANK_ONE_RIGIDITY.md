# Exact normal-modulus coefficients and rigidity for rank-one pairs

## 1. Domain, normalization and mathematical sources

**Definition 1.1 (The coefficient of an ordered pair).** Let $n\geq2$ and let $A,B\in M_n(\mathbb C)$ be nonzero normal matrices of rank one. The adjoint is denoted by $X^*$, the genuine right modulus is

$$
|X|=(X^*X)^{1/2},
$$

and $H\leq K$ for Hermitian matrices means that $K-H$ is positive semidefinite. Put

$$
D=|A|+|B|,\qquad
c_*(A,B)=\inf\{c\geq0:\ \exists U\in\mathcal U(n),\ |A+B|\leq D+cUDU^*\}.
\tag{1.1}
$$

Here $\mathcal U(n)$ is the full ambient unitary group. In particular, the infimum does not restrict $U$ to preserve the ranges of $A$ and $B$. The notation $c_*$ always refers to this same ordered pair.

**Citation convention 1.2 (The target and its suppliers).** The target in (1.1) is the inequality in Bourin–Lee, *Triangle inequalities for the operator symmetric modulus*, [arXiv:2602.19607v1](https://arxiv.org/abs/2602.19607v1), §4, Corollary 4.2:

$$
|A+B|\leq D+\frac14VDV^*\qquad(A,B\text{ normal}).
\tag{1.2}
$$

That corollary states sharpness for $n\geq3$, and its following paragraph asks for the best constant when $n=2$. Its introductory display instead has $V|A+B|V^*/4$ as correction; the correction in (1.1)–(1.2) is $VDV^*/4$, as in §4. The locators here bind to the indicated author version, not to an asserted identity with the journal body associated with DOI [10.1090/proc/17861](https://doi.org/10.1090/proc/17861).

The universal quarter constant is a supplied result. So is the fixed rational pair

$$
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
Q=\frac1{25}\begin{pmatrix}9&-12\\-12&16\end{pmatrix},\qquad
(A,B)=(P,-Q),
\tag{1.3}
$$

with $|P-Q|=(4/5)I_2$ and eigenvalues $2/5,8/5$ for $P+Q$, in the repository's [normal-modulus source](https://github.com/the-omega-institute/trureturing/blob/e5f431c998df9823e97567e6115f38f6951ebe7f/Problems/bourin-lee-2026-normal-modulus-constant-n2.md) and its [companion declaration source](https://github.com/the-omega-institute/trureturing/blob/e5f431c998df9823e97567e6115f38f6951ebe7f/D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.lean). Neither (1.2) nor (1.3) is a new proposition here.

The spectral theorem for normal and Hermitian matrices, uniqueness of the positive square root, Cayley–Hamilton in dimension two, and the spectral description of unitary orbits are standard matrix-analysis inputs; see Bhatia, *Matrix Analysis*, Springer, Chapters I–II, DOI [10.1007/978-1-4612-0653-8](https://doi.org/10.1007/978-1-4612-0653-8). The two-projection coordinates used below are the rank-one case of Bourin–Lee, *Involutions and angles between subspaces*, [arXiv:2602.19599v1](https://arxiv.org/abs/2602.19599v1), §1, Proposition 1.1 and Corollary 1.2. The balanced opposite-phase family $P,-Q$, including its scalar modulus and its angle parameter, is already present in Bourin–Lee, *Positive linear maps on normal matrices*, [arXiv:2006.09692v1](https://arxiv.org/abs/2006.09692v1), §2, after (2.4), and in *Diagonal and off-diagonal blocks of positive definite partitioned matrices*, [arXiv:2307.02034v3](https://arxiv.org/abs/2307.02034v3), §4 before Corollary 4.3. These classical and supplied calculations occur only as intermediate steps below. The mathematical additions are the coefficient for arbitrary positive magnitudes and complex relative phase, and its exact joint defect and stability.

**Definition 1.3 (Normalized invariants).** Write the pair, after multiplication by one common unit scalar, as

$$
A=aP,\qquad B=b\omega Q,\qquad
a,b>0,\quad |\omega|=1,
\tag{1.4}
$$

where $P,Q$ are rank-one orthogonal projections. The existence of this representation and its relation to (1.1) are established in Theorem 2.1. Define

$$
\begin{aligned}
r&=\sqrt{\operatorname{tr}(PQ)}, &s&=a+b,
&z&=\frac{a-b}{s}, &q&=\frac{4ab}{s^2}=1-z^2,\\
\eta&=\frac{1-\operatorname{Re}\omega}{2},
&x&=\sqrt{1-q(1-r^2)},
&y&=\sqrt{1-qr^2\eta},\\
x_0&=\sqrt{1-y^2}=\sqrt q\,r\sqrt\eta,
&W&=z^2+qr^2(1-\eta)=x^2-x_0^2.
\end{aligned}
\tag{1.5}
$$

All square roots in (1.5) are nonnegative. The nondegenerate domain means precisely

$$
a,b>0,\qquad 0<r<1,\qquad |\omega|=1,\quad \omega\ne1.
\tag{1.6}
$$

In that domain $0<q\leq1$, $0<\eta\leq1$, $0<x<1$, $0<y<1$, $0<x_0<1$, and $x\geq x_0$. The clauses $r=0$, $r=1$ and $\omega=1$ will be treated separately, without divisions by $y$, $x_0$ or $x+x_0$ at their endpoints.

## 2. The exact coefficient in the full ambient unitary group

**Theorem 2.1 (Unequal magnitudes and complex relative phase).** For every integer $n\geq2$ and every ordered pair of nonzero rank-one normal complex matrices $A,B$, representation (1.4) is valid up to one common unit scalar, and $D=aP+bQ$. The coefficient in (1.1) is attained. Its zero set is exactly

$$
c_*=0\quad\Longleftrightarrow\quad
r=0\ \text{or}\ r=1\ \text{or}\ \omega=1.
\tag{2.1}
$$

In the remaining domain (1.6), it is

$$
c_*=
\frac{\sqrt{(1-y)^2+2(1-x^2)(1-y)/y}-(1-y)}{1+x}>0.
\tag{2.2}
$$

Equivalently, $c_*$ is the unique positive root of

$$
\frac{1+x}{2}c^2+(1-y)c-\frac{(1-x)(1-y)}{y}=0.
\tag{2.3}
$$

For each such pair a unitary attaining (2.2) exists in $\mathcal U(n)$, and every $U\in\mathcal U(n)$ fails the inequality in (1.1) when $0\leq c<c_*$. No change of the realized pair is involved in these two assertions.

*Proof.* By the standard spectral theorem, a nonzero normal matrix of rank one has exactly one nonzero eigenvalue, counted with multiplicity. Thus the original pair has the form

$$
A=\alpha P,\qquad B=\beta Q,\qquad \alpha,\beta\ne0,
$$

with orthogonal rank-one spectral projections $P,Q$. Put $a=|\alpha|$, $b=|\beta|$, and $\xi=\overline\alpha/|\alpha|$. Multiplication of both matrices by the single scalar $\xi$ gives (1.4), with $\omega=\xi\beta/b$. Indeed $|\xi X|=|X|$ for $|\xi|=1$, so neither side of (1.1) changes. Moreover $(\alpha P)^*(\alpha P)=a^2P$, whose positive square root is $aP$; similarly $|B|=bQ$. This establishes $D=aP+bQ$ and the normalization using only the credited spectral and positive-square-root facts. Independent changes of the phases of $A$ and $B$ have not been made.

Choose unit vectors $u,v$ spanning the ranges of $P,Q$. Then $\operatorname{tr}(PQ)=|u^*v|^2$, so $0\leq r\leq1$. If $r=0$, the projections are orthogonal and

$$
(aP+b\omega Q)^*(aP+b\omega Q)=a^2P+b^2Q=D^2,
$$

hence $|A+B|=D$ and $c_*=0$. If $r=1$, equality in the vector Cauchy–Schwarz inequality gives $P=Q$, whence

$$
|A+B|=|a+b\omega|P\leq(a+b)P=D
$$

and again $c_*=0$. If $\omega=1$, the sum $aP+bQ$ is positive semidefinite, so its modulus is $D$ and $c_*=0$. In each boundary clause $c=0$ is itself feasible.

Now assume (1.6). In particular $0<qr^2\eta<1$, so $0<y<1$; also $0<x_0\leq x<1$. Let $S=\operatorname{ran}P+\operatorname{ran}Q$, which has dimension two. Both matrices and their adjoints vanish on $S^\perp$. Changing the phase of the vector $v$ leaves $Q$ unchanged and allows $u^*v=r$. In the orthonormal basis $u,(v-ru)/\sqrt{1-r^2}$ of $S$, the standard two-projection reduction is

$$
P\big|_S=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
Q\big|_S=\begin{pmatrix}r^2&r\sqrt{1-r^2}\\
r\sqrt{1-r^2}&1-r^2\end{pmatrix}.
\tag{2.4}
$$

This changes neither the relative scalar $\omega$ nor the pair being studied. In the following trace and determinant calculations all matrices are restricted to $S$, and $I_S$ is its identity. Set

$$
N=aP+b\omega Q,\qquad M=N^*N,\qquad T=M^{1/2},\qquad
\delta=ab(1-r^2)>0.
$$

Formula (2.4) gives

$$
\operatorname{tr}D=s,\qquad \det D=\delta,
\qquad \lambda_\pm(D)=\frac s2(1\pm x).
\tag{2.5}
$$

The product in the *right* modulus has the order

$$
M=a^2P+b^2Q+ab(\omega PQ+\overline\omega QP).
\tag{2.6}
$$

In particular,

$$
\begin{aligned}
\det N&=ab\omega(1-r^2),& \det M&=\delta^2,\\
\operatorname{tr}M
&=a^2+b^2+2ab r^2\operatorname{Re}\omega
=s^2y^2-2\delta.
\end{aligned}
\tag{2.7}
$$

The standard two-dimensional square-root formula, applied to these invariants, reads

$$
T=\frac{M+\delta I_S}{sy}.
\tag{2.8}
$$

For completeness, Cayley–Hamilton gives $M^2-(\operatorname{tr}M)M+\delta^2I_S=0$, and hence $(M+\delta I_S)^2=(\operatorname{tr}M+2\delta)M=s^2y^2M$. The numerator in (2.8) is positive definite and $sy>0$, so uniqueness of the positive square root proves (2.8). Consequently

$$
\operatorname{tr}T=sy,\qquad \det T=\delta.
\tag{2.9}
$$

We need the mixed trace for the same $D$ and $T$, rather than independently chosen spectral data. Using $P^2=P$, $Q^2=Q$, $\operatorname{tr}(PQ)=r^2$ and cyclicity of trace in (2.6), one obtains

$$
\begin{aligned}
\operatorname{tr}(DM)
&=a^3+b^3+ab s r^2(1+2\operatorname{Re}\omega)\\
&=s\operatorname{tr}M-s\delta,\\
\operatorname{tr}(DT)
&=\frac{\operatorname{tr}(DM)+\delta s}{sy}
=\frac{\operatorname{tr}M}{y}
=s^2y-\frac{2\delta}{y}.
\end{aligned}
\tag{2.10}
$$

Put $K=T-D$ on $S$. For two-dimensional matrices the identity

$$
\det(T-D)=\det T+\det D-\operatorname{tr}T\operatorname{tr}D+\operatorname{tr}(TD)
$$

follows by expanding the determinant. Equations (2.5), (2.9) and (2.10) yield

$$
\operatorname{tr}K=-s(1-y),\qquad
\det K=-\frac{2\delta(1-y)}{y}<0.
\tag{2.11}
$$

Thus $K$ has one positive eigenvalue $\kappa_+$ and one negative eigenvalue $\kappa_-$. Its positive eigenvalue is

$$
\kappa_+=\frac s2
\left(\sqrt{(1-y)^2+\frac{2(1-x^2)(1-y)}{y}}-(1-y)\right),
\tag{2.12}
$$

because $4\delta=s^2(1-x^2)$. Set $L=\lambda_+(D)=s(1+x)/2$ and $l=\lambda_-(D)=s(1-x)/2>0$.

Extend $K$ by zero on $S^\perp$. The standard spectral bound $D\leq LI_n$ implies $UDU^*\leq LI_n$ for **every** ambient unitary $U$, including ones that mix $S$ and $S^\perp$. If $e_+\in S$ is a unit eigenvector of $K$ for $\kappa_+$, feasibility in (1.1) forces

$$
\kappa_+=e_+^*Ke_+\leq c\,e_+^*UDU^*e_+\leq cL.
\tag{2.13}
$$

This proves the necessary bound $c\geq\kappa_+/L$ against the full group.

To attain it, choose orthonormal eigenvectors $d_+,d_-$ of $D|_S$ for $L,l$, and orthonormal eigenvectors $e_+,e_-$ of $K|_S$ for $\kappa_+,\kappa_-$. Define $U d_+=e_+$, $U d_-=e_-$ and let $U$ be the identity on $S^\perp$. This specifies a genuine unitary. At $c=\kappa_+/L$ it gives

$$
cUDU^*-K
=0\,e_+e_+^*+(cl-\kappa_-)e_-e_-^*\succeq0
\tag{2.14}
$$

on $S$, and zero on $S^\perp$. Here $cl-\kappa_->0$. It follows that the infimum is attained and equals (2.2). In particular it is positive throughout (1.6), completing both directions of (2.1). Every larger $c$ is feasible with this same $U$ as well.

Finally $\kappa_+$ satisfies $\kappa_+^2+s(1-y)\kappa_+-2\delta(1-y)/y=0$. Substitution of $\kappa_+=Lc$ and division by $s^2(1+x)/2>0$ gives (2.3). Its constant term is negative and its derivative for $c\geq0$ is $(1+x)c+1-y>0$. Hence it has exactly one positive root. This also verifies the equivalence of (2.2) and (2.3). $\square$

## 3. Extremality of the least coefficient and the exact joint defect

**Definition 3.1 (Joint defect variables).** In the domain (1.6), set

$$
C_0=\frac{x_0+y-1}{1+x_0},\qquad
d^2=\left(x_0-\frac35\right)^2+\left(y-\frac45\right)^2,
\qquad \epsilon=\frac14-c_*.
\tag{3.1}
$$

The extremal parameter locus means $a=b$, $\omega=-1$, $r=3/5$. Extremality here means that the **least feasible coefficient** $c_*$ equals $1/4$. It does not mean equality of the entire matrices in (1.1).

**Theorem 3.2 (Exact defect and coefficient extremality).** For every pair in Definition 1.1,

$$
c_*\leq\frac14,
\qquad
c_*=\frac14\quad\Longleftrightarrow\quad
a=b,\quad \omega=-1,\quad r=\frac35.
\tag{3.2}
$$

In the nondegenerate domain the following exact identity holds:

$$
\frac14-c_*
=\frac{5d^2}{8(1+x_0)}
+\frac{W\left[C_0^2/2+(1-y)/y\right]}
{(x+x_0)\left[(1+x)(C_0+c_*)/2+1-y\right]}.
\tag{3.3}
$$

Every displayed denominator in (3.3) is strictly positive. This identity is asserted only in (1.6).

*Proof.* Throughout the nondegenerate domain $x_0^2+y^2=1$ with $x_0,y\in(0,1)$. It follows that $x_0+y>1$, so $C_0>0$. For $X\geq0$ put

$$
F_X(t)=\frac{1+X}{2}t^2+(1-y)t-\frac{(1-X)(1-y)}{y}.
$$

Equation (2.3) says $F_x(c_*)=0$. The balanced-circle value $C_0$ is the positive root of $F_{x_0}$. To verify the substitution directly, use

$$
\begin{aligned}
(1+x_0)C_0^2+2(1-y)C_0
&=\frac{x_0^2-(1-y)^2}{1+x_0}\\
&=\frac{2y(1-y)}{1+x_0}
=\frac{2(1-x_0)(1-y)}{y}.
\end{aligned}
\tag{3.4}
$$

Thus $F_{x_0}(C_0)=0$. Since $x\geq x_0$,

$$
F_x(C_0)=(x-x_0)\left[\frac{C_0^2}{2}+\frac{1-y}{y}\right]\geq0.
\tag{3.5}
$$

The strict increase of $F_x$ on $[0,\infty)$ therefore gives $0<c_*\leq C_0$. Cauchy–Schwarz on the unit circle gives $3x_0+4y\leq5$ and

$$
\frac14-C_0
=\frac{5-3x_0-4y}{4(1+x_0)}
=\frac{5d^2}{8(1+x_0)}\geq0.
\tag{3.6}
$$

Here the second equality follows by expanding $d^2$ and using $x_0^2+y^2=1$. This proves $c_*\leq1/4$ in (1.6); the boundary cases have $c_*=0$ by Theorem 2.1.

Subtracting the values $F_x(C_0)$ and $F_x(c_*)$ gives the exact factorization

$$
(C_0-c_*)\left[\frac{(1+x)(C_0+c_*)}{2}+1-y\right]
=(x-x_0)\left[\frac{C_0^2}{2}+\frac{1-y}{y}\right].
\tag{3.7}
$$

Since $x^2-x_0^2=W$, substitute $x-x_0=W/(x+x_0)$ into (3.7) and add (3.6). This proves (3.3). The divisions are legitimate: $y>0$, $1+x_0>0$, $x+x_0>0$, and the last bracket in the denominator is positive because $1-y>0$. The numerator bracket is positive for the same reason. In particular, both summands in (3.3) are nonnegative, and the second vanishes exactly when $W=0$.

Equality $c_*=1/4$ consequently holds exactly when $d^2=0$ and $W=0$. The first condition says $(x_0,y)=(3/5,4/5)$. Since

$$
W=z^2+qr^2(1-\eta)
$$

is a sum of nonnegative terms and $qr^2>0$, its vanishing is equivalent to $z=0$ and $\eta=1$. These conditions mean $a=b$ and $\operatorname{Re}\omega=-1$, respectively; $|\omega|=1$ makes the latter equivalent to $\omega=-1$. Then $q=1$ and $x_0=r$, so $r=3/5$. Conversely these three parameter conditions give $W=d^2=0$ and hence $c_*=1/4$. None of the three boundary clauses has that value. This proves (3.2). $\square$

## 4. Quantitative stability and the meaning of its invariant error

**Definition 4.1 (Invariant error).** For the rank-one pairs of Definition 1.1 define

$$
\Delta=\sqrt{W+d^2},\qquad
 d^2=\left(x_0-\frac35\right)^2+\left(y-\frac45\right)^2.
\tag{4.1}
$$

This expression is defined also on the boundary by (1.5); no division is used in (4.1). It measures error in the normalized magnitudes, overlap and relative phase from Definition 3.1's locus. It is not defined as a metric on the space of matrix pairs or as an absolute distance between unnormalized matrices.

**Theorem 4.2 (Joint stability with exponent one half).** For every $n\geq2$ and pair in Definition 1.1, if $\epsilon=1/4-c_*\leq1/16$, then the pair lies in (1.6) and

$$
W+d^2\leq\frac{2608}{15}\epsilon,
\qquad
\Delta\leq\sqrt{\frac{2608}{15}}\sqrt\epsilon.
\tag{4.2}
$$

More precisely, in that range,

$$
\begin{aligned}
\frac{|a-b|}{a+b}&\leq\Delta,&
\left|\frac{a}{a+b}-\frac12\right|
=\left|\frac{b}{a+b}-\frac12\right|&\leq\frac\Delta2,\\
\left|r-\frac35\right|&\leq\sqrt2\,\Delta,&
|1+\omega|&\leq\frac{32}{3}\Delta.
\end{aligned}
\tag{4.3}
$$

For arbitrary pairs in Definition 1.1, $\Delta=0$ exactly on the extremal parameter locus. For any sequence of such pairs, $\Delta\to0$ if and only if

$$
\frac{a-b}{a+b}\longrightarrow0,\qquad
r\longrightarrow\frac35,\qquad
\omega\longrightarrow-1.
\tag{4.4}
$$

The quantities $c_*,\Delta,z,r,\omega$ are invariant under simultaneous unitary conjugation and multiplication of both matrices by a common nonzero complex scalar. No optimality of the numerical constant in (4.2) is asserted.

*Proof.* By Theorems 2.1 and 3.2, $0\leq\epsilon\leq1/4$, and any boundary pair has $\epsilon=1/4$. The assumed range therefore lies in (1.6). Equation (3.3) first gives

$$
d^2\leq\frac{8(1+x_0)}5\epsilon\leq\frac{16}{5}\epsilon.
\tag{4.5}
$$

Also $C_0\geq c_*=1/4-\epsilon\geq3/16$, whereas

$$
C_0=\frac{x_0+y-1}{1+x_0}\leq\frac{x_0}{1+x_0}\leq x_0.
$$

It follows that $x_0\geq3/16$ and

$$
\frac{C_0^2}{2}+\frac{1-y}{y}
\geq1-y=\frac{x_0^2}{1+y}\geq\frac9{512}.
\tag{4.6}
$$

On the other hand $x,x_0\leq1$ and $0<c_*\leq C_0\leq1/4$, so

$$
(x+x_0)\left[\frac{(1+x)(C_0+c_*)}{2}+1-y\right]
\leq2\left(\frac12+1\right)=3.
\tag{4.7}
$$

Using the positive denominator in (3.3), equations (4.6)–(4.7) imply

$$
\epsilon\geq\frac3{512}W,\qquad
W\leq\frac{512}{3}\epsilon.
\tag{4.8}
$$

Adding (4.5) and (4.8) proves (4.2), since $512/3+16/5=2608/15$.

For the meaning of $\Delta$, the identity $W=z^2+qr^2(1-\eta)$ gives $|z|\leq\sqrt W\leq\Delta$, and $a/s=(1+z)/2$, $b/s=(1-z)/2$. Furthermore,

$$
0\leq r^2-x_0^2=r^2z^2+qr^2(1-\eta)\leq W.
\tag{4.9}
$$

Since $r\geq x_0\geq0$, this entails $(r-x_0)^2\leq W$. Thus

$$
\left|r-\frac35\right|
\leq\sqrt W+\left|x_0-\frac35\right|
\leq\sqrt2\sqrt{W+d^2}=\sqrt2\,\Delta.
\tag{4.10}
$$

Finally $|1+\omega|^2=4(1-\eta)$, and $qr^2\geq x_0^2\geq9/256$ in the stated range. Hence

$$
|1+\omega|\leq\frac{2\sqrt W}{\sqrt q\,r}
\leq\frac{32}{3}\sqrt W\leq\frac{32}{3}\Delta.
\tag{4.11}
$$

This proves (4.3).

Without assuming near extremality, $\Delta=0$ implies $z=0$, $x_0=3/5$, $y=4/5$ and $qr^2(1-\eta)=0$. Then $q=1$, $r>0$, $\eta=1$, and $r=x_0=3/5$. The converse follows by substitution. If $\Delta\to0$ along any sequence, then $z\to0$ and (4.10), whose proof did not use the near-extremal range, gives $r\to3/5$. Consequently $qr^2\to9/25>0$, and $qr^2(1-\eta)\leq W\to0$ gives $\eta\to1$ and $\omega\to-1$. Conversely the three convergences in (4.4) imply $q\to1$, $\eta\to1$, $x_0\to3/5$, $y\to4/5$ and $W\to0$ by (1.5), proving $\Delta\to0$.

Simultaneous unitary conjugation preserves the nonzero eigenvalues and $\operatorname{tr}(PQ)$. Multiplication by a common nonzero complex scalar multiplies $a,b$ by the same positive number and leaves their relative phase unchanged. It therefore leaves all the normalized invariants and $\Delta$ unchanged; it multiplies the two sides of the feasibility inequality by the same positive number, so it also leaves $c_*$ unchanged. This proves the asserted invariance, with no conclusion about absolute unnormalized matrix distances. $\square$

**Theorem 4.3 (Sharpness of the stability exponent).** Along the balanced opposite-phase angle family

$$
a=b>0,\qquad \omega=-1,\qquad r=\frac35+h,
$$

with $h\to0$ and $0<r<1$, one has

$$
\epsilon=\frac{625}{1024}h^2+o(h^2),\qquad
\Delta=\frac54|h|+o(|h|).
\tag{4.12}
$$

In particular, for no exponent $\alpha>1/2$ does there exist a finite constant $K$ such that $\Delta\leq K\epsilon^\alpha$ for all such pairs in a neighborhood of the extremal locus.

*Proof.* This family is realized, for each $r\in(0,1)$ and each $n\geq2$, by the projections in (2.4) on a fixed two-dimensional subspace, extended by zero on its orthogonal complement. It is the supplied angle family cited in Convention 1.2. Here $q=\eta=1$, $W=0$, $x=x_0=r$ and $y=\sqrt{1-r^2}$. The coefficient in Theorem 2.1 consequently reduces to the balanced value

$$
c_*=C_0=\frac{r+\sqrt{1-r^2}-1}{1+r}.
$$

At $r=3/5$, the derivative of $\sqrt{1-r^2}$ is $-3/4$. Therefore

$$
y=\frac45-\frac34h+O(h^2),\qquad
d^2=h^2+\left(-\frac34h+O(h^2)\right)^2
=\frac{25}{16}h^2+o(h^2).
$$

The first summand of (3.3) is now the entire defect. Since $1+x_0\to8/5$,

$$
\epsilon=\frac{5d^2}{8(1+x_0)}
=\frac{25}{64}\cdot\frac{25}{16}h^2+o(h^2)
=\frac{625}{1024}h^2+o(h^2).
$$

Also $\Delta=\sqrt{d^2}=(5/4)|h|+o(|h|)$. For $\alpha>1/2$, the ratio $\Delta/\epsilon^\alpha$ is a positive constant times $|h|^{1-2\alpha}(1+o(1))$, which tends to infinity as nonzero $h\to0$. This proves the exponent assertion. $\square$

## 5. Primary-source correspondence and mathematical scope

**Citation convention 5.1 (Adjacent inequalities).** The correspondence of the sources is as follows; each article locator denotes the stated arXiv author version.

Bourin–Lee, [arXiv:2006.09692v1](https://arxiv.org/abs/2006.09692v1), Theorem 2.2, proves the positive-map estimate

$$
|\Phi(N)|\leq\beta\Phi(|N|)+\frac1{4\beta}V\Phi(|N|)V^*,\qquad \beta>0,
$$

for normal $N$ and a positive map $\Phi$. Taking $N=A\oplus B$ and $\Phi\bigl(\begin{smallmatrix}X&Y\\Z&R\end{smallmatrix}\bigr)=X+R$, with $\beta=1$, supplies the upper bound (1.2); this is precisely the specialization stated in [arXiv:2602.19607v1](https://arxiv.org/abs/2602.19607v1), §4. The angle example following (2.4) of the older positive-map article supplies $\lambda_{\min}(P+Q)=1-r$ and $|P-Q|=\sqrt{1-r^2}I_2$ on the support. These are attributed intermediates, not separate new results of this source.

Bourin–Lee, [arXiv:2307.02034v3](https://arxiv.org/abs/2307.02034v3), §4, Propositions 4.1–4.2, concerns Schur products; Corollary 4.3 concerns Hermitian $S,T$ with $\pm S\leq T$ and a unitary-orbit correction by $T/4$. Its Corollary 4.4 and Remark 4.5 instead concern the scalar correction $(k/4)I$ for sums of $k$ contractions. These targets have different quantifiers and corrections from the least coefficient of one specified pair in (1.1).

Aouichaoui–Lee, *Solutions to some open problems in matrix analysis*, [arXiv:2609.20094v2](https://arxiv.org/abs/2609.20094v2), Introduction and §2, Theorem 2.2, also treats the scalar correction $(k/4)I$ for contractions. Its Introduction states the standard unitary-orbit order criterion: for Hermitian $H,J$, there is a unitary $U$ with $H\leq UJU^*$ exactly when their decreasing eigenvalues obey the corresponding coordinatewise inequalities. The eigenvector argument (2.13)–(2.14) is the needed instance of this standard spectral principle, with the ambient quantifier retained.

The mathematical argument in Colbrook, [*MI-03: Resolution*, `solution.tex`](https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/matrix-inequalities-and-norms/MI-03/solution.tex), proves sharpness of the scalar correction $(k/4)I$ for $k\geq2$ contractions, using complex rank-one contractions $e_1v_j^*$ in dimension two and Hermitian contractions in dimension three. Those dimension-two summands are not the normal rank-one domain (1.4), and the scalar-$I$ correction is not $cUDU^*$. Only that mathematical argument is relevant to this comparison.

Zhang, *Operator symmetric moduli and sharp triangle inequalities*, [arXiv:2603.01046v1](https://arxiv.org/abs/2603.01046v1), Introduction and §2, studies arithmetic and quadratic symmetric moduli and inequalities for unitarily invariant norms. Its Lemma 2.4 records standard rank-one modulus calculations; Theorem 2.5 exhibits norm sharpness in dimension three. Zhang, *An operator triangle inequality for the quadratic symmetric modulus*, [arXiv:2602.01463v3](https://arxiv.org/abs/2602.01463v3), §1.2 and §4, treats the quadratic symmetric modulus and its equality conditions. In the latter article’s quadratic-modulus theorems the modulus is $[(X^*X+XX^*)/2]^{1/2}$, whereas (2.6)–(2.8) use the genuine right modulus even when $A+B$ is not normal.

Bourin–Lee, *Matrix inequalities from a two variables functional*, [arXiv:1511.06977v3](https://arxiv.org/abs/1511.06977v3), (1.3), Proposition 1.1, Theorem 2.9 and Corollary 2.10, concerns weak log-majorization for normal matrices and positive maps. A log-majorization conclusion is distinct from the fixed-pair Loewner inequality with the unitary-orbit correction in (1.1).

The attribution of the mathematical additions in Convention 1.2 is relative to the pinned repository sources cited there and the specified primary-source versions and sections in this convention. This bounded correspondence makes no assertion of worldwide priority, exhaustive absence from the literature, identity of author and journal texts, or present unresolved status of an external problem. Theorems 2.1–4.3 concern nonzero rank-one normal pairs only; they provide an attaining unitary, not a classification of all attaining unitaries, and classify extremality of $c_*$ in that domain, not equality cases for all normal or higher-rank matrices.

## 追加锚（本行以下为增补区）
