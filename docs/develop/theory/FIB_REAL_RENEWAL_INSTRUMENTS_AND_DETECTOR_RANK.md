# Real renewal instruments and detector rank

## 1. The law, coordinate field and memory being compared

**Definition 1.1 (Fixed monomial-geometric renewal law).** Fix an integer $n\ge1$ and a real parameter $0<q<1$. Throughout, $k\ge0$ is the number of zeros preceding the next tick, whose visible symbol is one. The interevent duration is $k+1$. Set

$$
Z_n(q)=\sum_{k=0}^{\infty}k^nq^k,\qquad
\gamma_k=\frac{k^nq^k}{Z_n(q)},\qquad
D_n=\left\lceil\frac n2\right\rceil+1. \tag{1.1}
$$

The term $0^n$ is zero. These are the parameters of [Chapter 35, equations (35.1)–(35.2)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#35-exact-monomial-geometric-laws-and-the-memory-comparison). The ratio test gives a finite positive $Z_n(q)$ and finite moments of every order. In particular,

$$
\gamma_0=0,\quad \gamma_k>0\ (k\ge1),\quad
\sum_{k\ge0}\gamma_k=1,\quad
S_a=\sum_{j\ge a}\gamma_j,\quad
\mu=\sum_{k\ge0}(k+1)\gamma_k
=1+\frac{Z_{n+1}(q)}{Z_n(q)},\quad \nu=\mu^{-1}. \tag{1.2}
$$

The stationary renewal law meant here is specified on every finite binary word. For a word with $r\ge1$ ones, its unique decomposition into boundary zero runs and internal gaps has probabilities

$$
\begin{aligned}
P(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{i=1}^{r-1}\gamma_{g_i},\\
P(0^N)&=\frac1\mu\sum_{a\ge0}S_{N+a}
=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j.
\end{aligned} \tag{1.3}
$$

Here $a,b,g_i,N$ are nonnegative integers; the product is one when $r=1$, and $N=0$ is the empty word. The construction below proves that these are the actual instrument probabilities, including the boundary tails, rather than merely identifying a conditional gap distribution.

**Definition 1.2 (Real coordinates for a complex-memory instrument).** The memory is $\mathbb C^D$ with its usual Hermitian inner product. A real instrument means two completely positive maps on the full algebra $M_D(\mathbb C)$,

$$
\Phi(X)=\sum_\alpha L_\alpha X L_\alpha^*,\qquad
\Psi(X)=\sum_i J_i X J_i^*,\qquad
\sum_\alpha L_\alpha^*L_\alpha+\sum_iJ_i^*J_i=I_D, \tag{1.4}
$$

whose displayed Kraus matrices are real in one fixed orthonormal basis. The zero branch is $\Phi$, and the tick branch is $\Psi$. Operator stars denote adjoints, and agree with transposes on these real matrices. A Choi rank is the minimum number of Kraus matrices for the specified branch, equivalently the dimension of the complex linear span of any Kraus family for that branch. It is distinct from the matrix rank of one Kraus operator and from the memory dimension.

Every persistent quantum or classical register is included in $D$. The source coordinate introduced for odd $n$ is part of this memory. Kraus indices are summed within their visible branch and do not persist as a measurement record. All matrices and parameters are fixed in time; there is no external correlated input or uncounted controller. A fresh auxiliary discarded after one step is not a persistent register. If any auxiliary or record is retained to influence later steps, it belongs to the memory being counted.

The comparison of real and complex coefficients concerns this same complex-memory model. It does not identify a real-Hilbert-space physical resource theory with complex quantum mechanics. Exact matrix entries impose no claim about finite precision, preparation, control cost or thermodynamic cost. Equality with the FIB legal language will concern visible support only.

**Definition 1.3 (Mathematical scope and dependencies).** The results below are ordinary mathematical derivations. General Lean proofs of the completion, the uniform realizations and their full stationary interfaces remain unfinished. The dimension lower bound used in Section 6 retains the handwritten finite-CP growth input of Chapter 31 and the reachability/radius argument of Chapter 32, as assembled in [Chapter 40, Theorem 40.1 and equations (40.1)–(40.3)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#40-actual-tails-force-the-sharp-quantum-dimension-and-kraus-parity). The mixed vector-recurrence parity argument in Chapter 29, applied in Chapter 40, Theorem 40.2 and (40.4), supplies a separate zero-branch lower bound without the finite-CP growth input.

The rank-one-effect completion in [Chapter 36, equations (36.1)–(36.3)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#36-a-faithful-gramian-completes-the-actual-renewal-instrument) is the input extended in Section 2. The factorization in [Chapter 37, equation (37.2)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#37-exact-even-amplitudes-and-odd-forward-difference-sums) is reused with its derivation in Section 3. Conjugate-root factorization, real and imaginary parts of a polynomial, and the Newton binomial basis are classical ingredients, not new mathematical claims of priority. The real odd realization and the cubic detector construction are repository derivations for the specified law; no exhaustive worldwide novelty claim is made.

## 2. A finite detector effect and an actual pure reset

**Theorem 2.1 (Faithful stable Gramian completion with several detector rows).** Let

$$
\mathcal T(X)=\sum_{\alpha=1}^{s}K_\alpha X K_\alpha^*,\qquad
F=\sum_{i=1}^{\ell}f_if_i^*\ne0,
\qquad F\ge0,\qquad \rho(\mathcal T)<1, \tag{2.1}
$$

on $M_d(\mathbb C)$, with a finite Kraus family and finitely many detector columns. The spectral radius is that of the complex linear superoperator on the full matrix algebra. Write $\mathcal T^*(Y)=\sum_\alpha K_\alpha^*YK_\alpha$ for its trace dual. Suppose

$$
Q=\sum_{k\ge0}(\mathcal T^*)^k(F)>0. \tag{2.2}
$$

For any nonzero raw reset vector $x$, define

$$
\begin{aligned}
S&=Q^{1/2},& z&=x^*Qx,& b&=Sx/\sqrt z,& \tau&=bb^*,\\
L_\alpha&=SK_\alpha S^{-1},&
J_i&=bf_i^*S^{-1},&
E&=S^{-1}FS^{-1}.
\end{aligned} \tag{2.3}
$$

These operators form the complete instrument (1.4), with

$$
\Psi(X)=\tau\operatorname{Tr}(EX),\qquad
\operatorname{rank}_{\rm Choi}\Psi=\operatorname{rank}F,\qquad
\rho(\Phi)=\rho(\mathcal T)<1. \tag{2.4}
$$

Every positive-probability tick has normalized output $\tau$, a pure density, even when $F$ has rank greater than one. Its actual gap probabilities and survival probabilities are

$$
\begin{aligned}
\gamma_k&=\operatorname{Tr}\Psi\Phi^k(\tau)
=\frac{\operatorname{Tr}[F\mathcal T^k(xx^*)]}{z},\\
\sum_{k\ge0}\gamma_k&=1,\qquad
\operatorname{Tr}\Phi^a(\tau)=\sum_{k\ge a}\gamma_k.
\end{aligned} \tag{2.5}
$$

If the raw matrices and vectors are real, so are $Q,S,b,L_\alpha,J_i$. The instrument is completely positive and complete for every complex positive input, including inputs with nonreal coherences.

Proof. Choose $r$ with $\rho(\mathcal T)<r<1$. Finite-dimensional Jordan estimates bound powers of $\mathcal T$ and its dual by $Cr^k$ in any fixed matrix-space norm, after increasing $C$. Consequently (2.2) converges in norm and is a sum of positive operators. Shifting the convergent series gives

$$
Q-\mathcal T^*(Q)=F. \tag{2.6}
$$

It is the unique solution: if $H=\mathcal T^*(H)$, iteration and stability give $H=0$. Positivity alone would allow a singular solution. The strict positivity in (2.2) is needed to obtain invertible $S$, positive scalar $z$, and $\|b\|=1$.

The normalized zero and tick effects satisfy

$$
\begin{aligned}
\sum_\alpha L_\alpha^*L_\alpha
&=S^{-1}\mathcal T^*(Q)S^{-1}=I-E,\\
\sum_iJ_i^*J_i
&=S^{-1}\Big(\sum_if_if_i^*\Big)S^{-1}=E,\\
\sum_iJ_iXJ_i^*
&=bb^*\sum_if_i^*S^{-1}XS^{-1}f_i
=\tau\operatorname{Tr}(EX).
\end{aligned} \tag{2.7}
$$

Thus $0\le E\le I$. Both branches are trace nonincreasing on positive inputs, their sum preserves trace, and a tick with nonzero probability resets to $\tau$. Each nonzero $J_i$ has matrix rank one; these operators need not be scalar multiples of one another. Indeed the map $g\mapsto bg^*S^{-1}$ is injective as a conjugate-linear map, because $b\ne0$ and $S$ is invertible. Hence the Kraus span has dimension $\dim\operatorname{span}\{f_i\}=\operatorname{rank}F$, proving the Choi-rank assertion. Equivalently, in the input-output Choi convention the tick Choi matrix is $E^{\mathsf T}\otimes\tau$, with rank $\operatorname{rank}E$.

For $\Gamma(X)=SXS$, the invertible linear similarity

$$
\Phi=\Gamma\mathcal T\Gamma^{-1},\qquad
\Phi^k(\tau)=\frac{S\mathcal T^k(xx^*)S}{z} \tag{2.8}
$$

proves stability and the first identity of (2.5). The scalar normalization is exactly

$$
z=x^*Qx=\sum_{k\ge0}\operatorname{Tr}[F\mathcal T^k(xx^*)]. \tag{2.9}
$$

No raw trace-contraction hypothesis was used. The completed branches, rather than the raw $K_\alpha$, are the instrument. If $s_a=\operatorname{Tr}\Phi^a(\tau)$, completeness gives $s_a-s_{a+1}=\gamma_a$. Stability gives $s_a\to0$, so telescoping yields the survival identity in (2.5). In particular a tick occurs eventually with probability one; there is no mass hidden at an infinite first gap.

For the real assertion, each term of (2.2) is real symmetric. If a real symmetric matrix $Q$ is positive definite on real vectors, then for $y=u+iv$ with $u,v$ real,

$$
y^*Qy=u^{\mathsf T}Qu+v^{\mathsf T}Qv, \tag{2.10}
$$

because the imaginary cross terms cancel. This is positive for every nonzero complex $y$. The same identity with nonstrict inequalities gives the corresponding positive-semidefinite statement. Thus real faithfulness proves complex Hermitian faithfulness and invertibility. Real orthogonal spectral decomposition constructs the unique positive square root $S$ as a real symmetric matrix. Formula (2.3) is then real. Nevertheless every Kraus expression acts on all of $M_d(\mathbb C)$; its amplifications are sums of conjugations by $L_\alpha\otimes I$ or $J_i\otimes I$ and preserve positivity. Equation (2.7) is an operator identity, not a calculation restricted to real diagonal states. This proves complete positivity and trace completeness on the full complex input cone. $\square$

Within this theorem, there is a useful exact observability test. For a word $w=(\alpha_1,\ldots,\alpha_k)$ set $K_w=K_{\alpha_k}\cdots K_{\alpha_1}$; the empty word is the identity. Expanding the CP power gives

$$
y^*Qy=\sum_{k\ge0}\sum_{|w|=k}\sum_i|f_i^*K_wy|^2. \tag{2.11}
$$

Thus $Q>0$ if and only if no nonzero memory vector is invisible to every word and every detector row. A positive value of $z$ for one reset vector does not by itself prove this full-memory condition. The constructions below establish it directly.

## 3. Every odd degree with real matrices and at most two detector rows

**Theorem 3.1 (Real odd-degree realization in $m+2$ dimensions).** For every $m\ge0$, $n=2m+1$ and $0<q<1$, there is a real instrument on $\mathbb C^{m+2}$ with actual gap probabilities (1.1), pure post-tick density $\tau$, zero-branch Choi rank exactly two, and tick-branch Choi rank at most two. Its raw observability Gramian is faithful on all $m+2$ coordinates, and its zero-word reachable span from $\tau$ is the full memory. At $m=0$ a single detector row suffices.

Proof. First factor the positive forward difference

$$
\Delta_n(t)=(t+1)^n-t^n. \tag{3.1}
$$

For odd $n$, the function $t\mapsto t^n$ is strictly increasing on the real line. Therefore $\Delta_n(t)>0$ for every real $t$, and its degree is $2m$ with leading coefficient $n$. For $m>0$ it has no real roots. Real coefficients pair the complex roots, with multiplicity, into conjugate pairs. Choose one root $\zeta_j$ from each pair and set

$$
p(t)=\sqrt n\prod_{j=1}^{m}(t-\zeta_j),\qquad
p(t)\overline{p(t)}=\Delta_n(t)\quad(t\in\mathbb R). \tag{3.2}
$$

This is precisely the factorization input of Chapter 37, (37.2). Write the coefficients of $p$ as real and imaginary parts to obtain real polynomials $a_1,a_2$ with

$$
p=a_1+ia_2,\qquad
\Delta_n=a_1^2+a_2^2,\qquad
\deg a_i\le m. \tag{3.3}
$$

The leading coefficient of $p$ is the real number $\sqrt n$, so $a_1$ has degree exactly $m$ and leading coefficient $\sqrt n$, while $a_2$ has degree at most $m-1$. For $m=0$ use $p=a_1=1$, $a_2=0$. Conjugate factorization and the two-square identity are classical algebraic steps inside this construction.

On a real target space of dimension $m+1$, with basis $e_0,\ldots,e_m$, fix the forward nilpotent shift

$$
Je_j=e_{j+1}\ (0\le j<m),\qquad Je_m=0,\qquad U=I+J,\qquad v=e_0. \tag{3.4}
$$

This shift orientation is chosen so that the fixed input $v$ generates the Newton basis at the output. For each $i$ there is a unique real column $h_i$ such that

$$
a_i(t)=\sum_{r=0}^{m}(h_i)_r\binom tr,
\qquad (h_i)_r=(\delta^ra_i)(0),\qquad
\delta a(t)=a(t+1)-a(t). \tag{3.5}
$$

The binomial polynomials have different degrees and nonzero leading coefficients, so they form a basis. The coefficient formula follows by iterating $\delta\binom tr=\binom t{r-1}$ and evaluating at zero. The finite binomial expansion of $U^t$ now gives, for every natural $t$,

$$
U^tv=\sum_{r=0}^{m}\binom tr e_r,\qquad
h_i^{\mathsf T}U^tv=a_i(t),\qquad
(h_1)_m=m!\sqrt n\ne0. \tag{3.6}
$$

Add a single source coordinate $s$ orthogonal to the target. On the full dimension $D=m+2$, define the real raw data

$$
\begin{aligned}
A&=\begin{pmatrix}U&0\\0&1\end{pmatrix},&
B&=|(v,0)\rangle\langle s|,& x&=s,\\
f_i&=(h_i,0),&
H&=h_1h_1^{\mathsf T}+h_2h_2^{\mathsf T},&
F&=\begin{pmatrix}H&0\\0&0\end{pmatrix},\\
K_A&=\sqrt q\,A,&K_B&=\sqrt q\,B,&
\mathcal T(X)&=q(AXA^{\mathsf T}+BXB^{\mathsf T}).
\end{aligned} \tag{3.7}
$$

A zero detector column may be omitted. The source and all target coordinates belong to the memory. The two-square coefficients have been placed in the effect $F$, while the injection vector $v$ and both no-tick matrices are real and independent of a root choice.

We compute the entire word sum, with its multiplicities. The relations $As=s$ and $BA^rB=0$ for every $r\ge0$ show that the all-$A$ word remains in the source and is invisible to $F$, whereas any word with two or more $B$ factors vanishes. For length $k\ge1$, every word with one $B$ has exactly the form $A^tBA^{k-1-t}$ for a unique $t\in\{0,\ldots,k-1\}$. Acting on $s$ it gives $(U^tv,0)$. Thus each position contributes once, and the separate word probabilities give

$$
\begin{aligned}
\operatorname{Tr}[F\mathcal T^k(ss^{\mathsf T})]
&=q^k\sum_{t=0}^{k-1}\sum_{i=1}^{2}|h_i^{\mathsf T}U^tv|^2\\
&=q^k\sum_{t=0}^{k-1}\big((t+1)^n-t^n\big)
=q^kk^n.
\end{aligned} \tag{3.8}
$$

For $k=0$, the source is invisible and the empty sum is zero, agreeing with $0^n$. There are no cross terms between different words or different detector rows: a CP sum adds their squared amplitudes. In particular $k$ is the preceding-zero count, not the duration $k+1$.

For stability, decompose the full complex matrix algebra into target-target, target-source, source-target and source-source blocks. The $A$ contribution preserves these blocks, with diagonal superoperator actions $qUXU^{\mathsf T}$, $qUX$, $qXU^{\mathsf T}$ and $qX$, respectively. Each has only eigenvalue $q$, since $U$ is unipotent. The $B$ contribution sends only the source-source block to the target-target block, as $qX_{ss}vv^{\mathsf T}$. Ordering this one-way coupling makes the full superoperator block triangular. Consequently

$$
\operatorname{spec}(\mathcal T)=\{q\},\qquad \rho(\mathcal T)=q<1. \tag{3.9}
$$

This is the spectrum on all matrices, including off-diagonal coherences.

The same word decomposition evaluates the full Gramian. An all-$A$ word contributes only a target-supported detector row; a one-$B$ word contributes only a source-supported row. Therefore no target-source cross block occurs, and

$$
Q=\begin{pmatrix}C&0\\0&Z_n(q)\end{pmatrix},\qquad
C=\sum_{t\ge0}q^t(U^t)^{\mathsf T}HU^t. \tag{3.10}
$$

Its source entry is (3.8) summed over all $k$. To prove $C>0$, let $y$ be a real target vector with $y^{\mathsf T}Cy=0$. Every nonnegative summand then vanishes, so in particular $h_1^{\mathsf T}U^ty=0$ for every natural $t$. The polynomial identity

$$
h_1^{\mathsf T}U^ty
=\sum_{r=0}^{m}\binom tr h_1^{\mathsf T}J^ry \tag{3.11}
$$

has infinitely many zeros, forcing all its binomial coefficients to vanish. The coefficient for $r=m$ is $(h_1)_m y_0$, hence $y_0=0$. The coefficient for $r=m-1$ then gives $(h_1)_m y_1=0$. Descending through $r=m-2,\ldots,0$ gives $y_2=\cdots=y_m=0$. This proves full target observability from the degree-$m$ coefficient; positivity of a scalar trace alone would not give it. Equation (2.10) extends the conclusion to complex vectors. Since $Z_n(q)>0$, (3.10) is faithful on the entire complex memory.

Theorem 2.1 now applies with $z=Z_n(q)$. In these block coordinates the completed matrices can be written explicitly as

$$
\begin{aligned}
\tau&=ss^{\mathsf T},\qquad b=s,\\
L_A&=\sqrt q\begin{pmatrix}C^{1/2}UC^{-1/2}&0\\0&1\end{pmatrix},\\
L_B&=\sqrt{q/Z_n(q)}\,|(C^{1/2}v,0)\rangle\langle s|,\\
J_i&=|s\rangle\langle(C^{-1/2}h_i,0)|,\qquad
E=\begin{pmatrix}C^{-1/2}HC^{-1/2}&0\\0&0\end{pmatrix}.
\end{aligned} \tag{3.12}
$$

These are real matrices acting on the complex memory. As a direct normalization check on the blocks, the target and source entries of the Stein equation are

$$
C-qU^{\mathsf T}CU=H,\qquad
(1-q)Z_n(q)=qv^{\mathsf T}Cv. \tag{3.13}
$$

They imply $\sum L^*L+\sum J^*J=I$ in (3.12), including the source diagonal. The common tick output is the same pure $ss^{\mathsf T}$ for all detector indices. Equation (3.8) and (2.5) give the normalized law and properness.

The matrices $A$ and $B$ are linearly independent over $\mathbb C$: $A$ is invertible and block diagonal, whereas $B$ is a nonzero off-diagonal rank-one matrix. Multiplication by $\sqrt q$ and invertible similarity preserve independence. The zero Choi rank is exactly two. The effect has rank at most two, hence so does the tick Choi matrix; at $m=0$, $h_1=(1)$ and $h_2=0$, so the tick rank is one.

Finally the raw reachable span contains $s$ and every $A^tBs=(U^tv,0)$. The vectors $v,Jv,\ldots,J^mv$ are the target basis, and the powers of $U$ span the same cyclic space because $J=U-I$. Thus all $m+2$ coordinates are reachable. Completed words satisfy $L_wb=SK_wx/\sqrt z$, so the invertible $S$ preserves full reachability.

For the degree-one endpoint of this construction, the dimension is two, with one tick Kraus operator and two zero Kraus operators. In target-source order its exact matrices and invariant density are

$$
\begin{aligned}
Q&=\operatorname{diag}\big((1-q)^{-1},q(1-q)^{-2}\big),\\
L_A&=\sqrt q\,I_2,\qquad
L_B=\sqrt{1-q}\,|e_0\rangle\langle s|,\qquad
J=\sqrt{1-q}\,|s\rangle\langle e_0|,\\
\tau&=|s\rangle\langle s|,\qquad \rho_*=I_2/2,\\
\gamma_k&=k(1-q)^2q^{k-1}\quad(k\ge1),\qquad \gamma_0=0.
\end{aligned} \tag{3.14}
$$

Here $U=1$, $v=h_1=1$, $C=(1-q)^{-1}$ and $Z_1(q)=q(1-q)^{-2}$, so (3.12) gives all three operators. Their effects sum to $qI_2+(1-q)|s\rangle\langle s|+(1-q)|e_0\rangle\langle e_0|=I_2$. On $I_2/2$ the zero contribution is $qI_2/2+(1-q)|e_0\rangle\langle e_0|/2$ and the tick contribution is $(1-q)|s\rangle\langle s|/2$, proving invariance. The gaps follow from (1.1). This is the real endpoint already displayed in Chapter 37, (37.5), included here to specify the degenerate one-effect interface of Theorem 3.1. $\square$

## 4. A cubic real construction with one detector

**Theorem 4.1 (Cubic dimension three, zero Choi rank two and tick Choi rank one).** For every $0<q<1$, there is a real instrument on $\mathbb C^3$ realizing (1.1) for $n=3$, with a pure actual post-tick reset, zero Choi rank exactly two and tick Choi rank exactly one. It is obtained from the following raw data in the ordered basis $e_0,e_1,e_2$:

$$
A=\begin{pmatrix}
1&\sqrt3&1\\
0&1&0\\
0&0&1
\end{pmatrix},\qquad
B=\begin{pmatrix}
0&1&0\\
0&0&1\\
0&0&0
\end{pmatrix},\qquad
x=e_2,\quad f=e_0,\quad F=ff^{\mathsf T}, \tag{4.1}
$$

with $K_A=\sqrt q A$, $K_B=\sqrt q B$ and $\mathcal T(X)=q(AXA^{\mathsf T}+BXB^{\mathsf T})$.

Proof. Write $A=I+N$ with $N=\sqrt3 E_{01}+E_{02}$. The matrix unit $E_{ij}$ sends $e_j$ to $e_i$. Then $N^2=0$, $BN=0$, $B^2=E_{02}$, $B^3=0$ and $NB^2=0$. These relations classify every interleaved word; no commutation of $A$ and $B$ is assumed.

For the all-$A$ word, $A^k=I+kN$, and

$$
f^{\mathsf T}A^kx=k. \tag{4.2}
$$

For exactly one $B$, every length-$k$ word is $A^tBA^{k-1-t}$ with a unique $0\le t<k$. Since $BA^r=B$ for every $r\ge0$, its action on $x$ is $A^te_1=e_1+\sqrt3\,t e_0$. Its detector amplitude is therefore $\sqrt3\,t$. There are exactly $k$ such positions, one for each $t$.

For exactly two $B$ factors, every word is uniquely

$$
A^aBA^bBA^c,\qquad a,b,c\ge0,\qquad a+b+c=k-2. \tag{4.3}
$$

The identity $BA^bB=B^2$ and $A^aB^2A^c=B^2$ show that its amplitude is $f^{\mathsf T}B^2x=1$, independently of all three intervening run lengths. For $k\ge2$ there are $\binom{k}{2}$ choices of the two positions, equivalently $\binom{k}{2}$ triples in (4.3). Three or more $B$ factors annihilate: after replacing adjacent interleavings by $B^2$, the next such factor gives $B^3=0$. For $k=0,1$ the two-$B$ contribution is absent.

Each word has the common Kraus scale $q^{k/2}$, and different words contribute separate squared amplitudes. Summing every class gives, for all integers $k\ge0$,

$$
\begin{aligned}
\operatorname{Tr}[F\mathcal T^k(xx^{\mathsf T})]
&=q^k\left(k^2+3\sum_{t=0}^{k-1}t^2+\binom{k}{2}\right)\\
&=q^k\left(k^2+\frac{k(k-1)(2k-1)}2+\frac{k(k-1)}2\right)
=q^kk^3.
\end{aligned} \tag{4.4}
$$

The empty sum and $\binom{k}{2}$ are zero for $k=0,1$ as appropriate. Thus the identity includes the zero-tick probability at $k=0$. All interleavings have been counted, including those with two jumps; their nonzero contribution is essential to the exact cubic.

Both $A$ and $B$ are upper triangular, with diagonals $(1,1,1)$ and $(0,0,0)$ respectively. In column vectorization the full complex superoperator is represented by

$$
q(A\otimes A+B\otimes B). \tag{4.5}
$$

It is upper triangular with every diagonal entry equal to $q$. Hence $\rho(\mathcal T)=q<1$. The Gramian converges, and selected positive word terms already give

$$
\begin{aligned}
Q&=\sum_{k\ge0}(\mathcal T^*)^k(F)\\
&\ge F+qB^{\mathsf T}FB+q^2(B^2)^{\mathsf T}FB^2
=\operatorname{diag}(1,q,q^2)>0.
\end{aligned} \tag{4.6}
$$

This is a positive-operator inequality on the full memory. The three selected terms belong respectively to the empty word, the word $B$ and the word $BB$; all omitted terms are positive. The real-to-complex positivity argument (2.10) supplies the same strict bound for complex vectors.

By (4.4), the scalar normalization is

$$
z=x^{\mathsf T}Qx=Z_3(q)
=\frac{q(1+4q+q^2)}{(1-q)^4}. \tag{4.7}
$$

The rational expression follows by applying $(q\,d/dq)^3$ to $(1-q)^{-1}$, with termwise differentiation valid for $|q|<1$. With $S=Q^{1/2}$, the actual completed instrument is

$$
\begin{aligned}
b&=Se_2/\sqrt{Z_3(q)},\qquad \tau=bb^{\mathsf T},\\
L_A&=\sqrt q\,SAS^{-1},\qquad
L_B=\sqrt q\,SBS^{-1},\qquad
J=be_0^{\mathsf T}S^{-1}.
\end{aligned} \tag{4.8}
$$

Theorem 2.1 proves exact completeness, real coefficients, complete positivity on all complex positive inputs, properness and the actual reset identity. In particular

$$
\Psi\Phi^k(\tau)=\frac{k^3q^k}{Z_3(q)}\tau\qquad(k\ge0). \tag{4.9}
$$

The invertible $A$ and nonzero strictly upper triangular $B$ are linearly independent; the zero Choi rank is two after similarity. The nonzero rank-one $F$ gives tick Choi rank one and exactly one nonzero reset Kraus operator. Raw reachability is already witnessed by $x=e_2$, $Bx=e_1$ and $B^2x=e_0$. Invertible completion preserves their span, giving full reachable memory. $\square$

**Theorem 4.2 (A one-jump restriction is not a cubic obstruction).** Real coefficients, a pure post-tick state, a single tick Kraus operator and the exact cubic renewal law do not force zero-branch Choi rank at least three, even when the memory dimension is three.

Proof. Theorem 4.1 supplies all four properties with zero Choi rank two. Its raw matrices satisfy $BA^rB=B^2\ne0$ for every $r\ge0$, so it is not in the one-jump subclass $BA^rB=0$ of Theorem 3.1. In that subclass a single real detector amplitude would give one square in the forward difference. For the cubic, $(t+1)^3-t^3=3t^2+3t+1$ is not the square of a real linear polynomial: the square's leading and linear coefficients would force its constant term to be $3/4$, not $1$. The cubic construction instead has the all-$A$ and two-$B$ contributions in (4.4). The obstruction to that single-square one-jump ansatz therefore supplies no general rank-three necessity. $\square$

## 5. Faithful invariant densities and every actual stationary cylinder

**Theorem 5.1 (Stationary realization for each completed family).** Let a completed instrument from Theorem 2.1 with real raw data have the actual law (1.1) and a full zero-word reachable span from its pure reset vector $b$. This applies to Theorems 3.1 and 4.1, and to the even-degree matrices specified in Section 6. Define

$$
R_0^{\rm op}=\sum_{a\ge0}\Phi^a(\tau),\qquad
\rho_*=\frac{R_0^{\rm op}}{\mu},\qquad
\mathcal E_0=\Phi,\quad \mathcal E_1=\Psi. \tag{5.1}
$$

Then $\rho_*$ is a real faithful invariant density, distinct from the pure post-tick density $\tau$. For every finite word, the actual output probability

$$
P(w_1\cdots w_N)
=\operatorname{Tr}\big[\mathcal E_{w_N}\cdots\mathcal E_{w_1}(\rho_*)\big] \tag{5.2}
$$

equals (1.3). It defines the proper stationary renewal law without an additional all-zero stationary component.

Proof. Stability of $\Phi$ gives norm convergence of (5.1). All terms are positive, and the survival formula (2.5) gives

$$
\operatorname{Tr}R_0^{\rm op}=\sum_{a\ge0}S_a
=\sum_{j\ge0}(j+1)\gamma_j=\mu. \tag{5.3}
$$

Tonelli's identity applies to these nonnegative summands; finiteness follows from (1.2). Thus $\rho_*$ has trace one. The reset formula strengthens the scalar gap identity to $\Psi\Phi^a(\tau)=\gamma_a\tau$. Summing the two branches separately yields

$$
\Phi(R_0^{\rm op})=R_0^{\rm op}-\tau,\qquad
\Psi(R_0^{\rm op})=\tau,\qquad
(\Phi+\Psi)(\rho_*)=\rho_*. \tag{5.4}
$$

For faithfulness, expand each power into its Kraus words. For any memory vector $y$,

$$
y^*R_0^{\rm op}y
=\sum_{a\ge0}\sum_{|w|=a}|y^*L_wb|^2. \tag{5.5}
$$

If this sum is zero, $y$ is orthogonal to the full reachable span and hence is zero. Therefore $R_0^{\rm op}>0$ on all of $\mathbb C^D$. This proves faithfulness using reachability, independently of the detector observability that established $Q>0$. Real matrices and a real $b$ make $\rho_*$ real symmetric. Since $D\ge2$, faithfulness also makes $\rho_*$ mixed.

For a prefix of $a$ zeros followed by the first visible one, (5.1) and the actual reset identity give

$$
\Psi\Phi^a(\rho_*)
=\frac1\mu\sum_{c\ge0}\Psi\Phi^{a+c}(\tau)
=\frac{S_a}{\mu}\tau. \tag{5.6}
$$

Each following internal gap $g_i$ and tick multiplies this state by $\gamma_{g_i}$ and returns it to the same $\tau$. A final run of $b$ zeros has trace $S_b$ from this reset. Therefore

$$
P(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
=\frac{S_aS_b}{\mu}\prod_{i=1}^{r-1}\gamma_{g_i} \tag{5.7}
$$

for every $r\ge1$, with the empty internal product at $r=1$. This calculation uses the actual conditioned states after each tick, not an independently assigned output formula.

For a word with no ones, apply $\Phi^N$ directly to (5.1):

$$
\begin{aligned}
P(0^N)
&=\frac1\mu\sum_{a\ge0}\operatorname{Tr}\Phi^{N+a}(\tau)
=\frac1\mu\sum_{a\ge0}S_{N+a}\\
&=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j.
\end{aligned} \tag{5.8}
$$

For $N=0$ this is one by (5.3), so the empty word is included. Equations (5.7)–(5.8) exhaust all finite words. Summing over the final symbol in (5.2) uses trace preservation and gives right consistency; summing over the first symbol uses invariance of $\rho_*$ and gives left consistency. These finite-alphabet consistent probabilities define a stationary process. Moreover

$$
0\le P(0^N)\le\frac1\mu\sum_{j\ge N}(j+1)\gamma_j\longrightarrow0, \tag{5.9}
$$

so there is no positive-probability infinite all-zero future, nor a separate all-zero stationary component.

Finally the reset and stationary densities have different tick probabilities:

$$
\operatorname{Tr}\Psi(\tau)=\gamma_0=0,\qquad
\operatorname{Tr}\Psi(\rho_*)=\nu>0. \tag{5.10}
$$

They cannot be identified. The pure state is the density immediately after a tick; the faithful mixed density is the unconditioned stationary initialization. $\square$

The stationary summation mechanism is that of [Chapter 39, equations (39.1)–(39.3)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#39-invariant-densities-give-every-stationary-cylinder). Here its reset premise comes from the finite-rank detector completion, so it applies unchanged in meaning when the tick has two Kraus operators with the same pure output.

## 6. All-degree real coordinates and the precise optimality dependencies

**Theorem 6.1 (The real upper bound for all degrees).** For each $n\ge1$ and $0<q<1$, the stationary law (1.3) has a real instrument on $D_n=\lceil n/2\rceil+1$ complex memory dimensions, with full reachable span, a faithful invariant density and a pure post-tick reset. Its zero Choi rank is one for even $n$ and two for odd $n$. The tick Choi rank can be chosen one for even $n$, for $n=1$, and for $n=3$; it is at most two for every other odd $n$ by Theorem 3.1.

Proof. Odd degrees are Theorem 3.1, with the cubic improvement of Theorem 4.1. For even $n=2m$, $m\ge1$, the existing [Chapter 37 even construction, equation (37.1)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#37-exact-even-amplitudes-and-odd-forward-difference-sums) already has entirely real data on $m+1$ dimensions. To specify the parameter mapping, use the backward shift $J_-e_j=e_{j-1}$ for $j\ge1$, $J_-e_0=0$, $U_-=I+J_-$, $f=e_0$ and

$$
K=\sqrt q\,U_-,\qquad
x_r=r!{m\brace r}\ (0\le r\le m),\qquad
F=ff^{\mathsf T},\qquad \mathcal T(X)=KXK^{\mathsf T}. \tag{6.1}
$$

Here ${m\brace r}$ denotes a Stirling number of the second kind. The classical Newton identity $k^m=\sum_r{m\brace r}r!\binom kr$ gives $f^{\mathsf T}U_-^kx=k^m$, so the raw observed weight is $q^kk^{2m}$ for all $k\ge0$. The unipotent $U_-$ gives spectral radius $q$. The rows $f^{\mathsf T}U_-^t$ distinguish every vector by the binomial basis, giving a faithful Gramian. Also $x_m=m!\ne0$ makes $x,J_-x,\ldots,J_-^mx$ independent, so reachability is full. These are the hypotheses established for (37.1), now passed to the real conclusion of Theorem 2.1 with $z=Z_{2m}(q)$. Its nonzero single zero Kraus operator and rank-one detector give Choi ranks one and one. The dimension is $m+1=D_{2m}$. Theorem 5.1 supplies every stationary cylinder for all these families. $\square$

**Theorem 6.2 (Optimal coordinate field under the same dimension lower input).** Assume the handwritten finite-CP growth theorem used in Chapter 40, Theorem 40.1: on a $d$-dimensional complex Hilbert space, the norm of powers of a finite CP map of positive spectral radius $r$ has an upper bound $C r^k(1+k)^{2d-2}$. In the finite homogeneous comparison class of Definition 1.2, enlarged to allow arbitrary complex Kraus entries, arbitrary mixed hidden conditional states, arbitrary Kraus multiplicities and a specified hidden initial density that need not be invariant, exact equality of all stationary output cylinders implies

$$
D\ge D_n=\left\lceil\frac n2\right\rceil+1. \tag{6.2}
$$

Consequently the minimum dimension with real Kraus matrices equals the minimum with unrestricted complex Kraus matrices, and both are $D_n$. This equality uses the same handwritten lower dependency; the real upper construction requires no finite-CP growth assumption.

Proof. The lower-bound transfer uses actual cylinders, as in Chapter 40. For a competing instrument $\widehat\Phi,\widehat\Psi$ with specified initial density $\widehat\rho$, the actual posterior after the cylinder $1$ is

$$
\widehat\tau=\widehat\Psi(\widehat\rho)/\nu,\qquad
\operatorname{Tr}\widehat\Psi\widehat\Phi^k(\widehat\tau)
=\frac{P(1\,0^k\,1)}{P(1)}=\gamma_k. \tag{6.3}
$$

It need not be pure or a common reset state. Completeness and normalization of $\gamma$ imply the actual survival formula $\operatorname{Tr}\widehat\Phi^k(\widehat\tau)=S_k$, including its limit zero. The explicit tail is

$$
S_k=q^kP_n(k),\qquad
P_n(k)=\frac1{Z_n(q)}\sum_{t\ge0}(k+t)^nq^t,\qquad
\deg P_n=n,\quad [k^n]P_n=\frac1{Z_n(q)(1-q)}>0. \tag{6.4}
$$

Restrict to the span $\mathcal H$ of all zero Kraus words acting on $\operatorname{supp}\widehat\tau$, of dimension $d\le D$. The finite reachability argument of Chapter 32, reused in Chapter 40, (40.3), gives a finite sum $X=\sum_{j=0}^{M}\widehat\Phi^j(\widehat\tau)$ faithful on $\mathcal H$. Bounds $aI\le X\le bI$ and the CP norm identity compare $\operatorname{Tr}\widehat\Phi^k(X)$ above and below with positive constants times $\|\widehat\Phi_{\mathcal H}^k\|$. The trace is

$$
\operatorname{Tr}\widehat\Phi^k(X)
=q^k\sum_{j=0}^{M}q^jP_n(k+j), \tag{6.5}
$$

whose polynomial factor still has exact degree $n$ and positive leading coefficient. Taking $k$th roots proves that the restricted spectral radius is $q$, rather than assuming the unused ambient blocks have that radius. The stated finite-CP growth input on $\mathcal H$ now forces $n\le2d-2$, hence (6.2). This is precisely the inherited lower mechanism, with both reachability and the radius identification retained.

Real-matrix instruments form a subclass of the complex competitors, so their minimum dimension cannot be smaller. Theorem 6.1 attains $D_n$ in that subclass. The two minima therefore coincide under the stated lower input. $\square$

**Theorem 6.3 (Zero-rank parity is independent of the CP growth input).** For the same complete stationary law and finite homogeneous comparison class, the minimum zero-branch Choi rank is one for even $n$ and two for odd $n$. This holds for the real-matrix subclass as well as for unrestricted complex matrices, and does not require the growth assumption in Theorem 6.2.

Proof. A zero branch of rank zero is the zero map and would give $\gamma_1=0$, contrary to (1.1). For a rank-one zero branch write $\widehat\Phi(X)=AXA^*$. Use the actual mixed posterior $\widehat\tau$ in (6.3), and let $F_1=\widehat\Psi^*(I)\ge0$. Then

$$
\gamma_k
=\operatorname{Tr}[F_1A^k\widehat\tau(A^*)^k]
=\|F_1^{1/2}A^k\widehat\tau^{1/2}\|_{\rm HS}^2
=\frac{k^nq^k}{Z_n(q)}. \tag{6.6}
$$

Cayley–Hamilton makes the matrix inside this norm a finite constant-coefficient vector recurrence. The mixed vector-recurrence argument of Chapter 29, (29.3)–(29.6), applied to exactly this positive-effect/mixed-state expression in Chapter 40, (40.4), says that a nonzero eventual squared norm equal to a polynomial times $q^k$ has even polynomial degree. Its reason is that the maximal nonzero exponential modulus $R$ and maximal polynomial degree $e$ contribute a leading unit-phase vector sum with positive Cesàro squared norm; distinct phases have zero cross-term means. Comparison with the exact exponential-polynomial squared norm forces $q=R^2$ and polynomial degree $2e$. Applying this to (6.6) excludes every odd $n$, without assuming a pure competitor, a reset or a single tick Kraus operator. The attained ranks of Theorem 6.1 give both minima. No finite-CP power bound is used. $\square$

## 7. Visible support, detector limits and interpretation

**Theorem 7.1 (Exactly the Fibonacci legal support).** Each real monomial-geometric instrument of Theorem 6.1, initialized at its $\rho_*$, gives positive probability to every finite binary word without adjacent ones and zero probability to every word with adjacent ones. Thus the number of supported length-$N$ words is $F_{N+2}$ for $F_0=0,F_1=1$.

Proof. In (5.7), adjacent ones give an internal gap $g_i=0$ and hence the zero factor $\gamma_0$. Otherwise every internal gap factor is positive. Every boundary tail $S_a$ is positive, since arbitrarily long gaps have positive mass, and (5.8) is positive for every finite $N$. This proves the exact support statement. If $b_N$ denotes the number of legal words, then $b_0=1$, $b_1=2$, and for $N\ge2$ a legal word either begins with zero followed by a legal word of length $N-1$, or begins with one-zero followed by a legal word of length $N-2$. Hence $b_N=b_{N-1}+b_{N-2}=F_{N+2}$. $\square$

**Definition 7.2 (Detector question left open by these constructions).** For odd $n\ge5$, ask whether dimension $D_n=(n+3)/2$ admits real fixed Kraus matrices with zero Choi rank two and tick Choi rank one, all ticks resetting to one pure state, while reproducing every cylinder (1.3). Theorem 3.1 gives tick rank at most two but does not settle the existence of such a rank-one effect. The cubic construction proves that rank-one real detection is possible at $n=3$ through multiple nonvanishing jumps; it supplies neither a uniform higher-odd construction nor a higher-odd impossibility theorem. In particular no higher-odd single-tick optimum is asserted.

**Definition 7.3 (Output and resource boundary).** The result compares exact generators of one fixed stationary renewal law, with all persistent registers counted. The equality of optimal real-coordinate and complex-coordinate dimensions in Theorem 6.2 is conditional on its stated handwritten lower input. The explicit real upper instruments and the rank-parity argument have their separate proofs and do not inherit that condition unnecessarily.

The visible Fibonacci support in Theorem 7.1 agrees with [Chapter 41, Theorem 41.1](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#41-the-common-fibonacci-legal-language-and-the-resource-boundary). It does not identify these probabilities with a product-activity measure or the native five-state AURIC source. It supplies no parent Hamiltonian, holonomy control, native preparation map or coherent square-root output state. The degree $n$ of the gap weight is not the observed window length $N$. Memory entropy, physical rebit equivalence, preparation resources, work and energy are not consequences of the matrix-coordinate equality. The precise output object established here consists of the actual classical cylinders (5.7)–(5.8) from the faithful invariant initialization, with a separate pure density after each tick.

## 追加锚（本行以下为增补区）

## 8. An exact quintic single-detector instrument in four dimensions

**Definition 8.1 (Positive quintic constants and two real amplitudes).** All square roots in this section are the positive real square roots. Set

$$
\phi=\frac{1+\sqrt5}{2},\qquad
\eta=\sqrt{\frac{\phi-\sqrt{\phi^2-4/5}}2},\qquad
\lambda=\phi^2\eta,\qquad
\alpha=\sqrt{\frac{5\lambda}{2}}. \tag{8.1}
$$

These are positive real algebraic constants: $\phi>1$, $0<\sqrt{\phi^2-4/5}<\phi$, and consequently $\eta,\lambda,\alpha>0$. They satisfy

$$
\phi^2=\phi+1,\qquad
\eta^4-\phi\eta^2+\frac15=0,\qquad
\lambda^2+\eta^2=3\lambda\eta. \tag{8.2}
$$

Define the real quadratic polynomials

$$
\begin{aligned}
s(t)&=\alpha t(t-\eta),\\
p(t)&=\sqrt5\left(t^2+(1-\lambda)t+\frac{1+\eta^2-\lambda}{2}\right)
       =p_0+p_1t+p_2t^2,\\
p_0&=\frac{\sqrt5}{2}(1+\eta^2-\lambda),\qquad
p_1=\sqrt5(1-\lambda),\qquad p_2=\sqrt5.
\end{aligned} \tag{8.3}
$$

**Theorem 8.2 (Quintic coefficient certificate).** For every real $t$ and every integer $k\ge0$,

$$
p(t)^2+s(t+1)^2-s(t)^2=(t+1)^5-t^5,\qquad
k^5=s(k)^2+\sum_{t=0}^{k-1}p(t)^2. \tag{8.4}
$$

Proof. The relation $\phi^4-3\phi^2+1=0$ gives the last equality of (8.2). Expanding the left side of the first identity in (8.4), using $\alpha^2=5\lambda/2$ and $\lambda^2+\eta^2=3\lambda\eta$, gives the coefficients $5,10,10,5$ in degrees $4,3,2,1$, respectively. Its constant coefficient is

$$
\frac54(1+\eta^2-\lambda)^2+\frac{5\lambda}{2}(1-\eta)^2
=1+\frac54\left(\eta^4-\phi\eta^2+\frac15\right). \tag{8.5}
$$

Thus, before applying the quartic relation for $\eta$, the complete residual is exactly

$$
p(t)^2+s(t+1)^2-s(t)^2-\big((t+1)^5-t^5\big)
=\frac54\left(\eta^4-\phi\eta^2+\frac15\right). \tag{8.6}
$$

Equation (8.2) makes it zero. Summing the resulting forward-difference identity for $t=0,\ldots,k-1$ and using $s(0)=0$ proves the second identity. At $k=0$ both the empty sum and $s(0)^2$ vanish. $\square$

**Definition 8.3 (Quintic raw memory and Newton correspondence).** On the ordered real coordinates $e_0,e_1,e_2,e_3$ inside $\mathbb C^4$, use target coordinates $e_0,e_1,e_2$ and source coordinate $x=e_3$. Put $f=e_0$, $F=ff^{\mathsf T}$ and

$$
A=\begin{pmatrix}
1&1&0&\alpha(1-\eta)\\
0&1&1&2\alpha\\
0&0&1&0\\
0&0&0&1
\end{pmatrix},\qquad
B=\begin{pmatrix}
0&0&0&p_0\\
0&0&0&p_1+p_2\\
0&0&0&2p_2\\
0&0&0&0
\end{pmatrix}. \tag{8.7}
$$

In target-source blocks, $A=\left(\begin{smallmatrix}U&u\\0&1\end{smallmatrix}\right)$ and $B=\left(\begin{smallmatrix}0&v\\0&0\end{smallmatrix}\right)$, where $U=I_3+N$, $N_{01}=N_{12}=1$, all other entries of $N$ are zero, and

$$
u=(\alpha(1-\eta),2\alpha,0)^{\mathsf T},\qquad
v=(p_0,p_1+p_2,2p_2)^{\mathsf T}. \tag{8.8}
$$

The coefficients are finite differences, with $\delta a(t)=a(t+1)-a(t)$:

$$
\begin{aligned}
p(t)&=p_0+(p_1+p_2)\binom t1+2p_2\binom t2,\\
\delta s(t)&=\alpha(1-\eta)+2\alpha\binom t1,\\
s(k)&=\alpha(1-\eta)\binom k1+2\alpha\binom k2.
\end{aligned} \tag{8.9}
$$

For any fixed $0<q<1$, the raw CP map is $\mathcal T_q(X)=q(AXA^{\mathsf T}+BXB^{\mathsf T})$ on the full complex matrix algebra, with Kraus matrices $\sqrt q A,\sqrt q B$.

**Theorem 8.4 (All quintic words, stability and full memory).** For the data (8.7), all integers $r,t,k\ge0$ satisfy

$$
f^{\mathsf T}A^kx=s(k),\qquad
f^{\mathsf T}A^tBA^rx=p(t),\qquad BA^rB=0. \tag{8.10}
$$

For each $0<q<1$, the full superoperator has spectral radius $q$, its observability Gramian $Q$ is positive definite on $\mathbb C^4$, and the raw words from $x$ span $\mathbb C^4$. Moreover

$$
\begin{aligned}
\operatorname{Tr}[F\mathcal T_q^k(xx^{\mathsf T})]&=q^kk^5\quad(k\ge0),\\
Q&=\sum_{k\ge0}(\mathcal T_q^*)^k(F),\\
z=x^{\mathsf T}Qx=Z_5(q)&=
\frac{q(1+26q+66q^2+26q^3+q^4)}{(1-q)^6}>0.
\end{aligned} \tag{8.11}
$$

Proof. The target component of $A^kx$ is $\sum_{j=0}^{k-1}U^ju$, and its source component is one. Since $e_0^{\mathsf T}U^j=(1,j,\binom j2)$, (8.9) gives $f^{\mathsf T}A^kx=\sum_{j<k}\delta s(j)=s(k)$. The matrix $B$ reads only the source component, so $BA^rx=(v,0)$, after which $A^t$ gives $(U^tv,0)$. Its first coordinate is $p(t)$ by (8.9). The image of $B$ is in the target, the target is preserved by $A$, and $B$ kills the target; hence $BA^rB=0$ as a matrix identity.

For a word $w$ of length $k$ in the letters $A,B$, use the ordered product with the rightmost letter acting first. Expansion of the CP power gives $q^k\sum_{|w|=k}|f^{\mathsf T}wx|^2$. The single all-$A$ word contributes $s(k)^2$. Every word with exactly one $B$ has the unique form $A^tBA^{k-1-t}$, $0\le t<k$, and contributes $p(t)^2$ once. Every word with at least two $B$ letters contains a factor $BA^rB$ and is zero. Therefore the entire ordered-word sum is

$$
\operatorname{Tr}[F\mathcal T_q^k(xx^{\mathsf T})]
=q^k\left(s(k)^2+\sum_{t=0}^{k-1}p(t)^2+0\right)=q^kk^5. \tag{8.12}
$$

There are no amplitude cross terms between different words. At $k=0$ the only word is the identity and $f^{\mathsf T}x=0$, so (8.12) also covers the empty word.

The matrices $A,B$ are upper triangular, with diagonal entries respectively one and zero. Column vectorization represents $\mathcal T_q$ by $q(A\otimes A+B\otimes B)$, upper triangular on all sixteen complex matrix coordinates, with diagonal $q$. Thus $\operatorname{spec}(\mathcal T_q)=\{q\}$ and the Gramian converges for every $0<q<1$.

To prove full observability, let $y=(y_T,y_s)\in\mathbb C^3\oplus\mathbb C$ obey $y^*Qy=0$. Formula (2.11), with positive weights $q^{|w|}$, forces $f^{\mathsf T}wy=0$ for every word. In particular $f^{\mathsf T}A^tBy=p(t)y_s=0$ for every natural $t$. The degree-two polynomial $p$ has leading coefficient $\sqrt5\ne0$, so some $t\in\{0,1,2\}$ has $p(t)\ne0$ and $y_s=0$. The all-$A$ rows then give $e_0^{\mathsf T}U^jy_T=0$ for $j=0,1,2$. Their coefficient matrix is

$$
\begin{pmatrix}1&0&0\\1&1&0\\1&2&1\end{pmatrix}, \tag{8.13}
$$

of determinant one. Thus $y_T=0$, establishing $Q>0$ on the whole complex memory, not just positivity on $x$.

For reachability, $x,Bx,ABx,A^2Bx$ span the source and the target vectors $v,Uv,U^2v$. The latter span the same space as $v,Nv,N^2v$. Since $v_2=2p_2=2\sqrt5\ne0$, these three vectors are independent. This proves full real and complex reachability. Finally sum (8.12) over $k$ to obtain $z=Z_5(q)$; applying $(q\,d/dq)^5$ to $(1-q)^{-1}$ gives the rational expression in (8.11). Termwise differentiation is valid for $|q|<1$. $\square$

**Theorem 8.5 (Completed quintic instrument and all stationary cylinders).** For every $0<q<1$, let $G=Q^{1/2}$ be the positive real symmetric square root of the faithful Gramian in (8.11), and define

$$
\begin{aligned}
b&=Gx/\sqrt{Z_5(q)},&\tau&=bb^{\mathsf T},\\
L_A&=\sqrt q\,GAG^{-1},&L_B&=\sqrt q\,GBG^{-1},&J&=bf^{\mathsf T}G^{-1},\\
\Phi(X)&=L_AXL_A^{\mathsf T}+L_BXL_B^{\mathsf T},&&
\Psi(X)=JXJ^{\mathsf T}.
\end{aligned} \tag{8.14}
$$

These real matrices constitute a complete homogeneous CP instrument on $M_4(\mathbb C)$. The zero branch has Choi rank two, with Kraus matrix ranks $4$ and $1$; the tick branch has Choi rank one and its single Kraus matrix has rank one. Each positive-probability tick resets to the pure density $\tau$, and

$$
\begin{aligned}
L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J&=I_4,\qquad \rho(\Phi)=q,\\
\Psi(X)&=\tau\operatorname{Tr}(J^{\mathsf T}JX),\\
\Psi\Phi^k(\tau)&=\gamma_k\tau,\qquad
\gamma_k=\frac{k^5q^k}{Z_5(q)}\quad(k\ge0).
\end{aligned} \tag{8.15}
$$

With $S_a=\sum_{j\ge a}\gamma_j$ and $\mu=\sum_{k\ge0}(k+1)\gamma_k=1+Z_6(q)/Z_5(q)$, the actual stationary initialization is

$$
\rho_*^{(5)}=\frac1\mu\sum_{a\ge0}\Phi^a(\tau)>0,\qquad
\operatorname{Tr}\Phi^a(\tau)=S_a. \tag{8.16}
$$

For every $r\ge1$ and $a,b,g_1,\ldots,g_{r-1},N\ge0$, its actual binary cylinders are

$$
\begin{aligned}
P(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{i=1}^{r-1}\gamma_{g_i},\\
P(0^N)&=\frac1\mu\sum_{a\ge0}S_{N+a}
=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j.
\end{aligned} \tag{8.17}
$$

Proof. The precise inputs to Theorem 2.1 are $d=4$, two raw Kraus matrices $K_A=\sqrt q A,K_B=\sqrt q B$, one detector column $f=e_0$, $F=ff^{\mathsf T}\ne0$, and raw reset vector $x=e_3\ne0$. Theorem 8.4 proves its full-superoperator stability premise and its full-memory Gramian premise. The theorem's $S,z,b$ correspond to $G,Z_5(q),b$ here. Real symmetric positivity gives an invertible real $G$, and $b^{\mathsf T}b=1$. In particular the Stein identity gives the full operator equality

$$
G^{-1}\big(qA^{\mathsf T}QA+qB^{\mathsf T}QB+F\big)G^{-1}=I_4. \tag{8.18}
$$

Its three terms are the three effects in (8.15). These are Kraus conjugations on the full complex algebra, so the CP and completeness assertions include complex inputs with nonreal coherences and every matrix amplification. They are not restricted to the real positive cone. Similarity by $X\mapsto GXG$ gives $\rho(\Phi)=q$, and (8.11) and Theorem 2.1 give the normalized gap law and reset formula for every $k$.

The matrix $A$ is invertible and $B=|(v,0)\rangle\langle e_3|$ is nonzero of rank one with zero diagonal. Thus $A,B$ are complex-linearly independent; invertible similarity preserves their matrix ranks and independence. This proves the zero Choi rank and the individual Kraus ranks. Since $b,f$ are nonzero, $J$ is nonzero of rank one, giving the tick Choi rank one.

For Theorem 5.1 the remaining premises are the exact law (1.1) with $n=5$ and full zero-word reachability from $b$. The latter follows from $L_wb=q^{|w|/2}Gwx/\sqrt{Z_5(q)}$ and the four spanning raw words of Theorem 8.4. The first moment is finite because $0<q<1$. Theorem 5.1 therefore gives (8.16)–(8.17), invariance under $\Phi+\Psi$, and faithfulness on all four dimensions. This invocation uses the actual ordered instrument probabilities (5.2). At $r=1$ the product is empty; at $N=0$ the all-zero formula equals one because $\sum_aS_a=\mu$. It includes every finite all-zero word and has $P(0^N)\to0$, with no extra all-zero stationary component.

The raw source coordinate $x$ is not an asserted stationary initialization: the normalized pure reset is $b=Gx/\sqrt{Z_5(q)}$, whereas $\rho_*^{(5)}$ is faithful and mixed. In particular $\operatorname{Tr}\Psi(\tau)=\gamma_0=0$ and $\operatorname{Tr}\Psi(\rho_*^{(5)})=1/\mu>0$. All three target coordinates and the source coordinate are counted in $D=4$. The two zero Kraus labels are summed within $\Phi$ and are not retained as a persistent record; the tick uses just $J$. No additional persistent classical or quantum register is used. $\square$

## 9. An exact septic single-detector instrument in five dimensions

**Definition 9.1 (A rationally isolated triple).** For real variables $\theta=(h,d,e)$ define

$$
\begin{aligned}
b(\theta)&=\frac58-\frac92h^2-5hd,\qquad
c(\theta)=3b(\theta)-\frac52-2d^2-4e,\\
E_0(\theta)&=h^2c(\theta)^2+\frac{hd(1+4e)}8-\frac1{448},\\
E_1(\theta)&=2b(\theta)c(\theta)+\frac38+d^2+2e+2e^2,\\
E_2(\theta)&=b(\theta)^2-6h^2c(\theta)+hd(5+6e)-\frac3{16},\qquad
E=(E_0,E_1,E_2)^{\mathsf T}.
\end{aligned} \tag{9.1}
$$

The constants $h,d,e$ used below are specified exactly as the unique zero of $E$ in the closed rational box

$$
\mathcal B=\{\theta:\|\theta-\theta_c\|_\infty\le r\},\qquad
\theta_c=\frac1{10^6}(10056,-1500211,2611067),\qquad
r=\frac1{10^5}. \tag{9.2}
$$

Theorem 9.2 establishes that this definition is well posed. The center of the box is rational data for the certificate, not a claimed decimal value of the root. The letters $b,c$ in this section mean the scalar polynomials in (9.1); the normalized reset vector will be denoted $\xi$.

**Theorem 9.2 (Exact existence, uniqueness in the box and nonsingularity).** The box (9.2) contains exactly one zero of $E$, and it lies in its interior. At that zero $DE$ is invertible and $h\ge10046/10^6>0$.

Proof. Use the rational matrix

$$
C=\frac1{10000}
\begin{pmatrix}
5455&-1&212\\
527345&472&65820\\
-362244&964&-58667
\end{pmatrix},\qquad
\det C=-\frac{360250635779}{10^{12}}\ne0. \tag{9.3}
$$

The exact center residual after multiplication by $C$ is

$$
CE(\theta_c)=\frac1{273437500000000000000000000000000000000}
\begin{pmatrix}
-10243150448844572256019578919535\\
5927470351553772870217603973935\\
45079277342660805371643189024388
\end{pmatrix},\qquad
\|CE(\theta_c)\|_\infty<\frac1{5000000}. \tag{9.4}
$$

For a three-variable indeterminate $z$, put $H(z)=I_3-CDE(\theta_c+z)$ and define its finite weighted coefficient row sums by

$$
M_i=\sum_{j=1}^{3}\sum_{\alpha\in\mathbb N^3}
\left|[z^\alpha]H_{ij}(z)\right|r^{|\alpha|},\qquad i=1,2,3. \tag{9.5}
$$

Every coefficient here is rational. Expansion of (9.1), with the derivative columns ordered as $h,d,e$, gives the following exact values and rational bounds:

| Row $i$ | Exact value of $M_i$ | Strict upper bound |
| --- | --- | --- |
| $1$ | $\dfrac{390478499067873421120556048493}{62500000000000000000000000000000}$ | $1/100$ |
| $2$ | $\dfrac{16183691879450395407223506946387}{62500000000000000000000000000000}$ | $27/100$ |
| $3$ | $\dfrac{14227528846784773295138168796547}{78125000000000000000000000000000}$ | $19/100$ |

These are finite rational identities and inequalities, obtained by substituting the rational center in $I_3-CDE$ and summing the absolute coefficients with weights $10^{-5|\alpha|}$. In particular, for every real $z$ with $\|z\|_\infty\le r$, the induced matrix infinity norm satisfies

$$
\|I_3-CDE(\theta_c+z)\|_\infty
\le\max_iM_i<\frac{27}{100}. \tag{9.6}
$$

Let $T(\theta)=\theta-CE(\theta)$. Integrating its derivative along each segment in the convex box shows that $T$ is a contraction there with Lipschitz constant at most $27/100$. Equations (9.4)–(9.6) give, for every $\theta\in\mathcal B$,

$$
\|T(\theta)-\theta_c\|_\infty
\le\|CE(\theta_c)\|_\infty+\frac{27}{100}\|\theta-\theta_c\|_\infty
<\frac1{5000000}+\frac{27}{100}r
=\frac{29}{10^7}<r. \tag{9.7}
$$

Thus $T$ maps the complete closed box into itself, and the contraction theorem gives exactly one fixed point there, in its interior. Because $C$ is invertible, fixed points are precisely zeros of $E$, proving both existence and uniqueness in this box. At any point of the box, (9.6) implies that $CDE$ is invertible by the Neumann series for $I_3-(I_3-CDE)$; therefore $DE$ is invertible at the zero. The $h$ interval in (9.2) gives its stated positive lower bound. This is an exact unique-zero specification; no global uniqueness outside $\mathcal B$ is asserted. $\square$

**Theorem 9.3 (Septic polynomial identity and Newton coefficients).** At the constants of Definition 9.1, set $y=t+1/2$, evaluate $b=b(\theta),c=c(\theta)$, and take positive real square roots in

$$
p(t)=\sqrt7\big(y^3-3hy^2+by+hc\big),\qquad
s(t)=\sqrt{7h}\,t(t^2+dt+e). \tag{9.8}
$$

Then for all real $t$ and all integers $k\ge0$,

$$
p(t)^2+s(t+1)^2-s(t)^2=(t+1)^7-t^7,\qquad
k^7=s(k)^2+\sum_{t=0}^{k-1}p(t)^2. \tag{9.9}
$$

Writing $p(t)=\sum_{j=0}^3p_jt^j$ and $s(t)=s_1t+s_2t^2+s_3t^3$, their coefficients are

$$
\begin{aligned}
p_3&=\sqrt7,&p_2&=\sqrt7\left(\frac32-3h\right),\\
p_1&=\sqrt7\left(\frac34-3h+b\right),&
p_0&=\sqrt7\left(\frac18-\frac{3h}{4}+\frac b2+hc\right),\\
s_1&=\sqrt{7h}\,e,&s_2&=\sqrt{7h}\,d,&s_3&=\sqrt{7h}.
\end{aligned} \tag{9.10}
$$

Proof. Before specializing $\theta$ to its zero, the definitions (9.1) give the exact symbolic residual, for any real $h>0,d,e$:

$$
p(t)^2+s(t+1)^2-s(t)^2-\big((t+1)^7-t^7\big)
=7\big(E_2y^2+hE_1y+E_0\big). \tag{9.11}
$$

Indeed substitute $t=y-1/2$ into $7(y^3-3hy^2+by+hc)^2+7h\big((t+1)^2((t+1)^2+d(t+1)+e)^2-t^2(t^2+dt+e)^2\big)-((t+1)^7-t^7)$. The definitions of $b$ and $c$ cancel degrees $6,5,4,3$ in $y$, leaving coefficients $7E_2,7hE_1,7E_0$ in degrees $2,1,0$. This proves (9.11) by polynomial expansion over the rational coefficient ring. At the zero, all three residual coefficients vanish. Since $s(0)=0$, summation gives (9.9), including $k=0$ with the empty sum. Expanding (9.8) gives (9.10). In particular both amplitudes have degree three and their leading coefficients are nonzero.

For the matrix correspondence below, the explicit Newton expansions are

$$
\begin{aligned}
p(t)&=p_0+(p_1+p_2+p_3)\binom t1
 +(2p_2+6p_3)\binom t2+6p_3\binom t3,\\
\delta s(t)&=(s_1+s_2+s_3)+(2s_2+6s_3)\binom t1+6s_3\binom t2,\\
s(k)&=(s_1+s_2+s_3)\binom k1+(2s_2+6s_3)\binom k2+6s_3\binom k3.
\end{aligned} \tag{9.12}
$$

These identities follow from the finite-difference coefficients at zero; the last also follows by summing the second. They fix the shift orientation and every entry used in the next construction. $\square$

**Definition 9.4 (Septic target and source matrices).** Use target coordinates $e_0,e_1,e_2,e_3$ and source coordinate $x=e_4$ on $\mathbb C^5$, with $f=e_0$, $F=ff^{\mathsf T}$. Let $N_{i,i+1}=1$ for $i=0,1,2$, all other entries of the $4\times4$ matrix $N$ be zero, and $U=I_4+N$. Define

$$
u=\begin{pmatrix}s_1+s_2+s_3\\2s_2+6s_3\\6s_3\\0\end{pmatrix},\qquad
v=\begin{pmatrix}p_0\\p_1+p_2+p_3\\2p_2+6p_3\\6p_3\end{pmatrix},\qquad
A=\begin{pmatrix}U&u\\0&1\end{pmatrix},\qquad
B=\begin{pmatrix}0_{4\times4}&v\\0&0\end{pmatrix}. \tag{9.13}
$$

For each $0<q<1$, set $\mathcal T_q(X)=q(AXA^{\mathsf T}+BXB^{\mathsf T})$ on $M_5(\mathbb C)$. Its two raw Kraus matrices are $\sqrt q A,\sqrt q B$; the source is part of the five-dimensional memory.

**Theorem 9.5 (Every septic word and faithful full memory).** The matrices (9.13) obey, for all natural $k,t,r$,

$$
f^{\mathsf T}A^kx=s(k),\qquad
f^{\mathsf T}A^tBA^rx=p(t),\qquad BA^rB=0. \tag{9.14}
$$

For every $0<q<1$, the full superoperator radius is $q$, the Gramian $Q=\sum_{k\ge0}(\mathcal T_q^*)^k(F)$ is faithful on all five complex coordinates, and the zero-word reachable span from $x$ is the entire memory. Its observed weights and normalization are

$$
\begin{aligned}
\operatorname{Tr}[F\mathcal T_q^k(xx^{\mathsf T})]&=q^kk^7\quad(k\ge0),\\
z=x^{\mathsf T}Qx=Z_7(q)
&=\frac{q(1+120q+1191q^2+2416q^3+1191q^4+120q^5+q^6)}{(1-q)^8}>0.
\end{aligned} \tag{9.15}
$$

Proof. Finite binomial expansion gives $U^t=\sum_{j=0}^3\binom tjN^j$. Thus $e_0^{\mathsf T}U^tv=p(t)$ and $e_0^{\mathsf T}U^tu=\delta s(t)$ by the explicit coefficients (9.12). The source entry of $A^kx$ is one and its target entry is $\sum_{j<k}U^ju$, so its detector amplitude telescopes to $s(k)$. Also $BA^rx=(v,0)$, and $B$ kills the $A$-invariant target. This proves all three identities (9.14) without commuting $A$ and $B$.

The ordered CP expansion has one all-$A$ word, with squared amplitude $s(k)^2$; exactly $k$ one-$B$ words $A^tBA^{k-1-t}$, one per $0\le t<k$, with squared amplitudes $p(t)^2$; and only zero contributions from words with two or more $B$ letters, by $BA^rB=0$. Consequently

$$
\operatorname{Tr}[F\mathcal T_q^k(xx^{\mathsf T})]
=q^k\left(s(k)^2+\sum_{t=0}^{k-1}p(t)^2+0\right)=q^kk^7. \tag{9.16}
$$

This includes $k=0$, when the one-$B$ sum is empty and $f^{\mathsf T}x=s(0)=0$. Different ordered words are summed as separate probabilities, with no interference cross terms.

Both raw matrices are upper triangular with respective diagonals one and zero. Therefore $q(A\otimes A+B\otimes B)$ is upper triangular on the entire $25$-dimensional complex matrix space with diagonal $q$, proving $\rho(\mathcal T_q)=q<1$ and norm convergence of $Q$.

Suppose $y=(y_T,y_s)\in\mathbb C^4\oplus\mathbb C$ is invisible to the Gramian. The positive word expansion (2.11) gives $f^{\mathsf T}A^tBy=p(t)y_s=0$ for all $t\ge0$. Since $p_3=\sqrt7\ne0$, it cannot vanish at all four integers $0,1,2,3$, so $y_s=0$. The remaining all-$A$ rows at those four indices give the triangular binomial system

$$
\begin{pmatrix}
1&0&0&0\\
1&1&0&0\\
1&2&1&0\\
1&3&3&1
\end{pmatrix}y_T=0. \tag{9.17}
$$

Its determinant is one, so $y_T=0$. Hence $Q>0$ on all of $\mathbb C^5$. For reachability, $x$ and $A^jBx=(U^jv,0)$ for $0\le j\le3$ span all five coordinates: the target vectors span $v,Nv,N^2v,N^3v$, which are independent since $v_3=6p_3=6\sqrt7\ne0$. This holds over both $\mathbb R$ and $\mathbb C$. Summing (9.16) gives $z=Z_7(q)$, and applying $(q\,d/dq)^7$ to $(1-q)^{-1}$ gives the displayed rational numerator. $\square$

**Theorem 9.6 (Real septic instrument with a single pure resetting tick).** For each $0<q<1$, take the positive real symmetric square root $G=Q^{1/2}$ of the Gramian of Theorem 9.5, and set

$$
\begin{aligned}
\xi&=Gx/\sqrt{Z_7(q)},&\tau&=\xi\xi^{\mathsf T},\\
L_A&=\sqrt q\,GAG^{-1},&L_B&=\sqrt q\,GBG^{-1},&J&=\xi f^{\mathsf T}G^{-1},\\
\Phi(X)&=L_AXL_A^{\mathsf T}+L_BXL_B^{\mathsf T},&&
\Psi(X)=JXJ^{\mathsf T}.
\end{aligned} \tag{9.18}
$$

This is a complete homogeneous CP instrument on the full algebra $M_5(\mathbb C)$ with real entries. It satisfies

$$
\begin{aligned}
L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J&=I_5,\qquad \rho(\Phi)=q,\\
\Psi(X)&=\tau\operatorname{Tr}(J^{\mathsf T}JX),\\
\Psi\Phi^k(\tau)&=\gamma_k\tau,\qquad
\gamma_k=\frac{k^7q^k}{Z_7(q)}\quad(k\ge0).
\end{aligned} \tag{9.19}
$$

Its zero branch has Choi rank exactly two, with individual Kraus matrix ranks $5$ and $1$. Its single tick matrix has rank one and its tick Choi rank is exactly one. Every positive-probability tick has the same pure actual output $\tau$.

Proof. In Theorem 2.1 take $d=5$, $K_A=\sqrt q A,K_B=\sqrt q B$, the single nonzero detector $f=e_0$, and nonzero raw reset $x=e_4$. Theorem 9.5 supplies $\rho(\mathcal T_q)=q<1$ and $Q>0$ on the entire memory; its $z$ is exactly $Z_7(q)$. The positive square root in Theorem 2.1 is $G$ and its normalized vector is $\xi$. The real positive-square-root conclusion applies to this real symmetric Gramian, including its complex Hermitian positivity. The Stein equation gives explicitly

$$
G^{-1}\big(qA^{\mathsf T}QA+qB^{\mathsf T}QB+F\big)G^{-1}=I_5,
\qquad J^{\mathsf T}J=G^{-1}FG^{-1}, \tag{9.20}
$$

because $\xi^{\mathsf T}\xi=1$. Thus completeness is an operator equality for every complex input, including nonreal coherences. The displayed Kraus maps and their amplifications preserve positivity; no real-input restriction enters. Theorem 2.1, the similarity $X\mapsto GXG$, and (9.15) give (9.19), including properness and the zero probability at preceding-zero index $k=0$.

The matrix $A$ is invertible, and $B=|(v,0)\rangle\langle e_4|$ is a nonzero rank-one strictly upper triangular matrix. They are linearly independent over $\mathbb C$. Scaling by $\sqrt q$ and conjugating by $G$ preserve their independence and matrix ranks, giving precisely two zero Kraus directions. Both factors of $J=\xi f^{\mathsf T}G^{-1}$ are nonzero, so its matrix rank and the tick Choi rank are one. Its outer-product form gives the actual reset identity in (9.19). $\square$

**Theorem 9.7 (Full septic stationary interface and persistent memory count).** Define from the actual gap probabilities in (9.19)

$$
S_a=\sum_{j\ge a}\gamma_j,\qquad
\mu=\sum_{k\ge0}(k+1)\gamma_k=1+\frac{Z_8(q)}{Z_7(q)},\qquad
\rho_*^{(7)}=\frac1\mu\sum_{a\ge0}\Phi^a(\tau). \tag{9.21}
$$

Then $\rho_*^{(7)}>0$ is a real mixed invariant density, $\operatorname{Tr}\Phi^a(\tau)=S_a$, and the actual binary-word probabilities from this density are

$$
\begin{aligned}
P(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{i=1}^{r-1}\gamma_{g_i}\quad(r\ge1),\\
P(0^N)&=\frac1\mu\sum_{a\ge0}S_{N+a}
=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j\quad(N\ge0).
\end{aligned} \tag{9.22}
$$

Here every boundary run and internal gap is a nonnegative integer; $r$ is the number of ones and $k$ in $\gamma_k$ is the number of preceding zeros, not the duration $k+1$. No persistent register beyond $\mathbb C^5$ is required.

Proof. Theorem 5.1 requires a real completed Theorem 2.1 instrument, the exact law (1.1), and full zero-word reachability from its normalized reset. Theorem 9.6 establishes the first two premises with $n=7$. For the third, each completed word satisfies $L_w\xi=q^{|w|/2}Gwx/\sqrt{Z_7(q)}$. Since $q>0$ and $G$ is invertible, the five raw spanning vectors in Theorem 9.5 give a full completed span. The finite positive $Z_7(q)$ and finite $Z_8(q)$ give $0<\mu<\infty$. All hypotheses of Theorem 5.1 therefore hold and give (9.21)–(9.22) as the probabilities of the actual maps, with the state ordering in (5.2).

In particular the series in (9.21) converges in norm, has trace $\mu$ before normalization, and is faithful by the full reachable span. Its invariance is that of $\Phi+\Psi$, not of the zero branch separately. Formula (9.22) at $r=1$ has an empty product; at $N=0$ it gives the empty-word probability one. It covers every finite all-zero cylinder and tends to zero as $N\to\infty$, so there is no hidden all-zero stationary component. Both boundary survival factors are retained, not replaced by internal gap probabilities.

The raw source vector is $x=e_4$, the actual post-tick vector is $\xi=Gx/\sqrt{Z_7(q)}$, and the stationary initialization is the different density $\rho_*^{(7)}$. Faithfulness in dimension five makes the latter mixed; also $\operatorname{Tr}\Psi(\tau)=0$ whereas $\operatorname{Tr}\Psi(\rho_*^{(7)})=1/\mu>0$. The four target coordinates and the source coordinate are all included in $D=5$. Kraus indices are summed, with neither a stored zero-branch label nor an extra persistent reset or controller register. Any retained auxiliary affecting future steps would count as memory under Definition 1.2. $\square$

**Theorem 9.8 (Scope of the two single-detector constructions).** The existence question of Definition 7.2 has affirmative instances at $n=5,D=4$ and $n=7,D=5$ for every $0<q<1$: both admit real fixed matrices with zero Choi rank two and a single rank-one resetting tick, realizing every cylinder (1.3). These dimension upper models require no finite-CP growth assumption. A dimension-optimality comparison for these models is conditional on the handwritten finite-CP growth hypothesis of Theorem 6.2 and its reachability and restricted-radius transfer.

Proof. Theorems 8.5 and 9.6–9.7 establish the two complete instruments and their full stationary laws. The dimensions equal $D_5=4$ and $D_7=5$. Applying Theorem 6.2 under its stated growth hypothesis, with the actual posterior, reachable restriction and radius identification of (6.3)–(6.5), gives the corresponding conditional lower bounds. The upper constructions and their exact ranks do not use that input. Their support is the Fibonacci legal language by (8.17) and (9.22): $\gamma_0=0$, every $\gamma_k$ for $k\ge1$ is positive, and every boundary tail is positive. $\square$

**Definition 9.9 (Remaining detector and interpretation boundaries).** Sections 8–9 address the two instances $n=5$ and $n=7$ of Definition 7.2. For odd $n\ge9$, existence of dimension $D_n$ real instruments with a single rank-one resetting tick remains unresolved by these constructions. The degree-two and degree-three pairs here provide no universal polynomial ansatz, no uniform existence theorem in the degree, and no higher-odd impossibility conclusion. Theorem 3.1 retains its all-odd upper construction with tick rank at most two.

These exact constructions and their parameter correspondences are repository derivations; they make no worldwide novelty or priority claim. The completion and stationary mechanisms are the existing Theorems 2.1 and 5.1, applied with the premises proved above. General Lean proofs of these instruments, their Gramians and their full stationary interfaces remain unfinished. Finite-word horizon work does not certify the full finite-CP growth theorem or these all-index instruments, and supplies no unconditional dimension-minimum conclusion.

The output object is the fixed classical renewal law (1.3), with the pure actual post-tick density distinguished from the mixed invariant initialization. No native five-state AURIC realization, physical real-Hilbert-space equivalence, finite-precision implementation, preparation map, coherent-output state, entropy, energy, work or control-cost conclusion follows. Exact real Kraus coordinates and the count of every persistent register have the meanings of Definitions 1.2 and 7.3.

## 追加锚（本行以下为增补区）

## 10. Uniform anchored telescoping squares

**Theorem 10.1 (Strictly positive even-degree polynomials admit anchored telescoping squares).** Let $m\ge1$ be an integer and let $d\in\mathbb R[t]$ have degree exactly $2m$, with $d(t)>0$ for every real $t$. Then there exist real polynomials $p,s$ such that

$$
\begin{aligned}
\deg p&=m,\qquad \deg s\le m,\qquad s(0)=0,\\
d(t)&=p(t)^2+s(t+1)^2-s(t)^2\quad(t\in\mathbb R),\\
\big([t^m]p\big)^2&=[t^{2m}]d>0.
\end{aligned} \tag{10.1}
$$

Proof. Write $\delta=[t^{2m}]d$. Positivity on the whole real line and the even degree imply $\delta>0$. Give the coefficient space

$$
V_m=\{s\in\mathbb R[t]:\deg s\le m,\ s(0)=0\}
\tag{10.2}
$$

its usual finite-dimensional real topology, and set

$$
c_0=0,\qquad c_j=\sum_{\ell=0}^{j-1}d(\ell),\qquad
\mathcal K=\{s\in V_m:|s(j)|\le\sqrt{c_j},\ 1\le j\le m\}.
\tag{10.3}
$$

Every $c_j$ for $j\ge1$ is strictly positive. Evaluation at $1,\ldots,m$ is a linear isomorphism from $V_m$ to $\mathbb R^m$: a polynomial in its kernel vanishes at the $m+1$ distinct points $0,1,\ldots,m$, so a polynomial of degree at most $m$ in that kernel is zero; the source and target both have dimension $m$. Thus $\mathcal K$ is the inverse image of the product of closed intervals $\prod_{j=1}^m[-\sqrt{c_j},\sqrt{c_j}]$ under a linear homeomorphism. It is nonempty, compact and convex, and contains the zero polynomial.

For $s\in V_m$, write $s_m=[t^m]s$, allowing $s_m=0$, and define

$$
H_s(t)=d(t)+s(t)^2,\qquad
\lambda_s=[t^{2m}]H_s=\delta+s_m^2\ge\delta>0.
\tag{10.4}
$$

The polynomial $H_s$ has degree exactly $2m$, real coefficients, and no real zero. Complex conjugation pairs its roots with their multiplicities, so precisely $m$ roots lie in each open half-plane. Let the lower-half-plane roots, counted with multiplicity, be $\zeta_1,\ldots,\zeta_m$. Define

$$
\begin{aligned}
b_s(z)&=\sqrt{\lambda_s}\prod_{j=1}^m(z-\zeta_j),\\
b_s^{\#}(z)&=\overline{b_s(\overline z)},\qquad H_s=b_s b_s^{\#},\\
a_s(z)&=b_s(z)\frac{\overline{b_s(-1)}}{|b_s(-1)|}.
\end{aligned} \tag{10.5}
$$

The positive square root makes the leading coefficient of $b_s$ positive real. This fixes $b_s$ uniquely because its multiset of roots is the entire lower-half-plane multiset of $H_s$. The real point $-1$ is never a root: $|b_s(-1)|^2=H_s(-1)>0$. Hence the last line is defined without choosing a branch of an argument, and

$$
a_s(-1)=|b_s(-1)|>0,\qquad
|a_s(t)|^2=H_s(t)\quad(t\in\mathbb R).
\tag{10.6}
$$

The leading coefficient of $a_s$ need not be positive real; the positive-leading normalization belongs to $b_s$, while the real-value anchor belongs to $a_s$. The factorization ingredient is the scalar case of real-line polynomial spectral factorization, as in [Ephremidze, arXiv:1011.3777v1, Theorem 2, p. 2](https://arxiv.org/pdf/1011.3777v1), whose factor is nonsingular in the upper half-plane. Here it is also given directly by (10.5). The coefficient-continuity and anchor assertions needed below follow from the next argument.

We prove continuity even at repeated roots. If $s_\nu\to s$ in coefficient space, then $H_{s_\nu}\to H_s$ coefficientwise and $\lambda_{s_\nu}\to\lambda_s\ge\delta$. On a sufficiently small coefficient neighborhood of $s$, the coefficients of the monic polynomials $H_{s'}/\lambda_{s'}$ are uniformly bounded. The Cauchy root bound therefore places all their roots in one fixed closed disk. More explicitly, if the absolute values of all nonleading coefficients are at most $M$, every root has modulus at most $1+M$.

Take any subsequence of the $s_\nu$, and enumerate the $m$ lower roots arbitrarily at each of its indices. Compactness of the product of the root disks supplies a further subsequence on which this $m$-tuple converges. No continuity of the enumeration is assumed. Every limiting root is a root of $H_s$, by coefficient convergence and the defining root equation, and lies in the closed lower half-plane. Since $H_s$ has no real roots, every such limit lies in the open lower half-plane. Along this further subsequence the products defining $b_{s_\nu}$ converge coefficientwise to a polynomial $b$ of degree $m$ with positive leading coefficient $\sqrt{\lambda_s}$. Passing to the limit in $H_{s_\nu}=b_{s_\nu}b_{s_\nu}^{\#}$ gives $H_s=bb^{\#}$. The roots of $b$ are all lower, those of $b^{\#}$ all upper, so this identity assigns to $b$ exactly every lower root of $H_s$ with its full multiplicity. Uniqueness of the positive-leading lower factor gives $b=b_s$.

Thus every subsequence has a further subsequence converging to $b_s$. In finite-dimensional coefficient space this implies $b_{s_\nu}\to b_s$: otherwise a subsequence staying a fixed positive distance from $b_s$ would contradict the further-subsequence conclusion. This proves continuity of $s\mapsto b_s$. Evaluation at $-1$, complex conjugation, modulus and division by a nonzero scalar are continuous, so (10.5) proves continuity of $s\mapsto a_s$. Root collisions within a half-plane cause no exception; multiplicities are retained by the product identity, and no continuously ordered individual roots are required.

Define a continuous coefficient map

$$
\mathcal F(s)(t)=\operatorname{Im}a_s(t-1).
\tag{10.7}
$$

Here real and imaginary parts are taken coefficientwise, equivalently by evaluating at real $t$. Its degree is at most $m$, and its value at zero vanishes by (10.6), so $\mathcal F(s)\in V_m$. For $s\in\mathcal K$ and $1\le j\le m$,

$$
\begin{aligned}
|\mathcal F(s)(j)|^2
&\le |a_s(j-1)|^2
=d(j-1)+s(j-1)^2\\
&\le d(j-1)+c_{j-1}=c_j.
\end{aligned} \tag{10.8}
$$

At $j=1$ the last inequality uses $s(0)=0=c_0$; for $j\ge2$ it uses precisely the constraint at $j-1$ in (10.3). Consequently $\mathcal F$ maps $\mathcal K$ into itself. Brouwer's fixed-point theorem for a nonempty compact convex subset of a finite-dimensional real vector space gives $`s_*\in\mathcal K`$ with $`s_*=\mathcal F(s_*)`$.

Set $`p(t)=\operatorname{Re}a_{s_*}(t)`$. The fixed-point identity at $t+1$ gives $`\operatorname{Im}a_{s_*}(t)=s_*(t+1)`$ for every real $t$. Hence

$$
a_{s_*}(t)=p(t)+i s_*(t+1),\qquad
p(t)^2+s_*(t+1)^2=d(t)+s_*(t)^2.
\tag{10.9}
$$

Both real polynomials have degree at most $m$, and $`s_*(0)=0`$. If $h$ is any polynomial of degree at most $2m$, the leading terms of $h(t+1)$ and $h(t)$ cancel, so $\deg(h(t+1)-h(t))\le2m-1$ whenever the difference is nonzero. Apply this to $`h=s_*^2`$. Comparison of degree $2m$ in (10.9) gives $([t^m]p)^2=\delta>0$, proving that $p$ has degree exactly $m$ and establishing (10.1). $\square$

**Theorem 10.2 (Uniform odd-power identity independent of the geometric parameter).** For each integer $m\ge1$, put $n=2m+1$. There is a pair $p,s\in\mathbb R[t]$, depending only on $m$, for which

$$
\begin{aligned}
\deg p&=m,\qquad \deg s\le m,\qquad s(0)=0,\qquad p_m^2=n,\\
p(t)^2+s(t+1)^2-s(t)^2&=(t+1)^n-t^n\quad(t\in\mathbb R),\\
k^n&=s(k)^2+\sum_{t=0}^{k-1}p(t)^2\quad(k\in\mathbb Z_{\ge0}),
\end{aligned} \tag{10.10}
$$

where $p_m=[t^m]p$. The same pair can be used for every $0<q<1$.

Proof. The polynomial

$$
d_m(t)=(t+1)^{2m+1}-t^{2m+1}
=(2m+1)\int_t^{t+1}u^{2m}\,du
\tag{10.11}
$$

is strictly positive for every real $t$: the integrand is continuous and nonnegative, and its only zero is $u=0$, so its integral on an interval of length one is positive. Its degree is $2m$ with leading coefficient $2m+1=n$. In Theorem 10.1 its evaluation bounds telescope to

$$
c_j=j^{2m+1},\qquad
\mathcal K_m=\{s\in V_m:|s(j)|\le j^{m+1/2},\ 1\le j\le m\}.
\tag{10.12}
$$

Applying that theorem gives the first two lines of (10.10). Summing the polynomial identity from $t=0$ to $t=k-1$ and using $s(0)=0$ gives the last line. At $k=0$ both $s(0)^2$ and the empty sum are zero. The construction of this pair contains no $q$, which proves the stated uniformity in that parameter. $\square$

**Corollary 10.3 (Algebraic existence for rational polynomial data).** If the polynomial $d$ in Theorem 10.1 has rational coefficients, at least one pair $p,s$ satisfying (10.1) has real algebraic coefficients. In particular the pairs in Theorem 10.2 can be chosen real algebraic.

Proof. Write $p(t)=\sum_{j=0}^m p_jt^j$ and $s(t)=\sum_{j=1}^m s_jt^j$. Equating all $2m+1$ coefficients of

$$
p(t)^2+s(t+1)^2-s(t)^2-d(t)=0
\tag{10.13}
$$

is a finite system of polynomial equations over $\mathbb Q$ in $2m+1$ real variables. Theorem 10.1 proves that its existential formula is true over $\mathbb R$. The real algebraic numbers form a real closed subfield, and the transfer principle for real closed fields carries this rational existential formula to that subfield. Any resulting solution has $s(0)=0$ by its parametrization and $p_m^2=[t^{2m}]d>0$ by its top coefficient equation. It therefore has all the required degree properties. This is an existence assertion for rational $d$, not a claim that every solution is algebraic or that a solution is isolated or nonsingular. It supplies no sampling algorithm or coefficient-computation bound. For arbitrary real $q$ it asserts no algebraicity of the completed instrument entries below. $\square$

## 11. Every higher odd degree with one real detector

**Definition 11.1 (Uniform Newton lift).** Fix $m\ge2$, $n=2m+1\ge5$, and one pair from Theorem 10.2. On target coordinates $e_0,\ldots,e_m$ and source coordinate $e_{m+1}$, all counted in $\mathbb C^D$ with $D=m+2=D_n$, set

$$
\begin{aligned}
\Delta h(t)&=h(t+1)-h(t),\qquad U=I_{m+1}+N,\\
N_{j,j+1}&=1\quad(0\le j<m),\qquad N_{ij}=0\text{ otherwise},\\
u_j&=\Delta^{j+1}s(0),\qquad v_j=\Delta^jp(0)\quad(0\le j\le m),\\
A&=\begin{pmatrix}U&u\\0&1\end{pmatrix},\qquad
B=\begin{pmatrix}0_{(m+1)\times(m+1)}&v\\0&0\end{pmatrix},\\
x&=e_{m+1},\qquad f=e_0,\qquad F=ff^{\mathsf T}.
\end{aligned} \tag{11.1}
$$

The entries are exact finite differences:

$$
\Delta^jh(0)=\sum_{\ell=0}^j(-1)^{j-\ell}\binom j\ell h(\ell),\qquad
u_m=0,\qquad v_m=m!p_m\ne0.
\tag{11.2}
$$

Here $f$ is a full-memory vector; on the target its row is $e_0^{\mathsf T}$. For $0<q<1$, define the raw CP map on the entire complex matrix algebra by

$$
\mathcal T_q(X)=q(AXA^{\mathsf T}+BXB^{\mathsf T}).
\tag{11.3}
$$

Its raw Kraus matrices are $\sqrt q A,\sqrt q B$. The polynomials and $A,B,x,f$ depend only on $m$ and the chosen pair; $q$ supplies the geometric Kraus scale and the subsequent Gramian completion. The raw map is not required to be trace nonincreasing.

**Theorem 11.2 (Every word intensity, full complex stability and full memory).** The data (11.1) satisfy, for all nonnegative integers $k,t,r$,

$$
f^{\mathsf T}A^kx=s(k),\qquad
f^{\mathsf T}A^tBA^rx=p(t),\qquad BA^rB=0.
\tag{11.4}
$$

For every $0<q<1$,

$$
\begin{aligned}
\operatorname{Tr}[F\mathcal T_q^k(xx^{\mathsf T})]&=q^kk^n\quad(k\ge0),\\
\operatorname{spec}(\mathcal T_q)&=\{q\},\qquad \rho(\mathcal T_q)=q<1,\\
Q=\sum_{k\ge0}(\mathcal T_q^*)^k(F)&>0\quad\text{on }\mathbb C^D,\\
z=x^{\mathsf T}Qx&=Z_n(q)\in(0,\infty).
\end{aligned} \tag{11.5}
$$

The raw reachable span from $x$ is all of $\mathbb C^D$, already witnessed by $x,A^jBx$ for $0\le j\le m$.

Proof. Newton's finite-difference identity and the finite binomial expansion of $U^t$ give

$$
\begin{aligned}
p(t)&=\sum_{j=0}^m v_j\binom tj,
&\Delta s(t)&=\sum_{j=0}^m u_j\binom tj,\\
U^t&=\sum_{j=0}^m\binom tjN^j,
&e_0^{\mathsf T}U^tv&=p(t),\quad e_0^{\mathsf T}U^tu=\Delta s(t).
\end{aligned} \tag{11.6}
$$

The polynomial expansions hold for real $t$; the matrix-power expansion is used at nonnegative integer $t$. Formula (11.2) follows from these finite differences and the fact that the $m$th difference of a degree-$m$ polynomial is its leading coefficient times $m!$.

The block power $A^k$ sends $x$ to $(\sum_{j=0}^{k-1}U^ju,1)$, with empty sum when $k=0$. Its first coordinate is $\sum_{j<k}\Delta s(j)=s(k)$ because $s(0)=0$. The source coordinate of $A^rx$ is one, so $BA^rx=(v,0)$, and $A^t$ then gives $(U^tv,0)$, proving the second identity in (11.4). The image of $B$ lies in the target, which $A$ preserves and $B$ annihilates. This proves the matrix identity $BA^rB=0$ without assuming commutation.

For a raw word $w$ of length $k$ in $A,B$, take its displayed ordered product with the rightmost matrix acting first. The full CP expansion is

$$
\operatorname{Tr}[F\mathcal T_q^k(xx^{\mathsf T})]
=q^k\sum_{|w|=k}|f^{\mathsf T}wx|^2
=q^k\left(s(k)^2+\sum_{t=0}^{k-1}p(t)^2+0\right)
=q^kk^n.
\tag{11.7}
$$

Indeed the sole all-$A$ word contributes $s(k)^2$. There are exactly $k$ one-$B$ words, uniquely $A^tBA^{k-1-t}$ for $0\le t<k$, each contributing $p(t)^2$. Every word with two or more $B$ factors contains a factor $BA^rB$ and vanishes. Thus all words and their multiplicities have been accounted for. At $k=0$ the sole empty word is the identity and $f^{\mathsf T}x=s(0)=0$. Different Kraus words contribute separate squared amplitudes; there is no interference between their amplitudes.

Both $A$ and $B$ are upper triangular, with diagonals identically one and zero, respectively. Since their entries are real, column vectorization represents $\mathcal T_q$ on the full $D^2$-dimensional complex matrix space by $q(A\otimes A+B\otimes B)$. This matrix is upper triangular with every diagonal entry equal to $q$, proving the full complex spectrum and radius in (11.5). Finite-dimensional stability gives norm convergence of the Gramian series. Its terms are real symmetric positive semidefinite matrices.

For full Gramian faithfulness, let $y=(y_T,y_s)\in\mathbb C^{m+1}\oplus\mathbb C$ obey $`y^*Qy=0`$. The positive word expansion (2.11) reads

$$
y^*Qy=\sum_{k\ge0}q^k\sum_{|w|=k}|f^{\mathsf T}wy|^2.
\tag{11.8}
$$

Every individual term must vanish. The rows $f^{\mathsf T}A^tB=p(t)e_{m+1}^{\mathsf T}$ therefore give $p(t)y_s=0$ for $0\le t\le m$. Since $p$ is a nonzero degree-$m$ polynomial, it cannot vanish at all these $m+1$ distinct integers. Hence $y_s=0$. The all-$A$ rows at $j=0,\ldots,m$ now give $e_0^{\mathsf T}U^jy_T=0$. Their coefficient matrix is

$$
\mathcal B_{j\ell}=\binom j\ell\quad(0\le j,\ell\le m),\qquad
\det\mathcal B=1,
\tag{11.9}
$$

because it is lower triangular with diagonal one. Thus $y_T=0$, proving $Q>0$ on every complex memory direction, not only on the reset vector.

For reachability, $A^jBx=(U^jv,0)$ for $0\le j\le m$. The binomial change of basis in (11.6) shows that $v,Uv,\ldots,U^mv$ span the same target space as $v,Nv,\ldots,N^mv$. In reversed target-coordinate order the latter columns form a triangular matrix with nonzero diagonal $v_m$. They are linearly independent over both $\mathbb R$ and $\mathbb C$. Together with the source vector $x$ they span all $D$ coordinates. Finally sum (11.7) in $k$ to obtain $z=Z_n(q)$. The ratio test proves finiteness for $0<q<1$, and its term $k=1$ is $q>0$. $\square$

**Theorem 11.3 (Uniform real instrument with one resetting detector).** For the data of Theorem 11.2 let $G=Q^{1/2}$ be the positive real symmetric square root, and define

$$
\begin{aligned}
\xi&=Gx/\sqrt{Z_n(q)},&\tau&=\xi\xi^{\mathsf T},\\
L_A&=\sqrt q\,GAG^{-1},&L_B&=\sqrt q\,GBG^{-1},
&J&=\xi f^{\mathsf T}G^{-1},\\
\Phi(X)&=L_AXL_A^{\mathsf T}+L_BXL_B^{\mathsf T},&&
\Psi(X)=JXJ^{\mathsf T}.
\end{aligned} \tag{11.10}
$$

They form a homogeneous complete CP instrument on all of $M_D(\mathbb C)$, with real entries, and satisfy

$$
\begin{aligned}
L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J&=I_D,
\qquad \rho(\Phi)=q,\\
\Psi(X)&=\tau\operatorname{Tr}(J^{\mathsf T}JX),\\
\Psi\Phi^k(\tau)&=\gamma_k\tau,\qquad
\gamma_k=\frac{k^nq^k}{Z_n(q)}\quad(k\ge0).
\end{aligned} \tag{11.11}
$$

The zero branch has Choi rank exactly two; the displayed zero Kraus matrix ranks are $D$ and one. The tick branch has Choi rank exactly one and one nonzero rank-one Kraus matrix. Every positive-probability tick has normalized actual output $\tau$, a fixed pure density.

Proof. The parameter mapping into Theorem 2.1 is its dimension $d=D=m+2$, raw family $K_A=\sqrt q A,K_B=\sqrt q B$, sole detector column $f=e_0$, and raw reset $x=e_{m+1}$. Both vectors are nonzero, $F=ff^{\mathsf T}\ne0$, the raw family is finite, and Theorem 11.2 establishes the required full-algebra radius $q<1$ and faithful Gramian. Its normalization is exactly $z=Z_n(q)>0$. The square root called $S$ in that theorem is $G$ here, and its normalized vector $b$ is $\xi$. All raw entries are real. The real positive-square-root conclusion of Theorem 2.1 thus applies, and $\xi^{\mathsf T}\xi=x^{\mathsf T}Qx/z=1$.

In particular the Stein identity and the effects are

$$
\begin{aligned}
Q-qA^{\mathsf T}QA-qB^{\mathsf T}QB&=F,\\
J^{\mathsf T}J&=G^{-1}FG^{-1},\\
L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J
&=G^{-1}\big(qA^{\mathsf T}QA+qB^{\mathsf T}QB+F\big)G^{-1}=I_D.
\end{aligned} \tag{11.12}
$$

These are operator equalities on the complex memory. The displayed real Kraus matrices act by their usual complex adjoints, equal to their transposes; their tensor amplifications preserve positivity for arbitrary complex positive inputs. Completeness makes each branch trace nonincreasing on such inputs. No restriction to real input densities is used.

Writing $\Gamma(X)=GXG$, one has $\Phi=\Gamma\mathcal T_q\Gamma^{-1}$, so $\rho(\Phi)=q$ and

$$
\Phi^k(\tau)=\frac{G\mathcal T_q^k(xx^{\mathsf T})G}{Z_n(q)}.
\tag{11.13}
$$

Theorem 2.1 and (11.7) therefore give the actual law and properness $\sum_{k\ge0}\gamma_k=1$. The outer-product form of $J$ gives the reset identity for every input matrix, hence the operator form $\Psi\Phi^k(\tau)=\gamma_k\tau$. In particular $\gamma_0=0$; the index is the number of preceding zeros, without a shift to duration $k+1$.

The matrix $A$ is invertible, while $B=|(v,0)\rangle\langle e_{m+1}|$ is nonzero, rank one and nilpotent. They are linearly independent over $\mathbb C$: a nonzero scalar multiple of $A$ is invertible and cannot equal $B$. Nonzero scaling and invertible similarity preserve their ranks and independence. The dimension of their completed Kraus span is therefore exactly two. Equivalently, the zero Choi matrix is a sum of the two outer products of their vectorizations and has rank two. Both factors of $J=\xi f^{\mathsf T}G^{-1}$ are nonzero, so $J$ has matrix rank one and its single-vectorization Choi matrix has rank one. This proves the stated ranks and the pure actual reset. $\square$

**Theorem 11.4 (Faithful stationary initialization and every actual cylinder).** For the completed instrument of Theorem 11.3 define

$$
\begin{aligned}
S_a&=\sum_{j\ge a}\gamma_j,\qquad
\mu=\sum_{k\ge0}(k+1)\gamma_k
=1+\frac{Z_{n+1}(q)}{Z_n(q)}<\infty,\\
\rho_*&=\frac1\mu\sum_{a\ge0}\Phi^a(\tau).
\end{aligned} \tag{11.14}
$$

Then $\operatorname{Tr}\Phi^a(\tau)=S_a$, and $`\rho_*`$ is a real faithful mixed density satisfying $`(\Phi+\Psi)(\rho_*)=\rho_*`$ and $`\rho_*\ne\tau`$. With the ordered word convention (5.2), every stationary cylinder equals

$$
\begin{aligned}
P(0^a1\,0^{g_1}1\cdots0^{g_r}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{i=1}^r\gamma_{g_i}\quad(r\ge0),\\
P(0^N)&=\frac1\mu\sum_{a\ge0}S_{N+a}
=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j\quad(N\ge0).
\end{aligned} \tag{11.15}
$$

Here $r$ counts internal gaps, so the first word has $r+1$ ones; $a,b,g_i$ are nonnegative integers. At $r=0$ the word is $0^a1\,0^b$ and the product is empty. This reparametrizes the number of ones in (1.3) and (5.7), while leaving every gap index unchanged. There is no additional all-zero stationary component.

Proof. To apply Theorem 5.1, Theorem 11.3 supplies a real completed Theorem 2.1 instrument with exactly the law (1.1) for $n=2m+1$. Its remaining full zero-word reachability premise follows as follows. For each raw word $w$, the corresponding completed word satisfies

$$
L_w\xi=\frac{q^{|w|/2}Gwx}{\sqrt{Z_n(q)}}.
\tag{11.16}
$$

The raw spanning vectors $x,A^jBx$ of Theorem 11.2 are therefore carried to a full completed span, since $q>0$ and $G$ is invertible. The ratio test gives finite $Z_{n+1}(q)$, while $Z_n(q)>0$, verifying the finite-mean parameter in (11.14). Thus every premise of Theorem 5.1 is met on the full $D$-dimensional memory, with its reset vector $b$ identified with $\xi$.

For explicit identification of the tails, put $h_a=\operatorname{Tr}\Phi^a(\tau)$. Completeness and (11.11) give $h_a-h_{a+1}=\gamma_a$. Stability gives $h_a\to0$, so $h_a=S_a$ by telescoping. The series $R=\sum_{a\ge0}\Phi^a(\tau)$ converges in norm, and

$$
\operatorname{Tr}R=\sum_{a\ge0}S_a=\mu,\qquad
\Phi(R)=R-\tau,\qquad \Psi(R)=\tau.
\tag{11.17}
$$

This proves normalization and invariance. For a complex vector $y$, the positive expansion $`y^*Ry=\sum_{a\ge0}\sum_{|w|=a}|y^*L_w\xi|^2`$ is zero only when $y$ is orthogonal to the full reachable span. Hence $R>0$, proving full complex faithfulness of $`\rho_*`$. Every term is real symmetric. Faithfulness in dimension $D\ge4$ makes $`\rho_*`$ mixed, whereas $\tau$ is pure.

The actual conditioned state after an initial zero run and the first one is

$$
\Psi\Phi^a(\rho_*)
=\frac1\mu\sum_{c\ge0}\Psi\Phi^{a+c}(\tau)
=\frac{S_a}{\mu}\tau.
\tag{11.18}
$$

Each of the $r$ following internal gaps and its tick multiplies this state by $\gamma_{g_i}$ and returns it to $\tau$. The terminal $b$ zeros contribute trace $S_b$. This gives the first formula in (11.15) as an actual ordered instrument probability. For a word with no ones, applying $\Phi^N$ directly to (11.14) gives the second formula. At $N=0$ it is one because $\sum_aS_a=\mu$; thus the empty word is included. These cases exhaust all finite binary words. Completeness and invariance supply the right and left consistency identities, respectively, as in Theorem 5.1.

Finally $P(0^N)\le\mu^{-1}\sum_{j\ge N}(j+1)\gamma_j\to0$, excluding an extra all-zero component. The two initialization meanings are also distinguished by the actual readouts

$$
\operatorname{Tr}\Psi(\tau)=\gamma_0=0,\qquad
\operatorname{Tr}\Psi(\rho_*)=\mu^{-1}>0.
\tag{11.19}
$$

The invariant-instrument and ordered-word conventions agree with [Monras–Beige–Wiesner, arXiv:1002.2337v2, p. 12, equations (25)–(27)](https://arxiv.org/pdf/1002.2337v2). The specific renewal tails, boundary factors and pure-reset identities here are the consequences of Theorems 2.1 and 5.1 with the displayed parameter mapping. $\square$

**Theorem 11.5 (Uniform affirmative single-detector upper construction).** For every odd $n\ge5$ and every $0<q<1$, Definition 7.2 has an affirmative mathematical realization on $D_n=(n+3)/2$ complex memory dimensions with real fixed Kraus entries, zero Choi rank two, one rank-one tick Kraus operator, a pure actual reset, and every stationary cylinder (1.3). This is an unconditional upper construction within Definition 1.2; it uses no finite-CP growth hypothesis.

Proof. Write $n=2m+1$ with $m\ge2$. Theorem 10.2 supplies the pair at that $m$, Definition 11.1 supplies exactly $m+2=D_n$ raw coordinates, Theorems 11.2–11.3 give the complete stable instrument and its exact ranks, and Theorem 11.4 gives the full stationary law. The $m+1$ target coordinates and the source coordinate are all inside those $D_n$ dimensions. No zero Kraus label is retained: the two zero terms are summed inside $\Phi$. The single tick is the map with matrix $J$, whose actual normalized output is $\tau$. There is no retained auxiliary reset register, controller or correlated external input. The complex polynomial $a_s$ of the existence proof is an auxiliary mathematical factor and introduces no physical register or dimension doubling; the final displayed matrices are real on the same complex memory as Definition 1.2.

This supplies the uniform target mentioned in Definition 9.9. Its phrase “by these constructions” concerns Sections 8–9 and their quintic and septic instances; the uniform conclusion here uses the separate anchored existence theorem. Since $\gamma_0=0$, $\gamma_k>0$ for $k\ge1$, and all boundary tails are positive, (11.15) also gives exactly the Fibonacci legal visible support as in Theorem 7.1. $\square$

**Definition 11.6 (Mathematical and interpretation limits of the uniform construction).** Theorem 10.1 assumes strict positivity on the entire real line and exact even degree $2m$ with $m\ge1$. Its $m=1$ range includes a cubic specialization; Section 11 concerns $m\ge2$, and neither argument here extends its statement to $m=0$ or $n=1$. Brouwer supplies existence of a fixed point, with no assertion of uniqueness, nonsingularity, convergence of iterating $\mathcal F$, or efficient coefficient computation. Corollary 10.3 is restricted to rational polynomial data and existence of some algebraic pair.

The anchored telescoping argument and its uniform detector application are a repository synthesis of standard complex polynomial factorization and root-continuity arguments, Brouwer's theorem, Newton finite differences, and the CP Gramian and stationary interfaces of Theorems 2.1 and 5.1. The cited scalar factorization does not supply the anchor or its continuity proof by attribution, and the stationary-instrument reference does not replace the renewal calculation. No worldwide novelty or priority claim is made.

The upper construction has an ordinary mathematical proof. General Lean proofs of the anchored fixed-point theorem, the full uniform instruments, their Gramians and stationary interfaces remain unfinished. Existing finite-word and reachable positive-semidefinite applications do not certify full finite-CP growth or this uniform instrument family. A dimension-minimum comparison continues to require the handwritten finite-CP growth and reachable-restriction/radius inputs stated in Theorem 6.2; the present upper construction supplies no unconditional dimension-minimum conclusion.

The output object remains the classical stationary renewal cylinders, with a faithful mixed invariant initialization distinct from the pure actual tick reset. Real coordinates are coordinates for ordinary CP maps on $M_D(\mathbb C)$, not a physical real-Hilbert-space equivalence. No native AURIC realization, preparation map, coherent-output state, finite-precision implementation, memory-entropy bound, energy, work or control-cost conclusion follows. The uniform real single-detector existence question is addressed at the ordinary mathematical level; the physical and full-kernel goals remain open.

## 追加锚（本行以下为增补区）

## 12. Certified ninth-degree coefficient selection

**Definition 12.1 (Monic amplitudes and a rational box).** Write $\Delta h(t)=h(t+1)-h(t)$. For $\theta=(a_0,a_1,a_2,a_3,b_1,b_2,b_3,b_4)\in\mathbb R^8$, put

$$
\begin{aligned}
P_\theta(t)&=t^4+a_3t^3+a_2t^2+a_1t+a_0,&
S_\theta(t)&=b_1t+b_2t^2+b_3t^3+b_4t^4,\\
E_j(\theta)&=[t^j]\left(P_\theta^2+\Delta(S_\theta^2)
-\frac{(t+1)^9-t^9}{9}\right),&&0\le j\le7.
\end{aligned} \tag{12.1}
$$

The coefficient of degree eight in the residual is identically zero, and there are no higher coefficients. In particular $E=(E_0,\ldots,E_7)^{\mathsf T}=0$ is the complete polynomial equation. With $P_i=[t^i]P_\theta$, $S_i=[t^i]S_\theta$, so that $P_4=1$ and $S_0=0$, its explicit rational coefficient map is

$$
E_j(\theta)=
\sum_{\substack{0\le r,s\le4\\r+s=j}}P_rP_s+
\sum_{\substack{1\le r,s\le4\\r+s>j}}\binom{r+s}{j}S_rS_s
-\frac19\binom9j. \tag{12.2}
$$

Define the rational center and radius by

$$
c=\frac1{10^{12}}
\begin{pmatrix}
30948152948\\
-193917702707\\
1376696052239\\
-826799586982\\
-359802936565\\
1031351485193\\
-1180309452555\\
840654445504
\end{pmatrix},
\qquad r=\frac1{10^8},\qquad
\mathcal B_9=\{\theta:\|\theta-c\|_\infty\le r\}. \tag{12.3}
$$

The constants $\theta_*$ below mean the unique zero of $E$ in $\mathcal B_9$, whose existence is proved next. The rational center is certificate data, not the exact zero.

**Theorem 12.2 (Quantitative localization and nonsingularity throughout the box).** There is exactly one zero $\theta_*$ of $E$ in $\mathcal B_9$. It lies in its interior, and $DE(\theta)$ is invertible at every point of that box.

Proof. The Jacobian has columns in the coordinate order of Definition 12.1 and coefficient rows in increasing degree $j=0,\ldots,7$. Extending $P_i$ by zero outside $0\le i\le4$, the Jacobian entries are

$$
\begin{aligned}
\frac{\partial E_j}{\partial a_r}&=2P_{j-r} &&(0\le r\le3),\\
\frac{\partial E_j}{\partial b_r}
&=2\sum_{\substack{1\le s\le4\\r+s>j}}\binom{r+s}{j}S_s
&&(1\le r\le4).
\end{aligned} \tag{12.4}
$$

The only nonzero Hessian entries are

$$
\frac{\partial^2 E_j}{\partial a_r\partial a_s}
=2\mathbf1_{\{r+s=j\}},\qquad
\frac{\partial^2 E_j}{\partial b_r\partial b_s}
=2\mathbf1_{\{r+s>j\}}\binom{r+s}{j};\qquad
\frac{\partial^2 E_j}{\partial a_r\partial b_s}=0. \tag{12.5}
$$

Here each $a$ index ranges over $0,\ldots,3$ and each $b$ index over $1,\ldots,4$. Let $J_0=DE(c)$, $M=10^{12}J_0$, and $H_\ell=DE(e_\ell)-DE(0)$ for the $\ell$th coordinate unit vector, $1\le\ell\le8$. Thus $M$ and every $H_\ell$ are integer matrices defined entry by entry by (12.3)–(12.5). Exact elimination gives

$$
\begin{aligned}
D:=\det M
&=1609746256772333630243120555818415603867799240610475316946905877536454627003261283417598578868092928,\\
\det J_0&=\frac{D}{10^{96}},\qquad 1609<\det J_0<1610,\\
C&=J_0^{-1}=\frac{10^{12}}D\operatorname{adj}(M).
\end{aligned} \tag{12.6}
$$

This defines $C$ exactly over $\mathbb Q$, without a rounded inverse. The center residual is

$$
E(c)=\frac{R}{9\cdot10^{24}},\qquad
R=\begin{pmatrix}
2749658638697\\
17343986166144\\
63810337611240\\
88047066463386\\
129434936347566\\
72396013326066\\
50235466044228\\
9914818609152
\end{pmatrix}. \tag{12.7}
$$

For the derivative tensor, put
$\beta_i=\sum_{k=1}^8\sum_{\ell=1}^8|(CH_\ell)_{ik}|$.
The following strict rational bounds specify all rows, not sampled values on the box:

| Coordinate $i$ | $u_i$ with $\lvert(CE(c))_i\rvert<u_i/10^{15}$ | $v_i$ with $\beta_i<v_i$ |
| --- | --- | --- |
| $1$ | $268$ | $30$ |
| $2$ | $202$ | $307$ |
| $3$ | $398$ | $212$ |
| $4$ | $336$ | $333$ |
| $5$ | $73$ | $213$ |
| $6$ | $214$ | $343$ |
| $7$ | $18$ | $212$ |
| $8$ | $132$ | $50$ |

Here is an integer-arithmetic form of the certificate, including how to reproduce the inequalities. Compute $M$ from (12.4), its adjugate $A_M=\operatorname{adj}(M)$ by signed minors, and $H_\ell$ from (12.5). Substitution of the eight integers in (12.3) into (12.2) gives (12.7). The determinant and the table amount precisely to

$$
\begin{aligned}
1609\cdot10^{96}&<D<1610\cdot10^{96},\\
1000\,|(A_MR)_i|&<9D\,u_i,\\
10^{12}\sum_{k=1}^8\sum_{\ell=1}^8|(A_MH_\ell)_{ik}|&<D\,v_i
\qquad(1\le i\le8).
\end{aligned} \tag{12.8}
$$

These finite integer inequalities follow by multiplication and comparison of the specified integers. For an elimination alternative to signed-minor expansion, start with $M$, previous pivot $d=1$, and update the lower-right submatrix at pivot $a=M_{kk}$ by
$M_{ij}\leftarrow(aM_{ij}-M_{ik}M_{kj})/d$ for $i,j>k$, then set $d=a$ and eliminate the entries below that pivot. All divisions are exact; a row interchange changes the determinant sign. The final entry gives $D$. Rational Gauss–Jordan elimination of $[M\mid I_8]$ gives $M^{-1}$, and $A_M=DM^{-1}$ gives the same integer comparisons (12.8). Thus the certificate is reproducible from a fully specified coefficient map by finite exact arithmetic.

In the vector maximum norm and its induced matrix norm, these comparisons give

$$
\begin{aligned}
\alpha&:=\|CE(c)\|_\infty<\bar\alpha:=\frac{398}{10^{15}},\\
\beta&:=\max_i\beta_i<343,\qquad
L:=343r=\frac{343}{10^8}<1.
\end{aligned} \tag{12.9}
$$

Since $E$ is quadratic, its derivative has the exact affine expansion
$DE(c+h)=J_0+\sum_{\ell=1}^8h_\ell H_\ell$.
Consequently for $\|h\|_\infty\le r$,

$$
\|I_8-CDE(c+h)\|_\infty
\le\beta\|h\|_\infty\le L.
\tag{12.10}
$$

Let $T(\theta)=\theta-CE(\theta)$. The segment integral of its derivative makes $T$ Lipschitz on the convex closed box with constant at most $L$. Its image lies strictly inside the box, since

$$
\begin{aligned}
\|T(\theta)-c\|_\infty
&\le\alpha+L\|\theta-c\|_\infty
<\bar\alpha+Lr
=\frac{4323}{10^{16}}<r,\\
\frac{\bar\alpha}{1-L}&<\frac4{10^{13}}.
\end{aligned} \tag{12.11}
$$

Banach's contraction theorem on this complete box gives a unique fixed point in its interior. Invertibility of $C$ makes the fixed points exactly the zeros of $E$. Moreover (12.10) makes $CDE(\theta)$ invertible by the Neumann series at every point of the box, so $DE(\theta)$ is invertible there. Uniqueness outside this box is not asserted. The fixed-point principle used here is the classical one of S. Banach, “Sur les opérations dans les ensembles abstraits et leur application aux équations intégrales,” *Fundamenta Mathematicae* **3**, 133–181, [doi:10.4064/fm-3-1-133-181](https://doi.org/10.4064/fm-3-1-133-181); the particular coefficient map, box and rational inequalities are the certificate for this degree. $\square$

**Theorem 12.3 (Exact rational selection, coefficient error and the uniform parameter match).** With $C,\bar\alpha,L$ as in (12.6) and (12.9), define for integers $N\ge0$

$$
\theta^{(0)}=c,\qquad
\theta^{(N+1)}=\theta^{(N)}-CE(\theta^{(N)}),\qquad
\varepsilon_N=\frac{\bar\alpha L^N}{1-L}.
\tag{12.12}
$$

Every iterate is rational and lies in the interior of $\mathcal B_9$. Its distance to the unique zero of Theorem 12.2 obeys both

$$
\begin{aligned}
\|\theta^{(N)}-\theta_*\|_\infty
&<\varepsilon_N<\frac4{10^{13}}\left(\frac{343}{10^8}\right)^N,\\
\|\theta^{(N)}-\theta_*\|_\infty
&\le\frac{\|CE(\theta^{(N)})\|_\infty}{1-L}.
\end{aligned} \tag{12.13}
$$

Set $p=3P_{\theta_*}$, $s=3S_{\theta_*}$ and $p^{(N)}=3P_{\theta^{(N)}}$, $s^{(N)}=3S_{\theta^{(N)}}$. For a polynomial $h$, let $\|h\|_{\mathrm{coef},\infty}=\max_j|[t^j]h|$. Then

$$
\begin{aligned}
\max\{\|p^{(N)}-p\|_{\mathrm{coef},\infty},
       \|s^{(N)}-s\|_{\mathrm{coef},\infty}\}
&\le3\varepsilon_N,\\
p_4=p^{(N)}_4&=3,\qquad s(0)=s^{(N)}(0)=0,\\
p(t)^2+s(t+1)^2-s(t)^2&=(t+1)^9-t^9\quad(t\in\mathbb R).
\end{aligned} \tag{12.14}
$$

Thus this exact limiting pair satisfies every polynomial hypothesis of (10.10) at $m=4,n=9$. In Definition 11.1 the parameter match is $D=6$, target $e_0,\ldots,e_4$, source $x=e_5$, detector $f=e_0$, $u_j=\Delta^{j+1}s(0)$ and $v_j=\Delta^jp(0)$ for $0\le j\le4$. In particular $u_4=0$ and $v_4=72$. Theorems 11.2–11.5 apply to this selected pair for each $0<q<1$; their full complex stability, faithful completion, exact branch ranks, actual pure reset and every stationary cylinder (11.15) are the existing uniform consumers.

For the corresponding raw matrices $A,B$ in (11.1), form $u^{(N)},v^{(N)},A^{(N)},B^{(N)}$ by the same finite-difference formulas applied to $s^{(N)},p^{(N)}$. In the induced matrix maximum norm,

$$
\begin{aligned}
\|A^{(N)}-A\|_\infty
=\|u^{(N)}-u\|_\infty&\le126\varepsilon_N,\\
\|B^{(N)}-B\|_\infty
=\|v^{(N)}-v\|_\infty&\le24\varepsilon_N,\\
u^{(N)}_4&=0,\qquad v^{(N)}_4=72.
\end{aligned} \tag{12.15}
$$

For any prescribed rational coefficient tolerance $\eta>0$, a reproducible finite selection is the first integer $N\ge0$ for which $3\varepsilon_N\le\eta$, followed by the rational recursion (12.12). This selects the raw amplitude coefficients within $\eta$ of the specified exact pair. Replacing $3$ by $126$ gives the same guarantee for both raw matrices in (12.15). These are exact-arithmetic error certificates, with no bit-complexity bound.

Proof. Theorem 12.2 gives a rational polynomial map $T$ taking the box to its interior with Lipschitz constant $L<1$, so the iterates have the stated location and rationality. Since
$\|T(c)-c\|_\infty=\alpha<\bar\alpha$, successive differences satisfy
$\|\theta^{(N+1)}-\theta^{(N)}\|_\infty\le L^N\alpha$.
Summing the geometric tail proves convergence to $\theta_*$ and the first bound in (12.13), including the bound from (12.11). For any $y\in\mathcal B_9$,

$$
\|y-\theta_*\|_\infty
\le\|y-T(y)\|_\infty+L\|y-\theta_*\|_\infty,
\tag{12.16}
$$

which proves the second bound. Each number in this stopping rule and its residual bound is obtained from the rational data (12.2)–(12.9) by finitely many additions, multiplications, divisions and comparisons. Since $L^N\to0$, the stopping rule terminates for every $\eta>0$.

Multiplication by three gives the coefficient estimate in (12.14). The zero of $E$ supplies the complete degree-eight identity by (12.1)–(12.2); multiplying it by nine gives the last line of (12.14). The degree of $p$ is four and $p_4^2=9$, while $s$ is anchored and has degree at most four. These are precisely the hypotheses used in the uniform Newton lift and its consumers; no identification with a particular fixed point of the spectral-factor map in Theorem 10.1 is required.

For the raw-matrix estimates, write $\delta=\|\theta^{(N)}-\theta_*\|_\infty$. Applying the finite-difference formula (11.2) to the coefficient errors gives the following coordinatewise bounds in order $j=0,1,2,3,4$:

$$
\begin{aligned}
|v^{(N)}_j-v_j|&\le\delta\,(3,9,24,18,0)_j,\\
|u^{(N)}_j-u_j|&\le\delta\,(12,66,126,72,0)_j.
\end{aligned} \tag{12.17}
$$

For example, the second and third forward differences at zero of a quartic $h(t)=\sum_{i=0}^4h_it^i$ are $2h_2+6h_3+14h_4$ and $6h_3+36h_4$. For $p$ the leading coefficient is fixed, whereas all four nonconstant coefficients of $s$ may vary. These give the multipliers in (12.17), and the fourth difference is $24h_4$. The fifth difference is zero. Only the final columns of $A$ and $B$ vary, so their maximum row-sum errors equal the maximum norms of the corresponding column errors. This proves (12.15). $\square$

The bounds (12.13)–(12.17) are independent of $q$ and concern the exact rational selection of raw coefficients. For a finite iterate the full polynomial residual is exactly

$$
(p^{(N)}(t))^2+(s^{(N)}(t+1))^2-(s^{(N)}(t))^2
-\big((t+1)^9-t^9\big)
=9\sum_{j=0}^7E_j(\theta^{(N)})t^j.
\tag{12.18}
$$

A coefficient approximation therefore does not assert the exact gap law unless this residual vanishes. The Gramian and final instrument in (11.5) and (11.10) depend on $q$ and on inversion and positive square roots of $Q$. The raw coefficient estimates supply no bound here on those operations, on final-instrument or stationary-cylinder probability sensitivity, or on a physical implementation with finite precision. Such estimates require additional conditioning and perturbation bounds. The convergent map in (12.12) is $T=I-CE$, not the spectral-factor map $\mathcal F$ of Theorem 10.1; no convergence assertion for that other iteration follows.

**Proposition 12.4 (Positive squarefree input does not force an anchored coefficient Jacobian to be nonsingular).** On monic degree-two $P$ and anchored polynomials $S$ of degree at most two, let
$H_2(P,S)=P^2+\Delta(S^2)$, with its degree-four leading coefficient fixed at one. There is a strictly positive, squarefree real polynomial $F$ and a solution with $S$ of degree exactly two at which the map from the four free coefficients to the four coefficients of degrees zero through three of $H_2$ has singular Jacobian. Explicitly, take

$$
P(t)=t^2+t+\frac13,\qquad
S(t)=\frac{t(t-1)}{100},\qquad
F(t)=P(t)^2+\frac{t^3}{2500}=H_2(P,S).
\tag{12.19}
$$

Proof. Direct multiplication gives $\Delta(t^2(t-1)^2)=4t^3$. Also

$$
P(t)-\frac{1+t^2}{24}=\frac{23t^2+24t+7}{24}>0,
\tag{12.20}
$$

because the numerator has positive leading coefficient and discriminant $24^2-4\cdot23\cdot7=-68$. For $x=|t|\ge0$, both $1+x^2\ge x$ and $1+x^2\ge x^2$, whence $|t|^3\le(1+t^2)^2$. Squaring the positive lower bound for $P$ gives

$$
F(t)\ge\left(\frac1{576}-\frac1{2500}\right)(1+t^2)^2
=\frac{481}{360000}(1+t^2)^2>0.
\tag{12.21}
$$

If $z$ were a repeated complex root of $F$, then $z\ne0$ since $F(0)=1/9$, and $P(z)\ne0$ by (12.19). Eliminating the cubic term between $F(z)=0$ and $F'(z)=0$ and dividing by $P(z)$ yields

$$
2zP'(z)-3P(z)=z^2-z-1=0.
\tag{12.22}
$$

Both roots of this quadratic are real, contradicting strict positivity of $F$. Thus $F$ is squarefree over $\mathbb C$.

The nonzero admissible tangent variation

$$
U(t)=-\frac t{25},\qquad V(t)=t^2+\frac t3
\tag{12.23}
$$

has $\deg U\le1$, $\deg V\le2$ and $V(0)=0$. Since

$$
SV=\frac{t^4-\frac23t^3-\frac13t^2}{100},\qquad
\Delta(SV)=\frac{t^3+t^2+t/3}{25}=\frac{tP(t)}{25},
\tag{12.24}
$$

one has $DH_2(P,S)[U,V]=2(PU+\Delta(SV))=0$. The coefficient vector of this variation, in order $(P_0,P_1,S_1,S_2)$, is $(0,-1/25,1/3,1)$, so the coefficient Jacobian is singular. $\square$

This example concerns one solution of one positive quartic input. Its cubic coefficient is $2+1/2500$, whereas that of $((t+1)^5-t^5)/5$ is two; it is not the normalized monomial-difference input. It proves neither singularity of every solution for its own input nor singularity of the ninth-degree zero in Theorem 12.2, and it gives no obstruction to the uniform existence theorem. Its computational consequence is that positivity and squarefreeness alone cannot replace the explicit derivative estimate (12.10) when certifying local coefficient selection. The certificate, its error transfer and this counterexample are repository mathematical derivations using the cited classical fixed-point principle and the existing uniform suppliers, without a claim of worldwide novelty.

## 追加锚（本行以下为增补区）

## 13. Detector dead time, reachable support and actual reset rigidity

**Definition 13.1 (Finite CP detection and gap indexing).** Let $H$ be a complex Hilbert space of finite dimension $D\ge0$. For a finite, possibly empty family of operators $K_i:H\to H$, let

$$
\Phi(X)=\sum_iK_iXK_i^\dagger,\qquad
\Phi^*(Y)=\sum_iK_i^\dagger YK_i.
\tag{13.1}
$$

Here $\dagger$ denotes the Hilbert-space adjoint and $\Phi^*$ the trace dual. A word $w=(i_1,\ldots,i_k)$ acts as $K_w=K_{i_k}\cdots K_{i_1}$; the empty word acts as the identity. For arbitrary positive semidefinite operators $\tau,F$, define

$$
\begin{aligned}
U&=\operatorname{ran}\tau,&u&=\operatorname{rank}\tau,\\
R&=\operatorname{span}\{K_wU:w\text{ a finite word}\},&r&=\dim R,\\
R^\vee&=\operatorname{span}\{K_{i_k}^\dagger\cdots K_{i_1}^\dagger
\operatorname{ran}F:k\ge0\},&r^\vee&=\dim R^\vee,\\
w_k&=\operatorname{Tr}[F\Phi^k(\tau)]\quad(k\ge0).
\end{aligned}
\tag{13.2}
$$

The seed need not be pure or normalized, and $F$ need not be an effect. If some $w_k>0$, the first-hit index is $h=\min\{k\ge0:w_k>0\}$. In a binary instrument, $\Phi$ is the no-tick branch: $k$ counts zeros after a tick and before the next tick. Thus a first possible gap index $h$ means an earliest interevent duration $h+1$; it means exactly that gap counts $0,\ldots,h-1$ are forbidden and gap count $h$ has positive probability. It makes no assertion about later gaps.

**Theorem 13.2 (Support horizon and its two detector bounds).** For the data of Definition 13.1, put $b=r-u$. Then

$$
X_b=\sum_{k=0}^{b}\Phi^k(\tau),\qquad
\operatorname{ran}X_b=R,\qquad \ker X_b=R^\perp.
\tag{13.3}
$$

Vanishing of $w_0,\ldots,w_b$ is equivalent both to $F$ annihilating $R$ and to vanishing of every $w_k$. If detection is nontrivial, both $\tau$ and $F$ have positive rank and

$$
h\le r-\operatorname{rank}\tau,\qquad
h\le r^\vee-\operatorname{rank}F,
\qquad
h\le\min(r-u,r^\vee-\operatorname{rank}F)
\le D-\max(\operatorname{rank}\tau,\operatorname{rank}F).
\tag{13.4}
$$

No trace preservation, trace contraction, stability, commutation or single-Kraus premise is required.

Proof. The increasing-support mechanism has the finite-dimensional antecedents of [Nengkun Yu and Mingsheng Ying, *Reachability and Termination Analysis of Concurrent Quantum Programs*, arXiv:1206.1935v1, Theorem 1, pp. 7–8](https://arxiv.org/pdf/1206.1935v1), and [Shenggang Ying, Yuan Feng, Nengkun Yu and Mingsheng Ying, *Reachability Probabilities of Quantum Markov Chains*, arXiv:1304.0060v2, Lemma 1(2), p. 5](https://arxiv.org/pdf/1304.0060v2). Those displayed horizons are $D-1$. The following argument keeps the reachable and seed ranks, and supplies the detector and dual interfaces needed here.

Let $W_n=\operatorname{span}\{K_wU:|w|\le n\}$. Then

$$
W_0=U,\qquad W_{n+1}=W_n+\sum_iK_iW_n,\qquad W_n\subseteq R.
\tag{13.5}
$$

If $W_{n+1}=W_n$, each $K_i$ preserves $W_n$, so induction on word length gives $W_n=R$. Otherwise the dimension increases by at least one. Therefore $W_{r-u}=R$: either a plateau has already occurred, or the $r-u$ strict increases from dimension $u$ reach dimension $r$. This includes $r=u$, since then $U\subseteq R$ already has equal dimension.

For any matrix $M$, $\ker(MM^\dagger)=\ker M^\dagger$, by $y^\dagger MM^\dagger y=\|M^\dagger y\|^2$; taking orthogonal complements gives $\operatorname{ran}(MM^\dagger)=\operatorname{ran}M$. Since $\operatorname{ran}\tau^{1/2}=U$, it follows that

$$
\operatorname{ran}(K_w\tau K_w^\dagger)=K_wU.
\tag{13.6}
$$

For a finite collection of positive semidefinite matrices $Y_j$, their sum has kernel $\bigcap_j\ker Y_j$: a zero quadratic form of the sum forces every nonnegative summand to be zero, and $y^\dagger Y_jy=\|Y_j^{1/2}y\|^2$. Hence its range is the sum of their ranges. Expanding $\Phi^k$ into all length-$k$ Kraus words and applying this fact yields

$$
\operatorname{ran}\Big(\sum_{k=0}^n\Phi^k(\tau)\Big)=W_n.
\tag{13.7}
$$

At $n=b$ this proves (13.3), including the exact orthogonal-complement kernel. A vector merely outside $R$ need not belong to that kernel.

For positive $F,X$,

$$
\operatorname{Tr}(FX)
=\|F^{1/2}X^{1/2}\|_{\rm HS}^2\ge0.
\tag{13.8}
$$

It vanishes exactly when $F^{1/2}$, equivalently $F$, annihilates $\operatorname{ran}X$. Thus $\sum_{k=0}^bw_k=\operatorname{Tr}(FX_b)=0$ exactly when $F$ annihilates $R$. Every later $\Phi^k(\tau)$ is supported in $R$, so this condition makes every later detection weight zero as well. Conversely, vanishing forever includes vanishing through $b$. Nontrivial detection must therefore occur by $b$.

Cyclicity of the finite-dimensional trace gives, for every $k$,

$$
w_k=\operatorname{Tr}\big[\tau(\Phi^*)^k(F)\big].
\tag{13.9}
$$

Apply the same argument to the CP map $\Phi^*$ with Kraus family $K_i^\dagger$, seed $F$ and detector $\tau$. Its reachable dimension is exactly $r^\vee$, by (13.2), and it has the same nontrivial sequence and the same $h$. This proves the second bound in (13.4). Since $r,r^\vee\le D$, taking the smaller of the two ambient bounds gives the last inequality.

If $\tau=0$, then $R=0$, $b=0$, $X_b=0$ and all weights vanish. If $F=0$, detection is also trivial. If $D=0$, both operators are zero. For an empty Kraus family, $\Phi=0$, $R=U$, $b=0$ and $X_b=\tau$; detection, if any, occurs at $h=0$. The same conclusion holds for a full-rank seed whenever detection occurs. These cases require no minimum over an empty set: $h$ is defined only for nontrivial detection. $\square$

**Theorem 13.3 (Saturation from an actual post-tick state forces global reset).** Let $D\ge1$ and let $(\Phi,\Psi)$ be any finite homogeneous binary CP instrument on $M_D(\mathbb C)$, with $\Phi+\Psi$ trace preserving. For a density matrix $\rho_0$, suppose

$$
\nu=\operatorname{Tr}\Psi(\rho_0)>0,\qquad
\tau=\frac{\Psi(\rho_0)}\nu,\qquad F=\Psi^*(I_D).
\tag{13.10}
$$

Assume the first nonzero value of $\operatorname{Tr}[F\Phi^k(\tau)]$ occurs at $h=D-1$. Then $\operatorname{rank}\tau=\operatorname{rank}F=1$, $R=R^\vee=\mathbb C^D$, and, for every complex matrix $X$,

$$
\Psi(X)=\tau\operatorname{Tr}(FX).
\tag{13.11}
$$

The tick branch has Choi rank one. Every nonzero member of any of its Kraus representations has matrix rank one, and all such members span a single operator direction. If a density $\rho$ is invariant under $\Phi+\Psi$ and has $\operatorname{Tr}\Psi(\rho)=\widetilde\nu>0$, then $\rho$ is faithful. It is mixed when $D>1$.

Proof. Nontrivial detection and (13.4) give $D-1\le D-\max(\operatorname{rank}\tau,\operatorname{rank}F)$. Both ranks are positive, so both equal one. The separate reachable bounds give $D-1\le r-1,r^\vee-1$, hence both reachable spaces have dimension $D$.

Choose a unit vector $\eta$ and $\lambda>0$ with $F=\lambda\eta\eta^\dagger$, and write an arbitrary Kraus representation $\Psi(X)=\sum_iJ_iXJ_i^\dagger$. For $y\perp\eta$,

$$
0=y^\dagger Fy=\sum_i\|J_iy\|^2.
\tag{13.12}
$$

Every $J_i$ therefore vanishes on $\eta^\perp$ and has the form $J_i=v_i\eta^\dagger$. Put $M=\sum_iv_iv_i^\dagger$. Then $\operatorname{Tr}M=\lambda$ and

$$
\Psi(X)=(\eta^\dagger X\eta)M,\qquad
\nu=\lambda\eta^\dagger\rho_0\eta>0,\qquad
\tau=M/\lambda.
\tag{13.13}
$$

The last identity uses precisely the actual-output premise (13.10), not an unrelated chosen pure seed. It proves (13.11). Write $\tau=\xi\xi^\dagger$ with $\|\xi\|=1$. Since $M=\lambda\xi\xi^\dagger$, for $y\perp\xi$ the identity $0=y^\dagger My=\sum_i|y^\dagger v_i|^2$ forces every $v_i$ to be parallel to $\xi$. Thus all nonzero $J_i$ are multiples of $\xi\eta^\dagger$, and the map has the single nonzero rank-one representation $J=\sqrt\lambda\xi\eta^\dagger$. Its Choi matrix is the nonzero outer product of the vectorization of $J$ with itself, so its rank is one. Extra proportional or zero Kraus matrices do not create additional directions.

By (13.11), any invariant $\rho$ with positive tick rate satisfies $\rho=\Phi(\rho)+\widetilde\nu\tau$. Iterating $D$ times gives

$$
\rho=\Phi^D(\rho)+\widetilde\nu\sum_{k=0}^{D-1}\Phi^k(\tau)
\ \ge\ \widetilde\nu\sum_{k=0}^{D-1}\Phi^k(\tau)>0.
\tag{13.14}
$$

The last sum is positive definite by (13.3), since $r=D$ and $u=1$. Hence $\rho$ has rank $D$, and is mixed if $D>1$. When $D=1$ and $h=0$, the same argument holds: the sole density is rank one and faithful, not mixed; the sum in (13.14) is just $\tau$. A zero-dimensional carrier admits no density and is excluded from this theorem. No conclusion about the required number of no-tick Kraus directions is used in this argument. $\square$

## 14. A delayed squared-falling-factorial renewal law with exact memory dimension

**Definition 14.1 (The delayed law and the comparison class).** Fix an integer $m\ge1$ and a real $0<q<1$. For nonnegative integers $t,k$, define

$$
\begin{aligned}
(t)_{\underline m}&=t(t-1)\cdots(t-m+1),\\
P_m(k)&=\sum_{t=0}^{k-1}(t)_{\underline m}^{\,2},\qquad P_m(0)=0,\\
\mathcal Z_m(q)&=\sum_{k\ge0}q^kP_m(k),\qquad
\gamma_k=\frac{q^kP_m(k)}{\mathcal Z_m(q)},\\
S_a&=\sum_{j\ge a}\gamma_j,\qquad
\mu=\sum_{k\ge0}(k+1)\gamma_k.
\end{aligned}
\tag{14.1}
$$

The $\gamma,S,\mu$ in Section 14 belong to (14.1). This is a separate law from the monomial law (1.1). The target stationary cylinders are

$$
\begin{aligned}
\mathbb P_{m,q}(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{i=1}^{r-1}\gamma_{g_i}\quad(r\ge1),\\
\mathbb P_{m,q}(0^N)&=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j\quad(N\ge0).
\end{aligned}
\tag{14.2}
$$

All zero-run lengths are nonnegative integers. The internal product is one at $r=1$, and $N=0$ denotes the empty word. The existence and stationary consistency of this law follow from the actual instrument in Theorem 14.4.

A competing realization consists of a finite-dimensional complex memory, fixed CP maps $\mathcal E_0,\mathcal E_1$ whose sum is trace preserving, and a density $\rho_0$, such that for every finite binary word

$$
\operatorname{Tr}\big[\mathcal E_{w_N}\cdots\mathcal E_{w_1}(\rho_0)\big]
=\mathbb P_{m,q}(w_1\cdots w_N).
\tag{14.3}
$$

Neither invariance of $\rho_0$ nor a reset structure is assumed for the competitor. Every persistent register and any controller affecting later operations belongs to the counted complex memory dimension, as in Definition 1.2. The maps are homogeneous in time and there is no additional correlated external input.

**Theorem 14.2 (Raw realization, full complex stability and two kinds of full span).** Put $D=m+2$ and use the ordered orthonormal basis $e_0,\ldots,e_m,e_s$, where $s=m+1$. On the target coordinates $e_0,\ldots,e_m$ let $N_{j,j+1}=1$ for $0\le j<m$, all other entries zero, and $U=I_{m+1}+N$. Embed $v=m!e_m$ in the target and set

$$
A=\begin{pmatrix}U&0\\0&1\end{pmatrix},\qquad
B=ve_s^{\mathsf T},\qquad x=e_s,\qquad f=e_0,\qquad
F_0=ff^{\mathsf T},\qquad
\mathcal T_q(X)=q(AXA^{\mathsf T}+BXB^{\mathsf T}).
\tag{14.4}
$$

These real matrices act on all of $M_D(\mathbb C)$. They satisfy

$$
\begin{aligned}
\operatorname{Tr}[F_0\mathcal T_q^k(xx^{\mathsf T})]&=q^kP_m(k),\\
\operatorname{spec}(\mathcal T_q)&=\{q\},\qquad \rho(\mathcal T_q)=q<1,\\
Q=\sum_{k\ge0}(\mathcal T_q^*)^k(F_0)&>0,\qquad
x^{\mathsf T}Qx=\mathcal Z_m(q)\in(0,\infty).
\end{aligned}
\tag{14.5}
$$

The raw reachable span from $x$ is all of $\mathbb C^D$. Moreover $P_m$ extends to a polynomial of degree $2m+1$ with leading coefficient $1/(2m+1)$, and its exact initial zero set on the nonnegative integers is $0,\ldots,m$.

Proof. Since $N^{m+1}=0$, the finite binomial expansion gives $U^t=\sum_{j=0}^m\binom tjN^j$ for every nonnegative integer $t$. Therefore

$$
f^{\mathsf T}A^kx=0,\qquad
f^{\mathsf T}A^tBA^rx=m!\binom tm=(t)_{\underline m},\qquad
BA^rB=0
\tag{14.6}
$$

for all $k,t,r\ge0$. Indeed $A^rx=x$, $Bx=v$, and $e_0^{\mathsf T}N^jv$ is zero except at $j=m$, where it is $m!$. The last matrix identity follows because $B$ maps into the target, $A$ preserves the target and $B$ annihilates it.

In the expansion of $\mathcal T_q^k$, the all-$A$ word has zero detector amplitude. The words with exactly one $B$ are uniquely $A^tBA^{k-1-t}$, one for each $0\le t<k$, and their squared detector amplitudes are $(t)_{\underline m}^{2}$. Every word with at least two $B$ factors contains a factor $BA^rB$ and is zero. Consequently

$$
\operatorname{Tr}[F_0\mathcal T_q^k(xx^{\mathsf T})]
=q^k\sum_{|w|=k}|f^{\mathsf T}wx|^2
=q^k\sum_{t=0}^{k-1}(t)_{\underline m}^{2}.
\tag{14.7}
$$

At $k=0$ the sole word is the identity and $f^{\mathsf T}x=0$, so the formula includes the empty word. The CP sum adds squared amplitudes of separate Kraus words, with no cross-word interference.

The squared falling factorial vanishes for integers $0\le t<m$ and is strictly positive for $t\ge m$. Thus $P_m(0)=\cdots=P_m(m)=0$, $P_m(m+1)=(m!)^2$, and $P_m(k)>0$ for every $k\ge m+1$. To justify the polynomial assertion, the difference operator $\Delta p(t)=p(t+1)-p(t)$ maps polynomials of degree at most $2m+1$ modulo constants bijectively onto polynomials of degree at most $2m$: in monomial bases it is triangular with nonzero leading coefficients $\Delta t^j=jt^{j-1}+\text{lower terms}$. There is therefore a unique polynomial with $p(0)=0$ and $\Delta p(t)=(t)_{\underline m}^{2}$. Telescoping identifies its nonnegative integer values with $P_m(k)$, and the leading coefficient is $1/(2m+1)$. For example, $P_1(k)=k(k-1)(2k-1)/6$, since the displayed polynomial is zero at zero and its forward difference is $k^2$.

Both $A$ and $B$ are upper triangular, with respective diagonals all one and all zero. Column vectorization on the full complex matrix algebra represents $\mathcal T_q$ by $q(A\otimes A+B\otimes B)$, an upper triangular $D^2$ by $D^2$ matrix with every diagonal entry $q$. This proves the spectrum assertion on the full complex space. Writing this matrix as $qI+V$ with $V^{D^2}=0$ bounds its $k$th power by a constant times a polynomial in $k$ times $q^k$. Equivalently, for each $q<a<1$ there is a constant $C_a$ with $\|\mathcal T_q^k\|\le C_aa^k$. The same bound holds for the dual, so the Gramian series converges in norm.

Every term of $Q$ is real symmetric positive semidefinite. Its quadratic form on a complex vector $y=(y_T,y_s)$ is

$$
y^\dagger Qy=\sum_{k\ge0}q^k\sum_{|w|=k}|f^{\mathsf T}wy|^2.
\tag{14.8}
$$

If this vanishes, the row $f^{\mathsf T}A^mB=m!e_s^{\mathsf T}$ forces $y_s=0$. The all-$A$ rows $f^{\mathsf T}A^j$ for $0\le j\le m$ then give $\sum_{\ell=0}^m\binom j\ell(y_T)_\ell=0$. Their coefficient matrix is lower triangular with diagonal one, so $y_T=0$. This proves $Q>0$ on complex vectors, not only on real states or the reset direction.

Separately, the vectors $x,A^jBx$ for $0\le j\le m$ span the full memory. Their target components are $U^jv=\sum_{\ell=0}^m\binom j\ell N^\ell v$. The same invertible binomial coefficient matrix relates these vectors to $N^\ell v=m!e_{m-\ell}$, a target basis. The additional $x=e_s$ supplies the source direction. This is reachability from $x$, distinct from the detector observability proving $Q>0$.

Finally $x^{\mathsf T}Qx=\sum_{k\ge0}q^kP_m(k)$ by (14.7). For $k\ge1$, $0\le P_m(k)\le k^{2m+1}$, since the terms below $m$ are zero and $0<(t)_{\underline m}\le t^m$ for $t\ge m$. The ratio test applied to $q^kk^{2m+1}$ proves convergence, and the $k=m+1$ term proves positivity. The same estimate with any additional fixed power of $k$ gives finite moments, in particular $\mu<\infty$ in (14.1). $\square$

**Theorem 14.3 (Real complete instrument and exact Kraus directions).** For (14.4)–(14.5), set $z=\mathcal Z_m(q)$, let $G=Q^{1/2}$ be the positive real symmetric square root, and define

$$
\begin{aligned}
\xi&=Gx/\sqrt z,&\tau&=\xi\xi^{\mathsf T},&E&=G^{-1}F_0G^{-1},\\
L_A&=\sqrt q\,GAG^{-1},&L_B&=\sqrt q\,GBG^{-1},&J&=\xi f^{\mathsf T}G^{-1},\\
\Phi(X)&=L_AXL_A^{\mathsf T}+L_BXL_B^{\mathsf T},&&
\Psi(X)=JXJ^{\mathsf T}.
\end{aligned}
\tag{14.9}
$$

This is a homogeneous binary CP instrument on $M_D(\mathbb C)$ with real entries and

$$
\begin{aligned}
L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J&=I_D,\\
\rho(\Phi)&=q<1,\qquad \Psi(X)=\tau\operatorname{Tr}(EX),\\
\Psi\Phi^k(\tau)&=\gamma_k\tau,\qquad
\sum_{k\ge0}\gamma_k=1,\qquad
\operatorname{Tr}\Phi^a(\tau)=S_a.
\end{aligned}
\tag{14.10}
$$

The no-tick branch has exactly two independent Kraus directions and Choi rank two. The displayed no-tick matrix ranks are $D$ and one. The tick branch has one nonzero rank-one Kraus operator and Choi rank one. Its positive-probability outputs all normalize to the same pure state $\tau$. Its first-hit gap index is $m+1=D-1$.

Proof. Theorem 2.1 applies with raw Kraus family $\sqrt q A,\sqrt q B$, detector column $f$, reset $x$, dimension $D=m+2$ and square root $G$. Theorem 14.2 verifies its full-complex stability and positive-Gramian premises and identifies its normalization as $z=\mathcal Z_m(q)$. Real orthogonal diagonalization of $Q>0$ gives real invertible $G$ and $\xi^{\mathsf T}\xi=1$. For explicit verification, shifting the norm-convergent Gramian gives

$$
Q-qA^{\mathsf T}QA-qB^{\mathsf T}QB=F_0.
\tag{14.11}
$$

Conjugating by $G^{-1}$ yields completeness in (14.10); the detector term is $J^{\mathsf T}J=E$. Each displayed Kraus expression is completely positive on arbitrary complex positive inputs, because its amplification is a sum of conjugations by the Kraus matrices tensored with the identity. Completeness gives trace preservation of the sum and trace nonincrease of each branch. Thus the real entries do not restrict the allowed inputs to real densities.

For the invertible matrix-space map $\Gamma(X)=GXG$,

$$
\Phi=\Gamma\mathcal T_q\Gamma^{-1},\qquad
\Phi^k(\tau)=\frac{G\mathcal T_q^k(xx^{\mathsf T})G}{z}.
\tag{14.12}
$$

This proves full stability. The outer-product formula for $J$ proves $\Psi(X)=\tau\operatorname{Tr}(EX)$ for every $X$. Combining (14.12) with (14.7) gives $\Psi\Phi^k(\tau)=q^kP_m(k)\tau/z$. Normalization is exactly the defining sum for $z$. If $s_a=\operatorname{Tr}\Phi^a(\tau)$, completeness gives $s_a-s_{a+1}=\gamma_a$, and stability gives $s_a\to0$. Telescoping gives $s_a=S_a$, including $S_0=1$ and no mass at an infinite next gap.

The matrix $A$ is invertible, whereas $B=ve_s^{\mathsf T}$ is nonzero of rank one. They are linearly independent over $\mathbb C$, since a nonzero scalar multiple of $A$ has rank $D>1$. Invertible similarity and nonzero scaling preserve their ranks and independence. The Choi matrix of $\Phi$ is the sum of the outer products of the vectorizations of $L_A,L_B$; its range is their two-dimensional span, by the positive-sum argument of (13.7). Hence its rank is two, which is also the minimum Kraus count: any Kraus representation gives such a sum and must span its range, while the displayed two operators attain that count. Both factors of $J$ are nonzero, so it has matrix rank one and its Choi matrix has rank one. Lastly Theorem 14.2 gives $\gamma_0=\cdots=\gamma_m=0$ and $\gamma_{m+1}>0$, proving the asserted first-hit index and earliest interevent duration $m+2$. $\square$

**Theorem 14.4 (Faithful mixed stationary initialization and every cylinder).** With the instrument of Theorem 14.3, define

$$
R_0=\sum_{a\ge0}\Phi^a(\tau),\qquad
\rho_* = R_0/\mu.
\tag{14.13}
$$

Then $\rho_*$ is a real faithful mixed invariant density, its tick rate is $1/\mu$, and its actual output cylinders equal (14.2) for every finite binary word. The process is the proper stationary renewal law of (14.1), without an additional all-zero component.

Proof. Stability makes the operator series converge in norm. By (14.10) and nonnegative summation,

$$
\operatorname{Tr}R_0=\sum_{a\ge0}S_a
=\sum_{j\ge0}(j+1)\gamma_j=\mu<\infty.
\tag{14.14}
$$

Thus $\rho_*$ is a density. The reset identity and gap normalization give

$$
\Phi(R_0)=R_0-\tau,\qquad
\Psi(R_0)=\sum_{a\ge0}\gamma_a\tau=\tau.
\tag{14.15}
$$

These prove invariance and tick rate $1/\mu$. For a raw word $w$ in $A,B$, the corresponding completed word obeys

$$
L_w\xi=\frac{q^{|w|/2}Gwx}{\sqrt z}.
\tag{14.16}
$$

The full raw reachability in Theorem 14.2 therefore persists under completion. For any complex $y$, expansion of the positive series gives $y^\dagger R_0y=\sum_{a\ge0}\sum_{|w|=a}|y^\dagger L_w\xi|^2$. Its vanishing forces $y$ orthogonal to that full reachable span, hence $y=0$. This proves faithfulness. Every summand is real symmetric, and $D=m+2\ge3$ makes the rank-$D$ density mixed, whereas $\tau$ is pure.

After an initial run of $a$ zeros and the first tick, the actual unnormalized memory is

$$
\Psi\Phi^a(\rho_*)
=\frac1\mu\sum_{c\ge0}\Psi\Phi^{a+c}(\tau)
=\frac{S_a}{\mu}\tau.
\tag{14.17}
$$

For a word with $r\ge1$ ticks, each internal gap $g_i$ followed by its tick multiplies this state by $\gamma_{g_i}$ and resets to $\tau$. The final $b$ zeros have survival probability $S_b$. Taking the trace gives exactly the first formula of (14.2), including the empty internal product when $r=1$. For a word with no ticks,

$$
\operatorname{Tr}\Phi^N(\rho_*)
=\frac1\mu\sum_{a\ge0}S_{N+a}
=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j.
\tag{14.18}
$$

At $N=0$, (14.14) makes this one. These two cases exhaust all finite words. Trace preservation gives consistency on summing the last symbol; invariance of $\rho_*$ gives consistency on summing the first symbol. Thus these are stationary cylinder probabilities. Conditioned on any positive-probability tick history, the memory is exactly $\tau$. Repeated use of $\Psi\Phi^k(\tau)=\gamma_k\tau$ gives the product of the $\gamma$ values for any finite sequence of following complete gaps; $\sum_k\gamma_k=1$ gives a proper next gap each time. This proves the renewal assertion from the actual conditioned states.

Moreover

$$
0\le\mathbb P_{m,q}(0^N)
\le\frac1\mu\sum_{j\ge N}(j+1)\gamma_j\longrightarrow0.
\tag{14.19}
$$

The decreasing events of having no tick in the first $N$ steps therefore have an intersection of probability zero. In particular no positive all-zero stationary component remains. Also $\operatorname{Tr}\Psi(\tau)=\gamma_0=0$, whereas $\operatorname{Tr}\Psi(\rho_*)=1/\mu>0$, so the stationary initialization and the post-tick state are distinct.

The invariant-state and ordered-cylinder convention agrees with [Alex Monras, Almut Beige and Karoline Wiesner, *Hidden Quantum Markov Models and non-adaptive read-out of many-body states*, arXiv:1002.2337v2, p. 12, equations (25)–(27)](https://arxiv.org/pdf/1002.2337v2). The summation mechanism is the one used in Section 5, but Theorem 5.1 and the application in Section 11 specify the monomial law. Equations (14.14)–(14.19) provide the stationary derivation for the distinct law (14.1) with its own tails and mean. $\square$

**Theorem 14.5 (Exact minimum complex dimension and saturation of every minimizer).** For every $m\ge1$ and $0<q<1$, the minimum complex memory dimension among all realizations in Definition 14.1 is exactly $m+2$. For a competitor of dimension $D'$ let $\tau_0$ be its actual average state just after the first tick and let $F_1=\mathcal E_1^*(I_{D'})$. Then

$$
D'\ge m+1+\max(\operatorname{rank}\tau_0,\operatorname{rank}F_1)
\ge m+2.
\tag{14.20}
$$

At the minimum, both ranks are one, both reachable spaces of (13.2) are the full memory, and the competitor's entire tick map is $\mathcal E_1(X)=\tau_0\operatorname{Tr}(F_1X)$ with Choi rank one. Any invariant initialization of that minimum-dimensional competitor reproducing the law is faithful and mixed. These conclusions allow a noninvariant hidden initializer in (14.3) and assume no reset for the competitor.

Proof. Theorem 14.4 supplies a realization in dimension $m+2$, establishing the upper bound with all stationary cylinders. For any competitor, use the one-symbol cylinder and the two-tick cylinders in (14.2):

$$
\begin{aligned}
\nu&=\operatorname{Tr}\mathcal E_1(\rho_0)
=\mathbb P_{m,q}(1)=1/\mu>0,\\
\tau_0&=\mathcal E_1(\rho_0)/\nu,\qquad
F_1=\mathcal E_1^*(I_{D'}),\\
\operatorname{Tr}[F_1\mathcal E_0^k(\tau_0)]
&=\frac{\operatorname{Tr}[\mathcal E_1\mathcal E_0^k\mathcal E_1(\rho_0)]}{\nu}
=\frac{\mathbb P_{m,q}(1\,0^k1)}{\mathbb P_{m,q}(1)}
=\gamma_k.
\end{aligned}
\tag{14.21}
$$

The last equality uses $S_0=1$. This is the conditional next-gap marginal after an actual tick; no independence premise is needed for the displayed equality. The imposed stationary output law fixes this marginal even when $\rho_0$ itself is not invariant. Positivity makes $\tau_0$ a density and $F_1$ a positive effect. A finite-dimensional CP map admits a finite Kraus representation, as follows by diagonalizing its finite positive Choi matrix and unvectorizing its eigenvectors, so Theorem 13.2 applies to $\mathcal E_0$ without a restriction on its Kraus count.

Theorem 14.2 identifies the first positive $\gamma_k$ as $k=m+1$. Equation (13.4), with $h=m+1$, proves (14.20). If $D'=m+2$, then $h=D'-1$ and (14.21) supplies precisely the actual-output premise of Theorem 13.3. That theorem gives the pure output, rank-one effect, full primal and dual reachable spaces, global reset and tick Choi rank one. If the competitor also has an invariant initialization reproducing the cylinders, its tick rate is $1/\mu>0$, and (13.14) makes it faithful; $D'\ge3$ makes it mixed. No hidden invariance is used for the lower bound or the global-reset conclusion. $\square$

**Definition 14.6 (Scope of the delayed-family conclusion).** The mathematical result of Section 14 concerns exact classical output cylinders of the finite homogeneous instruments in Definition 14.1. Its lower bound uses the initial forbidden block of gap counts $0,\ldots,m$ and the first positive count $m+1$, via Theorem 13.2. It uses no finite-CP polynomial-growth or peripheral-radius lower bound. The original monomial law (1.1) has a different initial support and is outside this minimum-dimension conclusion; the unresolved minimum dependencies stated for that law are not resolved by (14.20).

The support-saturation mechanism cited in Theorem 13.2 and the ordered-instrument convention cited in Theorem 14.4 are literature antecedents. The two-sided detector interface, its actual-post-tick saturation consequence, and the completed delayed-family application are repository derivations with the complete arguments above. These attributions do not assert global novelty or priority. In particular the cited reachability formulas do not by attribution establish the explicit matrices, their stationary law or its minimum; those are derived in (14.4)–(14.21).

The displayed construction has two independent no-tick Kraus directions. The saturation argument proves a restriction on the tick branch, and supplies no universal lower bound on the no-tick Kraus count. Its global reset conclusion requires the actual-output identity (13.10); choosing an unrelated pure seed is not that premise. Positive tick rate alone does not prove renewal independence or exclude a silent stationary component; the construction uses its reset identity and stability to establish those facts explicitly.

These are handwritten mathematical arguments. A general Lean verification of the detector interfaces, rigidity, completed family and all stationary cylinders is not supplied here. Real coordinates mean ordinary CP maps on a complex memory; they do not assert a physical real-Hilbert-space equivalence, native AURIC realization, preparation or precision guarantee, coherent-output equivalence, memory entropy, energy or work bound. The memory comparison counts persistent complex Hilbert-space dimension only.

## 追加锚（本行以下为增补区）

## 15. Polynomial residuals control actual stationary output

**Definition 15.1 (Anchored residual data and the actual comparison law).** Fix an integer $m\ge2$, put $n=2m+1$ and $D=m+2$, and take real polynomials $P,S$ with $P$ monic of degree $m$, $\deg S\le m$, and $S(0)=0$. Define

$$
\begin{aligned}
e(t)&=P(t)^2+\Delta(S^2)(t)-\frac{\Delta(t^n)}n
=\sum_{j=0}^{n-2}E_jt^j,\\
H(k)&=k^n+n\sum_{t=0}^{k-1}e(t)
=n\left(S(k)^2+\sum_{t=0}^{k-1}P(t)^2\right)
\quad(k\in\mathbb Z_{\ge0}),\\
Z_H(q)&=\sum_{k\ge0}H(k)q^k,\qquad
\widehat\gamma_k=\frac{H(k)q^k}{Z_H(q)}\quad(0<q<1).
\end{aligned} \tag{15.1}
$$

Empty sums are zero. The second expression for $H$ follows by telescoping and the anchor. The top coefficients of $P^2$ and $\Delta(t^n)/n$ are both one, while $\deg\Delta(S^2)\le2m-1$; thus $\deg e\le n-2$. Discrete antidifferentiation makes $H$ a monic polynomial of degree $n$ with $H(0)=0$. On the nonnegative integers it is nonnegative by the square expression, and it is positive for all $k\ge m+1$: a degree-$m$ monic polynomial cannot vanish at all of $0,\ldots,m$. Consequently $Z_H(q)$ is positive and finite, and $\widehat\gamma$ has every finite moment. No vanishing-residual hypothesis is included in this definition.

The reference law remains $\gamma_k=k^nq^k/Z_n(q)$ from (1.1), with its full stationary law (1.3). Theorem 10.2 supplies its exact amplitude pair, changing the sign of $p$ if necessary to obtain $P=p/\sqrt n$ monic, and taking $S=s/\sqrt n$. That pair has $e=0$. General data in (15.1) instead specify their own exact law $\widehat\gamma$; comparison to the reference law is a further conclusion under a scalar envelope below.

**Theorem 15.2 (Completion does not require the residual to vanish).** Every pair in Definition 15.1 and every $0<q<1$ yield a homogeneous complete real instrument on the full algebra $M_D(\mathbb C)$ whose exact actual gap law is $\widehat\gamma$. Its zero branch has Choi rank exactly two and its tick branch has one nonzero rank-one Kraus matrix. Every positive-probability tick resets to the same pure density. The observability Gramian is faithful and the zero-word reachable span is all of $\mathbb C^D$.

Proof. Use the Newton lift (11.1) with

$$
p=\sqrt n P,\quad s=\sqrt n S,\quad
u_j=\Delta^{j+1}s(0),\quad v_j=\Delta^jp(0),\quad
u_m=0,\quad v_m=m!\sqrt n\ne0.
\tag{15.2}
$$

Thus $A,B,x,f,F$ have exactly the block definitions of (11.1), and the raw map is $\mathcal T_q(X)=q(AXA^{\mathsf T}+BXB^{\mathsf T})$. This uses the Newton algebra in the proof of Theorem 11.2, without importing that theorem's monomial-intensity conclusion. In detail, finite differences give $e_0^{\mathsf T}U^tv=p(t)$ and $e_0^{\mathsf T}U^tu=\Delta s(t)$. The block powers and anchor give

$$
f^{\mathsf T}A^kx=s(k),\qquad
f^{\mathsf T}A^tBA^rx=p(t),\qquad BA^rB=0.
\tag{15.3}
$$

Among words of length $k$, the all-$A$ word contributes $s(k)^2$, the $k$ one-$B$ words contribute $\sum_{t<k}p(t)^2$, and every word containing at least two $B$ factors vanishes. Hence the actual raw intensity is

$$
\operatorname{Tr}[F\mathcal T_q^k(xx^{\mathsf T})]
=q^k\left(s(k)^2+\sum_{t<k}p(t)^2\right)=q^kH(k).
\tag{15.4}
$$

This includes the empty word at $k=0$, with zero detector amplitude. As before, $A$ is upper triangular with unit diagonal and $B$ is upper triangular with zero diagonal. Thus the full complex superoperator matrix $q(A\otimes A+B\otimes B)$ has spectrum $\{q\}$ and is stable. Set $Q=\sum_{k\ge0}(\mathcal T_q^*)^k(F)$.

The faithfulness and reachability arguments of Theorem 11.2 require only $p_m\ne0$, not the polynomial identity (10.10). To check their exact premises, if $y=(y_T,y_s)$ has $y^*Qy=0$, every word detector amplitude vanishes. The rows $f^{\mathsf T}A^tB=p(t)e_{m+1}^{\mathsf T}$ for $0\le t\le m$ force $y_s=0$. The rows $e_0^{\mathsf T}U^j$ for $0\le j\le m$ then force $y_T=0$, since their binomial coefficient matrix has determinant one. This works for complex vectors and proves $Q>0$ on the full memory. Likewise $v_m\ne0$ makes $v,Nv,\ldots,N^mv$ a basis of the target; the invertible binomial change of basis makes $A^jBx=(U^jv,0)$, $0\le j\le m$, span that target. Including $x$ gives all $D$ dimensions.

Now apply Theorem 2.1 with raw matrices $\sqrt qA,\sqrt qB$, detector $f$, reset $x$, and its actual normalization

$$
z=x^{\mathsf T}Qx=Z_H(q),\qquad G=Q^{1/2},\qquad
\xi=Gx/\sqrt{Z_H(q)},\qquad \tau=\xi\xi^{\mathsf T}.
\tag{15.5}
$$

All its hypotheses have been established. Its completed matrices and branches are

$$
\begin{aligned}
L_A&=\sqrt q\,GAG^{-1},&L_B&=\sqrt q\,GBG^{-1},&J&=\xi f^{\mathsf T}G^{-1},\\
\Phi(X)&=L_AXL_A^{\mathsf T}+L_BXL_B^{\mathsf T},&&
\Psi(X)=JXJ^{\mathsf T},\\
L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J&=I_D,&
\rho(\Phi)&=q,&\Psi\Phi^k(\tau)&=\widehat\gamma_k\tau.
\end{aligned} \tag{15.6}
$$

Theorem 2.1 supplies real matrices, full complex complete positivity, trace completeness and the actual pure reset. Invertible $A$ and nonzero rank-one nilpotent $B$ are linearly independent over $\mathbb C$; similarity and nonzero scaling preserve this independence. Thus the zero Choi rank is exactly two. Both factors of $J$ are nonzero, so its matrix rank and the tick Choi rank are one. For every raw word $w$, $L_w\xi=q^{|w|/2}Gwx/\sqrt{Z_H(q)}$, so the completed reachable span is also full.

Exactly the target and source coordinates of (11.1) are used. The two zero Kraus contributions are summed inside $\Phi$; their labels do not survive. All matrices are fixed in time. There is no additional quantum or classical register, retained clock, correlated external input or controller. This proves the resource contract for the actual law in (15.1), regardless of whether $e$ vanishes. $\square$

**Theorem 15.3 (Stationary completion and a parameter-uniform finite-window bound).** For the instrument of Theorem 15.2, put

$$
\widehat S_a=\sum_{k\ge a}\widehat\gamma_k,\qquad
\widehat\mu=\sum_{k\ge0}(k+1)\widehat\gamma_k,\qquad
\widehat\rho=\frac1{\widehat\mu}\sum_{a\ge0}\Phi^a(\tau).
\tag{15.7}
$$

Then $\widehat\rho$ is a real faithful mixed invariant density, distinct from $\tau$. Every actual stationary cylinder is

$$
\begin{aligned}
\mathsf P_H(0^a1\,0^{g_1}1\cdots0^{g_r}1\,0^b)
&=\frac{\widehat S_a\widehat S_b}{\widehat\mu}
\prod_{i=1}^r\widehat\gamma_{g_i}\quad(r\ge0),\\
\mathsf P_H(0^W)&=\frac1{\widehat\mu}
\sum_{k\ge W}(k-W+1)\widehat\gamma_k\quad(W\ge0).
\end{aligned} \tag{15.8}
$$

There is no extra all-zero stationary component. Suppose in addition that explicit constants $0<\ell\le u$ satisfy

$$
\ell\le r(k):=\frac{H(k)}{k^n}\le u\quad(k\ge1),\qquad
c_{\ell,u}=\frac{\sqrt u-\sqrt\ell}{\sqrt u+\sqrt\ell}.
\tag{15.9}
$$

Let $\mathsf P_{H,W}$ and $\mathsf P_{n,W}$ be the probability distributions on $\{0,1\}^W$ for this actual stationary instrument and the exact reference (1.3), respectively. Total variation means half the $\ell^1$ distance. Uniformly over $0<q<1$,

$$
\begin{aligned}
d_{\rm TV}(\widehat\gamma,\gamma)&\le c_{\ell,u},\\
d_{\rm TV}(\widehat\lambda,\lambda)&\le c_{\ell,u},\qquad
d_{\rm TV}(\widehat\alpha,\alpha)\le c_{\ell,u},\\
d_{\rm TV}(\mathsf P_{H,W},\mathsf P_{n,W})
&\le 1-(1-c_{\ell,u})^{\lceil W/2\rceil}
\le\min\{1,\lceil W/2\rceil c_{\ell,u}\}\quad(W\ge0).
\end{aligned} \tag{15.10}
$$

Here $\lambda$ and $\widehat\lambda$ are the stationary interval-and-position distributions, and $\alpha,\widehat\alpha$ their initial forward-wait marginals, defined explicitly by

$$
\lambda(k,a)=\frac{\gamma_k}{\mu},\qquad
\widehat\lambda(k,a)=\frac{\widehat\gamma_k}{\widehat\mu}
\quad(k\ge1,\ 0\le a\le k),\qquad
\alpha_a=\frac{S_a}{\mu},\quad
\widehat\alpha_a=\frac{\widehat S_a}{\widehat\mu}.
\tag{15.11}
$$

In particular the length-biased interval marginals $(k+1)\gamma_k/\mu$ and $(k+1)\widehat\gamma_k/\widehat\mu$ also have total variation at most $c_{\ell,u}$. Every binary word, including an all-zero or empty word, has probability error bounded by the last line of (15.10).

Proof. First extend the stationary supplier to its actual finite-mean law. Theorem 5.1 assumes (1.1), so it is not invoked unchanged for $\widehat\gamma$. Instead use its summation mechanism with the hypotheses just proved. By completeness, the survival traces satisfy
$\operatorname{Tr}\Phi^a(\tau)-\operatorname{Tr}\Phi^{a+1}(\tau)=\widehat\gamma_a$; stability makes the traces tend to zero. Hence $\operatorname{Tr}\Phi^a(\tau)=\widehat S_a$. The norm-convergent positive series $R=\sum_{a\ge0}\Phi^a(\tau)$ therefore obeys

$$
\operatorname{Tr}R=\sum_{a\ge0}\widehat S_a=\widehat\mu<\infty,
\qquad \Phi(R)=R-\tau,\qquad \Psi(R)=\tau.
\tag{15.12}
$$

Tonelli justifies the trace identity and the finite mean follows from (15.1). Normalizing gives invariance. The Kraus-word expansion $y^*Ry=\sum_w|y^*L_w\xi|^2$, together with full reachability, proves $R>0$ for every nonzero complex $y$. All terms are real symmetric. Thus $\widehat\rho$ is faithful and mixed, and cannot equal the pure $\tau$.

The first tick after $a$ visible zeros has unnormalized state
$\Psi\Phi^a(\widehat\rho)=\widehat S_a\tau/\widehat\mu$.
Each subsequent completed gap and tick multiplies by $\widehat\gamma_{g_i}$ and resets to $\tau$; the final zero run contributes $\widehat S_b$. This proves the first line of (15.8). Applying $\Phi^W$ to the defining stationary series proves its second line. At $W=0$ the result is one. Trace completeness and invariance give right and left consistency, so these are a stationary process's actual cylinders. Moreover
$\mathsf P_H(0^W)\le\widehat\mu^{-1}\sum_{k\ge W}(k+1)\widehat\gamma_k\to0$, excluding an all-zero component. The tick rates at $\tau$ and $\widehat\rho$ are respectively zero and $1/\widehat\mu$.

For the comparison, the following elementary change-of-density estimate is used inside the proof. If a probability measure $\pi$ is tilted by a scalar $r\in[\ell,u]$, with $a=\mathbb E_\pi r$, then for $\ell<u$ the chord bound for $|r-a|$ gives

$$
\begin{aligned}
d_{\rm TV}\left(\frac{r\pi}{a},\pi\right)
&=\frac{\mathbb E_\pi|r-a|}{2a}
\le\frac{(u-a)(a-\ell)}{a(u-\ell)}\\
&=\frac{u+\ell-a-u\ell/a}{u-\ell}
\le\frac{u+\ell-2\sqrt{u\ell}}{u-\ell}
=c_{\ell,u}.
\end{aligned} \tag{15.13}
$$

The penultimate inequality is $a+u\ell/a\ge2\sqrt{u\ell}$. If $\ell=u$, the tilt is constant and the distance is zero. The gap law is precisely such a tilt of $\gamma$, with mean $a=Z_H/Z_n$.

The stationary initialization requires a different normalization. Its interval-position law in (15.11) is normalized because $\sum_k(k+1)\gamma_k=\mu$. Writing $M_H=\sum_{k\ge1}(k+1)H(k)q^k$ and $M_n=\sum_{k\ge1}(k+1)k^nq^k$ gives

$$
\lambda(k,a)=\frac{k^nq^k}{M_n},\qquad
\widehat\lambda(k,a)=\frac{H(k)q^k}{M_H}
=\frac{r(k)}{\mathbb E_\lambda r(K)}\lambda(k,a).
\tag{15.14}
$$

Thus the same bound (15.13) applies to the joint length-biased law, with no assumption that $\widehat\mu=\mu$. Its projections to $K$ and to the remaining wait $a$ cannot increase total variation; summing over $k\ge a$ gives exactly (15.11). This establishes both initialization bounds in (15.10), including length bias and all tail contributions.

To pass to a whole window, the actual cylinder formula has the following scalar sampling representation: draw an initial wait $A$ with law $\alpha$, place $A$ zeros before the first one, and then draw independent gaps with law $\gamma$ after each one. The corresponding hatted representation has exactly (15.8). This is a representation of output probabilities; the instrument itself remains (15.6).

For $W\ge1$, at most $B_W=\lceil W/2\rceil$ draws are needed: one initial wait and at most $B_W-1$ subsequent gaps. Indeed every post-tick gap has at least one zero. A gap draw can affect the window only after a tick in a position at most $W-2$; after a tick at position $W-1$ the remaining symbol is forced to be zero. Such draw-triggering ticks are separated by at least two positions and number at most $\lceil(W-2)/2\rceil=B_W-1$ (zero for $W=1,2$). One can therefore pre-draw $B_W-1$ independent gaps and use a deterministic truncation map to the length-$W$ word.

For two countable distributions, match their common masses $\min\{p_i,p'_i\}$ first and couple the remaining masses arbitrarily. This gives a coupling with equality probability $1-d_{\rm TV}$. Apply it to the initial waits and independently to each of those gap pairs. Every pair agrees with probability at least $1-c_{\ell,u}$; consequently all needed draws agree with probability at least $(1-c_{\ell,u})^{B_W}$. Equal draws produce equal words. For any event, the difference of its two probabilities is at most the disagreement probability, which proves (15.10). The empty window is deterministic and has distance zero, as the same formula with exponent zero states. These couplings are a proof of a classical distribution bound, not retained registers, shared physical input, or a proposed simulation controller.

The maximal-coupling and equilibrium-renewal ingredients are classical; see H. Thorisson, *Coupling, Stationarity, and Regeneration*, Springer (2000), [doi:10.1007/978-1-4612-1236-2](https://doi.org/10.1007/978-1-4612-1236-2). The calculations above supply their full specialization, including the two distinct normalizers and the window draw count, for the actual completed instrument. Under (15.9), $\widehat\gamma_0=0$ and every $\widehat\gamma_k$ for $k\ge1$ is positive. Formula (15.8) then gives exactly the no-adjacent-ones visible support, including positive boundary tails. $\square$

**Theorem 15.4 (Two finite coefficient certificates for the scalar envelope).** For the residual coefficients in (15.1), define

$$
\epsilon_{\rm sum}=n\sum_{j=0}^{n-2}\frac{|E_j|}{j+1},\qquad
\epsilon_{\rm bin}=n\max_{0\le j\le n-2}
\frac{|E_j|}{\binom{n-1}{j}},\qquad
\epsilon=\min\{\epsilon_{\rm sum},\epsilon_{\rm bin}\}.
\tag{15.15}
$$

Then, for every integer $k\ge1$,

$$
\left|\frac{H(k)}{k^n}-1\right|\le\frac{\epsilon}{k}.
\tag{15.16}
$$

In particular $\epsilon<1$ certifies (15.9) with $\ell=1-\epsilon$, $u=1+\epsilon$. If every $E_j\ge0$, it instead certifies $\ell=1$, $u=1+\epsilon$, without requiring $\epsilon<1$. These certificates require only finitely many exact coefficient operations; rational $P,S$ give rational certificates.

Proof. For nonnegative integers $t$, the monomial $t^0$ means one, including at zero. Since $x^j$ is nondecreasing on $[0,\infty)$,

$$
\sum_{t=0}^{k-1}t^j\le\int_0^k x^j\,dx
=\frac{k^{j+1}}{j+1}.
\tag{15.17}
$$

Consequently $n|\sum_{t<k}e(t)|/k^n$ is at most
$n\sum_j|E_j|k^{j+1-n}/(j+1)\le\epsilon_{\rm sum}/k$, because $j\le n-2$ and $k\ge1$. For the other bound put $b=\max_j|E_j|/\binom{n-1}{j}$. The binomial theorem gives, for every integer $t\ge0$,

$$
|e(t)|\le b\sum_{j=0}^{n-2}\binom{n-1}{j}t^j
=b\big((t+1)^{n-1}-t^{n-1}\big).
\tag{15.18}
$$

Summing telescopes to $bk^{n-1}$, and multiplication by $n/k^n$ gives $\epsilon_{\rm bin}/k$. Taking the better bound proves (15.16). Nonnegative coefficients give $e(t)\ge0$ at the integers used in (15.1), yielding the single-sided envelope. In the symmetric case the per-draw constant also satisfies the convenient estimate

$$
c_{1-\epsilon,1+\epsilon}
=\frac{\epsilon}{1+\sqrt{1-\epsilon^2}}\le\epsilon
\quad(0\le\epsilon<1).
\tag{15.19}
$$

The theorem certifies a scalar law and then uses Theorems 15.2–15.3 to obtain actual stationary-output estimates. It is not an estimate for raw matrices substituted for a probability bound. $\square$

**Theorem 15.5 (The rational ninth-degree center and every certified iterate are actual-output consumers).** For the center $c$ of (12.3), use $P=P_c,S=S_c$ from (12.1) and the actual instrument of Theorem 15.2. Define the exact rational number

$$
\delta_9=\frac{2749658638697}{10^{24}}.
\tag{15.20}
$$

For every integer $k\ge1$,

$$
1\le\frac{H_c(k)}{k^9}\le1+\frac{\delta_9}{k}\le1+\delta_9.
\tag{15.21}
$$

The constant endpoints $1$ and $1+\delta_9$ are optimal for this center over all positive integers: the lower endpoint is an infimum and the upper endpoint is attained at $k=1$. For all $0<q<1$ the center therefore produces a real complete $D=6$ instrument with the full resource contract, its own exact gap law $H_c(k)q^k/Z_{H_c}(q)$ and a faithful actual stationary initialization. Its stationary finite-window error is bounded by

$$
\begin{aligned}
c_9&=\frac{\sqrt{1+\delta_9}-1}{\sqrt{1+\delta_9}+1}
=\frac{\delta_9}{(\sqrt{1+\delta_9}+1)^2}
<\frac{2749658638697}{4\cdot10^{24}},\\
d_{\rm TV}(\mathsf P_{H_c,W},\mathsf P_{9,W})
&\le1-(1-c_9)^{B_W}
\le1-\left(1-\frac{2749658638697}{4\cdot10^{24}}\right)^{B_W}\\
&\le\min\left\{1,\frac{2749658638697 B_W}{4\cdot10^{24}}\right\},
\qquad B_W=\lceil W/2\rceil.
\end{aligned} \tag{15.22}
$$

These are exact rational upper certificates as well as an exact radical bound. The same $c_9$ controls the gap, stationary length-biased interval, and initial-wait distances in (15.10). The center's actual law is distinct from the exact monomial law for every $0<q<1$.

For the rational iterates $\theta^{(N)}$ of Theorem 12.3, retain its coefficient bound $\varepsilon_N=\bar\alpha L^N/(1-L)$ and set

$$
a_N=612\varepsilon_N
=\frac{612\cdot398}{10^{15}(1-343/10^8)}
\left(\frac{343}{10^8}\right)^N
<\frac{2448}{10^{13}}\left(\frac{343}{10^8}\right)^N<1.
\tag{15.23}
$$

Each finite iterate is a valid input to Theorem 15.2 and satisfies

$$
\begin{aligned}
\left|\frac{H_N(k)}{k^9}-1\right|&\le\frac{a_N}{k}\quad(k\ge1),\\
d_{\rm TV}(\mathsf P_{H_N,W},\mathsf P_{9,W})
&\le1-\left(1-\frac{a_N}{1+\sqrt{1-a_N^2}}\right)^{B_W}
\le\min\{1,612B_W\varepsilon_N\}.
\end{aligned} \tag{15.24}
$$

Thus for any fixed finite $W$ and rational tolerance $\eta>0$, choosing the first $N\ge0$ with $612B_W\varepsilon_N\le\eta$ gives a terminating rational selection rule for an actual stationary window within $\eta$, simultaneously for every $0<q<1$. The empty window already has error zero.

Proof. The coefficient formula (12.2) evaluated at the eight rational center entries gives (12.7). All eight displayed numerators $R_j$ there are strictly positive. The two certificates (15.15) evaluate exactly to

$$
\epsilon_{\rm sum}(c)
=\frac{7075065748837739}{7\cdot10^{25}},\qquad
\epsilon_{\rm bin}(c)
=\frac1{10^{24}}\max_{0\le j\le7}\frac{R_j}{\binom8j}
=\delta_9.
\tag{15.25}
$$

For a fully integer comparison proving the last maximum, the nonnegative slack vector is

$$
\left(\binom8jR_0-R_j\right)_{j=0}^7
=\begin{pmatrix}
0\\4653282943432\\13180104272276\\65933817303646\\63041168361224\\81584870440966\\26754975839288\\12082450500424
\end{pmatrix}.
\tag{15.26}
$$

The first expression of (15.25) is the rational sum $10^{-24}\sum_{j=0}^7R_j/(j+1)$; it exceeds $\delta_9$ since all terms are positive and its first term is already $\delta_9$. Theorem 15.4 proves (15.21). At $k=1$, (15.1) gives $H_c(1)=1+9E_0(c)=1+\delta_9$. As $k\to\infty$, (15.16) gives $H_c(k)/k^9\to1$. These prove the two optimal endpoints. Theorem 15.3 now gives (15.22); the rational bound follows from $(\sqrt{1+\delta_9}+1)^2>4$ and the union bound. A normalized monomial gap law would require $H_c(k)/k^9$ to be constant for all $k\ge1$, because every $q^k$ is positive. Its different value at one and limiting value at infinity exclude this.

For completeness the iterate transfer uses the entire box, not a statement that a finite iterate solves the polynomial identity. Throughout $\mathcal B_9$ all eight free coefficients have absolute value less than two; the fixed leading coefficient of $P$ is one. The Jacobian formula (12.4) therefore gives, for $0\le j\le7$,

$$
\sum_{i=1}^8\left|\frac{\partial E_j}{\partial\theta_i}(\theta)\right|
\le68\binom8j\quad(\theta\in\mathcal B_9).
\tag{15.27}
$$

Indeed the four $a$ columns contribute at most four when $j=0$ and at most sixteen otherwise, always at most $4\binom8j$. The four $b$ columns contain at most sixteen summands in total, each bounded by $4\binom8j$: for $r,s\in\{1,2,3,4\}$ with $r+s>j$, one has $\binom{r+s}{j}\le\binom8j$. Their total is at most $64\binom8j$. Integrating the derivative along the segment from $\theta_*$ to $\theta^{(N)}$, which stays in the convex box, and using $E(\theta_*)=0$ gives
$|E_j(\theta^{(N)})|\le68\binom8j\varepsilon_N$.
Thus $\epsilon_{\rm bin}(\theta^{(N)})\le9\cdot68\varepsilon_N=a_N$. Equations (15.16), (15.19) and (15.10) prove (15.24), and $L<1$ proves termination of the selection rule.

The monic and anchored conditions are exact for the center, for every iterate, and for the limiting root. Their scaled Newton data have $p=3P$, $s=3S$, $u_4=0$, $v_4=72$, so the structural completion of Theorem 15.2 applies at each finite stage. At the limiting root, Theorem 12.3 gives $e=0$ and Theorems 11.2–11.5 supply the already established exact monomial instrument. At a finite stage only its explicitly computed residual determines whether the law is exact; neither coefficient convergence nor (15.24) asserts finite-stage residual vanishing. $\square$

**Definition 15.6 (Scope of the output consequence).** Theorem 11.5 remains the exact all-degree existence supplier; Theorem 12.3 remains the rational ninth-degree coefficient supplier. The new consequence is the composition (15.1), (15.6), (15.8) and (15.10): a residual-controlled scalar law is produced by an actual complete instrument and compared after its own stationary initialization. The stationary-output sensitivity left unbounded after (12.18) is addressed here through this scalar identity. Estimates for inverses and square roots of Gramians remain separate questions; no uniform Gramian conditioning is assumed or concluded.

The bounds concern each finite classical output window, with its stated dependence on $W$. They do not assert total-variation closeness of probability measures on infinite streams. They give no operator-, diamond-, state- or Kraus-distance estimate, no physical finite-precision implementation, and no preparation or control-cost bound. The coupling variables occur only in a comparison proof and do not change the instrument's memory accounting. The complete instrument uses exact matrix entries even when its input coefficients are rational; its Gramian and square root need not have rational entries. No bit-complexity or unconditional dimension-minimum conclusion follows. The results are ordinary paper mathematics, not a claim of Lean verification.

The residual-to-output construction and the specified coefficient consumers are repository derivations using the prior Newton lift, faithful Gramian completion and anchored existence results, the cited classical renewal/coupling principles, and the fixed-point coefficient supplier of Section 12. No worldwide novelty claim is made.

## 追加锚（本行以下为增补区）

## 16. Nonnegative anchored squares, exact delay and general real renewal instruments

**Definition 16.1 (Polynomial data and anchored pairs).** Let $d\in\mathbb R[t]$ be nonzero and globally nonnegative, of exact degree $2m$, where $m\ge0$, and write $\delta=[t^{2m}]d>0$. Put $\Delta v(t)=v(t+1)-v(t)$ and $\operatorname{fall}_j(t)=\prod_{i=0}^{j-1}(t-i)$, with $\operatorname{fall}_0=1$. A degree-bounded anchored pair for $d$ is a pair of real polynomials $p,s$ satisfying

$$
\deg p,\deg s\le m,\qquad s(0)=0,\qquad d=p^2+\Delta(s^2).
\tag{16.1}
$$

The zero polynomial is permitted in a degree bound. Positive orientation means $[t^m]p=\sqrt\delta$. Define the discrete integral polynomial by

$$
P(t)=\sum_{j=0}^{2m}\Delta^j d(0)\binom{t}{j+1},\qquad
\binom{t}{j}=\frac{\operatorname{fall}_j(t)}{j!}.
\tag{16.2}
$$

Throughout this section, a gap index is the number of zeros between successive ticks; the corresponding interevent duration is one larger. Adjoints are denoted by $\dagger$, and the star on a CP map denotes its trace dual. Real matrices act on the full complex matrix algebra, as in Definition 1.2.

**Theorem 16.2 (Closure at real roots, with constants and the zero boundary).** Every $d$ of Definition 16.1 has a positively oriented anchored pair. For every degree-bounded anchored pair,

$$
\begin{aligned}
\deg p&=m,\qquad ([t^m]p)^2=\delta,\\
\Delta P&=d,\qquad P(0)=0,\qquad
\deg P=2m+1,\qquad [t^{2m+1}]P=\frac{\delta}{2m+1},\\
P(k)&=s(k)^2+\sum_{j=0}^{k-1}p(j)^2
=\sum_{j=0}^{k-1}d(j)\quad(k\ge0).
\end{aligned}
\tag{16.3}
$$

The identity at $k$ is for every nonnegative integer $k$. Here $P$ is the unique polynomial with the displayed difference and anchor. For a positive constant $d=c$, the degree-bounded pairs are exactly $(\sqrt c,0)$ and $(-\sqrt c,0)$; positive orientation selects the first. For $d=0$, the only polynomial pair with $s(0)=0$ and $p^2+\Delta(s^2)=0$, even without a prescribed degree bound, is $(0,0)$.

Proof. The polynomials $\binom{t}{j}$ form a basis in each finite degree, since their leading coefficients are $1/j!$. The identity $\Delta\binom{t}{j+1}=\binom{t}{j}$ follows by subtracting the falling-factorial products, or by the binomial identity on infinitely many nonnegative integers. Successive differences at zero therefore recover the Newton coefficients: $d(t)=\sum_{j=0}^{2m}\Delta^j d(0)\binom{t}{j}$. This proves $\Delta P=d$ and $P(0)=0$. A nonconstant polynomial of degree $r$ and leading coefficient $a$ has forward difference of degree $r-1$ and leading coefficient $ra$; hence a polynomial with zero difference is constant. This proves uniqueness and the exact degree and leading coefficient in (16.3). Telescoping identifies its integer values with the sum of $d(j)$, which is nonnegative and nondecreasing in $k$.

For $m\ge1$, set $d_n=d+1/n$ for integers $n\ge1$. It is strictly positive on the entire real line, has degree $2m$ and retains leading coefficient $\delta$. Theorem 10.1 supplies real pairs $p_n,s_n$ of degrees at most $m$, with $s_n(0)=0$ and $d_n=p_n^2+\Delta(s_n^2)$. Replacing $p_n$ by its negative when necessary makes its leading coefficient exactly $\sqrt\delta$. Summation gives the exact nonnegative identity

$$
P(k)+\frac{k}{n}=s_n(k)^2+\sum_{j=0}^{k-1}p_n(j)^2\qquad(k\ge0).
\tag{16.4}
$$

Let $M=\sqrt{P(m+1)+m+1}$. Taking $k=m+1$ bounds every $|p_n(j)|$ for $0\le j\le m$ by $M$. Taking $k=j$ and using $P(j)\le P(m+1)$ bounds every $|s_n(j)|$ at the same nodes by $M$. These bounds are simultaneous in $n$ and in the two polynomials. Explicitly, the fixed Lagrange polynomials

$$
\ell_j(t)=\prod_{\substack{0\le i\le m\\i\ne j}}\frac{t-i}{j-i}
\quad(0\le j\le m)
\tag{16.5}
$$

satisfy $v(t)=\sum_{j=0}^m v(j)\ell_j(t)$ for every polynomial of degree at most $m$. Thus each coefficient of either $p_n$ or $s_n$ has absolute value at most $M\sum_{j=0}^m|[t^r]\ell_j|$. The combined coefficient sequence lies in a bounded subset of $\mathbb R^{2m+2}$. Finite-dimensional compactness gives one subsequence along which both polynomials converge coefficientwise, to $p,s$.

Polynomial multiplication, translation and coefficient extraction are continuous in these finite-dimensional spaces. Passing along that common subsequence gives $d=p^2+\Delta(s^2)$, $s(0)=0$, $\deg s\le m$ and $[t^m]p=\sqrt\delta$. In particular $\deg p=m$. For any other degree-bounded pair, $\Delta(s^2)$ has degree at most $2m-1$ when nonzero, so comparison of degree $2m$ forces the same squared leading coefficient. Telescoping (16.1) proves the remaining identity in (16.3).

For $m=0$, the anchor forces the constant $s$ to vanish, and $p^2=c$ gives exactly the two stated pairs; (16.2) is $P(t)=ct$. For $d=0$ and arbitrary polynomial degrees, telescoping gives $0=s(k)^2+\sum_{j<k}p(j)^2$ for every $k\ge0$. Every summand is nonnegative, so $s$ and $p$ each vanish at every nonnegative integer and are zero polynomials.

No separation of the real zeros of $d$ was used, so repeated real zeros are included. This compactness proof supplies existence, not a continuous selection of pairs, uniqueness for general $d$, or convergence of a coefficient algorithm. The input Theorem 10.1 uses the scalar ingredient of [Ephremidze, *An Elementary Proof of the Polynomial Matrix Spectral Factorization Theorem*, arXiv:1011.3777v1, Theorem 2](https://arxiv.org/pdf/1011.3777v1): a polynomial matrix positive definite almost everywhere on the real line admits a polynomial factor nonsingular in the open upper half-plane, unique up to a constant right unitary multiplier. That result supplies neither the telescoping anchor nor a continuously chosen anchored pair at real roots. The argument here takes limits of the already anchored strictly positive pairs instead. $\square$

**Theorem 16.3 (Exact delay, every-pair divisibility and maximal-delay rigidity).** For $d$ as above define

$$
h=1+\min\{j\in\mathbb Z_{\ge0}:d(j)>0\}.
\tag{16.6}
$$

This minimum exists, $1\le h\le m+1$, and $P(k)=0$ exactly for $0\le k<h$, while $P(k)>0$ for every integer $k\ge h$. For each integer $h$ in that range the exact classification is

$$
d(t)=\operatorname{fall}_{h-1}(t)^2r(t),\qquad
r\ge0\text{ on }\mathbb R,\qquad
\deg r=2(m-h+1),\qquad r(h-1)>0.
\tag{16.7}
$$

Every allowed $h$ occurs at every fixed $m$. Every polynomial pair satisfying $s(0)=0$ and $d=p^2+\Delta(s^2)$, even without a degree bound, obeys

$$
\operatorname{fall}_{h-1}\mid p,\qquad
\operatorname{fall}_h\mid s.
\tag{16.8}
$$

In particular $h=m+1$ if and only if $d=c\operatorname{fall}_m^2$ for some $c>0$. In that case every degree-bounded anchored pair is $s=0$, $p=\pm\sqrt c\operatorname{fall}_m$.

Proof. At a real zero $a$ write $d(t)=(t-a)^er(t)$ with $r(a)\ne0$. Continuity makes the sign of $r$ constant close to $a$. If $e$ were odd, the two sides of $a$ would give opposite signs for $d$, contrary to global nonnegativity. Thus each real zero has even multiplicity. A nonzero degree-$2m$ polynomial has at most $m$ distinct real zeros. Among the $m+1$ integers $0,\ldots,m$, some value of $d$ is therefore positive, proving existence and the bound on $h$. The sums in (16.3) are zero before $h$ and thereafter contain the strictly positive term $d(h-1)$; later zero values of $d$ cannot make $P$ zero again.

The prescribed zeros $0,\ldots,h-2$ each have multiplicity at least two, so their squared product divides $d$. Its quotient has the degree in (16.7); it is nonnegative away from those finitely many roots because the divisor is positive there, and nonnegative at the roots by continuity. Moreover $\operatorname{fall}_{h-1}(h-1)=(h-1)!\ne0$, so $d(h-1)>0$ is equivalent to $r(h-1)>0$. Conversely (16.7) makes the first $h-1$ values of $d$ zero and the next positive, proving the classification. For each $h\in\{1,\ldots,m+1\}$ the explicit example

$$
d(t)=\operatorname{fall}_{h-1}(t)^2
\big(1+(t-h+1)^2\big)^{m-h+1}
\tag{16.9}
$$

has degree $2m$, is globally nonnegative and satisfies exactly that classification.

For any polynomial pair with the stated identity and anchor, telescoping gives $P(k)=s(k)^2+\sum_{j<k}p(j)^2$ without any degree assumption. Thus $P(k)=0$ for $0\le k<h$ forces $s(k)=0$ at all those points. At $k=h-1$, the same identity forces $p(j)=0$ for $0\le j<h-1$; when $h=1$ this is an empty list. Division by these distinct linear factors proves (16.8), including the case $s=0$. At $h=m+1$ the quotient $r$ in (16.7) is a positive constant $c$. For a degree-bounded pair, $s$, of degree at most $m$, has the $m+1$ distinct zeros $0,\ldots,m$, so $s=0$. Now $p^2=c\operatorname{fall}_m^2$ implies $(p-\sqrt c\operatorname{fall}_m)(p+\sqrt c\operatorname{fall}_m)=0$; the polynomial ring has no zero divisors, giving the two signs. Conversely this $d$ has precisely the stated first positive integer value. These arguments include $m=0,h=1$. $\square$

**Theorem 16.4 (Sharp positive-delay tradeoff for seed and detector ranks).** Let $H$ have finite complex dimension $D\ge0$, let $\mathcal T(X)=\sum_iK_iXK_i^\dagger$ have a finite, possibly empty Kraus family, and let $\tau,F\ge0$ have ranks $a,b$. Put $w_k=\operatorname{Tr}[F\mathcal T^k(\tau)]$. Suppose a first positive weight exists at an index $h\ge1$. Then

$$
a,b\ge1,\qquad D\ge a+b,\qquad
h\le D-a-b+1.
\tag{16.10}
$$

This bound is sharp for raw CP detection for every $a,b,h\ge1$, in dimension $D=a+b+h-1$. It requires no normalization, trace contraction, completeness, stability or commutation. Its positive-delay hypothesis cannot be dropped.

Proof. Let $U=\operatorname{ran}\tau$ and $H_n=\operatorname{span}\{K_wU:|w|\le n\}$. The empty word is included. As in Section 13,

$$
H_0=U,\qquad H_{n+1}=H_n+\sum_iK_iH_n,\qquad
\operatorname{ran}\Big(\sum_{k=0}^n\mathcal T^k(\tau)\Big)=H_n.
\tag{16.11}
$$

For completeness, $\operatorname{ran}(MM^\dagger)=\operatorname{ran}M$ follows by taking orthogonal complements of $\ker(MM^\dagger)=\ker M^\dagger$. Use this with $M=K_w\tau^{1/2}$. The kernel of a finite sum of positive matrices is the intersection of their kernels, because its zero quadratic form forces each nonnegative quadratic form to be zero. The range of the sum is consequently the span of the ranges, proving the last equality in (16.11). Finally $\operatorname{Tr}(FX)=\|F^{1/2}X^{1/2}\|_{\rm HS}^2$ for $X\ge0$, so a zero trace is equivalent to $F$ annihilating $\operatorname{ran}X$.

The zero weights through $h-1$ give $H_{h-1}\subseteq\ker F$. If $H_{n+1}=H_n$ for any $0\le n<h-1$, every $K_i$ preserves $H_n$, hence every later reachable vector lies in $H_n\subseteq\ker F$. That would force $w_h=0$. Thus all $h-1$ successive inclusions from $H_0$ to $H_{h-1}$ are strict; for $h=1$ there are none. Therefore

$$
a+h-1\le\dim H_{h-1}\le D-b,
\tag{16.12}
$$

which proves the bound. Nontrivial detection forces $a,b>0$, and $U\subseteq\ker F$ already gives $a+b\le D$.

To attain equality, choose an orthonormal basis consisting of a chain $e_0,\ldots,e_h$, seed spectators $u_1,\ldots,u_{a-1}$ and detector spectators $v_1,\ldots,v_{b-1}$. All three sets are mutually orthogonal. Set

$$
\begin{aligned}
Ke_j&=e_{j+1}\quad(0\le j<h),&Ke_h&=0,&Ku_i&=Kv_i=0,\\
\tau&=e_0e_0^\dagger+\sum_{i=1}^{a-1}u_iu_i^\dagger,
&F&=e_he_h^\dagger+\sum_{i=1}^{b-1}v_iv_i^\dagger,
&\mathcal T(X)&=KXK^\dagger.
\end{aligned}
\tag{16.13}
$$

The space has dimension $(h+1)+(a-1)+(b-1)=a+b+h-1$, and the two projections have ranks $a,b$. At time zero their ranges are disjoint. For $1\le k\le h$, $K^k\tau(K^\dagger)^k=e_ke_k^\dagger$; for $k>h$ it is zero. Hence $w_h=1$ and every other $w_k=0$. This proves raw CP sharpness. It is not a normalized seed when $a>1$, and an effect and a raw zero map do not specify a complete binary instrument. Indeed here

$$
K^\dagger K+F=I-\sum_{i=1}^{a-1}u_iu_i^\dagger.
\tag{16.14}
$$

Thus for $a>1$ even the necessary completeness identity with this fixed detector effect fails. No claim of complete-instrument sharpness for arbitrary ranks is part of this example.

If $\tau=0$, $F=0$ or $D=0$, every weight vanishes and $h$ is undefined. An empty Kraus family gives zero weights for $k\ge1$, so cannot have positive delay. If either seed or detector has full rank and the other is nonzero, $w_0>0$, since a positive definite operator has strictly positive trace pairing with a nonzero positive operator. Finally $\tau=F=I_2$ has $h=0$ for any Kraus family, whereas the proposed right side of (16.10) would be $2-2-2+1=-1$. This explicitly excludes the $h=0$ extension.

The support mechanism reuses Section 13. Its literature antecedents are [Yu–Ying, arXiv:1206.1935v1, Theorem 1](https://arxiv.org/pdf/1206.1935v1), for the reachable support of a finite-dimensional concurrent quantum program with trace-preserving CP program steps $\mathcal E_i$, a continuation measurement operator $M_1$, a density seed, $F_i(X)=\mathcal E_i(M_1XM_1^\dagger)$ and $F=\sum_iF_i$, and [Ying–Feng–Yu–Ying, arXiv:1304.0060v2, Lemma 1(2)](https://arxiv.org/pdf/1304.0060v2), for a finite-dimensional quantum Markov chain with a trace-preserving CP transition and a density seed. Both display a $D-1$ support horizon. The unrestricted raw CP assumptions, arbitrary positive seed, detector-kernel inequality (16.12) and sharpness witness above are supplied by the present argument, not attributed to those statements. $\square$

**Definition 16.5 (The general law and the full competitor interface).** For $d$ of Definition 16.1 and $0<q<1$, set

$$
\begin{aligned}
Z&=\sum_{k\ge0}q^kP(k),&\gamma_k&=q^kP(k)/Z,\\
S_a&=\sum_{j\ge a}\gamma_j,&
\mu&=\sum_{k\ge0}(k+1)\gamma_k.
\end{aligned}
\tag{16.15}
$$

The normalizer, tails and mean in this section belong to this $d,q$, not to a monomial law specified elsewhere. The target cylinders are

$$
\begin{aligned}
\mathbb P_{d,q}(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{i=1}^{r-1}\gamma_{g_i}\quad(r\ge1),\\
\mathbb P_{d,q}(0^N)&=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j\quad(N\ge0).
\end{aligned}
\tag{16.16}
$$

All indices are nonnegative integers, the internal product is one when $r=1$, and $N=0$ denotes the empty word. The theorems below prove normalization, consistency and realization. A competitor consists of fixed CP maps $\widehat\Phi,\widehat\Psi$ on $M_{D'}(\mathbb C)$ whose sum preserves trace, and a specified density $\widehat\rho$, such that the ordered instrument trace equals (16.16) for every finite word. Its matrices can be complex, its hidden state can be mixed and noninvariant, and its tick map can have arbitrary Kraus rank without a reset premise. Every persistent quantum or classical register, retained record and controller influencing later steps belongs to $D'$. There is no uncounted correlated input or time-dependent external control. The Kraus alternatives within each visible branch are summed, not retained as a further visible or persistent register.

**Theorem 16.6 (Newton realization, stability, observability and reachability for every pair).** Choose any degree-bounded anchored pair for $d$. On $\mathbb C^{m+2}$ use target basis $e_0,\ldots,e_m$ and source basis vector $e_{\mathrm{src}}=e_{m+1}$. Define

$$
\begin{aligned}
N_{j,j+1}&=1\ (0\le j<m),\quad N_{ij}=0\text{ otherwise},&U&=I_{m+1}+N,\\
u_j&=\Delta^{j+1}s(0),&v_j&=\Delta^jp(0)\quad(0\le j\le m),\\
A&=\begin{pmatrix}U&u\\0&1\end{pmatrix},&
B&=\begin{pmatrix}0&v\\0&0\end{pmatrix},\\
x&=e_{\mathrm{src}},&f&=e_0,\qquad F_0=ff^{\mathsf T},\\
\mathcal T_q(X)&=q(AXA^{\mathsf T}+BXB^{\mathsf T}).
\end{aligned}
\tag{16.17}
$$

The polynomial $s$ retains its meaning in (16.1). All unshown blocks of $B$ are zero. For all nonnegative integers $k,t,r$,

$$
\begin{aligned}
u_m&=0,\qquad v_m=m![t^m]p\ne0,\\
f^{\mathsf T}A^kx&=s(k),\qquad f^{\mathsf T}A^tBA^rx=p(t),\qquad BA^rB=0,\\
\operatorname{Tr}[F_0\mathcal T_q^k(xx^{\mathsf T})]&=q^kP(k),\\
\operatorname{spec}(\mathcal T_q)&=\{q\}\text{ on }M_{m+2}(\mathbb C),\\
Q=\sum_{k\ge0}(\mathcal T_q^*)^k(F_0)&>0,\qquad x^{\mathsf T}Qx=Z\in(0,\infty).
\end{aligned}
\tag{16.18}
$$

The raw reachable span from $x$ is all of $\mathbb C^{m+2}$, witnessed by $x,A^jBx$ for $0\le j\le m$. All moments of $\gamma$ are finite, $\gamma_k>0$ exactly for $k\ge h$, and

$$
S_a=q^aH(a),\qquad
H(t)=\frac1Z\sum_{r\ge0}q^rP(t+r),\qquad
\deg H=2m+1,\quad [t^{2m+1}]H=\frac{\delta}{(2m+1)Z(1-q)}.
\tag{16.19}
$$

Proof. Newton expansion as in (16.2) gives $p(t)=\sum_jv_j\binom tj$ and $\Delta s(t)=\sum_ju_j\binom tj$. At integer $t\ge0$, $U^t=\sum_{j=0}^m\binom tjN^j$, so the first target row applied to $U^tv$ is $p(t)$ and applied to $U^tu$ is $\Delta s(t)$. Since $\deg s\le m$ and $\deg p=m$, the last coefficients have precisely the values in (16.18). The block power sends $x$ to $(\sum_{j<k}U^ju,1)$, whose first coordinate is $s(k)-s(0)=s(k)$. Also $BA^rx=(v,0)$, giving the second word amplitude. The image of $B$ is in the target, which $A$ preserves and $B$ annihilates, so $BA^rB=0$.

With rightmost factors acting first, the sole all-$A$ word of length $k$ contributes $s(k)^2$. The exactly $k$ words with one $B$ are $A^tBA^{k-1-t}$ for $0\le t<k$, contributing $p(t)^2$. Every word with at least two $B$ factors is zero. Thus the complete Kraus-word sum is

$$
q^k\sum_{|w|=k}|f^{\mathsf T}wx|^2
=q^k\left(s(k)^2+\sum_{t<k}p(t)^2\right)=q^kP(k).
\tag{16.20}
$$

At $k=0$ the empty word contributes $s(0)^2=0$. Separate words contribute separate squared amplitudes, so no interference between different Kraus alternatives is being assumed.

Both $A$ and $B$ are upper triangular, with diagonals all one and all zero. Column vectorization represents $\mathcal T_q$ on the full complex matrix space by $q(A\otimes A+B\otimes B)$, upper triangular with every diagonal entry $q$. This proves its spectrum, without restricting to real or diagonal matrices. Subtracting $qI$ gives a nilpotent matrix of index at most $(m+2)^2$. Its binomial power expansion shows that for every $q<\theta<1$, $\|\mathcal T_q^k\|\le C_\theta\theta^k$: each of the finitely many terms is a fixed constant times $\binom{k}{j}q^{k-j}$, and a polynomial times $(q/\theta)^k$ is bounded. The dual has the same stability bound, ensuring norm convergence of $Q$.

For a complex vector $y=(y_T,y_{\mathrm{src}})$, positivity gives

$$
y^\dagger Qy=\sum_{k\ge0}q^k\sum_{|w|=k}|f^{\mathsf T}wy|^2.
\tag{16.21}
$$

If this vanishes, every summand vanishes. The rows $f^{\mathsf T}A^tB=p(t)e_{\mathrm{src}}^{\mathsf T}$ force $y_{\mathrm{src}}=0$, since a nonzero degree-$m$ polynomial cannot vanish at every integer $0,\ldots,m$. The rows $f^{\mathsf T}A^j$ for $0\le j\le m$ then force $\sum_{\ell=0}^m\binom j\ell(y_T)_\ell=0$. This coefficient matrix is lower triangular with diagonal one, so $y_T=0$. Hence $Q$ is faithful on every complex memory direction. This detector observability is separate from reachability: the target parts of $A^jBx$ are $U^jv$, whose span equals that of $v,Nv,\ldots,N^mv$ by the same invertible binomial matrix. In reversed target-coordinate order the latter columns form a triangular matrix with diagonal $v_m\ne0$. They span the target, and $x$ supplies the remaining source direction.

Summing (16.20) yields $x^{\mathsf T}Qx=Z$. The polynomial bound $0\le P(k)\le C(1+k)^{2m+1}$ and the ratio test give finiteness of $Z$ and of every moment sum; $P(h)>0$ gives strict positivity of $Z$. The support assertion follows from Theorem 16.3. For (16.19), expand each monomial of $P(t+r)$ in powers of $t$. Each coefficient is a finite linear combination of convergent sums $\sum_{r\ge0}r^jq^r$, with $r^0=1$ also at $r=0$. Thus $H$ is a polynomial, and its top coefficient is the top coefficient of $P$ times $1/(Z(1-q))>0$. Substitution $j=a+r$ in the tail sum proves the identity for $S_a$.

These are the Newton and word mechanisms of Section 11 with the actual polynomial $P$ replacing the monomial, and with $m=0$ included: then $N=0$, $u=0$ and $v_0=p\ne0$, so every step above still holds. $\square$

**Theorem 16.7 (Complete real instrument and a single global resetting tick).** Let $G=Q^{1/2}$ and $D=m+2$, and define

$$
\begin{aligned}
\xi&=Gx/\sqrt Z,&\tau&=\xi\xi^{\mathsf T},&E&=G^{-1}F_0G^{-1},\\
L_A&=\sqrt q\,GAG^{-1},&L_B&=\sqrt q\,GBG^{-1},&J&=\xi f^{\mathsf T}G^{-1},\\
\Phi(X)&=L_AXL_A^{\mathsf T}+L_BXL_B^{\mathsf T},&&
\Psi(X)=JXJ^{\mathsf T}.
\end{aligned}
\tag{16.22}
$$

This is a complete homogeneous binary CP instrument on $M_D(\mathbb C)$ with real entries, no-tick Choi rank exactly two and tick Choi rank exactly one. The matrix ranks of $L_A,L_B,J$ are respectively $D,1,1$. On every input matrix, $\Psi(X)=\tau\operatorname{Tr}(EX)$; every positive-probability tick therefore has the same pure normalized output $\tau$. Moreover

$$
\rho(\Phi)=q<1,\qquad
\Psi\Phi^k(\tau)=\gamma_k\tau,\qquad
\operatorname{Tr}\Phi^a(\tau)=S_a.
\tag{16.23}
$$

Proof. The parameters of Theorem 2.1 are the raw family $\sqrt q A,\sqrt q B$, the single detector column $f$, the reset $x$, the dimension $D$ and the faithful Gramian $Q$ of Theorem 16.6. That theorem applies without any trace-contraction assumption on the raw map. More explicitly, shifting the norm-convergent series gives

$$
Q-qA^{\mathsf T}QA-qB^{\mathsf T}QB=F_0,
\qquad L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J=I.
\tag{16.24}
$$

Real orthogonal diagonalization of $Q>0$ gives a real invertible positive square root $G$, and $\xi^{\mathsf T}\xi=x^{\mathsf T}Qx/Z=1$. Conjugation by $G^{-1}$ proves the second identity. These Kraus expressions are CP on all complex matrices: their ampliations are sums of conjugations by each Kraus matrix tensored with an identity. Completeness gives trace preservation of the sum and trace nonincrease of each positive branch, including on complex coherent inputs.

The invertible map $\Gamma(X)=GXG$ satisfies $\Phi=\Gamma\mathcal T_q\Gamma^{-1}$ and

$$
\Phi^k(\tau)=\frac{G\mathcal T_q^k(xx^{\mathsf T})G}{Z}.
\tag{16.25}
$$

This proves stability, while the outer-product formula for $J$ proves the global reset identity. Combining it with (16.20) proves the actual gap formula. The definition of $Z$ gives $\sum_k\gamma_k=1$. For $t_a=\operatorname{Tr}\Phi^a(\tau)$, completeness yields $t_a-t_{a+1}=\gamma_a$ and stability yields $t_a\to0$. Telescoping gives $t_a=S_a$, with no probability left at an infinite next gap.

Finally $A$ is invertible and $B=(v,0)e_{\mathrm{src}}^{\mathsf T}$ is nonzero of rank one. Since $D\ge2$, they are linearly independent over $\mathbb C$. Similarity and nonzero scaling preserve both independence and matrix ranks. The Choi matrix of $\Phi$ is the sum of the outer products of the vectorizations of $L_A,L_B$; the range of a sum of positive operators is the span of their ranges. Its rank is therefore two, and any Kraus representation must span that same Choi range. The two nonzero factors of $J$ make its matrix rank and its Choi rank one. This proves all stated rank distinctions. $\square$

**Theorem 16.8 (Faithful stationary density, all tails and all cylinders).** For (16.22), the series

$$
R_0=\sum_{a\ge0}\Phi^a(\tau),\qquad \rho_*=R_0/\mu
\tag{16.26}
$$

defines a real faithful mixed density invariant under $\Phi+\Psi$. Its actual ordered-word traces give exactly (16.16), including the empty word, and define a proper stationary renewal law with tick rate $1/\mu$ and no all-zero stationary component. Its visible support consists exactly of finite words with at least $h$ zeros between successive ones. This is exactly the no-adjacent-one Fibonacci language if and only if $d(0)>0$.

Proof. Stability gives norm convergence of $R_0$. Nonnegative summation and (16.23) give

$$
\operatorname{Tr}R_0=\sum_{a\ge0}S_a
=\sum_{j\ge0}(j+1)\gamma_j=\mu<\infty,\qquad
\Phi(R_0)=R_0-\tau,\qquad \Psi(R_0)=\tau.
\tag{16.27}
$$

Thus $\rho_*$ is normalized, invariant and has tick rate $1/\mu$. For each raw word $w$ in $A,B$, its completed word satisfies $L_w\xi=q^{|w|/2}Gwx/\sqrt Z$. Invertible $G$ and positive $q$ preserve the full reachable span of Theorem 16.6. For complex $y$,

$$
y^\dagger R_0y=\sum_{a\ge0}\sum_{|w|=a}|y^\dagger L_w\xi|^2.
\tag{16.28}
$$

Vanishing forces orthogonality to that full span, hence $y=0$. This proves faithfulness. The summands are real symmetric, and full rank in dimension $D\ge2$ makes $\rho_*$ mixed. Its tick probability $1/\mu>0$ differs from $\operatorname{Tr}\Psi(\tau)=\gamma_0=0$, so it is distinct from the pure post-tick state.

For an initial run of $a$ zeros and its first tick, the actual unnormalized output is

$$
\Psi\Phi^a(\rho_*)
=\frac1\mu\sum_{c\ge0}\Psi\Phi^{a+c}(\tau)
=\frac{S_a}{\mu}\tau.
\tag{16.29}
$$

Each following gap $g_i$ and tick multiplies this density by $\gamma_{g_i}$ and returns it to $\tau$. The final $b$ zeros have trace $S_b$ from that reset. Taking the trace proves the first line of (16.16) for every number of ticks. With no tick, applying $\Phi^N$ directly to (16.26) gives

$$
\operatorname{Tr}\Phi^N(\rho_*)
=\frac1\mu\sum_{a\ge0}S_{N+a}
=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j.
\tag{16.30}
$$

At $N=0$ this is one by (16.27). These cases exhaust all words. Summing the last symbol uses trace preservation and gives right consistency; summing the first uses invariance and gives left consistency. The finite-alphabet consistent cylinders consequently define a stationary process. After any positive-probability tick history the memory is $\tau$, so the joint law of any finite sequence of subsequent complete gaps is the product of their $\gamma$ values. Their normalization proves a proper next gap at each renewal. Also

$$
0\le\mathbb P_{d,q}(0^N)
\le\frac1\mu\sum_{j\ge N}(j+1)\gamma_j\longrightarrow0,
\tag{16.31}
$$

excluding an infinite all-zero future of positive probability and hence any all-zero stationary component.

All $S_a$ and all finite all-zero cylinders are positive, since $\gamma_k>0$ for every $k\ge h$. The first cylinder formula is positive exactly when each internal gap is at least $h$. By (16.6), $h=1$ exactly when $d(0)>0$; if $h>1$, even the no-adjacent-one word $101$ has probability zero. This proves the exact support assertion.

The stationary convention is that of [Monras–Beige–Wiesner, *Hidden Quantum Markov Models and non-adaptive read-out of many-body states*, arXiv:1002.2337v2, equations (25)–(27)](https://arxiv.org/pdf/1002.2337v2): a fixed point of the sum of the symbol operations supplies ordered trace probabilities. Equations (16.27)–(16.31) derive the new law's renewal factors, mean and boundary tails using the summation mechanism of Sections 5 and 14. The monomial hypotheses of Theorem 5.1 do not themselves quantify over Definition 16.5. $\square$

**Theorem 16.9 (Actual-posterior rank bounds and reused no-tick Choi minimum).** For the competitor class of Definition 16.5 the minimum possible no-tick Choi rank, across all finite complex memory dimensions, is exactly two. If a competitor has dimension $D'$, let $\tau_0$ be its actual posterior after the positive-probability first tick and let $F_1=\widehat\Psi^*(I)$. With $a=\operatorname{rank}\tau_0$ and $b=\operatorname{rank}F_1$,

$$
D'\ge h+a+b-1\ge h+1,
\qquad h+1\le D_{\min}\le m+2.
\tag{16.32}
$$

When $h=m+1$, equivalently $d=c\operatorname{fall}_m^2$, the memory minimum is $m+2$. Every competitor at that minimum has $a=b=1$, full primal and dual no-tick reachable spaces and a global pure resetting tick map with Choi rank one. Any invariant initialization of such a minimizer reproducing the law is faithful and mixed. These minimum-memory conclusions do not assert that every larger-dimensional competitor has a resetting tick.

Proof. The one-tick and two-tick cylinders give the actual extraction

$$
\begin{aligned}
\nu&=\operatorname{Tr}\widehat\Psi(\widehat\rho)
=\mathbb P_{d,q}(1)=1/\mu>0,\\
\tau_0&=\widehat\Psi(\widehat\rho)/\nu,\qquad F_1=\widehat\Psi^*(I),\\
\operatorname{Tr}[F_1\widehat\Phi^k(\tau_0)]
&=\frac{\mathbb P_{d,q}(1\,0^k1)}{\mathbb P_{d,q}(1)}
=\gamma_k=\frac{q^kP(k)}Z.
\end{aligned}
\tag{16.33}
$$

Here $\tau_0$ is a density, possibly mixed, and $F_1$ is a positive effect. This uses neither a common reset nor invariance of $\widehat\rho$. Finite-dimensional CP maps have finite Kraus representations by diagonalizing their positive Choi matrices. Theorem 16.4 therefore applies at the exact positive delay $h$, giving the first bound. The explicit complete instrument gives the upper bound. For the actual competitor survival $t_k=\operatorname{Tr}\widehat\Phi^k(\tau_0)$, completeness gives $t_0=1$ and $t_k-t_{k+1}=\gamma_k$; normalization of $\gamma$ gives $t_k=S_k\to0$. This identifies its actual tails without any assumption on an unused spectral block.

For the no-tick lower bound, rank zero would mean $\widehat\Phi=0$ and hence $\gamma_h=0$, contradicting $h\ge1$ and $\gamma_h>0$. Rank one would give $\widehat\Phi(X)=CXC^\dagger$ for some complex matrix $C$, so (16.33) becomes

$$
\left\|F_1^{1/2}C^k\tau_0^{1/2}\right\|_{\rm HS}^2
=\frac{q^kP(k)}Z.
\tag{16.34}
$$

This is the exact positive-effect, mixed-seed interface of the generic finite-vector-recurrence argument in [Chapter 29, equations (29.3)–(29.6), reused in Chapter 40, equation (40.4)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#29-the-original-sns-needs-two-unresolved-no-tick-kraus-alternatives), and in Theorem 6.3 here. Its generic assertion is that an eventual nonzero squared norm of a finite constant-coefficient complex vector recurrence, equal to $q^k$ times a real polynomial with positive leading coefficient, has even polynomial degree. It is not restricted to the SNS or monomial conclusions of the named theorems.

To give its full application, put $V_k=F_1^{1/2}C^k\tau_0^{1/2}$ in finite Hilbert–Schmidt space. Cayley–Hamilton gives a scalar constant-coefficient recurrence for every coordinate. After finitely many initial indices, its nonzero terms have the form $V_k=\sum_jR_j(k)\lambda_j^k$ with distinct nonzero $\lambda_j$ and nonzero vector polynomials $R_j$. This is the classical recurrence representation of [Stanley, *Enumerative Combinatorics*, Volume 1, Theorem 4.1.1 and Proposition 4.2.2](https://math.mit.edu/~rstan/ec/ec1.pdf): a rational generating series with denominator nonzero at zero gives exponential-polynomial coefficients outside a finite exceptional set. Theorem 4.1.1 requires a nonzero last recurrence coefficient; zero-root transients can be discarded, or handled by the exceptional-set proposition. Thus no invertibility of $C$ is required. Equivalently, on each nonzero Jordan block $\lambda I+N$, the finite expansion $\sum_j\binom{k}{j}\lambda^{k-j}N^j$ gives the same representation; zero Jordan blocks vanish eventually.

The right side of (16.34) is positive for all $k\ge h$, so $V_k$ is not eventually zero. Choose the largest modulus $R>0$ of an occurring $\lambda_j$, and the largest vector-polynomial degree $e$ at that modulus. With leading vectors $a_j\ne0$ of those terms and distinct phases $\omega_j=\lambda_j/R$, one has

$$
\frac{V_k}{R^kk^e}=T_k+o(1),\qquad
T_k=\sum_{j\in J}a_j\omega_j^k,\qquad
\lim_{N\to\infty}\frac1N\sum_{k=1}^N\|T_k\|^2
=\sum_{j\in J}\|a_j\|^2>0.
\tag{16.35}
$$

Terms of smaller modulus or smaller degree vanish after this normalization. The mean identity follows by expansion: diagonal phase products equal one, and every off-diagonal average is $N^{-1}\sum_{k=1}^N\zeta^k\to0$ for a fixed $|\zeta|=1$, $\zeta\ne1$, by the finite geometric-sum formula. No orthogonality of leading vectors is needed. The normalized vectors are bounded and their squared norms have this same strictly positive Cesàro mean, since their difference from $T_k$ tends to zero. By (16.34) their squared norms equal

$$
\frac{P(k)}{Zk^{2e}}\left(\frac q{R^2}\right)^k.
\tag{16.36}
$$

If $q<R^2$, this tends to zero; if $q>R^2$, it tends to infinity, contradicting respectively the positive mean or boundedness. Hence $q=R^2$. The same alternatives for polynomial growth then force $\deg P=2e$. But $\deg P=2m+1$ with positive leading coefficient, a contradiction. This reuses the existing parity proof with the new polynomial $P/Z$; no CP-growth estimate, pure hidden trajectory, hidden-source radius identification or tick-rank restriction enters. Theorem 16.7 attains rank two, proving its minimum over all finite competitor dimensions, independently of whether $m+2$ is minimum memory.

At maximal delay, (16.32) and the construction give $D_{\min}=m+2=h+1$. If a competitor has this dimension, its positive ranks obey $a+b\le2$, so $a=b=1$. The separate support bounds of Theorem 13.2 give $h\le r-a$ and $h\le r^\vee-b$, forcing $r=r^\vee=D'$. To spell out the actual-output consequence of Theorem 13.3, write $F_1=\lambda\eta\eta^\dagger$ for a unit $\eta$ and $\lambda>0$. In any tick Kraus representation $\widehat\Psi(X)=\sum_iJ_iXJ_i^\dagger$, the identity $\sum_i\|J_iy\|^2=y^\dagger F_1y=0$ for $y\perp\eta$ gives $J_i=v_i\eta^\dagger$. Thus $\widehat\Psi(X)=(\eta^\dagger X\eta)M$ with $M=\sum_iv_iv_i^\dagger$ and $\operatorname{Tr}M=\lambda$. The positive actual tick in (16.33) gives $\tau_0=M/\lambda$, so

$$
\widehat\Psi(X)=\tau_0\operatorname{Tr}(F_1X).
\tag{16.37}
$$

Since $\tau_0$ has rank one, positivity forces all $v_i$ into its one-dimensional range. Hence all nonzero $J_i$ span a single rank-one direction, and tick Choi rank is one. If an invariant initialization $\sigma$ reproduces the law, it satisfies $\sigma=\widehat\Phi(\sigma)+\nu\tau_0$. Iterating $D'$ times gives $\sigma\ge\nu\sum_{j=0}^{D'-1}\widehat\Phi^j(\tau_0)>0$, where full reachability and the positive-sum range identity prove the strict inequality. Since $D'=m+2\ge2$, it is mixed. For $m\ge1$ this is the delayed-family minimum of Section 14 under positive scaling of $d$; the proof also supplies its constant endpoint $m=0$. For nonmaximal delay, (16.32) is the dimension conclusion asserted here; no general equality $D_{\min}=m+2$ is inferred. $\square$

**Proposition 16.10 (The constant endpoint, scaling and the nonnormalizable zero case).** For $d=c>0$ one has $m=0$, $h=1$, $P(k)=ck$ and

$$
Z=\frac{cq}{(1-q)^2},\qquad
\gamma_0=0,\qquad \gamma_k=k(1-q)^2q^{k-1}\ (k\ge1),\qquad
\mu=\frac2{1-q}.
\tag{16.38}
$$

In basis $e_0,e_1$ a completed instrument is

$$
L_A=\sqrt q I_2,\qquad
L_B=\sqrt{1-q}\,e_0e_1^{\mathsf T},\qquad
J=\sqrt{1-q}\,e_1e_0^{\mathsf T},\qquad
\tau=e_1e_1^{\mathsf T},\quad \rho_*=I_2/2.
\tag{16.39}
$$

Its dimension two and no-tick Choi rank two are both minimum in the full competitor class. For fixed $q$, positive scaling of any nonzero $d$ leaves the law unchanged; two such polynomials give the same law if and only if they are positive scalar multiples. The zero polynomial gives no normalized law of the form (16.15).

Proof. The unique positively oriented constant pair is $p=\sqrt c,s=0$. Thus the raw matrices are $A=I_2$, $B=\sqrt c\,e_0e_1^{\mathsf T}$. The Gramian terms are $q^k(e_0e_0^{\mathsf T}+kc\,e_1e_1^{\mathsf T})$, giving

$$
Q=\operatorname{diag}\left(\frac1{1-q},\frac{cq}{(1-q)^2}\right).
\tag{16.40}
$$

Here $\sum_{k\ge0}q^k=(1-q)^{-1}$, and multiplying $\sum_{k\ge1}kq^k$ by $1-q$ leaves $\sum_{k\ge1}q^k=q/(1-q)$, proving the stated second sum. Substituting (16.40) into (16.22) gives precisely (16.39). Its effects sum to $qI_2+(1-q)e_1e_1^{\mathsf T}+(1-q)e_0e_0^{\mathsf T}=I_2$. By induction, for $k\ge1$,

$$
\Phi^k(\tau)=q^ke_1e_1^{\mathsf T}
+k(1-q)q^{k-1}e_0e_0^{\mathsf T}.
\tag{16.41}
$$

The step uses $\Phi(e_0e_0^{\mathsf T})=qe_0e_0^{\mathsf T}$ and $\Phi(e_1e_1^{\mathsf T})=qe_1e_1^{\mathsf T}+(1-q)e_0e_0^{\mathsf T}$. Applying the tick gives (16.38). Summing (16.41), together with the $k=0$ term, gives $R_0=I_2/(1-q)$, so its trace is $\mu=2/(1-q)$ and $\rho_*=I_2/2$. The minima and actual global tick reset at minimum follow from Theorem 16.9 with $h=m+1=1$.

For general $d$, multiplication by $c>0$ multiplies its uniquely anchored integral $P$ and normalizer $Z$ by $c$, leaving $\gamma$, its tails, mean and every cylinder unchanged. Conversely, at fixed $q$, equality of the gap laws gives $P_1(k)/Z_1=P_2(k)/Z_2$ at all nonnegative integers. Polynomial identity then gives $P_1=(Z_1/Z_2)P_2$ and, by taking differences, $d_1=(Z_1/Z_2)d_2$, with positive ratio. Equality of stationary cylinders implies equality of these gaps through (16.33), so the same assertion holds for the full laws. Finally for $d=0$ its anchored integral is identically zero, its only anchored pair is $(0,0)$ by Theorem 16.2, and $Z=0$. There is no probability normalization by this zero denominator. $\square$

**Definition 16.11 (Scope of the polynomial extension).** The new polynomial class includes real-root boundary cases and arbitrary repeated real zeros under global nonnegativity. Existence of an anchored pair is the compactness consequence in Theorem 16.2, not an extension of a chosen half-plane factor across real roots. The exact delay and divisibility classification and the positive-delay detector tradeoff have the separate arguments in Theorems 16.3–16.4. Spectral factorization, polynomial interpolation and finite differences, finite-dimensional compactness, support reachability and recurrence representations are classical ingredients; the cited results have the conditions stated with their uses. The no-tick parity obstruction is explicitly the reused generic argument, and the Newton, Gramian and stationary interfaces are derived here for the actual law (16.15).

The resource is finite persistent complex memory dimension, and the output object is the classical stationary cylinder law. The construction establishes an upper bound $m+2$, while unconditional equality here is restricted to maximal delay. The positive-delay rank witness (16.13) proves raw CP sharpness, not complete-instrument sharpness for arbitrary seed and effect ranks. The original monomial memory minimum and the general finite-CP growth obligation are separate from this extension. A pure tick posterior is distinct from the faithful mixed stationary density; real Kraus entries do not change the complex input model. No native AURIC identification, coherent-output preparation, physical precision, entropy, energy, work or control-cost consequence is included.

## 追加锚（本行以下为增补区）


## 17. Information and testing from one actual stationary history

This section compares the two actual output laws supplied by Theorems 11.5 and 15.3. The observer receives consecutive bits of one of these laws, starting at a stationary time, and the model promise specifies which two laws are possible. The residual is a known part of the alternative model. A small residual bounds finite-window change in Section 15; the question here is how many actual bits can distinguish that change at a prescribed risk. The initial waiting time and the last incomplete gap belong to this question.

**Definition 17.1 (Promised pair and observation contract).** Fix the polynomial data of Definition 15.1 independently of $q$, with $e\ne0$, $H(k)>0$ for every integer $k\ge1$, and constants $0<\ell\le u<\infty$ such that $\ell\le r_k:=H(k)/k^n\le u$. For each fixed common $q\in(0,1)$ put

$$
\begin{aligned}
p_k&=\frac{k^nq^k}{Z_n(q)},&h_k&=\frac{H(k)q^k}{Z_H(q)},&
c&=\frac{Z_H(q)}{Z_n(q)}=\mathbb E_p r_K,\\
p_0&=h_0=0,&U_a&=\sum_{k\ge a}p_k,&V_a&=\sum_{k\ge a}h_k,\\
\mu_0&=\mathbb E_p(K+1),&\mu_1&=\mathbb E_h(K+1),&\kappa&=u/\ell.
\end{aligned} \tag{17.1}
$$

In particular $U_0=U_1=V_0=V_1=1$. Write $\mathsf P_0,\mathsf P_1$ for the stationary binary renewal laws with these gap laws, and $\mathsf P_i^W$ for their restrictions to $X_0,\ldots,X_{W-1}$. Their cylinders are (15.8), using $p,U,\mu_0$ or $h,V,\mu_1$. Define $z_i(W)=\mathsf P_i(0^W)$; the empty word has $z_i(0)=1$.

The observer's available action is to read the next bit, or stop and emit a label in $\{0,1\}$. Reading a zero costs one bit just as reading a one does. There is no query of hidden age, instrument memory, exact source probability, or an alternative response on the same state; no reset, second source, omitted interval or free gap sample is available. A deadline $W$ means a label must be emitted after at most $W$ consecutive reads. The two errors are $\alpha_0=\mathsf P_0(\text{label }1)$ and $\alpha_1=\mathsf P_1(\text{label }0)$. An independently randomized rule may use an additional seed with the same law under both hypotheses; its randomness and storage are separate resources. The sufficient rules below are deterministic. Known real parameters define statistical experiments; bit-effective execution requires the additional representation stated in Section 19. All logarithms in Sections 17–19 are natural.

**Theorem 17.2 (Residual variance, exact visible information and censored endpoints).** Let

$$
\begin{aligned}
d_0&=D(p\Vert h)=\log c-\mathbb E_p\log r_K,&I_0&=d_0/\mu_0,\\
d_1&=D(h\Vert p)=\mathbb E_h\log r_K-\log c,&I_1&=d_1/\mu_1.
\end{aligned} \tag{17.2}
$$

Both $d_i,I_i$ are strictly positive, and

$$
\frac{\operatorname{Var}_p(r_K)}{2u^2}\le d_0
\le\frac{\operatorname{Var}_p(r_K)}{2\ell^2}.
\tag{17.3}
$$

For $W\ge1$, the exact finite-record relative entropy is

$$
\begin{aligned}
D(\mathsf P_0^W\Vert\mathsf P_1^W)
={}&(1-z_0(W))\log\frac{\mu_1}{\mu_0}
+\frac2{\mu_0}\sum_{a=0}^{W-1}U_a\log\frac{U_a}{V_a}\\
&+\frac1{\mu_0}\sum_{k=1}^{W-2}(W-k-1)p_k\log\frac{p_k}{h_k}
+z_0(W)\log\frac{z_0(W)}{z_1(W)}.
\end{aligned} \tag{17.4}
$$

An upper limit below a sum's lower limit gives zero. For both orientations,

$$
\left|D(\mathsf P_i^W\Vert\mathsf P_{1-i}^W)-WI_i\right|
\le3\log\kappa\quad(W\ge1),\qquad
\lim_{W\to\infty}\frac{D(\mathsf P_i^W\Vert\mathsf P_{1-i}^W)}W=I_i.
\tag{17.5}
$$

At $W=0$ the relative entropy is zero.

Proof. The tilt $h_k=p_kr_k/c$ gives (17.2). Applied to $f(x)=-\log x$ on $[\ell,u]$, Taylor's formula about $c$, with $1/u^2\le f''\le1/\ell^2$, gives (17.3) after taking expectations. If $p=h$, positivity of $q^k$ forces $H(k)=ck^n$ at every positive integer. Polynomial identity and the leading coefficient of $H$ give $c=1$ and $H=k^n$, hence $ne=\Delta(H-k^n)=0$, a contradiction. Strict convexity gives both positive divergences. Bounded ratios make them finite.

For a legal word containing a one, write its unique decomposition as $w=0^a1\,0^{g_1}1\cdots0^{g_j}1\,0^b$, with $j\ge0$. The supplier's cylinder formula gives

$$
\log\frac{\mathsf P_0(w)}{\mathsf P_1(w)}
=\log\frac{\mu_1}{\mu_0}+\log\frac{U_a}{V_a}
+\sum_{v=1}^j\log\frac{p_{g_v}}{h_{g_v}}
+\log\frac{U_b}{V_b}.
\tag{17.6}
$$

The chance that the first one of the window is at position $a<W$ is $U_a/\mu_0$. The chance that the final run contains $b<W$ zeros after the last one is $U_b/\mu_0$, by the same cylinder formula. An internal $k$-gap has both endpoint ones in the window at exactly $W-k-1$ possible starting positions when $k\le W-2$, each of probability $p_k/\mu_0$ by stationarity. Taking expectations in (17.6), and adding the all-zero word's own likelihood, proves (17.4). This calculation includes a one-symbol window, a word with only one tick, and either zero-length boundary run. A boundary run is never counted as a complete gap.

To bound the endpoint contribution sharply, let $\lambda_0(k,a)=p_k/\mu_0$, $0\le a\le k$, be the normalized interval-and-position law of (15.11), and put $b_*:=\mathbb E_{\lambda_0}r_K$. Then $\mu_1/\mu_0=b_*/c$. The tail tilts $r^{(a)}:=\mathbb E_p(r_K\mid K\ge a)$ lie in $[\ell,u]$ and satisfy $V_a/U_a=r^{(a)}/c$. Thus the three boundary terms in (17.6) together are

$$
\log\frac{b_*c}{r^{(a)}r^{(b)}},
\qquad\left|\log\frac{b_*c}{r^{(a)}r^{(b)}}\right|
\le2\log\kappa.
\tag{17.7}
$$

For an all-zero word, its integrated-tail sum in (15.8) is tilted by a conditional weighted average $r^{[W]}\in[\ell,u]$; the full cylinder ratio is $z_1(W)/z_0(W)=r^{[W]}/b_*$. Its logarithm has absolute value at most $\log\kappa$. These statements use the common normalizers; bounding three unrelated logarithms separately loses this improvement.

Finally, $|\log(p_k/h_k)|\le\log\kappa$, and

$$
\frac1{\mu_0}\sum_{k\ge1}
\left(W-(W-k-1)_+\right)p_k
\left|\log\frac{p_k}{h_k}\right|
\le\frac{\log\kappa}{\mu_0}\mathbb E_p(K+1)=\log\kappa.
\tag{17.8}
$$

The internal-gap expectation therefore differs from $WI_0$ by at most $\log\kappa$, while the expected remaining contribution has absolute value at most $2\log\kappa$. This proves (17.5). Reversing the laws uses the reciprocal tilt, whose endpoint ratio is also $\kappa$, and proves the other orientation. $\square$

**Theorem 17.3 (A finite-record converse with the stationary initial cost).** Define

$$
\pi_0(a)=U_a/\mu_0,\quad\pi_1(a)=V_a/\mu_1,\quad
C_i=D(\pi_i\Vert\pi_{1-i}),\quad
\lambda_1(k,a)=h_k/\mu_1\ (0\le a\le k).
\tag{17.9}
$$

For every $W\ge1$,

$$
\begin{aligned}
D(\mathsf P_i^W\Vert\mathsf P_{1-i}^W)&\le C_i+(W-1)I_i,\\
C_0&\le D(\lambda_0\Vert\lambda_1)
\le\frac{\operatorname{Var}_{\lambda_0}(r_K)}{2\ell^2}
\le\frac{(u-\ell)^2}{8\ell^2}.
\end{aligned} \tag{17.10}
$$

The analogous initial bound holds after reversing the tilt. If a rule with deadline $W$ has both errors at most $\alpha\in(0,1/2)$, then, for $i=0,1$,

$$
 b_\alpha:=(1-2\alpha)\log\frac{1-\alpha}{\alpha}
 \le D(\mathsf P_i^W\Vert\mathsf P_{1-i}^W),\qquad
 W\ge1+\frac{(b_\alpha-C_i)_+}{I_i}.
\tag{17.11}
$$

These necessary bounds include independently randomized rules and rules that stop before the deadline.

Proof. Use a countable age chain only as a proof variable. Its state is zero at a tick and $a\ge1$ at the $a$th zero following that tick. For the first law, its transitions from $a$ are to zero with probability $p_a/U_a$ and to $a+1$ with probability $U_{a+1}/U_a$. Its invariant distribution is $\pi_0$: incoming advance mass is $U_a/\mu_0$ for $a\ge1$, and incoming reset mass is $\sum_a p_a/\mu_0=1/\mu_0$. The second chain uses $h,V,\pi_1$. Emitting $\mathbf1_{\{a=0\}}$ gives the stationary renewal cylinders, so the observed word is a deterministic projection of the chain's $W$ states. At $a=0$ the reset term is zero under both laws and the advance is forced.

Multiplying the one-step conditional divergence by $\pi_0(a)$, and summing, gives the telescoping identity

$$
\begin{aligned}
\mu_0\sum_{a\ge0}\pi_0(a)D(Q_0(a,\cdot)\Vert Q_1(a,\cdot))
={}&\sum_{a\ge0}p_a\log\frac{p_a}{h_a}\\
&+\sum_{a\ge0}\left(
U_{a+1}\log\frac{U_{a+1}}{V_{a+1}}-U_a\log\frac{U_a}{V_a}\right)
=d_0.
\end{aligned} \tag{17.12}
$$

Here $0\log(0/0)$ denotes the absent reset term at zero. All other log ratios are bounded by fixed multiples of $\log\kappa$, and $\sum_aU_a=\mu_0<\infty$. The terminal tail term tends to zero and the initial term is zero. Thus the finite path chain rule gives exactly $C_0+(W-1)I_0$ for the augmented path, and data processing gives the first inequality in (17.10) in the displayed upper-bound direction. No hidden age is provided to the observer.

The projection of $\lambda_i$ to $a$ is $\pi_i$. Moreover $\lambda_1=r_K\lambda_0/b_*$. Data processing and the Taylor argument of (17.3) give the next bound. For a variable in $[\ell,u]$, $(r-\ell)(u-r)\ge0$ implies $\operatorname{Var}(r)\le(u-\mathbb Er)(\mathbb Er-\ell)\le(u-\ell)^2/4$, proving the last bound.

An early-stopped decision is a function of the complete $W$-prefix, ignoring its unused suffix. Adding an independent common seed changes neither relative entropy nor the argument. Data processing to the decision gives, in the forward orientation, the Bernoulli divergence with probabilities $1-\alpha_0\ge1-\alpha$ and $\alpha_1\le\alpha$ for label zero. On the region $x>y$, $D(\operatorname{Ber}(x)\Vert\operatorname{Ber}(y))$ increases with $x$ and decreases with $y$, as follows by differentiation. Its minimum on this region is attained at $(1-\alpha,\alpha)$ and equals $b_\alpha$. The reverse direction is identical. Combining with (17.10) and the necessary $W\ge1$ gives (17.11). $\square$

**Theorem 17.4 (An attainable test with every waiting bit charged).** Put

$$
 A=\sum_{k\ge1}\sqrt{p_kh_k}=\frac{\mathbb E_p\sqrt{r_K}}{\sqrt c},\qquad 0<A<1.
\tag{17.13}
$$

Wait for the first actual one at $\tau=\min\{t\ge0:X_t=1\}$, then acquire $N\ge1$ complete subsequent gaps $K_1,\ldots,K_N$. The last required tick is at $T_N=\tau+\sum_{j=1}^N(K_j+1)$, and the actual number of bits read is $L_N=T_N+1$. Choose label zero when $\prod_{j=1}^N p_{K_j}/h_{K_j}\ge1$, with a fixed rule at equality. Without a deadline this rule terminates almost surely, each error is at most $A^N$, and

$$
\mathsf P_i(\tau=a)=\pi_i(a),\qquad
\mathbb E_i L_N=1+\frac{\mathbb E_i[K(K+1)]}{2\mu_i}+N\mu_i.
\tag{17.14}
$$

With a deadline $W$, perform this same acquisition until $W$ bits have been read. If $L_N\le W$, use the gap decision; otherwise emit a prescribed default label. Each error is at most

$$
 A^N+\mathsf P_i(T_N\ge W)
 \le A^N+\min\left\{\frac{\mathbb E_i L_N}{W},
 \inf_{1<z<1/q}z^{-W}F_i(z)G_i(z)^N\right\},
\tag{17.15}
$$

where $Z_0=Z_n$, $Z_1=Z_H$ and

$$
G_i(z)=\mathbb E_i z^{K+1}=\frac{zZ_i(qz)}{Z_i(q)},\qquad
F_i(z)=\mathbb E_i z^\tau=\frac{G_i(z)-1}{\mu_i(z-1)}.
\tag{17.16}
$$

In particular, both errors are at most $\alpha$ with the explicit mathematical choices

$$
N=\left\lceil\frac{\log(2/\alpha)}{-\log A}\right\rceil,\qquad
W=\left\lceil\frac2\alpha\max_{i=0,1}\mathbb E_i L_N\right\rceil.
\tag{17.17}
$$

Proof. Strict Cauchy–Schwarz gives $A<1$, since equality would imply $p=h$. The actual cylinder for $0^a1\,0^{k_1}1\cdots0^{k_N}1$ equals $\pi_i(a)\prod_j f_i(k_j)$, with $f_0=p,f_1=h$. Summing these nonnegative terms proves that $\tau$ is finite almost surely and that the gaps after this actual tick are iid with law $f_i$, independently of $\tau$. The initial wait itself is not a gap sample. On the space of these $N$ completed gaps, the sum of the two likelihood-test errors is the sum of the smaller of the two product masses, bounded by the sum of their geometric means, namely $A^N$. Therefore each error is at most $A^N$.

Since $\sum_{a=0}^k a=k(k+1)/2$, summing $a\pi_i(a)$ proves (17.14). Polynomial times geometric tails make every moment used here finite. Independence and $\sum_{a=0}^k z^a=(z^{k+1}-1)/(z-1)$ prove (17.16) and $\mathbb E_i z^{T_N}=F_i(z)G_i(z)^N$. The last tick fits precisely when $T_N\le W-1$; timeout is $T_N\ge W$, including a partially observed final gap or no observed tick. Exponential Markov at this integer threshold gives the second bound in (17.15); ordinary Markov on $L_N>W$ gives the first. A wrong deadline decision lies in the union of a wrong uncapped decision and timeout. This union bound does not condition the gap distribution on completing before the deadline. Formula (17.17) now gives the two error guarantees. $\square$

**Corollary 17.5 (What finite certification does and does not mean).** No rule can be correct with probability one under both hypotheses and emit a terminal label at a finite time with positive probability under either. Nevertheless the finite-confidence rules of Theorem 17.4 exist at every fixed $q$. On infinite paths,

$$
\frac1W\log\frac{\mathsf P_0(X_0\cdots X_{W-1})}
                         {\mathsf P_1(X_0\cdots X_{W-1})}
\longrightarrow
\begin{cases}I_0,&\mathsf P_0\text{-almost surely},\\-I_1,&\mathsf P_1\text{-almost surely}.
\end{cases}
\tag{17.18}
$$

Proof. Both laws assign positive probability to every legal finite word, including all-zero words, and zero to every illegal word. Their finite restrictions therefore have exactly the same null sets. The property persists after adjoining any common independent seed. For each finite time and each terminal label, an error-free rule would require a stopping event of zero probability under the opposite law; equivalence makes its probability zero under both. The countable union over terminal times proves the first assertion, including rules with possible nontermination.

For the last assertion, after the first observed tick use the strong laws for the iid cycle lengths $K_j+1$ and the bounded rewards $\log(p_{K_j}/h_{K_j})$. The number of complete subsequent cycles divided by $W$ tends to $1/\mu_i$, and their average reward tends to $d_0$ or $-d_1$. The initial wait is finite almost surely, and (17.7) bounds the remaining likelihood contribution uniformly. This proves (17.18). The sign of this limit classifies the infinite path almost surely; no finite stopping certificate follows. Finite risks concern the promised pair, not certification of exact probabilities, the model promise, or residual vanishing against all unspecified stationary alternatives. $\square$


## 18. Endpoint record costs determined by the residual

**Definition 18.1 (Fixed-pair endpoint parameters and optimal record length).** Keep $n,H$ fixed as in Definition 17.1. Let $W^*_\alpha(q)$ be the least integer $W\ge0$ for which a deterministic decision from $W$ consecutive stationary bits has both errors at most the fixed $\alpha\in(0,1/2)$. A rule stopping earlier and ignoring the remaining bits is allowed in this definition. Theorem 17.4 proves finiteness. Write

$$
\begin{aligned}
j_*&=\min\{k\ge2:r_k\ne r_1\},&c_*&=r_{j_*}/r_1,\\
R(k)&=H(k)-k^n,&d&=n-\deg R,&a_*&=[k^{n-d}]R(k),&s&=-\log q.
\end{aligned} \tag{18.1}
$$

Then $2\le j_*\le n$, $1\le d\le n-1$, $a_*\ne0$, and $c_*>0$, $c_*\ne1$. In particular

$$
r_k=1+a_*k^{-d}+O(k^{-d-1})\quad(k\to\infty).
\tag{18.2}
$$

These parameters describe each admissible polynomial pair; they do not assert that every possible value of $d$ is attained by an anchored square representation. All endpoint constants and remainder constants below may depend on this fixed pair. No coefficient-uniform separation is assumed.

To verify the assertions, $\Delta R=ne\ne0$ and $R(0)=0$ show that $1\le\deg R\le n-1$ and that its leading coefficient is $n[t^{\deg e}]e/(\deg e+1)$. The nonzero polynomial $H-r_1k^n$ cannot vanish at all of $0,1,\ldots,n$; otherwise $r_1=1$, $H=k^n$, and $e=0$. This proves existence and the stated bound for $j_*$.

**Theorem 18.2 (Rare departures from the alternating limit).** As $q\downarrow0$,

$$
\begin{aligned}
I_0&=\frac{j_*^n}{2}(c_*-1-\log c_*)q^{j_*-1}+O(q^{j_*}),\\
I_1&=\frac{j_*^n}{2}(c_*\log c_*+1-c_*)q^{j_*-1}+O(q^{j_*}),\\
1-A&=\frac{j_*^n}{2}(\sqrt{c_*}-1)^2q^{j_*-1}+O(q^{j_*}),\\
\mu_i&=2+O(q),&\mathbb E_i\tau&=\tfrac12+O(q),&C_i&\longrightarrow0.
\end{aligned} \tag{18.3}
$$

All three displayed leading coefficients are positive.

Proof. It is useful to give exact identities that will also control the other endpoint. For a bounded variable $v>-1$, define the convex kernels

$$
f(v)=v-\log(1+v),\quad
g(v)=(1+v)\log(1+v)-v,\quad
h(v)=1+v/2-\sqrt{1+v}.
\tag{18.4}
$$

For any representation of the tilt as $h_k/p_k=(1+v_k)/(1+\bar v)$, where $\bar v=\mathbb E_pv_K$, direct substitution gives

$$
 d_0=\mathbb E_pf(v_K)-f(\bar v),\quad
 d_1=\frac{\mathbb E_pg(v_K)-g(\bar v)}{1+\bar v},\quad
 1-A=\frac{\mathbb E_ph(v_K)-h(\bar v)}{\sqrt{1+\bar v}}.
\tag{18.5}
$$

Here the symbol $h(v)$ is the scalar kernel in (18.4), distinguished by its argument from the gap masses $h_k$.

For this endpoint set $v_k=r_k/r_1-1$. It vanishes for $k<j_*$ and equals $c_*-1$ at $j_*$. The analytic generating series, whose coefficients are bounded constants times $k^n$, give $Z_n(q)=q(1+O(q))$, $\bar v=O(q^{j_*-1})$, and for $F=f,g,h$,

$$
\mathbb E_pF(v_K)=j_*^n F(c_*-1)q^{j_*-1}+O(q^{j_*}).
\tag{18.6}
$$

For example, for $0<q\le q_0<1$, the tail starting at $j_*+1$ is bounded in absolute value by a constant times $q^{j_*+1}\sum_{v\ge0}(v+j_*+1)^n q_0^v$ before division by $Z_n$. This proves the stated uniform remainder on a sufficiently small endpoint interval. All three kernels vanish to second order at zero. Hence $F(\bar v)=O(q^{2j_*-2})=O(q^{j_*})$. Formula (18.5) yields the gap divergences and affinity; division by $\mu_i=2+O(q)$ gives (18.3). The mean and waiting-time assertions follow from their polynomial-geometric moment formulas, whose $k=1$ term dominates.

For the initial cost, the $K$ marginal of $\lambda_0$ concentrates at one. Its tilt is $r_K/\mathbb E_{\lambda_0}r_K$, so boundedness of $r$ and $\log r$ gives $D(\lambda_0\Vert\lambda_1)\to0$. The same argument for the reciprocal tilt gives the reverse limit. Equation (17.10) then gives $C_i\to0$. Strict positivity of the kernels away from zero proves the coefficient assertions. $\square$

**Theorem 18.3 (Bulk, critical and summable residual regimes).** As $s=-\log q\downarrow0$, both means and initial waiting times satisfy

$$
\mu_i\sim\frac{n+1}{s},\qquad
\mathbb E_i\tau\sim\frac{n+2}{2s},\qquad C_i\longrightarrow0.
\tag{18.7}
$$

If $2d<n+1$, set

$$
V_{n,d}=\frac{\Gamma(n-2d+1)}{\Gamma(n+1)}
-\left(\frac{\Gamma(n-d+1)}{\Gamma(n+1)}\right)^2>0.
\tag{18.8}
$$

Then

$$
 I_0\sim I_1\sim\frac{a_*^2V_{n,d}}{2(n+1)}s^{2d+1},\qquad
 1-A\sim\frac{a_*^2V_{n,d}}8s^{2d}.
\tag{18.9}
$$

If $2d=n+1$, then

$$
 I_0\sim I_1\sim\frac{a_*^2}{2(n+1)n!}s^{n+2}\log(1/s),\qquad
 1-A\sim\frac{a_*^2}{8n!}s^{n+1}\log(1/s).
\tag{18.10}
$$

If $2d>n+1$, put $v_k=r_k-1$ and

$$
 B_f=\sum_{k\ge1}k^nf(v_k),\quad
 B_g=\sum_{k\ge1}k^ng(v_k),\quad
 B_h=\sum_{k\ge1}k^nh(v_k).
\tag{18.11}
$$

These series are finite and strictly positive, and

$$
 I_0\sim\frac{B_f}{(n+1)n!}s^{n+2},\qquad
 I_1\sim\frac{B_g}{(n+1)n!}s^{n+2},\qquad
 1-A\sim\frac{B_h}{n!}s^{n+1}.
\tag{18.12}
$$

In particular nonzero residual alone does not select the cubic rate in (18.9).

Proof. The sum estimates needed for every remainder can be obtained directly. For any integer $b\ge0$,

$$
\sum_{k\ge1}k^be^{-sk}=b!s^{-b-1}(1+O(s)),\quad
\sum_{k\ge1}\frac{e^{-sk}}k=-\log(1-e^{-s})=\log(1/s)+O(s).
\tag{18.13}
$$

For the first assertion, apply the Riemann sum with mesh $s$ to $x^be^{-x}$ on $[0,\infty)$. Its derivative is integrable, and the sum of the errors on all mesh intervals is at most $s\int_0^\infty|(x^be^{-x})'|\,dx$ (with the same elementary bound for $b=0$). The integral is $b!$. The logarithmic identity follows by integrating the geometric series. For $b<-1$, the positive series $\sum k^be^{-sk}$ is bounded and tends to $\sum k^b$ by domination. These facts also justify upper bounds when a displayed coefficient is replaced by an absolute value.

Take $v_k=r_k-1$. Since $d\le n-1$, (18.2) and (18.13) give

$$
\bar v=\frac{a_*\Gamma(n-d+1)}{n!}s^d+o(s^d),\qquad
Z_n(e^{-s})\sim n!s^{-n-1}.
\tag{18.14}
$$

The polynomial expression for $H=k^n+R$ gives the same leading normalizer for $Z_H$. Applying (18.13) also to the numerators of $\mathbb E_iK$ and $\mathbb E_iK^2$ proves (18.7)'s moment assertions via (17.14). The length-biased laws assign vanishing mass to every fixed finite set of $k$ at this endpoint. Because $r_k\to1$ and $r,\log r$ are bounded, splitting at a fixed large $k$ shows that their expectations tend to $1,0$ respectively. The tilt argument of Theorem 18.2 and (17.10) therefore prove $C_i\to0$.

For $F=f,g,h$, Taylor's theorem on the compact interval containing all $v_k$ and zero gives

$$
 F(v)=b_Fv^2+O(|v|^3),\qquad
 (b_f,b_g,b_h)=(1/2,1/2,1/8).
\tag{18.15}
$$

The remainder constant is finite because $1+v$ is bounded away from zero. In the first regime, (18.13) gives

$$
\mathbb E_pv_K^2=
\frac{a_*^2\Gamma(n-2d+1)}{n!}s^{2d}+o(s^{2d}),\qquad
\mathbb E_p|v_K|^3=o(s^{2d}).
\tag{18.16}
$$

For clarity, the error in the first numerator is bounded by a constant times $\sum k^{n-2d-1}e^{-sk}$. It is of smaller order than $s^{-n+2d-1}$ even when that error sum is logarithmic. The cubic numerator is bounded by a constant times $\sum k^{n-3d}e^{-sk}$. According as $n-3d$ is above, at, or below $-1$, its normalized bound is $O(s^{3d})$, $O(s^{n+1}\log(1/s))$, or $O(s^{n+1})$; each is $o(s^{2d})$. Thus no small-gap Taylor remainder is discarded. Subtracting the Taylor term at $\bar v$ in (18.5) yields $b_Fa_*^2V_{n,d}s^{2d}+o(s^{2d})$. The constant $V_{n,d}$ is the variance of $X^{-d}$ for a Gamma variable $X$ with density $x^ne^{-x}/n!$. Its second moment is finite exactly under $2d<n+1$, and its variance is positive because this function is not almost surely constant. Division by the means proves (18.9).

In the critical regime, the quadratic numerator is $a_*^2\sum e^{-sk}/k+O(1)$. Consequently

$$
\mathbb E_pv_K^2=\frac{a_*^2}{n!}s^{n+1}\log(1/s)+O(s^{n+1}),\quad
\mathbb E_p|v_K|^3=O(s^{n+1}),\quad
\bar v^2=O(s^{n+1}).
\tag{18.17}
$$

The relative $O(s)$ normalizer error contributes $O(s^{n+2}\log(1/s))$, which is absorbed by the displayed remainder. Formula (18.15), followed by (18.5), now gives the critical constants and (18.10).

In the last regime, $k^nF(v_k)=O(k^{n-2d})$ is summable. Dominated convergence, without a Taylor replacement at any fixed small $k$, gives

$$
 \mathbb E_pF(v_K)=\frac{B_F}{n!}s^{n+1}+o(s^{n+1}).
\tag{18.18}
$$

Here $F(\bar v)=O(s^{2d})=o(s^{n+1})$, so (18.5) proves (18.12). At least one $v_k$ is nonzero, and each kernel is positive away from zero. This proves positivity of all $B_F$ and completes all three regimes. $\square$

**Theorem 18.4 (Matching necessary and sufficient deterministic record orders).** For every fixed admissible nonzero residual pair and fixed $\alpha\in(0,1/2)$,

$$
W^*_\alpha(q)=\Theta_{n,H,\alpha}(q^{1-j_*})\quad(q\downarrow0),
\tag{18.19}
$$

and, as $s=-\log q\downarrow0$,

$$
W^*_\alpha(q)=
\begin{cases}
\Theta_{n,H,\alpha}(s^{-(2d+1)}),&2d<n+1,\\
\Theta_{n,H,\alpha}(s^{-(n+2)}/\log(1/s)),&2d=n+1,\\
\Theta_{n,H,\alpha}(s^{-(n+2)}),&2d>n+1.
\end{cases}
\tag{18.20}
$$

The same orders hold if independent randomization is allowed in the decision. These are fixed-pair optimal orders for deterministic record lengths, not sharp minimax constants or optimal expected stopping times.

Proof. Since $b_\alpha>0$ and $C_0\to0$, (17.11) gives $W\ge b_\alpha/(2I_0)$ in a sufficiently small neighborhood of either endpoint. This holds for every permitted rule, including randomized ones. Theorems 18.2–18.3 give the lower orders.

For the upper orders use (17.17). Since $A\to1$ and $-\log A\sim1-A$, its $N$ is $O_\alpha((1-A)^{-1})$. At zero, both $\mu_i$ and $\mathbb E_i\tau$ remain bounded, hence its $W=O_\alpha((1-A)^{-1})$. At one, (18.7) gives $W=O_\alpha(s^{-1}(1-A)^{-1})$. Inserting the positive affinity asymptotics proves exactly the orders in (18.19)–(18.20), with a deterministic rule. In particular the proof uses an attainable deadline guarantee in addition to the information-rate converse.

For each fixed $W$, the two window laws converge to the same limit at both endpoints. At zero, their gap laws tend to $K=1$, their means tend to two, and their cylinder formulas tend to the half-half mixture of the two alternating phases. At one, the probability of any one in the window is at most $W/\mu_i\to0$, so both tend to the all-zero word. The alphabet of length-$W$ words is finite, hence these statements are convergence in total variation. The sum of two testing errors is at least $1-d_{\rm TV}(\mathsf P_0^W,\mathsf P_1^W)$, by summing the smaller of the two masses, and therefore tends to one. No finite record budget works uniformly over all $q\in(0,1)$ for any fixed $\alpha<1/2$, even when the rule knows $q$. $\square$


## 19. The rational ninth-degree observer and its resource profile

**Theorem 19.1 (Exact visible separation and a finite-record obstruction).** Take the actual rational center $P_c,S_c$ of (12.3), not the limiting root $\theta_*$, and set $H=H_c$. Write $\delta=\delta_9$ from (15.20). Then

$$
\begin{aligned}
r_1&=1+\delta,&r_2&=\frac{64000000000054585242730647}{64\cdot10^{24}},\\
r_1-r_2&=\frac{121392910145961}{64\cdot10^{24}}>0,&
a_*&=[k^8](H_c-k^9)=\frac{9914818609152}{8\cdot10^{24}}
=\frac{605152503}{488281250000000000000}.
\end{aligned} \tag{19.1}
$$

At every $q\in(0,1)$ the gap-one signal is positive:

$$
 h_1-p_1=\frac{q(r_1Z_9-Z_H)}{Z_9Z_H}
 =\frac{\mathsf P_1(101)}{\mathsf P_1(1)}
  -\frac{\mathsf P_0(101)}{\mathsf P_0(1)}>0.
\tag{19.2}
$$

For every $W\ge1$ there is also the information upper bound

$$
 D(\mathsf P_0^W\Vert\mathsf P_1^W)
 \le\frac{\delta^2\bigl(Z_8(q)+WZ_7(q)\bigr)}{2\bigl(Z_9(q)+Z_{10}(q)\bigr)}.
\tag{19.3}
$$

At $q=1/2$ the exact signal is

$$
 h_1-p_1=\frac{1040731346079192329}
 {11162059662694743670610553961701435710}.
\tag{19.4}
$$

Any decision from a deterministic record cap with both errors at most $1/4$, including an independently randomized one, must then have

$$
 W\ge305776485212150493333616781.
\tag{19.5}
$$

Proof. The coefficient vector (12.7) and Theorem 15.5 already provide the strictly positive residual and $1\le r_k\le1+\delta/k$, with equality $r_1=1+\delta$. Thus $r_k<r_1$ for every $k\ge2$. The first two evaluations use $H(1)=1+9E_0$ and $H(2)=512+9(e(0)+e(1))$. The top coefficient uses $\Delta(H-k^9)=9e$ and $[t^7]e=9914818609152/(9\cdot10^{24})$, so $8a_*=9[t^7]e$. These give (19.1) by rational arithmetic. Since every $p_k$ is positive, $c=\mathbb E_pr_K<r_1$, proving (19.2). Its cylinder interpretation follows directly from (15.8); it is an identity of model probabilities, not permission to query those probabilities as observations.

For (19.3), $r_k\ge1$ allows the Taylor bound with $\ell=1$. Its gap and initial interval versions give

$$
 d_0\le\tfrac12\mathbb E_p(r_K-1)^2
 \le\frac{\delta^2Z_7}{2Z_9},\qquad
 C_0\le D(\lambda_0\Vert\lambda_1)
 \le\frac{\delta^2(Z_7+Z_8)}{2(Z_9+Z_{10})}.
\tag{19.6}
$$

The first comparison replaces variance by the second moment about one; the second uses the length-biased $K$ marginal $(k+1)k^9q^k/(Z_9+Z_{10})$. Also $\mu_0=(Z_9+Z_{10})/Z_9$. Substitution in (17.10), including its $W-1$ transitions, gives (19.3).

Here is a finite rational way to verify the evaluations without an infinite numerical sum. Polynomial division of $\Delta(H-k^9)=9e$, with $H(0)=0$, gives

$$
H(k)-k^9=\frac1{35\cdot10^{24}}igl(
55800726477138k-224986136658885k^2+420664314485485k^3
-540138133491075k^4+518234977000797k^5
-254383031435085k^6+77668004560980k^7+43377331415040k^8\bigr).
\tag{19.7}
$$

Taking its forward difference and comparing the eight coefficients with $9e$ verifies this polynomial; its constant is zero. For every integer $j\ge0$, the rational functions $Z_j$ can be evaluated by

$$
 Z_0(q)=\frac q{1-q},\qquad
 Z_j(q)=\frac q{1-q}\left(1+\sum_{v=0}^{j-1}\binom jv Z_v(q)\right)\quad(j\ge1).
\tag{19.8}
$$

Indeed shift $k$ to $k+1$ in the defining series, expand $(k+1)^j$, and move $qZ_j$ to the left. Evaluating (19.7) by these power sums proves (19.4) and gives

$$
 (Z_7,Z_8,Z_9,Z_{10})(1/2)=(94586,1091670,14174522,204495126).
\tag{19.9}
$$

For $\alpha=1/4$, (17.11) gives a required divergence $\tfrac12\log3>1/2$. The last strict inequality follows from $e<3$, for example from the exponential series and $j!\ge2^{j-1}$ for $j\ge1$, with strict inequality for some terms. Hence (19.3) implies

$$
 W>\frac{218669648/\delta^2-1091670}{94586}.
\tag{19.10}
$$

The right side lies strictly between $305776485212150493333616780$ and $305776485212150493333616781$. Multiplication by the positive integer $94586\cdot2749658638697^2$ verifies these two comparisons exactly. Taking the next integer proves (19.5). This is a rigorous necessary bound, not a sharp optimum or an estimate of physical elapsed time. $\square$

**Corollary 19.2 (The ninth-degree endpoint constants and optimal orders).** Define the exact rational number

$$
 c_*:=\frac{r_2}{r_1}
 =1-\frac{121392910145961}{64(10^{24}+2749658638697)}\in(0,1).
\tag{19.11}
$$

For this fixed pair, as $q\downarrow0$,

$$
\begin{aligned}
 I_0&=256(c_*-1-\log c_*)q+O(q^2),\\
 I_1&=256(c_*\log c_*+1-c_*)q+O(q^2),\\
 1-A&=256(1-\sqrt{c_*})^2q+O(q^2).
\end{aligned} \tag{19.12}
$$

As $s=-\log q\downarrow0$,

$$
\begin{aligned}
 I_0&=\frac{a_*^2}{12960}s^3+O(s^4),&
 I_1&=\frac{a_*^2}{12960}s^3+O(s^4),\\
 1-A&=\frac{a_*^2}{5184}s^2+O(s^3),&
 \frac{a_*^2}{12960}&=
 \frac{4521105578853889}{38146972656250000000000000000000000000000000}.
\end{aligned} \tag{19.13}
$$

Consequently, for every fixed $\alpha\in(0,1/2)$,

$$
 W^*_\alpha(q)=\Theta_{H_c,\alpha}(q^{-1})\quad(q\downarrow0),\qquad
 W^*_\alpha(q)=\Theta_{H_c,\alpha}((-\log q)^{-3})\quad(q\uparrow1).
\tag{19.14}
$$

Proof. Equation (19.1) identifies $j_*=2$, $d=1$ and the nonzero $a_*$. Theorem 18.2 gives (19.12). For (19.13), (18.13) and the polynomial (19.7) give

$$
\mathbb E_pK^{-1}=s/9+O(s^2),\quad
\mathbb E_pK^{-2}=s^2/72+O(s^3),\quad
\operatorname{Var}_p(r_K)=a_*^2s^2/648+O(s^3),\quad
\mathbb E_p|r_K-1|^3=O(s^3).
\tag{19.15}
$$

The first two formulas are $Z_8/Z_9$ and $Z_7/Z_9$. In the variance, $r_k-1=a_*/k+O(k^{-2})$ and $Z_6/Z_9=O(s^3)$ bound every omitted cross term; the square of the mean must be subtracted. Also $\mu_i=10/s+O(1)$. Applying (18.5) and (18.15) gives the stated $O(s^3)$ gap-divergence and affinity remainders, and division by $\mu_i$ gives $O(s^4)$ in each rate. This proves the full remainders as well as the exact coefficient. The two-sided record orders are Theorem 18.4. Their multiplicative constants are not asserted to equal the reciprocals of the information-rate constants. $\square$

**Theorem 19.3 (A counting observer with the same ninth-degree endpoint orders).** For any $J\ge1$ let

$$
 u_J=\mathsf P_0(K\le J),\quad v_J=\mathsf P_1(K\le J),\quad
 \Delta_J=|v_J-u_J|,\quad
 V_J=\max\{u_J(1-u_J),v_J(1-v_J)\}.
\tag{19.16}
$$

Whenever $\Delta_J>0$, acquire $N$ complete gaps as in Theorem 17.4, count how many satisfy $K\le J$, and decide between the two binomial means at their midpoint. Each error before a deadline is at most $4V_J/(N\Delta_J^2)$. Thus, with

$$
 N=\left\lceil\frac{8V_J}{\alpha\Delta_J^2}\right\rceil,\qquad
 W=\left\lceil\frac2\alpha\max_i\mathbb E_iL_N\right\rceil,
\tag{19.17}
$$

and the same timeout default, both actual-record errors are at most $\alpha$.

For the rational center, $J=1$ works for every fixed $q$. It attains the $O_{H_c,\alpha}(q^{-1})$ record order at zero. Near one, the choice

$$
 J(q)=\left\lfloor\frac9{1-q}\right\rfloor
\tag{19.18}
$$

has $v_J-u_J>0$ for all sufficiently large $q<1$, and attains the $O_{H_c,\alpha}(s^{-3})$ order. After parameter preprocessing, the online control storage of this rule is

$$
 O\bigl(\log(J+2)+\log(N+2)+\log(W+2)\bigr)\text{ bits}.
\tag{19.19}
$$

It needs no retained raw record or independent randomization. This is an achievable control bound, not a memory lower bound.

Proof. The gap indicators after the first observed tick are iid Bernoulli variables with the indicated means. A midpoint error requires their sample mean to differ from its true mean by at least $\Delta_J/2$. Its variance is at most $V_J/N$. Chebyshev's inequality gives the asserted bound. The timeout is again bounded without conditioning on successful acquisition. Formula (19.17), together with Markov on $L_N$, allocates at most $\alpha/2$ to each of these two events.

At zero, (19.1)–(19.2) and power-series expansion give

$$
 u_1=1-512q+O(q^2),\quad
 v_1=1-512c_*q+O(q^2),\quad
 \Delta_1=512(1-c_*)q+O(q^2),\quad V_1\sim512q.
\tag{19.20}
$$

Thus (19.17) uses $N=O(q^{-1})$ and, since the mean cycle and initial wait are bounded, $W=O(q^{-1})$. The strict all-$q$ signal for $J=1$ was proved in Theorem 19.1.

For the other endpoint, let $F_b(x)$ denote the cumulative distribution of a Gamma variable of shape $b$ and rate one. The Riemann sums used in (18.13), now truncated at $sJ\to9$, give

$$
 u_J\longrightarrow F_{10}(9)\in(0,1),\qquad
 s^{-1}\mathbb E_p[K^{-1}\mathbf1_{K\le J}]\longrightarrow\tfrac19F_9(9).
\tag{19.21}
$$

The limits follow by integration of $x^9e^{-x}/9!$ and $x^8e^{-x}/9!$ over $[0,9]$; the moving endpoint changes a vanishing integral. The tilt identity yields exactly

$$
 v_J-u_J=
 \frac{\mathbb E_p[(r_K-1)\mathbf1_{K\le J}]-u_J\mathbb E_p(r_K-1)}c.
\tag{19.22}
$$

The $O(k^{-2})$ part of $r_k-1$ contributes at most a constant times $Z_7/Z_9=O(s^2)$. Therefore (19.15) and (19.21) imply

$$
 v_J-u_J=a_*s\,\frac{F_9(9)-F_{10}(9)}9+o(s)
 =a_*s\,\frac{e^{-9}9^9}{9\cdot9!}+o(s)>0
\tag{19.23}
$$

for sufficiently small $s>0$. The identity between the Gamma cumulative distributions follows by one integration by parts. Also $V_J\to F_{10}(9)(1-F_{10}(9))>0$. Thus $N=O(s^{-2})$ and, by (18.7), $W=O(s^{-3})$. These derivations prove the remainders needed for both endpoint order assertions.

For online implementation, keep a deadline/read counter, a counter for the number of completed gaps, a success count, and the current zero-run count saturated at $J+1$. Before the first one, only the deadline counter and a first-tick flag need updating. A later one closes one gap, updates the success count if its saturated count is at most $J$, and resets that count to zero. After $N$ such gaps compare the success count with the precomputed integer midpoint threshold; for $v_J>u_J$ this may be $\lceil N(u_J+v_J)/2\rceil$, assigning equality to label one. The opposite ordering reverses the comparison with a fixed tie convention. Integer counters and the threshold have precisely the sizes in (19.19). The deadline counter is an observer resource, not an uncharged clock supplied by the generator. An all-zero prefix or an unfinished gap at the deadline triggers the stated default. With ordinary binary counter and comparison operations, a conservative online bit-operation bound is

$$
 O\bigl(W\log((J+2)(N+2)(W+2))\bigr).
\tag{19.24}
$$

Keeping all observed bits for later use would require up to $W$ additional bits. $\square$

**Definition 19.4 (Effective inputs and separate resource coordinates).** The statistical theorems allow arbitrary fixed real $q,P,S$ satisfying their hypotheses. They do not treat an arbitrary known real as a finite input string. An explicit sufficient effectivity contract is rational $q\in(0,1)$, rational coefficients of $P,S$, and rational $\alpha\in(0,1/2)$, each supplied as binary integers with positive denominators. All computations below use these descriptions of the two promised models; no probability is read from the realized source.

Under this contract, $H$ is computed by its polynomial finite difference and zero constant, and (19.8) gives $Z_n,Z_H$, means and waiting-time means by rational arithmetic. The finite sums for $u_J,v_J$ are rational. Hence whenever their difference is nonzero, $N,W$ and the integer count threshold in (19.17) can be computed exactly. For the center one can always use $J=1$; for an endpoint implementation, (19.18) is also an exact rational computation and its signal can be checked before selection. If it is zero, use $J=1$. The positive asymptotic (19.23) proves that this fallback is unnecessary sufficiently near one. No cost-free evaluation of $\log q$ is needed for this counting implementation.

The general likelihood rule has an effective version too. Compute rational upper enclosures for

$$
 A\le\sum_{k=1}^M\sqrt{p_kh_k}+\sqrt{U_{M+1}V_{M+1}}.
\tag{19.25}
$$

Cauchy–Schwarz bounds the omitted tail. Rational interval bisection encloses each square root. Increasing $M$ and reducing the total enclosure width to zero eventually produces a rational $\overline A<1$, because $A<1$ and both tails tend to zero. Choose $N$ by rational comparisons until $\overline A^N\le\alpha/2$, then use the rational mean deadline in (17.17). This is a terminating preprocessing procedure at each rational input. A sharper deadline from (17.15) can instead use any rational $z\in(1,1/q)$; its powers, normalizers and bound are rational. The refinement count, rational operand lengths, all preprocessing storage and operations, and the integer descriptions of the selected parameters are paid separately; no uniform efficient preprocessing bound over this family is asserted.

In the likelihood rule, a completed gap contributes the exact rational factor

$$
 \frac{p_k}{h_k}=c\frac{k^n}{H(k)}.
\tag{19.26}
$$

The common $q^k$ cancels. Let $B$ bound the bit lengths of the precomputed normalizer and a common-denominator coefficient description of $H$, including the model description. For gaps $k\le W$, Horner evaluation and integer powers give factor numerator and denominator lengths $O(B+n\log(W+1))$. Write $L=O(B+n\log(W+1))$ for such a bound. Multiplying the $N$ factors without fraction reduction uses $O(NL)$ accumulator bits, in addition to the model and $O(\log(W+2)+\log(N+2))$ counter bits. Schoolbook multiplication of an $O(jL)$-bit accumulated product by an $O(L)$-bit factor costs $O(jL^2)$; Horner evaluation and powers cost $O(nL^2)$ per gap. Thus a conservative post-preprocessing bound is

$$
 O\bigl(W\log(W+2)+N(n+N)L^2\bigr)
\tag{19.27}
$$

bit operations, with arithmetic workspace charged. This bound is only an implementation upper bound. It is not a constant-memory real accumulator. The counting rule avoids this growing product online by charging its threshold computation in advance, and still attains both center endpoint orders.

The complete generating instruments for the center and for the exact ninth-degree law have complex memory dimension $D=6$ by Sections 11 and 15. That producer dimension, the observer's control and arithmetic workspace, parameter preprocessing, read count, optional raw-record storage, and termination protocol are different coordinates. Theorems 19.1–19.3 compare the observed laws of these actual instruments; they do not identify any of these observer resources with $D$ or prove an unconditional minimum generator dimension.

**Definition 19.5 (Supplier correspondence, classical ingredients and limits).** The mathematical contribution of Sections 17–19 is the residual-specific visible-information comparison, its finite-record converse and attainable protocol, the cancellation-sensitive endpoint record orders, and the exact rational-center consumer. The renewal and testing principles used inside the proofs are classical. The correspondence is as follows.

| Supplier | Input actually used here and boundary of reuse |
| --- | --- |
| This volume, Theorems 11.5 and 15.2–15.5; Definition 12.1 | Actual complete instruments, their own faithful stationary initializations and cylinders, the residual polynomial, and the rational center envelope. The finite center is not an exact residual-zero solution. |
| [Renewal closure and observable dependence](FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md), Definition 2.1 and Lemma 2.2 | Normalized stationary suspension and event-conditioned iid gaps; its Section 10.3 expressly supplies no finite-sample guarantee. The formulas above price acquisition from that stationary history. |
| [Visible tail phase rigidity and window limits](FIB_LEGAL_EDGE_LOAD_VISIBLE_TAIL_PHASE_RIGIDITY_AND_WINDOW_LIMITS.md), Sections 17–20 and 29–35 | Existing use of the stationary initial information term, projection from augmented paths, and acquisition of complete intervals in actual windows. Its four-state phase family and central-bit recovery task differ from the two monomial/residual laws and endpoint parameters here; its numerical bounds are not substituted. |
| S. Marzen and J. P. Crutchfield, *Informational and Causal Architecture of Discrete-Time Renewal Processes*, [arXiv:1408.6876v2](https://arxiv.org/html/1408.6876v2), Section III and Appendix A | Their interevent zero-count law $F(k)$ is $p_k$ or $h_k$, their survival $w(a)$ is $U_a$ or $V_a$, and their mean zero count plus one is $\mu_i$. The stationary age distribution $w(a)/(\mu+1)$ and hazard $F(a)/w(a)$ are the classical objects used in (17.12). Shannon entropy rate and the relative entropy between two laws are distinct quantities. |
| M. Zamparo, *Renewal model for dependent binary sequences*, *Journal of Statistical Physics* **187**, 5 (2022), [arXiv:2108.11293v2](https://arxiv.org/html/2108.11293v2), Theorem 2.1 and Proposition 2.1 | His interarrival $S_2$ is $K+1$, and his delayed first arrival $S_1$ is $\tau+1$ under the shift from indices starting at one to indices starting at zero. His stationarity condition is exactly $\mathsf P_i(\tau=a)=U_a/\mu_i$ or $V_a/\mu_i$; his binary-word probabilities retain both boundary tails and the all-zero case. Renewal laws and these cylinder formulas are not new claims. |
| J. Birrell, M. A. Katsoulakis and L. Rey-Bellet, *Quantification of Model Uncertainty on Path-Space via Goal-Oriented Relative Entropy*, [arXiv:1906.09282v4](https://arxiv.org/pdf/1906.09282v4), Section 5.4, equations (88)–(91) | Their semi-Markov rate is mean jump relative entropy divided by mean sojourn, with attribution there to Girardin and Limnios. Here the corresponding reward is $d_i$ and the cycle duration is $K+1$ with mean $\mu_i$. Their continuous-time density and ergodicity hypotheses are not imported into this discrete visible experiment; (17.4)–(17.8) directly prove its rate and boundary remainder. |
| Y. Polyanskiy and Y. Wu, [*Information Theory*, Chapter 7 notes](https://people.lids.mit.edu/yp/homepage/data/LN_fdiv.pdf), Theorems 7.2 and 7.5, equation (7.4) | Relative-entropy data processing, the minimum sum of two simple-testing errors, and squared Hellinger distance $2(1-A)$. The product affinity in Theorem 17.4 applies to the acquired Palm gaps; it does not posit independent visible bits. |

The supplied polynomial-growth result, Theorem 31.2 of [Product upper edge field stability and phase cut rank](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md), remains a separate structural supplier; no CP growth argument is repeated here. [Native nonlinear readout capacity](https://github.com/the-omega-institute/trureturing/blob/c329900c035f42d4c7ca3f4aa78ac5d43c04c2e7/docs/develop/theory/FIB_NATIVE_NONLINEAR_READOUT_CAPACITY_AND_MINIMAL_DIMENSION.md) permits a deterministic nonlinear readout of exact native relation coordinates. It supplies neither stochastic samples of this renewal experiment nor free exact-probability responses to its observer, so its readout capacity is not a substitute for (17.11) or (17.15).

These are ordinary paper derivations using the stated source conditions and cited classical methods, without a claim of Lean verification or worldwide novelty. The cited correspondences and bounded source comparison do not establish exhaustive repository or literature coverage. The endpoint orders are for a fixed pair of polynomials and a fixed risk; they do not give a uniform finite budget over $q$ or over nonzero residuals. Unknown-$q$ composite inference, sharp minimax constants, optimal expected stopping, optimal control storage, and efficient uniform preprocessing are not settled here. None of the bounds is an operator-, diamond- or hidden-state-distance estimate, a physical finite-precision or thermodynamic-cost statement, or a certificate for arbitrary hidden-dimensional attainment. Infinite-path identification, finite-confidence termination and finite zero-error certification retain the separate meanings proved in Section 17.

## 追加锚（本行以下为增补区）

## 20. Unknown parameter identification by paid conditional gap pairs

The fixed rational center of Section 19 admits a finite conditional statistic that removes the unknown geometric parameter. This section addresses that part of the unknown-$q$ boundary in Definition 19.5: it proves a single family-uniform risk guarantee with pointwise finite mean acquisition, effective deadlines on supplied compact bands, and the optimal deterministic-deadline order on bands approaching zero. Sections 17–19 retain their common-known-$q$ meanings. In particular their $q^{-1}$ order at zero is a different experiment from the composite $\epsilon^{-2}$ order below.

**Definition 20.1 (Two full nuisance families on the original history).** Throughout this section fix $H=H_c$ exactly as in (19.7), and put

$$
\begin{aligned}
F_0(k)&=k^9,&F_1(k)&=H(k),&Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,\\
f_{i,q}(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),&f_{i,q}(0)&=0,\\
\mu_i(q)&=\mathbb E_{i,q}(K+1),&
\beta_i(q)&=\frac{\mathbb E_{i,q}[K(K+1)]}{2\mu_i(q)}.
\end{aligned} \tag{20.1}
$$

Write $\mathsf P_{i,q}$ for the actual stationary binary law supplied by Theorems 11.5 and 15.3 with these weights. Positivity and the bound
$1\le r_k:=H(k)/k^9\le1+\delta_9/k$ are supplied by Theorem 15.5. The promise is membership in one of the two families $\{\mathsf P_{0,q}:0<q<1\}$ and $\{\mathsf P_{1,q'}:0<q'<1\}$. The opposing $q'$ is unconstrained by $q$; only an explicitly supplied band below restricts either parameter.

The only source actions remain consecutive read-next-bit and stop, beginning at a stationary time. The observer knows the two fixed rational polynomials and a rational risk allowance $0<\alpha<1/2$, but receives no value, approximation or oracle for the true parameter. Each source has its own stationary initialization. There are no resets, parallel copies, hidden ages, probability queries, skipped zeros or free conditional samples. The initial wait, rejected pairs and any unfinished interval at a deadline all count as reads. Rational allowances suffice for any prescribed positive real risk by choosing a smaller rational allowance. All logarithms below are natural.

**Theorem 20.2 (A finite positive shape certificate and its conditional mark).** Define

$$
\begin{aligned}
\chi&=\frac{r_1r_3}{r_2^2},&\lambda&=\frac{r_1}{r_2},\\
C_i&=F_i(2)^2+2F_i(1)F_i(3),&
\theta_i&=\frac{F_i(2)^2}{C_i},&
\eta_i(q)&=\frac{C_iq^4}{Z_i(q)^2}.
\end{aligned} \tag{20.2}
$$

Then $\chi>1$, $1<\lambda<2$ and $0<\theta_1<\theta_0<1$. The two full stationary families in Definition 20.1 are disjoint. For two independent complete gaps of either shape, the event $E=\{K_1+K_2=4\}$ has probability $\eta_i(q)>0$, and

$$
\mathsf P_{i,q}\big((K_1,K_2)=(k,4-k)\mid E\big)
=\frac{F_i(k)F_i(4-k)}{C_i}\quad(k=1,2,3).
\tag{20.3}
$$

Thus the conditional mark $Y=\mathbf1_{\{(K_1,K_2)=(2,2)\}}$ has the parameter-free Bernoulli mean $\theta_i$. In particular $C_0=301510$ and $\theta_0=131072/150755$.

Proof. Substituting $k=1,2,3$ in the fixed polynomial (19.7) gives the exact finite certificate

$$
\begin{aligned}
r_1&=\frac{1000000000002749658638697}{10^{24}},\\
r_2&=\frac{64000000000054585242730647}{64\cdot10^{24}},\\
r_3&=\frac{29160000000015267459958171}{2916\cdot10^{22}},\\
r_1r_3-r_2^2
&=\frac{520040714516414119558257878908551006355871}
{331776\cdot10^{48}}>0.
\end{aligned} \tag{20.4}
$$

These identities are verified by multiplying the displayed rational numbers and clearing positive denominators. They use no rounded coefficient. Equation (19.1) gives $r_1>r_2$, while $r_1=1+\delta_9<2$ and $r_2\ge1$, proving the assertion about $\lambda$.

For either nuisance value the positive gap probabilities obey

$$
\frac{f_{i,q}(1)f_{i,q}(3)}{f_{i,q}(2)^2}
=\frac{F_i(1)F_i(3)}{F_i(2)^2}
=\begin{cases}3^9/2^{18},&i=0,\\(3^9/2^{18})\chi,&i=1.\end{cases}
\tag{20.5}
$$

Both the powers of $q$ and the normalizers cancel. Hence no gap law in one family equals any gap law in the other. Equality of two stationary binary laws would imply equality of their gaps, since their cylinders give
$f_{i,q}(k)=\mathsf P_{i,q}(10^k1)/\mathsf P_{i,q}(1)$ and $\mathsf P_{i,q}(1)=1/\mu_i(q)>0$. This proves stationary disjointness. The ratio is an identity used in a proof, not an observation available to the controller.

The three ordered compositions of four have masses $F_i(k)F_i(4-k)q^4/Z_i(q)^2$. Summing and dividing proves (20.3), including its normalization. Also $\theta_i=(1+2F_i(1)F_i(3)/F_i(2)^2)^{-1}$, so (20.4) proves the strict ordering. Among pairs of positive gaps, sums two and three have only one unordered composition; their conditional laws are respectively a point mass and two equal masses. Sum four is the first such pair sum with a shape distinction. This is a statement about this conditional construction, not an observer minimality theorem. $\square$

**Theorem 20.3 (One parameter-free rule, uniform risk and finite paid mean).** Set the positive rational constants

$$
\Delta=\theta_0-\theta_1,\qquad
V=\max_{i=0,1}\theta_i(1-\theta_i),\qquad
M=\left\lceil\frac{8V}{\alpha\Delta^2}\right\rceil.
\tag{20.6}
$$

Read until the first actual one, at $\tau=\min\{t\ge0:X_t=1\}$. Partition all subsequent complete gaps consecutively into disjoint pairs $(K_1,K_2),(K_3,K_4),\ldots$. Accept a pair exactly when its sum is four and retain its mark from Theorem 20.2. Read every rejected pair through its closing tick. Stop at the tick closing the $M$th accepted pair. If $S$ is the sum of the $M$ retained marks, emit label zero exactly when

$$
S\ge\left\lceil M\frac{\theta_0+\theta_1}{2}\right\rceil;
\tag{20.7}
$$

otherwise emit label one. The two family-wise errors satisfy the separate bounds

$$
\sup_{0<q<1}\mathsf P_{0,q}(\text{label }1)\le\alpha/2,
\qquad
\sup_{0<q'<1}\mathsf P_{1,q'}(\text{label }0)\le\alpha/2.
\tag{20.8}
$$

The rule terminates almost surely at every fixed true parameter in either family. If $J_M$ is the number of complete pairs read through its last acceptance and $L$ is the number of actual bits read, then

$$
\begin{aligned}
L&=1+\tau+\sum_{j=1}^{J_M}(K_{2j-1}+K_{2j}+2),\\
\mathbb E_{i,q}J_M&=\frac{M}{\eta_i(q)},\qquad
\mathbb E_{i,q}L=1+\beta_i(q)+\frac{2\mu_i(q)M}{\eta_i(q)}<\infty.
\end{aligned} \tag{20.9}
$$

Proof. Theorem 17.4 derives from the actual stationary cylinders that $\tau$ is finite almost surely, has mean $\beta_i(q)$, and is independent of the iid complete gaps following that observed tick. Its argument applies to each actual law individually; it does not require knowledge of $q$ to acquire those gaps. Consequently the nonoverlapping pairs are iid. For a block consisting of $j-1$ rejected pairs followed by an accepted mark $y\in\{0,1\}$, its probability is

$$
(1-\eta_i(q))^{j-1}\eta_i(q)
\theta_i^y(1-\theta_i)^{1-y}\quad(j\ge1).
\tag{20.10}
$$

Multiplying this formula over successive blocks and summing over their positive integer lengths proves that retained marks are iid Bernoulli($\theta_i$), and the block lengths are iid geometric variables of mean $1/\eta_i(q)$. In particular $J_M$ is finite almost surely and has the mean in (20.9). Every gap has finite length almost surely, so the stated stopping tick exists.

A wrong midpoint decision entails $|S/M-\theta_i|\ge\Delta/2$, with (20.7) resolving ties. The Bernoulli variance bound used in Theorem 19.3 therefore gives an error at most $4V/(M\Delta^2)\le\alpha/2$. Its distribution is independent of the nuisance value, proving both suprema in (20.8), without equating their parameters.

To account for acquisition, put $B_j=K_{2j-1}+K_{2j}+2$. The event $\{J_M\ge j\}$ depends only on earlier pairs, and hence is independent of $B_j$. Tonelli and nonnegativity give

$$
\mathbb E_{i,q}\sum_{j=1}^{J_M}B_j
=\sum_{j\ge1}\mathsf P_{i,q}(J_M\ge j)\mathbb E_{i,q}B_j
=2\mu_i(q)\mathbb E_{i,q}J_M.
\tag{20.11}
$$

Pair duration is not assumed independent of that pair's acceptance. The predictable inclusion event is what justifies the product. Adding the first $\tau+1$ reads proves (20.9). Polynomial-geometric tails give finite $\mu_i(q),\beta_i(q)$, and $\eta_i(q)>0$, so the full expectation is finite for each fixed true parameter. Discarding a pair's statistic has not discarded its time cost. $\square$

**Theorem 20.4 (Effective deterministic deadlines on supplied compact bands).** Supply rational $0<a<b<1$ and promise that the true parameter lies in $[a,b]$ under either label, still independently across the two hypotheses. Define

$$
\begin{aligned}
\eta_{a,b}&=\min_{i=0,1}\frac{C_i a^4}{Z_i(b)^2}>0,&
\overline\mu_b&=\max_i\mu_i(b),&\overline\beta_b&=\max_i\beta_i(b),\\
\mathcal B_{a,b}&=1+\overline\beta_b+
\frac{2\overline\mu_b M}{\eta_{a,b}},&
W_{a,b}&=\left\lceil\frac{2\mathcal B_{a,b}}\alpha\right\rceil.
\end{aligned} \tag{20.12}
$$

Run Theorem 20.3 with at most $W_{a,b}$ reads; if unfinished, emit a fixed default label. This deterministic rule has each family-wise error at most $\alpha$ uniformly on the supplied band. Every quantity in (20.12) is computable by finite rational arithmetic from $a,b,H,\alpha$.

Proof. Positivity of the values $F_i(k)$ implies $Z_i(q)\le Z_i(b)$ for $q\le b$, regardless of signs in the monomial coefficient description of $H$. Thus $\eta_i(q)\ge\eta_{a,b}$ on the band. Differentiating an expectation under weights $w_kq^k$ with respect to $\log q$ gives $\operatorname{Var}(K)$ when the observable is $K$; all differentiations are justified by polynomial-geometric domination on compact subintervals of $(0,1)$. Apply this first with $w_k=F_i(k)$ to see that $\mu_i$ is nondecreasing. Apply it with $w_k=(k+1)F_i(k)$ to see that

$$
\beta_i(q)=\frac12
\frac{\sum_{k\ge1}k(k+1)F_i(k)q^k}
{\sum_{k\ge1}(k+1)F_i(k)q^k}
\tag{20.13}
$$

is nondecreasing too. Equation (20.9) now gives $\mathbb E_{i,q}L\le\mathcal B_{a,b}$. A wrong capped decision is contained in the union of a wrong uncapped decision and $\{L>W_{a,b}\}$. Markov's inequality bounds the latter probability by $\mathcal B_{a,b}/W_{a,b}\le\alpha/2$. This argument does not condition retained marks on finishing before the deadline. It includes no initial tick, an unfinished rejected pair, and an unfinished final gap at timeout.

For effectivity, writing each fixed $F_i$ in monomials expresses $Z_i$, $\sum kF_i(k)q^k$ and $\sum k^2F_i(k)q^k$ as finite rational combinations of $Z_j(q)$ for $j\le11$. Recurrence (19.8) evaluates them exactly at rational $b$. Their normalizers are positive by Definition 20.1. Rational maxima, minima and ceilings then compute (20.12). The true parameter itself need not be rational or represented. $\square$

**Proposition 20.5 (Finite controller and separate arithmetic resources).** The uncapped rule requires only a first-tick flag, pair phase, the first gap's category in $\{1,2,3,\ge4\}$, a current zero count saturated at four, an accepted-pair count and a mark count, together with the precomputed integers $M$ and the threshold (20.7). It uses $O(\log(M+2))$ online control bits in addition to the fixed model and risk descriptions. A capped rule adds $O(\log(W_{a,b}+2))$ bits. With binary arithmetic, conservative online operation bounds are

$$
O\bigl(L\log(M+2)\bigr)\quad\hbox{and}\quad
O\bigl(W_{a,b}\log((M+2)(W_{a,b}+2))\bigr),
\tag{20.14}
$$

respectively. These are attainable upper bounds, not optimal storage or computation claims.

Proof. Before the first one only the flag and, if present, the read counter are updated. Thereafter each zero updates the saturated counter. A tick closes a gap, saves its category or completes the current pair, and resets the zero counter. Exactly $(1,3),(2,2),(3,1)$ trigger acceptance; only $(2,2)$ increments the mark count. Pair phase advances after every completed pair, including rejected ones. Even when a category already forces rejection, the controller continues reading through both closing ticks before starting the next pair. No unbounded gap counter or trial-count register is needed. The accepted-pair and mark counts are at most $M$, and the final decision is an integer comparison. The uncapped rule stops only at the designated closing tick; the capped rule additionally stops after the actual read counter reaches its deadline, using the ordinary decision if that very read completes it and the default otherwise. These updates give the storage and operation bounds.

The constants in (20.2), (20.6), (20.7) and, when needed, (20.12) are preprocessed from finite binary numerator-denominator descriptions. All rational operand lengths, preprocessing workspace and operations, and the stored integers are charged separately. Positivity of $\Delta$ proves termination of this exact preprocessing without any approximation to a source probability or to $\log q$. No efficient bound uniform in the risk or band inputs is asserted. The rules require no independent random seed and retain no raw record. The generating instruments' existing complex dimension $D=6$ is a separate resource coordinate; it is not the observer's control storage or a physical running-time estimate. $\square$

**Lemma 20.6 (The unequal-parameter converse on actual histories).** Fix any $q,t\in(0,1)$ and put $p=f_{0,q}$, $h=f_{1,t}$, $U_a=\sum_{k\ge a}p_k$, $V_a=\sum_{k\ge a}h_k$, $\mu=\mathbb E_p(K+1)$ and $\widetilde\mu=\mathbb E_h(K+1)$. Define

$$
\begin{aligned}
d(q,t)&=D(p\Vert h),&I(q,t)&=d(q,t)/\mu,\\
\pi(a)&=U_a/\mu,&\widetilde\pi(a)&=V_a/\widetilde\mu,&
C(q,t)&=D(\pi\Vert\widetilde\pi),\\
\Lambda(k,a)&=p_k/\mu,&
\widetilde\Lambda(k,a)&=h_k/\widetilde\mu\quad(0\le a\le k).
\end{aligned} \tag{20.15}
$$

These divergences are finite, $d(q,t)>0$, and for every integer $W\ge1$,

$$
D(\mathsf P_{0,q}^W\Vert\mathsf P_{1,t}^W)
\le C(q,t)+(W-1)I(q,t),\qquad
C(q,t)\le D(\Lambda\Vert\widetilde\Lambda).
\tag{20.16}
$$

Consequently a decision with deadline $W$ and both errors at most $\alpha$ for this selected pair must satisfy

$$
b_\alpha:=(1-2\alpha)\log\frac{1-\alpha}\alpha
\le C(q,t)+(W-1)I(q,t).
\tag{20.17}
$$

This includes early stopping and common independent randomization. Interchanging the two laws gives the analogous bounds.

Proof. The age-chain projection and chain rule in Theorem 17.3 apply once their summability and terminal-tail conditions are checked for this pair. They cannot be imported from its bounded-common-$q$ premise. Here

$$
\log\frac{p_k}{h_k}
=\log\frac{Z_1(t)}{Z_0(q)}-\log r_k+k\log(q/t),
\tag{20.18}
$$

which need not be bounded in $k$, but has absolute value at most a constant times $k+1$. To check tails explicitly, for $0<v<1$ put $S_9(v)=\sum_{j\ge0}(j+1)^9v^j<\infty$. For $a\ge1$, $(a+j)^9\le a^9(j+1)^9$ and the center envelope imply

$$
\begin{aligned}
\frac{a^9q^a}{Z_0(q)}&\le U_a\le
\frac{a^9q^a S_9(q)}{Z_0(q)},\\
\frac{a^9t^a}{Z_1(t)}&\le V_a\le
\frac{(1+\delta_9)a^9t^a S_9(t)}{Z_1(t)}.
\end{aligned} \tag{20.19}
$$

Thus $|\log(U_a/V_a)|\le A+B a$ for finite constants depending on the fixed pair. Both $\sum_a(a+1)U_a$ and $\sum_k(k+1)^2p_k$ are finite. It follows that the gap, age and interval-position log-density ratios are absolutely integrable, that $U_{N+1}\log(U_{N+1}/V_{N+1})\to0$, and that the reset and advance log terms of the age chains are absolutely summable against their stationary transition masses. At age zero the advance is forced under both laws; the absent reset term is taken as zero.

In detail, if $Q,\widetilde Q$ are the two age transition kernels, summing their two branches through age $N$ gives exactly

$$
\begin{aligned}
\mu\sum_{a=0}^N\pi(a)D(Q(a,\cdot)\Vert\widetilde Q(a,\cdot))
={}&\sum_{a=1}^Np_a\log\frac{p_a}{h_a}
+U_{N+1}\log\frac{U_{N+1}}{V_{N+1}}
-U_0\log\frac{U_0}{V_0}.
\end{aligned} \tag{20.20}
$$

The last term is zero because $U_0=V_0=1$. The established bounds let $N$ tend to infinity, leaving $d(q,t)$. The two chains start in their own invariant laws $\pi,\widetilde\pi$, and their binary emissions are the actual stationary cylinders by the same construction as in Theorem 17.3. The chain rule for their $W$ states therefore gives $C(q,t)+(W-1)d(q,t)/\mu$. Projection to the visible word proves the first part of (20.16). Projection of interval-position to age proves the second. Strict positivity of $d$ follows from Theorem 20.2 and strictness of relative entropy for different positive probability laws. The Bernoulli-decision data-processing argument of (17.11) gives (20.17); adjoining the same independent seed does not change the divergence. Neither a bounded same-parameter log ratio nor the remainder $3\log\kappa$ of (17.5) is asserted here. Age and interval-position variables are only converse proof variables. $\square$

**Theorem 20.7 (The composite small-band deadline order).** Let $\mathcal W_\alpha([a,b])$ be the least integer cap for one deterministic rule that receives $H,\alpha,[a,b]$ and has both family-wise errors at most $\alpha$ on that band. It may stop early and is not supplied the true nuisance value. For the fixed $H$ of this section, as rational $\epsilon\downarrow0$ with $2\epsilon<1$,

$$
\mathcal W_\alpha([\epsilon,2\epsilon])
=\Theta_{H,\alpha}(\epsilon^{-2}).
\tag{20.21}
$$

The same order holds if the decision may use independent randomization. The constants depend on the fixed center and risk, and are not sharp minimax constants.

Proof. For the necessary bound choose the permitted unequal-parameter pair $p=f_{0,q}$, $h=f_{1,\lambda q}$, with $q>0$ small enough that $\lambda q<1$. Theorem 20.2 gives $1<\lambda<2$. With

$$
d_k=\frac{r_k}{r_1}\lambda^{k-1},\qquad
A(q)=\sum_{k\ge1}k^9q^{k-1},\qquad
B(q)=\sum_{k\ge1}k^9d_kq^{k-1},
\tag{20.22}
$$

we have $d_1=d_2=1$, $d_3=\chi>1$, and $p_k=k^9q^{k-1}/A(q)$, $h_k=k^9d_kq^{k-1}/B(q)$. In particular $h_2/h_1=p_2/p_1=512q$: changing the nuisance matches the first rare-gap odds exactly. The analytic expansions are

$$
\begin{aligned}
A(q)&=1+512q+19683q^2+O_H(q^3),\\
B(q)&=1+512q+19683\chi q^2+O_H(q^3),\\
\mathbb E_p\log d_K&=19683\log\chi\,q^2+O_H(q^3).
\end{aligned} \tag{20.23}
$$

Here is a remainder justification that includes the unbounded tilt. Fix $q_0>0$ with $\lambda q_0<1$. The envelope for $r_k$ gives $d_k\le(1+\delta_9)\lambda^{k-1}/r_1$ and $|\log d_k|\le A_0+B_0k$. After extracting $q^3$ from the terms $k\ge4$, the three tail series in (20.23) are bounded uniformly for $0<q\le q_0$ by convergent constant multiples of $\sum_{k\ge4}k^{10}(\lambda q_0)^{k-4}$. The denominator $A(q)$ is at least one. Expanding its reciprocal and the logarithms near one thus preserves the displayed remainders; all constants are for this fixed $H$.

It follows that, with $\gamma=19683(\chi-1-\log\chi)>0$,

$$
\begin{aligned}
d(q,\lambda q)&=\log\frac{B(q)}{A(q)}-\mathbb E_p\log d_K
=\gamma q^2+O_H(q^3),\\
I(q,\lambda q)&=\frac\gamma2q^2+O_H(q^3).
\end{aligned} \tag{20.24}
$$

The mean in the second line is $\mu_0(q)=2+O_H(q)$. To control the stationary initial information as well, the $K$ marginals of $\Lambda,\widetilde\Lambda$ in (20.15) have weights $a_kq^{k-1}$ and $a_kd_kq^{k-1}$, where $a_k=(k+1)k^9/2$. Conditional on $K=k$, both position laws are uniform on $\{0,\ldots,k\}$. Their divergence is therefore exactly the divergence of those marginals. Their two normalizers begin

$$
1+768q+39366q^2+O_H(q^3),\qquad
1+768q+39366\chi q^2+O_H(q^3).
\tag{20.25}
$$

The same calculation gives
$D(\Lambda\Vert\widetilde\Lambda)=2\gamma q^2+O_H(q^3)$: the first nonzero log-tilt term is $39366\log\chi\,q^2$. Its remainder is controlled as above with $k^{11}$ in place of $k^{10}$. Hence $C(q,\lambda q)=O_H(q^2)$ by (20.16), not by a common-$q$ variance bound. Since $b_\alpha>0$, (20.17) and (20.24) imply $W=\Omega_{H,\alpha}(q^{-2})$ for any rule handling this pair. More explicitly, sufficiently small $q$ has $C\le b_\alpha/2$ and $I\le\gamma q^2$, giving $W\ge1+b_\alpha/(2\gamma q^2)$. Set $q=\epsilon$; both $\epsilon$ and $\lambda\epsilon$ belong to $[\epsilon,2\epsilon]$. Every composite rule must handle this pair, proving the necessary band order also for randomized rules.

For sufficiency use the concrete deadline (20.12). The fixed positive coefficients at the first gap and convergent power series give, uniformly near zero,

$$
Z_i(q)=F_i(1)q(1+O_H(q)),\qquad
\mu_i(q)=2+O_H(q),\qquad
\beta_i(q)=\tfrac12+O_H(q).
\tag{20.26}
$$

With $a=\epsilon,b=2\epsilon$ this yields

$$
\eta_{\epsilon,2\epsilon}
=\min_i\frac{C_i}{4F_i(1)^2}\,\epsilon^2(1+O_H(\epsilon)).
\tag{20.27}
$$

The positive minimum is a fixed constant, $M$ depends only on $H,\alpha$, and the other terms of $\mathcal B_{\epsilon,2\epsilon}$ stay bounded. Thus $W_{\epsilon,2\epsilon}=O_{H,\alpha}(\epsilon^{-2})$, with both errors controlled for every parameter in the band. The deterministic rule supplies the upper bound for both decision classes. $\square$

**Proposition 20.8 (Achieved endpoint costs and the global time boundary).** For the particular uncapped rule of Theorem 20.3, with $M$ fixed by its risk,

$$
\begin{aligned}
\mathbb E_{i,q}L
&=\frac{4MF_i(1)^2}{C_i}\,q^{-2}(1+O_H(q))
&& (q\downarrow0),\\
\mathbb E_{i,e^{-s}}L
&=\frac{20M(9!)^2}{C_i}\,s^{-21}(1+O_H(s))
&& (s\downarrow0).
\end{aligned} \tag{20.28}
$$

The second line is an inefficiency of fixed-small-sum rejection, not an unknown-$q$ optimal-order assertion. No fixed finite deadline, and no uniformly finite mean read count, can support a two-family risk bound $\alpha<1/2$ on the entire open interval.

Proof. Near zero, (20.26) gives
$\eta_i(q)=(C_i/F_i(1)^2)q^2(1+O_H(q))$. Substitute in (20.9); its initial cost is bounded and gives a smaller relative error. Near one, the monicity and degree nine of both polynomials, with (18.13), give

$$
\begin{aligned}
Z_i(e^{-s})&=9!s^{-10}(1+O_H(s)),&
\mu_i(e^{-s})&=10/s+O_H(1),\\
\beta_i(e^{-s})&=11/(2s)+O_H(1),&
\eta_i(e^{-s})&=\frac{C_i}{(9!)^2}s^{20}(1+O_H(s)).
\end{aligned} \tag{20.29}
$$

For the waiting mean, the leading numerator in (20.13) is $11!s^{-12}$ and its denominator is $2\cdot10!s^{-11}$. All remaining polynomial terms have at least one lower power, so the remainders stated here follow from the same power-sum bounds. Formula (20.9) proves the second line of (20.28), including every rejected long pair. No sharp near-one composite cost is inferred.

The final paragraph of Theorem 18.4 already proves that, at either endpoint, each fixed-length same-$q$ pair of stationary window laws coalesces in total variation. These pairs lie inside the two composite families. The minimum sum of two errors tends to one, so no fixed deadline can make both errors at most any fixed number below $1/2$. For the mean assertion, suppose a uniformly $\alpha$-correct stopping rule had $B:=\sup_{i,q}\mathbb E_{i,q}L<\infty$. Choose $\alpha<\alpha'<1/2$ and an integer $W>B/(\alpha'-\alpha)$. Truncating that rule at $W$, with a fixed default on timeout, gives both family-wise errors at most $\alpha+B/W<\alpha'$, a contradiction. Independent randomization does not alter either argument. This excludes a uniformly bounded mean, while leaving the pointwise finite mean in (20.9) intact. $\square$

**Definition 20.9 (Supplier correspondence and remaining scope).** The new consumer consists of the exact certificate (20.4), its actually acquired conditional marks, the paid random acceptance count, and the unequal-nuisance comparison yielding (20.21). Conditional inference, stationary renewal structure, variance bounds, chain rules and data processing are classical ingredients. Their specific correspondence is:

| Supplier | Input used in this section and limit of the application |
| --- | --- |
| This volume, Theorems 11.5, 15.3, 15.5 and 17.4; equations (19.7)–(19.8) | The two actual stationary instruments, positive weights, the fixed rational $H$, iid complete gaps after the first observed tick, paid initial wait, and exact rational power sums. The conditional observer changes no source-generating construction. |
| This volume, Theorems 17.3, 18.4 and 19.3 | The age-chain and Bernoulli-decision mechanisms, endpoint coalescence and midpoint variance calculation. Lemma 20.6 supplies the unequal-parameter integrability missing from the common-$q$ version; no bounded common-$q$ likelihood remainder is transferred. |
| M. Zamparo, *Renewal model for dependent binary sequences*, *Journal of Statistical Physics* **187**, 5 (2022), [arXiv:2108.11293v2](https://arxiv.org/html/2108.11293v2), Theorem 2.1 and Propositions 2.1, 3.1 | His $S_2=K+1$ and $S_1=\tau+1$. The stationarity condition $\mathbb E[S_2]\mathsf P(S_1=s)=\mathsf P(S_2\ge s)$, boundary-tail cylinders and regeneration identify the classical renewal objects used here. They do not supply free acquired gaps. |
| M. Broniatowski and V. Caron, *Conditional inference in parametric models*, [arXiv:1202.0944v1](https://arxiv.org/pdf/1202.0944v1), Section 4.1, equations (9)–(11) | The classical principle is cancellation of a nuisance canonical parameter on conditioning on its sufficient statistic. Here the discrete weights embed as $k^9\exp\{\gamma\log r_k+\eta k\}$, with $\gamma\in\{0,1\}$ and $\eta=\log q<0$; bounded $\log r_k$ ensures normalization. Conditioning a pair on its sum cancels $\eta$. Equation (20.3) proves the finite discrete specialization directly; the paper's continuous-density approximations and Monte Carlo procedures are not imported. |
| Y. Polyanskiy and Y. Wu, [*Information Theory*, Chapter 7 author notes](https://people.lids.mit.edu/yp/homepage/data/LN_fdiv.pdf), Theorems 7.2, 7.5 and equation (7.15) | Relative-entropy data processing and minimum simple-testing sum of errors $1-d_{\rm TV}$. The composite lower bound selects one admissible cross-parameter pair; it does not assume that a simple-test achievability result solves composite inference. |
| [FIB atom statistical laws](FIB_ATOM_STATISTICAL_LAWS.md), Section 100, especially (100.8) | The existing effective-information Schur complement is for a separately specified regular experiment. It is not a premise of this finite conditional observer or its deadline bound, and no generic Fisher or LAN assertion is added here. |

The external passages specified above support only these correspondences; no unavailable conditional-inference theorem is a premise. The source-specific calculations are ordinary paper derivations, with no Lean, physical implementation, worldwide novelty or exhaustive-search claim. The shape is the single fixed rational center $H_c$; arbitrary residuals, varying centers and uniformity as the residual vanishes are outside the conclusions. All cost constants may depend on this fixed $H$ and risk. Uniform risk in (20.8), pointwise finite expected reads in (20.9), and supplied-band deterministic deadlines in (20.12) have different quantifiers.

This resolves the stated fixed-center portion of the unknown-$q$ boundary in Definition 19.5. Sharp composite constants, optimal expected stopping, optimal observer storage, efficient uniform preprocessing, and an efficient unknown-$q$ near-one acquisition rule remain unsettled here. The $s^{-21}$ mean describes only this deliberately small conditional statistic. The known-$q$ orders in (19.14) remain unchanged. Positive probabilities for every legal finite word also persist across arbitrary nuisance pairs, so Corollary 17.5's finite zero-error obstruction still applies; finite-confidence identification does not certify the model promise or exact probabilities. Producer dimension, physical precision, hidden-state comparison and thermodynamic resources retain their separate boundaries.

## 追加锚（本行以下为增补区）
## 21. The joint delay boundary and its rank-one limiting consumer

**Definition 21.1 (Fixed pair, normalizers and stationary laws).** Let $d_0,d_1$ be fixed globally nonnegative real polynomials, $d_0\ne0$. For $0<q<1$ and nonnegative integer gap counts, put

$$
P_i(k)=\sum_{t=0}^{k-1}d_i(t),\quad Z_i(q)=\sum_{k\ge0}q^kP_i(k),\quad
\gamma_{i,q}(k)=\frac{q^kP_i(k)}{Z_i(q)}.
$$

Assume $P_0(0)=\cdots=P_0(h-1)=0$, $A=P_0(h)>0$ for an integer $h\ge2$, and $a=d_1(0)>0$. For $\varepsilon>0$ let $d_\varepsilon=d_0+\varepsilon d_1$, with the analogous symbols $P_\varepsilon,Z_\varepsilon,\gamma_{\varepsilon,q}$. Write

$$
R=\frac{Aq^{h-1}}{\varepsilon a},\qquad
\alpha_R=\frac1{1+R},\qquad \beta_R=\frac R{1+R},\qquad
\bar\gamma_R=\alpha_R\delta_1+\beta_R\delta_h.
\tag{21.1}
$$

The equilibrium renewal law associated with a gap law $\gamma$ is written $\nu_\gamma$. Its interval mean and tails are

$$
\mu_\gamma=\sum_{k\ge0}(k+1)\gamma(k),\qquad S_\gamma(a)=\sum_{k\ge a}\gamma(k).
\tag{21.2}
$$

For a word with at least one tick, the stationary cylinder convention is

$$
\nu_\gamma(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
=\frac{S_\gamma(a)S_\gamma(b)}{\mu_\gamma}
 \prod_{j=1}^{r-1}\gamma(g_j),
\tag{21.3}
$$

and

$$
\nu_\gamma(0^N)=\frac1{\mu_\gamma}
 \sum_{k\ge N}(k-N+1)\gamma(k).
\tag{21.4}
$$

Here an interval with gap count $k$ has length $k+1$; the factor $k+1$ in (21.4) is the stationary length bias. All word indices are nonnegative integers, the empty product is one, and $N=0$ denotes the empty word. This is the finite-mean discrete renewal convention of [Marzen–Crutchfield, *Informational and Causal Architecture of Discrete-Time Renewal Processes*, arXiv:1408.6876v2, Section II.A and Appendix A](https://arxiv.org/pdf/1408.6876v2): their zero-count law $F(k)$ and tail $w(a)$ are $\gamma(k)$ and $S_\gamma(a)$ here, and their count mean plus one is the interval mean $\mu_\gamma$.

**Theorem 21.2 (Uniform first-hit scaling, stationary transfer and all cylinders).** For every integer $s\ge0$ there is a constant $C_s$, depending only on $(d_0,d_1)$, such that for $0<q\le\frac12$ and every $\varepsilon>0$,

$$
\sum_{k\ge0}(k+1)^s\left|\gamma_{\varepsilon,q}(k)-\bar\gamma_R(k)\right|\le C_s q.
\tag{21.5}
$$

There is a constant $C$ such that, for every window length $W\ge1$,

$$
 d_{\rm TV}\!\left(\nu_{\gamma_{\varepsilon,q}}^{(W)},
 \nu_{\bar\gamma_R}^{(W)}\right)\le\min\{1,CWq\}.
\tag{21.6}
$$

The same $O(q)$ estimate holds for the stationary interval-and-phase law, its length marginal, the initial forward-wait law $S_\gamma(a)/\mu_\gamma$, and the means. In particular, for any $q_n\to0$, $\varepsilon_n>0$ and integers $W_n\ge1$ with $W_nq_n\to0$, (21.6) gives convergence in total variation to the moving $W_n$-window law at $R_n=Aq_n^{h-1}/(\varepsilon_na)$. Consequently, if $q_n,\varepsilon_n\downarrow0$ and $R_n\to R_0\in[0,\infty]$, then every fixed cylinder converges to the law in (21.3)–(21.4) with

$$
\bar S_R(a)=\alpha_R\mathbf 1_{a\le1}+\beta_R\mathbf 1_{a\le h},\qquad
\bar\mu_R=2\alpha_R+(h+1)\beta_R
=\frac{2+(h+1)R}{1+R}.
\tag{21.7}
$$

At a stationary observation time the limiting interval type is length biased:

$$
\Pr(K^*=1)=\frac{2}{2+(h+1)R},\qquad
\Pr(K^*=h)=\frac{(h+1)R}{2+(h+1)R}.
\tag{21.8}
$$

For $N\ge0$ the limiting all-zero cylinder is

$$
\bar\nu_R(0^N)=\frac{\alpha_R(2-N)_++\beta_R(h+1-N)_+}{\bar\mu_R}.
\tag{21.9}
$$

Proof. Polynomial growth gives, for fixed $s$, constants $B_s$ such that
$P_i(k)\le B_s(k+1)^{B_s}$ after increasing $B_s$ if necessary. Since $P_0(h)=A$ and $P_1(1)=a$,

$$
Z_0(q)=Aq^hB_0(q),\qquad Z_1(q)=aqB_1(q),\qquad B_i(q)=1+O(q),
\tag{21.10}
$$

where the $O(q)$ bounds hold together with every fixed polynomial moment: the terms after the first positive index are bounded by a polynomial times a geometric series. Therefore

$$
\sum_k(k+1)^s|\gamma_{0,q}(k)-\delta_h(k)|=O(q),\qquad
\sum_k(k+1)^s|\gamma_{1,q}(k)-\delta_1(k)|=O(q).
\tag{21.11}
$$

Moreover

$$
\gamma_{\varepsilon,q}=\widetilde\beta_R\gamma_{0,q}+(1-\widetilde\beta_R)\gamma_{1,q},\qquad
\widetilde\beta_R=\frac{RB_0(q)}{RB_0(q)+B_1(q)}.
\tag{21.12}
$$

The factors $B_i$ stay between two positive constants for $q\le\frac12$, and
$|\widetilde\beta_R-\beta_R|\le Cq$ uniformly for $R\ge0$ (multiply the difference by the two denominators; the remaining factor is $R/(R+1)^2\le1/4$). Combining this with (21.11) proves (21.5).

The stationary interval-and-phase law assigns mass $\gamma(k)/\mu_\gamma$ to each phase $0\le a\le k$. Its total variation distance is bounded by the $s=1$ case of (21.5), and $|\mu_{\gamma_{\varepsilon,q}}-\bar\mu_R|=O(q)$. Summing phases gives the same bound for the length marginal. The forward-wait law has masses $S_\gamma(a)/\mu_\gamma$; summing $|S_\gamma-S_{\bar\gamma_R}|$ costs at most the first moment in (21.5), and the normalizer difference costs the same amount. Couple the initial interval and phase maximally, then couple each subsequent gap maximally and independently. A length-$W$ word uses at most $W$ post-tick gap draws, so a union bound gives (21.6). This also proves the stated $W=o(q^{-1})$ limit.

Equations (21.7)–(21.9) follow by inserting the two-point law into (21.2)–(21.4). The interval probabilities in (21.8) are $(k+1)\bar\gamma_R(k)/\bar\mu_R$, which proves the length-bias claim. At $R=0$ the limit is $\delta_1$; at $R=\infty$ read $(\alpha_R,\beta_R)=(0,1)$ and the limit is $\delta_h$. For the delayed square of Section 14, $h=m+1$, $A=(m!)^2$ and $a=1$, so $R=(m!)^2q^m/\varepsilon$: the three regimes $\varepsilon/q^m\to\infty$, $\varepsilon/q^m\to c\in(0,\infty)$ and $\varepsilon/q^m\to0$ give respectively $\delta_1$, $c\delta_1/(c+(m!)^2)+(m!)^2\delta_h/(c+(m!)^2)$, and $\delta_h$. $\square$

**Theorem 21.3 (Exact four-window response and the boundary scale).** Put

$$
M_i(q)=\sum_{k\ge0}(k+1)q^kP_i(k),\qquad E=\{1010,0101\}.
$$

Then

$$
\nu_{\gamma_{\varepsilon,q}}^{(4)}(E)
=\frac{2\varepsilon aq}{M_0(q)+\varepsilon M_1(q)},\qquad
\left.\partial_\varepsilon\nu_{\gamma_{\varepsilon,q}}^{(4)}(E)\right|_{0+}
=\frac{2aq}{M_0(q)}
=\frac{2a}{(h+1)A}q^{-(h-1)}(1+O(q)).
\tag{21.13}
$$

There is a constant $C$ such that

$$
\left|d_{\rm TV}\!\left(\nu_{\gamma_{\varepsilon,q}}^{(4)},
\nu_{\gamma_{0,q}}^{(4)}\right)-\frac{2}{2+(h+1)R}\right|\le Cq.
\tag{21.14}
$$

For every pair of sequences $q_n\in(0,1)$ and $\varepsilon_n>0$ with $q_n\to0$ and $\varepsilon_n\to0$, put $R_n=Aq_n^{h-1}/(\varepsilon_na)$. Then

$$
\left[\ \forall W\in\mathbb N_{\ge1},\quad
 d_{\rm TV}\!\left(\nu_{\gamma_{\varepsilon_n,q_n}}^{(W)},
 \nu_{\gamma_{0,q_n}}^{(W)}\right)\longrightarrow0\ \right]
\quad\Longleftrightarrow\quad
\frac{\varepsilon_n}{q_n^{h-1}}\longrightarrow0.
\tag{21.15}
$$

For $0<R<\infty$, the endpoint mixture identity (21.16) for four-symbol marginals does not extend to a mixture of the whole stationary endpoint processes: their five-symbol cylinder $10101$ differs.

Proof. By (21.3), each word in $E$ has probability $\gamma_{\varepsilon,q}(1)/\mu_{\gamma_{\varepsilon,q}}$; $P_\varepsilon(1)=\varepsilon a$ and $\mu_{\gamma_{\varepsilon,q}}=(M_0+\varepsilon M_1)/(Z_0+\varepsilon Z_1)$, giving (21.13). Also $M_0(q)=(h+1)Aq^h(1+O(q))$.

Let $\nu_1$ and $\nu_h$ be the stationary periodic laws with deterministic gap counts $1$ and $h$. Formula (21.3)–(21.4), checked according to the number of ticks in a four-symbol word, gives

$$
\nu_{\bar\gamma_R}^{(4)}
=\frac{2}{2+(h+1)R}\nu_1^{(4)}
 +\frac{(h+1)R}{2+(h+1)R}\nu_h^{(4)}.
\tag{21.16}
$$

Indeed $\nu_1^{(4)}$ is supported on $E$, while every word outside $E$ has the $\nu_h$ probability multiplied by $(h+1)R/[2+(h+1)R]$; this includes the all-zero word through (21.9). The supports of $\nu_1^{(4)}$ and $\nu_h^{(4)}$ are disjoint, so the distance in (21.16) from $\nu_h^{(4)}$ is exactly $2/[2+(h+1)R]$. Apply (21.6) to the perturbed law and (21.5) with $d_0$ to the boundary law to obtain (21.14).

To prove the forward implication in (21.15), suppose $\varepsilon_n/q_n^{h-1}\to0$, so $R_n\to\infty$, and fix any $W\ge1$. The boundary estimate (21.11), with its first moment, gives
$d_{\rm TV}(\nu_{\gamma_{0,q_n}}^{(W)},\nu_h^{(W)})\le C_0Wq_n$
by the interval-and-phase and subsequent-gap coupling in the proof of Theorem 21.2. Each length-$W$ cylinder in (21.3)–(21.4) for $\bar\gamma_R$ is a finite product or sum of $\alpha_R,\beta_R$, divided by $\bar\mu_R\ge2$. Thus it is continuous at $(\alpha_R,\beta_R)=(0,1)$ and converges to the corresponding $\nu_h$ cylinder as $R\to\infty$. Since $\{0,1\}^W$ is finite, this is convergence in total variation. Together with the actual general-window bound (21.6), the triangle inequality gives

$$
\begin{aligned}
 d_{\rm TV}\!\left(\nu_{\gamma_{\varepsilon_n,q_n}}^{(W)},
 \nu_{\gamma_{0,q_n}}^{(W)}\right)
 &\le (C+C_0)Wq_n+
 d_{\rm TV}\!\left(\nu_{\bar\gamma_{R_n}}^{(W)},\nu_h^{(W)}\right)
 \longrightarrow0.
\end{aligned}
$$

Conversely, agreement on every fixed window includes $W=4$. Equation (21.14) then forces $2/[2+(h+1)R_n]\to0$, hence $R_n\to\infty$, which is equivalent to $\varepsilon_n/q_n^{h-1}\to0$ because $A,a>0$.

For the asserted failure of process identification, (21.3) gives, when $0<R<\infty$,

$$
\bar\nu_R(10101)=\frac1{(1+R)[2+(h+1)R]},
$$
whereas the endpoint process mixture with the weights forced by (21.16) assigns $1/[2+(h+1)R]$ to this word: $\nu_1(10101)=1/2$ and $\nu_h(10101)=0$. The two quantities differ, proving the claim. $\square$

**Proposition 21.4 (Noncommuting limits, endpoint exclusion and the varying-family counterexample).** For each fixed $\varepsilon>0$ and $W\ge4$,

$$
\sup_{0<q<1}d_{\rm TV}\!\left(\nu_{\gamma_{\varepsilon,q}}^{(W)},
\nu_{\gamma_{0,q}}^{(W)}\right)=1,
\tag{21.17}
$$

and the supremum is not attained at positive $q$. Four symbols are minimal for this supremum-one conclusion: as $q\downarrow0$ the three-window distance tends to $h/(h+1)<1$, because both endpoint laws give positive mass to $010$; as $q\uparrow1$ both three-window laws tend to $\delta_{000}$. For fixed positive $q$ the two laws are continuous in $\varepsilon$ at zero.

Coefficientwise convergence of a varying perturbation is insufficient without a uniform envelope. Specifically, with

$$
 d_0(t)=t^2(t-1)^2,\qquad d_{1,\varepsilon}(t)=1+\varepsilon^{-3/4}t^2,\qquad q=\frac{\sqrt\varepsilon}{2},
$$

one has $h=3$, $A=4$, $a=1$, $R=1$, but $\gamma_{\varepsilon,q}\to\delta_2$ rather than $(\delta_1+\delta_3)/2$.

Proof. Since $d_\varepsilon(0)>0$, the perturbed endpoint as $q\downarrow0$ is the deterministic gap-one law; the boundary endpoint is the deterministic gap-$h$ law. Their four-symbol supports are disjoint, proving (21.17) by the limit. At every positive $q$, both laws assign positive mass to $0^W$, so their distance is strictly below one. The fixed-$q$ continuity is immediate from the positive normalizers. For $W=3$, the endpoint supports share $010$ with boundary mass $1/(h+1)$, giving distance $h/(h+1)$; the $q\uparrow1$ limit follows from the diverging interval mean. Extending continuously to the two endpoints and using positivity in the interior gives a maximum below one for each fixed pair.

For the varying family, the first three raw weights satisfy

$$
qP_\varepsilon(1)=\Theta(\varepsilon^{3/2}),\quad
q^2P_\varepsilon(2)=\tfrac14\varepsilon^{5/4}+O(\varepsilon^2),\quad
q^3P_\varepsilon(3)=\Theta(\varepsilon^{3/2}).
$$
For $k\ge3$, polynomial summation gives
$P_\varepsilon(k)\le C(k+1)^5+C\varepsilon^{1/4}(k+1)^3+C\varepsilon(k+1)$, so
$\sum_{k\ge3}q^kP_\varepsilon(k)=O(\varepsilon^{3/2})$. The $k=2$ term therefore dominates the normalizer, proving convergence to $\delta_2$. $\square$

**Definition 21.5 (The limiting two-gap law).** Fix $h\ge2$ and $0\le\alpha<1$, put $\beta=1-\alpha>0$, and let

$$
\gamma^*(1)=\alpha,\qquad \gamma^*(h)=\beta,\qquad \gamma^*(k)=0\ (k\notin\{1,h\}),
$$

with $S^*(a)=\sum_{k\ge a}\gamma^*(k)$ and

$$
\mu^*=2\alpha+(h+1)\beta.
\tag{21.18}
$$

**Theorem 21.6 (A complete rank-one instrument on $\mathbb C^{h+1}$).** On the orthonormal basis $e_0,\ldots,e_h$, set $x=e_0$, $f=e_h$, and define the real matrix $C$ by

$$
Ce_0=\sqrt\alpha\,e_h+\sqrt\beta\,e_1,
\qquad Ce_j=e_{j+1}\ (1\le j<h),
\qquad Ce_h=0.
\tag{21.19}
$$

Then $C^{h+1}=0$, $|f^*C^kx|^2=\gamma^*(k)$ for every $k\ge0$, and the vectors $C^kx$ for $0\le k\le h$ span $\mathbb C^{h+1}$. The Gramian

$$
Q=\sum_{k=0}^{h}(C^*)^kff^*C^k
$$

is positive definite and $x^*Qx=1$. With $G=Q^{1/2}$, define

$$
\xi=Gx,\quad \tau=\xi\xi^*,\quad E=G^{-1}ff^*G^{-1},\quad
L=GCG^{-1},\quad J=\xi f^*G^{-1},
\tag{21.20}
$$

and $\Phi(X)=LXL^*$, $\Psi(X)=JXJ^*$. Then

$$
L^*L+J^*J=I,\qquad
\Psi(X)=\tau\operatorname{Tr}(EX),\qquad
\Psi\Phi^k(\tau)=\gamma^*(k)\tau.
\tag{21.21}
$$

The series $R_0=\sum_{a=0}^{h}\Phi^a(\tau)$ is positive definite. Thus $\rho_*=R_0/\mu^*$ is a faithful mixed invariant density, and its cylinders are exactly (21.3)–(21.4) with $\gamma=\gamma^*$.

Proof. The path in (21.19) gives $C^kx=\sqrt\beta e_k$ for $2\le k\le h$, while $Cx=\sqrt\alpha e_h+\sqrt\beta e_1$; hence the stated weights and nilpotence. The rows $f^*C^k$, $0\le k\le h$, force a vector in the kernel of $Q$ to have first coordinate zero from $k=h$, last coordinate zero from $k=0$, and then every intermediate coordinate from the remaining rows. Thus $Q>0$. The same path vectors span: $C^hx=\sqrt\beta e_h$ isolates $e_h$, and then $Cx$ isolates $e_1$; the other $C^kx$ give $e_k$.

The finite Gramian identity $Q-C^*QC=ff^*$, the completion mechanism of Theorem 2.1, gives (21.21) after conjugation by $G^{-1}$. Since $x^*Qx=|f^*Cx|^2+|f^*C^hx|^2=\alpha+\beta=1$, $\xi$ is normalized. The reset formula follows from the outer product defining $J$. Reachability of the $C^kx$ gives positive definiteness of $R_0$, and telescoping gives $\operatorname{Tr}\Phi^a(\tau)=S^*(a)$ and $\operatorname{Tr}R_0=\mu^*$. More explicitly, $\Phi(R_0)=R_0-\tau$ and $\Psi(R_0)=\sum_k\gamma^*(k)\tau=\tau$, so $R_0/\mu^*$ is invariant. Applying $\Psi\Phi^a$ to this series gives the first factor $S^*(a)/\mu^*$, every later tick multiplies by $\gamma^*$ and resets to $\tau$, and a final zero run contributes $S^*(b)$. With no tick,
$\operatorname{Tr}\Phi^N(\rho_*)=(\mu^*)^{-1}\sum_{a\ge0}S^*(N+a)=(\mu^*)^{-1}\sum_{k\ge N}(k-N+1)\gamma^*(k)$,
which is (21.4). Thus (21.3) and (21.4) follow directly, including the empty word. The ordered CP word traces use the stationary convention of [Monras–Beige–Wiesner, *Hidden Quantum Markov Models and non-adaptive read-out of many-body states*, arXiv:1002.2337v2, equations (25)–(27)](https://arxiv.org/pdf/1002.2337v2). Here $\rho_*$ is the faithful mixed initialization and $\tau$ is the pure tick posterior. Every operator acts on the full complex matrix algebra; the real entries do not restrict the input states. $\square$

**Theorem 21.8 (Exact limiting memory minimum and the endpoint compression).** Any finite homogeneous binary CP instrument on a complex memory, with any mixed initial density and with every persistent quantum, classical or controller register counted in that memory, that reproduces all stationary cylinders of $\gamma^*$ has dimension at least $h+1$. The instrument in Theorem 21.6 attains this bound and has no-tick Choi rank one and tick Choi rank one. Thus the limiting law has exact memory minimum $h+1$ and no-tick Choi minimum one.

For $\alpha=1$ the law is $\delta_1$; it has the two-dimensional realization

$$
C=e_1e_0^*,\quad f=e_1,\quad x=e_0,\quad
L=C,\quad J=e_0e_1^*,\quad \tau=e_0e_0^*,\quad \rho_*=\tfrac12I_2,
\tag{21.22}
$$

with both Choi ranks one, and dimension and no-tick Choi rank are minimal.

For the fixed-polynomial family of Definition 21.1, along every joint sequence with $q_n,\varepsilon_n\to0$ and $R_n\to R_0\in[0,\infty]$, the stationary output limit therefore has no-tick Choi minimum one and memory minimum $h+1$ when $R_0>0$, and memory minimum two when $R_0=0$. In contrast, at every finite $0<q<1$ and $\varepsilon>0$ its no-tick Choi minimum is two, as for every polynomial law of Definition 16.5. These minima use the full competitor class of Definition 16.5, with the target cylinders replaced by those of $\gamma^*$ for the limit; all persistent registers and retained records influencing later outputs are counted.

Proof. In a competitor write its branches as $\widehat\Phi,\widehat\Psi$ and initial density $\widehat\rho$. The one-tick probability is $\nu=1/\mu^*>0$. Its actual post-tick state
$\tau_0=\widehat\Psi(\widehat\rho)/\nu$ is a density, and the stationary cylinders give, without invariance or a reset assumption,

$$
\operatorname{Tr}\widehat\Phi^k(\tau_0)
=\frac{\Pr(1,0^k)}{\Pr(1)}=S^*(k).
\tag{21.23}
$$

For $0\le\alpha<1$, (21.23) gives positive survival $S^*(h)=\beta$ and extinction $S^*(h+1)=0$ from this actual posterior. The dimension step is the classical finite-termination mechanism: [Yu–Ying, *Reachability and Termination Analysis of Concurrent Quantum Programs*, arXiv:1206.1935v1, Theorem 5, proof (1), pp. 10–11](https://arxiv.org/pdf/1206.1935v1), proves termination within the Hilbert-space dimension, including mixed inputs, for the sequential program $F(X)=\mathcal E(M_1XM_1^*)$. Its program interface uses a CPTP step $\mathcal E$ after a continuation measurement. The following kernel argument supplies the CP statement needed here without requiring the no-tick branch itself to be trace preserving.

Write $\widehat\Phi(X)=\sum_iK_iXK_i^*$ on $M_D(\mathbb C)$, put $H=h+1$, $Y_j=(\widehat\Phi^*)^j(I)$ and $V_j=\ker Y_j$. Positivity gives
$x\in V_{j+1}$ if and only if every $K_ix$ belongs to $V_j$. Starting from $V_0=\{0\}$, this identity implies $V_j\subseteq V_{j+1}$ by induction, and equality at one step makes the chain constant thereafter. Also
$\operatorname{Tr}\widehat\Phi^j(\tau_0)=\operatorname{Tr}(Y_j\tau_0)=0$
is equivalent to $\operatorname{ran}\tau_0\subseteq V_j$: both operators are positive and the trace is $\|Y_j^{1/2}\tau_0^{1/2}\|_{\rm HS}^2$. Thus (21.23) puts the actual posterior support in $V_H$ but not in $V_{H-1}$. No earlier equality is possible, so

$$
0=\dim V_0<\dim V_1<\cdots<\dim V_H\le D,
$$

which proves $D\ge h+1$ for arbitrary mixed, noninvariant, nonreset competitors.

The nilpotent-map formulation of this same intermediate step is [Bhat–Mallick, *Nilpotent Completely Positive Maps*, arXiv:1310.0591v1, Proposition 2.2 and Corollary 2.5](https://arxiv.org/pdf/1310.0591v1): a CP map is nilpotent of order at most the Hilbert-space dimension, provided it is nilpotent on the whole space in question. To verify that premise here, let
$U=\operatorname{span}\{K_w\operatorname{ran}\tau_0: w\text{ a finite no-tick Kraus word}\}$,
including the empty word. The equality
$0=\operatorname{Tr}\widehat\Phi^H(\tau_0)=\sum_{|w|=H}\|K_w\tau_0^{1/2}\|_{\rm HS}^2$
shows that every length-$H$ product kills $\operatorname{ran}\tau_0$, and consequently every longer product does too. Hence $U$ is invariant under all $K_i$, is spanned by words of length less than $H$, and every length-$H$ product kills $U$. The restricted CP map on $M(U)$, with Kraus operators $K_i|_U$, is therefore nilpotent; its order is exactly $H$ because $\widehat\Phi^{H-1}(\tau_0)\ne0$. The cited corollary applies on $U$, giving $H\le\dim U\le D$. The unused ambient no-tick map need not be nilpotent. Neither trace preservation nor a pure posterior is needed for this restriction argument.

Theorem 21.6 gives the upper bound and has one nonzero no-tick Kraus operator and one rank-one globally resetting tick, so both Choi ranks are one. Both branches have positive output probability and therefore cannot have Choi rank zero. For $\alpha=1$, the same kernel argument uses $S^*(1)=1$ and $S^*(2)=0$, with $H=2$, giving dimension at least two. The matrices in (21.22) satisfy $L^*L+J^*J=I_2$, and direct iteration gives the deterministic gap count one, $R_0=I_2$ and the faithful mixed stationary density $\rho_*=I_2/2$. A positive no-tick probability forces Choi rank at least one, so the endpoint minima follow.

Finally, $d_\varepsilon=d_0+\varepsilon d_1$ is a nonzero globally nonnegative polynomial for every $\varepsilon>0$. At each $0<q<1$, Theorem 16.9 applies with exactly the mixed-state competitor interface of Definition 16.5 and gives no-tick Choi minimum two. This reuses that theorem's positive-effect, mixed-seed recurrence parity obstruction, inherited from Theorem 6.3 and [Chapter 29, equations (29.3)–(29.6)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#29-the-original-sns-needs-two-unresolved-no-tick-kraus-alternatives), together with the attaining construction of Theorems 16.7–16.8; it also applies to every other polynomial law of Definition 16.5. By Theorem 21.2 the joint output limit has $\alpha=1/(1+R_0)$, interpreted as zero at $R_0=\infty$. Applying the two cases above gives the stated limiting memory minima and no-tick Choi minimum one. The convergence used here is convergence of stationary classical finite-cylinder probabilities; the finite-parameter and limiting instruments are separate realizations of those laws. $\square$

## 追加锚（本行以下为增补区）

## 22. All-sum conditional acquisition at the cubic near-one order

**Definition 22.1 (Fixed source, all pair sums and finite input).** Keep exactly the two stationary families, read-next-bit contract and fixed rational polynomial $H=H_c$ of Definition 20.1 and (19.7). In particular the opposing parameters $q$ and $q'$ are quantified separately. Write

$$
a=a_*=[k^8](H-k^9)=\frac{605152503}{488281250000000000000}>0,
\qquad \delta=\delta_9=\frac{2749658638697}{10^{24}},
\qquad U=(1+\delta)^2<2.
\tag{22.1}
$$

The supplied envelope is $1\le r_k=H(k)/k^9\le1+\delta/k$. Supply a rational $0<\alpha<1/2$. A prescribed real risk allowance is accommodated by a supplied positive rational allowance no larger than it; no arbitrary real input has a free finite encoding. All logarithms are natural, except explicitly marked binary logarithms used to specify integers.

For integers $t\ge2$ and $1\le k<t$, define

$$
\begin{aligned}
A_i(t)&=\sum_{k=1}^{t-1}F_i(k)F_i(t-k),&
c_{i,t}(k)&=\frac{F_i(k)F_i(t-k)}{A_i(t)},\\
w_t(k)&=r_kr_{t-k},&m_t&=\frac{A_1(t)}{A_0(t)},&
\ell_t(k)&=\frac{w_t(k)}{m_t},\\
d_{0,t}&=D(c_{0,t}\Vert c_{1,t}),&
d_{1,t}&=D(c_{1,t}\Vert c_{0,t}),&
\mathfrak d_i(q)&=\sum_{t\ge2}\frac{A_i(t)q^t}{Z_i(q)^2}d_{i,t}.
\end{aligned} \tag{22.2}
$$

Here $F_i,Z_i,\mu_i,\beta_i$ retain (20.1). The conditional cancellation used in Theorem 20.2, applied to any pair sum, identifies $c_{i,t}$ as the law of the first gap given the sum $t$, and $A_i(t)q^t/Z_i(q)^2$ as that sum's law. It also gives $m_t=\mathbb E_{c_{0,t}}w_t$, $c_{1,t}=c_{0,t}\ell_t$ and

$$
1\le w_t,m_t\le U,\qquad U^{-1}\le\ell_t\le U,\qquad
|\log\ell_t|\le\log U\le2\delta.
\tag{22.3}
$$

The functions in (22.2) specify statistics of actually completed pairs. They are not probability observations or access to a hidden age. No pair is discarded by the observer below. The stationary initial wait and every bit through the last closing tick are acquired consecutively on the same history.

**Theorem 22.2 (Finite endpoint bridge for the fixed residual).** Uniformly over integer $t\ge2$, with constants depending only on the fixed $H$,

$$
d_{i,t}=\frac{19a^2}{324t^2}+O_H(t^{-3})\quad(i=0,1).
\tag{22.4}
$$

For every $q\in(0,1)$, $0<\mathfrak d_i(q)<\infty$. As $s\downarrow0$,

$$
\mathfrak d_i(e^{-s})=\frac{a^2}{5832}s^2+O_H(s^3)
\quad(i=0,1).
\tag{22.5}
$$

The remainders include both extreme compositions of a pair and the entire unbounded sum distribution.

Proof. For nonnegative integer exponents put

$$
S_{b,c}(t)=\sum_{k=1}^{t-1}k^b(t-k)^c,\qquad
\mathsf B=\frac{(9!)^2}{19!}.
\tag{22.6}
$$

These are rational polynomials. One explicit coefficient construction starts with $Q_0(t)=t$ and

$$
Q_m(t)=\frac{t^{m+1}-\sum_{j=0}^{m-1}\binom{m+1}{j}Q_j(t)}{m+1}\quad(m\ge1).
\tag{22.7}
$$

Telescoping $(k+1)^{m+1}-k^{m+1}$ shows $Q_m(t)=\sum_{k=0}^{t-1}k^m$. Expand $(t-k)^c$ and use these polynomials, replacing $Q_0$ by $t-1$ if the zero exponent occurs in a sum starting at one. This constructs every $S_{b,c}$ and hence $A_i$ without an infinite summation.

For the positive exponents needed here, comparison of the mesh sum of $x^b(1-x)^c$ with its integral gives

$$
S_{b,c}(t)=\frac{b!c!}{(b+c+1)!}t^{b+c+1}+O_{b,c}(t^{b+c}).
\tag{22.8}
$$

Indeed the error of the normalized mesh sum is at most $t^{-1}\int_0^1|(x^b(1-x)^c)'|\,dx$; repeated integration by parts gives the displayed integral. Alternatively, the same leading coefficient follows from (22.7). These arguments supply explicit rational bounds: after the leading coefficient is removed, the sum of absolute polynomial coefficients bounds the remainder for $t\ge1$. In particular $A_0=S_{9,9}$ has leading coefficient $\mathsf B>0$ and is positive for every $t\ge2$.

Under $c_{0,t}$ put $u=1/K+1/(t-K)=t/[K(t-K)]$. For $j=1,2,3$ the exact identities and their consequences are

$$
\begin{aligned}
\mathbb E u^j&=\frac{t^jS_{9-j,9-j}(t)}{S_{9,9}(t)},\\
\mathbb E u&=\frac{38}{9t}+O(t^{-2}),&
\mathbb E u^2&=\frac{323}{18t^2}+O(t^{-3}),&
\mathbb E u^3&=\frac{1615}{21t^3}+O(t^{-4}),\\
\operatorname{Var}(u)&=\frac{19}{162t^2}+O(t^{-3}).
\end{aligned} \tag{22.9}
$$

For example the three leading coefficients are
$\mathsf B^{-1}(9-j)!^2/(19-2j)!$; the variance coefficient is $323/18-(38/9)^2=19/162$. Quotient expansions use a positive lower bound $A_0(t)\ge\mathsf B t^{19}/2$ for all sufficiently large $t$, obtainable from its coefficients. Enlarging constants covers the remaining finite set $2\le t<T$.

The estimates have not restricted $K/t$ away from zero or one. More explicitly, for $j\le3$ and $0<\eta\le1/2$ they give the uniform endpoint control

$$
t^j\mathbb E\!\left[u^j\mathbf1_{\{\min(K,t-K)\le\eta t\}}\right]
\le C_j\eta^{10-j}.
\tag{22.10}
$$

If $\eta t<1$ the sum is empty. Otherwise sum over $k\le\eta t$ and its reflection: the numerator is at most a constant times
$t^{2j}t^{9-j}\sum_{1\le k\le\eta t}k^{9-j}\le C t^{19}\eta^{10-j}$.
Divide by $A_0(t)\ge c t^{19}$, whose constant can again include the finite initial set. Thus the inverse moments and third remainder used below are uniformly integrable even at the extreme compositions.

Write $r_k=1+a/k+\rho_k$. The exact polynomial (19.7) gives $|\rho_k|\le B_2/k^2$, where $B_2$ is the sum of the absolute coefficients of $k^{-2},\ldots,k^{-8}$ in $r_k$. With $B=B_2+\delta^2/4$ and $D=\delta+\delta^2/2$, the envelope and $u\le2$ give, at every composition,

$$
w_t-1=au+e_t,\qquad |e_t|\le Bu^2,\qquad
0\le w_t-1\le Du.
\tag{22.11}
$$

For the first bound use $k^{-2}+(t-k)^{-2}\le u^2$ and $1/[k(t-k)]\le u^2/4$; the product of the two residuals is at most $\delta^2/[k(t-k)]$. Hölder gives $(\mathbb E u)(\mathbb E u^2)\le\mathbb E u^3$. Consequently

$$
\begin{aligned}
|\operatorname{Cov}(u,e_t)|&\le2B\mathbb E u^3,\\
\operatorname{Var}(e_t)&\le B^2\mathbb E u^4\le2B^2\mathbb E u^3,\\
\operatorname{Var}(w_t)&=a^2\operatorname{Var}(u)+O_H(t^{-3}),&
\mathbb E|w_t-1|^3&=O_H(t^{-3}).
\end{aligned} \tag{22.12}
$$

To handle both divergence directions, set $v=w_t-1\ge0$, $\bar v=\mathbb E v$. Their exact expressions are

$$
\begin{aligned}
d_{0,t}&=\log(1+\bar v)-\mathbb E\log(1+v),\\
d_{1,t}&=\frac{\mathbb E[(1+v)\log(1+v)]-(1+\bar v)\log(1+\bar v)}{1+\bar v}.
\end{aligned} \tag{22.13}
$$

Taylor's formula on $[0,U-1]$ bounds the remainders after the quadratic terms by $v^3/3$ for $\log(1+v)$ and by $v^3/6$ for $(1+v)\log(1+v)$. Jensen gives $\bar v^3\le\mathbb E v^3$. In the second line replacing $1+\bar v$ in the quadratic denominator by one costs at most $(\bar v/2)\mathbb E v^2\le\mathbb E v^3/2$. Hence both lines equal $\tfrac12\operatorname{Var}(w_t)+O(\mathbb E v^3)$, with absolute remainder constants independent of $t$. Equations (22.9)–(22.12) prove (22.4), including $t=2,3$ where the divergences vanish. Bounds (22.3) prove finiteness, and the strict sum-four certificate (20.4), whose sum has positive probability for every $q$, proves $\mathfrak d_i(q)>0$.

For the final averaging step the fixed polynomials are monic of degree nine, so

$$
A_i(t)=\mathsf B t^{19}+O_H(t^{18}),\qquad
Z_i(e^{-s})^2=(9!)^2s^{-20}(1+O_H(s)).
\tag{22.14}
$$

The latter is the power-sum estimate (18.13). For completeness, the rate used in this application follows by applying the mesh estimate to $x^m e^{-x}$ on $[0,\infty)$: its integrable derivative gives
$\sum_{n\ge1}n^m e^{-sn}=m!s^{-m-1}+O_m(s^{-m})$ for the positive integers in question. Thus a bound by $Ct^r$ can be summed over every $t\ge2$ with the corresponding $O(s^{-r-1})$ control. Multiplying (22.4) by (22.14) gives

$$
A_i(t)d_{i,t}=\mathsf B\frac{19a^2}{324}t^{17}+O_H(t^{16}).
\tag{22.15}
$$

Summing this bound over all $t\ge2$ against $e^{-st}$ and dividing by $Z_i(e^{-s})^2$ proves (22.5), since
$\mathsf B\,17!/(9!)^2=1/(19\cdot18)$.
In particular the corresponding inverse moments satisfy

$$
\mathbb E_{i,e^{-s}}T^{-2}=\frac{s^2}{19\cdot18}+O_H(s^3),
\qquad \mathbb E_{i,e^{-s}}T^{-3}=O_H(s^3).
\tag{22.16}
$$

Every fixed small sum contributes $O_H(s^{20})$; the full remainder sum is $O_H(s^3)$ after normalization, including arbitrarily large sums. The beta density $x^9(1-x)^9/\mathsf B$ and gamma density $y^{19}e^{-y}/19!$ explain the constants in (22.9) and (22.16). The finite sums and their bounds establish the required inverse-moment bridge; weak convergence is not used to integrate an unbounded score. $\square$

**Theorem 22.3 (One finite-arithmetic rule with full-family confidence and finite paid mean).** Let $h$ be the least nonnegative integer with $2^{-h}\le\alpha/2$, and set

$$
p_j=2\lceil\log_2(j+1)\rceil+2\quad(j\ge1),
\qquad R_\alpha=h+2+2\delta.
\tag{22.17}
$$

The ceiling is computed by integer comparisons with powers of two. Read until the first actual tick at $\tau$, then partition all subsequent complete gaps consecutively into disjoint pairs. At pair $j$'s closing tick set $t_j=K_{2j-1}+K_{2j}$ and compute a dyadic number $\widehat Y_j$ of denominator $2^{p_j}$ satisfying

$$
|\widehat Y_j-\log\ell_{t_j}(K_{2j-1})|\le2^{-p_j}.
\tag{22.18}
$$

Use the deterministic exact-arithmetic construction in Proposition 22.6 below. Accumulate $\widehat S_n=\sum_{j\le n}\widehat Y_j$ exactly, increasing its binary denominator when $p_j$ increases. At the first completed pair $N$ with $|\widehat S_N|\ge h+1$, stop and emit label one at the upper boundary and label zero at the lower boundary. Until then the source action is always read-next-bit. The separate errors obey

$$
\sup_{0<q<1}\mathsf P_{0,q}(\text{label }1)\le\alpha/2,
\qquad
\sup_{0<q'<1}\mathsf P_{1,q'}(\text{label }0)\le\alpha/2.
\tag{22.19}
$$

For each fixed parameter in either family this rule terminates almost surely, and its actual paid reads obey

$$
\begin{aligned}
L&=1+\tau+\sum_{j=1}^N(K_{2j-1}+K_{2j}+2),\\
\mathbb E_{i,q}N&\le\frac{R_\alpha}{\mathfrak d_i(q)},&
\mathbb E_{i,q}L&=1+\beta_i(q)+2\mu_i(q)\mathbb E_{i,q}N<\infty.
\end{aligned} \tag{22.20}
$$

In fact this particular rule has $\mathbb E_{i,e^{-s}}L=\Theta_{H,\alpha}(s^{-3})$. This is an achieved mean order for this rule, not an optimum over all stopping rules. All positive integer moments of $L$ are finite at each fixed parameter.

Proof. The stationary delayed-renewal calculation of Theorem 17.4 gives the finite first tick, its mean $\mathbb E\tau=\beta_i(q)$, and independent iid complete gaps only after that observed tick. In the completed-pair filtration
$\mathcal G_n=\sigma(\tau,K_1,\ldots,K_{2n})$, put

$$
S_n=\sum_{j=1}^nY_j,\qquad Y_j=\log\ell_{t_j}(K_{2j-1}),\qquad M_n=e^{S_n}.
\tag{22.21}
$$

Under each $\mathsf P_{0,q}$, $M_n$ is a mean-one nonnegative martingale: the next conditional factor has expectation
$\sum_k c_{0,t}(k)\ell_t(k)=1$ at every sum, and averaging over that law's own sum distribution preserves one. Under each $\mathsf P_{1,q'}$, $M_n^{-1}$ is such a martingale, using $\sum_k c_{1,t}(k)/\ell_t(k)=1$. These statements do not identify $M_n$ with the unconditional likelihood ratio of any fixed opposing nuisance pair.

The precision schedule gives the pathwise bound

$$
|\widehat S_n-S_n|\le\sum_{j\ge1}2^{-p_j}
\le\frac14\sum_{j\ge1}\frac1{(j+1)^2}
\le\frac14\sum_{j\ge1}\frac1{j(j+1)}=\frac14.
\tag{22.22}
$$

An erroneous upper crossing under label zero entails $M_n\ge e^{h+3/4}$ for some $n$; an erroneous lower crossing under label one entails $M_n^{-1}\ge e^{h+3/4}$. Ville's nonnegative-martingale inequality bounds either event by $e^{-h-3/4}\le2^{-h}\le\alpha/2$. Its hypotheses hold at $\mathcal G_n$: for a finite horizon, stopping the nonnegative martingale at its first crossing gives the crossing probability at most the reciprocal barrier, and an increasing union removes the horizon. This use requires no assumption that $N$ is integrable.

The classical inequality is Lemma 1, equation (2.11), of S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via nonnegative supermartingales*, [arXiv:1808.03204v8](https://arxiv.org/html/1808.03204v8), attributed there to Ville. Here the exact products are proof variables; the controller stores only $\widehat S_n$. Nor is a product held constant inside a partially read pair asserted to be a martingale for the finer bit filtration. A boundary decision occurs only at a completed pair, and its closing tick is a stopping time of the actual bit history. The crossing-event bound therefore proves (22.19) for the actual emitted decision.

Under label $i$ orient the true score as $Z_n=(-1)^{1-i}S_n$. Its iid increments have mean $\mathfrak d_i(q)>0$ and absolute value at most $2\delta$. Before exit $|S_n|<h+5/4$ by (22.22); at exit the last true increment adds at most $2\delta$. Thus $|S_{N\wedge n}|\le R_\alpha$ for every $n$. Finite-sum independence, with $\{N\ge j\}\in\mathcal G_{j-1}$, yields

$$
\mathbb E_{i,q}Z_{N\wedge n}
=\mathfrak d_i(q)\sum_{j=1}^n\mathsf P_{i,q}(N\ge j)
=\mathfrak d_i(q)\mathbb E_{i,q}(N\wedge n)\le R_\alpha.
\tag{22.23}
$$

Monotone convergence establishes $\mathbb E N<\infty$ and almost-sure termination, before any unbounded stopping identity is used. Every acquired gap is finite almost surely. For $B_j=K_{2j-1}+K_{2j}+2$, the event $\{N\ge j\}$ depends only on earlier pairs and is independent of $B_j$. Tonelli therefore gives exactly

$$
\mathbb E\sum_{j=1}^N B_j
=\sum_{j\ge1}\mathsf P(N\ge j)\mathbb E B_j
=2\mu_i(q)\mathbb E N.
\tag{22.24}
$$

A pair's duration is not assumed independent of its own score or its own decision to stop. Adding the stationary initial $\tau+1$ reads proves (22.20), including all zeros and closing ticks.

The bounded stopped scores also allow dominated convergence in (22.23). On a correct exit $Z_N\ge h$, on an erroneous one $Z_N\ge-R_\alpha$. Equation (22.19) consequently gives

$$
\frac{c_\alpha}{\mathfrak d_i(q)}\le\mathbb E_{i,q}N
\le\frac{R_\alpha}{\mathfrak d_i(q)},\qquad
c_\alpha=(1-\alpha)h-\alpha(1+\delta)>0.
\tag{22.25}
$$

For positivity, $h\ge3$, $\alpha<1/2$ and $\delta<1/4$ suffice. Substitute (22.5) and the supplied moment expansions (20.29), namely $\mu_i(e^{-s})=10/s+O_H(1)$ and $\beta_i(e^{-s})=11/(2s)+O_H(1)$, to obtain the asserted mean order.

For the final integrability assertion fix $i,q$. If $X$ is one oriented increment, boundedness and $\mathbb E X=\mathfrak d_i(q)>0$ imply that $\mathbb E e^{-\theta X}=\rho<1$ for some $\theta>0$: differentiate its bounded-variable exponential moment at zero. On $\{N>n\}$, $Z_n<h+5/4$. Markov and independence give

$$
\mathsf P_{i,q}(N>n)\le e^{\theta(h+5/4)}\rho^n.
\tag{22.26}
$$

At fixed $q$, polynomial-geometric tails give all moments of $\tau$ and $B_1$. For each integer $p\ge1$, Minkowski applied first to finite sums, and predictable inclusion as in (22.24), give

$$
\left\|\sum_{j\ge1}B_j\mathbf1_{\{N\ge j\}}\right\|_p
\le\|B_1\|_p\sum_{j\ge1}\mathsf P(N\ge j)^{1/p}<\infty.
\tag{22.27}
$$

The geometric bound makes the series converge; monotone convergence of its nonnegative partial sums completes the argument. This establishes pointwise moments, without a uniform bound over the open parameter interval. $\square$

**Theorem 22.4 (Rational compact-band deadlines preserving the cubic order).** The same uncapped observer admits an effective deterministic cap on every supplied rational band $[u,v]\subset(0,1)$, with separately quantified family-wise errors at most $\alpha$ on that band. The following construction uses only finite rational arithmetic.

Using (22.7), form the fixed rational polynomials

$$
\begin{aligned}
B_i(t)&=\sum_{k=1}^{t-1}k(t-k)F_i(k)F_i(t-k),\\
P(t)&=B_0(t)A_1(t)-B_1(t)A_0(t),&Q(t)&=A_0(t)A_1(t).
\end{aligned} \tag{22.28}
$$

Their relevant degrees and leading coefficients are respectively

$$
\deg A_0=19,\quad [t^{19}]A_0=\mathsf B;\qquad
\deg P=39,\quad [t^{39}]P=\frac{a\mathsf B^2}{189};\qquad
\deg Q=38,\quad [t^{38}]Q=\mathsf B^2.
\tag{22.29}
$$

For a polynomial $f(t)=f_dt^d+\sum_{j<d}f_jt^j$ in this list, put $E_f(T)=\sum_{j<d}|f_j|T^{j-d}$. Choose $T_0$ by starting with $T=4$ and doubling until

$$
E_{A_0}(T)\le\mathsf B/2,\qquad
E_P(T)\le a\mathsf B^2/378,\qquad
E_Q(T)\le\mathsf B^2/2;\qquad T_0=T.
\tag{22.30}
$$

Set the positive fixed rational constants and band quantities

$$
\begin{aligned}
d_*&=\frac{a}{756},&g_*&=\frac{16\mathsf B d_*^2}{U^2},\\
G_{17}(u,T_0)&=\sum_{t\ge T_0}t^{17}u^t,&
\underline d_{u,v}&=\frac{g_*G_{17}(u,T_0)}{\max_i Z_i(v)^2},\\
\overline\mu_v&=\max_i\mu_i(v),&\overline\beta_v&=\max_i\beta_i(v),\\
\mathcal B_{u,v}&=1+\overline\beta_v+
\frac{2\overline\mu_v R_\alpha}{\underline d_{u,v}},&
W_{u,v}&=\left\lceil\frac{2\mathcal B_{u,v}}\alpha\right\rceil.
\end{aligned} \tag{22.31}
$$

The infinite-sum notation here has the finite rational evaluation

$$
G_{17}(u,T_0)=u^{T_0}\sum_{j=0}^{17}\binom{17}{j}T_0^{17-j}R_j(u),
\qquad R_0(u)=\frac1{1-u},\quad R_j(u)=\sum_{n\ge1}n^ju^n\ (j\ge1),
\tag{22.32}
$$

where the monomial power sums $R_j$ are evaluated by (19.8). Run Theorem 22.3 for at most $W_{u,v}$ actual reads, giving its ordinary decision priority if that final read closes a crossing pair; otherwise emit a fixed default on timeout. Then

$$
\sup_{q\in[u,v]}\mathsf P_{0,q}(\text{label }1)\le\alpha,
\qquad
\sup_{q'\in[u,v]}\mathsf P_{1,q'}(\text{label }0)\le\alpha.
\tag{22.33}
$$

For fixed $H,\alpha$, on rational bands $[u,v]=[1-2\epsilon,1-\epsilon]$ as $\epsilon\downarrow0$,

$$
\underline d_{u,v}=\Theta_H(\epsilon^2),
\qquad W_{u,v}=O_{H,\alpha}(\epsilon^{-3}).
\tag{22.34}
$$

Proof. Let $b_t(k)=k(t-k)/t^2\in[0,1/4]$ and
$\Delta_t=\mathbb E_{c_{0,t}}b_t-\mathbb E_{c_{1,t}}b_t=P(t)/(t^2Q(t))$.
The exact identities $b_tu=1/t$, (22.9), and $\mathbb E_{c_{0,t}}b_t=S_{10,10}(t)/(t^2A_0(t))=5/21+O(t^{-1})$ imply

$$
\operatorname{Cov}_{c_{0,t}}(b_t,u)=-\frac1{189t}+O(t^{-2}).
\tag{22.35}
$$

The remainder in (22.11) has $\mathbb E|e_t|=O_H(t^{-2})$, while $b_t$ is bounded. Since $m_t=1+O_H(t^{-1})$,

$$
\Delta_t=-\frac{\operatorname{Cov}_{c_{0,t}}(b_t,w_t)}{m_t}
=\frac{a}{189t}+O_H(t^{-2}).
\tag{22.36}
$$

Here $B_i$ has degree 21 and leading coefficient $10!^2/21!$. The degree-40 terms in $P$ cancel; (22.14) and (22.36) give its nonzero degree-39 coefficient in (22.29). The other degree assertions follow directly. Thus all leading coefficients in (22.30) are positive. Each $E_f(T)$ decreases to zero as $T$ doubles, so the finite rational search terminates. For every real $t\ge T_0$, its inequalities imply

$$
A_0(t)\ge\tfrac12\mathsf B t^{19},\qquad
P(t)\ge\frac{a\mathsf B^2}{378}t^{39},\qquad
Q(t)\le2\mathsf B^2t^{38},\qquad
\Delta_t\ge d_*/t.
\tag{22.37}
$$

For a lower information bound valid in both directions, the second derivatives of $-\log x$ and $x\log x$ on $[1,U]$ are at least $U^{-2}$ and $U^{-1}$ respectively. Their Jensen gaps, and the divisor $m_t\le U$ in the second direction, give

$$
d_{i,t}\ge\frac{\operatorname{Var}_{c_{0,t}}(w_t)}{2U^2}.
\tag{22.38}
$$

Explicitly, subtract the tangent at $m_t$ and integrate the lower second-derivative bound, then average; the linear term disappears. Also $\operatorname{Var}(b_t)\le1/64$, since $|b_t-1/8|\le1/8$. Cauchy–Schwarz and $m_t\ge1$ yield
$\operatorname{Var}(w_t)\ge64m_t^2\Delta_t^2\ge64\Delta_t^2$.
Together with $A_i(t)\ge A_0(t)$ and (22.37), this proves

$$
A_i(t)d_{i,t}\ge g_*t^{17}\quad(t\ge T_0, i=0,1).
\tag{22.39}
$$

On the supplied band $q^t\ge u^t$ and $Z_i(q)\le Z_i(v)$, so summing (22.39) gives
$\mathfrak d_i(q)\ge\underline d_{u,v}>0$.
Omitting $t<T_0$ here is a lower-bound operation on nonnegative summands; their actual contributions and remainders were included in Theorem 22.2. Monotonicity of $\mu_i,\beta_i$, proved in (20.13), and (22.20) now give $\mathbb E_{i,q}L\le\mathcal B_{u,v}$. A wrong capped decision lies in the union of a wrong uncapped decision and $\{L>W_{u,v}\}$, whose latter probability is at most $\alpha/2$ by Markov. This proves (22.33), including timeout before the first tick or inside either gap of a pair. No conditional law is reconditioned on finishing before the deadline.

Equation (22.32) follows by writing $t=T_0+n$, expanding $(T_0+n)^{17}$, and summing each power of $n$ with (19.8). The two shape normalizers and the moment numerators in (22.31) use monomial power sums through degree 11. Thus the search, the bound and the ceiling are all finite rational calculations on the supplied inputs. The actual $q$ need not be represented or rational.

Finally (18.13), (20.29) and fixed $T_0$ give

$$
G_{17}(1-2\epsilon,T_0)\sim\frac{17!}{(2\epsilon)^{18}},\qquad
\max_i Z_i(1-\epsilon)^2\sim(9!)^2\epsilon^{-20}.
\tag{22.40}
$$

Their ratio is a positive constant times $\epsilon^2$, while $\overline\mu_{1-\epsilon}$ and $\overline\beta_{1-\epsilon}$ are $O_H(\epsilon^{-1})$. Substitution in (22.31) proves (22.34). $\square$

**Theorem 22.5 (Source-specific unequal-nuisance converse and matching deadline order).** For the composite cap optimum $\mathcal W_\alpha$ of Theorem 20.7,

$$
\mathcal W_\alpha([1-2\epsilon,1-\epsilon])
=\Theta_{H,\alpha}(\epsilon^{-3})\quad(\epsilon\downarrow0).
\tag{22.41}
$$

This holds for deterministic rules and for rules using common independent randomization. It concerns deterministic deadlines with the stated band promise, not a sharp minimax constant or an optimum expected stopping time. A permitted unequal-parameter pair supplying its necessary bound is

$$
q=e^{-s},\qquad q'=e^{-s+cs^2},\qquad c=a/90.
\tag{22.42}
$$

For this pair, in the notation of Lemma 20.6,

$$
\begin{aligned}
d(q,q')&=\frac{a^2}{6480}s^2+O_H(s^3),&
I(q,q')&=\frac{a^2}{64800}s^3+O_H(s^4),\\
C(q,q')&\le D(\Lambda\Vert\widetilde\Lambda)
=\frac{a^2}{8100}s^2+O_H(s^3).
\end{aligned} \tag{22.43}
$$

Proof. Relative to $p_s=f_{0,e^{-s}}$, the other gap law is the normalized exponential tilt by

$$
V_s(k)=\log r_k+cs^2k,\qquad
f_{1,q'}(k)=\frac{p_s(k)e^{V_s(k)}}{\mathbb E_{p_s}e^{V_s(K)}},\qquad
d(q,q')=\log\mathbb E_{p_s}e^{V_s(K)}-\mathbb E_{p_s}V_s(K).
\tag{22.44}
$$

The term linear in $k$ is unbounded. Its remainder must therefore be integrated against the actual geometric law. The fixed envelope and polynomial give

$$
0\le V_s(k)\le\delta/k+cs^2k,\qquad
\log r_k=a/k+e_k,\qquad |e_k|\le(B_2+\delta^2/2)k^{-2}.
\tag{22.45}
$$

The latter bound uses $0\le x-\log(1+x)\le x^2/2$ for $x\ge0$. Write $\mathcal Z_m(s)=\sum_{k\ge1}k^m e^{-sk}$ to distinguish monomial moments from shape indices. The power-sum estimate used in Theorem 22.2 gives

$$
\begin{aligned}
\mathbb E_{p_s}K^{-1}&=s/9+O(s^2),&
\mathbb E_{p_s}K^{-2}&=s^2/72+O(s^3),\\
\operatorname{Var}_{p_s}(K^{-1})&=s^2/648+O(s^3),&
\operatorname{Cov}_{p_s}(K^{-1},K)&=-1/9+O(s),\\
\operatorname{Var}_{p_s}(K)&=10s^{-2}+O(s^{-1}),&
\mathbb E_{p_s}K^{-4}&=O(s^4).
\end{aligned} \tag{22.46}
$$

For example $\mathbb E K^j=\mathcal Z_{9+j}(s)/\mathcal Z_9(s)$, and $K^{-1}K=1$ gives the covariance. The error $e_K$ has second moment $O_H(s^4)$, so Cauchy–Schwarz bounds its contribution to the variance of $a/K+cs^2K$ by $O_H(s^3)$. Therefore

$$
\begin{aligned}
\operatorname{Var}_{p_s}(V_s)
&=\left(\frac{a^2}{648}-\frac{2ac}{9}+10c^2\right)s^2+O_H(s^3)\\
&=\frac{a^2}{3240}s^2+O_H(s^3).
\end{aligned} \tag{22.47}
$$

For sufficiently small $s$, put $s'=s-cs^2\ge s/2$. Since $e^{V_s(k)}=r_ke^{cs^2k}\le(1+\delta)e^{cs^2k}$ and $(x+y)^3\le4(x^3+y^3)$ for nonnegative $x,y$,

$$
\mathbb E_{p_s}[V_s^3e^{V_s}]
\le4(1+\delta)\frac{\delta^3\mathcal Z_6(s')+c^3s^6\mathcal Z_{12}(s')}{\mathcal Z_9(s)}
=O_H(s^3).
\tag{22.48}
$$

All constants in this estimate are uniform on a sufficiently small $s$ interval; it includes both very small and arbitrarily large $k$. Also $\mathbb E V_s=O_H(s)$ and $\mathbb E V_s^2=O_H(s^2)$. Taylor's exponential remainder is bounded by $V_s^3e^{V_s}/6$, and the logarithm is then expanded at $1+O_H(s)$. Thus
$\log\mathbb E e^{V_s}-\mathbb E V_s=\tfrac12\operatorname{Var}(V_s)+O_H(s^3)$.
Equations (22.44)–(22.48) prove the first line of (22.43), using $\mu_0(e^{-s})=10/s+O(1)$ for the information per read.

For the stationary initial term, the interval-position law $\Lambda$ in (20.15) has $K$ marginal proportional to $(k+1)k^9e^{-sk}$ and, conditional on $K=k$, the uniform position on $\{0,\ldots,k\}$. The other interval-position law has the same conditional position and exactly the tilt $e^{V_s(k)}$ of this marginal. Its monomial moments are

$$
\mathbb E_*K^j=\frac{\mathcal Z_{10+j}(s)+\mathcal Z_{9+j}(s)}{\mathcal Z_{10}(s)+\mathcal Z_9(s)}.
\tag{22.49}
$$

For the powers used above this gives
$\operatorname{Var}_*(K^{-1})=s^2/900+O(s^3)$,
$\operatorname{Cov}_*(K^{-1},K)=-1/10+O(s)$,
$\operatorname{Var}_*(K)=11s^{-2}+O(s^{-1})$ and $\mathbb E_*K^{-4}=O(s^4)$.
The analogue of (22.48) replaces its numerator by
$\delta^3(\mathcal Z_7(s')+\mathcal Z_6(s'))+c^3s^6(\mathcal Z_{13}(s')+\mathcal Z_{12}(s'))$
and its denominator by $\mathcal Z_{10}(s)+\mathcal Z_9(s)$, with the same fixed prefactor. It is again $O_H(s^3)$. The same justified expansion gives

$$
D(\Lambda\Vert\widetilde\Lambda)
=\tfrac12\left(\frac{a^2}{900}-\frac{2ac}{10}+11c^2\right)s^2+O_H(s^3)
=\frac{a^2}{8100}s^2+O_H(s^3).
\tag{22.50}
$$

Projection to age gives the asserted bound on $C$ by Lemma 20.6. These are converse variables, not data supplied to the observer. In particular no common-$q$ bounded-likelihood estimate has been applied to the unbounded tilt.

Now choose $q=1-3\epsilon/2$ and $s=-\log q$. Equation (22.42) gives $q'-q=q(e^{cs^2}-1)=O_H(\epsilon^2)>0$. For all sufficiently small $\epsilon$, both $q,q'$ are in $[1-2\epsilon,1-\epsilon]$ and $q'<1$. Every rule covering the two independent nuisance ranges must handle this selected pair. The already established actual-history converse (20.17) gives

$$
0<b_\alpha\le C(q,q')+(W-1)I(q,q')
=O_H(\epsilon^2)+(W-1)O_H(\epsilon^3).
\tag{22.51}
$$

For small enough $\epsilon$ its initial term is at most $b_\alpha/2$, and its rate is at most a fixed positive constant times $\epsilon^3$. Hence $W=\Omega_{H,\alpha}(\epsilon^{-3})$. Lemma 20.6 includes early stopping and independent randomization. The deterministic q-free upper rule of Theorem 22.4 gives the opposite bound, proving (22.41). For an arbitrary fixed real allowance $0<\alpha<1/2$, use a supplied smaller positive rational allowance in the upper construction and the original $b_\alpha$ in the converse; the same order follows. $\square$

**Proposition 22.6 (Exact arithmetic, growing memory and separate preprocessing).** The rule in Theorem 22.3 and its capped version have implementations by finite binary integer arithmetic. Let $B$ count the fixed model and preprocessed polynomial descriptions, and let $B_\alpha$ count the supplied rational risk description. After $L$ reads put $D_L=1+B+B_\alpha+\lceil\log_2(L+2)\rceil$. The uncapped rule admits

$$
\begin{aligned}
\text{persistent control and retained descriptions}&=O(D_L)\text{ bits},\\
\text{temporary exact-arithmetic workspace}&=O(D_L^2)\text{ bits},\\
\text{online bit operations through }L\text{ reads}&=O(LD_L+ND_L^5),
\end{aligned} \tag{22.52}
$$

where $N$ in this bound denotes the number of completed pairs by that read. Under a supplied cap $W$, replace $L$ by $W$ and add its $O(\log(W+2))$ persistent counter bits; all retained input descriptions are charged. The resulting worst-case online work is $O(WD_W^5)$. For fixed $H,\alpha$, the caps of (22.34) therefore use $O(\log(1/\epsilon))$ persistent control bits and $O(\log^2(1/\epsilon))$ temporary workspace, in addition to any supplied band description retained after preprocessing. The uncapped online work has finite expectation at each fixed parameter.

Proof. Precompute $A_0,A_1$ by (22.7). Their fixed degree is 19, so at a pair $(k,l)$ its exact factor

$$
\ell=\frac{H(k)H(l)A_0(k+l)}{k^9l^9A_1(k+l)}
\tag{22.53}
$$

is obtained by a fixed number of Horner evaluations and integer multiplications after clearing fixed coefficient denominators. Numerators, denominators and evaluation intermediates have $\lambda=O(B+\log(k+l+2))$ bits. Positivity follows from the defining sums, regardless of signs in the monomial coefficients. There is no online enumeration of $k+l-1$ compositions.

For an exact positive rational $\ell$, set $z=(\ell-1)/(\ell+1)=u_0/v_0$, with $v_0>0$. By (22.3) and $U<2$, $|z|<1/3<1/2$. For target precision $p=p_j$ take $m=p+2$ and compute the rational partial sum

$$
T_m=2\sum_{r=0}^{m-1}\frac{z^{2r+1}}{2r+1},\qquad
|\log\ell-T_m|\le\frac{2|z|^{2m+1}}{(2m+1)(1-z^2)}
\le\frac43\,4^{-m}<2^{-p-1}.
\tag{22.54}
$$

The identity and bound follow by integrating the geometric series for $2/(1-z^2)$ from zero to $z$, with absolute values for negative $z$. Round $T_m$ to the nearest multiple of $2^{-p}$, resolving an exact rational tie by a fixed rule. Integer division determines this rounded number with error at most $2^{-p-1}$. It therefore satisfies (22.18), even if a real logarithm is arbitrarily close to a rounding boundary. No equality-sensitive refinement or real-logarithm oracle is involved.

Here is a denominator-controlled exact evaluation. Compute
$R_{m-1}=1/(2m-1)$ and then $R_r=1/(2r+1)+z^2R_{r+1}$ for $r=m-2,\ldots,0$, finally $T_m=2zR_0$. If $R_{r+1}=n/d$, take

$$
R_r=\frac{v_0^2d+(2r+1)u_0^2n}{(2r+1)v_0^2d}.
\tag{22.55}
$$

This recurrence uses only integer additions and multiplications; no reduction is required. Its final denominator is
$v_0^{2m-1}\prod_{r=0}^{m-1}(2r+1)$.
Intermediate $R_r$ lie between zero and $4/3$, so their numerator lengths are bounded by their denominator lengths plus a constant. Thus all these integers, the final signed numerator and the rounding division require

$$
M=O\bigl(m(\lambda+\log(m+2))+p\bigr)
\tag{22.56}
$$

bits of workspace. A constant number of such integers is live at once. Schoolbook integer multiplication and division use $O(M^2)$ bit operations, and there are $O(m)$ recurrence steps, giving the safe per-pair bound $O(m^3(\lambda+\log(m+2))^2)$, including factor evaluation and rounding. At a prefix of length $L$, $p,m=O(\log(L+2))$, which gives the workspace and per-pair bounds in (22.52).

The persistent controller retains the first-tick flag, pair phase, first completed gap, current zero count, pair index and signed dyadic score. All gap and pair counters are at most $L$. The precision schedule is nondecreasing, so raising the score denominator is an exact binary shift with no further error. Before exit $|\widehat S_n|<h+1$; the terminal update overshoots by at most $2\delta+2^{-p_n}$. Its numerator consequently has $O(p_n+\log(h+2))$ bits. These observations prove the persistent bound, including a fixed number of flags and descriptions. Other reads require at most $O(D_L)$ counter work; completed-pair reads also pay the rational calculation just bounded. No raw record, list of pair sums or independent random seed is stored.

In the uncapped rule these counters and precision lengths are genuinely unbounded over possible histories. A capped rule stops after $W$ reads, so counters need never exceed $W$; it never substitutes a saturated length into a scored completed pair. If the last read closes a pair it first performs that pair's arithmetic and ordinary decision, and only then applies a timeout default if needed. Temporary memory and arithmetic at that read are included in (22.52). A fixed number of integer registers is not a fixed number of states. A bounded likelihood value likewise would not justify bounded storage of an exact product; the rule uses the proved dyadic error invariant instead.

For explicit preprocessing costs let $B_{\rm in}$ be the total binary length of supplied band and risk fractions. Polynomial degrees in (22.7), (22.28) and (22.30) are bounded by 40. If the fixed-model coefficient descriptions have at most $B$ bits in total, the doubling search in (22.30) can be performed in
$O((1+\log(T_0+2))(B+\log(T_0+2))^2)$ schoolbook bit operations and $O(B+\log(T_0+2))$ workspace, up to absolute fixed-degree factors. Each comparison is rational after multiplying by $T^d$; operand lengths are $O(B+\log T)$. The finitely many coefficient-generation operations have the same fixed-degree rational-arithmetic interpretation and are separately included in $B$ and their preprocessing work.

After this fixed-model preparation, one conservative bound for rational band preprocessing is

$$
K_{\rm pre}=O\bigl(B+(T_0+20)(B_{\rm in}+\log(T_0+2))+1\bigr)
\tag{22.57}
$$

bits of workspace and $O((1+\log(T_0+2))K_{\rm pre}^2)$ bit operations, up to fixed-degree factors. Indeed binary exponentiation of $u^{T_0}$ has numerators and denominators of length $O(T_0B_{\rm in})$; (19.8), (22.31) and (22.32) require only fixed-degree rational operations in addition, including positive-denominator divisions, comparisons and ceilings. The integer $h$ is found by shifts and comparisons with the rational risk. Its value is at most $B_{\rm in}+2$, so its calculation and representation fit this bound. The output $W$ also fits within these operand lengths. Large intermediate fractions may be discarded once $W$ is retained; their creation and workspace have nevertheless been charged. These are terminating arithmetic upper bounds, not a claim of optimized preprocessing uniformly over varying centers.

Finally $N\le L$ and, for fixed inputs, $D_L$ grows logarithmically. Theorem 22.3 gives all integer moments of $L$, which dominate $L D_L^5$, proving finite expected online bit work at each fixed parameter. Read count, arithmetic work, preprocessing and storage are distinct resource coordinates. They do not imply a physical elapsed-time or thermodynamic bound, and are unrelated to the source instrument's existing dimension $D=6$. $\square$

**Definition 22.7 (Supplier correspondence and scope of the conclusions).** The source-specific conclusions are the finite residual-dependent bridge (22.4)–(22.16), the rational large-sum certificate (22.28)–(22.39), their use by the paid dyadic observer, and the unequal-nuisance expansion (22.43). Their classical proof inputs have the following correspondence.

| Supplier | Input and precise application |
| --- | --- |
| This volume, Theorems 15.5, 17.4, 20.2 and Lemma 20.6; (18.13), (19.7)–(19.8), (20.13), (20.29) | The fixed positive residual, actual delayed renewal and first-tick acquisition, strict sum-four separation, already proved actual-history off-diagonal converse, polynomial-geometric moments and monotonicity. The generic conditional cancellation and age-chain inequality are reused; the endpoint applicability and integrable unequal tilt are established here. |
| M. Broniatowski and V. Caron, *Conditional inference in parametric models*, [arXiv:1202.0944v1](https://arxiv.org/html/1202.0944v1), Section 4.1, (9)–(11) | The nuisance canonical parameter is $\eta=\log q$, its statistic is $k$, the shape parameter has values zero and one with statistic $\log r_k$, and the base weights are $k^9$. Pair-sum conditioning is the finite discrete sufficient-statistic calculation from Section 20. No continuous conditional approximation from that paper is needed. |
| M. Zamparo, *Renewal model for dependent binary sequences*, *Journal of Statistical Physics* **187**, 5 (2022), [arXiv:2108.11293v2](https://arxiv.org/html/2108.11293v2), Theorem 2.1 and Propositions 2.1, 3.1 | The correspondence is $S_2=K+1$, $S_1=\tau+1$, with $\mathbb E[S_2]\mathsf P(S_1=s)=\mathsf P(S_2\ge s)$. The initial stationary wait and regeneration after an observed tick match Theorem 17.4. This supplies no free initial gap or uncharged conditional draw. |
| Howard–Ramdas–McAuliffe–Sekhon, cited in Theorem 22.3, Lemma 1, (2.11) | Ville's bound is used on the two respective nonnegative products at completed-pair times. Dyadic approximations only certify inclusion of the error event in a true-product crossing event. |
| Y. Polyanskiy and Y. Wu, [*Information Theory*, Chapter 7 author notes](https://people.lids.mit.edu/yp/homepage/data/LN_fdiv.pdf), Theorems 7.2, 7.5 and (7.15) | Data processing and simple-testing error bounds are already consumed by Lemma 20.6 and Proposition 20.8. The composite converse selects the admissible pair (22.42); a simple known-parameter upper rule is not a composite upper rule. |

All constants are for this one fixed exact $H_c$ and the specified risk. The uniform error suprema on $(0,1)$, finite mean at each fixed parameter, and effective deterministic caps on supplied compact bands are different quantifiers. The global impossibility of a finite uniform cap or uniformly bounded mean in Proposition 20.8 remains applicable. The deadline order (22.41) and achieved mean order of Theorem 22.3 make no assertion of sharp constants, optimal expected stopping, optimal storage, or a fixed-state efficient observer. Varying centers and uniformity as the residual vanishes are outside these conclusions. The results are ordinary mathematical derivations; they assert neither Lean verification nor physical realization nor worldwide priority. The finite-confidence decision assumes the family promise and does not certify it or measure exact probabilities.

## 追加锚（本行以下为增补区）

## 23. Mean order forced by full-family confidence

**Definition 22.8 (Protocol class and proof-fixed timeout).** Keep the fixed rational $H=H_c$ from (19.7), and fix $0<\alpha<1/2$. A protocol in this section may have arbitrary persistent memory and a common independent random seed, but has the same $q$-free read-next-bit-or-stop rule for every nuisance value, starts from the stationary history, reads consecutive bits, pays for every zero, tick, initial wait, partial gap and pair, and emits its label internally. It terminates almost surely with finite pointwise mean $m_{i,q}:=\mathbb E_{i,q}L$. Its two separate promises are

$$
\sup_{0<q<1}\mathsf P_{0,q}(D=1)\le\alpha,
\qquad
\sup_{0<q'<1}\mathsf P_{1,q'}(D=0)\le\alpha.
\tag{22.58}
$$

Put

$$
\rho=\frac{1-2\alpha}{4},\qquad \beta=\alpha+\rho<\frac12,
\qquad b=(1-2\beta)\log\frac{1-\beta}{\beta}>0.
\tag{22.59}
$$

For a proof-fixed target $i\in\{0,1\}$ and a proof-fixed $q\in(0,1)$, set
$W=\max\{1,\lceil m_{i,q}/\rho\rceil\}$. Run the protocol through read $W$; retain its ordinary label if it stops by then, including on read $W$, and otherwise emit the predetermined label $1-i$. The index $i$ is fixed in this construction and is not supplied as a true label to the observer.

**Theorem 22.9 (Pointwise mean lower bound for every protocol).** Write

$$
R_j(q)=\sum_{k\ge1}k^jq^k,\qquad
A(q)=\frac{\delta_9^2R_8(q)}{2(R_9(q)+R_{10}(q))},\qquad
B(q)=\frac{\delta_9^2R_7(q)}{2(R_9(q)+R_{10}(q))}.
\tag{22.60}
$$

For every protocol satisfying Definition 22.8, every $i$ and every $q$,

$$
\begin{aligned}
m_{i,q}
&\ge \rho\,\frac{[b-A(q)-B(q)]_+}{B(q)}\\
&=\rho\left[
\frac{2b(R_9(q)+R_{10}(q))}{\delta_9^2R_7(q)}
-\frac{R_8(q)}{R_7(q)}-1\right]_+ .
\end{aligned}
\tag{22.61}
$$

Consequently, with $q=e^{-s}$, there are $c>0$ and $s_0>0$, depending only on $H_c$ and $\alpha$, such that

$$
\mathbb E_{i,e^{-s}}L\ge c\,s^{-3}
\qquad(0<s<s_0),
\tag{22.62}
$$

simultaneously for both labels, all protocols, and all nuisance points.

**Proof.** For the target family, the timeout event has probability at most
$\mathsf P_{i,q}(L>W)\le m_{i,q}/W\le\rho$ by the ordinary Markov inequality. Thus the capped rule's target error is at most $\beta$, while the opposing-family error does not increase: on timeout the default label $1-i$ is correct for that family, and on an ordinary stop the original label is retained. The capped decision is one common measurable function of the $W$-prefix and the same-law independent seed.

For the selected pair $(\mathsf P_{0,q},\mathsf P_{1,q})$, write $\widehat D$ for this capped decision. If $i=0$, the timeout default is one, so its two errors, in family order $(0,1)$, are bounded by $(\beta,\alpha)$. If $i=1$, the timeout default is zero, so those errors are bounded by $(\alpha,\beta)$. Thus in either case $\mathsf P_{0,q}(\widehat D=0)\ge1-\beta$ and $\mathsf P_{1,q}(\widehat D=0)\le\beta$.

The forward Bernoulli data-processing bound of Theorem 17.3 therefore gives the same lower bound $b$ on $D(\mathsf P_{0,q}^{W}\Vert\mathsf P_{1,q}^{W})$ for either target choice. The target index selects $W$ and the timeout default only; the family order in this divergence is fixed. The cap is a constant in this comparison experiment, not an input to the original protocol. The source-specific forward prefix estimate (19.3), written with the fresh monomial sums in (22.60), now gives

$$
 b\le D(\mathsf P_{0,q}^{W}\Vert\mathsf P_{1,q}^{W})
 \le A(q)+W B(q).
\tag{22.63}
$$

Since $W\le m_{i,q}/\rho+1$, rearrangement yields (22.61), including the positive-part case. This is a prefix data-processing argument; no stopped information-rate or Wald substitution is used. By (18.13),

$$
A(e^{-s})\sim\frac{\delta_9^2}{180}s^2,\qquad
B(e^{-s})\sim\frac{\delta_9^2}{1440}s^3.
\tag{22.64}
$$

Hence the bracket in (22.61) is asymptotic to
$1440b\,\delta_9^{-2}s^{-3}$. For example, take
$c=720\rho b/\delta_9^2$ and then choose $s_0$ so that the bracket is at least half its leading term. These constants are fixed before the all-protocol and all-label quantifiers. The selected proof opponent is $q'=q$, which is admissible in the independent nuisance range; no equality is promised to, observed by, or supplied to the protocol. $\square$

**Corollary 22.10 (Per-family optimal mean order near one).** Let
$\mathfrak M_i(q)$ be the infimum of $\mathbb E_{i,q}L$ over all protocols of Definition 22.8. The q-free observer of Theorem 22.3, with a supplied smaller positive rational allowance when the requested allowance is real, and its resource accounting in Proposition 22.6 give the matching upper order. Therefore

$$
\mathfrak M_i(e^{-s})=\Theta_{H_c,\alpha}(s^{-3})\qquad(s\downarrow0),
\tag{22.65}
$$

for each $i=0,1$. This is an order statement for the per-family infimum. It does not say that every protocol has a cubic upper bound, and it gives no sharp constant or exact optimizer.

**Corollary 22.11 (Retuned common-band means).** Let $I_\varepsilon=[1-2\varepsilon,1-\varepsilon]$ be a supplied rational band, and let $\mathcal C_\varepsilon$ contain protocols with the same observation contract whose two risk suprema are required only over $I_\varepsilon$, while the protocol may be retuned from that band description. For all sufficiently small $\varepsilon$,

$$
\varepsilon\le -\log q\le4\varepsilon\quad(q\in I_\varepsilon).
\tag{22.66}
$$

Fix any $\mathcal A\in\mathcal C_\varepsilon$ and $q\in I_\varepsilon$, and repeat the proof of Theorem 22.9 on the selected pair $(\mathsf P_{0,q},\mathsf P_{1,q})$, with the admissible opponent $q'=q$. That proof uses only the two selected risk bounds at this $q$, both supplied by the band promises; no risk outside $I_\varepsilon$ enters. The same constants $c,s_0$ therefore apply independently of the band tuning. Using (22.66), take $c_B=c/64$ and $0<\varepsilon<\min\{1/4,s_0/4\}$. Then, uniformly over every $\mathcal A\in\mathcal C_\varepsilon$, every $q\in I_\varepsilon$ and both labels,

$$
\mathbb E_{i,q}^{\mathcal A}L\ge c_B\varepsilon^{-3}.
\tag{22.67}
$$

The same q-free observer from Theorem 22.3 supplies the upper bound $C_B\varepsilon^{-3}$ on this band. Thus both separate worst-band infima and the joint worst-band infimum satisfy

$$
\inf_{\mathcal A\in\mathcal C_\varepsilon}\sup_{q\in I_\varepsilon}\mathbb E_{i,q}^{\mathcal A}L
=\Theta_{H_c,\alpha}(\varepsilon^{-3}),
\qquad
\inf_{\mathcal A\in\mathcal C_\varepsilon}\sup_{i,q\in\{0,1\}\times I_\varepsilon}
\mathbb E_{i,q}^{\mathcal A}L
=\Theta_{H_c,\alpha}(\varepsilon^{-3}).
\tag{22.68}
$$

**Definition 22.12 (Correspondence and boundary of this append).** The finite-record data-processing step is Theorem 17.3; the prefix envelope is Theorem 19.1, equation (19.3); the sums in (22.60) use the power-sum estimates (18.13); and the matching upper rule and finite binary implementation are Theorem 22.3 and Proposition 22.6. The only truncation estimate introduced here is the proof-local Markov bound in the proof of Theorem 22.9. These supplier results are applied to the actual stationary, consecutively paid history and its common independent seed, with no hidden age, free completed gap, reset, or second source.

This append resolves the previously unstated optimal-mean order near $q=1$ for each full family and the specified common-band mean order. The deadline order in Theorem 22.5 is a different, already solved objective and is not used as a mean lower bound. All other limits in Sections 17–22 remain unchanged: there is no sharp constant, exact optimizer, minimum storage or arithmetic claim, physical or global-novelty claim, varying-$H_c$ or residual-uniform claim, and no stopped-information-rate substitution. The result is an ordinary paper consequence of the cited source statements, not a generic theorem chapter.

## 追加锚（本行以下为增补区）
