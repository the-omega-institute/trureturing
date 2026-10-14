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

## 15. Nonnegative anchored squares, exact delay and general real renewal instruments

**Definition 15.1 (Polynomial data and anchored pairs).** Let $d\in\mathbb R[t]$ be nonzero and globally nonnegative, of exact degree $2m$, where $m\ge0$, and write $\delta=[t^{2m}]d>0$. Put $\Delta v(t)=v(t+1)-v(t)$ and $\operatorname{fall}_j(t)=\prod_{i=0}^{j-1}(t-i)$, with $\operatorname{fall}_0=1$. A degree-bounded anchored pair for $d$ is a pair of real polynomials $p,s$ satisfying

$$
\deg p,\deg s\le m,\qquad s(0)=0,\qquad d=p^2+\Delta(s^2).
\tag{15.1}
$$

The zero polynomial is permitted in a degree bound. Positive orientation means $[t^m]p=\sqrt\delta$. Define the discrete integral polynomial by

$$
P(t)=\sum_{j=0}^{2m}\Delta^j d(0)\binom{t}{j+1},\qquad
\binom{t}{j}=\frac{\operatorname{fall}_j(t)}{j!}.
\tag{15.2}
$$

Throughout this section, a gap index is the number of zeros between successive ticks; the corresponding interevent duration is one larger. Adjoints are denoted by $\dagger$, and the star on a CP map denotes its trace dual. Real matrices act on the full complex matrix algebra, as in Definition 1.2.

**Theorem 15.2 (Closure at real roots, with constants and the zero boundary).** Every $d$ of Definition 15.1 has a positively oriented anchored pair. For every degree-bounded anchored pair,

$$
\begin{aligned}
\deg p&=m,\qquad ([t^m]p)^2=\delta,\\
\Delta P&=d,\qquad P(0)=0,\qquad
\deg P=2m+1,\qquad [t^{2m+1}]P=\frac{\delta}{2m+1},\\
P(k)&=s(k)^2+\sum_{j=0}^{k-1}p(j)^2
=\sum_{j=0}^{k-1}d(j)\quad(k\ge0).
\end{aligned}
\tag{15.3}
$$

The identity at $k$ is for every nonnegative integer $k$. Here $P$ is the unique polynomial with the displayed difference and anchor. For a positive constant $d=c$, the degree-bounded pairs are exactly $(\sqrt c,0)$ and $(-\sqrt c,0)$; positive orientation selects the first. For $d=0$, the only polynomial pair with $s(0)=0$ and $p^2+\Delta(s^2)=0$, even without a prescribed degree bound, is $(0,0)$.

Proof. The polynomials $\binom{t}{j}$ form a basis in each finite degree, since their leading coefficients are $1/j!$. The identity $\Delta\binom{t}{j+1}=\binom{t}{j}$ follows by subtracting the falling-factorial products, or by the binomial identity on infinitely many nonnegative integers. Successive differences at zero therefore recover the Newton coefficients: $d(t)=\sum_{j=0}^{2m}\Delta^j d(0)\binom{t}{j}$. This proves $\Delta P=d$ and $P(0)=0$. A nonconstant polynomial of degree $r$ and leading coefficient $a$ has forward difference of degree $r-1$ and leading coefficient $ra$; hence a polynomial with zero difference is constant. This proves uniqueness and the exact degree and leading coefficient in (15.3). Telescoping identifies its integer values with the sum of $d(j)$, which is nonnegative and nondecreasing in $k$.

For $m\ge1$, set $d_n=d+1/n$ for integers $n\ge1$. It is strictly positive on the entire real line, has degree $2m$ and retains leading coefficient $\delta$. Theorem 10.1 supplies real pairs $p_n,s_n$ of degrees at most $m$, with $s_n(0)=0$ and $d_n=p_n^2+\Delta(s_n^2)$. Replacing $p_n$ by its negative when necessary makes its leading coefficient exactly $\sqrt\delta$. Summation gives the exact nonnegative identity

$$
P(k)+\frac{k}{n}=s_n(k)^2+\sum_{j=0}^{k-1}p_n(j)^2\qquad(k\ge0).
\tag{15.4}
$$

Let $M=\sqrt{P(m+1)+m+1}$. Taking $k=m+1$ bounds every $|p_n(j)|$ for $0\le j\le m$ by $M$. Taking $k=j$ and using $P(j)\le P(m+1)$ bounds every $|s_n(j)|$ at the same nodes by $M$. These bounds are simultaneous in $n$ and in the two polynomials. Explicitly, the fixed Lagrange polynomials

$$
\ell_j(t)=\prod_{\substack{0\le i\le m\\i\ne j}}\frac{t-i}{j-i}
\quad(0\le j\le m)
\tag{15.5}
$$

satisfy $v(t)=\sum_{j=0}^m v(j)\ell_j(t)$ for every polynomial of degree at most $m$. Thus each coefficient of either $p_n$ or $s_n$ has absolute value at most $M\sum_{j=0}^m|[t^r]\ell_j|$. The combined coefficient sequence lies in a bounded subset of $\mathbb R^{2m+2}$. Finite-dimensional compactness gives one subsequence along which both polynomials converge coefficientwise, to $p,s$.

Polynomial multiplication, translation and coefficient extraction are continuous in these finite-dimensional spaces. Passing along that common subsequence gives $d=p^2+\Delta(s^2)$, $s(0)=0$, $\deg s\le m$ and $[t^m]p=\sqrt\delta$. In particular $\deg p=m$. For any other degree-bounded pair, $\Delta(s^2)$ has degree at most $2m-1$ when nonzero, so comparison of degree $2m$ forces the same squared leading coefficient. Telescoping (15.1) proves the remaining identity in (15.3).

For $m=0$, the anchor forces the constant $s$ to vanish, and $p^2=c$ gives exactly the two stated pairs; (15.2) is $P(t)=ct$. For $d=0$ and arbitrary polynomial degrees, telescoping gives $0=s(k)^2+\sum_{j<k}p(j)^2$ for every $k\ge0$. Every summand is nonnegative, so $s$ and $p$ each vanish at every nonnegative integer and are zero polynomials.

No separation of the real zeros of $d$ was used, so repeated real zeros are included. This compactness proof supplies existence, not a continuous selection of pairs, uniqueness for general $d$, or convergence of a coefficient algorithm. The input Theorem 10.1 uses the scalar ingredient of [Ephremidze, *An Elementary Proof of the Polynomial Matrix Spectral Factorization Theorem*, arXiv:1011.3777v1, Theorem 2](https://arxiv.org/pdf/1011.3777v1): a polynomial matrix positive definite almost everywhere on the real line admits a polynomial factor nonsingular in the open upper half-plane, unique up to a constant right unitary multiplier. That result supplies neither the telescoping anchor nor a continuously chosen anchored pair at real roots. The argument here takes limits of the already anchored strictly positive pairs instead. $\square$

**Theorem 15.3 (Exact delay, every-pair divisibility and maximal-delay rigidity).** For $d$ as above define

$$
h=1+\min\{j\in\mathbb Z_{\ge0}:d(j)>0\}.
\tag{15.6}
$$

This minimum exists, $1\le h\le m+1$, and $P(k)=0$ exactly for $0\le k<h$, while $P(k)>0$ for every integer $k\ge h$. For each integer $h$ in that range the exact classification is

$$
d(t)=\operatorname{fall}_{h-1}(t)^2r(t),\qquad
r\ge0\text{ on }\mathbb R,\qquad
\deg r=2(m-h+1),\qquad r(h-1)>0.
\tag{15.7}
$$

Every allowed $h$ occurs at every fixed $m$. Every polynomial pair satisfying $s(0)=0$ and $d=p^2+\Delta(s^2)$, even without a degree bound, obeys

$$
\operatorname{fall}_{h-1}\mid p,\qquad
\operatorname{fall}_h\mid s.
\tag{15.8}
$$

In particular $h=m+1$ if and only if $d=c\operatorname{fall}_m^2$ for some $c>0$. In that case every degree-bounded anchored pair is $s=0$, $p=\pm\sqrt c\operatorname{fall}_m$.

Proof. At a real zero $a$ write $d(t)=(t-a)^er(t)$ with $r(a)\ne0$. Continuity makes the sign of $r$ constant close to $a$. If $e$ were odd, the two sides of $a$ would give opposite signs for $d$, contrary to global nonnegativity. Thus each real zero has even multiplicity. A nonzero degree-$2m$ polynomial has at most $m$ distinct real zeros. Among the $m+1$ integers $0,\ldots,m$, some value of $d$ is therefore positive, proving existence and the bound on $h$. The sums in (15.3) are zero before $h$ and thereafter contain the strictly positive term $d(h-1)$; later zero values of $d$ cannot make $P$ zero again.

The prescribed zeros $0,\ldots,h-2$ each have multiplicity at least two, so their squared product divides $d$. Its quotient has the degree in (15.7); it is nonnegative away from those finitely many roots because the divisor is positive there, and nonnegative at the roots by continuity. Moreover $\operatorname{fall}_{h-1}(h-1)=(h-1)!\ne0$, so $d(h-1)>0$ is equivalent to $r(h-1)>0$. Conversely (15.7) makes the first $h-1$ values of $d$ zero and the next positive, proving the classification. For each $h\in\{1,\ldots,m+1\}$ the explicit example

$$
d(t)=\operatorname{fall}_{h-1}(t)^2
\big(1+(t-h+1)^2\big)^{m-h+1}
\tag{15.9}
$$

has degree $2m$, is globally nonnegative and satisfies exactly that classification.

For any polynomial pair with the stated identity and anchor, telescoping gives $P(k)=s(k)^2+\sum_{j<k}p(j)^2$ without any degree assumption. Thus $P(k)=0$ for $0\le k<h$ forces $s(k)=0$ at all those points. At $k=h-1$, the same identity forces $p(j)=0$ for $0\le j<h-1$; when $h=1$ this is an empty list. Division by these distinct linear factors proves (15.8), including the case $s=0$. At $h=m+1$ the quotient $r$ in (15.7) is a positive constant $c$. For a degree-bounded pair, $s$, of degree at most $m$, has the $m+1$ distinct zeros $0,\ldots,m$, so $s=0$. Now $p^2=c\operatorname{fall}_m^2$ implies $(p-\sqrt c\operatorname{fall}_m)(p+\sqrt c\operatorname{fall}_m)=0$; the polynomial ring has no zero divisors, giving the two signs. Conversely this $d$ has precisely the stated first positive integer value. These arguments include $m=0,h=1$. $\square$

**Theorem 15.4 (Sharp positive-delay tradeoff for seed and detector ranks).** Let $H$ have finite complex dimension $D\ge0$, let $\mathcal T(X)=\sum_iK_iXK_i^\dagger$ have a finite, possibly empty Kraus family, and let $\tau,F\ge0$ have ranks $a,b$. Put $w_k=\operatorname{Tr}[F\mathcal T^k(\tau)]$. Suppose a first positive weight exists at an index $h\ge1$. Then

$$
a,b\ge1,\qquad D\ge a+b,\qquad
h\le D-a-b+1.
\tag{15.10}
$$

This bound is sharp for raw CP detection for every $a,b,h\ge1$, in dimension $D=a+b+h-1$. It requires no normalization, trace contraction, completeness, stability or commutation. Its positive-delay hypothesis cannot be dropped.

Proof. Let $U=\operatorname{ran}\tau$ and $H_n=\operatorname{span}\{K_wU:|w|\le n\}$. The empty word is included. As in Section 13,

$$
H_0=U,\qquad H_{n+1}=H_n+\sum_iK_iH_n,\qquad
\operatorname{ran}\Big(\sum_{k=0}^n\mathcal T^k(\tau)\Big)=H_n.
\tag{15.11}
$$

For completeness, $\operatorname{ran}(MM^\dagger)=\operatorname{ran}M$ follows by taking orthogonal complements of $\ker(MM^\dagger)=\ker M^\dagger$. Use this with $M=K_w\tau^{1/2}$. The kernel of a finite sum of positive matrices is the intersection of their kernels, because its zero quadratic form forces each nonnegative quadratic form to be zero. The range of the sum is consequently the span of the ranges, proving the last equality in (15.11). Finally $\operatorname{Tr}(FX)=\|F^{1/2}X^{1/2}\|_{\rm HS}^2$ for $X\ge0$, so a zero trace is equivalent to $F$ annihilating $\operatorname{ran}X$.

The zero weights through $h-1$ give $H_{h-1}\subseteq\ker F$. If $H_{n+1}=H_n$ for any $0\le n<h-1$, every $K_i$ preserves $H_n$, hence every later reachable vector lies in $H_n\subseteq\ker F$. That would force $w_h=0$. Thus all $h-1$ successive inclusions from $H_0$ to $H_{h-1}$ are strict; for $h=1$ there are none. Therefore

$$
a+h-1\le\dim H_{h-1}\le D-b,
\tag{15.12}
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
\tag{15.13}
$$

The space has dimension $(h+1)+(a-1)+(b-1)=a+b+h-1$, and the two projections have ranks $a,b$. At time zero their ranges are disjoint. For $1\le k\le h$, $K^k\tau(K^\dagger)^k=e_ke_k^\dagger$; for $k>h$ it is zero. Hence $w_h=1$ and every other $w_k=0$. This proves raw CP sharpness. It is not a normalized seed when $a>1$, and an effect and a raw zero map do not specify a complete binary instrument. Indeed here

$$
K^\dagger K+F=I-\sum_{i=1}^{a-1}u_iu_i^\dagger.
\tag{15.14}
$$

Thus for $a>1$ even the necessary completeness identity with this fixed detector effect fails. No claim of complete-instrument sharpness for arbitrary ranks is part of this example.

If $\tau=0$, $F=0$ or $D=0$, every weight vanishes and $h$ is undefined. An empty Kraus family gives zero weights for $k\ge1$, so cannot have positive delay. If either seed or detector has full rank and the other is nonzero, $w_0>0$, since a positive definite operator has strictly positive trace pairing with a nonzero positive operator. Finally $\tau=F=I_2$ has $h=0$ for any Kraus family, whereas the proposed right side of (15.10) would be $2-2-2+1=-1$. This explicitly excludes the $h=0$ extension.

The support mechanism reuses Section 13. Its literature antecedents are [Yu–Ying, arXiv:1206.1935v1, Theorem 1](https://arxiv.org/pdf/1206.1935v1), for the reachable support of a finite-dimensional concurrent quantum program with trace-preserving CP program steps $\mathcal E_i$, a continuation measurement operator $M_1$, a density seed, $F_i(X)=\mathcal E_i(M_1XM_1^\dagger)$ and $F=\sum_iF_i$, and [Ying–Feng–Yu–Ying, arXiv:1304.0060v2, Lemma 1(2)](https://arxiv.org/pdf/1304.0060v2), for a finite-dimensional quantum Markov chain with a trace-preserving CP transition and a density seed. Both display a $D-1$ support horizon. The unrestricted raw CP assumptions, arbitrary positive seed, detector-kernel inequality (15.12) and sharpness witness above are supplied by the present argument, not attributed to those statements. $\square$

**Definition 15.5 (The general law and the full competitor interface).** For $d$ of Definition 15.1 and $0<q<1$, set

$$
\begin{aligned}
Z&=\sum_{k\ge0}q^kP(k),&\gamma_k&=q^kP(k)/Z,\\
S_a&=\sum_{j\ge a}\gamma_j,&
\mu&=\sum_{k\ge0}(k+1)\gamma_k.
\end{aligned}
\tag{15.15}
$$

The normalizer, tails and mean in this section belong to this $d,q$, not to a monomial law specified elsewhere. The target cylinders are

$$
\begin{aligned}
\mathbb P_{d,q}(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{i=1}^{r-1}\gamma_{g_i}\quad(r\ge1),\\
\mathbb P_{d,q}(0^N)&=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j\quad(N\ge0).
\end{aligned}
\tag{15.16}
$$

All indices are nonnegative integers, the internal product is one when $r=1$, and $N=0$ denotes the empty word. The theorems below prove normalization, consistency and realization. A competitor consists of fixed CP maps $\widehat\Phi,\widehat\Psi$ on $M_{D'}(\mathbb C)$ whose sum preserves trace, and a specified density $\widehat\rho$, such that the ordered instrument trace equals (15.16) for every finite word. Its matrices can be complex, its hidden state can be mixed and noninvariant, and its tick map can have arbitrary Kraus rank without a reset premise. Every persistent quantum or classical register, retained record and controller influencing later steps belongs to $D'$. There is no uncounted correlated input or time-dependent external control. The Kraus alternatives within each visible branch are summed, not retained as a further visible or persistent register.

**Theorem 15.6 (Newton realization, stability, observability and reachability for every pair).** Choose any degree-bounded anchored pair for $d$. On $\mathbb C^{m+2}$ use target basis $e_0,\ldots,e_m$ and source basis vector $e_{\mathrm{src}}=e_{m+1}$. Define

$$
\begin{aligned}
N_{j,j+1}&=1\ (0\le j<m),\quad N_{ij}=0\text{ otherwise},&U&=I_{m+1}+N,\\
u_j&=\Delta^{j+1}s(0),&v_j&=\Delta^jp(0)\quad(0\le j\le m),\\
A&=\begin{pmatrix}U&u\\0&1\end{pmatrix},&
B&=\begin{pmatrix}0&v\\0&0\end{pmatrix},\\
x&=e_{\mathrm{src}},&f&=e_0,\qquad F_0=ff^{\mathsf T},\\
\mathcal T_q(X)&=q(AXA^{\mathsf T}+BXB^{\mathsf T}).
\end{aligned}
\tag{15.17}
$$

The polynomial $s$ retains its meaning in (15.1). All unshown blocks of $B$ are zero. For all nonnegative integers $k,t,r$,

$$
\begin{aligned}
u_m&=0,\qquad v_m=m![t^m]p\ne0,\\
f^{\mathsf T}A^kx&=s(k),\qquad f^{\mathsf T}A^tBA^rx=p(t),\qquad BA^rB=0,\\
\operatorname{Tr}[F_0\mathcal T_q^k(xx^{\mathsf T})]&=q^kP(k),\\
\operatorname{spec}(\mathcal T_q)&=\{q\}\text{ on }M_{m+2}(\mathbb C),\\
Q=\sum_{k\ge0}(\mathcal T_q^*)^k(F_0)&>0,\qquad x^{\mathsf T}Qx=Z\in(0,\infty).
\end{aligned}
\tag{15.18}
$$

The raw reachable span from $x$ is all of $\mathbb C^{m+2}$, witnessed by $x,A^jBx$ for $0\le j\le m$. All moments of $\gamma$ are finite, $\gamma_k>0$ exactly for $k\ge h$, and

$$
S_a=q^aH(a),\qquad
H(t)=\frac1Z\sum_{r\ge0}q^rP(t+r),\qquad
\deg H=2m+1,\quad [t^{2m+1}]H=\frac{\delta}{(2m+1)Z(1-q)}.
\tag{15.19}
$$

Proof. Newton expansion as in (15.2) gives $p(t)=\sum_jv_j\binom tj$ and $\Delta s(t)=\sum_ju_j\binom tj$. At integer $t\ge0$, $U^t=\sum_{j=0}^m\binom tjN^j$, so the first target row applied to $U^tv$ is $p(t)$ and applied to $U^tu$ is $\Delta s(t)$. Since $\deg s\le m$ and $\deg p=m$, the last coefficients have precisely the values in (15.18). The block power sends $x$ to $(\sum_{j<k}U^ju,1)$, whose first coordinate is $s(k)-s(0)=s(k)$. Also $BA^rx=(v,0)$, giving the second word amplitude. The image of $B$ is in the target, which $A$ preserves and $B$ annihilates, so $BA^rB=0$.

With rightmost factors acting first, the sole all-$A$ word of length $k$ contributes $s(k)^2$. The exactly $k$ words with one $B$ are $A^tBA^{k-1-t}$ for $0\le t<k$, contributing $p(t)^2$. Every word with at least two $B$ factors is zero. Thus the complete Kraus-word sum is

$$
q^k\sum_{|w|=k}|f^{\mathsf T}wx|^2
=q^k\left(s(k)^2+\sum_{t<k}p(t)^2\right)=q^kP(k).
\tag{15.20}
$$

At $k=0$ the empty word contributes $s(0)^2=0$. Separate words contribute separate squared amplitudes, so no interference between different Kraus alternatives is being assumed.

Both $A$ and $B$ are upper triangular, with diagonals all one and all zero. Column vectorization represents $\mathcal T_q$ on the full complex matrix space by $q(A\otimes A+B\otimes B)$, upper triangular with every diagonal entry $q$. This proves its spectrum, without restricting to real or diagonal matrices. Subtracting $qI$ gives a nilpotent matrix of index at most $(m+2)^2$. Its binomial power expansion shows that for every $q<\theta<1$, $\|\mathcal T_q^k\|\le C_\theta\theta^k$: each of the finitely many terms is a fixed constant times $\binom{k}{j}q^{k-j}$, and a polynomial times $(q/\theta)^k$ is bounded. The dual has the same stability bound, ensuring norm convergence of $Q$.

For a complex vector $y=(y_T,y_{\mathrm{src}})$, positivity gives

$$
y^\dagger Qy=\sum_{k\ge0}q^k\sum_{|w|=k}|f^{\mathsf T}wy|^2.
\tag{15.21}
$$

If this vanishes, every summand vanishes. The rows $f^{\mathsf T}A^tB=p(t)e_{\mathrm{src}}^{\mathsf T}$ force $y_{\mathrm{src}}=0$, since a nonzero degree-$m$ polynomial cannot vanish at every integer $0,\ldots,m$. The rows $f^{\mathsf T}A^j$ for $0\le j\le m$ then force $\sum_{\ell=0}^m\binom j\ell(y_T)_\ell=0$. This coefficient matrix is lower triangular with diagonal one, so $y_T=0$. Hence $Q$ is faithful on every complex memory direction. This detector observability is separate from reachability: the target parts of $A^jBx$ are $U^jv$, whose span equals that of $v,Nv,\ldots,N^mv$ by the same invertible binomial matrix. In reversed target-coordinate order the latter columns form a triangular matrix with diagonal $v_m\ne0$. They span the target, and $x$ supplies the remaining source direction.

Summing (15.20) yields $x^{\mathsf T}Qx=Z$. The polynomial bound $0\le P(k)\le C(1+k)^{2m+1}$ and the ratio test give finiteness of $Z$ and of every moment sum; $P(h)>0$ gives strict positivity of $Z$. The support assertion follows from Theorem 15.3. For (15.19), expand each monomial of $P(t+r)$ in powers of $t$. Each coefficient is a finite linear combination of convergent sums $\sum_{r\ge0}r^jq^r$, with $r^0=1$ also at $r=0$. Thus $H$ is a polynomial, and its top coefficient is the top coefficient of $P$ times $1/(Z(1-q))>0$. Substitution $j=a+r$ in the tail sum proves the identity for $S_a$.

These are the Newton and word mechanisms of Section 11 with the actual polynomial $P$ replacing the monomial, and with $m=0$ included: then $N=0$, $u=0$ and $v_0=p\ne0$, so every step above still holds. $\square$

**Theorem 15.7 (Complete real instrument and a single global resetting tick).** Let $G=Q^{1/2}$ and $D=m+2$, and define

$$
\begin{aligned}
\xi&=Gx/\sqrt Z,&\tau&=\xi\xi^{\mathsf T},&E&=G^{-1}F_0G^{-1},\\
L_A&=\sqrt q\,GAG^{-1},&L_B&=\sqrt q\,GBG^{-1},&J&=\xi f^{\mathsf T}G^{-1},\\
\Phi(X)&=L_AXL_A^{\mathsf T}+L_BXL_B^{\mathsf T},&&
\Psi(X)=JXJ^{\mathsf T}.
\end{aligned}
\tag{15.22}
$$

This is a complete homogeneous binary CP instrument on $M_D(\mathbb C)$ with real entries, no-tick Choi rank exactly two and tick Choi rank exactly one. The matrix ranks of $L_A,L_B,J$ are respectively $D,1,1$. On every input matrix, $\Psi(X)=\tau\operatorname{Tr}(EX)$; every positive-probability tick therefore has the same pure normalized output $\tau$. Moreover

$$
\rho(\Phi)=q<1,\qquad
\Psi\Phi^k(\tau)=\gamma_k\tau,\qquad
\operatorname{Tr}\Phi^a(\tau)=S_a.
\tag{15.23}
$$

Proof. The parameters of Theorem 2.1 are the raw family $\sqrt q A,\sqrt q B$, the single detector column $f$, the reset $x$, the dimension $D$ and the faithful Gramian $Q$ of Theorem 15.6. That theorem applies without any trace-contraction assumption on the raw map. More explicitly, shifting the norm-convergent series gives

$$
Q-qA^{\mathsf T}QA-qB^{\mathsf T}QB=F_0,
\qquad L_A^{\mathsf T}L_A+L_B^{\mathsf T}L_B+J^{\mathsf T}J=I.
\tag{15.24}
$$

Real orthogonal diagonalization of $Q>0$ gives a real invertible positive square root $G$, and $\xi^{\mathsf T}\xi=x^{\mathsf T}Qx/Z=1$. Conjugation by $G^{-1}$ proves the second identity. These Kraus expressions are CP on all complex matrices: their ampliations are sums of conjugations by each Kraus matrix tensored with an identity. Completeness gives trace preservation of the sum and trace nonincrease of each positive branch, including on complex coherent inputs.

The invertible map $\Gamma(X)=GXG$ satisfies $\Phi=\Gamma\mathcal T_q\Gamma^{-1}$ and

$$
\Phi^k(\tau)=\frac{G\mathcal T_q^k(xx^{\mathsf T})G}{Z}.
\tag{15.25}
$$

This proves stability, while the outer-product formula for $J$ proves the global reset identity. Combining it with (15.20) proves the actual gap formula. The definition of $Z$ gives $\sum_k\gamma_k=1$. For $t_a=\operatorname{Tr}\Phi^a(\tau)$, completeness yields $t_a-t_{a+1}=\gamma_a$ and stability yields $t_a\to0$. Telescoping gives $t_a=S_a$, with no probability left at an infinite next gap.

Finally $A$ is invertible and $B=(v,0)e_{\mathrm{src}}^{\mathsf T}$ is nonzero of rank one. Since $D\ge2$, they are linearly independent over $\mathbb C$. Similarity and nonzero scaling preserve both independence and matrix ranks. The Choi matrix of $\Phi$ is the sum of the outer products of the vectorizations of $L_A,L_B$; the range of a sum of positive operators is the span of their ranges. Its rank is therefore two, and any Kraus representation must span that same Choi range. The two nonzero factors of $J$ make its matrix rank and its Choi rank one. This proves all stated rank distinctions. $\square$

**Theorem 15.8 (Faithful stationary density, all tails and all cylinders).** For (15.22), the series

$$
R_0=\sum_{a\ge0}\Phi^a(\tau),\qquad \rho_*=R_0/\mu
\tag{15.26}
$$

defines a real faithful mixed density invariant under $\Phi+\Psi$. Its actual ordered-word traces give exactly (15.16), including the empty word, and define a proper stationary renewal law with tick rate $1/\mu$ and no all-zero stationary component. Its visible support consists exactly of finite words with at least $h$ zeros between successive ones. This is exactly the no-adjacent-one Fibonacci language if and only if $d(0)>0$.

Proof. Stability gives norm convergence of $R_0$. Nonnegative summation and (15.23) give

$$
\operatorname{Tr}R_0=\sum_{a\ge0}S_a
=\sum_{j\ge0}(j+1)\gamma_j=\mu<\infty,\qquad
\Phi(R_0)=R_0-\tau,\qquad \Psi(R_0)=\tau.
\tag{15.27}
$$

Thus $\rho_*$ is normalized, invariant and has tick rate $1/\mu$. For each raw word $w$ in $A,B$, its completed word satisfies $L_w\xi=q^{|w|/2}Gwx/\sqrt Z$. Invertible $G$ and positive $q$ preserve the full reachable span of Theorem 15.6. For complex $y$,

$$
y^\dagger R_0y=\sum_{a\ge0}\sum_{|w|=a}|y^\dagger L_w\xi|^2.
\tag{15.28}
$$

Vanishing forces orthogonality to that full span, hence $y=0$. This proves faithfulness. The summands are real symmetric, and full rank in dimension $D\ge2$ makes $\rho_*$ mixed. Its tick probability $1/\mu>0$ differs from $\operatorname{Tr}\Psi(\tau)=\gamma_0=0$, so it is distinct from the pure post-tick state.

For an initial run of $a$ zeros and its first tick, the actual unnormalized output is

$$
\Psi\Phi^a(\rho_*)
=\frac1\mu\sum_{c\ge0}\Psi\Phi^{a+c}(\tau)
=\frac{S_a}{\mu}\tau.
\tag{15.29}
$$

Each following gap $g_i$ and tick multiplies this density by $\gamma_{g_i}$ and returns it to $\tau$. The final $b$ zeros have trace $S_b$ from that reset. Taking the trace proves the first line of (15.16) for every number of ticks. With no tick, applying $\Phi^N$ directly to (15.26) gives

$$
\operatorname{Tr}\Phi^N(\rho_*)
=\frac1\mu\sum_{a\ge0}S_{N+a}
=\frac1\mu\sum_{j\ge N}(j-N+1)\gamma_j.
\tag{15.30}
$$

At $N=0$ this is one by (15.27). These cases exhaust all words. Summing the last symbol uses trace preservation and gives right consistency; summing the first uses invariance and gives left consistency. The finite-alphabet consistent cylinders consequently define a stationary process. After any positive-probability tick history the memory is $\tau$, so the joint law of any finite sequence of subsequent complete gaps is the product of their $\gamma$ values. Their normalization proves a proper next gap at each renewal. Also

$$
0\le\mathbb P_{d,q}(0^N)
\le\frac1\mu\sum_{j\ge N}(j+1)\gamma_j\longrightarrow0,
\tag{15.31}
$$

excluding an infinite all-zero future of positive probability and hence any all-zero stationary component.

All $S_a$ and all finite all-zero cylinders are positive, since $\gamma_k>0$ for every $k\ge h$. The first cylinder formula is positive exactly when each internal gap is at least $h$. By (15.6), $h=1$ exactly when $d(0)>0$; if $h>1$, even the no-adjacent-one word $101$ has probability zero. This proves the exact support assertion.

The stationary convention is that of [Monras–Beige–Wiesner, *Hidden Quantum Markov Models and non-adaptive read-out of many-body states*, arXiv:1002.2337v2, equations (25)–(27)](https://arxiv.org/pdf/1002.2337v2): a fixed point of the sum of the symbol operations supplies ordered trace probabilities. Equations (15.27)–(15.31) derive the new law's renewal factors, mean and boundary tails using the summation mechanism of Sections 5 and 14. The monomial hypotheses of Theorem 5.1 do not themselves quantify over Definition 15.5. $\square$

**Theorem 15.9 (Actual-posterior rank bounds and reused no-tick Choi minimum).** For the competitor class of Definition 15.5 the minimum possible no-tick Choi rank, across all finite complex memory dimensions, is exactly two. If a competitor has dimension $D'$, let $\tau_0$ be its actual posterior after the positive-probability first tick and let $F_1=\widehat\Psi^*(I)$. With $a=\operatorname{rank}\tau_0$ and $b=\operatorname{rank}F_1$,

$$
D'\ge h+a+b-1\ge h+1,
\qquad h+1\le D_{\min}\le m+2.
\tag{15.32}
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
\tag{15.33}
$$

Here $\tau_0$ is a density, possibly mixed, and $F_1$ is a positive effect. This uses neither a common reset nor invariance of $\widehat\rho$. Finite-dimensional CP maps have finite Kraus representations by diagonalizing their positive Choi matrices. Theorem 15.4 therefore applies at the exact positive delay $h$, giving the first bound. The explicit complete instrument gives the upper bound. For the actual competitor survival $t_k=\operatorname{Tr}\widehat\Phi^k(\tau_0)$, completeness gives $t_0=1$ and $t_k-t_{k+1}=\gamma_k$; normalization of $\gamma$ gives $t_k=S_k\to0$. This identifies its actual tails without any assumption on an unused spectral block.

For the no-tick lower bound, rank zero would mean $\widehat\Phi=0$ and hence $\gamma_h=0$, contradicting $h\ge1$ and $\gamma_h>0$. Rank one would give $\widehat\Phi(X)=CXC^\dagger$ for some complex matrix $C$, so (15.33) becomes

$$
\left\|F_1^{1/2}C^k\tau_0^{1/2}\right\|_{\rm HS}^2
=\frac{q^kP(k)}Z.
\tag{15.34}
$$

This is the exact positive-effect, mixed-seed interface of the generic finite-vector-recurrence argument in [Chapter 29, equations (29.3)–(29.6), reused in Chapter 40, equation (40.4)](FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md#29-the-original-sns-needs-two-unresolved-no-tick-kraus-alternatives), and in Theorem 6.3 here. Its generic assertion is that an eventual nonzero squared norm of a finite constant-coefficient complex vector recurrence, equal to $q^k$ times a real polynomial with positive leading coefficient, has even polynomial degree. It is not restricted to the SNS or monomial conclusions of the named theorems.

To give its full application, put $V_k=F_1^{1/2}C^k\tau_0^{1/2}$ in finite Hilbert–Schmidt space. Cayley–Hamilton gives a scalar constant-coefficient recurrence for every coordinate. After finitely many initial indices, its nonzero terms have the form $V_k=\sum_jR_j(k)\lambda_j^k$ with distinct nonzero $\lambda_j$ and nonzero vector polynomials $R_j$. This is the classical recurrence representation of [Stanley, *Enumerative Combinatorics*, Volume 1, Theorem 4.1.1 and Proposition 4.2.2](https://math.mit.edu/~rstan/ec/ec1.pdf): a rational generating series with denominator nonzero at zero gives exponential-polynomial coefficients outside a finite exceptional set. Theorem 4.1.1 requires a nonzero last recurrence coefficient; zero-root transients can be discarded, or handled by the exceptional-set proposition. Thus no invertibility of $C$ is required. Equivalently, on each nonzero Jordan block $\lambda I+N$, the finite expansion $\sum_j\binom{k}{j}\lambda^{k-j}N^j$ gives the same representation; zero Jordan blocks vanish eventually.

The right side of (15.34) is positive for all $k\ge h$, so $V_k$ is not eventually zero. Choose the largest modulus $R>0$ of an occurring $\lambda_j$, and the largest vector-polynomial degree $e$ at that modulus. With leading vectors $a_j\ne0$ of those terms and distinct phases $\omega_j=\lambda_j/R$, one has

$$
\frac{V_k}{R^kk^e}=T_k+o(1),\qquad
T_k=\sum_{j\in J}a_j\omega_j^k,\qquad
\lim_{N\to\infty}\frac1N\sum_{k=1}^N\|T_k\|^2
=\sum_{j\in J}\|a_j\|^2>0.
\tag{15.35}
$$

Terms of smaller modulus or smaller degree vanish after this normalization. The mean identity follows by expansion: diagonal phase products equal one, and every off-diagonal average is $N^{-1}\sum_{k=1}^N\zeta^k\to0$ for a fixed $|\zeta|=1$, $\zeta\ne1$, by the finite geometric-sum formula. No orthogonality of leading vectors is needed. The normalized vectors are bounded and their squared norms have this same strictly positive Cesàro mean, since their difference from $T_k$ tends to zero. By (15.34) their squared norms equal

$$
\frac{P(k)}{Zk^{2e}}\left(\frac q{R^2}\right)^k.
\tag{15.36}
$$

If $q<R^2$, this tends to zero; if $q>R^2$, it tends to infinity, contradicting respectively the positive mean or boundedness. Hence $q=R^2$. The same alternatives for polynomial growth then force $\deg P=2e$. But $\deg P=2m+1$ with positive leading coefficient, a contradiction. This reuses the existing parity proof with the new polynomial $P/Z$; no CP-growth estimate, pure hidden trajectory, hidden-source radius identification or tick-rank restriction enters. Theorem 15.7 attains rank two, proving its minimum over all finite competitor dimensions, independently of whether $m+2$ is minimum memory.

At maximal delay, (15.32) and the construction give $D_{\min}=m+2=h+1$. If a competitor has this dimension, its positive ranks obey $a+b\le2$, so $a=b=1$. The separate support bounds of Theorem 13.2 give $h\le r-a$ and $h\le r^\vee-b$, forcing $r=r^\vee=D'$. To spell out the actual-output consequence of Theorem 13.3, write $F_1=\lambda\eta\eta^\dagger$ for a unit $\eta$ and $\lambda>0$. In any tick Kraus representation $\widehat\Psi(X)=\sum_iJ_iXJ_i^\dagger$, the identity $\sum_i\|J_iy\|^2=y^\dagger F_1y=0$ for $y\perp\eta$ gives $J_i=v_i\eta^\dagger$. Thus $\widehat\Psi(X)=(\eta^\dagger X\eta)M$ with $M=\sum_iv_iv_i^\dagger$ and $\operatorname{Tr}M=\lambda$. The positive actual tick in (15.33) gives $\tau_0=M/\lambda$, so

$$
\widehat\Psi(X)=\tau_0\operatorname{Tr}(F_1X).
\tag{15.37}
$$

Since $\tau_0$ has rank one, positivity forces all $v_i$ into its one-dimensional range. Hence all nonzero $J_i$ span a single rank-one direction, and tick Choi rank is one. If an invariant initialization $\sigma$ reproduces the law, it satisfies $\sigma=\widehat\Phi(\sigma)+\nu\tau_0$. Iterating $D'$ times gives $\sigma\ge\nu\sum_{j=0}^{D'-1}\widehat\Phi^j(\tau_0)>0$, where full reachability and the positive-sum range identity prove the strict inequality. Since $D'=m+2\ge2$, it is mixed. For $m\ge1$ this is the delayed-family minimum of Section 14 under positive scaling of $d$; the proof also supplies its constant endpoint $m=0$. For nonmaximal delay, (15.32) is the dimension conclusion asserted here; no general equality $D_{\min}=m+2$ is inferred. $\square$

**Proposition 15.10 (The constant endpoint, scaling and the nonnormalizable zero case).** For $d=c>0$ one has $m=0$, $h=1$, $P(k)=ck$ and

$$
Z=\frac{cq}{(1-q)^2},\qquad
\gamma_0=0,\qquad \gamma_k=k(1-q)^2q^{k-1}\ (k\ge1),\qquad
\mu=\frac2{1-q}.
\tag{15.38}
$$

In basis $e_0,e_1$ a completed instrument is

$$
L_A=\sqrt q I_2,\qquad
L_B=\sqrt{1-q}\,e_0e_1^{\mathsf T},\qquad
J=\sqrt{1-q}\,e_1e_0^{\mathsf T},\qquad
\tau=e_1e_1^{\mathsf T},\quad \rho_*=I_2/2.
\tag{15.39}
$$

Its dimension two and no-tick Choi rank two are both minimum in the full competitor class. For fixed $q$, positive scaling of any nonzero $d$ leaves the law unchanged; two such polynomials give the same law if and only if they are positive scalar multiples. The zero polynomial gives no normalized law of the form (15.15).

Proof. The unique positively oriented constant pair is $p=\sqrt c,s=0$. Thus the raw matrices are $A=I_2$, $B=\sqrt c\,e_0e_1^{\mathsf T}$. The Gramian terms are $q^k(e_0e_0^{\mathsf T}+kc\,e_1e_1^{\mathsf T})$, giving

$$
Q=\operatorname{diag}\left(\frac1{1-q},\frac{cq}{(1-q)^2}\right).
\tag{15.40}
$$

Here $\sum_{k\ge0}q^k=(1-q)^{-1}$, and multiplying $\sum_{k\ge1}kq^k$ by $1-q$ leaves $\sum_{k\ge1}q^k=q/(1-q)$, proving the stated second sum. Substituting (15.40) into (15.22) gives precisely (15.39). Its effects sum to $qI_2+(1-q)e_1e_1^{\mathsf T}+(1-q)e_0e_0^{\mathsf T}=I_2$. By induction, for $k\ge1$,

$$
\Phi^k(\tau)=q^ke_1e_1^{\mathsf T}
+k(1-q)q^{k-1}e_0e_0^{\mathsf T}.
\tag{15.41}
$$

The step uses $\Phi(e_0e_0^{\mathsf T})=qe_0e_0^{\mathsf T}$ and $\Phi(e_1e_1^{\mathsf T})=qe_1e_1^{\mathsf T}+(1-q)e_0e_0^{\mathsf T}$. Applying the tick gives (15.38). Summing (15.41), together with the $k=0$ term, gives $R_0=I_2/(1-q)$, so its trace is $\mu=2/(1-q)$ and $\rho_*=I_2/2$. The minima and actual global tick reset at minimum follow from Theorem 15.9 with $h=m+1=1$.

For general $d$, multiplication by $c>0$ multiplies its uniquely anchored integral $P$ and normalizer $Z$ by $c$, leaving $\gamma$, its tails, mean and every cylinder unchanged. Conversely, at fixed $q$, equality of the gap laws gives $P_1(k)/Z_1=P_2(k)/Z_2$ at all nonnegative integers. Polynomial identity then gives $P_1=(Z_1/Z_2)P_2$ and, by taking differences, $d_1=(Z_1/Z_2)d_2$, with positive ratio. Equality of stationary cylinders implies equality of these gaps through (15.33), so the same assertion holds for the full laws. Finally for $d=0$ its anchored integral is identically zero, its only anchored pair is $(0,0)$ by Theorem 15.2, and $Z=0$. There is no probability normalization by this zero denominator. $\square$

**Definition 15.11 (Scope of the polynomial extension).** The new polynomial class includes real-root boundary cases and arbitrary repeated real zeros under global nonnegativity. Existence of an anchored pair is the compactness consequence in Theorem 15.2, not an extension of a chosen half-plane factor across real roots. The exact delay and divisibility classification and the positive-delay detector tradeoff have the separate arguments in Theorems 15.3–15.4. Spectral factorization, polynomial interpolation and finite differences, finite-dimensional compactness, support reachability and recurrence representations are classical ingredients; the cited results have the conditions stated with their uses. The no-tick parity obstruction is explicitly the reused generic argument, and the Newton, Gramian and stationary interfaces are derived here for the actual law (15.15).

The resource is finite persistent complex memory dimension, and the output object is the classical stationary cylinder law. The construction establishes an upper bound $m+2$, while unconditional equality here is restricted to maximal delay. The positive-delay rank witness (15.13) proves raw CP sharpness, not complete-instrument sharpness for arbitrary seed and effect ranks. The original monomial memory minimum and the general finite-CP growth obligation are separate from this extension. A pure tick posterior is distinct from the faithful mixed stationary density; real Kraus entries do not change the complex input model. No native AURIC identification, coherent-output preparation, physical precision, entropy, energy, work or control-cost consequence is included.

## 追加锚（本行以下为增补区）
