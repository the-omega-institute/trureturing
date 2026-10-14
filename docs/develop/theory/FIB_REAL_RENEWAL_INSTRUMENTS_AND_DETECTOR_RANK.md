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
