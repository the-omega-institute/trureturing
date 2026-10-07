# Stabilizer-entropy gaps of the qudit parity sectors

This volume is reference input; nothing in it is kernel-verified. Its text is append-only: corrections and additions belong after the final append anchor.

## 1. Scope

For an odd qudit dimension $d\ge3$ the parity operator $P|j\rangle=|-j\rangle$ splits $\mathbb C^d$ into an even sector of dimension $(d+1)/2$ and an odd sector of dimension $(d-1)/2$. This volume computes in closed form the extrinsic term of the average linear stabilizer entropy of each sector with respect to the single-qudit Weyl–Heisenberg group of $\mathbb C^d$, and from it the average stabilizer-entropy gap of each sector embedding. The extrinsic term of either sector equals $4/(d+3)$ when $3\nmid d$ and differs from it by an explicit rational correction when $3\mid d$; the gap is positive for every odd $d\ge3$. The proof holds for every odd $d$, prime or composite.

## 2. Notation and cited facts

**Cited facts.** The following definitions and formulas are taken from S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd, *Stabilizer Entropy of Subspaces*, arXiv:2512.23013v1; equation numbers are those of the arXiv HTML rendering of v1.

- (a) Weyl operators, Sec. II, Eqs. (II.1)–(II.4) and (II.8). With $\omega=e^{2\pi i/d}$, $X|j\rangle=|j+1\rangle$, $Z|j\rangle=\omega^j|j\rangle$ on $\mathbb C^d$ with basis indexed by $\mathbb Z_d$, and $\tau=-e^{i\pi/d}$, the displacement operators are $D_{\mathbf a}=\tau^{a_1a_2}X^{a_1}Z^{a_2}$ for $\mathbf a=(a_1,a_2)$. For odd $d$, $D_{\mathbf a}$ depends only on $\mathbf a$ modulo $d$, so the labels range over $\mathbb Z_d^2$.
- (b) Linear stabilizer entropy, Sec. II, Eq. (II.25): for a pure state $\psi$ on $\mathbb C^d$, $M(\psi)=1-\frac1d\sum_{\mathbf a\in\mathbb Z_d^2}|\mathrm{tr}(D_{\mathbf a}^\dagger\psi)|^4$.
- (c) Average stabilizer-entropy gap, Sec. III, Eqs. (III.4)–(III.8): for an isometry $\mathcal E:\mathbb C^{d_S}\to\mathbb C^{d_B}$, $\Delta M(\mathcal E)=d_S\,\mathrm{tr}(Q_S\mathcal A_4^S)-d_B\,\mathrm{tr}(Q_B\,\mathcal E^{\otimes4}(\mathcal A_4^S))$, where $Q=\frac1{d^2}\sum_{\mathbf a}(D_{\mathbf a}\otimes D_{\mathbf a}^\dagger)^{\otimes2}$ on the respective space and $\mathcal A_4^S=\mathbb E_\psi[\psi^{\otimes4}]=\binom{d_S+3}{4}^{-1}\Pi^S_{\mathrm{sym}^4}$ is the Haar fourth moment of pure states on $\mathbb C^{d_S}$, with $\Pi_{\mathrm{sym}^4}=\frac1{24}\sum_{\sigma\in S_4}T_\sigma$ and $T_\sigma$ the permutation of tensor factors.
- (d) Intrinsic term, Sec. III, Eq. (III.11), derived in App. D: for the single-qudit Weyl–Heisenberg group of $\mathbb C^{k}$, $k\,\mathrm{tr}(Q_S\mathcal A_4^S)$ equals $3/(k+2)$ for odd $k$ and $3(k+2)/((k+1)(k+3))$ for even $k$.
- (e) Cycle traces, App. D, Eq. (D.5): $\mathrm{tr}((Y_1\otimes Y_2\otimes Y_3\otimes Y_4)T_\sigma)=\prod_{c}\mathrm{tr}\big(\prod_{i\in c}Y_i\big)$, the product over the cycles $c$ of $\sigma$, each cycle product taken in cycle order.

**Convention 2.1 (Parity sectors).** Throughout, $d\ge3$ is odd and $P$ is the unitary $P|j\rangle=|-j\rangle$ on $\mathbb C^d$. Put $e_0=|0\rangle$ and, for $1\le j\le (d-1)/2$, $e_j^{\pm}=(|j\rangle\pm|-j\rangle)/\sqrt2$. The even sector $E_d=\ker(P-I)$ has orthonormal basis $e_0,e_1^+,\dots,e_{(d-1)/2}^+$ and dimension $(d+1)/2$; the odd sector $O_d=\ker(P+I)$ has orthonormal basis $e_1^-,\dots,e_{(d-1)/2}^-$ and dimension $(d-1)/2$. For $V\in\{E_d,O_d\}$ write $k_V=\dim V$, $\varepsilon_V=+1$ for $E_d$ and $\varepsilon_V=-1$ for $O_d$, and $\Pi_V$ for the orthogonal projector onto $V$. Stance: repo-derived (notation fixed in this volume).

**Convention 2.2 (Sector moments, extrinsic term and gap).** For $V\in\{E_d,O_d\}$ and $\mathbf a\in\mathbb Z_d^2$ let

$$
F_V(\mathbf a)=\mathbb E_{\psi}\,|\langle\psi|D_{\mathbf a}|\psi\rangle|^4 ,
$$

the expectation over the unitarily invariant probability measure on unit vectors $\psi\in V$. The extrinsic term of $V$ is $X(V)=\frac1d\sum_{\mathbf a\in\mathbb Z_d^2}F_V(\mathbf a)$, the intrinsic term is $I(k)$, equal to $3/(k+2)$ for odd $k$ and to $3(k+2)/((k+1)(k+3))$ for even $k$, and the gap of $V$ is $\Delta M(V)=I(k_V)-X(V)$. For every isometry $\mathcal E:\mathbb C^{k_V}\to\mathbb C^d$ with image $V$, $\Delta M(V)$ is the quantity $\Delta M(\mathcal E)$ of cited fact (c), with the single-qudit Weyl–Heisenberg group of $\mathbb C^{k_V}$ on the small space. Indeed, for a pure state $\phi$ on $\mathbb C^d$, $d\,\mathrm{tr}(Q\phi^{\otimes4})=\frac1d\sum_{\mathbf a}|\langle\phi|D_{\mathbf a}|\phi\rangle|^4$ because $\mathrm{tr}(D_{\mathbf a}^\dagger\phi)=\overline{\langle\phi|D_{\mathbf a}|\phi\rangle}$; this expression is linear in $\phi^{\otimes4}$, and $\mathcal E$ carries the Haar measure on unit vectors of $\mathbb C^{k_V}$ to the unitarily invariant measure on unit vectors of $V$, so $d\,\mathrm{tr}(Q\,\mathcal E^{\otimes4}(\mathcal A_4^S))=X(V)$; the first term of (c) is $I(k_V)$ by cited fact (d). Stance: repo-derived (specialization of the cited definitions).

## 3. Reduction to diagonal cosines

**Lemma 3.1 (Parity-commuting label reduction).** Let $V\in\{E_d,O_d\}$. Then $F_V(\mathbf 0)=1$, and for every nonzero $\mathbf a\in\mathbb Z_d^2$ there is an integer $h$ with $\gcd(h,d)=\gcd(a_1,a_2,d)$ and $F_V(\mathbf a)=F_V((0,h))$. Stance: repo-derived.

**Proof.** $F_V(\mathbf 0)=1$ because $D_{\mathbf 0}=I$ and $\psi$ is a unit vector.

Step 1 (two unitaries commuting with $P$). Let $\mathcal F|j\rangle=d^{-1/2}\sum_{l\in\mathbb Z_d}\omega^{jl}|l\rangle$ and $S|j\rangle=\tau^{j^2}|j\rangle$. Since $d$ is odd, $\tau=e^{i\pi(d+1)/d}=\omega^{(d+1)/2}$ has $\tau^d=1$, so $S$ is well defined on $\mathbb Z_d$ and unitary; $\mathcal F$ is unitary by orthogonality of characters. Both commute with $P$: $\mathcal FP|j\rangle=d^{-1/2}\sum_l\omega^{-jl}|l\rangle=P\mathcal F|j\rangle$ after substituting $l\mapsto -l$, and $\tau^{(-j)^2}=\tau^{j^2}$. Direct evaluation on basis vectors gives $\mathcal FX\mathcal F^\dagger=Z$, $\mathcal FZ\mathcal F^\dagger=X^{-1}$, $SXS^\dagger=\tau XZ$ (as $\tau^{(j+1)^2-j^2}=\tau\,\omega^{j}$) and $SZS^\dagger=Z$. From $ZX=\omega XZ$, every product of powers of $X$ and $Z$ equals a unimodular scalar times $X^uZ^v$, and $X^uZ^v$ is a unimodular scalar times $D_{(u,v)}$ with $(u,v)$ read modulo $d$ (as $X^d=Z^d=I$). Hence, for integer labels,

$$
\mathcal FD_{(x,y)}\mathcal F^\dagger\in\mathbb T\cdot D_{(-y,x)},\qquad SD_{(x,y)}S^\dagger\in\mathbb T\cdot D_{(x,x+y)},
$$

with $\mathbb T$ the unit circle, and correspondingly $\mathcal F^\dagger,S^\dagger$ (which also commute with $P$) realize the inverse label maps.

Step 2 (invariance). Let $U$ be unitary with $UP=PU$ and $UD_{\mathbf a}U^\dagger=cD_{\mathbf b}$, $|c|=1$. Then $U$ maps $V$ onto $V$, so $\psi\mapsto U\psi$ preserves the unitarily invariant measure on unit vectors of $V$, and $|\langle\psi|D_{\mathbf a}|\psi\rangle|=|\langle U\psi|D_{\mathbf b}|U\psi\rangle|$. Hence $F_V(\mathbf a)=F_V(\mathbf b)$.

Step 3 (Euclid on integer lifts). On $\mathbb Z^2$ let $\rho(x,y)=(-y,x)$ and $\sigma(x,y)=(x,x+y)$. By Steps 1–2, $F_V$ of the residue of $(x,y)$ is unchanged by $\rho^{\pm1}$ and $\sigma^{\pm1}$. The composite $\rho\circ\sigma^{-t}\circ\rho^{-1}$ sends $(x,y)$ to $(x+ty,y)$ for every $t\in\mathbb Z$, and $\sigma^t$ sends $(x,y)$ to $(x,y+tx)$. Lift a nonzero $\mathbf a$ to $(x,y)\in\{0,\dots,d-1\}^2\setminus\{(0,0)\}$. Subtracting integer multiples of one coordinate from the other as in the Euclidean algorithm reaches $(h',0)$ or $(0,h')$ with $h'\neq0$; one application of $\rho$ turns $(h',0)$ into $(0,h')$. All maps used are given by integer matrices of determinant $1$, so the entries of the image are integer combinations of $x,y$ and conversely; hence $\gcd(x,y,d)$ is invariant and the final label $(0,h)$ satisfies $\gcd(h,d)=\gcd(a_1,a_2,d)$. ∎

**Lemma 3.2 (Sector compressions of clock powers and their power sums).** Let $h$ be an integer and $\theta_j=2\pi hj/d$. For $V=E_d$ the matrix of $\Pi_VZ^h\Pi_V$ on $V$ in the basis of Convention 2.1 is diagonal with entries $1$ and $\cos\theta_j$ for $1\le j\le(d-1)/2$; for $V=O_d$ it is diagonal with entries $\cos\theta_j$ for $1\le j\le (d-1)/2$. Let $p_m^V(h)$ be the sum of the $m$-th powers of these entries. If $h\not\equiv0\pmod d$ and $n=d/\gcd(h,d)$, then with $\varepsilon=\varepsilon_V$

$$
p_1^V=\frac{\varepsilon}2,\qquad p_2^V=\frac{d+2\varepsilon}4,\qquad p_3^V=\begin{cases}\dfrac{\varepsilon}2,& n\neq3,\\ \dfrac{d+4\varepsilon}8,& n=3,\end{cases}\qquad p_4^V=\frac{3d+8\varepsilon}{16}.
$$

Stance: repo-derived.

**Proof.** $Z^h$ is diagonal in the computational basis. For distinct $1\le i,j\le(d-1)/2$ the supports $\{i,-i\}$, $\{j,-j\}$ and $\{0\}$ are pairwise disjoint (since $2\le i+j\le d-1$), so all off-diagonal entries within each sector vanish, while $\langle e_j^\pm|Z^h|e_j^\pm\rangle=(\omega^{hj}+\omega^{-hj})/2=\cos\theta_j$ and $\langle e_0|Z^h|e_0\rangle=1$.

Let $T_m=\sum_{j\in\mathbb Z_d}\cos^m\theta_j$. Since $\cos\theta_{-j}=\cos\theta_j$ and $\theta_0=0$, $T_m=1+2H_m$ with $H_m=\sum_{j=1}^{(d-1)/2}\cos^m\theta_j$, so $p_m^{E_d}=1+H_m=(T_m+1)/2$ and $p_m^{O_d}=H_m=(T_m-1)/2$, that is, $p_m^V=(T_m+\varepsilon)/2$. Expanding $\cos^m\theta=2^{-m}\sum_{r=0}^m\binom mr e^{i(m-2r)\theta}$ and using $\sum_{j\in\mathbb Z_d}\omega^{shj}=d$ if $d\mid sh$ and $0$ otherwise, write $g=\gcd(h,d)$: $d\mid sh$ holds iff $n\mid s(h/g)$ iff $n\mid s$, because $\gcd(h/g,n)=1$. For $|s|\le4$ and odd $n\ge3$, $n\mid s$ holds exactly for $s=0$, and in addition for $s=\pm3$ when $n=3$. The exponents $s=m-2r$ give $T_1=0$, $T_2=\frac d4\binom21=\frac d2$, $T_3=0$ for $n\ne3$ and $T_3=\frac d8\big(\binom30+\binom33\big)=\frac d4$ for $n=3$, and $T_4=\frac d{16}\binom42=\frac{3d}8$. Substituting into $p_m^V=(T_m+\varepsilon)/2$ gives the stated values. ∎

**Proposition 3.3 (Moment of one nonzero label).** Let $V\in\{E_d,O_d\}$, let $\mathbf a\in\mathbb Z_d^2$ be nonzero and let $n=d/\gcd(a_1,a_2,d)$ be its order. If $n\ne3$ then

$$
F_{E_d}(\mathbf a)=F_{O_d}(\mathbf a)=\frac{3}{(d+1)(d+3)} .
$$

If $n=3$ then

$$
F_{E_d}(\mathbf a)=\frac{3d+35}{(d+1)(d+5)(d+7)},\qquad F_{O_d}(\mathbf a)=\frac{3d-5}{(d-1)(d+1)(d+5)} .
$$

Stance: suspected-novel (see §5).

**Proof.** By Lemma 3.1, $F_V(\mathbf a)=F_V((0,h))$ with $\gcd(h,d)=\gcd(a_1,a_2,d)$, so $h\not\equiv0$ and $d/\gcd(h,d)=n$; and $D_{(0,h)}=Z^h$. Let $A$ be the real diagonal matrix of Lemma 3.2 with entries $c_1,\dots,c_k$, $k=k_V$. For a unit vector $\psi\in V$, $\langle\psi|Z^h|\psi\rangle=\langle\psi|A|\psi\rangle=\sum_ic_i|\psi_i|^2$ is real, so $|\langle\psi|Z^h|\psi\rangle|^4=\mathrm{tr}(A^{\otimes4}\psi^{\otimes4})$. By cited facts (c) and (e), applied on $V\cong\mathbb C^k$, and since $24\binom{k+3}4=k(k+1)(k+2)(k+3)$,

$$
F_V((0,h))=\frac{\sum_{\sigma\in S_4}\prod_{c}\mathrm{tr}(A^{|c|})}{k(k+1)(k+2)(k+3)}=\frac{p_1^4+6p_1^2p_2+3p_2^2+8p_1p_3+6p_4}{k(k+1)(k+2)(k+3)},
$$

using the cycle types of $S_4$: one identity, six transpositions, three double transpositions, eight $3$-cycles and six $4$-cycles; here $p_m=p_m^V(h)$.

For $V=E_d$, $k=(d+1)/2$ and $k(k+1)(k+2)(k+3)=(d+1)(d+3)(d+5)(d+7)/16$. With the values of Lemma 3.2 for $n\ne3$ the numerator is $\frac1{16}\big(1+6(d+2)+3(d+2)^2+32+6(3d+8)\big)=\frac{3d^2+36d+105}{16}=\frac{3(d+5)(d+7)}{16}$. For $n=3$ the term $8p_1p_3$ increases by $8\cdot\frac12\cdot\frac d8=\frac{8d}{16}$, giving $\frac{3d^2+44d+105}{16}=\frac{(3d+35)(d+3)}{16}$.

For $V=O_d$, $k=(d-1)/2$ and $k(k+1)(k+2)(k+3)=(d-1)(d+1)(d+3)(d+5)/16$. For $n\ne3$ the numerator is $\frac1{16}\big(1+6(d-2)+3(d-2)^2+32+6(3d-8)\big)=\frac{3d^2+12d-15}{16}=\frac{3(d-1)(d+5)}{16}$. For $n=3$ the term $8p_1p_3$ changes by $8\cdot(-\frac12)\cdot\frac d8=-\frac{8d}{16}$, giving $\frac{3d^2+4d-15}{16}=\frac{(3d-5)(d+3)}{16}$.

Dividing by the respective denominators gives the four stated values. The computation is valid for every $k\ge1$, including $O_3$ with $k=1$. ∎

## 4. Extrinsic terms and gaps

**Theorem 4.1 (Extrinsic term of the parity sectors).** For every odd $d\ge3$:

$$
X(E_d)=\begin{cases}\dfrac4{d+3},&3\nmid d,\\ \dfrac4{d+3}+\dfrac{64}{(d+1)(d+3)(d+5)(d+7)},&3\mid d,\end{cases}
\qquad
X(O_d)=\begin{cases}\dfrac4{d+3},&3\nmid d,\\ \dfrac4{d+3}-\dfrac{64}{(d-1)(d+1)(d+3)(d+5)},&3\mid d.\end{cases}
$$

In particular $X(E_3)=7/10$ and $X(O_3)=1/2$. Stance: suspected-novel (see §5).

**Proof.** The labels $\mathbf a\in\mathbb Z_d^2$ of order dividing $3$ form the subgroup $(d/3)\mathbb Z_d^2$ of order $9$ when $3\mid d$ and the trivial subgroup otherwise, so the number $N_3$ of labels of order exactly $3$ is $8$ if $3\mid d$ and $0$ otherwise. Write $G=3/((d+1)(d+3))$ and $G_V^{(3)}$ for the order-$3$ value of Proposition 3.3. By Lemma 3.1 and Proposition 3.3,

$$
X(V)=\frac1d\Big(1+(d^2-1-N_3)\,G+N_3\,G_V^{(3)}\Big).
$$

If $3\nmid d$ this is $\frac1d\big(1+\frac{3(d-1)}{d+3}\big)=\frac1d\cdot\frac{4d}{d+3}=\frac4{d+3}$. If $3\mid d$ it is $\frac4{d+3}+\frac8d\big(G_V^{(3)}-G\big)$, and

$$
G_{E_d}^{(3)}-G=\frac{(3d+35)(d+3)-3(d+5)(d+7)}{(d+1)(d+3)(d+5)(d+7)}=\frac{8d}{(d+1)(d+3)(d+5)(d+7)},
$$

$$
G_{O_d}^{(3)}-G=\frac{(3d-5)(d+3)-3(d-1)(d+5)}{(d-1)(d+1)(d+3)(d+5)}=\frac{-8d}{(d-1)(d+1)(d+3)(d+5)} .
$$

Multiplying by $8/d$ gives the corrections $\pm64/(\cdots)$. At $d=3$: $\frac46+\frac{64}{4\cdot6\cdot8\cdot10}=\frac7{10}$ and $\frac46-\frac{64}{2\cdot4\cdot6\cdot8}=\frac12$. ∎

**Corollary 4.2 (Gaps of the parity sectors).** With the single-qudit intrinsic term of Convention 2.2, for every odd $d\ge3$ the gaps are as follows. The even sector has $k=(d+1)/2$, odd exactly when $d\equiv1\pmod4$; the odd sector has $k=(d-1)/2$, odd exactly when $d\equiv3\pmod4$.

| Sector and class of $d$ | $\Delta M$ when $3\nmid d$ | $\Delta M$ when $3\mid d$ |
| --- | --- | --- |
| $E_d$, $d\equiv1\pmod4$ | $\dfrac{2(d-1)}{(d+3)(d+5)}$ | $\dfrac{2(d^2+4d-13)}{(d+1)(d+5)(d+7)}$ |
| $E_d$, $d\equiv3\pmod4$ | $\dfrac{2(d+1)}{(d+3)(d+7)}$ | $\dfrac{2(d^3+7d^2+11d-27)}{(d+1)(d+3)(d+5)(d+7)}$ |
| $O_d$, $d\equiv3\pmod4$ | $\dfrac{2}{d+3}$ | $\dfrac{2(d^3+5d^2-d+27)}{(d-1)(d+1)(d+3)(d+5)}$ |
| $O_d$, $d\equiv1\pmod4$ | $\dfrac{2(d^2+6d+17)}{(d+1)(d+3)(d+5)}$ | $\dfrac{2(d^2+2d+5)}{(d-1)(d+1)(d+5)}$ |

Every entry is positive, so $\Delta M(E_d)>0$ and $\Delta M(O_d)>0$ for every odd $d\ge3$. Stance: suspected-novel (see §5).

**Proof.** The intrinsic terms are: for $E_d$ with $k=(d+1)/2$ odd, $I=3/(k+2)=6/(d+5)$; for $E_d$ with $k$ even, $I=3(k+2)/((k+1)(k+3))=6(d+5)/((d+3)(d+7))$; for $O_d$ with $k=(d-1)/2$ odd, $I=6/(d+3)$; for $O_d$ with $k$ even, $I=6(d+3)/((d+1)(d+5))$. Subtracting Theorem 4.1, with $\Pi_E=(d+1)(d+3)(d+5)(d+7)$ and $\Pi_O=(d-1)(d+1)(d+3)(d+5)$:

$$
\begin{aligned}
\frac6{d+5}-\frac4{d+3}&=\frac{2(d-1)}{(d+3)(d+5)},\\
\frac{2(d-1)}{(d+3)(d+5)}-\frac{64}{\Pi_E}&=\frac{2(d^3+7d^2-d-39)}{\Pi_E}=\frac{2(d^2+4d-13)}{(d+1)(d+5)(d+7)},\\
\frac{6(d+5)}{(d+3)(d+7)}-\frac4{d+3}&=\frac{2(d+1)}{(d+3)(d+7)},\\
\frac{2(d+1)}{(d+3)(d+7)}-\frac{64}{\Pi_E}&=\frac{2(d+1)^2(d+5)-64}{\Pi_E}=\frac{2(d^3+7d^2+11d-27)}{\Pi_E},\\
\frac6{d+3}-\frac4{d+3}&=\frac2{d+3},\\
\frac2{d+3}+\frac{64}{\Pi_O}&=\frac{2(d-1)(d+1)(d+5)+64}{\Pi_O}=\frac{2(d^3+5d^2-d+27)}{\Pi_O},\\
\frac{6(d+3)}{(d+1)(d+5)}-\frac4{d+3}&=\frac{6(d+3)^2-4(d+1)(d+5)}{(d+1)(d+3)(d+5)}=\frac{2(d^2+6d+17)}{(d+1)(d+3)(d+5)},\\
\frac{2(d^2+6d+17)}{(d+1)(d+3)(d+5)}+\frac{64}{\Pi_O}&=\frac{2(d+3)(d^2+2d+5)}{\Pi_O}=\frac{2(d^2+2d+5)}{(d-1)(d+1)(d+5)},
\end{aligned}
$$

where the second line uses $(d^2+4d-13)(d+3)=d^3+7d^2-d-39$ and the last uses $2(d-1)(d^2+6d+17)+64=2(d^3+5d^2+11d+15)=2(d+3)(d^2+2d+5)$. Positivity for odd $d\ge3$: all denominators are products of positive factors; $d-1>0$; $d^2+4d-13\ge8$ for $d\ge3$; $d^3+7d^2+11d-27\ge96$ for $d\ge3$; $d^3+5d^2-d+27>0$ because $d^3\ge d$; and $d^2+6d+17$, $d^2+2d+5$, $d+1$, $2$ are positive. ∎

**Remark 4.3 (Small cases).** The corollary gives $\Delta M(E_3)=1/10$, $\Delta M(O_3)=1/2$, $\Delta M(E_5)=1/10$, $\Delta M(O_5)=3/10$, $\Delta M(E_7)=4/35$, $\Delta M(O_7)=1/5$, $\Delta M(E_9)=13/140$ and $\Delta M(O_9)=13/70$. For $O_3$ the sector is one-dimensional, $I(1)=1$, and the gap $1/2$ equals the linear stabilizer entropy of cited fact (b) of the unique state $(|1\rangle-|2\rangle)/\sqrt2$ of $O_3$, as it must since $1-I(1)=0$. Stance: repo-derived (instances of Corollary 4.2).

**Remark 4.4 (Comparison with the whole space).** For $3\nmid d$ both sectors have extrinsic term $4/(d+3)$, which exceeds the intrinsic term $3/(d+2)$ of $\mathbb C^d$ itself, because $4(d+2)-3(d+3)=d-1>0$. Stance: repo-derived.

**Remark 4.5 (Boundaries).** The results concern only odd $d$, the two parity sectors, the single-qudit Weyl–Heisenberg groups on both the large and the small space, and the linear stabilizer entropy of cited fact (b). They give no statement about even $d$, about multiqubit Weyl–Heisenberg conventions on either space, about other subspaces, about subspaces with zero or negative gap, or about whether the parity sectors are extremal among subspaces of the same dimension. Stance: repo-derived.

## 5. Sources and literature status

| Source | Exact scope and use |
| --- | --- |
| S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd, *Stabilizer Entropy of Subspaces*, arXiv:2512.23013v1, Sec. II Eqs. (II.1)–(II.4), (II.8), (II.25); Sec. III Eqs. (III.4)–(III.8), (III.11); App. D Eq. (D.5) (equation numbers of the arXiv HTML rendering) | `literature-attested`: the Weyl operators, the linear stabilizer entropy, the average stabilizer-entropy gap, the Haar fourth moment $\binom{d_S+3}4^{-1}\Pi_{\mathrm{sym}^4}$, the single-qudit intrinsic term, and the cycle-trace identity, used as cited facts (a)–(e). The paper contains no statement about parity sectors. |
| — | `repo-derived`: Conventions 2.1, 2.2, Lemmas 3.1, 3.2, Remarks 4.3, 4.4, 4.5. |
| — | `suspected-novel`: Proposition 3.3, Theorem 4.1, Corollary 4.2. Searched: the full TeX source of arXiv:2512.23013v1; arXiv:2512.19657v2, *Extremizing Measures of Magic on Pure States*, which treats non-degenerate Clifford eigenstates and not Haar averages over Clifford eigenspaces; web and arXiv searches combining stabilizer entropy, stabilizer Rényi entropy, nonstabilizerness or magic with parity sector, parity eigenspace, Fourier or Clifford eigenspace, qudit cat state, symmetric subspace, $\mathbb Z_2$ symmetry sector and average magic gap. No statement of these results was found in the searched scope; this establishes no worldwide priority. |

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后,并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）
