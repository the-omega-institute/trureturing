# Long palindromic markers at singleton saturation

## 1. Words, exponents and the source fixed points

**Definition 1.1 (Words and exponents).** For a finite alphabet $B$, write $`B^*`$ for its free monoid, with concatenation as multiplication and empty word $\varepsilon$. A factor is a contiguous subword. Reversal is denoted by $w\mapsto\overline w$; a palindrome satisfies $w=\overline w$. For a nonempty finite word $w=w_0\cdots w_{n-1}$, a positive integer $t\le n$ is a period if $w_j=w_{j+t}$ whenever $0\le j<n-t$. Its least positive period is $\operatorname{per}(w)$, and its exponent is $|w|/\operatorname{per}(w)$. For a one-sided infinite word $x$, put

$$
E(x)=\sup\left\{\frac{|w|}{\operatorname{per}(w)}:
 w\text{ is a nonempty finite factor of }x\right\}.
$$

Define $`E^*(x)=+\infty`$ when $E(x)=+\infty$; otherwise define

$$
E^*(x)=\lim_{N\to\infty}\sup\left\{
\frac{|w|}{\operatorname{per}(w)}:
 w\text{ is a factor of }x,\ |w|\ge N\right\}.
$$

These are the ordinary and asymptotic critical exponents, with the infinite-exponent convention of Dvořáková and Pelantová, *The limit of repetition thresholds of rich sequences*, [arXiv:2509.06104v1, Introduction](https://arxiv.org/html/2509.06104v1#S1).

**Definition 1.2 (Richness and marked return morphisms).** A finite word $w$ is rich if it has exactly $|w|+1$ distinct palindromic factors, counting $\varepsilon$. An infinite word is rich if each of its finite factors is rich. A complete return to a nonempty word $p$ is a finite word having $p$ as prefix and suffix and exactly two occurrences of $p$, allowing these occurrences to overlap. An injective monoid morphism $`\eta:A^*\to B^*`$ belongs to $P_{\mathrm{ret}}$ with chosen nonempty marker $p$ if $p$ is a palindrome and, for every $i\in A$,

$$
\eta(i)=p q_i,\qquad q_i=\overline{q_i},
$$

and $\eta(i)p$ is a palindromic complete return to $p$. The words $q_i$ may be empty. This is the convention of [Dvořáková–Pelantová, Definition 18](https://arxiv.org/html/2509.06104v1#Thmtheorem18), following Balková, Pelantová and Starosta, *Infinite words with finite defect*, Advances in Applied Mathematics 47 (2011), 562–574.

**Definition 1.3 (The fixed points and their spectral target).** For $m\ge3$, put $A_m=\{0,\ldots,m-1\}$ and define the monoid morphism $\varphi_m$ by

$$
\varphi_m(i)=0(i+1)\quad(0\le i<m-1),\qquad
\varphi_m(m-1)=0(m-1)(m-1).
$$

Here every parenthesized integer denotes one letter. Let $u_m=\varphi_m^\omega(0)$. For $r\ge3$, let $\Lambda_r\in(2,3)$ satisfy

$$
\Lambda_r^r(\Lambda_r-2)=1,
\qquad e_r=1+\frac{1}{3-\Lambda_r}.
$$

The function $t\mapsto t^r(t-2)$ is strictly increasing for $t>2$, so this specifies $\Lambda_r$ uniquely. The identity

$$
E^*(u_{2r+1})=e_r
$$

is literature-attested: [Dvořáková–Pelantová, §2, equation (4)](https://arxiv.org/html/2509.06104v1#S2.E4), recalling Dvořáková, Klouda and Pelantová, *The asymptotic repetition threshold of sequences rich in palindromes*, European Journal of Combinatorics 126 (2025), 104124. Their equation $t^{2r}(t-2)^2=1$ gives the displayed equation for $\Lambda_r$ because $\Lambda_r>2$.

## 2. A boundary obstruction for palindromic separators

**Theorem 2.1 (All but one singleton separator; repo-derived).** Let $B$ be a finite alphabet with $|B|\ge2$, let $S\subseteq B$ have $|S|=|B|-1$, and let $p\in B^*$ be a palindrome with $|p|\ge2$. Let $x$ be an infinite word over $B$. Suppose that $pp$ is a factor of $x$ and that $pcp$ is a factor of $x$ for every $c\in S$. Then

$$
E(x)\ge\frac52.
$$

More precisely, write $a,b$ for the first two letters of $p$. If $a\in S$, then $a^3$ is a factor of $x$. If $a\notin S$ and $b=a$, then $a^4$ is a factor of $x$. If $a\notin S$ and $b\ne a$, then $babab$ is a factor of $x$.

*Proof.* Since $p$ is a palindrome, its last letter is $a$ and its last two letters are $ba$.

If $a\in S$, the factor $pap$ contains the three consecutive letters consisting of the last letter of the first $p$, the separator $a$, and the first letter of the second $p$. These letters form $a^3$, whose least period is one and whose exponent is three.

Suppose $a\notin S$. Since $S$ omits exactly one letter of $B$, it follows that $S=B\setminus\{a\}$. If $b=a$, the last two letters of the first $p$ and first two letters of the second $p$ in $pp$ form $a^4$. Its exponent is four.

If $b\ne a$, then $b\in S$, so $pbp$ is a factor of $x$. The last two letters of its first copy of $p$, its separator, and the first two letters of its second copy of $p$ form

$$
ba\,b\,ab=babab.
$$

This word has period two and does not have period one because $a\ne b$. Its least positive period is therefore two and its exponent is $5/2$. Each of the three cases supplies an actual finite factor of $x$ with exponent at least $5/2$, as required. $\square$

## 3. Exclusion of every longer-marker equality row

**Theorem 3.1 (Universal longer-marker saturation).** Let $r\ge3$ and $\ell\ge2$ be integers. Let $B$ be a finite alphabet of size $r+1$, let $p\in B^*$ be a palindrome of length $\ell$, and let $`\eta:A_{2r+1}^*\to B^*`$ be an injective monoid morphism whose actual infinite image $x=\eta(u_{2r+1})$ has alphabet exactly $B$. Assume that, for every $0\le i\le2r$, there is a palindrome $q_i$, possibly empty, such that $\eta(i)=p q_i$ and $\eta(i)p$ is a palindromic complete return to $p$. Put $h_i=|\eta(i)|$ and assume

$$
h_0=\ell,\qquad h_1=\cdots=h_r=\ell+1,
$$

and

$$
h_{r+j}=h_r+\sum_{i=0}^{j-1}2^{j-1-i}h_i
\qquad(1\le j\le r).
$$

Then

$$
E\bigl(\eta(u_{2r+1})\bigr)\ge\frac52
   > E^*(u_{2r+1}).
$$

Consequently, under these exact hypotheses, $\eta(u_{2r+1})$ is not rich or $`E(\eta(u_{2r+1}))>E^*(u_{2r+1})`$.

*Proof.* Because $\eta(0)$ begins with $p$ and has length $|p|$, it equals $p$. For $1\le i\le r$, the length condition gives a letter $c_i\in B$ with

$$
\eta(i)=p c_i.
$$

Injectivity implies that these $r$ letters are pairwise distinct. Thus $S=\{c_1,\ldots,c_r\}$ has cardinality $r=|B|-1$.

Every letter of $A_{2r+1}$ occurs in $u_{2r+1}$. Indeed, $0$ occurs in $\varphi_{2r+1}^0(0)$, and whenever $k<2r$ occurs in $\varphi_{2r+1}^k(0)$, its image contains $k+1$, so $k+1$ occurs in $\varphi_{2r+1}^{k+1}(0)$. These iterates are prefixes of $u_{2r+1}$ because $\varphi_{2r+1}(0)$ begins with $0$.

All images under $\eta$ begin with the nonempty word $p$, so the morphism is nonerasing. An occurrence of any letter $i$ in the one-sided infinite source has a following letter. At the corresponding concatenation boundary in $x$, the factor $\eta(i)p$ therefore occurs. Taking $i=0$ gives $pp$; taking $i=1,\ldots,r$ gives $p c_i p$. Theorem 2.1 now yields $E(x)\ge5/2$. This inference concerns factors in the actual infinite concatenation.

To compare this lower bound with the spectral target, observe that

$$
\left(\frac73\right)^r\left(\frac73-2\right)
 =\frac{7^r}{3^{r+1}}
 \ge\frac{343}{81}>1.
$$

Since $t^r(t-2)$ is strictly increasing for $t>2$ and has value one at $\Lambda_r$, it follows that $\Lambda_r<7/3$. Hence

$$
E^*(u_{2r+1})
 =1+\frac{1}{3-\Lambda_r}
 <1+\frac{1}{2/3}=\frac52.
$$

The asserted strict inequality and its disjunctive consequence follow. $\square$

## 4. Strictness of the conditional marker-cost bound

**Definition 4.1 (Explicit spectral and lattice conditions).** Let $r\ge3$ be an integer, and let $M_r$ be the incidence matrix of $\varphi_{2r+1}$ with column $j$ equal to the letter-count vector of $\varphi_{2r+1}(j)$. Let $\beta_r\in(1,2)$ be the root of $\beta_r^r(\beta_r-2)=-1$, and put

$$
v_{\beta_r}=
\bigl(\beta_r^{2r-1}(\beta_r-2),
      \beta_r^{2r-2}(\beta_r-2),\ldots,
      \beta_r-2,1\bigr)^T.
$$

This is the $\beta_r$ right eigenvector in [Dvořáková–Pelantová, Appendix, P2](https://arxiv.org/html/2509.06104v1#S9). For a length row $h=(h_0,\ldots,h_{2r})$, impose explicitly both the cancellation and the lattice equations

$$
h\cdot v_{\beta_r}=0,
\qquad
h_{r+j}=h_r+\sum_{i=0}^{j-1}2^{j-1-i}h_i
\quad(1\le j\le r).
$$

Write

$$
T=\sum_{i=0}^{2r}h_i,
\qquad C_r(\ell)=(\ell+1)(2^{r+1}+r-1)-2^r.
$$

**Corollary 4.2 (The longer-marker cost is strict).** Let $r\ge3$ and $\ell\ge2$ be integers. Let $`\eta:A_{2r+1}^*\to B^*`$ belong to $P_{\mathrm{ret}}$ with chosen marker $p$ of length $\ell$, where $|B|=r+1$ and the letters occurring in $\eta(u_{2r+1})$ are exactly $B$. For $h_i=|\eta(i)|$, assume the explicit cancellation and lattice conditions of Definition 4.1. If $\eta(u_{2r+1})$ is rich and

$$
E\bigl(\eta(u_{2r+1})\bigr)\le E^*(u_{2r+1}),
$$

then

$$
T>(\ell+1)(2^{r+1}+r-1)-2^r.
$$

In particular, when $r=3$ these hypotheses imply $T\ge18\ell+12$, and thus $T\ge48$ for every chosen marker of length at least two.

*Proof.* The [marker-cost inequality and its equality characterization](https://github.com/the-omega-institute/trureturing/issues/22900#issuecomment-6455260239) for injective $P_{\mathrm{ret}}$ morphisms with the stated output alphabet, chosen marker and explicit spectral cancellation gives $T\ge C_r(\ell)$, and equality forces

$$
h_0=\ell,\qquad h_1=\cdots=h_r=\ell+1.
$$

If equality held, all hypotheses of Theorem 3.1 would hold, including the lattice equations imposed here. That theorem would give $E(\eta(u_{2r+1}))>E^*(u_{2r+1})$, contradicting the assumed ordinary exponent bound. Therefore $T>C_r(\ell)$.

For $r=3$, summing the imposed lattice equations gives

$$
T=8h_0+4h_1+2h_2+4h_3,
$$

so $T$ is even. Since $C_3(\ell)=18\ell+10$ is even, strictness gives $T\ge18\ell+12$. Finally $\ell\ge2$ gives $T\ge48$. $\square$

## 追加锚（本行以下为增补区）
