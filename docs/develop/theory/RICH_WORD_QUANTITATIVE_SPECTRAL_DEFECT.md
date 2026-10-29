# Quantitative spectral defect of ordinary morphic repetition

## 1. Words, the source substitution and the spectral normalization

**Definition 1.1 (Ordinary exponent).** For a finite alphabet $B$, write $`B^*`$ for its free monoid. A factor is a contiguous subword. A positive integer $p\le |z|$ is a period of a nonempty finite word $z=z_0\cdots z_{|z|-1}$ if $z_j=z_{j+p}$ for $0\le j<|z|-p$. Write $\operatorname{per}(z)$ for its least period. For a one-sided infinite word $x$, its ordinary critical exponent is the extended real number

$$
E(x)=\sup\left\{\frac{|z|}{\operatorname{per}(z)}:
 z\text{ is a nonempty finite factor of }x\right\}.
$$

If $E(x)=+\infty$, put $`E^*(x)=+\infty`$; otherwise put

$$
E^*(x)=\lim_{N\to\infty}\sup\left\{
\frac{|z|}{\operatorname{per}(z)}:
 z\text{ is a factor of }x,\ |z|\ge N\right\}.
$$

These are the conventions in Dvořáková and Pelantová, *The limit of repetition thresholds of rich sequences*, [arXiv:2509.06104v1, Introduction](https://arxiv.org/html/2509.06104v1#S1), published in *The Electronic Journal of Combinatorics* 33(2), P2.15, [doi:10.37236/14600](https://doi.org/10.37236/14600). All numbered source results cited below use the arXiv version.

**Definition 1.2 (Source words and length rows).** For an integer $r\ge3$, let $A_r=\{0,\ldots,2r\}$ and define

$$
\varphi(i)=0(i+1)\quad(0\le i<2r),\qquad
\varphi(2r)=0(2r)(2r),\qquad u=u_{2r+1}=\varphi^\omega(0).
$$

Each parenthesized integer denotes one letter. Let $M$ be the incidence matrix whose column $i$ is the Parikh vector of $\varphi(i)$, and let $b_i$ be the $i$th coordinate column vector. For a finite word $w$, let $\vec w$ be its Parikh column vector. Given a nonempty finite alphabet $B$ and a nonerasing monoid morphism $`\eta:A_r^*\to B^*`$, write

$$
h=(h_0,\ldots,h_{2r}),\qquad h_i=|\eta(i)|,\qquad
H=\sum_{i=0}^{2r}h_i.
$$

Thus $h_i\ge1$, $H>0$ and $|\eta(w)|=h\vec w$.

**Definition 1.3 (Spectral parameters).** Let $\Lambda\in(2,3)$ and $\beta\in(1,2)$ be specified by

$$
\Lambda^r(\Lambda-2)=1,\qquad
\beta^r(\beta-2)=-1,
$$

where $\beta$ is the positive root of $t^r-t^{r-1}-\cdots-t-1$. Put

$$
L=\frac{1}{3-\Lambda},\qquad e_r=1+L,\qquad
\kappa_r=\frac{\log\Lambda}{\log\beta},
$$

and, for each eigenvalue $\lambda$ of $M$, use the normalization

$$
v_\lambda=
\bigl(\lambda^{2r-1}(\lambda-2),
 \lambda^{2r-2}(\lambda-2),\ldots,\lambda-2,1\bigr)^T.
$$

In particular,

$$
\rho=\frac{|h v_\beta|}{H}.
$$

The source identity $`E^*(u_{2r+1})=e_r`$ and the eigenvector normalization are literature-attested: [arXiv:2509.06104v1, §2, equation (4), and Appendix P1–P2](https://arxiv.org/html/2509.06104v1). The parameter $r$ here is the parameter $d$ in that paper's Type I/II formulas.

## 2. A uniform quantitative defect

**Theorem 2.1 (Effective spectral defect; repo-derived).** There is an effective assignment of positive rational numbers $r\mapsto c_r$ such that, for every integer $r\ge3$, every nonempty finite alphabet $B$ and every nonerasing monoid morphism $`\eta:A_r^*\to B^*`$,

$$
E\bigl(\eta(u_{2r+1})\bigr)
 \ge e_r+c_r\min(1,\rho)^{\kappa_r}.
$$

The inequality uses the ordinary extended-real critical exponent. No injectivity, richness, synchronization, marker or description of the output bispecial factors is assumed. An effective rational choice is given in the proof.

*Proof.* Fix $r$. We first use complete returns to obtain actual finite factors of the output. If $s<t$ are two consecutive occurrences of a nonempty source factor $w$ and $R=u_s\cdots u_{t-1}$ is the corresponding return word, then $Rw$ is a factor of $u$ having $w$ as both prefix and suffix. Consequently,

$$
z=\eta(Rw)=\eta(R)\eta(w)
$$

is a finite factor of $x=\eta(u)$, having $\eta(w)$ as both prefix and suffix. Set $p=|\eta(R)|>0$ and $q=|\eta(w)|>0$. Then $|z|=p+q$, and the equality of its prefix and suffix of length $q$ says precisely that $z_j=z_{j+p}$ for $0\le j<q$. Thus $p$ is a period of $z$. It need not be its least period, and extra occurrences of $\eta(w)$ cause no difficulty. We obtain

$$
E(x)\ge\frac{|z|}{\operatorname{per}(z)}
 \ge 1+\frac{|\eta(w)|}{|\eta(R)|}
 =1+\frac{h\vec w}{h\vec R}. \tag{1}
$$

This argument also covers overlapping occurrences in the source. It makes no assertion that $\eta(w)$ is bispecial or that $\eta(R)$ is a shortest output return word.

For the source factors and returns in (1), we reuse the Type I/II data and Lemmas 8–9 of [arXiv:2509.06104v1, §3](https://arxiv.org/html/2509.06104v1#S3). Let

$$
\mathsf A=(M-2I)(3I-M)^{-1},
$$

$$
\mathsf B_i=(3I-M)^{-1}
 +2(M-2I)(M-I)^{-1}(M^i-I)(3I-M)^{-1}
 \quad(0\le i<2r).
$$

With $b=b_{2r}$ and $i\equiv n\pmod{2r}$, those lemmas give

$$
f_n=\mathsf A M^n b-\mathsf B_i b_0. \tag{2}
$$

For every $n\ge0$ there is a Type I factor $w_n^{\mathrm I}$ with a return word $R_n^{\mathrm I}$ having

$$
\vec w_n^{\mathrm I}=f_n+M^n b,\qquad
\vec R_n^{\mathrm I}=M^n b. \tag{3}
$$

For every $n\ge2r$ there is a Type II factor $w_n^{\mathrm {II}}$ with a return word $R_n^{\mathrm {II}}$ having

$$
\vec w_n^{\mathrm {II}}=f_n,\qquad
\vec R_n^{\mathrm {II}}=M^n b_0. \tag{4}
$$

The index $n$ in (4) is $n-2r$ in the source's Type II series. These are actual source return words supplied by Lemma 9, not just vectors satisfying a recurrence. Their source minimality is unnecessary for (1).

To compute the excess of the ratios in (1) above $L$, use $b_0=(M-2I)b$ and define

$$
T_{\mathrm I}=\mathsf A-(L-1)I,\qquad
T_{\mathrm {II}}=\mathsf A-L(M-2I).
$$

Equations (2)–(4) give, for the respective allowed indices,

$$
\begin{aligned}
\Delta_{\mathrm I}(n)
 &=h\vec w_n^{\mathrm I}-Lh\vec R_n^{\mathrm I}
   =hT_{\mathrm I}M^n b-h\mathsf B_i b_0,\\
\Delta_{\mathrm {II}}(n)
 &=h\vec w_n^{\mathrm {II}}-Lh\vec R_n^{\mathrm {II}}
   =hT_{\mathrm {II}}M^n b-h\mathsf B_i b_0.
\end{aligned} \tag{5}
$$

Here the corresponding scalar rational functions are

$$
\begin{aligned}
g_{\mathrm I}(z)
 &=\frac{z-2}{3-z}-\frac{\Lambda-2}{3-\Lambda}
   =\frac{z-\Lambda}{(3-z)(3-\Lambda)},\\
g_{\mathrm {II}}(z)
 &=\frac{z-2}{3-z}-\frac{z-2}{3-\Lambda}
   =(z-2)g_{\mathrm I}(z).
\end{aligned} \tag{6}
$$

Both functions vanish at $\Lambda$. At $\beta$ they have opposite signs:

$$
g_{\mathrm I}(\beta)<0<g_{\mathrm {II}}(\beta),\qquad
0<g_{\mathrm {II}}(\beta)<-g_{\mathrm I}(\beta). \tag{7}
$$

We now bound all other spectral contributions uniformly in the length row. Appendix P1 of the source gives

$$
\chi_M(z)=(z^{r+1}-2z^r-1)
 (z^r-z^{r-1}-\cdots-z-1).
$$

All its roots are distinct; the only roots of modulus greater than or equal to one are $\Lambda$ and $\beta$. Write $S$ for its root set and $S_0=S\setminus\{\Lambda,\beta\}$. For $\lambda\in S$, define the spectral projector

$$
P_\lambda=\prod_{\substack{\mu\in S\\\mu\ne\lambda}}
 \frac{M-\mu I}{\lambda-\mu}.
$$

Thus $M^n=\sum_{\lambda\in S}\lambda^nP_\lambda$ and $T_jP_\lambda=g_j(\lambda)P_\lambda$ for $j\in\{\mathrm I,\mathrm {II}\}$. The inverses in (2) exist since neither one nor three is a root of $\chi_M$.

For clarity about the coefficient of the normalized $v_\beta$, take the left eigenvector from Appendix P2:

$$
\ell_\beta=
 \left(\frac{\beta^{i+1}-2\beta^i+1}{\beta-1}
 \right)_{i=0}^{2r},\qquad
q_\beta=\frac{\ell_\beta b}{\ell_\beta v_\beta}.
$$

The denominator is nonzero because the eigenvalue is simple. Moreover,

$$
\ell_\beta b=\frac{1-\beta^r}{\beta-1}\ne0,
\qquad P_\beta b=q_\beta v_\beta. \tag{8}
$$

The first identity follows from $\beta^r(\beta-2)=-1$. In particular, $q_\beta$ is a nonzero real algebraic number.

For a complex vector, let $\|\cdot\|_\infty$ denote the maximum of the moduli of its coordinates. Define the nonnegative real algebraic number

$$
C=\max_{0\le i<2r}\|\mathsf B_i b_0\|_\infty
 +\sum_{\lambda\in S_0}
 \max_{j\in\{\mathrm I,\mathrm {II}\}}|g_j(\lambda)|
 \,\|P_\lambda b\|_\infty.
$$

Choose an integer $R>C$. Since $h_i\ge0$ and $\sum h_i=H$, the inequalities $|h y|\le H\|y\|_\infty$ and $|\lambda|^n\le1$ for $\lambda\in S_0$ show from (5)–(8) that

$$
\Delta_j(n)=g_j(\beta)q_\beta(hv_\beta)\beta^n
                  +\mathcal R_j(n),\qquad
|\mathcal R_j(n)|\le RH. \tag{9}
$$

The bound is simultaneous for every length row, every allowed index and both types. It includes every residue $i=n\bmod2r$ in (2).

Set $\alpha=g_{\mathrm {II}}(\beta)|q_\beta|>0$ and choose a positive integer $J$ with $J\alpha>1$. Whenever $hv_\beta\ne0$, choose Type I if $q_\beta hv_\beta<0$ and Type II if $q_\beta hv_\beta>0$. Equations (7) and (9) then imply for the selected type $j$

$$
\Delta_j(n)\ge \frac{|hv_\beta|}{J}\beta^n-RH.
 \tag{10}
$$

This selection uses both source series, so either sign of the spectral defect is covered.

We also need a uniform upper bound for the actual output period in (1). The positive eigenvector $v_\Lambda$ has coordinates $\Lambda^{r-1},\Lambda^{r-2},\ldots,\Lambda^{-r},1$. Hence its largest and smallest coordinates are $\Lambda^{r-1}$ and $\Lambda^{-r}$. Coordinatewise, $b_k\le\Lambda^r v_\Lambda$ for every coordinate vector $b_k$. Since $M$ has nonnegative entries,

$$
M^n b_k\le\Lambda^{n+r}v_\Lambda,
\qquad
hM^n b_k\le H\Lambda^{n+2r-1}
 \le DH\Lambda^n,\quad D=3^{2r-1}. \tag{11}
$$

This applies to both return vectors in (3)–(4).

All the quantities used to choose $R$ and $J$ depend only on $r$ and are algebraic. Integer polynomial root isolation, followed by arithmetic and comparison of real algebraic numbers, computes them: choose any integer $R>C$, and then increment $J$ until $J\alpha>1$. Distinct roots, nonzero denominators and $\alpha>0$ ensure termination of these finite computations. Define integers and a rational number by

$$
T=2^{2r}+J(R+1)+1,\qquad
D=3^{2r-1},\qquad
c_r=\frac{1}{D(2T)^3}>0. \tag{12}
$$

For definiteness, $R$ may be the least positive integer strictly greater than $C$, and $J$ the least positive integer with $J\alpha>1$; algebraic comparison decides both choices. Formula (12) therefore specifies an effective rational assignment without choosing any morphism or output alphabet.

Suppose first that $\rho>0$, and put $t=\min(1,\rho)$. Choose the least integer $n\ge0$ with

$$
t\beta^n\ge T. \tag{13}
$$

It exists because $\beta>1$. Since $t\le1$ and $T>2^{2r}>\beta^{2r}$, this index satisfies $n>2r$, so either source series is available. Minimality also gives

$$
\beta^n<\frac{\beta T}{t}<\frac{2T}{t}. \tag{14}
$$

For the type selected in (10), $|hv_\beta|=\rho H\ge tH$. Thus (10), (12) and (13) imply

$$
\Delta_j(n)\ge H\left(\frac{t\beta^n}{J}-R\right)
 \ge H\left(\frac{T}{J}-R\right)\ge H. \tag{15}
$$

Take the actual source factor and return from (3) or (4) at this index. The finite output factor $\eta(R_n^j w_n^j)$ in (1) has the certified period $h\vec R_n^j$. Using (11) and (15) in (1) yields

$$
E(x)\ge e_r+\frac{\Delta_j(n)}{h\vec R_n^j}
       \ge e_r+\frac{1}{D\Lambda^n}. \tag{16}
$$

This witness is finite for each individual morphism. To locate an occurrence explicitly, one can scan the increasing prefixes $\varphi^k(0)$ for two occurrences with the factor and return Parikh vectors in (3) or (4). Existence of those source occurrences guarantees termination; a match itself certifies the needed prefix and suffix equality. There is no inference from finite sampling to a universal statement.

Finally $0<\kappa_r<3$. Indeed $z^r-z^{r-1}-\cdots-z-1$ has exactly one positive root, and its value at $z=3/2$ is $2-(3/2)^r<0$. Thus $\beta>3/2$, and $\beta^3>27/8>3>\Lambda$. By (14) and $\Lambda^n=(\beta^n)^{\kappa_r}$,

$$
\frac{1}{D\Lambda^n}
 \ge\frac{t^{\kappa_r}}{D(2T)^{\kappa_r}}
 \ge\frac{t^{\kappa_r}}{D(2T)^3}
 =c_rt^{\kappa_r}. \tag{17}
$$

This proves the claim when $\rho>0$.

For $\rho=0$, we still need the asserted lower bound $E(x)\ge e_r$. Use Type I in (1). The positive left and right Perron eigenvectors imply $hP_\Lambda b>0$. All other eigenvalues have modulus strictly smaller than $\Lambda$, so (2) gives

$$
\lim_{n\to\infty}
 \frac{h(f_n+M^n b)}{hM^n b}
 =1+\frac{\Lambda-2}{3-\Lambda}=L.
$$

Taking the supremum of the finite-factor lower bounds (1) therefore gives $E(x)\ge1+L=e_r$. If $E(x)=+\infty$, the same finite-factor inequalities remain valid and the theorem's extended-real conclusion holds directly. This completes all cases. $\square$

The literature-attested inputs to this proof are the source Type I/II returns, Lemmas 8–9, the simple-spectrum data of Appendix P1–P2 and the spectral decomposition of Lemma 20. The quantitative bound, its effective constant (12) and its use of actual output periods are repo-derived. The opposite signs in (7) also underlie source Proposition 17, whose statement includes a finite-boundary hypothesis and exact equality of exponents; neither hypothesis is used here. This is a mathematical extension of that supplied argument, with no assertion of global literature priority.

## 3. Near attainment on the morphic upper route

**Corollary 3.1 (Necessary restriction on near-attaining images).** Let $r\ge3$, let $c_r$ be as in (12), and let $`\eta:A_r^*\to B^*`$ be nonerasing. If

$$
0<\varepsilon<c_r,\qquad
E\bigl(\eta(u_{2r+1})\bigr)\le e_r+\varepsilon,
$$

then

$$
\rho\le\left(\frac{\varepsilon}{c_r}\right)^{1/\kappa_r}.
$$

In particular, this holds whenever the image is rich and its actual alphabet has exactly $r+1$ letters. If a family of such morphic images has ordinary exponents tending to $e_r$, its normalized defects $\rho$ tend to zero.

*Proof.* Theorem 2.1 gives $\min(1,\rho)^{\kappa_r}\le\varepsilon/c_r<1$. Consequently $\rho<1$, and taking the positive $\kappa_r$th root proves the displayed bound. Apply the bound eventually along any family whose exponent excess tends to zero. Richness and the actual output alphabet impose no additional step in this inference. $\square$

**Corollary 3.2 (Exact attainment forces cancellation).** For every nonerasing $`\eta:A_r^*\to B^*`$, if $E(\eta(u_{2r+1}))=e_r$, then $hv_\beta=0$.

*Proof.* The strictly positive constant in Theorem 2.1 forces $\min(1,\rho)=0$, hence $\rho=0$. $\square$

**Definition 3.3 (Scope of the unrestricted threshold problem).** A finite word $w$ is rich if it has exactly $|w|+1$ distinct palindromic factors, including the empty word; an infinite word is rich if every finite factor is rich. Let $\mathcal C_d$ be all one-sided infinite rich words over an alphabet of $d$ letters, without additional recurrence, morphicity or aperiodicity conditions. Put

$$
RT(\mathcal C_d)=\inf_{x\in\mathcal C_d}E(x).
$$

The unrestricted target is $`RT(\mathcal C_d)=E^*(u_{2d-1})`$ for every $d\ge2$, as in source Conjecture 3. With $d=r+1$, Corollary 3.1 constrains candidate morphic families for its upper inequality. It supplies a necessary restriction: it neither constructs such a family nor proves the lower inequality for all of $\mathcal C_d$. Corollary 3.2 gives no sufficiency statement for spectral cancellation, richness or an ordinary exponent bound.

## 追加锚（本行以下为增补区）

## 4. Positive cancellation rows and the exact minimum total length

**Definition 4.1 (Cancellation rows and the supplied polynomial).** Fix an integer $r\ge3$ and retain exactly $A_r$, $\varphi$, $u=u_{2r+1}$, $\Lambda$, $\beta$ and $e_r$ from Definitions 1.2–1.3. In particular,

$$
\varphi(i)=0(i+1)\ (0\le i<2r),\qquad
\varphi(2r)=0(2r)(2r),\qquad
\Lambda^r(\Lambda-2)=1,
$$

and the polynomial and descending eigenvector coordinates used here are

$$
g_r(X)=X^r-\sum_{k=0}^{r-1}X^k,\qquad
v_\beta=\bigl(\beta^{2r-1}(\beta-2),
 \beta^{2r-2}(\beta-2),\ldots,\beta-2,1\bigr)^T.
$$

Let

$$
\mathcal K_r=\{h\in\mathbb Z_{>0}^{2r+1}:hv_\beta=0\},\qquad
H(h)=\sum_{i=0}^{2r}h_i,
$$

and write

$$
h^*=\bigl(\underbrace{1,\ldots,1}_{r\text{ entries}},
 2^0,2^1,\ldots,2^r\bigr).
$$

The root $\beta$ is the existing $r$-bonacci root: the interval-and-equation characterization `eq_dbonacciPerronRoot_iff` and the characteristic/nontrivial-equation equivalence in [the Perron-root source](../../../D5/S0/Tower/DBonacci/PerronRoot.lean) identify it with `dbonacciPerronRoot r`. The rational irreducibility conjunct of `dbonacci_irreducible` in [the irreducibility source](../../../D5/S0/Tower/DBonacci/Irreducibility.lean), with $q=r$, applies to the literal polynomial $g_r$. We use these existing results as supplied. Thus $g_r$ is the monic minimal polynomial of $\beta$ over $\mathbb Q$, of degree $r$, and

$$
(X-1)g_r(X)=X^r(X-2)+1,\qquad
\beta^r(\beta-2)=-1.
\tag{18}
$$

The vector $h^*$ is the published weighted length row in Dvořáková–Pelantová, [*The limit of repetition thresholds of rich sequences*, Definition 12 and Appendix Lemma 22, EJC 33(2), P2.15](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i2p15/pdf/), [doi:10.37236/14600](https://doi.org/10.37236/14600). Those are Definition 11 and Lemma 21 in [arXiv:2509.06104v1](https://arxiv.org/html/2509.06104v1); their parameter $d$ equals $r$. That lemma already supplies cancellation for this particular row. In this section, external result numbers refer to the journal version unless the arXiv version is named explicitly.

**Theorem 4.2 (Complete positive integer cancellation family).** For every integer $r\ge3$ and every $h=(h_0,\ldots,h_{2r})\in\mathbb Z_{>0}^{2r+1}$, writing $t=h_r$, one has

$$
hv_\beta=0
\quad\Longleftrightarrow\quad
h_{r+j}=t+\sum_{i=0}^{j-1}2^{j-1-i}h_i
\quad\text{for every }j=1,\ldots,r.
\tag{19}
$$

Consequently the $r+1$ independent parameters $h_0,\ldots,h_{r-1},t$ range freely over the positive integers and uniquely parameterize $\mathcal K_r$.

*Proof.* Fix $r$ and a positive integer row $h$. Form polynomials in $\mathbb Q[X]$ by

$$
\begin{aligned}
a(X)&=\sum_{i=0}^{r-1}h_iX^{r-1-i},\\
b(X)&=\sum_{j=0}^{r-1}h_{r+j}X^{r-1-j},\\
F(X)&=(X-2)\bigl(X^ra(X)+b(X)\bigr)+h_{2r},\\
R(X)&=(X-2)b(X)-a(X)+h_{2r}.
\end{aligned}
$$

The descending order in $v_\beta$ gives $F(\beta)=hv_\beta$. By (18),

$$
F(X)=(X-1)g_r(X)a(X)+R(X).
\tag{20}
$$

Since the supplied $g_r$ is the minimal polynomial of $\beta$, a rational polynomial vanishes at $\beta$ exactly when it is divisible by $g_r$. Hence (20) implies

$$
hv_\beta=0\quad\Longleftrightarrow\quad g_r\mid R.
$$

The degree of $R$ is $r$ and its leading coefficient is $h_r=t>0$: the leading term comes from $Xb(X)$, while all other terms have degree at most $r-1$. As $g_r$ is monic of degree $r$, divisibility is therefore equivalent to the exact identity

$$
R(X)=t g_r(X).
\tag{21}
$$

For $1\le j<r$, comparing coefficients of $X^{r-j}$ in (21) gives

$$
h_{r+j}-2h_{r+j-1}-h_{j-1}=-t.
$$

The constant coefficient gives $h_{2r}-2h_{2r-1}-h_{r-1}=-t$, the same formula for $j=r$. Thus the coefficient equations, including the already equal leading coefficients, are exactly

$$
h_r=t,\qquad
h_{r+j}=2h_{r+j-1}+h_{j-1}-t
\quad(1\le j\le r).
\tag{22}
$$

Subtracting $t$ from both sides shows that $s_j=h_{r+j}-t$ satisfies $s_0=0$ and $s_j=2s_{j-1}+h_{j-1}$. Induction yields

$$
s_j=\sum_{i=0}^{j-1}2^{j-1-i}h_i,
$$

which proves the forward implication in (19). Conversely, the displayed sums satisfy this recurrence, hence every coefficient equation (22), hence (21), (20) and $F(\beta)=0$. This proves the reverse implication without additional conditions on $h$.

Finally choose any positive integers $h_0,\ldots,h_{r-1},t$. Formula (19) assigns a positive integer to each remaining coordinate, so the resulting row belongs to $\mathcal K_r$. Every member is recovered from its first $r$ coordinates and its coordinate $h_r=t$; no two parameter choices give the same row. $\square$

**Corollary 4.3 (Componentwise minimum and sharp total size).** For every integer $r\ge3$ and every $h\in\mathcal K_r$, with $t=h_r$,

$$
H(h)=(r+1)t+\sum_{i=0}^{r-1}2^{r-i}h_i
 \ \ge\ r+2^{r+1}-1.
\tag{23}
$$

Moreover $h\ge h^*$ coordinatewise, $h_{2r}\ge2^r$, and equality in the total-length bound holds exactly when $h=h^*$. Thus $h^*$ is the unique row minimizing $H$ on $\mathcal K_r$.

*Proof.* The first $r$ coordinates and $t$ are at least one. For $1\le j\le r$, Theorem 4.2 gives

$$
h_{r+j}\ge1+\sum_{i=0}^{j-1}2^{j-1-i}=2^j.
$$

Together with $h_r\ge1=2^0$, this proves componentwise domination and the last-coordinate bound. Summing the full parameterization and reversing the finite sums gives

$$
\begin{aligned}
H(h)
 &=\sum_{i=0}^{r-1}h_i+(r+1)t
   +\sum_{j=1}^{r}\sum_{i=0}^{j-1}2^{j-1-i}h_i\\
 &=(r+1)t+
   \sum_{i=0}^{r-1}\left(1+\sum_{j=i+1}^{r}2^{j-1-i}\right)h_i\\
 &=(r+1)t+\sum_{i=0}^{r-1}2^{r-i}h_i.
\end{aligned}
$$

The minimum of this expression over positive integer parameters is

$$
(r+1)+\sum_{i=0}^{r-1}2^{r-i}
 =(r+1)+(2^{r+1}-2)=r+2^{r+1}-1.
$$

All coefficients of the independent parameters are strictly positive. Equality therefore forces, and is forced by, $t=h_0=\cdots=h_{r-1}=1$. Formula (19) then gives exactly $h^*$. $\square$

**Theorem 4.4 (Exact minimum over actual morphic images).** Fix an integer $r\ge3$. For every finite nonempty alphabet $B$ and every nonerasing monoid morphism $`\eta:A_r^*\to B^*`$ satisfying the ordinary critical-exponent equality

$$
E(\eta(u))=e_r=1+\frac{1}{3-\Lambda},
$$

its length row $h_i=|\eta(i)|$ has the full parameterization (19), dominates $h^*$ coordinatewise and satisfies (23), in particular $|\eta(2r)|\ge2^r$.

Let $\mathcal M_r$ consist of all such pairs $(B,\eta)$, allowing $B$ to range over finite nonempty alphabets, and let $\mathcal R_r\subseteq\mathcal M_r$ consist of the pairs whose image $\eta(u)$ is rich. Then both classes are nonempty and

$$
\min_{(B,\eta)\in\mathcal M_r}\sum_{i=0}^{2r}|\eta(i)|
 =\min_{(B,\eta)\in\mathcal R_r}\sum_{i=0}^{2r}|\eta(i)|
 =r+2^{r+1}-1.
\tag{24}
$$

A pair in either class attains the minimum exactly when its length row is $h^*$. This is uniqueness of the minimizing row, with no assertion of uniqueness of the morphism.

*Proof.* Nonerasure makes $h$ a positive integer row. Corollary 3.2 applies to every such morphism into every finite nonempty $B$ and gives $hv_\beta=0$. Theorem 4.2 and Corollary 4.3 prove all the necessary row conditions and the lower bound in (24). This step uses Corollary 3.2 in full; it does not impose the finite-boundary premise of source Proposition 18 (arXiv Proposition 17), injectivity, richness or any restriction on the output alphabet size.

For attainment, reuse the weighted morphism of Dvořáková–Pelantová with their parameter $d=r$, as specified by journal Definition 12 and proved in Proposition 14 and Theorem 2, with equation (4) for the asymptotic exponent of the source. These complete supplied results give a finite alphabet $B_r$ of size $r+2^r$ and a nonerasing morphism $`\pi_r:A_r^*\to B_r^*`$ for which

$$
\bigl(|\pi_r(0)|,\ldots,|\pi_r(2r)|\bigr)=h^*,\qquad
\pi_r(u)\text{ is rich},\qquad
E(\pi_r(u))=E^*(u)=e_r.
$$

The corresponding arXiv numbers are Definition 11, Proposition 13 and Theorem 2; the supplied spectral computation for this row is journal Appendix Lemma 22, arXiv Lemma 21. The [journal proof in §§5–6 and Appendix](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i2p15/pdf/) supplies the word construction, richness and exact ordinary exponent together. Thus this is an actual member of $\mathcal R_r$, and hence of $\mathcal M_r$, with total length $r+2^{r+1}-1$. This proves both equalities in (24). The equality characterization follows from Corollary 4.3 for members of these classes. $\square$

**Proposition 4.5 (Cancellation, richness and exact-attainment scope).** For every integer $r\ge3$ and every $h\in\mathcal K_r$, there is a nonerasing morphism with length row $h$ and rich image whose ordinary critical exponent is $+\infty$. Therefore cancellation, even together with richness, does not imply $E(\eta(u))=e_r$. There is also a nonerasing morphism with the same length row whose image is not rich.

The minimum in (24) is over varying finite output alphabets. It gives no attainment assertion for each fixed $B$, or for an alphabet with exactly $r+1$ letters as in Definition 3.3. It also gives no positive separation from $e_r$ for families that only approach $e_r$ without attaining it, and no lower bound $RT(\mathcal C_{r+1})\ge e_r$ for all rich words.

*Proof.* Take $B=\{a\}$ and define $\eta(i)=a^{h_i}$. Every coordinate is positive, so the infinite image is $a^\omega$. The word $a^n$ has precisely the palindromic factors $\varepsilon,a,\ldots,a^n$, so this image is rich. Its factors $a^n$ have least positive period one, giving unbounded exponents $n$ and hence $E(a^\omega)=+\infty$. Since $\Lambda<3$, the number $e_r$ is finite. This proves the failure of sufficiency, including when $h=h^*$.

For the non-rich image, take $B=\{a,b,c\}$, put $\eta(2r)=abca\,a^{h_{2r}-4}$ and put $\eta(i)=a^{h_i}$ for $i<2r$. Corollary 4.3 gives $h_{2r}\ge2^r\ge8$, so these words have the prescribed positive lengths. The source contains the letter $2r$ (it occurs in $\varphi^{2r}(0)$), so the output contains $abca$. This length-four factor has exactly four distinct palindromic factors, $\varepsilon,a,b,c$, and is not rich. Thus a cancellation row alone also gives no richness conclusion.

For (24), the supplied attaining alphabet has size $r+2^r$, and the proof takes its minimum over the union of the classes indexed by all finite nonempty alphabets. No inference to a prescribed alphabet is part of that minimization. The cancellation step uses the exact equality $E(\eta(u))=e_r$; a family having only exponents tending to $e_r$ is instead subject to Corollary 3.1, which bounds the normalized defect and need not make it zero at any member. Finally the lower bound in (23) concerns lengths of morphisms with that exact exponent, not the ordinary exponents of every word in $\mathcal C_{r+1}$. Thus the smaller-alphabet upper route and the unrestricted lower inequality of Definition 3.3 retain their stated scope. $\square$

## 追加锚（本行以下为增补区）
## 5. Exact $r=3$ source-image boundary

Proposition 4.5 gives a constructive non-rich image for every $r\ge3$ and $h\in\mathcal K_r$: it locates the factor $abca$ through the occurrence of $2r$ in $\varphi^{2r}(0)$ and gives its complete palindrome set $\{\varepsilon,a,b,c\}$. The following $r=3$ instance records the prescribed four-letter dictionary $\eta_3$ and its specific certificate in the actual image of $u_7$: the factor at $[60,72)$ has the exhaustive palindrome count below and defect $2$.

**Proposition 5.1 (The normalized cancellation boundary).** Specialize Definition 1.2 to $r=3$, write the substitution as $\varphi_3$, and let $u_7=\varphi_3^\omega(0)$. Define the nonerasing morphism $\eta_3:\{0,1,2,3,4,5,6\}^*\to\{0,1,2,3\}^*$ by

$$
\eta_3(0)=0,\quad \eta_3(1)=1,\quad \eta_3(2)=2,\quad \eta_3(3)=3,\quad
\eta_3(4)=11,\quad \eta_3(5)=1221,\quad \eta_3(6)=12133121.
$$

For its length row $h=(1,1,1,1,2,4,8)$ and the normalized eigenvector $v_\beta$ of Definition 1.3, one has $h v_\beta=0$. Nevertheless, for the infinite image $w_3=\eta_3(u_7)$ the factor

$$
z=w_3[60,72)=301020101213
$$

has exactly $11$ distinct palindromic factors, including the empty word. Since $|z|=12$, it is not rich and its palindromic defect is $2$.

**Proof.** For the cancellation, the chosen row and the normalization in Definition 1.3 give

$$
h v_\beta=(\beta-2)(\beta^5+\beta^4+\beta^3+\beta^2+2\beta+4)+8.
$$

The polynomial identity

$$
(x-2)(x^2+x^3+x^4+x^5+2x+4)+8
=x^3(x^3-x^2-x-1)
$$

holds identically. The number $\beta$ is the positive root of $x^3-x^2-x-1$, so the displayed scalar is zero. This is the normalized relation $h v_\beta=0$, rather than a statement about an unnormalized eigenvector.

It remains to locate the stated factor in the actual infinite word. Put $T_n=\varphi_3^n(0)$ and let $\nu_2(q)$ denote the exponent of $2$ in a positive integer $q$. For $0\le n\le6$,

$$
|T_n|=2^n,\qquad T_n[j]=\nu_2(j+1)\quad(0\le j<2^n).
$$

The assertion is immediate for $n=0$. If $n<6$, every letter occurring in $T_n$ is at most $n$, so only the length-two rules $\varphi_3(i)=0(i+1)$ are used. Thus

$$
T_{n+1}[2j]=0=\nu_2(2j+1),\qquad
T_{n+1}[2j+1]=T_n[j]+1=\nu_2(2j+2),
$$

which proves the induction through $T_6$. The letter $6$ first occurs at $T_6[63]$; the exceptional rule $\varphi_3(6)=066$ is therefore not used in constructing $T_6$.

The positions $55$ through $63$ of $T_6$ correspond to the integers $56$ through $64$, hence

$$
T_6[55,64)=(3,0,1,0,2,0,1,0,6).
$$

Before position $55$, a letter greater than $3$ occurs exactly when $j+1$ is a multiple of $16$. The only such positions are $15,31,47$, with letters $4,5,4$. Since the images of $4,5,4$ have lengths $2,4,2$ and every other image in $T_6[0,55)$ has length one,

$$
|\eta_3(T_6[0,55))|=55+(2-1)+(4-1)+(2-1)=60.
$$

The next eight source letters have single-letter images, so

$$
\eta_3(T_6[55,63))=30102010,
$$

while $\eta_3(6)$ begins with $1213$. Consequently

$$
\eta_3(T_6)[60,72)=301020101213.
$$

The whole prefix has length

$$
|\eta_3(T_6)|=64+(2-1)+(4-1)+(2-1)+(8-1)=76,
$$

so both endpoints of this interval lie inside $\eta_3(T_6)$. Since $T_{n+1}=T_n\varphi_3^n(1)$ is a proper prefix extension and $\eta_3$ is nonerasing, these prefixes embed compatibly in $w_3=\eta_3(u_7)$; the displayed finite word is therefore the actual factor $w_3[60,72)$.

For the palindrome count, the adjacent letters of $z$ are all different, so no nonempty even-length palindrome occurs. The largest odd radii at centers $0,1,\ldots,11$ are

$$
(0,0,1,0,3,0,1,1,0,1,0,0).
$$

Every odd palindrome is obtained by choosing a center and a radius no larger than the corresponding entry. Centers $2$ and $6$ give $010$; center $4$ gives $020$, $10201$, and $0102010$; center $7$ gives $101$; and center $9$ gives $121$. Radius zero gives the four single letters. Thus the complete set of distinct palindromic factors is

$$
\{\varepsilon,0,1,2,3,010,020,101,121,10201,0102010\}.
$$

It has $1+4+4+1+1=11$ elements, whereas richness of a length-$12$ word requires $12+1=13$. Hence $z$ has defect $2$ and is not rich. \qed

## 6. Scope of the cancellation boundary

The example satisfies the exact necessary cancellation condition from Corollary 3.2 and is an actual nonerasing source image, but its finite factor $z$ fails the defining richness condition. Therefore $h v_\beta=0$ is not sufficient for richness, and it is not a richness-preserving construction principle. Theorem 2.1 still supplies the ordinary bound $E(w_3)\ge e_3$ through its zero-defect case; this example supplies no matching upper bound and no assertion about attainment.

This conclusion is restricted to the displayed $r=3$ morphic image and its explicit factor. It does not impose a condition on every rich word, does not prove or refute the unrestricted equality

$$
RT(\mathcal C_d)=E^*(u_{2d-1})\qquad(d\ge2),
$$

and does not provide the upper construction required for that equality. In particular, cancellation, richness, and control of the ordinary exponent remain separate requirements for any proposed source-image route.

## 追加锚（本行以下为增补区）

## 7. A necessary cone and an unbounded excluded cancellation family

**Definition 7.1 (Original source and actual alphabet).** Throughout Sections 7–11, $r\ge3$ is an integer and $u$, $\varphi$, $\Lambda$, $\beta$, $v_\beta$, $e_r$, $\mathcal K_r$ and $H$ retain Definitions 1.2–1.3 and 4.1. Thus the source is exactly

$$
\varphi(i)=0(i+1)\quad(0\le i<2r),\qquad
\varphi(2r)=0(2r)(2r),\qquad u=\varphi^\omega(0).
$$

For a nonerasing morphism $`\eta:A_r^*\to B^*`$, put $x=\eta(u)$ and $h_i=|\eta(i)|$. Its actual alphabet is the set $\operatorname{Alph}(x)$ of letters occurring in $x$, rather than an arbitrarily enlarged ambient $B$. Every letter of $A_r$ occurs in $u$: the letter $i$ occurs in $\varphi^i(0)$ for $0\le i\le2r$. Hence

$$
\operatorname{Alph}(x)=\bigcup_{i=0}^{2r}\operatorname{Alph}(\eta(i)).
$$

All exponents below are the ordinary least-period exponents of Definition 1.1. Define

$$
D_r=\Lambda^r-2^r-2,\qquad S_r=r+2^{r+1}-1.
$$

**Theorem 7.2 (Necessary cone on the full cancellation locus).** Let $r\ge3$, let $B$ be any nonempty finite alphabet and let $`\eta:A_r^*\to B^*`$ be any nonerasing morphism. If $h\in\mathcal K_r$ and $E(x)\le e_r$, then, writing $t=h_r$,

$$
D_rh_0\le2t+\sum_{i=1}^{r-1}2^{r-i}h_i.
\tag{25}
$$

In particular, every exact attaining image satisfies (25), with no injectivity, richness or output-alphabet-size assumption and with all independent positive integer parameters in Theorem 4.2 allowed.

*Proof.* The actual-factor inequality (1), using the already supplied Type I return at index $1$ in (3), gives the reused intermediate bound

$$
E(x)\ge2+\frac{h_0}{h_0+2h_{2r}}.
\tag{26}
$$

Its input is the Type I factor $0(2r)(2r)0$ and the return $0(2r)(2r)$; the inequality certifies an output period and does not require that period to be least. The supplier is Dvořáková–Pelantová, [arXiv:2509.06104v1, §3, Lemma 9 and Type I](https://arxiv.org/pdf/2509.06104v1), journal Lemma 10 in [EJC 33(2), P2.15](https://doi.org/10.37236/14600), used in Theorem 2.1. Thus (26) is reused, rather than an additional local-period result.

The equation $\Lambda^r(\Lambda-2)=1$ implies

$$
e_r=2+\frac{1}{\Lambda^r-1}.
\tag{27}
$$

All denominators are positive. Combining (26) with $E(x)\le e_r$ and multiplying gives

$$
(\Lambda^r-2)h_0\le2h_{2r}.
$$

On the entire cancellation locus, Theorem 4.2 gives

$$
2h_{2r}=2t+2^rh_0+\sum_{i=1}^{r-1}2^{r-i}h_i.
$$

Substitution proves (25). For an exact attaining image, Corollary 3.2 supplies $h\in\mathcal K_r$, so the same calculation applies. $\square$

**Theorem 7.3 (Uniform exclusion of an unbounded positive family).** For every integer $r\ge5$, one has $D_r>1/4$. For every such $r$ and every integer $N\ge2^{r+2}$, set

$$
h_0=N,\qquad h_1=\cdots=h_{r-1}=t=1,\qquad
h_{r+j}=2^{j-1}(N+1)\quad(1\le j\le r).
\tag{28}
$$

This is a positive cancellation row. Every nonerasing dictionary with this row into every nonempty finite alphabet satisfies

$$
E(\eta(u))\ge e_r+
\frac{D_rN-2^r}
 {\bigl((2^r+1)N+2^r\bigr)(\Lambda^r-1)}
>e_r.
\tag{29}
$$

*Proof.* Put $a=2^r$ and $y=\Lambda^r$. Since $\Lambda=2+1/y$, the binomial inequality gives

$$
y=\left(2+\frac1y\right)^r\ge a+\frac{ra}{2y}.
$$

If $y\le a+9/4$, then, since $r\ge5$ and $a\ge32$,

$$
\frac{ra}{2y}\ge\frac{ra}{2(a+9/4)}
\ge\frac52\frac{32}{32+9/4}
=\frac{320}{137}>\frac94.
$$

This would give $y>a+9/4$, a contradiction. Thus $D_r=y-a-2>1/4$.

Theorem 4.2 applied to the independent parameters in (28) gives

$$
t+\sum_{i=0}^{j-1}2^{j-1-i}h_i
=1+2^{j-1}N+(2^{j-1}-1)=2^{j-1}(N+1).
$$

It therefore supplies cancellation for every row (28). For this row, (26) becomes

$$
E(\eta(u))\ge2+\frac{N}{(2^r+1)N+2^r}.
$$

Subtracting (27) yields exactly the fraction in (29). Its numerator is positive because

$$
D_rN>\frac{N}{4}\ge2^r.
$$

The denominator is positive as well. This proves the exclusion for every dictionary with the prescribed lengths, including those with infinite exponent. The family is unbounded since $N$ is arbitrary above the stated threshold. This argument excludes neither all cancellation rows nor any family at $r=3$ or $r=4$. $\square$

## 8. Length restrictions for the literal prefix class

**Definition 8.1 (Same-morphism literal prefix class).** A pair $(\eta,p)$ belongs to $\mathcal L_r$ if $`\eta:A_r^*\to B^*`$ is an injective nonerasing morphism into a finite alphabet, $p$ is a nonempty palindrome, and for every $i\in A_r$ there is a palindrome $q_i$, possibly empty, such that

$$
\eta(i)=p q_i,\qquad \eta(i)p=pq_ip
\text{ has exactly two occurrences of }p,
$$

at its prefix and suffix. Put $m=|p|\ge1$. An attaining pair additionally satisfies $E(\eta(u))=e_r$. This is the literal representation in Dvořáková–Pelantová, journal Definition 19, [doi:10.37236/14600](https://doi.org/10.37236/14600), arXiv Definition 18. The same $\eta$ acts on the original $u$; no conjugation, replacement by a derived sequence, or change of source is included in this definition.

**Theorem 8.2 (Marker and total-length relaxations).** For every $r\ge3$ and every attaining pair $(\eta,p)\in\mathcal L_r$,

$$
h_{2r}\ge m(\Lambda^r-1),\qquad
H\ge(m+1)S_r-2^r.
\tag{30}
$$

Equality in the second bound can occur only with the independent parameters

$$
h_0=m,\qquad h_1=\cdots=h_{r-1}=t=m+1.
\tag{31}
$$

For $r=3$ this gives $H\ge28$. Equality $H=28$ forces $m=1$ and the full row

$$
(h_0,\ldots,h_6)=(1,2,2,2,3,6,12).
\tag{32}
$$

These are necessary length conditions; (31) and (32) do not assert the existence of an attaining dictionary.

*Proof.* Write $c=2r$. The letter $c$ occurs in $u$, and $u=\varphi(u)$ contains $cc0$: use the suffix $cc$ of $\varphi(c)=0cc$ and the initial $0$ of the following letter image. Since $\eta(0)$ begins with $p$, the word

$$
z=\eta(c)\eta(c)p
$$

is an actual factor of $\eta(u)$. The word $p$ is a prefix of $\eta(c)$, so $|\eta(c)|=h_c$ is a period of $z$. Consequently

$$
E(\eta(u))\ge2+\frac{m}{h_c}.
$$

For an attaining pair, (27) now gives the first bound in (30).

Every length $h_i$ is at least $m$. A length equal to $m$ forces $q_i=\varepsilon$ and $\eta(i)=p$. Injectivity permits at most one such $i$. In particular, among the independent parameters $h_0,\ldots,h_{r-1},t$ at most one can equal $m$, and all others are at least $m+1$. Cancellation follows from Corollary 3.2. The exact supplied formula (23) is

$$
H=(r+1)t+\sum_{i=0}^{r-1}2^{r-i}h_i.
\tag{33}
$$

Its coefficient sum is $S_r$. Its unique largest coefficient is $2^r$, at $h_0$, because $2^r>r+1$ for $r\ge3$. Starting with every independent parameter equal to $m+1$, at most one parameter can decrease by one; the greatest possible decrease in (33) is $2^r$. This proves the second inequality in (30). Equality requires the decrease to occur at $h_0$ and requires every other parameter to remain $m+1$, giving (31).

When $r=3$, $S_3=18$, so $H\ge18(m+1)-8$. As $m\ge1$, equality $H=28$ forces $m=1$, $h_0=1$ and $h_1=h_2=t=2$. Formula (19) then gives $h_4=3$, $h_5=6$, $h_6=12$, proving (32).

For comparison, the larger-alphabet attaining supplier in Theorem 4.4 already supplies members of this literal class. Reuse its weighted morphism $\pi_r$ and put $\widehat\eta=\pi_r\circ\varphi$. Its output is the very same supplied word, since $\varphi(u)=u$:

$$
\widehat\eta(u)=\pi_r(u),\qquad
E(\widehat\eta(u))=e_r,\qquad
\#\operatorname{Alph}(\widehat\eta(u))=r+2^r.
$$

Indeed $\pi_r(0)$ is a single letter $a$ occurring in no other letter image. With $p=a$, the palindromes in the literal representation are

$$
q_i=\pi_r(i+1)\quad(i<2r),\qquad
q_{2r}=\pi_r(2r)\pi_r(2r).
$$

Each $aq_i a$ has exactly two occurrences of $a$. The substitution $\varphi$ is injective, and so is $\pi_r$: its disjoint nonempty image alphabets identify each maximal run of source letters, with the run length determined by the length of its image. Thus $\widehat\eta$ is injective. The richness and exact ordinary exponent are the complete reused conclusions of journal Proposition 14 and Theorem 2, rather than another proof of that construction. Its row is

$$
\widehat h_i=1+h^*_{i+1}\quad(i<2r),\qquad
\widehat h_{2r}=1+2h^*_{2r}.
$$

For $r=3$ it is $(2,2,2,3,5,9,17)$, of total length $40$, on $11$ actual letters. In particular, the length relaxation does not leave all larger-alphabet literal-prefix attainment without a supplied example. $\square$

## 9. A strengthened boundary on the actual small alphabet

**Theorem 9.1 (The minimal relaxed row forces an ordinary fifth power).** Let $r\ge3$ and $(\eta,p)\in\mathcal L_r$. Suppose that $\eta(u)$ is rich, that its actual alphabet has exactly $r+1$ letters, and that its row is

$$
h_0=1,\qquad h_i=2\quad(1\le i\le r),\qquad
h_{r+j}=3\cdot2^{j-1}\quad(1\le j\le r).
\tag{34}
$$

Then $\eta(u)$ contains a one-letter fifth power, and hence $E(\eta(u))\ge5$.

*Proof.* Since $1=h_0\ge|p|\ge1$, the marker is a single letter, say $p=a$, and $\eta(0)=a$. For $1\le i\le r$, the literal representation and $h_i=2$ give

$$
\eta(i)=a b_i
$$

for a letter $b_i$. The complete-return condition says that $ab_i a$ has exactly two occurrences of $a$, so $b_i\ne a$. Injectivity says that $b_1,\ldots,b_r$ are pairwise distinct. These $r+1$ letters already occur in the output by Definition 7.1. The actual-alphabet hypothesis therefore gives

$$
\operatorname{Alph}(\eta(u))=\{a,b_1,\ldots,b_r\}.
\tag{35}
$$

Set $k=r+2\le2r$. Formula (34) gives $h_k=6$, so $\eta(k)=a q_k$ with $|q_k|=5$. Since $a q_k a$ is a complete return to $a$, the word $q_k$ contains no $a$. By (35), its letters are among $b_1,\ldots,b_r$.

We locate a suitable occurrence in the original source. For $0\le n\le2r$, put $T_n=\varphi^n(0)$. Only the length-two rules are used before constructing $T_{2r}$, and induction on $n$ gives

$$
|T_n|=2^n,\qquad T_n[j]=\nu_2(j+1)\quad(0\le j<2^n),
\tag{36}
$$

where $\nu_2$ is the exponent of $2$ in a positive integer. In the induction step, the even positions become $0$ and the odd positions increase the old letter by one; these are precisely the two corresponding valuation identities. Let $F_{r+1}$ be $T_{r+1}$ with its last letter $r+1$ removed. The last $2^{r+1}$ letters of $T_{r+2}$ are $F_{r+1}(r+2)$ by (36). The word $F_{r+1}$ uses only $0,\ldots,r$, contains every one of those letters, and ends in $0$.

Thus an actual output factor is

$$
\eta(F_{r+1})a q_k.
\tag{37}
$$

In the part $\eta(F_{r+1})a$, each $b_i$ occurs, and every occurrence of a $b_i$ is immediately followed by $a$. This follows from $\eta(0)=a$, $\eta(i)=ab_i$ for $1\le i\le r$, and the final appended $a$.

Let $b$ be the first letter of $q_k$. Suppose that some different letter $d$ occurs in $q_k$, and take its first occurrence there. It is not the first position of $q_k$, and its preceding letter is different from $a$. Take the last occurrence of $d$ in $\eta(F_{r+1})a$. The factor from that occurrence to the chosen first $d$ in $q_k$ contains exactly two $d$'s. It starts with $da$ and ends with $ed$ for a letter $e\ne a$. It cannot be a palindrome, since its second and penultimate letters differ.

But a single letter is a palindrome, and every complete return to a palindromic factor in a rich word is a palindrome. This is exactly Glen–Justin–Widmer–Zamboni, [*Palindromic richness*, arXiv:0801.1656v1, Theorem 2.14 and Remark 2.15](https://arxiv.org/pdf/0801.1656v1), [doi:10.1016/j.ejc.2008.04.006](https://doi.org/10.1016/j.ejc.2008.04.006). That criterion applies to finite and infinite words, without a recurrence or reversal-closure hypothesis. It contradicts the complete return just found. Hence every letter of $q_k$ is $b$, so $q_k=b^5$. This factor has least period one and exponent five, proving the claim. $\square$

**Corollary 9.2 (Length boundary for every nonempty marker).** Let $r\ge3$. Every attaining pair $(\eta,p)\in\mathcal L_r$ whose output is rich on exactly $r+1$ actual letters satisfies

$$
H\ge2r+3\cdot2^r-2+\gcd(2,r+1).
\tag{38}
$$

In particular, for $r=3$ and four actual letters, $H\ge30$. This is a necessary condition in $\mathcal L_r$, with no assertion of feasibility or sharpness at the lower bound.

*Proof.* Write $H_0=2S_r-2^r=2r+3\cdot2^r-2$. If $m\ge2$, Theorem 8.2 gives $H\ge H_0+(m-1)S_r>H_0$. If $m=1$, the same theorem gives $H\ge H_0$, with equality possible only at $h_0=1$, $h_1=\cdots=h_{r-1}=t=2$. The complete supplied family (19) then gives exactly (34). Theorem 9.1 would force $E(\eta(u))\ge5$, whereas (27) and $\Lambda^r>2^r\ge8$ give $e_r<2+1/7<5$. Hence equality is impossible, and $H>H_0$ for every marker length.

Put $g=\gcd(2,r+1)$. Formula (33) shows that $g$ divides $H$. The same formula at the positive cancellation row (34) shows that $g$ divides $H_0$. Therefore the strict integer inequality $H>H_0$ implies $H\ge H_0+g$, proving (38). For $r=3$, $H_0=28$ and $g=2$. The distinction between $m=1$ and $m\ge2$ was only a proof by cases; the corollary imposes no global minimum-marker assumption. $\square$

## 10. An arithmetic size corollary of the spectral defect

**Corollary 10.1 (Classical norm specialization and near-attainment size).** Let $r\ge3$, let $`\eta:A_r^*\to B^*`$ be any nonerasing morphism into any nonempty finite alphabet, and suppose $hv_\beta\ne0$. With exactly $v_\beta$, $\kappa_r$ and $c_r$ of Definitions 1.3 and Theorem 2.1,

$$
E(\eta(u))\ge e_r+
 c_r3^{-(r-1)\kappa_r}H^{-r\kappa_r}
\ge e_r+\frac{c_r}{27^{r-1}}H^{-3r}.
\tag{39}
$$

Consequently, for every $\varepsilon>0$, a noncancelling image satisfying $E(\eta(u))\le e_r+\varepsilon$ must satisfy both

$$
H\ge3^{-(r-1)/r}\left(\frac{c_r}{\varepsilon}\right)^{1/(r\kappa_r)},
\qquad
H\ge\left(\frac{c_r}{27^{r-1}\varepsilon}\right)^{1/(3r)}.
\tag{40}
$$

The norm step is classical; (39) is its arithmetic corollary combined with the repo-derived ordinary-factor Theorem 2.1, rather than a new algebraic-norm theorem.

*Proof.* The supplied polynomial $g_r(X)=X^r-\sum_{j=0}^{r-1}X^j$ is the monic minimal polynomial of $\beta$, of degree $r$, as specified in Definition 4.1. Its other complex roots $\zeta_2,\ldots,\zeta_r$ have modulus strictly less than one. The latter fact is supplied both by Appendix P1 of Dvořáková–Pelantová and by the existing $q=r$ statement `dbonacci_complex_root_location` in [DBonacci irreducibility](../../../D5/S0/Tower/DBonacci/Irreducibility.lean); that source also contains its proof-local root-equation argument and the monic integer factor argument used by `dbonacci_irreducible`. The root is the same one fixed by `eq_dbonacciPerronRoot_iff` in [DBonacci Perron root](../../../D5/S0/Tower/DBonacci/PerronRoot.lean). No rescaling of the eigenvector or replacement of the degree is made here.

Define the integer polynomial

$$
P_h(X)=(X-2)\sum_{i=0}^{2r-1}h_iX^{2r-1-i}+h_{2r},
$$

so that $\alpha=P_h(\beta)=hv_\beta$. Because $\beta$ is an algebraic integer, $\alpha$ is an algebraic integer in $K=\mathbb Q(\beta)$. The classical norm formulas give

$$
N_{K/\mathbb Q}(\alpha)
=P_h(\beta)\prod_{j=2}^{r}P_h(\zeta_j)\in\mathbb Z\setminus\{0\}.
\tag{41}
$$

Here the product is over all $r$ embeddings of $K$, even if $\alpha$ generates a proper subfield. These are the standard integrality and conjugate-product norm statements; see J. S. Milne, [*Algebraic Number Theory*, version 3.08, Theorem 2.1, Corollaries 2.20–2.21 and Aside 2.22](https://www.jmilne.org/math/CourseNotes/ANT.pdf).

For $j\ge2$, $|\zeta_j|<1$ and $|\zeta_j-2|<3$, whence

$$
|P_h(\zeta_j)|
\le |\zeta_j-2|\sum_{i=0}^{2r-1}h_i|\zeta_j|^{2r-1-i}+h_{2r}
\le3H.
$$

Taking absolute values in (41), using its nonzero integer value, gives

$$
1\le|\alpha|(3H)^{r-1},\qquad
\rho=\frac{|\alpha|}{H}\ge3^{-(r-1)}H^{-r}.
\tag{42}
$$

The last lower bound lies in $(0,1]$, since $H\ge1$. Thus

$$
\min(1,\rho)\ge3^{-(r-1)}H^{-r}.
$$

Applying Theorem 2.1 proves the first inequality in (39). Its proof already supplies $0<\kappa_r<3$. Since $3^{r-1}H^r\ge1$, raising its reciprocal to $\kappa_r$ gives a value at least its third power, proving the second inequality. Combining each of these positive excess bounds with $E(\eta(u))-e_r\le\varepsilon$ and taking the respective positive roots proves (40).

If $hv_\beta=0$, the integer norm in (41) is zero and the lower bound (42) does not follow. Thus this corollary gives no positive gap on cancellation and no existence of approaching images. $\square$

## 11. Separate mathematical targets and representation boundaries

**Definition 11.1 (Exact, approaching and unrestricted targets).** For each $r\ge3$, the exact original-source small-alphabet question asks for a nonerasing morphism $\eta$ for which

$$
\#\operatorname{Alph}(\eta(u_{2r+1}))=r+1,\qquad
\eta(u_{2r+1})\text{ is rich},\qquad
E(\eta(u_{2r+1}))=e_r,
$$

allowing every positive length row and arbitrary morphisms. The distinct approaching question asks for a family with the same actual alphabet size and richness whose ordinary exponents tend to $e_r$. The unrestricted threshold target remains Definition 3.3:

$$
RT(\mathcal C_d)=E^*(u_{2d-1})\quad(d\ge2),
$$

where $\mathcal C_d$ contains all infinite rich words on $d$ actual letters, without a recurrence or morphic restriction. Its lower inequality quantifies over every word in that class. The cone, the excluded family and (38) supply necessary restrictions, leaving these existence and unrestricted lower-bound obligations unresolved here, already for the exact original $u_7$ question on four letters. In particular, (38) is not an impossibility assertion for arbitrary morphisms or a construction at $H=30$.

The representation in Definition 8.1 is narrower than the complete-return formulation in Balková–Pelantová–Starosta, [*Infinite words with finite defect*, arXiv:1009.5105v1, Definition 5.1, Proposition 5.4 and Theorem 5.5](https://arxiv.org/pdf/1009.5105v1), [doi:10.1016/j.aam.2010.11.006](https://doi.org/10.1016/j.aam.2010.11.006). That formulation allows a return word shorter than its marker and uses conjugation and derived words. A literal factorization $\eta(i)=p q_i$ for the same morphism on the same $u$ is an additional condition. Neither the derived-word representation nor conjugacy alone supplies that condition while preserving this length row. The marker and length conclusions (30) and (38) are restricted to Definition 8.1; they impose no condition on the broader overlapping-return class or on arbitrary rich morphisms without such a bridge.

For the source/exponent distinction, Dvořáková–Klouda–Pelantová, [*The asymptotic repetition threshold of sequences rich in palindromes*, arXiv:2409.06849v1, Theorems 24–25 and Corollary 29](https://arxiv.org/pdf/2409.06849v1), [doi:10.1016/j.ejc.2025.104124](https://doi.org/10.1016/j.ejc.2025.104124), supplies a rich binary projection $i\mapsto ab^i$ preserving the asymptotic exponent. This is an asymptotic supplier, not an ordinary-exponent upper bound. Currie–Mol–Peltomäki, [*The repetition threshold for ternary rich words*, EJC 32(2), P2.55, Theorems 1.1–1.2](https://doi.org/10.37236/13499), supplies the ternary ordinary threshold and its transducer construction. Dvořáková–Pelantová, [*Symmetries of rich sequences with minimum critical exponent*, arXiv:2501.15135v1, Proposition 2](https://arxiv.org/pdf/2501.15135v1), supplies its original-source morphic representation on $u_5$. These are exact supplied results in their respective ranges, rather than solutions of the original $u_{2r+1}$ problem for $r\ge3$. A finite rich word, including a long word with a controlled exponent, is also distinct from the infinite-word existence required in Definition 3.3.

## 追加锚（本行以下为增补区）
