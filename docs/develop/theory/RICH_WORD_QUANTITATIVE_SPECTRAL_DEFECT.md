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
