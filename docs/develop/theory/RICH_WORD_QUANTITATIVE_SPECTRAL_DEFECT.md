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
## 12. A four-letter literal image of the original source

**Definition 12.1 (The dictionary and its parameters).** Retain the original $u_7$ of Definition 1.2 with $r=3$, and put

$$
\begin{gathered}
p=a,\qquad
(\eta(0),\ldots,\eta(6))
=(a,ab,abb,ac,acc,accdcc,accdccddccdcc),\\
q_i=a^{-1}\eta(i),\qquad
(q_0,\ldots,q_6)=(\varepsilon,b,bb,c,cc,ccdcc,ccdccddccdcc),\\
h=(1,2,3,2,3,6,13),\qquad x=\eta(u_7),\qquad
L=\frac1{3-\Lambda},\qquad e_3=1+L=2+\frac1{\Lambda^3-1},
\end{gathered}
\tag{43}
$$

where $a,b,c,d$ are four distinct letters and $\Lambda>2$ satisfies $\Lambda^3(\Lambda-2)=1$. The notation $a^{-1}\eta(i)$ means deletion of the displayed initial letter, not inversion in a group. All critical exponents are those of Definition 1.1.

The source inputs used below are Dvořáková–Pelantová, [*The limit of repetition thresholds of rich sequences*, arXiv:2509.06104v1](https://arxiv.org/pdf/2509.06104v1), Theorem 5, §§3–4, Lemmas 8–10, Proposition 19 and Appendix Lemmas 20–21. Their spectral parameter $d$ is $3$, their source alphabet is $\{0,\ldots,6\}$, and their Perron equation is exactly the equation in (43). Proposition 19 instead uses $d$ for the source alphabet size: its applicable instance is $d=7$. The corresponding journal results are Theorem 5, Lemmas 9–11, Proposition 20 and Appendix Lemmas 21–22 in [EJC 33(2), P2.15](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i2p15/pdf/). Source extension and return descriptions also occur in Dvořáková–Klouda–Pelantová, [*The asymptotic repetition threshold of sequences rich in palindromes*, arXiv:2409.06849v1](https://arxiv.org/pdf/2409.06849v1), Proposition 4, Corollary 5, Definition 8 and Propositions 15 and 19, with source-size parameter $d=7$. These results supply the source classifications and the criteria; the dictionary (43), its boundary estimates and its equality classification are the additional inferences here.

**Theorem 12.2 (Literal membership and infinite richness).** The morphism in (43) is nonerasing and injective as a morphism of free monoids. The pair $(\eta,a)$ belongs to the original literal class $\mathcal L_3$ of Definition 8.1, its total image length is $H=30$, and $x$ is an infinite rich word with exactly four actual letters.

*Proof.* Each $q_i$ is a palindrome without $a$. Therefore $a q_i a$ is a palindrome with exactly two occurrences of $a$, its endpoints, including when $q_0=\varepsilon$. In a concatenation of image words, successive occurrences of $a$, together with the end of a finite concatenation, identify the intervening $q_i$. The seven intervening words are distinct. They uniquely recover the source letters, proving monoid injectivity. The positive lengths in (43) sum to $30$. Every source letter occurs in $u_7$, so all of $a,b,c,d$, and only these letters, occur in $x$.

It remains to verify the hypothesis of the supplied richness criterion, arXiv Proposition 19, journal Proposition 20. A nonempty factor without $a$ lies inside one of the displayed $q_i$. For such a factor $v$, encode a both-sided extension $\ell v r$ by the pair $\ell r$. Its complete extension set is obtained inside the finite words $a q_i a$. The following table gives all the nonempty bispecial factors without $a$, their extension pairs, their bilateral orders, and the numbers of palindromic extensions when applicable.

| $v$ | Extension pairs | $\mathrm b(v)$ | $\#\mathrm{Pext}(v)$ for palindromic $v$ |
|---|---|---:|---:|
| $b$ | $aa,ab,ba$ | $0$ | $1$ |
| $c$ | $aa,ac,ca,cd,dc$ | $0$ | $1$ |
| $d$ | $cc,cd,dc$ | $0$ | $1$ |
| $cc$ | $aa,ad,da,dd$ | $1$ | $2$ |
| $ccd$ | $ac,dc,dd$ | $0$ | — |
| $dcc$ | $ca,cd,dd$ | $0$ | — |
| $dccd$ | $cd,dc$ | $-1$ | $0$ |
| $ccdcc$ | $aa,ad,da$ | $0$ | $1$ |

For completeness of this finite list, the nonempty left-special factors without $a$ are precisely

$$
b,c,d,cc,dc,ccd,dcc,ccdc,dccd,ccdcc.
$$

The two words $dc$ and $ccdc$ have only the right extension $c$ and are discarded. This enumeration follows by taking all substrings of the explicit $q_i$ and comparing their preceding letters in $a q_i a$. No word of length at least six can add an entry: it occurs only in $q_6$, and the longest substring repeated at different positions in $q_6$ has length five. Each such longer factor thus has a fixed preceding and following letter. All the extension pairs in the table actually occur, since each $i$ occurs in the recurrent source and each image block is surrounded by marker letters.

The empty factor has extension pairs

$$
aa,ab,ba,bb,ac,ca,cc,cd,dc,dd.
$$

Its bilateral order is $10-4-4+1=3$, and it has four palindromic extensions. Thus it too satisfies the criterion. In the nonempty table every nonpalindrome has bilateral order zero, and every palindrome has bilateral order $\#\mathrm{Pext}(v)-1$. Proposition 19 applies with the nonempty marker $a$ and source $u_7$, and proves infinite richness. $\square$

## 13. The complete ordinary upper bound

**Theorem 13.1 (Ordinary exponent of the dictionary).** For the very same $u_7$ and $\eta$ in (43),

$$
E(x)=e_3.
\tag{44}
$$

*Proof.* The source is uniformly recurrent, since its defining substitution is primitive. A nonerasing image of a uniformly recurrent word is uniformly recurrent: a sufficiently long output factor contains the image of a sufficiently long source factor, and the bounded gaps of each source factor give bounded output gaps. The source is aperiodic; in particular its supplied finite value $E^*(u_7)=e_3$ precludes eventual periodicity. If $x$ were eventually periodic, the successive gaps between its marker letters would give an eventually periodic sequence of the distinct words $q_i$. Decoding them would make $u_7$ eventually periodic. Hence $x$ is aperiodic as well.

We may therefore apply the supplied ordinary-exponent Theorem 5 to $x$: it suffices to prove $|v|\le L|R'|$ for every bispecial factor $v$ of $x$ and every return word $R'$ to $v$. This criterion covers every finite factor and its least period; it is not an asymptotic criterion.

First suppose $v$ does not contain $a$. For the empty factor the ratio is zero. For the eight nonempty factors in Theorem 12.2 the following lower bounds on the distance $P=|R'|$ suffice.

| $v$ | Lower bound on $P$ | Upper bound on $|v|/P$ |
|---|---:|---:|
| $b,c,d$ | $1$ | $1$ |
| $cc$ | $3$ | $2/3$ |
| $ccd,dcc$ | $3$ | $1$ |
| $dccd$ | $4$ | $1$ |
| $ccdcc$ | $6$ | $5/6$ |

Here $cc$ occurs only as a run of exactly two $c$'s, so two starts are at distance at least three. The words $ccd,dcc$ have least period three. Within $q_6$, the two starts of $dccd$ are at positions $2$ and $6$, using zero-based positions; it occurs in no other $q_i$. Starts in different blocks are farther apart. The starts of $ccdcc$ in $q_6$ are $0$ and $7$, and its only other block is $q_5$ itself. Two occurrences in different blocks have a marker between them, hence distance at least six. These facts prove every bound in the table, including possible overlapping returns. Since $L>1$, all these ratios are at most $L$.

Now suppose $v$ contains $a$. Markers uniquely delimit image blocks. Highlighting its first and last marker writes it uniquely as

$$
v=s\eta(w)a t,
\qquad |v|=h\vec w+1+|s|+|t|,
\tag{45}
$$

where $s,t$ have no $a$ and $w$ is a source factor, possibly empty. As in the proof of the supplied Proposition 19, bispeciality of $v$ makes $w$ bispecial. The possible $s$ are longest common suffixes of distinct blocks $q_i$, and $t$ are the corresponding longest common prefixes. Directly from (43), the only possible boundary words are

$$
\mathcal S=\{\varepsilon,b,c,cc,T\},\qquad T=ccdcc.
\tag{46}
$$

All these words are palindromes. Shorter suffixes of a common suffix cannot create a new left extension until their preceding letters differ; this explains why, for example, $dcc$ and $cdcc$ do not occur in (46).

Every occurrence of (45) determines an occurrence of $w$. Two occurrences of $v$ at distance $P$ determine two occurrences of $w$ whose gap has output length $P$: their offsets from the first highlighted marker are the same. If they are not consecutive occurrences of $w$, the gap is a concatenation of source return words. Consequently any lower bound on the image length of every source return to $w$ also bounds $P$. This observation includes restrictions imposed by $s,t$; it does not assert that every source return is an output return.

The supplied exhaustive source classification has the finite palindromes $F_k$, $0\le k\le5$, the two infinite palindromic series, and the nonpalindromic series and their reversals. We treat all these classes.

For $w=F_k$, the source extension pairs are

$$
\{(k,j),(j,k):k<j\le6\}\cup\{(6,6)\}.
\tag{47}
$$

This is source Proposition 4 for $k\le4$; the final pair of extensions $\{5,6\}$ gives the same formula for $F_5$. Put $D_k=|\eta(F_k)|$. The recursion for $F_k$ or its ruler-word expression gives

$$
(D_0,D_1,D_2,D_3,D_4,D_5)=(0,1,4,11,24,51).
$$

For $k\ge1$, each return to $F_k$ is an image $\varphi^k(i)$: the occurrences of $F_{k+1}=\varphi(F_k)0$ are exactly the images of the occurrences of $F_k$, since the zeros are precisely the substitution boundaries. This is also the return description used in the proof of source Lemma 9. Each such return begins with $F_k$ and has at least one further letter; thus occurrences of $F_k$ do not overlap. If the output occurrence in (45) has a right neighbor $j$ of $F_k$, and the next one has a left neighbor $i$, then

$$
P\ge D_k+h_j,\qquad P\ge D_k+h_i.
\tag{48}
$$

The first follows by including the prefix $F_kj$ of the gap; the second by including its prefix $F_k$ and its final letter $i$. These bounds remain true if the gap contains several returns. At $k=0$ the same bounds hold with $D_0=0$.

Restrict (46) to extension indices at least $k$ in (47). For instance, the suffix $b$ permits indices $1,2$, the suffix $c$ permits $3,4,5,6$, $cc$ permits $4,5,6$, and $T$ permits $5,6$. Their preceding letters are read from the explicit blocks. Formula (47), and the requirement of two distinct extensions on both sides, give the following table containing every possible unordered boundary pair; reversing a pair is allowed.

| $k$ | Boundary pairs $\{s,t\}$ covering all possibilities, with multiplicity | Bound on $|v|/P$ |
|---:|---|---:|
| $0$ | $(\varepsilon,z)$, $z\in\mathcal S$ | $1$ |
| $1$ | $(\varepsilon,z)$, $z\in\mathcal S$; $(b,b)$ | $1$ |
| $2$ | $(\varepsilon,z)$, $z\in\{\varepsilon,c,cc,T\}$ | $1$ |
| $3$ | $(c,c),(c,cc),(c,T)$ | $14/13$ |
| $4$ | $(cc,cc),(cc,T)$ | $29/27$ |
| $5$ | $(T,T)$ | $62/57$ |

Here is a full numerical verification of the bounds. At $k=0$, a nonempty boundary of length $1,1,2,5$ requires a gap containing respectively a block of length at least $2,2,3,6$, equal to $1+|z|$. At $k=1$ the corresponding numerators $D_k+1+|z|$ are $3,3,4,7$, bounded by (48); the empty pair has numerator $2$ and denominator at least $3$. For $(b,b)$ the numerator is $4$. A smaller possible gap would have to be the single return $01$, of output length $3$, with both output occurrences supported on source extensions $1,2$. Formula (47) would then force the source factor $20102$. It is absent: its middle $010$ parses as $\varphi(0)0$, and parsing the complete factor forces $101$ in the preimage; $101$ would in turn force $00$, which the substitution never produces. Thus $P\ge4$. At $k=2$ the positive-boundary numerators are $6,7,10$, with denominators at least $6,7,10$; the empty numerator is $5$ and its denominator at least $6$. At $k=3$ the three ratios are bounded by $14/13,15/14,18/17$; at $k=4$ by $29/27,32/30$; and at $k=5$ by $62/57$. This proves the table. Its boundary list is exhaustive: if both boundary restrictions omit the central index $k$, (47) leaves only $(6,6)$ and no bispecial factor; the remaining exclusions have a single output extension. All displayed bounds are smaller than $10/9<L$. The last strict inequality follows from $\Lambda>21/10$, since $(21/10)^3(21/10-2)<1$.

For a nonpalindromic source bispecial $w$, including either orientation, source Lemma 10 gives for every source return $R$ either

$$
\vec R\ge\vec w+b_6
\quad\text{or}\quad
\vec R\ge\vec w+b_0+b_1+\cdots+b_5.
$$

The respective extra image lengths are $13$ and $17$. Since $1+|s|+|t|\le11$ by (46), every output return satisfies $|v|\le P-2<P$. This disposes of every nonpalindromic series at every index.

For the infinite palindromic series, retain $M,\mathsf A,\mathsf B_i,f_n$ from (2). Here $i=n\bmod6$. Both extension sets of the Type I factor at index $n$, and of the Type II factor corresponding to $f_n$ for $n\ge6$, are $\{i,6\}$. This follows from the cyclic extension update in source Definition 8, starting with extensions $\{0,6\}$. Therefore their boundary contributions in (45) are bounded by

$$
(b_0',b_1',b_2',b_3',b_4',b_5')=(1,1,1,3,5,11).
\tag{49}
$$

The primes distinguish these six scalars from the coordinate vectors $b_j$. Source Lemma 9 and Remark 7 supply the minimum return vectors $M^n b_6$ for Type I and $M^n b_0$ for Type II, with componentwise domination by every other return vector. Thus it remains to prove

$$
\begin{aligned}
h(f_n+M^n b_6)+b_i'&\le LhM^n b_6 &&(n\ge0),\\
h f_n+b_i'&\le LhM^n b_0 &&(n\ge6).
\end{aligned}
\tag{50}
$$

We give finite and uniform estimates for the entire index domains. Put

$$
k=(1,1,1,1,2,4,8),\qquad
Q(z)=(z-1)(z^2-3),\qquad A_n=hM^n b_6.
$$

Direct row multiplication gives $h=kQ(M)$. Using the whole supplied spectral formula of Appendix Lemma 21, with its exact $d=3$ normalization, gives

$$
A_n=\sum_{\lambda^4-2\lambda^3-1=0}
 \frac{Q(\lambda)\lambda^{n+4}}{4\lambda-6}.
\tag{51}
$$

In particular, there are no tribonacci-root contributions, and

$$
A_{n+4}=2A_{n+3}+A_n,\qquad
(A_0,A_1,A_2,A_3)=(13,27,57,121).
$$

Define

$$
S(n)=\sum_{\substack{\lambda^4-2\lambda^3-1=0\\\lambda\ne\Lambda}}
 \frac{Q(\lambda)}{4\lambda-6}
 \left(\frac{\lambda-2}{3-\lambda}
       -\frac{\Lambda-2}{3-\Lambda}\right)\lambda^{n+4}.
$$

The supplied expression (2), with the rational functions (6), now yields the exact equalities

$$
\begin{aligned}
h(f_n+M^n b_6)-LA_n&=S(n)-h\mathsf B_i b_0,\\
h f_n-LhM^n b_0&=S(n-3)-h\mathsf B_i b_0\qquad(n\ge6).
\end{aligned}
\tag{52}
$$

For the second equality, use $(\lambda-2)\lambda^3=1$ for every root in (51). No estimate of an asymptotic exponent replaces either equality.

The exact boundary margins are

$$
\begin{gathered}
(h\mathsf B_i b_0)_{i=0}^5
 =\tfrac1{13}(19,31,41,45,83,171),\\
(h\mathsf B_i b_0-b_i')_{i=0}^5
 =\tfrac1{13}(6,18,28,6,18,28).
\end{gathered}
\tag{53}
$$

They follow by substituting the row $h$ into the explicit matrix $\mathsf B_i$ in (2). Notice that the margins have period three, which will cover Type II without losing its initial indices.

We next bound $S(n)$ uniformly. The negative root of $z^4-2z^3-1$ is $-s$, with $7/10<s<3/4$. The derivative $2z^2(2z-3)$ shows that the only real roots are this root and $\Lambda$; write the others as $z,\overline z$. Their product gives $|z|^2=1/(\Lambda s)<100/147<25/36$, since $\Lambda>21/10$. Thus each of the three non-Perron roots has modulus less than $5/6$. For any such root $\lambda$,

$$
|Q(\lambda)|<7,\qquad |4\lambda-6|>8/3,
$$

and its summand before the factor $\lambda^n$ can be bounded using

$$
\begin{aligned}
\left|\left(\frac{\lambda-2}{3-\lambda}
 -\frac{\Lambda-2}{3-\Lambda}\right)\lambda^4\right|
&\le \frac{|\lambda|}{3-|\lambda|}
 +\frac{|\lambda|^4}{\Lambda^3-1}\\
&<\frac5{13}+\frac{625}{9072}<\frac12.
\end{aligned}
$$

We used $(\lambda-2)\lambda^3=1$ and $\Lambda^3>8$. Summing the three terms proves

$$
|S(n)|<\frac{63}{16}(5/6)^n<4(5/6)^n.
$$

For every $n\ge12$, this is smaller than $6/13$, because $4(5/6)^{12}<6/13$. It is therefore smaller than every margin in (53).

For $0\le n\le11$, use the rational lower bound

$$
\Lambda>\frac{2106919}{10^6},\qquad L>\frac{10^6}{893081}.
$$

Indeed substitution into $z^4-2z^3-1$ gives
$-3668139160725701279/10^{24}<0$, and the polynomial is strictly increasing for $z>2$. The following integer table proves the first inequality in (50) at all the remaining indices: its last column is exactly
$10^6 A_n-893081(A_n+h f_n+b_i')$.

| $n$ | $A_n$ | $h f_n$ | $b_i'$ | Positive numerator |
|---:|---:|---:|---:|---:|
| $0$ | $13$ | $0$ | $1$ | $496866$ |
| $1$ | $27$ | $1$ | $1$ | $1100651$ |
| $2$ | $57$ | $4$ | $1$ | $1628978$ |
| $3$ | $121$ | $11$ | $3$ | $434065$ |
| $4$ | $255$ | $24$ | $5$ | $1364996$ |
| $5$ | $537$ | $51$ | $11$ | $2044481$ |
| $6$ | $1131$ | $134$ | $1$ | $359454$ |
| $7$ | $2383$ | $283$ | $1$ | $1152973$ |
| $8$ | $5021$ | $598$ | $1$ | $1884780$ |
| $9$ | $10579$ | $1263$ | $3$ | $455555$ |
| $10$ | $22289$ | $2662$ | $5$ | $1270564$ |
| $11$ | $46961$ | $5609$ | $11$ | $1907939$ |

Every entry follows from (51) and the supplied recurrence
$f_0=0$, $f_{n+1}=Mf_n+b_0+2b_6$ when $n+1\equiv0\pmod6$, and $f_{n+1}=Mf_n+b_0$ otherwise. Thus the table is finite exact arithmetic, with the remaining infinitely many indices covered by the preceding estimate.

Together with (52)–(53) this proves $S(n)<h\mathsf B_i b_0-b_i'$ for every $n\ge0$. For Type II, set $m=n-3\ge3$. The margin at $m\bmod6$ equals the margin at $n\bmod6$ by (53). Apply the already proved inequality to $S(m)$ in the second line of (52). This proves the second line of (50) for every $n\ge6$, including its finite initial segment. Componentwise domination of all source returns then proves the required output return bound for both series.

We have exhausted the marker-free factors, all finite source classes, both infinite palindromic classes and every nonpalindromic class, including all output boundary contributions. The ordinary-exponent criterion consequently gives $E(x)\le1+L=e_3$. The reverse inequality follows directly from Theorem 2.1 for this nonerasing morphism. This proves (44). $\square$

## 14. Equality classification at total length thirty

**Theorem 14.1 (Sharpness and uniqueness in the four-total-letter literal class).** Among all $(\theta,p)\in\mathcal L_3$ for which $\theta(u_7)$ is rich, has exactly four actual letters, and has ordinary exponent $e_3$, the minimum of

$$
H(\theta)=\sum_{i=0}^6|\theta(i)|
$$

is $30$. Every pair attaining $H=30$ is (43), including its marker, up to a bijective renaming of the four output letters.

*Proof.* Corollary 9.2 already supplies $H\ge30$ with precisely these hypotheses and every nonempty marker. Theorems 12.2 and 13.1 supply attainment, so only equality classification remains.

Write $m=|p|$, $h_i=|\theta(i)|$ and $t=h_3$. Theorem 8.2 excludes $m\ge2$, since then $H\ge46$. Thus $p=a$ is a single letter. Cancellation, the complete row parameterization and the size formula are reused from Corollary 3.2 and Theorem 4.2:

$$
H=4t+8h_0+4h_1+2h_2=30.
\tag{54}
$$

Each independent parameter is at least one, and at most one of $h_0,h_1,h_2,t$ can be one, by monoid injectivity. If none is one, the right side of (54) is at least $36$. If its unique one is at $h_1,t,h_2$, the respective minimum values are $32,32,34$. Hence $h_0=1$, the other three parameters are at least two, and (54) reduces to

$$
4(t-2)+4(h_1-2)+2(h_2-2)=2.
$$

It forces $(h_0,h_1,h_2,t)=(1,2,3,2)$. Formula (19) gives the full row $(1,2,3,2,3,6,13)$. This arithmetic step establishes row uniqueness only; the following steps determine the words.

Write $\theta(i)=a q_i$ with palindromic, $a$-free $q_i$. Then $q_0=\varepsilon$, $q_1=b$ and $q_3=c$ for distinct nonmarker letters $b,c$. Let $d$ be the third nonmarker. There are exactly these three nonmarkers, since every source letter occurs. The length-two palindromes are

$$
q_2=z^2,\qquad q_4=y^2,\qquad z,y\in\{b,c,d\},\quad z\ne y.
\tag{55}
$$

We use the supplied complete-return characterization of richness, Glen–Justin–Widmer–Zamboni, [*Palindromic richness*, arXiv:0801.1656v1, Theorem 2.14 and Remark 2.15](https://arxiv.org/pdf/0801.1656v1). In particular, a factor from a last previous occurrence of a letter $\ell$ to its first occurrence in a new block is a complete return. Its second and penultimate letters must agree. Also $e_3<15/7$, so any explicitly found repetition of larger exponent is impossible.

First $z\ne c$. Otherwise the actual source factor $2F_2 3F_2 2$ gives the two occurrences of

$$
v=c\theta(F_2)a c.
$$

The word $F_2=010$ has image length $4$, so $|v|=7$. The starts are at distance $|\theta(F_2 3)|=6$, since $q_2=cc$ and $q_3=c$. The factor ending at the end of the second occurrence has period $6$ and length $13$, giving $E\ge13/6>15/7$. The source factor used here occurs already in $F_4$.

If $z=d$, or if $y=d$, all three nonmarkers have occurred in the unary blocks $q_1,q_2,q_3,q_4$ before the first $q_5$. Consider the actual prefix $\theta(F_5)a q_5$. For each of these letters its last occurrence in $\theta(F_5)a$ is followed by $a$. If $q_5$ is not constant, take its first letter different from its initial letter. This occurrence is preceded by a nonmarker, and the complete return from its last previous occurrence cannot be a palindrome. If $q_5$ is constant, its length five gives exponent five. Both alternatives are impossible. Consequently (55) forces

$$
q_2=bb,\qquad q_4=cc.
\tag{56}
$$

This accounts for every ordered choice in (55).

The only letters used before $q_5$ are now $a,b,c$. In $\theta(F_5)a$, the last $b$ and last $c$ are followed by $a$. In $q_5$, the first occurrence of either of these two letters cannot be at a noninitial position, by the same complete-return argument. A constant $q_5$ is impossible. It follows that $q_5$ uses exactly $\{x,d\}$, starts with $x\in\{b,c\}$, and contains $d$. Write its length-five palindrome as $xuvux$. There are only three possibilities using both letters:

$$
xxdxx,\qquad xdxdx,\qquad xdddx.
$$

Indeed the alternative $u=x,v=x$ is constant. The last two displayed possibilities have exponents $5/2$ and $3$ on their indicated alternating factor or constant run. Thus

$$
q_5=xxdxx\qquad(x=b\text{ or }c).
\tag{57}
$$

We next determine $q_6$ without choosing between these two branches. The ruler identity gives $F_6=F_5 5F_5$. Immediately before the first $q_6$, the last occurrences of $b,c$ are in the final unary-block word $\theta(F_5)$ and are followed by $a$. The last $d$ is the middle of the preceding $q_5=xxdxx$ and is followed by $x$.

The first letter of $q_6$ cannot be $d$: its preceding letter would be the marker $a$, contradicting the complete return from the preceding $d$, whose second letter is $x$. If the first letter is the other letter in $\{b,c\}\setminus\{x\}$, the first subsequent $x$ would contradict its preceding complete return, and a first subsequent $d$ would have to be preceded by $x$, also impossible. This would make $q_6$ constant. Hence $q_6$ starts with $x$, contains no other member of $\{b,c\}$, and contains $d$.

The complete return from the last preceding $d$ to the first $d$ in $q_6$ has the form

$$
d\,xx\,\theta(F_5)a\,x^j d,
$$

where $j$ is the initial run length of $x$ in $q_6$. It must be a palindrome. A run of length three is impossible, and $j=1$ makes its third letter $x$ and its third letter from the end $a$. Thus $j=2$. Palindromicity and the even length $12$ now give

$$
q_6=xxd\,u v w w v u\,dxx,
\qquad (u,v,w)\in\{x,d\}^3.
\tag{58}
$$

All eight branches of (58) are settled by the following table. The indicated obstruction is a factor of the corresponding word in (58).

| $uvw$ | Obstruction or surviving word |
|---|---|
| $xxx$ | $xxx$ |
| $xxd$ | $xxdxxddxxdxx$ |
| $xdx$ | $xdxdx$ |
| $xdd$ | $ddd$ |
| $dxx$ | $xxx$ |
| $dxd$ | $ddxddxdd$ |
| $ddx$ | $ddd$ |
| $ddd$ | $ddd$ |

The obstructions have exponents $3$, $5/2$ or, for $ddxddxdd$, $8/3$, all larger than $e_3$. Consequently

$$
q_6=xxdxxddxxdxx.
\tag{59}
$$

Finally exclude $x=b$. In that branch $q_2=bb$ and $q_6$ both start and end in $bb$. Take the supplied Type I source factor at index $2$. It has both extension sets $\{2,6\}$, Parikh vector $f_2+M^2b_6$, and an actual return of Parikh vector $M^2b_6$. The already fixed row gives

$$
h f_2=4,\qquad hM^2b_6=57.
$$

Extend each of two occurrences realizing this return by $bb$ to the left and $a bb$ to the right. All these extensions are legitimate, because both possible source neighbors are $2$ or $6$. Thus the actual output factor

$$
v=bb\,\theta(w_2^{\mathrm I})a bb
$$

has length $57+4+5=66$, and two occurrences at distance $57$. The factor from the first start through the second end has period $57$, hence exponent at least

$$
1+\frac{66}{57}=\frac{41}{19}>\frac{15}{7}>e_3.
$$

This contradiction excludes the entire $x=b$ branch. Hence $x=c$, and (56), (57), (59), together with $q_0,q_1,q_3$, give precisely (43). The marker was already forced to be $a$. All identifications used only a bijective naming of the four actual letters, completing the equality classification. $\square$

## 15. Consequences for the original-source and threshold questions

**Corollary 15.1 (Four-letter existence and the retained lower-bound question).** The original $u_7$ admits a nonerasing morphism onto exactly four actual letters whose image is infinite rich and has ordinary critical exponent $e_3$. In the notation of Definition 3.3,

$$
RT(\mathcal C_4)\le e_3.
\tag{60}
$$

The minimum $H=30$ and the equality classification of Theorem 14.1 concern the literal class $\mathcal L_3$ with a nonempty marker. They impose no such minimum or classification on arbitrary nonliteral morphisms. The unrestricted reverse inequality $RT(\mathcal C_4)\ge e_3$, the analogous exact small-alphabet existence for every $r\ge4$, and existence of a nonconstant family of rich original-source images with exponents strictly above and tending to $e_3$ remain separate questions.

*Proof.* Apply Theorems 12.2 and 13.1 to (43). This is also an arbitrary-nonerasing-morphism existence witness, since that larger class contains the literal class. Taking the infimum over all infinite rich four-letter words proves (60). Theorem 14.1 uses the literal marker conditions in its size and word arguments; there is no implication giving them for an arbitrary morphism. Inequality (60) is an upper bound supplied by one actual word and supplies no lower bound for all words in $\mathcal C_4$. The construction fixes $r=3$ and gives one exact exponent, so it supplies neither the higher-parameter constructions nor a family with strictly positive exponent excess. $\square$

## 追加锚（本行以下为增补区）
