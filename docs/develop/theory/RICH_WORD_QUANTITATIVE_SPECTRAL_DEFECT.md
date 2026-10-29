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
## 4. Cancellation without richness in an actual source image

**Proposition 4.1 (The normalized cancellation boundary).** Specialize Definition 1.2 to $r=3$, write the substitution as $\varphi_3$, and let $u_7=\varphi_3^\omega(0)$. Define the nonerasing morphism $\eta_3:\{0,1,2,3,4,5,6\}^*\to\{0,1,2,3\}^*$ by

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

## 5. Scope of the cancellation boundary

The example satisfies the exact necessary cancellation condition from Corollary 3.2 and is an actual nonerasing source image, but its finite factor $z$ fails the defining richness condition. Therefore $h v_\beta=0$ is not sufficient for richness, and it is not a richness-preserving construction principle. Theorem 2.1 still supplies the ordinary bound $E(w_3)\ge e_3$ through its zero-defect case; this example supplies no matching upper bound and no assertion about attainment.

This conclusion is restricted to the displayed $r=3$ morphic image and its explicit factor. It does not impose a condition on every rich word, does not prove or refute the unrestricted equality

$$
RT(\mathcal C_d)=E^*(u_{2d-1})\qquad(d\ge2),
$$

and does not provide the upper construction required for that equality. In particular, cancellation, richness, and control of the ordinary exponent remain separate requirements for any proposed source-image route.

## 追加锚（本行以下为增补区）
