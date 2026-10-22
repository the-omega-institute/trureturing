# An actual-source Gaussian record attainer

## 1. Sources, preparations and exact settings

**Definition 1.1 (The historical source and its complete worlds).** Write G for [Shared Gaussian Record Laws](https://github.com/the-omega-institute/trureturing/blob/f64e5d450ddd0c3ac65b4d11005f3ef9ee961176/docs/develop/theory/FIB_SHARED_GAUSSIAN_RECORD_LAWS.md), C for [Categorical Decision Blindness](https://github.com/the-omega-institute/trureturing/blob/f64e5d450ddd0c3ac65b4d11005f3ef9ee961176/docs/develop/theory/FIB_ATOM_CATEGORICAL_DECISION_BLINDNESS.md), and III for [Strict Real Joint Incidence Support III](https://github.com/the-omega-institute/trureturing/blob/30b32d5e17e23590839090a0b244c019c4796817/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md). The III in this definition is precisely the historical source specified by G, Definition 12.1. In particular its arc is the arc of III, Definition 16.2, Lemma 16.3 and Theorem 16.4, with the exact polynomial centres in (16.7), not an arc reselected from a later version.

Other repository references are read at `4b07e9740ce998ee7cf899f4b1897bf61a3bf713` unless a different revision is explicitly given, and each cited definition retains its own historical supplier bindings.

Use a parameter $\beta$ for the upper-right entry of a source matrix; it is distinct from the height $b$ of C, Definition 13.1. For $t,\beta>0$ with $t\beta<1$, put

$$
\begin{gathered}
r=t\beta,\qquad c=t(1-r),\qquad
P=\begin{pmatrix}r&\beta\\c&1-r\end{pmatrix},\\
j=t+\beta(1-t^2),\qquad n=j+r,\qquad
T=1+\beta,\qquad U=1+2\beta,\\
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
\kappa=\frac6T-\frac2U,\qquad
\eta=-\frac{24}{5}\left(\beta-\frac18\right)\kappa.
\end{gathered}
\tag{1.1}
$$

On $\Lambda\ne0$ define $e=\eta/\Lambda$, $d=24+e$, and

$$
\begin{gathered}
G_0=-24-e,\qquad G_1=-e/j,\qquad
G_2=(27/5-e)/T,\qquad G_3=-e/n,\\
\lambda_h(s)=\prod_{\substack{0\le k\le3\\k\ne h}}\frac{s-k}{h-k},\qquad
g(s)=\sum_{h=0}^3G_h\lambda_h(s)=\sum_{h=0}^3a_hs^h,\\
G_5=-4G_0+15G_1-20G_2+10G_3,\\
G_6=-10G_0+36G_1-45G_2+20G_3,\\
G_7=-20G_0+70G_1-84G_2+35G_3,\\
p(t,\beta)=d+(U+n)G_5,\qquad
V(t,\beta)=d+(2U+n)G_6,\\
a(t,\beta)=d+(T+2j+4r)G_7,\qquad
m(t,\beta)=d+(3U+2n)G_7.
\end{gathered}
\tag{1.2}
$$

These formulas specify the entire polynomial, including all padded coefficients, and both original seventh-clock alternatives. They are the regular-source form of III, (16.1)–(16.5). Indeed, if $A=(8\beta-1)(2+5\beta)$ and $D=(5/2)TUjn\Lambda$, then $e=-3Ajn/D$, the drift and first four gain values in (1.2) are exactly $-C_0/D,C_0/D,C_1/D,C_2/D,C_3/D$ in that source, with $d$ listed first.

Let

$$
z_J(p)=(t_H(p),\beta_H(p),t_L(p),\beta_L(p)),\qquad 10\le p\le34,
\tag{1.3}
$$

be the unique zero in the certified pointwise radius-$10^{-5}$ balls of III, (16.6)–(16.7). The identification across the parameter seams is that of III, Lemma 16.3. Let $W_L(p)$ be the complete world $(P,g,d)$ obtained from its lower pair $(t_L(p),\beta_L(p))$ by (1.1)–(1.2), and write

$$
f(p)=v_J(p)=V(t_L(p),\beta_L(p)).
\tag{1.4}
$$

The ambient parent $\mathcal H_{\rm par}$ and the source set remain exactly those of G, Definition 12.1:

$$
K_J=\{W\in\mathcal H_{\rm par}:10\le p(W)\le34,\quad v(W)=v_J(p(W))\}.
\tag{1.5}
$$

Thus all companions of each such child are included, as are the retained $p=24$ fibre and any singular, lower-degree, sampled-zero or zero-drift strata allowed there. The function $W_L$ selects some preparations from $K_J$; it does not replace $K_J$ by a selected pair or by a curve of deduplicated laws.

**Assumption 1.2 (The original shared apparatus).** Use exactly G, Assumptions 2.1 and 4.1, with $\sigma=1$. In particular, the system is $\mathcal H=L^2(\mathbb R^{17};\mathbb C)$, column vectorization is $\operatorname{vec}(X)=(X_{11},X_{21},X_{12},X_{22})^T$, and the supplied preparation for a complete world is

$$
\begin{gathered}
m_W=(d,\operatorname{vec}(a_0P),\operatorname{vec}(a_1P),
\operatorname{vec}(a_2P),\operatorname{vec}(a_3P)),\\
\psi_W(x)=\pi^{-17/4}\exp(-\|x-m_W\|^2/2),\qquad
\rho_W=|\psi_W\rangle\langle\psi_W|.
\end{gathered}
\tag{1.6}
$$

Supply eight independent probes in $k_1(z)=(2\pi)^{-1/4}e^{-z^2/4}$, independent of the system and the controller. The original controls are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
A_E=\operatorname{diag}(1,I_2\otimes E,I_2\otimes E,I_2\otimes E,I_2\otimes E),
\tag{1.7}
$$

with the fixed half-density pullback $(U_A\psi)(x)=|\det A|^{-1/2}\psi(A^{-1}x)$. At each acquired clock use G's coupling $\exp(-iF_j(q)\otimes\pi_j^{\rm pr})$ and probe-position meter, where

$$
\ell_j^T=(1,t_0^T,jt_0^T,j^2t_0^T,j^3t_0^T),\qquad
t_0=\operatorname{vec}(I_2),\qquad F_j(q)=\ell_j^Tq.
\tag{1.8}
$$

The first matrix-block coefficient is one also at clock zero. There is no intervening free evolution that changes system positions, no reset and no postselection. All meter values are retained. Preparation availability is an explicit premise for (1.6); it supplies neither an encoder from an unknown original carrier nor a preparation algorithm or physical installation theorem.

**Definition 1.3 (One word and exact public constants).** Fix the chronological word

$$
w=JMJMMM,
\tag{1.9}
$$

with reads $0,\ldots,6$. Put $Q_0=I_2$, $Q_j=E_j\cdots E_1$, $T_j=A_{E_j}\cdots A_{E_1}$, and stack the seven rows

$$
L_j=\ell_j^TT_j
=(1,\operatorname{vec}(Q_j^T)^T,j\operatorname{vec}(Q_j^T)^T,
j^2\operatorname{vec}(Q_j^T)^T,j^3\operatorname{vec}(Q_j^T)^T)
\tag{1.10}
$$

into $L\in\mathbb R^{7\times17}$. Define

$$
\begin{gathered}
C_7=I_7+\tfrac12LL^T,\qquad S=C_7^{-1/2},\\
y(p)=(0,24,147/5,24,18,p,f(p))^T,\qquad
\gamma(p)=Sy(p).
\end{gathered}
\tag{1.11}
$$

Here the square root is the positive definite square root; $C_7$ is positive definite because $x^TC_7x=\|x\|^2+\|L^Tx\|^2/2>0$ for $x\ne0$.

For $n\ge0$ and $0\le k<2^n$, let

$$
a_{nk}=15+\frac{17k}{2^n},\qquad d_{nk}=15+\frac{17(k+1)}{2^n}.
\tag{1.12}
$$

Order these pairs first by $n$ and then by $k$. Choose the first pair for which

$$
f\left(\frac{a_{nk}+d_{nk}}2\right)
\ne\frac{f(a_{nk})+f(d_{nk})}2,
\tag{1.13}
$$

and call its endpoints $a_*,d_*$. Put

$$
A=\gamma(a_*),\qquad D=\gamma(d_*),\qquad Z=(A+D)/2,
\tag{1.14}
$$

and let $c_*$ be the least zero on $[a_*,d_*]$ of

$$
H(p)=\|\gamma(p)-A\|^2-\|\gamma(p)-D\|^2.
\tag{1.15}
$$

Finally set

$$
\begin{gathered}
B=\gamma(c_*),\qquad q=\tfrac12\|D-A\|,\qquad b=\|B-Z\|,\\
u=(D-A)/(2q),\qquad v=(B-Z)/b.
\end{gathered}
\tag{1.16}
$$

Complete $u,v$ to an orthonormal basis of $\mathbb R^7$ by Gram–Schmidt on the standard basis in its usual order, omitting each zero residual. Let $O$ have these basis vectors as rows, beginning with $u^T,v^T$, and define the whole-record affine map

$$
\mathcal F(r)=O(Sr-Z),\qquad
\mathcal F^{-1}(s)=C_7^{1/2}(O^Ts+Z).
\tag{1.17}
$$

The existence of the chosen pair and root, and $q,b>0$, are conclusions of Theorem 2.1. These selection rules define mathematical constants. They do not posit a decision procedure for equality of real numbers, an arithmetic acquisition bound or a bounded-precision implementation.

## 2. The source-specific complete-law attainer

**Theorem 2.1 (Five original labels attained by one complete source execution).** Under Assumption 1.2, all constants of Definition 1.3 exist, and $q,b>0$. The five complete worlds

$$
W_1=W_2=W_L(a_*),\qquad W_3=W_L(c_*),\qquad
W_4=W_5=W_L(d_*)
\tag{2.1}
$$

belong to the actual $K_J$ in (1.5). Let $I$ have the uniform prior on the five original labels, with one common initialization

$$
\Omega=\frac15\sum_{i=1}^5|i\rangle\langle i|
\otimes\rho_{W_i}\otimes(|k_1\rangle\langle k_1|)^{\otimes8}
\otimes\rho_{\rm ctl}.
\tag{2.2}
$$

The label register is inaccessible to the controller. Its initial state $\rho_{\rm ctl}$, the executed word (1.9), the couplings, meter settings and $\sigma=1$ are the same for every label and independent of all outcomes. Then the entire actual acquired record $R=(R_0,\ldots,R_6)$ satisfies

$$
R\mid(I=i)\sim\mathcal N_7(y(p_i),C_7),\qquad
(p_1,p_2,p_3,p_4,p_5)=(a_*,a_*,c_*,d_*,d_*).
\tag{2.3}
$$

For the single public invertible map (1.17), write $Y=\mathcal F(R)=(Y^{(2)},N)$, with $N\in\mathbb R^5$. Its exact joint law is

$$
\mathbb P(I=i,Y^{(2)}\in dx,N\in dz)
=\frac15\,\mathcal N_2(\mu_i,I_2)(dx)\,\mathcal N_5(0,I_5)(dz),
\tag{2.4}
$$

where

$$
\mu_1=\mu_2=(-q,0),\qquad \mu_3=(0,b),\qquad
\mu_4=\mu_5=(q,0).
\tag{2.5}
$$

In particular every nuisance coordinate is standard Gaussian, the five nuisance coordinates are independent, and their vector is independent of the joint pair $(I,Y^{(2)})$. The original five-label prior is preserved; the three distinct preparation clusters have weights $2/5,1/5,2/5$.

The map preserves the complete relevant instrument, including its selective system successors and its nonselective channel. More precisely, let $\mathcal I_w$ be G's seven-acquisition instrument on the system and define $\mathcal I_w^{\mathcal F}(E)=\mathcal I_w(\mathcal F^{-1}E)$ for Borel $E\subseteq\mathbb R^7$. With

$$
\begin{aligned}
\mathsf K_w(r)
&=K_6(r_6)U_{A_{E_6}}\cdots K_1(r_1)U_{A_{E_1}}K_0(r_0),\\
K_j(r_j)&=k_1(r_j-\ell_j^Tq),\qquad D_{\mathcal F}=OS,
\end{aligned}
\tag{2.6}
$$

its density in transformed coordinates is

$$
\widetilde{\mathsf K}(s)
=|\det D_{\mathcal F}|^{-1/2}\mathsf K_w(\mathcal F^{-1}s).
\tag{2.7}
$$

Thus, for every trace-class system input $\rho$, the complete CP output is the pushforward of the original CP output, and normalized selective states at $r$ and $\mathcal F(r)$ coincide whenever their outcome density is positive. No acquisition, posterior factor or relevant quantum successor is replaced by the two-coordinate marginal. The unused eighth probe remains in its original independent state.

This theorem establishes one actual preparation-to-complete-acquired-law interface, with an exact all-record representation of C, Definition 13.1. It does not assert that every $q,b>0$, any prescribed critical path, a shortest word or an optimal total cost is attained.

**Proof.** First consider the actual complete-world equations. On each selected lower source, III, (16.12) gives $0<r<1$, $\beta>0$ and $\Lambda>0$. The matrix has $c=r(1-r)/\beta>0$, trace one and determinant zero. To verify the gain correspondence directly, $j=\beta+c$ and $n=j+r$ are positive, and the first four readouts from (1.2) are

$$
d+G_0=0,\quad d+jG_1=24,\quad
d+TG_2=147/5,\quad d+nG_3=24.
\tag{2.8}
$$

Lagrange extrapolation gives $G_4=-G_0+4G_1-6G_2+4G_3$. Hence

$$
G_4=24-\frac{162}{5T}+e(\Lambda-1/U),\qquad
d+UG_4=24+24U-\frac{162U}{5T}+U\eta=18.
\tag{2.9}
$$

The last equality follows from the identity

$$
\eta=\frac{162}{5T}-24-\frac6U,
\tag{2.10}
$$

which is (1.1) after multiplication by the positive denominator $TU$. Equations (2.8)–(2.9) are the original whole parent history $H_4$, with one fixed drift and one entire polynomial. That polynomial is nonzero because otherwise all five values would equal $d$, contradicting $0\ne24$. The formulas for $G_5,G_6,G_7$ are evaluations of this same polynomial. The four equations defining $z_J(p)$ then give $p(t_L,\beta_L)=p$ and $V(t_L,\beta_L)=v_J(p)$, as well as equality with the other actual source in the clock-seven $J$ response. This is precisely the lifting of III, Theorem 16.4. It proves $W_L(p)\in K_J$ for all $p\in[10,34]$, without dividing by any sampled gain or imposing regular-source conditions on other members of $K_J$. In particular each world retains both values $a(t_L,\beta_L)$ and $m(t_L,\beta_L)$ of (1.2) as its original alternative responses.

We next prove that $f$ is not affine on $[15,32]$ using the exact historical source, rather than a rounded drawing of the arc. At $p=15,25,32$, the lower coordinates of the respective centre maps in III, (16.7) are the following rational pairs; each entry is divided by $10^{20}$:

| $p$ | Centre $t$ numerator | Centre $\beta$ numerator |
| --- | --- | --- |
| $15$ | $210788533712955551542$ | $4532053336144848092$ |
| $25$ | $219625886685223990790$ | $13475282226511291486$ |
| $32$ | $221845194568232864125$ | $20494322221751046893$ |

Call these pairs $C_{15},C_{25},C_{32}$. The contraction bounds of III, (16.11), together with its proof's estimate $\|z_J(p)-\widehat z(p)\|_\infty\le\eta_{\rm con}/(1-q_{\rm con})$, give respectively

$$
\|(t_L(p),\beta_L(p))-C_p\|_\infty
<\frac1{300000},\quad\frac1{2000000},\quad\frac1{4000000}.
\tag{2.11}
$$

Indeed the three upper quotients are $(19/10^7)/(1-2/5)$, $(41/10^8)/(1-17/100)$ and $(2/10^7)/(1-3/100)$. The centre and the entire segment to the actual root lie in

$$
\mathcal D=[2,9/4]\times[1/25,21/100].
\tag{2.12}
$$

For clarity, the rational response and its error bound can be estimated without the large numerator arrays of III. On $\mathcal D$,

$$
\begin{gathered}
j\ge137/100,\qquad n\ge179/100,\qquad
T\ge26/25,\qquad U\ge27/25,\\
\Lambda\ge1+600/121+50/71-400/137-400/179>3/2,\\
0<\kappa<22/5,\qquad |e|<6/5.
\end{gathered}
\tag{2.13}
$$

For example $j_t=1-2t\beta>0$ and $n_t=1+\beta(1-2t)>0$ on this rectangle, whereas $j_\beta=1-t^2<0$ and $n_\beta=1+t-t^2<0$; these signs give the displayed lower bounds for $j,n$. The $T,U$ upper endpoints give the positive terms in the lower bound for $\Lambda$. The estimate for $e$ follows from $|\beta-1/8|\le17/200$, $\Lambda>3/2$ and the bound on $\kappa$.

Write the stable sixth-gain formula as

$$
\begin{gathered}
k_6=240-243/T,\qquad h_6=10-36/j+45/T-20/n,\\
G_6=k_6+eh_6,\qquad V=24+e+(2U+n)G_6.
\end{gathered}
\tag{2.14}
$$

All entries in the following table are exact rational endpoints, with finite decimals denoting rationals. Direct substitution of the three rational pairs into (1.1) and (2.14) gives these strict enclosures:

| Centre | $e$ | $k_6$ | $h_6$ | $2U+n$ |
| --- | --- | --- | --- | --- |
| $C_{15}$ | $(.4088,.4090)$ | $(7.535,7.536)$ | $(24.835,24.838)$ | $(4.2286,4.2287)$ |
| $C_{25}$ | $(-.0651,-.0650)$ | $(25.856,25.857)$ | $(18.123,18.126)$ | $(4.5159,4.5161)$ |
| $C_{32}$ | $(-.7937,-.7936)$ | $(38.330,38.332)$ | $(11.201,11.203)$ | $(4.6891,4.6893)$ |

These are rational inequalities: for the first $e$ entry, for example, substitute the first pair to obtain $.4088\Lambda<\eta<.4090\Lambda$; for $k_6$, multiply the two asserted inequalities by $T$; for $h_6$, multiply by $jnT$; and for $2U+n$, substitute its polynomial expression. The same positive-denominator operations apply in all three rows, so no root approximation is used in this table. Multiplication of its signed intervals in (2.14) yields

$$
\begin{array}{c|c}
p&V(C_p)\\\hline
15&(99.1,99.3)\\
25&(135.3,135.5)\\
32&(161.2,161.3).
\end{array}
\tag{2.15}
$$

Here is an explicit derivative bound for passing from those rational centres to the actual sources. On $\mathcal D$, $|j_t|,|n_t|\le1$, $|j_\beta|\le65/16$ and $|n_\beta|\le29/16$. Differentiating (1.1), using (2.13), gives

$$
|\Lambda_t|<17/5,\quad |\Lambda_\beta|<91/5,\quad
|e_t|<68/25,\quad |e_\beta|<313/10.
\tag{2.16}
$$

For the last inequality one may use $|\kappa_\beta|<6/(26/25)^2$, then
$|\eta_\beta|\le(24/5)(22/5+(17/200)6/(26/25)^2)$ and
$|e_\beta|\le(|\eta_\beta|+|e|\,|\Lambda_\beta|)/\Lambda$.
Likewise $e_t=-e\Lambda_t/\Lambda$. The other two bounds follow from

$$
\begin{aligned}
|\Lambda_t|&\le4/(137/100)^2+4/(179/100)^2,\\
|\Lambda_\beta|&\le6/(26/25)^2+2/(27/25)^2
+4(65/16)/(137/100)^2+4(29/16)/(179/100)^2.
\end{aligned}
\tag{2.17}
$$

The same denominators in (2.14) give $|k_6|<40$, $|h_6|<91$, $|(h_6)_t|<26$ and $|(h_6)_\beta|<131$. It follows that

$$
|G_6|<150,\qquad |(G_6)_t|<280,\qquad |(G_6)_\beta|<3240.
\tag{2.18}
$$

For example the derivative bounds follow from $(68/25)91+(6/5)26<280$ and $243/(26/25)^2+(313/10)91+(6/5)131<3240$. Finally $2U+n\le509/100$, $|(2U+n)_t|\le1$ and $|(2U+n)_\beta|\le3$. Differentiating $V$ in (2.14) gives

$$
|V_t|<3000,\qquad |V_\beta|<20000.
\tag{2.19}
$$

Consequently $|V(x)-V(x')|<23000\|x-x'\|_\infty$ for distinct points of $\mathcal D$. Equations (2.11) and (2.15) bound the three errors by $23/300$, $23/2000$ and $23/4000$, respectively, and hence also by $.08,.012,.006$. Therefore

$$
\begin{aligned}
f(32)-\tfrac{17}{10}f(25)+\tfrac7{10}f(15)
&>161.2-\tfrac{17}{10}135.5+\tfrac7{10}99.1
-.006-\tfrac{17}{10}.012-\tfrac7{10}.08\\
&=.1376>0.
\end{aligned}
\tag{2.20}
$$

An affine function would make this expression zero since $32=(17/10)25-(7/10)15$. Thus $f$ is not affine on $[15,32]$. Its continuity follows from the analytic arc in III, Lemma 16.3.

If (1.13) failed for every dyadic interval, induction over the dyadic subdivisions would put every dyadic value of $f$ on the endpoint chord from $15$ to $32$. Continuity and density of those grid points would make $f$ affine throughout that interval, contradicting (2.20). The first pair in (1.13) therefore exists. Since $S$ is invertible and the sixth coordinate of $y(p)$ is $p$, $A\ne D$. Moreover

$$
H(a_*)=-\|D-A\|^2<0<\|D-A\|^2=H(d_*).
\tag{2.21}
$$

The intermediate value theorem gives a zero; the zero set is a nonempty compact subset of $[a_*,d_*]$, so its least member $c_*$ exists and lies in the interior. Expanding $H(c_*)=0$ gives

$$
(D-A)^T(B-Z)=0.
\tag{2.22}
$$

If $B=Z$, applying $S^{-1}$ first forces $c_*=(a_*+d_*)/2$ from the $p$ coordinate, and then forces $f(c_*)=(f(a_*)+f(d_*))/2$ from the last coordinate. This contradicts (1.13). Thus $q,b>0$, and (2.22) makes $u,v$ orthonormal. Gram–Schmidt completes them as specified, since the standard basis spans the remaining orthogonal complement. This proves every existence assertion in Definition 1.3, not only a conditional geometry statement.

We now identify the actual acquisition. The chronological matrix products, calculated from the original $J,M$, are

$$
\begin{gathered}
Q_0=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad
Q_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Q_2=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
Q_3=\begin{pmatrix}1&1\\1&0\end{pmatrix},\\
Q_4=\begin{pmatrix}1&0\\2&1\end{pmatrix},\quad
Q_5=\begin{pmatrix}2&1\\3&1\end{pmatrix},\quad
Q_6=\begin{pmatrix}3&1\\5&2\end{pmatrix}.
\end{gathered}
\tag{2.23}
$$

Their traces against $P$ are $1,j,T,n,U,U+n,2U+n$. G, Theorem 3.2 therefore gives $L_jm_W=d+g(j)\operatorname{tr}(Q_jP)$, and (2.8)–(2.9) and the defining arc equations give $Lm_{W_L(p)}=y(p)$. These are original response means, not a replacement of random acquisitions by deterministic history values.

G, Theorems 4.2 and 5.1 apply to this same input and word. In particular their complete all-factor identity is

$$
\mathsf K_w(r)=U_{T_6}\prod_{j=0}^6k_1(r_j-L_jq),
\tag{2.24}
$$

with every factor acting on the same initial position vector. For $m_i=m_{W_i}$ the actual conditional record density is consequently

$$
p_i(r)=\int_{\mathbb R^{17}}\pi^{-17/2}e^{-\|x-m_i\|^2}
\prod_{j=0}^6\frac{e^{-(r_j-L_jx)^2/2}}{\sqrt{2\pi}}\,dx.
\tag{2.25}
$$

Every one of the seven acquisitions appears in (2.24)–(2.25); the shared fifth read is not dropped from the consecutive $M$ actions. Tonelli and normalization of each factor give total mass one. The same theorem identifies (2.25) with the law of $LX+\epsilon$, where $X\mid I=i\sim\mathcal N_{17}(m_i,I_{17}/2)$ and $\epsilon\sim\mathcal N_7(0,I_7)$ is independent of that common $X$. This latent expression follows from the instrument density; it is not a separately supplied sampler or a coupling inferred from separately attainable marginals. It proves (2.3).

The Gaussian supplier can also be expressed in the observation notation of [GaussianObservationLaw](../../../D5/S3/Observer/Linear/GaussianObservationLaw.lean): centre by $m_i$, use observation matrix $L$, prior precision $2$ and noise precision $1$, and translate the observation by $Lm_i$. This is exactly the parameter correspondence in G, Definition 5.2. Affine transformation and independence of Gaussian blocks are the usual finite-dimensional Gaussian facts; for instance they are represented in Mathlib's [HasGaussianLaw independence results](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean). No new Gaussian observation or classification theorem is needed here.

By (1.17), $\operatorname{Cov}(Y\mid I=i)=OSC_7SO^T=I_7$. Its three distinct means are

$$
O(A-Z)=(-q,0,0,0,0,0,0)^T,\quad
O(B-Z)=(0,b,0,0,0,0,0)^T,\quad
O(D-Z)=(q,0,0,0,0,0,0)^T.
\tag{2.26}
$$

Here all subsequent rows of $O$ annihilate both $D-A$ and $B-Z$. The conditional Gaussian density therefore factors into the asserted two-dimensional law and the same five-dimensional standard Gaussian density for every original label. Multiplication by the unchanged prior $1/5$ proves (2.4), including independence from the joint object $(I,Y^{(2)})$, rather than only conditional independence given $I$.

For completeness, fix any trace-class input $\rho$. G's normal instrument defines its output by trace pairings, so the ordinary change of variables $s=\mathcal F(r)$ gives

$$
\begin{aligned}
\mathcal I_w^{\mathcal F}(E)(\rho)
&=\int_{\mathcal F^{-1}E}\mathsf K_w(r)\rho\mathsf K_w(r)^\dagger\,dr\\
&=\int_E\widetilde{\mathsf K}(s)\rho\widetilde{\mathsf K}(s)^\dagger\,ds.
\end{aligned}
\tag{2.27}
$$

For positive inputs Tonelli applies to positive trace pairings; general trace-class inputs follow by linearity. This establishes the CP-output equality for all such inputs, not only equality of five probabilities. Taking $E=\mathbb R^7$ preserves the entire nonselective channel. At corresponding outcomes the Jacobian scalar in (2.7) cancels on normalization. In particular (2.25) is everywhere positive and the full normalized selective pure state for label $i$ is

$$
\Psi_{i,r}
=\frac{U_{T_6}\left[\psi_{W_i}(x)\prod_{j=0}^6k_1(r_j-L_jx)\right]}{\sqrt{p_i(r)}}.
\tag{2.28}
$$

This wavefunction, not just its position marginal, is identical at $r$ and at the relabelled record $s=\mathcal F(r)$. The unused probe contributes the unchanged tensor factor $|k_1\rangle\langle k_1|$. Any auxiliary output retained in a chosen dilation can likewise be left untouched by the outcome relabelling; (2.27) changes only the classical outcome coordinates.

G, Proposition 5.3 directly supplies the initial-coordinate position posterior of (2.28):

$$
B_{\rm pos}=(2I_{17}+L^TL)^{-1},\qquad
\mu_{i,r}=m_i+B_{\rm pos}L^T(r-Lm_i),
\tag{2.29}
$$

followed by the actual $U_{T_6}$ on the quantum branch. In particular the corresponding final position covariance is $T_6B_{\rm pos}T_6^T$. Formula (2.28) retains the rest of the state as well. If the label is unobserved, its selective system state is the same Bayes mixture on both sides of (2.27), with weights $p_i(r)/\sum_h p_h(r)$; these weights are an identity for the supplied ensemble, not access to a label port.

Since (1.17) recovers every $R_j$, any already supplied lawful continuation controlled by the full record can be expressed in the new coordinates by substituting $r=\mathcal F^{-1}(s)$ and applying the same system action to the same successor. In particular an available original seventh-clock $J$ or $M$ instrument keeps its full conditional and nonselective response after this substitution. This conditional correspondence does not install a new controller or change the admissible action family. Independence of $N$ from the label and first pair in (2.4) gives no independence of $N$ from (2.28), and licenses no erasure for all later quantum continuations. Thus the complete relevant outputs, successors and records are retained.

Finally the first two coordinates of (2.4) are exactly C, Definition 13.1. C, Theorem 13.3 may be applied directly, with the present $q,b$, to the optional later common Borel rule

$$
Q_{q,b}(u,v)=\mathbf1\left\{v>
\frac{\ln4-q^2/2+\ln\cosh(qu)+b^2/2}{b}\right\}.
\tag{2.30}
$$

Its singleton Bayes gain is the already defined $B(q,b)>0$. The nuisance factor in (2.4) cancels in the posterior likelihood ratio. This decision application introduces neither a new classifier nor a claim that (2.30) is an installed finite-precision action or that the full retained record has been replaced by that bit. $\square$

## 3. Resource and continuation domains

**Definition 3.1 (Resources of this run).** Distinguish the source execution, its affine representation, its retained accessible record, and an optional later decision or action. The source execution in Theorem 2.1 uses one supplied seventeen-mode preparation, eight probes supplied in advance, seven probes used, six original controls (two $J$ and four $M$), seven couplings, and seven meter acquisitions. The eighth probe is unused and retained. Thus twenty-five quantum modes are supplied, and twenty-four take part in the specified execution. The acquired and retained real-record dimension is seven in either coordinate system, of which five coordinates have the nuisance law in (2.4). No second physical measurement is defined by applying the notation $Y=\mathcal F(R)$.

For the reference oscillator of G, Theorem 2.2, the initial system energy at label $i$ is $17/2+\|m_i\|^2/2$. Each supplied $\sigma=1$ probe has initial oscillator energy $(1+1/4)/2=5/8$. These are initial expectations for the specified oscillator, not a total execution cost. Preparation synthesis, public-constant acquisition, exact or approximate arithmetic for (1.17), controller workspace, record storage, backing and lifetime, later comparison, call/return operations and authority to perform later actions have no prices or implementations supplied here. The finite control word does not assert finite-bit storage of seven exact reals. If an affine-record implementation or later readout is required as a paid operation, it is an additional task with its own supplied resources.

The constants in (1.3), (1.12)–(1.17) depend on the public ensemble and the fixed apparatus, not on unacquired information about the label of a run. Their exact mathematical selection is proved; neither a bound on the first successful dyadic level nor a root-computation or precision bound is part of this resource definition. In particular the theorem makes no shortest-word, minimum-mode, minimum-probe or total-cost optimum assertion.

**Definition 3.2 (The attained interface and the remaining recovery problem).** The attained relation is the common actual instrument law and CP-output correspondence (2.3)–(2.7). Its source is the explicitly available Gaussian preparation family, its time ordering is the original clocked six-action process, its observation boundary is the seven probe meters, and its retained accessible data are their complete real record. The preparation-to-record-law implication is thereby instantiated by actual $W_i\in K_J$, rather than left conditional on the existence of matching means.

The Gaussian program is a distinct declared model from an unknown original carrier. It does not extract an unknown seed, identify a world from a specimen, or provide a paid callable-memory service. The native acquisition and continued-use interfaces of [Native Clocked Recovery and Order](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), [Native Paid View Conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), [Transport Memory Completion, §57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), and the [Native Callable Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md) retain their own actual tree/tape inputs, installed controls, backing, conversion, retention and call/return hypotheses. None is identified with the present Gaussian source by (1.17). Their supplied operational capabilities remain available within their respective domains; an adapter to those domains would require its own common-source and same-run proof.

The further common-relation objective requires independent meanings for space, time, boundary and memory, every asserted recovery direction between them, agreement of different recovery routes, compatibility with dynamics, lawful internal selection, and actual later callable use. None of these additional conclusions is defined merely by giving each view the complete record. Reduction of this apparatus to the proposed $\alpha/\beta$ generators is a separate unproved bridge. The fixed-$G_{gc}$, original-$Q$, parked-consumer and unchanged-initialization questions retain their original hypotheses and conclusions. Likewise G's positive-noise distinction between a population-law fibre and an exactly acquired deterministic history remains in force: (2.25) is an everywhere positive Gaussian density, not a postselected acquisition of $h(p,f(p))$.

The source-specific inference in Theorem 2.1 is the proved choice of complete preparations with the non-affine separation (2.20), the exact source selection (1.12)–(1.16), and their complete acquired-law attainment. The shared Kraus, Gaussian observation and decision results are reused as cited. In particular it does not reproduce the generic source/Acquire/whitening/readout chain as a new theorem of Gaussian geometry. This is a repository-derived application; no worldwide novelty or priority assertion is included.

The distinct source statements relevant to this inference have the following domains. [C, §15 at its extended version](https://github.com/the-omega-institute/trureturing/blob/3e17c0be3887f202810b4825e90c5bdba14474d4/docs/develop/theory/FIB_ATOM_CATEGORICAL_DECISION_BLINDNESS.md) concerns exact rational Boolean factor representations of finite positive-noise laws; those abstract finite factors do not give the Gaussian preparations or continuous acquired record in (2.25). [Strict Real VIII, §§10–20](https://github.com/the-omega-institute/trureturing/blob/3e17c0be3887f202810b4825e90c5bdba14474d4/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VIII.md) concerns an evaluated lower-face target near $p=8.947$, its entire-child $M$ exclusion and strict-unit-$j$ incidence conditions. That target is outside $[10,34]$; those statements neither select the varying sources above nor exclude their Gaussian record laws. [Boundary Geometry Continuation VIII, Theorem 240.3](https://github.com/the-omega-institute/trureturing/blob/4b07e9740ce998ee7cf899f4b1897bf61a3bf713/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VIII.md) excludes a common exact heralded conversion of two specified full fermionic Gibbs preparations at $t=3-2\sqrt2$. Its explicit predecessor is [Continuation VII, §239 at its historical binding](https://github.com/the-omega-institute/trureturing/blob/b92a26f3f99eb2cdad322dbd60d0e95eadf7b024/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VII.md), with its different $t=1/10$ and separable-map domain. Those full-output conversion requirements are distinct from the invertible outcome relabelling of an unchanged Gaussian instrument in (2.27). Neither supplies nor contradicts the actual-source selection inference of Theorem 2.1.

## 追加锚（本行以下为增补区）
