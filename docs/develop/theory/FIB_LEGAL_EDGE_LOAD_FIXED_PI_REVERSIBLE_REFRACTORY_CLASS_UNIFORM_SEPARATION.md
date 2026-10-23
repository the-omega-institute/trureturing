# FIB harmonic-edge load: uniform separation of the fixed-pi reversible refractory class

## 1. Original words, actual laws and finite producers

**Definition 1.1 (Complete open-path objective).** For integers $n\ge1$, let

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\}.
$$

The graph $\Gamma_n$ contains every vertex of $B_n$ and every legal
Hamming-one edge. To test an insertion, take $w_0=w_{n+1}=0$; the first and
last coordinates are not joined. On the entire probability simplex put

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\qquad
\Phi_n(\mu)=\sum_{\{w,v\}\in E(\Gamma_n)}h(\mu_w,\mu_v),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
$$

Zero masses do not remove vertices or edges. All-zero words, legal endpoint
ones and all legal edges across any grouping seam remain in this domain.

**Convention 1.2 (One stationary law and its exterior).** Let $P$ be a
normalized two-sided stationary law on

$$
X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

Write $[w]$ for an interval cylinder, $P_n$ for its actual length-$n$
marginal, and $X_i$ for the coordinate bits. Stationarity makes cylinder
probabilities independent of the interval's starting point. Define

$$
\begin{aligned}
\mathcal E_0&=\sigma(X_j:j\ne0),&
q_P&=\mathbb E_P[X_0\mid\mathcal E_0],\\
\mathcal F_r&=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r),&
D_r(P)&=\mathbb E_P[(X_0-\mathbb E_P[X_0\mid\mathcal F_r])^2].
\end{aligned}
$$

[Stationary, §2][P1] and [Growth, Theorem 5.2][P6] supply, without support,
memory or mixing assumptions,

$$
\begin{aligned}
d(P)&:=\lim_{n\to\infty}\Phi_n(P_n)/n
=\mathbb E_P[(X_0-q_P)^2]=\inf_{r\ge1}D_r(P)\le c_\star,\\
D_r(P)&=\sum_{\substack{u,v\in B_r\\u_r=v_1=0}}
h(P([u0v]),P([u1v])),\\
c_\star&=\lim_{n\to\infty}\kappa_n/n,\qquad
nc_\star\le\kappa_n\le(n+1)c_\star.
\end{aligned}
\tag{1.1}
$$

A neighboring one forces the center to zero. A zero-total fiber contributes
zero, irrespective of its chosen conditional-probability version. The
open-word density identity keeps endpoint contributions and also holds
along $n=3N$. Every expectation in a model calculation below belongs to
that model's single actual law.

**Definition 1.3 (Unrestricted finite producer domain).** For each integer
$N\ge1$, retain [Universal, Definition 4.1][P4] in its entire domain:

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
\ M_0,M_1\ge0,\ A=M_0+M_1,\ A\mathbf1=\mathbf1,
\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.2}
$$

Here $\lambda$ is an $N$-component row, the matrices are $N\times N$, and
all entries are exact real numbers. Structural zeros, zero stationary
masses, reducibility and periodicity are allowed. With
$M_w=M_{w_1}\cdots M_{w_n}$, [Universal, Proposition 4.2][P4] constructs
one coherent stationary joint law whose visible cylinders are
$P_\theta([w])=\lambda M_w\mathbf1$.

## 2. Complete reversible class and a uniform actual-risk certificate

**Definition 2.1 (Fixed stationary row and unchanged constructor).** Fix

$$
\pi=(7/10,3/20,3/20),\qquad R=\{2,3\}.
$$

Let $\mathcal K$ contain every entrywise nonnegative stochastic
$3\times3$ matrix $K$ satisfying
$\pi_iK_{ij}=\pi_jK_{ji}$ for all $i,j$. No entry is fixed. In particular
$K_{13}$ is unrestricted. There is no additional positivity, rank,
positive-semidefiniteness, irreducibility, aperiodicity or mixing condition.

Use the refractory constructor of [Slice, Definition 2.1][Slice]: let $J$
include coordinates $2,3$, $E=JJ^{\mathsf T}$ and $D=I_3-E$. In state
order $(1,2,3,2',3')$ put

$$
M_0(K)=\begin{pmatrix}DK&0_{3\times2}\\J^{\mathsf T}K&0_{2\times2}\end{pmatrix},\qquad
M_1=\begin{pmatrix}0_{3\times3}&J\\0_{2\times3}&0_{2\times2}\end{pmatrix},
$$

$$
b=\pi(R)=3/10,\qquad
\lambda=\frac{(\pi,\pi J)}{1+b}
=(7/13,3/26,3/26,3/26,3/26),\qquad
\theta_K=(\lambda,M_0(K),M_1).
\tag{2.1}
$$

Free state $1$ emits zero and advances by $K$. A free state in $R$ emits
one into its own tail; a tail emits zero and advances by $K$. Time is the
integer emitted-bit clock, with stationary row $\lambda$.

**Theorem 2.2 (Entire-class separation).** Every $K\in\mathcal K$ gives
$\theta_K\in\Theta_5$ and one normalized two-sided stationary law $P_K$.
For every such $K$, including all feasible boundary cases,

$$
d(P_K)\le D_2(P_K)\le B:=\frac{5980689}{41600000}
<W:=\frac1{38}\left(\frac{1372}{543}+\frac{588}{247}+\frac{63}{113}\right)
\le c_\star.
\tag{2.2}
$$

Here $W$ is the actual full-exterior risk of the supplied TwoStep law.
In particular,

$$
W-d(P_K)\ge W-B>\frac{32669}{790400000}>0.
\tag{2.3}
$$

Proof. Put $\alpha=14/3$, $x=K_{12}$, $y=K_{13}$ and $\tau=K_{23}$.
Detailed balance and row sums give exactly

$$
K(x,y,\tau)=\begin{pmatrix}
1-x-y&x&y\\
\alpha x&1-\alpha x-\tau&\tau\\
\alpha y&\tau&1-\alpha y-\tau
\end{pmatrix},
$$

$$
0\le x,y\le3/14,\qquad
0\le\tau\le\min\{1-\alpha x,1-\alpha y\}.
\tag{2.4}
$$

These inequalities are necessary from the second and third rows. They
imply $x+y\le3/7$, so the first diagonal is automatically at least $4/7$.
Conversely, every triple in (2.4) makes all entries nonnegative, all rows
stochastic and all detailed-balance identities valid. Thus (2.4) is the
complete three-parameter polytope, with no missing face or corner.
Detailed balance gives $\pi K=\pi$.

For $A=M_0(K)+M_1$, direct block multiplication gives

$$
A\mathbf1=\mathbf1,\qquad M_1^2=0,\qquad
\lambda M_0(K)=\frac{(\pi K,0)}{1+b},\qquad
\lambda M_1=\frac{(0,\pi J)}{1+b}.
\tag{2.5}
$$

Hence $\lambda A=\lambda$, $\lambda\mathbf1=1$ and all conditions of
(1.2) hold. Every row of $K$ occurs in $M_0(K)$, so the constructor does
not conceal a negative entry. The joint-law correspondence cited in
Definition 1.3 applies on the entire polytope. Explicitly, its interval
probabilities are

$$
J_{\theta_K}(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=w_a,\ldots,X_b=w_b)
=\lambda_{h_a}\prod_{i=a}^b M_{w_i}(h_i,h_{i+1}).
\tag{2.6}
$$

Right and left marginalization use $A\mathbf1=\mathbf1$ and
$\lambda A=\lambda$, respectively; the total mass is one. Summing hidden
paths gives $P_K([w])=\lambda M_w\mathbf1$. Every adjacent $11$ has zero
mass, and a countable union gives support on $X$. Also
$P_K([1])=b/(1+b)=3/13$. Every legal endpoint, all-zero word and seam has
its actual cylinder mass, including possible zero masses. A seam $uv$
uses $\lambda M_uM_v\mathbf1$.

To compute the free radius-two fibers, set

$$
\rho=x+y,\quad a=1-\rho,\quad \eta=7/13,\quad m=3/7,\quad
u=(x,y),\quad q=\alpha u^{\mathsf T},\quad C=K_{RR},\quad
\omega=(3/14,3/14),\quad z=uq=\alpha(x^2+y^2).
\tag{2.7}
$$

For exterior bits $i,j\in\{0,1\}$, let
$s_{ij}=P_K([i000j])$ and $t_{ij}=P_K([i010j])$. Direct word multiplication
and stationary extension give the following table throughout (2.4):

| Context $ij$ | $s_{ij}/\eta$ | $t_{ij}/\eta$ |
| --- | --- | --- |
| $00$ | $a^3$ | $z$ |
| $01$ | $a^2\rho$ | $\rho-z$ |
| $10$ | $a^2\rho$ | $\rho-z$ |
| $11$ | $a\rho^2$ | $m-2\rho+z$ |

Here is the unrestricted-entry derivation of this extension of
[Slice, Lemma 3.1][Slice]. In the five-state order,

$$
M_0^2=f w,\qquad f=(a,0,0,q_2,q_3)^{\mathsf T},\qquad
w=(a,x,y,0,0),\qquad
\lambda f=\eta,\quad w\mathbf1=1,\quad wM_0=aw.
$$

Therefore $P_K([0^\ell])=\eta a^{\ell-2}$ for $\ell\ge2$.
Subtracting actual left and right extensions gives

$$
\begin{aligned}
s_{00}&=P_K([0^5]),\\
s_{01}=s_{10}&=P_K([0^4])-P_K([0^5]),\\
s_{11}&=P_K([0^3])-2P_K([0^4])+P_K([0^5]),
\end{aligned}
$$

which proves the zero-center column. For the one-center column, $C$ is
symmetric, $C\mathbf1=\mathbf1-q$ and $\omega_jq_j=u_j$.
The actual event cylinders satisfy

$$
\begin{aligned}
P_K([1])&=\eta m,\\
P_K([101])&=\eta\omega C\mathbf1=\eta(m-\rho),\\
P_K([10101])&=\eta\omega C^2\mathbf1
=\eta\sum_{j\in R}\omega_j(1-q_j)^2=\eta(m-2\rho+z).
\end{aligned}
\tag{2.8}
$$

The quadratic identity uses symmetry of $C$ and the equal components of
$\omega$. A center one forces both its neighbors zero. Inclusion-exclusion
at distance two now gives

$$
t_{11}=P_K([10101]),\quad
t_{01}=t_{10}=P_K([101])-P_K([10101]),\quad
t_{00}=P_K([1])-2P_K([101])+P_K([10101]).
$$

All four pairs are masses from the same law. All other radius-two exterior
atoms force the center zero. Thus (1.1) gives
$D_2(P_K)=\sum_{i,j}h(s_{ij},t_{ij})$. The table is independent of $\tau$;
this does not assert that the full visible law is independent of $\tau$.

The new return-mass control is the unrestricted row-moment inequality

$$
0\le z=\sum_{j\in R}\omega_jq_j^2
\le\sum_{j\in R}\omega_jq_j=\rho,
\qquad
\rho-z=uC\mathbf1\ge0.
\tag{2.9}
$$

Indeed, (2.4) gives $0\le q_j\le1$, so $q_j^2\le q_j$ termwise. It also
gives $m-2\rho+z=\sum_j\omega_j(1-q_j)^2\ge0$. No division or strict
positivity is used. The fixed-entry substitution for $z$ in the slice is
replaced by (2.9) on every feasible split of $\rho$.

Reuse [Slice, Theorem 3.2][Slice]'s exterior-measurable predictor

$$
F=\{X_{-1}=X_1=0\},\qquad
g=\mathbf1_F\left(\frac7{20}+\frac{X_{-2}+X_2}{25}\right).
$$

Conditional expectation is the least-squares projection on the same
$P_K$. Consequently

$$
\mathbb E_{P_K}(X_0-g)^2
=d(P_K)+\mathbb E_{P_K}(q_{P_K}-g)^2,
\qquad d(P_K)\le D_2(P_K)\le\mathbb E_{P_K}(X_0-g)^2.
\tag{2.10}
$$

On forced fibers both $X_0$ and $g$ are zero. Put $c=7/20$, $t=1/25$.
The four free pairs give the exact loss $\eta H(\rho,z)$, where

$$
\begin{aligned}
H(\rho,z)
&=a^3c^2+2a^2\rho(c+t)^2+a\rho^2(c+2t)^2\\
&\quad+z(1-c)^2+2(\rho-z)(1-c-t)^2
 +(m-2\rho+z)(1-c-2t)^2\\
&=\frac{9161}{35000}+\frac{311}{10000}\rho
 -\frac7{125}\rho^2-\frac2{625}\rho^3+\frac2{625}z.
\end{aligned}
\tag{2.11}
$$

For the expansion, the zero-center part is
$(1-\rho)(c^2+4ct\rho+2t^2\rho+2t^2\rho^2)$, and the one-center part is
$m(1-c-2t)^2+[4(1-c)t-6t^2]\rho+2t^2z$.
The coefficient of $z$ is positive, so (2.9) yields

$$
\begin{aligned}
H(\rho,z)
&\le\frac{9161}{35000}+\frac{343}{10000}\rho
 -\frac7{125}\rho^2-\frac2{625}\rho^3\\
&=\frac{5980689}{22400000}
 -\frac7{125}\left(\rho-\frac{343}{1120}\right)^2
 -\frac2{625}\rho^3
\le\frac{5980689}{22400000}.
\end{aligned}
\tag{2.12}
$$

The square-completion constant follows from
$(343/10000)^2/[4(7/125)]=117649/22400000$ and
$9161\cdot640+117649=5980689$. Since $\rho\ge0$, both discarded terms are
nonnegative. Multiplication by $\eta=7/13$ and (2.10) prove the bound $B$.

For the actual comparator, [TwoStep, Definition 2.1 and Proposition
2.2][TwoStep] give a stationary legal-pair law $Q$ with states $(00,01,10)$,

$$
T=\begin{pmatrix}7/10&3/10&0\\0&0&1\\2/3&1/3&0\end{pmatrix},\qquad
\xi=(10/19,9/38,9/38).
$$

Its four free five-bit mass pairs, in the same context order, are
$(343,200),(147,100),(147,100),(63,50)$, each divided by $1900$.
[TwoStep, Proposition 2.4][TwoStep] proves that flipping a free center in
any window of radius at least two changes exactly three transition
factors. Its odds are respectively $200/343,100/147,100/147,50/63$,
independent of the farther completion. The finite-exterior posteriors
therefore remain the same as the windows increase; conditional projection
convergence identifies them with the full-exterior posterior. Their
harmonic sum is the exact $W=d(Q)$ in (2.2), also obtained by the supplied
full-word grouping and endpoint remainder in [TwoStep, Theorem 3.1][TwoStep].
Thus (1.1) gives $W\le c_\star$, and the growth identity gives
$\kappa_n\ge nW$ for every $n\ge1$.

Use this exact actual risk for the comparison. The positive integer
differences

$$
1372\cdot10000-25267\cdot543=19,\quad
588\cdot10000-23805\cdot247=165,\quad
63\cdot10000-5575\cdot113=25
$$

imply

$$
W>A_0:=\frac{54647}{380000},\qquad
A_0-B=\frac{54647\cdot2080-5980689\cdot19}{790400000}
=\frac{32669}{790400000}>0.
\tag{2.13}
$$

This proves (2.2)–(2.3). The looser supplied floor
$23/160+1/76000$ alone would not prove this particular certificate:
$B-(23/160+1/76000)=2691/790400000>0$.

All arguments apply to the closed domain (2.4), including $K=I_3$.
For that member, the emitted chain has an all-zero closed component and
two closed alternating period-two components. The proof evaluates their
actual stationary mixture. It also retains every other reducible,
periodic or rank-degenerate member. The specified $\lambda$ is positive
as a consequence of fixed $\pi$; zero-mass states can be added in any
same-law representation without changing $d$. The predictor divides by
no cylinder mass, and the harmonic formula uses $h(0,0)=0$.
Neither $d=D_2$ for this class nor optimality of $g$, $B$ or $W$ is asserted.
$\square$

The fixed-entry slice $y=3/20$ retains its stronger supplied bound
$328609787/2288000000$ from [Slice, Theorem 3.2][Slice], including its
complete epsilon curve. The new coverage in (2.2) is the entire
three-parameter class (2.4), using the consumed unrestricted inequality
(2.9).

**Theorem 2.3 (One restricted finite separation pair).** Over precisely
the class in Definition 2.1,

$$
\max_{K\in\mathcal K}D_2(P_K)\le B
<\frac{4000}{4001}A_0<\frac{4000}{4001}W
\le\frac{\kappa_{4000}}{4001}.
\tag{2.14}
$$

Proof. The polytope (2.4) is compact. Cylinder probabilities are polynomials
in its parameters, and $h$ is continuous at zero-total fibers, so this
restricted maximum exists. The first strict comparison is equivalent to

$$
4000\cdot32669-5980689\cdot19=17042909>0.
$$

The remaining inequalities follow from (2.13) and $\kappa_n\ge nW$.
Thus $(r,m)=(2,4000)$ is a sufficient finite certificate for this
constructor class. This maximum is not $U_{5,2}$ over all $\Theta_5$;
neither radius nor length is asserted minimal. $\square$

## 3. A distinct nonrenewal law with infinite visible memory

**Proposition 3.1 (Actual coverage outside the fixed-entry slice).** The
member

$$
K_\dagger=\begin{pmatrix}
7/10&1/10&1/5\\
7/15&1/2&1/30\\
14/15&1/30&1/30
\end{pmatrix}
\tag{3.1}
$$

gives a full-support visible law $P_\dagger$ outside the entire visible-law
set of the fixed-entry slice, including its relabeling of states $2,3$.
It fails event independence, has no finite visible Markov order, and
nevertheless satisfies the uniform actual-risk bound (2.2).

Proof. It is the point $(x,y,\tau)=(1/10,1/5,1/30)$ of (2.4).
All base entries are positive; the normalized constructor is unchanged.
Every legal word has a positive hidden path: use free state $3$ for each
one and its tail for the following zero, and free state $1$ for remaining
zeros. The positive initial masses and base transitions also cover an
initial zero, a final one and every all-zero word.

Here $\rho=3/10$ and $z=7/30$. The observable cylinder
$P_K([000])=\eta(1-\rho)$ determines $\rho$. On the old slice
$y=3/20$, the same $\rho$ forces $x=3/20$ and $z=21/100$.
But $P_K([00100])=\eta z$, so the two laws differ. Swapping the equal-mass
states leaves $\rho,z$ unchanged and gives the same slice comparison.
This distinguishes actual visible laws, beyond merely distinguishing
parameter presentations.

For [Renewal, Definition 5.1][P7]'s aligned event residual, (2.8) gives

$$
\begin{aligned}
\Gamma_{10,01}(P_K)
&:=P_K([10101])P_K([1])-P_K([101])^2\\
&=\eta^2(mz-\rho^2)=\eta^2(x-y)^2.
\end{aligned}
$$

For (3.1) it is $49/16900>0$. Thus $P_\dagger$ is outside the
event-independent renewal family and its weak closure identified in
[Renewal, Theorems 5.2 and 6.1][P7]. In this presentation $M_1$ has rank
two. The lower two rows of $M_0M_1$ contain

$$
C=\begin{pmatrix}1/2&1/30\\1/30&1/30\end{pmatrix},\qquad
\det C=7/450>0,
$$

so $M_0M_1$ also has rank two. The two rank-one reset conditions of
[Renewal, Theorem 8.3][P7] do not hold in this presentation.

For visible memory, define $A_n=uC^n\mathbf1$ for $n\ge0$ and
$H_n=00(10)^n$ for $n\ge1$. Direct products from (2.1) give

$$
P_\dagger([H_n])=\eta A_{n-1},\qquad
P_\dagger([H_n1])=\eta A_n,
\qquad
P_\dagger(X_0=1\mid X_{-|H_n|}\cdots X_{-1}=H_n)
=\frac{A_n}{A_{n-1}}.
\tag{3.2}
$$

Indeed, after $00$ the unnormalized hidden row is $\eta w$. The first
$10$ uses its $R$ row $u$; each further $10$ retains the $R$ row by
multiplication with $C$. A final zero has total continuation mass one;
an appended one selects the $R$ coordinates. This proves both products
with their stated indices.

The symmetric matrix $C$ has distinct eigenvalues

$$
\ell_\pm=\frac4{15}\pm\frac{\sqrt2}{6},\qquad
0<\ell_-<\ell_+<1.
$$

Their product is $7/450$ and their sum is $8/15$, which verify the stated
positive bounds. The unequal row sums $8/15$ and $1/15$ mean that
$\mathbf1$ is not an eigenvector; its orthogonal projections $v_\pm$ onto
both eigenspaces are nonzero. Since
$u=(3/14)\mathbf1^{\mathsf T}(I-C)$, spectral decomposition gives

$$
A_n=b_+\ell_+^n+b_-\ell_-^n,\qquad
b_\pm=(3/14)(1-\ell_\pm)\|v_\pm\|^2>0.
$$

For every $n\ge1$,

$$
A_{n+1}A_{n-1}-A_n^2
=b_+b_-(\ell_+\ell_-)^{n-1}(\ell_+-\ell_-)^2>0.
\tag{3.3}
$$

Thus the next-one probabilities in (3.2) strictly increase with $n$.
For any proposed finite visible order $r$, all sufficiently long $H_n$
have the same last $r$ bits. The tower property for that order would make
all their positive-mass next-one probabilities equal to the same suffix
row, contradicting (3.3). Order zero is excluded as well by positive
one-bit mass and the forbidden $11$ cylinder. Hence the law has infinite
visible memory. The eigenvalue properties used for this example are not
conditions on $\mathcal K$. Finally apply Theorem 2.2. These facts give
coverage evidence without a claim of minimal hidden dimension. $\square$

## 4. The arbitrary-finite attainment problem remains open

**Open Problem 4.1 (Complete original quantifiers).** For the unchanged
domains (1.2), put

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
$$

Does some finite $N$ and exact $\theta\in\Theta_N$ satisfy
$d(P_\theta)=c_\star$, or does every finite $N$ satisfy $C_N<c_\star$?
[Universal, Theorems 3.1 and 6.2][P4] show that every attainer has positive
legal cylinders, that $C_N$ is attained on the complete compact domain,
and that the second alternative is equivalent to

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\kappa_m/(m+1).
\tag{4.1}
$$

Theorem 2.2 excludes every law representable by Definition 2.1, and any
other admissible representation of such a law. Its image is a restricted
subset of $\Theta_5$, and (2.14) is only a certificate on that subset.
The proof relies on fixed $\pi$, reversibility and the exact refractory
constructor, notably $M_0^2=fw$ and the return-mass correspondence (2.7).
General finite producers need not admit those identities. The theorem
does not supply (4.1) or an exact finite attainer. Every structural zero,
zero stationary mass, reducible and periodic parameter remains in (4.1).

The stationary and ergodic attainment results of [Stationary][P1] and
[Ergodic, Theorem 2.1][P0] remain existence results without a finite
hidden representation. [Nonattainment, Theorem 1.5][P2] excludes positive
finite visible-order laws; Proposition 3.1 does not meet that memory
hypothesis. [Completeness, Theorem 1.4][P3] and [Universal, Corollary
7.3][P4] retain $\sup_N C_N=c_\star$, which does not decide finite
attainment. Finite-volume positivity and uniqueness in [Optimizer,
Theorem 3.1][P5] do not decide it either.

[Renewal, §§7–9][P7] excludes event-independent laws, the stated rank-one
reset representations and effective state count $N_+\le3$. General
nonreset producers with $N_+\ge4$ remain outside the whole-class
certificate here. The route of [Conditional Response, §§3–5][P8] still
needs a productive same-law witness for every hypothetical finite
attainer: a matrix null direction alone supplies neither nonzero total
response nor a strict finite certificate. A finite block response is
not identified with that total response. No universal productivity
statement follows from (2.14).

## 5. Mathematical attribution and scope

**Convention 5.1 (Suppliers and the new deduction).** The objective and
growth identities belong to [Growth][P6], and the actual exterior-risk
identity to [Stationary][P1]. The full producer correspondence and
all-$N$ separation equivalence belong to [Universal][P4]. The constructor,
four-fiber mechanism and predictor belong to [Slice][Slice]; its
fixed-entry polynomial $z=(14/3)\rho^2-(7/5)\rho+21/100$ applies on
$y=3/20$. The unrestricted moment inequality (2.9), consumed by
(2.11)–(2.13), gives the `repo-derived` whole-class conclusion. The
distinct actual-law and infinite-memory witness in Proposition 3.1
locates additional coverage. The sufficient constant and finite length
are not asserted optimal.

[TwoStep, §§2–4][TwoStep] supplies the actual comparison law and its exact
risk. Its common full-word ratios justify equality with the full-exterior
value; a finite-window risk alone is an upper bound. Conditional
expectation as an $L^2$ projection and its increasing-field convergence
are established probability machinery, with the precise same-law proof
given in [Universal, Lemma 1.4][P4] and the reference to Gray §5.9 there.
The new proof uses no external scoring-rule, Gibbs or estimation theorem.
The literature attribution is confined to those stated mechanisms and
the supplied corpus; no claim of world priority follows.

The results are ordinary mathematical derivations. They determine neither
the exact function $K\mapsto d(P_K)$, a maximizing kernel, an exact
$c_\star$ nor an attainer. The five states count the specified producer
presentation, without a minimality or observer-resource assertion.
No acquisition efficiency, universal renewal $1/7$ ceiling or empirical
machine-learning benefit is a consequence claimed here.

[P0]: FIB_LEGAL_EDGE_LOAD_ERGODIC_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[P1]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[P2]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md
[P3]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_COMPLETENESS.md
[P4]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[P5]: FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md
[P6]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[P7]: FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md
[P8]: FIB_LEGAL_EDGE_LOAD_CONDITIONAL_NULL_RESPONSE_AND_FINITE_CERTIFICATE.md
[TwoStep]: FIB_LEGAL_EDGE_LOAD_TWO_STEP_BULK_SEPARATION.md
[Slice]: FIB_LEGAL_EDGE_LOAD_REVERSIBLE_FIVE_STATE_SLICE_UNIFORM_SEPARATION.md

## 追加锚（本行以下为增补区）
