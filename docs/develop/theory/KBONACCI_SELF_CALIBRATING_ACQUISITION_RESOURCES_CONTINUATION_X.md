# k-bonacci 自校准获取资源续卷 X：完整证书坐标与条件库存阈值

This volume continues
[Continuation IX, §§207–209](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md).
The statements are ordinary mathematical results. Write $x_+=\max(x,0)$;
empty sums are zero. Every weak inequality includes its equality case.

## 210. Complete-certificate coordinates and attained stock thresholds

**Definition 210.1 (Inherited full comparison and notation).** Use the
source and resource classes of 207.1, the full scores of 207.2 and the
single certificate of 207.3. Explicitly, the countable labeled source is

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
 \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\qquad
N(r,g)=1+F_rg,\qquad q_i=\mathbf1_{p_i\mid N(r,g)}.
$$

Here $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$, the $p_i$ are increasing
primes, and $n(x)=\min\{i:q_i(x)=0\}$. The full Borel tape carrier is
$\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, with every block a
copy of $(0,1)$. Its unchanged consumer returns unknown on $B_j$ and
proposes $j$ on $P_j$; the original nonatomic targets remain those of
Acquisition Resources 73.1. The marks $\theta_j=(B_1,1/(j+2))$,
$j\ge0$, support the separately selected laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_j\longrightarrow0.
$$

The resources are exactly Acquisition Resources 90.1: zero advice,
one source-independent common seed, actual sourcewise almost-sure
finite handoff, arbitrary addresses and full-carrier outputs.
$N$ preselects and obtains its schedule's replies. $O$ preselects an
increasing schedule and stops at its first queried zero or exhaustion.
At most two actual requests are allowed, including repeated or ignored
requests. TV is uniform over all actual sources and all Borel events.

For $L\ge3$, retain every $w\in\{0,1\}^L$, all labels $0,\ldots,L$,
and $\Omega_n=\{w:n(w)=n\}$. At every zero word, independent
coefficients $A_w,C_w,P_w\ge0$ score a label by

$$
g_V(w,\ell)=A_w\mathbf1_{\ell=0}+C_w\mathbf1_{\ell=n(w)}
                    +P_w\mathbf1_{\ell\in\{0,n(w)\}};
\qquad g_V(1^L,\ell)=T\mathbf1_{\ell=0},\quad T\ge0.
\tag{210.1}
$$

The independent demands are $1-b_n-e,b_n-e,1-e$, respectively,
and $1-e$ at $1^L$. Negative singleton demands, multiple-zero words
and zero-scored event rows remain. $B_N,B_O$ maximize the sum of
all-label cell maxima over every empty, singleton and pair schedule;
pair cells are $00,01,10,11$ for $N$, and $0,10,11$ for $O$.
For $R=(1,2;1,2,0)$ in stopped-cell order set

$$
\begin{aligned}
W_V&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_C(V)&=B_C(V)-W_V\ge0\quad(C=N,O),\\
Q(V)&=(\beta,K),\quad \beta_n=\sum_{\Omega_n}(C_w-A_w),\quad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
\tag{210.2}
$$

Earlier unqueried labels are legal. The restricted-catalog equality
194.2 and the surviving-label hypothesis in 197.3 are unchanged:
on $0100$, the full $N$ table $(3,4;1,0,0,0)$ correctly outputs 1.
Changing that output to zero loses its correct row.

The input family, when explicitly invoked, has $A=0$, arbitrary $C$,
and $P$ supported on $\Omega_1\cup\Omega_2$, including early $00$.
Write $\gamma_n=\sum_{\Omega_n}C$, $E=\gamma_1+\gamma_2$,
$G=\sum_{n\ge3}\gamma_n$, $S=\sum P$, $B=S+T$; then
$W=E+B$, $Q=(\gamma,G+W)$. The actual late measure is
$\nu(x)=P_{00x}+P_{01x}+P_{10x}$. Use
$m_i=\nu\{x_i=0\}$ and $D_{ij}=\nu\{x_i=1,x_j=0\}$ for $i<j$.
These are measures of proof weights, not laws on sources or acquisition
probabilities. Write $w(Z)$ for the full word with zero set $Z$.
Unspecified coefficients are zero and coincident coefficients add.

For signed $q=(\beta,K)$, put $\alpha=(1,1,0,\ldots,0)$ and

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\ b_2=b_3,\\
 &(L+1)e\le\sum_{j=3}^Lb_j,\quad
 b_1+\sum_{j=3}^Lb_j-(L+1)e\le1\},\\
F_q(b,e)&=\sum_j\beta_j(b_j-\alpha_j)-Ke,\qquad
\sigma_H(q)=\max_{H_L}F_q.
\end{aligned}
\tag{210.3}
$$

The vertices $o,p,u_k,v_k$ are exactly those of 198.5 and 207.3.
A complete certificate for $q$ is one $V\ge0$, $\theta\in[0,1]$ with

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(q-Q(V))\le\theta.
\tag{210.4}
$$

Its set of quotients is $E_N$. In particular $\theta=1$ permits a
nonzero zero-cost $V$. Let $r=z_R=d(\alpha,0)$, $h=d-r$,
$G_C=(z_D-r)_D$, and
$H_N=\{b\in H_L:\exists\lambda\ge0,\ G_N\lambda\ge h(b)\}$.
For the same complete feasible $\lambda$ of mass $M$, the existing
weak-duality inequality is
$F_q\le M\Delta_N(V)+\theta\le\max(1,M)$.
No cell or component receives a second allowance.

The full hull and alternative belong to
[198.5 and 199.3–199.6](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md).
The latter uses the finite Farkas alternative of Volker Kaibel,
[*Basic Polyhedral Theory*, Theorem 1(ii)](https://arxiv.org/pdf/1001.2161v1).
The full-table comparison here retains its resource constraints;
David Blackwell's
[*Comparison of Experiments*, §§2 and 5](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf)
supplies the classical attainable-risk and common-randomization framework,
not a conversion between these two constrained catalogs.

### 210.1 A four-late inequality and a specified relaxation obstruction

**Theorem 210.2 (A complete four-late support inequality).** For every
$L\ge6$, every full score $V\ge0$, and $C=N,O$,

$$
-\beta_1-2\beta_2+2\sum_{j=3}^6\beta_j
       +\sum_{j=7}^L\beta_j-K\le3\Delta_C(V).
\tag{210.5}
$$

In the input family this reads
$\sum_{j=3}^6\gamma_j\le W+\gamma_1+2\gamma_2+3\Delta_C(V)$.

**Proof.** Set
$b^\dagger=(3/4,1/2,1/2,1/2,1/2,1/2,1/4,\ldots,1/4;1/4)$.
Its late sum is $(L+2)/4$; the lower hull inequality has slack $1/4$
and the upper one is equality. Thus $b^\dagger\in H_L$.
Give $R$ probability $1/4$ and each of the following stopped tables
probability $1/8$:

$$
\begin{gathered}
(1,3;1,3,0),\quad(1,4;1,4,0),\quad
(2,3;0,3,0),\quad(2,4;0,4,0),\\
(3,5;0,5,6),\quad(4,5;0,5,6).
\end{gathered}
\tag{210.6}
$$

For its output probabilities the following bounds hold on every
word in each first-zero class. The last column is mass outside
$\{0,n\}$, not a replacement for the independent pair demand.

| First zero | Correct mass | Zero mass | Other mass |
| --- | --- | --- | --- |
| $1$ | $1/2$ | at least $1/4$ | at most $1/4$ |
| $2$ | $1/4$ | $1/2$ | $1/4$ |
| $3$ | $1/4$ | at least $1/2$ | at most $1/4$ |
| $4$ | $1/4$ | $5/8$ | $1/8$ |
| $5,6$ | $1/4$ | $3/4$ | $0$ |
| $n>6$ | $0$ | $3/4$ | $1/4$ |

At $1^L$ the zero mass is $3/4$. To check the only variable suffix
cases, at $n=1$ a wrong output from $(2,k;0,k,0)$ requires $w_k=0$,
whereas a nonzero output from $(k,5;0,5,6)$ requires $w_k=1$,
for $k=3,4$. Each pair therefore contributes at most one wrong eighth.
At $n=2$, exactly one table in each pair
$\{(1,k;1,k,0),(k,5;0,5,6)\}$ is wrong. At $n=3$, $w_4=0$
gives two wrong eighths and $w_4=1$ gives one. The remaining rows
follow from the fixed prefix and do not constrain any later bit.
These readings dominate all three event demands at $b^\dagger$.

Remove the anchor component. The six other tables give a conic
configuration $\lambda_0$ of mass $3/4$ with
$G_O\lambda_0\ge h(b^\dagger)$; copying the stopped first cell
gives the same inequality in $N$. Multiplication by $V$ gives

$$
F_{Q(V)}(b^\dagger)\le\tfrac34\Delta_C(V).
\tag{210.7}
$$

Four times its left side is (210.5). Substituting $K=G+W$ proves
the input specialization. For any complete certificate it also gives
$F_q(b^\dagger)\le3\Delta_N(V)/4+\theta\le1$, with arbitrary
signed residuals and all zero-cost cores included.

The normalized seven-table mixture itself is an actual stopped rule
for $a_1=3/4$, $a_2=\cdots=a_6=1/2$,
$a_n=2^{-(n-5)}$ for $n\ge7$, at closed cap $1/4$.
Partition one uniform seed into the displayed table probabilities
before replies; execute the selected increasing schedule and return
its mark. Every execution hands off after at most two actual requests.
The three-event readings give error $1/4$ at each low first zero.
For every actual $n>6$ the output is
$(3/4)\delta_{\theta_0}+(1/4)\delta_{\theta_6}$, whose error is
$\max(1/4,a_n)=1/4$, including $a_7=1/4$.
Acquiring the full preselected schedule gives its $N$ realization by
90.2 on the same seed. Thus this witness is feasible in both classes;
it is no separator. The constant auxiliary tail of $b^\dagger$ has
not replaced the actual vanishing tail. $\square$

**Proposition 210.3 (Failure of the critical-stock relaxation).**
Define $R_{\rm crit}$ on four active late coordinates $3,4,5,6$ as
the following conjunction, with $s=\mu-E-1>0$: one actual Boolean
pair measure, $S\ge4s$, $m_i\ge2s$, $D_{ij}\ge s$ for $i<j$,
$S\ge3s$, $T\ge\mu-1$, the basic-data bound $d_0\le1$ of
206.7, and $m_i+\gamma_j+\gamma_k\le W+1$ for
$3\le i<j<k\le6$. Here, writing $M_r$ for the sum of the $r$
largest late totals,

$$
\begin{aligned}
c_0&=\min((E+S)/2,S+\min(\gamma_1,\gamma_2)),\qquad
q_{\rm ch}=\max(\mu,M_2-T),\\
d_0&=\max(0,\mu-T,M_2-E-S,M_3-W,q_{\rm ch}-c_0).
\end{aligned}
$$

For every $s>2$ and $L\ge6$, there is an input-family score whose
data satisfy this conjunction but whose quotient is outside $E_N$.
It is not a unit-$O$ score, and no representative of its quotient is
unit-$O$.

**Proof.** Put $g=3s-1$, $\gamma_1=2s-2$, $\gamma_2=0$,
$\gamma_3=\cdots=\gamma_6=g$, and all later totals zero.
On subsets of $\{3,4,5,6\}$ put mass $2/3$ on every two-subset
and $s-1$ on every three-subset. Pad inactive bits with ones.
Counting subsets gives

$$
S=4s,\quad m_i=g,\quad D_{ij}=s+1/3,\qquad
(p_{00},p_{01},p_{10},p_{11})
 =(2s-4/3,s+1/3,s+1/3,2/3).
\tag{210.8}
$$

Split each pair atom equally onto early prefixes $01,10$.
Put $C_{w(\{1\})}=2s-2$, $C_{w(\{j\})}=g$ for $3\le j\le6$,
and $T=3s-2$. This defines a full nonnegative score with

$$
E=2s-2,\quad W=9s-4,\quad G=12s-4,\quad K=21s-8.
\tag{210.9}
$$

All weak atom and relaxation inequalities hold already for $s\ge1$.
In particular $g-E-1=s$, $c_0=g$, $q_{\rm ch}=g+1$;
the five entries of $d_0$ are $0,1,0,1,1$.
Every ordered triple reads $3g=W+1$. The actual-input guards and
triple mechanism are those of 208.2; their application here proves
only this explicitly listed conjunction.

For the quotient $q_s=(\gamma,21s-8)$, direct substitution yields

$$
F_{q_s}(b^\dagger)=(s+2)/4>1\quad(s>2).
\tag{210.10}
$$

The certificate consequence of (210.7) rules out every (210.4),
including signed residuals and nonzero zero cores. Conversely (210.7)
forces every nonnegative representative $V$ of this quotient to obey
$\Delta_O(V)\ge(s+2)/3>1$. The displayed representative has the
still larger lower reading $(3s-1)/2$ from $(1,3;1,3,0)$:
that table earns $E+g+S-g/2+T$, and subtracting $W$ gives $g/2$.
At $s=4$, $W=32$, $K=76$, $F_{q_s}(b^\dagger)=3/2$.
The strict exclusion is only for $s>2$; (210.10) proves neither
membership nor nonmembership at $s=2$.
$R_{\rm crit}$ does not mean the full old necessary hierarchy or
complete $O$ feasibility. Its failure therefore does not refute
unit-$O$ quotient containment or the original universal comparison.
$\square$

### 210.2 A necessary cylinder coordinate in every certificate

**Theorem 210.4 (The full-certificate $0010$ bound and its exact minimum).**
For $L\ge4$ set

$$
m(V)=\sum_{w_1w_2w_3w_4=0010}P_w,\qquad
b^*=(3/4,3/4,3/4,3/4,1/4,\ldots,1/4;1/4).
$$

For every full $V\ge0$,

$$
F_{Q(V)}(b^*)\le\Delta_O(V)+m(V)/4
                       \le\Delta_N(V)+m(V)/4.
\tag{210.11}
$$

Consequently every complete certificate for any signed $q$ satisfies
$m(V)\ge4\max(0,F_q(b^*)-1)$.
There are explicit scores $Y,Z$ below such that, for every real
$\tau\ge0$,

$$
\begin{aligned}
\Delta_N(Y+\tau Z)&=\Delta_O(Y+\tau Z)=1,\\
q_\tau=Q(Y+\tau Z)&=(0,1+\tau/2,4+2\tau,4+2\tau,0,\ldots;
                                      37/2+11\tau),\\
\min_{(V,\theta)\text{ satisfying }(210.4)\text{ for }q_\tau}m(V)
 &= (1+\tau)/2.
\end{aligned}
\tag{210.12}
$$

The minimum is attained by $V=(1+\tau)Z$, $\theta=1$.
The auxiliary point $b^*$ belongs to $H_L$ but not to $H_N$.

**Proof.** By 198.5, $b^*=(3/8)u_4+(5/8)v_4\in H_L$.
Average these four legal stopped tables with weights $1/4$:

$$
(1,2;1,2,4),\quad(1,3;1,3,0),\quad
(2,3;2,3,0),\quad(3,4;0,4,0).
\tag{210.13}
$$

Every first-zero class $n\le4$ has correct mass $1/2$.
For completeness the zero masses on all four-prefixes are

| Prefix | $0000$ | $0001$ | $0010$ | $0011$ | $0100$ | $0101$ | $0110$ | $0111$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Zero mass | $1/4$ | $1/4$ | $0$ | $1/4$ | $1/4$ | $1/4$ | $1/4$ | $1/2$ |

| Prefix | $1000$ | $1001$ | $1010$ | $1011$ | $1100$ | $1101$ | $1110$ | $1111$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Zero mass | $1/4$ | $1/4$ | $1/4$ | $1/2$ | $1/4$ | $1/4$ | $1/2$ | $3/4$ |

For $n\le4$ the three demands at $b^*$ are $(0,1/2,3/4)$;
for $n>4$ they are $(1/2,0,3/4)$. The positive-word demand is
$3/4$. Hence the averaged event vector dominates every demand except
the pair row on prefix $0010$, where its deficit is exactly $1/4$.
Suffixes never enter these tables, so this is an all-word statement
for every $L$. Multiplying by arbitrary independent $A,C,P,T$ gives
$W_V+F_{Q(V)}(b^*)\le B_O(V)+m(V)/4$, proving (210.11).
Adding the one residual reading at $b^*$ and using (210.4) proves
the certificate bound, without any restriction on the event support
of its $V$.

Here are the full nonzero atoms defining $Y,Z$. Each displayed word
is padded by $1^{L-4}$; blank entries mean zero. Both have $A=0$.

| Word | $P_Z$ | $C_Z$ | $P_Y$ | $C_Y$ |
| --- | --- | --- | --- | --- |
| $0010$ | $1/2$ | $0$ | $1$ | $0$ |
| $0100$ | $3/2$ | $0$ | $2$ | $0$ |
| $0110$ | $1/2$ | $0$ | $1/2$ | $0$ |
| $1000$ | $1$ | $0$ | $3/2$ | $0$ |
| $1001$ | $1/2$ | $0$ | $1/2$ | $0$ |
| $1010$ | $1/2$ | $1/2$ | $1/2$ | $1/2$ |
| $1011$ | $0$ | $0$ | $0$ | $1/2$ |
| $1100$ | $0$ | $2$ | $0$ | $7/2$ |
| $1101$ | $0$ | $0$ | $0$ | $1/2$ |
| $1110$ | $0$ | $2$ | $0$ | $4$ |
| $1^L$ | — | $T_Z=2$ | — | $T_Y=7/2$ |

Summing each label's atoms in each cell gives the following complete
$N$ maxima, in cell order $00,01,10,11$:

| Schedule | $Z$ maxima | $Y$ maxima |
| --- | --- | --- |
| $12$ | $(1/2,2,5/2,2)$ | $(1,5/2,7/2,4)$ |
| $13$ | $(3/2,1,2,5/2)$ | $(2,3/2,4,4)$ |
| $14$ | $(5/2,0,2,5/2)$ | $(7/2,0,4,4)$ |
| $23$ | $(3/2,1,2,5/2)$ | $(2,3/2,4,4)$ |
| $24$ | $(2,1/2,2,2)$ | $(3,1,4,7/2)$ |
| $34$ | $(5/2,1/2,2,2)$ | $(7/2,1/2,4,7/2)$ |

The anchors are $W_Z=7$, $W_Y=21/2$, so the maxima imply
$\Delta_N(Z)=0$, $\Delta_N(Y)=1$. The stopped table
$(1,3;1,3,0)$ attains excesses $0,1$ respectively. Nonnegative
homogeneity and subadditivity of the full support, together with this
same lower table, give both costs one for every $Y+\tau Z$.
For $L>4$, inactive coordinates are constant one on every scored atom;
queries there reduce to shorter information types. Empty and singleton
$N$ functions embed in distinct pairs; repetitions and reversals add no
information, without cancelling actual request counts. Additional output
labels earn zero. This establishes the complete-catalog claim at all
lengths, while leaving every unscored row in the domain.

For $V=(1+\tau)Z$ the residual is independent of $\tau$:
$q_\tau-Q(V)=(0,1/2,2,2,0,\ldots;15/2)$.
The exact signed hull readings from 198.5 are

$$
\begin{array}{c|c}
o,p&-1/2\\
u_3&3/4\\
u_k\ (k\ge4)&-1/2+9/[2(k-1)]\\
v_3&5/8\\
v_k\ (k\ge4)&4-(15/2)(k-2)/(k+1).
\end{array}
\tag{210.14}
$$

Their maximum is one, attained at $u_4,v_4$; both expressions for
$k\ge4$ decrease. Thus $\theta=1$ with this nonzero zero-cost
core satisfies (210.4). Direct substitution gives
$F_{q_\tau}(b^*)=(9+\tau)/8$, so (210.11) forces
$m(V)\ge(1+\tau)/2$. The displayed core has exactly that mass.

Finally $F_{Q(Z)}(b^*)=1/8$ but $\Delta_N(Z)=0$.
Any finite feasible $G_N\lambda\ge h(b^*)$ would, on multiplication
by $Z$, imply $1/8\le0$. Thus $b^*\notin H_N$.
The four-table law is short of the independent pair demand and is not
a cap attainer there. All $q_\tau$ are in $E_N$; the obstruction is
to certificates whose final score has $m=0$, including their one-budget
convex, signed and zero-core combinations only while $m=0$ remains.
Suppliers which introduce this cylinder are not excluded. $\square$

### 210.3 Conditional cardinalities and three-peak selectors

**Theorem 210.5 (Exact conditional-moment criterion and its score construction).**
Choose actual late addresses $J=\{j_1<\cdots<j_h<p<z\}$,
$h\ge2$, containing every positive late correct total; zero-total
slots are allowed. Suppose

$$
s>0,\quad 0<d\le s,\quad r=d/s,\quad
2\le u\le\min(2+r,3-r),\quad a=3+r-u,
$$

and define

$$
\phi(x)=2\lfloor x\rfloor x-\lfloor x\rfloor(\lfloor x\rfloor+1),
\quad x_+=\frac{h(3-u)}a,\quad x_- =\frac{h(u-1)}u.
\tag{210.15}
$$

There is a finite nonnegative Boolean measure of mass $(3+r)s$,
with $z$ always zero and moments

$$
m_{j_i}=2s,\quad \nu(x_{j_i}=x_{j_l}=0)=s\ (i\ne l),\quad
m_p=us,\quad \nu(x_{j_i}=x_p=0)=(u-1)s
\tag{210.16}
$$

if and only if

$$
a\phi(x_+)+u\phi(x_-)\le h(h-1).
\tag{210.17}
$$

When this holds, every input-family profile with
$0\le\gamma_j\le s+d$ and $B\ge4s+d$ has an explicit
same-$Q$, same-$W$ score with $\Delta_N\le d$.
Arbitrary early correct rows may be retained. This last condition
on $B$ is sufficient; the moment equivalence concerns exactly (210.16).

**Proof.** Let $K$ count zeros among the first $h$ selected slots.
Conditioning on $x_p=1,0$ gives masses $as,us$ and conditional means
$x_+,x_-$, respectively. Both masses are positive and both means lie
in $[0,h]$: $a\ge1$, $0\le3-u\le a$, and $0\le u-1\le u$.
For an integer variable $K\in\{0,\ldots,h\}$ of mean $x$, putting
$q=\lfloor x\rfloor$ gives
$(K-q)(K-q-1)\ge0$. Its expected factorial moment is therefore at
least $\phi(x)$, attained by the adjacent-integer law at
$\lfloor x\rfloor,\lceil x\rceil$. The upper bound
$K(K-1)\le(h-1)K$ is attained by the law on $\{0,h\}$ with mean
$x$. Integral means use a single atom in the first construction.

Summing the specified pair intersections requires
$\int K(K-1)=h(h-1)s$. The sum of the two conditional lower
bounds is $s[a\phi(x_+)+u\phi(x_-)]$, while their upper bounds sum
to $2h(h-1)s$, since $ax_++ux_-=2h$. This proves necessity of
(210.17). For sufficiency let $L_0$ be that combined lower bound and
$U_0=2h(h-1)s$. Mix each conditional minimum law with its respective
maximum law using the same parameter

$$
\lambda=\frac{h(h-1)s-L_0}{U_0-L_0}\in[0,1].
$$

The denominator is positive. Conditional on each chosen $K$, choose a
uniform $K$-subset of the first $h$ slots. Set $x_p$ to the chosen
conditioning bit and $x_z=0$. This is one actual finite measure.
Symmetry gives each first-slot marginal $2s$, each pair intersection
$s$, and each intersection with $p$ equal to $(u-1)s$, proving all
moments simultaneously. No exchangeability hypothesis was used for
necessity; symmetry is only a constructive choice for sufficiency.

To construct the score, put inactive coordinates to one, lift half of
each atom to each early prefix $01,10$, and use the threshold placement
of [203.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md).
In detail, set $a_{nk}=\nu(x_n=0,x_k=1)$ for selected $n<k$.
For $t\in[0,\gamma_n)$ the correct word has every earlier bit one,
bit $n$ zero, and later selected bit $k$ equal to one exactly when
$t<a_{nk}$. Its coefficient is the length of the corresponding
parameter interval. Finitely many cutoffs define nonnegative atoms;
threshold equalities have zero length. Inactive bits are one.
Set $T=s+(B-4s-d)$ and retain the original early $C$ rows.
All class totals, $B$, $Q$ and $W$ are preserved.

For the whole-table bound first set every selected total to
$\mu=s+d$, remove early $C$, and set $T=s$. The actual pair cells
of the carrier, in answer order $00,01,10,11$, are

$$
\begin{array}{c|c}
j_i,j_l&(s,s,s,d)\\
j_i,p&((u-1)s,(3-u)s,s,d)\\
i,z&(m_i,0,(3+r)s-m_i,0).
\end{array}
\tag{210.18}
$$

Every selected marginal is at least $2s\ge\mu$; for $p$ use $u\ge2$,
and for $z$ use $m_z=(3+r)s$. Every ordered target capacity is at
least $s$: on pairs with $z$ the smallest is $as\ge s$, using
$u\le2+r$. Thus the quantity $\kappa$ of (203.6) is at most $d$.
The non-$11$ part of the proof of 203.2 bounds all those cells
together by this one $\kappa$, independently of $T$.
In particular its off-diagonal clipped-threshold bounds retain
earlier labels, and its simultaneous $00,10$ argument uses

$$
g_{00}+g_{10}
 \le\gamma_n+\gamma_l-\nu(\{x_n=0\}\cup\{x_l=0\})\le\kappa
\quad(n\le i<l\le j)
$$

when both gains are positive. This is the union estimate (203.18),
not two copies of $d$.

No extra $11$ allowance is needed. At a late pair not involving $z$,
its baseline including $T$ is $s+d=\mu$.
At early/$j_i$ it is $s+(s+d)/2\ge\mu$.
At early/$p$ it is $s+as/2\ge\mu$, because
$a\ge2r$ follows from $u\le3-r$.
Every correct word has $z=0$, since $a_{nz}=0$, so a pair involving
$z$ has no correct reward in $11$. The head pair has excess $d$.
These cases account for all labels and every pair type. Inactive queries
give shorter information types, handled by 207.2's catalog completion.
Hence both complete excesses of the equal-total core are exactly $d$.
Reducing a late class to its prescribed total cannot increase support
and leaves the anchor unchanged. Adding early $C$ or terminal surplus
increases each table by at most the added anchor mass, so excess cannot
increase. This proves the asserted general upper bound. $\square$

**Theorem 210.6 (Five- and seven-slot minima with three peaks).**
Let $E=0$ and let exactly five, or exactly seven, designated late
slots contain all positive late totals. Suppose at least three totals
equal $\mu=\max\gamma_j$, and let $d>0$. In the respective ranges

$$
2d\le\mu\le5d\quad\text{(five slots)},\qquad
2d\le\mu\le11d/3\quad\text{(seven slots)},
\tag{210.19}
$$

the least $B=S+T$ permitting $\Delta_O\le d$, or permitting
$\Delta_N\le d$, is exactly $4\mu-3d$.
Competitors are the entire input family with those totals and $E=0$,
allowing arbitrary early $00$, correct suffixes, joint projections and
$S/T$ splits. An attainer has $T=\mu-d$ and $S=3\mu-2d$.
Consequently an actual input in this profile with
$\delta=\Delta_O(y)>0$ satisfying the corresponding (210.19) with
$d=\delta$ has a same-$Q$, same-$W$ representative of $N$ cost at
most $\delta$. If $\delta\le1$, its certificate has $\theta=0$.

**Proof.** Apply the actual-input inequalities of 208.2 at three
ordered peak addresses $i<j<k$. They give
$m_i\ge2(\mu-d)$ and $m_i+2\mu\le B+d$, hence
$B\ge4\mu-3d$. Early $00$ is included in that owner's disjoint-loss
proof, and no suffix condition is imposed on a competitor.

For the upper witness first construct equal totals at two endpoints
with $d=1$. At $s=1$, give the fair product measure on all nonterminal
selected bits total mass four, force the terminal bit zero, and use
the threshold placement with totals two and $T=1$.
This is 210.5 with $r=1,u=2,a=2$; a conditional binomial law realizes
the required moments. Its costs are one.

For five slots take $h=3,s=4,u=9/4,r=1/4,a=1$. In the slot order
$(j_1,j_2,j_3,p,z)$ one realizing measure is

| Answer words | Mass of each word |
| --- | --- |
| $00010$ | $1$ |
| $00100,01000,10000$ | $2$ |
| $00110,01010,10010$ | $1$ |
| $01100,10100,11000$ | $1$ |

It has $S=13$, marginals $(8,8,8,9,13)$, and $T=4$.
Here $x_+=9/4$, $x_-=5/3$, and
$\phi(9/4)+(9/4)\phi(5/3)=6$, so (210.17) is equality.
With all five totals five, $B=W=17$ and the full support is 18.
For example the complete $N$ cell maxima are

$$
\begin{array}{c|c}
\text{head}&(0,13/2,13/2,5)\\
\text{early}/j_i&(4,5/2,5,13/2)\\
\text{early}/p&(9/2,2,5,6)\\
\text{early}/z&(13/2,0,13/2,4)\\
j_i/j_l&(4,4,5,5)\\
j_i/p&(5,3,5,5)\\
j_i/z&(8,0,5,4)\\
p/z&(9,0,5,4).
\end{array}
\tag{210.20}
$$

The head is a stopped attainer. These arrays are also direct readings
of the general complete bound in 210.5.

For seven slots use $h=5,s=8/3,u=19/8,r=3/8,a=1$.
Force $z=0$. On $x_p=1$, give total masses $7s/8,s/8$ to uniform
zero subsets of sizes $3,4$ among the first five slots. On $x_p=0$,
give total masses $s/4,17s/8$ to uniform zero subsets of sizes $2,3$.
These four conditional layers give $S=9$, first-five marginals $16/3$,
$m_p=19/3$, $T=8/3$, and all totals $11/3$.
The two conditional factorial lower contributions, divided by $s$,
are $27/4$ and $53/4$, summing to $20=h(h-1)$.
Thus $B=W=35/3$ and both supports are $38/3$ by 210.5.

Interpolate entire endpoint scores with one convex parameter, then
scale by $d$. For five slots this gives every $s\in[d,4d]$;
for seven it gives every $s\in[d,8d/3]$. The resulting totals are
$s+d$, $S=3s+d$, $T=s$, and $B=4s+d$.
Convexity bounds the single complete excess by $d$.
Reduce each late correct measure proportionally to the prescribed
$\gamma_j\le\mu=s+d$, leaving the pair rows and terminal unchanged.
A peak remains, so the head attains $\mu-T=d$.
This proves the minimum and its attainment. For an actual input the
lower bound makes this construction affordable at $d=\delta$;
add the surplus $B-(4\mu-3\delta)$ to $T$ to preserve its quotient.
This yields an upper bound $\delta$, without claiming the same cost
is the minimum at surplus stock.

The five-slot endpoint $\mu=5d,B=17d$ is also the equal-profile
endpoint of 210.8 below. It is one attained stock value with two
possible carriers, not two separate increments. Relative to the
displayed aggregate test 205.10, the stricter thresholds supplied here
begin at $4d<\mu\le5d$ for five slots and
$3d<\mu\le11d/3$ for seven: its respective competing branches are
$(13/3)(\mu-d)$ and $(9/2)(\mu-d)$.
The endpoint values of those branches are $52d/3$ and $12d$.
Earlier portions of (210.19) retain that supplier's ownership.

There is also a bounded single-template comparison at the contiguous
five-slot endpoint. For the named template 202.11, let
$u_0=\max_j\eta_j$ be its retained late maximum, $D\in[0,1]$ its
cost and $\theta$ its sole residual charge; normalize $d=1$.
Its pair stock is at least $13u_0/4$, and its head forces
$T'\ge u_0-D$, hence $W'\ge17u_0/4-D$.
Overscaling that template only increases this reserve.
Since $\sum\eta_j\le5u_0$, the $u_7,v_7$ residual readings in
207.8 are at least

$$
\frac{25-5u_0}{6},\qquad
\frac{25u_0/4-10-5D}{8}.
$$

The one budget $D+\theta\le1$ would require both
$u_0\ge19/5+6D/5$ and $u_0\le72/25-12D/25$, which are incompatible.
This excludes only that entire specified single-template family,
including its $D=0,\theta=1$ case; mixtures with other suppliers
are not excluded. The use of $u_0=\max\eta$ is essential.

Finally $E=0$ is essential for the necessity above. At $L=7$ put
correct mass $\mu$ at each absorbing-chain word
$1^{j-1}0^{8-j}$ for $1\le j\le7$, take $A=P=0$ and
$T=\mu-d$, where $\mu\ge2d>0$.
Each pair has at most three nonempty chain cells, each label earns
at most $\mu$, and a stopped table collecting three classes attains
$3\mu$. Thus $E=2\mu$, $B=\mu-d$, $W=3\mu-d$, and both costs
are $d$, although $B<4\mu-3d$. This is the absorbing-chain
supplier 206.7 applied inside the boundary argument. It is already
an affordable score, not a separator. The ratios in (210.15)–(210.19)
require $d,s>0$; no division at $d=0$ is intended. $\square$

### 210.4 Nonuniform stock in a protected fixed-terminal class

**Theorem 210.7 (One heavy internal class and equal light classes).**
Let $m\ge2$, $a>0$, $0\le c\le a$. Choose a heavy address $h\ge3$,
a disjoint set $J$ of $m$ light late addresses, and
$z>\max(\{h\}\cup J)$ with $L\ge z$. Put $I=\{h\}\cup J$.
Consider the following restricted class of input-family scores.
The late correct rows are fixed as

$$
C_{w(\{h,z\})}=a,\qquad C_{w(\{j,z\})}=c\ (j\in J),\qquad
C_{w(\{z\})}=a.
\tag{210.21}
$$

There are no other late correct rows. Early $C$ is arbitrary.
Pair rows may have any early prefix $00,01,10$, but their terminal
bit is zero and inactive late bits are one. Their projection onto $I$
is one measure $\nu$. Take $T=\tau\ge0$.
Require protection: after early $C$ is removed, every late-label
reward in every non-$11$ cell of every distinct-pair $N$ schedule is
at most that cell's zero-label pair reward.

Put $q_m=\lfloor m^2/4\rfloor$ and

$$
r_m(a,c)=\max\left\{a,
 \max_{1\le k\le m-1}\frac{2(mkc-q_ma)}{k(k+1)}\right\},\qquad
S_m(a,c)=2a+r_m(a,c).
\tag{210.22}
$$

The exact least pair stock in this protected fixed-terminal class is
$S_m(a,c)$, and it is attained. Every protected member has
$\Delta_N=\Delta_O=(a-\tau)_+$.
At fixed $B=S+\tau$, the class is empty for $B<S_m$; otherwise its
attained minimum excess in either catalog is $(a-B+S_m)_+$.
Thus for $d\ge0$ it contains a score of cost at most $d$ exactly when

$$
B\ge S_m(a,c)+(a-d)_+.
\tag{210.23}
$$

In particular the least stock is $3a$ exactly when

$$
\frac ca\le\min_{1\le k\le m-1}
                \frac{k(k+1)+2q_m}{2mk}.
\tag{210.24}
$$

All these necessities and minima are restricted to the stated protection
and fixed correct placements.

**Proof.** Use zero subsets $Z\subseteq I$ and write
$m_i=\nu(i\in Z)$, $a_{ij}=\nu(i\in Z,j\notin Z)$ for both
ordered orientations. Protection forces

$$
m_i\ge2\gamma_i,\qquad a_{ij}\ge\gamma_i\ (i\ne j\text{ in }I),
\qquad S-m_i\ge a,\qquad S\ge2a.
\tag{210.25}
$$

Indeed class $i$ has reward $\gamma_i$ in the $10$ cell of each
early/$i$ schedule. The two pair loss sets are disjoint, even with
early $00$, and their sum is at most $m_i$.
At an internal pair, the queried correct classes occupy the two
opposite off-diagonal cells, forcing both directed bounds.
On $(i,z)$ the terminal class in $10$ forces $S-m_i\ge a$.
The two early/$z$ loss sets force $S\ge2a$.

Conversely, a projected measure satisfying (210.25) gives a protected
score by balanced early lifts at $w(\{1,z\}\cup Z)$ and
$w(\{2,z\}\cup Z)$, each with coefficient $\nu(Z)/2$.
Internal pairs have only their queried classes outside $11$;
their directed capacities cover them. On $(i,z)$ the $00$ reward is
at most $\gamma_i\le m_i$, and every $10$ correct reward is at most
$a\le S-m_i$. Early/internal pairs use $m_i/2\ge\gamma_i$;
early/terminal pairs use $S/2\ge a$.
Inactive queries give singleton or constant information. Early labels
collect subsets of pair mass. These cases prove protection for all
labels; the converse assertion concerns the balanced lift, since an
arbitrary early allocation can fail protection despite its projection.

For a necessary stock bound set
$U=\nu(h\in Z)\ge2a$, $V=\nu(h\notin Z)\ge a$, and
$K=|Z\cap J|$. The light/light directed bounds and light/heavy
bounds give

$$
\int K(m-K)\,d\nu\ge m(m-1)c,\qquad
\int_{h\notin Z}K\,d\nu\ge mc.
\tag{210.26}
$$

On $h\in Z$ use $K(m-K)\le q_m$.
For an integer $k\ge\lfloor m/2\rfloor$, $k\le m-1$,
$(K-k)(K-k-1)\ge0$ gives

$$
K(m-K)\le(m-2k-1)K+k(k+1).
$$

The coefficient of $K$ is nonpositive and $k(k+1)\ge q_m$.
Integrating and using (210.26) yields

$$
2mkc\le q_mU+k(k+1)V
 \le2aq_m+k(k+1)(S-2a).
\tag{210.27}
$$

The second inequality uses $U\ge2a$ with the nonpositive coefficient
$q_m-k(k+1)$. Also $S=U+V\ge3a$.
If $f_k=2(mkc-q_ma)/(k(k+1))$, then

$$
f_{k+1}-f_k=\frac{2(2q_ma-mkc)}{k(k+1)(k+2)}\ge0
 \quad(1\le k<\lfloor m/2\rfloor),
$$

using $c\le a$ and $mk\le2q_m$ in that range. Thus smaller $k$
cannot increase the maximum, and (210.27) proves $S\ge S_m$.
The cut-count principle $K(m-K)$ is the classical one in Robert
Šámal, [*Cubical coloring — fractional covering by cuts and semidefinite
programming*, Lemma 2.1 and Corollary 2.2](https://arxiv.org/pdf/0911.2589v3).
Here the two conditional regions and their unequal directed requirements
are supplied by (210.25), not by an undirected covering formula.

To attain the bound put $r=r_m(a,c)$. On $h\in Z$ place mass $2a$
on a uniform central-size subset of $J$: size $m/2$ if $m$ is even,
or an equal mixture of sizes $(m-1)/2,(m+1)/2$ if $m$ is odd.
On $h\notin Z$ place mass $r$; set $x=mc/r\in[0,m]$, choose
the adjacent-integer law of mean $x$ for $K$, then choose a uniform
$K$-subset of $J$. These are actual finite nonnegative atoms.
Their moments are

$$
m_h=2a,\qquad m_j=a+c,\qquad a_{hj}=a,\qquad a_{jh}=c.
\tag{210.28}
$$

For the remaining directed bounds, let $f_m(p)$ be the linear
interpolation of $k(m-k)/(m(m-1))$ at $p=k/m$.
The concavity of this interpolation, or its successive slopes, gives

$$
r f_m(c/r)=\min_{0\le k\le m-1}
 \frac{m(m-2k-1)c+k(k+1)r}{m(m-1)}.
\tag{210.29}
$$

For every $k\ge1$ the definition of $r$ implies
$2aq_m+m(m-2k-1)c+k(k+1)r\ge m(m-1)c$;
for $k=0$ this is immediate. Hence each light/light directed mass,
equal by symmetry to
$2aq_m/[m(m-1)]+r f_m(c/r)$, is at least $c$.
The complements in (210.25) are $r$ for $h$ and $a+r-c$ for a
light, both at least $a$. Also $a+c\ge2c$.
Thus all of (210.25) hold, and balanced lifts attain $S_m$.
Additional stock at the empty internal subset preserves those bounds
and protection.

The complete-support argument of 207.13 applies with largest late
weight $a$. Every non-$11$ maximum of the protected core is its pair
baseline; its $11$ maximum is at most that baseline plus
$\max(\tau,a)$. The full support is at most $S+\max(\tau,a)$.
Adding early correct mass $E$ increases each table by at most $E$
and the anchor by exactly $E$. The stopped head table outputs 1,2
on its first two cells and either zero or $z$ on exhaustion, attaining
$E+S+\max(\tau,a)$. Thus both costs equal $(a-\tau)_+$.
At fixed $B$, minimize $(a-B+S)_+$ over $S\ge S_m$, with
$\tau=B-S\ge0$. This proves (210.23), including $d=0$, $\tau=0$
and all ties. Formula (210.24) is exactly the condition that every
$f_k\le a$. The case $c=0$ is included; $c=a$ specializes to the
already-owned uniform protected result 207.13 with $m+1$ internal
coordinates. No new uniform endpoint is asserted.

The attaining pair measure also protects any reduced profile
$0\le\eta_h,\eta_z\le a$, $0\le\eta_j\le c$ on $J$, with
other late totals zero, by using the corresponding rows (210.21).
Its cost is exactly $D=(\mu_\eta-\tau)_+$, by the same upper bound
and a head attainer at a largest remaining label. This does not assert
that $S_m$ is the least stock for the reduced profile.

For a same-$Q$ application to an arbitrary input with the exact
two-level totals, $B\ge S_m$ permits retaining its early $C$ and
using $T=B-S_m$. Its cost is $(a-B+S_m)_+$; in particular
(210.23) is a sufficient certificate threshold.
For an altered profile $\eta$ of the allowed reduced shape, set
$B'=S_m+\tau$ and $R_k=\sum_{j=3}^k(\gamma_j-\eta_j)$.
Substitution in the old full signed hull (207.8), retaining early $C$,
gives the exact nonnegative residual charge

$$
\Theta=\max\left\{0,\max_{3\le k\le L}\frac{R_k}{k-1},
 \max_{3\le k\le L}\frac{3R_k+(k-2)(B'-B)}{k+1}\right\}.
\tag{210.30}
$$

The $o,p$ readings are zero; $R_k$ may have either sign. One condition
$D+\Theta\le1$ supplies the certificate, including $D=0,\Theta=1$.
It uses $F_{Q(y)}\le MD+\Theta$ for the same feasible configuration
of mass $M$, not separate allowances for components. This is an
application of the existing hull inside the stock construction.

For an explicit nonuniform example take $h=3$, $z=10$,
$J=\{4,5,6,7,8,9\}$, $a=10$, $c=8$. Then
$q_m=9$, $r=51/5$, $S_m=151/5$; the $k=4$ bound in (210.27)
is equality. The attaining internal measure can be written

$$
\nu(\{3\}\cup U)=1\ (|U|=3),\qquad
\nu(U)=1/5\ (|U|=4),\qquad
\nu(U)=6/5\ (|U|=5),\quad U\subseteq J.
\tag{210.31}
$$

Use balanced early lifts, the correct rows (210.21), $E=0$ and $T=9$.
Its heavy marginal is 20, each light marginal 18, each heavy-to-light
directed mass 10, each reverse mass 8, and every light/light directed
mass 8. Therefore $W=196/5$, $K=536/5$, and both supports are
$201/5$, giving protected-class minimum cost one at this $B$.

This example admits a precise comparison with the positive 201.2
block cone sharing the same terminal $z$ and preserving all these
correct totals. The sum of block coefficients must be 10, and the
heavy total 10 forces $h$ into every positive block. A block with
$k$ lights has stock coefficient $c_{k+2}\ge11/4+k/8$ for
$0\le k\le6$. For $k=0,1,\ldots,6$ the actual coefficients from
201.2 are $3,3,3,10/3,10/3,7/2,7/2$, verifying the inequality
and its equality at $k=2,6$.
The total light incidence is 48, so every such mixture has stock at
least $110/4+48/8=67/2$. Equality is attained by weight 7 on the
full block and weight $1/5$ on each of the fifteen two-light blocks
$\{h,i,j,z\}$. Each light appears in five of the latter.
Thus this precisely specified cone costs more than $151/5$.
The ordinary nested-layer stock of 201.3 is $8(7/2)+2(3)=34$,
with unit total-stock threshold 43. The sufficient aggregate test
205.10 instead requires
$\max((18/5+1)9,27+10)=207/5>196/5$.
The sparse sufficient test 202.8 requires the internal light sum
to be at most $2a$; here it is $48>20$.
Changing terminals, suffix placements, event types or allowing general
signed and zero-core combinations is outside this block-cone exclusion.
Neither its lower bound nor protection proves that an arbitrary actual
unit-$O$ input must afford (210.23) or (210.30). $\square$

### 210.5 Four leading peaks and one lower total

**Theorem 210.8 (Exact five-coordinate joint stock threshold).**
Let $L\ge7$, $J=\{j_1<j_2<j_3<j_4<j_5\}\subseteq\{3,\ldots,L\}$.
In the input family impose $E=0$ and

$$
\gamma_{j_1}=\cdots=\gamma_{j_4}=g,\qquad
\gamma_{j_5}=h,\qquad \gamma_j=0\ (j\notin J,\ j\ge3),
\quad d\ge0,\quad g\ge2d,\quad 0\le h\le g.
$$

Correct suffixes and early pair allocation, including $00$, are free.
Put

$$
u=g-d,\qquad v=(h-d)_+,\qquad
B_*=4u+\max(d,v/4).
\tag{210.32}
$$

At each prescribed $B\ge0$, there exists an input of these totals and
stock $B$ with $O$ excess at most $d$ if and only if $B\ge B_*$,
if and only if there exists such an input with $N$ excess at most $d$.
For every $B\ge B_*$ an explicit common score has
$T=u$, $S=B-u$ and both excesses exactly $d$.
At this fixed $T=u$ the exact least pair stock is
$3u+\max(d,v/4)$. Thus every actual $O$ input in the stated class
with cost at most $d$ has a same-$Q$, same-$W$ $N$ representative
of cost $d$; for $d\le1$ take $\theta=0$ in (210.4).
Adding any prescribed early correct rows to the constructed score
preserves its cost $d$, so the threshold remains sufficient for
arbitrary $E$. Necessity and automatic affordability here require
$E=0$. At $B>B_*$ no assertion that $d$ is the minimum excess is made.

**Proof.** For an actual competitor project all early pair mass onto
the five selected zero indicators $Z_i=\mathbf1_{w_{j_i}=0}$.
This includes early $00$ and gives one measure of mass $S$.
By the existing guards in 208.2, cost at most $d$ and $E=0$ imply

$$
m_i\ge2(\gamma_{j_i}-d)_+,\qquad
D_{ij}=\int(1-Z_i)Z_j\,d\nu\ge(\gamma_{j_j}-d)_+,
\qquad T\ge g-d=u.
\tag{210.33}
$$

For every Boolean vector $(z_1,\ldots,z_5)$,

$$
2z_1+z_2+\sum_{1\le i<j\le4}(1-z_i)z_j+(1-z_4)z_5\le4.
\tag{210.34}
$$

To prove it let $k=z_1+z_2+z_3$. The first three coordinates give
$(5k-k^2)/2$: the terms $2z_1+z_2$ compensate their ordered linear
coefficients. If $z_4=1$, the whole expression is
$3+(3k-k^2)/2$; if $z_4=0$ it is $(5k-k^2)/2+z_5$.
Each is at most four for $k=0,1,2,3$. Integrating (210.34) and
then using (210.33) gives

$$
4S\ge2m_1+m_2+\sum_{i<j\le4}D_{ij}+D_{45}\ge12u+v.
\tag{210.35}
$$

The single stopped table $(j_1,j_2;0,j_2,j_3)$ collects at least
$m_1+2g$, so $B+d\ge2u+2g$, or $B\ge4u+d$.
This is the ordered-triple mechanism of 208.2, applied within this
proof. Combining (210.35) with $T\ge u$ gives
$B\ge4u+v/4$, proving $B\ge B_*$. At fixed $T=u$ subtract $u$.
These lower bounds use whole legal tables on the actual input and
impose no condition on its correct suffixes.

For attainment suppose first $u>0$. In local zero-subset coordinates
$\{1,2,3,4,5\}$ let $\nu_0$ put mass $u$ on each of
$\{1,2,4\},\{1,3,4\},\{2,3,4\}$.
Let $\nu_1$ put mass $u/3$ on every $Z\cup\{5\}$ with
$Z\subseteq\{1,2,3,4\}$ of size two or three. These are the
three-internal forced-terminal and subset-block atoms already supplied
by 201.2, used here on a common five-coordinate carrier.
Define

$$
\alpha=\frac{3v}{4u},\qquad x=(d-v/4)_+,\qquad q=B-B_*\ge0,
\qquad \nu=(1-\alpha)\nu_0+\alpha\nu_1+(x+q)\delta_\varnothing.
\tag{210.36}
$$

Since $0\le v\le u$ and $d\le u$, these are nonnegative weights
with $0\le\alpha\le3/4$. Their total is
$3u+v/4+x+q=B-u$. Lift half of each atom onto each actual pair
word $w(\{1\}\cup\{j_i:i\in Z\})$ and
$w(\{2\}\cup\{j_i:i\in Z\})$; set all inactive bits to one.
Take $T=u$. Place correct rows by the threshold construction of 203.2:
for selected $i<j$ let $a_{ij}=\nu(Z_i=1,Z_j=0)$, and give class
$j_i$ length measure on $t\in[0,\gamma_{j_i})$ with later bit
$j_j$ one exactly when $t<a_{ij}$. This defines finitely many full
words and preserves all correct totals. It uses no acquisition seed.

It suffices first to bound the core with $q=0$ and fifth total $v+d$.
When $h<d$ this total can subsequently be reduced to $h$.
Counting the atoms in (210.36) gives, with $I_0=\{1,2,3\}$,

$$
\begin{aligned}
m_i&=2u\ (i\in I_0),&m_4&=3u-3v/4,&m_5&=5v/2,\\
D_{ij}&=u\ (i<j\le4),&D_{i5}&=v\ (i\le4),\\
a_{ij}&=u\ (i<j\text{ in }I_0),&a_{i4}&=3v/4\ (i\in I_0),\\
a_{i5}&=2u-3v/2\ (i\in I_0),&a_{45}&=c_*=3u-9v/4.
\end{aligned}
\tag{210.37}
$$

The $11$ pair masses are $v/4+x$ within $I_0$ or from $I_0$ to 4,
$u-3v/4+x$ from $I_0$ to 5, and $x$ for $(4,5)$.
For example these also follow from $p_{11}=S-m_i-D_{ij}$.
The first four marginals are at least $2u\ge g$; the fifth unary
half-mass deficit is $(v+d-5v/4)_+=x\le d$.
Each directed target deficit is at most $d$.
Thus $\kappa\le d$ in (203.6): its paired first deficit vanishes
because a first index of an active ordered pair is among the first four.
The non-$11$ proof (203.14)–(203.18) controls those cells jointly,
including every earlier and unqueried correct label.

For every late pair except $(4,5)$ its $11$ pair mass is at least
$v/4+x=\max(v/4,d)$, since $u\ge v$.
After adding $T=u$ it covers every correct total at most $g=u+d$.
For $(4,5)$ an earlier label contributes at most
$a_{i4}=3v/4\le u$ in $11$; there is no later positive class.
Thus that $11$ cell also has no excess. No positive terminal shortage
is added to the non-$11$ allowance.

For an early query followed by $j_i$, $i\in I_0$, the two early-zero
cells contain no late correct reward. Its $10$ excess is at most $d$.
The $11$ baseline covers $g$, since its pair mass is
$(u+v/4+x)/2\ge d$. For early/$j_4$, the only possible positive
gains, in $10$ and $11$, are bounded respectively by

$$
A=(d-u/2+3v/8)_+,\qquad
C=(d-u+v/2-x/2)_+.
\tag{210.38}
$$

Indeed the $10$ correct maximum is at most $g$, and its pair baseline
is $m_4/2$; the $11$ correct maximum is at most $g$, and its zero
baseline is $u+(S-m_4)/2=2u-v/2+x/2$.
Each of $A,C$ is at most $d$. If both are positive, then

$$
A+C=2d-3u/2+7v/8-x/2
 \le3d/2-3u/2+v\le d,
$$

using $x\ge d-v/4$ and $d/2+v\le3u/2$.
If at most one is positive its individual bound suffices.

For early/$j_5$, earlier $10$ rewards are at most $v+d$:
for $i\in I_0$ they are
$(g-a_{i5})_+=(d-u+3v/2)_+\le v+d$;
for class 4 they are $(g-c_*)_+=(d-2u+9v/4)_+\le v+d$.
The fifth reward is $v+d$, so its $10$ excess is at most $x\le d$.
The largest earlier $11$ reward is at most $\min(u+d,c_*)$, because
$c_*\ge2u-3v/2$. It satisfies
$\min(u+d,c_*)\le u+c_*/2$: if $c_*\le2u$ use the first term
$c_*$, and if $c_*\ge2u$ use $u+d\le2u\le u+c_*/2$.
The zero baseline is $u+(c_*+x)/2$, so the $11$ gain is zero.
The head pair has excess $g-u=d$.
This bounds every complete early pair with one $d$.

Inactive queries supply singleton or constant information on the core;
the full catalog completion of 207.2 includes empty rules, repetitions
and reversals and every output label. Therefore $\Delta_N\le d$.
The stopped head table $(1,2;1,2,j_1)$ attains $W+d$, proving both
costs exactly $d$. Reduce the fifth class when $h<d$; the head
attainer is unaffected. Add the surplus pair mass $q$ at the empty
selected subset. It changes neither threshold cutoff nor correct row,
increases each fixed table by at most $q$, and increases the anchor
and this head reward by exactly $q$. Hence both costs remain $d$.
Arbitrary early $C$ additions have the same monotonicity and are all
collected by that head table. This proves the sufficient arbitrary-$E$
extension, without using $E=0$ necessity outside its domain.

If $u=0$, $g\ge2d$ forces $g=h=d=0$.
For any $B\ge0$ take only early pair mass $B$ at
$w(\{1\})$, with $T=0$; both costs are zero. No division by $u$
is used. The construction also includes $d=0$ with $u>0$,
$h=0,d,g$, arbitrary address gaps, and the branch equality $v=4d$.
The old $d=0$ equal-five endpoint from 202.11 is an application of
that supplier, not an additional assertion of new endpoint coverage.

The pointwise cut also has a useful input consequence with arbitrary
$E$ and arbitrary ordered selected totals. Put
$r_i=(\gamma_{j_i}-E-d)_+$. The same actual guards and (210.34) give

$$
4S\ge4r_1+3r_2+2r_3+3r_4+r_5,\qquad
B\ge2r_1+\gamma_{j_2}+\gamma_{j_3}-E-d.
\tag{210.39}
$$

The coefficients follow by counting target occurrences in the six
directed terms, the extra $(4,5)$ term, and $2m_1+m_2$.
The second inequality is the same whole stopped table lower bound.
These are necessary only; they do not imply a certificate by themselves.

For a boundary illustrating the joint budget, set $d=1,u=v=3$ and
omit $x=1/4$ from (210.36). Then $S=39/4$, $T=3$, $g=h=4$,
$B=51/4$. The marginal and directed conditions still hold, but
$(j_1,j_2;0,j_2,j_3)$ has excess
$m_1+2g-B=6+8-51/4=5/4$.
The full upper bound is also $5/4$: for late pairs other than $(4,5)$,
the non-$11$ allowance is at most one and the $11$ shortage at most
$1/4$; $(4,5)$ has no $11$ shortage.
Early/first-three has gain at most $1+1/8$,
early/4 gains at most $5/8+0$, and early/5 at most $1/4$;
the head costs one. Catalog completion gives both complete costs
$5/4$. Adding the missing $1/4$ yields $B_*=13$ and cost one.
This is a failure of a simultaneous-cell shortcut, not an acquisition
counterexample.

The common five-slot value $g=h=5d,B_*=17d$ is the endpoint already
displayed in 210.6. At $d=1,g=h=9$ the other branch gives
$B_*=34$, $S=26$, $T=8$, $K=79$ and both costs one.
At $d=1,g=2,h=1/2$ it gives $B_*=5$, $S=4$, $T=1$,
$K=27/2$ and both costs one. These substitutions illustrate the
$v/4$ branch and the $h<d$ domain within the same theorem.

Applying the existing finite-prefix transport argument of 207.20 to
this score gives, for any original $N_2$ or $O_2$ closed-cap attainer,

$$
g\sum_{i=1}^4a_{j_i}+h a_{j_5}
 \le d+(4g+h+B)\varepsilon.
\tag{210.40}
$$

Indeed the target event score is
$W+g\sum_{i=1}^4a_{j_i}+h a_{j_5}-K\varepsilon$,
$K=4g+h+B$, while complete support is $W+d$.
The arbitrary-address and actual-tail passage is precisely 110.2
with 207.20's finite-prefix argument, not an assumption restricting
competitors to these five queries. This is a necessary amplitude
inequality only. At the shared endpoint it reads
$5\sum_{i=1}^5a_{j_i}\le1+42\varepsilon$ after normalization $d=1$.
$\square$

**Definition 210.9 (Mathematical ownership and remaining domain).**
The constructions above use the subset atoms of 201.2, threshold words
and union bound of 203.2, signed hull of 198.5 and complete certificate
of 199.3–199.6. Actual-input marginal and triple guards remain owned
by 208.2. The fixed-projection identities 209.2–209.5, comparable
submeasure constructions 209.7–209.11, and unary-preserving mixed-carrier
conditions 209.12–209.15 retain their respective hypotheses. None is
replaced by an unconditional pruning or by a presumed disjointness
from every old convex, signed and zero-core consequence.

The additional statements here are the four-late full-score inequality
and specified relaxation obstruction, the all-certificate cylinder-mass
minimum, the exact specified conditional moments and their finite-slot
selectors, the nonuniform protected stock function, and the five-coordinate
joint threshold with its constructive attainment. Their mathematical
status is repository-derived ordinary proof; no literary priority or
exhaustive novelty assertion is made. Classical cut counting, integer
moment convexity and finite support separation are methods within these
proofs, not separately advertised new theorems.

The comparisons with 208.8 and 208.9 have concrete scope boundaries.
At the shared five-slot data $\gamma_j=5,S=13,T=4,E=0$, 208.8
gives support lower bound 18 and its relocated upper bound 23;
its dominance condition is absent. This compares that displayed formula,
not its entire certificate closure. The two-leading-class condition
$\mu\ge\eta+d$ in 208.9 fails for positive-$d$ equal leading peaks.
The heavy/light example (210.31) has a later heavy total outside its
small-later-total condition. The general results of 209 likewise do
not assert automatic existence of their required carrier or matching
conditions for all profiles. Applications of these existing statements
are used inside the foregoing proofs and comparisons.

Scores, their conditional laws, and conic vectors of arbitrary mass
are not probability-vector kernels. Only actual normalized finite kernels
satisfying every event row can use
[109.1 and 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md).
The former requires the degree-at-most-two probability-vector domain
and $c\ge H$, with the displayed scalar $\beta\le1$ implied under
that normalization. For sufficiency, one source-independent uniform
seed selects the entire schedule and terminal table before replies;
different class configurations can use a common refinement of partitions
of that same seed. Every executed schedule respects its actual request
bound and hands off finitely. Apart from the normalized seven-table
witness in 210.2, the constructions here are dual proof scores.

The necessary direction of 110.2 retains arbitrary-address and
full-carrier competitors: countability supplies a common probability-one
seed event, the maximum address of the entire schedule has a vanishing
seed tail, each finite Boolean pattern has an actual source witness by
Boundaries 35.2, and sourcewise finite handoff permits finite witness
cutoffs. The compact finite-catalog limit retains the exact closed cap.
At $L_a=\max(\{j:a_j>\varepsilon\}\cup\{0\})$, every actual
$n>L_a$ has exact error

$$
\operatorname{TV}\left(\sum_{j=0}^{L_a}p_{1^{L_a}}(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-p_{1^{L_a}}(0),a_n\}.
\tag{210.41}
$$

Equality $a_n=\varepsilon$, small active lengths and the cap-one
endpoint are included; for larger caps immediate base output suffices.
Neither auxiliary $e=0$ nor a zero score coordinate changes a positive
original amplitude. The source, full carrier, consumer, nonatomic
targets, marked-law quantifier and common seed remain fixed.

For every original positive monotone vanishing amplitude sequence and
every positive closed cap, the universal implication

$$
\mathcal F_N(a,\varepsilon)\ne\varnothing
 \quad\Longrightarrow\quad
\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing
\tag{210.42}
$$

remains unresolved. The four-late counterfamily is outside unit-$O$;
the cylinder point is outside $H_N$; conditional selectors require
their stated ratios and three peaks; protected necessity requires the
fixed-terminal protected class; the exact five-coordinate necessity
requires $E=0$ and $g\ge2d$. Arbitrary early credit, unordered and
growing profiles and the remaining low-terminal regimes have no
automatic certificate supplied here. A method obstruction is not
$E_N$ nonmembership, and $E_N$ nonmembership without the original
required feasible witnesses is not a separator. No original common-seed
$N_2$ attainer with a uniform lower certificate against every full-carrier,
arbitrary-address $O_2$ competitor is established here. The exact-law
obstruction 112.2 continues to allow a different stopped law at the
same cap.

## 追加锚（本行以下为增补区）

## 211. Safe correlation switches, retained-head packing and limits of fixed choices

**Definition 211.1 (Full scores and the single comparison budget).**
Use the original source, tape carrier and acquisition contract of 210.1.
All results below are ordinary mathematics about finite proof weights.
For an integer $L\ge3$, write $\Omega_n$ for all Boolean words whose
first zero is $n$, and $w(Z)$ for the word with zero set exactly $Z$.
A full score $V$ consists of independent nonnegative $A_w,C_w,P_w$
for every $w\ne1^L$, and $T\ge0$ at $1^L$. Its reward at output
$\ell\in\{0,\ldots,L\}$ is exactly (210.1). In particular $P_w$
is the independent pair-event weight, not a sum of singleton weights.
Unspecified coefficients in a construction are zero; coincident rows add.
Write $x_+=\max(x,0)$, and take empty maxima of nonnegative quantities
and empty sums to be zero.

For a schedule $s$, let $B_C^s(V)$ be the sum of its cell reward
maxima over all output labels, and let $B_C(V)=\max_s B_C^s(V)$,
where $C=N,O$. The schedules include empty and singleton schedules.
For distinct $i<j$, the $N$ cells are $00,01,10,11$, while the $O$
cells are $0,10,11$. A tuple $(i,j;\ell_{00},\ell_{01},\ell_{10},\ell_{11})$
denotes a full $N$ table; a three-label tuple denotes a stopped table.
Use the anchor $R=(1,2;1,2,0)$, with $N$ completion $(1,1,2,0)$,
and the inherited coordinates

$$
\begin{aligned}
W_V&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_C(V)&=B_C(V)-W_V,\qquad
Q(V)=(\beta,K),\\
\beta_n&=\sum_{\Omega_n}(C_w-A_w),\qquad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
\tag{211.1}
$$

The anchor makes both excesses nonnegative. Static repetitions and
reversals introduce no new information partition; each actual request
still counts. Every short $N$ output function refines into a distinct-pair
$N$ table when $L\ge3$. Every $O$ output function belongs to $N$ by
completion. These facts, together with explicit stopped attainers below,
control short $O$ schedules. A singleton at the last address is never
presumed to embed in a nonexistent later stopped pair.

For the input family only, impose $A=0$ and
$\operatorname{supp}P\subseteq\Omega_1\cup\Omega_2$, allowing early
prefix $00$ and every correct suffix. Put

$$
\begin{aligned}
\gamma_j&=\sum_{\Omega_j}C_w,&c_1&=\gamma_1,&c_2&=\gamma_2,&E&=c_1+c_2,\\
\mu&=\max_{j\ge3}\gamma_j,&S&=\sum_wP_w,&t&=T,&W&=E+S+t.
\end{aligned}
\tag{211.2}
$$

On the full late cube $\{0,1\}^{\{3,\ldots,L\}}$ define actual measures
$\nu_{ab}(x)=P_{abx}$ for $ab=00,01,10$, and
$\nu=\nu_{00}+\nu_{01}+\nu_{10}$, of mass $S$. Let
$Z_j=\{x:x_j=0\}$, $m_j=\nu(Z_j)$,
$D_{ij}=\nu(Z_j\setminus Z_i)$ for $i<j$, and $p_{00}=|\nu_{00}|$.
These definitions precede every use of a stock or marginal below.

Keep $H_L,F_q,\sigma_H$ and $E_N$ exactly as in (210.3)–(210.4).
More explicitly, $H_L$ is the set of $(b_1,\ldots,b_L;e)$ with
$1\ge b_1\ge\cdots\ge b_L\ge e\ge0$, $b_2=b_3$,
$(L+1)e\le\sum_{j=3}^Lb_j$, and
$b_1+\sum_{j=3}^Lb_j-(L+1)e\le1$.
With $\alpha=(1,1,0,\ldots,0)$ and signed $q=(\beta,K)$,
$F_q(b,e)=\sum_j\beta_j(b_j-\alpha_j)-Ke$ and
$\sigma_H(q)=\max_{H_L}F_q$.
The full event-demand vector $d(b,e)$ has entries
$1-b_n-e,b_n-e,1-e$ at every $w\in\Omega_n$ and $1-e$ at $1^L$.
Let $z_D$ be the complete event-indicator vector of table $D$,
$r=z_R=d(\alpha,0)$, $h=d-r$ and $G_C=(z_D-r)_D$. Then

$$
\rho_C(b)=\min\left\{\sum_D\lambda_D:
 \lambda\ge0,\ G_C\lambda\ge h(b)\right\},\qquad
H_N=\{b\in H_L:\rho_N(b)<\infty\},
\tag{211.3}
$$

with value $\infty$ for an empty feasible set. Here $b$ abbreviates
$(b_1,\ldots,b_L;e)$ when used as an argument. A certificate for $q$
uses one score and one charge:

$$
V\ge0,\quad\theta\in[0,1],\qquad
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(q-Q(V))\le\theta.
\tag{211.4}
$$

$E_N$ is the set of signed quotients $q$ admitting such a certificate.
For the same full-row feasible $\lambda$ of mass $M$, it gives
$F_q(b)\le M\Delta_N(V)+\theta\le M(1-\theta)+\theta
\le\max(1,M)$. This is the existing 199.3–199.4 certificate interface,
not a new alternative or an unproved bridge. All negative singleton
demands, zero-weight rows, multiple-zero words and earlier unqueried
labels remain. In particular $(3,4;1,0,0,0)$ correctly outputs 1
on $0100$; replacing that label by zero loses the correct event.
The surviving-label premise of 197.3 remains necessary for its stated
restricted-catalog implication. Nonzero zero-cost scores remain allowed
at $\theta=1$ by 199.5–199.6.

### 211.1 A single safe switch and its attained fixed-data interval

**Theorem 211.2 (Exact donor and competing-maximum criterion).**
Let $V$ be any full score, $1\le n<i<j\le L$, and choose four words
$w_{ab}\in\Omega_n$, $a,b\in\{0,1\}$, differing only at $i,j$,
where their bits are $a,b$. On the full schedule $(i,j)$ let
$r_{ab}$ be the total reward of label $n$ in cell $ab$, let $M_{ab}$
be the maximum reward of all other labels there, and let
$c_{ab}=C_{w_{ab}}$. The cell data include every row of $V$.
Assume

$$
r_{00}\ge M_{00},\qquad r_{01}\le M_{01},\quad
r_{10}\le M_{10},\quad r_{11}\le M_{11},
$$

and define the complete available slack

$$
\tau=\min\{c_{00},c_{11},r_{00}-M_{00},
                         M_{01}-r_{01},M_{10}-r_{10}\}\ge0.
\tag{211.5}
$$

For $0\le u\le\tau$, subtract $u$ from $C_{w_{00}},C_{w_{11}}$
and add $u$ to $C_{w_{01}},C_{w_{10}}$, obtaining $V_u$.
It is nonnegative and preserves the entire $A,P,T$, $Q,W$, every
correct-class total, and every correct unary marginal
$\sum_{w\in\Omega_k,w_r=1}C_w$ for all $k,r$.
Every $O$ schedule support is unchanged. Every $N$ schedule except
$(i,j)$ has all individual cell-label rewards unchanged. Put

$$
D_{ij}=B_N^{(i,j)}(V)-W_V,\qquad
D_{\rm rest}=\max_{s\ne(i,j)}(B_N^s(V)-W_V).
$$

This local $D_{ij}$ denotes excess, not the input-measure mass in
211.1. Then

$$
\Delta_N(V_u)=\max\{D_{\rm rest},D_{ij}-u\},\qquad
\Delta_O(V_u)=\Delta_O(V).
\tag{211.6}
$$

Thus, for $0\le d\le1$, the conditions
$D_{\rm rest}\le d$ and $D_{ij}\le d+\tau$ supply the exact-$Q$
certificate $(V_u,0)$ with $u=(D_{ij}-d)_+$.

**Proof.** The two donor bounds ensure nonnegativity, including
$u=\tau$. The signed square $(-1,+1,+1,-1)$ has zero total and
zero projection onto each single coordinate. Its projection onto any
pair other than $\{i,j\}$ is zero: one varying coordinate is summed
out and its opposite signs cancel. All four rows have the same first
zero, so the changed correct reward always has label $n$.
This proves all stated invariant totals, unary data and other
cell-label rewards, even if $n$ is early and contributes to $W$.

At the exceptional $N$ pair, the four label-$n$ rewards become
$r_{00}-u,r_{01}+u,r_{10}+u,r_{11}-u$.
By (211.5), the first still attains its cell maximum, while the
other three do not exceed their unchanged competing maxima.
Exactly the first cell maximum falls by $u$.
In $O$, the merged first-cell label-$n$ reward is
$r_{00}+r_{01}$, unchanged; every competing reward there is unchanged.
The $10,11$ maxima stay fixed by the same inequalities. Hence its
whole support is unchanged, as are all other stopped supports.
Maximization gives (211.6). The proposed $u$ lies in $[0,\tau]$
and bounds every $N$ schedule by $W+d$. Its residual is zero, so
(211.4) holds. Ties, absent donors and $\tau=0$ are included.
No statement supplies jointly compatible slack for several switches.
$\square$

**Theorem 211.3 (An all-length attained interval with fixed unary data).**
For every $L\ge6$, choose actual addresses
$3\le a<b<c<z\le L$, parameters $d>0$, $s\ge2d$, and
$h_j\in[0,d/2]$ for each late $j\notin\{a,b,c,z\}$.
Set $A=0$, $T=s$, no early correct mass, and, for $e=1,2$, put
pair mass $s/2$ at each of

$$
w(\{e,a,b,z\}),\qquad w(\{e,a,c,z\}),\qquad w(\{e,b,z\}).
\tag{211.7}
$$

For $0\le u\le d$, define the remaining score $Y_u$ by

$$
\begin{array}{c|rrrrrrr}
Z&\{a,b,c,z\}&\{a,b,z\}&\{a,c,z\}&\{a,z\}&\{b,z\}&\{c,z\}&\{z\}\\\hline
C_{w(Z)}&d-u&u&u&s-u&d&d&s+d
\end{array}
\tag{211.8}
$$

and $C_{w(\{j\})}=h_j$ at every other late class. Then

$$
\Delta_O(Y_u)=d,\qquad\Delta_N(Y_u)=2d-u,\qquad W=4s,\qquad
K=6s+4d+\sum_jh_j.
\tag{211.9}
$$

The entire pair measure, $Q,W$, all correct unary data and every
individual stopped schedule support are fixed throughout this interval.
The totals are $\gamma_a=\gamma_z=s+d$, $\gamma_b=\gamma_c=d$
and $\gamma_j=h_j$ otherwise. Among input-family scores with these
fixed pair rows, terminal mass, correct totals and unary data, the
minimum in each catalog is $d$, attained by $Y_d$.
The family attains every $N$ cost in $[d,2d]$; this does not assert
that $2d$ is the maximum over that entire fixed-data class.

**Proof.** First consider $Y_d$ without the extra $h_j$ rows.
Its exact full-label $N$ cell maxima are as follows, with $e=1,2$.

| Schedule | Maxima in $00,01,10,11$ order |
| --- | --- |
| $(1,2)$ | $(0,3s/2,3s/2,s+d)$ |
| $(e,a)$ | $(s,s/2,s+d,3s/2)$ |
| $(e,b)$ | $(s,s/2,s,3s/2)$ |
| $(e,c)$ | $(s/2,s,s/2,2s)$ |
| $(e,z)$ | $(3s/2,0,3s/2,s)$ |
| $(a,b)$ | $(s,s,s,s+d)$ |
| $(a,c)$ | $(s,s,d,2s)$ |
| $(a,z)$ or $(b,z)$ | $(2s,0,s+d,s)$ |
| $(b,c)$ | $(0,2s,s,s+d)$ |
| $(c,z)$ | $(s,0,2s,s)$ |

Indeed zero collects all pair mass in each cell and $T$ in $11$;
an early label collects a subset of that pair mass; each late label
collects exactly its own displayed correct atoms. Substitution of
(211.7)–(211.8), using $s\ge2d$, gives the entries and shows that
no unqueried label is larger. Every row sums to at most $4s+d$.
The empty and each single core-coordinate support are $4s$.
Coordinates outside the six core addresses are constant one on these
atoms and reduce to shorter information types.

Extra sole-zero class $j$ has reward $h_j\le d/2\le s$ in the
$11$ cell of any core pair, already dominated there. At a core/extra
pair the old support is the corresponding singleton support $4s$,
and the new zero cell adds at most $h_j$. At two distinct extra
coordinates $j,k$ the support is $4s+h_j+h_k\le4s+d$.
Other extra labels are dominated in the positive cell. These arguments
also handle short schedules by full $N$ refinement. The stopped head
table $(1,2;1,2,a)$ earns $4s+d$, so $O\subseteq N$ proves both
costs $d$ at $u=d$, for all address gaps and all extra classes.

At $Y_0$, on $(b,c)$ the label-$a$ rewards are $(d,0,0,s)$,
and their competing maxima are $(0,2s,s,s+d)$.
The donor rows have weights $d,s$, and (211.5) gives $\tau=d$.
Theorem 211.2 changes $Y_0$ precisely into (211.8).
All other supports stay at their values for $Y_d$, while the
exceptional support is $4s+2d-u$. This proves (211.9) and every
claimed invariant, including both $u$ endpoints and $s=2d$.
For any competitor with the fixed data, the stopped head table still
earns $S+\gamma_a=4s+d$, proving the minimum $d$.
Taking every $h_j>0$ gives positive totals at every late address at
arbitrarily large lengths. If the displayed formulas are specialized
to $d=0$, they have $u=h_j=0$ and both costs zero by the same
cell bounds; at $s=0$ the score is zero. The nontrivial interval and
strict decrease require $d>0$. $\square$

The generic unary-preserving relocation is already
[209.12–209.15](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md).
The additional assertions here are the explicit donor/slack decrement,
invariance of every stopped schedule maximum and the attained interval.
For a precise boundary of that supplier, in class $a$ of (211.8) the
signed cut $1-X_b-X_c$ of (209.31), where $X_k$ is the zero indicator,
has desired value $(s+d)-d-d=s-d>0$.
The pair carrier conditioned on $x_a=0$ has only the two atoms with
exactly one of $b,c$ zero, so its positive-part support for that cut
is zero. With $E=0$ the other early carriers are dominated by it.
Thus that matching hypothesis does not already certify this fixed-unary
family. This is a condition failure, not exclusion from $E_N$.

The unchanged threshold placement is still the supplier 203.2, not a
new construction. For this example its cutoffs in class $a$ are
$a_{ab}=a_{ac}=s$, $a_{az}=0$: the length parameter in (203.10)
puts mass $s$ in $(b,c)=11$ and $d$ in $00$.
The full $N$ table $(b,c;a,0,0,z)$ then earns $4s+2d$.
For the full projection the core marginals are $(2s,2s,s,3s)$ and
its ordered directed masses are $(s,0,s,s,s,2s)$ in order
$ab,ac,az,bc,bz,cz$. Extra coordinates are always one under $\nu$;
their correct totals are at most $d/2$. Hence (203.6) has
$\kappa=d$, $\pi=d$, proving the matching upper bound $2d$.
At $d\le1$, $Y_d$ itself is a certificate, whereas this unchanged
threshold score with $\theta=0$ exceeds unit cost if $d>1/2$.
The factor-two failure is already owned by 204.9. The moment interfaces
remain those of 206.5–206.6; no new quotient-region coverage follows.

### 211.2 Actual retained-head marginals, strict packing and two funding regions

**Theorem 211.4 (Retained head credit on one actual measure).**
Let $y$ be an input-family score as in 211.1 and let
$d\ge\Delta_O(y)$. For every late $j$,

$$
\begin{aligned}
\nu_{10}(Z_j)&\ge(\gamma_j-c_2-d)_+,\\
\nu_{01}(Z_j)&\ge
 \max\{0,\gamma_j-E-d,\gamma_j-c_1-p_{00}-d\},\\
\nu(Z_j\setminus Z_i)&\ge(\gamma_j-E-d)_+\quad(3\le i<j),\\
t&\ge(\mu-d)_+.
\end{aligned}
\tag{211.10}
$$

Choose $m\ge2$ late addresses $J=\{j_1<\cdots<j_m\}$ with
$\gamma_j\ge g>E+d$, and define

$$
s=g-E-d>0,\qquad\bar c=c_1+(c_2-p_{00})_+,\qquad
 a=2s+\bar c,\qquad
\Psi=\frac{a^2}{a-s}=4s+\frac{\bar c^2}{s+\bar c}.
\tag{211.11}
$$

On this same actual $\nu$, every $j\in J$ has $m_j\ge a$ and
every $i<j$ in $J$ has $D_{ij}\ge s$. In particular $S\ge a+s$.

**Proof.** The following three legal stopped tables have exactly the
listed excesses, before any maximization:

$$
\begin{array}{c|c}
(1,j;1,j,0)&\gamma_j-c_2-\nu_{10}(Z_j)\\
(2,j;0,j,0)&\gamma_j-E-\nu_{01}(Z_j)\\
(2,j;2,j,0)&\gamma_j-c_1-p_{00}-\nu_{01}(Z_j).
\end{array}
\tag{211.12}
$$

The first keeps every class-1 correct and pair reward, including early
$00$, and loses the class-2 correct total and exactly the indicated
$10$ lift of pair mass. The second earns no early correct reward;
its pair loss is only the $01$ lift on $Z_j$. The third retains
class 2, loses every early-$00$ pair row as well as that same $01$
loss, and earns no class-1 correct reward. In all three, the whole
class-$j$ correct measure is in the second cell, and $T$ is retained.
All other correct labels earn zero. This proves the identities for
arbitrary suffixes and early allocations. Their excesses are at most
$d$, giving the first two lines of (211.10).
The late table $(i,j;0,j,0)$ has excess
$\gamma_j-E-\nu(Z_j\setminus Z_i)$; the head table
$(1,2;1,2,j_*)$, $\gamma_{j_*}=\mu$, has excess $\mu-t$.
These prove the remaining lines, using nonnegativity for positive parts.

For $j\in J$, the first lift is at least $s+c_1$, and the second
is at least $s+(c_2-p_{00})_+$. These are masses on disjoint early
lifts. Their sum is at most $\nu(Z_j)$, even with arbitrary positive
$\nu_{00}$. This gives $a$ without discarding any early-$00$ row.
Finally $Z_i$ and $Z_j\setminus Z_i$ are disjoint, proving
$S\ge a+s$. The identities are necessary conditions on actual
inputs; their conjunction alone is not a sufficient score or certificate
construction. $\square$

**Theorem 211.5 (Finite packing strictly below the critical stock).**
With (211.11), for each real $\tau$ in the range
$a+s\le\tau<\Psi$, define

$$
\begin{aligned}
\epsilon_\tau&=s-a+\frac{a^2}{\tau},\\
n_\tau&=\max\left\{1,
 \left\lceil\frac{2(\tau-a-s)}{\epsilon_\tau}\right\rceil\right\},\qquad
w_\tau=\frac{\tau-a-s}{n_\tau},\\
\Pi(s,a,\tau)&=n_\tau
 \left\lfloor\frac{s}{\epsilon_\tau-w_\tau}\right\rfloor.
\end{aligned}
\tag{211.13}
$$

Then

$$
S\le\tau\quad\Longrightarrow\quad m-1\le\Pi(s,a,\tau).
\tag{211.14}
$$

The same formula and proof apply with any weaker marginal lower bound
$a_0\in[2s,a]$, using $a_0$ in place of $a$ and its corresponding
range. Thus the first-credit bound $a_1=2s+c_1$ is included, rather
than a second packing result. The parameter $\tau$ has the units of
pair stock; it is not the normalized parameter of 208.4.

**Proof.** Delete the largest address of $J$. For each of the remaining
$m-1$ addresses let $A_i=Z_i^c$ and $r_i=\nu(A_i)$.
The outgoing directed bound to the deleted event and the marginal bound
give

$$
s\le r_i\le S-a\le\tau-a,\qquad
\nu(A_i\cap A_j)=r_i-D_{ij}\le r_i-s\quad(i<j).
\tag{211.15}
$$

The notation $A_i$ here denotes an event, not an event-row score.
Partition the interval $[s,\tau-a]$ into $n_\tau$ bins of width
$w_\tau$, assigning every shared endpoint to one bin. If the interval
has zero length, use one singleton bin. In a bin with lower endpoint
$r$ and $N>0$ events, put $X=\sum_i\mathbf1_{A_i}$.
All integrals use the one actual measure $\nu$, so

$$
\int X\ge Nr,\qquad
\int X^2\le N(r+w_\tau)+N(N-1)(r+w_\tau-s)
          =N^2(r+w_\tau-s)+Ns.
\tag{211.16}
$$

Cauchy–Schwarz, with $S\le\tau$ and $S>0$, gives
$\int X^2\ge N^2r^2/\tau$. Therefore
$N(s-r-w_\tau+r^2/\tau)\le s$.
Here $a\ge2s$ implies $\Psi\le2a$, and $\tau<\Psi$ gives
$\epsilon_\tau>0$ and $\tau-a<\tau/2$.
The function $s-r+r^2/\tau$ decreases on $[s,\tau-a]$;
its value at the right endpoint is $\epsilon_\tau$.
The choice of $n_\tau$ ensures $0\le w_\tau\le\epsilon_\tau/2$.
Each bin consequently contains at most
$\lfloor s/(\epsilon_\tau-w_\tau)\rfloor$ events. Summing proves
(211.14) for arbitrary real weights. Only numerical marginal masses
have been binned; the original address order has not changed.
The argument uses only $m_j\ge a$ and $D_{ij}\ge s$, so it also
proves the stated weaker-bound substitution.

At $\tau=a+s$ the denominator is positive and the one zero-width
bin is valid. At $\tau=\Psi$ the positive gap vanishes and no finite
bound is asserted. Indeed a product measure of mass $\Psi$ with
independent zero probability $(a-s)/a$ has every marginal $a$ and
every directed mass $s$, for arbitrarily many coordinates. The next
result also supplies actual full scores at this equality. The product
measure alone is not a normalized acquisition. At $\bar c=0$,
substitution $\tau=s\tau_{208}$ reduces (211.13)–(211.14) to 208.4;
that case and its $4s$ threshold retain their existing ownership.
$\square$

**Theorem 211.6 (One unrestricted-placement asymptotic minimum with positive credit).**
Fix $s>0$, $c>0$ and $0\le d\le s^2/(s+c)$. For each integer
$m\ge1$, set $L=m+2$, and let $S_m^O,S_m^N$ be the least pair
stock in the input family subject, respectively, to $\Delta_O\le d$
and $\Delta_N\le d$, with fixed data

$$
c_1=c,\quad c_2=0,\quad\gamma_j=s+c+d\ (j\ge3),\qquad T=s+c.
\tag{211.17}
$$

The competitor class allows every correct suffix, every pair projection,
and every early split including $00$. Both minima are attained, and

$$
S_m^O\le S_m^N\le S_*:=\frac{(2s+c)^2}{s+c},\qquad
\lim_{m\to\infty}S_m^O=\lim_{m\to\infty}S_m^N=S_*.
\tag{211.18}
$$

This is one asymptotic minimum, not an exact finite-$m$ formula or a
minimum over arbitrary full or signed representatives.

**Proof.** For every competitor in the $O$ class, 211.4 has
$g=s+c+d$, $E=c$, $\bar c=c$ and $a=2s+c$.
For every fixed $\tau<S_*$, the elementary $S\ge a+s$ bound
rules out $S\le\tau$ when $\tau<a+s$ and $m\ge2$.
Otherwise 211.5 bounds $m-1$ by a finite number independent of $m$.
Thus all sufficiently large $m$ force $S_m^O>\tau$.

For the common upper witness apply 207.5 with its parameters
$s_{207}=s+c$, $d_{207}=d$, retained early masses $(c,0)$,
$S=S_*$ and $t=s+c$. Its inequalities become
$c\le s+c$ and $s^2\ge(s+c)d$, with $d\le s+c$ automatic.
Explicitly let $M=2s+c$, $q=(s+c)/M$, and put

$$
\nu(x)=S_*\prod_{j=3}^Lq^{\mathbf1_{x_j=0}}
                             (1-q)^{\mathbf1_{x_j=1}},\qquad
P_{01x}=\frac{s}{M}\nu(x),\quad
P_{10x}=\frac{s+c}{M}\nu(x).
\tag{211.19}
$$

Put early correct mass $c$ at $w(\{1,3,\ldots,L\})$;
for each late $j$ put $s$ at $w(\{j\})$ and $c+d$ at
$w(\{j,j+1,\ldots,L\})$, adding coincidences, and take $T=s+c$.
This is exactly the biased supplier (207.12)–(207.13) under the
specified parameter map. Its complete support proof gives both costs
at most $d$, and the stopped head earns excess
$\gamma_j-T=d$, proving equality. It also gives
$m_j=2s+c$, $D_{ij}=s$ and $S=S_*$ for every $m$.

For fixed $m$, restrict each feasible set to $S\le S_*$.
It is a nonempty closed bounded set of finitely many nonnegative
coefficients: correct totals and $T$ are fixed, and all complete-table
inequalities are closed. The continuous stock function attains a minimum
there, which is also the unrestricted minimum because a feasible point
with stock $S_*$ exists. Since $O\subseteq N$, the minima are ordered
as in (211.18). The preceding lower bounds and the common upper bound
prove both limits. The endpoints $d=0$ and $d=s^2/(s+c)$ are included.
The zero-credit limit theorem is already 208.3 and is not counted again;
209.3 and 209.5 instead fix the entire carrier. $\square$

**Corollary 211.7 (A guarded biased-supplier funding region).**
Suppose the actual input has $\Delta_O(y)\le d\le1$, $\mu\ge2$,
and a selected set satisfying (211.11). Define

$$
h=\mu-1,\qquad c_*=\min\{E,h-\sqrt h\},\qquad
U=\frac{(2h-c_*)^2}{h}.
\tag{211.20}
$$

If either $U<a+s$, or

$$
a+s\le U<\Psi,\qquad m-1>\Pi(s,a,U),
\tag{211.21}
$$

then $S>U$ and there is an exact-$Q$, same-$W$ score $V$ with
$\Delta_N(V)\le1$. Its certificate has $\theta=0$.

**Proof.** If $S\le U$, 211.4 contradicts the first alternative
and 211.5 contradicts the second. Independently the head bound gives
$t\ge\mu-d\ge h$. Since $h\ge1$,
$0\le c_*\le h-\sqrt h\le h$. Split $c_*$ into
$0\le c_a^*\le c_a$, for example $c_a^*=c_*c_a/E$ if $E>0$,
and take both zero when $E=0$.
Use 207.5 with $s_{207}=h$, $d_{207}=1$ and these retained masses.
Its conditions are $1\le h$, $\gamma_j\le h+1$, $c_*\le h$,
$(h-c_*)^2\ge h$, $S\ge U$ and $t\ge h$, all verified above.

For clarity its core has product zero probability $h/(2h-c_*)$,
stock $U$, early lifts $(h-c_a^*)/(2h-c_*)$, early correct mass
$c_a^*$ at $w(\{a,3,\ldots,L\})$, late singleton weight
$\min(\gamma_j,h-c_*)$, late absorbing-suffix weight
$(\gamma_j-h+c_*)_+$, and terminal mass $h$.
Complete the totals by adding $c_a-c_a^*$ at those early correct
words, pair mass $S-U$ at $w(\{1,3,\ldots,L\})$, and terminal
mass $t-h$. Each addition is collected by the anchor, so it increases
any table by at most the same anchor increase. This is the completion
already proved in 207.5; it preserves every class total, $S,t,Q,W$.
The entire resulting score has excess at most one and zero residual.
At $\mu=2$, $h=1,c_*=0$, so no division or square-root endpoint
is exceptional. The stock/count conditions are sufficient hypotheses;
no assertion makes them necessary for $E_N$ or automatically true
for every unit-$O$ input. $\square$

**Corollary 211.8 (A separately guarded fair-supplier funding region).**
Under the same input hypotheses $\Delta_O(y)\le d\le1$, $\mu\ge2$
and $s=g-E-d>0$ on $m\ge2$ selected classes, put

$$
a_1=2s+c_1,\qquad\Psi_1=\frac{a_1^2}{a_1-s},\qquad
\tau_f=4\mu-5+d-E.
\tag{211.22}
$$

If either $\tau_f<a_1+s$, or

$$
a_1+s\le\tau_f<\Psi_1,\qquad m-1>\Pi(s,a_1,\tau_f),
\tag{211.23}
$$

then $W>5(\mu-1)$, and a full score $V$ has
$\Delta_N(V)=\Delta_O(V)=1$ and
$\sigma_H(Q(y)-Q(V))=0$. It is a certificate with $\theta=0$,
although its early correct totals need not equal the input's.

**Proof.** The bound $a_1\le a$ permits the weaker-bound substitution
in 211.5. If $W\le5(\mu-1)$, then $t\ge\mu-d$ implies
$S\le4\mu-5+d-E=\tau_f$. This contradicts the corresponding
stock bound in either alternative, including a negative $\tau_f$.
Put $h=\mu-1\ge1$. Apply 203.6 with
$\kappa_f=2h$, terminal $\tau=W-4h>h$, the original late totals
and zero early correct mass. The second-largest late total is at most
$\mu=h+1\le2h$, so every hypothesis of that supplier holds.
Its actual coefficients are

$$
C^V_{1^{j-1}0v}=\frac{\gamma_j}{2^{L-j}},\qquad
P^V_{01x}=P^V_{10x}=\frac{2h}{2^{L-2}},\qquad T_V=W-4h,\quad A^V=0.
\tag{211.24}
$$

The pair stock is $4h$, the anchor is $W$ and the total quotient
mass $K$ is unchanged. Formula (203.28) gives the exact cost
$\max(0,\mu-h,\mu-T_V)=1$. Only the early quotient coordinates
were removed, so

$$
F_{Q(y)-Q(V)}(b,e)=c_1(b_1-1)+c_2(b_2-1)\le0.
\tag{211.25}
$$

Equality holds, for example, at the hull point
$(1,1,1,1/4,\ldots,1/4;1/4)$ (also when $L=3$, with no later
coordinates). Thus the support charge is exactly zero. This is one
complete score with one budget, not an addition of separately funded
cells. The construction is the old fair supplier, and the implication
from the actual input to its affordability is the stated restricted
consequence of retained credit. $\square$

To compare the strict parameters with 208.5, write $k=c_1/s$ and
$t_0=\tau_f/s$. Then
$\Phi(k)=(2+k)^2/(1+k)$ and (211.23) reads
$3+k\le t_0<\Phi(k)$ with

$$
\begin{aligned}
\eta&=\frac{(2+k)^2}{t_0}-1-k,\qquad
n=\max\{1,\lceil2(t_0-3-k)/\eta\rceil\},\\
w&=(t_0-3-k)/n,\qquad
\Pi(s,a_1,\tau_f)=n\lfloor1/(\eta-w)\rfloor.
\end{aligned}
\tag{211.26}
$$

The upper strict condition alone is equivalently
$4(\mu-g)+3E+5d-5<c_1^2/(g-c_2-d)$.
It does not remove the lower alternative or finite-count condition.
It can include the old critical equality
$4(\mu-g)+3E+5d=5$ when $c_1>0$ and the stated count holds;
it does not include the new critical equality $t_0=\Phi(k)$.
The biased and fair funding regions are separate sufficient domains,
with different retained coordinates; neither is advertised as universal
or as disjoint from the complete old signed and convex closure.

For exact nonempty examples, $s=c=1,d=1/2$ in 211.6 gives $S_*=9/2$.
At $\tau=17/4$, (211.13) has
$\epsilon_\tau=2/17,n_\tau=5,w_\tau=1/20,\Pi=70$;
thus $m\ge72$ forces stock greater than $17/4$.
For biased funding, take $c_1=2,c_2=0,\mu=g=5,d=7/8$ and
$m\ge116$ maximum classes. Then $s=17/8,a=25/4$,
$\Psi=625/66,h=4,c_*=2,U=9$ and
$\epsilon_U=31/144,n_U=6,w_U=5/48,\Pi=114$.
The actual family (211.19) has stock $625/66$, terminal $33/8$
and both costs $7/8$, so the conditions are not empty.
For fair funding take $c_1=4/3,c_2=0,d=1/5,\mu=g=43/15$ and
at least six maximum classes. Now $s=4/3,k=1,t_0=4$,
$\Phi(k)=9/2$, and (211.26) gives $\Pi=4$.
The product witness has $S=6,T=8/3,W=10$ and both costs $1/5$;
its fair comparison has $T_V=38/15$ and both costs one.
These are applications and endpoint illustrations, not additional
minimum theorems or amplitude classifications.

### 211.3 A fixed menu of actual joint measures

**Definition 211.9 (The exact menu class).** Let $m\ge3$,
$L=m+3$, $J=\{3,\ldots,L-1\}$, $z=L$, $d\ge0$ and $s>4d$.
Set $g=s+d$. For every unordered pair $\{i,j\}\subset J$ define
$q_{ij}=(\beta,K)$ by

$$
\beta_i=\beta_j=\beta_z=g,\qquad
\beta_k=0\ (k\notin\{i,j,z\}),\qquad K=7s+4d.
\tag{211.27}
$$

An eligible representative of $q_{ij}$ is an input-family score
$V$ with exact $Q(V)=q_{ij}$ and $\Delta_N(V)\le d$.
Because $A=0$, these conditions force zero early correct mass,
exactly the three displayed late totals, and $S+T=4s+d$.
Correct suffixes and the early split, including $00$, are otherwise
free. The pair/terminal split is also free.

A menu is a finite list of fixed nonnegative measures on the entire
late cube. It covers $\{i,j\}$ if an eligible representative has
actual projection $\nu(x)=P_{00x}+P_{01x}+P_{10x}$ equal to one
entry, as a measure on all late coordinates. The representative and
its correct suffixes may depend on $\{i,j\}$. The entry itself is
fixed before that pair is selected. A new mixture, permutation or
formula-generated projection must be counted as its actual resulting
measure unless it already equals an entry. Let $\mathcal M(m,s,d)$
be the least menu size covering every pair in $J$.
Write $C(m,3,2)$ for the least number of three-element subsets of
$J$ containing every two-element subset.

**Theorem 211.10 (The fixed-measure menu equals the triple covering number).**
In exactly the class of 211.9,

$$
\mathcal M(m,s,d)=C(m,3,2)
 \ge\left\lceil\frac{m(m-1)}6\right\rceil.
\tag{211.28}
$$

For $m=3^r$, every integer $r\ge1$, equality with $m(m-1)/6$
is attained. Every quotient (211.27) separately has an actual score
with both complete costs $d$; when $d\le1$ it is a unit-$O$
quotient with an $E_N$ certificate of charge zero.
The simultaneous menu requirement is the assertion here, not a new
individual membership result.

**Proof.** For any eligible representative, $\Delta_O\le\Delta_N\le d$.
The actual guards of 203.2 and 208.2, equivalently (211.10) with
$E=0$, give for every active $k$ and every late $a<k$

$$
\nu(Z_k)\ge2s,\qquad \nu(Z_k\setminus Z_a)\ge s,\qquad
T\ge g-d=s,\qquad S\le3s+d.
\tag{211.29}
$$

These are full stopped-table lower bounds with no suffix or early-$00$
restriction. Fix one menu entry $\nu$, and call $k\in J$ eligible
for this entry if it occurs in any pair covered by that entry.
For such $k$, its representative also has active terminal $z$;
hence $D_{kz}\ge s$. With $A_k=Z_k^c$ and $a_k=\nu(A_k)$,

$$
s\le a_k\le S-2s\le s+d,\qquad
\nu(A_a\cap A_b)=a_a-D_{ab}\le a_a-s
 \quad(a<b\text{ eligible}).
\tag{211.30}
$$

For the second assertion it suffices to use a representative making
$b$ active: (211.29) permits every earlier address $a$, whether active
in that representative or not. All these inequalities coexist because
the full measure $\nu$ is exactly the same across representatives.
There is no assumption that their correct placements agree.

Four eligible indices $k_1<k_2<k_3<k_4$ are impossible. The pointwise
inequality $\mathbf1_{\cup A_k}\ge\sum\mathbf1_{A_k}
-\sum_{k<l}\mathbf1_{A_k\cap A_l}$ holds because, at a point in
$r_0$ of these four events, its right side is
$r_0-\binom{r_0}2\le\mathbf1_{r_0>0}$.
Integration and (211.30) give

$$
\begin{aligned}
S&\ge\nu\left(\bigcup_{r=1}^4A_{k_r}\right)\\
 &\ge\sum_{r=1}^4a_{k_r}
           -\sum_{r<t}(a_{k_r}-s)\\
 &=6s-2a_{k_1}-a_{k_2}+a_{k_4}
 \ge4s-3d.
\end{aligned}
\tag{211.31}
$$

Together with $S\le3s+d$, this forces $s\le4d$, a contradiction.
Thus each entry covers pairs only within one set of at most three
eligible indices. Extend that set to a triple if necessary, ignoring
entries covering no pair. A covering menu therefore gives a triple
covering, proving $\mathcal M\ge C(m,3,2)$.

For the reverse inequality choose any triple covering. For each block
$F\subset J$ with $|F|=3$, make one fixed late measure

$$
\nu_F=s\sum_{k\in F}\delta_{(F\setminus\{k\})\cup\{z\}}
                       +d\delta_\varnothing,
\tag{211.32}
$$

where atoms are described by zero sets and every unlisted late bit is
one. Its stock is $3s+d$. For a requested $\{i,j\}\subset F$,
lift each atom equally to prefixes $01,10$, set $T=s$, and put

$$
\begin{aligned}
C_{w(\{n,z\})}&\mathrel{+}=s,\qquad
C_{w(\{n,z\}\cup\{k\in F:k>n\})}\mathrel{+}=d
                         &&(n=i,j),\\
C_{w(\{z\})}&=g.
\end{aligned}
\tag{211.33}
$$

There is no early correct mass. This is the three-coordinate subset
measure $\mathcal L_3(s)$ of 201.2/207.4, with terminal zero, plus
the empty-set stock $d$, and the threshold words of 203.2.
The parameter map is $a_{nk}=s$ for $n<k$ in $F$ and
$a_{nz}=0$, so a class of mass $s+d$ splits into its singleton
part of length $s$ and its absorbing part of length $d$ exactly as
in (211.33). No new realization supplier is required.
It has $Q=q_{ij}$ and $W=4s+d$.

Here is a complete support bound for this specialization, including
all unqueried labels. At the head pair the exact maxima are
$(0,(3s+d)/2,(3s+d)/2,g)$, totaling $W+d$.
At an early/$k$ pair, $k\in F$, the early-zero maxima sum to
$(3s+d)/2$; the $10$ maximum is at most $g$; and the $11$
maximum is $(3s+d)/2$, which dominates every correct reward since
$s>d$. At early/$z$, the first two maxima again sum to
$(3s+d)/2$, the $10$ maximum is $3s/2$, and the $11$ maximum is
$s+d/2$, so its support is $W$. Here $3s/2\ge g$ follows from
$s>4d$.

At two coordinates of $F$, the four maxima are bounded by
$(s,s,g,g)$. The pair baselines are $(s,s,s,d)$ and the terminal
adds $s$ in $11$. Correct $00$ rewards are absorbing pieces at most
$d\le s$; $01$ rewards are at most $s$; the queried or intermediate
$10$ rewards are at most $g$; earlier and later $11$ rewards are
also at most $g$. On $(k,z)$ with $k\in F$, the bounds are
$(2s,0,g,g)$: all correct words have $z=0$, the terminal class
is in $10$, and $T+d=g$ covers $11$. Each bound sums to at most
$W+d$. Early labels collect only subsets of the pair baseline in
these late pairs. Unused coordinates are constant one on every scored
word and give shorter observations; short $N$ rules refine into pairs.
This proves the complete $N$ bound. The stopped head table
$(1,2;1,2,i)$ attains $W+d$, so both complete costs equal $d$.
Thus one entry serves every pair of its block, proving
$\mathcal M\le C(m,3,2)$.

A triple contains three pairs, so counting pairs gives (211.28).
For $m=3^r$, identify $J$ bijectively with the vector space
$\mathbb F_3^r$. The affine lines
$\{x,x+v,x+2v\}$, $v\ne0$, are triples; each pair determines
exactly one of them. Therefore they partition the $\binom m2$
pairs into groups of three and give exactly $m(m-1)/6$ blocks.
Using (211.32) for these blocks attains the menu bound.
The covering definition, pair count and finite-geometry method are
classical; see Gordon, Kuperberg, Patashnik and Spencer,
[*Asymptotically optimal covering designs*, introduction and §2](https://arxiv.org/pdf/math/9511224v1).
No asymptotic design theorem is used. $\square$

The theorem includes $d=0$, still requiring $s>0$; it asserts nothing
at $s=4d$ or below. For example $m=9,s=5,d=1$ gives exactly twelve
fixed measures for the thirty-six placements, each profile having
$W=21,K=39$ and both costs one. This count restricts a method of
choosing proof measures. It is not a lower bound on requests, seeds,
computation or source information. Allowing arbitrary full scores,
late pair rows, signed residuals, nonzero zero-cost cores or new
mixture projections leaves the stated menu class. Every displayed
quotient is already certified; a smaller menu's failure cannot prove
unrestricted $E_N$ nonmembership.

### 211.4 Full-output positive linear selectors

**Definition 211.11 (Balanced stock and an exact positive selector).**
For $L\ge4$, a balanced stock is any full nonnegative score $Z$ with
$Q(Z)=(0,\ldots,0;3)$. Thus the aggregate $A$ and $C$ masses agree
separately in each first-zero class. No support, early-credit, pair-row
or terminal restriction is imposed. For $j=3,4$, let $U_j$ be any
pure correct score of total one on $\Omega_j$, with arbitrary suffixes.
Write $e_j$ for the $j$th unit vector in $\mathbb R^L$ and put

$$
\mathcal Q_L^+=\{(\gamma,K):\gamma\in\mathbb R_+^L,
                                      \ K\ge\sum_j\gamma_j\},\qquad
q_j=(e_j,4).
\tag{211.34}
$$

A positive linear exact-$Q$ selector is a linear map
$\mathcal S:\mathbb R^{L+1}\to\mathbb R^{3(2^L-1)+1}$ with
$\mathcal S(q)\ge0$ and $Q(\mathcal S(q))=q$ for every
$q\in\mathcal Q_L^+$. The output may use arbitrary independent
$A,C,P,T$ on every word. Positivity is on this entire parameter cone.
An affine selector has the same properties and may initially have a
constant offset.

**Theorem 211.12 (Two full-row tradeoffs and one sharp maximum).**
For every balanced $Z$ and every $U_3,U_4$ as above, define
$\delta_j=\Delta_N(Z+U_j)$. Then both

$$
\delta_3+\delta_4\ge\frac12,\qquad
3\delta_3+\delta_4\ge1.
\tag{211.35}
$$

The common sharp conclusion is

$$
\inf_{Z,U_3,U_4}\max(\delta_3,\delta_4)=\frac14,
\tag{211.36}
$$

and it is attained for every $L\ge4$.
For every positive linear exact selector, (211.35) holds with
$\delta_j=\Delta_N(\mathcal S(q_j))$, and the infimum of this
maximum over selectors is the same attained $1/4$.
Every positive affine exact selector on the whole cone has zero offset
and is included.

**Proof.** For a complete table $D$ put
$a_D(V)=V\cdot(z_D-r)$. Consider two lists of four legal $N$ tables:

$$
\begin{array}{c|c|c}
 &\mathcal W&\mathcal F\\\hline
1&(1,3;1,0,3,0)&(1,2;1,1,2,3)\\
2&(2,3;2,0,3,0)&(1,3;1,1,3,0)\\
3&(1,2;1,1,2,4)&(2,3;2,0,3,0)\\
4&(3,4;0,0,4,0)&(3,4;0,0,4,0).
\end{array}
\tag{211.37}
$$

Define $J_{\mathcal W}=\sum_{D\in\mathcal W}a_D$ and
$J_{\mathcal F}=\sum_{D\in\mathcal F}a_D$ as linear functionals
on the full score space. Lower bounds for their coefficients on every
independent row are

| First zero or row | $J_{\mathcal W}$ coefficients $(A,C,P)$ | $J_{\mathcal F}$ coefficients $(A,C,P)$ |
| --- | --- | --- |
| $1$ | $(1,-3,-1)$ | $(1,-2,-1)$ |
| $2$ | $(1,-3,-1)$ | $(1,-3,-1)$ |
| $3$ | $(-3,2,-1)$ | $(-3,3,0)$ |
| $4$ | $(-2,2,0)$ | $(-2,1,-1)$ |
| $n\ge5$ | $(-1,0,-1)$ | $(-1,0,-1)$ |
| positive $T$ | $-1$ | $-1$ |

To verify this all-word table, if $N_0,N_n$ count the four outputs
equal to zero and to the actual first zero, respectively, the three
coefficients are
$N_0-4\mathbf1_{n\ge3}$,
$N_n-4\mathbf1_{n\le2}$, and $N_0+N_n-4$.
For $\mathcal W$ on either early class, at least one table is correct,
at least one outputs zero, and at most one outputs outside $\{0,n\}$.
Indeed the head table is correct; if bit 3 is zero the last table is
zero, whereas if bit 3 is one both early/3 tables are zero.
For $\mathcal F$ on class 1, its first two tables are correct;
if the third is wrong then bit 3 is zero and the fourth is zero,
while if the fourth is wrong then bit 3 is one and the third is zero.
On class 2 the outputs are $(2,3,2,0)$ when bit 3 is zero;
when it is one they are $(2,0,0,4)$ or $(2,0,0,0)$.
These facts prove the early bounds including every multiple-zero prefix.

For class 3 the outputs are $(3,3,4,0)$ for $\mathcal W$ and
$(3,3,3,0)$ for $\mathcal F$. For class 4 they are
$(0,0,4,4)$ and $(3,0,0,4)$ respectively.
For later classes and the positive word they are $(0,0,4,0)$ and
$(3,0,0,0)$ respectively. This verifies every remaining coefficient;
bits beyond four are unrestricted, not deleted.
In each list, the $A$ lower coefficient plus the $C$ lower coefficient
is at least $-2$ in every class, and every $P,T$ coefficient is at
least $-1$. If $t_n$ is the common aggregate $A,C$ mass of balanced
$Z$ in class $n$, integration gives

$$
J_{\mathcal W}(Z)\ge-2\sum_nt_n-\sum_wP_w-T=-K_Z=-3,\qquad
J_{\mathcal F}(Z)\ge-3.
\tag{211.38}
$$

This uses classwise equality of totals; it never pairs individual $A$
and $C$ atoms or restricts their supports.

The first two $\mathcal W$ tables collect every unit of $U_3$;
the last two collect every unit of $U_4$. Their correct anchors are
zero. Hence

$$
2\delta_3+2\delta_4\ge4+J_{\mathcal W}(Z)\ge1.
$$

The first three $\mathcal F$ tables collect all of $U_3$ and the
last collects all of $U_4$, giving
$3\delta_3+\delta_4\ge4+J_{\mathcal F}(Z)\ge1$.
Both are comparisons of whole tables integrated against the same stock.
They prove (211.35), and either implies the maximum is at least $1/4$.

For simultaneous sharpness, put pair mass $3/8$ at each
$w(\{a,3\}),w(\{a,4\}),w(\{a,3,4\})$, $a=1,2$, and
$T=3/4$, obtaining balanced $Z$ of mass three. Choose $U_3$ as
unit correct mass at $w(\{3,4\})$ and $U_4$ at $w(\{4\})$.
All later bits are one. Zero collects the whole stock in every
schedule, so its total baseline is three. Early labels collect only
subsets of this pair stock; the only possible excess is the unit
correct reward in its own cell. For the six pairs on coordinates
$1,2,3,4$, the zero-label stock in that target cell is

$$
\begin{array}{c|rrrrrr}
 &12&13&14&23&24&34\\\hline
U_3&3/4&3/4&3/4&3/4&3/4&3/4\\
U_4&3/4&9/8&3/4&9/8&3/4&3/4.
\end{array}
\tag{211.39}
$$

These entries follow by counting the six specified pair atoms and
adding $T$ only in the positive cell. Thus every such support is at
most $3+(1-3/4)=13/4$. A schedule involving a later constant-one
coordinate reduces to a singleton or empty observation; its target
cell contains a refined cell listed above and cannot have smaller
baseline. This also controls all short $N$ functions and hence all
short $O$ functions. The stopped head table $(1,2;1,2,j)$ attains
$13/4$ for the respective $j$. Consequently both complete costs of
each sharp score are $1/4$, proving attained (211.36) and simultaneous
equality in both tradeoffs.

It remains to connect arbitrary selectors to these full scores.
For every nonnegative score the exact identity

$$
K-\sum_j\beta_j=2\sum_wA_w+\sum_wP_w+T
\tag{211.40}
$$

holds. Let $s_0=(0,\ldots,0;1)$ and $c_j^0=(e_j,1)$ be the
stock and correct generators of $\mathcal Q_L^+$.
For any selector, $U_j=\mathcal S(c_j^0)$ has $K=\sum\beta=1$;
(211.40) forces $A=P=T=0$ and then forces pure correct mass one
on class $j$. Set $Z_1=\mathcal S(s_0)$.
It has classwise balanced $A,C$ and $K_{Z_1}=1$.
The stock in (211.35) is exactly $Z=3Z_1$, and

$$
\mathcal S(q_j)=U_j+3Z_1=U_j+Z.
\tag{211.41}
$$

This factor three is essential: a mass-one stock bound must be
multiplied by three before applying the unit correct rays of mass four.
Linearity now proves both selector tradeoffs.
Conversely take the sharp $Z,U_3,U_4$ above, choose any pure unit
correct $U_j$ on every other class, and define

$$
\mathcal S(\gamma,K)=\sum_j\gamma_jU_j
                     +\frac{K-\sum_j\gamma_j}{3}\,Z.
\tag{211.42}
$$

It is positive and exact on the whole cone, so it attains the same
sharp maximum. Finally an affine selector's offset is its value at
zero. That score is nonnegative and has $K=0$, which forces all its
coordinates zero. Its linear part is therefore the entire selector.
This argument uses the closed whole cone, including its origin.
$\square$

**Corollary 211.13 (Scaled actual zero-cost inputs defeat only this selector method).**
For $j=3,4$ let $Y_j$ have unit correct mass at $w(\{j\})$,
unit pair mass at each of $w(\{1,j\}),w(\{2,j\})$, and $T=1$.
These are the existing zero-cost rays of 198.7 and 204.4, with
$Q(Y_j)=q_j$ and $\Delta_N(Y_j)=\Delta_O(Y_j)=0$.
For every selector in 211.11 there is one $j\in\{3,4\}$ such
that, for every real $r_0>4$,

$$
\Delta_O(r_0Y_j)=0,\qquad
\Delta_N(\mathcal S(Q(r_0Y_j)))\ge r_0/4>1.
\tag{211.43}
$$

**Proof.** Reuse the zero-ray supplier with its sole late address
mapped to $j$, early addresses fixed as $1,2$, and all other bits one.
Its support argument keeps every competitor: a table collecting the
correct word leaves at least one of the three coordinates $1,2,j$
unqueried; flipping that coordinate produces one of the three other
scored words with the same acquired information but a lost reward.
If it does not collect the correct word, that reward is already lost.
Thus support is at most three and the anchor attains three in both
catalogs. This is the stated supplier applied at the new address,
not a new zero-core result. Choose $j$ from 211.12's maximum bound.
Linearity and positive homogeneity of complete support prove (211.43).
The selected score has exact quotient and hence zero residual, but its
cost exceeds one for every permitted $\theta\ge0$.

Each actual input $r_0Y_j$ nevertheless has its own exact zero-cost
$N$ certificate $V=r_0Y_j$, with either $\theta=0$ or $\theta=1$.
For every $b\in H_N$ and every full feasible $\lambda$,
$F_{Q(r_0Y_j)}(b)\le r_0Y_j\cdot G_N\lambda\le0$.
It cannot be the strict separator required by 199.3.
Nonlinear or piecewise-linear quotient choices, choices depending on
the entire input score, maps not factoring through $Q$, signed residuals
and nonzero zero-cost cores all remain available. There is no assertion
at $L=3$ and no exclusion of those alternative methods. $\square$

### 211.5 Suppliers, original resources and the unresolved universal relation

**Definition 211.14 (Scope of the ordinary results and their source interface).**
The four groups above concern, respectively, a safe one-pair operation
with a fixed-data interval, necessary actual-input packing and conditional
funding, a fixed-single-measure menu, and a full-output positive linear
selector obstruction. Their proofs are repository-derived ordinary
mathematics. The statements of 209 and 210 are also ordinary theory;
none is being used as Lean or kernel evidence.

The reused mathematical suppliers have specific roles. The threshold
words and their complete non-$11$ bound are 203.2–203.3; 204.9 already
owns failure of an unchanged threshold transfer. The moment applications
206.5–206.6 and the matching relation 209.12–209.15 already own the
general unary/pair distinction and unary-preserving relocation.
The actual marginal, directed and triple guards and the zero-credit
packing/minimum mechanism are 208.2–208.5. Fair and biased upper
constructions are 203.6 and 207.5–207.6, with parameter maps given
above. Fixed-carrier minima 209.3/209.5 have a different competitor
class from 211.6. The menu upper witness uses the existing subset
and threshold construction; the added relation is simultaneous coverage
by one fixed entry per requested placement. The zero rays are 198.7
and 204.4, and 205.5 already supplies a four-table all-row technique.
Here the selector statements impose one balanced stock across different
inputs and permit arbitrary full output scores. Their sharp $1/4$
conclusion is counted once, with both tradeoffs retained.

The complete four-late inequality, cylinder-mass minimum, finite-slot
selectors, protected heavy/light minimum and five-coordinate threshold
in 210 remain their own results. No consequence of those statements,
no generic convex alternative, and no previously covered profile is
presented as newly uncovered here. In particular the menu does not
relax its strict $s>4d$ premise using a five-slot construction, and a
selector or threshold method failure does not exclude the old convex,
signed or nonzero zero-cost certificate closure. The scope of the
source and novelty comparison is these cited owner bodies and the
following primary passages, without a worldwide originality or priority
claim.

Gordon–Kuperberg–Patashnik–Spencer's covering definition, elementary
count and finite-geometry constructions supply the classical context
for (211.28), not a new design theorem. Robert Šámal,
[*Cubical coloring — fractional covering by cuts and semidefinite
programming*, equations (2)–(3), Lemma 2.1 and Corollary 2.2](https://arxiv.org/pdf/0911.2589v3),
gives fractional-cut optimization and the common-measure double count.
The directed guards and retained-head terms here come from actual
complete tables; undirected cut counting does not assert their
sufficiency. The finite alternative and zero-cost meanings remain
199.3–199.6, using the expository finite Farkas framework in Volker
Kaibel, [*Basic Polyhedral Theory*, Theorem 1(ii)](https://arxiv.org/pdf/1001.2161v1).
That framework proves the owned equivalence, not the unresolved inclusion.

Kaniewski, Lee and de Wolf,
[*Query complexity in expectation*, Definition 8 and Theorem 9](https://arxiv.org/pdf/1411.7280v1),
characterize scalar nonnegative expected output with the maximum path
length among supported deterministic trees. Their normalization of
coefficients followed by output rescaling supplies neither normalized
probability-vector rows nor increasing first-zero stopping.
Blackwell, [*Comparison of Experiments*, summary and §5, Theorem 6](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf),
uses common stochastic-kernel conditions; the converse stated as proved
in that paper's summary is restricted to dichotomies. No hard-two
conversion follows from the general comparison analogy.
Leskelä, [*Stochastic relations of random variables and processes*,
Theorem 2.5 and Remark 2.7](https://arxiv.org/pdf/0806.3562v1),
requires the full set of closed-relation coupling inequalities (finite
sets in the countable case). Separately feasible local capacities do
not supply those joint hypotheses. None of these passages is a missing
source/acquisition bridge for the scores in this section.

Explicitly the actual source remains

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
 \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\qquad
N(r,g)=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},
\tag{211.44}
$$

where $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$ and $p_i$ are the
increasing primes. Every finite pattern on arbitrary finite prime
addresses, including every multiple-zero word, has actual witnesses
by Boundaries 35.2. No probability law on the source labels is added.
The full carrier is $\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$,
with each block a copy of $(0,1)$ and the disjoint-union Borel sigma
algebra. The unchanged consumer immediately returns unknown on $B_j$
and proposes $j$ on $P_j$; the original nonatomic targets are those
retained in Acquisition Resources 73.1. They are not replaced by the
separately selected marked laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                    +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
\theta_j=(B_1,1/(j+2)),\quad n(x)=\min\{i:q_i(x)=0\},
\tag{211.45}
$$

for every $1\ge a_1\ge a_2\ge\cdots>0$ with $a_j\to0$.
There is zero advice, one source-independent common seed and actual
sourcewise almost-sure finite handoff. The rule and the consumer run
on the same actual source and original tape. Competitors retain
arbitrary query addresses and the full output carrier; TV means
$\sup_{E\in\mathcal F}|\nu(E)-\lambda(E)|$, uniformly over all
actual sources and all Borel events.
The resource is at most two actual requests, including ignored and
repeated requests. $N_2$ preselects its sequence and obtains its replies;
$O_2$ preselects a strictly increasing sequence and stops at the first
queried zero or exhaustion. A queried zero need not be the actual
first absence, and an output need not name a queried address.
No mean count, address, runtime, depth or source distribution replaces
this hard request bound.

Only a normalized all-row finite probability configuration can use
109.1 and 110.2. In the notation of 108.2, for a degree-at-most-two
probability-vector kernel
$p_w=c+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}^{\rm ker}w_iw_j$, set
$V_i^{\rm ker}=\sum_{j>i}(-Q_{ij}^{\rm ker})_+$ and
$H^{\rm ker}=\sum_i(V_i^{\rm ker}-\ell_i)_+$, coordinatewise.
The criterion is $c\ge H^{\rm ker}$; its scalar mass condition is
implied by normalization as in 108.4. These kernel coefficients are
unrelated to the proof-credit parameters or score quotient $Q$.
Theorem 110.2 supplies both directions of original closed-cap feasibility
transport, retaining arbitrary addresses and full-carrier competitors.
Its necessity uses the countable common probability-one seed event,
finite actual witnesses, sourcewise finite handoff and the compact
finite-catalog limit. Its sufficiency partitions one source-independent
uniform seed to choose the entire table and schedule before replies.
Different configurations may use different partitions of that same seed,
with a common refinement; pointwise equality of their outputs is not
required. Every execution of such a finite construction hands off after
at most two actual requests. None of $\nu,Y_u,V,Z$ above is promoted
from proof weights to such a probability configuration.

For a positive cap $0<\varepsilon\le1$, set
$L_a=\max(\{j:a_j>\varepsilon\}\cup\{0\})$.
The actual tail identity from 110.2 remains

$$
\operatorname{TV}\left(\sum_{j=0}^{L_a}p_{1^{L_a}}(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-p_{1^{L_a}}(0),a_n\}\quad(n>L_a).
\tag{211.46}
$$

It retains $a_n=\varepsilon$ at the closed cap. Auxiliary hull
endpoints with $e=0$ and zero score coordinates never replace positive
original tails. Small active lengths and cap one remain within the
existing transport; for caps greater than one immediate base output
suffices. No amplitude restriction or new amplitude classification is
implied by a menu, selector or packing theorem alone.

At an actual active length $L=L_a\ge6$, the fixed-data family also
has the following necessary amplitude inequality, as an application of
110.2. If either original class has a closed-cap attainer, then for
every choice of the parameters of 211.3,

$$
(s+d)(a_a+a_z)+d(a_b+a_c)
 +\sum_{\substack{j\ge3\\j\notin\{a,b,c,z\}}}h_j a_j
 \le d+\left(6s+4d+\sum_jh_j\right)\varepsilon.
$$

Indeed transport supplies one normalized complete finite probability
configuration. Pairing all its correct, pair-event and positive-word
inequalities with the nonnegative score $Y_d$ gives expected reward
at least $W+\sum_j\gamma_ja_j-K\varepsilon$; its expected reward
is at most the complete support $W+d$ in either catalog. Substituting
(211.9) gives the displayed inequality, with equality allowed throughout.
Negative correct singleton demands require no truncation in this pairing.
This is an inherited necessary inequality, not a sufficient feasibility
test, an acquisition constructor or a new amplitude classification.

The universal target remains for every finite length $L$ in the
original comparison, and in the coordinates above for every $L\ge3$
and every $b\in H_N$,

$$
\rho_O(b)\le\max\{1,\rho_N(b)\},
\quad\text{equivalently}\quad
Q(y)\in E_N\ \text{for every full actual }y\ge0
                      \text{ with }\Delta_O(y)\le1.
\tag{211.47}
$$

This equivalence is already proved in 199.3–199.4. The remaining task
is its universal inclusion, not another proof of that equivalence.
In original-source terms it is the unresolved implication
$\mathcal F_N(a,\varepsilon)\ne\varnothing\Rightarrow
\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing$
for every selected amplitude sequence and every positive closed cap,
where $\mathcal F_N$ is the all-word finite cap slice of 110.1 and
$\mathscr C_{L_a}$ is the normalized stopped region of 109.1.
Arbitrary early credit, early-$00$ stock, unordered or growing late
profiles and low terminal stock outside the stated conditions remain.

A genuine refutation requires the same actual $y,b,\lambda$ with

$$
b\in H_N,\qquad y\ge0,\quad\Delta_O(y)\le1,\qquad
\lambda\ge0,\quad G_N\lambda\ge h(b),\quad
M=\sum_D\lambda_D\ge1,\quad F_{Q(y)}(b)>M,
\tag{211.48}
$$

and the owned original-source transport to an actual common-seed
$N_2$ attainer and a uniform lower certificate against every original
$O_2$ competitor. Hull-only points, weakened necessary-condition
relaxations, separately funded measures and restricted-method failures
supply none of this compatible witness. The exact-law obstruction
112.2 still allows a different stopped law at the same cap.
No universal comparison, original separator, new quotient-region
coverage or kernel verification is asserted here.

## 追加锚（本行以下为增补区）
