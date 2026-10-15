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

## 212. Coupled surplus carriers, equality-block moves and joint fixed-data minima

**Definition 212.1 (Complete scores, actual measures and one budget).**
Retain the source and acquisition contract of 210.1 and 211.14.
For an integer $L\ge3$, let $\Omega_n\subseteq\{0,1\}^L$ contain
all words with first zero $n$. Every word, including every multiple-zero
word and $1^L$, remains in the domain. A score $y$ consists of independent
nonnegative weights $A_w,C_w,P_w$ at each $w\ne1^L$ and $T\ge0$.
At label $r\in\{0,\ldots,L\}$ its reward is

$$
g_y(w,r)=A_w\mathbf1_{r=0}+C_w\mathbf1_{r=n(w)}
              +P_w\mathbf1_{r\in\{0,n(w)\}},\qquad
 g_y(1^L,r)=T\mathbf1_{r=0}.
\tag{212.1}
$$

Thus $P$ is the independent two-label event weight. For a cell $E$ put
$m_y(E)=\max_{0\le r\le L}\sum_{w\in E}g_y(w,r)$.
The full catalogs contain empty schedules, every singleton, and every
pair $i<j$. The $N$ pair cells are $00,01,10,11$; the $O$ cells are
$0=\{w_i=0\},10,11$. A label may be earlier than both queried addresses
and need not be queried. Let $B_N^s,B_O^s$ be the sums of these cell
maxima and $B_N,B_O$ their maxima over the respective complete catalogs.
A tuple $(i,j;r_0,r_{10},r_{11})$ denotes a stopped table, and four
output entries denote a full table in $00,01,10,11$ order.

The anchor is the stopped table $R=(1,2;1,2,0)$, with full completion
$(1,2;1,1,2,0)$. Write

$$
\begin{aligned}
W_y&=\sum_{n(w)\ge3}A_w+\sum_{n(w)\le2}C_w+\sum_wP_w+T,\\
\Delta_{\mathcal C}(y)&=B_{\mathcal C}(y)-W_y\ge0
                         \quad(\mathcal C=N,O),\\
Q(y)&=(\beta,K),\qquad
\beta_n=\sum_{\Omega_n}(C_w-A_w),\qquad
K=\sum_w(A_w+C_w+P_w)+T.
\end{aligned}
\tag{212.2}
$$

All sums over zero words include zero coefficients. Static reversals
only exchange cells and repetitions give singleton information; their
actual requests still count. Every empty or singleton $N$ output
function has a distinct-pair $N$ representation. Completing an $O$
schedule gives an $N$ function. These representation facts do not
embed a last-address singleton in a nonexistent later stopped pair.

The complete event-demand vector $d(b,e)$ has the three independent
entries $1-b_n-e,b_n-e,1-e$ at every $w\in\Omega_n$, and $1-e$
at $1^L$. Negative singleton demands are retained. Use the existing
hull and signed quotient coordinates of 198.5 and 199.1–199.4:

$$
\begin{aligned}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,
 \quad b_2=b_3,\\
 &(L+1)e\le\sum_{n=3}^Lb_n,
 \quad b_1+\sum_{n=3}^Lb_n-(L+1)e\le1\},\\
\alpha&=(1,1,0,\ldots,0),\qquad
 F_q(b,e)=\sum_n\beta_n(b_n-\alpha_n)-Ke,\qquad
 \sigma_H(q)=\max_{H_L}F_q.
\end{aligned}
\tag{212.3}
$$

If $z_D$ is the full event-indicator vector of a table, set
$r=z_R=d(\alpha,0)$, $h=d-r$ and $G_{\mathcal C}=(z_D-r)_D$.
In particular $F_{Q(y)}=y\cdot h$. The domain of finite full-$N$
configurations is

$$
H_N=\{b\in H_L:\exists\lambda\ge0,
                         \ G_N\lambda\ge h(b)\}.
\tag{212.4}
$$

As in 199.2, $q\in E_N$ means that one full score and one number satisfy

$$
V\ge0,\quad 0\le\theta\le1,\qquad
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(q-Q(V))\le\theta.
\tag{212.5}
$$

For the same actual full configuration $\lambda$ at $b\in H_N$,
with $M=\sum_D\lambda_D$, the existing weak-duality calculation gives
$F_q(b)\le M\Delta_N(V)+\theta\le\max(1,M)$.
The residual is signed; at $\theta=1$ the score $V$ can be nonzero
with zero cost. No class, cell or pair has an additional budget.

Every measure below is an actual finite measure on the indicated
Boolean cube. Its coordinates are proof weights, not a distribution
on source labels or an acquisition probability kernel. Unspecified
weights are zero, coincident atoms add, $x_+=\max(x,0)$, and a maximum
over an absent family of nonnegative entries contributes zero.

### 212.1 Full-score surplus carriers and coupled moment boxes

**Definition 212.2 (Retained rewards and projected surplus).**
Let $y$ be an arbitrary complete score and $I=\{3,\ldots,L\}$.
Put $\gamma_n=\sum_{\Omega_n}C_w$ for $n\in I$ and $W=W_y$.
Delete exactly these late correct rows to obtain $Z$; all $A,P,T$
and early correct rows stay at their actual words. Thus $W_Z=W$.
For every label $r$, let $z_r(w)=g_Z(w,r)$ be its reward measure
on the whole cube, including the positive word.

For $n\in I$, let $\pi_n(v)=P_{1^{n-1}0v}$ on the full suffix
cube $\{0,1\}^{\{n+1,\ldots,L\}}$, and put
$p_n=|\pi_n|$, $\pi_{nj}=\pi_n\{v_j=0\}$.
Let $\omega_{rn}$ be the suffix projection of
$z_r|_{\{w_n=0\}}$. In particular
$\omega_{nn}=\pi_n$ and $\omega_{0n}\ge\pi_n$ atomwise.
Define the nonempty compact convex set

$$
\mathcal T_n=\left\{\tau\ge0:\sum_{r=0}^L\tau_r=1,
 \quad\Omega_{\tau,n}:=\sum_r\tau_r\omega_{rn}\ge\pi_n\right\}.
\tag{212.6}
$$

A permitted replacement chooses one $\tau_n\in\mathcal T_n$ and
one actual suffix measure

$$
0\le\sigma_n\le\Omega_{\tau_n,n}-\pi_n,
\qquad |\sigma_n|=\eta_n\ge0,
\qquad c_{nj}=\sigma_n\{v_j=0\}.
\tag{212.7}
$$

Set $C^V_{1^{n-1}0v}=\sigma_n(v)$ for every late class and retain
$Z$ everywhere else. Write $k_n=p_n+\eta_n$ and
$t_{nj}=\pi_{nj}+c_{nj}$ for the total reward of label $n$.
These definitions specify one score $V$. Different labels may reuse
the same carrier atoms: there is no additional constraint
$\sum_n\sigma_n\le\omega$. Only one output label wins a terminal cell.
The subtraction of the retained $\pi_n$ in (212.7) is compulsory.

For $i<j$, put

$$
\begin{aligned}
b_{ij}^{ab}&=\max_r z_r\{w_i=a,w_j=b\},\qquad
 b_{ij}^0=\max_r z_r\{w_i=0\},\\
a_{ij}&=b_{ij}^{00}+b_{ij}^{01},\qquad
 \chi_{ij}=a_{ij}-b_{ij}^0\ge0,\\
X_{ij}&=\max\left\{b_{ij}^{10},\ k_j\ (j\in I),\
                     t_{nj}\ (n\in I,\ i<n<j)\right\},\\
Y_{ij}&=\max\left\{b_{ij}^{11},\ k_n\ (n\in I,\ n>j),\
                     k_n-t_{nj}\ (n\in I,\ i<n<j)\right\}.
\end{aligned}
\tag{212.8}
$$

All baseline maxima include every label. In particular a positive
$\chi_{ij}$ is a retained split defect, not removable by selecting
a different maximizer after merging the cells.

**Theorem 212.3 (Exact full-score support and joint carrier-box criterion).**
For every permitted replacement,

$$
\begin{aligned}
B_N^{ij}(V)&=a_{ij}+X_{ij}+Y_{ij},\\
B_O^{ij}(V)&=b_{ij}^0+X_{ij}+Y_{ij},\\
\Delta_N(V)&=\max_{i<j}(a_{ij}+X_{ij}+Y_{ij}-W).
\end{aligned}
\tag{212.9}
$$

For completeness, put $b_i^a=\max_r z_r\{w_i=a\}$ and
$b_\varnothing=\max_r|z_r|$. Both catalogs have the exact short supports

$$
B^\varnothing(V)=\max(b_\varnothing,\max_{n\in I}k_n),\qquad
B^{(i)}(V)=b_i^0+\max(b_i^1,\max_{n\in I,\ n>i}k_n).
\tag{212.10}
$$

Fix any $\eta_n\ge0$ and $d\ge0$. A replacement (212.7) with
$\Delta_N(V)\le d$ exists if and only if there are common ceilings
$u_{ij},v_{ij}$ for all $i<j$ such that

$$
\begin{gathered}
u_{ij}\ge\max\{b_{ij}^{10},k_j\ (j\in I)\},\qquad
v_{ij}\ge\max\{b_{ij}^{11},k_n\ (n\in I,n>j)\},\\
a_{ij}+u_{ij}+v_{ij}\le W+d,
\tag{212.11}
\end{gathered}
$$

and the following moment-box conditions hold for each $n\in I$.
For $j>n$ set

$$
\begin{aligned}
\ell_{nj}&=\max\left(0,\max_{i<n}
                     (k_n-v_{ij}-\pi_{nj})\right),\\
h_{nj}&=\min\left(\eta_n,\min_{i<n}(u_{ij}-\pi_{nj})\right).
\end{aligned}
\tag{212.12}
$$

Require $\ell_{nj}\le h_{nj}$ and, for every real vector
$\xi=(\xi_0,(\xi_j)_{j>n})$, require

$$
\begin{aligned}
\xi_0\eta_n+\sum_{j>n}
 \bigl((\xi_j)_+\ell_{nj}+\min(\xi_j,0)h_{nj}\bigr)
 &\le\mathcal H_n(\xi),\\
\mathcal H_n(\xi)
 &=\max_{\tau\in\mathcal T_n}\sum_v
 (\Omega_{\tau,n}(v)-\pi_n(v))
 \left(\xi_0+\sum_{j>n}\xi_j\mathbf1_{v_j=0}\right)_+.
\end{aligned}
\tag{212.13}
$$

At $n=L$ there is only the mass coordinate $\xi_0$.
The criterion concerns exactly the declared fixed-baseline replacement
class, including zero capacities and all closed boundaries.

For any resulting score define the signed prefixes

$$
R_k=\sum_{n=3}^k(\gamma_n-\eta_n),\qquad
\Theta=\max\left(0,\max_{3\le k\le L}\frac{3R_k}{k+1}\right).
\tag{212.14}
$$

Then $\sigma_H(Q(y)-Q(V))=\Theta$. If the common ceilings satisfy
$d+\Theta\le1$, the same score with $\theta=\Theta$ is a certificate
(212.5). No universal existence of affordable $\eta,d$ or ceilings
is asserted.

**Proof.** For a late class $n\le i$, the reward of its label after
replacement is the reset of $\pi_n+\sigma_n$, not of $\sigma_n$
alone. By (212.7), this whole measure is dominated by
$\Omega_{\tau_n,n}$. When $n<i$, both queried bits are suffix bits
and survive reset to $1^{n-1}0v$. When $n=i$, the first queried bit
is already zero on the restricted donor. Therefore, on any applicable
pair cell $E$,

$$
\text{reward of label }n\text{ in }V\text{ on }E
 \le\sum_r\tau_{n,r}z_r(E\cap\{w_n=0\})
 \le\max_r z_r(E).
\tag{212.15}
$$

The same statement holds for the merged cell $w_i=0$.
Classes $n>i$ never occupy that branch. Since adding correct rows to
$Z$ only increases rewards, its maxima in $00,01,0$ remain exactly
$b_{ij}^{00},b_{ij}^{01},b_{ij}^0$.

For $i<n<j$ the total label-$n$ rewards in $10,11$ are exactly
$t_{nj},k_n-t_{nj}$. Class $j$ contributes $k_j,0$ and every class
$n>j$ contributes $0,k_n$. All other rewards are retained in the
baseline maxima or bounded by (212.15). This exhausts the labels and
proves the two pair identities, with their exact difference $\chi_{ij}$.
For a singleton at $i$, classes $n\le i$ are bounded by the corresponding
baseline cell maxima by the same restriction argument; those with
$n>i$ contribute their whole totals in the positive cell. Label totals
give the empty formula. Short $N$ functions refine into pairs, proving
the last identity in (212.9); it is nonnegative because $R$ is available.
Taking the maximum of (212.9)'s stopped expressions and (212.10) also
gives the complete $O$ support without a short-schedule assumption.

For fixed ceilings, $X_{ij}\le u_{ij}$ and $Y_{ij}\le v_{ij}$
are equivalent to their baseline, queried and future lower bounds
in (212.11) and, for every intermediate class,

$$
k_n-v_{ij}-\pi_{nj}\le c_{nj}\le u_{ij}-\pi_{nj}.
\tag{212.16}
$$

Intersecting (212.16) over all $i<n$, with $0\le c_{nj}\le\eta_n$,
gives exactly (212.12). This intersection must be used for one unary
number, rather than different numbers for different first addresses.

Let $\mathcal D_n$ be the mass/unary image of all pairs
$(\tau,\sigma)$ satisfying $\tau\in\mathcal T_n$ and
$0\le\sigma\le\Omega_{\tau,n}-\pi_n$. This is a compact convex
polytope: the variables range in finite bounded closed polyhedra and
the moment map is linear. This is the finite projection framework
of Kaibel, [*Basic Polyhedral Theory*, arXiv:1001.2161v1,
Theorem 8 and §1.6](https://arxiv.org/pdf/1001.2161v1), applied to
suffix-atom capacities and their mass/unary map.
For a fixed $\tau$, a linear functional is maximized by taking the
full capacity at atoms with positive affine coefficient and zero at
atoms with negative coefficient. Maximization over $\tau$ therefore
gives precisely $\mathcal H_n$ as the support of $\mathcal D_n$.

The desired box is
$\mathcal B_n=\{\eta_n\}\times\prod_{j>n}[\ell_{nj},h_{nj}]$.
The left side of (212.13) is its infimum in direction $\xi$.
Intersection with $\mathcal D_n$ implies every cut. Conversely, if
the two nonempty compact convex sets were disjoint, choose closest
points $b\in\mathcal B_n,z\in\mathcal D_n$ and put $\xi=b-z$.
Differentiating squared distance along segments in each set gives

$$
\inf_{x\in\mathcal B_n}\langle\xi,x\rangle
 \ge\langle\xi,b\rangle
 >\langle\xi,z\rangle
 \ge\sup_{x\in\mathcal D_n}\langle\xi,x\rangle,
$$

contradicting (212.13). This is the classical finite convex separation
step within this carrier argument. Thus the cuts supply an actual
single suffix measure with every required moment, not only separately
attainable marginals. Each class choice coexists with the others in
its distinct first-zero class. The common table ceilings then prove
$\Delta_N(V)\le d$. Conversely, any permitted score of that cost
supplies the ceilings $X_{ij},Y_{ij}$ and its actual moment vectors,
which satisfy every cut. This proves the equivalence.

Only late correct totals changed, so $W_V=W$ and

$$
F_{Q(y)-Q(V)}(b,e)
 =\sum_{n=3}^L(\gamma_n-\eta_n)(b_n-e).
\tag{212.17}
$$

Use all four vertex families of the already established hull 198.5.
The readings are zero at $o,p$, $R_k/(k-1)$ at $u_k$, and
$3R_k/(k+1)$ at $v_k$. For $R_k\ge0$ the last reading dominates
the $u_k$ reading because $k\ge3$; for $R_k<0$ both are below zero.
Their maximum is (212.14), with no sign restriction on the residual.
Combining this charge once with the complete score cost proves
(212.5) by 199.3–199.4. $\square$

The following are variants of the same mechanism. They do not give
three different inclusion statements. If only a selected subset
$J\subseteq I$ is replaced, retain the other correct rows in $Z$,
restrict every changed-class index in (212.6)–(212.17) to $J$, and
put $\gamma_n-\eta_n=0$ outside $J$. The proof is unchanged because
all unchanged labels stay in the baseline maxima. A stronger sufficient
carrier choice requires the full-word difference

$$
D_n=\sum_r\tau_{n,r}z_r-z_n\ge0\quad\text{at every word}
\qquad(n\in J).
\tag{212.18}
$$

Its restricted suffix projection is exactly
$\Omega_{\tau_n,n}-\pi_n$. Thus a submeasure of that projected
difference satisfies (212.7). Requiring (212.18) is stronger than
requiring only nonnegativity of the projected surplus.

A second useful specialization keeps $\eta_n=\gamma_n$ and uses
original-input cell intervals. For every $n<j$ put

$$
H^0_{nj}=\min_{i<n}m_y(10;i,j),\qquad
H^1_{nj}=\min_{i<n}m_y(11;i,j),\qquad
k_n-H^1_{nj}\le t_{nj}\le H^0_{nj}.
\tag{212.19}
$$

These bounds allow unary movement. In the moment test substitute
$\ell_{nj}=\max(0,k_n-H^1_{nj}-\pi_{nj})$ and
$h_{nj}=\min(\gamma_n,H^0_{nj}-\pi_{nj})$.
The original correct moments show these intervals are nonempty,
but need not belong to the surplus moment image.
Whenever actual dominated measures meet them, the new stopped pair
supports do not exceed the original ones: intermediate rewards obey
(212.19), queried and future totals are unchanged, and $Z\le y$.
The singleton comparison follows from (212.10), and empty support
is unchanged because all label totals are unchanged.

Consequently, with

$$
\overline B=\max\left\{
 \max_{|s|\le1}B^s(y),\
 \max_{i<j}\bigl(a_{ij}+m_y(10;i,j)+m_y(11;i,j)\bigr)\right\},
\qquad\overline d=\max(0,\overline B-W),
\tag{212.20}
$$

one has $\Delta_N(V)\le\overline d$ and
$\Delta_O(V)\le\Delta_O(y)$, with zero quotient residual.
If every $\chi_{ij}=0$, then $\overline d\le\Delta_O(y)$;
a nonzero defect can also be paid by the global slack in (212.20).
There is no need for each individual cell to decrease in the general
criterion (212.11). For example, inequalities between two intermediate
entries include differences $c_{nj}-c_{mj}$; when $n=m$ their
complementary contributions sum to $k_n$ and cannot be charged twice.
For an explicit sufficient measure, any admissible surplus of mass
$M\ge\eta_n$ can be used at constant density $\eta_n/M$ if its
moments obey the required box. At $M=\eta_n=0$ use zero; if
$M=0<\eta_n$ that particular choice is impossible.

**Proposition 212.4 (Actual full-row relocation and the fixed-baseline boundary).**
The criterion permits changes excluded by exact unary matching, but
its fixed-baseline class is not universally affordable on unit-$O$
inputs.

**Proof.** For a full-row instance at $L=5$, put

$$
P_{01001}=P_{01010}=P_{10001}=P_{10010}=1/2,\qquad
A_{11100}=P_{11100}=1/4,\qquad C_{11000}=2,\qquad T=1.
\tag{212.21}
$$

Keep all other coefficients zero. Retain every row except $C_3$ and
replace it by $C^V_{11001}=C^V_{11010}=1$.
The class-3 label-zero surplus has mass one at each suffix $01,10$,
so these are actual permitted measures in the selected-class variant.
Here $W=7/2$ and
$Q(y)=Q(V)=((0,0,2,-1/4,0),11/2)$.
The complete pair supports, with all labels included, are

| Pairs | $B_N^s(y)$ | $B_O^s(y)$ | $B_N^s(V)$ | $B_O^s(V)$ |
| --- | --- | --- | --- | --- |
| $12$ | $4$ | $4$ | $4$ | $4$ |
| $13,23$ | $9/2$ | $9/2$ | $9/2$ | $9/2$ |
| $14,15,24,25$ | $9/2$ | $9/2$ | $7/2$ | $7/2$ |
| $34,35$ | $9/2$ | $7/2$ | $7/2$ | $7/2$ |
| $45$ | $5$ | $4$ | $7/2$ | $7/2$ |

These entries follow directly from (212.1): the new $N$ maxima in
these five rows are respectively
$(0,1,1,2)$, $(1,0,2,3/2)$, $(1/2,1/2,1,3/2)$,
$(1,1,1/2,1)$ and $(1/2,1,1,1)$.
The empty support is $7/2$ for both scores; singleton supports are
$(7/2,7/2,7/2,4,4)$ for $y$ and all $7/2$ for $V$.
Thus the costs are $(3/2,1)$ before and $(1,1)$ after replacement.
Exact unary matching would require mass two with zero moments $(2,2)$,
whereas every mass-two measure on $\{01,10\}$ has sum of those
moments two. All retained label carriers are supported there. The
actual certificate is $(V,0)$; this example concerns the carrier
route, not exclusion from other certificates.

Retained pair subtraction cannot be omitted even at unit cost.
At $L=4$, take $P_{1100}=C_{1100}=1$ and no other weights.
Then $W=1$ and both complete costs are one. Deleting $C_3$ leaves
$\pi_3=\omega_{03}=\delta_0$. Gross reward would incorrectly permit
another unit $C_3$ and bound label 3's reward in pair-$34$ cell $00$
by one, although that reward is two. The actual surplus is zero.

Finally take the complete $L=3$ input

$$
A_{000}=A_{011}=C_{001}=C_{010}=1,
\tag{212.22}
$$

all other weights zero. Its anchor is two, and
$Q(y)=(0,0,0;4)$. Pair $23$ has full cell maxima $(1,1,1,1)$
and stopped maxima $(1,1,1)$. Pairs $12,13$, all singletons and the
empty schedule have support two. Hence
$\Delta_N(y)=2$ and $\Delta_O(y)=1$.
There is no late correct input, so $Z=y$. Every permitted replacement
has $V\ge Z$ and the same anchor, forcing $\Delta_N(V)\ge2$
for every $\eta$. Yet the unrestricted certificate $V=0,\theta=0$
works because $F_{Q(y)}=-4e\le0$ on $H_L$.
This distinguishes failure of the fixed-baseline method from failure
of $E_N$ membership. $\square$

### 212.2 Equality-block locality and the entire unary fiber

**Definition 212.5 (One equality block and funded face moves).**
Fix $L\ge5$, nonempty disjoint sets $U,V\subseteq\{4,\ldots,L\}$,
$J=U\cup V$, $d=|J|$, and $K=\{4,\ldots,L\}\setminus J$.
Let $\kappa$ be any probability measure on the full $K$-cube,
including the one-point cube when $K$ is empty. Choose $c>0,t\ge c$.
For a three-bit prefix $h$, let $w_{ab}^h(v)$ have prefix $h$,
all $U$ bits equal to $a$, all $V$ bits equal to $b$, and $K$ bits $v$.
Define the actual full score $Y$ by

$$
\begin{aligned}
P_{w_{01}^{010}(v)}=P_{w_{10}^{010}(v)}
 =P_{w_{01}^{100}(v)}=P_{w_{10}^{100}(v)}&=t\kappa(v)/2,\\
C_{w_{00}^{110}(v)}=C_{w_{11}^{110}(v)}&=c\kappa(v),\qquad T=t,
\end{aligned}
\tag{212.23}
$$

with $A=0$ and all unspecified coefficients zero. In particular
$W=3t$, $Q(Y)=(2c e_3,2c+3t)$, where $e_3$ here denotes a
quotient coordinate vector. Let $\mathcal U(Y)$ consist of every
nonnegative replacement of the class-3 correct measure that preserves
its mass and every unary marginal, with all other score rows fixed.
No joint-marginal or support restriction is imposed in $\mathcal U(Y)$.
For such a replacement $C'$ define its moved mass by

$$
\operatorname{mov}(C',C)=\frac12\sum_{w\in\Omega_3}|C'_w-C_w|.
\tag{212.24}
$$

A coordinate-face move is a signed change of this correct measure,
supported on one face on which all coordinates outside a set $S$
are fixed. It preserves mass and every unary marginal, and its addition
to the current measure must be nonnegative. Its width is $|S|$,
counting suffix coordinates only. A batch is funded when the sum of
its atomwise withdrawals is bounded by the current measure. Finite
batches and countable batches with that property are allowed; mass
preservation makes the latter absolutely summable. This definition
does not allow unfunded summands merely because their net sum would
be feasible.

**Theorem 212.6 (Exact intermediate cost, sharp moved mass and locality).**
For $0\le x_v\le c\kappa(v)$, put $X=\sum_vx_v$.
Replace the class-3 measure in each stratum by

$$
\begin{array}{c|rrrr}
\text{word}&w_{00}^{110}(v)&w_{01}^{110}(v)&w_{10}^{110}(v)&w_{11}^{110}(v)\\\hline
C^{Y_x}&c\kappa(v)-x_v&x_v&x_v&c\kappa(v)-x_v
\end{array}
\tag{212.25}
$$

and leave all other rows fixed. Then $Y_x\in\mathcal U(Y)$ and,
with $\delta=(2c-t)_+$,

$$
\Delta_O(Y_x)=\delta,\qquad
\Delta_N(Y_x)=\max(\delta,c-X).
\tag{212.26}
$$

For every $D\ge0$, the least moved mass over the entire declared
fiber, subject to $\Delta_N\le D$, is

$$
\min_{C'\in\mathcal U(Y),\ \Delta_N(C')\le D}
 \operatorname{mov}(C',C)
 =\begin{cases}
 +\infty,&D<\delta,\\
 2(c-D)_+,&D\ge\delta.
 \end{cases}
\tag{212.27}
$$

The finite value is attained by (212.25) with
$x_v=(c-D)_+\kappa(v)$.

Starting at $Y$, every sequence of feasible face moves each omitting
at least one coordinate of $J$ preserves support on
$E_J=\{v:\text{all bits in }J\text{ agree}\}$ and has
$\Delta_N\ge c$. The same holds after funded batches and under
coordinatewise limits. If $\delta<c$, the least maximum face width
that can lower cost below $c$ is exactly $d=|J|$: a successful path
must contain a face including $J$, and width-$d$ moves suffice.
Width is a locality constraint on proof-weight changes, not a number
of requests, an address bound, a seed size or a runtime bound.

**Proof.** The signed change in each stratum is
$x_v(-1,1,1,-1)$. Its total and both block marginals vanish,
and $K$ coordinates are fixed in that stratum. It therefore preserves
all unary marginals, $Q$ and $W$. Nonnegativity is exactly the displayed
donor bound. Distinct strata have disjoint donors; each stratum's one
withdrawal repairs all pairs in $U\times V$ simultaneously.

Here is the full schedule calculation. Write $z_j=1/2$ on $J$
and $z_j=\kappa\{v_j=0\}$ on $K$. The excesses over $W=3t$ are

| Schedule | $N$ excess | $O$ excess |
| --- | --- | --- |
| $12,13,23$ | $\delta$ | $\delta$ |
| $(a,j)$, $a\in\{1,2\}$, $j\ge4$ | $z_j\delta$ | $z_j\delta$ |
| $(3,j)$, $j\ge4$ | $0$ | $0$ |
| Suffix pair crossing $U,V$ | $c-X$ | $0$ |
| Every other suffix pair | $0$ | $0$ |
| Empty and every singleton | $0$ | $0$ |

To verify every label in this table, zero earns the pair stock in each
cell and $t$ at the positive word; labels 1 and 2 earn subsets of that
stock. The only other nonzero label is 3. At the three head pairs the
support is $2t+\max(t,2c)$. At $(a,j)$ the first-zero contribution
is $t$ and the remaining two maxima are

$$
z_j\max(t,2c),\qquad
\max\{t(2-z_j),2c(1-z_j)\}=t(2-z_j),
\tag{212.28}
$$

using $t\ge c$. Splitting the first-zero branch does not change its
maximum sum, since it has only pair stock. This gives $z_j\delta$.
At $(3,j)$, label-3 cell masses are $2cz_j,2c(1-z_j),0,0$;
the corresponding pair masses are $2tz_j,2t(1-z_j),0,0$ and
$T$ contributes $t$ to $11$. Zero dominates, as asserted.

For a pair crossing $U,V$, the zero-label masses are $(0,t,t,t)$,
including $T$ in the last entry. The correct-label masses are
$(c-X,X,X,c-X)$. Since $0\le X\le c\le t$, the full maxima are

$$
(c-X,t,t,t),\qquad\text{and the stopped maxima are }(t,t,t).
\tag{212.29}
$$

The merged correct reward is $c\le t$. On any noncrossing suffix
pair, its correct projection is $c/t$ times its pair projection.
For pairs within one block this follows from the two preserved block
marginals in each stratum; for a block/$K$ pair it follows from those
same stratum marginals; for a $K/K$ pair it follows from the preserved
stratum total. This remains valid for nonuniform $\kappa$ and unequal
$x_v$. Zero dominates these cells, with $T$ added in $11$.
Early singleton maxima are $t,2t$, query-3 maxima are $2t,t$,
and suffix singletons have maxima $2tz_j,2t(1-z_j)+t$.
The empty maximum is $3t$. These statements include all legal labels;
other labels have zero reward here rather than being removed from the
catalog. The table proves (212.26).

For an arbitrary member of $\mathcal U(Y)$, a head pair still forces
cost at least $\delta$, because its class-3 total is $2c$.
Fix $i\in U,j\in V$. Total mass $2c$ and the two zero marginals
$c$ force the new correct pair table to be
$(u,c-u,c-u,u)$ with $0\le u\le c$.
With the unchanged stock its full support is exactly $3t+u$.
Thus cost at most $D$ forces $u\le D$. Projection to these two
coordinates contracts the $\ell^1$ distance: the triangle inequality
bounds the absolute value of each projected signed sum by the sum of
its absolute values. The original pair table is $(c,0,0,c)$,
so its projected distance is $4(c-u)$. At least $2(c-D)$ mass
must therefore move if $D<c$. For $D\ge c$ the zero lower bound
is attained without change. For $\delta\le D<c$, (212.25) with
$X=c-D$ has exactly moved mass $2X$ and complete cost $D$.
These arguments prove the entire-fiber minimum, not just optimality
among the displayed stratum changes.

For locality, suppose the current measure is supported on $E_J$,
and a face omits $j_0\in J$, fixed there to bit $b$.
Every old positive atom on that face has every $J$ bit equal to $b$.
For each movable $j\in J$, its opposite-bit mass on the face is zero.
A move supported there and preserving the global mass and unaries
preserves those face quantities as well. Nonnegativity forces the new
opposite-bit mass to remain zero. A face of zero mass must remain empty.
Thus no such move creates mass outside $E_J$.

Induction proves the assertion for finite paths. In a funded batch
each summand is individually feasible, since its negative part is
bounded by the current measure. Each summand consequently vanishes
outside $E_J$; their sum does too. In a countable funded batch,
$\sum\|\text{move}\|_1$ is at most twice the current total mass,
so the same conclusion follows by absolute convergence. Finally,
nonnegative measures supported on $E_J$ with fixed unary data form a
closed set in this finite-dimensional space. Coordinatewise limits
retain the invariant. Every crossing pair then still has table
$(c,0,0,c)$ and forces cost at least $c$, independently of any changes
on $K$ or of monotonicity along the path.

Conversely (212.25) consists of width-$d$ moves, one per nonzero $x_v$,
with the $K$ bits fixed. If $\delta<c$, any $0<X\le c$ lowers the
cost below $c$ until the head bound takes over. Taking
$X=c-\delta$ reaches cost $\delta$. Every successful path must
therefore use at least one face containing $J$, and the displayed
moves attain this width. All endpoints $x_v=0,c\kappa(v)$,
$t=c$, $t=2c$, zero carrier atoms and empty $K$ are included.
$\square$

For example, $L=6$, $U=\{4\}$, $V=\{5,6\}$, $c=2,t=3$
and the one-point outside carrier give $W=9$ and costs $(2,1)$.
The four nonzero pair rows are
$P_{010011}=P_{010100}=P_{100011}=P_{100100}=3/2$,
and the original correct rows are $C_{110000}=C_{110111}=2$.
The choice $x=1$ makes the four correct rows
$110000,110011,110100,110111$ all have mass one; it attains costs
$(1,1)$ with the least moved mass two. For any prescribed width
bound $k\ge2$, take $|J|=k+1$ with the same $c,t$ to obtain the
corresponding unit-$O$ locality obstruction. Taking $t=2c$ gives a
zero-$O$ input with arbitrary positive initial $N$ cost $c$.

The full-relocation endpoint $X=c$ directly reuses 209.13:
its new correct measure is $c/t$ times the actual pair carrier
conditioned at address 3, preserves the original unaries, and has
label zero as a common baseline maximizer. The four-word mechanism
of 211.2 remains its existing supplier. The additional assertions
here are the whole-fiber moved-mass optimum, its intermediate complete
cost and the all-length locality invariant. Whenever $\delta\le1$,
$X=(c-1)_+$ gives the single certificate $(Y_x,0)$; $X=c-\delta$
compares at the original stopped cost. No failure of bounded-width
moves excludes nonlocal changes, changes of unaries or other rows,
or signed residual certificates.

The mass/unary map is a nonnegative real-table fiber. For rational
prescribed margins and a fixed positive integer $D$ clearing them,
scaling by $D$ identifies the tables restricted to the
$D^{-1}\mathbb Z_{\ge0}$ grid with an integer fiber in the terminology of
Clarke and Kosta, [*Distance Reducing Markov Bases*,
arXiv:2406.17730v1, Definition 2.2 and Propositions 2.3 and 7.2](https://arxiv.org/pdf/2406.17730v1).
Their applicable moves require donor nonnegativity; their Graver-basis
result reduces $\ell^1$ distance in integer fibers. Neither supplies
a bounded coordinate width nor a decrease of the complete maximum
$\Delta_N$. The real-weight support argument and the projected
$\ell^1$ lower bound above supply those distinct conclusions here.

### 212.3 Unequal star carriers at every terminal mass

**Definition 212.7 (The full fixed-star class).** On
$I=\{3,\ldots,L\}$ choose arbitrary real numbers
$a_\varnothing,a_i,\gamma_i,t\ge0$ and let

$$
\nu=a_\varnothing\delta_{0^I}
                 +\sum_{i\in I}a_i\delta_{x^{(i)}},\qquad
x^{(i)}_j=\mathbf1_{j=i},\qquad
S=a_\varnothing+\sum_{i\in I}a_i.
\tag{212.30}
$$

Thus the positive-coordinate events are pairwise disjoint under the
one actual measure $\nu$. Let $\mathcal A(\nu,\gamma,t)$ contain
all scores with $A=0$, no early correct mass, $P$ supported in
$\Omega_1\cup\Omega_2$, late projection
$P_{00x}+P_{01x}+P_{10x}=\nu(x)$, correct totals $\gamma_i$
and $T=t$. Every early allocation, including prefix $00$, and every
correct suffix is permitted. The only restrictions on $\gamma,t$
are nonnegativity: they can be unordered, exceed the carrier stock,
and have arbitrarily many nonzero classes. All these scores have
$W=S+t$ and $Q=(\gamma,\sum_i\gamma_i+S+t)$, with early
quotient coordinates zero.

**Theorem 212.8 (Nine-family simultaneous fixed-data minimum).**
Let $B_*$ be the maximum of these nine families:

$$
\begin{array}{c|l|l}
 &\text{entry}&\text{indices}\\\hline
1&S+t&\text{none}\\
2&S+\gamma_i&i\in I\\
3&S/2+\gamma_i+a_i/2+t&i\in I\\
4&S/2+\gamma_i+\gamma_j&i<j\text{ in }I\\
5&\gamma_i+\gamma_j+t&i<j\text{ in }I\\
6&S-a_i+\gamma_j+t&i<j\text{ in }I\\
7&\gamma_i+\gamma_j+\gamma_k&i<j<k\text{ in }I\\
8&S-a_i+\gamma_j+\gamma_k&i<j<k\text{ in }I\\
9&\gamma_i+a_i+\gamma_k&i<j<k\text{ in }I.
\end{array}
\tag{212.31}
$$

Absent indexed families are omitted; in family 9 the intermediate
index $j$ requires an actual address strictly between $i$ and $k$.
Then

$$
\min_{y\in\mathcal A(\nu,\gamma,t)}B_N(y)
 =\min_{y\in\mathcal A(\nu,\gamma,t)}B_O(y)=B_*.
\tag{212.32}
$$

One score attains both minima simultaneously. It has balanced lifts
$P^*_{01x}=P^*_{10x}=\nu(x)/2$, terminal mass $t$, and the existing
threshold placement of 203.2: for each $n\in I$, send length measure
on $[0,\gamma_n)$ to the word

$$
w^n_k(r)=1\ (k<n),\qquad w^n_n(r)=0,\qquad
w^n_j(r)=\mathbf1_{r<a_j}\ (j>n).
\tag{212.33}
$$

Put the length of each inverse image in its correct row and add
coincident rows. The parameter correspondence to (203.10) is
$a_{nj}=\nu\{x_n=0,x_j=1\}=a_j$ for $n<j$.
This uses the same threshold constructor even when $t<\max\gamma$;
the assertion here is its exact all-terminal fixed-data minimum.
For every input in this class the resulting single score $V_*$ has

$$
Q(V_*)=Q(y),\qquad
\Delta_N(V_*)=\Delta_O(V_*)=B_*-S-t\le\Delta_O(y).
\tag{212.34}
$$

Every unit-$O$ input in the class consequently has certificate
$(V_*,0)$.

**Proof.** First take an arbitrary competitor, with its entire early
allocation and arbitrary correct suffixes. Constant zero earns $S+t$,
and the head table earns $S+\max(t,\max_i\gamma_i)$, supplying
families 1 and 2. For each $i\in I$, the two legal stopped tables
$(a,i;0,i,0)$, $a=1,2$, earn $S+t+\gamma_i-p_a$, where
$p_a=P\{w_a=1,w_i=0\}$. Their pair-loss sets are disjoint on
$\Omega_1\cup\Omega_2$, even in the presence of prefix $00$,
and $p_1+p_2\le S-a_i$. The better table gives family 3.

Write $P_a=\sum_{\Omega_a}P$, so $P_1+P_2=S$.
For $i<j$, table $(a,i;a,i,j)$ collects at least
$P_a+\gamma_i+\gamma_j$. Choosing $P_a\ge S/2$ gives family 4.
The stopped tables $(i,j;i,j,0)$ and $(i,j;i,j,k)$ give families
5 and 7. Their correct classes lie wholly in their respective
stopped cells, independently of suffixes. Table $(i,j;0,j,0)$
gives family 6 because the first cell contains pair mass $S-a_i$.
For $i<j<k$, tables $(i,j;0,j,k)$ and $(i,j;i,0,k)$ give
families 8 and 9, respectively: in the latter, pair cell $10$ has
mass $a_i$. Any additional rewards are nonnegative. Thus each of
the nine expressions is a lower bound from one complete legal table,
and $B_O(y)\ge B_*$ throughout the fixed-data class.

We bound the full support of (212.33), retaining every possible
winning label. The head support is $S+\max(t,\max\gamma)$.
At an early/late pair $(a,j)$ the early-zero cell maxima sum to
$S/2$. The other two maxima are

$$
\begin{aligned}
M_{10}&=\max\left\{(S-a_j)/2,\gamma_j,
                         (\gamma_n-a_j)_+\ (n<j)\right\},\\
M_{11}&=\max\left\{a_j/2+t,\gamma_n\ (n>j),
                              \min(\gamma_n,a_j)\ (n<j)\right\}.
\end{aligned}
\tag{212.35}
$$

Every correct-class index here is late. If $M_{10}$ uses its pair
baseline, $S/2+M_{10}+M_{11}$ is at most a family-1 or family-2
entry. Otherwise let its winning class be $n\le j$, of reward
$\gamma_n-\epsilon$, where $\epsilon=0$ for $n=j$ and
$\epsilon=a_j$ for $n<j$. Against the final baseline the total
is at most family 3 at $n$: for $n<j$, the correction
$-a_j+a_j/2\le a_n/2$, and for $n=j$ it is equality.
Against a different final correct class it is at most family 4,
after ordering the two indices. Against the same class, the two
complementary pieces sum to $\gamma_n$, so family 2 bounds it.
This proves every early/late full-pair bound without independent
allowances for its last two cells.

For a late pair $i<j$, let $b=S-a_i-a_j\ge0$.
The four full-label maxima are

$$
\begin{aligned}
M_{00}&=\max\{b,(\gamma_i-a_j)_+,
                (\gamma_n-\max(a_i,a_j))_+\ (n<i)\},\\
M_{01}&=a_j,\\
M_{10}&=\max\{a_i,\gamma_j,
                (\gamma_n-a_j)_+\ (i<n<j)\},\\
M_{11}&=\max\{t,\gamma_n\ (n>j),
 \min(\gamma_n,a_i,a_j)\ (n<i),
 \min(\gamma_n,a_j)\ (i<n<j)\}.
\end{aligned}
\tag{212.36}
$$

Indeed the zero-label pair projection is $(b,a_j,a_i,0)$, with
$t$ added in $11$. Early labels earn subsets of it.
For $n<i$, the threshold intervals give mass
$(\gamma_n-\max(a_i,a_j))_+$ in $00$ and
$\min(\gamma_n,a_i,a_j)$ in $11$; its off-diagonal interval
lengths are bounded by $a_j$ in $01$ and by $a_i$ in $10$.
For $n=i$ the only possible nonzero cells are $00,01$ with
masses $(\gamma_i-a_j)_+,\min(\gamma_i,a_j)$.
For $i<n<j$ they are the complementary $10,11$ entries;
$n=j$ contributes only $\gamma_j$ in $10$ and $n>j$ only
$\gamma_n$ in $11$. This proves (212.36) for all labels, including
earlier unqueried ones.

Choose the baseline on a tie in $00$ or $10$. When $00$ exceeds
$b$, let its winner be $n\le i$, with reward $\gamma_n-h$,
where $h=a_j$ if $n=i$ and $h=\max(a_i,a_j)$ if $n<i$.
When $10$ exceeds $a_i$, let its winner be $q\in(i,j]$, with
reward $\gamma_q-\epsilon$, where $\epsilon=0$ if $q=j$ and
$\epsilon=a_j$ otherwise. A final winner is terminal, future
$k>j$, earlier $k<i$, or intermediate $i<k<j$; $k=i,j$ is
impossible there. There are four exhaustive cases.

If neither cell gains, the support is $S+M_{11}$, bounded by
families 1 and 2.

If only $10$ gains, the support is
$S-a_i+\gamma_q-\epsilon+M_{11}$.
A terminal winner is bounded by family 6 at $(i,q)$; a future
winner by family 8 at $(i,q,k)$.
An earlier winner contributes at most $a_i$, giving family 2 at $q$.
For an intermediate winner with $q<j$, its contribution is at most
$a_j=\epsilon$, again giving family 2. If $q=j$, an intermediate
winner $k$ instead gives family 8 at $(i,k,j)$.

If only $00$ gains and $n=i$, the support is
$\gamma_i+a_i+M_{11}$.
For a terminal winner, $a_i\le S$ bounds this by family 3 at $i$;
for a future winner use family 9 at $(i,j,k)$.
Earlier or intermediate final rewards are at most $a_j$, so family 2
bounds them. If instead $n<i$, the support is
$\gamma_n+\min(a_i,a_j)+M_{11}$.
Since $\min(a_i,a_j)\le S/2$, a terminal winner is bounded by
family 3 at $n$, and a distinct correct winner by family 4.
If the final winner is that same $n$, its $00,11$ pieces are
parts of one measure. As $00$ gained, $\gamma_n>\max(a_i,a_j)$,
and the support is $\gamma_n+2\min(a_i,a_j)\le\gamma_n+S$,
bounded by family 2.

If both cells gain, the support is

$$
\gamma_n+\gamma_q+M_{11}+a_j-h-\epsilon,
\qquad a_j-h-\epsilon\le0.
\tag{212.37}
$$

A terminal winner gives family 5 and a third distinct correct class
gives family 7, after ordering the indices. If the final winner is
$q$, then $q<j$; its $10,11$ pieces sum to $\gamma_q$ and
$h\ge a_j$ leaves at most $\gamma_n+\gamma_q$.
If the final winner is $n$, then $n<i$.
When $q<j$, complementarity and $\epsilon=a_j$ give the same bound.
When $q=j$, the remaining expression is

$$
\gamma_n+\gamma_j+a_j-\max(a_i,a_j)+\min(a_i,a_j)
 \le\gamma_n+\gamma_j+S/2,
$$

since the last correction is at most $\min(a_i,a_j)\le S/2$.
Family 4 bounds it. Thus repeated winners never receive two copies
of the same correct mass.

Every full pair is now at most $B_*$. Short $N$ rules refine into
such pairs, so $B_N(V_*)\le B_*$. The stopped lower bound applies
to this very score and $B_O(V_*)\le B_N(V_*)$, proving both
attained minima. Totals give (212.34). The proof makes no divisions
by masses, and includes $L=3$, $t=0$, zero classes, zero carrier,
unequal tied thresholds and every closed endpoint. It asserts global
catalog minima, not pair-by-pair equality or decrease. $\square$

For a growing unequal instance, let $m=L-2\ge4$,
$a_\varnothing=0$, $a_3=1$, $a_j=2$ for $j\ge4$,
$\gamma_j=3$ and $t=2$. Balanced lifts with correct mass three at
each sole-zero word give an input $Y$.
Here $S=2m-1,W=S+2$. On a late pair the full maxima are
$(S-a_i-a_j,3,3,3)$ and the stopped maxima are
$(S-a_i,3,3)$; maximizing gives $S+6,S+5$.
The head and early/late pairs have support at most $S+5$, as do
short schedules by direct singleton marginals. Thus the costs are
$(4,3)$. Constructor (212.33) puts mass two at each sole-zero word
and mass one at $1^{j-1}0^{L-j+1}$ in class $j$, adding coincident
rows at $j=L$. Formula (212.31) gives its two costs as three.
Scaling all weights by $1/3$ gives an actual unit-$O$ input and a
same-$Q$ certificate of cost one at every such length.

For the original class 3, every suffix unary zero moment is zero.
Its conditioned carrier has one suffix one per atom and at least
two suffix zeros. The signed cut $1-\sum_{j>3}\mathbf1_{v_j=0}$
has target mass three and positive-part carrier integral zero.
Thus exact unary matching does not produce this comparison; the
threshold attainer changes those unaries. This is a route distinction,
not exclusion from the old signed or convex certificate set.
At $t\ge\max\gamma$, the protected-terminal minimum is already
203.2; the equal-pair specialization is already 209.3, including
207.17's bounded subcase. Formula (212.31) supplies the unequal-star
minimum for arbitrary terminal mass. Its carrier assumption excludes
atoms with two late ones, and its input class excludes positive early
correct mass, base rows and late pair rows. No reduction of general
complete scores to this class is asserted.

### 212.4 Graph coupling inside the complete score catalogs

**Definition 212.9 (One graph stock and the full preserving fiber).**
Let $r\ge1,m\ge2$, $L=r+m+2$,
$I_c=\{3,\ldots,r+2\}$, $J=\{r+3,\ldots,L\}$ and
$I=I_c\cup J$. Let $G=(J,E_G)$ be any finite simple graph.
Choose $g>0$, $0\le\gamma_n\le g$ for $n\in I_c$, and $t\ge g$.
For a set $Z$ of addresses, write $w(Z)$ for the full word with
zero set exactly $Z$. On the late cube, identified by its zero sets,
define the single measure

$$
\nu=2g\delta_\varnothing+2g\sum_{i\in I}\delta_{\{i\}}
       +g\sum_{\{i,j\}\in\binom I2\setminus E_G}\delta_{\{i,j\}},
\qquad
S=|\nu|=g\left(2(|I|+1)+\binom{|I|}{2}-|E_G|\right).
\tag{212.38}
$$

Graph edges are only between vertices of $J$; all pairs involving
$I_c$ are included among the nonedges in this formula.
Put $B=S+t$ and $\Gamma=\sum_{n\in I_c}\gamma_n$.
For each $n\in I_c$ choose any actual measure $\mu_n$ on all
subsets of $J$ of mass $\gamma_n$. Assemble the score $Y(\mu)$ by

$$
P_{w(\{1\}\cup Z)}=P_{w(\{2\}\cup Z)}=\nu(Z)/2,\qquad
C_{w(\{n\}\cup Z)}=\mu_n(Z),\qquad A=0,\quad T=t.
\tag{212.39}
$$

In the pair formula $Z\subseteq I$; in the correct formula
$Z\subseteq J$. Thus every correct atom has first zero $n$.
The quotient is $q=(\beta,\Gamma+B)$, with $\beta_n=\gamma_n$
on $I_c$ and zero elsewhere, and $W_{Y(\mu)}=B$.

For $0\le c_j\le\gamma$, define the common-coupling minimum

$$
\kappa_G(\gamma,c)=
\min_{\substack{\mu\ge0,\ |\mu|=\gamma\\
                       \mu\{Z:j\in Z\}=c_j\ (j\in J)}}
       \max_{e\in E_G}\mu\{Z:e\subseteq Z\}.
\tag{212.40}
$$

The maximum for an edgeless graph is zero. The domain is compact and
nonempty: for $\gamma>0$ an independent product of Bernoulli variables
with means $c_j/\gamma$, scaled by $\gamma$, is one feasible measure;
for $\gamma=0$ every $c_j=0$ and only the zero measure is feasible.
This product supplies nonemptiness, not a claim of optimality.

Given $c_{nj}\in[0,\gamma_n]$, let $\mathcal F_G(c)$ contain all
full nonnegative scores $V$ satisfying

$$
\begin{gathered}
Q(V)=q,\qquad \sum_wP_w+T=B,\\
\sum_{w:w_i=w_j=0}P_w=0\quad(\{i,j\}\in E_G),\qquad
\sum_{w\in\Omega_n:w_j=0}C_w=c_{nj}
                      \quad(n\in I_c,j\in J).
\end{gathered}
\tag{212.41}
$$

This fiber permits all full output rows. It does not fix $\nu$, the
early pair allocation, individual pair rows, terminal mass, or other
correct suffix coordinates. Its explicit invariants, rather than an
implicit restriction to (212.39), define its competitor class.

**Theorem 212.10 (Complete graph embedding and attained fiber minimum).**
For the actual assembled score (212.39), every stopped schedule has
support $B$. Every full schedule also has support $B$ except possibly
graph-edge pairs, on which

$$
B_N^{ij}(Y(\mu))=B+\max_{n\in I_c}\mu_n\{Z:i,j\in Z\}
                           \quad(\{i,j\}\in E_G).
\tag{212.42}
$$

In particular $\Delta_O(Y(\mu))=0$ and
$\Delta_N(Y(\mu))=\max_{n,e}\mu_n\{e\subseteq Z\}$.
Over the larger full-score fiber (212.41), one score attains

$$
\min_{V\in\mathcal F_G(c)}\Delta_N(V)
       =\max_{n\in I_c}\kappa_G(\gamma_n,c_n),
\qquad \Delta_O(V)=0
\quad\text{for that same attainer}.
\tag{212.43}
$$

A zero-cost score in the fiber exists exactly when

$$
c_n/\gamma_n\in\operatorname{STAB}(G)
   :=\operatorname{conv}\{\mathbf1_Z:Z\subseteq J
                                  \text{ is independent in }G\}
\quad\text{for every }\gamma_n>0;
\tag{212.44}
$$

zero classes require $c_n=0$. A certificate of the form $(V,0)$ with
$V$ in this fiber exists exactly when the maximum in (212.43) is at
most one. The same criterion holds if any $\theta$ in (212.5) is
allowed while retaining $Q(V)=q$.

**Proof.** For every late pair $i<j$ the stock has
$\nu_{01},\nu_{10},\nu_{11}\ge2g$.
Its $00$ mass is zero on a graph edge and exactly $g$ on a nonedge.
Each individual correct label contributes at most $\gamma_n\le g$
to any cell; early label rewards are subsets of the zero-label pair
reward. On a nonedge zero therefore dominates all four cells.
On an edge, whose endpoints are both after every $n\in I_c$, the
full maxima are precisely

$$
\left(\max_n\mu_n\{i,j\in Z\},\ \nu_{01},\ \nu_{10},\ \nu_{11}+t\right).
\tag{212.45}
$$

The earlier unqueried correct labels are retained in its first maximum.
For a stopped late pair, the merged first-zero stock
$\nu_{00}+\nu_{01}\ge2g$ dominates every correct unary reward;
the other two cells are also dominated by zero. Its support is $B$.

At the head pair, the full maxima are $(0,S/2,S/2,t)$ and the
stopped maxima $(S/2,S/2,t)$, using $t\ge g$.
At an early/late pair $(a,j)$ the early-zero pieces sum to $S/2$.
In $10$ the pair baseline is $\nu\{x_j=0\}/2\ge g$;
in $11$ it is $(S-\nu\{x_j=0\})/2+t\ge g$.
They dominate every correct label, so both supports are $B$.
Every singleton has a full refinement at an early-containing pair
of support $B$; the empty function refines into the head pair.
Constant zero already earns $B$. Consequently all short supports
are exactly $B$, also in $O$. This proves the complete identity,
including pairs inside $I_c$ and pairs between $I_c,J$.

For any full score, direct summation gives

$$
K-\sum_j\beta_j=2\sum_wA_w+\sum_wP_w+T.
\tag{212.46}
$$

Inside (212.41), its left side is $B$ and its last two terms total
$B$. Nonnegativity forces $A=0$. Thus the correct masses are precisely
$\gamma_n$ in $I_c$, zero in all other classes, and $W_V=B$.
Project the actual class-$n$ correct measure to $J$, obtaining
$\sigma_n$ with the prescribed mass and all prescribed unaries.

For $n\in I_c$ and an edge $e=\{i,j\}$, $i<j$, use the legal
full table

$$
D_{n,e}=(i,j;n,0,0,0).
\tag{212.47}
$$

Constant zero earns $B$. Changing its $00$ output to $n$ loses
no pair mass by (212.41) and gains exactly $\sigma_n\{e\subseteq Z\}$.
Thus every member of the full fiber has
$\Delta_N(V)\ge\max_{n,e}\sigma_n\{e\subseteq Z\}
\ge\max_n\kappa_G(\gamma_n,c_n)$.
Compactness of each marginal polytope and continuity of its finite
maximum supply minimizing measures $\mu_n$. Assemble all these
minimizers with the same stock (212.38). The complete support identity
proves equality in (212.43) and stopped cost zero for that very score.
The cost is a maximum across classes, not their sum; there is no
separate replenishment of the stock for different pairs or classes.

A nonnegative measure has zero intersection on every graph edge
exactly when all of its positive atoms are independent sets. Dividing
by its positive mass gives exactly the convex combinations in
(212.44), and every such combination gives an actual measure.
This uses the classical stable-set polytope, as defined in
Pulleyblank and Shepherd, [*Formulations for the Stable Set Polytope*,
author-hosted manuscript, §1](https://bshepherd.ca/img/papers/wpclaw.pdf),
with manuscript SHA-256
`08515245032617db6c0627463db32cb5b6db035f8ce032cf8c620948f3b46a52`.
Their incidence vector is $\mathbf1_Z$ here, and its convex coefficients
are $\mu(Z)/\gamma$. The graph may be arbitrary; no graph-class
algorithm or complexity bound from that paper is assumed.
The score embedding and the full-fiber lower bound are (212.45)–(212.47).
The zero-class and edgeless cases follow directly from the definitions.
Finally exact quotient equality makes the residual zero, so allowing
$\theta>0$ cannot improve the available score budget; $\theta=0$
is sufficient whenever the displayed minimum is at most one.
$\square$

**Theorem 212.11 (Odd-cycle simultaneous attainers and full-output escape).**
For the construction of 212.9, let $G=C_m$ with $m=2k+1\ge3$,
and prescribe $c_{nj}=\gamma_n/2$. Then

$$
\kappa_{C_m}(\gamma_n,c_n)=\frac{\gamma_n}{2m},\qquad
\min_{\mathcal F_{C_m}(c)}\Delta_N
 =\frac{\gamma_*}{2m},\qquad
\gamma_*:=\max_{n\in I_c}\gamma_n.
\tag{212.48}
$$

All edge values and all unaries are attained by one measure per class,
and these measures coexist with the single stock. Every proper edge
subfamily nevertheless permits a simultaneous zero-cost repair on
those selected pair schedules with the same unaries and stock.
This last statement gives no zero-cost assertion on the omitted edges.
The unit threshold $\gamma_*=2m$ is attained, including equality.

More generally, for any graph in 212.9 and every full nonnegative
score $V$ with $Q(V)=q$, drop all the other restrictions of (212.41).
For $n\in I_c$, $U\subseteq J$, set

$$
A_n=\sum_{\Omega_n}A_w,\quad
c^V_{nj}=\sum_{w\in\Omega_n:w_j=0}C_w,\quad
Z_J(w)=\{j\in J:w_j=0\},\quad
e_U(Z)=|E(G[U\cap Z])|.
$$

Writing $\alpha_U=\alpha(G[U])$ for the independence number, one has

$$
\sum_{j\in U}c^V_{nj}-\alpha_U\gamma_n
 \le |E(G[U])|\Delta_N(V)+\alpha_U A_n
               +\sum_{w\ne1^L}(A_w+P_w)e_U(Z_J(w)).
\tag{212.49}
$$

In the odd-cycle case $U=J$, this reads

$$
\frac{\gamma_n}{2}\le m\Delta_N(V)+kA_n
 +\sum_w(A_w+P_w)e_J(Z_J(w))
 +\sum_{j\in J}\left(\frac{\gamma_n}{2}-c^V_{nj}\right).
\tag{212.50}
$$

The last sum is signed unary drift. The stock term counts each
actual atom with its number of induced edges; it is not an allocation
of independent stocks to the edges.

**Proof.** For any subset $Z$ of a graph, deleting at most one chosen
endpoint for each induced edge leaves an independent set. Therefore
$|Z\cap U|\le\alpha_U+e_U(Z)$.
For $C_{2k+1}$ this gives $|Z|-k\le e_J(Z)$.
Integrating against a measure of mass $\gamma$ with all unary masses
$\gamma/2$ yields

$$
\sum_{e\in E(C_m)}\mu\{e\subseteq Z\}\ge\gamma/2.
\tag{212.51}
$$

The largest of the $m$ edge masses is at least $\gamma/(2m)$.
This is the classical independent-set/odd-cycle counting inequality,
used here for the actual correct-class measure.

Index the cycle by $0,\ldots,2k$ and put
$Z_+=\{0,2,\ldots,2k\}$, $Z_-=J\setminus Z_+$.
Give each of their $2m$ cyclic rotations mass $\gamma/(2m)$.
Each complementary pair gives every unary mass $\gamma/(2m)$,
so the sum has unaries $\gamma/2$ and total $\gamma$.
Each rotation of $Z_+$ contains exactly one cycle edge, each rotation
of $Z_-$ contains none, and every edge appears once among the former
rotations. Thus every edge mass is exactly $\gamma/(2m)$.
Use this same construction for each class and (212.43) proves (212.48).
It also covers $\gamma=0$ by the zero measure.
A proper subset of the cycle edges is bipartite; choose a bipartition
of its vertices, including any isolated vertices, and put mass
$\gamma/2$ on each of the two complementary color classes.
This one measure has half unaries and no intersection on any selected
edge. Formula (212.42) proves their simultaneous local repair.
It also identifies why an omitted edge can retain positive cost.

For the unrestricted output inequality, $\beta_1=\beta_2=0$
implies $W_V=\sum_wA_w+\sum_wP_w+T$ even when $A$ is nonzero.
The excess of the same legal table (212.47), with
$E_e=\{w:w_i=w_j=0\}$, is exactly

$$
(z_{D_{n,e}}-r)\cdot V
 =C_n(E_e)+P_n(E_e)-A(E_e)-P(E_e),
\tag{212.52}
$$

where the subscript restricts to $\Omega_n$ and the unsubscripted
measure sums over every zero word. The positive word is never in
$E_e$. Since every table excess is at most $\Delta_N(V)$ and
$P_n(E_e)\ge0$,

$$
C_n(E_e)\le\Delta_N(V)+A(E_e)+P(E_e).
\tag{212.53}
$$

The actual class-$n$ correct measure has mass $\gamma_n+A_n$,
because its quotient coordinate is $\gamma_n$.
Integrate $|Z_J(w)\cap U|\le\alpha_U+e_U(Z_J(w))$ against
this same measure and sum (212.53) over $E(G[U])$.
Finite interchange of sums gives exactly
$\sum_w(A_w+P_w)e_U(Z_J(w))$ for the stock incidence term.
This proves (212.49), with its multiplicities and without changing
any measure between edges. Substituting $|J|=m=2k+1$ and adding
the signed drift to both sides gives (212.50).
All zero masses, empty $U$, edgeless induced graphs, and closed cost
endpoints are included. $\square$

At half marginals, $X_j=\mathbf1_{j\in Z}$ under $\mu/\gamma$
is a symmetric Bernoulli vector. Huber and Marić,
[*Bernoulli Correlations and Cut Polytopes*, arXiv:1706.06182v2,
Theorem 4 and §§4.1–4.2](https://arxiv.org/pdf/1706.06182v2),
identify its jointly attainable agreement vectors with a switched
cut polytope, using mixtures of complementary two-point laws.
Here the agreement coordinate on an edge is
$2\mu\{i,j\in Z\}/\gamma$, since its $00$ and $11$ probabilities
are equal at half marginals. The rotation and bipartition measures
above are concrete mixtures of that kind. This classical common-law
mechanism does not make separately optimal edge couplings compatible;
nor does its symmetric statement apply to arbitrary unequal marginals.
For general $c$ the exact domain is the actual marginal polytope in
(212.40), and (212.44) is the independent-set convex-hull criterion.

For an explicit full input, take $L=8$, $I_c=\{3\}$,
$J=\{4,5,6,7,8\}$, the cycle with edges
$45,56,67,78,48$, and $\gamma_3=g=t=11$.
The stock has mass 22 on the empty zero set and each singleton,
and mass 11 on each nonedge pair of $I=\{3,\ldots,8\}$.
Its balanced lifts specify all 34 positive pair rows and $S=264$.
Choose $C_{11001010}=C_{11010101}=11/2$.
Then $W=275$, $q=(11e_3,286)$ and every class-3 unary on $J$
is $11/2$. Pair $48$ has full maxima
$(11/2,55,55,165)$ and stopped maxima $(55,55,165)$.
All other full pairs and all short schedules have support 275;
all stopped schedules do as well. The input costs are $(11/2,0)$.
The ten rotated alternating atoms, each of mass $11/10$, give
complete costs $(11/10,0)$ and attain the full preserving-fiber
minimum. For $\gamma_*>2m$, (212.50) shows how a unit-cost exact-$Q$
output must pay by some combination of signed unary drift, base mass
and edge-bearing stock; preserving them all cannot suffice.

These graph obstructions do not prove $E_N$ nonmembership.
For every quotient in 212.9, move each correct measure to
$\mu_n=\gamma_n\delta_\varnothing$, keeping the same $\nu,t$.
The resulting nonzero score $V_0$ has $Q(V_0)=q$ and, by the
complete identity, $\Delta_N(V_0)=\Delta_O(V_0)=0$.
It is directly the existing threshold score of 203.2: for each
$n\in I_c$ and $j>n$, the stock atom $\{n\}$ alone gives
$a_{nj}=\nu\{x_n=0,x_j=1\}\ge2g\ge\gamma_n$, so every
threshold suffix bit is one. Its zero-cost certificate is allowed by
199.5–199.6 and is included in the zero-$O$ endpoint of 203.3.
Both $\theta=0$ and $\theta=1$ are permitted in (212.5).
For every $b\in H_N$ and the same actual feasible full $\lambda$,

$$
F_q(b)=V_0\cdot h(b)\le V_0\cdot G_N\lambda\le0.
\tag{212.54}
$$

Thus none of these quotients can satisfy the strict original-negative
inequality $F_q(b)>M$ with $M\ge1$.
The obstruction concerns the explicit unary/stock invariants, even
for nonlinear choices of the full output score. Those invariants
are not required by the unrestricted certificate definition.

### 212.5 Suppliers, source correspondence and the remaining comparison

**Definition 212.12 (Scope and original-source interface).**
The substantive relations in this section are repository-derived:
the full-score surplus and split-defect calculation with its coupled
moment-box criterion; the equality-block invariant and whole-fiber
moved-mass minimum; the unequal-star minimum for all terminal masses;
and the graph embedding, attained full preserving-fiber minimum and
unrestricted-output escape accounting. The three carrier variants
in 212.1 are one mechanism. Restricted-method failures neither prove
nonmembership in $E_N$ nor exclude the old convex, signed and nonzero
zero-cost certificates.

The supplier correspondences are specific. The signed hull and the
complete alternative are
[198.5 and 199.3–199.6](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md);
(212.14) evaluates that hull rather than replacing it.
The threshold constructor is
[203.2–203.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md),
with $a_{nj}=a_j$ in (212.33), and its $t\ge\max\gamma$ endpoint
is directly reused. The equal-pair minimum and exact-unary matching
belong to
[209.3 and 209.12–209.15](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md).
The latter supplies the $X=c$ endpoint in 212.6; the safe four-word
switch is 211.2. Full-fiber minima here impose exactly their displayed
constraints, rather than inheriting extra pairwise or stock constraints
from those suppliers. The conditional-moment and stock thresholds in
210, and the fixed-menu and positive-linear-selector results in 211,
retain their different domains. These comparisons are bounded to the
named owner results and primary references, without an exhaustive
novelty or worldwide-priority assertion.

Kaibel's versioned finite polyhedral representation and projection
results supply the classical geometry used inside the carrier proof;
the box consists of actual suffix measures, not hypothetical independent
moments. Clarke–Kosta's stated integer-fiber results provide the precise
move-applicability comparison, not a real-score maximum theorem.
Pulleyblank–Shepherd's author-hosted §1 supplies the classical
independent-set convex hull. Huber–Marić's version 2 concerns symmetric
Bernoulli agreement vectors, with the half-marginal correspondence
given above. None of these classical results is a new standalone
assertion of this section.

Blackwell, [*Comparison of Experiments*, pp. 93–98, §§2–5](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf),
provides the attainable-risk and common-kernel framework.
A Boolean word is a state, a schedule supplies a transcript partition,
and a label is an action in that comparison. Its common stochastic
postprocessing requirement does not itself respect increasing first-zero
stopping or the hard-two count. The decision-theoretic correspondence
therefore supplies no missing acquisition conversion. In particular,
separately feasible cells or edge marginals do not constitute one
normalized common rule.

Concretely the actual source and static answers remain

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
        \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\qquad
n(x)=\min\{i:q_i(x)=0\},
\end{aligned}
\tag{212.55}
$$

where $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$ and $p_i$ are the
increasing primes. Boundaries 35.2 supplies actual witnesses for every
finite pattern on arbitrary finite addresses. Hence all Boolean words
used above, including multiple-zero words, have the original meaning.
The full output carrier is
$\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, with each
block a copy of $(0,1)$ and the disjoint-union Borel sigma algebra.
The consumer returns unknown on $B_j$ and proposes $j$ on $P_j$;
its original nonatomic targets remain those of Acquisition Resources
73.1. The distinct marks $\theta_j=(B_1,1/(j+2))$ support the
separately selected laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                    +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_j\longrightarrow0.
\tag{212.56}
$$

Every sequence in (212.56) remains in the original comparison.
Advice is zero, one source-independent seed fixes a deterministic
rule common to all sources, and handoff is actually sourcewise almost
surely finite. The resource is at most two actual requests, including
repetitions and ignored replies. $N_2$ preselects its entire schedule
and obtains the replies; $O_2$ preselects an increasing schedule and
stops at its first queried zero or exhaustion. A queried zero need
not be the actual first absence. Competitors retain arbitrary addresses
and arbitrary outputs in the full carrier. The error remains uniform
over all actual sources and all Borel events, with no source law,
mean-request, address, depth or runtime surrogate.

The finite measures and table maximizers in this section are dual
scores. Only normalized probability-vector configurations satisfying
all event rows can use
[109.1 and 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md).
For a degree-at-most-two probability-vector kernel
$p_w=c+\sum_i\ell_iw_i+\sum_{i<j}Q^{\rm ker}_{ij}w_iw_j$,
109.1 gives the stopped criterion

$$
c\ge H^{\rm ker}:=\sum_i
 \left(\sum_{j>i}(-Q^{\rm ker}_{ij})_+-\ell_i\right)_+.
\tag{212.57}
$$

Normalization makes its scalar schedule-mass bound redundant, as
in 108.4; these are kernel coefficients, not the score quotient $Q$.
Theorem 110.2 retains full-carrier, arbitrary-address necessity and
exact closed-cap sufficiency. A normalized finite configuration is
realized by a partition of one source-independent uniform seed selecting
the entire schedule and terminal table before replies. Different
configurations can use different partitions and their common refinement
on that same seed, without requiring seedwise equal outputs.
The actual execution asks at most two questions and hands off finitely.
A support-maximizing table alone is not asserted cap-feasible.

For $0<\varepsilon\le1$, at the actual active length
$L_a=\max(\{j:a_j>\varepsilon\}\cup\{0\})$, every actual
$n>L_a$ retains the exact tail identity supplied by 110.2:

$$
\operatorname{TV}\left(\sum_{j=0}^{L_a}p_{1^{L_a}}(j)\delta_{\theta_j},
 (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
 =\max\{1-p_{1^{L_a}}(0),a_n\}.
\tag{212.58}
$$

Thus equality $a_n=\varepsilon$ is retained at a positive closed cap.
Zero score masses and auxiliary $e=0$ hull vertices do not replace
positive original tails. Small active lengths and cap one remain
within the existing transport, and caps above one admit immediate
base output.

The universal inclusion remains unresolved:

$$
Q(y)\in E_N\quad\text{for every complete }y\ge0
 \text{ with }\Delta_O(y)\le1\text{ and every }L\ge3.
\tag{212.59}
$$

Its existing equivalent clipped comparison is
$\rho_O(b)\le\max(1,\rho_N(b))$ for every $b\in H_N$.
The original all-amplitude, all-positive-closed-cap question remains
$\mathcal F_N(a,\varepsilon)\ne\varnothing\Rightarrow
\mathcal F_N(a,\varepsilon)\cap\mathscr C_{L_a}\ne\varnothing$,
with the all-word slice of 110.1 and normalized stopped region of
109.1. Arbitrary base and late pair rows, unrestricted early credit,
overlapping positive-event carriers, and unordered growing profiles
outside the stated conditions still require a jointly affordable
score and signed residual. The fixed-baseline equivalence does not
supply that universal affordability; the explicit quartet rules out
that promotion of this method.

An original negative requires one actual complete unit-$O$ score $y$,
a point in $H_N$, and the same actual full-$N$ configuration throughout:

$$
b\in H_N,\quad y\ge0,\quad\Delta_O(y)\le1,\qquad
\lambda\ge0,\quad G_N\lambda\ge h(b),\quad
M=\sum_D\lambda_D\ge1,\qquad F_{Q(y)}(b)>M.
\tag{212.60}
$$

It also requires the owned original-source transport to an actual
common-seed $N_2$ attainer and a uniform lower certificate against
every full-carrier arbitrary-address $O_2$ competitor. A point in
$H_L$ alone, or separately feasible cells using different configurations,
does not meet (212.60). The graph quotients all have the zero-cost
core (212.54), and the equality-block and star families have their
explicit same-$Q$ certificates. These conclusions are structural
relations and restricted-method boundaries, not original separators.
The exact-law obstruction 112.2 still permits a different stopped
law at the same cap.

## 追加锚（本行以下为增补区）
