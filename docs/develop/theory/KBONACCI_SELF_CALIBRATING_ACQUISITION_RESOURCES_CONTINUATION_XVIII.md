# KBONACCI self-calibrating acquisition resources XVIII

## 315. Original objects and the complete affine feasibility problem

**Definition 315.1 (Source, targets and hard resource).**
Use the source and carrier of
[297.1–297.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVII.md).
Explicitly, $F_0=0$, $F_1=1$, $F_{k+2}=F_{k+1}+F_k$, $p_i$ are the
increasing primes, and

$$
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\quad
N(r,g)=1+F_rg,\quad q_i(x)=[p_i\mid N(x)],\quad
n(x)=\min\{i:q_i(x)=0\}.
\tag{315.1}
$$

The source is countable, replies are static, and every actual first
absence is finite. There is no probability law on $X$ or supplied
source label, integer $N(x)$, first absence or extra observation.
The full carrier is the Borel disjoint union
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, each block a
copy of $(0,1)$. The unchanged consumer returns unknown on $B_j$ and
proposes $j$ on $P_j$, without making prime requests.

The original nonatomic targets remain
$\mu_x^{\rm orig}=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$ of 297.1:
$0<h_0<1$, $t_x=\sum_i3^{-i}q_i(x)$,
$Z_t=\int_0^1e^{tu}\,du$, $\nu_x$ has density $e^{t_xu}/Z_{t_x}$ on
$B_{n(x)}$, $\pi_j$ is uniform on $P_j$, and $\Omega(x)$ counts
distinct prime divisors of $N(x)$. The separately selected accuracy
targets in this volume are

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                   +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
\theta_j=(B_1,1/(j+2)),\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\to0.
\tag{315.2}
$$

For an acquisition $A$, set
$e_a(A)=\sup_{x\in X}\operatorname{TV}(\mathcal L(A(x)),\lambda_x^a)$.
All accuracy conclusions below concern (315.2).

The original classes are exactly Definition 90.1 of
[Acquisition Resources](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md).
There is zero advice, one source-independent common seed, and actual
sourcewise almost-sure finite handoff. In $\mathcal N_2$ the entire
schedule is preselected and all its replies are acquired. In
$\mathcal O_2$ an increasing schedule is preselected and execution
stops at its first **queried** zero or exhaustion. The second address
does not depend on the first reply. The hard bound is two actual
requests, including repetitions and ignored replies. Competitors retain
arbitrary addresses and all Borel outputs in $\Theta$; no bound on
address, runtime or mean request count is imposed.

**Definition 315.2 (Full rows, allocations and scores).**
For $L\ge3$ retain every $w\in\{0,1\}^L$, every output label
$0,\ldots,L$, and $+=1^L$. At a word with first zero $n$, the
three independent events $A,C,P$ are $\{0\},\{n\},\{0,n\}$ and
their demands are $1-b_n-e,b_n-e,1-e$. At $+$ retain the event
$\{0\}$ with demand $1-e$. Negative singleton demands remain literal.
For a probability vector and $0\le b_n\le1$,

$$
\operatorname{TV}(p_w,(1-b_n)e_0+b_ne_n)
=\max\{1-b_n-p_w(0),\ b_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
\tag{315.3}
$$

For unrestricted real $(b,e)$ these linear demands define an affine
feasibility problem; a probability-target interpretation additionally
requires normalized laws and $b_n\in[0,1]$.

The complete finite $N$ catalog contains constants, singletons and every
$N(i,j;u,v,s,z)$ with arbitrary output labels on $00,01,10,11$.
The complete $O$ catalog contains constants, singletons and every
$O(i,j;u,s,z)$, $i<j$, on stopped cells $0,10,11$. Earlier and
unqueried output labels are legal. Repetition gives singleton information
without refunding an actual request; reversal of static queries permutes
the four cells.

Write $z_D$ for the full event-incidence vector of $D$, and set

$$
R=O(1,2;1,2,0),\quad \alpha=(1,1,0,\ldots,0),\quad
r=z_R=d(\alpha,0),\quad h=d(b,e)-r,\quad
G_C=(z_D-r)_{D\in\mathcal D_C}.
\tag{315.4}
$$

One complete feasible allocation is one $\lambda\ge0$ satisfying
every row of $G_C\lambda\ge h$, with its single finite mass
$M=\sum_D\lambda_D$. Mass one is normalized feasibility. Dividing
by $M$ does not normalize an allocation at unchanged $(b,e)$.

A nonnegative full score $Y=(A_w,C_w,P_w;T)$ has rewards

$$
\begin{aligned}
g_Y(w,\ell)&=A_w[\ell=0]+C_w[\ell=n(w)]
                           +P_w[\ell\in\{0,n(w)\}],\quad w\ne+,\\
g_Y(+,\ell)&=T[\ell=0],\\
W_Y&=Yr,\quad B_C(Y)=\max_DYz_D,\quad\Delta_C(Y)=B_C(Y)-W_Y,\\
\beta_n&=\sum_{w:n(w)=n}(C_w-A_w),\quad
K_Y=\sum_{w\ne+}(A_w+C_w+P_w)+T,\\
F_{QY}(b,e)&=\sum_n\beta_n(b_n-\alpha_n)-K_Ye=Yh.
\end{aligned}
\tag{315.5}
$$

The reused nonnegative pairing from 297.5 and 309.2 is

$$
F_{QY}(b,e)\le YG_C\lambda
 =\sum_D\lambda_D(Yz_D-W_Y)\le M\Delta_C(Y).
\tag{315.6}
$$

It pairs a score with the same entire allocation; it does not combine
separately optimized output, head or tail budgets.

**Reused correspondence 315.3 (Actual words and exact closed caps).**
The actual finite-pattern interface is the elementary proof of 297.3
and Proposition 280.1, without dependence on an absent locator.
For completeness, modulo a prime $p$ the Fibonacci matrix
$Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ is invertible,
and
$Q^k=\left(\begin{smallmatrix}F_{k+1}&F_k\\F_k&F_{k-1}\end{smallmatrix}\right)$.
It is scalar precisely when $p\mid F_k$. Its class in the finite group
$\operatorname{PGL}_2(\mathbb F_p)$ has order $z(p)\ge3$, since
$F_1=F_2=1$. Consequently $p\mid F_k$ iff $z(p)\mid k$.
For a finite prime set of product $D$, choose a prime $r$ above all
these ranks, large enough that $F_r\ge10(D+2)$. Then no rank divides
$r$, so $F_r$ is invertible modulo $D$. Prescribe
$g=-F_r^{-1}\pmod p$ at desired ones and $g=0\pmod p$ at desired
zeros. CRT gives a residue modulo $D$. The actual integer interval
$[\lceil F_r/10\rceil,\lfloor F_r/5\rfloor]$ has length at least
$F_r/10-2\ge D$, and therefore contains a representative. This
realizes every finite word, including all multiple-zero words and
positive prefixes. Finite prime support of the actual positive integer
$N(r,g)$ gives finite first absence.

Reuse the complete
[Theorems 109.1 and 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md)
and the prefix consequence 280.3, as stated in 297.3 and proved in
309.3. At a positive closed cap $c\le1$, an arbitrary original
competitor supplies some normalized finite representative in its own
class on $L_a=\max(\{i:a_i>c\}\cup\{0\})$ bits. Necessity uses
countability for one common probability-one execution event, finite
actual witnesses, whole-schedule truncation, sourcewise finite handoff
and finite-simplex compactness. It preserves class feasibility and
does not assert preservation of an arbitrary initial law or coupling.
The normalized stopped criterion is $c_0\ge H$ coordinatewise for
$p_w=c_0+\sum_i\ell_iw_i+\sum_{i<j}Q_{ij}w_iw_j$,
$H=\sum_i(\sum_{j>i}(-Q_{ij})_+-\ell_i)_+$; its scalar schedule
budget follows from normalization. Degree at most two alone is insufficient.

At a required prefix $K$, restrict a longer representative by fixing
higher replies to zero, projecting higher labels to zero and contracting
constant observations. TV contracts, including on a positive low
prefix whose target projects to zero. Extend a shorter representative
by ignoring added inputs. For a probability law on labels at most $H$
and any actual $n>H$, the exact marked-target identity is

$$
\operatorname{TV}(p_+,(1-a_n)e_0+a_ne_n)
                      =\max\{1-p_+(0),a_n\}.
\tag{315.7}
$$

Thus each newly represented first-zero class satisfies the cap, since
$a_n\le c$. All independent rows and closed ties are retained in
one representative. These are proof representations, not free actual
observations. A finite positive word represents later actual zeros,
not an infinite all-positive source. Every positive vanishing tail
is retained; no summability assumption is needed.

The support rule reused from Lemma 309.3 will be applied twice below.
For a $d$-bit score put

$$
m^Y_{ij,uv}=\max_{0\le\ell\le d}
 \sum_{w:(w_i,w_j)=uv}g_Y(w,\ell),\qquad uv=00,01,10,11.
\tag{315.8}
$$

Four-cell sums at most $W_Y$, with the stopped anchor attaining $W_Y$,
prove $B_N=B_O=W_Y$. A full $N$ table chooses a label independently
in each cell. Constants, singletons and repeats coarsen a distinct-pair
partition, reversal permutes cells, and stopped tables merge $00,01$;
none increases the sum of cell maxima. At every embedding
$(1,2,j_1,\ldots,j_{d-2})$, set nonskeleton bits to one on scored
words and map numerical labels accordingly. Outside queries then
give constant or singleton information on that support; outside labels
earn zero. Hence the bound is for the complete catalog at every
horizon and gap, with all unscored constraints still present. Pairing
with (315.6) proves the resulting affine relation for any real profile
and any finite allocation mass. The preceding closed-cap transport
gives necessity for every original arbitrary-address, full-carrier
competitor. Applying each positive cap above its error and decreasing
the cap proves the corresponding error lower bound, including zero
error. At error one the specific inequalities below follow directly
from $a_i\le1$.

## 316. A three-tail constraint from one complete score

**Definition 316.1 (The ten-coordinate score $Z_8$).**
Its complete nonzero coefficients are the following 61 integer rows.
Every $A$ and every unlisted coefficient is zero. The rows are scored
events; zero coefficients delete no feasibility constraints.

| Row | Word | Weight |
| --- | --- | --- |
| C | 1011000110 | 74 |
| C | 1011001110 | 2 |
| C | 1100001001 | 76 |
| C | 1100101100 | 76 |
| C | 1101000010 | 16 |
| C | 1101001111 | 60 |
| C | 1101010000 | 68 |
| C | 1101110100 | 8 |
| C | 1110001001 | 74 |
| C | 1110010110 | 16 |
| C | 1110011101 | 62 |
| C | 1110100001 | 70 |
| C | 1110100110 | 82 |
| C | 1110101110 | 2 |
| C | 1110111010 | 74 |
| C | 1111001010 | 16 |
| C | 1111001011 | 49 |
| C | 1111001101 | 87 |
| C | 1111010000 | 228 |
| C | 1111100000 | 54 |
| C | 1111100100 | 84 |
| C | 1111100101 | 76 |
| C | 1111101010 | 166 |
| C | 1111110000 | 304 |
| C | 1111111000 | 138 |
| C | 1111111010 | 166 |
| C | 1111111100 | 98 |
| C | 1111111101 | 206 |
| C | 1111111110 | 304 |
| P | 0011000110 | 68 |
| P | 0011001000 | 8 |
| P | 0100100100 | 69 |
| P | 0100101000 | 3 |
| P | 0101000101 | 13 |
| P | 0101001010 | 17 |
| P | 0101001100 | 57 |
| P | 0101010000 | 38 |
| P | 0101100000 | 31 |
| P | 0110000011 | 6 |
| P | 0110001101 | 55 |
| P | 0110010000 | 42 |
| P | 0110100001 | 53 |
| P | 1000100010 | 15 |
| P | 1000101001 | 19 |
| P | 1000101010 | 46 |
| P | 1001000100 | 3 |
| P | 1001001001 | 62 |
| P | 1001010000 | 38 |
| P | 1001100000 | 24 |
| P | 1001100001 | 4 |
| P | 1001100010 | 9 |
| P | 1001101010 | 6 |
| P | 1001101100 | 2 |
| P | 1010000100 | 2 |
| P | 1010001010 | 67 |
| P | 1010001100 | 22 |
| P | 1010010000 | 34 |
| P | 1010100000 | 18 |
| P | 1010100100 | 5 |
| P | 1100010000 | 76 |
| T | 1111111111 | 304 |

**Theorem 316.2 (Complete support and eight-late necessity).**
This score has

$$
\begin{gathered}
\beta=(0,76,304,380,380,380,304,304,304,304),\quad K=3952,\\
\sum P=912,\quad T=304,\quad
W=B_N=B_O=1292,\quad\Delta_N=\Delta_O=0.
\end{gathered}
\tag{316.1}
$$

For every $L\ge10$, every ordered $3\le j_1<\cdots<j_8\le L$,
every real finite profile $(b,e)$ and the same complete feasible
$N$ allocation of any finite mass,

$$
b_2+4b_{j_1}+5b_{j_2}+5b_{j_3}+5b_{j_4}
 +4b_{j_5}+4b_{j_6}+4b_{j_7}+4b_{j_8}\le1+52e.
\tag{316.2}
$$

The same holds for $O$. No order, hull or normalization premise is
imposed on this finite affine implication. For every entire sequence
(315.2) and every original competitor in either class,

$$
52e_a(A)\ge a_2+4a_{j_1}+5a_{j_2}+5a_{j_3}+5a_{j_4}
 +4a_{j_5}+4a_{j_6}+4a_{j_7}+4a_{j_8}-1.
\tag{316.3}
$$

**Proof.** Summing correct rows by first zero and all weights gives
the displayed $\beta,K$. The anchor earns all 912 union units, all
304 positive units and the 76 class-2 correct units, totaling 1292.
Here is the full integer cell certificate for (315.8). Each entry
maximizes over all eleven labels, in cell order $00,01,10,11$.

| Pair | Maxima in $00,01,10,11$ |
| --- | --- |
| 1,2 | $(76,384,452,380)$ |
| 1,3 | $(228,232,380,452)$ |
| 1,4 | $(228,232,380,452)$ |
| 1,5 | $(304,156,380,452)$ |
| 1,6 | $(380,80,380,452)$ |
| 1,7 | $(320,140,304,528)$ |
| 1,8 | $(198,262,418,338)$ |
| 1,9 | $(369,91,315,447)$ |
| 1,10 | $(333,127,367,389)$ |
| 2,3 | $(228,224,380,460)$ |
| 2,4 | $(228,224,380,460)$ |
| 2,5 | $(304,148,380,460)$ |
| 2,6 | $(380,72,380,460)$ |
| 2,7 | $(226,232,328,436)$ |
| 2,8 | $(350,110,304,498)$ |
| 2,9 | $(241,219,437,327)$ |
| 2,10 | $(367,85,333,431)$ |
| 3,4 | $(228,304,380,380)$ |
| 3,5 | $(304,228,380,380)$ |
| 3,6 | $(380,152,380,380)$ |
| 3,7 | $(320,212,304,456)$ |
| 3,8 | $(388,144,304,456)$ |
| 3,9 | $(439,93,315,445)$ |
| 3,10 | $(434,136,304,418)$ |
| 4,5 | $(304,228,380,380)$ |
| 4,6 | $(380,152,380,380)$ |
| 4,7 | $(320,212,304,456)$ |
| 4,8 | $(379,162,304,447)$ |
| 4,9 | $(398,174,315,404)$ |
| 4,10 | $(399,206,304,383)$ |
| 5,6 | $(380,228,380,304)$ |
| 5,7 | $(320,288,304,380)$ |
| 5,8 | $(388,220,304,380)$ |
| 5,9 | $(450,158,304,380)$ |
| 5,10 | $(472,136,304,380)$ |
| 6,7 | $(320,364,304,304)$ |
| 6,8 | $(388,296,304,304)$ |
| 6,9 | $(450,234,304,304)$ |
| 6,10 | $(472,212,304,304)$ |
| 7,8 | $(388,160,304,440)$ |
| 7,9 | $(450,98,304,440)$ |
| 7,10 | $(472,76,304,440)$ |
| 8,9 | $(450,166,304,372)$ |
| 8,10 | $(472,144,304,372)$ |
| 9,10 | $(472,206,304,310)$ |

These values are specified by finite addition of the displayed row
weights and a maximum over all eleven labels. For example, pair
$(1,2)$ has sole class-1 scored union weight 76 in cell $00$,
class-1 union total 384 in $01$, and the indicated maxima 452 and
380 in the other two cells. Every quadruple sums to at most 1292.
The anchor attains 1292, so the complete-support rule of 315.3
proves both zero excesses, including all shorter, repeated, reversed,
outside-query and outside-label cases at every ordered embedding.

For the same complete $\lambda$, (315.6) now gives

$$
Yh=76\bigl[b_2-1+4b_{j_1}+5b_{j_2}+5b_{j_3}+5b_{j_4}
 +4b_{j_5}+4b_{j_6}+4b_{j_7}+4b_{j_8}-52e\bigr]
 \le M\Delta_N(Y)=0.
$$

Division by 76 proves (316.2). This uses the full row inequality,
with negative singleton demands unchanged, and never divides by $M$.
For original rules apply the exact closed-cap and prefix correspondence
315.3, then decrease caps to the actual error. When the error is one,
the weighted amplitude sum is at most 36, less than $1+52$; caps
above one are likewise immediate. This proves (316.3) for arbitrary
addresses, full-carrier outputs, inactive selected addresses and every
actual positive tail. $\square$

**Corollary 316.3 (One allowance for three positive residuals).**
For these same ordered addresses put

$$
s_J=1+40e-b_2-4b_{j_1}-5b_{j_2}-5b_{j_3}-5b_{j_4}-4b_{j_5}.
$$

On the same complete feasible allocation in either class,

$$
4\bigl[(b_{j_6}-e)_++(b_{j_7}-e)_++(b_{j_8}-e)_+\bigr]\le s_J.
\tag{316.4}
$$

It holds with $b=a$ at every positive original closed cap.

**Proof.** Reuse the $Y_2$ inequality 299.1 for the empty subset,
305.2 for each singleton and 310.2 for each pair of
$\{j_6,j_7,j_8\}$. Together with (316.2), these give, on this
one profile and allocation, all eight inequalities
$s_J\ge4\sum_{k\in S}(b_{j_k}-e)$, $S\subseteq\{6,7,8\}$.
The maximum of the eight subset sums is exactly
$\sum_{k=6}^8(b_{j_k}-e)_+$: include precisely the positive terms.
This takes the maximum of necessary inequalities about one witness;
it does not add budgets from different laws. Only the score subset
is chosen, and no original demand is clipped. The correspondence
315.3 proves the original assertion, retaining closed ties. $\square$

**Corollary 316.4 (A saturated-head lower consequence).**
If an entire sequence (315.2) satisfies $\tau>0$,
$a_2=1-11\tau$ and $(a_3,\ldots,a_7)=(13,10,9,8,6)\tau$,
every original competitor in either class has

$$
e_a(A)\ge5\tau+\frac{a_8+a_9+a_{10}-15\tau}{13}.
\tag{316.5}
$$

**Proof.** The first five weighted late terms sum to $211\tau$.
Using consecutive late addresses in (316.3) gives
$52e_a(A)\ge200\tau+4(a_8+a_9+a_{10})$, which is (316.5).
Only sequence order is imposed on the later tail here. This is a
lower bound; it asserts neither attainment nor a larger-cap
classification. $\square$

## 317. A strict comparison with an expressly named necessary basis

**Proposition 317.1 (A complete-sequence diagnostic).**
Set

$$
e_0=501/2400,\qquad
(a_1,\ldots,a_{10})=(1300,1300,1300,1000,900,800,600,506,506,506)/2400,
\qquad a_n=e_0\,2^{-(n-11)}\quad(n\ge11).
\tag{317.1}
$$

This is positive, nonincreasing and vanishing, has active horizon ten
at $e_0$, and retains the closed tie $a_{11}=e_0$. Its ten-coordinate
finite profile belongs to $H_{10}$, where

$$
H_L=\{1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\ b_2=b_3,
\ 0\le\sum_{n=3}^Lb_n-(L+1)e\le1-b_1\}.
\tag{317.2}
$$

It passes the named families 299.1, 304.6, 305.2, 310.2 and 312.2
at every permitted embedding and finite omitted set, but violates
(316.2) by $1/120$. It has no complete feasible $N$ allocation at
$e_0$ at any finite mass, and hence no such $O$ allocation. Every
original competitor for this sequence has error at least $3259/15600$.

**Proof.** The hull excess and its head sum are
$\sum_{3}^{10}a_n-11e_0=607/2400$ and $1907/2400<1$.
Order and $b_2=b_3$ give all remaining hull conditions. The complete
left-minus-right maxima for the named old tests are:

| Family | Maximum reading |
| --- | ---: |
| $Y_1$ of 299.1 | $-139/800$ |
| $Y_2$ of 299.1 | $-1/60$ |
| $C$ of 299.1 | $-57/800$ |
| Collective residuals 304.6 | $-13/960$ |
| Six-late cut 305.2 | $-1/120$ |
| Seven-late cut 310.2 | $0$ |
| Head-independent cut 312.2 | $-43/2400$ |

The values have an explicit arithmetic specification. For the
nonnegative-coefficient cuts insert consecutive ordered late coordinates
in their printed formulas: these maximize their readings by order.
For 304.6, for a selected five-tuple $J$ put $r_k=(a_k-e_0)_+$,
take every omitted positive residual, and compute

$$
\max\{\max_{k\notin\{1,2\}\cup J}r_k,
          \tfrac12\sum_{k\notin\{1,2\}\cup J}r_k\}-s_J.
\tag{317.3}
$$

At $J=(3,\ldots,7)$ the omitted residuals are three copies of
$5/2400$, so the maximum is $15/4800=1/320$ and
$s_J=1/60$. Their difference is $-13/960$.
These consecutive computations already give the displayed old maxima
over all unbounded embeddings, as follows. All residuals from 11 on
are zero. In any legal single-address move later, let the selected
amplitude decrease by $\delta\ge0$. For (317.3) the omitted
residual sum can grow by at most $\delta$, and its maximum individual
residual can grow by at most $\delta$. Thus its displayed maximum
grows by at most $\delta$, while $s_J$ increases by at least
$4\delta$. Its reading cannot increase. Starting with the consecutive
tuple, move coordinates from right to left to reach any ordered tuple;
each intermediate tuple is legal. Taking every omitted positive
residual maximizes all finite-$I$ tests of 304.6. This proves their
full scope, without relying on a finite horizon scan.

At the consecutive eight-late placement the new reading is

$$
4\,3\,(506-501)/2400-1/60=1/120>0.
$$

The zero-cost pairing in 316.2 therefore excludes every complete
allocation of every finite mass. Its original inequality gives

$$
e_a(A)\ge e_0+\frac{1/120}{52}
         =e_0+\frac1{6240}=\frac{3259}{15600}.
\tag{317.4}
$$

This is refinement of the expressly printed basis, not exhaustive
historical nonderivability. The profile is $N$-infeasible at the tested
cap, so is not a same-profile $N/O$ separator. Attainment of (317.4)
is not asserted. $\square$

## 318. A seven-late lower certificate for an attained family

**Definition 318.1 (The nine-coordinate score $Y_{128}$).**
Use the following complete 46-row integer score. Every $A$ and every
unlisted coefficient vanishes; all unscored full constraints remain.

| Row | Word | Weight |
| --- | --- | --- |
| P | 001100010 | 8 |
| P | 001100100 | 8 |
| P | 010010000 | 16 |
| P | 010010010 | 16 |
| P | 010100010 | 24 |
| P | 010101000 | 12 |
| P | 010110001 | 4 |
| P | 011000010 | 16 |
| P | 011000100 | 16 |
| P | 011001000 | 4 |
| P | 011010000 | 4 |
| P | 100010100 | 16 |
| P | 100011000 | 8 |
| P | 100100100 | 24 |
| P | 100101000 | 12 |
| P | 100110000 | 12 |
| P | 101000010 | 8 |
| P | 101000100 | 8 |
| P | 101001000 | 20 |
| P | 101010000 | 12 |
| C | 101100000 | 8 |
| C | 101100010 | 4 |
| C | 101100011 | 4 |
| C | 110000000 | 52 |
| P | 110001000 | 16 |
| C | 110100110 | 16 |
| C | 110101001 | 4 |
| C | 110110000 | 16 |
| C | 111000000 | 59 |
| C | 111000111 | 2 |
| C | 111001010 | 5 |
| C | 111001101 | 2 |
| C | 111010101 | 2 |
| C | 111010110 | 33 |
| C | 111011100 | 1 |
| C | 111100000 | 40 |
| C | 111100110 | 52 |
| C | 111100111 | 4 |
| C | 111101000 | 8 |
| C | 111110000 | 80 |
| C | 111110010 | 8 |
| C | 111110100 | 8 |
| C | 111111000 | 88 |
| C | 111111100 | 88 |
| C | 111111110 | 88 |
| T | 111111111 | 88 |

**Theorem 318.2 (Complete 128-charge lower bound).**
Its invariants are

$$
\begin{gathered}
\beta=(0,16,88,104,104,96,88,88,88),\quad K=1024,\\
\sum P=264,\quad T=88,\quad
W=B_N=B_O=368,\quad\Delta_N=\Delta_O=0.
\end{gathered}
\tag{318.1}
$$

For every $L\ge9$, every ordered $3\le j_1<\cdots<j_7\le L$,
every real finite profile and the same complete feasible allocation
in either class of any finite mass,

$$
2b_2+11b_{j_1}+13b_{j_2}+13b_{j_3}+12b_{j_4}
 +11b_{j_5}+11b_{j_6}+11b_{j_7}\le2+128e.
\tag{318.2}
$$

For every entire original sequence and every original competitor
in either class,

$$
128e_a(A)\ge2a_2+11a_{j_1}+13a_{j_2}+13a_{j_3}+12a_{j_4}
 +11a_{j_5}+11a_{j_6}+11a_{j_7}-2.
\tag{318.3}
$$

**Proof.** Class summation gives $\beta$ and the total 1024.
The anchor earns $264+88+16=368$. All 36 complete cell maxima
(315.8), maximizing over every label $0,\ldots,9$, are:

| Pair | Maxima in $00,01,10,11$ |
| --- | --- |
| 12 | $(16,112,136,104)$ |
| 13 | $(72,56,104,136)$ |
| 14 | $(72,56,104,136)$ |
| 15 | $(88,40,104,136)$ |
| 16 | $(112,16,96,144)$ |
| 17 | $(104,24,88,136)$ |
| 18 | $(64,64,128,96)$ |
| 19 | $(124,4,136,88)$ |
| 23 | $(72,64,104,128)$ |
| 24 | $(72,64,104,128)$ |
| 25 | $(88,48,104,128)$ |
| 26 | $(96,40,96,120)$ |
| 27 | $(88,56,112,104)$ |
| 28 | $(120,16,88,144)$ |
| 29 | $(136,4,124,92)$ |
| 34 | $(72,88,104,104)$ |
| 35 | $(88,72,104,104)$ |
| 36 | $(112,48,96,112)$ |
| 37 | $(120,40,88,120)$ |
| 38 | $(120,40,88,120)$ |
| 39 | $(156,4,104,88)$ |
| 45 | $(88,72,104,104)$ |
| 46 | $(112,48,96,112)$ |
| 47 | $(120,40,88,120)$ |
| 48 | $(120,40,88,120)$ |
| 49 | $(160,6,100,92)$ |
| 56 | $(112,64,96,96)$ |
| 57 | $(120,56,88,104)$ |
| 58 | $(120,56,88,104)$ |
| 59 | $(176,4,96,92)$ |
| 67 | $(120,72,88,88)$ |
| 68 | $(120,72,88,88)$ |
| 69 | $(188,4,88,88)$ |
| 78 | $(120,72,88,88)$ |
| 79 | $(188,4,88,88)$ |
| 89 | $(188,4,88,88)$ |

Each quadruple sums to at most 368. These finite additions and
maxima, together with the anchor, prove complete support and both
zero excesses by 315.3. That argument covers every horizon, ordered
gap embedding, shorter or repeated schedule, reversal, outside query
and outside label. The same allocation pairing gives

$$
Y_{128}h=8\bigl[2b_2-2+11b_{j_1}+13b_{j_2}+13b_{j_3}
 +12b_{j_4}+11b_{j_5}+11b_{j_6}+11b_{j_7}-128e\bigr]\le0,
$$

proving (318.2) with no normalization, order or hull hypothesis.
The exact closed-cap and prefix transport in 315.3 proves (318.3)
against every original arbitrary-address, full-carrier competitor.
In particular a smaller cap activating more tail coordinates is
still covered. At error one the weighted amplitude sum is at most
$84<130$, so that endpoint is immediate. $\square$

## 319. The unchanged seven-coordinate endpoint used in the mixture

**Construction 319.1 (The law $P^0$).**
Use precisely the endpoint $\tau=1/24$, $a_1=a_2=13/24$ of
[Theorem 295.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md).
Here are its sixteen tables, with mass equal to the final column
divided by 24. Stopped cells are $0,10,11$.

| $i$ | $j$ | $u$ | $v$ | $z$ | Count /24 |
| --- | --- | --- | --- | --- | --- |
| 1 | 2 | 1 | 2 | 0 | 4 |
| 1 | 2 | 1 | 2 | 3 | 2 |
| 1 | 2 | 1 | 2 | 4 | 1 |
| 1 | 2 | 1 | 2 | 5 | 1 |
| 1 | 3 | 1 | 3 | 0 | 3 |
| 1 | 4 | 0 | 4 | 0 | 1 |
| 2 | 3 | 0 | 3 | 0 | 3 |
| 2 | 4 | 0 | 4 | 0 | 1 |
| 3 | 4 | 0 | 4 | 0 | 1 |
| 3 | 4 | 0 | 4 | 5 | 1 |
| 3 | 5 | 0 | 5 | 0 | 1 |
| 3 | 6 | 0 | 6 | 0 | 1 |
| 4 | 5 | 0 | 5 | 0 | 1 |
| 4 | 6 | 0 | 6 | 0 | 1 |
| 5 | 6 | 0 | 6 | 0 | 1 |
| 6 | 7 | 0 | 7 | 0 | 1 |

The row $O(1,4;0,4,0)$ has its displayed first output zero.
The masses sum to 24. On nine input coordinates this law ignores
bits eight and nine and emits no label above seven.

**Reused endpoint verification 319.2 (Every word of $P^0$).**
The target amplitudes on nine bits are
$A^0=(13,13,13,10,9,8,6,5,5)/24$ and its cap is $5/24$.
To retain the full construction and all-word proof, write
$(s,v,u,z,h)=(w_3,w_4,w_5,w_6,w_7)$ and put

$$
B=2s(1-v)+sv+(s+v)(2-u-z)+u(1-z)+z(1-h),\qquad
G=3(1-s)+(1-v).
\tag{319.1}
$$

For $q=s+v$, the four maxima over $h$ of
$q(2-u-z)+u(1-z)+z(1-h)$ at $uz=00,01,10,11$ are
$2q,q+1,q+1,1$. Maximizing gives $1,2,2,4$ for
$sv=00,01,10,11$. Adding $2s(1-v)+sv+G$ bounds $B+G$
by five in all four cases, and also $B\le5$.

Direct addition of these same sixteen tables gives the following
correct and outside-pair counts in units of $1/24$:

| First zero | Correct count | Outside-$\{0,n\}$ count |
| --- | ---: | --- |
| 1 | 11 | $B+w_2G$ |
| 2 | 8 | $B+G$ |
| 3 | 8 | $2+2(1-v)+v(2-u-z)+u(1-z)+z(1-h)$ |
| 4 | 5 | $3+(1-u)+(1-z)+u(1-z)+z(1-h)$ |
| 5 | 4 | $3+2(1-z)+z(1-h)$ |
| 6 | 3 | $5$ |
| 7 | 1 | $5$ |

All outside counts are at most five. In class 3, $v=0$ gives
$4+u(1-z)+z(1-h)\le5$ and $v=1$ gives
$4-uz-zh\le4$. In class 4 the added bracket is
$2-uz-zh\le2$. Class 5 follows by $z=0,1$; the first two
classes use $B+G\le5$. Correct counts are independent of every
multiple-zero suffix. The target minus correct count is two in
class 1 and five in classes 2 through 7. Correct count is at most
target count, so the base deficit is at most the outside count.
Thus each of the three independent rows is bounded by $5/24$.

At a positive seven-bit prefix the law is
$19e_0/24+2e_3/24+e_4/24+2e_5/24$.
In first-zero classes 8 and 9 its target amplitude is $5/24$,
so (315.7) gives error $5/24$, on every suffix. The nine-bit
positive word also has nonbase mass $5/24$. This verifies all
nine-bit rows of the unchanged $P^0$. Its earlier attainment and
the $t=0$ case below are reused results; the modified head-fill
table of 300.1, whose class-1 count is twelve, is not substituted.

## 320. One complete nine-coordinate endpoint law

**Construction 320.1 (The law $P^\star$).**
The target amplitudes and cap are

$$
A^\star=(13,13,13,10,9,8,6,6,6)/24,
\qquad e^\star=331/1536=662/3072.
\tag{320.1}
$$

All counts in this construction are divided by 3072. The following
sixteen deterministic rows give $O(i,j;u,v,z)$ its listed count.

| $i$ | $j$ | $u$ | $v$ | $z$ | Count /3072 |
| --- | --- | --- | --- | --- | --- |
| 1 | 3 | 0 | 3 | 0 | 391 |
| 1 | 4 | 1 | 4 | 0 | 110 |
| 1 | 5 | 1 | 5 | 0 | 27 |
| 2 | 4 | 0 | 4 | 0 | 110 |
| 2 | 5 | 0 | 5 | 0 | 27 |
| 3 | 5 | 0 | 5 | 0 | 132 |
| 3 | 6 | 0 | 6 | 0 | 125 |
| 3 | 7 | 0 | 7 | 0 | 15 |
| 3 | 8 | 0 | 8 | 0 | 15 |
| 4 | 5 | 0 | 5 | 0 | 117 |
| 4 | 6 | 0 | 6 | 0 | 110 |
| 5 | 6 | 0 | 6 | 0 | 127 |
| 5 | 7 | 0 | 7 | 0 | 17 |
| 5 | 8 | 0 | 8 | 0 | 17 |
| 7 | 8 | 0 | 8 | 0 | 17 |
| 8 | 9 | 0 | 9 | 0 | 17 |

There are five further schedule rows. Each entry is an unnormalized
label vector on the indicated stopped cell; each vector in a row
has the same schedule count $m$.

| Schedule | $m$ | First vector | Middle vector | Exhaustion vector |
| --- | --- | --- | --- | --- |
| $(1,2)$ | 944 | $944e_{1}$ | $944e_{2}$ | $463e_{0}+220e_{3}+162e_{4}+99e_{5}$ |
| $(2,3)$ | 391 | $333e_{0}+58e_{2}$ | $391e_{3}$ | $391e_{0}$ |
| $(3,4)$ | 236 | $236e_{0}$ | $236e_{4}$ | $148e_{0}+88e_{5}$ |
| $(6,7)$ | 74 | $74e_{0}$ | $74e_{7}$ | $17e_{0}+4e_{8}+53e_{9}$ |
| $(6,8)$ | 53 | $53e_{0}$ | $53e_{8}$ | $17e_{0}+36e_{9}$ |

The deterministic counts sum to 1374 and the five schedule counts
sum to 1698. Thus total schedule count is 3072. Every vector is
nonnegative and sums to its own $m$, including each exhaustion
vector. Counterfactual cell masses are not added together.

Here is an explicit complete-table coupling for each mixed row.
Order its labels increasingly and, in each of the three cells,
partition $[0,1)$ into half-open intervals of lengths given by that
cell's counts divided by $m$. For each triple of cell labels
$(u,v,z)$ assign to $O(i,j;u,v,z)$ mass

$$
\frac{m}{3072}\,\bigl|I_0(u)\cap I_{10}(v)\cap I_{11}(z)\bigr|.
\tag{320.2}
$$

These intersections partition the interval, give nonnegative full
table weights summing to $m/3072$, and recover every displayed
cell marginal by summation. Equivalently the same local uniform
coordinate fixes all three counterfactual labels by their cell
quantiles before replies. This defines one whole probability law.
It imposes no sum-fill condition on different counterfactual cells.

**Theorem 320.2 (All-word endpoint certificate).**
For every $w\in\{0,1\}^9$, $P^\star$ satisfies every independent
row at target (320.1) and cap $662/3072$. Its positive-word base
mass is $1-662/3072$.

**Proof.** In units $1/3072$ the target counts and correct counts
on the complete first-zero fibres are

$$
\begin{aligned}
T&=(1664,1664,1664,1280,1152,1024,768,768,768),\\
c&=(1081,1002,1002,618,490,362,106,106,106).
\end{aligned}
\tag{320.3}
$$

These follow by adding the same schedule vectors. A positive first
or middle output is its queried label, and every numerical exhaustion
output is later than both queries. In its first-zero fibre those
earlier queried bits are one. Hence the correct contributions are
constant on the entire fibre, independently of all later zeros.
For example class 1 receives $944+110+27=1081$; class 2 receives
$944+58=1002$; class 3 receives $391+391+220=1002$.
For classes 4 through 9 the sums are respectively
$110+110+236+162$, $27+27+132+117+99+88$,
$125+110+127$, $15+17+74$, $15+17+17+4+53$,
and $17+53+36$. They give the remaining entries of $c$.
Thus $T_n-662\le c_n\le T_n$, with left equality for $n\ge2$.

To bound the independent pair deficit, write $x_i=w_i$ and
$Z(x)=3072[1-P^\star_x(0)]$. Directly from the complete vectors,

$$
Z(x)=\sum_{(i,j)}\bigl[f_{ij}(1-x_i)
              +v_{ij}x_i(1-x_j)+z_{ij}x_ix_j\bigr],
\tag{320.4}
$$

where $f_{ij},v_{ij},z_{ij}$ are the nonzero-label counts in
that schedule's first, middle and exhaustion vectors. This is one
common polynomial for the same law, not independently maximized
wrong masses. Collecting its terms gives

$$
\begin{aligned}
Z={}&J+A x_6+B(x_7+x_8)
            -17(x_6x_7+x_6x_8+x_7x_8+x_8x_9),\\
A={}&127-125x_3-110x_4-127x_5,\\
B={}&17-15x_3-17x_5,\\
J={}&1139+391x_1+470x_2+523x_3+227x_4+161x_5\\
 &-463x_1x_2-391x_1x_3-110x_1x_4-27x_1x_5\\
 &-391x_2x_3-110x_2x_4-27x_2x_5
      -148x_3x_4-132x_3x_5-117x_4x_5.
\end{aligned}
\tag{320.5}
$$

For fixed $x_1,\ldots,x_5$, $B\le17$. Set $x_9=0$ when
maximizing. If $x_6=0$, the remaining maximum is
$\max\{0,B,2B-17\}=\max\{0,B\}$. If $x_6=1$, the
coefficients of $x_7,x_8$ are $B-17\le0$ and their product
coefficient is nonpositive, so the maximum is $A$, at
$x_7=x_8=0$. Therefore

$$
\max_{x_6,\ldots,x_9}Z=J+\max\{0,A,B\}.
\tag{320.6}
$$

For a first-zero class $n\le5$, substitute
$x_1=\cdots=x_{n-1}=1$, $x_n=0$, and each lexicographic
assignment of $x_{n+1},\ldots,x_5$. Subtracting its constant
correct count $c_n$ gives these complete grouped maxima of the
outside-$\{0,n\}$ count:

| Class | Grouped wrong-count maxima |
| --- | --- |
| 1 | $185,219,302,329,583,610,662,572,655,662,662,662,662,662,631,514$ |
| 2 | $655,662,662,662,662,662,631,514$ |
| 3 | $662,642,559,532$ |
| 4 | $662,635$ |
| 5 | $649$ |

This is finite substitution into (320.5)–(320.6), specifying all
$16+8+4+2+1$ groups without an optimization assumption.
For classes 6 through 9, $x_1=\cdots=x_5=1$ gives
$J=995$, $A=-235$, $B=-15$. The restricted expressions and
their complete wrong-count maxima are

| Class | Restricted $Z$ | $\max(Z-c_n)$ |
| --- | --- | ---: |
| 6 | $995-15(x_7+x_8)-17(x_7x_8+x_8x_9)$ | 633 |
| 7 | $760-32x_8-17x_8x_9$ | 654 |
| 8 | $728$ | 622 |
| 9 | $679$ | 573 |

Every grouped value is at most 662. If $d_w=Z(w)-c_n$ is the
outside-pair count on a zero word, the three deficits (315.3),
multiplied by 3072, are

$$
c_n+d_w-T_n\le d_w\le662,\qquad
T_n-c_n\le662,\qquad d_w\le662.
\tag{320.7}
$$

This proves the base, correct and independent union rows separately
for every word, including every multiple-zero suffix. At $1^9$,
(320.5) gives $Z=995-235-30-68=662$, proving the positive
row and its stated equality. $\square$

## 321. An attained continuum with nine active coordinates

**Theorem 321.1 (Every real parameter and every permitted actual tail).**
For every real

$$
0<\tau\le1/24,\quad0\le t\le\tau,\quad
a_1=a_2=1-11\tau,\quad(a_3,\ldots,a_7)=(13,10,9,8,6)\tau,
\quad a_8=a_9=5\tau+t,
\tag{321.1}
$$

put $E_*=5\tau+11t/64$ and append any positive nonincreasing
vanishing actual tail with $a_{10}\le E_*$. Then both original
marked-target hard-two optima are attained and equal $E_*$:

$$
\min_{A\in\mathcal N_2}e_a(A)
 =\min_{A\in\mathcal O_2}e_a(A)=E_*.
\tag{321.2}
$$

For this fixed entire sequence, every positive closed cap $c$ is
feasible in either class if and only if $c\ge E_*$. At $t>0$
the actual active length at $E_*$ is nine; at $t=0$ it is seven.
The endpoints $t=\tau$, $\tau=1/24$, zero mixture weights and
$a_{10}=E_*$ are included.

**Proof.** Order holds: $1-11\tau\ge13\tau$, the five late
amplitudes are decreasing, $6\tau\ge5\tau+t$, and
$0<E_*\le5\tau+t$. In particular (321.1) with every specified
tail is an original entire sequence (315.2).

Define the following one whole-law mixture on nine coordinates:

$$
p=(1-24\tau)R+24(\tau-t)P^0+24tP^\star.
\tag{321.3}
$$

The three branch weights are nonnegative and sum to one. The auxiliary
finite $R$ has target amplitudes $\alpha=(1,1,0,\ldots,0)$ and
cap zero. The other endpoint target profiles and caps are (319.2)
and (320.1). Their same affine combination has first two amplitudes
$1-24\tau+13\tau=1-11\tau$, next five amplitudes
$(13,10,9,8,6)\tau$, final two amplitudes
$5(\tau-t)+6t=5\tau+t$, and cap

$$
24(\tau-t)\frac5{24}+24t\frac{331}{1536}
 =5\tau+\frac{11t}{64}=E_*.
\tag{321.4}
$$

For each fixed word and each of its independent events, both its
probability and its demand are affine in law, amplitudes and cap.
The zero-word and positive-word endpoint inequalities of 319.2 and
320.2 therefore prove every full row for (321.3), for all real
parameters in the stated closed domain. This is an affine proof
of the continuum, not interpolation from sampled parameters.
The same calculation at the positive word gives $p_+(0)=1-E_*$.

Here is its original source and seed realization. Partition one
source-independent $U\in[0,1)$ into the three branch intervals in
(321.3), omitting zero intervals. Subdivide the selected branch into
its schedule intervals. For a mixed $P^\star$ row use its same
rescaled coordinate for all the quantile partitions of (320.2).
Thus before replies the one seed fixes the whole schedule and all
counterfactual labels. Execute only that chosen increasing schedule
on the same actual source, stop at its first queried zero or
exhaustion, and hand off its indicated actual $\theta_j$ to the
unchanged consumer. Half-open intervals specify all endpoints.
Every seed and source terminates finitely, measurably, with zero
advice and at most two actual requests.

The $N$ completion uses the identical source and seed, obtains the
entire preselected schedule and reconstructs the same stopped output.
Its ignored second reply counts as an actual request. It has identical
output laws. No arbitrary initially supplied $N$ law is being preserved.
The explicitly stopped normalized law also satisfies the reused exact
criterion 109.1 at its actual active horizon; no degree-only or scalar
expectation surrogate is used.

No mark above nine is emitted. For every actual $n>9$, (315.7)
therefore gives exact error

$$
\max\{1-p_+(0),a_n\}=\max\{E_*,a_n\}=E_*.
\tag{321.5}
$$

This includes $a_{10}=E_*$ and every later positive vanishing tail.
Every finite positive prefix and later first absence has an actual
witness by 315.3. If $t>0$, $a_8-E_*=a_9-E_*=53t/64>0$,
so the active length is nine. If $t=0$, bits eight and nine have
amplitude equal to the cap; the $P^\star$ branch is absent, the
law ignores them, and (315.7) gives error $5\tau$ on these
classes too. Since $a_7=6\tau>5\tau$, the active length is seven.
The algebraic $\tau=0$ degeneration is $R$ and is not an original
positive-sequence assertion.

For a lower bound against every original competitor, substitute
the consecutive seven late addresses into (318.3). The contributions
are

$$
2a_2-2=-22\tau,\quad
11a_3+13a_4+13a_5+12a_6+11a_7=552\tau,\quad
11(a_8+a_9)=110\tau+22t.
$$

Hence $128e_a(A)\ge640\tau+22t=128E_*$ for every original
arbitrary-address, full-carrier $N$ or $O$ competitor. The bound
continues to apply to a smaller cap that activates more tail
coordinates, by 315.3. The one constructed law has error $E_*$
by the upper rows and actual tails. It and its completion attain
both minima. The same law meets every larger closed cap; the lower
bound excludes every smaller one. This proves (321.2) and the full
closed-cap equivalence. $\square$

## 322. A regional full-score consumer and a direct-extension boundary

**Corollary 322.1 (Every unit-$O$ score on the specified $H_9$ continuum).**
Restrict Theorem 321.1 to $\tau=1/24$ and $0<t\le1/24$.
Its actual finite profile lies in $H_9$ of (317.2) and its
full-feasible part $H_N$, with the same mass-one stopped allocation
$\lambda^O$. For every unrestricted full score $y\ge0$,

$$
F_{Qy}(b,E_*)\le\Delta_O(y).
\tag{322.1}
$$

In particular a full unit-$O$ score, $\Delta_O(y)\le1$, cannot
satisfy $F_{Qy}(b,E_*)>M$ for a same-profile $N$ allocation of
mass $M\ge1$.

**Proof.** Here $b_2=b_3$. Its hull excess and head sum are

$$
\sum_{n=3}^9b_n-10E_*=\frac14+\frac{9t}{32}\ge0,\qquad
b_1+\sum_{n=3}^9b_n-10E_*
 =\frac{19}{24}+\frac{9t}{32}\le\frac{617}{768}<1.
\tag{322.2}
$$

The remaining hull conditions follow from the order and active
length in 321.1. Its same normalized stopped law witnesses $H_N$.
For every full nonnegative $y$, apply the existing pairing to this
one stopped law:
$y h\le yG_O\lambda^O\le\Delta_O(y)$, since its mass is one.
This proves (322.1) and the claimed exclusion. The restriction on
$\tau$ is essential to the stated hull conclusion; no $H_9$
membership is asserted for all other scales. $\square$

**Proposition 322.2 (The specified direct $m=7$ residual extraction fails).**
For the $t>0$ family of 321.1, the direct residual extension of
[173–174](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_V.md),
with $m=7$, $L=9$, cannot supply the stated profile at cap $E_*$
by extracting its core as in 174.1. This excludes that construction
only, not every previous supplier or arbitrary replacement law.

**Proof.** The residuals required by those fixed extension equations
are $g_8=g_9=53t/64$. The reused identities 173.4 give

$$
W=\frac{9g_8+g_9}{3}=\frac{265t}{96},\qquad
E_{\rm res}=\frac{6g_8+g_9}{3}=\frac{371t}{192}.
\tag{322.3}
$$

Here $W\le265/2304<1$ and
$E_*-E_{\rm res}=5\tau-169t/96\ge311\tau/96>0$.
The uniquely extracted core would be
$A_i=(a_i-W)/(1-W)$, $e_0=(E_*-E_{\rm res})/(1-W)$.
But its reused necessary $Y_2$ reading, from 299.1, is

$$
A_2+4A_3+5A_4+5A_5+5A_6+4A_7-1-40e_0
 =\frac{665t/96}{1-W}>0.
\tag{322.4}
$$

To check the identity, its numerator before division is
$[a_2+4a_3+5a_4+5a_5+5a_6+4a_7-1-40E_*]
-23W+40E_{\rm res}$.
The bracket is $-55t/8$, and substituting (322.3) leaves
$665t/96$. Thus the extracted core cannot have any complete
feasible $N$ allocation, and in particular cannot be a stopped
core for that direct extension. At $\tau=t=1/24$, its reading
is $665/2039>0$. This argument is a necessary-core obstruction to
the specified extraction, not a classification of all old
constructions. $\square$

**Comparison 322.3 (Scope relative to the earlier attained domains).**
The two-tail lower consequence 310.5 on the family 321.1 is
$5\tau+t/6$. Its difference from the matching value here is
$E_*-(5\tau+t/6)=t/192>0$ for $t>0$.
The attained laws 300.1, 306.1 and the entire cone optimum 313.1
retain their stated seven-active hypotheses with eighth amplitude
at most their cap. Here $a_8=a_9>E_*$ when $t>0$.
The new attained scope is this nine-active continuum, with its one
matching complete-$N$ lower bound and stopped upper law. The $P^0$
endpoint, $t=0$ family, old cones, parameter axes, head-tight contacts,
43/35/61 alternative lower routes, source arithmetic, common-seed
realization and exact closed-cap transport are reused without
additional result credit. The new scope of 316 is the joint
three-tail constraint; its zero-, one- and two-tail premises remain
the earlier results.

## 323. Target, literature and unrestricted boundaries

**Example 323.1 (The actual earlier-unqueried output).**
At $(r,g)=(19,436)$, $F_{19}=4181$, the legal window is
$419\le436\le836$, and $N=1822917$. Its residues modulo
$2,3,5,7$ are $1,0,2,5$, so its prime-reply word is $0100$.
The legal $N(3,4;1,0,0,0)$ makes two actual requests, obtains
$00$, and emits earlier **unqueried** label 1. Replacing its
unit mass there by the endpoint output zero changes mass one and
has $\ell^1$ defect two, TV one. No such pruning is used in the
full-catalog support bounds. A numerical exhaustion output later
than both queries in 320 is a property of that explicit law only,
not a restriction on the competitor catalog.

**Literature scope 323.2.**
David Blackwell, *Comparison of Experiments*, Second Berkeley
Symposium (1951), pp. 93–102,
[sections 2–3, Theorem 2 and proof](https://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-08.pdf),
uses finitely many probability measures on a Borel space, bounded
finite-dimensional loss actions and whole attainable loss vectors
under randomized decision procedures and their convex closure.
Its supporting-hyperplane comparison is the mature whole-vector
framework used here. It supplies neither the displayed integer
coefficients nor a reverse hard-two increasing-stopping theorem.

Jędrzej Kaniewski, Troy Lee and Ronald de Wolf, *Query complexity
in expectation*,
[arXiv:1411.7280v1, Definitions 6 and 8, Theorem 9 and both directions](https://arxiv.org/pdf/1411.7280v1),
characterize nonnegative scalar expectation through nonnegative literal
degree. Cost is the maximum supported root-to-leaf depth. Their
converse samples nonnegative coefficients of total mass $M$ with
probabilities $\alpha/M$ and rescales the scalar output by $M$.
This gives a scalar expectation, and does not furnish a normalized
joint output law, equal counterfactual schedule masses or increasing
first-queried-zero execution. Those vector and resource conditions
are supplied by the actual constructions 319–321. These citations
carry only their specified framework roles; no broad novelty or
priority assertion follows.

Finite atomic output laws here give their finite support mass one,
whereas every unchanged original nonatomic target gives it mass zero.
Their TV distance is therefore one. Selected marked-target accuracy
does not approximate those nonatomic targets or change the consumer.
Both the full original output carrier and all original competitors
remain present in the lower directions. Every permitted positive
vanishing actual tail, every multiple-zero word, negative singleton
demand, independent union row and closed cap has its stated role.

**Unresolved question 323.3 (The original simultaneous budget).**
With the full definitions of 315 and the hull (317.2), the remaining
unrestricted assertion is: for every $L\ge3$ and every full
$y\ge0$ with $\Delta_O(y)\le1$, there exist one unrestricted
full $V\ge0$ and one $\theta\in[0,1]$ such that

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(Qy-QV)\le\theta,\qquad
\sigma_H(q)=\max_{(b,e)\in H_L}F_q(b,e).
\tag{323.1}
$$

The residual is signed, and nonzero zero-cost $V$ at $\theta=1$
remains allowed. There is no exact-law, exact-quotient, fixed-anchor,
unary-only, restricted-label or positive-residual restriction.
The alternative negative witness requires the same actual
$(b,e)\in H_N$, one complete feasible $N$ allocation of mass
$M\ge1$, and a full unit-$O$ score satisfying $F_{Qy}(b,e)>M$,
together with an actual original common-seed $N$ attainer and a
uniform strict lower bound against every original arbitrary-address,
full-carrier $O$ competitor. Equivalently the original positive-cap
question is whether, for every entire sequence (315.2),
$\mathcal F_N(a,c)\ne\varnothing$ implies
$\mathcal F_N(a,c)\cap\mathscr C_{L_a}\ne\varnothing$.

The diagnostic 317.1 is excluded from full $N$ feasibility, while
321.1 supplies a law in both classes on its declared family. The
regional statement 322.1 excludes a separator only on that stated
$H_9$ continuum. These results establish neither unrestricted
alternative, a general unequal-tail optimum, a four-tail allowance,
a gapped primal construction nor attainment at the diagnostic lower
bound. The complete support tables and Boolean endpoint proof are
finite exact certificates; the all-horizon embeddings, all-real
affine proof and original correspondence provide their stated
quantifiers. No formal kernel verification is asserted.

## 追加锚（本行以下为增补区）
