# KBONACCI self-calibrating acquisition resources XVI

## 273. Complete allocations, original objects and signed coordinates

**Definition 273.1 (The complete finite experiment).**
Fix $L\ge3$, $B_L=\{0,1\}^L$, $J_L=\{0,\ldots,L\}$,
$J=\{3,\ldots,L\}$ and $m=L-2$.
Write $+=1^L$, $\Omega_n=\{w:\min\{i:w_i=0\}=n\}$,
$v^i$ for the sole-zero word at $i$, and $v^{ij}$ for the word
whose zeros are exactly $i<j$.
Every word and every output label in $J_L$ is retained.
In particular a terminal label may be earlier than, or absent from,
the queried addresses.

The complete $N$ catalog consists of constants, singletons and
preselected distinct-pair tables
$N(i,j;u,v,s,t)$, $i<j$, whose outputs on $00,01,10,11$ are
$u,v,s,t$. The complete $O$ catalog consists of constants,
singletons and $O(i,j;v,s,t)$ on stopped cells $0,10,11$.
An $N$ table obtains its entire preselected schedule. An $O$ table
uses an increasing preselected schedule and stops at its first
queried zero or exhaustion. Its second address is not chosen from
the first reply. Reversal of static queries permutes cells, and
repetition gives singleton information; these identities do not
discount any repeated or ignored actual request from the bound two.

At every $w\in\Omega_n$ the three independent demand rows are
$\{0\},\{n\},\{0,n\}$ with demands $1-b_n-e,b_n-e,1-e$.
At $+$ there is the demand $1-e$ on $\{0\}$. Denote the whole
vector by $d(b,e)$ and the complete incidence vector of a table by
$z_D$. Negative singleton demands and zero-score rows remain.
For a probability vector $p_w$, these rows express exactly

$$
\operatorname{TV}(p_w,(1-b_n)e_0+b_ne_n)
=\max\{1-b_n-p_w(0),\ b_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
\tag{273.1}
$$

Here $e_r$ denotes a point mass at label $r$.
The third row is the independent union event, not a sum of
approximate singleton bounds. Formula (273.1) follows by splitting
the positive and negative parts of the signed difference on
$\{0,n\}$ and its complement.

**Definition 273.2 (One full conic allocation and its scores).**
Let $R=O(1,2;1,2,0)$, $\alpha=(1,1,0,\ldots,0)$,
$\mathbf r=z_R=d(\alpha,0)$, and set

$$
G_C=(z_D-\mathbf r)_{D\in\mathcal D_C},\qquad
h(b,e)=d(b,e)-\mathbf r.
\tag{273.2}
$$

One full allocation $\lambda_D\ge0$ has finite mass
$M=\sum_D\lambda_D$ and equal-mass word measures
$\mu_w=\sum_D\lambda_D e_{D(w)}$.
Full conic feasibility means $G_C\lambda\ge h(b,e)$ on all rows,
or, with $\eta_n=[n\le2]$,

$$
\begin{aligned}
\mu_w(0)&\ge1-b_n-e+(M-1)(1-\eta_n),\\
\mu_w(n)&\ge b_n-e+(M-1)\eta_n,\\
\mu_w(\{0,n\})&\ge M-e\quad(w\in\Omega_n),\\
\mu_+(0)&\ge M-e.
\end{aligned}
\tag{273.3}
$$

The same allocation supplies every word measure; its cell vectors
have equal mass and are not independently funded laws.
At $M=1$ these are probability kernels.

A full score $y=(A_w,C_w,P_w;T)\ge0$ has reward

$$
g_y(w,r)=A_w[r=0]+C_w[r=n]+P_w[r\in\{0,n\}]
\quad(w\in\Omega_n),\qquad g_y(+,r)=T[r=0].
\tag{273.4}
$$

Brackets denote indicators. Define

$$
\begin{gathered}
W_y=y\cdot\mathbf r,\quad B_C(y)=\max_D y\cdot z_D,
\quad\Delta_C(y)=B_C(y)-W_y\ge0,\\
\beta_n=\sum_{w\in\Omega_n}(C_w-A_w),\qquad
K=\sum_{w\ne+}(A_w+C_w+P_w)+T,\quad Qy=(\beta;K),\\
F_q(b,e)=\sum_n\beta_n(b_n-\alpha_n)-Ke,
\qquad F_y=F_{Qy}=y\cdot h(b,e).
\end{gathered}
\tag{273.5}
$$

For a fixed feasible allocation its actual score slack is
$S_y=y\cdot(G_C\lambda-h)\ge0$.
The auxiliary closed hull and its feasible-cone part are

$$
\begin{aligned}
H_L=\{(b,e):\ &1\ge b_1\ge\cdots\ge b_L\ge e\ge0,
\quad b_2=b_3,\\
&0\le E_b:=\sum_{n=3}^Lb_n-(L+1)e\le1-b_1\},\\
H_N&=\{(b,e)\in H_L:\exists\lambda\ge0,\ G_N\lambda\ge h(b,e)\},
\qquad\sigma_H(q)=\max_{H_L}F_q.
\end{aligned}
\tag{273.6}
$$

These are the complete-score coordinates of Sections 198–199 and
[Definitions 251.1–251.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XV.md#251-complete-kernels-event-scores-and-original-source-applicability).
No sign restriction is placed on a quotient difference.

**Mathematical scope 273.3 (Actual source, carrier and resources).**
The source and replies throughout are the original objects

$$
\begin{gathered}
F_0=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)=1+F_rg,\quad q_i(x)=[p_i\mid N(x)],
\quad n(x)=\min\{i:q_i(x)=0\}.
\end{gathered}
\tag{273.7}
$$

The primes $p_i$ increase. Replies are static and the first absence
is finite. Boundaries, Theorem 35.2, with its entry-rank supplier,
realizes every finite Boolean pattern, including every multiple-zero
word used here. Its CRT and growing-window argument is the arithmetic
supplier; no distribution on sources is introduced.

The full carrier is the Borel disjoint union
$\Theta=\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$ of copies
of $(0,1)$. The unchanged consumer returns unknown on $B_j$ and
proposes $j$ on $P_j$, without prime requests. Its original nonatomic
targets remain those of Source-Correlated Laws, Theorem 67.5,
and Acquisition Resources, Definitions 71.1 and 73.1: for fixed
$h_0\in(0,1)$, put $t_x=\sum_i3^{-i}q_i(x)$,
$Z_t=\int_0^1\exp(tu)\,du$, let $\nu_x$ have density
$\exp(t_xu)/Z_{t_x}$ on $B_{n(x)}$, and let $\pi_j$ be uniform
on $P_j$. The target is
$\mu_x^{\rm orig}=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$, where
$\Omega(x)$ counts distinct prime divisors of $N(x)$.

The comparison targets here are separately selected marked laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
\theta_j=(B_1,1/(j+2)),\quad j\ge0,
\quad 1\ge a_1\ge a_2\ge\cdots>0,\quad a_n\longrightarrow0.
\tag{273.8}
$$

A finite marked law has TV distance one from each unchanged
nonatomic target, by its finite support. Marked-law estimates give
no accuracy assertion against those targets.

A probability allocation is executed with one source-independent
$U\sim\operatorname{Unif}[0,1)$ selecting the entire schedule and
all counterfactual terminal outputs before replies. There is zero
advice and sourcewise almost-sure finite handoff. Every actual
request, repeated or ignored, counts toward two. No address,
runtime, depth or mean-request bound replaces this count.
Original competitors may use arbitrary addresses and output anywhere
on $\Theta$.

The normalized stopped criterion of Theorem 109.1 uses $c\ge H$;
its scalar budget is redundant after normalization. Theorem 110.2
supplies exact closed-cap class feasibility for arbitrary original
addresses and full-carrier outputs. Its necessity uses the countable
source's common probability-one termination event, control of the
whole preselected schedule, actual finite-pattern witnesses and
compactness of a finite catalog simplex. It supplies some complete
finite representative. It need not preserve a starting law, seed
coupling, curvature or table decomposition. Conversely a finite
probability allocation emits the actual original marks; the same-seed
counted completion is the supplier of Proposition 90.2.

For an entire sequence (273.8) and a positive closed cap $e$, the
actual active length is
$L_a=\max(\{i:a_i>e\}\cup\{0\})$. Apply a finite theorem only
in its stated length range. Every actual $n>L_a$ retains its positive
amplitude, including $a_n=e$. A finite marked kernel has exact tail
error

$$
\operatorname{TV}\left(\sum_{r=0}^Lp_+(r)\delta_{\theta_r},
           (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
=\max\{1-p_+(0),a_n\}\quad(n>L).
\tag{273.9}
$$

This follows from overlap mass $\min\{p_+(0),1-a_n\}$.
The finite positive word records actual later-zero sources; it is
not an infinite all-positive source. Proof averages below add no
operational seed, observation or prior on sources.

For conic mass $M\ge1$, division changes the auxiliary profile:

$$
x=(1-1/M)\alpha+b/M,\qquad e_x=e/M,
\qquad Z_N(\lambda/M)\ge d(x,e_x).
\tag{273.10}
$$

Indeed $Z_N\lambda=M\mathbf r+G_N\lambda$ and $d$ is affine.
This is not cap feasibility at unchanged $(b,e)$; $x$ need not
satisfy $x_2=x_3$ or belong to $H_L$. Same-point conic pairings
below do not use this division. If $M<1$, padding at the zero
$G_R$ column to mass one is permitted, without claiming law
preservation.

## 274. Complete-fibre reserves and the signed early loss

**Definition 274.1 (A complete-fibre capacity score).**
Let $L\ge4$ and $c=c_m=4-2/\lceil(m+1)/2\rceil$, so $3\le c<4$.
Use the balanced suffix measure $\nu$ of Section 201.2, also used
in Sections 207.4 and 271.1. In zero-set notation, if $m=2q-1$
each $q$-subset has mass $2m/(q\binom mq)$; if $m=2q$, each
$q$-subset has mass $2/\binom mq$ and each $(q+1)$-subset has
mass $2q/((q+1)\binom m{q+1})$.
Its mass is $c$, each zero marginal is 2, and each distinct pair
has reply-cell masses $(1,1,1,c-3)$ in $00,01,10,11$ order.
For odd $m$, the marginal calculation is
$(2m/q)(q/m)=2$ and the two-zero mass is
$(2m/q)q(q-1)/(m(m-1))=1$. For even $m$, the two layers give
unary masses $1+1=2$ and two-zero masses
$(q-1)/(2q-1)+q/(2q-1)=1$; subtraction gives the other cells.

Define $Y$ by

$$
P_{01z}=P_{10z}=\nu(z)/2,\qquad
C_{1^{n-1}0v}=2^{-(L-n)}\quad(n\ge3),\qquad T=1,
\tag{274.1}
$$

with every other score zero. Each complete late correct fibre has
total weight one and every suffix on it has positive weight.
Consequently $W_Y=c+1$, $\beta_j(Y)=1$ for $j\in J$ and zero
otherwise, $K_Y=m+c+1$, and
$F_Y=E_b-(c-2)e$. Write $\delta_b=(c-2)e-E_b$.
The measure and its capacity projection are existing suppliers;
the whole-fibre and column information below retains their common
allocation before projection.

**Theorem 274.2 (One reserve pays full-fibre slacks and late disagreement).**
For every complete $N$ column let $d_Y(D)=c+1-Y\cdot z_D$.
Let $I_{\rm late}(D)$ indicate a distinct pair $3\le i<j\le L$
with $u\ne v$. Then

$$
\Delta_N(Y)=\Delta_O(Y)=0,\qquad
d_Y(D)\ge[D(+)\in\{1,2\}]+\tfrac12 I_{\rm late}(D).
\tag{274.2}
$$

For every one full feasible $N$ allocation, of any mass, let
$\eta=\mu_+(1)+\mu_+(2)$ and
$\Gamma_{\rm late}=\sum_D\lambda_DI_{\rm late}(D)$. Then

$$
\delta_b=S_Y+\sum_D\lambda_Dd_Y(D)
\ge S_Y+\eta+\tfrac12\Gamma_{\rm late}.
\tag{274.3}
$$

In particular, $\delta_b=0$ forces $\eta=0$, all positive-mass
late pairs to have $u=v=0$, and

$$
\mu_w(n)=b_n-e\quad(w\in\Omega_n,\ n\ge3),\qquad
\mu_+(0)=M-e.
\tag{274.4}
$$

Both early pair slacks vanish at every suffix with $\nu(z)>0$.
These zero-reserve assertions are conditional.

**Proof.** Put $a=c/2-1$. The full reward vectors of an output
label, in four-cell order, are as follows. Every legal label occurs
in a listed class.

| Pair | Label | Reward vector |
| --- | --- | --- |
| $(1,2)$ | $0$ | $(0,c/2,c/2,1)$ |
| $(1,2)$ | $1$ | $(0,c/2,0,0)$ |
| $(1,2)$ | $2$ | $(0,0,c/2,0)$ |
| $(1,2)$ | $r\in J$ | $(0,0,0,1)$ |
| $(h,j)$, $h\in\{1,2\},j\in J$ | $0$ | $(1,a,1,c/2)$ |
| $(h,j)$, $k=3-h$ | $h$ | $(1,a,0,0)$ |
| $(h,j)$ | $k$ | $(0,0,1,a)$ |
| $(h,j)$ | $r\in J,r<j$ | $(0,0,1/2,1/2)$ |
| $(h,j)$ | $r=j$ | $(0,0,1,0)$ |
| $(h,j)$ | $r>j$ | $(0,0,0,1)$ |
| $(i,j)$, $3\le i<j$ | $0$ | $(1,1,1,c-2)$ |
| $(i,j)$ | $r\in\{1,2\}$ | $(1/2,1/2,1/2,(c-3)/2)$ |
| $(i,j)$ | $3\le r<i$ | $(1/4,1/4,1/4,1/4)$ |
| $(i,j)$ | $r=i$ | $(1/2,1/2,0,0)$ |
| $(i,j)$ | $i<r<j$ | $(0,0,1/2,1/2)$ |
| $(i,j)$ | $r=j$ | $(0,0,1,0)$ |
| $(i,j)$ | $r>j$ | $(0,0,0,1)$ |

The early pair rows contribute their stated $\nu$ cell masses,
half to each early numerical label and their sum to zero.
For a late correct label before both late queries, its fair suffix
splits into quarters. At the first queried address it splits into
halves; between the addresses its cells are $10,11$; at the second
address its cell is $10$; after both its cell is $11$.
The positive row contributes one only to zero in $11$.
This derives the table directly from every scored word, including
earlier and unqueried labels.

The sums of cell maxima are always $c+1$.
Every shorter function embeds in a distinct pair by ignoring another
coordinate, preserving its positive output. Thus all columns have
reward at most $c+1$. The anchor $R$ attains it in $O\subset N$,
so both costs vanish.

On a late pair, zero is the unique maximizer in each of $00,01$,
with reward one; every other label earns at most one half.
If $u\ne v$, at least one of these cells loses at least one half.
The table $N(i,j;i,0,0,0)$ loses exactly one half.
Separately, positive output 1 or 2 loses at least one in $11$:
the head-pair gap is one, the mixed-pair gap is at least one,
and the late-pair gap is $(c-1)/2\ge1$.
The cells of these two losses are distinct, so they add.
Pair embedding proves the positive-output bound for shorter tables.
This proves (274.2), with columnwise half-gap sharpness only.

Define the actual nonnegative slacks

$$
\begin{gathered}
s_c(w)=\mu_w(n)-(b_n-e)\quad(w\in\Omega_n,n\ge3),\\
r_1(z)=\mu_{01z}(\{0,1\})-M+e,\quad
r_2(z)=\mu_{10z}(\{0,2\})-M+e,\quad
s_+=\mu_+(0)-M+e.
\end{gathered}
\tag{274.5}
$$

Their weighted sum is exactly

$$
S_Y=s_++\sum_{n=3}^L2^{-(L-n)}\sum_v s_c(1^{n-1}0v)
       +\tfrac12\int(r_1+r_2)\,d\nu.
\tag{274.6}
$$

On the same allocation,
$Y G_N\lambda=F_Y+S_Y=-\delta_b+S_Y
=-\sum_D\lambda_Dd_Y(D)$.
This proves the identity and, by summing (274.2), its inequality.
At zero reserve all nonnegative terms vanish. Every late correct
row has strictly positive coefficient, giving (274.4) on its
entire fibre. Zero column deficit forces the unique maximizing
labels zero in both late first-zero cells. Positive and supported
early pair slacks give the remaining conclusions. No different
allocation or independently attained margin was combined. $\square$

**Theorem 274.3 (Necessary unrestricted-score bound with signed early loss).**
For every full $y\ge0$ define

$$
\begin{gathered}
H_{ij}^y(r)=\sum_{w:w_i=w_j=0}g_y(w,r),\\
\omega_{\rm late}(y)=\max_{3\le i<j\le L}
                  \bigl(\max_rH_{ij}^y(r)-\min_rH_{ij}^y(r)\bigr),\\
\mathcal E_y(\lambda)=
 \sum_{D=N(i,j;u,v,s,t),\ i\le2}
             \lambda_D\bigl(H_{ij}^y(u)-H_{ij}^y(v)\bigr).
\end{gathered}
\tag{274.7}
$$

The early term is signed. For the same full feasible allocation,

$$
F_y+S_y\le M\Delta_O(y)+\mathcal E_y(\lambda)
       +2\omega_{\rm late}(y)(\delta_b-S_Y-\eta).
\tag{274.8}
$$

Thus, if $\Delta_O(y)\le1$, $M\ge1$ and $g=F_y-M>0$,

$$
g+S_y+M(1-\Delta_O(y))
\le\mathcal E_y(\lambda)
       +2\omega_{\rm late}(y)(\delta_b-S_Y-\eta).
\tag{274.9}
$$

**Proof.** Replace each pair by its endpoint table $O(i,j;v,s,t)$,
keeping shorter tables and all coefficients. The exact reward loss
of that column is $H_{ij}^y(u)-H_{ij}^y(v)$.
The late loss is zero for $u=v$, and otherwise at most
$\omega_{\rm late}(y)$. The early loss is the single signed
aggregate in (274.7), without positive-part substitution.
The repaired conic allocation has mass $M$ and reward excess at
most $M\Delta_O(y)$, whereas the old excess is exactly $F_y+S_y$.
Use $\Gamma_{\rm late}\le2(\delta_b-S_Y-\eta)$ from (274.3),
then subtract $M$ for (274.9).

The early term has not been paid or given a favorable sign.
For example $N(1,j;1,0,j,0)$ has zero potentials in Section 275
but unequal first-zero cells. These are column facts, not a full
feasible separator or an obstruction to a wholly different stopped
law. Zero reserve does not imply full $O$ membership, and no
positive-cap zero-reserve attainer is asserted. $\square$

## 275. A sharp late-cell potential retaining every double-zero slack

**Definition 275.1 (Potentials of the same complete table).**
Let $L\ge6$, so $c>3$. Use the same balanced $\nu$ and define

$$
\begin{aligned}
t_D&=\sum_{j\in J}([D(v^j)=j]-[D(+)=j]),\\
a_D&=\tfrac12\int([D(01z)\in J]+[D(10z)\in J])\,d\nu,\\
g_D&=a_D-t_D,\qquad
x_D=\tfrac12\int([D(01z)=2]+[D(10z)=1])\,d\nu,\\
\ell_D&=\sum_{3\le i<j\le L}
                  ([D(v^i)=i]-[D(v^{ij})=i]).
\end{aligned}
\tag{275.1}
$$

For a late pair let $H_D=[u\ne0]+[v\ne0]$; for other schedules
let $H_D=0$. Set $H_\lambda=\sum_D\lambda_DH_D$,
$G=\sum_D\lambda_Dg_D$ and $X=\sum_D\lambda_Dx_D$.
For a full feasible allocation also put

$$
s_i=\mu_{v^i}(i)-(b_i-e),\qquad
s_{ij}=\mu_{v^{ij}}(i)-(b_i-e)\quad(3\le i<j\le L).
\tag{275.2}
$$

These nonnegative quantities are their own full correct-row slacks.
The same-allocation identity of Theorem 271.2, consumed here, is

$$
\delta_b=s_++\sum_{j\in J}s_j+\eta+R_{\rm pair}+X+G,
\qquad R_{\rm pair}=\tfrac12\int(r_1+r_2)\,d\nu.
\tag{275.3}
$$

For clarity, its equal-mass cancellation is
$\mu_{01z}(J)=e-r_1(z)-\mu_{01z}(2)$ and
$\mu_{10z}(J)=e-r_2(z)-\mu_{10z}(1)$, so
$\sum_D\lambda_Dt_D+G+R_{\rm pair}+X=ce$.
The positive and sole-zero rows give
$\sum_D\lambda_Dt_D=E_b+2e+s_++\sum_js_j+\eta$.
Subtraction is (275.3). The identity and balanced moments are used
as existing results, without a second scalar capacity theorem.

**Theorem 275.2 (Column potential and its full-allocation consequence).**
Every deterministic complete $N$ table satisfies

$$
g_D\ge0,\qquad H_D\le\ell_D+2(g_D+x_D).
\tag{275.4}
$$

The coefficient two is sharp at column level. Every one full feasible
allocation, at any real $b$ and $e\ge0$ and any mass, satisfies

$$
\begin{aligned}
H_\lambda+\sum_{3\le i<j\le L}s_{ij}
 &\le\sum_{i=3}^L(L-i)s_i+2(G+X),\\
0\le\Gamma_{\rm late}\le H_\lambda&\le(L-3)\delta_b.
\end{aligned}
\tag{275.5}
$$

At $\delta_b=0$, every positive-mass late pair has the whole-table
form $N(i,j;0,0,s,0)$ with $s\in\{0,j\}$. All $s_{ij}$ vanish,
and every entire late correct fibre has the value in (274.4).
No monotonicity, head equality, fixed unary law or normalization
is needed for (275.4)–(275.5).

**Proof.** Write $E=\{1,2\}$. If no late bit is queried then
$t_D=\ell_D=0$ and $g_D=a_D\ge0$.
For a late singleton at $j$ with zero/one outputs $s,t$,

$$
g_D=2[s\in J]+(c-2)[t\in J]-[s=j]+[t=j].
\tag{275.6}
$$

For a mixed pair $(h,j)$, $h\in E$, its four outputs give

$$
g_D=[u\in J]+[s\in J]-[s=j]
          +\tfrac{c-2}{2}([v\in J]+[t\in J])+[t=j].
\tag{275.7}
$$

Both are nonnegative. In either of these schedule types,
$\ell_D=[t\in J,t<j]-[s\in J,s<j]$.
Its only negative term, if present, contributes at least one to
$g_D$. Hence $\ell_D+g_D\ge0$, which proves (275.4) there
because $H_D=0$ and $x_D\ge0$. Empty and early singleton
tables were included in the no-late case.

For a late pair $D=N(a,b;u,v,s,t)$, $3\le a<b\le L$, direct
evaluation of the sole-zero, double-zero and positive words gives

$$
\begin{aligned}
g_D={}&[u\in J]+[v\in J]-[v=a]+[s\in J]-[s=b]\\
 &+(c-3)[t\in J]+[t\in\{a,b\}],\\
2x_D={}&[u\in E]+[v\in E]+[s\in E]+(c-3)[t\in E],\\
\ell_D={}&[v=a]-[u=a]+2[t\in J,t<a]
             -[v\in J,v<a]-[s\in J,s<a]\\
 &+[t\in J,a<t<b]-[s\in J,a<s<b].
\end{aligned}
\tag{275.8}
$$

The first line is a sum of nonnegative grouped terms.
To see the last formula, a correct label below $a$ can change
only when the added zero is at $a$ or $b$, giving the two
$t$-to-$v,s$ differences. Between $a$ and $b$ only the added
zero at $b$ matters. At $a$ the change is $v$ to $u$.
At or above $b$ there is no later queried bit. This exhausts
every term in $\ell_D$, including earlier unqueried labels.

Group $\ell_D+2g_D+2x_D$ by the four actual outputs. Its terms are

$$
\begin{aligned}
U={}&-[u=a]+2[u\in J]+[u\in E]\ge[u\ne0],\\
V={}&2[v\in J]-[v=a]-[v\in J,v<a]+[v\in E]\ge[v\ne0],\\
S={}&2[s\in J]-2[s=b]-[s\in J,s<a]
                   -[s\in J,a<s<b]+[s\in E]\ge0,\\
T'={}&2[t\in J,t<a]+[t\in J,a<t<b]+2(c-3)[t\in J]\\
 &+2[t\in\{a,b\}]+(c-3)[t\in E]\ge0.
\end{aligned}
\tag{275.9}
$$

For $S$, the values are zero at $0,b$, one at a late label below
$b$ other than $a$, two at $a$ or above $b$, and one at an early
label. Thus no label case is omitted. The sum proves (275.4).
The column $N(3,4;1,0,0,0)$ has
$(H_D,\ell_D,g_D,x_D)=(1,0,0,1/2)$, so no smaller coefficient
than two works. This is column sharpness, not feasible-law
sharpness at a hard-hull profile.

Linearity under the one allocation gives exactly

$$
\sum_D\lambda_D\ell_D
=\sum_{3\le i<j\le L}(\mu_{v^i}(i)-\mu_{v^{ij}}(i))
=\sum_{i=3}^L(L-i)s_i-\sum_{3\le i<j\le L}s_{ij}.
\tag{275.10}
$$

Integrate (275.4) and substitute this equality to obtain the first
line of (275.5). A late pair with $u\ne v$ has at least one
nonzero first-cell label, so $\Gamma_{\rm late}\le H_\lambda$.
In (275.3) all terms are nonnegative. Since $L\ge6$,
$L-i\le L-3$ and $2\le L-3$; dropping the double-zero slacks
therefore gives the final bound.

At zero reserve all charges vanish, hence every positive-mass
table has $g_D=x_D=0$, and every late pair has $u=v=0$.
In (275.8), $c-3>0$ excludes late $t$, and $x_D=0$ excludes
early $s,t$. The remaining possibility is $t=0$, $s\in\{0,b\}$.
The allocation inequality also forces all $s_{ij}=0$.

One can check the entire-fibre statement directly. A table with
no late query is constant on each late first-zero fibre. Formula
(275.6) excludes late outputs from a zero-charge late singleton.
In a mixed pair, (275.7) allows a late label on the early-11
fibre only as its queried label $j$ in cell $10$; that cell is
reached on every first-zero-$j$ word. A late pair now can emit
only its second address $b$ in $10$, reached on every
first-zero-$b$ word. Thus for every positive-mass table,
$[D(w)=n]=[D(v^n)=n]$ whenever $n(w)=n\ge3$.
Integrate and use $s_n=0$. These are conditional equalities;
Section 278 excludes this zero-reserve boundary at positive caps
for $L\ge6$. $\square$

## 276. Observable curvature and head budgets for Borel kernels

**Definition 276.1 (Equal-mass measure kernels without output restrictions).**
Let $L\ge3$ and let $\mu_w$ be finite nonnegative Borel measures
on the full carrier $\Theta$, all of mass $M\ge0$, obtained by
one measurable nonnegative allocation over complete $N$ or $O$
tables. Each terminal value may be any point of $\Theta$; no
support, feasibility, marginal or decomposition restriction is
imposed. The finite marked catalog is a special case.
For a total-mass-zero signed measure $\xi$ put
$\|\xi\|_{\rm TV}=|\xi|(\Theta)/2$.
Let $E_j=\{\theta_j\}$, disjoint actual Borel events, and define

$$
\rho_i=\max_{w,v\in\Omega_i}\|\mu_w-\mu_v\|_{\rm TV}\ (i=1,2),
\qquad f_{ab}(x)=\mu_{(a,b,1-x)},\quad x\in\{0,1\}^{J}.
\tag{276.1}
$$

For any such suffix function write
$\tau(f)=\sum_{j\in J}(f(e_j)(E_j)-f(0)(E_j))$, and put
$\mathcal T=\tau(f_{11})$.
With $e_j$ now denoting the suffix unit vector, set

$$
\begin{gathered}
c_{jk}=f_{10}(e_j+e_k)-f_{10}(e_j)-f_{10}(e_k)+f_{10}(0),\\
\kappa=-\tfrac12\sum_{j<k}c_{jk}(E_j\cup E_k),\qquad
H_i=M-[\mu_{v^i}(E_i)-\mu_+(E_i)]_+\quad(i=1,2).
\end{gathered}
\tag{276.2}
$$

The symbol $[t]_+=\max(t,0)$ in this definition is not applied
to $\kappa$. Curvature remains signed. These are observables of
the same measure kernel, independent of a chosen table representation.

**Theorem 276.2 (Unrestricted necessary curvature and variation bounds).**
Put $(\gamma_C,a_C)=(1,2)$ for $N$ and $(2,1)$ for $O$.
Every kernel in Definition 276.1 satisfies

$$
\begin{aligned}
\gamma_C|\kappa|&\le\min(H_1,H_2),\\
|\mathcal T-\kappa|
&\le\min\left\{
2\rho_2+\min\{4\rho_1,a_C(H_1-\gamma_C|\kappa|)\},
2\rho_1+a_C(H_2-\gamma_C|\kappa|)\right\}.
\end{aligned}
\tag{276.3}
$$

All remaining head budgets in parentheses are nonnegative.
These are necessary conditions, not a characterization of
realizable kernels or a sufficient signed certificate.

**Proof.** For a fixed seed, the output measure depends on at most
two distinct bits. Its event evaluations, and hence the measure
itself by finite Boolean differences, are multilinear of degree
at most two. Integration preserves these measure equalities.
A suffix-pair interaction cannot also depend on either early bit,
since that would require a third queried coordinate. Thus each
$c_{jk}$ is the same on every prefix fibre.

Write a suffix function as a signed-measure polynomial
$f(x)=A+\sum_jB_jx_j+\sum_{j<k}C_{jk}x_jx_k$ and put
$W_j=B_j+\frac12\sum_{k\ne j}C_{jk}$.
For signs $s_j\in\{-1,1\}$ and $x=(1+s)/2$, expansion gives

$$
f(x)-f(1-x)=\sum_js_jW_j,\qquad
\mathbb E_s\sum_js_j(f(x)-f(1-x))(E_j)
 =\sum_jW_j(E_j)=\tau(f)-\kappa.
\tag{276.4}
$$

For any total-mass-zero signed Borel measure $d$, disjointness
gives $|\sum_js_jd(E_j)|\le\sum_j|d(E_j)|\le2\|d\|_{\rm TV}$.
If $f$ has diameter at most $\rho$, (276.4) yields
$|\tau(f)-\kappa|\le2\rho$. Apply this to $f_{10}$ and
$f_{01}$, of diameters at most $\rho_2$ and $\rho_1$.
No finite-support approximation of a Borel measure is used.

For any representation let $q_0$ be its mass on two distinct late
addresses, $q_1$ its mass on $\{1,j\}$ with $j\in J$, and
$q_2$ its mass on $\{2,j\}$ with $j\in J$.
A late-pair column has curvature

$$
\kappa_D=\tfrac12\bigl([v\in E_j\cup E_k]+[s\in E_j\cup E_k]
                       -[u\in E_j\cup E_k]-[t\in E_j\cup E_k]\bigr).
\tag{276.5}
$$

Here membership means membership of its actual terminal tape.
Other schedules contribute zero. The absolute value is at most
one in $N$. In $O$, $u=v$, so it is at most one half.
Consequently $\gamma_C|\kappa|\le q_0$.

The measure function $h=f_{01}-f_{00}$ is affine in $x$, has
total mass zero, and $\sup_x\|h(x)\|_{\rm TV}\le\rho_1$.
Apply the affine version of (276.4) to $h(x)-h(1-x)$.
Its TV norm is at most $2\rho_1$, giving $|\tau(h)|\le4\rho_1$.
Only schedules $\{2,j\}$ contribute to this trace: unqueried
selected coordinates cancel, and querying the head alone gives a
constant suffix function. Each $N$ table contributes a difference
of two indicator increments, of absolute value at most two.
For $O$ the head-zero branch has already stopped and is constant,
so the bound is one. Hence also $|\tau(h)|\le a_Cq_2$.

The mixed prefix difference
$f_{11}-f_{10}-f_{01}+f_{00}$ is constant in the suffix, again
by the degree-two bound. Taking traces therefore gives
$\mathcal T=\tau(f_{10})+\tau(h)$. The preceding estimates imply

$$
|\mathcal T-\kappa|
\le2\rho_2+\min(4\rho_1,a_Cq_2),\qquad
|\mathcal T-\kappa|\le2\rho_1+a_Cq_1.
\tag{276.6}
$$

The second inequality uses $f_{01}$ and $f_{10}-f_{00}$ instead;
it does not identify the targets on different early fibres.

Let $t_i=\mu_{v^i}(E_i)-\mu_+(E_i)$. A table avoiding $i$
contributes zero, while one querying $i$ contributes at most its
mass. Thus the mass querying $i$ is at least $[t_i]_+$,
so $H_i\ge0$ bounds the mass avoiding it.
The disjoint schedule classes counted by $q_0,q_2$ avoid 1,
and those counted by $q_0,q_1$ avoid 2. Therefore

$$
q_0+q_2\le H_1,\qquad q_0+q_1\le H_2.
\tag{276.7}
$$

Eliminate them using $q_0\ge\gamma_C|\kappa|$ in (276.6).
This proves (276.3) for actual Borel measures and every
representation, with both signs of curvature and every terminal
tape retained. The finite sign average is a proof operation, not
another source-dependent or operational seed. $\square$

**Corollary 276.3 (Exact conic slack substitution on the same Borel law).**
If the same kernel satisfies the full rows (273.3), interpreted as
the actual marked Borel events, put

$$
\begin{gathered}
s_+=\mu_+(E_0)-M+e,\quad s_j=\mu_{v^j}(E_j)-(b_j-e),\\
\eta=\mu_+(E_1)+\mu_+(E_2),\quad
\omega=\mu_+(\Theta\setminus\{\theta_0,\ldots,\theta_L\}),\\
u_i=\mu_{v^i}(E_i)-(M-1+b_i-e)\quad(i=1,2).
\end{gathered}
\tag{276.8}
$$

All these quantities are nonnegative. Then exactly

$$
\begin{aligned}
\mathcal T&=E_b+2e+s_++\sum_{j\in J}s_j+\eta+\omega,\\
H_i&=\min\{M,1-b_i+e+\mu_+(E_i)-u_i\}\\
&\le\min\{M,1-b_i+2e-u_i-s_+\}.
\end{aligned}
\tag{276.9}
$$

Substituting these actual values in (276.3) is a necessary joint
constraint on every full cap-feasible allocation. The trace part
consumes the same-allocation identity of Theorems 266.2 and 268.4;
the Borel expression retains its actual outside-mark mass $\omega$.

**Proof.** Sum the late correct equalities to obtain
$\sum_J\mu_{v^j}(E_j)=E_b+3e+\sum_Js_j$.
Equal mass and the positive row give
$\sum_J\mu_+(E_j)=e-s_+-\eta-\omega$.
Their difference proves the trace identity, retaining mass outside
all marks. The definition of $H_i$ and the early correct equality
give its exact minimum expression. Finally
$\mu_+(E_i)\le e-s_+$ by the same positive row and nonnegativity.
No union row is inferred from singleton rows, and $M$ has not
been divided out at unchanged $b$. $\square$

**Proposition 276.4 (An all-word family and the actual active length).**
For $m\ge2$, let $L=m+2$, $C=\binom m2$ and $0<s\le1/2$.
Use mass $1-s$ on $R$ and mass $s/C$ on every late pair
$N(i,j;0,i,j,0)$. Put

$$
e=s\frac{\lfloor m^2/4\rfloor}{C},\qquad
a_1=a_2=1-s,\qquad a_n=\frac e{n-2}\quad(n\ge3).
\tag{276.10}
$$

This is an original positive nonincreasing vanishing profile and
one all-word cap-$e$ realization. Its observables are

$$
\mathcal T=2s,\quad\kappa=s,\quad H_1=H_2=s,
\quad\rho_1=\rho_2=e.
\tag{276.11}
$$

The auxiliary construction length $m+2$ is not its actual active
length: $a_3=e$, and $L_a=2$ whenever $1-s>e$.
At the degenerate endpoint $m=2,s=1/2$, also $a_1=a_2=e$,
so $L_a=0$. In all cases every $n\ge3$ is inactive at this cap.
The different law $(1-s)R+s\,\text{constant }0$ is stopped and
meets the same cap; it has curvature zero.

**Proof.** If the late zero set is $Z$, $|Z|=k$, the pair
component gives each $j\in Z$ mass $(m-k)/C$. Its total nonbase
mass is $t_k=k(m-k)/C\le\lfloor m^2/4\rfloor/C$.
At an early first zero, correct mass is $1-s$, base mass is
$s(1-t_k)$ and error is $st_k\le e$.
At a late first zero, the whole law has base mass $1-st_k$,
and the target amplitude $a_n\le e$. The base deficit is at most
$st_k$, the correct deficit is at most $a_n$, and the independent
union deficit is at most $st_k$. Thus all three rows hold on
every multiple-zero word. The positive word outputs zero, so
each actual tail $n>L$ has exact error $a_n\le e$.
Since $\lfloor m^2/4\rfloor/C\le1$, the entire profile is
ordered. It is strictly positive and vanishes. The stated strict
head inequality fails only at the displayed endpoint.

At a sole late zero $j$, its correct mass is
$s(m-1)/C$; summing gives $\mathcal T=2s$.
Every late-pair column has curvature one, while $R$ has zero,
so $\kappa=s$. The early contrasts equal $1-s$, giving
$H_1=H_2=s$.

For late zero sets of sizes $k\le l$ and overlap $h$, the pair
law has common mass $h(m-l)/C$ on their common nonzero labels.
Its common base mass is
$1-\max\{k(m-k),l(m-l)\}/C$.
Subtracting total common mass from one gives exactly

$$
\operatorname{TV}(p_Z,p_{Z'})
=\frac{\max\{k(m-k),l(m-l)\}-h(m-l)}C
\le\frac{\lfloor m^2/4\rfloor}C.
\tag{276.12}
$$

A maximizing set versus the empty set attains equality.
On each early fibre $R$ is constant, so scaling by $s$ proves
both diameter values in (276.11).
The $N$ inequality (276.3) reduces to $s\le2e$ here, and
$s/(2e)=C/(2\lfloor m^2/4\rfloor)\to1$.
Thus the coefficient two cannot be uniformly reduced in this
joint relation. Locally, the curvature bounds one and one half
are attained by $N(i,j;0,i,j,0)$ and $O(i,j;i,j,0)$.
The head-interaction prices two and one are attained by mixed
tables with four-cell outputs $(0,j,j,0)$ and $(0,0,j,0)$.

For the alternative stopped law, early correct mass remains
$1-s$ and early base mass is $s$, so the early target is exact.
On every late first-zero class the output is zero, with error
$a_n\le e$. It therefore meets every independent row and actual
tail at the same closed cap, with different curvature and law.
Both constructions use one source-independent whole-table seed
and at most two actual requests. The family illustrates necessary
observable sharpness; it supplies no new amplitude coverage or
feasibility separator. Theorem 110.2 need not preserve its law or
curvature when selecting a representative at its shorter actual
active length. $\square$

## 277. One signed payer for the full interleaved input class

**Theorem 277.1 (All coefficient totals and one residual).**
Fix $L\ge7$, $3<r<k<\ell<m\le L$, $s\ge0$ and
$0\le h\le47s/13$. Let $y$ be any full nonnegative score with

$$
\beta_1=-s,\quad\beta_3=s,\quad\beta_r=-s,\quad
\beta_k=s,\quad\beta_\ell=h,\quad\beta_m=s,
\qquad\beta_i=0\text{ otherwise}.
\tag{277.1}
$$

Here $m$ is the final selected address, rather than the suffix
cardinality $L-2$ used in the surrounding sections.
There is no restriction on its word support, event placements,
$A/C$ cancellations, $P$, $T$, baseline or actual total $K$.
Necessarily $K\ge5s+h$. One explicit full $V\ge0$ satisfies

$$
\Delta_N(V)=0,\qquad\sigma_H(Qy-QV)=s,
\qquad\Delta_O(y)\ge s.
\tag{277.2}
$$

Consequently every unit-$O$ input in this entire class admits the
single jointly paid certificate $(V,\theta=s)$, with
$\Delta_N(V)+\theta=s\le1$.
For every same $(b,e)\in H_N$ and every same complete feasible
$\lambda$ of mass $M\ge1$, a unit-$O$ input in this class has
$F_y(b,e)\le s\le1\le M$, and hence cannot be a strict separator.

**Proof.** Put $J_*=(3,r,k,\ell,m)$, and for a zero set $Z$
let $w(Z)$ be the full $L$-word with precisely those zeros.
Use the existing five-coordinate zero-cost ray from the balanced
capacity construction of Sections 201.2 and 204.2:

$$
C_{w(\{j\})}(Y_*)=1\ (j\in J_*),\qquad
P_{w(\{a\}\cup Z)}(Y_*)=1/6
\ (a\in\{1,2\},\ Z\subset J_*,\ |Z|=3),\qquad T(Y_*)=1.
\tag{277.3}
$$

All unspecified scores are zero. Giving each three-subset of five
coordinates weight $1/3$ has total $10/3$, zero marginals two,
and pair cells $(1,1,1,1/3)$: there are respectively
$10,6,3,3,3,1$ subsets for the total, a fixed zero, and the four
pair conditions. Thus
$QY_*=(1_{J_*};28/3)$ and $W_{Y_*}=13/3$.

To consume the zero-cost ray on the complete catalog, zero
dominates each label separately on every cell. On $(1,2)$ its
nonempty-cell rewards are $5/3,5/3,1$; early labels earn subsets
of these pair rewards, and each late correct label earns at most
one in $11$. On an early/selected-late pair its four rewards are
$1,2/3,1,5/3$. The queried late correct label earns one in $10$,
and each other selected late correct label earns one in $11$.
On two selected late coordinates the zero rewards are
$1,1,1,4/3$; the two queried correct labels occupy $01,10$,
and all other correct labels occupy $11$, each with reward one.
Other numerical labels earn zero, while remaining legal.
An inactive coordinate is one on every scored word. A query there,
or a shorter, repeated or ignored schedule, gives a coarsening of
these partitions. Summing the label inequalities over merged cells
preserves domination, also under $O$ stopping.
Constant zero earns $13/3$, so
$B_N(Y_*)=B_O(Y_*)=W_{Y_*}=13/3$.
This is an application of that existing ray, not an additional
standalone capacity result.

Let $t=(s+h)/5$ and choose the single score $V=tY_*$.
For every full input, $K\ge\sum_i|\beta_i|=5s+h$ by summing
$|C_i-A_i|\le C_i+A_i$ over its class totals.
Constant zero minus the input's own baseline is
$-\beta_1-\beta_2=s$, giving $\Delta_O(y)\ge s$.

For $(b,e)\in H_L$, let $x=(b_3,b_r,b_k,b_\ell,b_m)$, a
decreasing nonnegative vector. The actual signed residual is

$$
F_{Qy-QV}=s+s(b_3-b_1)+\sum_{i=1}^5a_ix_i-(K-28t/3)e,
\quad a=(-t,-s-t,s-t,h-t,s-t).
\tag{277.4}
$$

Its five coefficient prefix sums are
$-t,-s-2t,-3t,h-4t,0$.
They are nonpositive: $h\le47s/13<4s$ unless $s=h=0$,
and $h-4t=(h-4s)/5$.
Abel summation, with $x_6=0$, gives
$\sum_ia_ix_i=\sum_{j=1}^5(\sum_{i\le j}a_i)(x_j-x_{j+1})\le0$.
Also

$$
K-28t/3\ge5s+h-\frac{28(s+h)}{15}
              =\frac{47s-13h}{15}\ge0.
\tag{277.5}
$$

Since $b_3\le b_1$ and $e\ge0$, (277.4) is at most $s$.
The auxiliary hull origin attains $s$, so its support is exactly
$s$, including $s=h=0$, $h=47s/13$ and all spare $K$.
That origin evaluates closed-hull support; it is not an original
positive-tail attainer.

For unit-$O$ input the constant-zero lower bound implies
$0\le s\le1$. Set $\theta=s$; the one score $V$ has zero
$N$ cost and its one signed residual has support $s$.
At $\theta=1$, nonzero zero-cost $V$ remains allowed.
For the same full feasible $\lambda$,

$$
F_{Y_*}(b,e)\le Y_*G_N\lambda
 =\sum_D\lambda_D(Y_*z_D-W_{Y_*})\le0.
\tag{277.6}
$$

Add the residual estimate to obtain $F_y\le s$.
All rows belong to this one allocation; no normalization or
independent component minimum was used. $\square$

**Mathematical scope 277.2 (Reuse and the sufficient threshold).**
The old five-coordinate ray receives no additional capacity content
from (277.3). The assertion is its explicit use with one signed
residual for every full input (277.1), every actual $K\ge5s+h$
and the stated larger $h$ interval. In particular the exact-$Q$
fibre $K=6s+h$, $0\le h\le s$ of Section 269 is already covered
with budget $s$, without requiring $Q(V)=Q(y)$ or its displayed
exact-$Q$ price $4s/3$.
The number $47/13$ is sufficient for this payer; no optimal
threshold, exact-$Q$ minimum or universal input reduction is claimed.
For example the published score $y=3Y/4$ of Proposition 269.3
has $s=h=3/4$, $\Delta_O(y)=1$ and raw $\Delta_N(y)=7/4$.
The present choice has $\Delta_N(V)=0$ and $\theta=3/4$,
whereas its published exact-$Q$ replacement has cost one.
This consumes that example to compare the two certificate budgets;
its support-maximizing $N$ column is not a cap-feasible primal
attainer.
All original competitor words, labels, independent union rows and
positive rows remain in (277.6). Fixing unused bits on the support
of a dual score does not restrict source words or competitor
addresses. $V$ is a dual score, not an acquisition probability law.
Original applications use the exact feasibility suppliers and actual
tails of Mathematical scope 273.3, with the displayed addresses
inside the finite theorem's length range. No stopped primal
attainer for every profile follows from this scoped input theorem.

## 278. Full correct rows, ordered cuts and a strict capacity bound

**Definition 278.1 (Explicit constants).**
Let $L\ge6$, $m=L-2\ge4$, $c=c_m$ and $k=\lceil m/2\rceil$.
In the balanced measure of Definition 274.1 every $k$-subset has
the same positive weight

$$
w_m=\begin{cases}
c/\binom mk,&m\text{ odd},\\
2/\binom mk,&m\text{ even}.
\end{cases}
\quad
C_m=\frac{(m+1)!}{(m-k+1)!},\quad
\gamma_m=\frac{w_m}{C_m},\quad
a_m=\frac{c-3}{2},\quad B_m=1+\frac m{a_m},\quad
\epsilon_m=\frac{\gamma_m}{1+cB_m}>0.
\tag{278.1}
$$

For example $\epsilon_4=1/5060$ and $\epsilon_5=1/37560$.
These constants are conservative, without a sharpness assertion.

**Theorem 278.2 (Strict necessity for every full feasible conic allocation).**
For every real profile $b$, every $e\ge0$, and every complete
$\lambda\ge0$ of any finite mass satisfying all rows (273.3),

$$
\delta_b=(c_m-2)e-E_b\ge\epsilon_m e,
\qquad
\sum_{j=3}^L(b_j-e)\le(c_m+1-\epsilon_m)e.
\tag{278.2}
$$

In particular $H_N\subset\{E_b\le(c_m-2-\epsilon_m)e\}$.
At positive caps the old boundary $\delta_b=0$ and the strip
$0\le\delta_b<\epsilon_m e$ have no full $N$ allocation.
The hypothesis retains the entire finite feasibility cone, without
monotonicity, hard-hull membership or a chosen output pattern.

**Proof.** Use all potentials and slacks of Section 275, including
the consumed identity (275.3). Let
$\mathfrak h_D=g_D+x_D+[D(+)\in\{1,2\}]$.
It is nonnegative, and every positive value is at least $a_m$.
To verify the gap, expand $x_D$ with the same unary and pair
moments. The late-pair coefficients are $1/2,(c-3)/2$, mixed-pair
coefficients are $1,(c-2)/2$, and no-late fibre coefficients are
$c/2$. The positive early-label indicator has coefficient one.
The grouped nonnegative terms of (275.6)–(275.8) have no negative
remainder. Since $10/3\le c<4$, every nonzero coefficient is at
least $(c-3)/2$.

Setting all those nonnegative terms to zero gives the entire
zero-$\mathfrak h$ catalog below. The pair labels are in
$00,01,10,11$ order; all listed choices are independent except
where stated.

| Schedule | Exactly the zero-charge outputs |
| --- | --- |
| empty | $0$ |
| singleton early $i$ | zero reply in $\{0,i\}$, one reply $0$ |
| singleton late | both replies $0$ |
| $(1,2)$ | $u$ arbitrary, $v\in\{0,1\}$, $s\in\{0,2\}$, $t\in\{0\}\cup J$ |
| $(1,j)$, $j\in J$ | $u,v\in\{0,1\}$, $s\in\{0,2,j\}$, $t=0$ |
| $(2,j)$, $j\in J$ | $u,v\in\{0,2\}$, $s\in\{0,1,j\}$, $t=0$ |
| $(i,j)$, $3\le i<j$ | $u=t=0$, $v\in\{0,i\}$, $s\in\{0,j\}$ |

This includes arbitrary head-pair $00$ outputs and permitted
unqueried early guesses. For no-late tables, $t_D=0$ and
$g_D=a_D$, so the early-fibre late outputs, opposite-head outputs
and positive early outputs vanish exactly as in the list.
For a mixed pair, zeroing (275.7) excludes late $u,v,t$ and permits
late $s$ only at $j$; zeroing $x_D$ excludes the opposite head
in $u,v$, its own head in $s$, and early $t$.
The last line follows by zeroing (275.8) with $c-3>0$.
Thus the list and gap hold for every label and schedule.

For the estimate, remove positive-charge columns. Their mass $\tau$
satisfies

$$
a_m\tau\le G+X+\eta\le\delta_b.
\tag{278.3}
$$

For each late $i$ let $u^i=1^{i-1}0^{L-i+1}$.
In a zero-charge column, the difference
$[D(v^i)=i]-[D(u^i)=i]$ is one exactly for late pairs $(i,j)$,
$j>i$, with $01$ output $i$, and zero otherwise.
Indeed a mixed column can emit a late label only at its queried
late zero, with both words agreeing there; a head-pair late
exhaustion also contributes equally at both words. In a late pair
the last line of the list makes the only loss the change from
$01=i$ to $00=0$ at its first address. All other late correct
labels have equal indicators. This verifies the difference on the
whole catalog, rather than just on sole-zero representatives.

Let $\sigma_i$ be the mass of these exceptional zero-charge pairs.
The removed positive-charge columns contribute at worst $-\tau$
to the same difference. The full correct row at $u^i$ implies
$\mu_{v^i}(i)-\mu_{u^i}(i)\le s_i$. Therefore
$\sigma_i\le s_i+\tau$.
Remove these exceptional columns as well. They are disjoint by
their first address, so with $\sigma=\sum_i\sigma_i$ and total
deleted mass $d=\tau+\sigma$,

$$
\sigma\le\sum_js_j+(m-1)\tau,\qquad
d\le\delta_b+m\tau\le B_m\delta_b.
\tag{278.4}
$$

The retained suballocation is a part of the same original law.
It is not asserted to be feasible, normalized or an acquisition
meeting the original cap.

In this retained suballocation, let $A_j$ be the mass of mixed
$(1,j)$ tables with $10$ output $j$, and $B_j$ the corresponding
$(2,j)$ mass. Let $D_{ij}$ be the mass of late $(i,j)$ tables
with $10$ output $j$. For a suffix zero set $Z\subset J$, the
late-output masses on the early $01$ and $10$ fibres are exactly

$$
\begin{aligned}
f_1(Z)&=\sum_jB_j[j\in Z]
           +\sum_{i<j}D_{ij}[i\notin Z,j\in Z],\\
f_2(Z)&=\sum_jA_j[j\in Z]
           +\sum_{i<j}D_{ij}[i\notin Z,j\in Z].
\end{aligned}
\tag{278.5}
$$

The other retained columns contribute no late label on these
fibres. All coefficients are nonnegative, and the same $D_{ij}$
appears in both functions. The full original independent pair
rows give
$0\le f_h(Z)\le\mu_{\text{early }h,Z}(J)\le e$ for every $Z$.
If $\ell_h(Z)$ is deleted late mass, $0\le\ell_h(Z)\le d$, then

$$
e-f_h(Z)=r_h(Z)+\chi_h(Z)+\ell_h(Z),\qquad
\tfrac12\int((e-f_1)+(e-f_2))\,d\nu
\le R_{\rm pair}+X+cd\le(1+cB_m)\delta_b.
\tag{278.6}
$$

Here $\chi_1=\mu_{01Z}(2)$ and $\chi_2=\mu_{10Z}(1)$,
the actual opposite-head errors. The equality uses full equal-mass
rows; it does not endow the retained part with their feasibility.

It remains to lower-bound the deficit of these ordered cuts.
Consider $r$ ordered vertices and

$$
f(Z)=\sum_ja_j[j\in Z]+\sum_{i<j}d_{ij}[i\notin Z,j\in Z],
\qquad a_j,d_{ij}\ge0,\qquad f(Z)\le e\text{ for all }Z.
\tag{278.7}
$$

Suppose $1\le s\le r-2$ and $e-f(Z)\le\zeta$ on every
$s$-subset. For an $s$-subset $S$ not containing sink $r$,
adding that sink increases $f$ by
$a_r+\sum_{i<r,i\notin S}d_{ir}$.
This is nonnegative and at most $\zeta$, since
$f(S)\ge e-\zeta$ and $f(S\cup\{r\})\le e$.
For each $i<r$ an $s$-subset can avoid both $i,r$, exactly
because $s\le r-2$. Hence $a_r\le\zeta$ and every
$d_{ir}\le\zeta$. For each $(s-1)$-subset $T$ of the first
$r-1$ vertices, adding $r$ changes $f$ by at most $r\zeta$.
Since $f(T\cup\{r\})\ge e-\zeta$,
$e-f(T)\le(r+1)\zeta$.

Restriction to the first $r-1$ vertices leaves another function
of form (278.7), bounded by $e$ on every subset.
Begin with $r=m,s=k$ and
$\zeta=\max_{|Z|=k}(e-f(Z))$. The condition $s\le r-2$
holds and is preserved after each removal. After $k$ removals
the layer is the empty set, of value zero. Multiplying the factors
$r+1$ yields

$$
e\le C_m\max_{|Z|=k}(e-f(Z)),\qquad
\int(e-f)\,d\nu\ge w_m\max_{|Z|=k}(e-f(Z))\ge\gamma_me.
\tag{278.8}
$$

The integrated inequality follows because all deficits are
nonnegative and each $k$-subset is an atom of mass $w_m$.
Apply it separately to the two actual functions in (278.5).
Their average integral is at least $\gamma_me$ and by (278.6)
at most $(1+cB_m)\delta_b$. This proves (278.2).
Every deletion, row comparison and cut belongs to the same full
allocation; no mass division, separately optimal charge or removal
of a negative demand is used. All inequalities are closed,
including $e=0$. $\square$

**Corollary 278.3 (Existence of a full zero-cost score on the improved cone).**
Let $\beta^*_j=1$ for $j\in J$, $\beta^*_1=\beta^*_2=0$, and
$K^*=m+c_m+1-\epsilon_m$. There exists a full nonnegative score
$V_m$ with

$$
Q(V_m)=(\beta^*;K^*),\qquad\Delta_N(V_m)=0.
\tag{278.9}
$$

For every full input $y\ge0$ with
$Qy=(t\beta^*;K)$, $t\ge0$, $K\ge tK^*$, there exists one
full $V\ge0$ with $QV=Qy$, $\Delta_N(V)=0$ and $\theta=0$.
It is an existence conclusion on this entire quotient cone, without
a specified row-coefficient selector outside or inside it.

**Proof.** Put $u=b-\alpha$, with $u$ free in $\mathbb R^L$,
and write $h=\mathcal H u-e\mathbf1$. The finite matrix
$\mathcal H$ has coefficient $-1$ in each base row of its
first-zero coordinate, $+1$ in each correct row, and zero in
pair and positive rows. Consider the entire finite cone

$$
\mathcal P=\{(u,e,\lambda):
G_N\lambda-\mathcal H u+e\mathbf1\ge0,
\quad e\ge0,\ \lambda\ge0,\ u\text{ free}\}.
\tag{278.10}
$$

It contains zero. Theorem 278.2, valid for every real $b$ on
these full rows, says
$\beta^*\cdot u-K^*e\le0$ throughout $\mathcal P$.
Apply the valid-inequality multiplier theorem for a nonempty finite
polyhedron, Kaibel, *Basic Polyhedral Theory*,
[Theorem 12, arXiv:1001.2161v1](https://arxiv.org/html/1001.2161v1).
In its notation a valid $a^Tx\le\beta$ on a nonempty
$\{x:Ax\le b\}$ has multipliers $v\ge0$ with
$v^TA=a^T$ and $v^Tb\le\beta$.
The cone (278.10) is nonempty and all dimensions are finite.
Coefficient matching for free $u$, nonnegative $\lambda$ and
nonnegative $e$ gives one $V\ge0$ on the original event rows with

$$
\mathcal H^TV=\beta^*,\qquad G_N^TV\le0,
\qquad\sum V\le K^*.
\tag{278.11}
$$

Explicitly, express the first constraint as
$-G_N\lambda+\mathcal H u-e\mathbf1\le0$ and also include
$-\lambda\le0,-e\le0$. The latter multipliers are
$-G_N^TV\ge0$ and $K^*-\sum V\ge0$, respectively.
This checks all multiplier signs without restricting $u$ to the
hard hull or replacing the full cone by deleted columns.

Add $K^*-\sum V$ to the original positive-row coefficient $T$.
That row has quotient increment $(0;1)$ and $G_N$ entries
$[D(+)=0]-1\le0$. Thus the resulting $V_m$ has exact $Q$
as in (278.9) and $G_N^TV_m\le0$.
The anchor column is zero, so its maximal excess is exactly zero.
For the stated input use
$V=tV_m+(K-tK^*)T_+$, where $T_+$ denotes unit positive-row
score. It has exact $Q$, is nonnegative, and has zero cost by
the same column argument. The residual is zero on the whole
$H_L$, so $\theta=0$ suffices.
This consumes the standard finite Farkas conclusion; it supplies
neither individual coefficient formulas nor an arbitrary-query
acquisition from that dual score. $\square$

**Mathematical comparison 278.4 (Parity and an excluded actual profile).**
The protected shared-terminal supplier of
[Theorem 207.13](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md)
already gives the all-late capacity coefficient $c_{m-1}$.
Indeed take its $m-1$ internal addresses to be $J\setminus\{L\}$,
its common terminal address to be $L$, its correct masses $s=1$
and its positive-row mass $T=1$, with no early correct scores.
Its protection conditions are the actual unary capacities at least
two and every directed capacity at least one. The attaining
balanced measure has stock $c_{m-1}$, so that existing score has
$\beta=1_J$, $K=m+c_{m-1}+1$ and zero $N$ cost. Pairing with
the same full feasible allocation yields
$E_b\le(c_{m-1}-2)e$.
For odd $m\ge5$, $c_{m-1}=c_m$; hence (278.2) improves that
specific inequality by $\epsilon_me$.
For even $m=2q\ge4$, $c_m-c_{m-1}=2/(q(q+1))$.
The old inequality is stronger: $w_m\le1/3$,
$C_m\ge m(m+1)$, so
$\epsilon_m<1/(3m(m+1))<2/(q(q+1))$.
Thus no additional numerical or quotient coverage is asserted
there relative to that supplier. The comparison concerns this
checked predecessor, without a claim about every possible older
consequence or sharp constants.

For a concrete odd case take $L=7$ and the entire profile

$$
e=1/20,\qquad a_1=\cdots=a_7=7/75,\qquad
a_n=\frac1{20(n-7)}\quad(n\ge8).
\tag{278.12}
$$

It is positive, nonincreasing and vanishing, with actual active
length seven and closed tail tie $a_8=e$.
Its finite point belongs to $H_7$ and has
$E_b=5(7/75)-8/20=1/15=(c_5-2)e$.
But (278.2) requires $E_b\le1/15-1/751200$.
Consequently no original $N_2$, hence no $O_2$, acquisition
attains this cap: exact closed-cap necessity of Theorem 110.2
would otherwise supply a full finite mass-one witness.
It is an excluded candidate profile, not a same-feasible-point
$N/O$ separator; in particular it has no original $N$ attainer.

## 279. Original regressions and the remaining unrestricted comparison

**Mathematical application 279.1 (An actual earlier unqueried label).**
At the source $(r,g)=(19,436)$, the recurrence gives $F_{19}=4181$,
the admissible window is $419\le g\le836$, and
$N=1+4181\cdot436=1822917$. The number is odd, divisible by
three, congruent to two modulo five and five modulo seven.
Thus its first four replies are $0100$.
The legal $N(3,4;1,0,0,0)$ emits label 1, earlier than and
unqueried by its schedule. Its endpoint repair
$O(3,4;0,0,0)$ emits 0 there. The pure-table changed mass is
one. Its old counting defect is two: the sole-zero correct count
is zero, the positive base count is one, and the deficit from
three is $3-1=2$.
The half-gap in (274.2) and coefficient-two equality in (275.4)
include this same column. Their sharpness remains columnwise;
the column is not asserted to be a full feasible strict separator.

**Boundary 279.2 (One unrestricted common budget).**
With every original sequence, source, operation and closed positive
cap of Mathematical scope 273.3, the universal positive obligation
is still: for every full $y\ge0$ with $\Delta_O(y)\le1$, find
one unrestricted full $V\ge0$ and one $\theta\in[0,1]$ such that

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Qy-QV)\le\theta.
\tag{279.1}
$$

Every coordinate of $V$ may change and the residual is signed.
Nonzero zero-cost $V$ at $\theta=1$ is allowed. There is no
fixed-law, anchor, unary, marginal, quotient, canonical-decomposition
or repair restriction on this obligation.
The exact alternative of Sections 199.3–199.4 requires the same
actual $(b,e)\in H_N$, the same complete feasible
$G_N\lambda\ge h(b,e)$ of mass $M\ge1$, and one actual full
unit-$O$ score with $F_y(b,e)>M$, followed by an original $N$
attainer and a uniform lower certificate against every original
arbitrary-address, full-carrier $O$ competitor.

The reserve and potential results of Sections 274–275 retain an
unpaid signed early term. Their zero-face rigidity is conditional,
and Section 278 excludes that old face at positive caps when
$L\ge6$. The Borel curvature relation of Section 276 is necessary;
a replacement stopped law may change curvature, every marginal
and every output law. Section 277 pays its full stated interleaved
input class with one residual; it gives no reduction of all other
inputs to that class. The Farkas consequence of Section 278 gives
existence of a zero-cost full score on its stated quotient cone,
without an individual selector or a general original acquisition.
None establishes (279.1) for every full input or supplies the
strict original alternative.

The balanced measures, the old rays and scalar cuts, the six-charge
identity of Section 271, the fair-fibre and repair mechanisms of
Sections 252–255 and 261–266, and the source/transport and generic
duality suppliers retain their stated mathematical ownership.
The additional conclusions here concern full-fibre and late-cell
information before projection, observable signed curvature and
head expenditure, the explicit signed use of an existing ray, and
full-correct-row elimination followed by ordered-cut stability.
All pair events, negative demands, positive rows, multiple zeros,
actual positive monotone vanishing tails and closed ties remain
part of those conclusions. No exhaustive novelty or unrestricted
amplitude classification is asserted.

## 追加锚（本行以下为增补区）

## 280. Finite patterns and the complete-score interface

**Proposition 280.1 (Entry ranks and actual finite words).**
For every finite collection of distinct primes and every prescribed Boolean
answer at each of them, there is an actual source (273.7) with precisely
those answers. The first absent prime of every actual source is finite.

**Proof.** Put $Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$.
Modulo any prime $p$, $Q$ is invertible and, for $n\ge1$,

$$
Q^n=\begin{pmatrix}F_{n+1}&F_n\\F_n&F_{n-1}\end{pmatrix}.
$$
Thus $Q^n$ is scalar exactly when $p\mid F_n$: the off-diagonal
entries vanish, and $F_{n+1}-F_{n-1}=F_n$. The inverse image of the
scalar subgroup under $n\mapsto Q^n$, $n\in\mathbb Z$, is a subgroup
$z(p)\mathbb Z$. Finiteness of $\operatorname{PGL}_2(\mathbb F_p)$
makes $z(p)>0$, and $F_1=F_2=1$ makes $z(p)\ge3$. Consequently

$$
p\mid F_n\quad\Longleftrightarrow\quad z(p)\mid n\qquad(n\ge1).
\tag{280.1}
$$
This is the entry-rank criterion also stated in
[Fibonacci Atomic Relation Generation, (363.13)](FIBONACCI_ATOMIC_RELATION_GENERATION.md).
The matrix argument supplies its needed prime-modulus case directly.

Let $M$ be the product of the finitely many queried primes. Choose a prime
$r>\max_p z(p)$, as large as necessary. Then no $z(p)$ divides $r$,
so $F_r$ is invertible modulo $M$. For each prescribed one require
$g\equiv-F_r^{-1}\pmod p$; for each prescribed zero require
$g\equiv0\pmod p$. The Chinese remainder theorem gives one residue
class modulo $M$. The interval
$[\lceil F_r/10\rceil,\lfloor F_r/5\rfloor]$ contains at least $M$
consecutive integers for all sufficiently large such $r$, since $F_r$
grows without bound. It therefore contains a representative of this
residue class. For this actual $(r,g)$, $1+F_rg$ is divisible by each
prescribed positive prime and congruent to one at each prescribed
negative prime. Both repeated and unqueried addresses have their actual
static answers. Finally $N(r,g)$ is a positive integer, hence has only
finitely many prime divisors. This proves finite first absence. $\square$

**Convention 280.2 (All rows and one allocation).**
Definitions 273.1–273.2 apply in every section below: all $2^L$ words,
all labels $0,\ldots,L$, all three independent zero-word events and the
positive event remain. In particular negative singleton demands are
retained. Write $w(Z)$ for the word with exactly the zero set $Z$.
A score is a nonnegative vector of independent $A,C,P,T$ coefficients,
not a probability law on sources. For any such score $V$ of zero cost,
and any one complete feasible allocation of any finite mass,

$$
F_{QV}(b,e)\le V G_N\lambda
 =\sum_D\lambda_D(Vz_D-W_V)\le0.
\tag{280.2}
$$
All coordinates in this pairing belong to the same $(b,e),\lambda$.
The definitions of $H_L,H_N,Q,\sigma_H$ are (273.5)–(273.6).
No monotonicity of $b$ is needed in (280.2).

The actual source, full disjoint-union Borel carrier, unchanged consumer
and original nonatomic targets are exactly those of 273.3. The selected
marked laws (273.8) remain distinct from those nonatomic targets. A
probability allocation is realized by one source-independent uniform seed
selecting its complete schedule and every counterfactual terminal output
before replies. It has zero advice and finite handoff. $N$ obtains its
whole preselected schedule; $O$ uses an increasing preselected schedule
and stops at its first queried zero or exhaustion. At most two actual
requests are allowed, including repeated and ignored requests. The
unchanged competitor classes allow arbitrary addresses and full-carrier
outputs. Theorems 109.1 and 110.2 supply, respectively, the normalized
stopped criterion $c\ge H$ and exact closed-cap class feasibility
transport. That transport need not preserve an arbitrary starting law or
coupling. Proposition 280.1 supplies the actual finite words used in its
source argument. Actual positive monotone vanishing tails always retain
the exact error (273.9), including $a_n=e$. Conic division uses (273.10),
with its changed profile; subunit mass can instead be padded at $R$.
These closed-cap assertions concern the selected marked targets on the
original acquisition interface. They give no approximation assertion for
the distinct unchanged nonatomic targets $\mu_x^{\rm orig}$.

**Lemma 280.3 (A necessary score on an arbitrary finite prefix).**
A zero-cost score supported on a finite prefix gives its necessary
inequality for an original positive monotone vanishing sequence even
when some scored addresses are inactive at the proposed positive cap.

**Proof.** This consumes the restriction and extension argument of
[Theorem 202.13](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VII.md).
Let $K_0$ contain the score support, and let $L_a$ be the actual active
length. By 110.2 obtain one full finite representative at that cap.
If $L_a\ge K_0$, restrict higher replies to zero and project labels above
$K_0$ to zero. A zero in the prefix keeps its target; the positive prefix
has a base target after this projection. TV contracts. For each table,
substitute the fixed high replies and contract constant observations.
The remaining function is a legal complete low-prefix table with at most
two informative coordinates. This algebraic restriction grants no free
actual high request. If $L_a<K_0$, ignore added inputs. At each added
first zero $n$ the law is the old positive law, so its exact error is
$\max\{1-p_+(0),a_n\}\le e$, since $a_n\le e$; the new positive row
is unchanged. This also covers $L_a=0$, multiple zeros, negative correct
demands and ties. Pair the score against this one full probability
configuration. For $e\ge1$, the weighted inequalities used below follow
directly from $a_j\le1$. The same conclusions for original $O$ rules
follow by counted same-seed completion to $N$. $\square$

## 281. Three realizations of one five-positive score

**Definition 281.1 (Seven-coordinate coefficient tables).**
In the tables below, unlisted coefficients and every $A$ coefficient are
zero. A word is written in coordinates $(1,2,3,4,5,6,7)$; $C$ at a word
rewards its actual first-zero label, and $P$ is its independent union row.
For $J_*=(j_1<\cdots<j_5)\subseteq\{3,\ldots,L\}$, embed these
coordinates as $(1,2,j_1,\ldots,j_5)$ and put every other bit equal to
one on the scored support. Numerical labels follow that embedding.
$T$ is at the full positive word. Denote the three scores by
$Y^{\rm f},Y^{\rm p},Y^{\rm n}$.

For $Y^{\rm f}$ divide the following integers by $30$. Each suffix row
in the first table supplies **both** $P_{01z}$ and $P_{10z}$.

| Suffix $z$ | Numerator |
| --- | ---: |
| $00010$ | 2 |
| $00100$ | 4 |
| $00101$ | 4 |
| $00110$ | 3 |
| $01000$ | 2 |
| $01001$ | 6 |
| $01010$ | 5 |
| $01100$ | 4 |
| $10000$ | 3 |
| $10001$ | 5 |
| $10010$ | 4 |
| $10100$ | 3 |
| $11000$ | 2 |

| Type | Word | Numerator |
| --- | --- | ---: |
| $P$ | $1100110$ | 2 |
| $P$ | $1110000$ | 2 |
| $P$ | $1111000$ | 2 |
| $P$ | $1111100$ | 2 |
| $P$ | $1111110$ | 2 |
| $C$ | $1100101$ | 10 |
| $C$ | $1100110$ | 16 |
| $C$ | $1101011$ | 4 |
| $C$ | $1110001$ | 18 |
| $C$ | $1110100$ | 12 |
| $C$ | $1111000$ | 30 |
| $C$ | $1111101$ | 30 |
| $C$ | $1111110$ | 30 |
| $T$ | $1111111$ | 22 |

For $Y^{\rm p}$ divide the following integers by $15$.

| Type | Word | Numerator |
| --- | --- | ---: |
| $C$ | $1101010$ | 10 |
| $C$ | $1101101$ | 5 |
| $C$ | $1110001$ | 1 |
| $C$ | $1110100$ | 14 |
| $C$ | $1111000$ | 4 |
| $C$ | $1111001$ | 11 |
| $C$ | $1111100$ | 14 |
| $C$ | $1111101$ | 1 |
| $C$ | $1111110$ | 15 |
| $P$ | $0100100$ | 4 |
| $P$ | $0100101$ | 3 |
| $P$ | $0100110$ | 1 |
| $P$ | $0101000$ | 2 |
| $P$ | $0101001$ | 5 |
| $P$ | $0110000$ | 4 |
| $P$ | $0110001$ | 2 |
| $P$ | $1000010$ | 2 |
| $P$ | $1000101$ | 1 |
| $P$ | $1000110$ | 2 |
| $P$ | $1001001$ | 1 |
| $P$ | $1001010$ | 5 |
| $P$ | $1001100$ | 4 |
| $P$ | $1010001$ | 3 |
| $P$ | $1010010$ | 3 |
| $P$ | $1010100$ | 3 |
| $P$ | $1011000$ | 2 |
| $P$ | $1100010$ | 1 |
| $P$ | $1110010$ | 1 |
| $P$ | $1111000$ | 1 |
| $P$ | $1111100$ | 1 |
| $T$ | $1111111$ | 12 |

For the 28 independent rows of $Y^{\rm n}$ divide by $60$.

| Type | Word | Numerator |
| --- | --- | ---: |
| $P$ | $0100100$ | 4 |
| $P$ | $0100110$ | 17 |
| $P$ | $0101000$ | 23 |
| $P$ | $0101100$ | 16 |
| $P$ | $0110000$ | 17 |
| $P$ | $0110010$ | 6 |
| $P$ | $0110100$ | 12 |
| $P$ | $0111001$ | 8 |
| $P$ | $1000101$ | 26 |
| $P$ | $1000110$ | 5 |
| $P$ | $1001000$ | 9 |
| $P$ | $1001010$ | 20 |
| $P$ | $1010000$ | 11 |
| $P$ | $1010001$ | 4 |
| $P$ | $1010010$ | 10 |
| $P$ | $1100010$ | 2 |
| $P$ | $1100100$ | 2 |
| $C$ | $1100110$ | 34 |
| $C$ | $1101101$ | 26 |
| $P$ | $1110001$ | 4 |
| $C$ | $1110100$ | 60 |
| $C$ | $1111000$ | 60 |
| $P$ | $1111001$ | 4 |
| $C$ | $1111100$ | 56 |
| $P$ | $1111100$ | 4 |
| $C$ | $1111101$ | 4 |
| $C$ | $1111110$ | 60 |
| $T$ | $1111111$ | 48 |

**Theorem 281.2 (Complete support and distinct column gaps).**
For each of these three scores, at every stated ordered embedding,

$$
\beta=1_{J_*},\quad K=46/5,\quad
W=B_N=B_O=21/5,\quad\Delta_N=\Delta_O=0.
\tag{281.1}
$$
Their minimum strictly positive complete-column deficits
$21/5-Yz_D$ are, respectively,

$$
\frac1{30},\qquad\frac1{15},\qquad\frac1{20}.
\tag{281.2}
$$
These are three realizations of one numerical core.

**Proof.** For each increasing core pair and cell $c$, define
$B_{ij}(c)=\sum_{w\in c}P_w+T[+\in c]$ and
$L_{ij}(c,r)=\sum_{w\in c,n(w)=r}(C_w+P_w)$ for a late label.
Early-label reward is its own subset of $P$ rows, hence no greater than
$B_{ij}(c)$; labels outside the embedded coordinates have zero reward.
The following certificates give every core pair. Vectors are in
$00,01,10,11$ order.

For $Y^{\rm f}$ these are $30(B-\max_{r=3}^7L_r)$; pair $(2,j)$
has the same vector as $(1,j)$.

| Pair | Late-label slack vector |
| --- | --- |
| $12 $ | $(0,47,47,0)$ |
| $13 $ | $(30,17,0,15)$ |
| $14 $ | $(28,19,0,15)$ |
| $15 $ | $(29,18,1,14)$ |
| $16 $ | $(33,14,7,8)$ |
| $17 $ | $(32,15,10,7)$ |
| $34 $ | $(0,30,0,0)$ |
| $35 $ | $(26,4,0,0)$ |
| $36 $ | $(30,0,0,0)$ |
| $37 $ | $(24,6,0,2)$ |
| $45 $ | $(10,2,0,2)$ |
| $46 $ | $(8,2,0,2)$ |
| $47 $ | $(24,0,0,4)$ |
| $56 $ | $(8,18,0,0)$ |
| $57 $ | $(8,4,2,0)$ |
| $67 $ | $(10,0,0,18)$ |

For $Y^{\rm p}$, the two vectors are $15B$ and $15(B-\max_{r=1}^7L_r)$, where early labels use their own union rows.

| Pair | Zero reward | Slack against all nonzero labels |
| --- | --- | --- |
| $12$ | $(0,21,26,16)$ | $(0,0,0,0)$ |
| $13$ | $(15,6,16,26)$ | $(0,0,0,10)$ |
| $14$ | $(14,7,16,26)$ | $(0,0,0,10)$ |
| $15$ | $(13,8,19,23)$ | $(0,0,3,7)$ |
| $16$ | $(20,1,16,26)$ | $(0,0,0,11)$ |
| $17$ | $(11,10,25,17)$ | $(0,0,4,6)$ |
| $23$ | $(15,11,16,21)$ | $(0,0,0,5)$ |
| $24$ | $(14,12,16,21)$ | $(0,0,0,5)$ |
| $25$ | $(16,10,16,21)$ | $(0,0,0,5)$ |
| $26$ | $(14,12,22,15)$ | $(0,0,2,0)$ |
| $27$ | $(21,5,15,22)$ | $(0,0,0,11)$ |
| $34$ | $(14,17,16,16)$ | $(6,2,0,0)$ |
| $35$ | $(16,15,16,16)$ | $(5,7,0,0)$ |
| $36$ | $(20,11,16,16)$ | $(6,0,0,1)$ |
| $37$ | $(21,10,15,17)$ | $(8,2,0,6)$ |
| $45$ | $(16,14,16,17)$ | $(8,0,0,1)$ |
| $46$ | $(20,10,16,17)$ | $(5,3,0,2)$ |
| $47$ | $(21,9,15,18)$ | $(6,4,0,7)$ |
| $56$ | $(20,12,16,15)$ | $(4,1,0,0)$ |
| $57$ | $(21,11,15,16)$ | $(9,0,0,11)$ |
| $67$ | $(21,15,15,12)$ | $(6,4,0,12)$ |

For $Y^{\rm n}$, the vectors are $60B$ and the largest reward among **all** nonzero labels. The final column is the minimum strictly positive cell loss in the pair, also in units $1/60$.

| Pair | Zero reward | Largest nonzero reward | Minimum positive loss |
| --- | --- | --- | ---: |
| $12$ | $(0,103,85,64)$ | $(0,103,85,64)$ | 4 |
| $13$ | $(60,43,64,85)$ | $(60,43,64,64)$ | 4 |
| $14$ | $(56,47,64,85)$ | $(56,47,64,64)$ | 8 |
| $15$ | $(54,49,64,85)$ | $(54,49,64,64)$ | 10 |
| $16$ | $(80,23,64,85)$ | $(80,23,64,60)$ | 14 |
| $17$ | $(95,8,63,86)$ | $(95,8,60,30)$ | 3 |
| $23$ | $(60,25,64,103)$ | $(60,25,64,64)$ | 4 |
| $24$ | $(56,29,64,103)$ | $(56,29,64,64)$ | 8 |
| $25$ | $(54,31,64,103)$ | $(54,31,64,64)$ | 10 |
| $26$ | $(50,35,94,73)$ | $(50,35,80,60)$ | 13 |
| $27$ | $(55,30,103,64)$ | $(55,30,95,26)$ | 8 |
| $34$ | $(56,68,64,64)$ | $(38,39,64,64)$ | 4 |
| $35$ | $(54,70,64,64)$ | $(29,62,64,64)$ | 4 |
| $36$ | $(80,44,64,64)$ | $(43,36,64,60)$ | 4 |
| $37$ | $(98,26,60,68)$ | $(60,26,60,8)$ | 25 |
| $45$ | $(54,66,64,68)$ | $(25,60,64,64)$ | 4 |
| $46$ | $(80,40,64,68)$ | $(64,36,64,60)$ | 4 |
| $47$ | $(86,34,72,60)$ | $(60,30,60,26)$ | 4 |
| $56$ | $(80,38,64,70)$ | $(64,30,64,60)$ | 4 |
| $57$ | $(98,20,60,74)$ | $(60,8,60,26)$ | 11 |
| $67$ | $(98,46,60,48)$ | $(72,30,60,0)$ | 16 |

Every entry is obtained by adding the displayed row numerators in its
specified cell. All slacks are nonnegative, so zero maximizes every
individual cell, including every earlier and unqueried label. Summing
cells gives support at most the constant-zero reward $21/5$.
Direct class summation gives each $C$ total one; the $(P,T)$ totals are
$(52/15,11/15)$ for $Y^{\rm f}$ and $(17/5,4/5)$ for each of the
other two. Thus $K=5+21/5$ and $R$ has the same reward as zero.
Both are legal in $O\subset N$ and give (281.1).

A singleton or constant partition coarsens a core pair. Repetition or
ignored coordinates give coarser information and reversal permutes cells.
An inactive queried coordinate is constantly one on the scored support.
Adding the separate label inequalities over merged cells preserves them,
including the $O$ merge of $00,01$. This proves the assertion for the
entire catalog and all embeddings, without restricting original words.

All positive losses for the first two scores are integer multiples of
$1/30$ and $1/15$. For the third, the final certificate column makes
every positive cell loss at least $3/60$. Coarsening adds nonnegative
losses. Pair $(1,5)$, with label $5$ only in cell $10$ and zero elsewhere,
attains loss $1/30$ for $Y^{\rm f}$. Pair $(1,2)$, with label $7$ only
in $11$, attains $1/15$ for $Y^{\rm p}$. For $Y^{\rm n}$ the table
$N(1,7;0,0,4,0)=O(1,7;0,4,0)$ attains $3/60$.
Their embedded versions give all three exact column minima. $\square$

## 282. Weighted necessity, exact five-positive threshold and attainment

**Theorem 282.1 (Weighted five-address necessity and a full quotient cone).**
Fix any five ordered late addresses $J_*$ and weights $\gamma_j\ge0$.
Put $G=\sum_{j\in J_*}\gamma_j$ and $\mu=\max_j\gamma_j$.
There is a nonnegative full score with

$$
\beta=\gamma,\quad K_0=G+21\mu/5,\quad
W=B_N=B_O=21\mu/5.
\tag{282.1}
$$
Every complete feasible $N$ allocation, of any mass and at any real
profile, therefore satisfies

$$
\sum_{j\in J_*}\gamma_jb_j\le(G+21\mu/5)e.
\tag{282.2}
$$
Every full input $y\ge0$ with this $\beta$, zero elsewhere, and actual
$K\ge K_0$ has one nonnegative full score $V$ with $QV=Qy$ and
$\Delta_N(V)=0$; its residual is zero and $\theta=0$ suffices.
For every original positive monotone vanishing $a$, an original $N_2$
cap attainer at $e>0$ necessarily satisfies

$$
\sum_{j\in J_*}\gamma_ja_j\le(G+21\mu/5)e,
\tag{282.3}
$$
including inactive selected addresses. The same necessity holds for $O_2$.

**Proof.** In $Y^{\rm f}$ scale every $P,T$ coefficient by $\mu$,
and the $C$ coefficients of class $j$ by $\gamma_j$. Every late-label
cell reward is at most $\mu$ times its former reward, whereas zero
receives exactly $\mu$ times its former reward. The complete domination
proof of 281.2 persists without division by $\mu$. Class sums give
(282.1), including the zero score when $\mu=0$. Equation (280.2) gives
(282.2). Add positive-row mass $K-K_0$ to obtain the exact input quotient;
that row has nonpositive excess at every column and zero at $R$.
This proves the unrestricted quotient assertion, regardless of the
input's cancellations or coefficient placements. Lemma 280.3 proves
(282.3) for the original entire sequence and every positive cap. $\square$

**Theorem 282.2 (An actual 16-table seven-active family).**
Let

$$
0<\tau\le1/29,\qquad e_*=5\tau,\qquad
(a_3,a_4,a_5,a_6,a_7)=(13,10,9,8,6)\tau,
$$
$$
\max\{1-21\tau,13\tau\}\le a_2\le a_1\le1-16\tau.
\tag{282.4}
$$
Attach any positive nonincreasing vanishing tail with $a_8\le5\tau$.
Both original hard-two infima are attained and equal to $5\tau$;
a positive closed cap is feasible in either class exactly when it is
at least $5\tau$. The active length at $e_*$ is seven.

**Proof.** Give $R=O(1,2;1,2,0)$ mass $1-21\tau$.
In the following table give each displayed $O(i,j;u,s,t)$ the mass
in the last column times $\tau$.

| $i$ | $j$ | $u$ | $s$ | $t$ | Integer mass |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 0 | 0 | 3 | 2 |
| 1 | 2 | 0 | 0 | 4 | 1 |
| 1 | 2 | 0 | 0 | 5 | 1 |
| 1 | 3 | 0 | 3 | 0 | 3 |
| 1 | 4 | 0 | 4 | 0 | 1 |
| 2 | 3 | 0 | 3 | 0 | 3 |
| 2 | 4 | 0 | 4 | 0 | 1 |
| 3 | 4 | 0 | 4 | 0 | 2 |
| 3 | 4 | 0 | 0 | 5 | 1 |
| 3 | 5 | 0 | 5 | 0 | 1 |
| 3 | 6 | 0 | 6 | 0 | 1 |
| 4 | 5 | 0 | 5 | 0 | 1 |
| 4 | 6 | 0 | 6 | 0 | 1 |
| 5 | 6 | 0 | 6 | 0 | 1 |
| 6 | 7 | 0 | 7 | 0 | 1 |

The integer masses sum to 21, so the whole law is nonnegative and has
mass one. One source-independent uniform seed selects the complete
increasing schedule and all its outputs. Execute that schedule with
first-queried-zero stopping, emitting the actual original mark indicated
by the output label. Its same-seed $N$ completion acquires both selected
replies, counting the ignored second request. There is finite handoff
on every source and seed, with no extra observation or advice.

Here is the all-word calculation. Put
$(s,t,u,v,z)=(w_3,w_4,w_5,w_6,w_7)$ and

$$
L_0=2s(1-t)+(s+t)(2-u-v)+u(1-v)+v(1-z)+st.
$$
On an early first-zero fibre the late tables contribute $\tau L_0$
wrong-label mass. If the other head is one, add
$\tau(3(1-s)+(1-t))$; otherwise add zero.
The maximum over $u,v,z$ of
$(s+t)(2-u-v)+u(1-v)+v(1-z)$ is respectively $1,2,2,4$
for $(s,t)=00,01,10,11$. Including the other terms makes every
wrong mass at most $5\tau$. Every early correct mass is
$c_0=1-21\tau$. Since $c_0\le a_i\le c_0+5\tau$ for $i=1,2$,
its correct deficit is at most $5\tau$, its union deficit is the
wrong mass, and its base deficit is $c_0+\text{wrong}-a_i\le5\tau$.
Thus each of the three independent rows holds.

On every first-zero-$n$ fibre for $n=3,\ldots,7$, the correct masses
are $(8,5,4,3,1)\tau$, independent of all later bits. The wrong masses,
in units $\tau$, are respectively

$$
\begin{array}{c|l}
3&2+2(1-t)+t(2-u-v)+u(1-v)+v(1-z)\\
4&3+(1-u)+(1-v)+u(1-v)+v(1-z)\\
5&3+2(1-v)+v(1-z)\\
6&5\\7&5.
\end{array}
\tag{282.5}
$$
At $t=0$ the first expression is
$4+u(1-v)+v(1-z)\le5$; at $t=1$ it is $4-uv-vz\le4$.
For the second,
the part after three is at most two, by its four $(u,v)$ cases;
the third is at most five by $v=0,1$. Hence all wrong masses are at
most $5\tau$. Since $a_n=\text{correct}+5\tau$, the correct deficit
is exactly $5\tau$, the base deficit is $\text{wrong}-5\tau\le0$,
and the independent union deficit is at most $5\tau$.
This proves every multiple-zero suffix, with one unchanged law.

At the positive word the three head exhaustion tables contribute
$4\tau$ nonbase mass and $O(3,4;0,0,5)$ contributes $\tau$.
Thus $p_+(0)=1-5\tau$. At every actual $n>7$ the error is exactly
$\max\{5\tau,a_n\}=5\tau$, including the closed tail tie.
All actual sources are covered by Proposition 280.1 and the finite
execution. Conversely (282.3) with five unit weights gives
$46\tau\le(46/5)e$ for every original $N$ attainer at any proposed
cap, so $e\ge5\tau$. This proves both attained optima and all closed
head and $\tau=1/29$ endpoints. The value $\tau=0$ is only a
degenerate finite law, outside this positive-sequence family.
For $1/34\le\tau\le1/29$ the choice $a_1=a_2=13\tau$ satisfies
(282.4), $b_2=b_3$ and $E_b=6\tau\le1-13\tau$.
The same mass-one law witnesses this subfamily in $H_N$. $\square$

**Theorem 282.3 (Exact named unrestricted fibre threshold).**
For every $L\ge7$, consider all full nonnegative scores whose quotient
has $\beta_3=\cdots=\beta_7=1$ and every other $\beta_i=0$.
For every such score with its actual total $K$,

$$
\Delta_O(y)\ge\frac{46-5K}{34}.
\tag{282.6}
$$
This unrestricted fibre contains a zero-cost score in either class
exactly when $K\ge46/5$.

**Proof.** In 282.2 take $\tau=1/34$ and heads $13/34$.
Pair an arbitrary full score in the stated fibre against that one
mass-one stopped law. It dominates all demands at cap $5/34$ and
late sum $46/34$, so its excess is at least $(46-5K)/34$.
For $L>7$ extend this auxiliary finite target by $b_n=0$, $n>7$.
The unchanged positive-word law has error $5/34$ against the base
target, so every extended finite row also holds. Additional score
coordinates and unrestricted $A,C,P,T$ cancellations therefore obey
the same lower bound. This zero extension is solely a finite algebraic
lower-score test; the original tails in 282.2 are positive.
A zero-cost $O$ or $N$ score must have $K\ge46/5$.
Theorem 281.2 attains equality, and positive-row padding attains every
larger $K$. No optimality on a different weighted or gapped fibre is
asserted. $\square$

## 283. One signed payer and the natural score's own reserve

**Theorem 283.1 (An unrestricted interleaved input class).**
Let $3<r<k<\ell<z\le L$, $s\ge0$, $0\le h\le79s/21$.
For every full nonnegative input $y$ with

$$
\beta_1=-s,\quad\beta_3=s,\quad\beta_r=-s,\quad
\beta_k=s,\quad\beta_\ell=h,\quad\beta_z=s,
\qquad \beta_i=0\text{ otherwise},
\tag{283.1}
$$
there is one full $V\ge0$ with

$$
\Delta_N(V)=0,\quad\sigma_H(Qy-QV)=s,\quad\Delta_O(y)\ge s.
\tag{283.2}
$$
In particular every unit-$O$ input in this class has the single
certificate $(V,\theta=s)$, including $s=0$ and $\theta=1$.
For any such unit-$O$ input and the same complete feasible $\lambda$
at the same $(b,e)\in H_N$
with mass $M\ge1$, it satisfies $F_y(b,e)\le s\le1\le M$.

**Proof.** Let $J_*=(3,r,k,\ell,z)$, $t=(s+h)/5$ and
$V=tY^{\rm p}_{J_*}$; the natural realization gives the same payer.
Every input in (283.1) necessarily has $K\ge\sum_i|\beta_i|=5s+h$,
by classwise $|C_i-A_i|\le C_i+A_i$. Constant zero has excess
$-\beta_1-\beta_2=s$ against this input's own anchor, proving
$\Delta_O(y)\ge s$ without a support restriction.
For decreasing $x=(b_3,b_r,b_k,b_\ell,b_z)$ the actual residual is

$$
F_{Qy-QV}=s+s(b_3-b_1)+a\cdot x-(K-46t/5)e,
\quad a=(-t,-s-t,s-t,h-t,s-t).
\tag{283.3}
$$
The successive sums of $a$ are $-t,-s-2t,-3t,h-4t,0$.
They are nonpositive since $h\le79s/21<4s$ unless $s=h=0$.
Abel summation gives $a\cdot x\le0$, and

$$
K-46t/5\ge\frac{79s-21h}{25}\ge0.
$$
Thus (283.3) is at most $s$ on the entire $H_L$. The auxiliary hull
origin attains $s$, so the support is exactly $s$, with every spare
$K$ and every weak endpoint included. It is a support test, not an
original zero-cap positive-tail attainer. By 281.2 the single $V$ has
zero $N$ cost. Unit-$O$ implies $s\le1$, proving the one-budget
certificate, allowing nonzero zero-cost $V$ when $\theta=1$.
Finally (280.2) for this same $V,\lambda$ and (283.3) give
$F_y\le s$. No marginal or component optimizer is substituted. $\square$

**Theorem 283.2 (Reserve and stability for the 28-row natural score).**
Use exactly $Y=Y^{\rm n}_{J_*}$ from Definition 281.1. For every one
full feasible $\lambda$, set $\delta_D=21/5-Yz_D$ and let
$\tau_Y=\sum_{D:\delta_D>0}\lambda_D$. Then

$$
\frac{46}{5}e-\sum_{j\in J_*}b_j
 =\sum_D\lambda_D\delta_D+Y(G_N\lambda-h),\qquad
\tau_Y\le20\left(\frac{46}{5}e-\sum_{j\in J_*}b_j\right).
\tag{283.4}
$$
The constant 20 is sharp for the column-deficit estimate
$[\delta_D>0]\le20\delta_D$. No sharpness among cap-feasible
reserve ratios is asserted.

**Proof.** Expand $YG_N\lambda=-\sum\lambda_D\delta_D$ and
$Yh=\sum_{J_*}b_j-(46/5)e$, keeping the same allocation.
The remaining term is the nonnegative full-row slack. By 281.2 every
positive $\delta_D$ is at least $1/20$, giving (283.4).
$N(1,j_5;0,0,j_2,0)=O(1,j_5;0,j_2,0)$ has exactly that deficit,
so no smaller column constant works. Reserve zero forces supported
columns to be optimal and every positively scored row to be tight;
it does not force an unscored row tight. The fidelity and proportional
scores have their own different gaps, $1/30$ and $1/15$.
Their optimal faces and constants are not substituted into (283.4).
$\square$

## 284. Asymmetric ordered blocks at every $6k-1$ late labels

**Definition 284.1 (One product coefficient measure).**
Fix $k\ge2$ and $6k-1$ ordered actual late addresses, partitioned into
consecutive blocks $A,B,\{z\}$ of sizes $4k-1,2k-1,1$.
All addresses of $A$ precede all of $B$, and $z$ is last. Choose a
uniform $2k$-subset of $A$ and, independently, a uniform $k$-subset of
$B$, and always include $z$ in the zero set. Multiply this one joint
probability measure by

$$
c=4-1/k,\qquad b=\frac{4k-1}{2k-1}.
\tag{284.1}
$$
Call the resulting zero-set measure $\nu$. It is a coefficient measure,
not a prior on actual sources.

**Theorem 284.2 (Full-catalog law and its necessary inequality).**
Let $s\ge0$, $0\le\gamma_j\le s$ on the selected late addresses,
and $G=\sum_j\gamma_j$. Put

$$
P_{w(\{1\}\cup Z)}=P_{w(\{2\}\cup Z)}=s\nu(Z)/2,
\qquad T=s,
$$
$$
C_{w(\{\ell:\ell\text{ selected},\ \ell\ge j\})}=\gamma_j
\quad\text{for each selected }j.
\tag{284.2}
$$
All other coefficients are zero and coincident contributions add.
This full score has

$$
\beta=\gamma,\quad K=G+(c+1)s,\quad
W=B_N=B_O=(c+1)s.
\tag{284.3}
$$
Every complete feasible $N$ allocation, with any finite mass and any
real profile, consequently satisfies

$$
\sum_j\gamma_jb_j\le\bigl(G+(5-1/k)s\bigr)e.
\tag{284.4}
$$
Every unrestricted full input with these $\beta$ and actual
$K\ge G+(5-1/k)s$ has a full nonnegative exact-$Q$ zero-cost
representative and $\theta=0$. For an entire original sequence the
same necessary inequality holds, including selected inactive addresses.
No least-stock or sufficient-feasibility assertion is made.

**Proof.** The unary zero masses on $A,B,\{z\}$ are $2,b,c$.
For two ordered selected addresses the full four reply masses are

$$
\begin{array}{c|cccc}
\text{type}&00&01&10&11\\\hline
AA&1&1&1&c-3\\
BB&b/2&b/2&b/2&c-3b/2\\
AB&2k/(2k-1)&2-2k/(2k-1)&1&c-3\\
Az&2&0&c-2&0\\
Bz&b&0&c-b&0.
\end{array}
\tag{284.5}
$$
For example the $AA$ double-zero probability is
$2k(2k-1)/((4k-1)(4k-2))$, which multiplied by $c$ is one;
subtract from unary two for its two mixed cells. The $BB$ double-zero
mass is $c\,k(k-1)/((2k-1)(2k-2))=b/2$.
Independence between the blocks gives $AB$ double-zero mass
$c(2k/(4k-1))(k/(2k-1))=2k/(2k-1)$; subtracting it from
unaries two and $b$ gives $01,10$. The final vertex is always zero,
giving the last two lines. These computations also give all $11$ cells
by subtraction from $c$, with no separately chosen pair marginals.
Every entry is nonnegative. The required $00,10$ entries are at least
one: for the last type,

$$
c-b-1=\frac{2k^2-4k+1}{k(2k-1)}\ge0\quad(k\ge2),
$$
and $b/2\ge1$, $c-2\ge1$; the other cases are immediate.
This includes $k=2$ and its zero $BB$ positive cell.

A threshold correct word in (284.2), observed at selected $i<j$,
can occur only in $00,10,11$, never $01$. Its own correct reward is
at most $s$. Zero receives $s\nu_{ij}(00),s\nu_{ij}(10)$ in the
first two of these cells and at least $T=s$ in $11$.
Thus zero dominates each late label separately, with its entire
$C$ mass in its one specified cell. On a head/late pair, correct
labels at or before the late address occur in $10$, where zero has
half its unary zero mass, at least $s$. Later correct labels are in
$11$, paid by $T=s$. On the head pair all correct labels lie in
$11$, also paid by $T$. Every early numerical label receives only
its own union rows, a subset of zero's reward; other labels receive
zero. Hence all labels in all distinct pairs are dominated.
Inactive coordinates are constantly one on the scored support, and
shorter, repeated or ignored schedules coarsen these partitions.
Summing the separate label bounds proves the same conclusion for all
of them and for $O$ stopping. The row sums give (284.3), and both
constant zero and $R$ attain it. Equation (280.2) proves (284.4) on
one complete allocation. Positive-row padding gives the full quotient
cone. Lemma 280.3 gives the original necessary inequality on arbitrary
selected addresses. No independent component stock was added. $\square$

**Corollary 284.3 (All-active specialization and a positive-tail exclusion).**
For $L=6k+1$ and $\gamma_j=s=1$ at all late addresses,

$$
E_b\le(2-1/k)e.
\tag{284.6}
$$
At $k=2$, the entire sequence

$$
a_1=\cdots=a_{13}=17/240,\qquad e=1/20,
\qquad a_{13+r}=e/r\quad(r\ge1)
\tag{284.7}
$$
has no original $N_2$ or $O_2$ attainer at this closed cap.

**Proof.** Subtract $(L+1)e$ in (284.4) to obtain (284.6).
For (284.7), $E_b=19/240$, whereas $(2-1/2)e=18/240$.
The profile is positive, nonincreasing and vanishing, with the actual
closed tail tie $a_{14}=e$ and active length thirteen. It lies in
$H_{13}$ but outside $H_N$, by 110.2 and (284.6). Its violation
$1/240$ is an infeasibility exclusion, not an $N/O$ separator: there
is no full feasible $N$ witness at this point. $\square$

## 285. A weighted-slice identity and an explicit all-length score

**Theorem 285.1 (Weighted slices and the adjacent-path equality cone).**
Fix $m\ge4$, $k=\lceil m/2\rceil$, $p=k/m$, and

$$
t_1=0,\qquad t_{j+1}=\frac{k t_j+1}{m-k-1}.
\tag{285.1}
$$
The denominator is positive. For $|Z|=k$ and $|T|=k+1$, put

$$
u_Z^*=\frac{1+k\sum_{j\notin Z}t_j}{\binom mk},\qquad
v_T^*=\frac{k\sum_{j\in T}t_j}{\binom mk},\qquad
U=\sum_{|Z|=k}u_Z^*=1+\frac{k(m-k)}m\sum_jt_j.
\tag{285.2}
$$
Then $\sum v_T^*=U-1$.
For every nonnegative unary/forward-edge function

$$
f(Z)=\sum_ja_j[j\in Z]+\sum_{i<j}d_{ij}[i\notin Z,j\in Z],
\qquad a_j,d_{ij}\ge0,
\tag{285.3}
$$
define
$\mathcal L(f)=\sum u_Z^* f(Z)-\sum v_T^* f(T)-p f([m])$.
Its exact value is

$$
\mathcal L(f)=-\frac{k(m-k)}m\sum_jt_ja_j
-\frac{k(m-k)}{m(m-1)}
 \sum_{i<j}\bigl((m-k-1)t_j-k t_i-1\bigr)d_{ij}\le0.
\tag{285.4}
$$
Equality holds exactly when $a_j=0$ for $j>1$ and $d_{ij}=0$
for $j>i+1$. Thus the equality cone consists of the first unary
and adjacent directed-path edges, with arbitrary nonnegative weights.
If also $f(Z)\le e$ on every subset, then

$$
\sum_{|Z|=k}u_Z^*(e-f(Z))\ge(1-p)e,
\quad
\frac1{\binom mk}\sum_{|Z|=k}(e-f(Z))
 \ge\frac{(1-p)e}{1+k\sum_{j=k+1}^m t_j}.
\tag{285.5}
$$

**Proof.** For $j\notin Z$,

$$
f(Z\cup\{j\})-f(Z)=a_j+\sum_{i<j,i\notin Z}d_{ij}
                         -\sum_{\ell>j,\ell\in Z}d_{j\ell}.
$$
Uniform $k$-set averaging of the sum of these increments weighted by
$t_j$ has unary coefficient $(m-k)t_j/m$ and edge coefficient
$(m-k)((m-k-1)t_j-k t_i)/(m(m-1))$.
The unweighted average of $f$ has unary coefficient $k/m$ and edge
coefficient $k(m-k)/(m(m-1))$. Subtract $p f([m])$ and $k$ times
the increment average. Grouping each $(k+1)$-set gives its coefficient
$v_T^*$, proving (285.4) and the totals in (285.2).
The sequence $t_j$ increases strictly, with $t_j>0$ exactly for $j>1$.
By (285.1), $(m-k-1)t_{i+1}-k t_i=1$; for $j>i+1$ the
left side is strictly larger. This gives the exact equality condition
using nonnegative primitive coefficients, not merely nonnegative
function values. Finally write $f=e-(e-f)$ in $\mathcal L(f)\le0$.
Its coefficient total is $1-p$, and every other deficit is nonnegative,
giving the first part of (285.5). Since $t$ increases,
$u_Z^*\le(1+k\sum_{j=k+1}^m t_j)/\binom mk$; apply this bound
to the nonnegative deficits for the second part. It is an average
bound, not a claim that every individual deficit has that size. $\square$

**Definition 285.2 (Explicit nonnegative coefficients).**
Let $L=m+2$, $J=\{3,\ldots,L\}$, $c=c_m$ and
$a=(c-3)/2>0$. Use the balanced measure $\nu$ of Definition 274.1.
Identify its ordered late vertices with $1,\ldots,m$ in (285.1).
Put $\ell=c$ for odd $m$, $\ell=2$ for even $m$, and

$$
\zeta=\frac{1+k\sum_{j=k+1}^m t_j}{\ell},\quad
\Lambda=\max\{mU/a,\zeta\},\quad
\varepsilon_C=\frac{1-p}{\Lambda}>0.
\tag{285.6}
$$
Start with the sole-zero score

$$
C_{v^i}(Y)=1\ (i\in J),\qquad
P_{01Z}(Y)=P_{10Z}(Y)=\nu(Z)/2,\qquad T(Y)=1.
$$
Let $\mathcal B$ be the signed union-row vector with half of $u_Z^*$
on each early lift on the $k$-layer, half of $-v_Z^*$ on each early
lift on the $(k+1)$-layer, and $-p/2$ on each early lift of the
all-zero suffix. Let $\mathbf C_w$ denote a unit correct-row vector,
let $u^i=1^{i-1}0^{L-i+1}$, and put

$$
\mathcal D=\sum_{i=3}^{L-1}(\mathbf C_{v^i}-\mathbf C_{u^i}),
\qquad V_m=Y-\mathcal B/\Lambda-(U/\Lambda)\mathcal D.
\tag{285.7}
$$
All coincident row contributions are added. These formulas specify
every coefficient without choosing an optimizing allocation.

**Theorem 285.3 (All-column zero cost of the explicit score).**
For every $m\ge4$, $V_m$ is nonnegative and

$$
QV_m=(1_J;K_C),\quad K_C=m+c+1-\varepsilon_C,\quad
W_{V_m}=B_N(V_m)=B_O(V_m)=c+1-\varepsilon_C.
\tag{285.8}
$$
Every one complete feasible $N$ allocation of arbitrary finite mass,
for any real $b$ and $e\ge0$, satisfies

$$
\delta_b:=(c-2)e-E_b\ge\varepsilon_C e,
\qquad\sum_{j\in J}b_j\le K_Ce.
\tag{285.9}
$$
Every full input with $Qy=(t1_J;K)$, $t\ge0$, $K\ge tK_C$,
has the single exact-$Q$ zero-cost representative
$tV_m+(K-tK_C)T_+$ and $\theta=0$.

**Proof.** The only subtracted union coefficients are on the $k$-layer,
where $u_Z^*/\nu(Z)\le\zeta\le\Lambda$; the changes on the next
layer and full suffix are positive. The sole-zero correct coefficients
become $1-U/\Lambda\ge0$ except at the last late address, where
the coefficient stays one. The removed mass is added at $u^i$ in the
same first-zero class. $T$ stays one. Thus $V_m\ge0$.
The vector $\mathcal D$ preserves both $\beta$ and $K$;
$\mathcal B$ has $\beta=0$ and total coefficient $1-p$.
Each of its union rows has anchor value one. This proves the claimed
quotient and anchor.

Here is the full column argument. For a table $D$, set
$H_D=c+1-Yz_D$. Use $g_D,x_D,\eta_D$ of 275.1 and 278.2,
with $g_D=\sum_i g_i(D)$ as defined explicitly in 286.1 below.
Partitioning early labels, late labels and zero gives

$$
H_D=g_D+x_D+\eta_D\ge0.
\tag{285.10}
$$
For clarity the nonnegative $g_D$ contributions are: no late query,
$g_D=a_D$; late singleton at $j$ with outputs $u,v$,
$2[u\in J]-[u=j]+(c-2)[v\in J]+[v=j]$; mixed pair $(h,j;u,v,s,t)$,

$$
[u\in J]+\tfrac{c-2}2[v\in J]+[s\in J]-[s=j]
       +\tfrac{c-2}2[t\in J]+[t=j];
$$
and late pair $(i,j;u,v,s,t)$,

$$
[u\in J]+[v\in J]-[v=i]+[s\in J]-[s=j]
       +(c-3)[t\in J]+[t\in\{i,j\}].
$$
The opposite-head coefficients in $x_D$ are $1/2$ in the first three
late-pair cells and $(c-3)/2$ in the last; mixed-pair coefficients
are one or $(c-2)/2$ and no-late early-fibre coefficients are $c/2$.
Together with $\eta_D$ these grouped expressions show that $H_D=0$
or $H_D\ge a$. Their exact zero face is

| Schedule | Zero-$H$ outputs |
| --- | --- |
| empty | $0$ |
| early singleton $h$ | zero output in $\{0,h\}$, positive output $0$ |
| late singleton | both outputs $0$ |
| $(1,2)$ | $00$ arbitrary; $01\in\{0,1\}$; $10\in\{0,2\}$; $11\in\{0\}\cup J$ |
| $(1,j)$ | $00,01\in\{0,1\}$; $10\in\{0,2,j\}$; $11=0$ |
| $(2,j)$ | $00,01\in\{0,2\}$; $10\in\{0,1,j\}$; $11=0$ |
| late $(i,j)$ | $00=11=0$; $01\in\{0,i\}$; $10\in\{0,j\}$ |

In particular the head-pair $00$ cell is empty on the score support
and has unrestricted output. The list follows by zeroing each grouped
nonnegative contribution, retaining every otherwise legal label.

Set $d_D=\mathcal D(z_D-\mathbf r)$.
On the zero face $d_D=1$ precisely at a late pair whose $01$ output
is its first address, and otherwise $d_D=0$: at that address $v^i$
uses $01$ whereas $u^i$ uses $00$; in all other cases their correct
indicators agree. Without a zero-face assumption $d_D\ge-(m-1)$.
For $h=1,2$, define $F_h(Z)=1-[D(\text{early}_h,Z)\in\{0,h\}]$,
where $\text{early}_1=01$, $\text{early}_2=10$, and put
$L_D=(\mathcal L(F_1)+\mathcal L(F_2))/2$.
Always $L_D\le U$, since $F_h$ takes values zero or one.
If $H_D=d_D=0$, the face list makes each $F_h$ a nonnegative
ordered cut (285.3): a mixed $10=j$ contributes its unary, and a
late $10=j$ contributes its forward edge. Hence $L_D\le0$ by
285.1. If $H_D=0,d_D=1$, use $L_D\le U$.
If $H_D>0$, then
$U d_D+(mU/a)H_D\ge-U(m-1)+mU=U\ge L_D$.
All columns therefore obey

$$
L_D\le U d_D+\Lambda H_D.
$$
The signed union vector satisfies
$\mathcal B(z_D-\mathbf r)=-L_D$, because its total coefficient
is $1-p$. Consequently

$$
V_m(z_D-\mathbf r)=-H_D+L_D/\Lambda-Ud_D/\Lambda\le0.
$$
$R$ gives equality, proving (285.8) on the complete catalog.
Equation (280.2) proves (285.9); positive-row padding proves the last
assertion, with all input cancellations and placements unrestricted.
No suballocation feasibility or separate optimum enters this proof.
$\square$

**Proposition 285.4 (Size and exact constants).**
The constants in (285.6) satisfy $\varepsilon_C=\Theta(m^{-3})$,
and

$$
\varepsilon_C(4)=1/576,\qquad
\varepsilon_C(5)=1/5295,\qquad
\varepsilon_C(7)=3/20356.
\tag{285.11}
$$
They are not asserted sharp.

**Proof.** Solving (285.1) gives
$t_j=((k/(m-k-1))^{j-1}-1)/(2k-m+1)$.
For $m=2q$ the largest value is $(q/(q-1))^{2q-1}-1\le7$;
for $m=2q-1\ge5$ it is
$((q/(q-2))^{2q-2}-1)/2\le40$.
To check these bounds, $(2x+1)\log(1+1/x)$ decreases for $x>0$:
its derivative is nonpositive by
$\int_x^{x+1}du/u\le(1/x+1/(x+1))/2$.
Use $x=q-1$ and $x=(q-2)/2$, respectively, and the smallest
permitted $q$. Also $t_j\ge(j-1)/m$, so $\sum_jt_j=\Theta(m)$.
Thus $U=\Theta(m^2)$, $\zeta=O(m^2)$,
$\Lambda=\Theta(m^3)$ and $1-p$ stays bounded away from zero.
Substitution gives (285.11). At $m=5$ explicitly
$t=(0,1,4,13,40)$, $U=353/5$, $\zeta=48$, $\Lambda=2118$,
and $K_C=16473/1765$. $\square$

## 286. Label-owned inequalities on every column and one allocation

**Definition 286.1 (A label's own charge).**
Let $L\ge4$, $J=\{3,\ldots,L\}$ and use the same balanced $\nu$
and $c=c_m$ as in 274.1. For every late label $i$ and every complete
$N$ table $D$, define

$$
\begin{aligned}
a_i(D)&=\tfrac12\int([D(01Z)=i]+[D(10Z)=i])\,d\nu,\\
g_i(D)&=a_i(D)-[D(v^i)=i]+[D(+)=i],\\
\ell_i(D)&=[D(v^i)=i]-[D(u^i)=i],\\
p_i(D)&=[D\text{ is a late pair }(i,j),\ j>i,
                  \text{ with }01\text{ output }i].
\end{aligned}
\tag{286.1}
$$
Here $u^i=1^{i-1}0^{L-i+1}$ and $v^i$ has its sole zero at $i$.
For one full feasible allocation put

$$
\begin{gathered}
G_i=\sum_D\lambda_Dg_i(D),\quad
\Pi_i=\sum_D\lambda_Dp_i(D),\\
s_i=\mu_{v^i}(i)-(b_i-e),\qquad
 t_i=\mu_{u^i}(i)-(b_i-e).
\end{gathered}
\tag{286.2}
$$
The symbol $t_i$ here is a correct-row slack, unrelated to (285.1).

**Theorem 286.2 (All-column ownership and its same-allocation form).**
For every $L\ge4$, every legal table, and each $i\in J$,

$$
g_i(D)\ge0,\qquad p_i(D)\le\ell_i(D)+g_i(D).
\tag{286.3}
$$
Consequently every one full feasible $\lambda$, of any finite mass,
satisfies

$$
\Pi_i+t_i\le s_i+G_i,\qquad
\sum_iw_i(\Pi_i+t_i)\le\sum_iw_i(s_i+G_i)
\quad(w_i\ge0).
\tag{286.4}
$$
All displayed slacks and $G_i,\Pi_i$ are nonnegative. For $L\ge6$,
with the common reserve of 275.3,

$$
\sum_i\Pi_i\le\sum_i s_i+G\le\delta_b,
\qquad G=\sum_iG_i.
\tag{286.5}
$$

**Proof.** The balanced moments are mass $c$, unary zero mass two,
and pair masses $(1,1,1,c-3)$, by 274.1. No late query makes
$D(v^i)=D(u^i)=D(+)$, so $\ell_i=0$ and $g_i=a_i\ge0$.
This includes every early-only, empty and early singleton table.
For a late singleton $j$, with outputs $u,v$ on replies zero, one,

$$
a_i=2[u=i]+(c-2)[v=i].
$$
If $i=j$, $g_i=[u=i]+(c-1)[v=i]$ and $\ell_i=0$.
If $i<j$, the trace in $g_i$ cancels and
$\ell_i=[v=i]-[u=i]$, so
$\ell_i+g_i=[u=i]+(c-1)[v=i]\ge0$.
If $i>j$, both comparison differences vanish. In all cases $p_i=0$.
For a mixed pair $(h,j;u,v,s,t)$, $h\in\{1,2\}$, put
$A=(c-2)/2$; then

$$
a_i=[u=i]+A[v=i]+[s=i]+A[t=i].
$$
At $i=j$, $g_i=[u=i]+A[v=i]+(A+1)[t=i]$ and $\ell_i=0$.
At $i<j$, the trace cancels and $\ell_i=[t=i]-[s=i]$,
giving the same nonnegative expression for $\ell_i+g_i$.
At $i>j$ the comparison differences vanish. Again $p_i=0$.

For a late pair $(a,b;u,v,s,t)$, $a<b$,
$a_i=[u=i]+[v=i]+[s=i]+(c-3)[t=i]$.
Only $i=a,b$ have nonzero trace, respectively
$[v=i]-[t=i]$ and $[s=i]-[t=i]$.
Subtracting them gives nonnegative grouped terms for every $g_i$.
In the five relative positions the sum with $\ell_i$ is

$$
\begin{array}{c|l}
i<a &[v=i]+[s=i]+(c-2)[t=i]\\
i=a &[v=i]+[s=i]+(c-2)[t=i]\\
a<i<b &[u=i]+[v=i]+(c-2)[t=i]\\
i=b &[u=i]+[v=i]+(c-2)[t=i]\\
i>b &a_i.
\end{array}
\tag{286.6}
$$
Only the second case has $p_i=[v=i]$, paid by its own term.
This exhausts every label, including earlier, opposite-head and
unqueried outputs; sorting or repeating a query changes only its
information partition, never the actual request count.
Thus (286.3) holds on the whole catalog.

Integrate against the same $\lambda$. Both comparison words have
first zero $i$, so $\sum\lambda_D\ell_i=s_i-t_i$.
Their own complete correct rows make $s_i,t_i\ge0$, proving (286.4)
and its arbitrary nonnegative weighted sums without optimizing any part.
For completeness the common reserve follows from equal mass and the
independent early union rows. With $r_h,\eta,X,R_{\rm pair},s_+$
as in 274.5 and 275.3,

$$
\begin{aligned}
\sum_D\lambda_D\sum_i a_i(D)&=ce-R_{\rm pair}-X,\\
\sum_D\lambda_D\sum_i([D(v^i)=i]-[D(+)=i])
 &=E_b+2e+s_++\sum_i s_i+\eta.
\end{aligned}
$$
Subtracting gives the existing same-allocation identity

$$
\delta_b=s_++\sum_i s_i+\eta+R_{\rm pair}+X+G.
\tag{286.7}
$$
All terms are nonnegative and calculated at that same allocation.
Drop $t_i$ in (286.4) and then use (286.7) for (286.5).
No independent union demand is replaced by singleton estimates. $\square$

**Proposition 286.3 (Actual positive-cap sharpness of the slack coefficient).**
The coefficient one on $s_i$ in (286.4), with the other displayed
coefficients fixed, cannot be reduced even on actual original
positive-cap feasible acquisitions. This sharpness is outside $H_L$.

**Proof.** Fix $L\ge6$ and $0<s\le1/2$. Use the one-seed law

$$
(1-s)R+sN(3,4;0,3,0,0),\qquad e=s,
\quad a_1=a_2=1-s,\quad a_3=\cdots=a_L=s,
\quad a_n=\frac{s}{n-L}\ (n>L).
\tag{286.8}
$$
Its entire profile is positive, ordered and vanishing, with
$a_{L+1}=e$. At an early first zero the correct mass is $1-s$,
and the extra wrong mass is at most $s$. At first zero three the
law is either $e_0$ or $(1-s)e_0+se_3$, according to bit four;
at every later first zero it is $e_0$. Every independent deficit
is therefore at most $s$ on every multiple-zero word. Positive
base is one, so every actual tail error is $a_n\le s$.
One source-independent seed fixes the entire table; $N$ acquires
both requests and hands off the specified original mark.

Here $\Pi_3=s_3=s$, $t_3=G_3=0$, by direct evaluation of
$v^3,u^3,+$ and the unary moments in $a_3(D)$.
Thus any smaller coefficient on $s_3$ fails. The profile has
$E_b=-3s<0$, so is outside $H_L$ even when the two heads tie
with the late amplitudes. It supplies no $H_N$ optimality,
separator, or new sufficient amplitude region. $\square$

## 287. Dimension-independent deletion and its scalar boundary

**Theorem 287.1 (One deletion bound from label-owned charges).**
Let $m=L-2\ge4$, $a=(c_m-3)/2$, and define

$$
B_D=1+1/a,\qquad C_m=\frac{(m+1)!}{(m-k+1)!},\quad
w_m=\frac{\ell}{\binom mk},\quad
\gamma_m=\frac{w_m}{C_m},\quad
\varepsilon_D=\frac{\gamma_m}{1+c_mB_D},
\quad k=\lceil m/2\rceil,
\tag{287.1}
$$
where $\ell=c_m$ for odd $m$ and $\ell=2$ for even $m$.
For every full feasible $N$ allocation, at any real $b$, $e\ge0$
and finite mass,

$$
\delta_b\ge\varepsilon_D e,
\qquad \sum_{i\in J}(b_i-e)\le(c_m+1-\varepsilon_D)e.
\tag{287.2}
$$
In the proof the total mass deleted from that same allocation is at
most $B_D\delta_b$. Neither the deleted part nor the retained part
is asserted feasible or normalized.

**Proof.** Put $H_D=\sum_i g_i(D)+x_D+\eta_D$.
The nonnegative grouped expressions in 286.2 and the moment
coefficients in 285.10 give $H_D=0$ or $H_D\ge a$.
Remove its positive columns, of mass

$$
\tau\le(G+X+\eta)/a.
$$
On the zero face, remove the late pairs whose $01$ output is their
first address. These columns are disjointly owned by that first
label, and their mass $\sigma$ is at most $\sum_i\Pi_i$ for the
original full allocation. By (286.4),

$$
\sigma\le\sum_i s_i+G,\qquad
 d:=\tau+\sigma\le\sum_i s_i+G+(G+X+\eta)/a
                    \le(1+1/a)\delta_b.
\tag{287.3}
$$
There is no coordinatewise repeated penalty for the first deletion.
The zero-face list in the proof of 285.3 now gives the exact retained
late-output functions on the two early fibres:

$$
\begin{aligned}
f_1(Z)&=\sum_jB_j[j\in Z]+\sum_{i<j}D_{ij}[i\notin Z,j\in Z],\\
f_2(Z)&=\sum_jA_j[j\in Z]+\sum_{i<j}D_{ij}[i\notin Z,j\in Z].
\end{aligned}
\tag{287.4}
$$
Here $A_j,B_j$ are the retained mixed-pair masses with heads one,
two and $10$ output $j$, and $D_{ij}$ is the retained late-pair
mass with $10$ output $j$. They are nonnegative parts of the same
$\lambda$, with the same $D_{ij}$ in both functions.
Every other retained column contributes no late label on these fibres.
The original full independent union rows imply
$0\le f_h(Z)\le\mu_{\text{early}_h,Z}(J)\le e$ on every subset.
If $q_h(Z)$ is the deleted late mass, then $0\le q_h(Z)\le d$ and

$$
e-f_h(Z)=r_h(Z)+\chi_h(Z)+q_h(Z),
\qquad
\tfrac12\int(2e-f_1-f_2)\,d\nu
 \le R_{\rm pair}+X+cd\le(1+cB_D)\delta_b.
\tag{287.5}
$$
The opposite-head masses $\chi_h$ and the row slacks are those of
the original full allocation. This equality does not transfer its
feasibility to either part.

Consume the sink estimate of Theorem 278.2 as follows. If an ordered
cut $f$ on $r$ vertices is bounded by $e$ everywhere and every
$s$-subset has deficit at most $\zeta$, $1\le s\le r-2$, adding
the last vertex to an $s$-subset avoiding it increases $f$ by
$a_r+\sum_{i\notin S}d_{ir}$, between zero and $\zeta$.
Choose $S$ avoiding any specified $i$ to obtain
$a_r,d_{ir}\le\zeta$. Adding the last vertex to an $(s-1)$-subset
therefore changes $f$ by at most $r\zeta$, giving deficit at most
$(r+1)\zeta$ on that lower layer. Restrict and repeat from $(m,k)$;
the condition $s\le r-2$ persists until the empty layer. Since
$f(\varnothing)=0$,

$$
e\le C_m\max_{|Z|=k}(e-f(Z)),\qquad
\int(e-f)\,d\nu\ge w_m\max_{|Z|=k}(e-f(Z))\ge\gamma_m e.
$$
The second inequality uses nonnegative deficits and the actual
$\nu$ mass $w_m$ on every $k$-set. Apply it to both functions
(287.4) and compare with (287.5). This proves (287.2), including
$e=0$ and vanishing charges. The balanced moments, common identity,
zero face, cut representation and sink estimate are consumed existing
results; (286.3) supplies the bound (287.3). $\square$

**Corollary 287.2 (Full zero-cost score existence on this cone).**
With $K_D=m+c_m+1-\varepsilon_D$, there is a full nonnegative score
of quotient $(1_J;K_D)$ and zero $N$ cost. Positive-row padding and
scaling give one exact-$Q$ zero-cost representative for every full
input with quotient $(t1_J;K)$, $t\ge0$, $K\ge tK_D$.

**Proof.** Apply the valid-inequality multiplier theorem to the nonempty
finite cone
$\{(u,e,\lambda):G_N\lambda-\mathcal H u+e\mathbf1\ge0,
 e\ge0,\lambda\ge0,u\text{ free}\}$, where $u=b-\alpha$ and
$h=\mathcal H u-e\mathbf1$. It contains zero and (287.2) is valid
for every real $u$ on it. In the notation of Kaibel,
[*Basic Polyhedral Theory*, Theorem 12, arXiv:1001.2161v1](https://arxiv.org/html/1001.2161v1),
a valid inequality on a nonempty finite real polyhedron is a
nonnegative combination of its defining inequalities, with the same
linear coefficients and no greater constant. Coefficient matching here
gives an original-row vector $V\ge0$ with
$\mathcal H^TV=1_J$, $G_N^TV\le0$, $\sum V\le K_D$.
These signs follow from writing the first constraint as
$-G_N\lambda+\mathcal H u-e\mathbf1\le0$ and including
$-e\le0,-\lambda\le0$. Add $K_D-\sum V$ to $T$.
Its excess entries are $[D(+)=0]-1\le0$, so the resulting exact
quotient still has zero cost, attained at $R$.
Scale and pad for the asserted cone. This consumes the same standard
multiplier argument as 278.3; it makes no separate discovery claim or
explicit row selector outside the specified cone. $\square$

## 288. Comparisons of the scalar cones and the unrestricted boundary

**Proposition 288.1 (Five-address and ordered-block comparisons).**
The three scores of 281.1 yield the same five-address unit-weight
inequality with stock $21/5$ and total $46/5$. Relative to the
five-address stocks $17/4$ and $13/3$ in Sections 202 and 205, the
stock differences are respectively $1/20$ and $2/15$.
For the signed pattern (283.1), the $37/4$ payer already covers
$h\le63s/17$. The larger range in 283.1 extends that condition only by

$$
63s/17<h\le79s/21.
\tag{288.1}
$$
At $m=6k-1$, the stock in 284.1 is smaller by $1/(3k)$ than both
the balanced stock $c_m$ and the terminal-protected stock $c_{m-1}$
of Theorem 207.13.

**Proof.** The first assertions follow from (281.1) and subtraction.
Use the existing $37/4$ score at the same five addresses, scaled by
$t=(s+h)/5$. The residual has exactly the partial sums in 283.1,
and its cap coefficient is at least

$$
5s+h-(37/4)t=(63s-17h)/20.
$$
The same Abel estimate therefore already proves the smaller signed
range. For $m=6k-1$, both $\lceil(m+1)/2\rceil$ and
$\lceil m/2\rceil$ equal $3k$. Hence
$c_m=c_{m-1}=4-2/(3k)$, whose difference from $4-1/k$ is
$1/(3k)$. The protected comparison is within the stated protected
class of 207.13; it gives no optimality statement for the asymmetric
law in the unrestricted catalog. $\square$

**Proposition 288.2 (The explicit all-length bound implies the deletion
scalar bound).** For every $m\ge4$,

$$
\varepsilon_C(m)>\varepsilon_D(m)>0.
\tag{288.2}
$$
Thus every profile excluded by (287.2) is already excluded by (285.9).
This implication does not replace the label-owned inequalities or the
same-allocation deletion bound.

**Proof.** In the notation of 285.2 and 287.1, $0<a<1/2$,
$\ell\ge2$, and $t_j\le40$ by 285.4. Since

$$
\zeta\le\frac{mU}{(m-k)\ell}\le\frac54U<\frac{mU}{a},
$$
we have $\Lambda=mU/a$ and
$\varepsilon_C=a(m-k)/(m^2U)$.
Put $N=\binom mk(m+1)!/(m-k+1)!$. Then

$$
\varepsilon_D=\frac{\ell a}{N((1+c)a+c)}<\frac aN,
\qquad
\frac U{m-k}\le\frac1{m-k}+40k\le20m+21.
\tag{288.3}
$$
For $m\ge7$, $k\ge4$ and central-binomial monotonicity gives
$\binom mk\ge\binom m4$. Also
$(m+1)!/(m-k+1)!\ge(m+1)m(m-1)(m-2)$. Consequently

$$
\frac N{m^2}\ge
\frac{(m-1)^2(m-2)^2(m-3)(m+1)}{24}
\ge150(m+1)>20m+21\ge\frac U{m-k}.
$$
This proves $\varepsilon_C>a/N>\varepsilon_D$ there. The remaining
three substitutions are exact:

| $m$ | $\varepsilon_C$ | $\varepsilon_D$ |
| ---: | ---: | ---: |
| 4 | $1/576$ | $1/1460$ |
| 5 | $1/5295$ | $1/8760$ |
| 6 | $4/4449$ | $1/38850$ |

They prove (288.2) for all $m\ge4$. $\square$

**Proposition 288.3 (Further containments at even, five-address and
ordered-block lengths).**
For $m=2q\ge4$, the terminal-protected supplier 207.13 has stock
$c_{m-1}<c_m-\varepsilon_C$. At $m=5$, the numerical and signed
consequences of 285.3 are implied by the five-address results
282.1 and 283.1. At $m=6k-1$, both scalar inequalities 285.9 and
287.2 are implied by 284.4 with unit weights.

**Proof.** For even $m$, recurrence (285.1) implies
$t_j\ge(j-1)/(q-1)$, so
$U=1+(q/2)\sum_jt_j\ge q^2$. Therefore

$$
\varepsilon_C=\frac{a}{4qU}<\frac1{8q^3}
 <\frac2{q(q+1)}=c_m-c_{m-1}.
$$
This proves the protected-stock comparison, including $m=4$.
At $m=5$, (285.11) gives
$K_C=16473/1765>46/5$. Using only $K\ge5s+h$, its signed payer
of the form in 283.1 gives the sufficient range

$$
h\le\frac{25-K_C}{K_C-5}s
 =\frac{6913}{1912}s<\frac{63}{17}s<\frac{79}{21}s.
$$
Hence that numerical inequality and that signed sufficient range
are already covered by 282.1 and the older signed range in 288.1.
The weighted-slice identity, its exact equality cone, and the explicit
all-length nonnegative score remain the statements of 285.1–285.3.
Neither this comparison nor those statements assert sharpness of
$\varepsilon_C$.

Finally $U\ge1$, $a<1/2$ give
$\varepsilon_C=a(m-k)/(m^2U)<1/(2m)$.
At $m=6k-1$ this is less than $1/(3k)$, the stock difference in
288.1. Thus the asymmetric bound is stronger than the $C$ scalar
bound at those lengths, and (288.2) also includes the $D$ scalar
bound. All comparisons concern the same quotient and full feasible
allocation, not separately attainable extrema. $\square$

**Example 288.4 (A positive-tail scalar exclusion with no feasible
witness).** Put

$$
L=7,\quad e=1/20,\quad
a_1=\cdots=a_7=\frac{8530229}{91396000},\qquad
a_{7+r}=e/r\quad(r\ge1).
$$
The finite point is in $H_7$ and

$$
\frac{\delta_b}{e}=\frac{193}{2741880},\qquad
\frac1{37560}<\frac{193}{2741880}<\frac1{8760}.
$$
These are obtained directly from $c_5=10/3$ and
$\delta_b=(28/3)e-5a_3$. The point meets the named earlier sink
bound with constant $1/37560$ and fails (287.2). It also fails
the stronger bounds 285.9 and 282.2, so it supplies no additional
excluded region beyond them. The actual tail is positive, ordered
and vanishing, with $a_8=e$. By 110.2 there is no full feasible
$N$ cap attainer for this selected marked target. In particular it
is not a separating $H_N$ point or an original $N/O$ separator.

**Mathematical boundary 288.5 (The remaining common-payment problem).**
All finite words, multiple zeros, labels and independent events in
273.1 remain part of the problem. The admissible competitors still use
arbitrary addresses and full-carrier outputs, with the original source,
consumer and nonatomic targets of 273.3 kept distinct from its selected
marked laws. The negative singleton demands, actual positive vanishing
tails, closed ties and both actual requests remain in force.

In particular the actual source $(19,436)$ has $F_{19}=4181$ and
$N=1822917$, and has first four replies $0100$. The table
$N(3,4;1,0,0,0)$ outputs the earlier unqueried label one on that
word. Its stopped endpoint repair outputs zero there. The mass is one
and the defect in the sourcewise inequality of 279 is two. The
same-seed completion of an $O$ rule to $N$ counts its ignored second
request; it does not invert that failed endpoint repair.

For every full $y\ge0$ with $\Delta_O(y)\le1$, the still required
common-payment conclusion is one unrestricted $V\ge0$ and
$\theta\in[0,1]$ satisfying

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(Qy-QV)\le\theta.
\tag{288.4}
$$
The alternative is one same actual $(b,e)\in H_N$ and one complete
feasible nonnegative $N$ allocation of mass $M\ge1$ with
$F_{Qy}(b,e)>M$, together with an original $N$ cap attainer and a
uniform lower certificate against all original $O$ competitors.
Such a separator must use the same profile and allocation throughout;
normalization (273.10) changes the profile. The genuine transports
109.1 and 110.2 do not supply that strict separator by themselves.
The exact quotient cones, signed class, reserve estimates and necessary
inequalities above do not settle this unrestricted alternative.

## 追加锚（本行以下为增补区）
