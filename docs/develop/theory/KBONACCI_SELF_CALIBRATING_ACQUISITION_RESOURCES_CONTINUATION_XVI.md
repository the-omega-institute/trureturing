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
