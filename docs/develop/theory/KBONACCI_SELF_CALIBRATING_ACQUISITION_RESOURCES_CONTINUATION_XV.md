# KBONACCI self-calibrating acquisition resources XV

## 251. Complete kernels, event scores and original-source applicability

**Definition 251.1 (Words, complete tables and independent cap rows).**
Fix $L\ge3$, $B_L=\{0,1\}^L$ and $J_L=\{0,\ldots,L\}$.
Write $w^+=1^L$, $\Omega_n=\{w:n=\min\{i:w_i=0\}\}$,
$v^i$ for the sole-zero word at $i$, and $v^{ij}$ for the word
whose zeros are exactly $i<j$. The output unit vector at label $r$
is $e_r$. All labels in $J_L$, including earlier unqueried labels,
are allowed on every terminal cell.

The complete $N$ catalog contains every constant, singleton and
sorted distinct-pair table. Write
$N(i,j;u,v,s,t)$ for its outputs on cells $00,01,10,11$, respectively.
The complete $O$ catalog contains every constant, singleton and
$O(i,j;v,s,t)$, with outputs on stopped cells $0,10,11$.
The schedule is fixed before replies. An $N$ table obtains its whole
schedule; an $O$ table stops at its first queried zero or exhaustion.
Static reversal or deletion of a repeated observation normalizes an
information partition only: every repeated or ignored actual request
still counts against the hard budget of two.

A normalized kernel $p$ is one probability distribution $\pi$ on
whole deterministic tables, including all counterfactual cell outputs.
It is not a collection of separately optimized word laws. For
$1\ge a_1\ge\cdots\ge a_L\ge0$ and $e\ge0$, its cap rows are

$$
\begin{split}
p_w(0)&\ge1-a_n-e,\\
p_w(n)&\ge a_n-e,\\
p_w(0)+p_w(n)&\ge1-e\qquad(w\in\Omega_n),\\
p_{w^+}(0)&\ge1-e.
\end{split}
\tag{251.1}
$$

All words, all multiple-zero suffixes, negative singleton demands
and zero-score rows remain present. The union row is independent.
For any probability vector on the full label set,

$$
\operatorname{TV}\bigl(p_w,(1-a_n)e_0+a_ne_n\bigr)
=\max\{1-a_n-p_w(0),\ a_n-p_w(n),\ 1-p_w(0)-p_w(n)\}.
\tag{251.2}
$$

Indeed the mass outside $\{0,n\}$ is nonnegative, and the positive
and negative parts of the signed difference have equal total mass.
Separating the signs of its two supported coordinates gives exactly
these three candidates. In particular no sum of singleton estimates
can replace the union event.

**Definition 251.2 (Full scores and conic coordinates).** A score
$y=(A_w,C_w,P_w;T)$ has independently nonnegative coordinates and
reward

$$
g_y(w,r)=A_w[r=0]+C_w[r=n]+P_w[r\in\{0,n\}]
\quad(w\in\Omega_n),\qquad g_y(w^+,r)=T[r=0].
\tag{251.3}
$$

Brackets denote indicators. Let $z_D$ be the complete event vector
of a table, $R=O(1,2;1,2,0)$,
$\alpha=(1,1,0,\ldots,0;0)$ and $\mathbf r=z_R=d(\alpha)$.
Here $d(b,e)$ is the vector of every demand in (251.1).
Set

$$
\begin{gathered}
G_C=(z_D-\mathbf r)_{D\in\mathcal D_C},\qquad
h(b,e)=d(b,e)-\mathbf r,\\
W_y=y\cdot\mathbf r,\quad B_C(y)=\max_{D\in\mathcal D_C}y\cdot z_D,
\quad\Delta_C(y)=B_C(y)-W_y\ge0,\\
\beta_n(y)=\sum_{w\in\Omega_n}(C_w-A_w),\qquad
K_y=\sum_{w\ne w^+}(A_w+C_w+P_w)+T,\\
Q(y)=(\beta_1,\ldots,\beta_L;K_y),\qquad
F_q(b,e)=\sum_n\beta_n(b_n-\alpha_n)-Ke.
\end{gathered}
\tag{251.4}
$$

Thus $F_{Q(y)}=y\cdot h$; abbreviate it to $F_y$.
The auxiliary closed domain is

$$
\begin{split}
H_L=\{(b,e):\;&1\ge b_1\ge\cdots\ge b_L\ge e\ge0,\quad b_2=b_3,\\
&0\le E:=\sum_{n=3}^Lb_n-(L+1)e\le1-b_1\}.
\end{split}
\tag{251.5}
$$

Write $\sigma_H(q)=\max_{H_L}F_q$ and
$H_N=\{b\in H_L:\exists\lambda\ge0,\ G_N\lambda\ge h(b)\}$.
A conic vector $\lambda$ has mass $M=\sum_D\lambda_D$; it is not
an acquisition probability distribution unless $M=1$.
All matrices here contain every event row and every terminal label.
These are the complete-score coordinates of
[Sections 198–199](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md#198-完整目录得分约化符号凸包与混合预算缺口)
and [Definitions 207.1–207.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_IX.md#207-joint-realizability-retained-early-credit-and-equal-cylinder-comparison).

**Definition 251.3 (Counting deficit and the fixed endpoint repair).**
For a normalized feasible $N$ kernel with a fixed decomposition $\pi$,
put

$$
\begin{gathered}
\delta=3-p_{w^+}(0)-\sum_i p_{v^i}(i),\qquad
s_0=p_{w^+}(0)-(1-e),\quad s_i=p_{v^i}(i)-(a_i-e),\\
S=\sum_i s_i,\quad D=2-\sum_i a_i+(L+1)e=\delta+s_0+S,\\
B=\sum_i(L-i)s_i+3\delta,\qquad c_L=\max\{3,L-1\}.
\end{gathered}
\tag{251.6}
$$

Replace each $N(i,j;u,v,s,t)$ by $\bar D=O(i,j;v,s,t)$,
keeping constant and singleton tables. Let $\bar p$ be this one
repaired mixture and $\mu=\pi\{\text{pair tables}:u\ne v\}$.
The normalized counting estimate of
[Section 248](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIV.md#248-quantitative-stopped-repair-of-every-full-normalized-n-law)
gives

$$
\delta,s_0,s_i\ge0,\qquad
\sup_w\operatorname{TV}(p_w,\bar p_w)\le\mu
\le\min\{1,B\}\le\min\{1,c_LD\}.
\tag{251.7}
$$

For clarity, its counting defect on a pair is
$d_D=3-[v=i]-[s=j]-[t=0\text{ or }t\notin\{i,j\}]$.
The last bracket counts positive base or one correct unqueried
sole-zero label, so $d_D\ge0$ and $\mathbb E_\pi d_D=\delta$.
The cap rows give the nonnegative slacks and their displayed sum.
The entire vectors at $w^+$ and every $v^i$ are preserved, since
these words never visit pair cell $00$. On every word, the same-seed
outputs can differ only in the one event of mass $\mu$.
Consequently each independent event row holds at $e+\mu$.
The counting and gain proof uses only the cap rows (251.1), not
$a_L\ge e$, so this finite formulation also covers inactive and
zero-cap auxiliary coordinates. The weighted bound in (251.7),
its $D=0$ endpoint and the balanced
full $N/O$ plateau face of Section 249 are used as existing results.

**Proposition 251.4 (Original source and the scope of finite repairs).**
All subsequent finite acquisitions apply to the separately selected
marked laws of [Definition 110.1 and Theorem 110.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#110-exact-closed-cap-transport-on-the-original-countable-source).
Explicitly retain

$$
\begin{gathered}
F_0=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)=1+F_rg,\quad q_i(x)=[p_i\mid N(x)],\quad
n(x)=\min\{i:q_i(x)=0\},\\
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}
                   +a_{n(x)}\delta_{\theta_{n(x)}},\qquad
1\ge a_1\ge a_2\ge\cdots>0,\quad a_i\longrightarrow0.
\end{gathered}
\tag{251.8}
$$

Here $p_i$ are the increasing primes. The countable source has
static answers and finite first absence. Every finite pattern has
an actual source witness by
[Boundaries, Theorem 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows),
under its stated entry-rank supplier. Its CRT construction chooses
a prime index for which $F_r$ is invertible modulo the finitely
prescribed primes, then selects the required residue class for $g$
in the growing Fibonacci window. This is the named arithmetic
premise, not a new claim eliminating that supplier.

The full Borel carrier is
$\bigsqcup_{j\ge1}B_j\sqcup\bigsqcup_{j\ge1}P_j$, with each
block a copy of $(0,1)$ and $\theta_j=(B_1,1/(j+2))$.
The consumer, unknown on $B_j$ and with proposal $j$ on $P_j$,
and its original nonatomic targets remain those of
[Acquisition Resources, Definitions 71.1 and 73.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES.md#73-monotone-marked-first-absence-laws-and-their-finite-certificates).
In particular, with its fixed $h_0\in(0,1)$,
$s(x)=\sum_i3^{-i}q_i(x)$ and $\Omega(x)$ the number of
distinct prime divisors of $N(x)$, those targets are
$\mu_x=(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$, where $\nu_x$ has
density $\exp(s(x)u)/\int_0^1\exp(s(x)v)\,dv$ on $B_{n(x)}$
and $\pi_j$ is uniform on $P_j$. They are distinct from (251.8).

Every displayed finite mixture is realized by a single
source-independent $U\sim\operatorname{Unif}[0,1)$ partitioned
into whole-table intervals before replies. An outer mixture, a choice
of midpoint daughter, or a refinement of terminal marginals is made
within that same seed. It does not supply another observation or seed.
Execution queries actual prime addresses, has zero advice, hands off
an original mark finitely for every source and seed, and makes at most
two actual requests. Its $N$ completion obtains the whole schedule
on the same $U$ and counts any ignored reply.

**Proof.** The finite table construction of Sections 109–110 fixes
the schedule and every counterfactual terminal output from $U$.
For a cell-marginal description, refine a schedule interval by the
finitely many marginal cutpoints; this gives a common whole-table
law without assuming independence among cells. The necessary
direction of Theorem 110.2 permits original competitors with arbitrary
addresses, arbitrary full-carrier outputs, repetitions and sourcewise
almost-sure finite handoff. Countability supplies one common conull
seed event; the maximum preselected address is finite almost surely.
Actual finite-pattern witnesses are fixed before seeds. Whole-schedule
address tails and finite-family execution cutoffs give approximate
finite catalog laws, and compactness gives the exact closed-cap law.
This transports feasibility and need not preserve an initially supplied
competitor's law or seed coupling. A same-seed repair begins with the
selected finite representative.

At an actual first absence $n>L$, any displayed finite law emits no
label $n$ and has the exact full-Borel error

$$
\operatorname{TV}\left(\sum_{r=0}^Lp_{w^+}(r)\delta_{\theta_r},
             (1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n}\right)
=\max\{1-p_{w^+}(0),a_n\}.
\tag{251.9}
$$

Thus repairs preserving the positive law retain every original tail
cap, including ties $a_{L+1}=e$. An increased head cap does not require
discarding the original tail. The finite all-positive word records
these actual tails; it is not an infinite all-positive source.
All statements use uniform all-source TV over all Borel events,
without a source prior, address bound, running-time bound, mean request
budget or access to $N(x)$ or $n(x)$. A finite marked law has TV one
from each unchanged nonatomic $\mu_x$, by its finite support. No
approximation to those targets is asserted. $\square$

## 252. A fair-suffix quarter gap and actual-deficit sharpness

**Definition 252.1 (Fair score and canonical tables).** Set
$A_w=P_w=0$, $C_w=2^{-(L-n)}$ for $w\in\Omega_n$, and $T=1$.
Call this full score $\zeta$. For a law $p$ let

$$
\Phi(p)=\zeta\cdot z_p=p_{w^+}(0)
 +\sum_n\frac1{2^{L-n}}\sum_{w\in\Omega_n}p_w(n),
\qquad\kappa=3-\Phi(p).
\tag{252.1}
$$

A canonical pair is $N(i,j;i,i,j,r)$ with $r=0$ or $r>j$.
It is already stopped. Let $\nu$ be the mass of every noncanonical
table, including constants and singletons, in the same decomposition.

**Theorem 252.2 (One quarter-gap repair).** For every normalized full
feasible $N$ law and every one of its whole-table decompositions,

$$
\begin{gathered}
\bar s_n=\frac1{2^{L-n}}\sum_{w\in\Omega_n}
                 [p_w(n)-(a_n-e)]\ge0,\\
0\le\kappa=D-s_0-\sum_n\bar s_n,\qquad
\mu\le\nu\le\min\{1,4\kappa\}\le\min\{1,4D\}.
\end{gathered}
\tag{252.2}
$$

The fixed repair of Definition 251.3 preserves the positive and
sole-zero vectors and satisfies all cap rows at $e+\mu$ under the
same seed. There is also a projection onto canonical mixtures with
uniform TV distance at most $\nu$ and nondecreasing positive base
probability; that projection need not preserve sole-zero laws.

**Proof.** For a pair $i<j$, the total fair-correct contribution of
one terminal label, together with the positive-base contribution, is
the following vector in $00,01,10,11$ order:

| terminal label $r$ | $00$ | $01$ | $10$ | $11$ |
|---|---:|---:|---:|---:|
| $0$ | $0$ | $0$ | $0$ | $1$ |
| $1\le r<i$ | $1/4$ | $1/4$ | $1/4$ | $1/4$ |
| $r=i$ | $1/2$ | $1/2$ | $0$ | $0$ |
| $i<r<j$ | $0$ | $0$ | $1/2$ | $1/2$ |
| $r=j$ | $0$ | $0$ | $1$ | $0$ |
| $r>j$ | $0$ | $0$ | $0$ | $1$ |

For example, when the first zero is earlier than both queried
indices, its fair suffix places each queried pair cell at probability
$1/4$. When it is $i$, its two cells each have probability $1/2$.
When it is $j$, the queried cell is $10$. This derives every entry
for every label, with no constraint on the remaining zero suffix.

The four cell maxima are $1/2,1/2,1,1$, attained simultaneously
exactly by canonical tables. Any other pair loses at least $1/4$.
A singleton has score at most two: its zero cell contributes at most
one and its positive cell at most one. A constant has score at most
one. Thus $\Phi(D)\le3$ on the entire catalog and
$[D\text{ noncanonical}]\le4(3-\Phi(D))$.
Every pair with $u\ne v$ is noncanonical. Integrating the one
decomposition proves $\mu\le\nu\le4\kappa$.
Substituting all averaged correct slacks and the positive slack in
(252.1) gives the identity in (252.2). Their nonnegativity proves
the remaining bound. Definition 251.3 proves the repair statements
on every event, including the independent union event.

For the canonical projection, retain canonical tables. Replace any
other pair by $N(i,j;i,i,j,r')$, taking $r'=t$ when $t=0$ or
$t>j$, and $r'=0$ otherwise. Replace constants and singletons by
$N(1,2;1,1,2,0)$. All replacements are canonical; they can change
outputs only on the one noncanonical seed event. A positive output
of zero is retained, and new zero outputs can be added. This proves
the asserted TV and positive-base properties. $\square$

**Proposition 252.3 (The factor four is sharp relative to $\kappa$).**
For every $L\ge3$ and $0<t<1$, there is an original cap-feasible
$N$ law for which

$$
\kappa=t/4,\qquad\mu=\nu=t,
\qquad\sup_w\operatorname{TV}(p_w,\bar p_w)=t.
\tag{252.3}
$$

**Proof.** Let $P$ be the uniform canonical triple law on
$[L]\cup\{\infty\}$: query the two smallest numerical labels
in the chosen triple and emit its third label on positive exhaustion,
with $\infty$ meaning zero. Its inclusion marginal is
$s=3/(L+1)$, so its correct probability is $s$ throughout every
first-zero class and its positive base probability is $s$.
Use the one law

$$
p=(1-t)P+tN(2,3;1,2,3,0),\qquad
a_i=1\ (i\le L),\qquad e=1-(1-t)s.
\tag{252.4}
$$

Every correct probability is at least $1-e=(1-t)s$, the union
probability is at least the correct probability, the base demand
is $-e$, and the positive base is $(1-t)s+t$. Thus every row holds.
On a first-zero-one word with bits two and three positive, correct
probability is exactly $(1-t)s$, so the uniform low-word error is
exactly $e$. Append any positive monotone vanishing tail bounded
by $e$. Formula (251.9) bounds its error by $e$.

The exceptional table has fair score $11/4$, versus three for
every triple. It is the only noncanonical or changed part. On a
word with bits two and three zero the difference between old and
repaired laws is exactly $t(e_1-e_2)$, proving (252.3).
For comparison, this same law has
$\delta=0$, $s_0=t$, $s_2=s_3=t$, all other $s_i=0$,
$D=3t$ and $B=(2L-5)t$.
Consequently the sharpness statement is about actual fair-score
deficit $\kappa$. It asserts neither sharpness of $\mu/D$ nor
sharpness of distance to the unrestricted $O$ class. That class
already has a plateau law on this profile. $\square$

## 253. Same-allocation slacks, signed score allowance and conic normalization

**Definition 253.1 (The changed-cell oscillation).** For a full
score $y$, put

$$
H_{ij}^y(r)=\sum_{w:w_i=w_j=0}g_y(w,r),\qquad
\omega_y=\max_{i<j}\left(\max_{r\in J_L}H_{ij}^y(r)
                              -\min_{r\in J_L}H_{ij}^y(r)\right).
\tag{253.1}
$$

Then $0\le\omega_y\le K_y$. It sums the actual changed $00$
cell before taking its oscillation; all terminal labels are included.

**Theorem 253.2 (One full $\lambda$, its actual slacks and its gap).**
Fix $(b,e)\in H_L$ and one full $\lambda\ge0$ with
$G_N\lambda\ge h(b,e)$ and mass $M\ge1$. For every full $y\ge0$,
define

$$
\begin{gathered}
S_y=y\cdot(G_N\lambda-h)\ge0,\qquad
S_\zeta=\zeta\cdot(G_N\lambda-h)\ge0,\\
D_b=2-\sum_i b_i+(L+1)e,\qquad
J_\lambda=D_b-S_\zeta
       =\sum_D\lambda_D(3-\zeta\cdot z_D)\ge0.
\end{gathered}
\tag{253.2}
$$

Then

$$
F_y(b,e)+S_y
\le M\Delta_O(y)+\omega_y\min\{M,4J_\lambda\}.
\tag{253.3}
$$

In particular a strict gap $F_y(b,e)>M$ with $\Delta_O(y)\le1$
requires $J_\lambda>0$ and $\omega_y>0$, and satisfies

$$
F_y-M+S_y+M(1-\Delta_O(y))
\le\omega_y\min\{M,4J_\lambda\}.
\tag{253.4}
$$

**Proof.** Since $\zeta\cdot\mathbf r=3$ and $F_\zeta=-D_b$,
expanding $S_\zeta$ gives (253.2). For each pair table, its old
score minus its repaired score is exactly
$H_{ij}^y(u)-H_{ij}^y(v)$, hence at most
$\omega_y[u\ne v]$. Other schedules have no difference.
The fair quarter-gap proof gives the column inequality
$[u\ne v]\le4(3-\zeta\cdot z_D)$ on pairs, and zero on
the other schedules. Integrating this inequality under the same
unnormalized $\lambda$ bounds changed mass by
$\min\{M,4J_\lambda\}$. Every repaired column is an $O$ column,
whose excess score is at most $\Delta_O(y)$. Thus

$$
y\cdot G_N\lambda
\le M\Delta_O(y)+\omega_y\min\{M,4J_\lambda\}.
$$

Its left side is exactly $F_y+S_y$, not just a lower estimate.
Rearrangement proves the strict-gap formula. Its left side is
positive when the gap is strict and the input is unit-$O$, so both
factors on the right must be positive. $\square$

**Proposition 253.3 (An explicit score and its unpaid residual).**
For every full $y\ge0$, the full nonnegative score
$V_y=y+4\omega_y\zeta$ satisfies

$$
\Delta_N(V_y)\le\Delta_O(y),\qquad
F_{Q(y)-Q(V_y)}=4\omega_yD_b,\qquad
\sigma_H(Q(y)-Q(V_y))=8\omega_y.
\tag{253.5}
$$

**Proof.** Columnwise,
$y\cdot(z_D-\mathbf r)\le\Delta_O(y)+\omega_y I_D$,
where $I_D=[u\ne v]$ on pairs and zero otherwise. Adding
$4\omega_y\zeta\cdot(z_D-\mathbf r)$ cancels its excess
because $I_D\le4(3-\zeta\cdot z_D)$.
Taking the maximum over the full $N$ catalog proves the budget
bound. The quotient difference is $-4\omega_yQ(\zeta)$ and
$F_\zeta=-D_b$, giving the exact residual. On $H_L$,
$D_b=2-b_1-b_2-E\le2$; it attains two at the auxiliary origin.
This proves the exact supremum.

The sufficient payment condition for this particular choice is
$\Delta_O(y)+8\omega_y\le1$, with $\theta=8\omega_y$.
It is not automatic for a unit-$O$ input. At $y=\zeta$,
$\omega_y=1/2$ and this construction gives $V_y=3\zeta$
with residual supremum four. Yet $V=\zeta$, $\theta=0$ is a
valid certificate because $\Delta_N(\zeta)=0$.
Thus failure of this score construction is not nonmembership in
the unrestricted certificate set. $\square$

**Proposition 253.4 (Conic division changes the auxiliary profile).**
For the $\lambda$ in Theorem 253.2, the normalized law
$p=\lambda/M$ is feasible at

$$
(x,e_x)=(1-M^{-1})\alpha+M^{-1}(b,e),\qquad e_x=e/M,
\quad D_x=D_b/M.
\tag{253.6}
$$

Its coordinates need not satisfy $x_2=x_3$, so it need not belong
to $H_L$. Dividing need not give cap feasibility at the unchanged
$(b,e)$.

**Proof.** Affineness gives
$Z_N(\lambda/M)=\mathbf r+G_N\lambda/M\ge
\mathbf r+h(b,e)/M=d(x,e_x)$. The coordinates remain ordered
between zero and one, so normalized repair theorems apply without
requiring membership in $H_L$. The formula for $D_x$ uses
$\sum_i\alpha_i=2$.

For a full same-profile counterexample, take $L=5$, $b_i=1$,
$e=1/2$, $T_*=O(3,4;3,4,5)$ and the anchor $R$.
This point belongs to $H_5$. The conic vectors
$\lambda_0=\tfrac12 e_{T_*}$ and
$\lambda_1=\lambda_0+e_R$ have masses $1/2$ and $3/2$;
both satisfy every full $N$ and $O$ demand at this same point.
For first zero one or two their correct and pair column sums are
$-1/2$, meeting demands $-1/2$, and their base column sum is zero,
above $-1/2$. For first zero three, four or five the correct sum is
$1/2$, the pair sum zero and the base sum $-1/2$, meeting demands
$1/2,-1/2,-3/2$. The positive column sum is $-1/2$, its exact
demand. These checks cover every suffix because $T_*$ always
emits the actual first zero in classes three through five.
The anchor column is zero, so adding it changes none of these sums.

At the unchanged profile, division gives law errors one and $2/3$,
respectively: early first-zero classes receive no correct mass from
$T_*$, and $\lambda_1/(3/2)$ receives only $2/3$ from $R$.
In contrast, padding $\lambda_0+\tfrac12e_R$ gives a mass-one
law at cap $1/2$. Appending
$a_{5+j}=\tfrac12 2^{1-j}$ retains positive vanishing actual tails.
These are normalization facts about the same profile, not a strict
separator: that profile has the padded stopped law. $\square$

## 254. All-real suffix polynomials and an optimized nonlinear bound

**Theorem 254.1 (Biased suffix inequality).** For the same $p,\pi$
and $S,\delta,\mu$ as in Definition 251.3, every real $t\in(0,1)$
satisfies

$$
t(1-t)\mu\le S+(3t-2t^2)\delta.
\tag{254.1}
$$

**Proof.** In each first-zero class $i$, average over all suffixes
with independent zero weight $t$ and one weight $1-t$.
This is a finite convex combination of existing correct rows, used
only in a proof; it is neither a source prior nor operational randomness.
For a deterministic table put

$$
L_D(t)=\sum_i\left([D(v^i)=i]
                  -\mathbb E_{t,\Omega_i}[D(w)=i]\right),
\quad u=t(1-t),\quad C_t=3t-2t^2=t+2u.
\tag{254.2}
$$

For a pair $a<b$, the summed average-correct contribution of a
cell emitting $r$ is

$$
\begin{split}
\phi_{00}(r)&=t[r=a]+t^2[1\le r<a],\\
\phi_{01}(r)&=(1-t)[r=a]+u[1\le r<a],\\
\phi_{10}(r)&=[r=b]+t[a<r<b]+u[1\le r<a],\\
\phi_{11}(r)&=[r>b]+(1-t)[a<r<b]+(1-t)^2[1\le r<a].
\end{split}
\tag{254.3}
$$

All four functions vanish at $r=0$. To derive the formulas, fix
the first zero to $r$. A query before $r$ is one, a query at $r$
is zero, and a query after $r$ has zero weight $t$.
This covers every relative position of every output label.

Write $A=[\ell_{01}=a]$, $B'=[\ell_{10}=b]$,
$Z=[\ell_{11}=0\text{ or unqueried}]$,
$d_D=3-A-B'-Z$, and $c=[\ell_{00}\ne\ell_{01}]$.
The first two cells satisfy

$$
A-\phi_{00}(\ell_{00})-\phi_{01}(\ell_{01})
\ge uc-C_t(1-A).
\tag{254.4}
$$

Here is the full case check. If $A=1,c=0$, the left side is zero.
If $A=1,c=1$, $\phi_{00}(\ell_{00})\le t^2$ and the
left side is at least $t-t^2=u$. If $A=0,c=0$, the two
contributions sum to at most $t$, so the left side is at least
$-t\ge-C_t$. If $A=0,c=1$, they sum to at most $t+u$,
giving $-(t+u)=u-C_t$.
Also

$$
B'-\phi_{10}(\ell_{10})\ge-t(1-B'),\qquad
[\ell_{11}\text{ numerical unqueried}]-\phi_{11}(\ell_{11})\ge0.
$$

The sole-zero contribution of cell $11$ is the bracket in this
last expression. Since $C_t\ge t$ and
$d_D\ge(1-A)+(1-B')$, summing yields
$L_D(t)\ge uc-C_td_D$.

A singleton at $a$ can gain, relative to its sole-zero indicators,
only by emitting an earlier first-zero label in its zero cell.
There is at most one such label and its gain is at most $t$.
Its positive cell cannot gain. Its counting defect is at least one,
so $L_D(t)\ge-t\ge-C_td_D$. A constant has $L_D(t)=0$.
Thus the inequality holds on the entire catalog, with $c=0$ on
nonpairs. For example $N(2,4;2,1,4,0)$ has $L_D(1/2)=-3/4$,
$d_D=c=1$, attaining equality. Earlier unqueried labels are
essential to this case, and remain legal.

Each averaged correct probability is at least $a_i-e$ by (251.1).
Therefore $\mathbb E_\pi L_D(t)\le\sum_i s_i=S$.
Integrating the preceding pointwise inequality under the same
$\pi$ gives $u\mu-C_t\delta\le S$, proving (254.1). $\square$

**Corollary 254.2 (Optimized $\Psi$ and the combined repair bound).**
Define

$$
\Psi(S,\delta)=2S+3\delta+2\sqrt{S(S+\delta)}.
\tag{254.5}
$$

For this same decomposition,

$$
\mu\le\min\{1,B,4\kappa,\Psi(S,\delta)\},\qquad
\Psi(S,\delta)\le4(S+\delta)=4(D-s_0).
\tag{254.6}
$$

Consequently the fixed repair is cap-feasible at
$\min\{1,e+\mu\}$, with the same positive and sole-zero vectors.

**Proof.** Dividing (254.1) gives

$$
\mu\le\frac S t+\frac{S+\delta}{1-t}+2\delta.
$$

For $S>0$, the minimum is attained at
$t=\sqrt S/(\sqrt S+\sqrt{S+\delta})$ and equals (254.5).
One can see the minimum without differentiation by completing
$\bigl(\sqrt{S(1-t)/t}-\sqrt{(S+\delta)t/(1-t)}\bigr)^2$.
For $S=0$, let $t\downarrow0$ in the numerical inequality to get
$\mu\le3\delta$, including $\delta=0$. This is a limit of
inequalities, not a limiting sampler. Finally
$2\sqrt{S(S+\delta)}\le2S+\delta$ by squaring the nonnegative
sides. Intersecting bounds on the same $\mu$ proves (254.6).
It does not claim that $\Psi$ always improves the actual
$4\kappa$ bound. The factor four already counted in Section 252
is one bound, not a second independent result. $\square$

**Corollary 254.3 (Original and conic consequences).** For every
entire original sequence and positive cap $e$ with active length
$L\ge3$, original $N_2$ feasibility gives an original $O_2$ rule
with error at most $\min\{1,e+\min(1,4D)\}$.
For any selected representative, (254.6) gives its sharper allowance.
Its actual tails still have error at most the original $e$.
For the same $b,\lambda,M$ as in Theorem 253.2, normalize as in
(253.6), and evaluate $S,\delta,\kappa,B$ on that law. Then
(253.3) holds with $\min\{M,4J_\lambda\}$ replaced by

$$
M\min\{1,B,4\kappa,\Psi(S,\delta)\}
=\min\{M,MB,4J_\lambda,\Psi(MS,M\delta)\}.
\tag{254.7}
$$

The coarser dimension-independent version is
$F_y\le M\Delta_O(y)+K_y\min\{M,4D_b\}$.

**Proof.** Use Theorem 110.2 to select a finite normalized witness,
then apply the repair and Proposition 251.4. The exact positive law
is preserved, so (251.9) retains the old tail cap even when the
increased cap has a different active horizon. In the conic statement,
$\kappa=J_\lambda/M$ and $\Psi$ is homogeneous of degree one.
The column score argument of Theorem 253.2 then uses (254.6)
instead of its single bound. Since $\omega_y\le K_y$ and
$D_x=D_b/M$, the stated coarse consequence follows.
Every positive allowance remains unpaid in the original one-unit
certificate problem. $\square$

**Proposition 254.4 (A strict comparison with the weighted guarantee).**
Take $L=24$, $\eta=1/144$, $s=3/25$ and the uniform triple law
$P$ on $[24]\cup\{\infty\}$. Set

$$
p=(1-\eta)P+\eta N(1,24;0,1,24,0),\qquad
a_i=1\ (i\le24),\quad e=1057/1200.
\tag{254.8}
$$

This is feasible at every independent row and has exact uniform
error $e$, with any positive monotone vanishing tail bounded by $e$.
For its displayed decomposition,

$$
\delta=0,\quad s_0=1/144,\quad S=1/72,\quad D=1/48,
\quad\mu=1/144,\quad B=23/144,\quad\Psi=1/18.
$$

**Proof.** The triple component supplies correct mass
$(1-\eta)s=1-e$ on every class. The union row follows from this
mass, and the base demand is negative. Its positive base is at least
$1-e$. A class-two word has exact correct deficit $e$.
Only the exceptional pair changes. It has zero counting defect,
adds sole-zero slack $\eta$ at one and 24, and positive slack
$\eta$, giving every displayed quantity by (251.6).
Thus the old weighted guaranteed cap clips to one, whereas
$e+\Psi=3371/3600$ and $e+4D=1157/1200$ are strictly below one.
This is an improvement of the universal repair estimate on a known
profile; the old plateau suppliers already give a better stopped law
there. It supplies no new plateau feasibility or optimality. $\square$

## 255. Midpoint repair, signed sensitivity and its preserving-law boundary

**Definition 255.1 (Midpoint daughters and signed sensitivity).**
Replace each pair $N(i,j;u,v,s,t)$ by the equal mixture of
$O(i,j;u,s,t)$ and $O(i,j;v,s,t)$, keeping constants and
singletons. Denote the resulting one law by $p^{\mathrm{mid}}$.
For a full score define

$$
\begin{gathered}
d_{ij}^y(r)=\sum_{w:w_i=w_j=0}g_y(w,r)
                 -\sum_{w:w_i=0,w_j=1}g_y(w,r),\\
\Xi_y=\frac12\max_{i<j}\operatorname{osc}_{r\in J_L}d_{ij}^y(r),
\qquad\operatorname{osc} f=\max f-\min f,\\
\Gamma_y=\sum_{w\ne w^+}\operatorname{osc}_{r\in J_L}g_y(w,r)
 =\sum_{w\ne w^+}\bigl(P_w+\max(A_w,C_w)\bigr)\\
 =K_y-T-\sum_{w\ne w^+}\min(A_w,C_w).
\end{gathered}
\tag{255.1}
$$

Because $L\ge3$, a zero word has a label outside $\{0,n\}$,
so its minimum reward is zero and this formula for $\Gamma_y$
is exact. Oscillation is subadditive, whence
$0\le\Xi_y\le\Gamma_y/2$.

**Theorem 255.2 (Half-mass repair and the signed score identity).**
For every normalized $N$ law with its fixed decomposition,

$$
\sup_w\operatorname{TV}(p_w,p_w^{\mathrm{mid}})\le\mu/2.
\tag{255.2}
$$

The entire positive law is preserved. Sole-zero laws need not be
preserved. If $p$ is feasible at $e$, the midpoint law satisfies
every independent row at $e+\mu/2$, hence at the corresponding
clipped cap. Any bound in (254.6) can be used for $\mu$.
For a pair table the exact old-minus-midpoint score is

$$
\frac12\bigl(d_{ij}^y(u)-d_{ij}^y(v)\bigr).
\tag{255.3}
$$

In particular, $\Delta_N(y)\le\Delta_O(y)+\Xi_y$.
For the same full $\lambda,b,M$ of Theorem 253.2,

$$
F_y+S_y\le M\Delta_O(y)
                +\Xi_y\min\{M,4J_\lambda\},
\tag{255.4}
$$

with the sharper minimum (254.7) also available.

**Proof.** On either cell with $w_i=0$, a changed pair originally
emits one of $u,v$ and now emits the midpoint
$(e_u+e_v)/2$. Its TV distance is exactly $1/2$ when $u\ne v$,
zero otherwise. On $w_i=1$ it is unchanged. Convexity of TV
under the same mixture gives (255.2), uniformly in every word.
The event loss bound applies independently to base, correct and
union rows. Positive words visit only cell $11$, which is unchanged.

For scores, sum the $00$ contribution and subtract the $01$
contribution before estimating. The old-minus-new difference is
one half of the $00$ reward of $u$ minus that of $v$, plus one
half of the $01$ reward of $v$ minus that of $u$. This is exactly
(255.3), at most $\Xi_y[u\ne v]$. Constants and singletons
have zero difference. Every midpoint daughter is an $O$ table,
so the support bound follows columnwise. Integrating the signed
identity under the same $\lambda$, then bounding its changed mass
as in (253.2) or (254.7), proves (255.4). This is one signed
aggregate, not a sum of independently optimized positive pieces.
The common-seed construction preselects the daughter as well as
the whole table before replies, within the same $U$.
The original tail conclusion is again (251.9), since the positive
law is preserved. $\square$

**Proposition 255.3 (A sufficient score test and its limitation).**
If $\Delta_O(y)+\Xi_y\le1$, then $V=y,\theta=0$ is a valid
full certificate. The condition is not necessary.

**Proof.** Theorem 255.2 gives $\Delta_N(y)\le1$, and the
signed residual is zero. For nonnecessity use the score ray of
[Proposition 198.7](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_VI.md):
at $L=3$, its only nonzero coordinates are
$C_{110}=s$, $P_{010}=P_{100}=s$, $T=s$, with $s\ge0$.
The anchor score is $3s$. Partitioning these four words by any
query pair shows their maximum score is $3s$ in both catalogs,
so $\Delta_N=\Delta_O=0$. The signed cell differences in
(255.1) have maximal oscillation $s$, giving $\Xi=s/2$;
also $\Gamma=3s$. For $s>2$ the sufficient test fails while
$V=y,\theta=0$ still pays the input exactly. $\square$

**Proposition 255.4 (Finite lower boundary with positive-law preservation).**
On $B_3$, let $p=N(1,2;0,1,2,2)$. Among finite $O$ kernels
$q$ satisfying the additional restriction $q_{111}=p_{111}=e_2$,

$$
\inf_q\sup_{w\in B_3}\operatorname{TV}(p_w,q_w)=1/2.
\tag{255.5}
$$

**Proof.** In any deterministic decomposition of such a $q$,
every positive-weight table emits two at $111$. A table emitting
one at $011$ must query coordinate one: otherwise it has the
same transcript there as at $111$. On the zero at coordinate one
it stops, and therefore emits one also at $001$.
Consequently, after integrating,

$$
q_{001}(0)+q_{011}(1)\le1.
$$

The original laws at these two words are $e_0,e_1$, respectively.
If the uniform radius is $r$, both displayed probabilities are at
least $1-r$, so $2(1-r)\le1$ and $r\ge1/2$.
The midpoint law has radius at most $\mu/2=1/2$ on the whole
cube and preserves $p_{111}=e_2$, attaining the bound.
This is a finite approximation boundary under the named
positive-law-preservation condition. It is neither a lower bound
over unrestricted replacement laws nor an arbitrary-address original
$N/O$ separator. The original problem imposes no such preservation
condition on its competing stopped law. $\square$

## 256. A mixed-row zero-cost cut at every original horizon

**Definition 256.1 (A complete mixed event score on eight coordinates).**
The following table specifies $y_*$ as word, event and nonnegative
integer weight. A singleton $\{n\}$ is a correct-row weight;
$\{0,n\}$ is an independent union-row weight; the positive-word
$\{0\}$ is the terminal base weight. All unspecified scores vanish,
and their constraints remain in the full matrix. Coincident words
with different events are separate rows. For $L>8$, append
$1^{L-8}$ to each word.

| word | event | weight |
|---|---|---:|
| $00101100$ | $\{0,1\}$ | 3 |
| $00101111$ | $\{0,1\}$ | 2 |
| $00110100$ | $\{0,1\}$ | 3 |
| $00110110$ | $\{0,1\}$ | 3 |
| $00111000$ | $\{0,1\}$ | 6 |
| $00111011$ | $\{0,1\}$ | 1 |
| $01001111$ | $\{0,1\}$ | 4 |
| $01010101$ | $\{0,1\}$ | 9 |
| $01011010$ | $\{0,1\}$ | 5 |
| $01100101$ | $\{0,1\}$ | 3 |
| $01101000$ | $\{0,1\}$ | 3 |
| $01101010$ | $\{0,1\}$ | 1 |
| $01101011$ | $\{0,1\}$ | 2 |
| $10001100$ | $\{0,2\}$ | 9 |
| $10010110$ | $\{0,2\}$ | 3 |
| $10011000$ | $\{0,2\}$ | 6 |
| $10100001$ | $\{2\}$ | 3 |
| $10100110$ | $\{0,2\}$ | 4 |
| $10101110$ | $\{2\}$ | 2 |
| $10110010$ | $\{0,2\}$ | 5 |
| $10110100$ | $\{2\}$ | 3 |
| $10111010$ | $\{2\}$ | 4 |
| $10111100$ | $\{2\}$ | 6 |
| $11000110$ | $\{0,3\}$ | 2 |
| $11000111$ | $\{3\}$ | 11 |
| $11001010$ | $\{0,3\}$ | 3 |
| $11001101$ | $\{3\}$ | 1 |
| $11001110$ | $\{3\}$ | 1 |
| $11010000$ | $\{0,3\}$ | 3 |
| $11010010$ | $\{0,3\}$ | 1 |
| $11010100$ | $\{3\}$ | 1 |
| $11011000$ | $\{3\}$ | 11 |
| $11011101$ | $\{3\}$ | 11 |
| $11100000$ | $\{4\}$ | 8 |
| $11100000$ | $\{0,4\}$ | 9 |
| $11100101$ | $\{4\}$ | 1 |
| $11101011$ | $\{4\}$ | 1 |
| $11101101$ | $\{4\}$ | 9 |
| $11101110$ | $\{4\}$ | 17 |
| $11110000$ | $\{5\}$ | 12 |
| $11110010$ | $\{5\}$ | 6 |
| $11110100$ | $\{5\}$ | 15 |
| $11110111$ | $\{5\}$ | 12 |
| $11111000$ | $\{6\}$ | 27 |
| $11111010$ | $\{6\}$ | 15 |
| $11111011$ | $\{6\}$ | 3 |
| $11111100$ | $\{7\}$ | 33 |
| $11111101$ | $\{7\}$ | 12 |
| $11111110$ | $\{8\}$ | 45 |
| $11111111$ | $\{0\}$ | 27 |

These are proof weights, not probabilities on actual sources or
probability budgets of acquisitions. Their totals are

$$
\begin{gathered}
A=0,\quad K=387,\quad\sum_wP_w=90,\quad T=27,\\
(\beta_1,\ldots,\beta_8)=(0,18,36,36,45,45,45,45),\qquad
\beta_n=0\ (n>8),\quad W=135.
\end{gathered}
\tag{256.1}
$$

**Lemma 256.2 (Full-label support certificate).**
$B_N(y_*)=B_O(y_*)=135$, so $\Delta_N(y_*)=\Delta_O(y_*)=0$.

**Proof.** For each queried pair $i<j$, compute

$$
g_{ij}^{uv}(r)=\sum_{(w,E,k):\,(w_i,w_j)=(u,v)}k[r\in E]
\qquad(r\in J_L).
\tag{256.2}
$$

The four maxima, in $00,01,10,11$ order, are as follows.
Every $i<j\le6$ gives $(18,27,45,45)$; every $i<7=j$
gives $(27,18,45,45)$; for $j=8$ the complete list is

| $i$ | $00$ | $01$ | $10$ | $11$ |
|---:|---:|---:|---:|---:|
| 1 | 24 | 21 | 45 | 27 |
| 2 | 42 | 3 | 45 | 45 |
| 3 | 32 | 23 | 45 | 35 |
| 4 | 34 | 12 | 45 | 37 |
| 5 | 33 | 12 | 45 | 36 |
| 6 | 42 | 3 | 45 | 45 |
| 7 | 42 | 12 | 45 | 36 |

Each entry is the maximum of the nine explicit finite sums
(256.2); labels above eight have zero reward. This supplies a
finite arithmetic certificate for all 28 pairs and all their labels.
Each row sum is at most 135. Empty, singleton and repeated schedules
coarsen a distinct-pair partition and cannot increase its maximal
score; reversal merely permutes its cells. At larger $L$, every
scored high bit is fixed to one, so querying it adds no partition
information and is covered by the same coarsening argument.
The stopped anchor attains 135. Since $O\subseteq N$, both support
values equal this number. Directly summing the score at the anchor
gives $W=135$, completing the certificate. $\square$

**Theorem 256.3 (All-horizon original necessary inequality).**
For every entire positive monotone vanishing sequence and every
original $A\in\mathcal N_2$, hence every $A\in\mathcal O_2$,

$$
43e_a(A)\ge2a_2+4a_3+4a_4+5(a_5+a_6+a_7+a_8)-2.
\tag{256.3}
$$

There is no hypothesis on its actual active horizon or tails.
Moreover, for every $L\ge8$, $(b,e)\in H_L$ and the same arbitrary
finite full feasible $N$ vector $\lambda$,

$$
43e\ge2b_2+4b_3+4b_4+5(b_5+b_6+b_7+b_8)-2,
\tag{256.4}
$$

independently of its conic mass.

**Proof.** The target score on $B_8$ is
$117+18a_2+36a_3+36a_4+45\sum_{5}^8a_i$.
Here the union events contribute 90 and the positive event 27.
A cap-$e$ normalized law has score at least that quantity minus
$387e$. Lemma 256.2 bounds it above by 135. Subtracting 135
and dividing by nine proves (256.3) for finite laws. This argument
uses the union events themselves, including the late union events,
without substituting sums of singleton inequalities.

For a conic law, use the same $y_*$ and $\lambda$:

$$
F_{y_*}(b,e)\le y_*\cdot G_N\lambda
 =\sum_D\lambda_Dy_*\cdot(z_D-\mathbf r)\le0.
$$

Expanding its left side gives nine times the right-minus-left
expression in (256.4). No mass-dependent allowance is needed.

For an original competitor with error $r\in(0,1]$, Theorem 110.2
supplies a finite feasible representative at its actual horizon.
If that horizon exceeds eight, fix all higher input bits to zero,
project labels above eight to zero and delete those fixed high
observations. Low first-zero targets are fixed by the projection;
the low all-positive target projects to base. If the horizon is
below eight, add ignored input coordinates. A new first zero has
$a_n\le r$, and the old positive row gives
$\operatorname{TV}=\max\{1-p_{w^+}(0),a_n\}\le r$.
The all-positive row is also retained. These are the exact
projection and extension operations proved in
[Theorem 117.2](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION.md#117-a-uniform-second-head-necessary-certificate).
They retain one preselected hard-two mixture. Thus the eight-word
score proof applies without bounding original addresses or outputs.
For error zero, apply the positive-cap conclusion for every $r>0$
and let $r\downarrow0$. Error one is included; larger alleged
caps need no additional argument. $\square$

**Corollary 256.4 (An exactly paid zero-cost ray).**
Every input $s y_*$, $s\ge0$, has the full certificate
$V=s y_*,\theta=0$. It supplies the half-space (256.4) on $H_N$.

**Proof.** Both costs vanish by Lemma 256.2 and the residual is zero.
The statement covers this entire mixed-row ray, and makes no
assertion about all other unit-$O$ inputs. $\square$

## 257. An exact two-parameter eight-active original family

**Theorem 257.1 (Whole-law construction and an attained optimum).**
Let

$$
\frac12\le t\le\frac35,\qquad t\le h\le t+\frac1{100},\qquad
e_*(t)=\frac{30t-2}{43}.
\tag{257.1}
$$

For every entire profile

$$
a=(h,t,t,t,t,t,t,t,a_9,a_{10},\ldots),\qquad
e_*\ge a_9\ge a_{10}\ge\cdots>0,\quad a_n\longrightarrow0,
\tag{257.2}
$$

both original hard-two infima are attained and equal $e_*$.
Both classes are feasible at a positive closed cap $\varepsilon$
exactly when $\varepsilon\ge e_*$. The actual active length at
$e_*$ is eight, and every actual tail has error exactly $e_*$,
including $a_9=e_*$.

**Definition 257.2 (The two complete endpoint laws).** The following
tables give unnormalized label counts on stopped cells $0,10,11$.
In each row the three cell totals agree, giving the schedule mass
after division by its displayed denominator. The sum of those
schedule masses is one. An entry $c e_r$ means count $c$ at label
$r$, and every omitted entry or schedule is zero.

At $t=1/2$, divide all counts by $1032$.

| schedule | $0$ cell | $10$ cell | $11$ cell |
|---|---|---|---|
| $(1,2)$ | $120e_{1}$ | $120e_{2}$ | $68e_{0}+36e_{3}+16e_{8}$ |
| $(1,3)$ | $84e_{0}$ | $84e_{3}$ | $68e_{0}+16e_{7}$ |
| $(1,4)$ | $68e_{1}$ | $68e_{4}$ | $68e_{0}$ |
| $(1,5)$ | $51e_{1}$ | $51e_{5}$ | $51e_{0}$ |
| $(1,6)$ | $25e_{0}$ | $25e_{6}$ | $25e_{0}$ |
| $(2,3)$ | $25e_{0}+59e_{2}$ | $84e_{3}$ | $68e_{0}+16e_{7}$ |
| $(2,4)$ | $68e_{0}$ | $68e_{4}$ | $68e_{0}$ |
| $(2,5)$ | $51e_{0}$ | $51e_{5}$ | $51e_{0}$ |
| $(2,6)$ | $25e_{2}$ | $25e_{6}$ | $25e_{0}$ |
| $(3,4)$ | $68e_{0}$ | $68e_{4}$ | $68e_{0}$ |
| $(3,5)$ | $51e_{0}$ | $51e_{5}$ | $51e_{0}$ |
| $(3,6)$ | $25e_{0}$ | $25e_{6}$ | $25e_{0}$ |
| $(4,5)$ | $51e_{0}$ | $51e_{5}$ | $51e_{0}$ |
| $(4,6)$ | $25e_{0}$ | $25e_{6}$ | $25e_{0}$ |
| $(4,7)$ | $68e_{0}$ | $68e_{7}$ | $68e_{8}$ |
| $(5,6)$ | $104e_{0}$ | $104e_{6}$ | $8e_{0}+40e_{7}+56e_{8}$ |
| $(5,7)$ | $6e_{0}$ | $6e_{7}$ | $6e_{8}$ |
| $(6,7)$ | $58e_{0}$ | $58e_{7}$ | $58e_{8}$ |

At $t=3/5$, divide all counts by $1290$.

| schedule | $0$ cell | $10$ cell | $11$ cell |
|---|---|---|---|
| $(1,2)$ | $135e_{1}$ | $135e_{2}$ | $64e_{0}+71e_{8}$ |
| $(1,3)$ | $70e_{0}$ | $70e_{3}$ | $64e_{0}+6e_{5}$ |
| $(1,4)$ | $102e_{1}$ | $102e_{4}$ | $64e_{0}+38e_{7}$ |
| $(1,5)$ | $81e_{1}$ | $81e_{5}$ | $64e_{0}+17e_{7}$ |
| $(1,6)$ | $34e_{1}$ | $34e_{6}$ | $34e_{0}$ |
| $(2,3)$ | $95e_{2}$ | $95e_{3}$ | $64e_{0}+15e_{5}+16e_{7}$ |
| $(2,4)$ | $64e_{0}$ | $64e_{4}$ | $64e_{0}$ |
| $(2,5)$ | $64e_{0}$ | $64e_{5}$ | $64e_{0}$ |
| $(2,6)$ | $64e_{2}$ | $64e_{6}$ | $34e_{0}+30e_{7}$ |
| $(3,4)$ | $128e_{0}$ | $128e_{4}$ | $64e_{0}+64e_{7}$ |
| $(3,5)$ | $64e_{3}$ | $64e_{5}$ | $64e_{0}$ |
| $(3,6)$ | $34e_{3}$ | $34e_{6}$ | $34e_{0}$ |
| $(3,7)$ | $31e_{3}$ | $31e_{7}$ | $31e_{8}$ |
| $(4,5)$ | $64e_{0}$ | $64e_{5}$ | $64e_{0}$ |
| $(4,6)$ | $34e_{0}$ | $34e_{6}$ | $34e_{0}$ |
| $(4,7)$ | $30e_{0}$ | $30e_{7}$ | $30e_{8}$ |
| $(5,6)$ | $128e_{0}$ | $128e_{6}$ | $34e_{0}+94e_{8}$ |
| $(6,7)$ | $68e_{0}$ | $68e_{7}$ | $68e_{8}$ |


These tables specify full probability laws. Explicitly, for a row
with positive common count $m$ and cell count vectors $c^0,c^{10},c^{11}$,
give whole table $O(i,j;r,s,u)$ probability

$$
\frac{c^0(r)c^{10}(s)c^{11}(u)}{D_0m^2},
\tag{257.3}
$$

where $D_0$ is that endpoint's denominator. Summing over two
labels recovers each count divided by $D_0$, and the row's total
probability is $m/D_0$. A zero row would be omitted. This finite
coupling fixes all terminal choices before replies, using one seed.
It imposes no independence requirement on the acquisition model.

**Proof of Theorem 257.1.** Denote the endpoint laws by $q^-$ at
$t=1/2$ and $q^+$ at $t=3/5$. Their denominators are 1032 and
1290. Every table count is nonnegative; the common row totals sum
to these denominators. All numerical exhaustion labels are later
than both queried indices. A numerical triple emits its contained
first-zero label regardless of subsequent zeros, and the listed
zero-first transfers depend only on their first queried index.
Thus direct summation of these same cell counts gives constant
correct probabilities on every first-zero class, with numerator
vectors

$$
(239,204,204,204,204,204,204,204),\qquad
(352,294,294,294,294,294,294,294).
\tag{257.4}
$$

This verifies all multiple-zero suffixes at once, rather than
inferring their probabilities from sole-zero values.

For the base rows put $k=w_1+w_2+w_3+w_4$, $u=w_5$ and
$v=w_6$. The base polynomials of these very same laws are

$$
\begin{split}
1032q^-_w(0)={}&709-144k+35w_1+34k(k-1)\\
 &+(-110+51k)u+(-58+25k)v+8uv,\\
1290q^+_w(0)={}&650-128k+58w_1+32k(k-1)\\
 &+(-128+64k)u+(-68+34k)v+34uv.
\end{split}
\tag{257.5}
$$

Bits seven and eight do not occur in the base polynomials.
These expressions follow by summing, for each row, its first base
count times $1-w_i$, its middle base count times $w_i(1-w_j)$,
and its exhaustion base count times $w_iw_j$.
For each first-zero class, the exact minimum base numerators are

$$
\begin{array}{c|rrrrrrrr}
n&1&2&3&4&5&6&7&8\\\hline
q^-&481&516&516&516&576&670&720&720\\
q^+&458&516&516&516&580&708&810&810.
\end{array}
\tag{257.6}
$$

Here is an exhaustive finite derivation of these minima from (257.5).
For class one, $w_1=0$ and $k=0,1,2,3$; for class two,
$w_1=1$ and $k=1,2,3$; for class three, $w_1=1$ and $k=2,3$;
for class four, $w_1=1,k=3$. In all these cases minimize over
the four pairs $(u,v)\in\{0,1\}^2$. For class five,
$w_1=1,k=4,u=0$ and minimize over $v$; for class six,
$w_1=1,k=4,u=1,v=0$; for classes seven and eight,
$w_1=1,k=4,u=v=1$. Substitution gives exactly (257.6), with
each permitted combination attainable in its class. These finitely
specified polynomial minima prove the bounds for every word.

For $n\ge2$, (257.4) equals $t-e_*$ at both endpoints, while
(257.6) is at least $1-t$. Therefore the correct row holds with
equality and the union row has probability at least $1-e_*$.
The base singleton demand $1-t-e_*$ also holds. The positive
base values are $720/1032$ and $810/1290$, respectively, equal
to $1-e_*$ at $e_*=13/43,16/43$.

At class one define the endpoint correct excesses
$\gamma^-=35/1032$ and $\gamma^+=29/645$.
Their correct probabilities are $t-e_*+\gamma^\pm$ and
their exact minimum base probabilities are $1-t-\gamma^\pm$.
Both excesses lie strictly above $1/100$ and below $e_*$.
For $h=t+d$, $0\le d\le1/100$, correctness is at least
$h-e_*$, and base is at least $1-h-e_*$ because
$\gamma^\pm\le e_*+d$. Their sum is at least $1-e_*$
independently of $h$. Thus all three rows hold for the full
closed head interval at each endpoint.

For general $t$ mix the whole endpoint laws with weight
$\tau=10(t-1/2)$ on $q^+$ and $1-\tau$ on $q^-$.
For any fixed $d\in[0,1/100]$, each target coordinate, each
demand, and $e_*(t)$ is the same affine mixture of its endpoint
values. Hence this one common law satisfies every row on the
entire closed rectangle (257.1), not just at sampled parameters.
Its correct probability at each class $n\ge2$ is exactly $t-e_*$,
and its positive base is exactly $1-e_*$. Proposition 251.4
realizes it and its counted $N$ completion with one common seed.
Every actual tail has error $\max\{e_*,a_n\}=e_*$.
Since $t>e_*>0$, its active length is eight.

The all-horizon lower cut (256.3) reduces on this profile to
$43e_a(A)\ge30t-2$, for every original $N$ competitor and
hence every $O$ competitor. It matches the constructed $e_*$,
so both infima are attained there. At any larger positive cap the
same original law is feasible, regardless of its new active length;
at a smaller cap the lower cut excludes feasibility. All tail and
parameter equalities are included. $\square$

**Corollary 257.3 (The regional same-profile full-score relation).**
Each point (257.1) lies in $H_8$ and has a full mass-one $O$
vector $\lambda^O$ satisfying $G_O\lambda^O\ge h$. For every
full $y\ge0$, $F_y(b,e_*)\le\Delta_O(y)$. Consequently no
unit-$O$ score and full feasible $N$ vector of mass $M\ge1$
at that same point can have $F_y>M$.

**Proof.** Order, $b_2=b_3$ and $b_8>e_*$ hold. Also
$E=6t-9e_*=(18-12t)/43\ge0$ and
$h+E\le(31t+18)/43+1/100<1$ on the closed range.
Theorem 257.1 supplies all full rows for one mass-one law.
Weak duality gives $F_y\le y\cdot G_O\lambda^O\le\Delta_O(y)$.
For a unit input the latter is at most one, hence at most $M$.
This relation is pointwise on this family; it supplies no uniform
$\sigma_H$ payer for arbitrary profiles. $\square$

**Proposition 257.4 (Concrete distinctions from named suppliers).**
The cut (256.3) excludes some profiles passing the two named
head-bound families, and the two-parameter law is outside the
following direct previously specified constructions.

**Proof.** For the cut diagnostic, take $a_1=\cdots=a_8=1/2$,
$e=3/10$, and $a_{8+j}=(3/10)2^{1-j}$. This point is in
$H_8$, with $E=3/10$. The residual necessary bound of
Theorem 113.2 gives $D_3=6/5\le7/5$.
The divided slack of Theorem 117.2 at $4\le m\le8$ is
$3(m+1)/10-((m-2)/2-(m-3)/(2(m-2)))$; its minimum is
$7/60$. For $m>8$, tail amplitudes at most $3/10$ bound that
slack below by $-3/10+(m-3)/(2(m-2))\ge7/60$.
Thus every named first- and second-head cut holds, whereas the
new cut requires $43(3/10)\ge13$, which is false.
The actual optimum here is $13/43$ by Theorem 257.1, exceeding
$3/10$ by $1/430$. This point is outside $H_N$ by (256.4),
so it is not a same-feasible-profile separator.

The score has union weight nine in each of classes three and four.
It is outside the early-union restriction of Section 207 and the
pure-correct restriction of Proposition 198.4. Its class-three
correct and union supports differ, so it is not the common-product
form of Proposition 198.2. These are literal score-class distinctions.

For the family, the high-flat eight-coordinate capacity corollary
of Section 245 starts at $t=139/157$, above the entire range
$t\le3/5$ here. For a direct proper-core residual construction
of Sections 173–174 with core length $2\le m\le7$, the flat
late residuals give $E_{\mathrm{res}}=2(t-e_*)>e_*$, because
$3e_*<2t$. This fails its positive residual-subtraction test
$e_*>E_{\mathrm{res}}$. The separate $W=1$ endpoint requires
unit head amplitudes and also does not apply. For the fixed-core
family of Section 187, $E/(1-a_2)=2/3$, whereas here this ratio
lies in $[24/43,27/43]$, strictly below $2/3$.
These computations distinguish named direct sufficient domains;
they assert neither impossibility of other representations nor
exclusion of every historical composition or future constructor.
The general terminal coupling and suffix-polynomial methods of
Sections 176 and 178 remain reused methods. $\square$

## 258. Signed event transfer, actual slack and universal common input maps

**Definition 258.1 (The schedule graph and its simultaneous map).**
Fix a normalized whole-table mixture $\pi$. Its directed support
graph $G$ has edge $i\to j$ precisely when its schedule $(i,j)$
has positive mass, with $i<j$. Retain also the set of positive-mass
singleton schedules. Define a proof map $F=f_G(w)$ by

$$
F_j=w_j\vee[\exists i\to j\text{ with }w_i=0].
\tag{258.1}
$$

All updates use the original $w$, simultaneously. The map preserves
the first zero, fixes $w^+$ and is idempotent. It is a proof device,
not an operational use of unqueried answers.

For an event $E\subseteq J_L$, define the signed transfer
$C_E(w)$ by summing the following terms with the weights of the
same original tables:

$$
\begin{array}{c|c|c}
\text{schedule}&\text{condition}&\text{term}\\\hline
(i)&w_i=0,\ F_i=1&[\ell_1\in E]-[\ell_0\in E]\\
(i,j)&w_i=0,\ F_i=1&[\ell_{11}\in E]-[\ell_{01}\in E]\\
(i,j)&w_i=1,\ w_j=0,\ F_j=1&[\ell_{11}\in E]-[\ell_{10}\in E].
\end{array}
\tag{258.2}
$$

No other term is included. Terms are signed and aggregated before
taking any positive part. On a row $E$ at $w$, let $d_E(w)$
be its demand in (251.1) and put
$s_E(F)=p_F(E)-d_E(F)$.

**Theorem 258.2 (Exact transfer and exact extra cap).**
For the endpoint repair $\bar p$ of this fixed $\pi$,

$$
\bar p_w(E)=p_{f_G(w)}(E)-C_E(w)
\qquad\text{for every }w\in B_L,\ E\subseteq J_L.
\tag{258.3}
$$

If $p$ is feasible at cap $e$, the exact extra cap required by
this fixed repair is

$$
\begin{split}
\rho_G&=\max\{0,\max_{\text{all independent rows at }w}
                        (C_E(w)-s_E(f_G(w)))\}\\
 &=\left(\max_{w\in B_L}\operatorname{TV}(\bar p_w,\eta_w)-e\right)_+.
\end{split}
\tag{258.4}
$$

Here $\eta_w=(1-a_n)e_0+a_ne_n$ on $\Omega_n$ and
$\eta_{w^+}=e_0$. Thus this repair is same-cap feasible if and
only if $C_E(w)\le s_E(f_G(w))$ at every independent row.

**Proof.** Bits can only change from zero to one. If $n$ is
the first zero, no earlier bit is zero, and every predecessor of
$n$ is earlier. Thus $F_n=0$ and the first zero is preserved.
The positive word is fixed. If a bit remains zero, all its
predecessors were originally one, and those predecessors remain
one under $F$. Applying the update again creates no new one.
This proves idempotence.

Now check each original table against its repaired output at $w$.
A singleton can differ from its output at $F$ only when its bit
flips, giving the first term of (258.2). For an edge $(i,j)$,
if $w_i=0,F_i=0$, the edge forces $F_j=1$, so the original
table at $F$ visits $01$, exactly the repaired first cell at $w$.
If $w_i=0,F_i=1$, the original visits $11$ and the repair visits
its old $01$, giving the second term. If $w_i=1,w_j=0,F_j=1$,
the original visits $11$ and the repair visits $10$, giving the
third term. If $w_i=1,w_j=0,F_j=0$, both visit $10$; if
$w_i=w_j=1$, both visit $11$. Constants have no difference.
These cases exhaust every cell and every legal label. Integrating
their indicator differences proves (258.3) for every event.

The demand at $F$ equals that at $w$, because its first zero is
the same. Consequently
$\bar p_w(E)-d_E(w)=s_E(F)-C_E(w)$ exactly. The maximum
deficit over the three independent events and the positive event
equals the maximum TV excess over cap by (251.2).
Taking its positive part proves (258.4), including ties and negative
singleton demands. The union event is a separate row throughout.
The displayed maximum is after all signed transfers have been
summed under one realization. $\square$

**Theorem 258.3 (Universal common-map criterion).**
Fix the positive schedule support, including its singleton set.
There exists one map $f:B_L\to B_L$ such that

$$
\bar D(w)=D(f(w))\quad\text{for every supported schedule, every
terminal-label assignment on it, and every }w
\tag{258.5}
$$

if and only if $G$ has no directed two-edge path, every vertex
has indegree at most one, and no positive singleton is placed
at a vertex of positive indegree. Equivalently, its nontrivial
components are disjoint outward stars and its positive singletons
avoid their leaves. In that case $f_G$ supplies such a map.

**Proof.** Arbitrary terminal labels distinguish any two distinct
transcript cells. Hence for each edge $i\to j$, (258.5) forces

$$
f_i(w)=w_i,\qquad
f_j(w)=\begin{cases}1,&w_i=0,\\ w_j,&w_i=1.\end{cases}
\tag{258.6}
$$

Indeed, for $w_i=0$ the repaired output is the old $01$ cell
for every label assignment, forcing input cell $01$ at $f(w)$;
for $w_i=1$ the old cell is already $1w_j$ and must be preserved.
A positive singleton at $j$ likewise forces $f_j(w)=w_j$.
If $k\to i\to j$, choose $w_k=w_i=0$. The incoming edge
requires $f_i=1$ and the outgoing edge requires $f_i=0$.
If two distinct parents $i,k$ enter $j$, choose $w_i=1,w_k=0,
w_j=0$. The two equations require $f_j=0$ and $f_j=1$.
A singleton at a leaf contradicts its incoming edge when both
parent and leaf are zero. These choices prove necessity.

Under the stated graph conditions, every edge leaves an indegree-zero
root and enters its unique leaf. Formula (258.1) fixes roots and
all singleton coordinates; it changes a leaf only when its unique
parent is zero. Thus it satisfies every equation (258.6) and every
singleton condition simultaneously. All original and repaired cells
then agree, for every choice of their labels. This proves sufficiency.

The quantifier over terminal labels is essential. This criterion
is not an iff for a particular kernel, where equal labels or
signed cancellations may remove discrepancies. It is also not an
iff for the existence of an arbitrary replacement $O$ kernel in
the same cap slice. Those unrestricted replacements need not be
given by a common input map at all. $\square$

**Corollary 258.4 (Optional same-cap affordability on the same conic data).**
Fix the same full $\lambda,b,M\ge1$ as in Theorem 253.2 and
normalize at the blended profile (253.6). Form its actual
$C_E$ and slacks $s_E(f_G(w))$. If every $C_E\le s_E$, its
repaired same-mass vector $\lambda^\sharp$ satisfies
$G_O\lambda^\sharp\ge h(b,e)$, and
$F_y(b,e)\le M\Delta_O(y)$ for every full score. In general,

$$
F_y(b,e)\le M\Delta_O(y)
 +M\sum_{\text{all rows }(w,E)}y_{w,E}
                [C_E(w)-s_E(f_G(w))]_+.
\tag{258.7}
$$

For the universal common-map schedules of Theorem 258.3,
$C_E=0$ at every row, so the same-cap condition holds.

**Proof.** Equation (258.3) says that the repaired probability of
each row is at least its normalized demand minus its exact
positive deficit. Multiply by $M$. Since
$M(d(x,e_x)-\mathbf r)=h(b,e)$ and the repaired vector has
mass $M$, the full row inequalities give the first assertion and,
after multiplication by the same nonnegative $y$, (258.7).
Every repaired column is in the full $O$ catalog, so its total
excess is at most $M\Delta_O(y)$. For a universal common map,
all transcript matches in the proof make (258.2) identically zero;
the original law at $f_G(w)$ is feasible because the first zero
is preserved. These are optional sufficient mechanisms, not
restrictions on the original competitors or certificate scores.
$\square$

The eligible reset of
[Definitions 220.3–220.5](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XIII.md#2202-eligible-coordinates-and-the-original-bad-pair-graph)
acts on a dual score: its wordwise hypothesis $C_w\le A_w$
on reset zero faces ensures contraction of each schedule support,
while preserving the quotient and baseline. Its graph records bad
score pairs. Equations (258.2)–(258.4) instead act on one primal
table distribution, use no such score domination, and compare signed
transcript changes with that distribution's actual event slacks.
The graph in Theorem 258.3 records positive schedules and its iff
quantifies all terminal assignments. These are different specified
maps and hypotheses; the dual reset is not re-proved by the primal
transfer identity.

## 259. Matched scalar summaries and a positive-mass same-cap repair

**Proposition 259.1 (Matched summaries do not determine repair payment).**
Even with the same target, cap and schedule graph, the values
$D,\delta,\mu,s_0,s_1,\ldots,s_L$ do not determine the extra
cap of the fixed endpoint repair.

**Proof.** Take $L=3$, $a=(1,1,1)$ and $e=3/10$.
The following two full mixtures use pair labels in $00,01,10,11$
order. All omitted tables have zero mass.

First mixture.

| mass | schedule | $00,01,10,11$ labels |
|---|---|---|
| $3/10$ | $(1,2)$ | $(1,1,2,3)$ |
| $1/5$ | $(1,2)$ | $(1,1,2,0)$ |
| $1/5$ | $(1,3)$ | $(1,1,3,0)$ |
| $1/10$ | $(2,3)$ | $(2,2,3,0)$ |
| $1/10$ | $(1,2)$ | $(1,0,2,0)$ |
| $1/10$ | $(1,3)$ | $(1,0,3,0)$ |

Second mixture.

| mass | schedule | $00,01,10,11$ labels |
|---|---|---|
| $3/10$ | $(1,2)$ | $(1,1,2,0)$ |
| $1/10$ | $(1,2)$ | $(1,1,2,3)$ |
| $1/10$ | $(1,2)$ | $(1,2,2,3)$ |
| $1/5$ | $(1,3)$ | $(1,1,3,0)$ |
| $1/10$ | $(1,3)$ | $(1,2,3,0)$ |
| $1/10$ | $(2,3)$ | $(2,2,3,0)$ |
| $1/10$ | $(2,3)$ | $(2,2,3,1)$ |


Both masses sum to one, and both have graph edges
$1\to2,1\to3,2\to3$. The complete word probabilities are
as follows; a dash at the positive word means there is no $n$.

| word | first $p_0$ | first $p_n$ | first $\bar p_0$ | first $\bar p_n$ | second $p_0$ | second $p_n$ | second $\bar p_0$ | second $\bar p_n$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $000$ | $0$ | $9/10$ | $1/5$ | $7/10$ | $0$ | $4/5$ | $0$ | $3/5$ |
| $001$ | $1/10$ | $4/5$ | $1/5$ | $7/10$ | $0$ | $7/10$ | $0$ | $3/5$ |
| $010$ | $1/10$ | $4/5$ | $1/5$ | $7/10$ | $0$ | $7/10$ | $0$ | $3/5$ |
| $011$ | $3/10$ | $7/10$ | $3/10$ | $7/10$ | $1/10$ | $7/10$ | $1/10$ | $7/10$ |
| $100$ | $0$ | $7/10$ | $0$ | $7/10$ | $0$ | $7/10$ | $0$ | $7/10$ |
| $101$ | $3/10$ | $7/10$ | $3/10$ | $7/10$ | $3/10$ | $7/10$ | $3/10$ | $7/10$ |
| $110$ | $3/10$ | $7/10$ | $3/10$ | $7/10$ | $3/10$ | $7/10$ | $3/10$ | $7/10$ |
| $111$ | $7/10$ | — | $7/10$ | — | $7/10$ | — | $7/10$ | — |

The correct and independent union demands are $7/10$, the base
demand is $-3/10$, and the positive base demand is $7/10$.
Every original row in this complete table satisfies its demand.
Both original laws have error exactly $3/10$, positive base
$7/10$ and sole-zero correct probabilities $7/10$.
Thus $s_0=s_1=s_2=s_3=0$, $\delta=D=1/5$, and exactly two
changed tables of mass $1/10$ each give $\mu=1/5$.

The first repaired law satisfies all rows at $3/10$. The second
has correct and union probabilities $3/5$ at $000,001,010$,
so its exact error is $2/5$ and its exact extra cap is $1/10$.
At $000$, $f_G(000)=011$. In the second mixture the $23$
table with exhaustion label one contributes $1/10$ to
$C_{\{1\}}(000)$, while $s_{\{1\}}(011)=0$.
This exhibits the unpaid transfer in the exact identity (258.4).
The exhaustion label is an earlier unqueried label and remains
legal. No scalar-summary estimate can erase it.

Append $a_{3+j}=(3/10)2^{1-j}$. Both original $N$ laws retain
error $3/10$; both repairs keep the positive law, so every actual
tail has exact error $3/10$, including $a_4=e$. Actual low-word
witnesses give the stated $2/5$ error of the second repair.
A different stopped plateau law is feasible at $3/10$ by the
existing suppliers. This example concerns the fixed repair and
does not separate the original feasibility classes. $\square$

**Proposition 259.2 (Nonstopped laws with a positive changed mass and no extra cap).**
Let $L\ge3$, $0<e<t\le1$, $c=t-e$, and choose

$$
\gamma>c,\qquad \gamma+(L-2)c\le e.
\tag{259.1}
$$

For $r\in\{3,\ldots,L\}$ and $a_i=t$ on the finite prefix,
use mass $c$ on each constant numerical output $n\ne2$,
mass $B_0=1-(L-1)c-\gamma$ on constant zero, and mass
$\gamma$ on $N(1,2;r,0,2,0)$.
This law is cap-$e$ feasible, is not a stopped kernel, has changed
mass $\mu=\gamma>0$, and its fixed endpoint repair is feasible
at the same cap.

**Proof.** The weights sum to one and
$B_0\ge1-c-e=1-t\ge0$ by (259.1).
For the original law, correct probability is $c$ in class one,
$\gamma$ in class two, and $c$ in every later class. These are
at least $t-e=c$. The repair keeps these correct probabilities:
it merely changes the exceptional $00$ output from $r$ to zero,
which can occur only in first-zero class one. In either law, base
probability is at least $B_0\ge1-t$, which is stronger than the
base singleton demand. The minimum union probabilities in the
three types of classes are, respectively,
$B_0+c$, $B_0+\gamma$, and $B_0+\gamma+c$.
Their deficits from one are bounded by
$(L-2)c+\gamma$, $(L-1)c$, and $(L-2)c$.
The first is at most $e$ by hypothesis; the second is strictly
less than the first because $\gamma>c$; the third is also at
most $e$. The positive base is $B_0+\gamma$ and satisfies
the same bound. Thus every independent row holds for both laws,
including every suffix. Its graph is the single edge $1\to2$,
with no singletons, so Theorem 258.3 also explains this same-cap
repair.

To verify nonstoppedness of the original law, use its unique
multilinear coefficients at output $r$. The exceptional contribution
is $\gamma(1-w_1)(1-w_2)$, added to its constant mass $c$.
Thus its constant coefficient at that label is $c+\gamma$,
its two linear coefficients are $-\gamma,-\gamma$ and its
quadratic coefficient is $\gamma$. In the coefficient criterion
of Theorem 109.1, $V_1(r)=V_2(r)=0$ and
$h_1(r)=h_2(r)=\gamma$, giving $H(r)=2\gamma>c+\gamma$.
The vector inequality fails, so this normalized kernel is not in
$\mathscr O_L$ even though its endpoint repair is cap feasible.

For a concrete original instance take $L=7$, $t=4/5$, $e=7/10$,
$c=1/10$, $\gamma=1/5$, $r=3$, $B_0=1/5$.
Here $D=2$. Append any positive monotone vanishing actual tail
bounded by $7/10$. The positive nonbase mass is $3/5$, so
(251.9) gives tail error $\max\{3/5,a_n\}\le7/10$ for both
laws, including equality tails. This verifies nonvacuity of the
transfer criterion with $\mu>0$ and a genuinely nonstopped
starting kernel. The old amplitude feasibility on this profile
receives no additional comparison content. $\square$

## 260. Original regression, reference frame and the remaining universal obligation

**Proposition 260.1 (A legal earlier unqueried output is changed and paid).**
For the actual source $(r,g)=(19,436)$,
$F_{19}=4181$ and $N=1+4181\cdot436=1822917$.
Its first four prime replies are $0100$.
The legal table $N(3,4;1,0,0,0)$ emits the earlier unqueried
label one there. Its endpoint repair emits zero there, has changed
mass one as a pure table, and has counting defect two.

**Proof.** The permitted window is $419\le g\le836$ and 19
is prime. The displayed integer is odd, divisible by three and
divisible by neither five nor seven. At this word, queried bits
three and four are $00$, whose old label is one and repaired
label is the old $01$ label zero. Its sole-zero correct count is
zero, positive base count one, so $d_D=3-1=2$.
The same calculations include this table in every applicable
full-catalog bound; none removes its earlier label or treats
the change as free. This pure table is not offered as a strict
active-horizon cap-feasible separator. $\square$

**Definition 260.2 (The unchanged full one-budget alternative).**
For every $L\ge3$ and every actual full $y\ge0$ with
$\Delta_O(y)\le1$, the positive alternative asks for one
unrestricted full $V\ge0$ and one $\theta\in[0,1]$ such that

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_H(Q(y)-Q(V))\le\theta.
\tag{260.1}
$$

The score $V$ may change every coordinate; the residual is signed.
At $\theta=1$, nonzero zero-cost scores are allowed.
There is no fixed-law, anchor, unary, quotient, schedule-graph,
canonical-table, positive-residual or separately funded component
restriction. By the full alternative of Theorem 199.3, its negative
route requires the same actual $b\in H_N$, one full feasible
$\lambda\ge0$ with $G_N\lambda\ge h(b)$, mass $M\ge1$,
and an actual full unit-$O$ score with the strict inequality
$F_y(b)>M$, together with the original source transport.

The relation (260.1) for every input remains unresolved here.
The estimates (253.3), (254.7) and (255.4) retain positive score
allowances; (253.5) computes an unpaid signed residual for one
particular score construction. The regional exact law in Section
257 excludes a separator on its own family, and the mixed cut
excludes some infeasible profiles. The event identity in Section
258 is exact for a fixed repair, and Section 259 distinguishes
its affordability from scalar summaries. None of these statements
proves the universal full-budget inclusion or constructs the required
same-feasible-profile separator. Equivalently, the original
all-sequence positive-closed-cap implication
$\mathcal F_N(a,e)\ne\varnothing\Rightarrow
\mathcal F_N(a,e)\cap\mathscr C_L\ne\varnothing$
retains its original quantifiers.

**Definition 260.3 (Mature comparisons and mathematical boundaries).**
Blackwell's *Comparison of Experiments*, Sections 2–5,
supplies the comparison and randomization frame: a common kernel
and all decision events must be considered jointly. It does not
supply the increasing stopped hard-two theorem here.
Kaniewski, Lee and de Wolf,
[*Query complexity in expectation*, Definition 8 and Theorem 9](https://arxiv.org/html/1411.7280v1),
concern nonnegative scalar expectation and worst positive-mixture
path depth. Their characterization does not impose this one
probability-vector mass budget, the three equal-mass stopped cells,
or increasing first-zero stopping. The general polyhedral alternative
used in Section 199 is the finite Farkas framework in Kaibel,
[*Basic Polyhedral Theory*, Theorems 1, 7, 8 and 10](https://arxiv.org/abs/1001.2161).

The additional results here are ordinary suffix, score and
whole-table arguments relative to those named suppliers. Their
construction principles are concrete: a fair suffix exposes a
quarter-unit loss from each noncanonical transcript, a biased suffix
chooses the best balance of slack and counting defect, a midpoint
splits a cell disagreement evenly, and the event identity compares
signed mass transfer with slack at the same legal word. These
principles motivate the formulas; the displayed inequalities and
cell proofs establish their claimed ranges. Each endpoint mixture
has one probability budget and one common seed; each score
certificate uses one joint allowance.
They make no exhaustive literary-priority claim or unrestricted
closure claim about previously named constructors. Existing lower
cuts, saturated and plateau laws, the normalized $D=0$ face,
terminal coupling and exact source/tail transport retain their own
mathematical ownership and are not additional results of these
arguments.

## 追加锚（本行以下为增补区）
