# Residual cancellation and the Impish-start cordiality number of crowns

Elliot Krop · Haobo Ma · Wenlin Zhang

**Definition 1 (Crown and payoff).** For an integer $m\ge1$, let
$L=\{\ell_1,\ldots,\ell_m\}$ and $R=\{r_1,\ldots,r_m\}$. The crown
$R_m$ has vertex set $L\sqcup R$ and edges $\ell_i r_j$ exactly when
$i\ne j$. The deleted matching pairs $\{\ell_i,r_i\}$ are called columns;
the two vertices of a column are mates. Admirable assigns spin $+1$
(vertex label $0$), Impish assigns spin $-1$ (vertex label $1$), and
the players alternate choosing one unplayed vertex. Each undirected edge
is counted once. For a complete labelling $x$, put

$$
d(x)=e_1-e_0=-\sum_{uv\in E(R_m)}x_ux_v.
$$

Admirable minimizes $|d|$ and Impish maximizes $|d|$. Write
$c_g^I(R_m)$ for the minimax value when Impish starts. These are the
cordiality conventions of Krop–Mittal–Wigal, Section 1
([KMW](../../../Library/GraphInvariants/kropmittalwigal2024cordiality.md));
the separate notation for the two starters and the distinction between
signed balance and absolute cordiality follow Dorbec–Henning–Tuza–Versteegen,
Section 1 ([DHTV](https://arxiv.org/html/2409.01796v1#S1)).
For any partial position the continuation retains every already played
spin and every contribution from that fixed boundary.

**Theorem 2 (Krop–Ma–Zhang).** For every integer $r\ge1$,

$$
c_g^I(R_{4r^2+1})=4r.
$$

**Lemma 3 (Cancellation with a fixed boundary).** Suppose two unplayed
vertices $u,v$ lie on the same side of a crown, their mates are played,
and their mates have equal spins. Deleting $u,v$ from the remaining game,
while retaining the fixed boundary, preserves its continuation minimax
value for either starter and either the signed or absolute payoff.

**Proof.** Let $F$ be the other unplayed vertices. The vertices $u,v$ are
nonadjacent and have the same neighbors in $F$, namely all unplayed
vertices on the opposite side. Their coefficients against the fixed
boundary are also equal: the two omitted mates have equal spins. Hence
the final signed score has the form

$$
d=d_{\rm core}-(x_u+x_v)
\left(c+\sum_{w\in F\cap N(u)}x_w\right),
$$

where $c$ is the common sum of adjacent fixed spins. Opposite spins at
$u,v$ make this exactly the core score for every final labelling of $F$.
Fix either player and an optimal core strategy for that player. Follow
it while a core move remains, except that an opponent move at $u$ or $v$
is immediately answered at the other vertex. The interruption has two
moves and preserves the next core player. If both vertices remain after
the core ends, the final two moves split them. Thus each player can
enforce the opposite-spin condition and obtain that player's core
guarantee. The two guarantees prove equality of minimax values. Equality
of scores on these continuations proves the absolute-payoff version as
well. The respond-at-the-partner strategy has the established antecedent
in [DHTV, Lemma 3.1](https://arxiv.org/html/2409.01796v1#S3.Thmtheorem1);
the displayed fixed-boundary identity supplies the equality used here. $\square$

**Definition 4 (Residual state).** A singleton is an unplayed vertex whose
mate has been played. Its type is $L_+,L_-,R_+$, or $R_-$: the letter
is its own side, and the subscript is its fixed mate's spin. Repeated
use of Lemma 3 leaves at most one singleton of each type. Removed
vertices belong to disjoint reserved pairs; no spin is assigned to them
by the reduction. Their fixed mates remain in the boundary.

Let $e$ be the number of empty columns, $s=S_L$ the sum of retained
fixed spins on the left, and $q=Q$ the sum of products in completed
columns of the active game. A split reserved pair contributes zero to
both its side sum and $Q$. Let $k$ be the four-bit mask whose bit
positions $0,1,2,3$ represent $L_+,L_-,R_+,R_-$, respectively; let
$P$ be the represented set and $|P|=\operatorname{popcount}(k)$.
The reduced state is $(e,s,q,k)$. The retained fixed spins include the
mates of every reserved pair.

**Theorem 5 (Exact recurrence and state bound).** For normalized positions
arising from an Impish-start crown, the continuation value depends only
on $(e,s,q,k)$. If $|P|$ is even then Impish moves, with spin $z=-1$;
if $|P|$ is odd then Admirable moves, with spin $z=+1$. The full list
of successors is as follows, with $\oplus$ denoting bitwise toggle.

1. For each set bit $b$, complete that singleton:
   $$
   (e,s,q,k)\longmapsto
   \bigl(e,s+z\mathbf1_{b<2},q+z(-1)^{b\bmod2},k\oplus2^b\bigr).
   $$
2. If $e>0$, choose a side $j\in\{0,1\}$, with $0=L$ and $1=R$,
   and open an empty column. Set
   $$b=2(1-j)+\mathbf1_{z=-1}.$$
   The successor is
   $$
   (e-1,s+z\mathbf1_{j=0},q,k\oplus2^b).
   $$

At $e=k=0$ the value is $|s^2+q|$. On Admirable turns take the minimum
of the successor values, and on Impish turns take the maximum. From
$(m,0,0,0)$ this gives an exact algorithm with at most
$16(m+1)(2m+1)^2$ states and at most six successors per state.

**Proof.** A cancelled pair removes two unplayed vertices and will have
zero total spin. The retained fixed total is therefore $t=0$ before
Impish and $t=-1$ before Admirable. There are $2e+|P|$ active unplayed
vertices, so its parity determines the next player. The crown identity is

$$
d=-S_LS_R+Q.
$$

At termination $S_R=-S_L$, giving $d=s^2+q$. Splitting a reserved pair
preserves this identity because its contributions to its side sum and to
$Q$ both cancel. Completing a singleton changes the left sum, if
appropriate, and adds its product with its mate to $Q$. Opening an
empty column creates the stated opposite-side singleton. If another
singleton of that type exists, Lemma 3 removes the two; this is exactly
the mask toggle. Thus every legal move has precisely a listed normalized
successor and the same child continuation value.

The rank $2e+|P|$ decreases by one or three at each transition. Induction
on this rank proves the Bellman recurrence. To lift a selected core
strategy to the board, keep the disjoint reserved pairs. During core
play, immediately answer any opponent entry into a reserved pair at its
partner; otherwise play the selected core move. Such interruptions leave
the core and its next player unchanged. At the end keep answering entries
into untouched pairs. If forced to open a pair, reserve its partner;
answer entries into other pairs immediately, and when the opponent closes
the reserved pair, open another untouched pair if one remains. This
splits every pair. Further pairs created by core normalization contain
previously active vertices and are disjoint from all earlier pairs.
Iterating this lifting gives the guarantee against every continuation.

The bounds $0\le e\le m$, $|s|\le m$, $|q|\le m$ follow because
at most $m$ retained left spins and at most $m$ completed-column products
contribute, each of absolute value one. There are sixteen masks. The
numeric recurrence stores one integer per state, with $O(\log m)$-bit
arithmetic. This proves the $O(m^3)$ numeric state bound. $\square$

**Definition 6 (Exact threshold sets).** For $B\in\mathbb Z_{\ge0}$,
let $W_B(e,s,k)$ be the set of integer $q$ from which Admirable can
guarantee $|d|\le B$. At $e=k=0$ it is
$[-B-s^2,B-s^2]\cap\mathbb Z$. For a transition changing $q$ by
$\Delta q$, shift the child's set by $-\Delta q$. Union the shifted
sets on Admirable turns and intersect them on Impish turns. These
operations on integer intervals retain holes. Side interchange sends
$s$ to $t-s$, with $t=0$ or $-1$ according to the next player, and
preserves $q$ and the value. The state bound in Theorem 5 concerns the
numeric recurrence, not the number of intervals in threshold sets.

**Definition 7 (Periodic invariant).** Fix an integer $r\ge1$ and put

$$
m=4r^2+1,\quad H=4r,\quad \rho=e\bmod4,\quad x=s^2+q,\quad h=|s|.
$$

For even masks define $\mathcal C_r(e,s,q,k)$ by

$$
-H+a_{\rho,P}(s)\le x\le H+b_{\rho,P}(s).
$$

The following tables give every correction pair $(a,b)$. Write
$\mathbf1_E$ for the indicator of a condition $E$.

| $P$ (mask $k$) | $\rho=0$ | $\rho=1$ |
|---|---|---|
| $\varnothing$ ($0$) | $(0,0)$ | $(2h,-2h)$ |
| $\{L_+,L_-\}$ ($3$) | $(2,-2)$ | $(\max(2,2h-2),-2h-2)$ |
| $\{L_+,R_+\}$ ($5$) | $(2h-1,-2h-1)$ | $(1,-3)$ |
| $\{L_-,R_+\}$ ($6$) | $(2\lvert s-1\rvert-1,-2\lvert s-1\rvert-1)$ | $(3-4\mathbf1_{s=1},-1)$ |
| $\{L_-,R_-\}$ ($10$) | $(2h-1,-2h-1)$ | $(1,-3)$ |
| All four ($15$) | $(4-4\mathbf1_{h=1},-4)$ | $(2h,-\max(4,2h))$ |

| $P$ (mask $k$) | $\rho=2$ | $\rho=3$ |
|---|---|---|
| $\varnothing$ ($0$) | $(2,-2)$ | $(2h-2,-2h-2)$ |
| $\{L_+,L_-\}$ ($3$) | $(4\mathbf1_{s\ge3},-4\mathbf1_{s<1})$ | $(2h,-\max(4,2h))$ |
| $\{L_+,R_+\}$ ($5$) | $(2h+1,-\max(3,2h-1))$ | $(3-4\mathbf1_{h=1},-1)$ |
| $\{L_-,R_+\}$ ($6$) | $(2h-1,-2h-1)$ | $(1,-3)$ |
| $\{L_-,R_-\}$ ($10$) | $(\max(1,2h-3),-2h-3)$ | $(3-4\mathbf1_{h=1},-1)$ |
| All four ($15$) | $(2,-2)$ | $(2h-2,-2h-2)$ |

For the remaining masks use side interchange at an Impish turn:

$$
(a_{\rho,12}(s),b_{\rho,12}(s))
=(a_{\rho,3}(-s),b_{\rho,3}(-s)),\qquad
(a_{\rho,9}(s),b_{\rho,9}(s))
=(a_{\rho,6}(-s),b_{\rho,6}(-s)).
$$

**Lemma 8 (Physical constraints and strip).** Put $t=0$ before Impish
and $t=-1$ before Admirable, and define

$$p_L=|P\cap\{L_+,L_-\}|,\qquad p_-=|P\cap\{L_-,R_-\}|.$$

Every normalized state from $R_m$ satisfies

$$
s\equiv m-e-p_L\pmod2,\qquad
q\equiv t-m+e+2p_-\pmod4,\qquad
q\ge e+|P|-m.
$$

If a nonterminal Impish-to-move state also satisfies $\mathcal C_r$,
then $|s|\le2r$.

**Proof.** Before singleton cancellation let $u,v$ count singletons with
fixed Admirable and Impish mates, and $a,b$ count completed $AA,II$
columns. The fixed spin total is $t=2(a-b)+u-v$. Column counting gives

$$q=4b+2v+e-m+t.$$

Cancellation changes $v$ by an even number, so the congruence for $q$
survives. Counting fixed and unplayed left vertices modulo two gives
the congruence for $s$; deleting two free left vertices preserves it.
With $n$ singleton columns before cancellation, at most $m-e-n$
completed products contribute negatively, hence
$q\ge-(m-e-n)\ge e+|P|-m$.
Every upper correction in Definition 7 is nonpositive, so

$$s^2+e+|P|\le m+H=(2r+1)^2.$$

At a nonterminal state $e+|P|>0$. Since $s$ is integral, this implies
$|s|\le2r$. $\square$

**Lemma 9 (Symbolic closure).** For every integer $r\ge1$, let
$(e,s,q,k)$ be a nonterminal even-mask state satisfying the two physical
congruences in Lemma 8, $|s|\le2r$, and $\mathcal C_r$. Every legal
Impish move has an Admirable reply whose normalized successor satisfies
$\mathcal C_r$.

**Proof.** The finite arithmetic certificate is specified in Definitions
10–12 and its complete witness tables below. They establish that every
possible failure system for such a response is rationally infeasible.
An integer counterexample would be a rational solution of one of these
systems, so there is none. The passage from $e=0,\ldots,7$ to every
$e\ge0$ is justified in Definition 10. $\square$

**Definition 10 (All failure systems).** Use the masks in the order
$0,3,5,6,9,10,12,15$ and empty-column representatives $e=0,\ldots,7$,
omitting $e=k=0$. Put $\rho=e\bmod4$ and

$$
s=2u+\sigma,\quad \sigma=(1-\rho-p_L)\bmod2\in\{0,1\},\quad
x=x_0+4v,\quad x_0=(\sigma-1+\rho+2p_-)\bmod4\in\{0,1,2,3\}.
$$

These are exactly the residue conditions for $s$ and $x$: $m\equiv1$
modulo four, $s^2\equiv\sigma$ modulo four, and $t=0$.
Partition the integer $u$ into seven regions, indexed $j=0,\ldots,6$:

$$
u\le-3;\quad u=-2;\quad u=-1;\quad u=0;\quad u=1;\quad u=2;\quad u\ge3.
$$

On a fixed region set

$$
A_0(u)=\left\lceil\frac{a_{\rho,P}(s)-x_0}{4}\right\rceil,
\qquad B_0(u)=\left\lfloor\frac{b_{\rho,P}(s)-x_0}{4}\right\rfloor.
$$

The source interval is $-r+A_0(u)\le v\le r+B_0(u)$.
Fix one Impish successor, then enumerate all its Admirable successors
by Theorem 5. For a two-move successor with net changes
$\delta=s'-s\in\{-1,0,1\}$ and $\eta=q'-q$, put

$$
g(u)=2s\delta+\delta^2+\eta,\qquad
A_i(u)=\left\lceil\frac{a_{\rho',P'}(s+\delta)-g(u)-x_0}{4}\right\rceil,
\qquad
B_i(u)=\left\lfloor\frac{b_{\rho',P'}(s+\delta)-g(u)-x_0}{4}\right\rfloor.
$$

Reply $i$ succeeds exactly when $-r+A_i(u)\le v\le r+B_i(u)$.
For every reply choose one failure alternative:

$$
\varepsilon_i=0:\ v\le-r+A_i(u)-1,\qquad
\varepsilon_i=1:\ v\ge r+B_i(u)+1.
$$

All successor lists put singleton bits in increasing order before the
two openings, left then right, when available. Retain distinct legal
actions even if their interval bounds coincide. List binary vectors
$\varepsilon$ lexicographically, with $0<1$.

All the functions $A_i,B_i$ are integer affine in $u$ on each region.
For a singleton region evaluate at its specified $u$, leaving slope
zero. On either half-line an affine function's sign follows from its
slope and its finite endpoint. This determines each absolute value,
maximum, and indicator in Definition 7 throughout the region, also
after replacing $s$ by $s+\delta$. In every numerator being divided
by four the coefficient of $u$ is a multiple of four. Thus if a
numerator is $4au+b$, its ceiling and floor are respectively
$au+\lceil b/4\rceil$ and $au+\lfloor b/4\rfloor$; no bound on $r$
or sampling of $u$ is involved.

For $e=0,1,2,3$ retain the actual low-column availability. For $e\ge4$
two moves remove at most two empty columns, so an opening remains
available at both moves; all corrections depend only on $e\bmod4$.
Consequently the representatives $4,5,6,7$ give exactly the same lists
of interval bounds and failure systems for all higher $e$ with the
corresponding residue.

**Definition 11 (Integer rows of a failure system).** A triple
$(a,b,c)$ denotes $ar+bu\le c$. A bound triple $(a,b,c)$ in a
lower or upper list denotes $ar+bu+c\le v$ or $v\le ar+bu+c$,
respectively. Write $A_i=\alpha_i u+\gamma_i$ and
$B_i=\beta_i u+\theta_i$. Start the lower list with
$(-1,\alpha_0,\gamma_0)$ and the upper list with
$(1,\beta_0,\theta_0)$. For each reply append
$(-1,\alpha_i,\gamma_i-1)$ to the upper list if $\varepsilon_i=0$,
or $(1,\beta_i,\theta_i+1)$ to the lower list if $\varepsilon_i=1$.
For every lower triple $(a,b,c)$ and upper triple $(a',b',c')$ include
the inequality row $(a-a',b-b',c'-c)$.

Also include the domain rows

$$(-1,0,-1),\qquad(-1,1,-\sigma),\qquad(-1,-1,0).$$

They express $r\ge1$, $r\ge u+\sigma$, and $r\ge-u$; the last two
are equivalent for integral $r,u$ to $|2u+\sigma|\le2r$.
For a finite region lower endpoint $\ell$ include $(0,-1,-\ell)$,
and for a finite upper endpoint $h$ include $(0,1,h)$.
Requiring every lower bound on $v$ to be at most every upper bound
eliminates $v$ over the rationals, giving exactly this system.

**Definition 12 (Rational contradiction witnesses).** Normalize any
nonzero integer row by dividing all entries by their positive greatest
common divisor; leave a zero row unchanged. Remove duplicates and sort
rows lexicographically in increasing order. Apply this to the triples
of Definition 11 to obtain $T$. Eliminate $r$: retain $(b,c)$ from
each $(0,b,c)\in T$, and for every
$p=(a_p,b_p,c_p)$ with $a_p>0$ and
$n=(a_n,b_n,c_n)$ with $a_n<0$ include

$$(-a_n b_p+a_p b_n,\ -a_n c_p+a_p c_n).$$

Normalize, deduplicate, and sort these pairs in the same way, obtaining
$F=((d_1,f_1),\ldots,(d_N,f_N))$. Its rows mean $d_i u\le f_i$.
A witness $i:0$ means $d_i=0$, $f_i<0$. A witness $i:j$ with $j>0$
means

$$d_i<0<d_j,\qquad d_j f_i-d_i f_j<0.$$

In the second case, the nonnegative combination of rows $i,j$ with
coefficients $d_j,-d_i$ gives the contradiction
$0\le d_j f_i-d_i f_j<0$. In the first case row $i$ already is a
contradiction. Each row of $F$ itself is a nonnegative rational
combination of the original system's rows. These witnesses therefore
prove rational infeasibility without an upper bound on $r$ or $u$.

**Proposition 13 (Finite certificate).** The witness tables following
Theorem 14 specify one valid witness in the sense of Definition 12 for
every failure system of Definitions 10–11. There are 1,680
Impish-move/region blocks and 25,368 systems: 10,136 systems for
$e=0,1,2,3$ and 15,232 for $e=4,5,6,7$.

**Proof.** Form the integer rows by Definitions 7 and 10–12. The table
has one witness for each binary failure vector, in the specified order.
For each entry $i:0$, its row has $d_i=0$, $f_i<0$; for each entry
$i:j$ with $j>0$, the two selected rows have
$d_i<0<d_j$ and $d_jf_i-d_if_j<0$. Thus every entry supplies the
displayed nonnegative-combination contradiction. All calculations are
integer additions, multiplications, sign comparisons, and division by
positive greatest common divisors; the finite data and row definitions
specify the complete certificate. $\square$

**Theorem 14 (Root strategy and equality).** The invariant of Definition 7
gives an Admirable strategy on $R_{4r^2+1}$ attaining the upper bound
in Theorem 2, and Impish's column pairing attains the reverse bound.

**Proof.** At the root $(e,s,q,k)=(m,0,0,0)$ one has $\rho=1$,
$a=b=0$, so $\mathcal C_r$ holds. At each nonterminal certified
Impish turn, Lemma 8 supplies $|s|\le2r$ and the physical congruences.
Lemma 9 then gives an invariant-preserving Admirable reply to every
Impish core move. Choose any such reply, and lift the core strategy
by the disjoint reserved-pair responses of Theorem 5. These responses
preserve the core position. The end-of-core rule splits all outstanding
pairs. The active rank $2e+|P|$ decreases strictly, so the core reaches
$e=0$, $P=\varnothing$. Its $\rho=0$ row is exactly
$|s^2+q|\le4r$. Every reserved pair contributes zero; hence this is
the payoff on the original board, proving $c_g^I(R_m)\le4r$.

For the reverse inequality, Impish first opens a column and thereafter
maintains one outstanding column after each Impish move. If Admirable
opens a fresh column, Impish closes that column. If Admirable closes
the outstanding column, Impish opens a fresh one when a move remains.
Every completed column then has opposite spins; the final Admirable
move closes the last outstanding column. Thus $q=-m$. Since $m$ is
odd, the final left spin sum $s$ is odd. The adjacent odd squares
around $m=4r^2+1$ are

$$
(2r-1)^2=m-4r,\qquad (2r+1)^2=m+4r.
$$

Consequently $|s^2-m|\ge4r$, proving $c_g^I(R_m)\ge4r$ and Theorem 2.
$\square$

**Definition 15 (Certificate table notation).** A block is indexed by
$(e,k,j,a)$, where $j$ is the region index in Definition 10 and $a$
is the Impish action. The symbols $b0,b1,b2,b3$ mean completing that
set singleton bit; $L,R$ mean opening an empty column on that side.
Every block refers to a witness sequence $C_n$. Its entries correspond,
in order, to all binary failure vectors for the Admirable responses
listed in Definition 10. The notation $i:j$ has exactly the meaning
in Definition 12, and row numbers start at one. Repeated sequences
are written once and referenced by their $C_n$ label. These are finite
integer data specifying the mathematical certificates of Proposition 13.

| Sequence | Ordered contradiction witnesses |
|---|---|
| $C_1$ | $1:0, 1:0$ |
| $C_2$ | $2:0, 2:0$ |
| $C_3$ | $1:2, 1:0$ |
| $C_4$ | $1:0, 1:2$ |
| $C_5$ | $2:0, 1:2$ |
| $C_6$ | $1:2, 2:0$ |
| $C_7$ | $1:0, 1:0, 1:0, 1:0, 3:0, 2:0, 2:0, 1:0$ |
| $C_8$ | $1:0, 1:0, 2:0, 1:0, 2:0, 1:0, 3:0, 1:0$ |
| $C_9$ | $2:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_10$ | $2:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_11$ | $2:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_12$ | $2:0, 3:0, 3:0, 4:0, 3:0, 3:0, 4:0, 2:0$ |
| $C_13$ | $2:0, 4:0, 3:0, 3:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_14$ | $2:0, 3:0, 3:0, 4:0, 3:0, 4:0, 3:0, 2:0$ |
| $C_15$ | $2:0, 4:0, 3:0, 3:0, 3:0, 4:0, 3:0, 2:0$ |
| $C_16$ | $2:0, 4:0, 3:0, 4:0, 2:0, 3:0, 2:0, 2:0$ |
| $C_17$ | $2:0, 3:0, 4:0, 3:0, 3:0, 4:0, 3:0, 2:0$ |
| $C_18$ | $2:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 2:0$ |
| $C_19$ | $3:0, 5:0, 5:0, 4:0, 5:0, 7:0, 5:0, 2:0$ |
| $C_20$ | $3:0, 5:0, 6:0, 4:0, 5:0, 7:0, 5:0, 2:0$ |
| $C_21$ | $2:0, 4:0, 6:0, 4:0, 5:0, 5:0, 5:0, 3:0$ |
| $C_22$ | $2:0, 4:0, 6:0, 6:0, 4:0, 5:0, 4:0, 3:0$ |
| $C_23$ | $1:3, 1:0, 3:0, 1:0, 3:0, 1:0, 4:0, 1:0$ |
| $C_24$ | $2:0, 1:0, 3:0, 1:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_25$ | $2:0, 1:0, 3:0, 1:0, 3:0, 1:0, 4:0, 1:0$ |
| $C_26$ | $2:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_27$ | $2:0, 3:0, 4:0, 3:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_28$ | $2:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 2:0$ |
| $C_29$ | $2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_30$ | $2:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_31$ | $2:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_32$ | $2:0, 4:0, 3:0, 4:0, 4:0, 4:0, 3:0, 2:0$ |
| $C_33$ | $2:0, 4:0, 4:0, 4:0, 6:0, 5:0, 4:0, 2:0$ |
| $C_34$ | $2:0, 3:0, 4:0, 5:0, 4:0, 5:0, 4:0, 2:0$ |
| $C_35$ | $2:0, 4:0, 6:0, 5:0, 4:0, 5:0, 4:0, 2:0$ |
| $C_36$ | $1:0, 1:0, 2:0, 2:0, 1:0, 1:0, 2:0, 1:0$ |
| $C_37$ | $1:0, 1:0, 2:0, 1:0, 2:0, 1:0, 2:0, 1:0$ |
| $C_38$ | $2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 2:0$ |
| $C_39$ | $2:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0$ |
| $C_40$ | $3:0, 6:0, 5:0, 5:0, 6:0, 3:0, 5:0, 2:0$ |
| $C_41$ | $2:0, 3:0, 5:0, 5:0, 5:0, 5:0, 5:0, 3:0$ |
| $C_42$ | $3:0, 6:0, 6:0, 4:0, 6:0, 7:0, 6:0, 2:0$ |
| $C_43$ | $2:0, 4:0, 7:0, 6:0, 5:0, 5:0, 5:0, 3:0$ |
| $C_44$ | $2:0, 4:0, 2:0, 3:0, 3:0, 4:0, 2:0, 2:0$ |
| $C_45$ | $3:0, 6:0, 6:0, 6:0, 6:0, 3:0, 6:0, 2:0$ |
| $C_46$ | $2:0, 4:0, 5:0, 5:0, 7:0, 6:0, 5:0, 3:0$ |
| $C_47$ | $3:0, 6:0, 6:0, 4:0, 6:0, 8:0, 6:0, 2:0$ |
| $C_48$ | $1:0, 1:0, 3:0, 2:0, 1:0, 1:0, 2:0, 1:0$ |
| $C_49$ | $2:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 2:0$ |
| $C_50$ | $3:0, 6:0, 6:0, 6:0, 6:0, 4:0, 7:0, 2:0$ |
| $C_51$ | $2:0, 3:0, 6:0, 6:0, 6:0, 6:0, 6:0, 3:0$ |
| $C_52$ | $2:0, 4:0, 7:0, 6:0, 6:0, 6:0, 6:0, 3:0$ |
| $C_53$ | $1:0, 1:0, 3:0, 2:0, 1:0, 1:0, 3:0, 2:0$ |
| $C_54$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 2:0$ |
| $C_55$ | $1:0, 1:0, 1:0, 1:0, 3:0, 3:0, 2:0, 2:0$ |
| $C_56$ | $1:3, 5:0, 4:0, 4:0, 5:0, 4:0, 6:0, 2:0$ |
| $C_57$ | $2:0, 5:0, 4:0, 4:0, 5:0, 3:0, 4:0, 2:0$ |
| $C_58$ | $2:0, 5:0, 4:0, 4:0, 4:0, 6:0, 4:0, 2:0$ |
| $C_59$ | $3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 2:0, 2:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_60$ | $2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0$ |
| $C_61$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0$ |
| $C_62$ | $1:0, 1:0, 4:0, 4:0, 1:0, 1:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 1:3$ |
| $C_63$ | $2:0, 1:0, 3:0, 1:0, 2:0, 1:0, 3:0, 1:0$ |
| $C_64$ | $1:0, 1:0, 1:0, 1:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_65$ | $2:0, 5:0, 5:0, 7:0, 5:0, 6:0, 5:0, 6:0, 4:0, 4:0, 6:0, 6:0, 6:0, 4:0, 6:0, 4:0, 5:0, 7:0, 4:0, 5:0, 5:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_66$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 3:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_67$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 5:0, 6:0, 6:0, 5:0, 5:0, 4:0, 6:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 5:0, 7:0, 4:0, 5:0, 7:0, 5:0, 5:0, 2:0$ |
| $C_68$ | $2:0, 4:0, 4:0, 6:0, 3:0, 3:0, 4:0, 4:0, 4:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_69$ | $2:0, 5:0, 5:0, 6:0, 5:0, 6:0, 5:0, 6:0, 4:0, 4:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 6:0, 4:0, 5:0, 5:0, 6:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_70$ | $2:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 3:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_71$ | $2:0, 3:0, 3:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 2:0$ |
| $C_72$ | $2:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_73$ | $2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_74$ | $2:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_75$ | $2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_76$ | $2:0, 3:0, 3:0, 4:0, 2:0, 3:0, 3:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_77$ | $2:0, 3:0, 4:0, 5:0, 3:0, 3:0, 5:0, 5:0, 3:0, 3:0, 5:0, 5:0, 3:0, 3:0, 5:0, 3:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_78$ | $2:0, 4:0, 5:0, 5:0, 4:0, 3:0, 5:0, 4:0, 4:0, 4:0, 5:0, 5:0, 4:0, 3:0, 5:0, 3:0, 4:0, 5:0, 4:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_79$ | $2:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 3:0, 4:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_80$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 5:0, 4:0, 4:0, 6:0, 6:0, 5:0, 4:0, 7:0, 5:0, 4:0, 6:0, 4:0, 6:0, 6:0, 5:0, 6:0, 5:0, 6:0, 6:0, 4:0, 4:0, 7:0, 5:0, 5:0, 2:0$ |
| $C_81$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_82$ | $2:0, 5:0, 5:0, 7:0, 5:0, 4:0, 7:0, 5:0, 5:0, 5:0, 6:0, 6:0, 5:0, 4:0, 6:0, 4:0, 4:0, 6:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_83$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 6:0, 3:0, 4:0, 4:0, 4:0, 3:0, 2:0$ |
| $C_84$ | $2:0, 4:0, 6:0, 7:0, 4:0, 4:0, 7:0, 5:0, 4:0, 4:0, 7:0, 7:0, 5:0, 4:0, 8:0, 5:0, 6:0, 7:0, 6:0, 7:0, 7:0, 5:0, 7:0, 5:0, 7:0, 7:0, 5:0, 5:0, 8:0, 5:0, 6:0, 2:0$ |
| $C_85$ | $2:0, 4:0, 6:0, 7:0, 4:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 1:3$ |
| $C_86$ | $2:0, 5:0, 6:0, 8:0, 5:0, 4:0, 8:0, 5:0, 5:0, 5:0, 7:0, 7:0, 5:0, 4:0, 7:0, 4:0, 5:0, 7:0, 5:0, 7:0, 7:0, 4:0, 7:0, 4:0, 7:0, 7:0, 6:0, 6:0, 7:0, 4:0, 6:0, 2:0$ |
| $C_87$ | $2:0, 5:0, 4:0, 7:0, 4:0, 4:0, 4:0, 4:0, 4:0, 7:0, 4:0, 7:0, 4:0, 4:0, 4:0, 4:0, 4:0, 7:0, 4:0, 7:0, 4:0, 4:0, 4:0, 4:0, 4:0, 7:0, 4:0, 6:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_88$ | $2:0, 4:0, 6:0, 5:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_89$ | $2:0, 5:0, 5:0, 4:0, 4:0, 6:0, 4:0, 2:0$ |
| $C_90$ | $1:0, 1:0, 3:0, 2:0, 3:0, 2:0, 2:0, 1:0$ |
| $C_91$ | $1:0, 1:0, 2:0, 2:0, 2:0, 2:0, 2:0, 1:0$ |
| $C_92$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0, 4:0, 4:0, 3:0, 3:0, 4:0, 3:0, 3:0, 1:0$ |
| $C_93$ | $2:0, 1:5, 4:0, 4:0, 4:0, 4:0, 3:0, 2:0$ |
| $C_94$ | $2:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 2:0$ |
| $C_95$ | $2:0, 2:0, 4:0, 3:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_96$ | $2:0, 3:0, 4:0, 4:0, 4:0, 4:0, 2:6, 2:0$ |
| $C_97$ | $3:0, 3:0, 6:0, 3:0, 6:0, 3:0, 6:0, 2:0$ |
| $C_98$ | $3:0, 3:0, 6:0, 4:0, 6:0, 4:0, 5:0, 2:0$ |
| $C_99$ | $3:0, 6:0, 7:0, 8:0, 6:0, 4:0, 8:0, 5:0, 6:0, 6:0, 7:0, 7:0, 6:0, 4:0, 7:0, 4:0, 6:0, 8:0, 6:0, 8:0, 8:0, 4:0, 8:0, 4:0, 8:0, 8:0, 7:0, 7:0, 8:0, 4:0, 7:0, 2:0$ |
| $C_100$ | $2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0$ |
| $C_101$ | $1:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_102$ | $2:0, 4:0, 3:0, 4:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_103$ | $2:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 2:0$ |
| $C_104$ | $2:0, 3:0, 5:0, 4:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_105$ | $1:0, 1:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0$ |
| $C_106$ | $2:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_107$ | $2:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_108$ | $2:0, 3:0, 3:0, 4:0, 3:0, 2:0, 4:0, 2:0$ |
| $C_109$ | $2:0, 4:0, 4:0, 5:0, 4:0, 3:0, 5:0, 2:0$ |
| $C_110$ | $1:0, 2:0, 2:0, 2:0, 2:0, 1:0, 2:0, 1:0$ |
| $C_111$ | $1:0, 2:0, 2:0, 3:0, 2:0, 1:0, 3:0, 1:0$ |
| $C_112$ | $1:0, 3:0, 3:0, 4:0, 3:0, 3:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 3:0, 4:0, 3:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_113$ | $2:0, 4:0, 4:0, 5:0, 4:0, 5:0, 4:0, 5:0, 4:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 5:0, 3:0, 4:0, 3:0, 4:0, 5:0, 5:0, 5:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_114$ | $2:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_115$ | $2:0, 3:0, 2:0, 3:0, 3:0, 4:0, 3:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 2:0, 3:0, 2:0, 3:0, 3:0, 4:0, 3:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_116$ | $2:0, 3:0, 2:6, 4:0, 3:0, 2:0, 4:0, 2:0$ |
| $C_117$ | $2:0, 4:0, 4:0, 6:0, 3:0, 3:0, 5:0, 4:0, 4:0, 4:0, 6:0, 6:0, 4:0, 3:0, 6:0, 4:0, 4:0, 6:0, 4:0, 6:0, 5:0, 4:0, 5:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 5:0, 2:0$ |
| $C_118$ | $2:0, 4:0, 2:6, 4:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_119$ | $2:0, 4:0, 5:0, 5:0, 4:0, 3:0, 5:0, 3:0$ |
| $C_120$ | $2:0, 3:0, 5:0, 5:0, 3:0, 3:0, 5:0, 3:0$ |
| $C_121$ | $2:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 5:0, 4:0, 4:0, 6:0, 6:0, 5:0, 4:0, 6:0, 5:0, 6:0, 6:0, 6:0, 6:0, 6:0, 5:0, 6:0, 5:0, 6:0, 6:0, 5:0, 5:0, 6:0, 5:0, 5:0, 3:0$ |
| $C_122$ | $1:0, 1:0, 4:0, 4:0, 1:0, 1:0, 4:0, 3:0, 1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 2:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 1:0$ |
| $C_123$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 2:0, 1:0, 1:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 2:0, 1:0$ |
| $C_124$ | $1:0, 2:0, 2:0, 3:0, 2:0, 1:0, 3:0, 1:0, 2:0, 3:0, 2:0, 3:0, 3:0, 1:0, 3:0, 1:0, 2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_125$ | $1:0, 2:0, 3:0, 2:0, 2:0, 1:0, 3:0, 1:0, 3:0, 3:0, 4:0, 3:0, 3:0, 1:0, 4:0, 1:0, 3:0, 2:0, 3:0, 2:0, 3:0, 1:0, 3:0, 1:0, 4:0, 3:0, 4:0, 3:0, 4:0, 1:0, 4:0, 1:0$ |
| $C_126$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 2:0, 2:0, 3:0, 3:0, 3:0, 3:0, 2:0, 2:0, 2:0, 2:0, 3:0, 3:0, 3:0, 3:0, 2:0, 2:0, 2:0, 2:0, 3:0, 3:0, 3:0, 2:0, 2:0, 2:0, 2:0, 1:0$ |
| $C_127$ | $1:0, 2:0, 2:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0$ |
| $C_128$ | $2:0, 5:0, 5:0, 8:0, 5:0, 5:0, 8:0, 6:0, 3:0, 4:0, 5:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 5:0, 7:0, 6:0, 6:0, 7:0, 5:0, 4:0, 5:0, 5:0, 6:0, 5:0, 5:0, 6:0, 2:0$ |
| $C_129$ | $2:0, 4:0, 4:0, 6:0, 4:0, 5:0, 6:0, 7:0, 4:0, 3:0, 6:0, 4:0, 5:0, 4:0, 7:0, 5:0, 4:0, 6:0, 4:0, 6:0, 6:0, 7:0, 4:0, 5:0, 6:0, 4:0, 6:0, 4:0, 7:0, 5:0, 5:0, 2:0$ |
| $C_130$ | $2:0, 5:0, 5:0, 6:0, 5:0, 4:0, 6:0, 5:0, 5:0, 6:0, 4:0, 5:0, 6:0, 5:0, 5:0, 4:0, 4:0, 4:0, 6:0, 6:0, 4:0, 3:0, 6:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_131$ | $2:0, 5:0, 6:0, 5:0, 5:0, 5:0, 6:0, 5:0, 5:0, 6:0, 6:0, 6:0, 6:0, 5:0, 6:0, 5:0, 6:0, 5:0, 5:0, 4:0, 6:0, 5:0, 6:0, 4:0, 6:0, 6:0, 5:0, 4:0, 6:0, 5:0, 5:0, 2:0$ |
| $C_132$ | $2:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 3:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 6:0, 5:0, 6:0, 6:0, 6:0, 6:0, 5:0, 4:0, 5:0, 5:0, 6:0, 5:0, 5:0, 6:0, 2:0$ |
| $C_133$ | $2:0, 4:0, 4:0, 6:0, 3:0, 4:0, 4:0, 5:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 5:0, 5:0, 4:0, 6:0, 4:0, 6:0, 4:0, 5:0, 4:0, 5:0, 6:0, 6:0, 6:0, 4:0, 5:0, 5:0, 5:0, 2:0$ |
| $C_134$ | $2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_135$ | $2:0, 4:0, 4:0, 4:0, 4:0, 5:0, 5:0, 5:0, 4:0, 4:0, 4:0, 3:0, 5:0, 5:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_136$ | $2:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_137$ | $2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_138$ | $2:0, 4:0, 3:0, 4:0, 4:0, 5:0, 5:0, 5:0, 3:0, 4:0, 3:0, 4:0, 5:0, 5:0, 5:0, 5:0, 3:0, 4:0, 3:0, 4:0, 4:0, 5:0, 4:0, 5:0, 3:0, 4:0, 3:0, 4:0, 4:0, 5:0, 4:0, 2:0$ |
| $C_139$ | $2:0, 4:0, 3:0, 5:0, 4:0, 4:0, 5:0, 5:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 5:0, 3:0, 5:0, 5:0, 5:0, 5:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_140$ | $2:0, 4:0, 3:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 3:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_141$ | $2:0, 4:0, 5:0, 5:0, 4:0, 3:0, 5:0, 4:0, 4:0, 5:0, 4:0, 5:0, 5:0, 3:0, 5:0, 3:0, 5:0, 5:0, 4:0, 5:0, 5:0, 4:0, 5:0, 4:0, 4:0, 5:0, 3:0, 4:0, 5:0, 3:0, 4:0, 2:0$ |
| $C_142$ | $2:0, 5:0, 4:0, 4:0, 4:0, 5:0, 5:0, 5:0, 5:0, 4:0, 4:0, 3:0, 5:0, 4:0, 5:0, 3:0, 5:0, 6:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 6:0, 6:0, 5:0, 4:0, 5:0, 4:0, 5:0, 2:0$ |
| $C_143$ | $2:0, 4:0, 5:0, 7:0, 3:0, 4:0, 5:0, 6:0, 5:0, 7:0, 5:0, 5:0, 5:0, 6:0, 5:0, 4:0, 4:0, 6:0, 5:0, 7:0, 3:0, 4:0, 4:0, 5:0, 5:0, 7:0, 5:0, 5:0, 4:0, 5:0, 4:0, 2:0$ |
| $C_144$ | $2:0, 3:0, 4:0, 5:0, 3:0, 3:0, 5:0, 5:0, 4:0, 5:0, 5:0, 6:0, 5:0, 3:0, 6:0, 4:0, 4:0, 5:0, 3:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 6:0, 4:0, 5:0, 6:0, 4:0, 5:0, 2:0$ |
| $C_145$ | $2:0, 5:0, 5:0, 7:0, 5:0, 4:0, 7:0, 6:0, 4:0, 6:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 5:0, 7:0, 4:0, 5:0, 7:0, 6:0, 5:0, 4:0, 4:0, 6:0, 3:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_146$ | $2:0, 6:0, 5:0, 5:0, 5:0, 7:0, 6:0, 6:0, 6:0, 5:0, 5:0, 4:0, 7:0, 5:0, 6:0, 4:0, 5:0, 7:0, 5:0, 5:0, 6:0, 8:0, 5:0, 5:0, 7:0, 6:0, 5:0, 4:0, 8:0, 5:0, 5:0, 2:0$ |
| $C_147$ | $2:0, 5:0, 5:0, 8:0, 4:0, 5:0, 6:0, 7:0, 5:0, 8:0, 5:0, 6:0, 6:0, 7:0, 6:0, 5:0, 4:0, 6:0, 5:0, 7:0, 4:0, 5:0, 5:0, 6:0, 5:0, 7:0, 5:0, 5:0, 5:0, 6:0, 5:0, 2:0$ |
| $C_148$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 6:0, 5:0, 7:0, 6:0, 4:0, 7:0, 5:0, 4:0, 6:0, 3:0, 4:0, 6:0, 6:0, 4:0, 4:0, 5:0, 7:0, 4:0, 5:0, 7:0, 5:0, 5:0, 2:0$ |
| $C_149$ | $4:0, 8:0, 7:0, 9:0, 8:0, 6:0, 9:0, 8:0, 6:0, 7:0, 6:0, 7:0, 7:0, 4:0, 7:0, 4:0, 7:0, 9:0, 7:0, 9:0, 9:0, 8:0, 9:0, 8:0, 6:0, 7:0, 6:0, 7:0, 7:0, 4:0, 7:0, 2:0$ |
| $C_150$ | $4:0, 7:0, 7:0, 7:0, 7:0, 8:0, 8:0, 8:0, 7:0, 6:0, 7:0, 6:0, 8:0, 5:0, 8:0, 4:0, 7:0, 8:0, 8:0, 8:0, 9:0, 10:0, 9:0, 9:0, 8:0, 7:0, 8:0, 7:0, 10:0, 5:0, 9:0, 2:0$ |
| $C_151$ | $2:0, 5:0, 8:0, 8:0, 4:0, 5:0, 7:0, 7:0, 8:0, 8:0, 8:0, 8:0, 7:0, 7:0, 7:0, 6:0, 6:0, 6:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 6:0, 7:0, 7:0, 7:0, 4:0$ |
| $C_152$ | $2:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 7:0, 7:0, 7:0, 9:0, 9:0, 7:0, 6:0, 9:0, 8:0, 7:0, 7:0, 6:0, 6:0, 7:0, 7:0, 6:0, 6:0, 9:0, 9:0, 7:0, 7:0, 9:0, 8:0, 7:0, 4:0$ |
| $C_153$ | $3:0, 6:0, 6:0, 8:0, 6:0, 4:0, 6:0, 4:0, 6:0, 8:0, 6:0, 8:0, 6:0, 4:0, 6:0, 4:0, 6:0, 8:0, 6:0, 8:0, 6:0, 4:0, 6:0, 4:0, 6:0, 8:0, 6:0, 8:0, 6:0, 4:0, 6:0, 2:0$ |
| $C_154$ | $2:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 3:0$ |
| $C_155$ | $2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 2:0, 2:0, 3:0, 3:0, 2:0, 1:0, 3:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_156$ | $2:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_157$ | $2:0, 5:0, 5:0, 7:0, 5:0, 4:0, 7:0, 5:0, 5:0, 7:0, 4:0, 6:0, 7:0, 5:0, 6:0, 4:0, 4:0, 4:0, 6:0, 6:0, 4:0, 3:0, 6:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_158$ | $2:0, 3:0, 4:0, 3:0, 3:0, 4:0, 4:0, 2:0$ |
| $C_159$ | $2:0, 3:0, 4:0, 4:0, 3:0, 4:0, 5:0, 5:0, 4:0, 4:0, 4:0, 4:0, 5:0, 5:0, 5:0, 4:0, 3:0, 4:0, 4:0, 5:0, 3:0, 4:0, 4:0, 5:0, 4:0, 5:0, 4:0, 5:0, 4:0, 5:0, 4:0, 2:0$ |
| $C_160$ | $2:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 2:0$ |
| $C_161$ | $2:0, 3:0, 6:0, 5:0, 6:0, 5:0, 4:0, 2:0$ |
| $C_162$ | $2:0, 4:0, 6:0, 5:0, 4:0, 5:0, 6:0, 2:0$ |
| $C_163$ | $2:0, 5:0, 8:0, 10:0, 4:0, 5:0, 8:0, 8:0, 8:0, 10:0, 8:0, 8:0, 8:0, 8:0, 8:0, 6:0, 6:0, 7:0, 8:0, 8:0, 5:0, 6:0, 7:0, 7:0, 8:0, 8:0, 8:0, 6:0, 7:0, 7:0, 7:0, 2:0$ |
| $C_164$ | $2:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 2:0$ |
| $C_165$ | $2:0, 3:0, 4:0, 4:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_166$ | $2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 2:0$ |
| $C_167$ | $4:0, 6:0, 7:0, 8:0, 6:0, 4:0, 6:0, 2:0$ |
| $C_168$ | $2:0, 4:0, 7:0, 6:0, 6:0, 6:0, 7:0, 4:0$ |
| $C_169$ | $2:0, 2:0, 4:0, 3:0, 4:0, 3:0, 2:6, 2:0$ |
| $C_170$ | $2:0, 3:0, 6:0, 5:0, 6:0, 5:0, 5:0, 3:0$ |
| $C_171$ | $2:0, 4:0, 3:0, 4:0, 4:0, 1:5, 4:0, 2:0$ |
| $C_172$ | $3:0, 6:0, 6:0, 7:0, 6:0, 3:0, 7:0, 2:0$ |
| $C_173$ | $3:0, 3:0, 6:0, 4:0, 6:0, 4:0, 6:0, 2:0$ |
| $C_174$ | $3:0, 6:0, 5:0, 7:0, 6:0, 3:0, 7:0, 2:0$ |
| $C_175$ | $2:0, 3:0, 7:0, 6:0, 7:0, 6:0, 6:0, 3:0$ |
| $C_176$ | $2:0, 4:0, 6:0, 6:0, 4:0, 3:0, 6:0, 3:0$ |
| $C_177$ | $1:0, 1:0, 4:0, 3:0, 1:0, 1:0, 3:0, 2:0$ |
| $C_178$ | $1:0, 1:0, 4:0, 4:0, 1:0, 1:0, 4:0, 3:0, 1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 2:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 3:0$ |
| $C_179$ | $2:0, 5:0, 4:0, 6:0, 5:0, 3:0, 6:0, 2:0$ |
| $C_180$ | $2:0, 5:0, 6:0, 6:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_181$ | $2:0, 7:0, 6:0, 9:0, 7:0, 5:0, 9:0, 7:0, 5:0, 7:0, 5:0, 7:0, 7:0, 4:0, 7:0, 4:0, 6:0, 9:0, 6:0, 8:0, 9:0, 7:0, 8:0, 6:0, 5:0, 7:0, 4:0, 6:0, 7:0, 4:0, 6:0, 2:0$ |
| $C_182$ | $2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 1:0, 4:0, 1:0$ |
| $C_183$ | $3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_184$ | $1:0, 1:0, 3:0, 2:0, 1:0, 1:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0$ |
| $C_185$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0$ |
| $C_186$ | $3:0, 3:0, 4:0, 3:0, 2:0, 1:0, 3:0, 1:0, 5:0, 4:0, 5:0, 4:0, 3:0, 1:0, 4:0, 1:0, 4:0, 3:0, 4:0, 3:0, 3:0, 1:0, 3:0, 1:0, 5:0, 4:0, 5:0, 4:0, 4:0, 1:0, 4:0, 1:0$ |
| $C_187$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 2:0, 1:0, 1:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0$ |
| $C_188$ | $2:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 3:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_189$ | $2:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 4:0, 6:0, 6:0, 6:0, 6:0, 4:0, 6:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 3:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_190$ | $2:0, 3:0, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 6:0, 5:0, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 6:0, 5:0, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 4:0, 2:0$ |
| $C_191$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 3:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 6:0, 4:0, 6:0, 6:0, 6:0, 6:0, 4:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 2:0$ |
| $C_192$ | $2:0, 5:0, 6:0, 5:0, 4:0, 4:0, 6:0, 4:0, 5:0, 6:0, 7:0, 6:0, 6:0, 5:0, 8:0, 5:0, 6:0, 5:0, 5:0, 4:0, 6:0, 4:0, 5:0, 3:0, 7:0, 6:0, 5:0, 4:0, 8:0, 5:0, 5:0, 2:0$ |
| $C_193$ | $2:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 3:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_194$ | $2:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 3:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_195$ | $2:0, 4:0, 4:0, 6:0, 4:0, 5:0, 5:0, 6:0, 4:0, 6:0, 4:0, 6:0, 5:0, 6:0, 4:0, 5:0, 4:0, 4:0, 4:0, 4:0, 5:0, 5:0, 5:0, 5:0, 4:0, 4:0, 4:0, 4:0, 5:0, 5:0, 4:0, 2:0$ |
| $C_196$ | $2:0, 5:0, 6:0, 5:0, 4:0, 4:0, 5:0, 4:0, 5:0, 6:0, 6:0, 6:0, 6:0, 5:0, 6:0, 5:0, 6:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 3:0, 6:0, 6:0, 5:0, 4:0, 6:0, 5:0, 5:0, 2:0$ |
| $C_197$ | $2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_198$ | $2:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_199$ | $2:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_200$ | $2:0, 3:0, 4:0, 5:0, 3:0, 3:0, 5:0, 5:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 5:0, 5:0, 4:0, 3:0, 5:0, 4:0, 4:0, 4:0, 5:0, 5:0, 4:0, 3:0, 5:0, 2:0$ |
| $C_201$ | $2:0, 4:0, 5:0, 4:0, 3:0, 3:0, 4:0, 3:0, 5:0, 4:0, 5:0, 4:0, 4:0, 3:0, 4:0, 3:0, 5:0, 4:0, 5:0, 4:0, 4:0, 3:0, 4:0, 3:0, 5:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_202$ | $2:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 3:0, 3:0, 2:0, 4:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_203$ | $2:0, 3:0, 4:0, 5:0, 3:0, 3:0, 5:0, 5:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_204$ | $2:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 6:0, 4:0, 5:0, 6:0, 6:0, 5:0, 5:0, 6:0, 6:0, 5:0, 5:0, 6:0, 4:0, 5:0, 2:0$ |
| $C_205$ | $2:0, 4:0, 5:0, 4:0, 4:0, 4:0, 6:0, 4:0, 5:0, 4:0, 5:0, 4:0, 6:0, 4:0, 6:0, 4:0, 5:0, 4:0, 5:0, 4:0, 6:0, 4:0, 6:0, 4:0, 5:0, 4:0, 4:0, 3:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_206$ | $2:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 3:0, 4:0, 6:0, 6:0, 6:0, 6:0, 4:0, 6:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_207$ | $2:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 5:0, 5:0, 6:0, 7:0, 6:0, 6:0, 7:0, 7:0, 6:0, 6:0, 7:0, 7:0, 6:0, 6:0, 7:0, 5:0, 6:0, 2:0$ |
| $C_208$ | $2:0, 4:0, 6:0, 7:0, 3:0, 4:0, 5:0, 5:0, 4:0, 4:0, 7:0, 7:0, 4:0, 4:0, 5:0, 5:0, 6:0, 7:0, 6:0, 7:0, 5:0, 5:0, 5:0, 5:0, 7:0, 7:0, 7:0, 5:0, 5:0, 5:0, 5:0, 2:0$ |
| $C_209$ | $2:0, 5:0, 6:0, 5:0, 5:0, 4:0, 7:0, 4:0, 6:0, 5:0, 6:0, 5:0, 7:0, 4:0, 7:0, 4:0, 6:0, 5:0, 6:0, 5:0, 7:0, 4:0, 7:0, 4:0, 6:0, 5:0, 6:0, 4:0, 7:0, 4:0, 6:0, 2:0$ |
| $C_210$ | $2:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 3:0, 5:0, 7:0, 7:0, 7:0, 7:0, 4:0, 7:0, 4:0, 7:0, 7:0, 6:0, 6:0, 7:0, 4:0, 6:0, 2:0$ |
| $C_211$ | $2:0, 4:0, 6:0, 7:0, 4:0, 4:0, 7:0, 7:0, 6:0, 7:0, 8:0, 9:0, 7:0, 5:0, 9:0, 7:0, 6:0, 7:0, 4:0, 5:0, 7:0, 7:0, 5:0, 5:0, 8:0, 9:0, 6:0, 6:0, 9:0, 7:0, 6:0, 2:0$ |
| $C_212$ | $2:0, 7:0, 7:0, 7:0, 6:0, 8:0, 8:0, 8:0, 7:0, 6:0, 7:0, 5:0, 8:0, 5:0, 8:0, 4:0, 6:0, 8:0, 8:0, 8:0, 8:0, 10:0, 8:0, 8:0, 8:0, 7:0, 8:0, 6:0, 10:0, 5:0, 8:0, 2:0$ |
| $C_213$ | $3:0, 5:0, 5:0, 7:0, 5:0, 3:0, 7:0, 2:0$ |
| $C_214$ | $2:0, 3:0, 7:0, 5:0, 7:0, 5:0, 5:0, 3:0$ |
| $C_215$ | $1:0, 1:0, 2:0, 2:0, 2:0, 2:0, 3:0, 1:0$ |
| $C_216$ | $1:0, 1:0, 2:0, 2:0, 3:0, 2:0, 2:0, 1:0$ |
| $C_217$ | $1:0, 1:0, 3:0, 2:0, 1:0, 1:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 3:0, 2:0, 2:0, 1:0$ |
| $C_218$ | $2:0, 3:0, 3:0, 4:0, 3:0, 4:0, 4:0, 2:0$ |
| $C_219$ | $2:0, 2:0, 4:0, 3:0, 3:0, 2:0, 4:0, 2:0$ |
| $C_220$ | $2:0, 3:0, 3:0, 2:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_221$ | $2:0, 4:0, 4:0, 3:0, 4:0, 3:0, 3:0, 2:0$ |
| $C_222$ | $3:0, 3:0, 6:0, 4:0, 6:0, 3:0, 7:0, 2:0$ |
| $C_223$ | $3:0, 4:0, 6:0, 3:0, 6:0, 3:0, 6:0, 2:0$ |
| $C_224$ | $4:0, 6:0, 7:0, 6:0, 6:0, 4:0, 8:0, 4:0, 7:0, 6:0, 7:0, 6:0, 8:0, 4:0, 8:0, 4:0, 7:0, 6:0, 7:0, 6:0, 8:0, 4:0, 8:0, 4:0, 7:0, 6:0, 7:0, 6:0, 8:0, 4:0, 8:0, 2:0$ |
| $C_225$ | $3:0, 3:0, 4:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_226$ | $1:0, 1:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0$ |
| $C_227$ | $2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 2:0$ |
| $C_228$ | $2:0, 3:0, 6:0, 5:0, 4:0, 3:0, 5:0, 2:0$ |
| $C_229$ | $2:0, 4:0, 5:0, 3:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_230$ | $1:0, 1:0, 3:0, 3:0, 3:0, 3:0, 4:0, 3:0$ |
| $C_231$ | $2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 1:0, 4:0, 1:0$ |
| $C_232$ | $1:0, 1:0, 4:0, 4:0, 1:0, 1:0, 3:0, 2:0$ |
| $C_233$ | $2:0, 4:0, 2:6, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 6:0, 4:0, 5:0, 6:0, 6:0, 5:0, 5:0, 6:0, 6:0, 5:0, 5:0, 6:0, 4:0, 5:0, 2:0$ |
| $C_234$ | $2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:6, 2:0$ |
| $C_235$ | $2:0, 3:0, 6:0, 5:0, 4:0, 3:0, 5:0, 1:3$ |
| $C_236$ | $1:3, 3:0, 5:0, 4:0, 5:0, 3:0, 6:0, 2:0$ |
| $C_237$ | $1:3, 3:0, 4:0, 4:0, 4:0, 1:0, 4:0, 1:0$ |
| $C_238$ | $1:0, 1:0, 4:0, 4:0, 4:0, 3:0, 4:0, 1:3$ |
| $C_239$ | $2:0, 1:0, 4:0, 1:0, 3:0, 1:0, 4:0, 1:0$ |
| $C_240$ | $1:0, 1:0, 4:0, 3:0, 1:0, 1:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_241$ | $2:0, 4:0, 4:0, 4:0, 4:0, 1:5, 4:0, 2:0$ |
| $C_242$ | $2:0, 1:5, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 6:0, 5:0, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 6:0, 5:0, 4:0, 4:0, 4:0, 4:0, 6:0, 5:0, 4:0, 2:0$ |
| $C_243$ | $2:0, 3:0, 3:0, 4:0, 2:0, 3:0, 3:0, 2:0$ |
| $C_244$ | $2:0, 3:0, 4:0, 4:0, 3:0, 4:0, 5:0, 2:0$ |
| $C_245$ | $2:0, 2:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_246$ | $2:0, 3:0, 5:0, 4:0, 5:0, 3:0, 6:0, 2:0$ |
| $C_247$ | $1:0, 2:0, 2:0, 3:0, 2:0, 1:0, 2:0, 1:0$ |
| $C_248$ | $1:0, 2:0, 3:0, 2:0, 2:0, 1:0, 2:0, 1:0$ |
| $C_249$ | $1:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 1:0, 2:0, 1:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_250$ | $2:0, 3:0, 2:0, 3:0, 3:0, 4:0, 3:0, 2:0$ |
| $C_251$ | $2:0, 4:0, 3:0, 5:0, 4:0, 4:0, 5:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_252$ | $2:0, 3:0, 3:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 3:0, 5:0, 2:0$ |
| $C_253$ | $2:0, 3:0, 5:0, 5:0, 3:0, 4:0, 5:0, 3:0$ |
| $C_254$ | $2:0, 3:0, 7:0, 6:0, 4:0, 3:0, 6:0, 3:0$ |
| $C_255$ | $2:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 6:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 6:0, 7:0, 4:0$ |
| $C_256$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 2:0, 2:0, 1:0, 1:0, 2:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 2:0, 1:0$ |
| $C_257$ | $1:0, 2:0, 2:0, 2:0, 2:0, 1:0, 2:0, 1:0, 2:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 2:0, 2:0, 2:0, 2:0, 2:0, 1:0, 2:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_258$ | $1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 2:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0$ |
| $C_259$ | $1:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0, 2:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0$ |
| $C_260$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 3:0, 6:0, 4:0, 4:0, 3:0, 6:0, 4:0, 4:0, 6:0, 4:0, 6:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 6:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_261$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 6:0, 4:0, 6:0, 6:0, 6:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_262$ | $2:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 2:0$ |
| $C_263$ | $2:0, 4:0, 4:0, 6:0, 4:0, 3:0, 6:0, 4:0, 4:0, 6:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 6:0, 6:0, 4:0, 3:0, 6:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_264$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 6:0, 6:0, 6:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_265$ | $2:0, 4:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 3:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_266$ | $2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_267$ | $2:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_268$ | $2:0, 4:0, 3:0, 5:0, 4:0, 4:0, 5:0, 5:0, 3:0, 5:0, 3:0, 5:0, 3:0, 3:0, 3:0, 3:0, 3:0, 5:0, 3:0, 4:0, 5:0, 5:0, 5:0, 4:0, 3:0, 5:0, 3:0, 4:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_269$ | $2:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0, 3:0, 2:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_270$ | $2:0, 4:0, 4:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 4:0, 3:0, 4:0, 2:0$ |
| $C_271$ | $2:0, 3:0, 4:0, 5:0, 3:0, 3:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 3:0, 5:0, 3:0, 4:0, 5:0, 3:0, 4:0, 5:0, 5:0, 4:0, 4:0, 4:0, 5:0, 3:0, 4:0, 5:0, 3:0, 4:0, 2:0$ |
| $C_272$ | $2:0, 3:0, 4:0, 5:0, 3:0, 3:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 3:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_273$ | $2:0, 4:0, 4:0, 6:0, 2:0, 3:0, 3:0, 4:0, 4:0, 4:0, 6:0, 6:0, 3:0, 3:0, 4:0, 4:0, 4:0, 6:0, 4:0, 6:0, 3:0, 4:0, 3:0, 4:0, 6:0, 6:0, 6:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_274$ | $2:0, 4:0, 4:0, 4:0, 4:0, 6:0, 6:0, 6:0, 4:0, 4:0, 4:0, 4:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 3:0, 3:0, 6:0, 6:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_275$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 4:0, 6:0, 3:0, 4:0, 6:0, 6:0, 4:0, 4:0, 4:0, 6:0, 3:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_276$ | $2:0, 4:0, 4:0, 6:0, 4:0, 4:0, 6:0, 6:0, 4:0, 6:0, 4:0, 6:0, 6:0, 6:0, 6:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_277$ | $3:0, 5:0, 5:0, 5:0, 5:0, 7:0, 7:0, 7:0, 5:0, 5:0, 5:0, 5:0, 7:0, 4:0, 7:0, 4:0, 5:0, 5:0, 5:0, 5:0, 7:0, 7:0, 7:0, 7:0, 5:0, 5:0, 5:0, 5:0, 7:0, 4:0, 7:0, 2:0$ |
| $C_278$ | $3:0, 5:0, 6:0, 7:0, 5:0, 5:0, 7:0, 7:0, 6:0, 7:0, 6:0, 7:0, 7:0, 4:0, 7:0, 4:0, 6:0, 7:0, 5:0, 7:0, 7:0, 7:0, 7:0, 7:0, 6:0, 7:0, 5:0, 7:0, 7:0, 4:0, 7:0, 2:0$ |
| $C_279$ | $2:0, 4:0, 6:0, 6:0, 4:0, 4:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 6:0, 4:0, 6:0, 4:0, 6:0, 6:0, 5:0, 5:0, 6:0, 6:0, 5:0, 5:0, 6:0, 6:0, 5:0, 5:0, 6:0, 4:0, 5:0, 3:0$ |
| $C_280$ | $2:0, 4:0, 6:0, 7:0, 4:0, 4:0, 7:0, 7:0, 6:0, 7:0, 6:0, 7:0, 7:0, 7:0, 7:0, 6:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 3:0$ |
| $C_281$ | $3:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 5:0, 5:0, 5:0, 5:0, 4:0, 5:0, 3:0, 6:0, 8:0, 8:0, 8:0, 8:0, 4:0, 8:0, 4:0, 8:0, 8:0, 7:0, 7:0, 8:0, 4:0, 7:0, 2:0$ |
| $C_282$ | $2:0, 4:0, 6:0, 6:0, 3:0, 4:0, 4:0, 5:0, 4:0, 4:0, 6:0, 6:0, 4:0, 4:0, 5:0, 5:0, 6:0, 6:0, 6:0, 6:0, 4:0, 5:0, 4:0, 5:0, 6:0, 6:0, 6:0, 5:0, 5:0, 5:0, 5:0, 3:0$ |
| $C_283$ | $2:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 3:0, 4:0, 4:0, 4:0, 4:0, 1:0, 4:0, 1:0, 3:0, 3:0, 3:0, 3:0, 3:0, 1:0, 3:0, 1:0, 4:0, 4:0, 4:0, 4:0, 4:0, 1:0, 4:0, 1:0$ |
| $C_284$ | $2:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 6:0, 6:0, 6:0, 6:0, 4:0, 6:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 6:0, 6:0, 4:0, 4:0, 6:0, 4:0, 4:0, 2:0$ |
| $C_285$ | $2:0, 3:0, 4:0, 5:0, 3:0, 3:0, 5:0, 5:0, 4:0, 5:0, 4:0, 5:0, 3:0, 3:0, 3:0, 3:0, 4:0, 5:0, 4:0, 4:0, 5:0, 5:0, 5:0, 4:0, 4:0, 5:0, 4:0, 4:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_286$ | $2:0, 4:0, 6:0, 7:0, 4:0, 4:0, 7:0, 7:0, 6:0, 7:0, 6:0, 7:0, 7:0, 5:0, 7:0, 5:0, 6:0, 7:0, 4:0, 5:0, 7:0, 7:0, 5:0, 5:0, 6:0, 7:0, 4:0, 5:0, 7:0, 5:0, 5:0, 2:0$ |
| $C_287$ | $3:0, 6:0, 6:0, 7:0, 6:0, 6:0, 7:0, 7:0, 6:0, 7:0, 6:0, 7:0, 7:0, 4:0, 7:0, 4:0, 6:0, 7:0, 6:0, 7:0, 7:0, 7:0, 7:0, 7:0, 6:0, 7:0, 6:0, 7:0, 7:0, 4:0, 7:0, 2:0$ |
| $C_288$ | $2:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 6:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 5:0, 3:0$ |
| $C_289$ | $3:0, 6:0, 6:0, 6:0, 6:0, 8:0, 8:0, 8:0, 6:0, 6:0, 6:0, 6:0, 8:0, 4:0, 8:0, 4:0, 6:0, 6:0, 6:0, 6:0, 8:0, 8:0, 8:0, 8:0, 6:0, 6:0, 6:0, 6:0, 8:0, 4:0, 8:0, 2:0$ |
| $C_290$ | $2:0, 4:0, 7:0, 7:0, 4:0, 4:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 7:0, 6:0, 7:0, 6:0, 7:0, 7:0, 6:0, 6:0, 7:0, 7:0, 6:0, 6:0, 7:0, 7:0, 6:0, 6:0, 7:0, 6:0, 6:0, 3:0$ |
| $C_291$ | $2:0, 4:0, 4:0, 4:0, 5:0, 7:0, 7:0, 7:0, 4:0, 4:0, 4:0, 4:0, 7:0, 4:0, 7:0, 4:0, 4:0, 4:0, 4:0, 4:0, 7:0, 7:0, 6:0, 6:0, 4:0, 4:0, 4:0, 4:0, 7:0, 4:0, 6:0, 2:0$ |
| $C_292$ | $1:0, 1:0, 4:0, 4:0, 1:0, 1:0, 4:0, 4:0, 1:0, 1:0, 3:0, 3:0, 1:0, 1:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 3:0, 2:0$ |
| $C_293$ | $2:0, 3:0, 4:0, 4:0, 3:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 4:0, 3:0, 4:0, 3:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_294$ | $2:0, 4:0, 6:0, 7:0, 4:0, 4:0, 7:0, 7:0, 6:0, 7:0, 6:0, 7:0, 7:0, 7:0, 7:0, 5:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 4:0, 2:0$ |
| $C_295$ | $2:0, 5:0, 5:0, 7:0, 5:0, 5:0, 7:0, 7:0, 5:0, 7:0, 5:0, 7:0, 7:0, 4:0, 7:0, 4:0, 5:0, 7:0, 4:0, 6:0, 7:0, 7:0, 6:0, 6:0, 5:0, 7:0, 4:0, 6:0, 7:0, 4:0, 6:0, 2:0$ |

| $e$ | $k$ | Region $j$ | Impish action $a$ | Sequence |
|---|---|---|---|---|
| 0 | 3 | 0 | b0 | $C_1$ |
| 0 | 3 | 0 | b1 | $C_1$ |
| 0 | 3 | 1 | b0 | $C_2$ |
| 0 | 3 | 1 | b1 | $C_2$ |
| 0 | 3 | 2 | b0 | $C_2$ |
| 0 | 3 | 2 | b1 | $C_2$ |
| 0 | 3 | 3 | b0 | $C_2$ |
| 0 | 3 | 3 | b1 | $C_2$ |
| 0 | 3 | 4 | b0 | $C_2$ |
| 0 | 3 | 4 | b1 | $C_2$ |
| 0 | 3 | 5 | b0 | $C_2$ |
| 0 | 3 | 5 | b1 | $C_2$ |
| 0 | 3 | 6 | b0 | $C_2$ |
| 0 | 3 | 6 | b1 | $C_2$ |
| 0 | 5 | 0 | b0 | $C_3$ |
| 0 | 5 | 0 | b2 | $C_4$ |
| 0 | 5 | 1 | b0 | $C_2$ |
| 0 | 5 | 1 | b2 | $C_2$ |
| 0 | 5 | 2 | b0 | $C_2$ |
| 0 | 5 | 2 | b2 | $C_2$ |
| 0 | 5 | 3 | b0 | $C_2$ |
| 0 | 5 | 3 | b2 | $C_2$ |
| 0 | 5 | 4 | b0 | $C_2$ |
| 0 | 5 | 4 | b2 | $C_2$ |
| 0 | 5 | 5 | b0 | $C_2$ |
| 0 | 5 | 5 | b2 | $C_2$ |
| 0 | 5 | 6 | b0 | $C_5$ |
| 0 | 5 | 6 | b2 | $C_6$ |
| 0 | 6 | 0 | b1 | $C_3$ |
| 0 | 6 | 0 | b2 | $C_4$ |
| 0 | 6 | 1 | b1 | $C_2$ |
| 0 | 6 | 1 | b2 | $C_2$ |
| 0 | 6 | 2 | b1 | $C_2$ |
| 0 | 6 | 2 | b2 | $C_2$ |
| 0 | 6 | 3 | b1 | $C_2$ |
| 0 | 6 | 3 | b2 | $C_2$ |
| 0 | 6 | 4 | b1 | $C_2$ |
| 0 | 6 | 4 | b2 | $C_2$ |
| 0 | 6 | 5 | b1 | $C_2$ |
| 0 | 6 | 5 | b2 | $C_2$ |
| 0 | 6 | 6 | b1 | $C_5$ |
| 0 | 6 | 6 | b2 | $C_6$ |
| 0 | 9 | 0 | b0 | $C_3$ |
| 0 | 9 | 0 | b3 | $C_4$ |
| 0 | 9 | 1 | b0 | $C_2$ |
| 0 | 9 | 1 | b3 | $C_2$ |
| 0 | 9 | 2 | b0 | $C_2$ |
| 0 | 9 | 2 | b3 | $C_2$ |
| 0 | 9 | 3 | b0 | $C_2$ |
| 0 | 9 | 3 | b3 | $C_2$ |
| 0 | 9 | 4 | b0 | $C_2$ |
| 0 | 9 | 4 | b3 | $C_2$ |
| 0 | 9 | 5 | b0 | $C_2$ |
| 0 | 9 | 5 | b3 | $C_2$ |
| 0 | 9 | 6 | b0 | $C_5$ |
| 0 | 9 | 6 | b3 | $C_6$ |
| 0 | 10 | 0 | b1 | $C_3$ |
| 0 | 10 | 0 | b3 | $C_4$ |
| 0 | 10 | 1 | b1 | $C_2$ |
| 0 | 10 | 1 | b3 | $C_2$ |
| 0 | 10 | 2 | b1 | $C_2$ |
| 0 | 10 | 2 | b3 | $C_2$ |
| 0 | 10 | 3 | b1 | $C_2$ |
| 0 | 10 | 3 | b3 | $C_2$ |
| 0 | 10 | 4 | b1 | $C_2$ |
| 0 | 10 | 4 | b3 | $C_2$ |
| 0 | 10 | 5 | b1 | $C_2$ |
| 0 | 10 | 5 | b3 | $C_2$ |
| 0 | 10 | 6 | b1 | $C_5$ |
| 0 | 10 | 6 | b3 | $C_6$ |
| 0 | 12 | 0 | b2 | $C_1$ |
| 0 | 12 | 0 | b3 | $C_1$ |
| 0 | 12 | 1 | b2 | $C_2$ |
| 0 | 12 | 1 | b3 | $C_2$ |
| 0 | 12 | 2 | b2 | $C_2$ |
| 0 | 12 | 2 | b3 | $C_2$ |
| 0 | 12 | 3 | b2 | $C_2$ |
| 0 | 12 | 3 | b3 | $C_2$ |
| 0 | 12 | 4 | b2 | $C_2$ |
| 0 | 12 | 4 | b3 | $C_2$ |
| 0 | 12 | 5 | b2 | $C_2$ |
| 0 | 12 | 5 | b3 | $C_2$ |
| 0 | 12 | 6 | b2 | $C_2$ |
| 0 | 12 | 6 | b3 | $C_2$ |
| 0 | 15 | 0 | b0 | $C_7$ |
| 0 | 15 | 0 | b1 | $C_7$ |
| 0 | 15 | 0 | b2 | $C_8$ |
| 0 | 15 | 0 | b3 | $C_8$ |
| 0 | 15 | 1 | b0 | $C_9$ |
| 0 | 15 | 1 | b1 | $C_9$ |
| 0 | 15 | 1 | b2 | $C_10$ |
| 0 | 15 | 1 | b3 | $C_10$ |
| 0 | 15 | 2 | b0 | $C_9$ |
| 0 | 15 | 2 | b1 | $C_9$ |
| 0 | 15 | 2 | b2 | $C_11$ |
| 0 | 15 | 2 | b3 | $C_12$ |
| 0 | 15 | 3 | b0 | $C_13$ |
| 0 | 15 | 3 | b1 | $C_14$ |
| 0 | 15 | 3 | b2 | $C_15$ |
| 0 | 15 | 3 | b3 | $C_16$ |
| 0 | 15 | 4 | b0 | $C_17$ |
| 0 | 15 | 4 | b1 | $C_17$ |
| 0 | 15 | 4 | b2 | $C_17$ |
| 0 | 15 | 4 | b3 | $C_17$ |
| 0 | 15 | 5 | b0 | $C_18$ |
| 0 | 15 | 5 | b1 | $C_18$ |
| 0 | 15 | 5 | b2 | $C_18$ |
| 0 | 15 | 5 | b3 | $C_18$ |
| 0 | 15 | 6 | b0 | $C_19$ |
| 0 | 15 | 6 | b1 | $C_20$ |
| 0 | 15 | 6 | b2 | $C_21$ |
| 0 | 15 | 6 | b3 | $C_22$ |
| 1 | 0 | 0 | L | $C_3$ |
| 1 | 0 | 0 | R | $C_4$ |
| 1 | 0 | 1 | L | $C_2$ |
| 1 | 0 | 1 | R | $C_2$ |
| 1 | 0 | 2 | L | $C_2$ |
| 1 | 0 | 2 | R | $C_2$ |
| 1 | 0 | 3 | L | $C_2$ |
| 1 | 0 | 3 | R | $C_2$ |
| 1 | 0 | 4 | L | $C_2$ |
| 1 | 0 | 4 | R | $C_2$ |
| 1 | 0 | 5 | L | $C_2$ |
| 1 | 0 | 5 | R | $C_2$ |
| 1 | 0 | 6 | L | $C_5$ |
| 1 | 0 | 6 | R | $C_6$ |
| 1 | 3 | 0 | b0 | $C_23$ |
| 1 | 3 | 0 | b1 | $C_24$ |
| 1 | 3 | 0 | L | $C_25$ |
| 1 | 3 | 0 | R | $C_4$ |
| 1 | 3 | 1 | b0 | $C_26$ |
| 1 | 3 | 1 | b1 | $C_27$ |
| 1 | 3 | 1 | L | $C_10$ |
| 1 | 3 | 1 | R | $C_2$ |
| 1 | 3 | 2 | b0 | $C_26$ |
| 1 | 3 | 2 | b1 | $C_27$ |
| 1 | 3 | 2 | L | $C_10$ |
| 1 | 3 | 2 | R | $C_2$ |
| 1 | 3 | 3 | b0 | $C_28$ |
| 1 | 3 | 3 | b1 | $C_29$ |
| 1 | 3 | 3 | L | $C_11$ |
| 1 | 3 | 3 | R | $C_2$ |
| 1 | 3 | 4 | b0 | $C_30$ |
| 1 | 3 | 4 | b1 | $C_31$ |
| 1 | 3 | 4 | L | $C_17$ |
| 1 | 3 | 4 | R | $C_2$ |
| 1 | 3 | 5 | b0 | $C_32$ |
| 1 | 3 | 5 | b1 | $C_14$ |
| 1 | 3 | 5 | L | $C_18$ |
| 1 | 3 | 5 | R | $C_2$ |
| 1 | 3 | 6 | b0 | $C_33$ |
| 1 | 3 | 6 | b1 | $C_34$ |
| 1 | 3 | 6 | L | $C_35$ |
| 1 | 3 | 6 | R | $C_6$ |
| 1 | 5 | 0 | b0 | $C_36$ |
| 1 | 5 | 0 | b2 | $C_37$ |
| 1 | 5 | 0 | L | $C_7$ |
| 1 | 5 | 0 | R | $C_8$ |
| 1 | 5 | 1 | b0 | $C_12$ |
| 1 | 5 | 1 | b2 | $C_27$ |
| 1 | 5 | 1 | L | $C_9$ |
| 1 | 5 | 1 | R | $C_10$ |
| 1 | 5 | 2 | b0 | $C_12$ |
| 1 | 5 | 2 | b2 | $C_29$ |
| 1 | 5 | 2 | L | $C_9$ |
| 1 | 5 | 2 | R | $C_12$ |
| 1 | 5 | 3 | b0 | $C_29$ |
| 1 | 5 | 3 | b2 | $C_38$ |
| 1 | 5 | 3 | L | $C_14$ |
| 1 | 5 | 3 | R | $C_16$ |
| 1 | 5 | 4 | b0 | $C_39$ |
| 1 | 5 | 4 | b2 | $C_31$ |
| 1 | 5 | 4 | L | $C_17$ |
| 1 | 5 | 4 | R | $C_17$ |
| 1 | 5 | 5 | b0 | $C_13$ |
| 1 | 5 | 5 | b2 | $C_14$ |
| 1 | 5 | 5 | L | $C_18$ |
| 1 | 5 | 5 | R | $C_18$ |
| 1 | 5 | 6 | b0 | $C_40$ |
| 1 | 5 | 6 | b2 | $C_41$ |
| 1 | 5 | 6 | L | $C_42$ |
| 1 | 5 | 6 | R | $C_43$ |
| 1 | 6 | 0 | b1 | $C_36$ |
| 1 | 6 | 0 | b2 | $C_8$ |
| 1 | 6 | 0 | L | $C_7$ |
| 1 | 6 | 0 | R | $C_1$ |
| 1 | 6 | 1 | b1 | $C_12$ |
| 1 | 6 | 1 | b2 | $C_26$ |
| 1 | 6 | 1 | L | $C_9$ |
| 1 | 6 | 1 | R | $C_2$ |
| 1 | 6 | 2 | b1 | $C_12$ |
| 1 | 6 | 2 | b2 | $C_28$ |
| 1 | 6 | 2 | L | $C_9$ |
| 1 | 6 | 2 | R | $C_2$ |
| 1 | 6 | 3 | b1 | $C_29$ |
| 1 | 6 | 3 | b2 | $C_44$ |
| 1 | 6 | 3 | L | $C_13$ |
| 1 | 6 | 3 | R | $C_2$ |
| 1 | 6 | 4 | b1 | $C_39$ |
| 1 | 6 | 4 | b2 | $C_30$ |
| 1 | 6 | 4 | L | $C_17$ |
| 1 | 6 | 4 | R | $C_2$ |
| 1 | 6 | 5 | b1 | $C_13$ |
| 1 | 6 | 5 | b2 | $C_32$ |
| 1 | 6 | 5 | L | $C_18$ |
| 1 | 6 | 5 | R | $C_2$ |
| 1 | 6 | 6 | b1 | $C_45$ |
| 1 | 6 | 6 | b2 | $C_46$ |
| 1 | 6 | 6 | L | $C_47$ |
| 1 | 6 | 6 | R | $C_2$ |
| 1 | 9 | 0 | b0 | $C_48$ |
| 1 | 9 | 0 | b3 | $C_37$ |
| 1 | 9 | 0 | L | $C_1$ |
| 1 | 9 | 0 | R | $C_8$ |
| 1 | 9 | 1 | b0 | $C_10$ |
| 1 | 9 | 1 | b3 | $C_27$ |
| 1 | 9 | 1 | L | $C_2$ |
| 1 | 9 | 1 | R | $C_10$ |
| 1 | 9 | 2 | b0 | $C_10$ |
| 1 | 9 | 2 | b3 | $C_29$ |
| 1 | 9 | 2 | L | $C_2$ |
| 1 | 9 | 2 | R | $C_11$ |
| 1 | 9 | 3 | b0 | $C_28$ |
| 1 | 9 | 3 | b3 | $C_38$ |
| 1 | 9 | 3 | L | $C_2$ |
| 1 | 9 | 3 | R | $C_15$ |
| 1 | 9 | 4 | b0 | $C_49$ |
| 1 | 9 | 4 | b3 | $C_31$ |
| 1 | 9 | 4 | L | $C_2$ |
| 1 | 9 | 4 | R | $C_17$ |
| 1 | 9 | 5 | b0 | $C_9$ |
| 1 | 9 | 5 | b3 | $C_14$ |
| 1 | 9 | 5 | L | $C_2$ |
| 1 | 9 | 5 | R | $C_18$ |
| 1 | 9 | 6 | b0 | $C_50$ |
| 1 | 9 | 6 | b3 | $C_51$ |
| 1 | 9 | 6 | L | $C_2$ |
| 1 | 9 | 6 | R | $C_52$ |
| 1 | 10 | 0 | b1 | $C_48$ |
| 1 | 10 | 0 | b3 | $C_8$ |
| 1 | 10 | 0 | L | $C_1$ |
| 1 | 10 | 0 | R | $C_1$ |
| 1 | 10 | 1 | b1 | $C_10$ |
| 1 | 10 | 1 | b3 | $C_26$ |
| 1 | 10 | 1 | L | $C_2$ |
| 1 | 10 | 1 | R | $C_2$ |
| 1 | 10 | 2 | b1 | $C_10$ |
| 1 | 10 | 2 | b3 | $C_28$ |
| 1 | 10 | 2 | L | $C_2$ |
| 1 | 10 | 2 | R | $C_2$ |
| 1 | 10 | 3 | b1 | $C_28$ |
| 1 | 10 | 3 | b3 | $C_44$ |
| 1 | 10 | 3 | L | $C_2$ |
| 1 | 10 | 3 | R | $C_2$ |
| 1 | 10 | 4 | b1 | $C_49$ |
| 1 | 10 | 4 | b3 | $C_30$ |
| 1 | 10 | 4 | L | $C_2$ |
| 1 | 10 | 4 | R | $C_2$ |
| 1 | 10 | 5 | b1 | $C_9$ |
| 1 | 10 | 5 | b3 | $C_32$ |
| 1 | 10 | 5 | L | $C_2$ |
| 1 | 10 | 5 | R | $C_2$ |
| 1 | 10 | 6 | b1 | $C_50$ |
| 1 | 10 | 6 | b3 | $C_46$ |
| 1 | 10 | 6 | L | $C_2$ |
| 1 | 10 | 6 | R | $C_2$ |
| 1 | 12 | 0 | b2 | $C_53$ |
| 1 | 12 | 0 | b3 | $C_54$ |
| 1 | 12 | 0 | L | $C_3$ |
| 1 | 12 | 0 | R | $C_55$ |
| 1 | 12 | 1 | b2 | $C_10$ |
| 1 | 12 | 1 | b3 | $C_12$ |
| 1 | 12 | 1 | L | $C_2$ |
| 1 | 12 | 1 | R | $C_9$ |
| 1 | 12 | 2 | b2 | $C_10$ |
| 1 | 12 | 2 | b3 | $C_12$ |
| 1 | 12 | 2 | L | $C_2$ |
| 1 | 12 | 2 | R | $C_9$ |
| 1 | 12 | 3 | b2 | $C_28$ |
| 1 | 12 | 3 | b3 | $C_29$ |
| 1 | 12 | 3 | L | $C_2$ |
| 1 | 12 | 3 | R | $C_13$ |
| 1 | 12 | 4 | b2 | $C_49$ |
| 1 | 12 | 4 | b3 | $C_39$ |
| 1 | 12 | 4 | L | $C_2$ |
| 1 | 12 | 4 | R | $C_17$ |
| 1 | 12 | 5 | b2 | $C_9$ |
| 1 | 12 | 5 | b3 | $C_13$ |
| 1 | 12 | 5 | L | $C_2$ |
| 1 | 12 | 5 | R | $C_18$ |
| 1 | 12 | 6 | b2 | $C_56$ |
| 1 | 12 | 6 | b3 | $C_57$ |
| 1 | 12 | 6 | L | $C_5$ |
| 1 | 12 | 6 | R | $C_58$ |
| 1 | 15 | 0 | b0 | $C_59$ |
| 1 | 15 | 0 | b1 | $C_60$ |
| 1 | 15 | 0 | b2 | $C_61$ |
| 1 | 15 | 0 | b3 | $C_62$ |
| 1 | 15 | 0 | L | $C_63$ |
| 1 | 15 | 0 | R | $C_64$ |
| 1 | 15 | 1 | b0 | $C_65$ |
| 1 | 15 | 1 | b1 | $C_66$ |
| 1 | 15 | 1 | b2 | $C_67$ |
| 1 | 15 | 1 | b3 | $C_68$ |
| 1 | 15 | 1 | L | $C_10$ |
| 1 | 15 | 1 | R | $C_9$ |
| 1 | 15 | 2 | b0 | $C_69$ |
| 1 | 15 | 2 | b1 | $C_70$ |
| 1 | 15 | 2 | b2 | $C_71$ |
| 1 | 15 | 2 | b3 | $C_68$ |
| 1 | 15 | 2 | L | $C_10$ |
| 1 | 15 | 2 | R | $C_9$ |
| 1 | 15 | 3 | b0 | $C_72$ |
| 1 | 15 | 3 | b1 | $C_73$ |
| 1 | 15 | 3 | b2 | $C_74$ |
| 1 | 15 | 3 | b3 | $C_75$ |
| 1 | 15 | 3 | L | $C_12$ |
| 1 | 15 | 3 | R | $C_14$ |
| 1 | 15 | 4 | b0 | $C_76$ |
| 1 | 15 | 4 | b1 | $C_77$ |
| 1 | 15 | 4 | b2 | $C_78$ |
| 1 | 15 | 4 | b3 | $C_79$ |
| 1 | 15 | 4 | L | $C_17$ |
| 1 | 15 | 4 | R | $C_17$ |
| 1 | 15 | 5 | b0 | $C_80$ |
| 1 | 15 | 5 | b1 | $C_81$ |
| 1 | 15 | 5 | b2 | $C_82$ |
| 1 | 15 | 5 | b3 | $C_83$ |
| 1 | 15 | 5 | L | $C_18$ |
| 1 | 15 | 5 | R | $C_18$ |
| 1 | 15 | 6 | b0 | $C_84$ |
| 1 | 15 | 6 | b1 | $C_85$ |
| 1 | 15 | 6 | b2 | $C_86$ |
| 1 | 15 | 6 | b3 | $C_87$ |
| 1 | 15 | 6 | L | $C_88$ |
| 1 | 15 | 6 | R | $C_89$ |
| 2 | 0 | 0 | L | $C_48$ |
| 2 | 0 | 0 | R | $C_8$ |
| 2 | 0 | 1 | L | $C_10$ |
| 2 | 0 | 1 | R | $C_26$ |
| 2 | 0 | 2 | L | $C_10$ |
| 2 | 0 | 2 | R | $C_28$ |
| 2 | 0 | 3 | L | $C_28$ |
| 2 | 0 | 3 | R | $C_44$ |
| 2 | 0 | 4 | L | $C_49$ |
| 2 | 0 | 4 | R | $C_30$ |
| 2 | 0 | 5 | L | $C_9$ |
| 2 | 0 | 5 | R | $C_32$ |
| 2 | 0 | 6 | L | $C_50$ |
| 2 | 0 | 6 | R | $C_46$ |
| 2 | 3 | 0 | b0 | $C_90$ |
| 2 | 3 | 0 | b1 | $C_91$ |
| 2 | 3 | 0 | L | $C_92$ |
| 2 | 3 | 0 | R | $C_37$ |
| 2 | 3 | 1 | b0 | $C_93$ |
| 2 | 3 | 1 | b1 | $C_14$ |
| 2 | 3 | 1 | L | $C_67$ |
| 2 | 3 | 1 | R | $C_27$ |
| 2 | 3 | 2 | b0 | $C_94$ |
| 2 | 3 | 2 | b1 | $C_14$ |
| 2 | 3 | 2 | L | $C_71$ |
| 2 | 3 | 2 | R | $C_29$ |
| 2 | 3 | 3 | b0 | $C_13$ |
| 2 | 3 | 3 | b1 | $C_14$ |
| 2 | 3 | 3 | L | $C_74$ |
| 2 | 3 | 3 | R | $C_38$ |
| 2 | 3 | 4 | b0 | $C_27$ |
| 2 | 3 | 4 | b1 | $C_95$ |
| 2 | 3 | 4 | L | $C_78$ |
| 2 | 3 | 4 | R | $C_31$ |
| 2 | 3 | 5 | b0 | $C_27$ |
| 2 | 3 | 5 | b1 | $C_96$ |
| 2 | 3 | 5 | L | $C_82$ |
| 2 | 3 | 5 | R | $C_14$ |
| 2 | 3 | 6 | b0 | $C_97$ |
| 2 | 3 | 6 | b1 | $C_98$ |
| 2 | 3 | 6 | L | $C_99$ |
| 2 | 3 | 6 | R | $C_51$ |
| 2 | 5 | 0 | b0 | $C_100$ |
| 2 | 5 | 0 | b2 | $C_101$ |
| 2 | 5 | 0 | L | $C_60$ |
| 2 | 5 | 0 | R | $C_62$ |
| 2 | 5 | 1 | b0 | $C_102$ |
| 2 | 5 | 1 | b2 | $C_14$ |
| 2 | 5 | 1 | L | $C_66$ |
| 2 | 5 | 1 | R | $C_68$ |
| 2 | 5 | 2 | b0 | $C_102$ |
| 2 | 5 | 2 | b2 | $C_14$ |
| 2 | 5 | 2 | L | $C_70$ |
| 2 | 5 | 2 | R | $C_68$ |
| 2 | 5 | 3 | b0 | $C_12$ |
| 2 | 5 | 3 | b2 | $C_14$ |
| 2 | 5 | 3 | L | $C_73$ |
| 2 | 5 | 3 | R | $C_75$ |
| 2 | 5 | 4 | b0 | $C_12$ |
| 2 | 5 | 4 | b2 | $C_95$ |
| 2 | 5 | 4 | L | $C_77$ |
| 2 | 5 | 4 | R | $C_79$ |
| 2 | 5 | 5 | b0 | $C_12$ |
| 2 | 5 | 5 | b2 | $C_94$ |
| 2 | 5 | 5 | L | $C_81$ |
| 2 | 5 | 5 | R | $C_83$ |
| 2 | 5 | 6 | b0 | $C_103$ |
| 2 | 5 | 6 | b2 | $C_104$ |
| 2 | 5 | 6 | L | $C_85$ |
| 2 | 5 | 6 | R | $C_87$ |
| 2 | 6 | 0 | b1 | $C_100$ |
| 2 | 6 | 0 | b2 | $C_105$ |
| 2 | 6 | 0 | L | $C_59$ |
| 2 | 6 | 0 | R | $C_54$ |
| 2 | 6 | 1 | b1 | $C_102$ |
| 2 | 6 | 1 | b2 | $C_94$ |
| 2 | 6 | 1 | L | $C_65$ |
| 2 | 6 | 1 | R | $C_12$ |
| 2 | 6 | 2 | b1 | $C_102$ |
| 2 | 6 | 2 | b2 | $C_94$ |
| 2 | 6 | 2 | L | $C_69$ |
| 2 | 6 | 2 | R | $C_12$ |
| 2 | 6 | 3 | b1 | $C_12$ |
| 2 | 6 | 3 | b2 | $C_13$ |
| 2 | 6 | 3 | L | $C_72$ |
| 2 | 6 | 3 | R | $C_29$ |
| 2 | 6 | 4 | b1 | $C_12$ |
| 2 | 6 | 4 | b2 | $C_27$ |
| 2 | 6 | 4 | L | $C_76$ |
| 2 | 6 | 4 | R | $C_39$ |
| 2 | 6 | 5 | b1 | $C_12$ |
| 2 | 6 | 5 | b2 | $C_27$ |
| 2 | 6 | 5 | L | $C_80$ |
| 2 | 6 | 5 | R | $C_13$ |
| 2 | 6 | 6 | b1 | $C_103$ |
| 2 | 6 | 6 | b2 | $C_106$ |
| 2 | 6 | 6 | L | $C_84$ |
| 2 | 6 | 6 | R | $C_57$ |
| 2 | 9 | 0 | b0 | $C_107$ |
| 2 | 9 | 0 | b3 | $C_101$ |
| 2 | 9 | 0 | L | $C_24$ |
| 2 | 9 | 0 | R | $C_61$ |
| 2 | 9 | 1 | b0 | $C_13$ |
| 2 | 9 | 1 | b3 | $C_14$ |
| 2 | 9 | 1 | L | $C_27$ |
| 2 | 9 | 1 | R | $C_67$ |
| 2 | 9 | 2 | b0 | $C_13$ |
| 2 | 9 | 2 | b3 | $C_14$ |
| 2 | 9 | 2 | L | $C_27$ |
| 2 | 9 | 2 | R | $C_71$ |
| 2 | 9 | 3 | b0 | $C_27$ |
| 2 | 9 | 3 | b3 | $C_14$ |
| 2 | 9 | 3 | L | $C_29$ |
| 2 | 9 | 3 | R | $C_74$ |
| 2 | 9 | 4 | b0 | $C_108$ |
| 2 | 9 | 4 | b3 | $C_95$ |
| 2 | 9 | 4 | L | $C_31$ |
| 2 | 9 | 4 | R | $C_78$ |
| 2 | 9 | 5 | b0 | $C_102$ |
| 2 | 9 | 5 | b3 | $C_94$ |
| 2 | 9 | 5 | L | $C_14$ |
| 2 | 9 | 5 | R | $C_82$ |
| 2 | 9 | 6 | b0 | $C_109$ |
| 2 | 9 | 6 | b3 | $C_104$ |
| 2 | 9 | 6 | L | $C_34$ |
| 2 | 9 | 6 | R | $C_86$ |
| 2 | 10 | 0 | b1 | $C_107$ |
| 2 | 10 | 0 | b3 | $C_105$ |
| 2 | 10 | 0 | L | $C_23$ |
| 2 | 10 | 0 | R | $C_53$ |
| 2 | 10 | 1 | b1 | $C_13$ |
| 2 | 10 | 1 | b3 | $C_94$ |
| 2 | 10 | 1 | L | $C_26$ |
| 2 | 10 | 1 | R | $C_10$ |
| 2 | 10 | 2 | b1 | $C_13$ |
| 2 | 10 | 2 | b3 | $C_94$ |
| 2 | 10 | 2 | L | $C_26$ |
| 2 | 10 | 2 | R | $C_10$ |
| 2 | 10 | 3 | b1 | $C_27$ |
| 2 | 10 | 3 | b3 | $C_13$ |
| 2 | 10 | 3 | L | $C_28$ |
| 2 | 10 | 3 | R | $C_28$ |
| 2 | 10 | 4 | b1 | $C_108$ |
| 2 | 10 | 4 | b3 | $C_27$ |
| 2 | 10 | 4 | L | $C_30$ |
| 2 | 10 | 4 | R | $C_49$ |
| 2 | 10 | 5 | b1 | $C_102$ |
| 2 | 10 | 5 | b3 | $C_27$ |
| 2 | 10 | 5 | L | $C_32$ |
| 2 | 10 | 5 | R | $C_9$ |
| 2 | 10 | 6 | b1 | $C_109$ |
| 2 | 10 | 6 | b3 | $C_106$ |
| 2 | 10 | 6 | L | $C_33$ |
| 2 | 10 | 6 | R | $C_56$ |
| 2 | 12 | 0 | b2 | $C_110$ |
| 2 | 12 | 0 | b3 | $C_111$ |
| 2 | 12 | 0 | L | $C_36$ |
| 2 | 12 | 0 | R | $C_112$ |
| 2 | 12 | 1 | b2 | $C_13$ |
| 2 | 12 | 1 | b3 | $C_102$ |
| 2 | 12 | 1 | L | $C_12$ |
| 2 | 12 | 1 | R | $C_69$ |
| 2 | 12 | 2 | b2 | $C_27$ |
| 2 | 12 | 2 | b3 | $C_12$ |
| 2 | 12 | 2 | L | $C_12$ |
| 2 | 12 | 2 | R | $C_113$ |
| 2 | 12 | 3 | b2 | $C_102$ |
| 2 | 12 | 3 | b3 | $C_114$ |
| 2 | 12 | 3 | L | $C_29$ |
| 2 | 12 | 3 | R | $C_115$ |
| 2 | 12 | 4 | b2 | $C_116$ |
| 2 | 12 | 4 | b3 | $C_12$ |
| 2 | 12 | 4 | L | $C_39$ |
| 2 | 12 | 4 | R | $C_117$ |
| 2 | 12 | 5 | b2 | $C_118$ |
| 2 | 12 | 5 | b3 | $C_12$ |
| 2 | 12 | 5 | L | $C_13$ |
| 2 | 12 | 5 | R | $C_80$ |
| 2 | 12 | 6 | b2 | $C_119$ |
| 2 | 12 | 6 | b3 | $C_120$ |
| 2 | 12 | 6 | L | $C_40$ |
| 2 | 12 | 6 | R | $C_121$ |
| 2 | 15 | 0 | b0 | $C_122$ |
| 2 | 15 | 0 | b1 | $C_123$ |
| 2 | 15 | 0 | b2 | $C_124$ |
| 2 | 15 | 0 | b3 | $C_125$ |
| 2 | 15 | 0 | L | $C_126$ |
| 2 | 15 | 0 | R | $C_127$ |
| 2 | 15 | 1 | b0 | $C_128$ |
| 2 | 15 | 1 | b1 | $C_129$ |
| 2 | 15 | 1 | b2 | $C_130$ |
| 2 | 15 | 1 | b3 | $C_131$ |
| 2 | 15 | 1 | L | $C_68$ |
| 2 | 15 | 1 | R | $C_70$ |
| 2 | 15 | 2 | b0 | $C_132$ |
| 2 | 15 | 2 | b1 | $C_133$ |
| 2 | 15 | 2 | b2 | $C_134$ |
| 2 | 15 | 2 | b3 | $C_135$ |
| 2 | 15 | 2 | L | $C_68$ |
| 2 | 15 | 2 | R | $C_73$ |
| 2 | 15 | 3 | b0 | $C_136$ |
| 2 | 15 | 3 | b1 | $C_137$ |
| 2 | 15 | 3 | b2 | $C_138$ |
| 2 | 15 | 3 | b3 | $C_139$ |
| 2 | 15 | 3 | L | $C_75$ |
| 2 | 15 | 3 | R | $C_140$ |
| 2 | 15 | 4 | b0 | $C_141$ |
| 2 | 15 | 4 | b1 | $C_142$ |
| 2 | 15 | 4 | b2 | $C_143$ |
| 2 | 15 | 4 | b3 | $C_144$ |
| 2 | 15 | 4 | L | $C_79$ |
| 2 | 15 | 4 | R | $C_77$ |
| 2 | 15 | 5 | b0 | $C_145$ |
| 2 | 15 | 5 | b1 | $C_146$ |
| 2 | 15 | 5 | b2 | $C_147$ |
| 2 | 15 | 5 | b3 | $C_148$ |
| 2 | 15 | 5 | L | $C_83$ |
| 2 | 15 | 5 | R | $C_81$ |
| 2 | 15 | 6 | b0 | $C_149$ |
| 2 | 15 | 6 | b1 | $C_150$ |
| 2 | 15 | 6 | b2 | $C_151$ |
| 2 | 15 | 6 | b3 | $C_152$ |
| 2 | 15 | 6 | L | $C_153$ |
| 2 | 15 | 6 | R | $C_154$ |
| 3 | 0 | 0 | L | $C_107$ |
| 3 | 0 | 0 | R | $C_105$ |
| 3 | 0 | 1 | L | $C_13$ |
| 3 | 0 | 1 | R | $C_94$ |
| 3 | 0 | 2 | L | $C_13$ |
| 3 | 0 | 2 | R | $C_94$ |
| 3 | 0 | 3 | L | $C_27$ |
| 3 | 0 | 3 | R | $C_13$ |
| 3 | 0 | 4 | L | $C_108$ |
| 3 | 0 | 4 | R | $C_27$ |
| 3 | 0 | 5 | L | $C_102$ |
| 3 | 0 | 5 | R | $C_27$ |
| 3 | 0 | 6 | L | $C_109$ |
| 3 | 0 | 6 | R | $C_106$ |
| 3 | 3 | 0 | b0 | $C_24$ |
| 3 | 3 | 0 | b1 | $C_63$ |
| 3 | 3 | 0 | L | $C_155$ |
| 3 | 3 | 0 | R | $C_101$ |
| 3 | 3 | 1 | b0 | $C_94$ |
| 3 | 3 | 1 | b1 | $C_156$ |
| 3 | 3 | 1 | L | $C_157$ |
| 3 | 3 | 1 | R | $C_14$ |
| 3 | 3 | 2 | b0 | $C_94$ |
| 3 | 3 | 2 | b1 | $C_156$ |
| 3 | 3 | 2 | L | $C_130$ |
| 3 | 3 | 2 | R | $C_14$ |
| 3 | 3 | 3 | b0 | $C_14$ |
| 3 | 3 | 3 | b1 | $C_11$ |
| 3 | 3 | 3 | L | $C_134$ |
| 3 | 3 | 3 | R | $C_14$ |
| 3 | 3 | 4 | b0 | $C_31$ |
| 3 | 3 | 4 | b1 | $C_158$ |
| 3 | 3 | 4 | L | $C_159$ |
| 3 | 3 | 4 | R | $C_95$ |
| 3 | 3 | 5 | b0 | $C_94$ |
| 3 | 3 | 5 | b1 | $C_160$ |
| 3 | 3 | 5 | L | $C_147$ |
| 3 | 3 | 5 | R | $C_94$ |
| 3 | 3 | 6 | b0 | $C_161$ |
| 3 | 3 | 6 | b1 | $C_162$ |
| 3 | 3 | 6 | L | $C_163$ |
| 3 | 3 | 6 | R | $C_104$ |
| 3 | 5 | 0 | b0 | $C_48$ |
| 3 | 5 | 0 | b2 | $C_8$ |
| 3 | 5 | 0 | L | $C_123$ |
| 3 | 5 | 0 | R | $C_125$ |
| 3 | 5 | 1 | b0 | $C_160$ |
| 3 | 5 | 1 | b2 | $C_156$ |
| 3 | 5 | 1 | L | $C_129$ |
| 3 | 5 | 1 | R | $C_131$ |
| 3 | 5 | 2 | b0 | $C_160$ |
| 3 | 5 | 2 | b2 | $C_11$ |
| 3 | 5 | 2 | L | $C_133$ |
| 3 | 5 | 2 | R | $C_135$ |
| 3 | 5 | 3 | b0 | $C_11$ |
| 3 | 5 | 3 | b2 | $C_164$ |
| 3 | 5 | 3 | L | $C_137$ |
| 3 | 5 | 3 | R | $C_139$ |
| 3 | 5 | 4 | b0 | $C_165$ |
| 3 | 5 | 4 | b2 | $C_158$ |
| 3 | 5 | 4 | L | $C_142$ |
| 3 | 5 | 4 | R | $C_144$ |
| 3 | 5 | 5 | b0 | $C_166$ |
| 3 | 5 | 5 | b2 | $C_160$ |
| 3 | 5 | 5 | L | $C_146$ |
| 3 | 5 | 5 | R | $C_148$ |
| 3 | 5 | 6 | b0 | $C_167$ |
| 3 | 5 | 6 | b2 | $C_168$ |
| 3 | 5 | 6 | L | $C_150$ |
| 3 | 5 | 6 | R | $C_152$ |
| 3 | 6 | 0 | b1 | $C_48$ |
| 3 | 6 | 0 | b2 | $C_37$ |
| 3 | 6 | 0 | L | $C_122$ |
| 3 | 6 | 0 | R | $C_111$ |
| 3 | 6 | 1 | b1 | $C_160$ |
| 3 | 6 | 1 | b2 | $C_94$ |
| 3 | 6 | 1 | L | $C_128$ |
| 3 | 6 | 1 | R | $C_102$ |
| 3 | 6 | 2 | b1 | $C_160$ |
| 3 | 6 | 2 | b2 | $C_14$ |
| 3 | 6 | 2 | L | $C_132$ |
| 3 | 6 | 2 | R | $C_12$ |
| 3 | 6 | 3 | b1 | $C_11$ |
| 3 | 6 | 3 | b2 | $C_38$ |
| 3 | 6 | 3 | L | $C_136$ |
| 3 | 6 | 3 | R | $C_114$ |
| 3 | 6 | 4 | b1 | $C_165$ |
| 3 | 6 | 4 | b2 | $C_169$ |
| 3 | 6 | 4 | L | $C_141$ |
| 3 | 6 | 4 | R | $C_12$ |
| 3 | 6 | 5 | b1 | $C_166$ |
| 3 | 6 | 5 | b2 | $C_96$ |
| 3 | 6 | 5 | L | $C_145$ |
| 3 | 6 | 5 | R | $C_12$ |
| 3 | 6 | 6 | b1 | $C_167$ |
| 3 | 6 | 6 | b2 | $C_170$ |
| 3 | 6 | 6 | L | $C_149$ |
| 3 | 6 | 6 | R | $C_120$ |
| 3 | 9 | 0 | b0 | $C_36$ |
| 3 | 9 | 0 | b3 | $C_8$ |
| 3 | 9 | 0 | L | $C_91$ |
| 3 | 9 | 0 | R | $C_124$ |
| 3 | 9 | 1 | b0 | $C_171$ |
| 3 | 9 | 1 | b3 | $C_156$ |
| 3 | 9 | 1 | L | $C_14$ |
| 3 | 9 | 1 | R | $C_130$ |
| 3 | 9 | 2 | b0 | $C_12$ |
| 3 | 9 | 2 | b3 | $C_11$ |
| 3 | 9 | 2 | L | $C_14$ |
| 3 | 9 | 2 | R | $C_134$ |
| 3 | 9 | 3 | b0 | $C_12$ |
| 3 | 9 | 3 | b3 | $C_164$ |
| 3 | 9 | 3 | L | $C_14$ |
| 3 | 9 | 3 | R | $C_138$ |
| 3 | 9 | 4 | b0 | $C_108$ |
| 3 | 9 | 4 | b3 | $C_158$ |
| 3 | 9 | 4 | L | $C_95$ |
| 3 | 9 | 4 | R | $C_143$ |
| 3 | 9 | 5 | b0 | $C_102$ |
| 3 | 9 | 5 | b3 | $C_160$ |
| 3 | 9 | 5 | L | $C_94$ |
| 3 | 9 | 5 | R | $C_147$ |
| 3 | 9 | 6 | b0 | $C_172$ |
| 3 | 9 | 6 | b3 | $C_168$ |
| 3 | 9 | 6 | L | $C_173$ |
| 3 | 9 | 6 | R | $C_151$ |
| 3 | 10 | 0 | b1 | $C_36$ |
| 3 | 10 | 0 | b3 | $C_37$ |
| 3 | 10 | 0 | L | $C_90$ |
| 3 | 10 | 0 | R | $C_110$ |
| 3 | 10 | 1 | b1 | $C_102$ |
| 3 | 10 | 1 | b3 | $C_94$ |
| 3 | 10 | 1 | L | $C_94$ |
| 3 | 10 | 1 | R | $C_13$ |
| 3 | 10 | 2 | b1 | $C_12$ |
| 3 | 10 | 2 | b3 | $C_14$ |
| 3 | 10 | 2 | L | $C_94$ |
| 3 | 10 | 2 | R | $C_27$ |
| 3 | 10 | 3 | b1 | $C_12$ |
| 3 | 10 | 3 | b3 | $C_38$ |
| 3 | 10 | 3 | L | $C_13$ |
| 3 | 10 | 3 | R | $C_102$ |
| 3 | 10 | 4 | b1 | $C_108$ |
| 3 | 10 | 4 | b3 | $C_95$ |
| 3 | 10 | 4 | L | $C_27$ |
| 3 | 10 | 4 | R | $C_108$ |
| 3 | 10 | 5 | b1 | $C_118$ |
| 3 | 10 | 5 | b3 | $C_94$ |
| 3 | 10 | 5 | L | $C_27$ |
| 3 | 10 | 5 | R | $C_102$ |
| 3 | 10 | 6 | b1 | $C_174$ |
| 3 | 10 | 6 | b3 | $C_175$ |
| 3 | 10 | 6 | L | $C_97$ |
| 3 | 10 | 6 | R | $C_176$ |
| 3 | 12 | 0 | b2 | $C_54$ |
| 3 | 12 | 0 | b3 | $C_177$ |
| 3 | 12 | 0 | L | $C_100$ |
| 3 | 12 | 0 | R | $C_178$ |
| 3 | 12 | 1 | b2 | $C_102$ |
| 3 | 12 | 1 | b3 | $C_160$ |
| 3 | 12 | 1 | L | $C_102$ |
| 3 | 12 | 1 | R | $C_128$ |
| 3 | 12 | 2 | b2 | $C_12$ |
| 3 | 12 | 2 | b3 | $C_160$ |
| 3 | 12 | 2 | L | $C_102$ |
| 3 | 12 | 2 | R | $C_132$ |
| 3 | 12 | 3 | b2 | $C_12$ |
| 3 | 12 | 3 | b3 | $C_11$ |
| 3 | 12 | 3 | L | $C_12$ |
| 3 | 12 | 3 | R | $C_136$ |
| 3 | 12 | 4 | b2 | $C_108$ |
| 3 | 12 | 4 | b3 | $C_165$ |
| 3 | 12 | 4 | L | $C_12$ |
| 3 | 12 | 4 | R | $C_141$ |
| 3 | 12 | 5 | b2 | $C_102$ |
| 3 | 12 | 5 | b3 | $C_166$ |
| 3 | 12 | 5 | L | $C_12$ |
| 3 | 12 | 5 | R | $C_145$ |
| 3 | 12 | 6 | b2 | $C_179$ |
| 3 | 12 | 6 | b3 | $C_180$ |
| 3 | 12 | 6 | L | $C_103$ |
| 3 | 12 | 6 | R | $C_181$ |
| 3 | 15 | 0 | b0 | $C_182$ |
| 3 | 15 | 0 | b1 | $C_183$ |
| 3 | 15 | 0 | b2 | $C_184$ |
| 3 | 15 | 0 | b3 | $C_185$ |
| 3 | 15 | 0 | L | $C_186$ |
| 3 | 15 | 0 | R | $C_187$ |
| 3 | 15 | 1 | b0 | $C_188$ |
| 3 | 15 | 1 | b1 | $C_189$ |
| 3 | 15 | 1 | b2 | $C_190$ |
| 3 | 15 | 1 | b3 | $C_191$ |
| 3 | 15 | 1 | L | $C_192$ |
| 3 | 15 | 1 | R | $C_129$ |
| 3 | 15 | 2 | b0 | $C_193$ |
| 3 | 15 | 2 | b1 | $C_194$ |
| 3 | 15 | 2 | b2 | $C_195$ |
| 3 | 15 | 2 | b3 | $C_71$ |
| 3 | 15 | 2 | L | $C_196$ |
| 3 | 15 | 2 | R | $C_133$ |
| 3 | 15 | 3 | b0 | $C_73$ |
| 3 | 15 | 3 | b1 | $C_197$ |
| 3 | 15 | 3 | b2 | $C_75$ |
| 3 | 15 | 3 | b3 | $C_198$ |
| 3 | 15 | 3 | L | $C_199$ |
| 3 | 15 | 3 | R | $C_137$ |
| 3 | 15 | 4 | b0 | $C_200$ |
| 3 | 15 | 4 | b1 | $C_76$ |
| 3 | 15 | 4 | b2 | $C_201$ |
| 3 | 15 | 4 | b3 | $C_202$ |
| 3 | 15 | 4 | L | $C_203$ |
| 3 | 15 | 4 | R | $C_142$ |
| 3 | 15 | 5 | b0 | $C_204$ |
| 3 | 15 | 5 | b1 | $C_133$ |
| 3 | 15 | 5 | b2 | $C_205$ |
| 3 | 15 | 5 | b3 | $C_206$ |
| 3 | 15 | 5 | L | $C_148$ |
| 3 | 15 | 5 | R | $C_146$ |
| 3 | 15 | 6 | b0 | $C_207$ |
| 3 | 15 | 6 | b1 | $C_208$ |
| 3 | 15 | 6 | b2 | $C_209$ |
| 3 | 15 | 6 | b3 | $C_210$ |
| 3 | 15 | 6 | L | $C_211$ |
| 3 | 15 | 6 | R | $C_212$ |
| 4 | 0 | 0 | L | $C_36$ |
| 4 | 0 | 0 | R | $C_37$ |
| 4 | 0 | 1 | L | $C_171$ |
| 4 | 0 | 1 | R | $C_94$ |
| 4 | 0 | 2 | L | $C_12$ |
| 4 | 0 | 2 | R | $C_14$ |
| 4 | 0 | 3 | L | $C_12$ |
| 4 | 0 | 3 | R | $C_38$ |
| 4 | 0 | 4 | L | $C_108$ |
| 4 | 0 | 4 | R | $C_169$ |
| 4 | 0 | 5 | L | $C_118$ |
| 4 | 0 | 5 | R | $C_96$ |
| 4 | 0 | 6 | L | $C_213$ |
| 4 | 0 | 6 | R | $C_214$ |
| 4 | 3 | 0 | b0 | $C_215$ |
| 4 | 3 | 0 | b1 | $C_216$ |
| 4 | 3 | 0 | L | $C_217$ |
| 4 | 3 | 0 | R | $C_8$ |
| 4 | 3 | 1 | b0 | $C_218$ |
| 4 | 3 | 1 | b1 | $C_32$ |
| 4 | 3 | 1 | L | $C_190$ |
| 4 | 3 | 1 | R | $C_156$ |
| 4 | 3 | 2 | b0 | $C_218$ |
| 4 | 3 | 2 | b1 | $C_14$ |
| 4 | 3 | 2 | L | $C_195$ |
| 4 | 3 | 2 | R | $C_11$ |
| 4 | 3 | 3 | b0 | $C_28$ |
| 4 | 3 | 3 | b1 | $C_29$ |
| 4 | 3 | 3 | L | $C_75$ |
| 4 | 3 | 3 | R | $C_164$ |
| 4 | 3 | 4 | b0 | $C_219$ |
| 4 | 3 | 4 | b1 | $C_220$ |
| 4 | 3 | 4 | L | $C_201$ |
| 4 | 3 | 4 | R | $C_158$ |
| 4 | 3 | 5 | b0 | $C_10$ |
| 4 | 3 | 5 | b1 | $C_221$ |
| 4 | 3 | 5 | L | $C_205$ |
| 4 | 3 | 5 | R | $C_160$ |
| 4 | 3 | 6 | b0 | $C_222$ |
| 4 | 3 | 6 | b1 | $C_223$ |
| 4 | 3 | 6 | L | $C_224$ |
| 4 | 3 | 6 | R | $C_168$ |
| 4 | 5 | 0 | b0 | $C_225$ |
| 4 | 5 | 0 | b2 | $C_226$ |
| 4 | 5 | 0 | L | $C_183$ |
| 4 | 5 | 0 | R | $C_185$ |
| 4 | 5 | 1 | b0 | $C_221$ |
| 4 | 5 | 1 | b2 | $C_32$ |
| 4 | 5 | 1 | L | $C_189$ |
| 4 | 5 | 1 | R | $C_191$ |
| 4 | 5 | 2 | b0 | $C_221$ |
| 4 | 5 | 2 | b2 | $C_14$ |
| 4 | 5 | 2 | L | $C_194$ |
| 4 | 5 | 2 | R | $C_71$ |
| 4 | 5 | 3 | b0 | $C_29$ |
| 4 | 5 | 3 | b2 | $C_29$ |
| 4 | 5 | 3 | L | $C_197$ |
| 4 | 5 | 3 | R | $C_198$ |
| 4 | 5 | 4 | b0 | $C_227$ |
| 4 | 5 | 4 | b2 | $C_220$ |
| 4 | 5 | 4 | L | $C_76$ |
| 4 | 5 | 4 | R | $C_202$ |
| 4 | 5 | 5 | b0 | $C_10$ |
| 4 | 5 | 5 | b2 | $C_221$ |
| 4 | 5 | 5 | L | $C_133$ |
| 4 | 5 | 5 | R | $C_206$ |
| 4 | 5 | 6 | b0 | $C_228$ |
| 4 | 5 | 6 | b2 | $C_229$ |
| 4 | 5 | 6 | L | $C_208$ |
| 4 | 5 | 6 | R | $C_210$ |
| 4 | 6 | 0 | b1 | $C_225$ |
| 4 | 6 | 0 | b2 | $C_230$ |
| 4 | 6 | 0 | L | $C_231$ |
| 4 | 6 | 0 | R | $C_232$ |
| 4 | 6 | 1 | b1 | $C_221$ |
| 4 | 6 | 1 | b2 | $C_218$ |
| 4 | 6 | 1 | L | $C_188$ |
| 4 | 6 | 1 | R | $C_160$ |
| 4 | 6 | 2 | b1 | $C_221$ |
| 4 | 6 | 2 | b2 | $C_218$ |
| 4 | 6 | 2 | L | $C_193$ |
| 4 | 6 | 2 | R | $C_160$ |
| 4 | 6 | 3 | b1 | $C_29$ |
| 4 | 6 | 3 | b2 | $C_28$ |
| 4 | 6 | 3 | L | $C_73$ |
| 4 | 6 | 3 | R | $C_11$ |
| 4 | 6 | 4 | b1 | $C_227$ |
| 4 | 6 | 4 | b2 | $C_219$ |
| 4 | 6 | 4 | L | $C_200$ |
| 4 | 6 | 4 | R | $C_165$ |
| 4 | 6 | 5 | b1 | $C_10$ |
| 4 | 6 | 5 | b2 | $C_10$ |
| 4 | 6 | 5 | L | $C_233$ |
| 4 | 6 | 5 | R | $C_234$ |
| 4 | 6 | 6 | b1 | $C_235$ |
| 4 | 6 | 6 | b2 | $C_236$ |
| 4 | 6 | 6 | L | $C_207$ |
| 4 | 6 | 6 | R | $C_180$ |
| 4 | 9 | 0 | b0 | $C_237$ |
| 4 | 9 | 0 | b3 | $C_238$ |
| 4 | 9 | 0 | L | $C_239$ |
| 4 | 9 | 0 | R | $C_240$ |
| 4 | 9 | 1 | b0 | $C_32$ |
| 4 | 9 | 1 | b3 | $C_32$ |
| 4 | 9 | 1 | L | $C_241$ |
| 4 | 9 | 1 | R | $C_242$ |
| 4 | 9 | 2 | b0 | $C_32$ |
| 4 | 9 | 2 | b3 | $C_14$ |
| 4 | 9 | 2 | L | $C_156$ |
| 4 | 9 | 2 | R | $C_195$ |
| 4 | 9 | 3 | b0 | $C_28$ |
| 4 | 9 | 3 | b3 | $C_29$ |
| 4 | 9 | 3 | L | $C_11$ |
| 4 | 9 | 3 | R | $C_75$ |
| 4 | 9 | 4 | b0 | $C_243$ |
| 4 | 9 | 4 | b3 | $C_220$ |
| 4 | 9 | 4 | L | $C_158$ |
| 4 | 9 | 4 | R | $C_201$ |
| 4 | 9 | 5 | b0 | $C_218$ |
| 4 | 9 | 5 | b3 | $C_221$ |
| 4 | 9 | 5 | L | $C_160$ |
| 4 | 9 | 5 | R | $C_205$ |
| 4 | 9 | 6 | b0 | $C_244$ |
| 4 | 9 | 6 | b3 | $C_229$ |
| 4 | 9 | 6 | L | $C_162$ |
| 4 | 9 | 6 | R | $C_209$ |
| 4 | 10 | 0 | b1 | $C_245$ |
| 4 | 10 | 0 | b3 | $C_230$ |
| 4 | 10 | 0 | L | $C_24$ |
| 4 | 10 | 0 | R | $C_54$ |
| 4 | 10 | 1 | b1 | $C_32$ |
| 4 | 10 | 1 | b3 | $C_218$ |
| 4 | 10 | 1 | L | $C_94$ |
| 4 | 10 | 1 | R | $C_102$ |
| 4 | 10 | 2 | b1 | $C_32$ |
| 4 | 10 | 2 | b3 | $C_218$ |
| 4 | 10 | 2 | L | $C_94$ |
| 4 | 10 | 2 | R | $C_12$ |
| 4 | 10 | 3 | b1 | $C_28$ |
| 4 | 10 | 3 | b3 | $C_28$ |
| 4 | 10 | 3 | L | $C_14$ |
| 4 | 10 | 3 | R | $C_12$ |
| 4 | 10 | 4 | b1 | $C_243$ |
| 4 | 10 | 4 | b3 | $C_219$ |
| 4 | 10 | 4 | L | $C_31$ |
| 4 | 10 | 4 | R | $C_108$ |
| 4 | 10 | 5 | b1 | $C_218$ |
| 4 | 10 | 5 | b3 | $C_10$ |
| 4 | 10 | 5 | L | $C_94$ |
| 4 | 10 | 5 | R | $C_102$ |
| 4 | 10 | 6 | b1 | $C_244$ |
| 4 | 10 | 6 | b3 | $C_246$ |
| 4 | 10 | 6 | L | $C_161$ |
| 4 | 10 | 6 | R | $C_179$ |
| 4 | 12 | 0 | b2 | $C_247$ |
| 4 | 12 | 0 | b3 | $C_248$ |
| 4 | 12 | 0 | L | $C_48$ |
| 4 | 12 | 0 | R | $C_249$ |
| 4 | 12 | 1 | b2 | $C_32$ |
| 4 | 12 | 1 | b3 | $C_221$ |
| 4 | 12 | 1 | L | $C_160$ |
| 4 | 12 | 1 | R | $C_193$ |
| 4 | 12 | 2 | b2 | $C_28$ |
| 4 | 12 | 2 | b3 | $C_29$ |
| 4 | 12 | 2 | L | $C_160$ |
| 4 | 12 | 2 | R | $C_73$ |
| 4 | 12 | 3 | b2 | $C_250$ |
| 4 | 12 | 3 | b3 | $C_114$ |
| 4 | 12 | 3 | L | $C_11$ |
| 4 | 12 | 3 | R | $C_251$ |
| 4 | 12 | 4 | b2 | $C_243$ |
| 4 | 12 | 4 | b3 | $C_219$ |
| 4 | 12 | 4 | L | $C_165$ |
| 4 | 12 | 4 | R | $C_252$ |
| 4 | 12 | 5 | b2 | $C_218$ |
| 4 | 12 | 5 | b3 | $C_10$ |
| 4 | 12 | 5 | L | $C_166$ |
| 4 | 12 | 5 | R | $C_204$ |
| 4 | 12 | 6 | b2 | $C_253$ |
| 4 | 12 | 6 | b3 | $C_254$ |
| 4 | 12 | 6 | L | $C_167$ |
| 4 | 12 | 6 | R | $C_255$ |
| 4 | 15 | 0 | b0 | $C_123$ |
| 4 | 15 | 0 | b1 | $C_256$ |
| 4 | 15 | 0 | b2 | $C_257$ |
| 4 | 15 | 0 | b3 | $C_124$ |
| 4 | 15 | 0 | L | $C_258$ |
| 4 | 15 | 0 | R | $C_259$ |
| 4 | 15 | 1 | b0 | $C_260$ |
| 4 | 15 | 1 | b1 | $C_261$ |
| 4 | 15 | 1 | b2 | $C_262$ |
| 4 | 15 | 1 | b3 | $C_263$ |
| 4 | 15 | 1 | L | $C_191$ |
| 4 | 15 | 1 | R | $C_194$ |
| 4 | 15 | 2 | b0 | $C_264$ |
| 4 | 15 | 2 | b1 | $C_265$ |
| 4 | 15 | 2 | b2 | $C_266$ |
| 4 | 15 | 2 | b3 | $C_134$ |
| 4 | 15 | 2 | L | $C_71$ |
| 4 | 15 | 2 | R | $C_197$ |
| 4 | 15 | 3 | b0 | $C_267$ |
| 4 | 15 | 3 | b1 | $C_136$ |
| 4 | 15 | 3 | b2 | $C_268$ |
| 4 | 15 | 3 | b3 | $C_269$ |
| 4 | 15 | 3 | L | $C_198$ |
| 4 | 15 | 3 | R | $C_115$ |
| 4 | 15 | 4 | b0 | $C_270$ |
| 4 | 15 | 4 | b1 | $C_271$ |
| 4 | 15 | 4 | b2 | $C_271$ |
| 4 | 15 | 4 | b3 | $C_272$ |
| 4 | 15 | 4 | L | $C_202$ |
| 4 | 15 | 4 | R | $C_273$ |
| 4 | 15 | 5 | b0 | $C_274$ |
| 4 | 15 | 5 | b1 | $C_275$ |
| 4 | 15 | 5 | b2 | $C_275$ |
| 4 | 15 | 5 | b3 | $C_276$ |
| 4 | 15 | 5 | L | $C_206$ |
| 4 | 15 | 5 | R | $C_133$ |
| 4 | 15 | 6 | b0 | $C_277$ |
| 4 | 15 | 6 | b1 | $C_278$ |
| 4 | 15 | 6 | b2 | $C_279$ |
| 4 | 15 | 6 | b3 | $C_280$ |
| 4 | 15 | 6 | L | $C_281$ |
| 4 | 15 | 6 | R | $C_282$ |
| 5 | 0 | 0 | L | $C_245$ |
| 5 | 0 | 0 | R | $C_230$ |
| 5 | 0 | 1 | L | $C_32$ |
| 5 | 0 | 1 | R | $C_218$ |
| 5 | 0 | 2 | L | $C_32$ |
| 5 | 0 | 2 | R | $C_218$ |
| 5 | 0 | 3 | L | $C_28$ |
| 5 | 0 | 3 | R | $C_28$ |
| 5 | 0 | 4 | L | $C_243$ |
| 5 | 0 | 4 | R | $C_219$ |
| 5 | 0 | 5 | L | $C_218$ |
| 5 | 0 | 5 | R | $C_10$ |
| 5 | 0 | 6 | L | $C_244$ |
| 5 | 0 | 6 | R | $C_246$ |
| 5 | 3 | 0 | b0 | $C_23$ |
| 5 | 3 | 0 | b1 | $C_24$ |
| 5 | 3 | 0 | L | $C_283$ |
| 5 | 3 | 0 | R | $C_226$ |
| 5 | 3 | 1 | b0 | $C_26$ |
| 5 | 3 | 1 | b1 | $C_27$ |
| 5 | 3 | 1 | L | $C_284$ |
| 5 | 3 | 1 | R | $C_32$ |
| 5 | 3 | 2 | b0 | $C_26$ |
| 5 | 3 | 2 | b1 | $C_27$ |
| 5 | 3 | 2 | L | $C_262$ |
| 5 | 3 | 2 | R | $C_14$ |
| 5 | 3 | 3 | b0 | $C_28$ |
| 5 | 3 | 3 | b1 | $C_29$ |
| 5 | 3 | 3 | L | $C_266$ |
| 5 | 3 | 3 | R | $C_29$ |
| 5 | 3 | 4 | b0 | $C_30$ |
| 5 | 3 | 4 | b1 | $C_31$ |
| 5 | 3 | 4 | L | $C_285$ |
| 5 | 3 | 4 | R | $C_220$ |
| 5 | 3 | 5 | b0 | $C_32$ |
| 5 | 3 | 5 | b1 | $C_14$ |
| 5 | 3 | 5 | L | $C_275$ |
| 5 | 3 | 5 | R | $C_221$ |
| 5 | 3 | 6 | b0 | $C_33$ |
| 5 | 3 | 6 | b1 | $C_34$ |
| 5 | 3 | 6 | L | $C_286$ |
| 5 | 3 | 6 | R | $C_229$ |
| 5 | 5 | 0 | b0 | $C_36$ |
| 5 | 5 | 0 | b2 | $C_37$ |
| 5 | 5 | 0 | L | $C_256$ |
| 5 | 5 | 0 | R | $C_124$ |
| 5 | 5 | 1 | b0 | $C_12$ |
| 5 | 5 | 1 | b2 | $C_27$ |
| 5 | 5 | 1 | L | $C_261$ |
| 5 | 5 | 1 | R | $C_263$ |
| 5 | 5 | 2 | b0 | $C_12$ |
| 5 | 5 | 2 | b2 | $C_29$ |
| 5 | 5 | 2 | L | $C_265$ |
| 5 | 5 | 2 | R | $C_134$ |
| 5 | 5 | 3 | b0 | $C_29$ |
| 5 | 5 | 3 | b2 | $C_38$ |
| 5 | 5 | 3 | L | $C_136$ |
| 5 | 5 | 3 | R | $C_269$ |
| 5 | 5 | 4 | b0 | $C_39$ |
| 5 | 5 | 4 | b2 | $C_31$ |
| 5 | 5 | 4 | L | $C_271$ |
| 5 | 5 | 4 | R | $C_272$ |
| 5 | 5 | 5 | b0 | $C_13$ |
| 5 | 5 | 5 | b2 | $C_14$ |
| 5 | 5 | 5 | L | $C_275$ |
| 5 | 5 | 5 | R | $C_276$ |
| 5 | 5 | 6 | b0 | $C_40$ |
| 5 | 5 | 6 | b2 | $C_41$ |
| 5 | 5 | 6 | L | $C_287$ |
| 5 | 5 | 6 | R | $C_288$ |
| 5 | 6 | 0 | b1 | $C_36$ |
| 5 | 6 | 0 | b2 | $C_8$ |
| 5 | 6 | 0 | L | $C_123$ |
| 5 | 6 | 0 | R | $C_248$ |
| 5 | 6 | 1 | b1 | $C_12$ |
| 5 | 6 | 1 | b2 | $C_26$ |
| 5 | 6 | 1 | L | $C_260$ |
| 5 | 6 | 1 | R | $C_221$ |
| 5 | 6 | 2 | b1 | $C_12$ |
| 5 | 6 | 2 | b2 | $C_28$ |
| 5 | 6 | 2 | L | $C_264$ |
| 5 | 6 | 2 | R | $C_29$ |
| 5 | 6 | 3 | b1 | $C_29$ |
| 5 | 6 | 3 | b2 | $C_44$ |
| 5 | 6 | 3 | L | $C_267$ |
| 5 | 6 | 3 | R | $C_114$ |
| 5 | 6 | 4 | b1 | $C_39$ |
| 5 | 6 | 4 | b2 | $C_30$ |
| 5 | 6 | 4 | L | $C_270$ |
| 5 | 6 | 4 | R | $C_219$ |
| 5 | 6 | 5 | b1 | $C_13$ |
| 5 | 6 | 5 | b2 | $C_32$ |
| 5 | 6 | 5 | L | $C_274$ |
| 5 | 6 | 5 | R | $C_10$ |
| 5 | 6 | 6 | b1 | $C_45$ |
| 5 | 6 | 6 | b2 | $C_46$ |
| 5 | 6 | 6 | L | $C_289$ |
| 5 | 6 | 6 | R | $C_254$ |
| 5 | 9 | 0 | b0 | $C_48$ |
| 5 | 9 | 0 | b3 | $C_37$ |
| 5 | 9 | 0 | L | $C_216$ |
| 5 | 9 | 0 | R | $C_257$ |
| 5 | 9 | 1 | b0 | $C_10$ |
| 5 | 9 | 1 | b3 | $C_27$ |
| 5 | 9 | 1 | L | $C_32$ |
| 5 | 9 | 1 | R | $C_262$ |
| 5 | 9 | 2 | b0 | $C_10$ |
| 5 | 9 | 2 | b3 | $C_29$ |
| 5 | 9 | 2 | L | $C_14$ |
| 5 | 9 | 2 | R | $C_266$ |
| 5 | 9 | 3 | b0 | $C_28$ |
| 5 | 9 | 3 | b3 | $C_38$ |
| 5 | 9 | 3 | L | $C_29$ |
| 5 | 9 | 3 | R | $C_268$ |
| 5 | 9 | 4 | b0 | $C_49$ |
| 5 | 9 | 4 | b3 | $C_31$ |
| 5 | 9 | 4 | L | $C_220$ |
| 5 | 9 | 4 | R | $C_271$ |
| 5 | 9 | 5 | b0 | $C_9$ |
| 5 | 9 | 5 | b3 | $C_14$ |
| 5 | 9 | 5 | L | $C_221$ |
| 5 | 9 | 5 | R | $C_275$ |
| 5 | 9 | 6 | b0 | $C_50$ |
| 5 | 9 | 6 | b3 | $C_51$ |
| 5 | 9 | 6 | L | $C_223$ |
| 5 | 9 | 6 | R | $C_290$ |
| 5 | 10 | 0 | b1 | $C_48$ |
| 5 | 10 | 0 | b3 | $C_8$ |
| 5 | 10 | 0 | L | $C_215$ |
| 5 | 10 | 0 | R | $C_247$ |
| 5 | 10 | 1 | b1 | $C_10$ |
| 5 | 10 | 1 | b3 | $C_26$ |
| 5 | 10 | 1 | L | $C_218$ |
| 5 | 10 | 1 | R | $C_32$ |
| 5 | 10 | 2 | b1 | $C_10$ |
| 5 | 10 | 2 | b3 | $C_28$ |
| 5 | 10 | 2 | L | $C_218$ |
| 5 | 10 | 2 | R | $C_28$ |
| 5 | 10 | 3 | b1 | $C_28$ |
| 5 | 10 | 3 | b3 | $C_44$ |
| 5 | 10 | 3 | L | $C_28$ |
| 5 | 10 | 3 | R | $C_250$ |
| 5 | 10 | 4 | b1 | $C_49$ |
| 5 | 10 | 4 | b3 | $C_30$ |
| 5 | 10 | 4 | L | $C_219$ |
| 5 | 10 | 4 | R | $C_243$ |
| 5 | 10 | 5 | b1 | $C_9$ |
| 5 | 10 | 5 | b3 | $C_32$ |
| 5 | 10 | 5 | L | $C_10$ |
| 5 | 10 | 5 | R | $C_218$ |
| 5 | 10 | 6 | b1 | $C_50$ |
| 5 | 10 | 6 | b3 | $C_46$ |
| 5 | 10 | 6 | L | $C_222$ |
| 5 | 10 | 6 | R | $C_253$ |
| 5 | 12 | 0 | b2 | $C_53$ |
| 5 | 12 | 0 | b3 | $C_54$ |
| 5 | 12 | 0 | L | $C_225$ |
| 5 | 12 | 0 | R | $C_187$ |
| 5 | 12 | 1 | b2 | $C_10$ |
| 5 | 12 | 1 | b3 | $C_12$ |
| 5 | 12 | 1 | L | $C_221$ |
| 5 | 12 | 1 | R | $C_260$ |
| 5 | 12 | 2 | b2 | $C_10$ |
| 5 | 12 | 2 | b3 | $C_12$ |
| 5 | 12 | 2 | L | $C_221$ |
| 5 | 12 | 2 | R | $C_264$ |
| 5 | 12 | 3 | b2 | $C_28$ |
| 5 | 12 | 3 | b3 | $C_29$ |
| 5 | 12 | 3 | L | $C_29$ |
| 5 | 12 | 3 | R | $C_267$ |
| 5 | 12 | 4 | b2 | $C_49$ |
| 5 | 12 | 4 | b3 | $C_39$ |
| 5 | 12 | 4 | L | $C_227$ |
| 5 | 12 | 4 | R | $C_270$ |
| 5 | 12 | 5 | b2 | $C_9$ |
| 5 | 12 | 5 | b3 | $C_13$ |
| 5 | 12 | 5 | L | $C_10$ |
| 5 | 12 | 5 | R | $C_274$ |
| 5 | 12 | 6 | b2 | $C_56$ |
| 5 | 12 | 6 | b3 | $C_57$ |
| 5 | 12 | 6 | L | $C_228$ |
| 5 | 12 | 6 | R | $C_291$ |
| 5 | 15 | 0 | b0 | $C_59$ |
| 5 | 15 | 0 | b1 | $C_60$ |
| 5 | 15 | 0 | b2 | $C_61$ |
| 5 | 15 | 0 | b3 | $C_62$ |
| 5 | 15 | 0 | L | $C_155$ |
| 5 | 15 | 0 | R | $C_292$ |
| 5 | 15 | 1 | b0 | $C_65$ |
| 5 | 15 | 1 | b1 | $C_66$ |
| 5 | 15 | 1 | b2 | $C_67$ |
| 5 | 15 | 1 | b3 | $C_68$ |
| 5 | 15 | 1 | L | $C_263$ |
| 5 | 15 | 1 | R | $C_261$ |
| 5 | 15 | 2 | b0 | $C_69$ |
| 5 | 15 | 2 | b1 | $C_70$ |
| 5 | 15 | 2 | b2 | $C_71$ |
| 5 | 15 | 2 | b3 | $C_68$ |
| 5 | 15 | 2 | L | $C_263$ |
| 5 | 15 | 2 | R | $C_265$ |
| 5 | 15 | 3 | b0 | $C_72$ |
| 5 | 15 | 3 | b1 | $C_73$ |
| 5 | 15 | 3 | b2 | $C_74$ |
| 5 | 15 | 3 | b3 | $C_75$ |
| 5 | 15 | 3 | L | $C_134$ |
| 5 | 15 | 3 | R | $C_136$ |
| 5 | 15 | 4 | b0 | $C_76$ |
| 5 | 15 | 4 | b1 | $C_77$ |
| 5 | 15 | 4 | b2 | $C_78$ |
| 5 | 15 | 4 | b3 | $C_79$ |
| 5 | 15 | 4 | L | $C_293$ |
| 5 | 15 | 4 | R | $C_271$ |
| 5 | 15 | 5 | b0 | $C_80$ |
| 5 | 15 | 5 | b1 | $C_81$ |
| 5 | 15 | 5 | b2 | $C_82$ |
| 5 | 15 | 5 | b3 | $C_83$ |
| 5 | 15 | 5 | L | $C_276$ |
| 5 | 15 | 5 | R | $C_275$ |
| 5 | 15 | 6 | b0 | $C_84$ |
| 5 | 15 | 6 | b1 | $C_85$ |
| 5 | 15 | 6 | b2 | $C_86$ |
| 5 | 15 | 6 | b3 | $C_87$ |
| 5 | 15 | 6 | L | $C_294$ |
| 5 | 15 | 6 | R | $C_295$ |
| 6 | 0 | 0 | L | $C_48$ |
| 6 | 0 | 0 | R | $C_8$ |
| 6 | 0 | 1 | L | $C_10$ |
| 6 | 0 | 1 | R | $C_26$ |
| 6 | 0 | 2 | L | $C_10$ |
| 6 | 0 | 2 | R | $C_28$ |
| 6 | 0 | 3 | L | $C_28$ |
| 6 | 0 | 3 | R | $C_44$ |
| 6 | 0 | 4 | L | $C_49$ |
| 6 | 0 | 4 | R | $C_30$ |
| 6 | 0 | 5 | L | $C_9$ |
| 6 | 0 | 5 | R | $C_32$ |
| 6 | 0 | 6 | L | $C_50$ |
| 6 | 0 | 6 | R | $C_46$ |
| 6 | 3 | 0 | b0 | $C_90$ |
| 6 | 3 | 0 | b1 | $C_91$ |
| 6 | 3 | 0 | L | $C_92$ |
| 6 | 3 | 0 | R | $C_37$ |
| 6 | 3 | 1 | b0 | $C_93$ |
| 6 | 3 | 1 | b1 | $C_14$ |
| 6 | 3 | 1 | L | $C_67$ |
| 6 | 3 | 1 | R | $C_27$ |
| 6 | 3 | 2 | b0 | $C_94$ |
| 6 | 3 | 2 | b1 | $C_14$ |
| 6 | 3 | 2 | L | $C_71$ |
| 6 | 3 | 2 | R | $C_29$ |
| 6 | 3 | 3 | b0 | $C_13$ |
| 6 | 3 | 3 | b1 | $C_14$ |
| 6 | 3 | 3 | L | $C_74$ |
| 6 | 3 | 3 | R | $C_38$ |
| 6 | 3 | 4 | b0 | $C_27$ |
| 6 | 3 | 4 | b1 | $C_95$ |
| 6 | 3 | 4 | L | $C_78$ |
| 6 | 3 | 4 | R | $C_31$ |
| 6 | 3 | 5 | b0 | $C_27$ |
| 6 | 3 | 5 | b1 | $C_96$ |
| 6 | 3 | 5 | L | $C_82$ |
| 6 | 3 | 5 | R | $C_14$ |
| 6 | 3 | 6 | b0 | $C_97$ |
| 6 | 3 | 6 | b1 | $C_98$ |
| 6 | 3 | 6 | L | $C_99$ |
| 6 | 3 | 6 | R | $C_51$ |
| 6 | 5 | 0 | b0 | $C_100$ |
| 6 | 5 | 0 | b2 | $C_101$ |
| 6 | 5 | 0 | L | $C_60$ |
| 6 | 5 | 0 | R | $C_62$ |
| 6 | 5 | 1 | b0 | $C_102$ |
| 6 | 5 | 1 | b2 | $C_14$ |
| 6 | 5 | 1 | L | $C_66$ |
| 6 | 5 | 1 | R | $C_68$ |
| 6 | 5 | 2 | b0 | $C_102$ |
| 6 | 5 | 2 | b2 | $C_14$ |
| 6 | 5 | 2 | L | $C_70$ |
| 6 | 5 | 2 | R | $C_68$ |
| 6 | 5 | 3 | b0 | $C_12$ |
| 6 | 5 | 3 | b2 | $C_14$ |
| 6 | 5 | 3 | L | $C_73$ |
| 6 | 5 | 3 | R | $C_75$ |
| 6 | 5 | 4 | b0 | $C_12$ |
| 6 | 5 | 4 | b2 | $C_95$ |
| 6 | 5 | 4 | L | $C_77$ |
| 6 | 5 | 4 | R | $C_79$ |
| 6 | 5 | 5 | b0 | $C_12$ |
| 6 | 5 | 5 | b2 | $C_94$ |
| 6 | 5 | 5 | L | $C_81$ |
| 6 | 5 | 5 | R | $C_83$ |
| 6 | 5 | 6 | b0 | $C_103$ |
| 6 | 5 | 6 | b2 | $C_104$ |
| 6 | 5 | 6 | L | $C_85$ |
| 6 | 5 | 6 | R | $C_87$ |
| 6 | 6 | 0 | b1 | $C_100$ |
| 6 | 6 | 0 | b2 | $C_105$ |
| 6 | 6 | 0 | L | $C_59$ |
| 6 | 6 | 0 | R | $C_54$ |
| 6 | 6 | 1 | b1 | $C_102$ |
| 6 | 6 | 1 | b2 | $C_94$ |
| 6 | 6 | 1 | L | $C_65$ |
| 6 | 6 | 1 | R | $C_12$ |
| 6 | 6 | 2 | b1 | $C_102$ |
| 6 | 6 | 2 | b2 | $C_94$ |
| 6 | 6 | 2 | L | $C_69$ |
| 6 | 6 | 2 | R | $C_12$ |
| 6 | 6 | 3 | b1 | $C_12$ |
| 6 | 6 | 3 | b2 | $C_13$ |
| 6 | 6 | 3 | L | $C_72$ |
| 6 | 6 | 3 | R | $C_29$ |
| 6 | 6 | 4 | b1 | $C_12$ |
| 6 | 6 | 4 | b2 | $C_27$ |
| 6 | 6 | 4 | L | $C_76$ |
| 6 | 6 | 4 | R | $C_39$ |
| 6 | 6 | 5 | b1 | $C_12$ |
| 6 | 6 | 5 | b2 | $C_27$ |
| 6 | 6 | 5 | L | $C_80$ |
| 6 | 6 | 5 | R | $C_13$ |
| 6 | 6 | 6 | b1 | $C_103$ |
| 6 | 6 | 6 | b2 | $C_106$ |
| 6 | 6 | 6 | L | $C_84$ |
| 6 | 6 | 6 | R | $C_57$ |
| 6 | 9 | 0 | b0 | $C_107$ |
| 6 | 9 | 0 | b3 | $C_101$ |
| 6 | 9 | 0 | L | $C_24$ |
| 6 | 9 | 0 | R | $C_61$ |
| 6 | 9 | 1 | b0 | $C_13$ |
| 6 | 9 | 1 | b3 | $C_14$ |
| 6 | 9 | 1 | L | $C_27$ |
| 6 | 9 | 1 | R | $C_67$ |
| 6 | 9 | 2 | b0 | $C_13$ |
| 6 | 9 | 2 | b3 | $C_14$ |
| 6 | 9 | 2 | L | $C_27$ |
| 6 | 9 | 2 | R | $C_71$ |
| 6 | 9 | 3 | b0 | $C_27$ |
| 6 | 9 | 3 | b3 | $C_14$ |
| 6 | 9 | 3 | L | $C_29$ |
| 6 | 9 | 3 | R | $C_74$ |
| 6 | 9 | 4 | b0 | $C_108$ |
| 6 | 9 | 4 | b3 | $C_95$ |
| 6 | 9 | 4 | L | $C_31$ |
| 6 | 9 | 4 | R | $C_78$ |
| 6 | 9 | 5 | b0 | $C_102$ |
| 6 | 9 | 5 | b3 | $C_94$ |
| 6 | 9 | 5 | L | $C_14$ |
| 6 | 9 | 5 | R | $C_82$ |
| 6 | 9 | 6 | b0 | $C_109$ |
| 6 | 9 | 6 | b3 | $C_104$ |
| 6 | 9 | 6 | L | $C_34$ |
| 6 | 9 | 6 | R | $C_86$ |
| 6 | 10 | 0 | b1 | $C_107$ |
| 6 | 10 | 0 | b3 | $C_105$ |
| 6 | 10 | 0 | L | $C_23$ |
| 6 | 10 | 0 | R | $C_53$ |
| 6 | 10 | 1 | b1 | $C_13$ |
| 6 | 10 | 1 | b3 | $C_94$ |
| 6 | 10 | 1 | L | $C_26$ |
| 6 | 10 | 1 | R | $C_10$ |
| 6 | 10 | 2 | b1 | $C_13$ |
| 6 | 10 | 2 | b3 | $C_94$ |
| 6 | 10 | 2 | L | $C_26$ |
| 6 | 10 | 2 | R | $C_10$ |
| 6 | 10 | 3 | b1 | $C_27$ |
| 6 | 10 | 3 | b3 | $C_13$ |
| 6 | 10 | 3 | L | $C_28$ |
| 6 | 10 | 3 | R | $C_28$ |
| 6 | 10 | 4 | b1 | $C_108$ |
| 6 | 10 | 4 | b3 | $C_27$ |
| 6 | 10 | 4 | L | $C_30$ |
| 6 | 10 | 4 | R | $C_49$ |
| 6 | 10 | 5 | b1 | $C_102$ |
| 6 | 10 | 5 | b3 | $C_27$ |
| 6 | 10 | 5 | L | $C_32$ |
| 6 | 10 | 5 | R | $C_9$ |
| 6 | 10 | 6 | b1 | $C_109$ |
| 6 | 10 | 6 | b3 | $C_106$ |
| 6 | 10 | 6 | L | $C_33$ |
| 6 | 10 | 6 | R | $C_56$ |
| 6 | 12 | 0 | b2 | $C_110$ |
| 6 | 12 | 0 | b3 | $C_111$ |
| 6 | 12 | 0 | L | $C_36$ |
| 6 | 12 | 0 | R | $C_112$ |
| 6 | 12 | 1 | b2 | $C_13$ |
| 6 | 12 | 1 | b3 | $C_102$ |
| 6 | 12 | 1 | L | $C_12$ |
| 6 | 12 | 1 | R | $C_69$ |
| 6 | 12 | 2 | b2 | $C_27$ |
| 6 | 12 | 2 | b3 | $C_12$ |
| 6 | 12 | 2 | L | $C_12$ |
| 6 | 12 | 2 | R | $C_113$ |
| 6 | 12 | 3 | b2 | $C_102$ |
| 6 | 12 | 3 | b3 | $C_114$ |
| 6 | 12 | 3 | L | $C_29$ |
| 6 | 12 | 3 | R | $C_115$ |
| 6 | 12 | 4 | b2 | $C_116$ |
| 6 | 12 | 4 | b3 | $C_12$ |
| 6 | 12 | 4 | L | $C_39$ |
| 6 | 12 | 4 | R | $C_117$ |
| 6 | 12 | 5 | b2 | $C_118$ |
| 6 | 12 | 5 | b3 | $C_12$ |
| 6 | 12 | 5 | L | $C_13$ |
| 6 | 12 | 5 | R | $C_80$ |
| 6 | 12 | 6 | b2 | $C_119$ |
| 6 | 12 | 6 | b3 | $C_120$ |
| 6 | 12 | 6 | L | $C_40$ |
| 6 | 12 | 6 | R | $C_121$ |
| 6 | 15 | 0 | b0 | $C_122$ |
| 6 | 15 | 0 | b1 | $C_123$ |
| 6 | 15 | 0 | b2 | $C_124$ |
| 6 | 15 | 0 | b3 | $C_125$ |
| 6 | 15 | 0 | L | $C_126$ |
| 6 | 15 | 0 | R | $C_127$ |
| 6 | 15 | 1 | b0 | $C_128$ |
| 6 | 15 | 1 | b1 | $C_129$ |
| 6 | 15 | 1 | b2 | $C_130$ |
| 6 | 15 | 1 | b3 | $C_131$ |
| 6 | 15 | 1 | L | $C_68$ |
| 6 | 15 | 1 | R | $C_70$ |
| 6 | 15 | 2 | b0 | $C_132$ |
| 6 | 15 | 2 | b1 | $C_133$ |
| 6 | 15 | 2 | b2 | $C_134$ |
| 6 | 15 | 2 | b3 | $C_135$ |
| 6 | 15 | 2 | L | $C_68$ |
| 6 | 15 | 2 | R | $C_73$ |
| 6 | 15 | 3 | b0 | $C_136$ |
| 6 | 15 | 3 | b1 | $C_137$ |
| 6 | 15 | 3 | b2 | $C_138$ |
| 6 | 15 | 3 | b3 | $C_139$ |
| 6 | 15 | 3 | L | $C_75$ |
| 6 | 15 | 3 | R | $C_140$ |
| 6 | 15 | 4 | b0 | $C_141$ |
| 6 | 15 | 4 | b1 | $C_142$ |
| 6 | 15 | 4 | b2 | $C_143$ |
| 6 | 15 | 4 | b3 | $C_144$ |
| 6 | 15 | 4 | L | $C_79$ |
| 6 | 15 | 4 | R | $C_77$ |
| 6 | 15 | 5 | b0 | $C_145$ |
| 6 | 15 | 5 | b1 | $C_146$ |
| 6 | 15 | 5 | b2 | $C_147$ |
| 6 | 15 | 5 | b3 | $C_148$ |
| 6 | 15 | 5 | L | $C_83$ |
| 6 | 15 | 5 | R | $C_81$ |
| 6 | 15 | 6 | b0 | $C_149$ |
| 6 | 15 | 6 | b1 | $C_150$ |
| 6 | 15 | 6 | b2 | $C_151$ |
| 6 | 15 | 6 | b3 | $C_152$ |
| 6 | 15 | 6 | L | $C_153$ |
| 6 | 15 | 6 | R | $C_154$ |
| 7 | 0 | 0 | L | $C_107$ |
| 7 | 0 | 0 | R | $C_105$ |
| 7 | 0 | 1 | L | $C_13$ |
| 7 | 0 | 1 | R | $C_94$ |
| 7 | 0 | 2 | L | $C_13$ |
| 7 | 0 | 2 | R | $C_94$ |
| 7 | 0 | 3 | L | $C_27$ |
| 7 | 0 | 3 | R | $C_13$ |
| 7 | 0 | 4 | L | $C_108$ |
| 7 | 0 | 4 | R | $C_27$ |
| 7 | 0 | 5 | L | $C_102$ |
| 7 | 0 | 5 | R | $C_27$ |
| 7 | 0 | 6 | L | $C_109$ |
| 7 | 0 | 6 | R | $C_106$ |
| 7 | 3 | 0 | b0 | $C_24$ |
| 7 | 3 | 0 | b1 | $C_63$ |
| 7 | 3 | 0 | L | $C_155$ |
| 7 | 3 | 0 | R | $C_101$ |
| 7 | 3 | 1 | b0 | $C_94$ |
| 7 | 3 | 1 | b1 | $C_156$ |
| 7 | 3 | 1 | L | $C_157$ |
| 7 | 3 | 1 | R | $C_14$ |
| 7 | 3 | 2 | b0 | $C_94$ |
| 7 | 3 | 2 | b1 | $C_156$ |
| 7 | 3 | 2 | L | $C_130$ |
| 7 | 3 | 2 | R | $C_14$ |
| 7 | 3 | 3 | b0 | $C_14$ |
| 7 | 3 | 3 | b1 | $C_11$ |
| 7 | 3 | 3 | L | $C_134$ |
| 7 | 3 | 3 | R | $C_14$ |
| 7 | 3 | 4 | b0 | $C_31$ |
| 7 | 3 | 4 | b1 | $C_158$ |
| 7 | 3 | 4 | L | $C_159$ |
| 7 | 3 | 4 | R | $C_95$ |
| 7 | 3 | 5 | b0 | $C_94$ |
| 7 | 3 | 5 | b1 | $C_160$ |
| 7 | 3 | 5 | L | $C_147$ |
| 7 | 3 | 5 | R | $C_94$ |
| 7 | 3 | 6 | b0 | $C_161$ |
| 7 | 3 | 6 | b1 | $C_162$ |
| 7 | 3 | 6 | L | $C_163$ |
| 7 | 3 | 6 | R | $C_104$ |
| 7 | 5 | 0 | b0 | $C_48$ |
| 7 | 5 | 0 | b2 | $C_8$ |
| 7 | 5 | 0 | L | $C_123$ |
| 7 | 5 | 0 | R | $C_125$ |
| 7 | 5 | 1 | b0 | $C_160$ |
| 7 | 5 | 1 | b2 | $C_156$ |
| 7 | 5 | 1 | L | $C_129$ |
| 7 | 5 | 1 | R | $C_131$ |
| 7 | 5 | 2 | b0 | $C_160$ |
| 7 | 5 | 2 | b2 | $C_11$ |
| 7 | 5 | 2 | L | $C_133$ |
| 7 | 5 | 2 | R | $C_135$ |
| 7 | 5 | 3 | b0 | $C_11$ |
| 7 | 5 | 3 | b2 | $C_164$ |
| 7 | 5 | 3 | L | $C_137$ |
| 7 | 5 | 3 | R | $C_139$ |
| 7 | 5 | 4 | b0 | $C_165$ |
| 7 | 5 | 4 | b2 | $C_158$ |
| 7 | 5 | 4 | L | $C_142$ |
| 7 | 5 | 4 | R | $C_144$ |
| 7 | 5 | 5 | b0 | $C_166$ |
| 7 | 5 | 5 | b2 | $C_160$ |
| 7 | 5 | 5 | L | $C_146$ |
| 7 | 5 | 5 | R | $C_148$ |
| 7 | 5 | 6 | b0 | $C_167$ |
| 7 | 5 | 6 | b2 | $C_168$ |
| 7 | 5 | 6 | L | $C_150$ |
| 7 | 5 | 6 | R | $C_152$ |
| 7 | 6 | 0 | b1 | $C_48$ |
| 7 | 6 | 0 | b2 | $C_37$ |
| 7 | 6 | 0 | L | $C_122$ |
| 7 | 6 | 0 | R | $C_111$ |
| 7 | 6 | 1 | b1 | $C_160$ |
| 7 | 6 | 1 | b2 | $C_94$ |
| 7 | 6 | 1 | L | $C_128$ |
| 7 | 6 | 1 | R | $C_102$ |
| 7 | 6 | 2 | b1 | $C_160$ |
| 7 | 6 | 2 | b2 | $C_14$ |
| 7 | 6 | 2 | L | $C_132$ |
| 7 | 6 | 2 | R | $C_12$ |
| 7 | 6 | 3 | b1 | $C_11$ |
| 7 | 6 | 3 | b2 | $C_38$ |
| 7 | 6 | 3 | L | $C_136$ |
| 7 | 6 | 3 | R | $C_114$ |
| 7 | 6 | 4 | b1 | $C_165$ |
| 7 | 6 | 4 | b2 | $C_169$ |
| 7 | 6 | 4 | L | $C_141$ |
| 7 | 6 | 4 | R | $C_12$ |
| 7 | 6 | 5 | b1 | $C_166$ |
| 7 | 6 | 5 | b2 | $C_96$ |
| 7 | 6 | 5 | L | $C_145$ |
| 7 | 6 | 5 | R | $C_12$ |
| 7 | 6 | 6 | b1 | $C_167$ |
| 7 | 6 | 6 | b2 | $C_170$ |
| 7 | 6 | 6 | L | $C_149$ |
| 7 | 6 | 6 | R | $C_120$ |
| 7 | 9 | 0 | b0 | $C_36$ |
| 7 | 9 | 0 | b3 | $C_8$ |
| 7 | 9 | 0 | L | $C_91$ |
| 7 | 9 | 0 | R | $C_124$ |
| 7 | 9 | 1 | b0 | $C_171$ |
| 7 | 9 | 1 | b3 | $C_156$ |
| 7 | 9 | 1 | L | $C_14$ |
| 7 | 9 | 1 | R | $C_130$ |
| 7 | 9 | 2 | b0 | $C_12$ |
| 7 | 9 | 2 | b3 | $C_11$ |
| 7 | 9 | 2 | L | $C_14$ |
| 7 | 9 | 2 | R | $C_134$ |
| 7 | 9 | 3 | b0 | $C_12$ |
| 7 | 9 | 3 | b3 | $C_164$ |
| 7 | 9 | 3 | L | $C_14$ |
| 7 | 9 | 3 | R | $C_138$ |
| 7 | 9 | 4 | b0 | $C_108$ |
| 7 | 9 | 4 | b3 | $C_158$ |
| 7 | 9 | 4 | L | $C_95$ |
| 7 | 9 | 4 | R | $C_143$ |
| 7 | 9 | 5 | b0 | $C_102$ |
| 7 | 9 | 5 | b3 | $C_160$ |
| 7 | 9 | 5 | L | $C_94$ |
| 7 | 9 | 5 | R | $C_147$ |
| 7 | 9 | 6 | b0 | $C_172$ |
| 7 | 9 | 6 | b3 | $C_168$ |
| 7 | 9 | 6 | L | $C_173$ |
| 7 | 9 | 6 | R | $C_151$ |
| 7 | 10 | 0 | b1 | $C_36$ |
| 7 | 10 | 0 | b3 | $C_37$ |
| 7 | 10 | 0 | L | $C_90$ |
| 7 | 10 | 0 | R | $C_110$ |
| 7 | 10 | 1 | b1 | $C_102$ |
| 7 | 10 | 1 | b3 | $C_94$ |
| 7 | 10 | 1 | L | $C_94$ |
| 7 | 10 | 1 | R | $C_13$ |
| 7 | 10 | 2 | b1 | $C_12$ |
| 7 | 10 | 2 | b3 | $C_14$ |
| 7 | 10 | 2 | L | $C_94$ |
| 7 | 10 | 2 | R | $C_27$ |
| 7 | 10 | 3 | b1 | $C_12$ |
| 7 | 10 | 3 | b3 | $C_38$ |
| 7 | 10 | 3 | L | $C_13$ |
| 7 | 10 | 3 | R | $C_102$ |
| 7 | 10 | 4 | b1 | $C_108$ |
| 7 | 10 | 4 | b3 | $C_95$ |
| 7 | 10 | 4 | L | $C_27$ |
| 7 | 10 | 4 | R | $C_108$ |
| 7 | 10 | 5 | b1 | $C_118$ |
| 7 | 10 | 5 | b3 | $C_94$ |
| 7 | 10 | 5 | L | $C_27$ |
| 7 | 10 | 5 | R | $C_102$ |
| 7 | 10 | 6 | b1 | $C_174$ |
| 7 | 10 | 6 | b3 | $C_175$ |
| 7 | 10 | 6 | L | $C_97$ |
| 7 | 10 | 6 | R | $C_176$ |
| 7 | 12 | 0 | b2 | $C_54$ |
| 7 | 12 | 0 | b3 | $C_177$ |
| 7 | 12 | 0 | L | $C_100$ |
| 7 | 12 | 0 | R | $C_178$ |
| 7 | 12 | 1 | b2 | $C_102$ |
| 7 | 12 | 1 | b3 | $C_160$ |
| 7 | 12 | 1 | L | $C_102$ |
| 7 | 12 | 1 | R | $C_128$ |
| 7 | 12 | 2 | b2 | $C_12$ |
| 7 | 12 | 2 | b3 | $C_160$ |
| 7 | 12 | 2 | L | $C_102$ |
| 7 | 12 | 2 | R | $C_132$ |
| 7 | 12 | 3 | b2 | $C_12$ |
| 7 | 12 | 3 | b3 | $C_11$ |
| 7 | 12 | 3 | L | $C_12$ |
| 7 | 12 | 3 | R | $C_136$ |
| 7 | 12 | 4 | b2 | $C_108$ |
| 7 | 12 | 4 | b3 | $C_165$ |
| 7 | 12 | 4 | L | $C_12$ |
| 7 | 12 | 4 | R | $C_141$ |
| 7 | 12 | 5 | b2 | $C_102$ |
| 7 | 12 | 5 | b3 | $C_166$ |
| 7 | 12 | 5 | L | $C_12$ |
| 7 | 12 | 5 | R | $C_145$ |
| 7 | 12 | 6 | b2 | $C_179$ |
| 7 | 12 | 6 | b3 | $C_180$ |
| 7 | 12 | 6 | L | $C_103$ |
| 7 | 12 | 6 | R | $C_181$ |
| 7 | 15 | 0 | b0 | $C_182$ |
| 7 | 15 | 0 | b1 | $C_183$ |
| 7 | 15 | 0 | b2 | $C_184$ |
| 7 | 15 | 0 | b3 | $C_185$ |
| 7 | 15 | 0 | L | $C_186$ |
| 7 | 15 | 0 | R | $C_187$ |
| 7 | 15 | 1 | b0 | $C_188$ |
| 7 | 15 | 1 | b1 | $C_189$ |
| 7 | 15 | 1 | b2 | $C_190$ |
| 7 | 15 | 1 | b3 | $C_191$ |
| 7 | 15 | 1 | L | $C_192$ |
| 7 | 15 | 1 | R | $C_129$ |
| 7 | 15 | 2 | b0 | $C_193$ |
| 7 | 15 | 2 | b1 | $C_194$ |
| 7 | 15 | 2 | b2 | $C_195$ |
| 7 | 15 | 2 | b3 | $C_71$ |
| 7 | 15 | 2 | L | $C_196$ |
| 7 | 15 | 2 | R | $C_133$ |
| 7 | 15 | 3 | b0 | $C_73$ |
| 7 | 15 | 3 | b1 | $C_197$ |
| 7 | 15 | 3 | b2 | $C_75$ |
| 7 | 15 | 3 | b3 | $C_198$ |
| 7 | 15 | 3 | L | $C_199$ |
| 7 | 15 | 3 | R | $C_137$ |
| 7 | 15 | 4 | b0 | $C_200$ |
| 7 | 15 | 4 | b1 | $C_76$ |
| 7 | 15 | 4 | b2 | $C_201$ |
| 7 | 15 | 4 | b3 | $C_202$ |
| 7 | 15 | 4 | L | $C_203$ |
| 7 | 15 | 4 | R | $C_142$ |
| 7 | 15 | 5 | b0 | $C_204$ |
| 7 | 15 | 5 | b1 | $C_133$ |
| 7 | 15 | 5 | b2 | $C_205$ |
| 7 | 15 | 5 | b3 | $C_206$ |
| 7 | 15 | 5 | L | $C_148$ |
| 7 | 15 | 5 | R | $C_146$ |
| 7 | 15 | 6 | b0 | $C_207$ |
| 7 | 15 | 6 | b1 | $C_208$ |
| 7 | 15 | 6 | b2 | $C_209$ |
| 7 | 15 | 6 | b3 | $C_210$ |
| 7 | 15 | 6 | L | $C_211$ |
| 7 | 15 | 6 | R | $C_212$ |
