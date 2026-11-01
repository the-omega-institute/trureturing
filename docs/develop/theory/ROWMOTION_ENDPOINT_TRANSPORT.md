# Rowmotion endpoint transport

Let $P$ be a finite poset and let $I\subseteq P$ be interval-closed: whenever
$u,v\in I$ and $u\le y\le v$, then $y\in I$.  For $x\in P$, write

$$
T_x(S)=
\begin{cases}
S\mathbin{\triangle}\{x\},&\text{if }S\mathbin{\triangle}\{x\}\text{ is interval-closed},\\
S,&\text{otherwise}.
\end{cases}
$$

If $x_1,\ldots,x_N$ is a complete reverse linear extension of $P$ (each point occurs exactly once and $x_i>x_j$ implies $i<j$), define $I_0=I$ and
$I_k=T_{x_k}(I_{k-1})$.  Put $J=I_N$.  For $S\subseteq P$, let
$\operatorname{Min}(S)$ and $\operatorname{Max}(S)$ denote extremal elements in the induced order, and let

$$
\uparrow I=\{x\in P:\exists a\in I,\ a\le x\},\qquad
\downarrow J=\{x\in P:\exists b\in J,\ x\le b\}.
$$

**命题 1.1（端点传输）。** 若 $m\in\operatorname{Min}(I)$、
$c\in\operatorname{Min}(\uparrow I\setminus I)$、且 $m<c$, 则

$$
c\in\operatorname{Max}(J)
\qquad\text{and}\qquad
m\in\operatorname{Max}(\downarrow J\setminus J).
$$

The statement uses the literal toggle trace above.  In particular, the endpoint conclusion is not a definition of a transition and does not assume a global rowmotion formula.  The proof must account for the processed/unprocessed membership at the exact step at which each point is toggled; the local alternatives are the interval-closed toggle conditions for an absent point and for a present point.

## 追加锚（本行以下为增补区）

## 2. Three-row periods outside a polynomial exceptional set

**定义 2.1 (States and separated coordinates).** Let $n\ge11$,
$P_n=[3]\times[n]$ with its coordinatewise order, and
let $\mathcal C_n=\mathcal{IC}(P_n)$ be the set of all interval-closed
subsets, including the empty set: $S\subseteq P_n$ belongs to $\mathcal C_n$
when $u,v\in S$ and $u\le y\le v$ imply $y\in S$ for every $y\in P_n$.
For each $x\in P_n$, define the literal convexity toggle on $\mathcal C_n$ by

$$
T_x(S)=
\begin{cases}
S\mathbin{\triangle}\{x\},&\text{if }S\mathbin{\triangle}\{x\}\in\mathcal C_n,\\
S,&\text{otherwise}.
\end{cases}
$$

A complete legal reverse extension is a sequence $e=(x_1,\ldots,x_{3n})$
containing every point of $P_n$ exactly once, with $x_i>x_j$ implying
$i<j$. For every such $e$ and every $I\in\mathcal C_n$, set $I_0=I$,
$I_k=T_{x_k}(I_{k-1})$ for $1\le k\le3n$, and define

$$
R_e(I)=I_{3n}=(T_{x_{3n}}\circ\cdots\circ T_{x_1})(I).
$$

Let $\operatorname{per}_{R_e}(I)$ be its least positive return time.
Put $L=n+4$. An integer interval $[v,w]$ is empty when $v>w$.

For a state meeting every row, write its three row intervals as
$[a_i,b_i]$, $1\le i\le3$. Define $\mathcal F_n$ to consist of those states
with

$$
a_1>a_2>a_3,\qquad b_1>b_2>b_3,\qquad
1\le a_i\le b_i\le n,
$$

for which the six **indexed** occurrences

$$
(z_1,z_2,z_3,z_4,z_5,z_6)
=(a_1,a_2,a_3,b_1+2,b_2+2,b_3+2)
$$

satisfy

$$
\min\{|z_r-z_s|,L-|z_r-z_s|\}\ge8
\quad\text{for every }1\le r<s\le6. \tag{2.1}
$$

Thus multiplicities count: equal occurrences violate (2.1). These coordinates
lie at sites $1,\ldots,L$ on a circle, with addition interpreted modulo $L$.
The two sites $n+3,n+4$ will be distinguished. Ordinary distances between any
two of the six unshifted endpoints of a state in $\mathcal F_n$ are at least
six, since shifting an endpoint changes a difference by at most two.

**命题 2.2 (A row formula including equal endpoints).** Suppose

$$
S=\bigcup_{i=1}^3\{i\}\times[A_i,B_i],\qquad
1\le A_i\le B_i\le n,\qquad
A_1\ge A_2\ge A_3,\quad B_1\ge B_2\ge B_3.
$$

All indices in the following index sets range over $\{1,2,3\}$,
and a predecessor comparison is used only for $i>1$. Set

$$
\begin{aligned}
M&=\{i:i=1\text{ or }A_i<A_{i-1}\},\\
K&=\{i:B_i<n,\ i=1\text{ or }B_i<B_{i-1}\},\\
d_r&=\max\bigl(\{B_i+1:i\in K,\ i\ge r\}\cup\{0\}\bigr),\\
c_r&=\min\bigl(\{B_i+1:i\in K,\ i\le r\}\cup\{n+1\}\bigr),\\
Q&=\{i\in M:A_i\le d_i\},\\
h_r&=\max\bigl(\{A_i:i\in Q,\ i\ge r\}\cup\{0\}\bigr).
\end{aligned}
$$

Then $S$ is interval-closed, $R_e$ is independent of $e$, and its image in
row $r$ is exactly

$$
(R_eS)_r=[h_r+1,d_r]\ \cup\
\bigl([d_r+1,c_r-1]\setminus[A_r,B_r]\bigr). \tag{2.2}
$$

In particular, if both endpoint sequences are strictly decreasing and
$B_1<n$, then $(R_eS)_r=[A_r+1,B_r+1]$ for all three rows.

*Proof.* If $(i,p),(j,q)\in S$, $i\le j$, and $p\le q$, then for
$i\le r\le j$ one has $A_r\le A_i\le p$ and $B_r\ge B_j\ge q$.
Thus every point between these two points belongs to $S$.

Incomparable interval-closed toggles commute, by Lemma 1.8 of
Lafrenière--Lewis--McNicholas--Striker--Welch,
*Interval-closed set rowmotion and homomesy on products of two chains*,
[arXiv:2505.04000v1](https://arxiv.org/html/2505.04000v1).
Any two reverse linear extensions are connected by adjacent swaps of
incomparable points: move the first point of the desired extension to the
front of the other extension, crossing only incomparable points, and proceed
inductively on the remaining poset. Hence all $R_e$ agree; write their common
value as $R$. Each toggle is an involution, since a permitted flip is undone
by the next application and a forbidden flip is the identity. Consequently
$R$ is a permutation of the whole finite set $\mathcal C_n$.

For $C=\operatorname{Min}(\uparrow S\setminus S)$, Theorem 1.1 and its proof
in the same paper identify this literal permutation as

$$
R(S)=(\operatorname{Inc}(C)\setminus S)
\cup\bigl(\downarrow C\setminus
\downarrow(\operatorname{Min}(S)\cap\downarrow C)\bigr), \tag{2.3}
$$

where $\operatorname{Inc}(C)$ contains the points incomparable with every
member of $C$. Here

$$
\operatorname{Min}(S)=\{(i,A_i):i\in M\},\qquad
C=\{(i,B_i+1):i\in K\}. \tag{2.4}
$$

Indeed, the upward closure in row $i$ is $[A_i,n]$, so its difference
from $S$ is $[B_i+1,n]$. The first point of this difference is globally
minimal exactly when $B_i<n$ and the preceding row has no hole at that
column, namely when $i=1$ or $B_i<B_{i-1}$. The description of
$\operatorname{Min}(S)$ follows in the same way from the left endpoints.

The rows of $\downarrow C$ are $[1,d_r]$. A minimum $(i,A_i)$ belongs
to this downset exactly when $i\in Q$, and the rows of its generated
downset are $[1,h_r]$. Finally $(r,j)$ is incomparable with every ceiling
point exactly when $d_r<j<c_r$: ceiling points in rows at least $r$
require $j>d_r$, and those in rows at most $r$ require $j<c_r$.
Substitution in (2.3) proves (2.2), including the conventions for empty
index sets. If the endpoints are strict and $B_1<n$, then
$M=K=Q=\{1,2,3\}$, $d_r=c_r=B_r+1$, and $h_r=A_r$.
This gives the final assertion. $\square$

**引理 2.3 (The three boundary steps).** Let $I\in\mathcal F_n$ have
$b_1=n$, and put

$$
u=a_3,\qquad v=a_2,\qquad w=a_1,\qquad x=b_3,\qquad y=b_2.
$$

Its endpoint order is exactly one of the following five orders:

$$
\begin{array}{c|l}
W_1&u<v<w<x<y<n\\
W_2&u<v<x<w<y<n\\
W_3&u<v<x<y<w<n\\
W_4&u<x<v<w<y<n\\
W_5&u<x<v<y<w<n.
\end{array} \tag{2.5}
$$

Write $S_t=R^tI$. The three row intervals of $S_1,S_2,S_3$ are as follows;
each triple lists rows $1,2,3$ in that order.

$$
\begin{array}{c|c|c}
\text{orders}&t&((S_t)_1,(S_t)_2,(S_t)_3)\\ \hline
W_1,W_2,W_4&1&
([w+1,y+1],[v+1,y+1],[u+1,x+1])\\
W_3,W_5&1&
([v+1,w-1],[v+1,y+1],[u+1,x+1])\\ \hline
W_1,W_2&2&
([w+2,y+2],[v+2,x+2],[u+2,x+2])\\
W_4&2&
([w+2,y+2],[u+2,v],[u+2,x+2])\\
W_3,W_5&2&
([v+2,w],[u+2,y+2],[u+2,x+2])\\ \hline
W_1,W_2&3&
([w+3,y+3],[v+3,x+3],[1,u+1])\\
W_4&3&
([w+3,y+3],[u+3,v+1],[1,x+3])\\
W_3,W_5&3&
([v+3,w+1],[u+3,y+3],[1,x+3]).
\end{array} \tag{2.6}
$$

All displayed intervals are nonempty and contained in $[n]$. The states
$S_1,S_2$ each have an equality in their left or right endpoint sequence;
$S_3$ has both sequences strictly decreasing.

*Proof.* The raw endpoints are pairwise separated by at least six. Also
$n-y\ge8$ and $u+2\ge8$, the latter from the circular gap between
$n+2$ and $u$. Thus all comparisons below remain strict after the displayed
changes by at most three. In particular none of the rows becomes empty,
and no right endpoint other than the initial $b_1$ can reach $n$ during
these three steps.

The conditions $u<v<w$, $x<y<n$, and $u<x$, $v<y$, $w<n$ give exactly
(2.5): regard the three starts, in increasing order, as opening parentheses
and the three ends as closing parentheses. The $j$th start precedes the
$j$th end, so no initial segment has more closes than opens. With three
of each, the five possibilities give the five orders displayed.

Apply (2.2) first to $I$. Its ceiling indices are $K=\{2,3\}$, so
$d=(y+1,y+1,x+1)$. If $w<y$, then $Q=\{1,2,3\}$ and
$h=(w,v,u)$. The incomparable part in row 1 lies in $[y+2,n]$,
which is already contained in its old row $[w,n]$, so it contributes
nothing. This gives the first line of (2.6).
If $w>y$, then $Q=\{2,3\}$ and $h=(v,v,u)$; the row-1
incomparable contribution is $[y+2,w-1]$. Together with
$[v+1,y+1]$ it is exactly $[v+1,w-1]$. This gives the second line.

For the first line's state $S_1$, one has $K=\{1,3\}$ and

$$
d=(y+2,x+2,x+2),\qquad c=(y+2,y+2,x+2).
$$

For $W_1,W_2$, $v<x$, and all three minima belong to $Q$. Thus
$h=(w+1,v+1,u+1)$; the incomparable interval in row 2 is contained
in its old row and contributes nothing. For $W_4$, $v>x$, so
$Q=\{1,3\}$, $h=(w+1,u+1,u+1)$, and the row-2 incomparable
contribution is $[x+3,v]$. Its union with $[u+2,x+2]$ is
$[u+2,v]$. These are the first two lines for $t=2$.
For the other state $S_1$, belonging to $W_3,W_5$, all ceiling
indices occur, while $M=Q=\{1,3\}$. Hence

$$
d=c=(w,y+2,x+2),\qquad h=(v+1,u+1,u+1),
$$

which gives the remaining line for $t=2$.

For $W_1,W_2$ at $t=2$, the equal right endpoints give
$K=\{1,2\}$, $Q=\{1,2\}$, and

$$
d=(y+3,x+3,0),\quad c=(y+3,x+3,x+3),\quad
h=(w+2,v+2,0).
$$

In row 3 the incomparable contribution is
$[1,x+2]\setminus[u+2,x+2]=[1,u+1]$.
For $W_4$ at $t=2$, all ceiling indices occur but
$M=Q=\{1,2\}$, giving

$$
d=c=(y+3,v+1,x+3),\qquad h=(w+2,u+2,0).
$$

For $W_3,W_5$ at $t=2$, again $M=Q=\{1,2\}$ and all
ceiling indices occur, giving

$$
d=c=(w+1,y+3,x+3),\qquad h=(v+2,u+2,0).
$$

In these last two cases row 3 refills as $[1,x+3]$, because $h_3=0$.
These computations prove every line for $t=3$ and account for the full
incomparable contribution, the equal-endpoint states, and the refill.
The endpoint inequalities in the statement now follow from the six-unit
raw separation. $\square$

**定义 2.4 (Separated circular matchings and their decoder).** Let
$\mathcal M_L$ consist of noncrossing perfect matchings on six distinct
sites of the circle $\{1,\ldots,L\}$, with all six indexed sites at
circular distance at least eight. Noncrossing means that no two matched
pairs have alternating endpoints in circular order. Let $\rho$ add one
to every site, preserving the matched pairs.

Call such a matching *ordinary* if neither $n+3$ nor $n+4$ is an endpoint.
For an ordinary matching, cut between $L$ and $1$ and call the smaller
endpoint of each pair an opening and the larger a closing. Write the
openings as $s_1<s_2<s_3$ and the closings as $t_1<t_2<t_3$. Define
$D_0$ by

$$
(D_0(M))_{4-j}=[s_j,t_j-2],\qquad j=1,2,3. \tag{2.7}
$$

For a matching with endpoint $n+3$, put $j=1$; for one with endpoint
$n+4$, put $j=2$. There can be only one such endpoint. Rotate back by
$j$, decode the resulting ordinary matching as $I=D_0(\rho^{-j}M)$,
and use the $t=j$ line of (2.6) to define $D(M)$. For an ordinary
matching put $D(M)=D_0(M)$. Thus $D$ is specified entirely by row
intervals.

**定理 2.5 (Literal transition and return reflection).** The ordinary
matchings in $\mathcal M_L$ are in bijection with $\mathcal F_n$ under
$D_0$. The decoder $D$ is well-defined on every matching in $\mathcal M_L$,
takes values in $\mathcal C_n$, and satisfies

$$
D(\rho M)=R_eD(M)\qquad(M\in\mathcal M_L) \tag{2.8}
$$

for every complete legal reverse extension $e$. If $I\in\mathcal F_n$
and $M=D_0^{-1}(I)$, then for every integer $t\ge0$,

$$
R_e^tI=D(\rho^tM),\qquad
R_e^tI=I\ \Longleftrightarrow\ \rho^tM=M. \tag{2.9}
$$

In particular $R_e^{n+4}I=I$, and its exact least period equals the
rotational period of this matching.

*Proof.* For any noncrossing matching cut on a line, the closing endpoint
of a pair must match the most recent unmatched opening. Otherwise an
opening between the proposed pair's endpoints would have to match a
later closing, giving alternating endpoints. Therefore the opening/closing
word determines the matching uniquely, by matching each close to that
most recent opening. Conversely this rule constructs a noncrossing
matching for every parenthesis word whose initial segments have at least
as many openings as closings and whose total numbers agree.

In particular $s_j<t_j$, and the separation gives $t_j-s_j\ge8$.
For an ordinary matching, all sites are at most $n+2$. Each opening
has a later partner, so $s_j\le n-6$; each closing has an earlier
partner, so $t_j\ge9$. Consequently (2.7) gives nonempty intervals
in $[n]$, with strictly decreasing starts and ends in row order. They
are interval-closed by Proposition 2.2. Their shifted coordinates are
exactly the original six sites, hence they belong to $\mathcal F_n$.

Conversely, the starts $a_3<a_2<a_1$ and shifted ends
$b_3+2<b_2+2<b_1+2$ of $I\in\mathcal F_n$ satisfy
$a_{4-j}<b_{4-j}+2$. They form such a parenthesis word; the matching
just constructed is the unique inverse of (2.7). This proves the
bijection. In particular it recovers the matched pairs from the actual
state; the matched pairs need not be its row-endpoint pairs.

If $M$ contains one of $n+3,n+4$, eight-unit separation forbids any
other endpoint among the sites that could cross the cut on rotating back
by $j=1$ or $2$. The matching $\rho^{-j}M$ is therefore ordinary,
with largest site $n+2$. Its decoder has $b_1=n$. Lemma 2.3 applies,
so the nonordinary part of $D$ is well-defined, and all its values are
actual interval-closed states.

It remains to compare the last line of the boundary evolution with
rotation. Start with an ordinary matching whose largest site is $n+2$,
and write its raw endpoints as in Lemma 2.3. The partner of $n+2$
is respectively

$$
\begin{array}{c|ccccc}
\text{order}&W_1&W_2&W_3&W_4&W_5\\ \hline
\text{partner}&u&u&w&v&w.
\end{array} \tag{2.10}
$$

This follows directly from the most-recent-opening rule. Adding two to
the ends does not change these orders because raw endpoints are
separated by six. Under $\rho^3$, $n+2$ becomes $1$. Its partner
changes from an opening to a closing; every other opening or closing
keeps its type. There are no other crossings of the cut, because the
second largest endpoint is at most $n-6$.

For $W_1,W_2$, the new opening sites are $1,v+3,w+3$, and the
new closing sites are $u+3,x+5,y+5$. Formula (2.7) gives the first
$t=3$ line of (2.6). For $W_4$, they are $1,u+3,w+3$ and
$x+5,v+3,y+5$, giving the second line. For $W_3,W_5$, they are
$1,u+3,v+3$ and $x+5,y+5,w+3$, giving the third line. All these
listed sequences are strictly increasing. Rotation preserves
noncrossing, so the uniqueness of the matching from its word also
proves equality of matched pairs, not only equality of site sets.
We have established

$$
D_0(\rho^3M)=R^3D_0(M) \tag{2.11}
$$

at every such boundary configuration.

If an ordinary matching has largest site less than $n+2$, then its
decoder has $b_1<n$. Its rotation is ordinary, all endpoints translate
by one, and Proposition 2.2 proves (2.8). If its largest site is
$n+2$, the next matching has endpoint $n+3$, and the definition of
$D$ and the $t=1$ line give (2.8). A matching with endpoint $n+3$
rotates to one with endpoint $n+4$, and the $t=1,2$ lines give
(2.8). Finally a matching with endpoint $n+4$ rotates to an ordinary
matching, and (2.11), together with the $t=2,3$ lines, gives (2.8).
These exhaust all matchings in $\mathcal M_L$. Induction proves the
first equality in (2.9).

If $R^tI=I$, its value has both endpoint sequences strictly decreasing.
The decoder of a nonordinary matching has an endpoint equality, by
Lemma 2.3, and thus cannot equal $I$. Hence $\rho^tM$ is ordinary.
Injectivity of $D_0$ gives $\rho^tM=M$. The converse follows from
the first equality in (2.9). Since $\rho^L$ is the identity, the least
positive return times are equal and divide $L$. $\square$

**定理 2.6 (Full-state exceptional bound).** For every integer $n\ge11$
and every complete legal reverse extension $e$ of the actual poset
$[3]\times[n]$,

$$
\#\{I\in\mathcal C_n:
\operatorname{per}_{R_e}(I)\ne n+4\}\le353n^5. \tag{2.12}
$$

The two separate return estimates are

$$
\begin{aligned}
\#\{I\in\mathcal C_n:R_e^{n+4}I\ne I\}&\le233n^5,\\
\#\bigcup_{1\le t<n+4}\{I\in\mathcal C_n:R_e^tI=I\}
&\le233n^5+120n^3\le353n^5.
\end{aligned} \tag{2.13}
$$

*Proof.* We first bound the complement of $\mathcal F_n$ in the full
state space. Corollary 3.6 of Elizalde--Lafrenière--Lewis--McNicholas--Striker--Welch,
*Motzkin paths, quarter-plane walks, and interval-closed set enumeration*,
[arXiv:2412.16368v1](https://arxiv.org/html/2412.16368v1), obtained in
Section 3.4 from the generating function in Theorem 3.5, supplies the
full cardinality

$$
T_n=|\mathcal C_n|
=\frac{n^6+9n^5+61n^4+159n^3+370n^2+264n+144}{144}. \tag{2.14}
$$

The good-set count in Section 4.1 of Lafrenière et al.,
arXiv:2505.04000v1, supplies

$$
G_n=5\binom{n-5}{6}
=\frac1{144}\prod_{j=5}^{10}(n-j). \tag{2.15}
$$

Here the good sets have all three rows nonempty and all six indexed raw
endpoints at mutual distance at least two. For any interval-closed state
meeting every row, $a_i\ge a_j$ and $b_i\ge b_j$ when $i<j$:
if $a_i<a_j$, convexity between $(i,a_i)$ and $(j,a_j)$ would force
$(j,a_i)$ into the state; if $b_i<b_j$, convexity between $(i,b_i)$
and $(j,b_j)$ would force $(i,b_j)$ into it. Both conclusions contradict
the relevant endpoint. Distinct endpoints therefore make these inequalities
strict. To see the parameters of the count explicitly, order these six
columns as $q_1<\cdots<q_6$ with
$q_{j+1}\ge q_j+2$. The values $q_j-(j-1)$ are arbitrary six
increasing elements of $[n-5]$. The five possible start/end assignments
are (2.5), giving the factor five. Thus the supplied enumerative count
uses the same original states as $\mathcal C_n$; no periodicity assertion
about all of these good sets is used.

For $n\ge11$, all factors $1-j/n$ are in $[0,1]$. The inequality
$1-\prod(1-r_j)\le\sum r_j$ for $r_j\in[0,1]$, proved by
successive use of $1-(1-r)(1-s)\le r+s$, gives

$$
0\le n^6-\prod_{j=5}^{10}(n-j)\le45n^5.
$$

Since every lower power of $n$ is at most $n^5$, (2.14)--(2.15) give

$$
0\le T_n-G_n\le\frac{1052}{144}n^5<8n^5. \tag{2.16}
$$

Among the good sets, failure of (2.1) means that some pair of indexed
shifted occurrences has circular distance less than eight. Fix one of
the $\binom62=15$ index pairs. Fix all five raw endpoints other than
one member of that pair, temporarily dropping every order and convexity
constraint. There are at most $n^5$ choices. The remaining shifted
endpoint must be congruent modulo $L$ to one of the fifteen values
within seven of the other member. Its raw endpoint lies in $[n]$,
an interval shorter than $L$, so there are at most fifteen choices.
The union bound over all fifteen pairs gives $225n^5$. Every good
state with no such failure belongs to $\mathcal F_n$. Therefore

$$
|\mathcal C_n\setminus\mathcal F_n|\le233n^5. \tag{2.17}
$$

By Theorem 2.5, no state in $\mathcal F_n$ fails the return at $L$.
This proves the first estimate in (2.13).

For the shorter returns, let $I\in\mathcal F_n$ return at an integer
$0<t<L$, and let $M$ be its ordinary matching. Return reflection implies
$\rho^tM=M$, so in particular the six-site set $H$ is invariant under
translation by $t$. The order of this translation is
$k=L/\gcd(t,L)>1$. Every orbit of a site under it has length $k$,
so $k$ divides six. Thus

$$
k\in\{2,3,6\},\qquad k\mid L.
$$

The subgroup generated by $t$ equals the subgroup generated by $L/k$.
An invariant six-site set is therefore a union of $6/k$ complete
residue classes modulo $L/k$, and there are exactly
$\binom{L/k}{6/k}$ choices of this kind. There are at most five
noncrossing matchings on any six-site set, as follows from the five
parenthesis words in (2.5). Ignoring the separation and ordinary-cut
restrictions only increases the bound. Hence the union of **all**
shorter-return classes inside $\mathcal F_n$ has cardinality at most

$$
5\sum_{\substack{k\in\{2,3,6\}\\k\mid L}}
\binom{L/k}{6/k}
\le15L^3\le120n^3. \tag{2.18}
$$

This counts each possible translation subgroup once, regardless of
how many values of $t$ generate it; it covers every $1\le t<L$.
Adding (2.17) proves the second estimate in (2.13).

Finally every state in $\mathcal F_n$ returns at $L$, and every one
whose least period differs from $L$ belongs to the shorter-return union
just counted. The whole exceptional set is contained in the complement
in (2.17) together with that union inside $\mathcal F_n$. Its size is
at most $233n^5+120n^3\le353n^5$, proving (2.12).
The denominator throughout is $T_n$, including the empty state and
all states outside the separated family. $\square$

**推论 2.7 (Density with uniform quantifiers).** For every $\varepsilon>0$
there exists $n_0$ such that for every $n\ge n_0$ and every complete
legal reverse extension $e$ of $[3]\times[n]$,

$$
\frac{\#\{I\in\mathcal C_n:
\operatorname{per}_{R_e}(I)\ne n+4\}}{|\mathcal C_n|}
\le\frac{50832}{n}<\varepsilon. \tag{2.19}
$$

One may take
$n_0=\max\{11,\lceil50832/\varepsilon\rceil+1\}$.
Thus the exceptional fraction is $O(1/n)$, uniformly in $e$.

*Proof.* The positive coefficients of (2.14) give $T_n\ge n^6/144$.
Divide (2.12) by this lower bound and use
$353\cdot144=50832$. The stated $n_0$ gives the strict inequality.
This is the fixed-height-three instance of the density question in
Conjecture 4.1 of Lafrenière et al., arXiv:2505.04000v1. Its proof
uses the return reflection (2.9), not a premise that all good states
have exact period $n+4$. $\square$

**命题 2.8 (Shorter periods among good states).** For $m\ge6$, let
$n=2m$ and

$$
E_m=(\{1\}\times[m,2m])\cup
(\{2\}\times[m-2,2m-2])\cup
(\{3\}\times[m-4,2m-4]).
$$

All six indexed endpoints are at mutual distance at least two, but
for every complete legal reverse extension $e$,

$$
\operatorname{per}_{R_e}(E_m)=m+2=\frac{n+4}{2}. \tag{2.20}
$$

*Proof.* The starts and ends are strictly decreasing, the intervals
are nonempty, and $m-(m-4)=4$ while the nearest endpoints from the
two different triples are separated by $m-4\ge2$. Thus this is a
good state in the sense of the count (2.15).

Apply the full row formula (2.2), which allows equal endpoints.
The successive row intervals are

$$
\begin{array}{c|ccc}
t&\text{row }1&\text{row }2&\text{row }3\\ \hline
0 &[m,2m]&[m-2,2m-2]&[m-4,2m-4]\\
1 &[m+1,2m-1]&[m-1,2m-1]&[m-3,2m-3]\\
2 &[m+2,2m]&[m,2m-2]&[m-2,2m-2]\\
3 &[m+3,2m-1]&[m+1,2m-1]&[1,m-3]\\
4 &[m+4,2m]&[2,m]&[2,m-2]\\
5 &[3,m+3]&[3,m+1]&[1,m-1]\\
6 &[4,m+4]&[2,m+2]&[2,m]\\
7\le t\le m+2 &[t-2,m+t-2]&[t-4,m+t-4]&[t-6,m+t-6].
\end{array} \tag{2.21}
$$

For explicit verification of the boundary and refill steps, the ceiling
and selected-minimum index sets in (2.2) for $t=0,\ldots,6$ are

$$
\begin{array}{c|c|c|c|c}
t&K&Q&d&h\\ \hline
0&\{2,3\}&\{1,2,3\}&(2m-1,2m-1,2m-3)&(m,m-2,m-4)\\
1&\{1,3\}&\{1,2,3\}&(2m,2m-2,2m-2)&(m+1,m-1,m-3)\\
2&\{2\}&\{1,2\}&(2m-1,2m-1,0)&(m+2,m,0)\\
3&\{1,3\}&\{1,3\}&(2m,m-2,m-2)&(m+3,1,1)\\
4&\{2,3\}&\{2\}&(m+1,m+1,m-1)&(2,2,0)\\
5&\{1,2,3\}&\{1,3\}&(m+4,m+2,m)&(3,1,1)\\
6&\{1,2,3\}&\{1,2\}&(m+5,m+3,m+1)&(4,2,0).
\end{array} \tag{2.22}
$$

The incomparable contributions not already removed by the old row
are $[1,m-3]$ in row 3 at $t=2$, $[m-1,m]$ in row 2 at
$t=3$, and $[m+2,m+3]$ in row 1 at $t=4$; all other such
contributions in these steps are empty. Together with the intervals
$[h_r+1,d_r]$, these are exactly the next lines of (2.21).
In particular $h_3=0$ at $t=4,6$ accounts for the displayed
refills in row 3.

At $t=7$ both endpoint sequences are strict. For
$7\le t<m+2$ its largest endpoint $m+t-2$ is less than $2m$,
so Proposition 2.2 translates all endpoints by one. This proves the
last line by induction, and at $t=m+2$ it is the initial state.
Before that return, row 1 starts successively at
$m,m+1,m+2,m+3,m+4$, then $3,4$, then the distinct values
$5,\ldots,m-1$ when this last range is nonempty. None except the
initial value equals $m$. Hence no positive time below $m+2$
returns to $E_m$, proving (2.20). $\square$

The scope of (2.12) is compatible with (2.20) and with the literal
$73$-state orbit in $[3]\times[12]$.
The latter orbit has period $73\nmid16$; its seed has an empty middle
row and is outside $\mathcal F_{12}$. The matching action above
represents only the rotation-invariant family $D(\mathcal M_{n+4})$.
The bound concerns the full set $\mathcal C_n$, without requiring
period divisibility on its complement. No assertion for heights
other than three follows from the three-row transition calculation.

## 追加锚（本行以下为增补区）
