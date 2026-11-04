# Periodic-family insertion degree

## 1. Words and masks

**Definition 1.1 (source masks and insertion degree).** Let $\Sigma$ be an
alphabet, and let $u,v\in\Sigma^*$ be nonempty words. A mask of a word $w$
labels every position by $\mathrm{U}$ or $\mathrm{V}$ so that the subsequence
of letters labeled $\mathrm{U}$ is $u$ and the subsequence labeled
$\mathrm{V}$ is $v$, in their original orders. A run is a maximal nonempty
consecutive block of one label. For a word admitting a mask, let
$d_{u,v}(w)$ be the minimum number of $\mathrm{U}$-runs among its masks.
Thus $u$ is the inserted source and $v$ the base source. Word powers have
their free-monoid meaning, including $T^0=\varepsilon$; $x[i:j]$ is the
zero-based half-open factor. These are the mask conventions of
Ma–Zhang–Hughes, *Block-exchange descent for insertion: commuting projections
and minimum masks*, [arXiv:2610.39941v1, §3](https://arxiv.org/html/2610.39941v1#S3).

**Definition 1.2 (periodic family).** Fix distinct letters $A\ne B$ and
positive integers $h,j,k,\ell$. Put

$$
\begin{aligned}
T&=ABA,& a_s&=T^{s-1}AB,&c_s&=BA\,T^{s-1}\quad(s\ge1),\\
u&=a_h A c_j,&v&=T^{k+\ell},&w&=a_hT^k A T^\ell c_j.
\end{aligned}
$$

This is the family in Ma–Zhang–Hughes, [v1, Theorem 9](https://arxiv.org/html/2610.39941v1).

## 2. Exact degree

**Theorem 2.1 (periodic-family degree criterion, Hughes).** For every choice
in Definition 1.2, the degree is either two or three, and

$$
d_{u,v}(w)=3
\quad\Longleftrightarrow\quad
k>h,\quad k\ge j,\quad \ell>j,\quad \ell\ge h.
$$

If at least one of these four inequalities fails, $d_{u,v}(w)=2$.
The criterion is due to Charles E. Hughes; the following proof is from
the joint Ma–Zhang–Hughes revision of *Block-exchange descent for insertion:
commuting projections and minimum masks*, Theorem 10 (unpublished revision
of the cited v1).

**Proof.** Write $d(w)=d_{u,v}(w)$.
Put $a_s=T^{s-1}AB$ and $c_s=BA\,T^{s-1}$ for $s\ge1$.
Then $u=a_hT^j=T^hc_j$ and $w=a_hT^kA\,T^\ell c_j$.
The mask
$$
 M=\mathrm{U}^{|a_h|}\mathrm{V}^{3k}\mathrm{U}
   \mathrm{V}^{3\ell}\mathrm{U}^{|c_j|}
$$
has inserted projection $a_h A c_j=u$, base projection $T^{k+\ell}=v$,
and three inserted runs, giving $d(w)\le3$.

Let $H=h+j+k+\ell$, and number the $B$'s of $w$ as
$B_0,\ldots,B_{H-1}$. The initial and final $A$-gaps have length one.
All internal gaps have length two except those after
$$
 B_{h-1},\qquad B_{h+k-1},\qquad B_{h+k+\ell-1},
$$
which have lengths $1,3,1$, respectively. Call these the left short
gap, central long gap, and right short gap. The source $u$ has $h+j$
$B$'s, with one internal gap of length one, after its $h$th $B$;
its other internal gaps have length two. The source $v$ has only
length-two internal gaps. Neither source contains $AAA$.

In any valid mask, at least one $B$ adjacent to each short gap must
be labeled $\mathrm{U}$: otherwise those consecutive $\mathrm{V}$-labeled $B$'s
would have at most one intervening $\mathrm{V}$-labeled $A$. A single
$\mathrm{U}$-run cannot meet both pairs of adjacent $B$'s, because it would
then contain the central $AAA$, contrary to its being a factor of
$u$. This rules out degree one. If there are two $\mathrm{U}$-runs, each
contains a $B$; the first meets the left pair and the second meets
the right pair. Their $B$'s are two consecutive index intervals,
of positive sizes $p,q$ with $p+q=h+j$.

Suppose now that all four displayed inequalities hold. We show that
neither $\mathrm{U}$-run can reach the central long gap. There are three
possibilities for the unique short gap of $u$.

If its two bounding $B$'s belong to different $\mathrm{U}$-runs, then
$p=h$ and $q=j$. The last $B$ in the first run has index at most
$h+p-1=2h-1<h+k-1$. The first $B$ in the second has index at least
$h+k+\ell-q=h+k+\ell-j>h+k$.

If both bounding $B$'s belong to the first run, its short gap must
be the left short gap of $w$. Indeed, that run already meets the
left pair and cannot also reach the right pair. Since the short gap
follows the $h$th $B$ of $u$, this run begins at $B_0$. It contains
at least $h+1$ $B$'s, so $q\le j-1$. Its last $B$ has index
$p-1\le h+j-2<h+k-1$. The first $B$ in the second run has index
at least $h+k+\ell-q>h+k$.

If both bounding $B$'s belong to the second run, its short gap must
be the right short gap of $w$. There are exactly $j$ $B$'s of $u$
after that gap, so this run ends at $B_{H-1}$. It has at least $j+1$
$B$'s, hence $p\le h-1$. The first run ends at an index at most
$h+p-1\le2h-2<h+k-1$. The second starts at index
$H-q=k+\ell+p\ge k+\ell+1>h+k$.

In every case the two $B$'s bounding the central long gap, and all
three intervening $A$'s, are labeled $\mathrm{V}$. To reach any of those
$A$'s from either $\mathrm{U}$-run would require crossing one of the bounding
$B$'s, which the index bounds exclude. This gives consecutive $B$'s
in $v$ with three intervening $A$'s, a contradiction. Thus $d(w)=3$.
The cases requiring $q\le j-1$ or $p\le h-1$ are simply impossible
when $j=1$ or $h=1$, respectively; no nonempty interval is assumed
in such a case.

Conversely, suppose at least one displayed inequality fails. We
give a two-run mask by bracketing consecutive factors and labeling
them. If $k<j$, the factorization
$$
 w=[a_hT^kA]_{\mathrm{U}}\,[T^\ell]_{\mathrm{V}}\,
   [c_{j-k}]_{\mathrm{U}}\,[T^k]_{\mathrm{V}}
$$
has projections $a_hT^kA c_{j-k}=a_hT^j=u$ and
$T^{\ell+k}=v$. In zero-based half-open source coordinates, the
$\mathrm{U}$-factors are $u[0:3(h+k)]$ and $u[3(h+k):|u|]$;
the $\mathrm{V}$-factors are $v[0:3\ell]$ and $v[3\ell:|v|]$.
If $\ell<h$, use
$$
 w=[T^\ell]_{\mathrm{V}}\,[a_{h-\ell}]_{\mathrm{U}}\,
   [T^k]_{\mathrm{V}}\,[A T^\ell c_j]_{\mathrm{U}}.
$$
Its inserted projection is
$a_{h-\ell}A T^\ell c_j=T^hc_j=u$, and its base projection is $v$.
Here the two $\mathrm{U}$-factors split $u$ at position $3(h-\ell)-1$,
and the two $\mathrm{V}$-factors split $v$ at position $3\ell$.

It remains to consider $k\ge j$ and $\ell\ge h$. If $k\le h$, use
$$
 w=[a_h]_{\mathrm{V}}\,[T^k]_{\mathrm{U}}\,
   [A T^{\ell-h+k}]_{\mathrm{V}}\,[T^{h-k}c_j]_{\mathrm{U}}.
$$
The exponents are nonnegative. The inserted projection is $T^hc_j$;
the base projection is
$$
 a_hA T^{\ell-h+k}=T^{k+\ell}.
$$
The $\mathrm{U}$-factors split $u$ at position $3k$, and the
$\mathrm{V}$-factors split $v$ at position $3h-1$.
For the remaining case, note that $T$ is a palindrome and reversal
interchanges $a_s$ with $c_s$. Thus reversing all words replaces
$(h,j,k,\ell)$ by $(j,h,\ell,k)$ within the same family.
If $\ell\le j$, the reversed parameters
satisfy the preceding construction's conditions, since $k\ge j$.
Reversing a mask preserves its number of inserted runs. These cases
cover every failure of the four inequalities. Each construction
therefore gives degree at most two; the earlier lower bound makes
the degree exactly two. $\square$

## 追加锚（本行以下为增补区）
