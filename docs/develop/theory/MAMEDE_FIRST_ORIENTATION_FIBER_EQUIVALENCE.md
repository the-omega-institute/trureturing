# First-orientation singleton-word fibers

## 1. Adjacent words and the source condition

For a permutation $\sigma$ on $n+1$ positions, let $W_n(\sigma)$ be the set of
lists of adjacent-transposition indices in $\{1,\ldots,n\}$ that represent
$\sigma$, have minimal length among valid representing lists, and have
successive indices differing by one. Products of lists are taken in list order;
permutations act on the rightmost factor first.

For a nonempty consecutive word, its spikes are its first letter, strict
internal local extrema, and last letter (a one-letter word has one spike).
Its segment lengths are the absolute differences of successive spikes; the
empty word has no spikes or segment lengths. Call a word oscillating when
these lengths, or their reversal, are weakly increasing, as in
Mamede--Santos--Soares, Definition 3.1, arXiv:2601.09395v1.

Fix $1\leq m<i\leq j<M\leq n$. Write $D_{u,v}$ for the descending list
$u,u-1,\ldots,v$ and $A_{u,v}$ for the ascending list $u,u+1,\ldots,v$. Put

$$
F=D_{j,m}\,A_{m+1,M}\,D_{M-1,i},\qquad
C=D_{i-1,m}\,A_{m+1,M}\,D_{M-1,i},\qquad
B=D_{j,i}.
$$

The source condition on $\sigma$ consists of the displayed order bounds,
the endpoint equations
$\sigma(M+1)=m$, $\sigma(m)=j+1$, and $\sigma(i)=M+1$ in
one-based positions, fixed points outside $[m,M+1]$,
$\sigma(m)\ne m$, $\sigma(M+1)\ne M+1$, and the existence of a
nonoscillating member of $W_n(\sigma)$.
For a shaped source $a=pFq$, every letter of $p$ lies strictly between $m$
and $j$, and every letter of $q$ lies strictly between $i$ and $M$.
## 2. Deletion equivalence

**Theorem 2.1 (First-orientation deletion equivalence).** Under the source
condition above, let $\gamma$ be the adjacent-transposition product of $C$
and let $\pi=\sigma\gamma^{-1}$. There is an equivalence
$e:W_n(\sigma)\simeq W_n(\pi)$ such that, for every source word $a$ and every
first-orientation shape $a=pFq$ with the stated prefix and suffix bounds,

$$
e(a)=pBq,\qquad |a|=|e(a)|+|C|,\qquad |C|>0.
$$

Proof. Every source singleton has the stated shape under the endpoint and
exterior fixed-point equations. The source product factors as
$\operatorname{prod}(pFq)=\operatorname{prod}(pBq)\gamma$: the deleted part
commutes past each suffix generator, whose index lies in $(i,M)$. The full and
retained blocks have the same first and last letters, so replacement preserves
the two outer adjacency checks; the retained descending block is consecutive.
Its letters are valid. If a shorter valid list $v$ represented $\pi$, then
$vC$ would represent $\sigma$. The shape gives
$|a|=|pBq|+|C|$, and the reducedness of $a$ rules out such a $v$. Thus
$pBq\in W_n(\pi)$, with the displayed exact length drop.

The image determines its decomposition: no prefix letter is $j$, while $B$
starts with $j$, so the first $j$ determines $p$. Canceling this prefix and the
fixed block $B$ determines $q$, even when $q$ contains $j$. The same argument
with $F$ makes the source decomposition independent of the chosen shape.
Therefore deletion is injective. The source condition supplies an actual
singleton source, and the first-orientation lifting theorem inserts $F$ into
each target singleton. This proves surjectivity and the equivalence. Finally,
$A_{m+1,M}$ is nonempty, so $|C|>0$.
## 追加锚（本行以下为增补区）
