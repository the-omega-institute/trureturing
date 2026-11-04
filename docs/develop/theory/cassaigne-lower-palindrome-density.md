# A binary word with palindrome density above one

## 1. Factors, palindromes, and the target densities

Let $\mathbb N=\{0,1,2,\ldots\}$. If $A$ is a finite nonempty alphabet and
$u:\mathbb N\to A$ is a one-sided infinite word, a factor of length $n$ is a
word
$$
u(i)u(i+1)\cdots u(i+n-1)
$$
for some $i\in\mathbb N$. Write $C_u(n)$ for the number of distinct factors of
length $n$, and write $P_u(n)$ for the number of those factors that are equal
to their reversal (the word $x_1\cdots x_n$ has reversal
$x_n\cdots x_1$). We set $C_u(0)=P_u(0)=1$, counting the empty word. Define

$$
\pi(u)=\liminf_{n\to\infty}\frac{nP_u(n)}{C_u(n)},
\qquad
\bar\pi(u)=\liminf_{n\to\infty}
 n\,\frac{\sum_{k=0}^{n-1}P_u(k)}{\sum_{k=0}^{n-1}C_u(k)},
$$

where both lower limits are taken in the extended nonnegative reals; no
convergence is assumed.

A word is eventually periodic if there are $N_0\ge 0$ and $p\ge 1$ such that
$u(i+p)=u(i)$ for every $i\ge N_0$. The question in Cassaigne (2008,
printed p. 709, Open problem 3) asks whether there exist a finite nonempty
$A$ and a non-eventually-periodic $u$ for which
$\pi(u)>1$ or $\bar\pi(u)>3$.

**Theorem 1.1 (the existential question has an affirmative answer).** There is
an explicitly defined binary one-sided word $u$ that is not eventually periodic
and satisfies
$$
\limsup_{n\to\infty}\frac{C_u(n)}{n^3}\le \frac29,
\qquad
\liminf_{n\to\infty}\frac{P_u(n)}{n^2}\ge \frac14.
$$
Consequently $\pi(u)\ge 9/8>1$, so the first branch of the stated
existential disjunction holds.

**Proof.** The construction is in Section 2. The comparison-language and
actual-factor estimates are Theorems 3.2 and 4.3, the palindrome estimate is
Theorem 5.4, and non-eventual periodicity is Theorem 6.1. The final ratio
calculation is Theorem 7.1. ∎

## 2. The blocks and their order

For positive integers $a,b$, put $q=a+b$ and define the finite binary block
$$
B(a,b)=(0^a1^b)^q.
$$
Thus $|B(a,b)|=q^2$. For each $m\ge1$, list first
$$
(m,m),(m+1,m),\ldots,(m^2,m),
$$
and then
$$
(m,m+1),(m,m+2),\ldots,(m,m^2);
$$
the second list is empty for $m=1$. Concatenate these finite lists, in order
of increasing $m$, to obtain $(a_j,b_j)_{j\ge1}$, and set
$$
 u=B(a_1,b_1)B(a_2,b_2)B(a_3,b_3)\cdots .
$$

**Lemma 2.1 (the pair enumeration).** The sequence $(a_j,b_j)$ contains every
pair in
$$
 I=\{(a,b)\in\mathbb N_{\ge1}^2:\max(a,b)\le\min(a,b)^2\}
$$
exactly once. Its layer is $m=\min(a,b)$, and the diagonal pair $(m,m)$ occurs
only in the first list of that layer. The concatenation defines an infinite
word $u:\mathbb N\to\{0,1\}$.

**Proof.** If $\min(a,b)=m$, then either $a\ge b=m$ and $a\le m^2$, or
$b\ge a=m$ and $b\le m^2$. The first list contains exactly the former pairs,
including $(m,m)$, and the second contains exactly the latter strict pairs.
The two lists are disjoint and different layers have different minima. Every
block is nonempty, and the infinitely many blocks have positive length, so the
cumulative lengths tend to infinity and define $u$ on all of $\mathbb N$. ∎

For $a,b\ge1$, let
$$
 v(a,b)=(0^a1^b)^\mathbb N
$$
be the one-sided periodic word, and let $L$ be the union of the finite-factor
languages of all the $v(a,b)$. Write $L(n)$ for its length-$n$ part and
$(t)_+=\max(t,0)$.

## 3. The comparison language

**Lemma 3.1 (three-run words).** The number of binary words of length $n$ with
at most three runs is $O(n^2)$.

**Proof.** Choose the initial letter and at most two of the $n-1$ inter-letter
positions at which a change occurs. ∎

**Theorem 3.2 (cubic upper bound for $L$).**
$$
\limsup_{n\to\infty}\frac{|L(n)|}{n^3}\le\frac16.
$$

**Proof.** Suppose that $w\in L(n)$ has at least four runs. Its first two
interior runs are complete runs of one periodic word $v(a,b)$, and their
lengths identify $a$ and $b$ uniquely. If $w$ begins with $0$ and its initial
run has length $r$, then $1\le r\le a$ and four runs require
$r+b+a+1\le n$. For fixed $a,b,r$, the entire word is determined. If $w$
begins with $1$, the analogous range is $1\le r\le b$. Hence
$$
|L(n)|\le O(n^2)+
\sum_{a,b\ge1}
\bigl(\min(a,(n-a-b)_+)+\min(b,(n-a-b)_+)\bigr).
\tag{3.1}
$$
The sum is finite. Divide it by $n^3$ and put $a=nx$, $b=ny$. It is a
Riemann sum for
$$
2I,
\qquad
I=\int_{x,y\ge0,\ x+y\le1}\min(x,1-x-y)\,dx\,dy.
$$
The integrand, extended by zero outside the triangle, is continuous on a
compact square. Splitting at $x=1/2$ gives
$$
\begin{aligned}
I
&=\int_0^{1/2}\left(x-\frac32x^2\right)dx
  +\int_{1/2}^1\frac{(1-x)^2}{2}\,dx\\
&=\frac1{12}.
\end{aligned}
$$
Thus the right-hand side of (3.1), divided by $n^3$, has limsup at most
$2I=1/6$. ∎

## 4. Windows at joins and the complete factor classification

Call a join ordinary when the two successive pairs are $(a,b),(a+1,b)$ or
$(a,b),(a,b+1)$ within one of the two lists in a layer. All other joins are
exceptional.

**Lemma 4.1 (an ordinary $a$-join).** Consider a length-$n$ window crossing
the join from $B(a,b)$ to $B(a+1,b)$. There are at most
$(n-2a-b-1)_+$ windows at this join whose words are not in $L(n)$.

**Proof.** In the two-sided periodic comparison, let $s$ be the beginning of
the last old $0$-run and let $e$ be the last position of the first new
$0$-run. Across the interface there is the fixed occurrence
$$
1\,0^a1^b0^{a+1},
\tag{4.1}
$$
of length $2a+b+2$, beginning at $s-1$ and ending at $e$. If a window starts
at or after $s$, its part from $s$ is a suffix of the new $0$-run followed by
new periodic runs, hence it is a factor of $v(a+1,b)$. If it ends before $e$,
its rightmost new $0$-run is truncated to length at most $a$, hence it is a
factor of $v(a,b)$. Therefore an outside-$L$ window contains the occurrence
(4.1). The number of possible starts is at most
$(n-(2a+b+2)+1)_+=(n-2a-b-1)_+$. ∎

**Lemma 4.2 (an ordinary $b$-join).** At a join from $B(a,b)$ to $B(a,b+1)$,
the number of length-$n$ windows outside $L(n)$ is at most
$(n-a-2b-1)_+$.

**Proof.** Use the fixed interface occurrence
$$
0\,1^b0^a1^{b+1},
\tag{4.2}
$$
of length $a+2b+2$. A window omitting its initial position on the left fits
the new periodic word, while a window ending before its final position fits
the old one. Thus every outside-$L$ window contains (4.2), and the same
starting-position count gives the bound. ∎

**Theorem 4.3 (all actual factors).** For every $n$,
$$
C_u(n)\le |L(n)|+R(n)+3n^2,
\tag{4.3}
$$
where
$$
R(n)=\sum_{a\ge b\ge1}(n-2a-b)_+
   +\sum_{b\ge a\ge1}(n-a-2b)_+.
\tag{4.4}
$$
Moreover,
$$
\limsup_{n\to\infty}\frac{C_u(n)}{n^3}\le\frac29.
$$

**Proof.** Partition actual length-$n$ windows into those inside one block,
those crossing exactly one join, and those crossing at least two joins. A window
inside a block belongs to $L(n)$.

For ordinary $a$-joins, the old pair has $a\ge b$; for ordinary $b$-joins,
the old pair has $b>a$. Every such old pair occurs once. Lemma 4.1 and Lemma
4.2 therefore bound the outside-$L$ words from ordinary joins by
$$
R(n),
$$
where the second sum includes the diagonal as well and so only enlarges the
count.

There are at most two exceptional joins assigned to each layer: the join
between its two lists, when present, and its join to the next layer. Every run
on either side of either such join has length at least the layer index $m$. If
$n\le m$, a window crossing only that join has at most two runs and belongs to
$L(n)$: any one- or two-run binary word is a factor of a periodic word whose
corresponding run lengths are at least its run lengths. Thus only layers
$m<n$ can contribute outside-$L$ words at exceptional single joins. Each
physical join is crossed by at most $n$ starting positions, giving at most
$2n^2$ such windows.

Finally, a window crossing at least two joins contains an entire intervening
block $B(a,b)$ of length $(a+b)^2<n$. There are at most $n$ such short blocks,
since then both coordinates are less than $\sqrt n$ and all pairs occur once.
For each fixed short block at most $n$ starting positions give a length-$n$
window containing it. This class contributes at most $n^2$ windows.
These three classes exhaust all actual factors, proving (4.3).

For the ordinary-join term, divide (4.4) by $n^3$. The first sum is a Riemann
sum on $0\le y\le x$ and $2x+y\le1$; the second is its coordinate-swapped
copy. Thus
$$
\lim_{n\to\infty}\frac{R(n)}{n^3}=2J,
\qquad
J=\int_{0}^{1/3}\int_{y}^{(1-y)/2}(1-2x-y)\,dx\,dy.
$$
Direct integration gives
$$
J=\int_0^{1/3}\frac{(1-3y)^2}{4}\,dy=\frac1{36},
$$
so the ordinary joins contribute $1/18$ at leading order. The two residual
classes contribute $O(n^2)$, hence vanish after division by $n^3$. Combining
this with Theorem 3.2 yields
$$
\limsup_{n\to\infty}\frac{C_u(n)}{n^3}
\le \frac16+\frac1{18}=\frac29.
$$ ∎

## 5. Palindromes realized in the same blocks

**Lemma 5.1 (palindromic periodic factors).** The bi-infinite periodic extension
of $v(a,b)$ is invariant under reflection about the midpoint of every $0$-run.
Consequently, if $n\equiv a\pmod 2$ and $a+2b+2\le n$, it has a length-$n$
palindrome centered on a $0$-run. If $n\equiv b\pmod 2$ and
$2a+b+2\le n$, it has a length-$n$ palindrome centered on a $1$-run. Each
such palindrome has at least five runs and determines $(a,b)$ uniquely.

**Proof.** Reflection about the midpoint of a $0$-run preserves the alternating
run pattern on both sides, and the parity condition places the midpoint at the
center of a length-$n$ word. Under $a+2b+2\le n$, the central full $0$-run,
the two adjacent full $1$-runs, and nonempty outside $0$-runs all occur; hence
there are at least five runs. The $1$-centered assertion is symmetric.
Two successive complete interior runs identify their lengths, so the pair is
unique. ∎

**Lemma 5.2 (the two center types are disjoint).** The palindromes in Lemma
5.1 centered on $0$-runs and those centered on $1$-runs are distinct.

**Proof.** For odd $n$ their central letters differ. For even $n$ their central
pairs are respectively $00$ and $11$. ∎

**Lemma 5.3 (realization inside $B(a,b)$).** Let $r=\lceil\sqrt n\rceil$. If
$a,b\ge r$ and either inequality in Lemma 5.1 holds, then $(a,b)\in I$ and
$B(a,b)$ contains the corresponding length-$n$ palindrome.

**Proof.** The inequalities in Lemma 5.1 imply $q=a+b\le n$. Since
$a,b\ge r$, we have $\max(a,b)\le n\le r^2\le\min(a,b)^2$, so $(a,b)\in I$ and
its block occurs in $u$. Also $q\ge2r$, hence $q^2\ge4n$. A segment of $q^2$
letters beginning at a period boundary contains every length-$n$ factor of the
periodic word whenever $q^2\ge n+q-1$; here this follows from $q\le n$ and
$q^2\ge4n$. The palindrome is therefore realized inside this block. ∎

**Theorem 5.4 (uniform palindrome lower bound).**
$$
\liminf_{n\to\infty}\frac{P_u(n)}{n^2}\ge\frac14.
$$

**Proof.** Let
$$
S_0(n)=\{(a,b):a,b\ge1,\ a+2b+2\le n,\ a\equiv n\pmod2\}.
$$
For $n=2t$ and all sufficiently large $t$,
$|S_0(n)|=(t-1)(t-2)/2$; for $n=2t+1$,
$|S_0(n)|=t(t-1)/2$. Thus in both parities
$$
|S_0(n)|=\frac{n^2}{8}+O(n).
$$
Interchanging $a$ and $b$ gives the same count for the $1$-centered family.
All pairs in the two triangles have both coordinates at most $n$. Removing
pairs with $a<r$ or $b<r$ discards at most $2rn$ pairs from each family.
By Lemmas 5.1–5.3 and Lemma 5.2, the retained pairs provide distinct actual
palindromes, and therefore
$$
P_u(n)\ge 2|S_0(n)|-4rn
      =\frac{n^2}{4}-O(n^{3/2}).
$$
This estimate holds for every sufficiently large integer $n$, including both
parities, and proves the asserted liminf. ∎

## 6. Non-eventual periodicity

**Theorem 6.1.** The word $u$ is not eventually periodic.

**Proof.** For every $m$, the block $B(m,m)$ occurs in layer $m$ and contains
$0^m1^m$. The starting positions of these blocks tend to infinity. If $u$ had
period $p\ge1$ after some $N_0$, choose $m\ge p$ with the block starting after
$N_0$. The consecutive run of $m$ zeros contains every residue class modulo
$p$, so periodicity forces every later symbol to be $0$. The following run of
$m$ ones is a contradiction. ∎

## 7. The density inequality

**Theorem 7.1 (lower palindrome density).** For the word $u$ above,
$$
\pi(u)\ge\frac98>1.
$$

**Proof.** Let $0<\varepsilon<1/4$. Theorems 4.3 and 5.4 imply that for all
sufficiently large $n$,
$$
\frac{P_u(n)}{n^2}\ge\frac14-\varepsilon,
\qquad
\frac{C_u(n)}{n^3}\le\frac29+\varepsilon.
$$
Since $C_u(n)>0$,
$$
\frac{nP_u(n)}{C_u(n)}
\ge\frac{1/4-\varepsilon}{2/9+\varepsilon}.
$$
Taking the lower limit and then letting $\varepsilon\downarrow0$ gives
$$
\pi(u)\ge\frac{1/4}{2/9}=\frac98>1.
$$
Theorem 6.1 supplies non-eventual periodicity, and Lemma 2.1 supplies the
finite nonempty alphabet and the one-sided word. Thus the $\pi$ branch alone
settles the existential disjunction. No assertion about $\bar\pi(u)$ is needed.
∎

## 8. Sources and scope

Cassaigne, Julien. “On extremal properties of the Fibonacci word.” *RAIRO –
Theoretical Informatics and Applications* 42 (2008), 701–715,
[DOI 10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003), printed
pp. 708–709. Its definitions of the two lower-limit densities and Open
problem 3 supply the target event used in Section 1.

The comparison-language estimates, the join classification, the realization
of both palindrome center types, and the resulting binary witness are the
argument proved in this volume. The proof addresses the full factor language
of the displayed one-sided word and does not assume recurrence,
reversal-closure, richness, morphicity, or a prescribed factor-complexity
growth law. It proves the $\pi$ branch only; it does not assert sharpness, a
bound for $\bar\pi$, or any neighboring theorem.

## 追加锚（本行以下为增补区）
