# Coupled low-row digit bijection for admissible two-layer boards

## 1. Boards, eligible pairs, and the integer weight

**定义 1.1（Permutation words and order maps）。** For an integer $m\geq0$, let
$[m]=\{1,\ldots,m\}$, with $[0]=\varnothing$, and let $\mathfrak S_m$ be the
set of words containing every element of $[m]$ exactly once. In particular,
$\mathfrak S_0$ contains the empty word. For a word $x$ with distinct entries,
put

$$
\operatorname{inv}(x)=\#\{(u,v):1\leq u<v\leq |x|,\ x_u>x_v\}.
$$

The subword on a specified set of labels retains their original order. Write
$\mathbf1_{\mathcal A}$ for the indicator of a condition $\mathcal A$. If
$a\in[m+1]$, define the increasing bijections

$$
\begin{aligned}
\delta_a:[m+1]\setminus\{a\}&\longrightarrow[m],
&\delta_a(r)&=r-\mathbf1_{r>a},\\
\ell_a:[m]&\longrightarrow[m+1]\setminus\{a\},
&\ell_a(r)&=r+\mathbf1_{r\geq a}.
\end{aligned}
$$

Standardizing after deletion of the label $a$ means applying $\delta_a$ to
every surviving entry. The maps $\delta_a$ and $\ell_a$ are inverse on their
displayed domains; this follows separately for labels below and above $a$.

**定义 1.2（Admissible board）。** An admissible board of size $k\geq0$ is a
pair $P=(\lambda,\mu)$ of nonincreasing lists of nonnegative integers of
length $k$, satisfying, for every $i\in[k]$,

$$
\mu_i\leq\lambda_i,\qquad
\lambda_i\leq k+1-i,\qquad
\mu_i\leq k-i.
$$

Put $n=k+1$ and define the front and back thresholds

$$
f_i=n-\lambda_i,\qquad g_i=n-\mu_i\qquad(i\in[k]).
$$

The corresponding allowed cells are $(r,i)$ with $r\leq f_i$ in the front
layer and $r\leq g_i$ in the back layer. Thus the forbidden cells are those
with $f_i<r\leq n$ and $g_i<r\leq n$, respectively. Both threshold lists are
nondecreasing, and $f_i\leq g_i$. At size zero both lists are empty.

**定义 1.3（Actual eligible pairs and distinguished endpoint）。** For
$\sigma\in\mathfrak S_n$ and $\pi\in\mathfrak S_k$, define two row words
$w,v\in\mathfrak S_n$ by

$$
\begin{aligned}
w_i&=\sigma_{\pi_i},&v_i&=\sigma_{\pi_i+1}&& (1\leq i\leq k),\\
w_n&=\sigma_n,&v_n&=\sigma_1.
\end{aligned}
$$

The set of eligible pairs is the literal subset

$$
\mathcal E(P)=\{(\sigma,\pi)\in\mathfrak S_n\times\mathfrak S_k:
 w_i\leq f_i\text{ and }v_i\leq g_i\text{ for every }i\in[k]\}.
$$

The index $n$ is an unconstrained distinguished endpoint; it is not a column
of the board. There is no value $\pi_n$. Define

$$
\begin{aligned}
H_f(\sigma,\pi;P)
 &=\#\{(i,j):1\leq i<j\leq k,
       w_i<w_j,\ \pi_i>\pi_j,\ w_j>f_i\},\\
H_b(\sigma,\pi;P)
 &=\#\{(i,j):1\leq i<j\leq n,
       v_i<v_j,\ v_j>g_i,
       [j=n\text{ or }(j\leq k\text{ and }\pi_i>\pi_j)]\},\\
E_P(\sigma,\pi)
 &=\operatorname{inv}(\sigma)+\operatorname{inv}(\pi)-H_f-H_b\in\mathbb Z.
\end{aligned}
$$

The subtraction in $E_P$ is integer subtraction. Nonnegativity is a
consequence of the bijection below, rather than part of this definition.
At $k=0$ the only pair is $((1),())$; both forbidden-cell counts and its
integer weight are zero.

These conventions are those of [Koprowski–Lewis](../../../Library/Combinatorics/koprowski2026enumeration.md),
Definition 4.4 and Propositions 4.24–4.25 of the arXiv version. In their
notation $v=wc$, where
$c=\bar\pi^{-1}(1\ 2\ \cdots\ n)\bar\pi$ and $w=\sigma\bar\pi$.
In particular $wc(n)=\sigma_1$. Their forbidden-entry statistic $h$ is
$H_f+H_b$ on $\mathcal E(P)$. To see the precise correspondence, take a
forbidden front cell $(r,i)$ and write $r=w_j$, uniquely. Eligibility and
monotonicity rule out $j\leq i$, since then $w_j\leq f_j\leq f_i$.
Also $w_i\leq f_i<r=w_j$. The cited front-entry criterion therefore says
exactly that $j\leq k$ and $\pi_i>\pi_j$; the front endpoint contributes no
cell. In the back layer write $r=v_j$. Again $j>i$ and $v_i<v_j$, and the
cited back-entry criterion is exactly $j=n$ or $\pi_i>\pi_j$. Each cell has
one target index $j$, so these are counts of the actual forbidden entries,
without multiplicity or an additional restriction on matrix-product indices.

## 2. The repaired local construction

**定义 2.1（Tail parameters and ordinary deletion）。** Let $k\geq1$ and
let $P$ be admissible. Write

$$
A=n-\lambda_1,\qquad B=k-\mu_1,\qquad L=A-1,
\qquad P'=(\lambda_2,\ldots,\lambda_k;
           \mu_2,\ldots,\mu_k).
$$

The tail $P'$ has size $k-1$. Its thresholds, indexed by $i\in[k-1]$, are

$$
f'_i=f_{i+1}-1=k-\lambda_{i+1},\qquad
g'_i=g_{i+1}-1=k-\mu_{i+1}.
$$

For $(\sigma,\pi)\in\mathcal E(P)$ put $t=\pi_1$ and $a=\sigma_t$.
Delete position $t$ from the row word and delete the first column label,
standardizing in both cases:

$$
s_u=\begin{cases}
\delta_a(\sigma_u),&u<t,\\
\delta_a(\sigma_{u+1}),&u\geq t,
\end{cases}
\qquad
p_i=\delta_t(\pi_{i+1}).
$$

Here $s\in\mathfrak S_k$ and $p\in\mathfrak S_{k-1}$. Ordinary insertion
with data $(s,p,a,t)$ reverses these formulas: lift every row by $\ell_a$,
insert $a$ immediately before row position $t$, and set

$$
\begin{aligned}
\sigma_u&=\begin{cases}
\ell_a(s_u),&u<t,\\
a,&u=t,\\
\ell_a(s_{u-1}),&u>t,
\end{cases}\\
\pi_1&=t,\qquad \pi_{i+1}=\ell_t(p_i)\quad(1\leq i<k).
\end{aligned}
$$

**定理 2.2（Coupled repaired digit bijection and exact weight）。** For every
admissible $P$ of size $k\geq1$, the following construction defines a
bijection

$$
\Phi_P:\mathcal E(P)\longrightarrow
\mathcal E(P')\times\{0,\ldots,A-1\}\times\{0,\ldots,B-1\}.
$$

Starting with $(\sigma,\pi)$, form its ordinary deletion $(s,p)$ as in
Definition 2.1. Let $\theta$ be the subword of $\sigma$ on $[A]$, let $\rho$
be $\theta$ with its maximum label $A$ removed, and put

$$
d=\#\{\text{entries after }A\text{ in }\theta\},\qquad
b=\#\{u<t:s_u\leq B\}.
$$

Replace the entries in the low-row slots $\{u:s_u\leq L\}$, in their
existing order, by the word $\rho$, and leave all other entries unchanged.
Call the resulting row word $s^\dagger$. Then

$$
\Phi_P(\sigma,\pi)=((s^\dagger,p),d,b),\qquad
E_P(\sigma,\pi)=E_{P'}(s^\dagger,p)+d+b.
$$

The inverse $\Psi_P$ is as follows, for every eligible tail
$(s^\dagger,p)$ and every pair of digits in the displayed intervals.
Read $\rho$ from the subword of $s^\dagger$ on $[L]$ and insert the maximum
$A$ at position $A-d$ to obtain $\theta$. Select $t$ to be the position of
the $(b+1)$-st entry of $s^\dagger$ whose label is at most $B$. Put

$$
j=\#\{u<t:s^\dagger_u\leq L\},\qquad a=\theta_{j+1}.
$$

Delete this entry $a$ from $\theta$ and apply $\delta_a$ to obtain a word
$\eta\in\mathfrak S_L$. Replace the low-row slots of $s^\dagger$ by
$\eta$ to obtain $s$, then apply the ordinary insertion formulas of
Definition 2.1 to $(s,p,a,t)$. In particular, the tail pair is one coupled
state: the row word and column permutation are retained together.

**证明。** We establish well-definedness, both inverse identities, and the
integer weight identity for these explicit maps.

First the bounds on the first column imply

$$
1\leq A\leq k+1,\qquad1\leq B\leq k,\qquad
A\leq B+1,\qquad0\leq L\leq B.
$$

For $i\in[k-1]$, the tail remains nonincreasing with
$\mu_{i+1}\leq\lambda_{i+1}$, and
$\lambda_{i+1}\leq k-i$, $\mu_{i+1}\leq k-1-i$, precisely the admissibility
bounds at size $k-1$. Moreover,

$$
f'_i\geq A-1=L,\qquad g'_i\geq B.
$$

For the ordinary deletion, eligibility gives $a\leq A$ and
$c=\sigma_{t+1}\leq g_1=B+1$. The successor $c$ exists because $t\leq k$,
including when $t=k$. Since $c\ne a$, its standardized label satisfies
$\delta_a(c)\leq B$: for $c<a$ it is at most $a-1\leq B$, and for $c>a$
it is $c-1\leq B$. Thus $s_t\leq B$.

Consider a surviving column $i+1$. Its front row is unchanged except for
standardization. For any unchanged row $x\ne a$ with $x\leq f_{i+1}$,
the inequality $a\leq A\leq f_{i+1}$ implies
$\delta_a(x)\leq f_{i+1}-1$: if $x<a$, use
$x\leq a-1\leq f_{i+1}-1$; if $x>a$, subtract one. The same reasoning
applies to an unchanged back row because $a\leq A\leq B+1\leq g_{i+1}$.
There is only one possible changed back row. If $t>1$, the surviving column
with original path position $t-1$ previously had successor $a$ and now has
successor $\delta_a(c)\leq B\leq g'_i$. If $t=1$, the changed successor
belongs to the unconstrained distinguished endpoint instead. Hence
$(s,p)\in\mathcal E(P')$ in all cases. This is the ordinary cycle
contraction used in the hyperrook argument of the cited source, expressed
in row-word coordinates.

Conversely, suppose $(s,p)\in\mathcal E(P')$, $a\in[A]$, and $t\in[k]$
with $s_t\leq B$. Ordinary insertion has first front row $a\leq A$ and
first back row $\ell_a(s_t)\leq B+1$. In any surviving column its front
row is the lift of its previous front row, so is at most $f'_i+1=f_{i+1}$.
An unchanged back row is similarly at most $g'_i+1=g_{i+1}$.
If $t>1$, the one predecessor column now has back row $a\leq B+1$,
which meets every original back threshold. If $t=1$, that predecessor
is the unconstrained endpoint. Therefore insertion is eligible.
Deletion and insertion are inverse operations on both words: the deleted
position and column value are $t$, and $\delta_a\ell_a$ and
$\ell_a\delta_a$ undo the row relabeling; the corresponding identities
with $t$ undo the column relabeling. This proves both ordinary inverse
identities on these domains.

We next identify the low-row symmetry of the actual tail. Fix $p$, the
positions of labels in $[L]$ in $s$, and every label greater than $L$.
Permute the labels $1,\ldots,L$ arbitrarily in their fixed positions.
Eligibility is preserved: every low row is below every front and back
threshold of the tail, while high rows are unchanged. Both $H_f$ and $H_b$
are also preserved. Indeed, a forbidden target row is greater than its
threshold and therefore greater than $L$. A low row cannot be a forbidden
target, and a low source is automatically smaller than any forbidden
target. All high-row comparisons, column comparisons, and the endpoint
condition remain the same. This argument includes the case that the back
endpoint itself is a low row.

Cross inversions between a low and a high row do not depend on which low
label is used; high-high inversions are fixed. Only inversions within the
low subword change. Thus, if $\eta$ is the low subword of $s$, there is an
integer $C$, depending on the fixed slots, high rows, and $p$, such that

$$
E_{P'}(s,p)=C+\operatorname{inv}(\eta).
\tag{2.1}
$$

This proves the required symmetry without treating the two faces as
independent boards. In particular, replacing the low subword by $\rho$
preserves eligibility, and

$$
E_{P'}(s^\dagger,p)-E_{P'}(s,p)
=\operatorname{inv}(\rho)-\operatorname{inv}(\eta).
\tag{2.2}
$$

For the forward map, the low subword $\eta$ is exactly $\theta$ with $a$
deleted and standardized. A surviving original label $x\leq A$ becomes
a label at most $A-1=L$, and an original label $x>A$ becomes $x-1>L$.
Thus there are exactly $L$ low slots. Both $\eta$ and $\rho$ permute
$[L]$, so the replacement gives a permutation $s^\dagger$.
The maximum $A$ has between zero and $A-1$ entries after it, hence
$0\leq d<A$. The row $s_t$ is one of the exactly $B$ rows at most $B$,
so $0\leq b<B$. This proves that $\Phi_P$ takes values in its stated
codomain.

For the inverse map, $s^\dagger\in\mathfrak S_k$ has exactly $B$ entries
at most $B$, so the selected $t$ exists and lies in $[k]$. Also
$0\leq j\leq L=A-1$, so $\theta_{j+1}$ exists and belongs to $[A]$.
Deleting it and standardizing gives a permutation $\eta$ of $[L]$.
The low-row symmetry proves that the restored $(s,p)$ is eligible for
$P'$. Because $L\leq B$, this relabeling preserves the set of positions
with labels at most $B$, as well as the low slots themselves. Consequently
$s_t\leq B$, and ordinary insertion is eligible for $P$. This proves
well-definedness of $\Psi_P$ for every tail and every allowed digit pair.

To prove $\Psi_P\Phi_P=\mathrm{id}$, start with an eligible original
pair. Relabeling to $s^\dagger$ preserves the positions of rows at most
$B$, so its $(b+1)$-st such row has the original position $t$. It also
preserves the number $j$ of low slots before $t$. In the original row word,
the deleted $a$ has exactly $j$ labels from $[A]$ preceding it; hence its
position in $\theta$ is $j+1$. Inserting $A$ into $\rho$ at position
$A-d$ recovers precisely the original $\theta$, since $d$ was the number
of entries after its maximum. The inverse therefore recovers the original
$a$ and the original standardized low subword $\eta$. High rows and $p$
were never changed, so it recovers the entire ordinary tail $(s,p)$.
The ordinary inverse identities then recover $(\sigma,\pi)$.

For $\Phi_P\Psi_P=\mathrm{id}$, start instead with an arbitrary
$((s^\dagger,p),d,b)$ in the codomain. In its reconstruction, the lifted
low rows are the entries of $\theta$ other than $a$, in their original
order. Every lifted high row is greater than $A$, since a raw high row
is at least $A$ and its lift is one larger. The insertion position has
exactly $j$ low slots before it, so the inserted $a=\theta_{j+1}$ makes
the original row word's subword on $[A]$ exactly $\theta$.
Deleting its maximum recovers the supplied $\rho$ and the digit $d$.
Ordinary deletion recovers $(s,p)$, and the rank of its position $t$
among rows at most $B$ is still $b+1$. The repaired replacement of its
low subword by $\rho$ consequently returns the supplied $s^\dagger$,
with the same $p,d,b$. Both compositions are thus identities.

It remains to prove the weight identity. Let
$R=(\sigma_1,\ldots,\sigma_{t-1})$ be the row prefix before the deleted
$a$. On surviving front comparisons both row order and column order are
preserved by standardization. For $x\ne a$ and $a\leq f_i$,

$$
\delta_a(x)>f_i-1\quad\Longleftrightarrow\quad x>f_i.
$$

Indeed, a row below $a$ is at most $f_i-1$, and a row above $a$ is reduced
by one. Thus every surviving contribution to $H_f$ agrees with its tail
counterpart. The deleted column has front row $a\leq A$, and its forbidden
targets are exactly the rows $r>A$ with path positions less than $t$:
the condition $\pi_j<t$ selects precisely those positions. Therefore

$$
H_f(\sigma,\pi;P)-H_f(s,p;P')=\#\{r\in R:r>A\}.
\tag{2.3}
$$

For the back statistic, all unchanged comparisons are likewise preserved,
using $a\leq g_i$ and
$\delta_a(x)>g_i-1\Longleftrightarrow x>g_i$. The one changed back row,
at a predecessor column or at the endpoint, originally equals $a$ and
now equals $\delta_a(c)$. The original values $a,c$ are at most $B+1$,
and every original back threshold is at least $B+1$; the new value is
at most $B$, and every tail back threshold is at least $B$.
It can therefore be a forbidden target neither before nor after deletion.
When it occurs as a source for a forbidden target, the comparison that
the source is smaller is automatically true on both sides. The column
comparison and distinguished endpoint status are preserved. This treats
the changed row in both roles and proves equality of all surviving back
contributions.

For the deleted first column, $v_1=c\leq B+1$. The ordinary target columns
with $\pi_j<t$ select path positions $2,\ldots,t$, and the distinguished
target $j=n$ selects position $1$, since $v_n=\sigma_1$. Position $t$
has row $a\leq B+1$ and cannot contribute. Hence the remaining forbidden
targets are exactly the prefix rows above $B+1$:

$$
H_b(\sigma,\pi;P)-H_b(s,p;P')=\#\{r\in R:r>B+1\}.
\tag{2.4}
$$

When $t=1$, the only possible deleted back target is the endpoint, whose
row is $a$ and contributes zero, agreeing with the empty prefix. When
$t=k$, the successor is the last row $\sigma_n$ and the same formula
holds. In particular, the distinguished target must be included in (2.4).

Deleting $\pi_1=t$ removes $t-1$ inversions. Deleting the row $a$ removes
one inversion for every prefix row greater than $a$ and for every suffix
row smaller than $a$. There are $a-1$ smaller labels in total. Consequently

$$
\begin{aligned}
&\operatorname{inv}(\sigma)+\operatorname{inv}(\pi)
 -\operatorname{inv}(s)-\operatorname{inv}(p)\\
&\quad=\#\{r\in R:r>a\}
       +(a-1-\#\{r\in R:r<a\})+(t-1)\\
&\quad=a-1+2\#\{r\in R:r>a\},
\end{aligned}
$$

because $R$ has $t-1$ entries and contains no $a$. Subtracting (2.3) and
(2.4), and partitioning rows above $a$ into the ranges ending at $A$ and
$B+1$, gives the exact ordinary contraction increment

$$
E_P(\sigma,\pi)-E_{P'}(s,p)
=a-1+2\#\{r\in R:a<r\leq A\}
     +\#\{r\in R:A<r\leq B+1\}.
\tag{2.5}
$$

Finally put

$$
j=\#\{r\in R:r\leq A\},\qquad
m=\#\{r\in R:A<r\leq B+1\},\qquad
N=\#\{r\in R:a<r\leq A\}.
$$

Since $a\leq A\leq B+1$ and $a$ is absent from the prefix,
$\delta_a(r)\leq B$ is equivalent there to $r\leq B+1$. Thus $b=j+m$.
Deleting $a$ from $\theta$ removes $N$ inversions with preceding larger
labels and $a-1-(j-N)$ inversions with following smaller labels. Order
standardization changes none of the surviving comparisons, so

$$
\operatorname{inv}(\theta)-\operatorname{inv}(\eta)
=a-1+2N-j.
\tag{2.6}
$$

The maximum $A$ contributes exactly $d$ inversions in $\theta$, whence
$\operatorname{inv}(\theta)=\operatorname{inv}(\rho)+d$. Combining
(2.5), (2.6), $b=j+m$, and (2.2) yields

$$
\begin{aligned}
E_P(\sigma,\pi)
 &=E_{P'}(s,p)+\operatorname{inv}(\theta)
                    -\operatorname{inv}(\eta)+b\\
 &=E_{P'}(s^\dagger,p)+\operatorname{inv}(\theta)
                    -\operatorname{inv}(\rho)+b\\
 &=E_{P'}(s^\dagger,p)+d+b.
\end{aligned}
$$

All equalities have been taken in $\mathbb Z$. This completes the proof.

## 3. Iterated code and the actual weighted sum

**定理 3.1（Arbitrary-board factorization）。** Let $k\geq0$ and let $P$ be
any admissible board of size $k$. For $i\in[k]$ put

$$
\alpha_i=k+2-i-\lambda_i,\qquad
\beta_i=k+1-i-\mu_i.
$$

Both are positive integers. Repeated application of $\Phi$ defines a
bijection of the actual eligible set with the full digit box

$$
\mathcal E(P)\longrightarrow
\prod_{i=1}^k
\bigl(\{0,\ldots,\alpha_i-1\}\times
      \{0,\ldots,\beta_i-1\}\bigr),
\qquad
(\sigma,\pi)\longmapsto((d_i,b_i))_{i=1}^k,
$$

whose inverse reconstructs the pairs in reverse order from the unique
size-zero pair using the explicit maps $\Psi$. Moreover,

$$
E_P(\sigma,\pi)=\sum_{i=1}^k(d_i+b_i)\geq0.
$$

For an indeterminate $q$ and a positive integer $r$, let
$[r]_q=\sum_{e=0}^{r-1}q^e$. Define, now using the proved nonnegative
integer exponents,

$$
F_P(q)=\sum_{(\sigma,\pi)\in\mathcal E(P)}q^{E_P(\sigma,\pi)}
\in\mathbb Z[q].
$$

Then the factorization is

$$
F_P(q)=\prod_{i=1}^k
[k+2-i-\lambda_i]_q\,[k+1-i-\mu_i]_q.
$$

**证明。** After $i-1$ deletions the board has size $k-i+1$ and consists
of the suffixes beginning at $\lambda_i,\mu_i$. Every suffix is admissible
by the calculation in Theorem 2.2. Its first front digit interval has
length $(k-i+1)+1-\lambda_i=\alpha_i$, and its first back digit interval
has length $(k-i+1)-\mu_i=\beta_i$. The original bounds make each length
at least one. Each local map is a bijection onto every eligible next tail
and every pair of digits, so their composition is a bijection onto the
entire displayed box. More explicitly, starting with arbitrary digits and
$((1),())$, apply $\Psi$ for the last suffix, then the penultimate suffix,
and so on. Each step gives an eligible pair, and the two local composition
identities prove both global composition identities by induction.

Let $E^{(i)}$ be the integer weight after $i$ repaired deletions, with
$E^{(0)}=E_P(\sigma,\pi)$. The local identity is
$E^{(i-1)}=E^{(i)}+d_i+b_i$. After $k$ steps the weight is zero, because
the terminal pair has no inversions and no forbidden targets. Summing the
identities telescopes to the claimed digit sum. Each digit is nonnegative,
so this also proves nonnegativity of the originally integer-defined $E_P$.

Reindex the finite sum defining $F_P$ by this bijection. It gives

$$
\begin{aligned}
F_P(q)
 &=\sum_{\substack{0\leq d_i<\alpha_i\\0\leq b_i<\beta_i\ (i\in[k])}}
       q^{\sum_{i=1}^k(d_i+b_i)}\\
 &=\prod_{i=1}^k
     \left(\sum_{d=0}^{\alpha_i-1}q^d\right)
     \left(\sum_{b=0}^{\beta_i-1}q^b\right).
\end{aligned}
$$

The second equality is finite distributivity in $\mathbb Z[q]$. The sum
is over the original eligible permutation pairs, not a function specified
by a recurrence. In particular, its local recurrence
$F_P(q)=[A]_q[B]_qF_{P'}(q)$ follows from the constructed bijection and
does not supply the definition of $F_P$.

The terminal case $k=0$ has one empty digit tuple and one pair, weight zero,
and empty product $F_P(q)=1$. It asserts only this combinatorial terminal
case. At $k=1$, admissibility forces $\mu_1=0$ and
$\lambda_1\in\{0,1\}$. Here $\pi=(1)$ and $H_f=H_b=0$: the only possible
back target has threshold $g_1=2$ and cannot be forbidden.
For $\lambda_1=0$ the two row words are $(1,2),(2,1)$ with weights $0,1$;
for $\lambda_1=1$ only $(1,2)$ is eligible. The code has $b=0$, $d=E_P$,
and the unique size-zero tail, giving $[2-\lambda_1]_q$.

When $A=1$, $L=0$, both low subwords are empty and $\theta=(1)$.
The forward digit is $d=0$, and the inverse always has $j=0$, $a=1$;
it still selects $t$ by the $B$-digit. Thus a maximal first front column
with a nonmaximal back column does not remove the back choices.
When $B=1$, the back digit is zero and exactly one tail row has label at
most $B$, so its selection is still well-defined. When $B=L$ (equivalently
$\lambda_1=\mu_1$), all selectable rows are low rows and relabeling keeps
their positions fixed. In this case the interval $(A,B+1]$ is empty,
$m=0$ and $b=j$, consistently with the weight proof. The possibilities
$t=1$ and $t=k$ were included in both ordinary maps and the endpoint
calculation (2.4), and no insertion after the final tail position is needed.

For the empty board $\lambda=\mu=(0,\ldots,0)$, all pairs are eligible,
$H_f=H_b=0$, and the factors give
$F_P(q)=[k+1]!_q[k]!_q$, where $[r]!_q=\prod_{a=1}^r[a]_q$ and
$[0]!_q=1$. For the fully maximal board
$\lambda_i=k+1-i$, $\mu_i=k-i$, all digit intervals have length one.
Hence there is exactly one eligible pair with weight zero; it is
$(\sigma,\pi)=((1,\ldots,k+1),(1,\ldots,k))$, which directly meets
$w_i=i$, $v_i=i+1$ and the thresholds $f_i=i$, $g_i=i+1$.
If only the front board is fully maximal, all $d_i=0$ but the independent
digits $b_i$ still range over their displayed intervals.

Finally, the polynomial identity can be specialized at any scalar in any
commutative ring. At $q=1$ it gives
$|\mathcal E(P)|=\prod_i\alpha_i\beta_i$. At $q=0$ every factor is one;
the zero digit tuple corresponds to the unique pair of weight zero.
These statements also hold for empty products. This completes the proof.

## 追加锚（本行以下为增补区）
