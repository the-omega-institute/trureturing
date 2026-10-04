[Index](../../../marked_head_profile.md) · [Grouped shallow slots](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment)

# Private-fibre cells and the cost of missing shallow suppliers

At one actual private point of a mixed original in a distinct
odd whole cover, each required prime-direction cell needs an
actual mixed supplier. If its suppliers omit the first $s$
possible prime heights, their number is at least
$((p-2)p^s+1)/(p-1)$. The bound retains the original residues
and the complete non-p coordinate.

The [Lettl–Sun library interface](../../../../../../Library/Arith/lettlsun2008cosets.md)
supplies the pointwise directional demand, original shell
disjointness, and the top-height supplier statement TS6.
The refinement here keeps individual sibling cells and uses
their full coverage with the finite pure-power tail. It is an
ordinary deduction, without a claim of Lean verification or
literature originality; scalar shell or suffix demands alone
do not assert the required cellwise coverage.

## One actual private fibre

Let $\mathcal C=\{C_n=a_n\pmod n:n\in D\}$ be one finite
whole cover of $\mathbb Z$, with distinct odd numerical
moduli $n>1$. Assume $D$ is divisor closed excluding $1$,
and put $N=\operatorname{lcm}(D)$. Choose an original
$d\in D$ with at least two distinct prime factors and one
actual private point

$$
x\in C_d,\qquad x\notin C_n\quad(n\ne d).
\tag{PF1}
$$

Only this target needs a private point. A mixed original means
$\omega(n)\ge2$ for its full numerical modulus $n$.
Fix a prime $p\mid d$, and write $e=v_p(d)$ and $H=v_p(N)$.
On $\mathbb Z/N\mathbb Z$, freeze the entire non-p source:

$$
y\equiv x\pmod{N/p^H}.
\tag{PF2}
$$

For $1\le h\le e$ and $b\in\{0,\ldots,p-1\}$ with
$b\ne\lfloor x/p^{h-1}\rfloor\bmod p$, let
$B_{p,h,b}(x)$ be the cell in PF2 whose first $h-1$
base-p digits agree with $x$ and whose next digit is $b$.
It has $p^{H-h}$ points, all outside $C_d$.

Write a supplier modulus as $n=p^k u$, $(u,p)=1$.
If $C_n$ meets this cell, then $u\mid a_n-x$ and $k\ge h$:
at smaller height it would also contain $x$, contradicting
PF1. Its first differing p-digit is exactly the one defining
the cell, and its relative density there is

$$
\frac{|C_n\cap B_{p,h,b}(x)|}{|B_{p,h,b}(x)|}
=p^{h-k}.
\tag{PF3}
$$

Thus a supplier of height $h$ fills the cell on this fibre;
one of greater height fills a proper subcell. No residue or
source family is changed.

## Pure ancestors and the integer bound

Divisor closure supplies the actual pure originals $p^h$.
Define

$$
\varepsilon_{p,h}(x)
=\mathbf1_{\{a_{p^h}\equiv x\pmod{p^{h-1}}\}},
\qquad g_p(x)=\sum_{h=1}^e\varepsilon_{p,h}(x).
\tag{PF4}
$$

When $\varepsilon_{p,h}=1$, privacy forces the next digit
of $a_{p^h}$ to differ from that of $x$, so this pure original
fills exactly one depth-h sibling cell. When it is zero,
the pure original meets none of them. Call the other
$p-1-\varepsilon_{p,h}$ cells required.

No shallower pure original meets a required cell. Distinctness
allows at most one pure original of each greater height, so
their total relative density in that cell is at most

$$
\sum_{r=1}^{H-h}p^{-r}<\frac1{p-1}<1.
\tag{PF5}
$$

Whole coverage therefore supplies a mixed original in each
required cell. One mixed original can meet only one of these
cells over all $h,b$: its first differing p-digit is fixed.
If $M_p(x)$ counts mixed originals meeting the union of all
$B_{p,h,b}(x)$ with $1\le h\le e$, then

$$
\begin{aligned}
\#\{\text{mixed originals meeting depth-h sibling cells}\}
&\ge p-1-\varepsilon_{p,h}(x),\\
M_p(x)&\ge e(p-1)-g_p(x).
\end{aligned}
\tag{PF6}
$$

More precisely, fix one required cell and suppose every mixed
supplier meeting it has p-height at least $h+s$, where
$s\ge1$. If there are $J$ such originals, PF3, PF5 and
whole coverage give

$$
1<\frac1{p-1}+Jp^{-s},\qquad
J>\frac{(p-2)p^s}{p-1}.
$$

Since $p^s\equiv1\pmod{p-1}$, strict integer rounding yields

$$
\boxed{
J\ge\frac{(p-2)p^s+1}{p-1}
=p^s-\sum_{j=0}^{s-1}p^j.
}
\tag{PF7}
$$

In particular, a required cell either has a mixed supplier
of height $h$, or has at least $p-1$ mixed suppliers of
greater height. The strictness comes from the finite pure
tail and remains valid for every finite $H$. A missing-height
configuration requiring suppliers above $H$ is impossible
under whole coverage.

If $M_p(x)=e(p-1)-g_p(x)$ in PF6, each required cell has
exactly one mixed supplier, of height exactly $h$: a single deeper one
and the pure tail have total density less than
$1/p+1/(p-1)<1$. No mixed supplier can then meet a sibling
cell already filled by the pure height-h original.

At this same $x$, the supplier families for distinct primes
are disjoint. A p-direction supplier agrees with $x$ at the
full non-p part of its modulus and disagrees at p; it cannot
also have its only disagreement at another prime. This is
the existing original-shell disjointness, so directional
counts may be added at one actual private point.

## A C1 target at q = 113

Use the actual EB1 family and a potentially active C1 cofactor
from [Report 388, Section 74](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment).
Here $q=113$, $m>1$, $(m,3q)=1$, and $d=9qm$ is actual.
The originals $qm,3qm,9qm$ share a q-digit $c$, and the
middle ternary root agrees with the final modulo-nine word.
SC483 in that report gives pairwise distinct actual phases
of $m,qm,3qm,9qm$ modulo $m$. Choose a private point $x$
of $9qm$, and write $z=x\bmod9$.

In the q-direction, $e=1$ and $\varepsilon_{q,1}=1$.
The pure q original fills one sibling cell, leaving
$q-2=111$ required cells. Let $N_q(x)$ count mixed originals
meeting those required cells. If $t$ of those cells have no mixed
supplier of q-height $1$, the cell families are disjoint,
and PF7 with $s=1$ gives

$$
\boxed{N_q(x)\ge(111-t)+112t=111(t+1).}
\tag{PF8}
$$

One missing shallow supplier thus forces at least $222$
originals in this direction. If a single required cell has
no mixed supplier of q-height $1$ or $2$, PF7 gives at least

$$
\frac{111\cdot113^2+1}{112}=12655
\tag{PF9}
$$

mixed originals in that cell. Both conclusions allow
arbitrary finite global q-height.

In the ternary direction, $e=2$ and
$g_3(x)=1+\mathbf1_{\{z\equiv a_9\pmod3\}}$. Therefore

$$
M_3(x)\ge
\begin{cases}
2,&z\equiv a_9\pmod3,\\
3,&z\not\equiv a_9\pmod3.
\end{cases}
\tag{PF10}
$$

EB1 irredundancy makes the actual pure 3 and pure 9 classes
disjoint. Consequently their five safe words modulo 9 split
into two in the pure-9 root and three in the other safe root.
This normalization uses the EB1 premise beyond PF1; the
single-target hypotheses alone do not impose it. When
$H_3=2$, the two depth-two sibling cells must have suppliers
of exact ternary height $2$. In the other safe root neither
supplier is pure 9, so they have distinct numerical moduli
$9u$ with $u>1$.

SC483 excludes $m,qm,3qm$ from both directional supplier
families: each differs from $x$ modulo $m$, whose primes
are different from $3,q$. The target itself misses all
these cells. Adding the disjoint q and ternary counts gives

$$
\boxed{
\#\{\text{other mixed originals in these two directions}\}
\ge113+\mathbf1_{\{z\not\equiv a_9\pmod3\}}.
}
\tag{PF11}
$$

The bound $114$ is conditional on the actual target word
lying in the three-word part. It does not assert the
existence of targets realizing every safe word. These
mixed originals have at least two primes in their full
moduli; this is not a count of cofactors with at least
three primes.

## Supplier reuse across targets

Different private points can use the same original supplier.
For example, let the actual $3q$ original have ternary root
$\eta$ and q-digit $\beta$. For every C1 target with root
$\eta$, privacy forces its digit $c\ne\beta$. The same
$3q$ original is then a mixed q-direction supplier on each
target's full non-q fibre.

Thus PF8 and PF11 cannot be multiplied by the number of C1
targets. Aggregation still needs a bound on supplier reuse
through the same-cover column capacities or further actual
incidence information. A replacement argument must also pay
for the suppliers' displaced service on the complete source
and for the numerical output labels. The cellwise bounds do
not provide that exchange or a contradiction to whole coverage.
