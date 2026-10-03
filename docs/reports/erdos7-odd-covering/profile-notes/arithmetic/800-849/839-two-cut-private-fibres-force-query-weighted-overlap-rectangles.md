# Two-cut private fibres force query-weighted overlap rectangles

On an admissible two-prime boundary, every other active original class
depends on at most one of the two residual prime coordinates. This gives
an exact classification of how a selected original class can complete
coverage on that fibre. If the fibre is covered and the selected class
has a private point there, both axis unions must contain their entire
complementary first-digit strips. Their overlap therefore contains
a full rectangle, including its weight under any actual nonnegative
query payoff.

The resulting bound depends on the support of the private fibres, not
only the mass of individual private points. A fixed-three-prime family
with arbitrary heights shows a positive, constant conditional rectangle
mass while the private mass tends to zero. Every original in this
family is irredundant and numerically distinct; integer 1 is uncovered
globally. Thus the example tests the local amplification and does not
provide an odd distinct covering system.

These are ordinary set and CRT proofs. The source-law and partner-bucket
conditions below remain necessary for an Erdős #7 application; no new
Lean verification or unrestricted noncoverage result is claimed.

## 1. The exact residual classification on one actual boundary fibre

Fix a finite original family $A_i=[a_i]_{d_i}$, with distinct odd moduli
$d_i>1$, and select a divisibility-maximal original $C=[a]_d$.
Let $N$ be a common finite CRT period. For each other original define

$$
D_i=\{r:r\text{ prime},\ r\mid d,\ v_r(d_i)<v_r(d)\}.
$$

Suppose $p,q$ are distinct prime divisors of $d$ and $T=\{p,q\}$ meets every
$D_i$. Use the canonical boundary period for this cut from
[report 838](838-weighted-primitive-overlap-on-admissible-prime-boundaries.md):

$$
b=q_T=
p^{v_p(d)-1}q^{v_q(d)-1}
\prod_{r\mid N,\ r\notin\{p,q\}}r^{v_r(N)}.       \tag{TR1}
$$

Here $q_T$ is a boundary modulus; $q$ without a subscript is a prime.
The product in TR1 is over primes $r$.
This period is maximal among periods with this exact set of cut axes;
it is globally maximal admissible when $T$ is inclusion-minimal.
Inclusion-minimality is not required for the classification. On any
literal boundary fibre $x\equiv z\pmod b$,
use the exact affine pullback $x=z+bt$, with the transported original
phases. Its relative Haar carrier factors as

$$
X_p\times X_q,
\qquad X_p=\mathbb Z/p^{\alpha}\mathbb Z,\quad
X_q=\mathbb Z/q^{\beta}\mathbb Z,
$$

where $\alpha=v_p(N)-v_p(d)+1\ge1$ and
$\beta=v_q(N)-v_q(d)+1\ge1$.

Restrict to a fibre where $C$ is active. Its residual modulus is $pq$,
so it is exactly $C_p\times C_q$, where $C_p,C_q$ fix one first
residual digit. Their relative Haar masses are $1/p,1/q$.
Every other active original has residual modulus
$d_i/\gcd(d_i,b)$ not divisible by $pq$. Thus it is a $p$-power
cylinder, a $q$-power cylinder, or the unit event covering the entire
fibre. No original tag is discarded when residual numerical moduli
coincide. Activity and phases use the same original boundary point $z$.

If a unit event is active, the selected target has no private point on
this fibre. Otherwise let

$$
A\subseteq X_p,\qquad B\subseteq X_q
$$

be the actual unions of the $p$-only and $q$-only residual originals,
and set $U=X_p\setminus A$, $V=X_q\setminus B$. The entire represented
union on this fibre is

$$
(A\times X_q)\ \cup\ (X_p\times B)\ \cup\ (C_p\times C_q).
$$

Consequently its uncovered set and the selected target's private set
are exactly

$$
\mathcal H=(U\times V)\setminus(C_p\times C_q),\qquad
\Pi=(U\cap C_p)\times(V\cap C_q).                  \tag{TR2}
$$

For an inactive target fibre the first two unions alone determine
coverage; it cannot contribute to private-target amplification.

## 2. Covered fibres: redundancy or a forced complementary rectangle

When no unit is active, the fibre is covered if and only if one of the
following holds:

1. $U=\varnothing$ or $V=\varnothing$. An axis union covers the entire
   fibre, and the selected target is redundant there.
2. $U,V$ are nonempty and $U\subseteq C_p$, $V\subseteq C_q$.
   The selected target is essential on this fibre, with private set
   $\Pi=U\times V$.

Indeed TR2 says coverage is equivalent to
$U\times V\subseteq C_p\times C_q$. If both factors are nonempty,
fix a point of each factor in turn to obtain the two separate
containments. The converse is immediate.

In the second case,

$$
C_p^c\subseteq A,\qquad C_q^c\subseteq B,
\qquad
\boxed{C_p^c\times C_q^c\subseteq A\times B.}       \tag{TR3}
$$

This is a pointwise relation between the actual unions. It is stronger
than a count of suppliers or a lower bound for two unrelated marginals.
The common private witness prevents either coordinate's uncovered set
from being empty; full coverage then forces both strips.

For a one-prime hitting cut, the same argument has only one residual
axis and every other active residual is a unit. A covered fibre cannot
then have a private target point. Thus a target essential to a whole
cover admits no one-prime hitting cut. This is the existing maximal
prime-height sibling mechanism, not a new essential-class theorem.

## 3. Actual private mass and arbitrary joint query weights

Let $h\ge0$ be any function on the same residual fibre. It may be the
hinge of one complete finite query layout with its actual phases. It
need not be a product, have a small Fourier spectrum, or be measurable
at the coarse boundary. By TR3, under coverage and private-target
nonemptiness,

$$
\boxed{
\int h\mathbf1_{A\times B}\,d\xi
\ \ge\int h\mathbf1_{C_p^c\times C_q^c}\,d\xi
}                                                       \tag{TR4}
$$

for **any one nonnegative measure** $\xi$ on this actual fibre. The
two sides use the same law and payoff. Under relative Haar $\mu_z$,
setting $h=1$ gives

$$
\mu_z(A\times B)\ge\frac{(p-1)(q-1)}{pq}.          \tag{TR5}
$$

The constant in TR5 uses the Haar mass of the complementary rectangle.
For a correlated or killed source one must use its actual mass on the
right side of TR4, which can be zero.

There is a useful exact conditioning corollary. The forced rectangle
lies outside the selected target $C_p\times C_q$. Under Haar conditioned
**only** on avoiding that target,

$$
\boxed{
\mu_z(A\times B\mid(C_p\times C_q)^c)
\ge\frac{(p-1)(q-1)}{pq-1}.
}                                                       \tag{TR5a}
$$

For $p=3,q=5$ this is $4/7$, although the conditioned target mass is
zero. More generally a weighted payoff has the right side
$\mu_z(h\mathbf1_{C_p^c\times C_q^c})/(1-1/(pq))$.
This avoids report 838's vanished target-mass term on this same fibre
by using a forced overlap outside the target. Further deletions or
reweighting require the actual rectangle mass in TR4; the conditional
Haar constant in TR5a cannot be carried over without that calculation.
For example, in the seven-original $3\times5$ fibre below, further
deleting all $p$-axis originals leaves the four points
$C_p\times C_q^c$. The surviving source has zero cross-union overlap,
despite its positive mass. This uses the same original fibre throughout.

Even without coverage, on a fibre with active target and no active
unit original, TR2 supplies an exact weighted private/hole identity:

$$
\int h\mathbf1_{\mathcal H}\,d\xi+
\int h\mathbf1_{\Pi}\,d\xi
=\int h\mathbf1_{U\times V}\,d\xi.                 \tag{TR6}
$$

In particular, under product Haar and for $h=f(x)g(y)$, $f,g\ge0$,

$$
\mu_z(h\mathbf1_{\mathcal H})
=\mu_p(f\mathbf1_U)\mu_q(g\mathbf1_V)
-\mu_p(f\mathbf1_{U\cap C_p})\mu_q(g\mathbf1_{V\cap C_q}). \tag{TR7}
$$

All four factors are computed from the same two actual axis unions.
TR7 is not a license to multiply independently optimized source laws
or replace a nonproduct query payoff by the product of its marginals.

## 4. Original labels, prefix consumers and shared overlap budgets

Let $I_p(z),I_q(z)$ be the actual active original tags in the two axis
groups. If desired, choose one fixed ordering of original labels and
let $O_i^p$ and $O_j^q$ be their disjoint first-owner regions within
the corresponding unions. Their products partition $A\times B$, so

$$
\sum_{i\in I_p(z),\ j\in I_q(z)}
\int h\mathbf1_{O_i^p\times O_j^q}\,d\xi
=\int h\mathbf1_{A\times B}\,d\xi
\ge\int h\mathbf1_{C_p^c\times C_q^c}\,d\xi.       \tag{TR8}
$$

The raw sum of original-pair intersections is at least this owner sum,
but can count the same point repeatedly. TR8 uses the same original
ordering for both directions and every query payoff.

Membership in a residual axis group does **not** identify an original
ending-prime bucket. An original can have large fixed prime factors in
the coarse boundary. To use a declared current-prefix subfamily
$J_p\subseteq I_p(z)$, write $A=A_{J_p}\cup A_{\rm other}$. Then

$$
\int h\mathbf1_{A_{J_p}\times X_q}\,d\xi
\ge\int h\mathbf1_{C_p^c\times X_q}\,d\xi
-\int h\mathbf1_{(A_{\rm other}\cap C_p^c)\times X_q}\,d\xi. \tag{TR9}
$$

For selected groups on both axes, with $B=B_{J_q}\cup B_{\rm other}$
and $R=C_p^c\times C_q^c$,

$$
\int h\mathbf1_{A_{J_p}\times B_{J_q}}\,d\xi
\ge\left[
\int h\mathbf1_R\,d\xi
-\int h\mathbf1_{R\cap(A_{\rm other}\times X_q)}\,d\xi
-\int h\mathbf1_{R\cap(X_p\times B_{\rm other})}\,d\xi
\right]_+.                                             \tag{TR10}
$$

On $R$, failure of one selected axis group must be paid by its actual
unselected group; a union bound proves TR10. Thus TR3 gives a forced
current-prefix load when the entire corresponding axis group belongs
to that prefix, or when the other tags can be bounded. Without that
mapping it gives an overlap statement for specified residual groups,
not a statement about which physical stage has already deleted it.

Let $E$ be the set of coarse fibres that are covered and contain a
private target point. Integrating TR4 against any chosen nonnegative
coarse law preserves it, using the same conditional source on both
sides. For full Haar and $h=1$,

$$
\mu\left(\bigcup_{z\in E}\{z\}\times(A_z\times B_z)\right)
\ge\frac{(p-1)(q-1)}{pq}\,\frac{|E|}{b}.            \tag{TR11}
$$

The notation represents the exact boundary-fibre identification, not
an independent replacement of its original phases. Under a hypothetical
whole cover with essential selected $C$, at least one such fibre exists.
Its full-Haar mass need only be $1/b$, which can tend to zero with the
original heights. A useful physical-chain conclusion needs positive
mass of these fibres under that actual source, and positive query
weight on their complementary rectangles.

Different selected targets can amplify their private regions into
overlapping rectangles, even though their private regions are disjoint.
Consequently TR11 cannot be summed over targets with a fresh copy of
the same overlap capacity. A common owner or multiplicity account is
still required.

## 5. A fixed-three-prime family with arbitrarily small private mass

Fix distinct odd primes $p,q,\ell$ and heights $H,J\ge1$. Put

$$
K=\max\{(p-1)(H-1),(q-1)(J-1)\},\qquad
M=K+\max\{p-1,q-1\}.
$$

The target is $C=[0]_{pq}$. For each axis prime $r\in\{p,q\}$,
with height $H_p=H$, $H_q=J$, and each
$1\le n\le H_r$, $1\le c\le r-1$, define

$$
j(r,n,c)=
\begin{cases}
K+c,&n=1,\\
(r-1)(n-2)+c,&n\ge2.
\end{cases}                                            \tag{TR12}
$$

Take the unique CRT class of modulus $r^n\ell^{j(r,n,c)}$ satisfying

$$
x\equiv c r^{n-1}\pmod{r^n},\qquad
x\equiv0\pmod{\ell^{j(r,n,c)}}.                        \tag{TR13}
$$

There are exactly $1+(p-1)H+(q-1)J$ originals. Every tag exponent lies
between 1 and $M$. At a fixed $(r,n)$, different $c$ have different
tag exponents, and different $n$ have different $r$-exponents. The two
axis supports differ, and the target has support $\{p,q\}$.
Thus all original numerical moduli are distinct odd nonunits; $pq$ is
divisibility-maximal. The missing-layer sets of the two axis families
are respectively $\{q\}$ and $\{p\}$, so their unique minimal
hitting set is $\{p,q\}$.

The full period is $N=p^Hq^J\ell^M$, and TR1 gives $b=\ell^M$.
On the single actual boundary fibre $x\equiv0\pmod{\ell^M}$ all
axis labels are active. The first-nonzero-digit cylinders on each
axis are disjoint and partition all nonzero full-height residues.
Hence

$$
A=X_p\setminus\{0\},\quad B=X_q\setminus\{0\},\quad
\Pi=\{(0,0)\},
$$

and this fibre is fully covered. Its exact conditional masses are

$$
\boxed{\mu_z(\Pi)=p^{-H}q^{-J},\qquad
\mu_z(A\times B)=(1-p^{-H})(1-q^{-J}),\qquad
\mu_z(C_p^c\times C_q^c)=\frac{(p-1)(q-1)}{pq}.}   \tag{TR14}
$$

Every original also has a global private point, not just an essential
residual label. For an axis label with $n=1$, use its prescribed
nonzero first digit, opposite axis value 0, and tag coordinate 0. The
target misses because the first digit is nonzero, while all opposite
axis classes miss 0 and all other same-axis shells are disjoint.
For $n\ge2$, its tag exponent $j$ satisfies $j\le K$. Use its own
shell, opposite axis value 1, and a tag coordinate of valuation exactly
$j$. The only opposite shell containing 1 has $n=1,c=1$ and tag
exponent $K+1>j$, so it is inactive; the target misses the opposite
nonzero root. Same-axis shells remain disjoint. These are actual CRT
witnesses because $j<M$. Finally both axis coordinates0 give a private
point of $C$. The edge $H=J=1$ has $K=0$ and no inside-root shells,
so the same construction and first case apply.

The integer 1 is uncovered globally: every axis original requires
divisibility by $\ell$, and $1\not\equiv0\pmod{pq}$. Therefore
the family is an irredundant noncover with one fully covered selected
fibre. Its role is to test the conditional theorem without assuming an
unknown distinct odd whole cover.

For $p=3,q=5,\ell=7,H=J=1$, the seven literal original classes are

$$
0\bmod15;\quad7\bmod21,\ 98\bmod147;\quad
21\bmod35,\ 147\bmod245,\ 343\bmod1715,\ 9604\bmod12005.
$$

On the actual $0\bmod7^4$ fibre they cover the complete $3\times5$
grid, leave $(0,0)$ private to the target, and have cross-union mass
$8/15$. For arbitrary $H,J$, the same $8/15$ complementary-rectangle
mass persists conditionally, while private mass is $3^{-H}5^{-J}$.
The ratio to $8$ times private mass is $3^{H-1}5^{J-1}$.
The full-Haar contribution still carries the source factor $7^{-M}$;
no height-independent global reserve follows from this example.

## 6. What this adds to the existing interfaces

The [Lettl--Sun bibliography and derived shell accounting](../../../../../../Library/Arith/lettlsun2008cosets.md)
already include weighted prime-mismatch demands, common-owner supplier
rectangles OB3--OB4, and exact private-shell overlap/hole identities
QC3--QC5. Those general results are reused and are not claimed anew.
OB4 integrates a demand of $(p-1)(q-1)$ over actual private points
under its global-top-height premises. Those premises are not silently
applied to the deep family here, whose selected target has smaller
heights. TR14 compares the displayed private-mass quantity with the
new conditional rectangle bound; it does not assert a new OB4
application outside that theorem's scope. TR3 uses the additional
**axis-only residual structure** to
amplify the existence of a private point on one fibre into coverage of
entire complementary strips. The resulting rectangle bound is measured
over the private-fibre support; TR14 separates these two quantities by
an unbounded conditional factor.

[Report 336](../../321-384/336-maximal-label-fourier-overlap-and-uncovered-density.md)
and report 838 bound overlap involving a selected original through its
primitive character. The new rectangle is an overlap of the two
**other** axis unions, outside that selected target. It is therefore
not obtained by renaming the selected-class overlap $X_w$.
[Report 341](../../321-384/341-conditional-future-avoidance-controls-the-current-prefix.md)
supplies conditional avoidance bounds for arbitrary residual futures
when its supersolution exists. Here the exact restricted residual
geometry gives TR3 without a supersolution, under coverage and actual
private-fibre nonemptiness. It does not replace report 341 for arbitrary
mixed residual futures.

The classification and amplification are consequences of the stated
finite set relations, not claims of a new published theorem. For the
unrestricted covering problem the remaining obligations are to locate
useful two-cut fibres with source mass, retain positive query payoff
on their complementary rectangles, and map the residual supplier
groups to the actual prefix or continuation budget without duplicating
shared original capacity. Families needing more than two cut primes
still have mixed residual hyperedges and do not satisfy this
two-axis classification.

## 7. Bounded exact controls

The standalone standard-library
[checker](../../../frontier/moments-survival/two_cut_private_fibre_rectangles.py)
and [result](../../../frontier/moments-survival/two_cut_private_fibre_rectangles.json)
construct the original CRT classes for $(p,q,\ell)=(3,5,7)$ and
$(H,J)=(1,1),(1,2),(2,1),(2,2)$. Literal original membership checks all
40 global private witnesses and the uncovered integer 1. On their
four selected coarse fibres, it checks the pointwise rectangle
inclusion on $15+75+45+225=360$ residual cells. It never enumerates
their full CRT periods, the largest of which is $1,297,080,225$.

| $(H,J)$ | Private mass | Actual cross-union mass | Forced rectangle | Rectangle / $8\mu_z(\Pi)$ |
|---|---:|---:|---:|---:|
| $(1,1)$ | $1/15$ | $8/15$ | $8/15$ | $1$ |
| $(1,2)$ | $1/75$ | $16/25$ | $8/15$ | $5$ |
| $(2,1)$ | $1/45$ | $32/45$ | $8/15$ | $3$ |
| $(2,2)$ | $1/225$ | $64/75$ | $8/15$ | $15$ |

The program also computes the same-law target-complement conditioning;
the rectangle mass is $4/7$ in all four cases. Three premise controls
retain the actual carrier: deleting one first-digit $p$-strip leaves
one hole and four failed rectangle cells; an active unit original
covers a fibre with no private target and no cross-union overlap;
further deleting all $p$-axis originals after the target leaves four
survivors and zero cross-union overlap in the first fixture.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/moments-survival/two_cut_private_fibre_rectangles.py
```

The command emits deterministic JSON; `--output` chooses a result file.
These finite controls verify the stated constructions and detect
misuse of the premises. The arbitrary-height construction and the
all-payoff inequality are proved above, not inferred from this sample.
