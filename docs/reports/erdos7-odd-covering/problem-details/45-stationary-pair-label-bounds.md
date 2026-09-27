# Stationary pair balance and original-label bounds

Sections 9–10 of [Complete event laws and first-hit costs](43-sharp-first-hit-ambiguity-with-identical-complete-event-laws.md); continued in [Rectangular overlap and all-height budgets](46-rectangular-overlap-and-all-height-budgets.md).

## 9. A fixed policy can preserve the current marginal without preserving either full pair

The fixed-leaf obstruction in Section 8 uses a complete Latin grid and
full pair-product marginals. Current-marginal stationarity alone does
not have that rigidity. The following source has 31 distinct original
odd moduli and preserves the current marginal for every fixed
\(0<\delta_7<1\).

### An original-congruence stationary source

Use the carrier \(3^{12}\times5^6\times7\), with pure classes
\(0\pmod3,0\pmod5,0\pmod7\). The incoming old law is the product
of the two uniform pure-survivor laws; the current base is uniform on
\(\{1,\ldots,6\}\). Partition the following 28 distinct
\(3,5\)-monomials into six groups:

| Current color | Monomials |
| --- | --- |
| 1 | \(1,5,375,405,625,2025,3125\) |
| 2 | \(3,15,225,243,6075\) |
| 3 | \(9,25,27,125,1125,1875,3375\) |
| 4 | \(45,81,135,675,5625\) |
| 5 | \(729,2187,3645\) |
| 6 | \(6561\) |

Each group sums to \(6561\). Enumerate the entries in table order by
\(h=0,\ldots,27\). For an entry \(3^i5^j\) in color \(c\), set
\[
 a_h=12-i,\qquad b_h=6-j,\qquad
 \rho_h=1+h+\lfloor h/2\rfloor.
\]
The associated original mixed class is the unique CRT class satisfying
\[
 x\equiv\rho_h\pmod{3^{a_h}},\qquad
 x\equiv1\pmod{5^{b_h}},\qquad x\equiv c\pmod7.
 \tag{FA40}
\]
All \(a_h\ge4\), all \(b_h\ge1\), and the 28 values
\(\rho_h\in\{1,2,4,5,\ldots,40,41\}\) are distinct nonzero
residues modulo \(81\). Consequently the old trigger rectangles are
pairwise disjoint. Unique monomials give unique pairs \((a_h,b_h)\),
hence all 28 mixed numerical moduli are distinct. Together with the
three pure classes these are 31 distinct odd moduli greater than one.

The old mass of a rectangle is
\[
 \frac{3^{1-a_h}}2\frac{5^{1-b_h}}4
 =\frac{15\,3^i5^j}{8\,3^{12}5^6}.
\]
Thus each color has trigger mass \(m=1/675000\), and the union of
all triggers has mass \(6m=1/112500\). Every active old row forbids
exactly one current color. Put
\[
 u=\frac{\min(1/6,\delta_7)}{1-\min(1/6,\delta_7)}.
\]
On a row forbidding \(c\), the actual current density is
\(1+u(1-6\mathbf1_{\{c\}})\); on inactive rows it is one.
Integrating any current color \(c\) therefore gives density
\[
 1+u(6m)-6um=1.
 \quad\text{Hence}\quad \mu_7=\nu_7
 \quad\text{for every }0<\delta_7<1.
 \tag{FA41}
\]
The actual source differs from the product law on its active rows.
On the head-avoiding set, its surplus above the unnormalized product
reference is
\[
 h=\frac56u\frac1{112500}>0.
 \tag{FA42}
\]
This is a stationarity counterexample, not an odd covering: the integer
\(2\) avoids all 31 classes.

### Disjoint original rectangles cannot preserve a full old-current pair

Let \(r<s<p\) be odd primes, \(n=p-1\), and take uniform old
pure-survivor bases at arbitrary finite heights \(E,F\). Consider a
nonempty family of original classes with moduli
\(r^{a_i}s^{b_i}p\), where \(1\le a_i\le E\),
\(1\le b_i\le F\), the pairs \((a_i,b_i)\) are distinct, and
the old rectangles \(C_i\times D_i\) are nonempty and pairwise
disjoint. Assign any current color \(c_i\in\{1,\ldots,n\}\) to
each class, and use one fixed \(0<\delta_p<1\). Then
\[
 \mu_{r,p}\ne\nu_r\otimes\nu_p,
 \qquad
 \mu_{s,p}\ne\nu_s\otimes\nu_p.
 \tag{FA43}
\]
This does not require a Latin grid or a density cap.

To prove the first inequality, set
\(u=\min(1/n,\delta_p)/(1-\min(1/n,\delta_p))>0\) and
\(v_i=\mathbf1-n e_{c_i}\in\mathbb R^n\). Disjointness gives
the current density \(\mathbf1+u v_i\) on rectangle \(i\).
The alleged full pair-product law would therefore imply, at every
complete old \(r\)-word \(x\),
\[
 F(x):=\sum_{i:x\in C_i}\frac{s^{1-b_i}}{s-1}v_i=0.
 \tag{FA44}
\]
Choose the largest occurring \(r\)-depth \(A\), and among labels
at that depth choose the unique largest \(s\)-depth \(B\).
Choose \(x\) in that label's \(r\)-cylinder and \(x'\) in a
different child of the same depth-\((A-1)\) parent. Such an old
survivor child exists: there are \(r\) children when \(A>1\),
and \(r-1\ge2\) at the first pure-survivor level.

All labels of depth less than \(A\) agree at \(x,x'\). Multiply
\(F(x)-F(x')=0\) by \((s-1)s^{B-1}\). Each remaining term of
\(s\)-depth \(b<B\) has integer coefficient divisible by \(s\).
The chosen label is the only term of depth \(B\), and has coefficient
one. In any current coordinate other than its color its vector entry
is one. That coordinate of the alleged equality reduces modulo \(s\)
to \(1=0\), a contradiction. Exchanging \(r,s\) proves the
second inequality. All complete digits are retained throughout.

The same first inequality holds under a weaker assumption than
disjointness: no old word triggers two labels of the same color, and
for each fixed \(x\), the positive values of
\(k(x,y)=\#B(x,y)\) are constant as \(y\) varies. The constant
may depend on \(x\). Indeed the density perturbation on that row is
\[
 \frac{u_k}{k}\sum_{i:(x,y)\in C_i\times D_i}v_i,
 \qquad
 u_k=\frac{\min(k/n,\delta_p)}{1-\min(k/n,\delta_p)}.
 \tag{FA45}
\]
The positive scalar \(u_k/k\) is constant on its active part.
Pair-product would again force (FA44), including rows with no active
point, and the same contradiction applies. The analogous columnwise
condition gives the second inequality. Arbitrary multicolor unions
with varying \(k\), or overlapping triggers of the same color,
are not covered by this argument; simultaneous full pair products
in that unrestricted source class remain unresolved here.

### Exact finite witness

The standard-library producer
[`fixed_stationary_boundary.py`](../frontier/cover-geometry/fixed_stationary_boundary.py)
and its [exact output](../frontier/cover-geometry/fixed_stationary_boundary.json)
give every literal modulus and residue in (FA40). The producer uses
the adjacent `balanced_prefix_budget.py` only for CRT, prefix
partitions and clipping, and rebuilds this source's probability law.
It partitions the complete old coordinates into \(352\times24\)
constant-test cylinders, representing \(4428675000\) old survivor
words. For the default thresholds it verifies:

| \(\delta_7\) | Head surplus \(h\) | \(\operatorname{TV}(\mu_{3,7},\nu_3\otimes\nu_7)\) | \(\operatorname{TV}(\mu_{5,7},\nu_5\otimes\nu_7)\) |
| --- | --- | --- | --- |
| \(1/96\) | \(1/12825000\) | \(1/12825000\) | \(341/6643012500\) |
| \(1/6\) | \(1/675000\) | \(1/675000\) | \(6479/6643012500\) |
| \(1/5\) | \(1/675000\) | \(1/675000\) | \(6479/6643012500\) |

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_stationary_boundary.py --output /tmp/fixed-stationary-boundary.json
```

Repeating `--delta` selects other exact rational thresholds. The
all-threshold assertion is proved by (FA41), not by the three sampled
policies. Section 9 is a repository-derived ordinary mathematical
argument with an exact computational witness, not a Lean-certified
result or a resolution of unrestricted Erdős #7; no literature-priority
assertion is made.

## 10. Full pair stationarity requires at least 3(p−1) original mixed labels

This is a self-contained ordinary mathematical proof, not a Lean certificate.
The result is a necessary label count. It does not construct a family attaining
the bound or settle unrestricted Erdős #7.

### 10.1. Quantified model and exact scope

Let `r < s < p` be odd primes, put `n = p - 1`, and let `E,F >= 1` be
integers. Fix the entire Cartesian pure-survivor carrier

\[
 X=\{x\in\mathbb Z/r^E\mathbb Z:x\not\equiv0\pmod r\},\qquad
 Y=\{y\in\mathbb Z/s^F\mathbb Z:y\not\equiv0\pmod s\}.
 \tag{FA46}
\]

The current colors are the `n` nonzero residues modulo `p`, with uniform
law `nu_p`. Let `rho` be **any probability law strictly positive at every
point of this entire fixed product `X x Y`**. It need not be a product law.
The incoming current color is independent of the old history, so the incoming
law is `rho x nu_p`.

An allowed old rectangle has positive depths in both coordinates:

\[
 R(a,\alpha)\times S(b,\beta),\qquad
 1\le a\le E,\quad 1\le b\le F,
 \tag{FA47}
\]

where `R(a,alpha)` is the nonempty cylinder `x = alpha mod r^a` in `X`,
and `S(b,beta)` is the corresponding nonempty cylinder in `Y`. Its residues
are nonzero modulo their respective primes.

A label consists of one such rectangle and one current color. Take a finite,
nonempty family of labels with **at most one label for each exponent pair
`(a,b)`**, across all residues and all colors. Equivalently, the original
numerical moduli `r^a s^b p` are distinct. Empty triggers are removed before
counting. Arbitrary intersections are permitted, including intersections
between labels of the same color.

For color `c`, let `U_c` be the union of its old rectangles, and put

\[
 B(x,y)=\{c:(x,y)\in U_c\},\qquad k(x,y)=|B(x,y)|.
\]

Allow an **arbitrary history-dependent positive threshold**

\[
 \delta:X\times Y\longrightarrow(0,1).
\]

At an old history with `k>0`, define

\[
 u=\frac{\min(k/n,\delta(x,y))}{1-\min(k/n,\delta(x,y))},
 \qquad w=\frac uk;
\]

set `u=w=0` when `k=0`. The actual clipped law is

\[
 \mu(x,y,c)=\frac{\rho(x,y)}n
 \left(1+u(x,y)-nw(x,y)\mathbf1_{U_c}(x,y)\right).
 \tag{FA48}
\]

Thus its density is `1/(1-min(k/n,delta))` on good colors and

\[
 \frac{k/n-\min(k/n,\delta)}{(k/n)(1-\min(k/n,\delta))}
\]

on bad colors. When `k=0` or `k=n`, the density is one. The density averages
to one over the current color at every old history, so `mu` is a probability
law whose old joint marginal remains exactly `rho`.

Assume both full-coordinate pair marginals are product with the fresh
uniform current law:

\[
 \mu_{X,C}=\rho_X\otimes\nu_p,\qquad
 \mu_{Y,C}=\rho_Y\otimes\nu_p.
 \tag{FA49}
\]

Let `N_c` be the number of effective labels of color `c`, and let
`L = sum_c N_c`.

**Positive-depth maximal components.** Throughout, maximal components of a
union of old cylinders mean maximal contained positive-depth cylinders.
No depth-zero cylinder is silently added. In particular, when `r=3`, the
union of the two surviving depth-one root cylinders has **two** maximal
components, not one depth-zero component. Whenever a positive-depth cylinder
has proper allowed refinements, its first refinement has `r`, respectively
`s`, equal children. Therefore two proper subcylinders cannot cover a
positive-depth cylinder. This is vacuous at the last finite depth.

The full-support assumption on `rho` refers to every point of the fixed
Cartesian carrier (FA46). A killed old law with additional zero-mass holes in
that carrier is not covered. Calling such a law full-support on its own
smaller support does not satisfy the hypothesis.

### 10.2. Main result

Under these hypotheses,

\[
 \boxed{L\ge3n.}
 \tag{FA50}
\]

In fact, every color has at least two labels. If any color has exactly two
labels, the stronger conditional bound is

\[
 \boxed{L\ge4n-4.}
 \tag{FA51}
\]

If there is no such color, every color has at least three labels directly.
Since `n=p-1 >= 6`, both cases imply (FA50).

For `(r,s)=(3,5)`, the current primes `7,11,31` consequently require at
least `18,30,90` effective labels, respectively. At `p=7`, the branch with
any two-label color requires at least `20` labels. These are necessary
conditions, not existence claims at the stated counts.

### 10.3. Pair balance and support propagation

Define the single actual observation weight

\[
 W(x,y)=\rho(x,y)\frac{u(x,y)}{k(x,y)}
 \quad(k(x,y)>0),\qquad W(x,y)=0\quad(k(x,y)=0).
\]

The first equality in (FA49) is equivalent to, for every actual `x` and all
colors `c,c'`,

\[
 \sum_{y\in Y}W(x,y)\mathbf1_{U_c}(x,y)
 =\sum_{y\in Y}W(x,y)\mathbf1_{U_{c'}}(x,y).
 \tag{FA52}
\]

The second pair gives the analogous equality at each `y`, summing over
`x`. Equivalence follows from (FA48) and the fact that the sum of all color
indicators is `k`, so their common weighted sum must be
`(1/n) sum_y rho(x,y)u(x,y)`. These are equalities of finite sums, with no
exceptional null set. Whenever any color occurs at a point, `k>0` and
`W(x,y)>0`.

It follows that all colors have the same nonempty projection `P` onto `X`
and the same nonempty projection `Q` onto `Y`. For example, if any color
occurs in one row, its weighted sum in (FA52) is positive. Equality forces
every color to occur in that row. The column argument is
identical. Nonemptiness of the family thus forces every color to occur.

There is a stronger local consequence:

> At a fixed `x`, one color's support in `Y` cannot be a strict subset of
> another color's support. The symmetric statement holds at fixed `y`.

The nonempty difference would contribute strictly positive common weight
to one of the equal sums in (FA52). This conclusion permits arbitrary other
colors and arbitrary same-color overlaps.

### 10.4. A uniform reference volume used only as a covering certificate

For geometric counting, separately introduce the uniform laws `nu_r,nu_s`
on the fixed sets `X,Y`, and write `lambda = nu_r x nu_s`. These are
**reference volumes for the same sets**, not a replacement for the actual
law `rho` and not an estimate of its probability or loss budget. They give

\[
 \nu_r(R(a,\alpha))=\frac{r^{1-a}}{r-1},\qquad
 \nu_s(S(b,\beta))=\frac{s^{1-b}}{s-1}.
 \tag{FA53}
\]

For a fixed positive-depth rectangle `A x D`, a contained rectangle with
depth increments `(i,j)` has relative reference volume `r^(-i)s^(-j)`.
Put

\[
 \gamma=\sum_{\substack{i,j\ge0\\(i,j)\ne(0,0)}}r^{-i}s^{-j}
 =\frac{r+s-1}{(r-1)(s-1)}\le\frac78<1.
 \tag{FA54}
\]

If the full exponent pair of `A x D` has already been used, a contained
family of distinct cofactors has at most one rectangle of each proper
subshape. Since that family is finite and the series in (FA54) has infinitely
many positive terms, its total reference volume, counted with multiplicity,
is **strictly less** than `gamma lambda(A x D)`. The finite heights only
reduce the available subshapes. The bound `gamma <= 7/8` uses `r>=3,s>=5`.

Thus such proper rectangles cannot cover `A x D` as a set. This conclusion
is valid regardless of the nonuniform positive values of `rho`.

### 10.5. One original rectangle cannot be a color's whole support

Suppose a color's entire support is one of its original rectangles `A x D`.
Common projections give `P=A,Q=D`, so all other rectangles lie inside it.
At each `x in A`, the distinguished color occupies all of `D`. Equation
(FA52) and positivity force every color to occupy all of `D` at that row.
Every other color must therefore cover the whole set `A x D`.

The distinguished original rectangle has used the full exponent pair.
The proper-subshape certificate in Section 10.4 makes this covering impossible.
In particular,

\[
 N_c\ge2\quad\text{for every color }c.
 \tag{FA55}
\]

Also, two rectangles of a two-label color cannot have one contained in
the other.

### 10.6. Excluding a two-label color with single-cylinder projections

Suppose a two-label color `c` has common projections that are single
positive-depth cylinders `X_0,Y_0`. To cover each projection with only two
cylinder factors, at least one `X` factor equals `X_0` and at least one
`Y` factor equals `Y_0`. If these occur in the same rectangle, the color's
whole support is that full rectangle, contrary to Section 10.5. Otherwise
its support is a cross

\[
 U_c=(X_0\times D)\cup(R\times Y_0),
 \qquad R\subsetneq X_0,\quad D\subsetneq Y_0.
 \tag{FA56}
\]

All other labels lie in `X_0 x Y_0` by common projections. At `y in D`,
the distinguished color occupies all of `X_0`; column balance forces all
colors to occupy all of `X_0`. At `x in R`, row balance forces all colors
to occupy all of `Y_0`. Therefore every color contains the entire cross.

For any `x` outside `R` but inside `X_0`, color `c` has support exactly
`D`. Every other color already contains `D`, so its equal weighted mass
in (FA52) leaves no room for additional support in that row. Consequently
**every color's support is exactly the same cross**. This argument only
uses positivity and common weights; neither a product `rho` nor a fixed
threshold is required.

Any rectangle contained in the cross is contained in at least one arm:
otherwise a point of its `X` side outside `R` and a point of its `Y` side
outside `D` would produce a point outside the cross. The distinguished
color has occupied both full arm exponent pairs. Assign each other
rectangle to an arm containing it. Each is a proper descendant there.

Write

\[
 A=\frac{\nu_r(R)}{\nu_r(X_0)}\le\frac1r,\qquad
 B=\frac{\nu_s(D)}{\nu_s(Y_0)}\le\frac1s.
\]

Section 10.4 bounds the total reference volume of all other rectangles by
strictly less than

\[
 \gamma(A+B)\lambda(X_0\times Y_0).
 \tag{FA57}
\]

But the reference volume of the cross is

\[
 (A+B-AB)\lambda(X_0\times Y_0)
 \ge\left(1-\frac1{r+s}\right)(A+B)\lambda(X_0\times Y_0)
 \ge\gamma(A+B)\lambda(X_0\times Y_0).
 \tag{FA58}
\]

Here `AB/(A+B) <= 1/(r+s)`, and the final inequality is equivalent to
`(r-2)(s-2) >= 3`. This holds for the stated primes. At `(r,s)=(3,5)`
the latter inequality is an equality; the strict finite-family bound
in (FA57) still excludes covering the cross. Even one other color cannot
have the required support. This rules out (FA56).

### 10.7. A two-label color forces two components in each projection

The projection of a two-label color is a union of at most two positive-depth
cylinders. It has either one maximal component or two disjoint maximal
components. This representation is intrinsic: two proper cylinders cannot
cover a positive-depth parent, and two disjoint components can be covered
by only two cylinders only by using those exact components.

Section 10.6 excludes the case where both common projections have one
component. A mixed case is also impossible, even if only one color has
two labels. To see this, suppose

\[
 P=X_1\mathbin{\dot\cup}X_2,\qquad Q=Y_0.
\]

The two rectangles of that color have `X` sides exactly `X_1,X_2`. Their
two `Y` sides cover `Y_0`, so at least one equals `Y_0`. The color therefore
contains a full strip `X_i x Y_0`. At every `x in X_i`, row balance forces
every other color to occupy all of `Y_0`, hence to cover this strip.

Any other rectangle meeting that strip is contained in it. Its `Y` side
is contained in the common `Y_0`; its `X` side is contained in `P` and
meets the maximal positive-depth component `X_i`, so must be contained
in `X_i`. The strip's full exponent pair has already been used. Section 10.4
excludes its covering by the remaining proper subshapes. The symmetric
mixed case is identical, using column balance.

Thus, whenever any two-label color exists, the common projections are

\[
 P=X_1\mathbin{\dot\cup}X_2,\qquad
 Q=Y_1\mathbin{\dot\cup}Y_2,
 \tag{FA59}
\]

with positive-depth maximal components. Every allowed rectangle is
contained in one of the four component products `X_i x Y_j`: a cylinder
contained in the union of two maximal components cannot cross them.

A two-label color must use a matching of these components, so its two
original rectangles are two full component products. Only four such
full products exist. Distinct cofactors prevent any of them from being
used twice; equal component depths can only reduce the number of distinct
available cofactors.

### 10.8. Any three-label color must use a full component product

Work under (FA59), and consider any color with exactly three original
rectangles. Each is contained in one of the four component products,
and its projections must cover both full `X` components and both full
`Y` components. Consider the occupied cells of this two-by-two array.

If just two cells are occupied, they must be a matching, since both rows
and both columns must occur. At least one of these cells contains only
one of the three rectangles. Its row and column have no other rectangles
of this color. To cover the corresponding projections, that single
rectangle must therefore be the full component product.

If three cells are occupied, each contains exactly one rectangle, and
they form an L shape. Relabeling components if necessary, write them as

\[
 A\times B\subseteq X_1\times Y_1,\qquad
 C\times Y_2\subseteq X_1\times Y_2,\qquad
 X_2\times D\subseteq X_2\times Y_1.
 \tag{FA60}
\]

The full factors displayed in the last two rectangles are forced by
the single occupied cell in their respective column and row. Covering
the remaining row and column projections requires

\[
 A\cup C=X_1,\qquad B\cup D=Y_1.
\]

Two proper positive-depth cylinders cannot cover a parent. Thus either
`C=X_1`, making the second rectangle full, or `A=X_1`. Likewise either
`D=Y_1`, making the third rectangle full, or `B=Y_1`. If neither outer
rectangle is full, the central rectangle has both full factors and is
itself full. These are all possibilities with three rectangles.

Therefore every three-label color uses at least one full component
product as an original label.

### 10.9. Counting the four available full shapes

Suppose at least one two-label color exists. Let `c_2,c_3` be the numbers
of colors with exactly two and exactly three labels. By Sections 10.7--10.8,
each two-label color uses two full component products and each three-label
color uses at least one. A full product cannot be reused, so

\[
 2c_2+c_3\le4.
 \tag{FA61}
\]

Section 10.5 rules out colors with fewer than two labels. All remaining
colors therefore have at least four labels, and

\[
 \begin{aligned}
 L&\ge2c_2+3c_3+4(n-c_2-c_3)\\
  &=4n-2c_2-c_3\\
  &\ge4n-4.
 \end{aligned}
 \tag{FA62}
\]

If no two-label color exists, every color has at least three labels and
`L >= 3n`. Otherwise (FA62) implies the same conclusion, since `n>=6`.
This proves the main result.

The proof uses no constant-threshold weight-ratio estimate, no product
assumption on the actual old law, and no enumeration of a finite list
of geometries. Its geometric series is a reference-volume certificate
that specified sets cannot be covered by the available distinct shapes.
The essential unhandled boundaries are depth-zero old factors, an actual
old law with additional holes in the fixed Cartesian carrier, and the
existence or nonexistence of families at larger label counts.

### 10.10. Why positivity on the entire carrier cannot be dropped

Take `E=n,F=1`. For each color `c=a`, where `1 <= a <= n`, use the label
with old conditions `x=1 mod r^a`, `y=1 mod s`, and current color `a`.
These are `n` original classes with distinct numerical moduli `r^a s p`.
Let the old law be the point mass at `(1,1)` in the fixed carrier (FA46).

Every color is bad at that one old history, so `k=n`. For any positive
threshold below one, including an arbitrary history-dependent choice,
the clipped density at the supported point is one for every current
color: the bad-density formula is `(1-delta)/(1-delta)=1`. Thus both
pair marginals equal the corresponding old marginal times `nu_p`, but
there are only `n < 3n` labels. The law has zero-mass holes in the full
Cartesian carrier and therefore violates the theorem's strict-positivity
hypothesis.

This is an abstract-source counterexample to dropping that hypothesis.
It is not asserted to arise from any prescribed sequence of original
preceding clipping stages. It is not an odd covering: the integer `2`
fails the old condition `1 mod r` for every listed class.

The count theorem supplies no quantitative lower bound on marginal total
variation, no construction with `3n` or more labels, and no optimality
claim for its numerical constant. Its conclusions remain ordinary
mathematics in this section, without a Lean certification claim.

This argument is repository-derived; no literature-priority assertion is made.

