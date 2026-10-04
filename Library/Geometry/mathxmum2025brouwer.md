---
bibkey: mathxmum2025brouwer
authors: Math_XMUM
year: 2025
title: Brouwer fixed-point theorem via Scarf's lemma
doi: null
url: https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb
claim: Finite indexed-order colorful-cell existence and the fixed-point theorem for continuous self-maps of positive-index real standard simplices.
strata_touched:
  - D5/S3/Combinatorics/Scarf/Dominance
  - D5/S3/Combinatorics/Scarf/Incidence
  - D5/S3/Combinatorics/Scarf/ColorfulDoors
  - D5/S3/Combinatorics/Scarf/ColorfulCell
  - D5/S3/Geometry/FixedPoint/SimplexMesh
  - D5/S3/Geometry/FixedPoint/Brouwer
license: MIT, Copyright (c) 2025 Math_XMUM
triage: anchor
---

<!-- GID: D5/L/Geometry/mathxmum2025brouwer -->
# Scarf's lemma and the real simplex fixed-point theorem

The source is Math_XMUM's *Brouwer* repository, revision
`f9dc162170e8711f78059a87edcd38ffc44a1bfb`. The year in the citation is the copyright
notice's year. The statements and mathematical arguments below are known results,
with no mathematical novelty claim. The two primary files are
[Scarf.lean](https://github.com/math-xmum/Brouwer/blob/f9dc162170e8711f78059a87edcd38ffc44a1bfb/Gametheory/Scarf.lean)
and [Brouwer.lean](https://github.com/math-xmum/Brouwer/blob/f9dc162170e8711f78059a87edcd38ffc44a1bfb/Gametheory/Brouwer.lean).

## Verified locator

The immutable source revision is `f9dc162170e8711f78059a87edcd38ffc44a1bfb` at
[https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb](https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb).
The exact source files and declarations used here are:

- `Gametheory/Scarf.lean`: `isDominant_erase_iff_M_set_empty`, `internal_door_two_rooms`, `doors_of_NCroom`, and `Scarf`.
- `Gametheory/Brouwer.lean`: `size_bound_key` and `Brouwer`.

The standalone collision declaration is retired in this receiving unit; its representative-selection argument is applied directly at the three live consuming proof sites.

## 1. Representative selection and indexed order objects

**Lemma 1.1 (one-unit image deficit).** For arbitrary types $A,B$ with decidable
equality, a finite subset $s$ of $A$, and $f:A\to B$, if
$|s|=|f(s)|+1$, then there are distinct $a,b\in s$ such that $f(a)=f(b)$
and $f$ is injective on $s\setminus\{a,b\}$.

**Proof.** Equal-image cardinality would imply injectivity and contradict the
deficit, so a collision pair exists. A third point with that image would give
$|f(s)|\leq |s|-2$ by separating the three-point fiber. The erased image is
therefore $f(s)\setminus\{f(a)\}$ and has the same cardinality as
$s\setminus\{a,b\}$, proving injectivity there.

**Definition 1.2 (dominant cells).** Let $T$ carry, for each index $i\in I$,
a linear order $\leq_i$. For finite subsets $\sigma\subseteq T$ and
$C\subseteq I$, call $(\sigma,C)$ dominant if

$$\forall y\in T\;\exists i\in C\;\forall x\in\sigma,\quad y\leq_i x.$$

A cell is a dominant pair. A room is a cell with $|C|=|\sigma|$.
A door is a cell with $|C|=|\sigma|+1$. An internal door has
$\sigma\ne\varnothing$; an outside door has $\sigma=\varnothing$.
For nonempty $\sigma$, let $m_i(\sigma)=\min_{\leq_i}\sigma$.
Every point of a dominant nonempty cell is one of these minima, so
$\sigma=\{m_i(\sigma):i\in C\}$ and $|\sigma|\leq |C|$.

**Definition 1.3 (incidence).** A door $(\tau,D)$ is incident to a room
$(\sigma,C)$ when either there exists $x\notin\tau$ with
$\sigma=\tau\cup\{x\}$ and $C=D$, or there exists $j\notin C$ with
$\sigma=\tau$ and $D=C\cup\{j\}$. Both the room cell condition and
the door condition are part of this relation.

**Definition 1.4 (the missing-minimum sets).** For a nonempty door
$(\tau,D)$ and $i\in I$, set

$$M_i=\{y\in T:\forall k\in D\setminus\{i\},\quad m_k(\tau)<_k y\}.$$

When $T$ is finite and $M_i$ is nonempty, its $i$-maximum is the point
$r_i\in M_i$ with $y\leq_i r_i$ for every $y\in M_i$.

## 2. Internal incidence

**Lemma 2.1 (erasing an index).** For finite $T$, a nonempty door
$(\tau,D)$ and every $i\in D$, dominance of $(\tau,D\setminus\{i\})$
is equivalent to existence of distinct $a,b\in D$ satisfying

$$m_a(\tau)=m_b(\tau),\qquad i\in\{a,b\},\qquad M_i=\varnothing.$$

**Proof.** The image of the minimum map is $\tau$ and its domain has
one more point. Lemma 1.1 gives a collision pair. Erasing an index outside
that pair leaves the collision and gives an image too small to be $\tau$.
For a preserving erasure, dominance excludes every point of $M_i$.
Conversely, emptiness of $M_i$ gives, for every $y$, an index
$k\in D\setminus\{i\}$ with $y\leq_k m_k(\tau)$, hence
$y\leq_k x$ for all $x\in\tau$.

**Theorem 2.2 (two incident rooms).** For finite $T$, every internal door
$(\tau,D)$ has precisely two distinct incident rooms: there exist
$(\sigma_1,C_1)\ne(\sigma_2,C_2)$, both rooms incident to $(\tau,D)$,
and every incident room is one of these two pairs.

**Proof.** Choose the two colliding minimum indices $a,b$. The sets $M_a$
and $M_b$ are disjoint: simultaneous strict inequalities contradict dominance
at their common point. Inserting $x\notin\tau$ preserves dominance exactly
when $x$ is the maximum of $M_a$ or of $M_b$. Such maxima are outside
$\tau$. Erasing an index preserves dominance exactly in the empty-set cases
of Lemma 2.1. Thus a nonempty $M_a$ contributes
$(\tau\cup\{r_a\},D)$, while an empty $M_a$ contributes
$(\tau,D\setminus\{a\})$; the same holds for $b$. Disjointness makes
the two inserted maxima distinct; inserted-point and erased-index cases are
distinct; and two erased color sets differ because $a\ne b$. The same
characterization exhausts all rooms in each of the four cases.

## 3. Colors and parity

**Definition 3.1 (colorful and nearly colorful cells).** Given $c:T\to I$,
a cell $(\sigma,C)$ is colorful if $c(\sigma)=C$, nearly colorful if
$|C\setminus c(\sigma)|=1$, and of missing color $i$ if
$C\setminus c(\sigma)=\{i\}$. Write $\mathrm{NCdoors}(\sigma,C)$
for the set of nearly colorful doors incident to $(\sigma,C)$.

**Lemma 3.2 (two nearly colorful doors).** Every nearly colorful room
$(\sigma,C)$ has distinct doors $d_1,d_2$ with
$\mathrm{NCdoors}(\sigma,C)=\{d_1,d_2\}$.

**Proof.** Cardinality gives either $|\sigma|=|c(\sigma)|$ or
$|\sigma|=|c(\sigma)|+1$. In the first case coloring is injective on
$\sigma$ and there is a unique point $y$ whose color lies outside $C$.
The doors are $(\sigma\setminus\{y\},C)$ and
$(\sigma,C\cup\{c(y)\})$. Deleting any other point or inserting any
other color creates two missing colors. In the second case
$c(\sigma)\subseteq C$. Lemma 1.1 supplies a collision pair $x,y$;
the doors are $(\sigma\setminus\{x\},C)$ and
$(\sigma\setminus\{y\},C)$. A third point in that fiber violates the
one-unit deficit, while deletion of any uniquely colored point creates a
second missing color. An inserted color outside $C$ also creates two
missing colors. These statements prove both construction and exhaustion.

**Theorem 3.3 (Scarf's lemma).** For finite nonempty $T,I$, any family of
linear orders on $T$ indexed by $I$, and any coloring $c:T\to I$, there
exists a colorful dominant cell $(\sigma,C)$.

**Proof.** Fix $i\in I$ and count incidences with doors of missing color
$i$. There is exactly one exterior incidence: the empty door with index set
$\{i\}$ is incident to the singleton room consisting of the maximum of
$T$ in the $i$-order. Every internal-door fiber has two rooms by Theorem 2.2.
An incident room is either colorful or of the same missing color. Every
noncolorful-room fiber has two doors by Lemma 3.2, and nearly colorful doors
incident to a room of missing color $i$ also have missing color $i$.
Partitioning the same finite incidence set first by outside/internal doors
and then by colorful/noncolorful rooms shows that the colorful incidence
count is odd. Its positivity produces a colorful room and hence a colorful
cell. No colorful cell is assumed in the construction.

## 4. Simplex lattices and limits

**Definition 4.1 (the lattice and coordinate orders).** For positive integers
$n,l$, set

$$T_{n,l}=\{x\in\{0,\ldots,l\}^{\{0,\ldots,n-1\}}:\sum_i x_i=l\}.$$

The order indexed by $i$ first compares $x_i$ and then compares the whole
coordinate tuple lexicographically. The projection to the real standard
simplex is $x\mapsto(x_i/l)_i$, where

$$\Delta_n=\{p\in\mathbb R^n:p_i\geq0,\quad\sum_i p_i=1\}.$$

**Lemma 4.2 (coordinate minima bound).** For every nonempty dominant
$(\sigma,C)$ in $T_{n,l}$, if $m_i=\min\{x_i:x\in\sigma\}$, then

$$l<\sum_{i\in C}m_i+|C|.$$

**Proof.** If the reverse weak inequality holds, assign $m_i+1$ to indices
in $C$ and zero to the others. Their sum is at most $l$. Add the residual
mass to coordinate zero. This gives a point of $T_{n,l}$ whose selected
coordinates strictly exceed the coordinate minima. The indexed-order minima
of $\sigma$ realize those coordinate minima, contradicting dominance.

The same inequality bounds differences of cell coordinates by $2(n+1)$ and
bounds coordinates outside $C$ by $n+1$. After division by $l$ these give
vanishing cell diameter and vanishing coordinates outside a constant $C$.

**Theorem 4.3 (Brouwer on real standard simplices).** For every positive
integer $n$ and every continuous $f:\Delta_n\to\Delta_n$, there exists
$p\in\Delta_n$ with $f(p)=p$.

**Proof.** Since the coordinates of $x$ and $f(x)$ have the same unit sum,
there is a coordinate $i$ with $x_i\leq f(x)_i$. Choose such a coordinate
as the color of each projected lattice point. Scarf's lemma gives a colorful
dominant cell at every mesh size $l=k+1$. There are only finitely many
possible index sets, so one occurs along an increasing subsequence.
Compactness supplies a further increasing subsequence of cell points
converging to $z\in\Delta_n$. The coordinate estimates make cell diameters
tend to zero, so points of each selected color converge to the same $z$.
Continuity gives $z_i\leq f(z)_i$ for selected colors. All other coordinates
of $z$ vanish. Nonnegativity and equality of the total sums force equality
in every coordinate, including the unselected ones. Thus $f(z)=z$.
The case $n=1$ is the singleton simplex and is included.

## 5. Finite real boxes

Let $E$ be finite and let

$$\Omega=\{x:E\to\mathbb R:\forall e,\ a_e\leq x_e\leq b_e\}$$

be nonempty. A continuous $F:\Omega\to\Omega$ has a fixed point.
For empty $E$ there is exactly one coordinate function and hence one point
of $\Omega$; every self-map fixes it. For nonempty $E$, enumerate it by
$\{0,\ldots,k-1\}$ and set $R=1+\sum_e(b_e-a_e)>0$.
Embed $x$ in $\Delta_{k+1}$ with coordinates
$(x_e-a_e)/R$ and one extra coordinate $1-\sum_e(x_e-a_e)/R$.
The projection sends simplex coordinates to

$$P(p)_e=\max(a_e,\min(b_e,a_e+Rp_e)).$$

Both maps are continuous and $P(\mathrm{embed}(x))=x$.
The fixed point of $\mathrm{embed}\circ F\circ P$ therefore gives a
fixed point of $F$. Zero-width coordinates require no division by their
width and are included.

For strictly positive widths and a continuous $K:\Omega\to\mathbb R^E$,
fix a target $\kappa\in\mathbb R^E$. If $K_e(x)>\kappa_e$ throughout
the entire lower face $x_e=a_e$ and $K_e(x)<\kappa_e$ throughout the
entire upper face $x_e=b_e$, the continuous clamped map

$$F(x)_e=\max(a_e,\min(b_e,x_e+K_e(x)-\kappa_e))$$

has a fixed point in the interior. Neither face can contain it because of
the corresponding strict inequality. At an interior fixed point the clamp
cannot hide a nonzero displacement, so $K(x)=\kappa$. These are statements
about a single specified box and its actual maps. They give no geometric
realization, uniqueness, trajectory containment, Hessian, or convergence
assertion without the corresponding additional hypotheses.

## Supplier reuse and retirement

The six source modules retain the supplier's immutable leaf results as ordinary
repository content, with the complete MIT notice. They introduce no Lake package
dependency. The supplier and this repository both pin
`leanprover/lean4:v4.33.0` and mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Matching pins, source availability
and the MIT notice are source qualification facts; they do not establish the
currently open A17 automatic dependency-admission predicates.

A retained supplier declaration is retired in favor of direct reuse when this
repository's own pinned mathlib contains an equivalent declaration with the
same hypotheses and conclusion. Equivalence and its exact application must be
checked against that pinned source. Supplier uptake by another repository is
not the retirement condition.

## License

The selected source portions carry the following complete supplier notice.
The immutable source license is
[LICENSE](https://github.com/math-xmum/Brouwer/blob/f9dc162170e8711f78059a87edcd38ffc44a1bfb/LICENSE).

```text
MIT License

Copyright (c) 2025 Math_XMUM

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
