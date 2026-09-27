[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="six-prime-prefix-measures-close-all-six-vertex-blocks"></a>
# Six-prime prefix measures close all six-vertex graph blocks

Every finite family of residue classes with pairwise distinct odd moduli
greater than one is noncovering if each block of its prime-interaction
graph has at most six vertices. The number of primes in the whole graph
is unrestricted, and every original finite prime-power height and residue
is allowed.

The new step handles all twelve root-3 child sets left by
[Chapter 28](28-unique-root-reserve-and-shared-descendant-budget.md).
It applies the first six coordinates of Michael Schroeder's existing
conditional-measure construction, transports the resulting measure to
the actual core primes, and deletes the actual attachment blockers using
its coordinate marginals. This conclusion uses Schroeder's ordinary
mathematical arguments and exact source calculations, together with the
recursion of [Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md)
and [Chapter 25](25-six-vertex-block-fees-and-a-finite-prime-core-frontier.md).
It is not a claim of a completed local Lean replay of Schroeder's theorem
or of an unrestricted resolution of Erdős #7.

The source is *Nine Prime Divisors in Odd Distinct Covering Systems*,
version 1.0.1, DOI
[10.5281/zenodo.22759614](https://doi.org/10.5281/zenodo.22759614).
The [library entry](../../../../Library/Arith/schroeder2026nine.md)
records its attribution, archive identity, licenses, and verification
boundary. The source's total-prime theorem alone does not imply the
statement above: the present graph may have arbitrarily many primes.
The transferable input is the actual submeasure constructed on six core
coordinates, with its marginal bounds.

## 1. Stop the source construction after six prime coordinates

Use the reference coordinates
\[
 (p_1,\ldots,p_6)=(3,5,7,11,13,17).
\]
Schroeder's Lemma 2.2 completes a finite family to selected pure and mixed
classes, preserving inclusion of its original covered set. Completion
can insert classes or move selected residues; it does not preserve each
original label and residue separately. A measure avoiding the completed
covered set nevertheless avoids every original class.

Start with the source's anchor submeasure \(\mathbf1_AH\) on the
3- and 5-coordinates, where \(A\) avoids every completed class supported
on those two primes. Expose 7, 11, 13, and 17 with the normalized capped
conditional kernels of source Lemma 3.1, deleting each current mixed bad
set. The source's charged enlargement at 7 may be retained; its ordinary
upper inventory dominates its charge by Lemma 9.2. Stop after 17. Every
class in the original six-coordinate family has then been removed.
Auxiliary pure completions at 19 and 23 are unnecessary; the selected
mixed completion moduli in source equation (2.2) involve no prime above
11.

The four kernel caps from source equation (3.4) are
\[
 C_7=\frac32,\qquad C_{11}=\frac53,\qquad
 C_{13}=\frac32,\qquad C_{17}=2.
 \tag{SP1}
\]
They are conditional bounds on the complete coordinates. The construction
retains the joint actual law; its comparison weights are used only to
bound losses.

The basic anchor calculation in source Section 5.1 has 32 vertices,
encoded by
\[
 (a,b,c,-1,j,0,0,0,-1),\qquad
 a\in\{1,2\},\ b\in\{2,4\},\ c\in\{a,3-a\},\ 1\le j\le4.
\]
For each vertex the source functions `reserve` and `ordinary` give a
lower reserve \(R\) and six upper losses
\((L_7,L_{11},L_{13},L_{17},L_{19},L_{23})\), all in units of Haar
mass \(1/135\). Each ordinary loss is rounded upward to a multiple
of \(10^{-10}\). Reading these existing bounds and retaining the first
four losses gives
\[
 \min\left(R-L_7-L_{11}-L_{13}-L_{17}\right)
 =\frac{68006602781}{10000000000}>\frac{27}{4}.
 \tag{SP2}
\]
The minimum occurs for \((a,b,c)=(2,4,1)\) and
\(j\in\{1,3,4\}\). At any such vertex, \(R=135/4\) and the
four upward-rounded losses are
\[
 \frac{105625469639}{10^{10}},\quad
 \frac{57425782611}{10^{10}},\quad
 \frac{6570532933}{10^9},\quad
 \frac{40736815639}{10^{10}}.
\]

The reserve is affine in the basic pure-5 budget and each ordinary upper
cost is convex. The source's vertex interpolation therefore applies to
this prefix: dropping the two later costs preserves the same concavity
argument. All 32 basic vertices already suffice; no finer anchor screen
or terminal-state comparison is needed.

First-hit accounting, source Lemma 3.2, consequently supplies a
submeasure \(\mu\) on the original reference coordinates satisfying
\[
 \mu(X)\ge m:=\frac{68006602781}{1350000000000}>\frac1{20},
 \qquad \mu\text{ is supported on the original uncovered set}.
 \tag{SP3}
\]
This is a prefix consequence of the source construction and its existing
numerical bounds. It is not a separately stated theorem attributed to
the author. The arbitrary-height completion and kernel arguments remain
the cited ordinary source premises.

## 2. Keep the coordinate marginals of the unnormalized survivor

In addition to (SP3), the measure has marginal domination
\[
 \mu_i(D)\le\alpha_i H_{p_i}(D)
 \quad\text{for every measurable one-coordinate set }D,
 \qquad
 (\alpha_1,\ldots,\alpha_6)
 =\left(1,1,\frac32,\frac53,\frac32,2\right).
 \tag{SP4}
\]
For either anchor coordinate, start from
\(\mathbf1_AH\le H\) and integrate every later normalized kernel
in reverse order. For a later coordinate, use its conditional density
cap \(C_{p_i}\) when integrating that coordinate. Other unconstrained
kernels integrate to one, and deleting forbidden sets only decreases
mass. This is the single-coordinate specialization of the proof of
source Lemma 3.2. The full-coordinate density caps make it valid for
arbitrary measurable coordinate sets, beyond individual prefix
cylinders. Undoing the source's coordinatewise Haar-preserving tree
normalizations preserves these bounds.

The measure is not normalized after deletions. In particular, neither
(SP3) nor (SP4) describes a normalized law on the survivors. The source
also gives the joint bound \(\mu\le(15/2)H\), which would imply
only
\[
 H(\text{uncovered})\ge\frac{68006602781}{10125000000000}.
\]
That scalar bound is insufficient for all attachment budgets below.
The mass and marginal bounds (SP3)–(SP4) retain the information needed
for deletion of those coordinate sets.

## 3. Transport the measure to the actual six primes

Let \(q_1<\cdots<q_6\) be the actual odd core primes, so
\(p_i\le q_i\). Use the complete-coordinate heights \(A_i\) of
the full original family, including all attachment classes. These heights
may exceed the exponents needed by classes internal to the core. A source
measure on infinite reference coordinates projects to these finite heights
without changing its mass or the applicable marginal bounds.

For each coordinate and digit position, choose an independent uniform
shift \(b_{i,\ell}\in\mathbb Z/q_i\mathbb Z\), and send the
reference digit \(u\in\{0,\ldots,p_i-1\}\) to
\(u+b_{i,\ell}\pmod{q_i}\). This is the random prefix-preserving
injection \(F_i\) of source Lemma C.1. Write \(F=\prod_i F_i\).
The inverse image of an original core class is empty or a prefix
cylinder with the same complete exponent vector. Discarding empty
inverse images therefore preserves distinctness and nonzero exponent
vectors.

For every \(F\), apply (SP3)–(SP4) to that pullback family to obtain
\(\mu_F\). It is supported outside the pullback covered set, has
mass at least \(m\), and has the same marginal factors \(\alpha_i\).
There are finitely many injections at these finite heights, so choosing
one measure for each \(F\) requires no measurable-selection assertion.
Define a measure on the actual original core coordinates by
\[
 \nu=\mathbb E_F[F_*\mu_F].
\]
It avoids every original core class and has mass at least \(m\). For
every set \(D\) on actual coordinate \(q_i\),
\[
 \begin{aligned}
 \nu_i(D)
 &=\mathbb E_F\mu_F(F_i^{-1}D)\\
 &\le\alpha_i\mathbb E_F H_{p_i}(F_i^{-1}D)
 =\alpha_i H_{q_i}(D).
 \end{aligned}
 \tag{SP5}
\]
The last equality is the uniform-output averaging calculation of source
Lemma C.1. Dependence of \(\mu_F\) on \(F\) is harmless: the
preceding domination holds separately for every \(F\) with the same
constant. No product structure or conditional-kernel representation of
\(\nu\) on the actual primes is asserted or needed. This
measure-valued extension of the source averaging argument is the ordinary
bridge used here. The same averaging, applied to arbitrary sets in the
full product, also transports the source bound \(\mu_F\le(15/2)H_p\)
to \(\nu\le(15/2)H_q\).

## 4. Pay the actual attachment blockers

Chapter 25 proves all legal non-3 orientations of six-vertex blocks.
Every unresolved root block contains \(\{3,5,7\}\), so distinct
blocks cannot both be unresolved: they share at most one vertex. Thus
an unresolved block \(K\) is unique, has parent 3, and all its strict
descendant blocks have established recursive fees before \(K\) is
estimated.

Write its sorted children as \(J\). Apply (SP5) to the original
pure classes on \(\{3\}\cup J\) and all original classes supported
within that core. Their moduli remain pairwise distinct. The resulting
\(\nu\) avoids every one of these original classes, including all
original pure classes.

For each \(q\in J\), let \(W_q\) be the union of the actual
outgoing strict-descendant block blockers on the complete \(q\)-coordinate.
The charge bounds used in the exact recursion (CK31) give directly
\[
 H_q(W_q)\le c_q e_q,\qquad
 e_q=\sum_{r\in D_q}f(r),\qquad
 c_5=\frac3{10},\quad c_q=\frac2{q-1}\ (q\ge7).
 \tag{SP6}
\]
This is a bound on the blockers themselves, before taking their union
with pure classes. It is not obtained by subtracting a pure-class upper
bound from an upper bound on \(V_q^c\).

Let \(W_3\) be the union of blockers of the other outgoing root blocks.
Use the unchanged fees and total bound \(F_*=1493/3072\), and set
\[
 C=\sum_{q\in J}f(q),\qquad E=F_*-C,\qquad
 x=\sum_{q\in J}e_q.
\]
The actual strict descendant sets are pairwise disjoint, and the other
root blocks' charged immediate child sets avoid them and \(J\).
Exactly as in Chapter 28, these charges give
\[
 H_3(W_3)\le E-x.
 \tag{SP7}
\]
All sets and budgets belong to the same original family.

The marginal factors for the sorted children are
\((1,3/2,5/3,3/2,2)\). For every one of the twelve inherited tuples,
\[
 \max_{q\in J}\alpha_qc_q\le\frac12.
\]
Combining (SP5)–(SP7) with the union bound for the actual submeasure gives
\[
 \nu\left(W_3\cup\bigcup_{q\in J}W_q\right)
 \le E-x+\sum_{q\in J}\alpha_qc_qe_q
 \le E-\frac{x}{2}\le E.
 \tag{SP8}
\]
Here each coordinate set denotes its cylinder in the full core product.
The child domains need not be independent under \(\nu\).

The twelve budgets are

| Actual child set \(J\) | Outside budget \(E\) |
| --- | ---: |
| \(5,7,11,13,17\) | \(3/1024\) |
| \(5,7,11,13,19\) | \(5/1024\) |
| \(5,7,11,13,23\) | \(13/2048\) |
| \(5,7,11,13,29\) | \(111/16384\) |
| \(5,7,11,13,31\) | \(223/32768\) |
| \(5,7,11,13,37\) | \(1791/262144\) |
| \(5,7,11,17,19\) | \(67/3072\) |
| \(5,7,11,17,23\) | \(143/6144\) |
| \(5,7,11,19,23\) | \(155/6144\) |
| \(5,7,13,17,19\) | \(131/3072\) |
| \(5,7,13,17,23\) | \(271/6144\) |
| \(5,7,13,19,23\) | \(283/6144\) |

Thus
\[
 E\le\frac{283}{6144}<\frac1{20}<m.
\]
The surviving submeasure after the actual attachment deletions has mass
at least \(m-E\), and therefore strictly more than
\[
 \frac1{20}-\frac{283}{6144}=\frac{121}{30720}>0.
 \tag{SP9}
\]
The smallest exact lower bound \(m-E\) is
\[
 \frac{11647971187}{2700000000000}>0,
\]
attained at \(J=(5,7,13,19,23)\). The transported joint density
cap additionally gives core Haar mass strictly greater than
\(121/230400\) after these attachment deletions. This last number
concerns the six-coordinate core, before witness gluing through the
remaining graph.

A surviving core point avoids the original core classes and belongs to
each actual attachment-compatible coordinate domain. The private sides
of its attached blocks are disjoint, so the established block-cut witness
gluing extends this point through all descendants and the other root
blocks. Different components glue by CRT. This closes all twelve entries
left by Chapter 28. Together with the already established cases, it
proves noncoverage whenever all graph blocks have at most six vertices.
The total number of graph vertices and the original finite heights remain
unrestricted.

## 5. Exact numerical input and verification boundary

The portable standard-library program
[six_prime_prefix_certificate.py](../frontier/cover-geometry/six_prime_prefix_certificate.py)
reads the explicit
[geometry input](../frontier/cover-geometry/six_prime_prefix_geometry.json)
and produces the [exact certificate](../frontier/cover-geometry/six_prime_prefix_certificate.json).
It imports no source verifier and runs no geometry enumerator. The input
retains all required integer maxima, their original file hashes, source
identifiers, and the complete MIT attribution and license text.

The source archive is pinned by SHA-256
`9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`.
Its original `checks/verify.py` has SHA-256
`e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135`.
The repository's existing source verification regenerated all 7,814
geometry batches on 19 September 2026 and matched the author's recorded
finite certificates. It did not replay the full source Lean development.

For (SP2), only 72 of those already verified cache batches are read,
containing 51,840 integer queries. No geometry is regenerated. The 32
basic prefix rows are exact rational postprocessing of the source's
ordinary upper losses with its prescribed upward rounding. The useful
certificate retains those rows and the provenance of the finite source
inputs, verifies the strict bound \(m>1/20\), and checks the twelve
budgets and all marginal attachment coefficients. The twelve tuples
match Chapter 28's exact remaining list.

These calculations establish the finite arithmetic input. The
arbitrary-height completion, conditional kernels and convex comparison
are cited ordinary source arguments. Sections 2–4 give the marginal
transport and actual-attachment assembly explicitly. No source comparison
weight is used as an actual probability law, no independent maxima are
combined as a joint realization, and no completed-label preservation or
full source kernel replay is claimed.

The program requires Python 3.10 or later and rejects optimized `-O`
execution. From the repository root, reproduce the certificate with

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/six_prime_prefix_certificate.py --geometry docs/reports/erdos7-odd-covering/frontier/cover-geometry/six_prime_prefix_geometry.json --output /tmp/six-prime-prefix-certificate.json
```
