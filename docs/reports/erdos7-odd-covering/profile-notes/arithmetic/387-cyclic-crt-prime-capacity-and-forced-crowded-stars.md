[Index](../../marked_head_profile.md) · [Original extremal family](../321-384/350-extremal-paired-branch-and-source-support.md) · [Original prime-star costs](382-prime-star-overlaps-and-no-prime-excess.md)

# Cyclic CRT witnesses and local prime-capacity noncoverage

A finite palette of distinct nonunit moduli is noncovering for every
residue assignment if, at each prime, the number of its prime neighbors
plus one possible higher-power channel is smaller than the prime.
The proof constructs a coprime-disjoint family on the original palette,
using cyclic support labels and complete prime-power prefixes. An
explicit product set avoids this witness. Shearer's theorem then
transfers its positive avoidance bound to arbitrary residues on the
same palette.

When the palette contains its degree-two divisors, the local condition
also characterizes coprime-disjoint realizability. In particular every
coprime-disjoint divisor ideal is noncovering. Applied to a hypothetical
extremal odd cover, the result forces a crowded original prime star,
so the positive excess cost in report 382 occurs somewhere. This does
not supply a uniform excess margin or resolve unrestricted Erdős #7.

The construction and its applications are ordinary mathematical
deductions. The Shearer transfer and the earlier full-divisor results
are cited below. No literature-priority or Lean-verification claim is
made.

## 1. The original palette and its prime graph

Let \(D\) be a nonempty finite set of distinct integers greater than
one. Oddness is not needed until section 5. Put

\[
 Q=\operatorname{lcm}(D),\qquad
 P=\{p:p\text{ prime},\ p\mid Q\},\qquad
 h_p=v_p(Q),\qquad \epsilon_p=\mathbf1_{h_p\ge2}.
 \tag{CC1}
\]

Join distinct primes \(p,q\) when \(pq\mid d\) for some original
\(d\in D\). Let \(N(p)\) be this neighbor set, \(g_p=|N(p)|\), and
\(\ell_p=|\{q\in N(p):q<p\}|\). This prime graph is different from
the gcd dependency graph on the original moduli. Define

\[
 K(D)=P\cup\{p^2:h_p\ge2\}
       \cup\{pq:p<q,\ q\in N(p)\}.
 \tag{CC2}
\]

The local capacity condition is

\[
 g_p+\epsilon_p\le p-1\qquad(p\in P).
 \tag{CC3}
\]

A residue assignment is **coprime disjoint**, abbreviated CD, if every
pair of classes whose numerical moduli have gcd greater than one is
disjoint. For \(J\subseteq D\), write

\[
 \Psi(J)=
 \sum_{\substack{I\subseteq J\\I\text{ pairwise coprime}}}
      (-1)^{|I|}\prod_{d\in I}\frac1d.
 \tag{CC4}
\]

The empty term is one. Throughout, \(H\) denotes uniform probability
on the **original** carrier \(\mathbb Z/Q\mathbb Z\).

## 2. A cyclic assignment realizes the local capacities

Assume CC3. At each prime assign its neighbors distinct colors

\[
 c_p(q)=1+\epsilon_p+|\{r\in N(p):r<q\}|.
 \tag{CC5}
\]

These colors lie in \(\{1,\ldots,p-1\}\), and in
\(\{2,\ldots,p-1\}\) when \(h_p\ge2\). For a pure power
\(p^a\in D\), prescribe

\[
 b_{p^a}=\begin{cases}
 0\pmod p,&h_p=1,\\
 p^{a-1}\pmod{p^a},&h_p\ge2.
 \end{cases}
 \tag{CC6}
\]

For a mixed modulus \(d=\prod_{p\in T}p^{a_p}\), \(|T|\ge2\),
let \(\sigma_T\) be the successor cycle on \(T\) in increasing
numerical order, with the largest prime pointing back to the smallest.
Use CRT to prescribe one actual residue \(b_d\bmod d\) by

\[
 b_d\equiv c_p(\sigma_T(p))p^{a_p-1}\pmod{p^{a_p}}
 \qquad(p\in T).
 \tag{CC7}
\]

Thus a local word has zero digits below depth \(a_p-1\), followed
by a nonzero color at that depth. Every original modulus appears once;
no divisor is added and no modulus or prime is relabeled.

Two facts prove that this is CD. First, for \(a<b\) and nonzero
\(c,c'\bmod p\),

\[
 cp^{a-1}\not\equiv c'p^{b-1}\pmod{p^a}.
 \tag{CC8}
\]

Second, if two supports \(T,U\) intersect and their successor maps
agree at every common prime, then \(T=U\). Indeed, their nonempty
intersection is closed under \(\sigma_T\); iterating that single
cycle exhausts \(T\), so \(T\subseteq U\). Applying the same
argument to \(U\) proves equality.

Now take distinct \(d,e\) with \(\gcd(d,e)>1\). Different
exponents at a shared prime separate their prefixes by CC8. At equal
exponent, a pure power and a mixed class have different colors:
\(0\) versus a nonzero color when \(h_p=1\), and \(1\) versus
at least \(2\) when \(h_p\ge2\). For two mixed classes with equal
exponents at every shared prime, distinct supports have different
successors at some shared prime. Equal supports instead force some
exponent to differ, since the numerical moduli are distinct. In all
cases the residues disagree modulo their gcd, as required.

## 3. Explicit survivors give strict positivity

A single uncovered point is already supplied by

\[
 x_*\equiv\begin{cases}
 p-1\pmod p,&h_p=1,\\
 0\pmod{p^{h_p}},&h_p\ge2.
 \end{cases}
 \tag{CC9}
\]

It avoids every pure power. It avoids a mixed class at any support
prime of height at least two. For a remaining mixed support, all
heights equal one. At its largest prime \(p\), the successor is a
smaller neighbor, so
\(c_p(\sigma_T(p))\le\ell_p\le p-2\), whereas the chosen digit is
\(p-1\). The last inequality uses the original numerical primes:
there are at most \(p-2\) integers strictly between \(1\) and \(p\).

A larger product set is useful. At height one, allow all nonzero
roots except colors pointing to smaller neighbors. At height at least
two, allow the zero word, and words whose first nonzero digit belongs
to \(\{2,\ldots,p-1\}\) and is not a color pointing to a smaller
neighbor. All digits above this first nonzero digit are free. The
numbers of allowed full coordinates are

\[
 M_p=\begin{cases}
 p-1-\ell_p,&h_p=1,\\
 1+(p-2-\ell_p)\dfrac{p^{h_p}-1}{p-1},&h_p\ge2.
 \end{cases}
 \tag{CC10}
\]

They are positive. For the second case, CC3 gives
\(\ell_p\le g_p\le p-2\). Each pure power is avoided by its first
nonzero digit. Each mixed class is avoided at its largest support
prime: agreement with its prefix would require exactly the excluded
color at its specified depth. Thus the product set \(W\) satisfies

\[
 H(W)=\prod_{p\in P}\frac{M_p}{p^{h_p}}>0,
 \qquad W\cap(b_d\bmod d)=\varnothing\quad(d\in D).
 \tag{CC11}
\]

For any CD family and any subfamily \(J\), an intersecting collection
of its classes has pairwise coprime moduli. Such a collection has Haar
intersection probability \(\prod_{d\in I}1/d\) by CRT. Inclusion–
exclusion therefore gives

\[
 H\left(\bigcap_{d\in J}(b_d\bmod d)^c\right)=\Psi(J).
 \tag{CC12}
\]

The same \(W\) avoids every subfamily, so
\(\Psi(J)\ge H(W)>0\) for all \(J\subseteq D\). This proves
strict positivity, including on the full original palette; no boundary
positivity is assumed.

## 4. Transfer to arbitrary residues, and the exact CD criterion

For arbitrary original residues \(a_d\), let \(A_d=a_d\bmod d\).
The gcd graph on \(D\) is a dependency graph under \(H\): an event
modulo \(d\) is independent of the joint sigma-algebra generated by
events whose moduli are coprime to \(d\). Its vertex probabilities
are exactly \(1/d\). All its induced independent-set polynomials at
these probabilities are positive by CC12.

[Scott–Sokal, arXiv:cond-mat/0309352v2, Theorems 2.10 and 4.1(a)](https://arxiv.org/abs/cond-mat/0309352)
therefore gives

\[
 H\left(\bigcap_{d\in D}A_d^c\right)
 \ge\Psi(D)\ge\prod_{p\in P}\frac{M_p}{p^{h_p}}>0.
 \tag{CC13}
\]

This is a comparison theorem for two families on the same original
palette and carrier. It does not identify their unions, intersections,
conditional laws, or individual overlap costs. In particular no cost
computed for the constructed CD residues is charged to the arbitrary
original residues.

If \(K(D)\subseteq D\), CC3 is also necessary for CD realizability.
For a given \(p\), the original labels

\[
 \{p\}\cup\{p^2:\epsilon_p=1\}\cup\{pq:q\in N(p)\}
 \tag{CC14}
\]

have pairwise gcd exactly \(p\). A CD assignment requires their
\(1+\epsilon_p+g_p\) first-\(p\) roots to be distinct, giving CC3.
Combining this with section 2 proves

\[
 K(D)\subseteq D
 \quad\Longrightarrow\quad
 [\ D\text{ admits a CD assignment}\iff\text{CC3}\ ].
 \tag{CC15}
\]

Consequently every actual CD assignment on such a palette is
noncovering. A divisor-closed palette contains \(K(D)\), so this
includes arbitrary finite divisor ideals, not only full divisor sets.
The sufficiency and arbitrary-residue conclusion CC13 do **not** need
\(K(D)\subseteq D\).

## 5. A whole cover forces an original crowded star

By contraposition of CC13, every finite distinct whole cover has

\[
 g_p+\epsilon_p\ge p\quad\text{for some }p\in P.
 \tag{CC16}
\]

Now assume a distinct odd whole cover exists and select the extremal
family of [350, EB1--EB3](../321-384/350-extremal-paired-branch-and-source-support.md):
first minimize its number of classes, then its modulus sum. Its
original palette is divisor-closed; comparable classes are disjoint;
a common CRT translation makes all original prime classes \(0\bmod p\).
By CC16 there are \(p\) distinct original children
\(pq_1,\ldots,pq_p\), where the \(q_i\) are distinct primes and
at most one equals \(p\). All their first-\(p\) roots are nonzero.
Two therefore collide in the \(p-1\) available roots.

Let \(Z\) avoid all original prime classes, and retain the same
\(H\) conditioned on \(Z\). With the actual star cost \(B_p\)
and complete composite mass \(S\) defined in report 382, its
PS6--PS7 give

\[
 S:=\sum_{\substack{d\in D\\d\text{ composite}}}\frac1{\varphi(d)}
 \ge1+B_p
 \ge1+\min_{i<j}\frac1{\varphi(pq_iq_j)}>1.
 \tag{CC17}
\]

The new input to that existing cost formula is that a crowded star
must occur somewhere in this extremal cover. CC17 does not force
\(p=3\), the particular triple \(9,15,21\), or a uniform positive
margin as the primes grow. Costs from different stars cannot be added
without their joint cycle and component accounting. No contradiction
with the unrestricted covering hypothesis has been obtained.

## 6. Exact controls and the scope of the improvement

The standard-library [program](../../frontier/cover-geometry/cd_prime_capacity_controls.py)
and its [exact results](../../frontier/cover-geometry/cd_prime_capacity_controls.json)
retain the small controls as original numerical moduli and residues;
the large palette is specified by its exact generating rule below.
For small canonical families, exhaustive CRT counts agree with CC12:

| Input | Period | Actual survivors | Product-set survivors |
| --- | ---: | ---: | ---: |
| All nonunit divisors of 54 | 54 | 1 | 1 |
| \(\{2,4,8,3,5,15,25,75\}\) | 600 | 32 | 26 |
| All nonunit divisors of 25725 | 25725 | 7043 | 4472 |
| \(\{3,9,5,25,45\}\) | 225 | 90 | 65 |

These exercise prime 2, unequal heights, intersecting cyclic supports,
and absence of divisor closure. Exhausting all 36 residue assignments
on \(\{2,3,6\}\) gives minimum avoidance \(1/6\), agreeing with
\(\Psi(\{2,3,6\})\). These checks verify the finite examples; the
unbounded-height result follows from the preceding proof.

For a separation from the specified scalar tests, let \(P\) be the
first 100 odd primes, from 3 through 547. Starting with no edges,
scan pairs \((p,q)\), \(p<q\), in lexicographic order and insert an
edge while both degrees are below their bounds \(p-2,q-2\).
The resulting graph is connected with 3673 edges. Use the original
palette

\[
 D_* =\{p^a:p\in P,\ 1\le a\le3\}
 \cup\{p^aq^b:pq\text{ an edge},\ 1\le a,b\le3\}.
 \tag{CC18}
\]

It is a divisor ideal with 33357 distinct odd labels satisfying CC3.
Apply CC6--CC7 and translate every residue by \(-1\), so all prime
classes become zero. Each pure square has first root \(p-1\), while
its \(pq\)-children have the different roots \(1,\ldots,g_p\).
Thus every actual child-star cost \(B_p\) is zero.

Writing \(A_p=\sum_{a=1}^3 1/\varphi(p^a)\), exact rational
arithmetic gives

\[
 S_* =\sum_p\left(A_p-\frac1{p-1}\right)
          +\sum_{pq\text{ an edge}}A_pA_q
       >\frac{1002858}{1000000}>1.
 \tag{CC19}
\]

The original prime reciprocal sum already exceeds one. Also
\(\omega(Q/3)=100\), so full-divisor niceness does not apply.
This actual family satisfies the uncorrected reciprocal test and
every scalar test \(S\ge1+B_p\), while CC13 excludes **every**
residue assignment on its palette. The comparison is only with these
specified tests, not all known covering-system methods.

Increasing every height to seven keeps CC3 valid. The palette then
has 180677 labels, exceeding the generalized Tarsi necessary bound
\(1+7\sum_{p\in P}(p-1)=172047\) for a minimal unsatisfiable digit
clause-set. Thus that additional count is also insufficient to imply
coverage; the clause interpretation and its scope are described in
[the Kullmann source note](../../../../../Library/Combinatorics/kullmann2011clausal.md).

Every class in these CD examples has a private point. If \(G_D\) is
the gcd graph on the moduli, then

\[
 H\left(A_d\setminus\bigcup_{e\ne d}A_e\right)
  =\frac1d\Psi(D\setminus N_{G_D}[d])>0.
 \tag{CC20}
\]

CD removes the neighbors, and CRT makes \(A_d\) independent of all
remaining events jointly. Strict positivity follows from CC12. The
examples' exclusion therefore does not depend on redundant classes.

## 7. Why the degree-two hypothesis cannot be dropped from necessity

The literal family

\[
 (d,a_d)=(3,0),(5,0),(7,0),(9,1),(45,11),(63,50)
 \tag{CC21}
\]

is CD. The three multiples of 9 have the different residues
\(1,2,5\bmod9\), and all relevant first-5 and first-7 roots are
nonzero. Nevertheless \(g_3+\epsilon_3=2+1>2\).
Its original palette omits 15 and 21, so it does not contain
\(K(D)\). Higher 3-adic digits separate classes whose first-3
roots coincide. Exactly 110 of its 315 original residues are
uncovered. This refutes extending the necessity in CC15 to arbitrary
nonclosed palettes; it is not a covering counterexample.

The full-divisor specialization of CC15 agrees with the known niceness
criterion discussed in [382, section 4](382-prime-star-overlaps-and-no-prime-excess.md#4-exact-scope-of-the-niceness-literature).
[Adenwalla, arXiv:2501.15170v3](https://arxiv.org/html/2501.15170v3)
provides the first-root packing argument and full-divisor noncoverage;
[Jia--Li--Liu, arXiv:2504.09579v3](https://arxiv.org/html/2504.09579v3)
provides the converse full-divisor realization criterion. Their section 3
already uses an ordered-support cycle of pair-family residue restrictions
(v3, PDF pp. 8--9 and p. 11, equation (13)), with support recovered by
following those restrictions around the cycle. This is a close antecedent
of the cyclic-support separation used here; reversing the cycle's
orientation does not remove that relationship. The present proof uses
the explicit colors and prime-power prefixes in CC5--CC7 and proves the
local-capacity and positive-survivor claims for the prescribed palette;
these are not quoted from their full-divisor theorem. No literature
priority is claimed for the cycle mechanism. Nor does the argument assume
that an arbitrary divisor ideal can be completed to a full-divisor CD
family.
