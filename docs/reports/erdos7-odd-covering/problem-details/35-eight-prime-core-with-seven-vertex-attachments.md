[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="eight-prime-core-with-seven-vertex-attachments"></a>
# The first eight odd primes support every seven-vertex attachment

Let a finite family have pairwise distinct odd moduli greater than one.
Form its original prime-interaction graph. Suppose one actual block has
vertex set
\[
 S=\{3,5,7,11,13,17,19,23\},
\]
and every other block has at most seven vertices. Then the family does
not cover the integers. There is no bound on the number or depth of
the other blocks, the total number of primes, the original residue
choices, or their finite prime-power heights.

More precisely, the Haar proportion of core configurations that avoid
all original core classes and admit an avoiding extension through their
entire connected component is greater than \(1/1200000\).
This is a bound on extendible **core configurations**, not the volume of
all avoiding tuples in the whole connected component.

The proof combines the eight-prime uncovered-density theorem already
used in [Chapter 33](33-seven-small-primes-with-an-unrestricted-large-prime-tail.md),
the descendant domains of
[Chapter 31](31-seven-vertex-block-noncoverage-with-actual-prime-measures.md),
and one exact conditional-kernel comparison. It uses ordinary mathematics
and exact rational computation; it is not a new Lean-certified theorem.
It does not establish all eight-vertex blocks or unrestricted Erdős #7.

## 1. One core measure and the original attached subtrees

Use the full original coordinates
\(X_p=\mathbb Z/p^{h_p}\mathbb Z\), where \(h_p\) resolves every
original class involving \(p\), including classes outside the core.
Let \(U\subseteq X_S=\prod_{p\in S}X_p\) avoid all original classes
supported entirely on \(S\), including their pure prime-power classes.
The pinned Schroeder *Nine Prime Divisors in Odd Distinct Coverings*
v1.0.1, Corollary C.2, gives
\[
 H_S(U)\ge\frac1{1002375}.
 \tag{EC1}
\]
This applies to every finite distinct family on these eight primes,
without a covering assumption. If a core coordinate has extra height
because of attached classes, lifting the core family to that height
preserves its uncovered proportion.

Take the unnormalized positive measure
\[
 \mu=H_S|_U.
 \tag{EC2}
\]
Then \(\mu\le H_S\), and every complete-coordinate marginal obeys
\((\pi_p)_*\mu\le H_p\). All subsequent deletion estimates refer to
this same measure; survivors are never renormalized. No source residues
or internal source kernels are used to modify an original attachment.

Root the block-cut tree at the actual core block. Every immediate
attachment meets the core in exactly one parent prime \(p\). Its other
vertices and its private descendant subtree contain no other core prime.
Distinct immediate attached subtrees have disjoint outside prime sets.
Every original modulus support is a clique in the original graph, hence
belongs to a single block when it has at least two vertices. Pure classes
are charged once at their own coordinates. Thus the decomposition retains
all original supports, residue choices, and heights.

## 2. Actual child domains and their common bound

Every prime outside \(S\) is at least 29. For every real child prime
\(q\) of an immediate attached block,
Chapter 31 gives the actual set \(V_q\) of words admitting an avoiding
extension through its descendant subtree, including its original pure
prime-power classes. With \(D_q\) its actual strict descendant prime set,
the established fees give
\[
 e_q=\sum_{r\in D_q}f(r)<\frac12.
 \tag{EC3}
\]
The actual domain satisfies
\[
 H_q(V_q)\ge d_q:=1-\frac1{q-1}-\frac{2e_q}{q-1}.
 \tag{EC4}
\]
The existing induction applies because those descendant blocks have at
most seven vertices and contain no prime 3. Its non-3 orientations are
part of the Chapter 31 theorem.

For the actual product law
\(\nu=\bigotimes_qH_q(\cdot\mid V_q)\), the complete cofactor
cylinder bounds are therefore
\[
 b_q=\frac1{(q-1)d_q}=\frac1{q-2-2e_q}\le\frac1{q-3}.
 \tag{EC5}
\]
These are bounds for domains belonging to the same original family;
no independent copies of a descendant budget are allocated.

## 3. One conditional-kernel comparison

An immediate attachment has at most six real children. If it has fewer,
adjoin independent dummy coordinates at unused primes larger than every
prime of the whole original family. Their domains are complete, and no
original event involves them. An avoiding augmented tuple projects to
an avoiding actual tuple. No dummy coordinate receives a descendant
expense or a fee, and the minimum child remains a real prime.

After sorting the six augmented children, they are coordinatewise at
least
\[
 (29,31,37,41,43,47).
\]
The six numbers
\[
 \bar b_q=\frac1{q-3}
 \quad(q=29,31,37,41,43,47)
 \tag{EC6}
\]
thus dominate the actual cylinder bounds. Section 2 of
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md)
allows these dominating bounds directly; no monotonicity assertion about
a quotient of avoidance polynomials is needed.

Use the conditional-kernel construction (CK6)--(CK12) at cutoff
\(t=17\). For a nonempty coordinate support \(A\), set
\(\bar b_A=\prod_{q\in A}\bar b_q\) and
\[
 v_t(A)=
 \begin{cases}
 t\bar b_A,&|A|=1,\\
 (t+1)\bar b_A,&|A|\ge2.
 \end{cases}
\]
Write \(Z_A\) for the alternating sum over pairwise-disjoint support
families in \(A\), including the empty family. All 64 coordinate residuals
are strictly positive; exact calculation gives
\[
 \min_A Z_A
 =\frac{756297}{1655413760}>0.
 \tag{EC7}
\]
Writing \(J=\{1,\ldots,6\}\), \(Z=Z_J\), and
\(L=\sum_{A\ne\varnothing}\bar b_AZ_{J\setminus A}\), the same
calculation gives
\[
 L=\frac{3825189}{1655413760}.
\]
For the actual full-parent blocker \(B\), meaning the words with no
avoiding child tuple in \(\prod_qV_q\), (CK12) yields
\[
 H_p(B)\le K_p:=\frac{L}{p^{17}(p-1)Z},
\]
and in particular
\[
 K_3=
 \frac{425021}{21704070634758}
 <\frac1{50000000}.
 \tag{EC8}
\]
The cutoff places no restriction on original heights: shallow levels
beyond the actual parent height have empty event families, and the deep
infinite sum only bounds the actual finite sum. The kernel conditions on
the actual shallow survivors at each complete parent word. It does not
replace this law by a fixed independent child marginal.

For every core parent,
\[
 \frac{K_p}{K_3}=\frac2{p-1}\left(\frac3p\right)^{17}\le1.
 \tag{EC9}
\]
Since \((\pi_p)_*\mu\le H_p\), deleting the cylinder of this blocker
from the same core measure costs at most \(K_3\).

## 4. Summing the actual attachments

Call an immediate attachment small when its real child set meets
\[
 T=\{29,31,37,41,43,47,53\}.
\]
Distinct attachment blocks have disjoint real child sets. Thus there
are at most seven small attachments, and their total deletion from
\(\mu\) is at most \(7K_3\).

Every remaining attachment has minimum real child prime \(s\ge59\).
The all-large theorem of Chapter 23 applies after the same harmless
padding to six children, since
\[
 s\ge59>6(6+3)+3=57.
\]
With the established \(f(s)=2^{-(s-1)/2}\) for \(s\ge29\), it gives
a blocker charge below \(f(s)\) at parent 3 and below
\(c_pf(s)\) otherwise, where \(c_5=3/10\) and
\(c_p=2/(p-1)\) for \(p\ge7\). Every coefficient is at most one.
The real minima are distinct across these blocks, so the total large
attachment charge is bounded by
\[
 \sum_{s\ge59\text{ prime}}f(s)
 \le\sum_{n\ge29}2^{-n}=2^{-28}.
 \tag{EC10}
\]
This permits arbitrarily many attachments; no fixed bound on their
number is assumed.

One union bound in the same core measure bounds the actual deletion by
\[
 \Delta:=7K_3+2^{-28}
 =\frac{410169506123395}{2913071048948736589824}
 <\frac1{7000000}.
 \tag{EC11}
\]
By (EC1)--(EC2), the remaining core configurations have Haar measure at
least \(1/1002375-\Delta\), and exact arithmetic gives
\[
 \frac1{1002375}-\Delta
 =\frac{3431999163577912931}{4005472692304512811008000}
 >\frac1{1200000}>0.
 \tag{EC12}
\]
Choose one such core configuration. Every immediate attachment admits
an avoiding tuple of its actual child domains; each chosen child word
in turn has a full avoiding extension. The private subtrees are
disjoint, so these finitely many choices combine. Other connected
components have only blocks of at most seven vertices and admit avoiding
tuples by Chapter 31. Finally the Chinese remainder theorem realizes
the combined full tuple by an integer outside every original class.

The density in (EC12) counts extendible core configurations. A lower
density for all full extensions needs lower measures for the private
fibres, such as the separate construction in
[Chapter 34](34-uniform-head-density-from-thick-block-domains.md).

## 5. Source premise and reproducible arithmetic

The external input in (EC1) is Corollary C.2 of
[Schroeder, v1.0.1](https://doi.org/10.5281/zenodo.22759614),
archive SHA-256
`9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`.
It is an attributed source theorem, already used by Chapter 33;
no new full replay of its Lean formalization is claimed here.

The program
[`eight_prime_core_attachment_certificate.py`](../frontier/cover-geometry/eight_prime_core_attachment_certificate.py)
uses exact rational arithmetic and the recurrence
\[
 Z_A=Z_{A\setminus\{i\}}
      -\sum_{\substack{R\subseteq A\\i\in R}}v_t(R)Z_{A\setminus R},
 \qquad i\in A,
\]
which distinguishes whether the least vertex is unused or belongs to
one unique selected support. It checks all 64 residuals, the eight
parent comparisons, and the shared budget, and writes
[`eight_prime_core_attachment_certificate.json`](../frontier/cover-geometry/eight_prime_core_attachment_certificate.json).
This requires one six-child dominating tuple; it does not enumerate
all seven-child blocks or generate new source geometry.
