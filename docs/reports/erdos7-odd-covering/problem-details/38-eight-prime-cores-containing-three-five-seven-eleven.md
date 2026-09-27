[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Eight-prime cores containing 3, 5, 7 and 11

Let a finite family have pairwise distinct odd moduli greater than one.
Suppose its original prime-interaction graph has an actual block with
eight vertices containing \(\{3,5,7,11\}\), and every other block has
at most seven vertices. Then the family does not cover the integers.
More precisely, the Haar proportion of complete core configurations
which avoid every original core class and extend through the whole
connected component is strictly greater than \(1/2200000\).

There is no bound on the number or depth of the attached blocks,
the original prime-power heights, or the residue choices. The four
remaining core primes need not be the next four primes. The density
conclusion counts extendible core configurations, not all full tuples
in the connected component.

This ordinary mathematical consequence extends
[Chapter 35](35-eight-prime-core-with-seven-vertex-attachments.md).
It uses the same original graph decomposition, the attributed
eight-prime density and ordinary source construction, the descendant
domains of
[Chapter 31](31-seven-vertex-block-noncoverage-with-actual-prime-measures.md),
and eleven explicit conditional-kernel comparisons. It is not a new
Lean theorem, a theorem for every eight-vertex block, or a resolution
of unrestricted Erdős #7.

## 1. Original core, original domains, and distinct attachment minima

Root the block-cut tree at the actual eight-vertex core. Use each full
original prime-power coordinate, including the heights required by
attachments. An immediate attached block meets the core in one parent
prime and has at most six real children. Distinct attached subtrees
have disjoint outside prime sets. Every original mixed-modulus support
is a clique and hence is contained in one block; pure classes are
assigned once to their own coordinates.

Every outside prime is at least 13. For an actual child \(q\),
Chapter 31 supplies its domain \(V_q\) of words admitting an avoiding
extension through its descendants, including its original pure classes,
with
\[
 H_q(V_q)\ge d_q:=1-\frac1{q-1}-\frac{2e_q}{q-1},
 \qquad e_q<\frac12.
\]
Its cofactor cylinder cap under the actual conditional domain law is
therefore bounded by
\[
 b_q=\frac1{(q-1)d_q}\le\frac1{q-3}.
 \tag{VE1}
\]
All descendant blocks have at most seven vertices, and prime 3 is
already in the core, so the enlarged non-3 induction of Chapter 31
applies to all these actual domains.

Pad an attachment with fewer than six children using fresh independent
dummy primes greater than every original prime. Their domains are
complete; original labels have exponent zero there. No dummy receives
a descendant fee, and the minimum child remains real. Conditional
avoidance projects back to the original block without changing a
modulus or residue. If the real minimum is \(s\), the sorted augmented
children are coordinatewise at least the first six primes starting
with \(s\).

For a chosen cutoff \(t_s\), put \(\bar b_q=1/(q-3)\) at that
successive-prime tuple. On its coordinate supports define
\[
 v(A)=(t_s+\mathbf1_{|A|\ge2})\bar b_A,
 \qquad \bar b_A=\prod_{q\in A}\bar b_q.
\]
The support polynomial and conditional-load numerator are
\[
 Z_A=Z_{A\setminus\{i\}}-
       \sum_{i\in R\subseteq A}v(R)Z_{A\setminus R},
 \quad Z_\varnothing=1,
 \quad L=\sum_{\varnothing\ne A\subseteq J}\bar b_AZ_{J\setminus A}.
\]
All 64 residuals are strictly positive in each row below. The actual
conditional-kernel argument of
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md)
then gives, with \(Z=Z_J\),
\[
 H_p(B)\le K_{p,s}:=\frac{L}{p^{t_s}(p-1)Z},
 \qquad k_s:=K_{3,s}.
 \tag{VE2}
\]
Here \(B\) is the actual full-parent blocker for that original block.
The dominating caps are used directly in the conditional probability
theorem; no monotonicity of \(L/Z\) is assumed. Comparison prime
labels supply numerical coordinate bounds, not new actual child labels.
If a comparison label equals a core parent, actual children still
remain different primes and the same dominating bound remains valid.

| Real minimum \(s\) | Comparison children | \(t_s\) | Exact \(k_s\) |
|---:|:---|---:|---:|
| 13 | 13,17,19,23,29,31 | 5 | 499487/159722442 |
| 17 | 17,19,23,29,31,37 | 8 | 91694/392262507 |
| 19 | 19,23,29,31,37,41 | 10 | 1635794/97069647267 |
| 23 | 23,29,31,37,41,43 | 13 | 648931/1244346780978 |
| 29 | 29,31,37,41,43,47 | 16 | 3215930/250543409694507 |
| 31 | 31,37,41,43,47,53 | 19 | 1492661/2346501298340970 |
| 37 | 37,41,43,47,53,59 | 23 | 2569231/227364249753299430 |
| 41 | 41,43,47,53,59,61 | 26 | 520592/1032544027454664735 |
| 43 | 43,47,53,59,61,67 | 28 | 9175739/416723308207682751585 |
| 47 | 47,53,59,61,67,71 | 30 | 6503191/5079165741198560042235 |
| 53 | 53,59,61,67,71,73 | 30 | 56140336/76935767377471116605271 |

For the new minimum-13 row in particular,
\[
 \min_A Z_A=Z_J=\frac{985941}{32614400}>0,
 \qquad L=\frac{1498461}{32614400}.
\]
Every cutoff uses the complete original parent word. If a cutoff
exceeds its actual height, the extra shallow levels contain no original
classes; the infinite deep sum only bounds the original finite sum.

There is at most one immediate attachment with each displayed real
minimum. A prime used inside the core cannot be such a minimum;
retaining its nonnegative comparison cost is a safe upper bound.
For minima at least 59, use the existing all-large six-child theorem,
whose threshold is 57. Its root-3 cost is below
\(f(s)=2^{-(s-1)/2}\), and its non-3 cost is below \(c_pf(s)\),
where \(c_5=3/10\), \(c_p=2/(p-1)\) for \(p\ge7\), and
\(c_3=1\) denotes the root fee. Distinct real minima give total
large-minimum root fee at most \(2^{-28}\).

## 2. Three ordinary source families on the actual core

Use the ordinary source construction on the unchanged 3- and 5-anchor
geometry, with its unchanged 7 and 11 stages. The six later-coordinate
thresholds are
\[
 (2,4,4,8,8,12).
\]
At each of the 32 basic anchor vertices of Chapters 30 and 31,
recompute the full multiplier laws with the displayed prime parameters.
The resulting lower masses and joint density caps are:

| Core lower proxies | Minimum ordinary mass \(m\) | Joint cap \(D\) |
|:---|---:|---:|
| 3,5,7,11,13,17,23,29 | 290064917/30000000000 | 165/8 |
| 3,5,7,11,13,19,23,29 | 12314552263/675000000000 | 297/16 |
| 3,5,7,11,17,19,23,29 | 13939935091/337500000000 | 33/2 |

The whole-coordinate marginal caps at those lower proxies are,
respectively,
\[
 \begin{aligned}
 &(1,1,3/2,5/3,3/2,2,11/7,7/4),\\
 &(1,1,3/2,5/3,3/2,9/5,11/7,7/4),\\
 &(1,1,3/2,5/3,4/3,9/5,11/7,7/4).
 \end{aligned}
 \tag{VE3}
\]
For every actual core in the associated range, this means one
unnormalized submeasure \(\mu\), supported outside every original
core class, satisfies
\[
 \mu(X)\ge m,\qquad \mu\le D H_{\mathrm{core}},\qquad
 (\pi_p)_*\mu\le\alpha_pH_p.
 \tag{VE4}
\]
The density bound follows from the restricted anchor Haar measure and
the product of the pointwise conditional kernel caps. It is not inferred
from multiplying marginal caps. Source completion enlarges the covered
set, so its surviving measure also avoids the original core family.

Here is why the prime ranges preserve the source statement. For an
actual later prime \(p\) and fixed threshold \(t\), the kernel uses
\[
 C_p=\frac{p-1}{p-1-t},\qquad \beta_p=p-1-t,
 \qquad \Pr(J_p\ge e)=\frac{C_p}{p^e}\quad(e\ge1).
\]
Increasing \(p\) decreases every displayed tail probability and
increases the positive denominator. Common quantile uniforms order
the complete multiplier product. The exact untruncated ordinary hinge
is increasing in that product, so its actual expectation is bounded
by the proxy expectation. Only after this comparison is the proxy
expectation evaluated by the inherited finite geometry and nonnegative
exact-moment remainder. No monotonicity of differences of truncated
approximations is used.

The source's affine reserve and convex loss interpolate the same
32 anchor vertices for these parameter choices. The arithmetic retains
all multiplier probabilities below 32 and their full first moment;
every required threshold is at most 12. All losses are rounded upward.
This changes only parameters of the actual ordinary kernels. It does
not replace any original modulus or residue by one on proxy primes.

In particular, when 13 is absent, the four primes after 7 and 11 are
coordinatewise at least \((17,19,23,29)\). The third row changes only
those four ordinary stages. The 3/5 normalization, the 7/11 stages,
the source geometry and its associated prime-specific prerequisites
stay unchanged. No missing-11 case or change of the source anchor is
asserted here.

For each attachment cutoff in the table, every source row satisfies
\[
 \alpha_p\frac{K_{p,s}}{k_s}
 =\frac{2\alpha_p}{p-1}\left(\frac3p\right)^{t_s}\le1,
 \qquad \alpha_pc_p\le1.
 \tag{VE5}
\]
These inequalities are checked at the lower proxies. At a later core
coordinate with its own threshold \(t\), the finite ratio is
\(2(3/p)^{t_s}/(p-1-t)\), and the large-minimum coefficient is
\(2/(p-1-t)\); both decrease as that actual prime increases.
The fixed 3- and 5-coordinates have cap one. Thus the same core measure
pays at most \(k_s\) for each small-minimum attachment and at most
\(2^{-28}\) for the entire large-minimum tail.

## 3. Exhaustive core cases and one budget per case

For \(j\in\{13,17,19,23\}\), define
\[
 \Delta_j:=\sum_{j\le s\le53\text{ prime}}k_s+2^{-28}.
 \tag{VE6}
\]
The finite and large-minimum attachments are disjoint classes of actual
blocks. The minima used within either class are distinct. Thus these
are shared deletion bounds, not sums of separately optimized measures.
Exact arithmetic gives
\[
 \Delta_{23}<\frac{27}{50000000},\quad
 \Delta_{19}<\frac7{400000},\quad
 \Delta_{17}<\frac{13}{50000},\quad
 \Delta_{13}<\frac{17}{5000}.
 \tag{VE7}
\]

First suppose 13 and 17 belong to the core. Its two remaining primes
can be written \(u<v\), with \(u\ge19\).

* If \((u,v)=(19,23)\), this is Chapter 35's first-eight core,
  whose extendible core Haar density exceeds \(1/1200000\).
* If \(u=19,v\ge29\), use the attributed eight-prime uncovered
  density to take \(\mu=H|_U\) with mass at least
  \(m_A=1/1002375\). All marginal and joint caps are one, and every
  outside prime is at least 23. Hence
  \[
   H_{\mathrm{core}}(\text{extendible original survivors})
     \ge m_A-\Delta_{23}>\frac1{2200000}.
  \]
* If \(u\ge23\), then \(v\ge29\). Use the first ordinary source
  row, with mass \(m_B=290064917/30000000000\) and joint cap
  \(D_B=165/8\). Every outside prime is at least 19. Therefore
  \[
    \frac{m_B-\Delta_{19}}{D_B}>\frac1{2200000}.
  \]

If 13 belongs to the core but 17 does not, its three other primes are
coordinatewise at least \((19,23,29)\). Use the second ordinary row:
\[
 m_C=\frac{12314552263}{675000000000},\qquad D_C=\frac{297}{16},
 \qquad \frac{m_C-\Delta_{17}}{D_C}>\frac1{2200000}.
\]

Finally suppose 13 does not belong to the core. Its four primes other
than \(3,5,7,11\) are coordinatewise at least \((17,19,23,29)\).
Use the third ordinary row:
\[
 m_D=\frac{13939935091}{337500000000},\qquad D_D=\frac{33}{2}.
\]
Every outside prime is at least 13, and
\[
 \Delta_{13}=k_{13}+\Delta_{17},\qquad
 \frac{m_D-\Delta_{13}}{D_D}>\frac1{2200000}.
 \tag{VE8}
\]
The extra term is the cost of at most one actual attachment whose
minimum is 13. Other attachments have different real minima and are
already accounted for by \(\Delta_{17}\). Numerically,
\(\Delta_{13}\) is approximately \(0.00337836585\), leaving
approximately \(0.0379251455\) of the same weighted source mass
before division by \(D_D\).

These cases exhaust every eight-prime core containing \(3,5,7,11\).
For an ordinary row, first remove the actual attachment blockers from
that same \(\mu\), using (VE5). Its remaining mass is at least
\(m-\Delta_j\). Only then divide by the full joint cap \(D\) in
(VE4) to obtain the Haar proportion of extendible core configurations.
Converting \(m\) to Haar first and subtracting the same weighted
budget would be a different estimate and is not used.

Each remaining core configuration has an avoiding tuple through every
immediate attachment, and those tuples have full extensions through
their actual descendant domains. Disjoint private subtrees allow all
choices to be combined. Other connected components have only blocks
of at most seven vertices and are handled by Chapter 31. The finite
Chinese remainder theorem then gives an integer avoiding all the
original congruence classes.

## 4. Sources, exact arithmetic, and verification boundary

The external source is Michael Schroeder, *Nine Prime Divisors in Odd
Distinct Covering Systems*, v1.0.1,
[DOI 10.5281/zenodo.22759614](https://doi.org/10.5281/zenodo.22759614).
Its Corollary C.2 supplies the eight-prime Haar seed. Sections 3--5
and 8--9 supply the ordinary construction and comparison already
used in Chapters 30, 31 and 36. The source archive SHA-256 is
`9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`.
No new local replay of its whole arbitrary-height Lean theorem is
claimed.

The portable producer
[`variable_eight_core_certificate.py`](../frontier/cover-geometry/variable_eight_core_certificate.py)
accepts `--geometry`, `--helper`, `--source-helper`, and `--output`.
It checks the input SHA-256 identities before importing either project
helper and rejects execution with assertions disabled. The ordinary
source helper is the existing Chapter 36 producer; its reusable
arithmetic functions do not invoke that producer's main routine.

The calculation verifies eleven fixed-cutoff rows and all 704 residuals,
three source families at all 32 vertices, 576 upward-rounded stage
losses, the applicable parent-cap comparisons, four distinct-minimum
budgets, and the uniform strict Haar bound. Its
[`JSON`](../frontier/cover-geometry/variable_eight_core_certificate.json)
contains the exact values and input identities. The Chapter 35 baseline
is an inherited result, not a new replay within this calculation.

The geometry comprises the same pinned 72 batches and 51,840 integer
queries. No new geometry, source verifier import, broad enumeration of
eight-vertex blocks, or Lean checker is involved. The full-law prime
comparison, vertex interpolation, actual conditional kernels,
whole-coordinate source caps, and original block-tree recursion remain
the mathematical premises stated above. The fixed case split and
all-large attachment theorem supply the infinite prime ranges; a finite
sample alone is not used to assert them.
