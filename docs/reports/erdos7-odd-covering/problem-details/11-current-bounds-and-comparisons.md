[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md) · [Next](12-coupling-the-shared-zero-exponent-layout.md)

# Current bounds and comparisons

For every \(H\ge3\), one has \(1/27\le A<1/18\), and the uniform
vertex bound is
\[
 \lambda\ge L(A):=\frac{25-102A}{40-72A}.             \tag{CM11}
\]
This is an interval certificate, not sampling of heights. For each of
1296 vertex choices and each of the two target roots and five target
cells, replace \(N_1,N_2\) by those target masses and form
\[
 P(A)=(40-72A)(s-T/6)-(25-102A)xz.
\]
The vertex deficits are either zero or \(9A\) in one coordinate, and
the late deletion is either zero or \(A/5\) in one coordinate. Thus
\(P\) has degree at most two. Write \(a=1/27\), \(b=1/18\) and
\(v=(A-a)/(b-a)\). Its Bernstein representation is
\[
 P(A)=P(a)(1-v)^2+
 2\left(P(a)+\tfrac12(b-a)P'(a)\right)v(1-v)+P(b)v^2.
\]
All three coefficients are nonnegative for every one of the 12960
branches; there are 656 distinct polynomials. Exact rational coefficient
verification therefore proves (CM11) over the whole interval, including
all finite heights. Taking the worst target root and cell recovers both
maxima in (CM10).

If the pure modulus-3 class is absent, use \(x\ge8/9-A\); if the
modulus-9 class is absent or ineffective, use \(x\ge2/3-A\).
The unsplit bound is
\[
 \lambda\ge
 \frac{xz-u/5-(zu+x/5+u/5)/6}{xz}.
\]
It increases with \(x,z\). At their respective lower endpoints,
subtracting \(L(A)\) and multiplying by the positive denominators
gives \(80/27+(148/15)A\) and \(16/27+4A\), respectively.
Both are positive. At \(H=2\), the two unsplit bounds are
\(35/48\) and \(47/72\), both above \(37/60\).
These cases also cover divisor families with smaller physical heights.

Multiplying (CM11) by the pure-density lower bound
\((5/9-A)(4/5)(6/7)\) gives ambient uncovered density at least
\[
 \frac5{21}-\frac{34}{35}A
 =\frac{58+17\cdot3^{-(H-2)}}{315}.
\]
The actual construction (CM3)--(CM7), with \(K=L=1\), attains this
quantity for every \(H\ge3\), proving (CM9). Its densities decrease
to \(58/315\), the exact infimum with arbitrary ternary height and
squarefree 5 and 7.

At 315, the lower pure density is \((5/9)(4/5)(6/7)=8/21\), so
\(\lambda\ge37/60\) leaves at least 74 residues. Equality is attained
by the following explicit \((\text{modulus},\text{residue})\) list:
\[
 (3,0),(9,4),(5,0),(15,11),(45,37),(7,0),
 (21,8),(63,16),(35,3),(105,53),(315,313).
\]
The first five classes leave cell masses \((3,4,3,3,3)/45\) in the
order \((1,7,2,5,8)\pmod9\). Maximizing old cylinders have
\((d,a)=(3,2),(9,7),(5,3),(15,8),(45,43)\); extending them with
distinct septenary residues 1 through 5 makes their deletions disjoint
and avoids the pure septenary class. Their total old cylinder mass is
\(22/45\), so the final survivor count is
\(315[(16/45)(6/7)-(22/45)/7]=74\).

The existing verifier records the vertex and interval certificate and
these attaining constructions under **finite_head_sharp_density**.
This is an ordinary universal proof with an exact polynomial certificate;
the endpoint density statement is not yet an end-to-end Lean theorem.

**Simultaneous sharpness of the mixed mass and the unmarked comparison law.**
The sharp head families also rule out a uniform limiting tradeoff between
mixed-head mass and the unmarked load distribution. In the actual
(CM3)--(CM7) construction, choose the test residue for every divisor by
coherent CRT centres \((5,2,2)\). These test residues are independent of
the forbidden residues assigned to the original moduli. Their three
first-level roots are \((2,2,2)\). All pure ternary forbidden cylinders
lie in roots 0 or 1, all pure quinary cylinders in roots 0 or 4, and all
pure septenary cylinders in roots 0 or 6. Every chosen test cylinder
therefore lies entirely inside its coordinate's pure survivor set.

If \(x_p\) is that pure survivor density and \(N_p\) counts the nested
test cylinders containing the coordinate, then
\[
 P_0(N_p\ge a)=\frac{p^{-a}}{x_p}\quad(1\le a\le h_p),
 \qquad L=\prod_{p=3,5,7}(1+N_p).                    \tag{CM12}
\]
The three counts are independent under the actual law \(P_0\). Thus
this complete test load has exactly the finite canonical auxiliary
product law from (PH2), including the terminal atoms. In particular,
\[
 \mathbb E_{P_0}L=\prod_p x_p^{-1},\qquad
 \mathbb E_{P_0}L^2=\prod_p\left(1+x_p^{-1}
                      \sum_{a=1}^{h_p}(2a+1)p^{-a}\right).
\]
As all three heights increase, these laws increase stochastically to the
infinite comparison law, while the same families satisfy
\[
 P_0(B_{\rm mixed})\longrightarrow82/135,\qquad
 \mathbb E_{P_0}L\longrightarrow16/5,\qquad
 \mathbb E_{P_0}L^2\longrightarrow325/18.
\]
Monotone convergence gives the same simultaneous sharpness for every
nonnegative increasing convex cost with finite comparison expectation,
including every fixed positive-part threshold. Consequently, approaching
the maximal mixed mass does not force a positive uniform deficit in this
unmarked comparison. This statement leaves open estimates involving the
actual mixed-head survivor indicator, such as
\(\mathbb E_{P_0}[\mathbf1_S(L-t)_+]\), and alternative supported laws.
The verifier's **sharp_head_unmarked_comparison** entry checks the exact
coordinate and product laws for the eight existing actual CRT families.

**Finite reduction retaining the survivor geometry.** A candidate bound
for the actual uniform survivor law can be reduced to a finite head
optimization with explicit high-height error. Fix truncation heights
\(h_p\), let \(Q=\prod_{p=3,5,7}p^{h_p}\), and let \(S_h\) be the
residues avoiding all original classes whose moduli divide \(Q\). Set
\[
 R_h=\frac{35}{16}-\prod_p\sum_{a=0}^{h_p}p^{-a},\quad
 K_h=\prod_p\sum_{a=0}^{h_p}(2a+1)p^{-a},\quad
 \Delta_h=\frac{35}{4}-K_h,\qquad
 d_h=\max\left\{\frac{53}{432},\frac{|S_h|}{Q}-R_h\right\}.
\]
For any extension to arbitrary finite heights, its full survivor set
\(S\) has ambient density at least \(d_h>0\): the omitted original
classes have total density at most \(R_h\), and (CM8) gives the other
lower bound. Split a complete test load as \(L=L_h+L_{>h}\), according
to whether its divisor divides \(Q\). Its omitted ambient mean is at
most \(R_h\). Expanding ordered divisor pairs gives
\(\mathbb E(L^2-L_h^2)\le\Delta_h\): a compatible pair has probability
\(1/\operatorname{lcm}(d,e)\), and the number of exponent pairs with
maximum \(a\) is \(2a+1\). Incompatible pairs only lower that sum.
For every real threshold \(t\), it follows that
\[
 \begin{aligned}
 \mathbb E_{\mathrm{Unif}(S)}(L-t)_+
 &\le\frac{\mathbb E_{\mathrm{Unif}(Q)}
                   [\mathbf1_{S_h}(L_h-t)_+]+R_h}{d_h},\\
 \mathbb E_{\mathrm{Unif}(S)}L^2
 &\le\frac{\mathbb E_{\mathrm{Unif}(Q)}
                   [\mathbf1_{S_h}L_h^2]+\Delta_h}{d_h}.
 \end{aligned}                                      \tag{CM13}
\]
Here \(S\subseteq S_h\), and
\((a+b-t)_+\le(a-t)_++b\) for \(b\ge0\). Maximizing the numerators
over the finitely many low-head forbidden assignments and test layouts
therefore gives universal profiles usable in (AP1)--(AP6). This reduction
retains actual shared-cylinder exclusions. It does not assert that the
resulting finite optimization already reaches prime 17 or 11.

**Finite supported laws retaining actual exclusions.** The
[finite head geometry result](../finite_head_geometry.md) solves the
complete independent-layout minimax problem for all original families
whose moduli divide 45:
\[
 \sup_F\inf_{\mu\text{ supported on }S_F}
       \max_{(b_d)}\mathbb E_\mu
       \left(\sum_{d\mid45}\mathbf1_{b_d\bmod d}\right)^2
       =\frac{22570}{3361}.                         \tag{CM14}
\]
Completion and symmetry reduce the problem to six actual survivor shapes.
Exact primal and dual probabilities check all 27720 independent test
layouts. Extending the same selected law by a uniform pure-7 coordinate
and conditioning once gives, for every original family with moduli
dividing 315, a supported law with
\(\Gamma\le198583/15619<12.715\). This latter upper bound is not
asserted sharp. For this same chosen law, its full convex profile is
also bounded by the explicit finite comparison law in that note, with
mean at most \(110151471/33504305\). The separate second-moment bound
remains \(198583/15619\); the comparison distribution's larger second
moment need not replace it. The reduction permits shrinking the support because the
conclusion is existence of a law; it does not assert monotonicity of
uniform survivor averages. Both statements are ordinary proofs with exact
certificates, and do not enlarge the prime-13 noncoverage range.

A second [supported-law construction](../marked_head_profile.md)
controls the entire convex profile on the 315 head. One common law,
uniform on a possibly smaller actual survivor set, satisfies
\[
 \mathbb E_\mu h(L)\le\mathbb E h(W),\qquad
 \Pr(W=2,3,4,5,6,8,12)
 =\left(\frac37,\frac{15}{77},\frac{18}{77},
          \frac{15}{2849},\frac{79}{814},\frac1{37},\frac1{74}\right)
                                                        \tag{CM15}
\]
for every complete test layout and nonnegative increasing convex cost.
Here \(\mathbb EW=37/11\) and \(\mathbb EW^2=41336/2849\).
Its high-threshold profile is attained by an actual 74-survivor family
for every real threshold at least six. The mean/profile in (CM15) and
the smaller moment in (CM14) belong to different selected laws and may
not be combined as one law. An elementary refinement replaces the nearby
integer atoms by an atom at \(117/22\), preserving the mean and lowering
the comparison second moment to \(909287/62678\). The same note proves,
for every probability law \(\nu\) on the full period,
\[
 \Theta_\nu(t)=(12-t)\|\nu\|_\infty
        \qquad(8\le t\le12).
\]
Thus the exact universal minimax over all supported laws is
\((12-t)/74\) on this interval. The uniform law is the unique minimizer
on each fixed survivor set when \(t<12\); nonuniform laws must improve
other parts of the profile to help. A separate actual 75-survivor family
shows that fixing the old marginal to be uniform can force second moment
\(1427/80\) and upper profile \((12-t)/16\). These statements still do
not close the tail from 11.

Retaining each original mixed-7 deletion in both numerator and denominator
strengthens (CM15) on the **same** uniform pruned-survivor law:
\[
 \Theta_\mu(0),\ldots,\Theta_\mu(5)
 \le\left(\frac{271}{86},\frac{185}{86},\frac{100}{81},
          \frac{61}{81},\frac{16}{39},\frac7{26}\right),
 \qquad \mathbb E_\mu L^2\le\frac{1131}{86}.             \tag{CM16}
\]
The established high-profile values at thresholds 6, 8 and 12 complete
one convex comparator with atoms
\[
\begin{array}{c|rrrrrrrr}
x&1&2&3&4&5&6&8&12\\\hline
\Pr(X=x)&581/6966&3031/6966&146/1053&425/2106&10/1443&45/481&1/37&1/74.
\end{array}
\]
Its mean is \(271/86\) and its second moment is
\(45292361/3350646\); the smaller actual second-moment bound
\(1131/86\) is independently valid under the same law.
The numerator bound keeps the deletion multiplicity of each old cylinder,
rather than replacing the actual survivor count by its minimum alone.
The note proves the universal reduction. The standard-library verifier
checks 194040 exact cap inequalities over all 27720 old layouts, with
no layout-pair optimization needed for this refinement. Retaining signed deletion unions gives the sharper square bound above:
4754 first-shape layouts pass a positive-cap screen and six require an
exact five-label partition calculation; the other shapes have smaller bounds.
An explicit 86-survivor family simultaneously attains mean 271/86 and
second moment 1131/86. Thus both are sharp for this prescribed uniform
law, without a minimax claim over all supported laws. Conditioning globally
after one 11-height also gives a supported 3465 law with mean at most
4816/1215, actual second moment at most 14518/675 and the full comparator
in the note.
This improves supported-head control but does not extend the established
prime-13 noncoverage range.

The same [supported-law note](../marked_head_profile.md)
also gives a general two-prime construction for an `m` by `n` survivor
grid with matching holes, where `m,n>=3` and the hole count is below
`min(m,n)`. Its explicit common quadratic coefficients work even when
the row sets, column sets and hole locations vary with the old residue;
the constructed law preserves the old marginal. A variable hole count
gives an additional mean-count subtraction, bounded using the original
cross-modulus cofactor labels. Fixed row, column and point-deletion
budgets also reduce arbitrary hole patterns to the one-hole case by
discarding a controlled number of rows and columns. These are ordinary
symbolic proofs for two new prime coordinates of height one and arbitrary
old heights. They do not provide the missing universal weighted estimate
for arbitrary new-prime heights or a new tail cutoff.

**Coupled densities of the three prime-pair subsystems.** Let \(\sigma_A\)
be the ambient density avoiding the original classes supported on \(A\),
and put \(z_p=\sigma_{\{p\}}\). These are subsets of the same fixed family.
Define

\[
 \theta_{ij}=\frac{\sigma_{\{i,j\}}}{z_i z_j},\qquad
 \lambda=\frac{\sigma_{\{3,5,7\}}}{z_3z_5z_7},\qquad
 r_p=\frac1{(p-1)z_p}\le\frac1{p-2},\qquad
 t=\lambda^{-1},\quad v_{ij}=\theta_{ij}/\lambda.
\]

The preceding recurrence proves positivity. The pair mixed-class union
bound gives \(\theta_{35}\ge1-r_3r_5\ge2/3\).
Adding prime 7 to the same uniform pair-survivor law, using
\(R_{35}\le15/7\), gives
\(\lambda\ge\theta_{35}(1-R_{35}r_7)\ge(4/7)\theta_{35}\).
Consequently

\[
 \tfrac23t-v_{35}\le0,\qquad \tfrac47v_{35}\le1.
\]

Inside the product of pure survivors, the forbidden pair-support union
has density at most
\(\sum_{\{i,j,p\}=\{3,5,7\}}(z_i z_j-\sigma_{\{i,j\}})z_p\),
where each unordered pair is counted once. The classes containing all
three primes have total ambient density at most
\(\prod_p1/(p-1)\). Hence

\[
 \lambda\ge\theta_{35}+\theta_{37}+\theta_{57}-2-r_3r_5r_7
 \ge\theta_{35}+\theta_{37}+\theta_{57}-\tfrac{31}{15},
\]
\[
 v_{35}+v_{37}+v_{57}-\tfrac{31}{15}t\le1.
\]

This uses the actual pair densities and a union bound; it does not assert
independence of the three forbidden pair-support unions. Multiply the
three displayed linear inequalities, in their order, by
\(31/30,\ 49/40,\ 1/3\). The \(t\) and \(v_{35}\) coefficients cancel,
and the nonnegative rational combination gives

\[
 \frac{v_{37}+v_{57}}3\le\frac{49}{40}+\frac13=\frac{187}{120}.
 \tag{P13}
\]

For any cylinder supported on \(T\), survival still requires avoidance
of all outside-only classes. Ambient product independence therefore gives

\[
 \mu_S(a\bmod d_T)\le\frac{\sigma_{S\setminus T}}{\sigma_Sd_T}.
\]

Applying this to pure ternary and quinary cylinders, using
\(z_3\ge1/2,z_5\ge3/4\), yields

\[
 \sum_{e\ge2}\max_a\mu_S(a\bmod3^e)\le v_{57}/3,\qquad
 \sum_{e\ge1}\max_a\mu_S(a\bmod5^e)\le v_{37}/3.
\]

These are disjoint groups of exponent vectors for the same law.
The profile obtained from the nine-cell pair bounds has
\(R_{\mathrm{envelope},357}=1663/360\),
\(c(\{3\})=21/4\), and \(c(\{5\})=26/9\).
On the two groups above its ordinary coefficients are below every
projection cap, and its exact contributions are respectively
\((21/4)\sum_{e\ge2}3^{-e}=7/8\) and
\((26/9)\sum_{e\ge1}5^{-e}=13/18\).
Keep the envelope on all other exponent vectors and replace these two
groups by (P13). This proves

\[
 R_{\mu_{\{3,5,7\}}}\le
 \frac{1663}{360}-\frac78-\frac{13}{18}+\frac{187}{120}
 =\frac{1649}{360}.
\]

Using this whole-sum bound in the next deletion step preserves every
individual cylinder inequality. Exact propagation to four primes gives

\[
 R_{\mu_{\{3,5,7,11\}}}\le\frac{5275731}{574351},\qquad
 \Gamma(\mu_{\{3,5,7,11\}})\le
 K_{\mathrm{envelope},35711}
 =\frac{187719326}{1723053}<108.945765.
 \tag{P14}
\]

This is the intermediate profile bound used by the actual-layout block
argument below, which proves (B6), and the shared-density improvement (P2). The
[independent density verifier](../elementary-checks/verify_joint_density_certificate.py)
and its
[fixed sparse rational certificate](../certificates/joint_density_certificate.json)
check all 3888 nine-cell parameter vertices, the missing-class branches,
the three-prime profile and exact infinite sums, the three nonnegative
weights and zero residual in (P13), the four-prime recurrence, and a
two-step continuation at 71 and 73 from this intermediate bound. They use Python 3.9+ standard-library
arithmetic with no solver or residue-family enumeration. The mathematical
arguments establish the meaning and universality of the checked
inequalities; these arithmetic checks do not claim Lean certification.

**Conclusion of (P1).** Apply (P2), proved by the shared-cofactor density refinement below, to
all classes involving only `{3,5,7,11}`. For any missing small prime use an
unused coordinate; this adds no forbidden class. Start (T6) with `G=C_4`
and `s=1`. Take the three steps `p=67,71,73`, with respective thresholds
`δ=1/4,53/200,27/100`. Their exact survivor-fraction lower bounds are

\[
 \frac{150994879}{155933910},\qquad
 \frac{55931291964461}{57643654012161},\qquad
 \frac{138545600701541742901}{142871787094690609776},
\]

all strictly positive. The corresponding ratios are

\[
 F_{67}=\frac{17123620477}{150994879},\qquad
 F_{71}=\frac{6921898229038187}{55931291964461},\qquad
 F_{73}=\frac{18699964911029778700842}{138545600701541742901}
 <\frac{138877}{1000}.
 \tag{P8}
\]

Any absent bridge prime may also be an unused coordinate. Continue at
prime 79, with absolute prime index 22, using the checked upper seed
`F_21=138877/1000`. No prime from 13 through 61 needs to be inserted into
the head: the index specifies where the tail starts, while (T1) allows any
coprime head. The exact continuation and BBMST's analytic termination leave
positive mass on complete survivors. CRT and periodicity supply an integer
avoiding every original congruence.

**Literature boundary.** The searched project has the two-prime density
theorem but no joint-load or cylinder-profile head theorem. The searched pinned
Mathlib congruence, probability and combinatorics files provide counting,
finite sums and Cauchy–Schwarz, with no exact profile result identified.
Hough–Nielsen's necessary factor 2 or 3, BBMST's odd-cover restriction involving
9 or both 3 and 5, BBMST's squarefreeness at primes at most 73, and the
density theorem for LCM `2^a3^b5^c` in [arXiv:2605.18644, Theorem 1.9](https://arxiv.org/abs/2605.18644)
do not directly cover (P1). The separately verified three-factors-per-modulus
theorem also has a different hypothesis: (P1) permits moduli divisible by four
or more primes. No dominating theorem was identified in this searched scope;
this is not a claim of literature priority. The theorem and its proof have
not been formalized in Lean.

<a id="an-actual-layout-improvement-from-incompatible-ternary-roots"></a>
### An actual-layout improvement from incompatible ternary roots

For any finite `{3,q}` family as above, the uniform complete-survivor law
satisfies the stronger bounds on the **actual joint-layout maximum**

\[
 \Gamma_{35}\le57/4,\qquad \Gamma_{37}\le123/13,\qquad
 \Gamma_{3,11}\le181/25.
 \tag{G1}
\]

In particular `57/4<59/4`. These bounds retain incompatible choices within
one test layout. They do not lower `R` or the sum of separate cylinder maxima
and are not substituted for either quantity in the profile recurrence.

Suppose first that the actual modulus-3 class is present, leaving two
possible survivor roots `A,B`. Use the same actual densities from the
two-root budget: `n=w(z−α)/3−t_1`, `m=v(z−β)/3−t_2`, `s=n+m`, and
`d_A=z−α,d_B=z−β`. Every depth-`k` ternary cylinder within root `A` has
raw complete-survivor density at most `d_A/3^k`, and likewise for `B`.
Thus the first-level mixed exclusions constrain the correct root even
when bounding higher-depth test classes.

Consider the pure ternary part `1,3,…,3^H` of a complete test layout.
If its modulus-3 test class chooses `A`, its diagonal and its two ordered
intersections with the constant class contribute exactly `3n` before
normalization. At a later depth `k≥2`, let `a,b` count earlier positive
test depths assigned to `A,B`. A class in `A` contributes at most
`(3+2a)d_A/3^k`: its pairs with the other root have zero mass, while
each earlier class in the same root contributes at most twice its own
mass. The corresponding bound in `B` is `(3+2b)d_B/3^k`.

The remaining scaled cost of every finite itinerary is bounded by

\[
 V(a,b)=3\max\{d_A(a+2),d_B(b+2)\}.
 \tag{G2}
\]

Induct on the number of remaining choices. A choice of `A` contributes
`(3+2a)d_A+V(a+1,b)/3`. If the latter maximum chooses `A`, this is
exactly `3d_A(a+2)`. Otherwise it is at most
`2d_A(a+2)+d_B(b+2)≤V(a,b)`. The other choice is symmetric, and the
empty tail has cost zero. Selecting the actual forbidden root contributes
zero and discounts the continuation by `1/3`, also preserving the bound.

For two active choices, this finite-itinerary induction is proved in
[TernaryRootLoadTail.root_load_tail_le](../../../../D5/S3/Arith/Congruence/TernaryRootLoadTail.lean).
The theorem allows arbitrary nonnegative real weights, arbitrary natural
initial counts and any finite Boolean list. Its proof uses only the permitted
`propext`, `Classical.choice` and `Quot.sound` axioms. It is a checked Lean
component. The actual event-to-itinerary inequality is additionally proved in
[TwoRootEventMoment.two_root_event_moment_le](../../../../D5/S3/Arith/Congruence/TwoRootEventMoment.lean).
For any finite weighted space split into two roots, initial load bounded by
`1+a` and `1+b`, and event list with successive root caps
`d_A,d_B`, `(d_A/3,d_B/3)`, and so on, it bounds the actual integrated
square increment by `3 max(d_A(a+2),d_B(b+2))`. Repeated list entries
count repeatedly; neither nesting nor probability normalization is assumed.
Empty events account for zero-mass choices. The proof advances the actual
load and root counts together before applying the itinerary theorem; its
axiom closure is also exactly the permitted three axioms. The congruence
cylinder caps, arithmetic embedding, normalization and remaining parts of
(G1) are not thereby formalized.

The root-switching estimate now extends to any root type and any discount
\(0\le r<1\). The Lean theorem
[ArbitraryRootEventMoment.arbitrary_root_event_moment_le](../../../../D5/S3/Arith/Congruence/ArbitraryRootEventMoment.lean)
allows arbitrary nonnegative weights on a finite carrier, an arbitrary root
map, an initial load at most \(1+a_i\) on root \(i\), and actual events
whose root-specific caps are multiplied by \(r\) after every event. Any
nonnegative common budget

\[
 M\ge d_i\left(\frac{2a_i+3}{1-r}+\frac{2r}{(1-r)^2}\right)
 \quad\text{for every root }i                           \tag{AR1}
\]

bounds the integrated square increment of every finite event list. The
proof updates the actual load and root counts directly. An event in root
\(i\) costs at most \(c=(2a_i+3)d_i\); its updated constant-root cost is
its old cost minus \(c\), while all other root costs are at most \(rM\).
The inequality \(c\le(1-r)M\) closes the induction with budget \(M-c\).
No finiteness assumption on the root type, event nesting, or normalization
of the weights is needed. Zero discount and empty lists are included.

For a prime-power coordinate use \(r=1/p\). If the first test cylinder
selects root \(j\), and higher cylinders in root \(i\) have mass at most
\(C_i p^{-e}\), take \(d_i=C_i/p^2\), \(a_j=1\), and all other counts zero.
The remaining square increment is at most

\[
 \frac{\max\{C_j(5p-3),(3p-1)\max_{i\ne j}C_i\}}
      {p(p-1)^2}.                                     \tag{AR2}
\]

For \(p=3\) this recovers the two-root bound below; for \(p=5\) it retains
four possible surviving roots and gives
\(\max\{11C_j/40,7\max_{i\ne j}C_i/40\}\). This arithmetic specialization
is an ordinary application, not another Lean declaration. The checked
component has only the three permitted axioms; its residue-cylinder caps
and the complete covering argument remain separate obligations.

At depth two the initial counts are `(1,0)`, so (G2), multiplied by `1/9`,
bounds the remaining contribution by `max(d_A,2d_B/3)`. The pure ternary
part, excluding the constant diagonal, is therefore at most
`3n+max(d_A,2d_B/3)`. If the modulus-3 test chooses `B`, swap the roles.
If it chooses the forbidden root, its tail is at most
`(2/3)max(d_A,d_B)`, which is no greater than these two-root upper bounds.

Every other ordered pair in the full test-square expansion has positive
`q` exponent in its least common multiple. Pairs with ternary lcm exponent
zero contribute at most `a_q x`; pairs with both exponents positive
contribute at most `2a_q`, using the complete geometric lcm counts.
These include all crosses between pure ternary and positive-`q` test groups.
No old cofactor or exponent group is omitted. Consequently

\[
 \Gamma(\mu)\le1+
 \frac{\max\{3n+d_A,\ 3n+2d_B/3,\ 3m+d_B,\ 3m+2d_A/3\}
       +a_qx+2a_q}{n+m}.
 \tag{G3}
\]

By symmetry it suffices to maximize the first two branches. Move all actual
higher-depth deletion to the unselected root and then enlarge it to `y/6`,
as in the preceding budget argument. This increases each bound and keeps
the denominator positive throughout. Each remaining branch is a ratio of
affine functions in each parameter group of (P10). The same eighteen
vertices, for each of two branches, suffice. Their exact maxima are (G1).
For `q=5` the maximum occurs in the `d_A` branch at
`w=1/2,v=1,α=0,β=1/4,z=3/4`. No actual residue family attaining this
relaxation maximum is asserted.

If the actual modulus-3 class is absent, the earlier unsplit bounds
`215/24,208/33,73/15` for `q=5,7,11` are smaller than (G1).
The [actual-layout verifier](../elementary-checks/verify_two_root_gamma.py)
checks all 108 rational vertex values and the three absent-modulus branches,
with explicit checks that remain active under optimized Python. The full
two-prime congruence theorem (G1) is an ordinary mathematical proof with
exact arithmetic verification; only the stated finite-itinerary component
has been checked in Lean.
