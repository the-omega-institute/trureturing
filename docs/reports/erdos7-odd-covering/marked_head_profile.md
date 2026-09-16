# A supported convex profile for the 315 head

The strongest comparison below retains the original mixed-class deletions in both the load numerator and survivor denominator. On the same supported law it gives mean at most **271/86**, actual second moment at most **1091/82**, and the complete increasing-convex comparator X specified in the deletion-coupling section. Its high-threshold profile remains sharp.

For any family of residue classes with distinct nonunit moduli dividing 315, there is a probability measure μ supported on its survivors such that every complete test layout

\[
 L(x)=\sum_{d\mid315}1_{x\equiv b_d\pmod d}
\]

satisfies \(E_\mu h(L)\le E h(W)\) for every nonnegative increasing convex function h. The same measure μ works for all layouts and functions h. One comparison law, refined below, is

| w | 2 | 3 | 4 | 5 | 6 | 8 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|
| P(W=w) | 3/7 | 15/77 | 18/77 | 15/2849 | 79/814 | 1/37 | 1/74 |

In particular,

\[
 EW=\frac{37}{11},\qquad EW^2=\frac{41336}{2849}.
\]

The measure μ is uniform on a possibly pruned survivor set. The construction uses containment of supports, not monotonicity of uniform averages under pruning.

The elementary argument below gives a sharper, noninteger comparison law W★ with the same mean and second moment 909287/62678. Its proof does not depend on exhaustive layout enumeration.

## Survivor reduction

Add any absent nonunit modulus. If a class is already contained in the union of previously processed classes, move it to delete a further residue without losing any existing deletion. Normalize the pure exclusions to 0 modulo 3, 4 modulo 9, 0 modulo 5 and 0 modulo 7. The surviving modulo-45 grid before mixed exclusions has rows (1,7,2,5,8) modulo 9 and columns (1,2,3,4) modulo 5.

Make the modulus-15 deletion effective and label its column 1. Its ternary root is either the short root 1 or the long root 2. Make the modulus-45 point nonredundant. The remaining coordinate symmetries place this point in exactly one of three positions: the same root and column 2; the other root and column 1; the other root and column 2. These are the six [finite head geometries](finite_head_geometry.md), whose exact symmetry orbits are checked there. There are thus six old survivor sets S₀. In this order, their sizes N are (17,17,17,16,16,16).

Above each x∈S₀ let r(x) be the number of surviving septenary digits. The pure-7 exclusion leaves six digits; the five mixed labels are 7d for d∈{3,5,9,15,45}. Hence

\[
 1\le r(x)\le6.
\]

For \(m_d=\max_a|S_0\cap(a\bmod d)|\), the full survivor count D satisfies

\[
 D=\sum_xr(x)\ge6N-\sum_dm_d=:D_{\min}.
\]

The six lower bounds are (77,78,78,75,74,74). In particular every original family has a nonempty pruned survivor set.

## Finite profile bound

Separate a complete test layout into its zero-7 block L₀ and its positive-7 block. Removing the factor 7 from the latter gives another complete modulo-45 load L₁. Above x, the nonnegative contributions Z_z from the positive block have total at most L₁(x). Convexity and monotonicity give

\[
 \sum_{z\text{ survives}}h(L_0(x)+Z_z(x))
 \le(r(x)-1)h(L_0(x))+h(L_0(x)+L_1(x)).
\]

Indeed, the sum of an increasing convex function cannot decrease when two nonnegative increments are combined at one point, and their combined size can then be increased to L₁(x).

Let a₁≤⋯≤a_N and b₁≤⋯≤b_N be the sorted values of L₀ and L₁. Uncrossing two oppositely ordered pairs, using increasing increments of h, gives

\[
 \sum_xh(L_0(x)+L_1(x))\le\sum_i h(a_i+b_i).
\]

Since r(x)−1 lies between zero and five and sums to D−N, define Top_{D−N}(h(a)) as the sum of the D−N largest entries among five copies of each h(a_i). For μ uniform on the full pruned survivor set,

\[
 E_\mu h(L)\le
 \frac{\sum_i h(a_i+b_i)+\operatorname{Top}_{D-N}(h(a))}{D},
 \qquad D_{\min}\le D\le6N. \tag{1}
\]

This is a relaxation: the two sorted old loads and the extra-fibre weights need not be simultaneously realizable in the maximizing configuration.

For each old survivor shape, enumerate a nonempty cylinder for every modulus 3,5,9,15,45, with the unit term fixed at one. Empty cylinders may be replaced by nonempty ones, increasing the load pointwise. There are 4,760 layouts for each short-root shape and 4,480 for each long-root shape, with respectively (170,135,179,139,131,162) distinct load histograms.

For each threshold t=0,…,12, maximize (1) over every ordered pair of these histograms and every integer D between D_min and 6N. The exact combined maxima are

\[
 (B(0),\ldots,B(12))=
 \left(\frac{37}{11},\frac{26}{11},\frac{15}{11},
 \frac{61}{77},\frac{32}{77},\frac3{11},
 \frac5{37},\frac7{74},\frac2{37},\frac3{74},
 \frac1{37},\frac1{74},0\right).
\]

This sequence is decreasing and convex. Its second differences give precisely the displayed law W. Thus \(E_\mu(L-t)_+\le E(W-t)_+\) at all integer thresholds. Since both loads are integer-valued, their hinge expectations are affine between consecutive integers. The bound extends to all real t, and the finite hinge expansion of h gives the stated increasing-convex comparison. The middle entries B(t) are exact maxima of the relaxation; no claim of actual-family sharpness there is required.

The [standard-library verifier](verify_marked_head_profile.py) recomputes every one of the 27,720 old layouts, retains all histograms, and checks all 44,608,551 ordered-histogram-pair, integer-D and integer-threshold cases using integer arithmetic. It compares the resulting rational profiles, law and moments with the [fixed rational certificate](marked_head_profile_certificate.json). The finite verification is separate from the ordinary mathematical pruning and convexity argument above; it is not an end-to-end Lean verification.

## Elementary proof and a sharper comparison law

Write an old load as ℓ=1+1_A+1_B+1_C+1_D+1_E, where A is a ternary root, B a ternary cell, C a quinary column, D a root-column intersection and E a point. These five choices are independent. Let Φ_S(u)=max_ℓ Σ_{x∈S}(ℓ(x)−u)₊. For either old survivor size n, the following bounds hold:

| n | Φ_S(1) | Φ_S(2) | Φ_S(3) | Φ_S(4) | Φ_S(6) |
|---|---:|---:|---:|---:|---:|
| 16 | 22 | 10 | 5 | 2 | 0 |
| 17 | 25 | 11 | 5 | 2 | 0 |

At threshold one, sum the five cylinder-size bounds. They are (9,4,5,3,1) when n=16 and (12,4,5,3,1) when n=17. To prove the other entries, first omit E and put J=1+1_A+1_B+1_C+1_D. Restoring its single point adds at most one to any summed hinge.

At threshold two, Σ(J−2)₊ is total cylinder multiplicity minus union size. If D⊆A and B⊆A, it equals |D|+|B|+|A∩C|. For n=16 this is at most max(3+3+3,2+4+2)=9: long-root cells have lost their forbidden column, while the short root has only two cells. For n=17 it is at most 3+4+3=10. If D⊆A and B∩A=∅, the expression is |D|+|C∩(A∪B)|≤3+4=7. If D∩A=∅, it is |B∩(A∪D)|+|C∩(A∪D∪B)|≤4+5=9. These cases exhaust the root relationships.

At threshold three, if A∩D=∅, then (J−3)₊≤1_{B∩C}, whose sum is at most one. If D⊆A, its sum is |B∩D|+|C∩D|+|(A∖D)∩B∩C|. This is at most 1+3+0 when C uses D's column, and at most 1+0+1 otherwise. At threshold four, J=5 requires membership in B∩C, a set of at most one point. Finally ℓ≤6. Restoring E proves the table.

Let φ₁₆ and φ₁₇ linearly interpolate the corresponding rows at thresholds 1,2,3,4,6, and vanish above 6. Convexity of the hinge makes each interpolant an upper bound for Φ_S. The threshold-one bounds also give D≥6n−Φ_S(1), hence D₁₆=74 and D₁₇=77 are valid universal denominators.

The fibre inequality, r−1≤5, and (a+b−t)₊≤(a−t/2)₊+(b−t/2)₊ imply, for t≥2,

\[
 \Theta_\mu(t)\le
 \max_{n\in\{16,17\}}\frac{5\phi_n(t)+2\phi_n(t/2)}{D_n}.
\]

The n=17 expression dominates until t★=117/22; the n=16 expression dominates afterwards. For 0≤t≤2 use (L−t)₊≤(L−2)₊+2−t. The resulting profile is

\[
\Psi(t)=
\begin{cases}
37/11-t,&0\le t\le2,\\
(193-44t)/77,&2\le t\le3,\\
(148-29t)/77,&3\le t\le4,\\
(76-11t)/77,&4\le t\le117/22,\\
(70-10t)/74,&117/22\le t\le6,\\
(28-3t)/74,&6\le t\le8,\\
(12-t)/74,&8\le t\le12,\\
0,&t\ge12.
\end{cases}
\]

Its nondecreasing slopes give the comparison law

| w | 2 | 3 | 4 | 117/22 | 6 | 8 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|
| P(W★=w) | 3/7 | 15/77 | 18/77 | 2/259 | 7/74 | 1/37 | 1/74 |

Thus Ψ(t)=E(W★−t)₊, EW★=37/11 and E[(W★)²]=909287/62678. The second moment is smaller than that of W by 15/8954. At integer thresholds Ψ agrees with the earlier profile B; between 5 and 6 it improves the linear interpolation, with Ψ(117/22)=5/22 whereas the integer law gives 1025/4477. Hence W★, as well as W, bounds every increasing convex function under the same supported law μ. The verifier independently checks the elementary table against every old layout, the exact transfer crossing and all law probabilities and moments; the table's proof itself is elementary.

## Coupling the original deletions to the load numerator

The following estimates apply simultaneously to **one law**: the uniform law on the actual complete survivors after the canonical old-head pruning already justified above. They do not assert that uniform expectations on the unpruned original set are monotone under pruning. The resulting law is supported on the original survivors.

Let S be one of the six canonical old survivor sets modulo 45, n=|S|∈{16,17}, and let D₀={3,5,9,15,45}. Pure modulus 7 leaves six digits. For x∈S, write b(x) for the number of distinct remaining digits deleted by the five original mixed classes of moduli 7d, d∈D₀. Thus 0≤b(x)≤5, r(x)=6−b(x)≥1, the complete survivor count is N=6n−Σₓb(x), and μ is uniform on these N actual points. If C_d is the old cylinder of the original class 7d, then

\[
 b(x)\le \sum_{d\in D_0}1_{C_d}(x).
\]

For an arbitrary complete 315 test layout, let A(x) be its old test load and B(x) its old cofactor test load from the 7-containing labels. Each is an independently arbitrary complete 45 test load, with values in {1,…,6}. At x, the nonnegative test increments over the r(x) allowed digits have total at most B(x). For any increasing convex function h, concentrating all increments into one allowed digit gives

\[
 N E_\mu h(L)
 \le 5\sum_x h(A(x))+\sum_xh(A(x)+B(x))-\sum_xb(x)h(A(x)). \tag{D1}
\]

This concentration is an upper bound; the concentrated test layout need not be realizable. Missing or inactive test labels can be completed upward before applying (D1).

Let J_h(A) bound max_B Σₓh(A(x)+B(x)). To prove Eμh(L)≤c, it therefore suffices to check, for every A,

\[
 5\sum_xh(A(x))+J_h(A)
 +\sum_{d\in D_0}\max_{C\bmod d}\sum_{x\in S\cap C}(c-h(A(x)))_+
 \le 6nc. \tag{D2}
\]

Indeed the difference between the numerator in (D1) and cN contains Σₓb(x)(c−h(A(x))). Discard its negative terms and bound b by the five original cylinder indicators. This yields exactly the positive cylinder caps in (D2). No independence assumption on the original forbidden classes or the two test blocks is used.

### Hinge and square costs

For integer t≥0 put H_t(A)=Σₓ(A(x)−t)₊ and M_t=max_B H_t(B). Hinge subadditivity gives the useful small verification bound

\[
 J_t(A):=\min_{0\le k\le t}\{H_k(A)+M_{t-k}\}
 \ \ge\ \max_B\sum_x(A(x)+B(x)-t)_+ . \tag{D3}
\]

For the square cost put Q=max_BΣₓB(x)² and

\[
 R(A)=\sum_xA(x)+\sum_{d\in D_0}\max_{C\bmod d}\sum_{x\in S\cap C}A(x).
\]

Independence of the five choices defining the test load B gives R(A)=max_BΣₓA(x)B(x). Hence the square version of (D2) is implied by

\[
 6\sum_xA(x)^2+2R(A)+Q
 +\sum_{d\in D_0}\max_{C\bmod d}\sum_{x\in S\cap C}(c-A(x)^2)_+
 \le 6nc. \tag{D4}
\]

Every effective old layout is enumerated; no pairwise layout search or optimizer is needed. The following exact rational constants satisfy (D2), using (D3), for t=0,…,5, and (D4) in the last column:

| Old shape | n | c₀ | c₁ | c₂ | c₃ | c₄ | c₅ | Square c |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Short root, same root / other column | 17 | 271/86 | 185/86 | 100/81 | 61/81 | 16/39 | 7/26 | 1091/82 |
| Short root, other root / same column | 17 | 263/85 | 178/85 | 101/84 | 30/41 | 32/79 | 21/79 | 1103/85 |
| Short root, other root / other column | 17 | 263/85 | 178/85 | 101/84 | 30/41 | 32/79 | 21/79 | 1103/85 |
| Long root, same root / other column | 16 | 3 | 2 | 89/75 | 11/15 | 2/5 | 4/15 | 965/76 |
| Long root, other root / same column | 16 | 234/77 | 157/77 | 91/76 | 14/19 | 2/5 | 4/15 | 993/77 |
| Long root, other root / other column | 16 | 234/77 | 157/77 | 91/76 | 14/19 | 2/5 | 4/15 | 993/77 |

The finite check covers 27,720 effective old layouts and 194,040 integer cap inequalities. It clears the denominator of each proposed rational c, computes the exact minimum scaled slack, and finds zero in all 42 cases. Zero slack certifies the displayed relaxation constants; it does **not** establish sharpness for realizable full families. All mathematical decisions use standard-library integers and fractions. The six-orbit completeness and the universal fibre argument are ordinary proof inputs to this finite certificate.

### A single improved full comparator

For Θμ(t)=sup_test Eμ(L−t)₊, take the largest constant in each hinge column and retain the established sharp high-profile values at t=6,8,12. The knots are

\[
\begin{array}{c|rrrrrrrrr}
t&0&1&2&3&4&5&6&8&12\\\hline
\Theta_\mu(t)\le&271/86&185/86&100/81&61/81&16/39&7/26&5/37&2/37&0.
\end{array}
\]

Convexity of Θμ bounds it above by the chord on each interval. The chord slopes are

\[
-1,-6385/6966,-13/27,-361/1053,-11/78,-129/962,-3/74,-1/74,0,
\]

which are nondecreasing. Consequently this chord function is the hinge profile of the probability law X with atoms

\[
\begin{array}{c|rrrrrrrr}
x&1&2&3&4&5&6&8&12\\\hline
P(X=x)&581/6966&3031/6966&146/1053&425/2106&10/1443&45/481&1/37&1/74.
\end{array}
\]

Every complete test load under the same μ is dominated by X in increasing convex order. In particular,

\[
 E_\mu L\le E X=\frac{271}{86},\qquad
 E_\mu L^2\le\frac{1091}{82},\qquad
 E X^2=\frac{45292361}{3350646}.
\]

The direct square bound is stronger than the comparator's second moment and may be used simultaneously with its complete hinge profile. These are supported-law head bounds; they do not by themselves establish a global tail cutoff or an end-to-end Lean proof.

## Actual sharpness for t≥6

Take the original classes (modulus, residue)

\[
 (3,0),(9,4),(5,0),(15,11),(45,1),(7,0),
 (21,8),(63,16),(35,17),(105,32),(315,47).
\]

Their old modulo-45 survivor count is 16. The five mixed septenary classes use distinct residues 1,2,3,4,5 and have old-cylinder masses 9,4,5,3,1, respectively. Their deleted sets are disjoint, so the complete survivor count is \(6\cdot16-22=74\). Septenary residue 6 contains all 16 old survivors.

Use the coherent test centre 272 modulo 315, which is 2 modulo 45 and 6 modulo 7. The old complete load has histogram

\[
 \#\{L_{45}=1,2,3,4,6\}=(5,6,2,2,1).
\]

In septenary residue 6 the full load is 2L₄₅; in every other residue it is L₄₅≤6. Its full survivor histogram is

\[
 \#\{L=1,2,3,4,6,8,12\}=(22,28,8,10,3,2,1).
\]

Consequently the uniform survivor law satisfies, for every real t≥6,

\[
 E(L-t)_+=\frac{(12-t)_++2(8-t)_+}{74}=E(W-t)_+.
\]

The verifier checks this actual residue family, both histograms, the clean septenary fibre and all integer endpoints of these affine pieces. Thus the uniform-survivor comparison is sharp throughout t≥6. This does not assert optimality of its lower thresholds among all supported laws.

## Exact upper-tail minimax and endpoint restriction

For every probability measure ν on ℤ/315ℤ, with no support restriction,

\[
 \Theta_\nu(t)=(12-t)\|\nu\|_\infty\qquad(8\le t\le12). \tag{2}
\]

The old threshold-four argument also holds on the entire period ℤ/45ℤ: Σ(ℓ−4)₊≤2 and ℓ≤6. Convexity gives Σ(ℓ−u)₊≤6−u for 4≤u≤6. On the full modulo-315 period, pool the positive septenary increments. For t≥8 the baseline term vanishes because L₀≤6, so

\[
 \sum_{y\bmod315}(L(y)-t)_+
 \le\sum_{x\bmod45}(L_0(x)+L_1(x)-t)_+
 \le2(6-t/2)=12-t.
\]

Multiplication by the maximum atom of ν proves the upper bound in (2). A coherent layout centered at a maximum-mass point has load 12 there and gives the matching lower bound. The verifier also enumerates the 91,125 full-period old layouts and checks their maximum unnormalized hinges (2,1,0) at thresholds (4,5,6).

Thus on every fixed survivor set T and for 8≤t<12, the unique minimizing supported law is uniform, with value (12−t)/|T|. Every original family has at least 74 survivors and the displayed actual family has exactly 74. Therefore

\[
 \sup_{\mathcal F}\ \inf_{\operatorname{supp}\nu\subseteq T_{\mathcal F}}
 \Theta_\nu(t)=\frac{12-t}{74}\qquad(8\le t\le12).
\]

The uniqueness statement excludes t=12, where every measure has zero hinge.

More generally, let S be a nonempty subset of ℤ/Qℤ, μ a probability measure supported on S, and τ=τ(Q) the number of positive divisors of Q. For complete divisor layouts,

\[
 \sup_{(b_d)}E_\mu(L-(\tau-1))_+=\max_{s\in S}\mu(s). \tag{3}
\]

Indeed 0≤L≤τ is integer-valued, so the hinge equals the indicator of L=τ. The divisor-Q term restricts that event to a single residue. Conversely the coherent layout b_d=s modulo d attains load τ at any selected s. This proves (3).

For a fixed S of size D, the uniform law uniquely minimizes (3), with value 1/D. Every distinct supported law gives a strictly larger endpoint. Hence no nonuniform law can pointwise improve the entire uniform-law worst-layout profile on that same S. On the 74-point sharp family, every nonuniform law worsens the entire interval 8≤t<12.

## Obstruction to a fixed uniform old marginal

Take original classes

\[
 (3,0),(9,4),(5,0),(15,11),(45,37),(7,0),
 (21,8),(63,2),(35,3),(105,53),(315,173).
\]

There are 16 old survivors and 75 full survivors. The five mixed classes have a common old centre 38 modulo 45 and distinct forbidden septenary digits 1,…,5. The coherent old load Y therefore satisfies r(x)=7−Y(x), with multiplicities (5,6,2,2,1) at loads (1,2,3,4,6).

Choose the uniform old marginal and then the uniform surviving fibre. For the coherent full test centre 83, conditionally on Y=y the full load equals y with probability (6−y)/(7−y), and 2y with probability 1/(7−y). Its exact mean is 63/20 and its second moment is 1427/80. The centre's fibre has size one, giving a maximum atom 1/16. Identity (2) consequently gives the exact worst-layout profile (12−t)/16 for 8≤t≤12. Conversely every such fixed-uniform-old-marginal construction on the normalized six shapes has maximum atom at most 1/16, since n≥16 and r≥1. This is its sharp universal upper-tail bound. The same verifier checks the actual classes, the pointwise fibre formula, conditional distribution and exact moments. The obstruction concerns this specified marginal rule; it does not apply to arbitrary nonuniform old marginals.

## Use as a head block

Conditional comparison over later-prime coordinates leaves a sum of m complete head layouts, where m is the realized positive integer suffix multiplier. Jensen's inequality yields

\[
 h\left(\sum_{j=1}^{m}L_j\right)
 \le\frac1m\sum_{j=1}^{m}h(mL_j).
\]

The same measure μ bounds every summand by E h(mX). Thus X can replace the head in subsequent complete-cofactor convex comparisons, with zero initial deletion charge. This comparison alone makes no claim that any particular tail continuation closes.

## Information retained when adjoining 11

The actual 315 cells give a residual-capacity criterion that permits empty fibres. Let S be the selected pruned survivor set, n=|S|, and D the eleven nonunit divisors of 315. Normalize the pure-11 forbidden digit to zero. If b(x) distinct nonzero digits are deleted above x, then r(x)=10−b(x) may be zero. The full survivor count is N=10n−Σb(x). Define

\[
 \mathcal R_S(v)=\sum_{d\in D}\max_{a\bmod d}
                 \sum_{\substack{x\in S\\x\equiv a\pmod d}}v(x).
\]

For a complete test layout modulo 3465, write A for its zero-11 load and B for its positive-11 load with the factor 11 removed. Both are complete old test loads. For a nonnegative increasing convex h, fibre concentration gives

\[
 \sum_{z\text{ survives at }x}h(L(x,z))
 \le(r(x)-1)h(A(x))+h(A(x)+B(x))
 -1_{r(x)=0}\bigl[h(A(x)+B(x))-h(A(x))\bigr]. \tag{P11.1}
\]

For r≥1 this is the earlier concentration argument; for r=0 the right side is exactly zero. Write J_h(A)=max_B Σh(A+B). Subtracting cN, discarding the nonnegative empty-fibre correction and using b(x)≤Σ_d1_{C_d}(x) shows that

\[
 9\sum_xh(A(x))+J_h(A)
 +\mathcal R_S((c-h(A))_+)\le10nc
       \quad\text{for every old test layout }A             \tag{P11.2}
\]

suffices for E_uniform(survivors)h(L)≤c. The same-law mean bound gives R_S(1)/n≤185/86, so N≥675n/86>0. Thus normalization is valid even with empty individual fibres. `PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le` already supplies the corresponding transfer under old-point-dependent weights; conditional laws at zero-weight old points can be chosen arbitrarily. No new Lean wrapper is required. A universal evaluation of (P11.2), beyond the scalar relaxation, remains open.

Two explicit witnesses show which information this criterion retains. Use the 74-point original family in the sharpness section. The coherent test layouts centred at 33 and 301 both have the entire histogram

\[
 \#\{A=1,2,4\}=(38,31,5).
\]

They therefore agree on every scalar cost of A, including every hinge. Nevertheless,

\[
 \mathcal R_S(1_{A_{33}=1})=98,\qquad
 \mathcal R_S(1_{A_{301}=1})=114,\qquad \mathcal R_S(1)=142.
\]

Here 1_{A=1}=(2−A²)₊ is precisely a residual weight in (P11.2). The complete scalar load distribution cannot determine this weighted cylinder capacity. This does not refute a conservative scalar upper bound or certify a new universal 3465 estimate.

For an actual empty fibre, add (11,0) and

\[
 (33,23),(55,2),(77,69),(99,92),(165,137),(231,83),
 (385,62),(495,272),(693,20),(1155,692),(3465,3422).
\]

These give exactly one original class for every nonunit divisor of 3465. Their old cofactors are centred at 272, and their forbidden 11-digits are 1,2,…,10,1 in increasing cofactor order. Exact enumeration gives 627 full survivors, with the only empty old fibre at 272 and fibre histogram

\[
 \#\{r=0,3,5,7,8,9,10\}=(1,2,3,10,8,28,22).
\]

A supported extension cannot preserve a positive old mass at 272. The uniform full-survivor law is valid and assigns zero old mass there.

## Remaining mass vectors do not determine the next original label

On the same 74-point head, 36 points satisfy x≡1 mod3. Add (11,0) and either (33,1) or (33,13). In the first case the mixed class forbids 11-digit 1 over this root; in the second it forbids digit 2. Every individual old point has the same surviving fraction in both systems: 9/11 over root 1 and 10/11 elsewhere. Both have 704 survivors modulo 3465, raw surviving mass 32/37, and the same normalized old marginal.

Now add the pure class (13,0). Each system has 8448 survivors modulo 45045. The fixed subsequent query class (143,1) has respectively 38 and 74 hits, hence probabilities

\[
 \frac{19}{4224}\quad\text{and}\quad\frac{37}{4224}.        \tag{P13.1}
\]

Thus even the entire head-indexed residual mass vector and the old law do not determine the next labelled cofactor probability. The surviving 11-prefixes must also be distinguished for exact propagation. The fixed certificate and verifier check all three witnesses directly from their actual original classes, the weighted cylinder maxima and the full CRT periods.

The exact prefix data have a finite representation. For each old point x, retain only minimal forbidden 11-prefixes; they form a disjoint antichain P_x. The raw mass V_{e,a}(x) surviving inside a query prefix a mod11ᵉ is zero if a member of P_x contains it. Otherwise

\[
 V_{e,a}(x)=11^{-e}
 -\sum_{\substack{(f,b)\in P_x\\f>e,\ b\equiv a\pmod{11^e}}}11^{-f}. \tag{P13.2}
\]

For any old law μ and positive Z=Σ_xμ(x)V_{0,0}(x), the normalized query mass for Q=(d,a,e,b) is Z⁻¹Σ_{x≡a mod d}μ(x)V_{e,b}(x). Two compatible prefix queries intersect in the deeper prefix; incompatible queries have zero intersection. Expanding a weighted labelled load and its square therefore retains every actual head-cylinder intersection until after the cross terms are formed. The disjoint-prefix counting and finite-law conditioning reuse the existing residual-law geometry and probability interfaces; no new general clipping theorem is asserted.

The repository's AP1–AP7 and W1–W5 comparisons and its scalar-fibre boundary, together with BBMST arXiv:1811.03547 §§2–3, arXiv:1901.11465 §5.3 and Hough arXiv:1307.0874 §3, supply the surrounding conditional-sieving framework. The residual operator specifies the additional labelled state exhibited by these counterexamples. It has not yet supplied a universal bound closing the tail from 11.
