# A supported convex profile for the 315 head

The strongest comparison below retains the original mixed-class deletions in both the load numerator and survivor denominator. On the same supported law it gives the sharp uniform-law mean bound **271/86**, sharp uniform-law second-moment bound **1131/86**, and the complete increasing-convex comparator X specified in the deletion-coupling section. Its high-threshold profile remains sharp.

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

The finite check covers 27,720 effective old layouts and 194,040 integer cap inequalities. It clears the denominator of each proposed rational c, computes the exact minimum scaled slack, and finds zero in all 42 cases. Zero slack certifies the displayed relaxation constants. The explicit witness below establishes actual-family sharpness at thresholds zero and one; zero slack alone does not establish sharpness at the other thresholds or for the square bound. The signed-union argument below further improves the square bound and supplies a simultaneous sharp witness. All mathematical decisions use standard-library integers and fractions. The six-orbit completeness and the universal fibre argument are ordinary proof inputs to this finite certificate.

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

## A sharp second-moment bound from signed deletion unions

For the same uniform law on complete survivors after canonical old-head
pruning, every complete 315 test load satisfies

    E L^2 <= 1131/86.

This improves 1091/82. The new bound is attained by an actual original family
and test layout, and the same example attains E L=271/86. The claim concerns
this prescribed uniform law, not minimax optimization over all supported laws.

Let S be an old 45 survivor set, n=|S|, A an old complete test load, and
B the old test load belonging to the 7-containing block. Put

    Q = max_B sum B^2,
    R(A) = max_B sum AB
         = sum A + sum_d max_(C mod d) sum_C A,
    K(A) = 6 sum A^2 + 2 R(A) + Q,

where d ranges over 3,5,9,15,45. With b(x) distinct deleted nonzero septenary
digits at x, the square numerator is at most K(A)-sum b(x)A(x)^2 and the
survivor count is 6 n-sum b(x). Thus a constant c is sufficient if

    K(A) + max_deletions sum_x b(x)(c-A(x)^2) <= 6 nc

for every A. Unlike the earlier cap estimate, the deletion maximum retains
the signed weights.

Partition the five original mixed 7 labels by their nonzero septenary digit.
For a block T, choose one old cylinder for each label and take their union
U. The block deletes exactly one digit on U, contributing sum_U(c-A^2).
Different blocks add, including where their old unions overlap. A label
may be inactive by using the already forbidden zero digit; this is modeled
by a virtual empty cylinder. There are at most five active blocks, leaving
a sixth digit globally free. Therefore every such partition/union choice
is realizable by original congruence classes, and all test 7 increments may
be placed at the free digit.

The verifier enumerates every attainable union mask for each of the 32
label subsets. If U_T is the maximum signed weight of a union for T, define

    D(empty)=0,
    D(S)=max_(T subset S, min(S) in T) [U_T+D(S\T)].

This subset recurrence enumerates every set partition exactly up to its
canonical first block. It computes the exact signed deletion maximum.
The separate bound K(A) can still have slack unless one B simultaneously
attains Q and R(A); the literal sharp witness below has B=A and attains both.

The first canonical old shape has 17 points and 4760 effective old layouts.
There are 2164 distinct union masks and 8919 mask entries across all subsets.
At c=1131/86, the verifier first tries the valid, cheaper positive-cap
upper bound. Exactly 4754 layouts pass this screen; the remaining 6 need the signed DP.
It then checks K(A)+D(all)<=6 nc by exact integer arithmetic after multiplying
by 86. The other five canonical shapes have previously verified constants
1103/85,1103/85,965/76,993/77,993/77, all strictly smaller than 1131/86.

For sharpness, use the original family

    (3,0), (9,4), (5,0), (15,1), (45,37), (7,0),
    (21,1), (35,9), (63,52), (105,4), (315,142),

and complete test layout

    (1,0), (3,2), (5,3), (9,2), (15,8), (45,38),
    (7,6), (21,20), (35,13), (63,20), (105,83), (315,83).

There are 86 actual survivors. Their test-load histogram is

| Load | 1 | 2 | 3 | 4 | 6 | 8 | 12 |
|---|---|---|---|---|---|---|---|
| Count | 5 | 38 | 14 | 18 | 8 | 2 | 1 |

Hence sum L=271 and sum L^2=1131. On the old 17-point set, A=B has
sum A^2=sum AB=sum B^2=130; the original classes delete 16 lifted points
with deleted old square sum 39. The attained ratio is therefore

    (6*130+2*130+130-39)/(6*17-16)=1131/86.

The same-law finite 3465 transfer keeps its existing comparison atoms and
hinges. Its separate actual moment now improves to

    1+[(13/10)(1131/86)-1]/(135/172)=14518/675,

which is smaller than that comparator's second moment 1746200/80919. This
is exact transfer arithmetic; it is not a new tail-feasibility result.

All displayed finite bounds and the literal witness are checked with
standard-library integer and rational arithmetic. The probabilistic
transfer and canonical pruning remain ordinary proof inputs; no Lean
verification or unrestricted odd-covering exclusion is claimed here.

## Actual sharpness of the uniform315 mean bound

The simultaneous uniform-pruned-survivor bounds at thresholds0 and1 are
sharp for that prescribed law. This does not establish minimax sharpness
over all probability laws supported on each original survivor set.

Take the complete original family of modulus/residue pairs

    (3,0), (9,4), (5,0), (15,1), (45,37), (7,0),
    (21,1), (35,9), (63,52), (105,4), (315,187).

Its old45 part is already the first canonical shape. The complete test
layout, including the unit term, is

    (1,0), (3,2), (5,3), (9,2), (15,2), (45,2),
    (7,6), (21,20), (35,13), (63,20), (105,62), (315,272).

Directly checking the315 residue classes gives86 surviving points and test
load histogram

| Load | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 10 |
|---|---|---|---|---|---|---|---|---|
| Count | 5 | 28 | 29 | 11 | 5 | 6 | 1 | 1 |

The total load is271, hence the uniform survivor law has E L=271/86.
All loads are at least1, so E(L-1)+=185/86. Together with the universal
upper bounds, these equalities establish actual-family sharpness at both
thresholds, beyond sharpness of the deletion-cap relaxation.

The deletion construction also explains why the relaxation is attained.
For the old test load A, choose the original old cylinders at residues
1 mod3, 4 mod5, 7 mod9, 4 mod15, and7 mod45. Assign their corresponding
mixed7 classes the distinct septenary digits1,2,3,4,5. These cylinders
contain5,5,3,2,1 old points, and their A-load sums are7,9,4,2,1. Every such
load is at most3, so discarding the negative part in (271/86-A)+ loses
nothing. Distinct septenary digits make the16 deleted lifted points
disjoint. Put all test7 labels at the free digit6. The old test blocks
satisfy B=A and sum A=sum B=42. Consequently the survivor count and total
test load are

    N = 6*17-(5+5+3+2+1) = 86,
    sum L = 6*42+42-(7+9+4+2+1) = 271.

The literal witness check uses only integer arithmetic and rational
division; its runtime checks remain enabled under Python optimization.
This is an ordinary finite certificate, not a Lean theorem.

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

## A supported full profile for the finite 3465 head

Adjoin one 11 digit to the same uniform pruned315 law μ, first deleting the pure-11 forbidden digit. Let ν be μ times the uniform law on the ten remaining digits. Fibre concentration and convexity give, for every complete3465 test load L,

\[
 E_\nu h(L)\le\tfrac9{10}Eh(X)+\tfrac1{10}Eh(2X)=Eh(Z),
\]

where Z=XY, with Y independent of the comparison variable X and P(Y=1)=9/10, P(Y=2)=1/10. The actual old test blocks need not be independent. The eleven mixed original labels have ν-union mass at most (EX−1)/10=37/172. Thus the actual survivor event E has probability s≥ρ=135/172. Conditioning once on E gives one supported law μ₁₁ for all layouts; its old marginal may change.

For every increasing convex h, using a=h(2) gives

\[
 E_{\mu_{11}}h(L)
 \le a+\rho^{-1}E_\nu(h(L)-a)_+
 \le a+\rho^{-1}E(h(Z)-a)_+.
\]

Retain the upper ρ mass of Z and normalize. Exactly 581/7740 is removed at value1 and 271/1935 at value2; part of value2 remains. The resulting probability law Y₁₁ has the following atoms:

| Value | Probability |
|---:|---:|
| 2 | 18104/54675 |
| 3 | 12556/78975 |
| 4 | 203878/710775 |
| 5 | 172/21645 |
| 6 | 252754/2022975 |
| 8 | 1491197/26298675 |
| 10 | 172/194805 |
| 12 | 989/36075 |
| 16 | 86/24975 |
| 24 | 43/24975 |

All removed values are at most2 and all retained values are at least2, so the last bound equals E h(Y₁₁). This proves a common increasing-convex comparison for every family with distinct nonunit moduli dividing3465. Missing original labels can be added before the construction; the supported resulting law still avoids the original family. In particular,

\[
 E_{\mu_{11}}L\le\frac{4816}{1215},\qquad
 E_{\mu_{11}}L^2\le\frac{14518}{675}.
\]

For t≥2, the complete comparator profile is

\[
 E(Y_{11}-t)_+
 =\frac{9E(X-t)_++2E(X-t/2)_+}{10-(271/86-1)}.
\]

Below2 it is E(Y₁₁−2)₊+2−t; above24 it vanishes. The comparator has second moment 1746200/80919. The sharp old actual moment gives the smaller bound 1+((13/10)(1131/86)−1)/ρ=14518/675, since L≥1 before conditioning. Both concern the same μ₁₁; the smaller actual bound above is used while all comparator atoms and hinges remain unchanged. The verifier reconstructs the exact quantile, all ten atoms and all25 integer hinge values, and independently recovers the same law by cancelling the negative value1 atom in the signed unit-loss expression. This is an ordinary proof with exact arithmetic, not a Lean theorem or a successful universal tail continuation.

## Uniform sharp-head obstruction to an excess energy rebate

This strengthens the previously retained arbitrary-law/Dirac saturation obstruction to the complete actual uniform315 survivor law attaining the sharp second-moment constant1131/86. All masses below belong to one actual normalized physical chain. The equal prefix caps are UNNORMALIZED caps of the good restriction; conditioning that restriction changes its caps.

Take the sharp head's eleven original classes

    (3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
    (21,1),(35,9),(63,52),(105,4),(315,142).

Its complete survivor set S has86points. Let mu be uniform on S. The complete test layout

    (1,0),(3,2),(5,3),(9,2),(15,8),(45,38),(7,6),
    (21,20),(35,13),(63,20),(105,83),(315,83)

has load L* and E_mu(L*)²=1131/86. The separately proved sharp upper bound therefore gives Gamma315(mu)=1131/86. Its five load-one points include c=19.

Adjoin the pure class0 mod11. For d=35,45,63,105,315 in this order, adjoin the unique CRT class whose old residue is19 mod d and whose11digit is respectively1,2,3,4,5. Original moduli11d are all distinct. Put delta11=2/5 and use the ordinary clipped kernel with base uniform on digits1,...,10.

At x in S let n(x) count active old cofactors. Their assigned digits are distinct. We have0<=n<=5, and n=5 exactly when x=19 because their least common multiple is315. Thus the actual conditional11charge is

    b11(x)=(n(x)-4)_+/6=1[x=19]/6.

The total charge is b=1/516. If r(x) is the good restriction's row mass, then r=1 away from19 and r(19)=5/6. Every complete head layout A has A>=1. Hence

    E_mu[r A²] <= E_mu[A²]-b <= Gamma315(mu)-b.

Equality holds for L*, because L*(19)=1. Consequently

    Gamma315(r mu)=1131/86-1/516=6785/516.

After normalization the exact old energy is `1357/103`, strictly greater than `1131/86`.

There is no old-layout suboptimality or excess loss available to pay an additional universal rebate. This conclusion concerns the maximum over ALL complete head layouts, not just the displayed layout. Its upper bound uses the existing verified sharp uniform315 theorem; the new exact verifier directly consumes that theorem's freshly computed result and sharp-witness fields.

The clipped mass of each good11digit is

    c(x)=1/[10-min(n(x),4)].

At least five good digits remain at every x. Therefore the largest depth-one prefix mass is c(x) both before and after killing the forbidden digits. The cap functions themselves agree pointwise, so Gamma315(c mu) also agrees before and after killing. At x=19 the unnormalized good cap is1/6, whereas the cap after row normalization is1/5; these are not confused.

### Same-law later charge with no intersection

Complete a test layout on3465 by retaining the twelve classes of L* at11exponent0 and using, for each old divisor d, the corresponding L* residue together with11digit10 at11exponent1. Its literal load is

    L(x,y)=L*(x)(1+1[y=10]).

Adjoin0 mod31 and, for each of the23nonunit divisors of3465, one original mixed31class at this test residue, assigning distinct31digits1,...,23. These are ordinary distinct moduli. Altogether there are41distinct odd original moduli, with actual lcm107415.

With delta31=2/5, the actual conditional31charge is

    b31(x,y)=(L(x,y)-13)_+/18.

The entire positive11charge lies over x=19, where L* is1 and L<=2, so the two charge events have zero intersection. The positive31charge lies over x=83,188,293 at y=10. Exact enumeration of actual CRT classes and normalized kernels gives

    P(B11)=1/516,
    P(B31)=17/15480,
    P(B11 intersect B31)=0.

Thus killing B11 leaves raw later charge17/15480 unchanged. Conditioning on avoiding B11 makes it17/15450, strictly larger. No later-charge saving is inferred from the first charge.

### All 11 heights

For any H>1, add the redundant pure class0 mod11^H. It is contained in0 mod11, preserves original-modulus distinctness, and makes the true lcm315*31*11^H. The actual pure base and both mixed bad events depend only on the first11digit. The normalized11kernel is therefore the preceding kernel extended uniformly over higher digits. At every positive depth e<=H its maximal prefix mass, before and after killing, is exactly

    c(x)*11^(-(e-1)).

The root charge, weighted old Gamma, and later-charge intersection are unchanged. This is an arbitrary-height actual congruence construction; the checker independently reconstructs every cap for H=1,2,3. It does not assert unchanged normalized caps.

### Scope and source reuse

This refutes any positive excess rebate asserted solely from: uniformity on the full actual315survivor set, the sharp old Gamma, positive first charge, original-modulus injectivity, and actual prefix caps. In particular those data need not force any of positive-depth cap loss, old-energy loss beyond b, or positive later-charge intersection. It does not rule out improvements requiring additional residue alignment or a different optimized head law, and does not settle unrestricted Erdos7.

Repository search reused the existing actual forbidden-class Gram projection, its old-layout deficit identity, the previously retained Dirac saturation and45-class residual obstruction, and the new sharp uniform315 square. Public Hough-Nielsen arXiv:1703.02133, Lemmas5-6, controls moments by bias statistics and transports them using good-fibre proportion and maximal biases; it does not supply a guaranteed positive test/forbidden alignment. BBMST arXiv:1901.11465, section5.3, constructs nonuniform survivor laws by optimizing over actual configurations. Those results remain reusable tools and do not imply the refuted uniform-law rebate. Both public HTML sources were retrieved and their cited passages read for this check.


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

## Survivor-weighted full convex comparison

Let p be prime, p∤Q, and H≥1. Let ρ be a finite nonnegative measure on Z/QZ, and let R_x be a nonnegative row measure on Z/pᴴZ with total mass r(x)∈[0,1]. Suppose every depth-e prefix has R_x-mass at most a_e(x), where a₁≥⋯≥a_H≥0. Put

\[
 \beta_0=r,\quad\beta_e=\min(r,a_e)\ (1\le e\le H),\quad
 \beta_{H+1}=0,\qquad w_k=\beta_k-\beta_{k+1}.
\]

For any complete enlarged layout write A_e for its complete old head layout at p-exponent e. All original pairs (old divisor,e) remain separate labels. Then every increasing convex h satisfies

\[
 \int h(L(x,y))\,dR_x(y)
 \le\sum_{k=0}^H w_k(x)h\!\left(\sum_{e=0}^kA_e(x)\right). \tag{C1}
\]

Here is a detailed verification of the comparison step. At fixed x retain only active positive-depth labels, each contributing a Bernoulli indicator, and order them by decreasing cap β_e(x). If their count is m and their indicators are I₁,…,I_m, then for every integer j≥0,

\[
 (\sum_iI_i-j)_+\le\sum_{i>j}I_i.
\]

Therefore the hinge integral is bounded by Σ_{i>j}β_i, which is exactly the hinge integral of nested indicators of those cap masses on an interval of total mass r. Every increasing convex function on the finitely many possible integer load values is a constant plus a nonnegative linear combination of the identity and these integer hinges. The constant is integrated against the same total mass r on both sides. The active labels of each depth have the same cap; grouping the nested comparison by depth gives (C1). This proves the inequality without any actual nestedness or identification of projected labels.

Jensen gives h(Σ_{e≤k}A_e)≤(k+1)⁻¹Σ_{e≤k}h((k+1)A_e). Extend Θ and Γ homogeneously to finite positive measures by maximizing, respectively, their hinge and square integrals over complete old layouts. Integrating (C1), then taking the maximum over enlarged layouts, yields

\[
 \Theta_{\rho R}(t)
 \le\sum_{k=0}^H(k+1)\Theta_{w_k\rho}(t/(k+1)), \tag{C2}
\]
\[
 \Gamma_{Qp^H}(\rho R)
 \le\sum_{k=0}^H(k+1)^2\Gamma_Q(w_k\rho). \tag{C3}
\]

These use the same physical finite measure. Empty rows contribute zero. No product structure of ρ, constant r, or preserved normalized prefix cap is assumed.

For a normalized distortion kernel relative to the actual pure-p survivor probability U_p, let B_x be the actual mixed union, α=U_p(B_x), and 0≤δ(x)<1. With θ=min(α,δ), its restriction to the good points is exactly

\[
 R_x(dy)=\frac{1_{B_x^c}(y)}{1-\theta(x)}U_p(dy),\qquad
 r(x)=1-\frac{(\alpha(x)-\delta(x))_+}{1-\delta(x)}.
\]

Its actual unnormalized prefix maxima may be used as a_e. Those maxima decrease with depth. Row-dependent thresholds are valid here because x is the entire previous history.

At a subsequent odd prime q, coprime to Qp, use one fixed threshold 0≤δ_q<1 and the actual pure-q base. Complete separately for each original q-exponent, with weights (q−1)q⁻ᶠ. Pure q classes are already absent, so completion subtracts exactly **one** unit cofactor. Jensen and the pure-q cylinder cap give the unnormalized assigned charge

\[
 b_q\le\frac{\Theta_{\rho R}(1+(q-2)\delta_q)}{(q-2)(1-\delta_q)}. \tag{C4}
\]

Combining with (C2) is valid. If the total surviving mass is s>0, normalized charges and moments divide by s. The comparison does not supply a fixed-dimensional closed recurrence.

### Relation to the existing square transfer

The dossier's W1 and `PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le` already give, after normalizing each nonempty row and using old measure rρ,

\[
 \Gamma_{Qp^H}(\rho R)
 \le\Gamma_Q(r\rho)+\sum_{e=1}^H(2e+1)\Gamma_Q(\beta_e\rho). \tag{C5}
\]

For empty rows choose any normalized kernel; its old mass is zero. Since Γ is subadditive on positive measures, r=Σ_kw_k and β_e=Σ_{k≥e}w_k imply

\[
 \Gamma_Q(r\rho)+\sum_{e=1}^H(2e+1)\Gamma_Q(\beta_e\rho)
 \le\sum_k(k+1)^2\Gamma_Q(w_k\rho).
\]

Thus (C3) is **not** a stronger second-moment result than W1. The useful extension is the full convex/hinge formula (C2), together with its row-mass dependence and the following sharp obstruction. Existing full-label rearrangement is also present in `ConditionalComparison/CappedGainRearrangement.lean` (`finite_run_rearrangement`, `depth_rearrangement`) and the finite Abel formulas in `Runs.lean`; no claim of a new underlying rearrangement theorem is made.

## Sharp geometric cap envelope

Fix a row and suppose a_e=c p⁻ᵉ. Feasibility requires r≤c (sum the leaf caps), in addition to 0≤r≤1; the usual c≥1 implies this. For head layers all having common value z≥0 at the selected point, the exact cap-only upper envelope is

\[
 C_r(h;z)=r h(z)+\sum_{e=1}^H\min(r,a_e)
                    [h(z(e+1))-h(ze)]. \tag{C6}
\]

To attain it, give a distinguished nested prefix chain masses β_e=min(r,a_e). At each branch distribute the excess β_e−β_{e+1} among the other p−1 children, and distribute each such off-chain mass uniformly below that child. The required capacity condition follows from β_e≤p a_{e+1}; the root uses r≤p a₁=c. Every deeper cap holds. Select all test p-prefixes along the chain, so (C1) is an equality and summation by parts gives (C6).

For feasible r₀≥r≥a₁, the entire reduction is (r₀−r)h(z). Hence every hinge with threshold T≥z is unchanged. For the square cost,

\[
 C_r(u^2;z)=z^2[r+\sum_{e=1}^H(2e+1)\min(r,a_e)].
\]

On a_{j+1}<r<a_j the derivative of the bracket is (j+1)²; above a₁ it is only1. Actual geometry may reduce a_e independently, but residual row-mass loss alone need not do so.

## The actual 45-class family

The exact checker constructs all45 original `(modulus,residue)` pairs and independently evaluates the physical chain.

1. For every nonunit d|315, forbid0 mod d. The survivors are the144 units modulo315, carrying the uniform head law μ.
2. Forbid0 mod11. For d in the ordered list (3,5,7,15,21,35,105,9,45), assign distinct11 digits1,…,9 and head residue1 mod d. Use δ₁₁=2/5.
3. Forbid0 mod31. Let w=1891 mod3465, so w=1 mod315 and w=10 mod11. For the23 nonunit divisors d|3465 in increasing order assign31 digits1,…,23, and old residue w mod d. Use δ₃₁=2/5.

All45 moduli are distinct, nontrivial and odd; their lcm is107415. The largest modulus has five distinct prime factors. No three-factor hypothesis is used.

Let ℓ(x)=Σ_{d|315}1_{x=1 mod d}. Its only values exceeding6 occur at x=1,106,211, where they are12,8,8. The nine active11 labels have count n(x); its complete histogram is

| n | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 9 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| count |45|54|15|19|3|5|2|1|

The pure11 law is uniform on ten digits. Thus α₁₁=n/10 and the exact conditional assigned charge is (n−4)₊/6. Averaging gives Pr(B₁₁)=1/54. At x=1,106,211, n=9,7,7, so the good-row masses are1/6,1/2,1/2. Digit10 is always good and has mass1/6 in every one of these rows, both before and after killing.

The coherent old load for the next prime is L(x,y)=ℓ(x)(1+1_{y=10}). Because all31 colours differ, the actual number of active mixed31 colours is L−1. There is one missing unit. The pure31 law has30 digits, so the exact conditional charge is (L−13)₊/18. It is positive only at y=10 above the three specified head points. Therefore

\[
 \Pr(B_{31})
 =\frac1{144}\frac16\left(\frac{11}{18}+\frac3{18}+\frac3{18}\right)
 =\frac{17}{15552}.
\]

Every B₁₁ point has y≠10, where the next charge is zero. Hence

\[
 \Pr(B_{11}\cap B_{31})=0,
 \qquad (\mu K_{11}|_{B_{11}^c})K_{31}(B_{31})=\frac{17}{15552}.
\]

Every head point carrying positive later charge was positively depleted at11, but the later unnormalized charge did not decrease. Normalizing the good restriction multiplies by54/53, giving

\[
 \frac{54}{53}\frac{17}{15552}=\frac{17}{15264}.
\]

This is a strict increase. The normalization is ν=(54/53)ρ for ρ=μK₁₁ restricted to B₁₁ᶜ.

At every finite11 height H, adding the pure classes0 mod11ᵉ for2≤e≤H changes no pure survivor root. Above x=1 the free root10 and every prefix inside it have mass1/[6·11ᵉ⁻¹], before and after killing. These are also the maximum actual depth-e prefix masses. The total row mass falls from1 to1/6. A complete test coherent with x=1 and that free11 root has load12 on every deleted point, so **all real hinge thresholds at least12** have unchanged unnormalized integrals. This proves the all-height statement. The checker additionally reconstructs all prefix maxima and every hinge segment endpoint for heights1,2,3.


The existing verifier and fixed certificate reconstruct all45 actual classes, their CRT unions, normalized kernels, total chain mass and all stated charge quantities using exact rational arithmetic. They also check the finite prefix instances at heights1 through3; the preceding argument supplies the all-height result. The comparison and obstruction are ordinary proofs, not end-to-end Lean verification or a new noncoverage cutoff.

## A block transfer retaining row, column and cell compatibility

This gives a universal finite two-coordinate transfer inequality and an
actual 11/13 example where it is strictly stronger than sequential scalar
prefix completion. It does not give a universal numerical head Gamma or
an odd-covering conclusion. All mathematical proof below is ordinary
finite convexity; the witness is checked by exact arithmetic, not Lean.

### Existing results and the retained distinction

The searched project already has the one-coordinate weighted-prefix
theorem PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le,
the dossier's W 1--W 5, the full convex comparison C 1--C 5 in the marked-head
note, and the actual two-prime root estimates G 1/ZG 3. These retain old-point
weights or separate prefix caps. No two-coordinate surviving-grid maximum
was identified in the searched congruence files and odd-covering notes.
The distinction below is compatibility: maxima for a row, a column, and
their intersection cannot always be attained together on the actual grid.

### Universal finite-height statement

Let S be an old supported finite set with a probability mu, and let q,r
be new coprime primes. Fix finite heights H,K. Remove the actual pure-q
and pure-r classes, giving coordinate sets P and R; their uniform product
is the new base. Keep every other original label (d,a,b), representing
old divisor d and new prime exponents a,b, distinct. At old point x define
T_x subset P times R by deleting exactly the new original rectangles
whose old congruence cylinder contains x. Thus a label containing both
new primes deletes a cell-prefix rectangle, an axis label deletes a strip,
and overlaps are counted as unions. Put

    N_x=|T_x|,   Z=sum_x mu(x) N_x.

Assume Z>0 and globally condition mu times the uniform product on these
actual survivors. The resulting law can change the old marginal.

For a complete test layout and exponent pair (a,b), let A_(a,b)(x) be
the complete old test load obtained by summing its old cofactor indicators.
Its individual labels can have different new prefixes. For nonnegative
numbers v_(a,b), define

    B_h(T;v)=max_(one prefix rectangle C_(a,b) for each pair)
               sum_(y,z in T) h(sum_(a,b) v_(a,b) 1_C_(a,b)(y,z)),

where C_(0,0) is the entire grid. Empty prefixes and prefixes outside the
pure survivor sets are permitted. Then for every increasing convex h,

    E_survivors h(L)
      <= Z^(-1) sum_x mu(x) B_h(T_x; (A_(a,b)(x))).                 (B 1)

The assertion is simultaneous for the one actual conditioned law. It
does not replace original labels by a family of projected distinct moduli.

Proof: at fixed x, group active old indicators by their selected new
prefix within each exponent pair. Their nonnegative amounts have total
A_(a,b)(x). The sum of h over T_x is convex in the allocation vector for
one pair while all other allocations are fixed. Allowing arbitrary
nonnegative allocations with this same total enlarges the feasible set:
individual labels need not be splittable, and the pointwise maximizing
allocation need not come from one common global test layout. Both facts
are harmless for this upper bound. A convex function on a
simplex is at most its maximum at a vertex, which places the whole amount
in one prefix. Apply this successively to the finitely many exponent pairs,
then integrate. Normalization is exactly Z; the pure-product size cancels.
This argument needs neither independence of the old test loads nor a
nonempty fibre at every old point.

Unlike replacing every rectangle by an independent prefix-mass cap, B 1
preserves the common actual grid until all cross terms are formed. The
operator can be expensive at large heights; no fixed-dimensional closure
or arbitrary-height numerical bound is claimed.

### Explicit one-height square operator

For H=K=1 write A,B,C,D for the old test loads at exponent pairs
(0,0),(1,0),(0,1),(1,1). Let T be the actual surviving grid, N=|T|, and
let n_i,m_j be its row and column counts. If N=0 set F_T=0. Otherwise
the convex concentration above gives the explicit expression

    F_T(A,B,C,D)=N A^2 + max_(i in rows,j in columns,z in T) [
        n_i (2 AB+B^2) + m_j (2 AC+C^2)
        +2 BC 1_((i,j) in T) +2 AD+D^2
        +2 BD 1_(z_row=i) +2 CD 1_(z_col=j)].                       (B 2)

Here i is any row, j any column, and z any surviving cell; i,j need not
themselves form a surviving cell. The notation max means independent
choices of i,j and z with only z constrained to T. The D contribution may
be placed in T because h is increasing. Formula B 1 with h(t)=t^2 therefore
has right side Z^(-1)sum_x mu(x)F_(T_x)(A(x),B(x),C(x),D(x)).

This is an upper bound for each fixed four old test layouts. Taking the
maximum over those layouts gives a universal second-moment bound, but
that old-layout optimization has not been evaluated for arbitrary families.

Independent scalar intersection caps instead give

    G_T=N A^2+n_max(2 AB+B^2)+m_max(2 AC+C^2)
        +2 BC+2 AD+D^2+2 BD+2 CD.                                   (B 3)

Always F_T<=G_T. Equality can fail because the row and column maxima
and the three positive mixed intersections must share one grid.

### Strict gain in a complete original 315 times 11 times 13 family

Use the 86-point old survivor family

    (3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
    (21,1),(35,9),(63,52),(105,4),(315,142).

Let d run increasingly through

    1,3,5,7,9,15,21,35,45,63,105,315.

All new old cofactor conditions are x=2 mod d. For the 11 axis, use digit 0
for d=1 and for the last four nonunit cofactors; for the first seven
nonunit cofactors use digits 4,5,...,10. For the 13 axis, similarly use
digits 4,5,...,12 for the first nine nonunit cofactors and digit 0 otherwise.
For the 143 d cross labels, use respectively

    (1,1),(2,2),(2,3),(3,2),(3,3)

at the first five cofactors d=1,3,5,7,9, and use (0,0) for all others.
CRT defines one residue for each modulus. Together with the old classes,
these are exactly all 47 nonunit divisors of 45045, without duplication.

At old point x=2, the surviving grid is exactly

    T={(1,2),(1,3),(2,1),(3,1)}.

Its unique largest row and largest column both have size 2, but their
intersection (1,1) is forbidden. With A=B=C=D=1, the exact block maximum
is 22, attained for example by row 1, column 2, and cell(1,2). The independent
intersection-cap bound is 25.

For comparison with sequential W 1 scalar completion, let k be the number
of nonempty rows. Its marginal old square contribution is N+3 n_max.
Under the conditional-prefix weight, every nonempty row has mass 1; the
two completed old layouts each have maximum square k+3. The one-height
W 1 coefficient therefore gives

    N+3 n_max+3(k+3).

This is 28 on T. Reversing the prime order also gives 28. Thus the strict
gain persists even after using actual conditional row caps in sequential
scalar completion; it is not an improvement obtained by changing the law.

The exact verifier also checks all 86 old points of this one actual family.
There are 7128 complete survivors. Take every nonunit old test cofactor
in each of the four groups to be its original forbidden residue. Then
A=B=C=D=1 throughout the old survivor set, so the same comparison applies
to one legitimate set of old test blocks. Summed square numerators are

| Bound | Numerator | Divided by 7128 |
|---|---:|---:|
| Joint surviving-grid operator | 12618 | 701/396 |
| Independent row/column/intersection caps | 12621 | 4207/2376 |
| Sequential scalar completion, either order | 12624 | 526/297 |

The extra compatibility gain beyond independent intersection caps is
1/2376. The gain over sequential scalar completion is 1/1188. Directly
maximizing the three global unit-cofactor test choices gives square
numerator 12522, so the joint pointwise bound itself is not asserted sharp
after integration. In particular, these numbers are not a Gamma bound
for all old test layouts of the family.

## Exact compatibility rebate for a two-prime block

For a nonempty finite grid T, let n_i,m_j be its row and column degrees,
with maxima n_max,m_max. For nonnegative real A,B,C,D, set

    a=B(2A+B),       b=C(2A+C),       e=2BC+2D min(B,C),
    P=a n_max+b m_max,
    E=max_((i,j) in T) (a n_i+b m_j).

The operators B 2 and B 3 satisfy the exact identity

    G_T-F_T = min(e,P-E)
            = min(e, min_((i,j) in T)
                         [a(n_max-n_i)+b(m_max-m_j)]).             (R1)

Thus degrees and one scan of T suffice to evaluate the joint operator.

To prove this, put u=2BD, v=2CD, c=2BC and
K=|T|A²+2AD+D². If the selected row and column intersect in T, place
the D-cell at that intersection. The maximum of these choices is
K+E+c+u+v. If their intersection is absent, a surviving D-cell can lie
in at most one of them, giving at most K+P+max(u,v). This second bound
is attained by a maximum-degree row and column whenever their intersection
is absent: both degrees are positive, so a D-cell can attain whichever
of u,v is larger. If their intersection survives, the first branch
already dominates. Consequently

    F_T=K+max(E+c+u+v, P+max(u,v)),
    G_T=K+P+c+u+v.

Subtracting proves R1, including zero coefficients and empty ambient
rows or columns. If B=0 or C=0, the rebate is zero. Otherwise a,b,e>0,
so strict gain occurs exactly when no surviving edge joins a
maximum-degree row to a maximum-degree column. This criterion is
independent of A and D.

For complete old test blocks A,B,C,D≥1, one has a,b≥3 and e≥4. Let
I(T) indicate that T is nonempty and has no such maximum-degree edge.
Integer degree deficits give

    G_T-F_T ≥ min(e,min(a,b)) I(T) ≥ 3 I(T).                      (R2)

Give empty grids zero contribution. With the same actual globally
conditioned law and Z from B 1,

    sum_x mu(x)F_(T_x)/Z
      ≤ sum_x mu(x)G_(T_x)/Z - 3 mu{x:I(T_x)=1}/Z.                (R3)

The event I(T_x) depends only on the actual surviving grid, so this
subtraction remains valid after maximizing over all complete old layouts.
No positive universal lower bound on its mass is asserted. For example,
put each new mixed original class inside an already forbidden pure class.
The distinct moduli remain present, but every surviving grid is a
rectangle and I(T_x)=0.

The exact verifier checks 77 targeted grid/coefficient cases against
literal allocation squares. They include both positive branches of the
minimum, their equality boundary, zero coefficients, rational coefficients,
empty ambient rows and columns, and the actual four-cell witness with
F=22,G=25. The preceding proof supplies the arbitrary nonnegative-real
scope. The final min/max subtraction reuses the standard order identity;
no standalone Lean wrapper is introduced.

## A nonuniform law for a block with zero compatibility rebate

There is a supported law that improves the complete second moment even
when the uniform grid's rebate R1 is zero. For every positive Q coprime
to143 and every probability mu on residues modulo Q, the explicit law rho
below satisfies the exact identity

    Gamma_(143Q)(mu × rho)
      = (6386411/3927000) Gamma_Q(mu).                            (NT1)

This allows every complete old test layout and arbitrary old prime-power
heights. The new prime heights at11 and13 are both one.

Use the actual new classes0 mod11,0 mod13 and1 mod143. Index the nonzero
11-residues by0,...,9 and the nonzero13-residues by0,...,11. The surviving
grid is

    T=({0,...,9} × {0,...,11}) minus {(0,0)}.

Its uniform law has exact factor194/119 in NT1. Every maximum-degree row
meets a maximum-degree column in a surviving cell, so R1 is zero for
all four nonnegative old loads. Instead assign

    rho(i,j)=a=2119/238000       if exactly one of i,j is zero,
             c=9781/1178100     if both i,j are positive.

Equivalently a=1/119+1/2000 and c=1/119−20/(99·2000). There are20adjacent
cells and99interior cells, so20a+99c=1. Both weights are positive and
the missing cell has mass zero. The improvement in the exact factor is

    194/119−6386411/3927000 = 131/33000 >0.                        (NT2)

### A common quadratic bound for all four old layouts

Let R_i and C_j be rho's row and column masses. For a selected row i,
column j and surviving cell z, the indicators1, row i, column j and
cell z have Gram matrix

    M=[[1,R_i,C_j,rho(z)],
       [R_i,R_i,rho(i,j),rho(z)·1[z_row=i]],
       [C_j,rho(i,j),C_j,rho(z)·1[z_col=j]],
       [rho(z),rho(z)·1[z_row=i],rho(z)·1[z_col=j],rho(z)]].

Choose the interior aligned configuration i=j=1,z=(1,1), and denote
its matrix by M*. Put R=a+11c and C=a+9c. The four row sums of M* are

    lambda=(1+R+C+c, 2R+2c, 2C+2c, 4c).

Simultaneously for every row, column and cell choice,

    M ≤ diag(lambda) in positive-semidefinite order.              (NT3)

The rational certificate proves NT3 by exact LDLᵀ factorizations of
its20distinct matrix differences. For each one the verifier reconstructs
every entry and checks every diagonal pivot is nonnegative, including
the remaining column at a zero pivot. All14280choices are accounted for;
no floating-point eigenvalue estimate is used. The coefficient sum is

    sum(lambda)=6386411/3927000.

Fix any complete test layout modulo143Q. At an old point x, let A_g(x)
be the complete old cofactor load in exponent group
 g=(0,0),(1,0),(0,1),(1,1). The new prefixes of individual old cofactors
may differ. The convex allocation argument of B 1 remains valid with
rho in place of counting measure: for an upper bound, concentrate each
group's nonnegative amount into one row, column or cell. Prefixes outside
support may be moved into support since the squared nonnegative load
is increasing. Thus, at this same old point,

    E_rho L(x,·)² ≤ max_(i,j,z) A(x)ᵀ M A(x)
                  ≤ sum_g lambda_g A_g(x)².

Every A_g is a complete Q-divisor layout. Integrating under mu gives
at most sum(lambda) Gamma_Q(mu), proving the upper bound of NT1 for
all old layouts simultaneously.

For equality, choose an old layout attaining Gamma_Q(mu); the finite
residue-choice set ensures it exists. Reuse that layout in all four
exponent groups with the fixed interior aligned new row, column and
cell. CRT gives one residue for every divisor of143Q. Its complete load
factors as the old load times(1+row indicator+column indicator+cell
indicator). The latter's square integral is the sum of entries of M*,
namely sum(lambda). This gives the reverse bound of NT1.

For the uniform law on T, the interior aligned Gram matrix dominates
all other Gram matrices entrywise. Its row-sum diagonal majorant follows
from the weighted square inequality, and the same coherent test attains
it. This proves its exact factor194/119. Hence NT2 compares two complete
supported laws for the same actual family, including the full old-layout
optimization.

### Actual arithmetic consumer and boundary

Adjoin(11,0),(13,0),(143,1) to the sharp315head's eleven original classes.
These14moduli are distinct, nontrivial and odd, with lcm45045. The full
survivor set has86·119=10234points. Keeping its old uniform law and using
rho on the new block gives the exact value

    Gamma45045=(6386411/3927000)(1131/86)
              =2407676947/112574000,

compared with109707/5117 for the fully uniform survivor law. The verifier
uses the already computed sharp315result, reconstructs every actual
survivor in one full period, and checks the product support.

This supplies one positive case for handling zero compatibility rebate;
it does not show that every zero-rebate grid admits this improvement.
Additional actual classes involving the new primes need not preserve
this grid. No unrestricted tail cutoff or arbitrary-height11/13block
bound follows from NT1.

The repository's B 1 convex allocation proof is reused directly; the
new quantitative input is the common rational quadratic bound NT3.
[Hough–Nielsen, Lemmas5–6](https://arxiv.org/html/1703.02133) controls
moments by maximal biases and good-fibre proportions.
[BBMST, section5.3](https://arxiv.org/html/1901.11465) constructs nonuniform
survivor laws by optimizing actual configurations. These provide the
public precedents; neither cited passage supplies NT1. The result here
is an ordinary universal proof with an exact finite certificate, not
Lean certification.
