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

## Rectangular matching holes: a symbolic common quadratic bound

The preceding finite construction extends to every m×n rectangle with
m,n≥3 and a matching of k deleted cells, where0≤k<min(m,n). Relabel the
holes as(0,0),…,(k−1,k−1), and call their rows and columns affected. Put

    S=m+n,  V=mn−k,  H=k(m+n−k−1),
    C=max(m+n+2k−1,2m,2n),  0≤epsilon≤1/(9C),
    c=1/(V+H epsilon),  a=(1+epsilon)c.

Assign mass zero to holes, mass a to every surviving cell touching an
affected row or column, and mass c elsewhere. There are H cells of the
first positive type and(m−k)(n−k) of the second; their masses sum to one.
Here epsilon is a ratio perturbation, distinct from NT1's additive
probability perturbation. The explicit interval is sufficient; it is
not sharp and does not recover NT1's larger specific perturbation.

Untouched rows have mass c(n+k epsilon), untouched columns have mass
c(m+k epsilon), and untouched cells have mass c. Define

    lambda=(1+c(S+1+2k epsilon),
            2c(n+1+k epsilon), 2c(m+1+k epsilon), 4c).

For every selected row i, column j and surviving cell z, its four
indicator Gram matrix M, as in NT3, satisfies

    M ≤ diag(lambda).                                           (MT1)

All four coefficients depend only on(m,n,k,epsilon), including when
m≠n. They do not depend on hole positions or selected coordinate labels.

### A uniform Laplacian estimate

Divide by c and write D(epsilon)=(diag(lambda)−M)/c=D_0+epsilon Delta.
At epsilon=0, let h_i,h_j indicate whether the selected row and column
are affected; put u=1[(i,j) survives],v=1[z_row=i],t=1[z_col=j]. The
unnormalized row and column masses are n−h_i,m−h_j. Decompose D_0 into
the graph Laplacian whose off-diagonal edge weights are(M/c)_ab plus
the diagonal matrix of row-sum slacks. Those slacks are exactly

    h_i+h_j,  2+2h_i−u−v,  2+2h_j−u−t,  2−v−t.                 (MT2)

They are nonnegative integers, and all vanish exactly for an untouched
aligned row, column and intersection cell. In that exceptional case,
lambda is the row-sum vector of M at every epsilon, so D(epsilon) is
itself a nonnegative weighted graph Laplacian for every epsilon≥0.

Otherwise at least one slack is at least one. The three Laplacian edges
from coordinate0 have weights n−h_i,m−h_j,1, each at least one. For
some ell∈{0,1,2,3}, therefore,

    xᵀD_0x ≥ sum_(j=1)^3(x_0−x_j)²+x_ell² ≥ ||x||²/9.           (MT3)

For the last inequality, express x in coordinates
(x_ell,x_0−x_1,x_0−x_2,x_0−x_3). The inverse transformation has squared
Frobenius norm7 for ell=0 and9 otherwise; rowwise Cauchy–Schwarz proves
MT3. This bound is independent of the grid dimensions.

The unnormalized row derivative r_i' is n−1 on affected rows and k
otherwise; the column derivative q_j' is m−1 or k. Every cell-weight
derivative w' is zero or one. Consequently

    Delta_00=2k, Delta_01=−r_i', Delta_02=−q_j', Delta_03=−w_z',
    Delta_11=2k−r_i', Delta_22=2k−q_j', Delta_33=−w_z',
    Delta_12=−w_ij', Delta_13=−w_z'v, Delta_23=−w_z't.

Its absolute row sums are bounded respectively by
m+n+2k−1,2n,2m,4. For example, row1 is at most r_i'+|2k−r_i'|+2:
the cases r_i'=k and r_i'=n−1 give either2k+2 or2n−2k, both at most2n.
The other bounds follow directly from k≤min(m,n)−1. Thus every row sum
is at most C. Applying2|x_ax_b|≤x_a²+x_b² gives

    |xᵀDelta x|≤C||x||²,
    D(epsilon)≥(1/9−epsilon C)I≥0

for all nonexceptional configurations. Together with the aligned
Laplacian case, this proves MT1 symbolically, without a grid enumeration.

### Exact factor, positive gain and moving fibres

The coefficient sum and its uniform-law counterpart are

    F_k=1+[3(S+3)+6k epsilon]/[V+H epsilon],
    U_k=1+3(S+3)/V.

Their exact difference is

    U_k−F_k=3k epsilon B/[V(V+H epsilon)],
    B=m²+n²+(2−k)(m+n)−k−3>0.                                  (MT4)

Indeed m=k+1+x,n=k+1+y with x,y≥0 gives
B=5k+3+(k+4)(x+y)+x²+y². Hence the gain is strict for k≥1,epsilon>0.
At epsilon=1/(9C), it is3kB/[V(9CV+H)]. For k=0 the law is uniform,
independent of epsilon, and F_0=U_0=(1+3/m)(1+3/n).

The B1 convex allocation argument and MT1 apply to all four complete
old-cofactor groups. For a fixed grid, the aligned untouched test
attains the upper bound by reusing one maximizing old layout in all
four groups, exactly as in NT1. Thus, for every old law mu,

    Gamma_new(mu×rho)=F_k Gamma_old(mu).                          (MT5)

This arithmetic statement uses a coprime pair of new height-one primes
with m,n actual available residue counts; old heights are unrestricted.
For the uniform punctured grid, the aligned untouched Gram matrix
entrywise dominates every other Gram matrix. The same allocation and
row-sum argument gives its exact factor U_k, proving that MT4 compares
complete laws on the same support, including the old-layout maximum.

If instead each old point x has available row and column sets of the
same sizes m,n and at most k matching holes, extend its matching to
exactly k by pairing unused rows and columns. Extra virtual holes only
restrict support. Construct rho_x after any fibrewise relabeling. Each
rho_x sums to one, so nu(x,y)=mu(x)rho_x(y) preserves the old marginal.
Because lambda is common to all fibres, integration of MT1 gives

    Gamma_new(nu)≤F_k Gamma_old(mu).                             (MT6)

The matching, row and column sets, and virtual holes may all move with
x. Equality is not asserted: one global test layout need not align in
every fibre. MT4 does not compare the padded law with each original
fibre's uniform law when it originally had fewer than k holes.

### Keeping the actual hole count gives an additive saving

Fix1≤K<min(m,n) and one0≤epsilon≤1/(9C_K). If fibre x has exactly k_x
matching holes with0≤k_x≤K, use its own law without virtual holes. Put

    D_j=mn−j+epsilon j(S−j−1), N_j=3(S+3)+6epsilon j, F_j=1+N_j/D_j.

The positive denominators strictly decrease, since
delta_j=D_j−D_(j+1)=1−epsilon(S−2j−2)>0. Each lambda coordinate has a
nondecreasing positive numerator and this decreasing denominator, so
lambda_g(j) increases. Every complete old load A_g includes its unit
cofactor and is at least one. Therefore, pointwise,

    sum_g lambda_g(k_x)A_g²
      ≤sum_g lambda_g(K)A_g²−(F_K−F_(k_x)).

After integration this strengthens MT6 to

    Gamma_new≤F_K Gamma_old−E_mu[F_K−F_(k_x)].                   (MT7)

The successive differences F_(j+1)−F_j have numerator
T_j=6epsilon D_j+N_j delta_j and denominator D_jD_(j+1). Their
numerators increase by T_(j+1)−T_j=2epsilon N_(j+1)≥0 and their
denominators decrease. Thus every difference is at least

    gamma=F_1−F_0
      =[6epsilon mn+3(S+3)(1−epsilon(S−2))]
        /[mn(mn−1+(S−2)epsilon)]>0,

and

    Gamma_new≤F_K Gamma_old−gamma(K−E_mu k_x).                  (MT8)

This holds also at epsilon=0. K=0 uses the full-rectangle bound alone.

For actual mixed moduli qrd with distinct old cofactors d, each class
activates on one old residue. The number of distinct forbidden cells
k_x is at most this activation count, which is at most one complete
old test load L_cross(x), obtained by filling any missing cofactors.
Writing R_mu for the sum of nonunit old cylinder maxima gives
E_mu k_x≤E_mu L_cross≤1+R_mu. Hence, whenever the remaining holes are
a partial matching and their count is at most K, MT8 gives

    Gamma_new≤F_K Gamma_old−gamma(K−1−R_mu)_+.                  (MT9)

This uses actual cofactor labels. It does not assume globally distinct
new digits, and it retains the hypotheses of fixed available dimensions
and a matching within each fibre.

### Arbitrary holes via fixed row and column deletion budgets

Suppose an ambient M×N fibre excludes at most a entire rows, b entire
columns and L individual cells. For L≥1 choose any fixed nonnegative
A,B with A+B≥L−1 and m=M−a−A≥3,n=N−b−B≥3. First pad the original
axis exclusions to exactly a,b. Of the remaining point holes, select
all but at most one; there are at most L−1 selected holes. Assign at
most A to their row endpoints and at most B to their column endpoints,
then delete those endpoints. Repeated endpoints save budget. Pad these
additional deletions to exactly A rows and B columns. The remaining
m×n rectangle has at most one hole. If necessary, add one virtual hole.

The k=1 law now has common lambda across all such fibres, is supported
on the original survivor set, and preserves the old marginal; MT6
applies. Endpoint choices and all padded deletions may vary with x.
For L=0, use the k=0 full rectangle after padding the original axis
exclusions. These are support constructions, not comparisons with the
uniform laws on the original irregular fibres.

The standard-library verifier checks10 sparse polynomial identities,
all32 abstract Boolean incidence/slack patterns in MT2, and the four
exact anchor transformations in MT3. It adds no concrete grid instances.
The universal inequalities and support arguments above are ordinary
proofs, independently reviewed; they are not Lean certification. Full
matchings k=min(m,n), higher new prime heights and varying dimensions
without fixed deletion budgets are outside the stated hypotheses. No
unrestricted tail cutoff follows from these bounds.

## Arbitrary-height transfer for matching kernels

Let Q be the old period, q and r new distinct primes coprime to Q, and
H,J≥1 finite. Let μ be a probability on the complete old survivors.
For every complete old test load A suppose

    Eμ A ≤ M,       Eμ A² ≤ G.

The first bound can be M=1+R_old (the sum of old nonunit cylinder maxima
plus one), or any sharper validated common first-moment bound. It can
always be tightened to min(M,sqrt(G)); since A≥1, G≥1.

Suppose each old point x has a first-q/r-digit law ρ_x avoiding all actual
classes whose new exponents are at most one. Assume these laws share
row, column and atom caps R,C,a and a common diagonal quadratic bound
whose coefficient sum is F. A valid improvement of the complete low
square may also be retained:

    Γ_(Qqr)(μρ_x) ≤ C0 := FG−η,       η≥0, C0≥1.                 (HT1)

Extend this single probability law uniformly in the additional H−1
q-digits and J−1 r-digits. Write

    u_q = Σ_(t=1)^(H−1) q^(−t),
    v_q = Σ_(t=1)^(H−1) (2t−1)q^(−t),
    w_q = 4u_q+v_q,

and similarly for r. Empty sums are zero. Define

    Λ=M[(R+a)u_q+(C+a)u_r+a u_q u_r],                           (HT2)
    E=(R+3a)w_q+(C+3a)w_r+a w_q w_r.                         (HT3)

For every distinct-original-modulus family with old factors dividing Q
and new exponents bounded by H,J, provided its low classes are already
avoided and Λ<1, the uniformly lifted law gives positive mass to the
complete survivor set. Conditioning that same law on all actual high
class exclusions yields

    Γ_(Q q^H r^J)(μ_final)
      ≤ [C0+EG−Λ]/[1−Λ]
      = [(F+E)G−η−Λ]/[1−Λ].                                  (HT4)

No nonempty lift over every old x is required; the final old marginal
can change. The actual high classes can overlap and can have repeated
new prefixes. Original modulus labels, not projected distinctness, are
used throughout.

### Proof of the bad-mass bound

At x a prescribed q-prefix of depth b≥1 has mass at most R q^(−(b−1));
an r-prefix has the analogous cap, and a prescribed positive-depth pair
has mass at most a q^(−(b−1))r^(−(c−1)). This follows from uniformity only
in the higher digits, without any independence hypothesis on ρ_x.

For each fixed new exponent pair, the actual old cofactors d occur at
most once because the original moduli d q^b r^c are distinct. Their
active old indicators form a partial complete old test load, so their
mean is at most M. Sum the prefix caps for b≥2,c=0; b=0,c≥2; and b,c≥1
with at least one exponent≥2. The sums are respectively

    R u_q, C u_r, a(u_q+u_r+u_q u_r).

The union bound proves that the actual deleted high mass β is at most Λ.
This argument includes the pure high prime-power classes (d=1) and does
not assume disjoint forbidden classes.

### Proof of the full-square bound

Group a complete fine test layout by its new exponent pair e=(b,c).
The sum A_e(x) of the old cofactor indicators is one complete old load.
For any e,e′, after expanding their two grouped fine loads, every new
prefix intersection is either empty or has the cap at exponent pair
max(e,e′). Therefore its integrated contribution is at most

    κ_(max(e,e′)) Eμ[A_e A_e′] ≤ κ_(max(e,e′)) G.

The last inequality is Cauchy–Schwarz; no independence between old
layouts is used. Keep the four low groups b,c∈{0,1} together and apply
(HT1) to them, instead of replacing their intersections by separate caps.
All remaining pairs have at least one maximum exponent at least two.

There are 2b+1 ordered pairs of exponents in {0,…,H} whose maximum is b.
Thus Σ_(b=1)^H(2b+1)q^(−(b−1))=3+w_q. Summing all the high pairs gives

    Rw_q+Cw_r+a[(3+w_q)(3+w_r)−9]=E.

Consequently the square of every fine layout has integral at most C0+EG.
Every complete fine load is at least one, so deleting high mass β saves
at least β from that integral. After conditioning,

    E_final L² ≤ (C0+EG−β)/(1−β)
                ≤ (C0+EG−Λ)/(1−Λ),

because C0+EG≥1. This is the repository's existing minimum-load deletion
saving/N9, reused on the present law, and proves (HT4).

### Matching row, column and atom caps

For m,n≥3, 0≤K<min(m,n), and 0≤ε≤1/(9C_K), put

    S=m+n, V=mn−K, H0=K(S−K−1),
    C_K=max(S+2K−1,2m,2n), D=V+H0ε, c=1/D,
    R=c(n+Kε), C=c(m+Kε),
    a=(1+ε)c if K≥1, and a=c if K=0,
    F=1+c[3(S+3)+6Kε].

These are global caps, not just values at selected cells. An affected
row has mass c(n−1)(1+ε), smaller than R by
c[1−(n−K−1)ε]>0; columns are analogous. Every positive atom is c or a.

They apply to fixed-K matching grids and moving matching fibres with
common m,n. If the true matching size is k_x≤K, the denominator D_j
decreases with j and the row/column numerators increase. Hence the K
caps also apply when each fibre keeps its actual k_x and uses MT7–MT9.
In particular retain either

    η=Eμ[F_K−F_(k_x)],

or its validated lower bound γ(K−M)_+, with the same first-moment M
bounding the actual cross-class activation load. This saving is not
discarded by the high extension.

### Exact criterion for preserving the ε improvement

Take a fixed positive matching size k, η=0, and keep the same low
support, old law and uniform higher-digit rule when comparing ε=0 to
ε>0. Let V=mn−k,H0=k(S−k−1), and put

    N0=V+3(S+3)+(n+3)w_q+(m+3)w_r+w_qw_r,
    N1=H0+6k+(k+3)(w_q+w_r)+w_qw_r,
    L0=(n+1)u_q+(m+1)u_r+u_qu_r,
    HT1=(k+1)(u_q+u_r)+u_qu_r.

The conditioned bound is the linear fractional expression

    B(ε)=[GN0−ML0+ε(GN1−ML1)]
          /[V−ML0+ε(H0−ML1)].                                (HT6)

Its ε derivative has constant sign wherever the denominator is positive.
In particular it strictly improves at every positive permitted ε iff

    Δ=(GN0−ML0)(H0−ML1)−(GN1−ML1)(V−ML0)>0.                 (HT7)

This is a checkable symbolic condition, not a consequence of F alone
decreasing: the larger positive atom cap can increase high error terms.
The exact gain is

    B(0)−B(ε)= εΔ / [(V−ML0)(V+εH0−M(L0+εL1))].             (HT8)

### All finite heights for the 11/13 ten-by-twelve one-hole grid

For q=11,r=13,m=10,n=12,k=1 the permitted interval is
0≤ε≤1/216. The improvement is strict for every positive ε in this
interval, every pair of finite heights, and every old first-moment
bound M≤40 (with G≥1 and the stated valid old bounds).

Here 0≤u_q≤1/10,0≤u_r≤1/12 and
0≤w_q≤13/25,0≤w_r≤31/72. Define δb=H0N0−VN1 and
δt=VL1−H0L0. Direct simplification gives

    δb=786−176w_q−216w_r−99w_qw_r ≥115863/200,
    δt=−22u_q+18u_r+99u_qu_r ≤3/2.

The latter maximum is at a corner of the indicated rectangle, since
the expression is bilinear. Also

    L0≤89/40, HT1≤3/8, N0≤186859/900.

The survival denominator is at least

    V+εH0−M(L0+εL1) ≥30+5ε>0.

The derivative is negative exactly when

    G δb(1−ML0/V) > (GN0/V−1)M δt.

If δt≤0 this is immediate, because N0/V≥1. If δt>0, divide by G,
use G≥1, and bound the left side below and the right side above.
Their strict positive margin is at least

    (115863/200)(30/119)
      −(186859/(900·119))·40·(3/2)=295331/7140>0.

This proves the all-finite-height statement; the finitely many regression
calculations are not its proof.

### Arithmetic consumer and exact uniform-in-height bound

Use the repository's sharp supported 315 law, G=1131/86,M=271/86,
and a first-digit 10×12 one-hole grid. Uniform infinite geometric sums
majorize every finite height, and the conditioned bound is increasing
in each u and w on its valid domain. They give

    ε=0:       Γ_final ≤140529901/5778615,
    ε=1/216:   Γ_final ≤6074954672/249830373,

with exact difference

    1271130847931/481224513624465>0.

At ε=1/216 the high deleted-mass bound is
5213769/88490560<1. These values are approximately 24.31895895 and
24.31631750, with gain 0.00264145. They are upper bounds, not asserted
exact Γ values.

One actual consumer is the eleven-class sharp 315 family together with
(11,0),(13,0),(143,1), already constructed in the repository. Adjoin
arbitrarily many distinct actual moduli d·11^a·13^b with d|315 and
a≥2 or b≥2, up to any finite heights, and arbitrary residues. The bound
gives a supported complete survivor probability for every such extension.
It does not say that an arbitrary odd family has this low support shape.
The next result combines this head bound with a full convex comparator and a tail certificate under an explicit low-grid hypothesis.

The matching common diagonal, the sharp 315 law, and the existing minimum-load deletion saving are reused directly. The quantitative step retains the complete low square and charges only higher exponent pairs to prefix caps. The adjacent verifier checks the exact displayed constants, ordered-pair identity and 64 finite-height regressions; the universal statements follow from the ordinary argument above. No new Lean wrapper is added.

## A matching 11/13 head with arbitrary heights and unrestricted tails

**Theorem.** Let a finite family have distinct odd nonunit moduli. Suppose
the full 3/5/7 part of every modulus divides 315, including those moduli
having later prime factors. Choose the canonical old 315 survivor law μ
constructed above. At each x in its support suppose there is a rectangle
A_x×B_x of 10 first 11-digits and 12 first 13-digits, with at most one cell
removed, which avoids all actual head classes whose 11/13 exponents are
both at most one. The row sets, column sets and hole may depend on x.
Then the family does not cover the integers. The 11/13 heights and the
number, heights and interactions of all tail primes at least 17 are
unrestricted.

Pad a missing hole by one virtual hole and use the matching law with
ε=1/216. Extend its higher 11/13 digits uniformly, at their full heights
in the original family, padding an absent coordinate to height one.
Condition on avoiding all actual head classes
having an 11 or 13 exponent at least two. The height theorem gives a single
supported head probability ν with

    Γ(ν)≤J0=6074954672/249830373,
    higher deleted mass≤b=5213769/88490560<1.                 (MH1)

All original labels d·11^a·13^b remain distinct; no assumption about
distinct projected moduli or disjoint high classes is made.

### A full comparator for the same supported law

For comparison, let τ sample x from μ, then sample independently given x
from the uniform laws on A_x and B_x, with uniform higher digits. The
matching atom cap is amax=217/25724, so its density relative to τ before
high-class conditioning is at most 120 amax. Afterwards,

    dν/dτ≤1/ell,
    ell=(1−b)/(120amax)=83276791/89577600.                    (MH2)

This remains true when entire old fibres are killed; ν may have a
different old marginal. The reference law τ is only a comparison law
and need not avoid the matching hole or high classes.

Under τ every positive-depth p-prefix, conditional on the full earlier
history, has mass at most c_p p^(−e), where c11=11/10,c13=13/12. Indeed
the first digit is uniform on 10 or 12 choices and all higher digits are
uniform. The sets may depend on x: their cardinalities give constants
independent of x, and B_x does not depend on the sampled 11-coordinate.

Let independent auxiliary variables N11,N13, independent also of the
published eight-atom old comparator X, have laws

    Pr(Np=1)=1−c_p/p,
    Pr(Np=k)=c_p(p−1)/p^k,  k≥2.

The existing conditional comparison C1 applies successively to 13 and 11.
Keeping the complete old load for each exponent tuple and applying
Jensen after comparison gives, for every complete head test load L and
nonnegative increasing convex h,

    Eτ h(L)≤E h(Y),        Y=X N11 N13.                     (MH3)

For fixed auxiliary values n11,n13 the compared load is a sum of
n=n11n13 complete old loads A_i. Its expectation is bounded by
n^(−1)Σ_i Eμ h(nA_i)≤E h(nX). This explains both the product comparator
and why moving first-digit sets do not require independence of old
test loads. Infinite auxiliary heights majorize every finite physical
height by adding nonnegative completed labels.

For every real z, density domination and (MH3), applied to (h(.)−z)_+,
give

    Eν h(L)≤z+ell^(−1)E(h(Y)−z)_+.                          (MH4)

The exact reference mean and first two masses are

    EY=1574239/412800,
    Pr(Y=1)=6391/92880,       Pr(Y=2)=807835/2173392.

They imply

    Pr(Y>2)=3040019/5433480<ell<86489/92880=Pr(Y≥2).

Let Z be the upper ell-quantile of Y, splitting its atom at 2:

    Pr(Z=2)=1837670057/4615287417,
    Pr(Z=z)=Pr(Y=z)/ell for integer z>2,
    EZ=2+[EY−2+Pr(Y=1)]/ell=3016548085/749491119.             (MH5)

Taking z=h(2) in (MH4) proves Eν h(L)≤E h(Z) for every layout and every
such h. Thus (MH1) and (MH5) bound the same actual supported probability.
The direct square J0 is used separately; it need not equal E[Z²].

### Exact continuation

Use Z in AP2 and J0 in AP5. For any subsequent independent auxiliary
product N, the step charge is bounded by E(ZN−T)_+/s. Its exact
positive-part identity uses the mean and only finitely many low states:

    E(W−t)_+=EW−t+Σ_(d≤t)(t−d)Pr(W=d),       W=ZN.

Here EW is the mean of a fully specified comparator, not an unknown
maximum actual head mean. Thus the caution following AP7 does not
invalidate this calculation. The retained directed-arithmetic
certificate processes 258 primes from 17 through 1693, with global prime
index 264, and gives

    survivor mass≥240819191260897231/10^18,
    Γ_stop≤1169229336100810112644/240819191260897231
           <4856<4868
           <264(log264+loglog264−3)^2.                      (MH6)

The last logarithmic inequality is certified by positive rational
atanh-series lower bounds. In particular, log 264 > 55759/10000 and
log log 264 > 17184/10000 give the shorter lower bound
60855341217/12500000 > 4868. AP6 and the dossier’s T1–T6 transfer into
BBMST Theorem 6.1 therefore continue through every later prime.
The new head construction is supplied here. If the original family ends earlier, the
already positive prefix mass suffices. Finite CRT supplies an integer
outside all original classes, proving the theorem.

The low-fibre hypothesis is the boundary of this result: the argument
does not establish a 10×12 single-hole rectangle for every arbitrary
old head assignment. Higher 3/5/7 exponents also remain outside the
theorem. This is an ordinary proof with an exact arithmetic certificate,
not an unrestricted solution of Erdős #7 or end-to-end Lean verification.

The fixed schedule and its 258 charges are retained in `matching_height_tail17` in the adjacent certificate. The verifier reuses the existing directed convolution and logarithm routines. It retains 384 low states, bounds all omitted states through the full exact mean, and rounds upwards on a grid of 10^-18. Independent arithmetic at scale 10^-24 gives charge < 0.759181, second moment < 1170 and Γ < 4856. These are finite arithmetic certificates for the ordinary proof, not a claim that the selected schedule is optimal.

## Arbitrary point holes and a common diagonal

### Statement

Let m,n>=3, let E be an arbitrary set of k holes in an m by n grid, and
assume k<mn. Write d_i and e_j for the row and column degrees of E. Set

```
C0 = max(m+n+1, 2(m−1), 2(n−1), 4),
0 <= epsilon <= 1/(9 k C0)                 (k>0),
w_ij = 1+epsilon(d_i+e_j)                  ((i,j) outside E),
H = k(m+n)−sum_i d_i^2−sum_j e_j^2,
Z = mn−k+epsilon H,
rho(i,j)=w_ij/Z.
```

For k=0 use the uniform full-grid law. The following diagonal dominates
every independently chosen row/column/single-cell Gram matrix of rho:

```
lambda_E = (1+(m+n+1+2k epsilon)/Z,
            2(n+1+k epsilon)/Z,
            2(m+1+k epsilon)/Z,
            4/Z).                                        (AH1)
```

Thus, for all real four-vectors A and every test row i, column j and cell z,

```
E_rho (A0+A1*1[row=i]+A2*1[column=j]+A3*1[cell=z])^2
    <= sum_g lambda_E[g] A_g^2.                          (AH2)
```

Now fix K>=1 and choose one epsilon<=1/(9 K C0). If K<mn and

```
D_K=mn−K+epsilon K(m+n−K−1)>0,
```

then every arbitrary hole pattern with 0<=k<=K admits the same diagonal

```
lambda_K = (1+(m+n+1+2K epsilon)/D_K,
            2(n+1+K epsilon)/D_K,
            2(m+1+K epsilon)/D_K,
            4/D_K).                                      (AH3)
```

The row, column and point probabilities of this same law satisfy

```
R_k=(n+k epsilon)/D_k,
C_k=(m+k epsilon)/D_k,
a_k=(1+k epsilon)/D_k,                                    (AH4)
```

where D_k=mn−k+epsilon k(m+n−k−1). These bounds are continuous at k=0.
All three increase with k, so the K-bounds work in every fibre. No extra
row/column deletion or matching hypothesis is used.

### Proof of the new Gram estimate

Use unnormalized matrices. For selected row i, column j and surviving
cell z, let r=n−d_i, c=m−e_j, u=1[(i,j) survives],
v=1[z lies in row i], and t=1[z lies in column j]. At epsilon=0 the Gram is

```
M0 = [[mn−k,r,c,1], [r,r,u,v], [c,u,c,t], [1,v,t,1]].
```

The unnormalized diagonal from (AH1) is initially
`(mn−k+m+n+1,2(n+1),2(m+1),4)`. Its difference D0 from M0 is a
nonnegative weighted graph Laplacian plus diagonal slacks

```
(d_i+e_j, 2+2d_i−u−v, 2+2e_j−u−t, 2−v−t).               (AH5)
```

All slacks are nonnegative integers. They all vanish precisely when
d_i=e_j=0 and z=(i,j). In that exceptional case both axes and their
intersection are untouched by holes.

In every other case D0 >= I/9. Here is a proof including fully missing
rows or columns, so k<min(m,n) is unnecessary. If r,c>=1, the graph
contains the unit star 01,02,03 and some vertex has a unit diagonal
anchor. Expressing four coordinates through the anchor and the three
star differences gives a matrix with squared Frobenius norm at most 9.
Thus `sum x_g^2 <= 9(x_anchor^2+sum_{a=1}^3(x0−xa)^2)`.

If r=0 then d_i=n. The center slack is at least n>=3 and the vertex-1
slack is at least 2n+2. Use two units of each slack and
`2x0^2+2x1^2 >= (x0−x1)^2` to restore the missing star edge 01.
The analogous construction restores 02 if c=0. If either edge was
missing, the remaining center slack is at least
`n*1[r=0]+m*1[c=0]−2(1[r=0]+1[c=0]) >=1`.
The full star and its center anchor therefore remain, giving the same
I/9 bound. All other edge and diagonal terms are nonnegative.

Write h=d_{z_row}+e_{z_column}, and let r',c' be the derivatives of the
selected raw row/column masses. Let u'=d_i+e_j if (i,j) survives and 0
otherwise. On a surviving cell, its row-incident and column-incident
hole sets are disjoint, so h<=k and u'<=k. Moreover

```
0<=r'<=k(n−1),    0<=c'<=k(m−1).
```

For a row with a hole this follows by summing at most n−1 cell
derivatives bounded by k. A row without holes has r'=sum e_j=k.
The column statement is identical. The difference matrix is affine:

```
D(epsilon)=D0+epsilon Delta,
Delta = [[2k, −r', −c', −h],
         [−r',2k−r',−u',−hv],
         [−c',−u',2k−c',−ht],
         [−h,−hv,−ht,−h]].                                (AH6)
```

Its absolute row sums are bounded respectively by

```
k(m+n+1), 2k(n−1), 2k(m−1), 4k.
```

For the second bound, use
`|2k−r'|+r'+u'+hv <= max(2k,2r'−2k)+2k
                    <= max(4k,2r') <=2k(n−1)`.
Symmetry and `2|xy|<=x^2+y^2` imply
`|x^T Delta x|<=k C0 ||x||^2`. Hence the nonexceptional matrices satisfy
`D(epsilon)>=(1/9−epsilon k C0)I>=0`.

In the exceptional case r'=c'=k and h=u'=0. Then Delta is itself the
nonnegative star Laplacian with weight k on 01 and 02. Thus D remains
positive semidefinite there too. This proves (AH1)–(AH2).

A test cell outside the survivor support has zero indicator. Its Gram
inequality follows by taking the upper-left principal submatrix for any
surviving test cell, together with the nonnegative fourth diagonal.
Test rows or columns outside chosen axis sets are likewise zero blocks.

### The graph identity and common coefficients

Summing cell derivatives gives exactly H above. If t(E) counts unordered
pairs of holes sharing neither row nor column, then

```
sum_i d_i^2+sum_j e_j^2 = k^2+k−2t(E),
H = k(m+n−k−1)+2t(E).                                    (AH7)
```

Indeed each pair of distinct holes shares at most one endpoint. It is
counted twice in the sum of degree squares when it shares an endpoint,
and zero times otherwise. Thus H>=k(m+n−k−1), and Z>=D_k.
Replacing Z by D_k in the positive fractions of (AH1) only increases
the diagonal. Also

```
D_j−D_(j+1)=1−epsilon(m+n−2j−2)>0,
```

since epsilon(m+n−2)<1. Positive numerators in all four coordinates
increase with j. Therefore their D_j-envelopes are coordinatewise
increasing, and D_K>0 ensures every earlier denominator positive.
This proves the shared vector (AH3) for all patterns with at most K holes.

Within this particular degree-weight certificate, for fixed m,n,k,epsilon,
all four coordinates improve as t(E) increases. Stars have t=0 and
matchings have t=binomial(k,2), when these patterns fit. This is an
ordering of these sufficient certificates, not an assertion about the
true minimax laws or all possible certificates.

### Same-law probability caps and arithmetic use

The selected raw row derivative has the exact expression

```
r'_i = d_i(n−d_i)+k−sum_{j:(i,j) in E} e_j
      <= k+d_i(n−d_i−1).
```

Consequently, since epsilon(n−2)<=1,

```
raw row mass = n−d_i+epsilon r'_i <= n+k epsilon.
```

The same argument gives raw column mass <=m+k epsilon. The disjoint
incident-hole observation above gives every raw point mass <=1+k epsilon.
Normalize by Z>=D_k to obtain (AH4). This point cap is different from
the old indicator-weight matching law's 1+epsilon cap.

Let an arbitrary old law mu index varying row/column sets and arbitrary
hole patterns E_x, always of size at most K and with the same m,n.
Use the conditional law rho_x above in each fibre. The old marginal is
exactly preserved. Apply (AH2) with the four old complete block loads,
then integrate using the common diagonal (AH3), to obtain

```
Gamma_new <= F_K Gamma_old,
F_K = sum lambda_K = 1+3(m+n+3+2K epsilon)/D_K.             (AH8)
```

The existing convex-concentration reduction allows each block's residue
choices to vary independently by original cofactor. Actual original
labels must remain distinct. This argument neither assumes independent
old coordinates nor mixes different selected old laws. The caps (AH4)
hold for the very same conditional laws and can be used in the existing
full-height extension and weighted-profile arguments.

One may retain the actual k(x) envelope. Since every complete old block
load includes the unit cofactor and hence is at least 1, subtraction gives

```
Gamma_new <= F_K Gamma_old − E_mu[F_K−F_(k(x))].           (AH9)
```

This is the same valid unit-load rebate as in the matching case, now for
arbitrary point-hole geometry. Any sharper use of H or t(E) must retain
the same-law weighted old-load bookkeeping.

### Concrete m=10,n=12,K=12 boundary

For the coarse common envelope, compare with the uniform-count factor
`F0_K=1+3(m+n+3)/(mn−K)`. Exact algebra gives

```
F0_K−F_K = 3K epsilon B_K / [(mn−K)D_K],
B_K=m^2+n^2+(2−K)(m+n)−K−3.
```

For m=10,n=12 this is B_K=285−23K. Thus the envelope is strictly better
for every integer 1<=K<=12 and epsilon>0; at K=12, B_K=9. Choosing the
conservative epsilon=1/(207 K) gives

```
epsilon=1/2484,
D_12=2485/23,
F_12=12632/7455,
R_12=1/9,
C_12=2071/22365,
a_12=208/22365.
```

The strict gain over the uniform-count factor 61/36 is exactly 1/89460.
All 12 point exclusions are allowed in arbitrary positions, including
an entirely removed row. The strict-improvement cutoff 12 belongs to
this sufficient envelope; PSD validity itself extends further whenever
the stated support and D_K positivity conditions hold.

The adjacent verifier checks 11 exact polynomial identities and four
nonnegative-coefficient certificates for these formulas. The graph-counting
and anchored-star arguments above prove the all-pattern statement. The
matching theorem, weighted-rectangle concentration and established SDP
framework are reused; the degree-weight construction supplies the new estimate.

`D5.S3.Arith.Congruence.ArbitraryHoleGram.degree_reweighted_grid_second_moment_le`
in [ArbitraryHoleGram.lean](../../../D5/S3/Arith/Congruence/ArbitraryHoleGram.lean)
formalizes the unnormalized weighted grid inequality for arbitrary finite
row and column carriers of cardinality at least three, arbitrary hole
relations, and the stated nonnegative small perturbation. Its proof derives
the incidence budgets and both Gram cases from the relation. Normalization,
the denominator lower bound, integration with arithmetic head laws, and
the tail continuation remain ordinary proof obligations. The later
zero-perturbation extension to axes of size one or two is also supplied by
an ordinary Laplacian proof, not by this Lean declaration. No
literature-priority claim is made.

## Mean hole count and the complete comparison profile

This result combines the degree-weighted point-hole kernel with the
repository's existing weighted conditional comparison, old 315 convex
profile, and high-digit lift. Its improvement comes from retaining the
correlation between hole count and old test loads. Replacing a supremum
density by its average while keeping the original comparator would not
be justified.

### Kernel inputs and one actual law

Use one old probability μ with common complete-load comparator X,
EX=M=271/86 and Γ(μ)≤G=1131/86. Above every old point x suppose there is
a 10×12 rectangle of first 11/13 digits. Its row and column sets may move
with x. Delete k(x) arbitrary cells, where 0≤k(x)≤K≤12, and suppose the
remaining cells avoid all actual classes with both new exponents at
most one. No matching assumption is made.

Use the degree-weighted kernel on that punctured rectangle, with one
common 0≤ε≤1/(207K). A surviving cell (i,j) receives unnormalized weight
1+ε(d_i+e_j), where d_i,e_j are the row/column hole degrees. The kernel
construction gives the following common bounds at hole count j:

    D_j=120−j+εj(21−j),
    R_j=(12+jε)/D_j,       C_j=(10+jε)/D_j,
    a_j=(1+jε)/D_j,        d_j=120a_j,
    F_j=1+(75+6jε)/D_j.                                      (VH1)

Here R,C,a are row, column and atom caps; d is the density cap relative
to the full uniform 10×12 rectangle. F is the sum of the common diagonal
quadratic coefficients

    1+(23+2jε)/D_j, 2(13+jε)/D_j, 2(11+jε)/D_j, 4/D_j.

The proof of this degree-weighted kernel, including wholly deleted rows
or columns, is a separate input. Its actual normalization may exceed
D_j; all displayed quantities are upper bounds, which is sufficient.

Uniformly lift all additional 11/13 digits to their full finite original
heights. Denote this probability by ν0. After deleting all actual high
classes, condition once, producing ν. All bounds below refer to these
same two laws, without choosing a new law for each test load.

Suppose in addition

    Eμ k≤M.                                                   (VH2)

For actual point holes from distinct original mixed moduli 11·13·d,
d|315, this follows because their activation count is bounded by one
complete old load. There are only 12 old divisor labels, so K=12 applies
automatically. Repeated forbidden cells reduce k. Virtual added holes
must not be counted under (VH2) without a separate justification.

### The weighted upper-quantile lemma

Put α=min(1,M/K). Let X_α be the upper α-quantile of X, splitting the
boundary atom as necessary, and put T_α=αEX_α. For every complete old
load A and nonnegative increasing convex g,

    Eμ[k g(A)]≤KαE g(X_α).                                   (VH3)

Proof: write w=k/K, so 0≤w≤1 and Ew≤α. At a quantile boundary t choose
z=g(t)≥0. Then

    E[w g(A)]≤αz+E(g(A)−z)_+
               ≤αz+E(g(X)−z)_+=αE g(X_α).

The middle step uses the old increasing-convex comparison. It neither
asserts nor requires independence of k and A. This is the same
upper-quantile argument already used for survivor conditioning, now
applied to the old-point weight.

For 0≤j≤K≤12, D_j is positive, decreasing and concave. Every numerator
in (VH1) is a positive affine function with nonnegative slope. Such a
ratio is increasing and convex: differentiating twice gives

    (N/D)''=−2N'D'/D²+N[2(D')²/D³−D''/D²]≥0.

The same differentiation applies to each of the four individual
diagonal coefficients, not just their sum F_j. Consequently every
individual low or high coefficient is monotone, and each scalar bound
f_j used below satisfies

    f_j≤f_0+(f_K−f_0)j/K.                                   (VH4)

In particular, for each complete old load A,

    Eμ[f_k A]≤f_0M+(f_K−f_0)T_α.                            (VH5)

The same statement holds for partial original cofactor loads by
completing them before applying the inequality.

### Better high-class mass and square bounds

For the actual finite higher heights put

    u_p=Σ_(t=1)^(H_p−1)p^(−t),
    v_p=Σ_(t=1)^(H_p−1)(2t−1)p^(−t), w_p=4u_p+v_p.

Uniform bounds for all finite heights use

    u11=1/10, u13=1/12, w11=13/25, w13=31/72.

Define

    T_j=(R_j+a_j)u11+(C_j+a_j)u13+a_j u11u13,
    E_j=(R_j+3a_j)w11+(C_j+3a_j)w13+a_j w11w13,
    χ_j=F_j+E_j.                                             (VH6)

The functions T_j,χ_j are again increasing and convex. Apply (VH5) to
each original exponent group in the high-class union bound. Distinct
original labels give at most one old cofactor class per divisor in each
group, exactly as in the existing height theorem. The actual removed
mass is at most

    Λ=T_0M+(T_K−T_0)T_α.                                   (VH7)

This improves the worst-K value T_KM whenever K>M: since X≥1 and α<1,
T_α<M, and T_K>T_0 whenever a higher digit is present.

There is also a rebate in the high square terms. Every complete old
load A_e is at least one, and therefore A_eA_f≥1 pointwise. If a high
pair has cap κ_j, replace κ_k A_eA_f by

    κ_K A_eA_f−(κ_K−κ_k).

Integrating uses E A_eA_f≤G. Summing all high pairs, and retaining the
existing common-diagonal low-group rebate, gives

    Γ(ν0)≤χ_KG−Eμ(χ_K−χ_k)
           ≤U:=χ_KG−(χ_K−χ_0)(1−α).                        (VH8)

Thus the same minimum-load argument applies to both the low and high
parts. In particular the low contribution alone retains the stronger
mean-hole saving (F_K−F_0)(1−α), which dominates the previously available
γ(K−M)_+ bound.

If Λ<1, condition ν0 on actual high-class survival. Every full load has
square at least one, so

    Γ(ν)≤J:=(U−Λ)/(1−Λ).                                   (VH9)

U≥1 follows from its valid bound on the square of a complete load. The
survival probability used here and below is s=1−Λ; it is a lower bound
on the true surviving mass, not an equality claim.

### A weighted full comparator

Let τ be the reference law that is uniform on each available 10×12
rectangle, given the old point x, and uniform on all higher digits.
Its constant conditional prefix caps give the independent auxiliaries
N=N11N13 used in MH3, independent of X. The weighted C1 comparison is
valid for the finite old measure kμ as well as for μ. Combining it with
(VH3) and Jensen for the complete old loads gives, for every nonnegative
increasing convex g,

    Eτ g(L)≤E g(XN),
    Eτ[k g(L)]≤KαE g(X_αN).                                (VH10)

The conditional reference kernels can depend on x through the available
sets: their common caps are what make the auxiliary N independent of x.
Each old load used after comparison is fixed before x is sampled.

The actual degree-weighted kernel has pointwise density at most d_k
relative to τ. Apply (VH4) to d, noting d_0=1. Then

    Eν0 g(L)≤E g(XN)+(d_K−1)αE g(X_αN).                     (VH11)

Define the finite comparison measure on old load values

    W_old=Law(X)+(d_K−1)αLaw(X_α),
    Dbar=mass(W_old)=1+(d_K−1)α.                            (VH12)

Multiply its old values by the independent N11N13; call the resulting
finite measure W. It has the same mass Dbar. The full comparator for
ν is the upper s-mass of W, normalized to mass one, equivalently the
upper ell-quantile of W/Dbar with ell=s/Dbar.

Indeed for every nonnegative increasing convex h and every real z,

    Eν h(L)≤z+(1/s)∫(h(y)−z)_+ dW(y).                       (VH13)

Take z at the corresponding quantile boundary. This proves a common
full convex comparison on exactly the law used in (VH9).

The formula is not an average-density replacement. The excess density
has been assigned to the upper old-load quantile X_α, which accounts
for the worst permitted correlation with hole count. The old finite
measure has total mass Dbar, so it must be normalized or integrated as
a finite measure; treating its atoms as a probability would be wrong.

#### Strict improvement over the worst-K comparison

For every nonnegative g,

    ∫g dW=E g(XN)+(d_K−1)αE g(X_αN)≤d_K E g(XN),

since the upper old quantile is a submeasure of Law(X). Simultaneously
Λ≤T_KM and U≤χ_KG. Thus (VH9) and (VH13) improve the same-law worst-K
height and density bounds. For K>M, the square, removed-mass, and
every finite hinge bounds improve strictly at positive higher heights.
The hinge statement uses the unbounded positive auxiliary N: even the
discarded lower old quantile contributes a positive hinge expectation.

#### Dependence on K

At fixed ε and within a common valid kernel range, all these bounds
are nondecreasing as K increases. For K≥M, write α=M/K. The secant
slopes(f_K−f_0)/K increase by convexity, and expectations under the
upper α-quantile increase as α decreases. These observations prove
monotonicity of Λ and of the raw comparison cost in (VH13). Also

    U=χ_0G+(χ_K−χ_0)(G−1)+M(χ_K−χ_0)/K

is nondecreasing, since G≥1. The survivor lower bound decreases, so J
and the final full comparator increase. For K≤M the formulas reduce
to the already monotone worst-K values. This is monotonicity of the
guaranteed bounds, not a claim about the optimized Γ of different
physical laws.

Choosing a different ε for each K changes the comparison and requires
separate evaluation. The exact verifier evaluates ε=1/(207K) for
K=1,…,12; no tail scheduling is part of that computation.

### Exact K=12 input

Take ε=1/2484 and the infinite geometric majorants, which cover every
finite 11/13 height. Then

    α=271/1032,        T_α=1633/1118,
    d_K=1664/1491,     Dbar=1585595/1538712,
    Λ=164881/2683200,  s=2518319/2683200,
    U=3968983906721/166180896000,
    J=51464038499033/2027599359660.                          (VH14)

The upper old α-quantile starts at 4. Its raw subprobability atoms are
1631/13416 at 4 and the original X masses at 5,6,8,12, with zero below 4.
Consequently W_old has these exact atoms:

| Value | Unnormalized mass |
| ---: | ---: |
|1|581/6966|
|2|3031/6966|
|3|146/1053|
|4|5552881/25718472|
|5|1280/165501|
|6|1920/18389|
|8|1664/55167|
|12|832/55167|

After multiplying by the independent auxiliaries,

    ∫y dW(y)=226440629/56347200,
    W{1}=6391/92880, W{2}=807835/2173392,
    ell=s/Dbar=3754813629/4122547000.

The upper s-mass of W starts at 2, strictly inside its atom. The final
comparison law Z therefore has

    Pr(Z=2)=37653203663/101379967983,
    Pr(Z=z)=W{z}/s for integer z>2,
    EZ=46851298771/11264440887.                              (VH15)

Numerically J≈25.38175910 and EZ≈4.159220972. The corresponding
worst-K bounds are J≈25.53775188 and comparison mean≈4.246698684.
The next theorem uses these head inputs in a fully certified tail continuation.

### Reuse, verification and scope

The kernel PSD bound is supplied by the independent degree-weighted
point-hole proof. Existing repository inputs are C1–C3 for arbitrary
finite old measures, AP2–AP7 for conditional comparison with original
labels, MT7 for the low minimum-load rebate, the established high pair
count, and the old 315 comparator X. The upper-quantile lemma itself is
standard reuse. The quantitative new combination retains the same
hole-count weight through high deletion, square, density and profile;
it does not create a bind-only Lean wrapper.

The adjacent standard-library verifier recomputes these exact inputs for K=1,…,12, all individual coefficient chord inequalities and 300 hinge comparisons. The symbolic argument establishes the continuous-domain bounds; the finite checks verify the displayed arithmetic.

## All cross-point labels with arbitrary heights and unrestricted tails

**Theorem.** Let a finite family have distinct odd nonunit moduli, and let
the full 3/5/7 part of every original modulus divide 315. Choose the
canonical supported old law μ. At each old point x suppose there are
10 first 11-digits avoiding all active classes of moduli d·11, and
12 first 13-digits avoiding all active classes of moduli d·13, for d|315.
The available sets may depend on x. Then the family cannot cover.
There is no restriction on the residues of the classes of moduli d·143,
on any higher 11/13 exponents, or on the number, exponents and interactions
of tail primes from 17.

Choose such available sets A_x,B_x. The actual d·143 classes remove
at most twelve distinct points of A_x×B_x, with hole count k(x) bounded
by one complete old cofactor load. Thus 0≤k≤12 and Eμk≤271/86.
Apply AH1–AH9 and VH1–VH15 to these actual holes, without adding virtual
holes. All complete original labels remain distinct even when their
projections coincide. After lifting to the full original heights and
conditioning away high head classes, the same supported law has

    J_head≤51464038499033/2027599359660,
    Θ_head(t)≤E(Z−t)_+,   EZ=46851298771/11264440887.

Use this complete comparator in AP2 and the separate square bound in
AP5. The fixed schedule in `arbitrary_holes12_tail17` processes every
prime from 17 through 2903: 414 steps, global prime index 420. Directed
exact arithmetic gives

    C_tail≤205435101024428611/250000000000000000,
    survivor mass≥44564898975571389/250000000000000000,
    Γ_stop≤1751428432885843299077/178259595902285556
           <9826<9833<420(log420+loglog420−3)^2.              (AH10)

For the last inequality, independent positive rational atanh sums give
log420>604025/100000 and loglog420>179844/100000. The resulting lower
bound is 4916713392381/500000000>9833. AP6 and the T1–T6 transfer to
BBMST Theorem 6.1 continue through every later prime. If the family
ends sooner, the positive prefix survivor mass already suffices. CRT
then supplies an integer outside every original class.

The verifier retains 768 low product states and includes the entire
omitted tail through the exact comparator mean. Probabilities and
moments are rounded upwards on a grid of 10^-18, and every hinge
correction has a nonnegative coefficient. An independent implementation
with trial-division prime generation and a 10^-24 grid confirms Γ<9826.
The prior single-hole certificate is retained unchanged and gives its
stronger numerical bound on that smaller class.

This theorem removes the earlier point-hole restriction entirely. The
axis hypothesis is still substantial: at any old point the active
first-power 11-axis classes must forbid at most one distinct digit,
and likewise for 13. Several different forbidden axis digits can
violate that hypothesis. Higher 3/5/7 powers also remain outside this
statement. The result is an ordinary proof with exact certificates,
not an unrestricted solution of Erdős #7 or an end-to-end Lean theorem.


# Unrestricted axis deletions and the optimal scalar clipped bound

For every family of distinct nonunit moduli dividing
315·11^H·13^J, H,J≥1, the construction below gives one probability
supported on the full survivors with

    Γ≤42723250051/1147550665 ≈37.229946663.                    (VC1)

There is no restriction on the original axis deletions or point-hole
pattern. The bound covers all finite H,J. The full3/5/7part must still
divide315. The same law has a full increasing-convex comparator of mean

    1263555626/229510133 ≈5.50545,

specified below. These are head bounds, not a completed unrestricted-tail
continuation. An exact robust linear program proves that(VC1)is the
best bound from the stated scalar clipped certificate for all C≥1;
it does not prove optimality among actual supported laws.

### Actual varying rectangles and their area

Use the canonical supported old315law μ, with common old comparator X,
EX=M=271/86, Γ315(μ)≤G=1131/86, and complete old loads in{1,…,12}.
First exclude the actual pure11and13root classes. If a root class is
absent, an arbitrary virtual root exclusion only restricts support.
The reference first-digit carrier is a10×12rectangle.

Let u(x),v(x) be the numbers of distinct remaining rows and columns
deleted by actual axis classes. By original-modulus distinctness there
are complete old layouts A,B with

    u≤A−1, v≤B−1.

Let D be a third complete old layout whose load bounds the number of
active mixed11·13·d labels. There is at most one original label per
d|315; repeated cells only reduce the number of holes. If N(x) is the
actual remaining first-digit cell count, then

    N(x)≥S(A,B,D):=[(11−A)_+(13−B)−D]_+.                    (VC2)

This retains the rectangular overlap u·v. It does not spend one common
vertex budget on both axes or select a fixed smaller rectangle. It
allows N=0 and makes no independence assumption about A,B,D.

Let τ sample x from μ, then sample uniformly from the10×12reference
rectangle and all extra11/13digits. Write s(x)=N(x)/120. Fix C≥1 and
define a subprobability measure ξ on the actual low survivors by the
following density relative to τ:

    f(x,y)=1_low-survives(x,y) min(C,1/s(x)).

Set f=0 when s=0. Its old row mass is

    h_C(x)=min(1,Cs(x)),    Z=Eμ h_C≤1.                      (VC3)

Thus empty fibres receive zero mass automatically, and the old marginal
is allowed to change. The density is at most C, while the old marginal
is bounded by μ. These two properties are used separately.

### Exact area information

For each of A,B,D impose all known marginal hinge bounds

    t: 0,1,2,3,4,5,6,8;
    θ(t):271/86,185/86,100/81,61/81,16/39,7/26,5/37,2/37,

and the square bound1131/86. Let P range over probability distributions
on the1728triples{1,…,12}³ satisfying these constraints. Then

    Z≥Z_*(C):=min_P E_P min(1,C S(A,B,D)/120).                (VC4)

This is an information relaxation: its distributions need not arise as
three actual arithmetic layouts. A feasible dual gives a universal
lower bound, and exact feasible primal distributions establish sharpness
within this specified marginal information.

At C=1 the exact optimum is

    Z_*(1)=3705715/6185808.

One pointwise certificate is

    S≥110−7(A−1)_+−4(A−2)_+−(A−6)_+
           −5(B−1)_+−4(B−2)_+−(B−6)_+−(D−1)_+.

At C=3/2 the exact optimum is1004221/1246752. Their finite marginal-profile optima are exact; the global clipped certificate below resolves the choice of C.

The constant used in(VC1)is

    C*=40/31,        Z_*(C*)=74101/97929.                    (VC5)

Its particularly short pointwise dual is

    min(1,S/93)
      ≥1−3(A−2)_+/31−2(A−4)_+/93
          −7(B−2)_+/93−2(B−4)_+/93−(D−2)_+/93.             (VC6)

The finite certificate verifies(VC6)for every triple. Averaging the
five hinge terms gives exactly the value in(VC5).

### High-class deletion and the complete-square bound

The uniform higher-digit reference has per-prefix caps
11^(−(a−1))/10,13^(−(b−1))/12 and their product. The sum over all
actual high original labels therefore has τ-mass at most

    λ0=M[(13/120)(1/10)+(11/120)(1/12)
                           +(1/120)(1/10)(1/12)]
       =24119/412800.                                       (VC7)

This is the existing distinct-cofactor height count; finite heights only
decrease it. Since ξ≤Cτ, the actual high deleted ξ-mass β is at most
Cλ0. No disjointness or preservation of every old fibre is assumed.

For a complete fine test layout, group its load by the full11/13
exponent pair. The old-only group A00 has

    ∫h_C A00² dμ≤G−Eμ(1−h_C)=G−1+Z.

Every other ordered pair has at least one positive new exponent.
The ξ-prefix intersection mass is at most C times the reference cap;
the old load product has expectation at most G by Cauchy–Schwarz.
The sum of all reference coefficients, including the old-only pair, is

    χ0=(1+(3+13/25)/10)(1+(3+31/72)/12)
       =187759/108000.

Consequently

    Γ(ξ)≤G−1+Z+C(χ0−1)G.                                   (VC8)

Here Γ is extended homogeneously to finite measures, as in the existing
weighted rectangle transfer. This uses the actual old marginal cap and
does not replace the entire right side by CΓ(τ).

Delete all actual high classes and normalize. The remaining mass is
at least Z_*(C)−Cλ0. Every full load is at least one, so deleting β
saves at least β from its square integral. Whenever the mass bound is
positive, the resulting single supported probability ν_C satisfies

    Γ(ν_C)≤1+[G−1+C(χ0−1)G]/[Z_*(C)−Cλ0].                  (VC9)

At(VC5)the denominator is

    Z_*(C*)−C*λ0=229510133/336875760>0,

and(VC9)is exactly(VC1). At heights H=J=1 there are no high exclusions
and the reference square factor is13/8. The same C* gives

    Γ≤99014608/3186343 ≈31.075.

This improves the earlier unrestricted first-height sequential bound
388385/10979≈35.375. It is not asserted to be the optimal first-height
choice of C.

### Full profile on the same law

Under τ the existing conditional comparison gives the common auxiliary

    Y=X N11 N13,

with independent factors and Pr(Np=1)=1−1/(p−1),
Pr(Np=k)=p^(1−k)for k≥2. The old/reference sets are fixed at10×12;
actual low deletions are in ξ and may vary arbitrarily with x.

The final law has density at most C/[Z_*(C)−Cλ0]relative to τ. Hence
its full increasing-convex comparator is the normalized upper ρ_C
quantile of Y, where

    ρ_C=Z_*(C)/C−λ0.

At C*, this fraction is229510133/434678400. The boundary is strictly
inside the atom at3. The reference mean and first masses give

    E comparator
      =3+[EY−3+2Pr(Y=1)+Pr(Y=2)]/ρ_C
      =1263555626/229510133.                                (VC10)

This comparator and(VC1)bound the same ν_C*. The scalar density
comparison is a limitation of the current argument: C=1 has a weaker
square bound≈41.440but a slightly smaller comparison mean≈5.447.
Thus square improvement must not be advertised as a simultaneous
improvement of every profile value. These head bounds alone do not provide a certified unrestricted-tail continuation.

### A sharper first moment under the same law

The old marginal cap also gives a first-moment estimate stronger than
(VC10). For each complete old test load A, the unit term gives
`∫h_C A dμ≤M−1+Z`. All positive new-exponent groups have total reference
first-moment coefficient `Nmean−1`, where

    Nmean=E(N11 N13)=(111/100)(157/144)=5809/4800.

Their ξ-integral is at most `C(Nmean−1)M`. Deleting high-class mass β
saves at least β from every complete-load integral. The same normalization
as (VC9) therefore gives

    sup_test Eν_C L
      ≤1+[M−1+C(Nmean−1)M]/[Z_*(C)−Cλ0].

At C=40/31 this is

    M*=1242116000/229510133≈5.41203120.                     (VC11)

It holds simultaneously with the actual square bound (VC1) and the
full comparator (VC10). The comparator's own mean remains the larger
`1263555626/229510133`; inserting M* in an identity for that comparator
would be invalid.

### Global optimization of this scalar certificate

For a fixed C, the dual to(VC4)maximizes

    Z=ν+Σ_i y_i b_i,
    y_i≤0,
    ν+Σ_i y_i f_i(l)≤1,
    ν+Σ_i y_i f_i(l)≤C S_l/120   for every triple l.

The f_i are the27marginal hinge/square features and b_i their bounds.
Set A0=G−1,B0=(χ0−1)G. To minimize(VC9)over all C≥1 and all valid
dual lower bounds, apply the standard linear-fractional substitution

    t=1/(Z−Cλ0), z=Ct, v=νt, w_i=y_it.

The objective becomes1+A0t+B0z, subject to

    v+Σ_iw_i b_i−zλ0≥1,
    v+Σ_iw_i f_i(l)≤t,
    v+Σ_iw_i f_i(l)≤z S_l/120,
    w_i≤0, t≥0, z≥t.

This is one linear program with30variables and3458constraints. Finite
LP duality makes the formulation exact for the current information
relaxation. A positive feasible denominator exists by(VC5); scaling
forces equality in the normalization constraint at an optimum.

The retained exact primal and dual have equal objective

    1+41575699386/1147550665.

The primal yields C=40/31; the dual has15nonzero inequality multipliers.
The independent verifier checks every primal inequality, every dual
sign, all30stationarity coordinates and exact equality. This proves
global optimality for this particular scalar clipped proof, without a
parameter grid. Improving its all-height square conclusion requires
additional information, such as the actual weighted old test energy,
rather than further optimization of C within the same certificate.

The measure construction reuses the residual-capacity and weighted
conditional comparisons above. The quantitative input is the actual
two-axis area objective, retaining its rectangular overlap, and its
exact optimization under the three complete old marginal profiles.
This is an ordinary proof with exact rational certificates, not an
end-to-end Lean theorem or an unrestricted solution of Erdős #7.

## Retaining the common old shape and survivor count

The same construction at the fixed constant C=40/31 satisfies the stronger
simultaneous bounds

    Γ≤2167128283/58962460 ≈36.754373597,
    sup_test Eν L≤24790300/4595881 ≈5.394025651.               (SC1)

These hold for every family of distinct nonunit moduli dividing
315·11^H·13^J, with arbitrary finite H,J≥1 and arbitrary axis and point
deletions. The full 3/5/7 part must divide 315. The improvement retains
information from the six canonical 45 shapes and their actual septenary
survivor count. This is the 45×7 divisor geometry of the odd part of
5040=16·315.

Fix the one old shape S selected by the original family, write n=|S|,
and let N be its actual 315 survivor count. Every test load and every
axis/cross activation load is evaluated on this same law. The possible
pairs (S,N) comprise 144 branches: N ranges from (77,78,78,75,74,74),
respectively, to 6n for the six shapes. None of the different loads may
choose a different branch.

### Deleted energy at a fixed survivor count

Put D=6n−N=Σₓb(x), using the actual deleted-digit counts from (D1).
For a nonnegative old cost h(A(x)), let T_D be the sum of the D smallest
entries among five copies of each h(A(x)). Since 0≤b(x)≤5,

    Σₓb(x)h(A(x))≥T_D.

The original cofactor labels give an additional lower bound. For every
η≥0, the identity b h=ηb−b(η−h), followed by
b≤Σ_d 1_Cd, gives

    Σₓb(x)h(A(x))
      ≥ηD−Σ_(d∈{3,5,9,15,45}) max_C Σ_(x∈S∩C)(η−h(A(x)))_+.
                                                                  (SC2)

Thus the maximum of T_D and all the right sides of (SC2) is a valid
deleted-energy lower bound L_D(A,h). The finite verifier takes η from
zero and the actual cost values. This finite selection is sufficient
for the bound; no optimality over η is required.

For h_t(a)=(a−t)_+, use (D3) to obtain

    Eμ(L−t)_+
      ≤max_A [5H_t(A)+min_(0≤k≤t)(H_k(A)+M_(t−k))
                         −L_D(A,h_t)]/N.                        (SC3)

For h(a)=a², (D4)'s numerator gives

    Eμ L²≤max_A [6ΣA²+2R(A)+Q−L_D(A,h)]/N.                     (SC4)

Intersect these bounds with the already proved constants for this same
shape. The resulting M_(S,N), G_(S,N), θ_(S,N)(2), θ_(S,N)(4) all hold
simultaneously for every complete old test layout. Effective old layouts
suffice: completing an inactive test cylinder only increases a load.
All 27,720 such layouts are checked directly.

The elementary old bound Φ(3)≤5 and old load≤6 also give
Eμ(L−6)_+≤10/N by the fibre inequality. Consequently any two complete
loads U,V on the same old law satisfy the useful joint restriction

    Eμ U²+50 Eμ(V−6)_+≤max_(S,N)(G_(S,N)+500/N)=761/39.       (SC5)

It retains a common arithmetic branch even when U and V are different
layouts. Separate globally maximized square and hinge constants discard
that information.

### Transfer on each common branch

Use exactly the existing pointwise inequality (VC6). Its average on one
branch gives the low-mass lower bound

    Z_(S,N)=1−[17θ_(S,N)(2)+4θ_(S,N)(4)]/93.

The same branch's higher deletion bound is λ_(S,N)=89M_(S,N)/4800.
Set s_(S,N)=Z_(S,N)−(40/31)λ_(S,N). Applying (VC9) and the first-moment
argument to that one branch gives

    Γ≤1+[G_(S,N)−1+(40/31)(χ0−1)G_(S,N)]/s_(S,N),
    sup_test Eν L
      ≤1+[M_(S,N)−1+(40/31)(5809/4800−1)M_(S,N)]/s_(S,N).
                                                                  (SC6)

Here χ0=187759/108000 as before. Every s_(S,N) is positive. The largest
square bound occurs in the first shape at N=81, where

    M=253/81, G=1131/86, θ(2)=100/81, θ(4)=32/81,
    Z=5705/7533, s=68561/100440.

Substitution gives the intermediate square bound
547762402/14740615≈37.160077921. The actual-rectangle refinement below
gives the square bound in (SC1). The largest first-moment
bound occurs in the same shape at N=84 and gives the other bound in
(SC1); these are uniform bounds on the same constructed law, not a claim
that one family attains both extrema.

The smallest certified full mass is 68561/100440. Hence that law's
density relative to the old uniform reference is at most
(40/31)/(68561/100440). It also has the full increasing-convex comparator
given by the upper

    ρ=68561/129600

quantile of the existing Y=X N11 N13. Its boundary is at 3 and its mean
is 1264886009/229953594. The comparator and both actual moment bounds in
(SC1) apply to the same law.

### The actual rectangle gives two further square savings

At an old point x, let m≤10 and n≤12 be the actual remaining row and
column counts after axis deletion, and let k≤12 be the number of distinct
remaining point holes. There are twelve possible original labels 143d,
d|315, which proves the hole cap. These are actual counts, not the
lower bounds for axis counts used in (VC2). Write T for the local
survivors and N_grid=mn−k for their number; N_grid is distinct from the
common old survivor count N.

When N_grid>0, the existing clipped density is f=min(40/31,120/N_grid)
on T, with old marginal h=f N_grid/120. Empty fibres have f=h=0. No
additional support restriction or change of probability measure is used.

For a selected row, column and surviving point, write r,c for their
surviving row/column sizes and u,v,w for the indicators that the row-column
intersection survives, the point is in the row, and the point is in the
column. The Gram matrix of the four indicators is

    [[N_grid,r,c,1], [r,r,u,v], [c,u,c,w], [1,v,w,1]].

Put d=n−r and e=m−c. Subtracting this matrix from
diag(N_grid+m+n+1,2(n+1),2(m+1),4) gives the weighted graph Laplacian
with edge weights r,c,1,u,v,w, plus diagonal slacks

    (d+e, 2+2d−u−v, 2+2e−u−w, 2−v−w).

All weights and slacks are nonnegative, so this is positive semidefinite
for every m,n≥1 and every point-hole pattern. An absent test row, column
or point has zero indicator and is handled by the corresponding
principal restriction. Convex concentration of the nonnegative
coefficients in each test block extends the bound to arbitrary row,
column and point assignments. Multiplying by f/120 gives the diagonal

    (h+f(m+n+1)/120, 2f(n+1)/120,
                         2f(m+1)/120, 4f/120).                (SC7)

The four block amplitudes A_i are complete old loads, each at least one
and with Eμ A_i²≤G_(S,N). They need not be independent of each other or
of the local geometry.

Write q for the four coefficients in (SC7) after removing h from the
first one, and set C=40/31. The following simultaneous bounds hold:

    q≤U:=(55/2,26C,22C,4C)/120,
    Σq=f(m+n+3)/40≤3/4,
    ΣU=391/496.                                               (SC8)

For completeness, if m+n≤20, then f(m+n+1)≤21C<55/2 and
Σq≤23/31<3/4. If m+n=21, the dimensions are (9,12) or (10,11),
so N_grid≥96 and f≤5/4; this gives both bounds. If m+n=22, the
dimensions are (10,12), N_grid≥108 and f≤10/9, which also suffices.
The other three coordinate bounds use f≤C directly. Both displayed
maxima occur at (m,n,k)=(9,12,12). Empty fibres have q=0.

Since A_i²≥1, the coordinatewise gaps in (SC8) give

    Σq_i A_i²≤ΣU_i A_i²−(ΣU_i−Σq_i)
              ≤ΣU_i A_i²−19/496.

After integration, the low-block square is at most

    G−1+Z+(391/496)G−19/496.

Here G=G_(S,N); the h term uses the same old-marginal saving as (VC8).
Every pair with at least one higher exponent retains the existing
reference estimate C(χ0−13/8)G. Thus the complete square bound gains
both a coefficient and a constant saving:

    Γ(ξ)≤G−1+Z+C(χ0−1)G−(9/496)G−19/496.                    (SC9)

Deleting the higher original classes and normalizing is unchanged.
The numerator below is positive in every common branch, so replacing
the remaining mass by its certified lower bound is valid:

    Γ(ν)≤1+[G−1+C(χ0−1)G−(9/496)G−19/496]/s_(S,N).        (SC10)

The maximum over the 144 branches is 2167128283/58962460, again at the
first shape with N=81. This proves (SC1). The first-moment and full
comparison bounds above apply to this same unchanged probability law.

The `shared_count_clipped_head` field is recomputed from the existing
old geometry by the adjacent standard-library verifier. It checks all
144 branches, the 1728 pointwise instances of the single existing
dual (VC6), and all 1372 nonempty actual rectangle count triples in
(SC8). The universal Gram inequality follows from the displayed
Laplacian identity. No optimizer output or new primal certificate is needed.
The former scalar optimality result still concerns its stated global
marginal information; (SC2)–(SC6) retain additional common geometry.
These are ordinary proofs with exact arithmetic, without a new tail
continuation or an end-to-end Lean theorem.

## Actual obstruction for uniform conditioning and its signed bound

At first 11/13 height, fix the reference law τ=μ times the uniform
10×12 pure-survivor rectangle. For the four complete old test blocks
A,B,C,D, the fine test's reference square is at most

    E[A²+(2AB+B²)/10+(2AC+C²)/12
                       +(2BC+2AD+2BD+2CD+D²)/120].

Write `Rμ(A)=max_B Eμ AB`. Cauchy–Schwarz on the other old products
bounds this by `Eμ A²+(23/60)Rμ(A)+(29/120)G`.
Every deleted cell has full load at least A. For a candidate final
bound z, union-bound only the positive deletion contribution `(z−A²)_+`.
Each nonunit old label contributes row, column and point caps totaling
`1/10+1/12+1/120=23/120`; the unit cross label contributes `1/120`.
Thus the following condition for every A is sufficient for the normalized
uniform-survivor law to have Γ≤z:

    Eμ A²+(23/60)Rμ(A)+(29/120)G
      +(23/120) Σ_{d|315,d>1} max_a Eμ[(z−A²)_+ 1_{x=a mod d}]
      +(1/120)Eμ(z−A²)_+ ≤ z.                              (SC1)

The low surviving mass is positive: its union bound is at least
`1−(23/120)(M−1)−1/120=1993/3440`. The signed argument retains
the same μ and every distinct original label. The exact examples below
bound the scope of this sufficient criterion and of this particular
conditioned law; they do not rule out different supported laws.

### Same old law and exact sufficient-criterion barrier

The old original classes are

```
(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
(21,16),(35,24),(63,25),(105,19),(315,109).
```

Their complement Omega modulo 315 has size 86. With mu uniform on Omega
and the complete coherent layout `A(x)=sum_{d|315}1[x=8 mod d]`, its
histogram is

```
A:       1  2  3  4  6  8  12
count:   5 38 14 18  8  2   1.
```

Consequently `sum A=271` and `sum A^2=1131`. Direct maximization of every
individual divisor cylinder gives

```
max_B E_mu B = 271/86,
R_mu(A):=max_B E_mu AB = 1131/86 = G,
E_mu A^2 = G.
```

Here B ranges over all independent complete old layouts; the maximum
separates exactly into one finite residue maximization per divisor.

Put `h_z=(z−A^2)_+` and
`W(z)=sum_{d|315,d>1}max_a E_mu[h_z 1[x=a mod d]]`.
For the proposed sufficient criterion,

```
Phi(A;z)=E_mu A^2+(23/60)R_mu(A)+(29/120)G
         +(23/120)W(z)+(1/120)E_mu h_z.
```

For 25<=z<=35 the direct cylinder checks give

```
86 E_mu h_z=75z−571,
86 W(z)=164z−1197.
```

Each recorded cylinder witness maximizes at both endpoints and therefore
throughout the interval: every cylinder expression is affine there.
The verifier computes its own maximizers instead of trusting the oracle's
compressed witness table. Substitution gives

```
Phi(A;z)=(192443+3847z)/10320,
Phi(A;z)−z=(192443−6473z)/10320.
```

Globally the map Phi is Lipschitz with constant at most

```
(23/120)(271/86−1)+1/120=1447/3440<1.
```

Thus Phi(z)−z is strictly decreasing, and its unique zero is
`z*=192443/6473`. The sufficient criterion fails for every positive
z<z*, not just the portion in [25,35]. At 30 it succeeds on this example:
`Phi(30)=30−1747/10320`. This does not establish a universal bound of 30.

### Actual conditioned moment and its narrower scope

Add pure classes 0 mod 11 and 0 mod 13. For each old divisor d the table
below specifies additional row, column and point exclusions, respectively
by `(old residue,11-residue)`, `(old residue,13-residue)` and
`(old residue,11-residue,13-residue)`.

| d | Row | Column | Point |
|---|---|---|---|
|1|—|—|(0,9,8)|
|3|(2,6)|(1,11)|(2,10,11)|
|5|(2,2)|(4,2)|(2,10,5)|
|7|(5,5)|(6,3)|(6,10,6)|
|9|(2,3)|(5,4)|(2,9,6)|
|15|(2,7)|(11,2)|(2,9,10)|
|21|(2,4)|(20,12)|(2,10,6)|
|35|(17,5)|(34,9)|(34,2,7)|
|45|(2,8)|(41,5)|(11,2,9)|
|63|(47,4)|(34,12)|(23,8,3)|
|105|(17,4)|(34,10)|(26,8,7)|
|315|(52,7)|(244,4)|(97,10,7)|

The complete family contains exactly one congruence for every nonunit
divisor of 45045, hence 47 distinct odd nonunit moduli. The coherent fine
test center is 17018, which reduces to 8 modulo 315 and 1 modulo both
11 and 13. Its complete load is

```
F(x,i,j)=A(x)(1+1[i=1])(1+1[j=1]).
```

Among 10320 equally weighted reference cells, exactly 6872 survive every
original class. Their squared-load sum is 177110. Therefore, for the law
nu obtained by uniform conditioning on these actual survivors,

```
E_nu F^2=177110/6872=88555/3436>25,
retained reference mass=6872/10320=859/1290.
```

This proves `Gamma(nu)>=88555/3436`; it is not a claim that equality is
the maximum over all fine test layouts. The pre-deletion estimate is sharp
for this layout, since `E_tau F^2=(13/8)G` exactly. The additional loss in
the threshold 29.7301 therefore comes from the sufficient deletion bound.

These are obstructions for this prescribed uniform-conditioning method
and its sufficient criterion. They do not obstruct all supported laws,
do not apply automatically to higher 11/13 exponents, and do not exhibit
an odd covering system: this actual family has 6872 uncovered residues.

The actual family was supplied by Nyx. The adjacent verifier reconstructs
every CRT residue, checks the full period and the independent 86×10×12
grid, and verifies every weighted-cylinder maximum. Its fixed
`signed_conditioning_obstruction` certificate stores the original classes
and load histograms. This is exact arithmetic, not a Lean theorem.

## What the rectangle data do not determine about a hinge

Here the input is an actual head family together with a complete test
layout. Retaining the old shape, its survivor count, every actual rectangle
size and all four old block functions does not determine the test's
threshold-six hinge. This concerns exact evaluation: taking a supremum
over the omitted configurations can still give a sound upper bound.

For a concentrated four-block load on a nonempty surviving grid, let Ngrid
be its cell count, r and c the selected surviving row and column counts,
and u,v,t indicate, respectively, whether their intersection survives,
whether the selected surviving point lies in the row, and whether it lies
in the column. Put phi_tau(a)=(a-tau)_+. The exact unweighted cell sum is

    H_tau=(Ngrid-r-c+u) phi_tau(A)
          +(r-u) phi_tau(A+B)+(c-u) phi_tau(A+C)
          +u phi_tau(A+B+C)
          +phi_tau(A+vB+tC+D)-phi_tau(A+vB+tC).              (HO1)

The first four terms partition the grid by row/column membership; the
last difference adds the point block at its actual location. Its clipped
fibre integral is f H_tau/120. Empty fibres contribute zero. Thus the five
incidence values together with Ngrid and the amplitudes determine this
concentrated hinge. General labelled tests still need their actual
cylinder arrangement, or the justified convex-concentration upper bound;
(HO1) does not reconstruct that arrangement from four block totals.

For an actual counterexample use the 86-point old family specified in the
preceding subsection, with its forbidden old residue a_d for every
nonunit d|315. Add pure classes0 mod11 and0 mod13. For every d>1, add the
11d,13d and143d classes with old residue a_d and new digits1 where present.
All of these classes are inactive on the old survivors. The unit mixed
143class instead deletes the cell(10,12). This specifies exactly one
original class for every nonunit divisor of45045:47distinct moduli.

Every old survivor therefore has the same10×12rectangle with one point
hole, Ngrid=119, clipping density f=120/119 and old marginal h=1. The
constructed law is uniform on the10234actual survivors. In both complete
tests, all four old block functions are

    A(x)=sum_(d|315) 1[x=8 mod d].

For each d, the11d test chooses new digit1, and the13d test chooses digit1.
The first test's143d block chooses point(1,1); the second chooses point(2,2).
The old d block chooses8 mod d in both. CRT gives48actual divisor labels
for each complete test, with all four old block functions unchanged.
Their selected incidence data are (r,c,u)=(12,10,1) in both cases, but
(v,t)=(1,1) and(0,0), respectively. Direct evaluation gives

    sum_survivors (L_first-6)_+ =3998,
    sum_survivors (L_second-6)_+=3844,

hence

    E(L_first-6)_+=1999/5117,
    E(L_second-6)_+=1922/5117,
    difference=11/731>0.                                   (HO2)

For the observation q retaining the shared shape/count, actual scalar
rectangle data and four old block functions, (HO2) gives equal q-values
and unequal hinge values: ker(q) is not contained in ker(H_6). A derived
encoding of those same readings cannot restore the missing incidence.
Keeping the actual test cylinders together with CRT-closed intersection
counts I_U(d,a) does distinguish the inputs: compatible cylinder
intersections are again CRT cylinders, so their counts determine the
joint load histogram. This is a different issue from (P13.1), which uses
two original survivor states and one fixed next class to show that
residual mass alone does not determine the deletion update.

The verifier reconstructs all47original classes and both48-label tests,
checks the full period modulo45045 against an independent86×119CRT grid,
and checks(HO1)at every integer threshold0through48 for both tests above
every old survivor:8428exact identities. The new
`rectangle_hinge_observation_gap` certificate field retains these actual
inputs and load histograms. This is an ordinary exact-arithmetic result;
it asserts neither a new hinge upper bound nor a tail continuation.

## Actual rectangle hinge bounds on the same law

The actual law in (SC1), with the same fixed C=40/31, also satisfies the
following simultaneous full-height bounds. Write
Theta_nu(t)=sup_test E_nu(L-t)_+, with the supremum over complete divisor
test layouts. The full original 3/5/7 part must divide 315; both 11 and 13
may have arbitrary finite positive heights, and all axis and point
deletions are allowed.

| t | Certified upper bound for Theta_nu(t) | Approximation |
|---|---|---|
|4|1850731457651/1285518750000|1.439676752|
|5|285616505131/257103750000|1.110899803|
|6|321137/403528|0.795823339|
|7|205590443009/321379687500|0.639712002|
|8|242331326613/499400000000|0.485244948|
|9|129498094659/312125000000|0.414891774|
|10|881984754807/2497000000000|0.353217764|
|11|165110502807/565775000000|0.291830680|
|12|47555781251/205683000000|0.231209100|

The displayed decimals are rounded upward. These are pointwise hinge
bounds on the same supported probability as (SC1), rather than a new
probability comparator. In particular the first p=17 query in (AP2) at
t=6 has charge at most 321137/4035280. The entries include the
whole-cost refinement (JC1) below, which also uses (FD2). This does not establish a complete
tail continuation.

### Concentrating the test and retaining the actual grid size

At an old survivor x, let a,b,c,d in {1,...,12} be the four complete old
test-block loads. After the actual axis deletions the carrier is an
m by n rectangle, where 0<=m<=10 and 0<=n<=12. Let k<=12 be the number
of distinct mixed point holes inside that carrier, and put Ngrid=mn-k.
For Ngrid>0 the actual clipping coefficient is

    f/120=1/max(93,Ngrid).                                  (HG1)

An empty fibre contributes zero. Put phi_t(v)=(v-t)_+. For a full
rectangle, the sum of the Ngrid largest hinge values bounds the sum on
its actual survivors. It is a convex function of every allocation of
the row, column and point blocks: it is the maximum of the sums over
all Ngrid-element subsets, each a sum of convex hinges. Enlarge the
possible allocations to the full simplices with totals b,c,d. Convexity
then permits concentration of each block on one row, one column and
one point. Components outside the carrier may first be moved into it,
which only increases the nonnegative cell loads. This is a pointwise
upper bound and does not assert that the concentrating choices arise
from one common arithmetic test layout.

The point mass can be placed at the row-column intersection. Indeed,
if two base loads satisfy u>=v, moving d from v to u cannot decrease
the sum of the Ngrid largest hinges. A selected subset taking neither
entry is unchanged. If it takes one, select the now larger entry; if
it takes both, convex increment monotonicity gives

    phi_t(u+d)+phi_t(v)>=phi_t(u)+phi_t(v+d).

The row-column intersection has the largest base load. Its point-loaded
cell is therefore retained when taking the Ngrid largest entries.
Consequently the exact concentrated upper envelope is

    K_t=[phi_t(a+b+c+d)+(n-1)phi_t(a+b)+(m-1)phi_t(a+c)
          +(m-1)(n-1)phi_t(a)-D_k]/max(93,mn-k),            (HG2)

where D_k is the sum of the k smallest nonintersection entries. These
are first the (m-1)(n-1) entries phi_t(a), then the row and column
entries ordered according to b<=c or c<=b. Formula (HG2) covers every
nonempty actual grid, including grids whose original selected
intersection or point was deleted; taking the largest surviving-count
subset was already an upper bound before concentration.

### Exact duals, point-load endpoints and empty fibres

The `actual_rectangle_hinge_profile` certificate retains one rational
dual at each t=4,...,12, of the form

    K_t <= c_t + sum_(i=0)^3 sum_(j=0)^11 w_(t,i,j) phi_j(A_i)
                 + sum_(j=0)^11 v_(t,j) phi_j(k),           (HG3)

with all w and v nonnegative. Every numerator, common denominator and
constant c_t is retained; no numerical optimizer or tolerance is part
of verification. At t=6 the particularly short dual is

    K_6 <= [psiA(a)+psiB(b)+psiC(c)+psiD(d)]/93
                     +(7/1984)phi_8(k),
    psiA=phi_1+2phi_2+16phi_3+74phi_6,
    psiB=phi_1+9phi_3+2phi_4,
    psiC=phi_2+7phi_3+2phi_4,
    psiD=phi_2.                                           (HG4)

There are 1372 nonempty triples (m,n,k). The checker uses all 12^3
values of a,b,c and the positive hinge knots of the point-load cost
in d. Before its first knot that cost is constant and the left side
increases, so the first knot bounds that entire interval. Between
successive knots, (HG2) minus the linear point cost is convex in d,
so its maximum occurs at an endpoint. Beyond the last knot, the
left-side slope is at most 1/max(93,Ngrid)<=1/93, while the checked
point-cost slope is at least 1/93. Thus the last knot bounds the
remaining d<=12. The endpoint sets, in threshold order, are

    {1}, {1,2}, {2}, {2}, {2}, {2,3}, {3}, {3}, {3}.

Multiplying by the positive common denominator and max(93,Ngrid)
reduces these checks to 26,078,976 integer inequalities. The endpoint
argument certifies all 256,048,128 original combinations. For empty
fibres the left side is zero. Nonnegative weights make the minimum
right side occur at a=b=c=d=1 and k=0; the checker verifies this
minimum is nonnegative. This check is essential because the retained
constants at t=4 and t=5 are negative.

### One arithmetic branch through higher digits and normalization

Use only the existing (SC2)--(SC6) bounds on a fixed branch (S,N):

    theta_0=M_(S,N), theta_1=M_(S,N)-1,
    theta_2=theta_(S,N)(2), theta_3=the existing shape bound,
    theta_4=theta_(S,N)(4), theta_5=the existing shape bound,
    (theta_6,...,theta_12)=(10,7,4,3,2,1,0)/N.              (HG5)

The high-threshold numerators are already checked by the complete
old profile: the five additional copies of an old load contribute
zero at every threshold at least 6, so the numerator is independent of N. The
checker identifies these numerators in all six existing profiles.
Every complete test load has these bounds on the same uniform old
law. The number k of distinct surviving mixed holes is at most the
number of active mixed labels, which is another complete old load.
Hence E phi_j(k)<=theta_j as well; no independence between deletions
and the four test blocks is assumed.

Average (HG3) on that branch to obtain B_t(S,N). Restricting further
to actual survivors of higher classes only decreases the nonnegative
low-load hinge. Write L=L_low+L_high. The elementary inequality

    phi_t(L)<=phi_t(L_low)+L_high

and the existing higher-exponent reference calculation give
integral_xi L_high<=C(89/4800)M_(S,N). In fact 89/4800 is the difference
5809/4800-143/120 between the full-height and first-power auxiliary
means, agreeing with the coefficient in (VC7). The same branch has surviving mass at least

    s_(S,N)=1-[17theta_2+4theta_4]/93-C(89/4800)M_(S,N)>0.

Therefore the normalized actual law satisfies

    Theta_nu(t) <= [B_t(S,N)+C(89/4800)M_(S,N)]/s_(S,N).    (HG6)

The certificate evaluates (HG6) separately on all 144 existing
branches and then takes the maximum. It does not combine a numerator from
one branch with the mass of another. Before the fixed-count refinement below,
the t=6 maximum is the first shape with N=81 and equals 19427/24198;
all nine are retained in `actual_rectangle_hinge_profile`. The displayed
table includes the further whole-cost refinement (JC1).

Since the actual hinge function is convex, linear interpolation
between adjacent certified knots is also a pointwise upper bound.
Taking its minimum with another valid pointwise hinge bound remains
valid. These operations do not assert that the resulting upper curve
is convex or is the hinge transform of a probability measure; (AP2)
requires only the pointwise bounds. The certificate supplies numerical
premises for that existing continuation criterion, with no new Lean
declaration and no assertion that a full tail schedule succeeds.

## Fixed-count labelled deletion refinement at threshold six

The threshold-six dual can be sharpened on the three branches where the
coarse joint-cost bound was above four fifths. Consider the first canonical
old survivor shape, `root1_same_other_column`, which has 17 points. Its five
mixed-seven labels have old cofactors `3,5,9,15,45`. Group labels that use
the same nonzero seven digit. A group deletes the union of the selected old
cylinders for its labels; overlaps inside a group count once, while groups
with different seven digits delete different lifted points.

For a complete old-45 test load A on this 17-point set U, write
H_t(A)=sum_U(A-t)_+, and let M_t be its maximum over old test layouts.
For either nonnegative hinge combination psi=sum_t w_t phi_t in (HG4), put

    Jbar_psi(A)=sum_t w_t min_(0<=s<=t) [H_s(A)+M_(t-s)],
    Kbar_psi(A)=5 sum_U psi(A)+Jbar_psi(A).

For every complete old load B, the inequality
phi_t(A+B)<=phi_s(A)+phi_(t-s)(B) proves
sum_U psi(A+B)<=Jbar_psi(A). Across the six surviving seven digits,
the additional test loads are nonnegative and sum to at most a complete
old load B. Convexity at each x gives total undeleted cost at most
5 psi(A(x))+psi(A(x)+B(x)), hence at most Kbar_psi(A) after summation.
Every actual deletion above x removes cost at least psi(A(x)), because
psi is nondecreasing. Thus if delta_x digits above x are deleted and
D=sum_x delta_x=102-N,

    N E psi(L315) <= Kbar_psi(A)-sum_x delta_x psi(A(x)).

Ineffective test cylinders can be replaced by effective ones before this
upper bound, so the complete effective layouts enumerated below dominate
all tests. For fixed A, give each x cost psi(A(x)). For a label subset T,
let b_T(u) be the least cost of a union of cardinality u, with an empty
cylinder allowed. The anchored recurrence

    d_empty(0)=0,
    d_S(D)=min_{T subset S, min(S) in T, u}
           (b_T(u)+d_(S\T)(D-u))                         (FD1)

is a lower bound for the cost removed by any actual labelled deletion with
`D=102-N` deleted points. Enlarging the feasible set by allowing empty masks
is safe in this direction: it can only reduce the minimum deleted cost and
therefore can only increase the final upper bound. The five empty residue-zero
cylinders are available on this 17-point survivor set.

Every actual deletion is represented by grouping its five original labels
by their seven digit, so (FD1) bounds its removed cost from below. Conversely,
each partition has at most five blocks and can be assigned distinct nonzero
seven digits. Cardinalities add across blocks. Nonnegative cardinalities
make truncation at D=22 sufficient for D=20,21,22.

Two cheaper lower bounds permit exact screening. Since delta_x<=5, the
removed cost is at least the sum of the D smallest costs among five copies
of each psi(A(x)). Also, for any eta>=0,

    sum_x delta_x psi(A(x))
      >= eta D - sum_(labels d) max_(a mod d)
                       sum_(x in U, x=a mod d) (eta-psi(A(x)))_+.

This follows from delta_x<=sum_d 1_(x=a_d mod d) and nonnegative positive
parts. Taking eta in {0} union {psi(A(x)):x in U} gives the screening
lower bound used by the verifier; it need not attain the best lower bound.
A layout is screened only if Kbar minus this lower bound is already at most
the target. Every remaining layout is checked using (FD1).

There are 2,164 distinct union masks and 8,919 subset-union entries. The
4,760 complete old-45 test layouts have old hinge maxima
`(42,25,11,5,2,1,0)` at thresholds zero through six. A cheap lower bound
discharges 4,688 layouts for

    psiA=(x-1)+ + 2(x-2)+ + 16(x-3)+ + 74(x-6)+,

and 4,640 for

    psiB=(x-1)+ + 9(x-3)+ + 2(x-4)+.

The exact anchored DP checks the remaining 72 and 120 layouts respectively.
For `N=80,81,82`, the resulting numerator caps are

    N E psiA <= (1986,1986,1992),
    N E psiB <= ( 728, 728, 732).                         (FD2)

The two bounds in (FD2) apply to the a and b costs of (HG4). The other
two test costs and the hole-activation hinge retain their (HG5) bounds.
The verifier checks that these cost coefficients reproduce the exact
threshold-six dual, then uses the same branch mean and surviving mass in
(HG6). Replacing only these three branches in all 144 common shape/count
branches gives

    Theta_nu(6) <= 26114497/32685768
                 = 4/5 - 170587/163428840 < 4/5.           (FD3)

The unique maximizing branch is `root1_same_other_column` with `N=79`; the
refinement changes the `N=80,81,82` branches. The corresponding first
prime-17 query costs at most `26114497/326857680`. This is an ordinary
exact-arithmetic finite-head result. It does not formalize the DP in Lean,
extend the result to unbounded 3/5/7 powers, or provide the unrestricted
tail stopping certificate.


## Whole convex costs on one old layout and deletion configuration

The same derivation applies to every nonnegative hinge combination appearing
in the rectangle witnesses, including the cost of the hole activation. For
each of the six canonical old sets U_S, put n=|U_S| and D=6n-N. For a fixed
complete effective old-45 load A, form Kbar_psi(A) as above using that shape's
hinge maxima. Let L_psi,D(A) be the maximum of the two cheap deleted-cost
lower bounds established before (FD2). Then

    N E psi(L315) <= B_psi(S,N),
    B_psi(S,N)=max_A [Kbar_psi(A)-L_psi,D(A)].              (JC1)

Both terms use the same A. This retains the relation between its hinge
costs and the energy removed by the original labelled cylinders. In
particular it improves some sums of separately maximized hinge bounds,
even without evaluating the partition DP. The possible ineffective tests
are dominated by complete effective layouts exactly as in the preceding
argument. The union-bound estimate for L remains valid when several
original labels use the same seven digit.

There are 32 distinct costs after extracting their positive common integer
factors. The verifier calculates (JC1) for all 27,720 effective layouts and
all allowed survivor counts: 21,324,800 layout/cost/count bounds. It averages
each whole cost using the smaller of B_psi(S,N)/N and the earlier sum of
individual hinge bounds. For the three applicable threshold-six branches
it also takes the smaller bound from (FD2). The hole count is bounded by a
complete old activation load, and its cost is nondecreasing; the same
whole-cost estimate therefore applies to it. No relation between that
activation load and the four test loads is assumed beyond their common
actual old shape and survivor set.

Combining these five costs with the fixed rectangle constant, then adding
higher-exponent load and dividing by the same branch's surviving mass in
(HG6), gives the table above. All 144 branches are evaluated. The refined
threshold-six maximum is

    Theta_nu(6) <= 321137/403528 < 4/5,                    (JC2)

again uniquely at `root1_same_other_column`, N=79. Seven of the nine
threshold maxima improve on the rectangle profile with (FD3); thresholds
8 and 12 retain their preceding values. The `joint_cost_hinge_refinement`
certificate field stores the normalized cost coefficients, the integer
numerator bounds, every full-height branch, and the maxima. All arithmetic
in its canonical verifier uses Python integers and fractions. The result
has the same full original 357-part-dividing-315 scope and arbitrary finite
11/13 heights, and supplies no unrestricted-tail or new Lean conclusion.

## Actual deletion vectors and a common full-height law

For every family whose original 3/5/7 part divides 315, the construction
with C=40/31 admits the following simultaneous bounds, allowing arbitrary
finite 11/13 heights and arbitrary axis and point deletions:

    Gamma <= 591122424341/16497075000 < 35.831954,
    sup_test E_nu L <= 1175795/219961 < 5.345471,
    Theta_nu(6) <= 306627/391318 < 0.783575.                 (DV1)

These are bounds for one supported probability nu for each original
family. The proof retains its actual old deletion vector throughout
the mass, moment and hinge estimates. It does not extend the original
3/5/7 exponents or establish a general tail continuation.

### Exact optimized costs of an actual deletion vector

Choose the canonical modulo-45 survivor set S by the preceding
support-shrinking reduction. All subsequent statements concern this
chosen carrier and its actual mixed-seven classes. Let b(x) count
the distinct deleted nonzero seven digits over x in S, and put
N=sum_x(6-b(x)). Five original mixed-seven labels use at most five
of the six nonzero digits. Consequently a single digit y_star survives
over every x in S, including when labels are absent, redundant or
assigned to the already excluded zero digit.

For a complete old-315 test, separate its zero-seven block A and project
its positive-seven block onto a complete old-45 load B. At each x,
concentrating the nonnegative positive-seven increments gives

    sum_(surviving y) psi(L(x,y))
      <= (5-b(x)) psi(A(x)) + psi(A(x)+B(x)).

This holds for every increasing convex psi. Conversely, choose any
actual old tests A,B, and place every positive-seven test class at
y_star. CRT realizes these residues for their original distinct test
moduli, and equality holds at every x. Thus, for the uniform law mu
on this actual old survivor set,

    N sup_test E_mu psi(L)
      = max_A [sum_x (5-b(x)) psi(A(x)) + J_psi(A)],
    J_psi(A) = max_B sum_x psi(A(x)+B(x)).                  (DV2)

Effective old test cylinders suffice: replacing an empty test cylinder
by a nonempty one only increases its load. The maximizing A can differ
between costs, but b and mu are fixed. In particular, b is sufficient
for these optimized convex costs; it need not determine an individual
test histogram or the effect or legality of a later original deletion.

The attainable b vectors also have an exact finite description. For
each labelled cofactor d in {3,5,9,15,45}, choose its cylinder on S,
allowing the empty mask. Partition the five labels by their nonzero
seven digit. A block deletes the union of its old cylinders at one
digit; summing these block indicators gives b. Conversely any such
partition uses at most five digits and is realized by CRT. Inactive
labels can be included with empty masks. This represents every original
mixed-seven assignment without an irredundancy assumption.

There are respectively 27679, 28939, 28735, 25813, 25238 and 24971
different b vectors on the six canonical shapes, totaling 161375.
The experimental verifier reconstructs these sets both by cylinder
choices and set partitions and by successive labelled digit-union
updates, then compares the complete resulting sets. It does not use
an independently optimized b for the mass denominator.

### A common matrix bound for all actual rectangles

Let an actual nonempty 11/13 fibre be an m-by-n rectangle with k
remaining point holes, where m<=10, n<=12 and k<=12. The existing
clipped density satisfies

    f/120 = 1/max(93,mn-k),    h=f(mn-k)/120.

For four nonnegative old test amplitudes A=(a,b,c,d), the row, column
and point intersection counts directly bound its low-block square by

    integral_fibre xi L_low^2 <= h a^2 + (f/120) A^T B(m,n) A,
    B(m,n) = [[0,n,m,1],[n,n,1,1],[m,1,m,1],[1,1,1,1]].

Absent test indicators only reduce this nonnegative expression. Convex
concentration within each test block extends it to arbitrary test
assignments. Set

    U=(228733,264815,215188,41873)/1000000.

For all 120 dimension pairs, the matrix
diag(U)-B(m,n)/max(93,mn-12) is positive definite. The adjacent
standard-library verifier checks exact rational LDL decompositions
and reconstructs every matrix. Since B has nonnegative entries and
A is nonnegative, this also bounds every actual k and empty fibres.
The sum of the common diagonal is 750609/1000000. Averaging its
four squares on the same old law, and using the existing marginal
and higher-exponent estimates, gives

    Gamma(nu) <= 1+[(1+750609/1000000+12259/83700)G-1]/s.  (DV3)

Here G is any simultaneous old square bound, and s is the certified
remaining mass on this same construction. The higher-exponent
coefficient is exactly (40/31)(chi0-13/8), as in (SC9).

For the first moment the three positive-exponent coefficients satisfy

    q=(fn,fm,f)/120 <= (4/31,10/93,1/93),
    sum(q)<=11/48.

All 1372 nonempty count triples satisfy these rational inequalities.
Each old test amplitude is at least one, so their unused coefficient
mass saves 23/93-11/48=9/496. Including the same high-exponent mean
coefficient 89/3720 gives

    sup_test E_nu L <= 1+[(1+1009/3720)M-1-9/496]/s.      (DV4)

Neither matrix nor first-moment refinement changes the probability law.

### Simultaneous transfer and exact arithmetic

For one b, let H_t be the unnormalized numerator in (DV2) for
psi(z)=(z-t)_+, and let G_num be its numerator for psi(z)=z^2.
Compute H_0,H_2,H_3,H_4,H_5 and G_num exactly; H_1=H_0-N because
every complete load is at least one. For t=6,...,12 retain the valid
numerator upper bounds (10,7,4,3,2,1,0). Put

    D_b=3720N-680H_2-160H_4-89H_0,
    s_b=D_b/(3720N),    ell_b=D_b/(4800N).                (DV5)

Every D_b is positive. Substituting M=H_0/N and G=G_num/N in
(DV3)--(DV4), always with this same D_b, proves the two bounds in
(DV1). Both maxima occur on the first shape at N=86, with

    M=271/86, G=1131/86, H_2/N=52/43, H_4/N=16/43,
    s_b=219961/319920.

The reference fraction is uniformly at least
ell_b>=108683/204000. Thus the existing upper-quantile comparator
may use this fraction while retaining all moment and hinge bounds
for the same nu.

For each rectangle dual, form each whole hinge cost on this b. Its
unnormalized numerator is bounded by the smaller of the sum of its
H_t bounds and the already certified (JC1) bound at this same (S,N).
The first-shape costs at N=77,...,83 can also use exact (DV2) maxima
over all actual b with that count. Including the rectangle constant
gives a numerator low_b and a positive dual denominator den. The
same high-exponent and mass transfer is

    Theta_nu(t) <= (3720 low_b+89 den H_0)/(den D_b).       (DV6)

Maximizing only after forming this ratio gives:

| t | Uniform upper bound for Theta_nu(t) |
|---|---|
| 4 | 1896712717819/1358537500000 |
| 5 | 5263525792649/4891475000000 |
| 6 | 306627/391318 |
| 7 | 306152576027/489147500000 |
| 8 | 2291713236139/4843600000000 |
| 9 | 1964369484727/4843600000000 |
| 10 | 169349448989/489147500000 |
| 11 | 21945226346/76429296875 |
| 12 | 111549448277/489147500000 |

The [actual-deletion experiment](verify_actual_deletion_profile.py)
and [exact result data](actual_deletion_profile_certificate.json)
reconstruct the complete finite geometry and costs. This separate
entry point explicitly requires NumPy; the original marked-profile
verifier remains standard-library only. Array arithmetic uses integers
with checked range bounds, and final rational comparisons use Python
integers. These are ordinary proofs with reproducible finite arithmetic,
not newly frozen Lean results. The unrestricted original 3/5/7 exponents
and a general successful tail certificate remain open.

## An actual full-fibre old configuration with unrestricted tails

Let U be the complement modulo 45 of the five classes

    (modulus, residue) = (3,0), (9,4), (5,0), (15,11), (45,2).

It has 16 points. In CRT coordinates modulo 315 put

    R = U × {1,2,3,4,5,6} ⊂ (Z/45Z) × (Z/7Z).             (BT1)

Consider a finite family of distinct odd nonunit moduli whose full original
3/5/7 part divides 315. Suppose its classes with modulus dividing 315 leave
exactly R in these coordinates. Then the family cannot cover the integers,
even with arbitrary finite 11/13 heights and arbitrary later prime factors,
exponents, cofactor supports and residues. The same assertion holds when
those old survivors contain R: the construction below uses a probability
supported on R, so it is still supported on the actual old survivors.

This is a genuine restriction on the old geometry. One complete original
315 family realizing it consists of the five displayed classes together with

    (7,0), (21,0), (35,0), (63,0), (105,0), (315,0).

All five mixed-seven classes in this example are redundant. The verifier
checks all 315 residues and obtains exactly the 96 points of (BT1). No
further move of those redundant classes is made. In particular, this result
is not an automatic removal of one branch from a procedure that first makes
every mixed-seven class effective. It does not settle unrestricted #7.

### The same supported head law throughout the continuation

Use the existing clipped construction with C_clip=40/31 on the old uniform
law on R. This is the `root2_same_other_column`, N=96 input to (SC2)--(SC10)
and (JC1). Those inequalities require only 0≤b≤5 and the labelled-cylinder
upper bound on b, so they apply with b=0. Their proof does not require a
positive effective mixed-seven deletion. In the containing-survivor case,
use this same reference law directly; none of the later distinct-label
estimates requires adding new original classes.

The old first moment, square, threshold-two hinge and threshold-four hinge
bounds on this branch are respectively

    259/96, 21/2, 23/24, 5/16.

Thus its low clipped mass is at least 1811/2232, its full clipped mass is at
least s0=88903/119040, and its density comparison fraction is
ell=s0/C_clip=88903/153600. After the actual-rectangle square saving, the
same full-height supported probability nu satisfies

    sup_L E_nu L ≤ M0 = 1134400/266709,
    sup_L E_nu L² ≤ G0 = 35754161/1333545.                  (BT2)

Its nine full-height hinge bounds, in increasing order of t=4,...,12, are

    6877275965987/6667725000000, 333388924487/416732812500,
    310127/533418, 3115275948431/6667725000000,
    475717686817/1333545000000, 2048775931829/6667725000000,
    439561169399/1666931250000, 1468244673773/6667725000000,
    589122335161/3333862500000.                            (BT3)

All moments, hinge values, high-exponent contributions and normalization
here retain this single old configuration. No maximum over other branches
is substituted at an intermediate tail query.

### A pointwise upper function with an exact finite observation

Write S=10^24, C=ceil(S M0)/S and G=ceil(S G0)/S, treating these rounded
constants as fixed exact rationals. The following construction is an upper
function for the actual hinge profile; it is not a probability comparator.

First, for 1<t≤43/13 set a=(t-1)/30, b=1-13a. Both are nonnegative, and
for every integer x≥1,

    Q_t(x)=a(x²-1)+b(x-1) ≥ (x-t)_+,
    Q_t(x)-(x-t)=a(x-6)(x-7).

The last expression is nonnegative on integer x, while Q_t(x)≥0. Therefore
a(G-1)+b(C-1) is a valid moment upper bound. For t>43/13 choose j≥7 with

    (j²-j+1)/(2j-1) ≤ t ≤ (j²+j+1)/(2j+1).

Comparing adjacent ratios (x-t)/(x²-1) shows that their positive maximum
over integers x≥2 is (j-t)/(j²-1). Hence

    E_nu(L-t)_+ ≤ (G-1)(j-t)/(j²-1).                     (BT4)

Next use the existing reference Y=X N11 N13, where X is the old comparator
and the two independent factors have probabilities
Pr(Np=1)=(p-2)/(p-1), Pr(Np=f)=p^(1-f) for f≥2. Density domination and
the actual hinge inequality give the reference upper function

    R(t)=3-t+E(Y-3)_+/ell       for 1<t≤3,
    R(t)=E(Y-t)_+/ell           for t≥3.

For t in [4,12], also use adjacent interpolation of (BT3). Let U(t) be the
minimum of all applicable reference, moment and interpolated upper bounds.
Define

    Psi(t)=C-t                         for t≤1,
    Psi(t)=max(C-t,U(t))               for t>1.            (BT5)

Then Psi dominates every actual complete-layout hinge. Its forced affine
baseline makes the following identity valid even though C is only an upper
bound on the actual first moment. For every positive integer random variable
N of finite mean and every T>1,

    E[N Psi(T/N)] = C E N - T
      + Σ_(1≤n<T) Pr(N=n) [n Psi(T/n)-Cn+T].              (BT6)

Each bracket is nonnegative by definition. This applies the finite-state
argument to Psi itself and does not replace the exact M by a rounded bound
inside the actual-profile identity (AP7).

The finite observation has a closed update. For a fixed K≥max T, retain
E N and Pr(N=n) for 1≤n<K. If an independent positive integer factor F is
adjoined, then

    E(NF)=E N·E F,
    Pr(NF=n)=Σ_(d|n) Pr(N=d) Pr(F=n/d),       n<K.         (BT7)

Every d on the right is less than K. A state at least K cannot return to
the retained range because F≥1. Equivalently, pulling observations backward
through the transition preserves the span of 1, n and the indicators
1_(n=j), j<K. Thus the full mean and finitely many point masses suffice for
all queries in this fixed schedule, without truncating the infinite mean.
This is an exact observation for the auxiliary comparison process; the
actual congruence family's labelled geometry remains an input to (AP2).

This use of the observation operator is the finite version of
[Recursive Relational Observation §32.3](https://github.com/the-omega-institute/trureturing/blob/11df59d12488feaf942a9b4c685b29c8dcc6ca4e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#32-bounded-borel-observation-uniqueness-and-order-sensitive-compact-completions).
The same volume's §33.9 distinguishes two measures with the same transition
matrix and different initial laws; here the head law and its moment/profile
bounds are fixed together. These are source connections, not additional Lean
verification or a deduction of positive residual mass from topology.

### Directed certificate and infinite continuation

Use (AP2), (AP5) and (AP6) from the Problems dossier. For each tail prime q,
put delta_q=(T_q-1)/(q-2), d_q=q-1-T_q, c_q=(q-1)/d_q. The stored threshold
runs specify the following inclusive endpoints; after one endpoint use the
next row's threshold.

| Prime endpoint | T | Prime endpoint | T |
|---:|---:|---:|---:|
|17|4|19|5|
|31|8|41|12|
|61|16|73|24|
|113|32|151|48|
|211|64|229|72|
|293|96|419|128|
|449|144|577|192|
|809|256|883|288|
|1153|384|1601|512|
|1787|576|2377|768|
|3271|1024|3719|1152|
|5051|1536|7019|2048|
|8117|2304|8191|3072|

For 8191<q≤30011 use T_q=1+floor(3(q-2)/8). The exact prime list has
pi(30011)=3246, including 2 and absent primes, and 3240 tail steps from 17.
Every step has 1<T_q<q-1 and c_q≤q. The largest threshold is 11254.

The verifier rounds every nonnegative atom, mean, correction, charge and
square upper bound upward on the S grid. Its product probabilities use
(BT7). The full first-moment multiplier is 1+1/d_q, and the square multiplier
is 1+(3q-1)/((q-1)d_q). The negative affine term in (BT6) uses the one fixed
constant C, so upward probability estimates never multiply negative
corrections.

Reference calls are evaluated by a positive convolution restricted to
N11,N13≤80. For p in {11,13}, the omitted mean is exactly

    E[Np; Np>80]
      = p^(-79) [81/(p-1)+1/(p-1)²].

The union bound on omitted factors gives an upper error
E X·(E N13·E[N11;N11>80]+E N11·E[N13;N13>80]) for every call; its upward
rounding is 1/S. Integer calls are interpolated exactly between adjacent
knots before division by ell. Thus neither reference truncation nor retained
product states discard an unaccounted tail contribution.

At B=30011 the exact total charge and moment bounds are

    C_B ≤ 951034037806531654678813/10^24,
    1-C_B ≥ 48965962193468345321187/10^24 > 0.04896,
    J_B ≤ 2001909435263859468210322417/250000000000000000000000.

Every earlier charge sum is also less than one. After the single final
conditioning in (AP6),

    Gamma ≤ 2668895569005877113728870285/16321987397822781773729
          < 163516 < 167115
          < 3246 (log 3246+log log 3246-3)².              (BT8)

The final logarithm comparison uses the existing exact positive-series
lower bound in `verify_finite_continuation.py`. Consequently the BBMST
continuation applies to every subsequent prime, proving the stated
noncoverage theorem. If the family ends earlier, extend the comparison with
absent prime coordinates; its actual violation probabilities there are zero.

The `joint_cost_branch_tail17` field contains the exact inputs, thresholds,
checkpoints, positive residual and stopping fractions. An independent
implementation uses divisor-indexed convolution, trial-division primes,
scale 10^30, reference cutoff 40 and a different rational logarithm lower
bound. It checks 15,148,804 integer moment queries and also obtains (BT8);
its Gamma upper bound differs by less than 3.01·10^-8. These are ordinary
mathematical arguments with exact arithmetic. No new Lean endpoint, freeze
or unrestricted-axis result for all old configurations is asserted.

## Retaining an original exponent label across the full auxiliary law

The conditional comparison in (AP3)--(AP4) permits a stronger order of
averaging and maximization than the separate scalar calls in (BT6).
Fix one supported head probability mu and write
F_mu(f)=sup_test E_mu f(L). Every complete head load is at least one.
Let K be the auxiliary vector of old-tail heights, independent of the
head point, and put N=product_p(1+K_p). Original exponent labels a are
fixed before K is sampled. There are exactly N labels with a<=K.
For each label define

    p_a(n)=Pr(a<=K,N=n),   w_a=Pr(a<=K),
    v_a=E[1_(a<=K)/N],
    g_a(z)=E[1_(a<=K)(z-T/N)_+].

Each original head test belonging to a is the same in every auxiliary
outcome that includes a. Applying the existing Jensen comparison,
then collecting this test's contributions before taking its supremum,
therefore gives

    d_q b_q <= sum_a F_mu(g_a).                            (FL1)

The current-prime depth weights sum to one, as in (AP4). Missing
original tuples can be completed in advance by arbitrary fixed tests;
the extra terms are nonnegative. No test choice depends on the sampled
head point. This is a direct reorganization of the existing original
label comparison, rather than a new independence assumption.

On z>=1, the exact finite-cost representation is

    f_a(z)=w_a z+sum_(1<=n<T)p_a(n)(T/n-z)_+,
    g_a(z)=f_a(z)-T v_a.                                 (FL2)

The omitted put terms vanish because n>=T. Each f_a is convex and
nondecreasing: its slope is at least w_a-sum_(n<T)p_a(n)>=0.
Since mu has mass one, F_mu(g_a)=F_mu(f_a)-Tv_a. Counting active
original labels gives the exact identities

    sum_a w_a=E N,    sum_a v_a=1,
    sum_a p_a(n)=n Pr(N=n).

All sums are legitimate. For a fixed finite physical head its test
loads have a finite bound D, so F_mu(g_a)<=D w_a; also E N is finite.
Consequently (FL1) is at most sum_a F_mu(f_a)-T.

Let C bound all first moments on this same mu, and let Psi bound all
hinges, enlarged to satisfy Psi(t)>=C-t. Define the nonnegative
quantity kappa_n=Psi(T/n)-C+T/n. Put P_a=sum_(n<T)p_a(n).
For every actual head test there is an exact decomposition

    E_mu f_a(L)=(w_a-P_a)E_mu L
       +sum_(n<T)p_a(n)[E_mu(L-T/n)_++T/n].

The mean coefficient is nonnegative. Substituting the simultaneous
upper bounds directly proves
F_mu(f_a)<=Cw_a+sum_(n<T)p_a(n)kappa_n. Thus for any selected finite
set J of original exponent labels, with certified B_a>=F_mu(f_a),

    d_q b_q <= sum_(a in J)B_a + C(E N-sum_(a in J)w_a)-T
      +sum_(n<T)[n Pr(N=n)-sum_(a in J)p_a(n)] kappa_n.    (FL3)

Every bracket in the finite correction is nonnegative, by the active
label count. The subtractions here remove exact labelled contributions
from a specified upper-bound decomposition; they do not subtract two
unrelated bounds for an unknown physical mass.

In particular, the zero exponent label is always active. For J={0},

    f_0(z)=z+sum_(n<T)Pr(N=n)(T/n-z)_+,
    d_q b_q <= B_0+C(E N-1)-T
      +sum_(n<T)(n-1)Pr(N=n)kappa_n.                     (FL4)

The linear coefficient one retains the entire auxiliary law, including
all N>=T. Only the put corrections require low multiplier probabilities.
One can take B_0 to be the smaller of a whole-cost bound and
C+sum_(n<T)Pr(N=n)kappa_n. Both bound the same F_mu(f_0), so this
choice guarantees that (FL4) is no worse than the corresponding (BT6).
Using the zero-label constants for a nonzero label would be invalid;
the general formula is (FL3).

For fixed maximum query threshold R, the probabilities Pr(N=n), n<R,
and the full mean E N form a closed observation for (FL4). Inserting
an independent positive integer multiplier updates each low probability
by divisor convolution; every predecessor of n<R is itself below R.
The full mean updates multiplicatively. For additional selected labels,
retain their restricted low probabilities p_a(n) and w_a as well.
The first and second moments and all hinge bounds must continue to
belong to the same actual head law.

Directed evaluation also preserves these distinctions. With C and Psi
fixed, upper probability and mean bounds multiply nonnegative remaining
coefficients. A rounded cost built with upper probabilities still
dominates f_0 pointwise. Before applying a theorem restricted to
increasing convex costs, verify their sum is at most one, or add
max(0,sum p_upper-1)z to restore monotonicity while keeping domination.

The finite observation principle agrees with the repository's recursive
relational observation analysis. Its newer
[convolution result, section 34](https://github.com/the-omega-institute/trureturing/blob/5744e73ad2/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)
has a different additional premise: its residual index grows by at least
one per factor. Here an auxiliary multiplier can equal one. Every finite
admitted prefix has positive probability of N=1, so that theorem's
finite-time disappearance cannot be transferred to this recursion.
The valid reduction is the explicit finite observation above. Neither
(FL3) nor (FL4) alone proves positive final residual or settles #7.

## Saturated low labels and arbitrary 3/5/7 heights

Fix P={3,5,7}, h=(2,1,1), the nonempty survivor set Omega of a
finite family of distinct nonunit divisors of 315, and one probability
mu on Omega. Let lambda extend
mu by independent uniform higher prime digits, up to the original
family's arbitrary finite heights. The following transfer preserves
every original modulus and works for nonuniform mu. The separate
ambient-density estimate below requires uniform mu.

For J contained in P, put

    D_J={d dividing 315 : v_p(d)=h_p for every p in J}.

Every higher original modulus has the unique representation

    m=d product_(p in J) p^e_p,
    J={p:v_p(m)>h_p}, e_p=v_p(m)-h_p>=1,
    d=product_p p^min(v_p(m),h_p) in D_J.                 (SH1)

Distinct tuples (J,e,d) remain distinct original labels even when they
project to the same d. A test block at fixed (J,e) chooses one low
residue for each d in D_J; different e may choose different low tests.
The seven nonempty restricted families have 4,6,6,2,2,3,1 labels,
in the order {3},{5},{7},{3,5},{3,7},{5,7},{3,5,7}.

For their complete low test families define

    M_J=max_A E_mu A,        C_JK=max_(A,B) E_mu AB,
    H_mu(t)=max_A E_mu(A-t)_+,  A in the empty-J family.

The two choices in C_JK are independent choices from their respective
families. In particular C_JJ=max_A E_mu A^2: Cauchy--Schwarz gives
the upper bound and A=B attains it. Include the unit divisor in the
empty-J family, so every complete low or full test load is at least one.

### The eight-type moment kernel

For each p let

    alpha_p=sum_(e>=1)p^-e=1/(p-1),
    beta_p=sum_(e,f>=1)p^-max(e,f)=(p+1)/(p-1)^2,
    a_J=product_(p in J)alpha_p,
    K_JK=product_(p in J symmetric_difference K)alpha_p
          product_(p in J intersection K)beta_p.         (SH2)

Here the set K in the subscripts is distinct from the matrix K.
The matrix is the tensor product over p=3,5,7 of
[[1,alpha_p],[alpha_p,beta_p]]. Its local pairs (alpha,beta) are
(1/2,1), (1/4,3/8), and (1/6,2/9). Finite physical heights use
the corresponding finite sums, which are bounded by these limits.

Write an actual full test load as L=A0+U, where U contains exactly
the higher labels. Then, for the same lambda,

    E_lambda U <= r=sum_(J nonempty)a_J M_J,
    E_lambda A0 U <= c=sum_(J nonempty)a_J C_empty,J,
    E_lambda U^2 <= s=sum_(J,K nonempty)K_JK C_JK,
    E_lambda L^2 <= C_empty,empty+2c+s.                  (SH3)

To prove this, condition on the low point. Saturation in (SH1) means
the low class already fixes all h_p low digits at every p in J.
One higher label therefore contributes its low indicator times
product p^-e_p. Two higher cylinders at a common prime are either
incompatible or nested, so their joint probability is at most
p^-max(e_p,f_p). Different prime coordinates are independent under
lambda. Sum these bounds over the complete original tuples and use
M_J and C_JK. This proves (SH3) for every finite height without
assuming independence between overlapping classes. The square sum
is ordered. Its different terms need not have simultaneous maximizers.

For every real t and u>0 the elementary pointwise bounds

    (A0+U-t)_+ <= (A0-(t-u))_+ +(U-u)_+,
    (U-u)_+ <= U,          (U-u)_+ <= U^2/(4u)

give the uniform-in-height profile transfer

    E_lambda(L-t)_+
      <= inf_(u>0) [H_mu(t-u)+min(r,s/(4u))].            (SH4)

H_mu is defined on all real thresholds. Since A0>=1, its extension
below one is H_mu(t)=M_empty-t. Since A0<=12, for t>12 the choice
u=t-12 gives the simpler min(r,s/(4(t-12))).

With the low projected residues fixed, every higher test prefix may
also be centered at zero. Conditional on the low point and the other
prime coordinates, the indicators then form a nested family with
their prescribed probabilities. Such a comonotone coupling maximizes
every increasing convex cost of a nonnegative weighted sum. Successive
centering in the three coordinates preserves the preceding centerings;
CRT realizes each resulting test residue without changing its low
projection. This comparison concerns lambda. It moves no original
forbidden class and makes no assertion about concentration after
conditioning on those forbidden classes.

### Actual deletion and the supported probability

Let F avoid all actual higher forbidden classes, q=lambda(F), and
nu=lambda(.|F). Completing missing test labels only adds nonnegative
terms, so their expected forbidden count is at most r and q>=1-r.
For uniform mu write delta=|Omega|/315. The existing density theorem
(CM8) in the Problems dossier then also gives delta*q>=53/432.
Consequently the following valid lower denominators are

    q_* = max(53/(432 delta),1-r)  for uniform mu;
    q_* = 1-r                    for any mu with r<1.

For the same lambda, F and nu,

    E_nu L^2 <= 1+(C_empty,empty-1+2c+s)/q_*,
    E_nu(L-t)_+ <=
      inf_(u>0)[H_mu(t-u)+min(r,s/(4u))]/q_*.            (SH5)

The square uses L^2-1>=0 before conditioning; its numerator is
nonnegative, so replacing q by q_* preserves the upper-bound direction.
The density alternative is unavailable for nonuniform low weights.
If low normalization added a class or moved a redundant class into
an effective position, nu is uniform on the strengthened family's
survivors and merely supported on the original family's survivors.
Only when Omega was the original low survivor set is it the original
unmodified full survivor law. No step replaces nu's low marginal by mu.

The adjacent certificate gives an explicit conditioning obstruction.
Choose a class a modulo 9 of positive mu-mass eta in its N=86 head,
and lift uniformly to period 945. Compare deletion of a modulo 27
with deletion of a+9 modulo 27. Both have the same low projection
and q=1-eta/3. For the fixed test 1+1_(x=a mod 27), the conditional
hinges at one are 0 and eta/(3-eta), and the squares are 1 and
1+3eta/(3-eta). Thus those compressed observations do not determine
the conditional cost; the centering comparison cannot be carried
through an unspecified deletion event.

### Exact low geometry and stronger truncation constants

For a normalized marked head, use its old45 carrier S and actual
deletion vector b from (DV2). For I contained in {3,5}, let T_I
be the complete old45 cofactor tests restricted to cofactors saturated
at the primes in I. Set I=J intersect {3,5} and let

    V_J=T_I times T_I   if 7 is not in J,
    V_J={0} times T_I   if 7 is in J.

For the uniform low315 law, with N=sum_x(6-b(x)), the globally unused
seven digit gives the exact finite optimization

    N M_J=max_((u,v) in V_J) sum_x[(6-b(x))u(x)+v(x)],
    N C_JK=max_((u,v) in V_J,(w,z) in V_K)
      sum_x[(5-b(x))u(x)w(x)+(u(x)+v(x))(w(x)+z(x))].   (SH6)

Indeed, expand the product at each low45 point. Its seven-containing
cross terms are at most uz+wv+vz; putting all such tests at the
common unused digit attains all three simultaneously. This proves
the product identity directly, without treating a bivariate product
as convex. For weights w_x common to the surviving digits over x,
multiply each summand by w_x and replace N by sum_x(6-b(x))w_x.
Thus (SH6) also supplies costs on that single nonuniform law.

There are useful explicit uniform bounds without optimizing (SH6).
If Omega avoids a class at each of 3,5,7, every cylinder d dividing315
obeys

    delta mu(a mod d) <= (1/d) product_(p not dividing d)(1-1/p).

Sum these bounds for D_J and for all ordered lcm intersections in
C_JK, then apply (SH2). This yields

    delta r<=103/720,  delta c<=7/9,
    delta s<=713/945,  delta(2c+s)<=2183/945.

The normalized heads also avoid an effective pure9 class disjoint
from the pure3 class. In cylinders with v_3(d)=0 the surviving
ternary proportion is therefore 5/9 rather than 2/3. For positive
v_3(d) the previous worst-case cap remains valid. The strengthened
result is

    delta r<=97/720,   delta c<=34/45,
    delta s<=16693/22680,
    delta(2c+s)<=10193/4536.                             (SH7)

For completeness, these sums have an independent product evaluation.
For each p set rho_3=4/9, rho_5=1/5, rho_7=1/7 and

    A_inf(p)=p/(p-1)-rho_p,
    A_low(p)=sum_(a=0..h_p)p^-a-rho_p,
    B_inf(p)=p(p+1)/(p-1)^2-rho_p,
    B_low(p)=sum_(a=0..h_p)(2a+1)p^-a-rho_p,
    D(p)=sum_(a=0..h_p)(a+1+1/(p-1))p^-a-rho_p.

The right sides for delta r, delta c and delta s are respectively
product A_inf-product A_low, product D-product B_low and
product B_inf-2 product D+product B_low. This proves (SH7) by
rational geometric sums. Compared with the previous ambient square
error 733/252, the error falls by 3001/4536. With the identical
density denominator 53/432 the saving is 6002/1113. This is a
truncation-error improvement; it does not by itself improve the
separate full357 square bound 3849/106 in (SD1).

### Twelve cylinder caps for optimizing the low probability

For arbitrary mu let m_d=max_a mu(a mod d), d dividing315, and set

    gamma_d=product_(p:v_p(d)=h_p)p/(p-1)-1.

For an ordered pair d,e, define gamma_de as the product of the
following prime factors, minus one:

    1                 if both exponents are below h_p,
    p/(p-1)           if exactly one exponent equals h_p,
    p(p+1)/(p-1)^2     if both exponents equal h_p.

Grouping (SH3) by the original labels' low projections proves

    R_high=sum_d gamma_d m_d,
    Delta_square=sum_(d,e)gamma_de m_lcm(d,e),
    q>=1-R_high,
    E_lambda L^2<=Gamma_low+Delta_square.                (SH8)

Here Gamma_low bounds the exact complete low square on this same mu.
If R_high<1, the supported full357 probability satisfies

    Gamma_nu <= 1+(Gamma_low-1+Delta_square)/(1-R_high).  (SH9)

All twelve cylinder caps are maxima of linear functions of the low
weights. They can therefore be optimized together with the exact
low square using epigraph constraints; (SH9) permits a linear
fractional transformation. The original high residues remain arbitrary.
This establishes a finite optimization route at unrestricted 3/5/7
heights, without importing uniform-density bounds into a changed law.

`verify_saturated_height.py` reconstructs the adjacent
`saturated_height_certificate.json` with exact standard-library arithmetic.
It checks six finite height boxes and 384 kernel entries by direct
exponent summation, both product and restricted-family evaluations
of (SH7), the twelve/144 regrouped coefficients, and three actual CRT
families of period 33075. The CRT cases check lifted moments, centering,
hinges and conditioning; a separate period945 case checks the
relative-position obstruction. The unrestricted-height conclusions
follow from the ordinary arguments above, not from the finite cases.
Run `python3 -I -O docs/reports/erdos7-odd-covering/verify_saturated_height.py`
from the repository root. No new Lean declaration or unrestricted #7
conclusion is supplied by this transfer.

### A common weighted low layout and a nonnegative tail correction

The independent cylinder caps in (SH8) can lose the joint geometry.
There is a stronger finite observation that keeps a single complete
weighted low layout in each auxiliary outcome. Let Z_3,Z_5,Z_7 be
independent nonnegative integers with

    Pr(Z_p>=k)=p^-k,   Pr(Z_p=k)=(p-1)/p^(k+1).

For d dividing315 set

    w_d(Z)=product_(p:v_p(d)=h_p)(1+Z_p),
    F_mu(Z)=max_(a_d mod d)
      E_mu [sum_(d dividing315)w_d(Z)1_(x=a_d mod d)]^2.

Then every full test at arbitrary finite 3/5/7 heights satisfies

    E_lambda L^2 <= E_Z F_mu(Z).                         (SH10)

To see this, first center the additional test prefixes as above,
keeping every low residue fixed. For fixed matching depths Z, the
number of active original labels projecting to d is
product_(p saturated in d)(1+min(Z_p,n_p)), where n_p is the physical
extra height. Average their low cylinder indicators. This average
belongs to the convex hull of the cylinder indicators for that d,
with coefficients independent of x. The squared norm of the sum
is convex on the product of these finite convex hulls. Applying
Jensen, one cofactor at a time, bounds it by a vertex value: one
actual low cylinder for each d, chosen jointly for the entire cost.
Finally increasing min(Z_p,n_p) to Z_p adds nonnegative weights.
This proves (SH10), and also shows why choosing a different residue
at each point x is not allowed. The vertex choice may depend on Z;
the bound does not assert a single optimizer for all Z. The convex
hull step directly reuses Mathlib's `ConvexOn.le_sup_of_mem_convexHull`.

For the marked heads of (SH6) the same globally unused seven digit
evaluates F_mu(Z) by only two weighted old45 layouts. In each such
layout give cofactor c dividing45 weight

    v_c(Z)=(1+Z_3)^(1_(9 divides c))
             (1+Z_5)^(1_(5 divides c)),
    A_Z(x)=sum_(c dividing45)v_c(Z)1_(x=a_c mod c),

and define B_Z with independently chosen old45 residues. For low
weights u_x common to the surviving seven digits, normalized by
R=sum_x(6-b(x))u_x, the exact identity is

    R F_mu(Z)=max_(A_Z,B_Z) sum_x u_x [
      (5-b(x))A_Z(x)^2
        +(A_Z(x)+(1+Z_7)B_Z(x))^2].                     (SH11)

In particular F_mu(0)=G is the exact unweighted low square.
All high original labels are still accounted for by their matching
depths; this expression does not identify them as the same modulus.

An exact polynomial upper bound controls the unbounded auxiliary
depths without discarding their contribution. Write

    P_mu(Z)=sum_(d,e dividing315)w_d(Z)w_e(Z)m_lcm(d,e),
    c0=P_mu(0)-G>=0.

For every fixed complete low layout, each ordered pair satisfies
mu(C_d intersect C_e)<=m_lcm(d,e). Thus its weighted deficit from
P_mu(Z) is a sum of nonnegative terms. Every coefficient w_d w_e
is at least one, so this deficit is at least the same layout's
unweighted deficit, hence at least c0. Minimizing over the layouts
proves P_mu(Z)-F_mu(Z)>=c0 for every Z. Also (SH8) gives
E_Z P_mu(Z)=P_mu(0)+Delta_square, using only the geometric first
and second moments of each 1+Z_p.

Consequently for any finite set B of auxiliary depth triples,

    E_lambda L^2 <= G+Delta_square
      -sum_(z in B) Pr(Z=z)[P_mu(z)-F_mu(z)-c0].         (SH12)

Every correction is nonnegative. The omitted depths retain the
entire baseline saving c0, so a small evaluated set already gives
a valid improvement whenever one of its corrections is positive.
Larger sets preserve the previous bound monotonically. The same
formula remains valid if F_mu(z) is replaced by a certified upper
bound B_z and its correction by max(0,P_mu(z)-B_z-c0).
Divide the resulting square-minus-one by the appropriate same-law
denominator in (SH5). This finite calculation controls arbitrary
physical heights; it does not move the actual deletion event or
reuse a uniform-density denominator for nonuniform weights.

The corrected upper bound has a convex form useful for joint weight
optimization. Put beta=Pr(Z in B) and

    eta_out(d)=E_Z[1_(Z not in B)
      sum_(lcm(e,f)=d)(w_e(Z)w_f(Z)-1)]>=0.

Rearranging (SH12) gives the identical expression

    U_B(mu)=(1-beta)G(mu)+sum_d eta_out(d)m_d(mu)
                +sum_(z in B)Pr(Z=z)F_mu(z).            (SH13)

Every coefficient is nonnegative and independent of mu. Each of G,
m_d and F_mu(z) is the maximum of finitely many linear functions of
the low probability. Thus U_B has a finite epigraph representation,
and `1+(U_B(mu)-1)/(1-R_high(mu))` admits the same linear fractional
transformation as (SH9). The coefficients eta_out are exact: subtract
the finite-box terms from the infinite geometric coefficients in
(SH8). Nonnegativity follows from their displayed expectation, rather
than from a numerical tolerance. All expectations are finite since
each Z_p has a finite second moment.

### An exact obstruction to optimizing the independent cylinder formula

There is an actual low family for which changing fibre weights alone
cannot make the particular formula (SH9) improve 3849/106. This is
a limitation of that upper-bound formula, not a lower bound for
the actual worst test moment or for arbitrary supported probabilities.

Take the eleven original classes (modulus,residue)

    (3,0),(9,4),(5,0),(15,11),(45,1),(7,0),
    (21,1),(35,9),(63,10),(105,74),(315,82).

The five old45 classes leave

    S=(2,7,8,14,16,17,19,23,28,29,32,34,37,38,43,44).

The five mixed-seven classes delete digits 1,2,3,4,5 respectively,
giving the actual deletion vector and fibre sizes

    b=(0,1,0,2,1,0,3,0,2,2,0,2,3,0,1,2),  r=6-b.

There are 77 survivors modulo315, with digit6 surviving over every
point of S. Consider every nonnegative weight vector w with
sum_x r_x w_x=1, assigning probability w_x to each surviving seven
digit over x. This allows unequal fibre totals but requires equal
point weights within each fibre.

Let G(w)=F_mu(0) be the exact low square from (SH11), and let
R(w)=R_high and Delta(w)=Delta_square from (SH8). On the nonempty
domain R(w)<1 the independent-cylinder formula satisfies

    1+[G(w)-1+Delta(w)]/[1-R(w)]
      >=101816531/2603049 >3849/106.                     (SH14)

The excess is exactly 773416685/275923194. Uniform point weights
w_x=1/77 have R=1825/3696<1, so this is not a vacuous assertion.
It does not exclude (SH12), which retains joint layouts, nor
probabilities with unequal weights inside a seven-digit fibre.

Here is a finite rational proof of the universal quantifier over w.
Use the nonnegative linear fractional variables

    v_x=w_x/(1-R),  t=1/(1-R),
    zG=G/(1-R),     z_d=m_d/(1-R).

Writing eta_d=sum_(lcm(e,f)=d)gamma_ef, these variables satisfy

    sum_x r_x v_x-t=0,
    t-sum_d gamma_d z_d=1,
    z_1-t=0.

Every actual low cylinder gives its mass constraint with upper
variable z_d. Every actual pair of old45 layouts gives its square
constraint with upper variable zG. Thus each chosen constraint
has the form A_i x<=0, with x=(v,t,zG,(z_d)). The objective in
(SH14) is 1+c x, where c x=zG-t+sum_d eta_d z_d.

The adjacent certificate specifies 21 actual cylinder constraints
and five actual pairs of old45 residue assignments, together with
rational multipliers y_i<=0 and three free equality multipliers z.
For the equality matrix E and right side b0=(0,1,0), it verifies

    A^T y+E^T z<=c  in all 30 coordinates,
    1+z dot b0=101816531/2603049.

Hence c x>=y^T A x+z^T E x>=z dot b0, proving (SH14).
Only valid explicit layout constraints are needed for this lower
bound; no exhaustive maximization or LP solver is part of its replay.

`verify_fiber_uniform_saturated_envelope_obstruction.py` uses the
adjacent `fiber_uniform_saturated_envelope_obstruction_certificate.json`.
It reconstructs the original family and all 315 residues, the actual
deletion vector, all saturated coefficients, all 26 constraints,
and the rational dual inequality. Run it with `python3 -I -O`.
The standalone certificate proves (SH14); it makes no claim about
attainment, the optimal joint-layout formula, or unrestricted #7.

### Grouping deletions by their single extra prime coordinate

The union bound for the survival denominator can also preserve
joint geometry. For p in {3,5,7}, choose E_p contained in D_{p}
with |E_p|<=p-1, and let A_p range over complete low test loads
with exactly one cylinder for each d in E_p. Put alpha_p=1/(p-1).
Define

    U_E(mu)=max_(A_3,A_5,A_7)
       E_mu[1-product_p(1-alpha_p A_p)],
    rho_d=gamma_d-sum_(p:d in E_p)alpha_p>=0,
    R_E(mu)=sum_d rho_d m_d(mu)+U_E(mu).

For the actual higher deletion event F from (SH5),

    lambda(F)>=1-R_E(mu).                               (SH15)

In particular this bound applies to a changed low probability;
it uses no ambient uniform-density assumption.

To prove it, group precisely the original labels (J,e,d) with
J={p} and d in E_p. Conditional on the low point x, the three
groups' hit events depend on disjoint additional prime coordinates
and are independent. Writing their probabilities as u_p(x), the
probability that at least one group hits equals
1-product_p(1-u_p(x)). Within a group the union
bound gives

    u_p(x)<=sum_(e>=1)p^-e A_(p,e)(x),

where each A_(p,e) is one complete E_p layout. Complete absent
labels arbitrarily. Dividing the coefficients by alpha_p writes
this upper bound as alpha_p times a convex combination of complete
layouts. At finite heights the remaining coefficient can likewise
be filled by any layout, only increasing the bound. Its value is
between zero and alpha_p |E_p|<=1.

The function 1-product_p(1-u_p) is nondecreasing in each coordinate
on this cube. After substituting the upper bounds, it is affine in
each of the three layout averages with the other two fixed.
Successively maximizing over their convex hulls therefore gives
the finite vertex maximum U_E. This operation chooses complete
layouts independent of x. The remaining original labels are
bounded by their separate cylinder masses. Removing exactly the
chosen singleton-J contributions from gamma_d gives rho_d>=0
by the subset expansion in (SH2), and proves (SH15).

Every integrand defining U_E is nonnegative and fixed before mu
is chosen. Thus R_E is a nonnegative sum of maxima of linear
functions of mu. It is no larger than the preceding R_high:
the pointwise union polynomial is at most sum_p alpha_p A_p,
whose separate maxima sum to the removed cylinder terms.
Consequently any square bound U_B from (SH13) gives, when R_E<1,

    Gamma_nu<=1+(U_B(mu)-1)/(1-R_E(mu)),                 (SH16)

on the same actual conditioned law. This is another finite convex
epigraph and linear fractional optimization, with a stronger
denominator as well as the joint numerator.

For marked heads there is a compact evaluator with

    E_3 contained in {9,45},
    E_5 contained in {5,15,45},
    E_7={7c:c dividing45}.

These choices meet the required size bounds. Write a=A_3/2 and
b=A_5/4; both are functions only of the old45 point. For normalized
per-digit weights w_x and fibre sizes r_x, the globally surviving
seven digit gives

    U_E=max_(A_3,A_5) [sum_x r_x w_x(a_x+b_x-a_x b_x)
      +(1/6)sum_(c dividing45) max_(t mod c)
          sum_(x=t mod c)w_x(1-a_x)(1-b_x)].             (SH17)

The last factors are nonnegative. For every cofactor c, assigning
its seven part to the globally surviving digit dominates any
other digit pointwise for that weighted mass. The six choices
then maximize independently. This centering concerns the low
test calculation defining U_E; it does not center the original
higher forbidden classes. Choosing only E_3={9}, E_5={5} already
retains the full seven group. Using both larger sets preserves
the same proof and cannot worsen the bound: the increase of the
union polynomial is at most the sum of the added alpha-weighted
loads, whose cylinder maxima were removed from the separate sum.

### A certified common-law improvement at unrestricted 3/5/7 heights

Let Omega be the 77-point survivor set of the eleven classes in
(SH14). For every finite distinct odd family using only 3,5,7,
whose complete low315 survivors contain Omega, all higher original
exponents and residues may be arbitrary. There is one probability
nu supported on its actual full survivors with

    Gamma(nu)<=2512626164927510733601/70505216618162484375
              <35.637451<3849/106.                      (SH18)

Here Gamma is the supremum of the second moment over complete
tests with one class for each original-period divisor, including
one. Padding low coordinates to 315 and completing test labels
only adds nonnegative contributions. The low geometry remains
a hypothesis; (SH18) is not a new bound for every three-prime
family or for unrestricted odd prime support.

Give each surviving seven digit over the ordered old45 points in
(SH14) the following integer weight, divided by 99999992:

    (1120062,1267867,1115811,1440615,
     1305700,1120062,1802478,1115811,
     1668294,1440615,1120062,1449636,
     1818198,1115811,1253063,1440615).

The r-weighted sum is exactly 99999992. Extend this low law
uniformly in the additional prime coordinates and condition
on all actual higher forbidden classes. Use (SH17) with
E_3={9,45}, E_5={5,15,45}, and the complete six-label E_7.
Exact maximization gives

    U_E=1777961435/4799999616,
    sum_d rho_d m_d=74007725/799999936,
    lambda(F)>=2577991831/4799999616>0.

For the same low law, take the auxiliary box
0<=Z_3<=8, 0<=Z_5<=5, 0<=Z_7<=4. The common-layout formula
(SH12), independently evaluated in the positive form (SH13), gives

    E_lambda L^2<=1286697806403687124613/65637332249013000000.

Substitution in (SH16) proves (SH18). Its exact saving over
3849/106 is 5036205280991264597669/7473552961525223343750.
No original high class is centered, and the numerator and
denominator belong to the same lifted and conditioned probability.

`verify_saturated_joint_head.py` replays the adjacent
`saturated_joint_head_certificate.json` using NumPy and exact
integer arithmetic. It reconstructs the actual315 survivors
and all 4480 active old45 layouts directly from the original
classes. Empty old cylinders are dominated by nonempty ones
for the nondecreasing costs used here. The 270 depth maxima
therefore examine all 5,419,008,000 ordered square-layout pairs;
the grouped deletion calculation examines all 35,840 pairs
of the two low layout families. Every maximizing value is
also checked with Python integers. The largest certified
integer range is 5,074,124,123,068, below 2^63. Geometric tails,
conditioning and the strict comparison use exact fractions.

Run `python3 -I -O docs/reports/erdos7-odd-covering/verify_saturated_joint_head.py`.
This requires no solver, saved layout cache, or scratch experiment
files. An independent standard-library calculation also checks
the complete grouped denominator. The all-height theorem uses
the ordinary arguments (SH10)--(SH17); this is not an end-to-end
Lean result or an optimality claim for the selected weights.

### Convex costs on the same arbitrary-height probability

The common-layout argument also supplies the observations needed by
subsequent prime steps. Keep the actual low law mu, its independent
higher-digit lift lambda, and its actual conditioned law nu from (SH18).
For a nonnegative increasing convex function h, define

    F_h(z)=max_(one low cylinder per d)
      E_mu h(sum_(d dividing315)w_d(z)1_(x=a_d mod d)).

The prefix centering and convex-hull argument of (SH10) give

    E_lambda h(L)<=E_Z F_h(Z).                          (SH19)

Center only the test prefixes before conditioning. Conditional on the
low point and other prime coordinates, their nested coupling maximizes
each convex cost, as in the earlier survivor-weighted comparison (C1).
For fixed depths, Jensen then replaces each cofactor's average indicator
by one cylinder, with mixing coefficients independent of the low point.
These two steps hold for h as well as for the square. The auxiliary
expectation may be infinite for unrestricted h; the hinge bounds below
are finite. Under fibre-constant weights w_x with sum_x r_x w_x=1,
the common surviving seven digit gives the exact formula

    F_h(z)=max_(A,B) sum_x w_x[
      (r_x-1)h(A_x)+h(A_x+(1+z_7)B_x)].

Let F_2 denote the square cost, and let U_B and beta be the square
upper bound and depth-box mass in (SH13). Put

    V_out=U_B-sum_(z in B)Pr(Z=z)F_2(z)-(1-beta)>=0.

For any integer threshold t>=1,

    H_lambda(t)<=sum_(z in B)Pr(Z=z)F_((.-t)_+)(z)
                      +t V_out/(4t^2-1),
    H_nu(t)<=H_lambda(t)/q_*.                           (SH20)

Indeed every complete load is an integer k>=1 and
(k-t)_+<=t(k^2-1)/(4t^2-1). On the positive branch the cleared
majorant difference is (k-2t)(t(k-2t)+1)>=0, by integrality;
equality at k=2t shows the coefficient is exact. Apply this inequality
outside the box, then use its complete square-minus-one budget V_out.
The box complement is never discarded. Conditioning only divides the
nonnegative hinge integral by its same-law lower denominator q_*.

There is an exact elimination of the two modulus45 choices. It makes
these convex observations substantially cheaper without approximating
the maximizing layout. Fix base old45 layouts A0,B0 omitting45, and put
v=(1+z_3)(1+z_5), u=1+z_7, X=A0+uB0. Their baseline cost is

    C=sum_x w_x[(r_x-1)h(A0_x)+h(X_x)].

For each old45 point i, define the increments

    a_i=w_i[(r_i-1)(h(A0_i+v)-h(A0_i))+h(X_i+v)-h(X_i)],
    b_i=w_i[h(X_i+uv)-h(X_i)],
    j_i=w_i[(r_i-1)(h(A0_i+v)-h(A0_i))
                      +h(X_i+(1+u)v)-h(X_i)].

The exact best cost after restoring both singleton45 labels is

    C+max(max_i a_i+max_j b_j, max_i j_i).               (SH21)

Different-point choices give a_i+b_j; coincident choices give j_i.
Convexity implies j_i>=a_i+b_i. If the independent maxima use
different points they are attained; if they coincide their value is
dominated by the attainable same-point choice. This proves both
inequalities in (SH21). Nonempty45 cylinders are precisely singleton
points, and empty choices are dominated by nonempty choices for these
costs. On the (SH18) carrier there are only 280 base layouts, compared
with 4480 after restoring45, so each convex query uses 78,400 base
pairs instead of 20,070,400 full pairs. The proof also applies to other
finite carriers with the stated singleton structure.

### A direct threshold-two correction and simultaneous bounds

Threshold two has an additional exact linear decomposition. For a
complete old45 layout A with weights v_c(z_3,z_5) from (SH11), put

    m_A(z)=max_A sum_x r_x w_x A_x,
    m_B(z)=max_B sum_x w_x B_x,
    bonus(A)=sum_x(r_x-1)w_x 1_(A_x=1),
    g(z_3,z_5)=max_A[bonus(A)-(m_A(z)-sum_x r_x w_x A_x)].

All cofactor weights are positive, so A_x=1 means that none of its
five nonunit old45 cylinders hits x; this observation is independent
of the depths. Since A>=1 and A+(1+z_7)B>=2, direct expansion gives

    F_((.-2)_+)(z)=m_A(z)+(1+z_7)m_B(z)-2+g(z_3,z_5).
                                                               (SH22)

The mean deficit of each layout is a sum of nonnegative individual
cylinder deficits multiplied by v_c. Each v_c is nondecreasing in
z_3,z_5. Thus g is nonincreasing in each coordinate. Also g>=0:
choose each cylinder to attain its independent mean maximum, leaving
zero deficit and a nonnegative bonus. The expected linear part in
(SH22), before subtracting two, is exactly

    M_lambda=sum_(d dividing315)(1+gamma_d)m_d.

For a finite box 0<=z_3<=n_3, 0<=z_5<=n_5, write
pi_p(k)=(p-1)/p^(k+1) and t_p=p^(-(n_p+1)). Monotonicity yields

    E g <= sum_(inside)pi_3(z_3)pi_5(z_5)g(z_3,z_5)
      +t_3 sum_(z_5<=n_5)pi_5(z_5)g(n_3+1,z_5)
      +t_5 sum_(z_3<=n_3)pi_3(z_3)g(z_3,n_5+1)
      +t_3 t_5 g(n_3+1,n_5+1).                         (SH23)

The three complement regions are disjoint and exhaust both infinite
tails. This gives H_nu(2)<=(M_lambda-2+E g upper)/q_* without
charging the omitted higher depths to a square bound.

On exactly the probability and low geometry in (SH18), use its
270-point box in (SH20), and n_3=12,n_5=8 in (SH23). The same
probability nu simultaneously satisfies

    E_nu L<=19618622895502373704/3964266656997890625
            <4.948866,
    E_nu L^2<=2512626164927510733601/70505216618162484375,
    E_nu(L-t)_+<=H_t,                                   (SH24)

where the displayed decimal bounds are rounded upward:

| t | H_t upper |
|---|---|
| 2 | 2.948865602 |
| 3 | 2.058624315 |
| 4 | 1.420795591 |
| 5 | 1.089549227 |
| 6 | 0.808227449 |
| 8 | 0.504434647 |
| 10 | 0.338457518 |
| 12 | 0.217859420 |

Every entry has an exact fraction in the adjacent certificate.
In particular H_2=11690089581506592454/3964266656997890625 and
H_6=171123706666048609715948/211727165504341940578125.
The mean follows from L<=2+(L-2)_+. Between listed thresholds,
the chord of the two hinge upper bounds is valid by convexity in t;
below two, H_2+2-t is valid. These are bounds for every complete
test on one fixed law. Taking a different law for each cost is not
part of the construction. All original3/5/7 heights remain arbitrary;
the specified low geometry remains a hypothesis.

### A same-law two-prime consumer

The pure-power charge bound (AP2), its convex comparison (AP3)--(AP4),
square bound (AP5) and final conditioning (AP6) consume (SH24) directly. Let G be
its square bound and use thresholds T_11=4, T_13=5. The first charge
is at most H_4/6. Its comparison multiplier N has

    E N=7/6, Pr(N=1)=28/33, Pr(N=2)=50/363.

At the next prime, use H_5 at N=1, the chord
H(5/2)<=(H_2+H_3)/2 at N=2, and H(t)<=2+H_2-t at N>=3.
The complete remaining multiplier tail is handled by E N. Thus

    b_11<=H_4/6,
    b_13<=[131 H_2/726+50 H_3/363+28 H_5/33+2/121]/7,
    J_13<=(1403/630)G,
    q_13>=1-b_11-b_13,
    Gamma_13<=1+(J_13-1)/q_13.                          (SH25)

Here the charges are those of the physical probability chain in
(AP2), and q_13 is measured relative to its normalized starting
law nu. This is not an assertion that the conditional low marginal
remains mu. The old period Q is the full3/5/7 part of the entire
original family's period, including exponents occurring in later-prime
moduli. Uniformly pad the (SH18) lift to these physical heights before
conditioning. Likewise extend11/13 to their full physical heights.
The distortion parameters are delta_11=1/3, c_11=5/3<=11 and
delta_13=4/11, c_13=12/7<=13, as required by (AP5).
With the exact (SH24) inputs,

    q_13>=1769882874608640689865554/3455108140373052546796875,
    Gamma_13<=3815365447008599276017720573/24778360244520969658117756
               <153.979740.

This allows arbitrary finite11/13 heights and residues in addition
to the arbitrary3/5/7 heights already present in (SH18). It supplies
a supported probability for further prime steps under that same low
geometry, not a general tail continuation or a solution of #7.

`verify_saturated_convex_profile.py` reconstructs its adjacent
`saturated_convex_profile_certificate.json`. The (SH18) certificate
is a hash-bound prerequisite checked by `verify_saturated_joint_head.py`.
The new replay checks all2160 hinge observations, compares the reduced
square evaluator with every one of the270 independently enumerated
square maxima, and checks the direct threshold-two identity against
all270 hinge observations. It reconstructs140 two-coordinate correction
values, including the23 boundary values for the omitted regions.
The largest certified vector-arithmetic range is85,377,593,169,792,
below2^63. Geometric sums, conditioning and the two-prime consumer use
exact fractions. Run the new replay with `python3 -I -O`.
The arbitrary-height conclusions use the ordinary proofs above;
no new Lean theorem or unrestricted noncoverage endpoint is asserted.

### Combining actual prefix-cap savings with their own coverage charge

The preceding continuation admits a refinement that leaves every
physical prime kernel unchanged. Start with one fixed supported head
law mu, and a finite deterministic admissible schedule from (AP1)--(AP6).
At each prime p write

    d_p=p-1-T_p, delta_p=(T_p-1)/(p-2),
    c_p=(p-1)/d_p<=p,
    a_p=(3p-1)/(p-1)^2, k_p=1+a_p c_p.

Let alpha_p(x) be the actual mixed forbidden density in row x relative
to its uniform pure-power survivor law. The existing distortion kernel
has its natural density multiplier bounded by
1/(1-min(alpha_p(x),delta_p)). Consequently its actual depth-e prefix
cap is c_actual(x)p^(-e), where

    c_actual(x)=(p-1)/[(p-2)(1-min(alpha_p(x),delta_p))]<=c_p.

These are the natural caps already retained by
`FiniteLaw.distort_prob_le_natural` and
`CappedGain.distorted_prefix_le`. Define D_p=E(c_p-c_actual)>=0
under the actual previous-history law. If J bounds every old complete
test square, two such tests A_e,A_f satisfy

    E[c_actual A_e A_f]<=c_p J-D_p,
    Gamma_new<=k_p J-a_p D_p.                           (SH26)

For the first inequality use Cauchy--Schwarz to bound E A_e A_f by J,
and A_e A_f>=1 to retain at least D_p from the density deficit.
For the second, expand an arbitrary new test over every ordered pair
of p-exponents. The zero-zero pair contributes at most J; every other
pair has intersection cap c_actual p^(-max(e,f)). Individual residues
may vary with the old modulus: expansion into old labelled indicators
still gives the complete loads A_e A_f after applying the cap.
Their finite coefficient is bounded by sum_(j>=1)(2j+1)p^-j=a_p.
This enlargement is valid because c_p J-D_p>=E c_actual>0.

Write f_p=product_(later r)k_r and P=product_p k_p. Let beta_p be
the actual assigned mixed-union probability at step p, and B=sum beta_p.
All these expectations are preserved by later normalized kernels.
Iterating (SH26) bounds every final complete test by

    E L^2<=G P-sum_p f_p a_p D_p.

For W>0 satisfying W>=f_p a_p(p-1)/d_p at each prime, define on z>=1

    h_p(z)=W(z-T_p)_+/d_p
       +f_p a_p[(p-1)/(p-1-min(z,T_p))-c_p].

This function is increasing and convex: below T_p its derivative is
f_p a_p(p-1)/(p-1-z)^2, above T_p it is W/d_p, and the stated condition
is exactly the nondecreasing slope condition at the join. Using the
original weighted mixed load R_p from (AP3), alpha_p<=R_p/(p-2) gives

    W beta_p-f_p a_p D_p
      <=E h_p(1+R_p)
      <=E_(N_p) max_L E_mu h_p(N_p L).                  (SH27)

The last comparison preserves the original labels and the single missing
unit in (AP3), then applies Jensen exactly as in (AP4). Its N_p is the
same auxiliary multiplier as in the original schedule. When h_p(1)<0,
apply the nonnegative convex comparison to h_p(1+R)-h_p(1), and restore
the constant once. No density deficit is estimated independently from
the negative intercept of this combined cost.

Suppose C_p(W) bounds the right side of (SH27). The finite criterion

    G P-1+sum_p C_p(W)<=W                               (SH28)

alone implies a positive final survivor law with Gamma<=1+W. No
separate scalar charge bound below one is needed. To see this, combine
(SH26)--(SH28): for every final complete test L,

    E L^2-1+W B<=W.

The normalized physical kernels exist on the entire earlier history;
none conditions on previous good events. Their union bound for final
bad mass therefore applies even before positivity is known. If3 divides
the full physical period, some mod3 cylinder has probability at least1/3.
Complete a test containing that cylinder and the unit class. Its load
is at least1+I, so its square expectation is at least2. Applying the
last inequality to this test gives B<=1-1/W<1. More generally any
nonunit divisor d gives B<=1-3/(dW)<1 by the same argument.
Thus final survivor mass rho>=1-B is positive. For every test,
E L^2-1<=W(1-B)<=W rho; discarding the complement saves at least
its mass, and one final conditioning proves Gamma<=1+W. The test
chosen to establish positivity does not change the physical law.

The costs in (SH27) have an exact finite observation formula for integer
head loads. For fixed n, put v_j=h_p(nj) and K=ceil(T_p/n). Then

    E_mu h_p(nL)=v_1+(v_2-v_1)(E_mu L-1)
       +sum_(j=2..K)(v_(j+1)-2v_j+v_(j-1))E_mu(L-j)_+.

All feature coefficients are nonnegative under the final W condition.
For n>=T_p the entire cost equals W(nL-T_p)/d_p, so the infinite
auxiliary tail is computed from its remaining probability and first
moment. For a fixed set of mean and hinge upper bounds, the resulting
certificate is affine in W. Algebraic evaluation at zero and one may
extract its coefficients, but only the final W satisfying convexity
gives a probability bound.

Using the exact same-law observations (SH24) and the unchanged schedule
11/T4,13/T5, the certificate (SH28) gives

    Gamma_13<=20165592223021484810434066670921
                 /131127082414004971430759164752
                <153.786631.                           (SH29)

The saving over (SH25) is exactly
25321722548022558251710601395/131127082414004971430759164752.
All physical heights and the low-geometry hypothesis remain as in
(SH25). The adjacent convex-profile verifier checks every active
integer cost coefficient, the full multiplier tail, convexity at the
final W, and exact equality in (SH28). This is an ordinary refinement
of the existing normalized distortion construction, not a new Lean
declaration or a complete unrestricted-prime continuation.

Repository searches covered (AP1)--(AP6), the scalar fibre boundary,
the actual clipped rectangle estimates, `PrimeRectangleTransfer`,
`ConditionalComparison/Distortion`, `CappedGainDistortion`, and
`ThreePrime/DistortionChain`. The existing natural-cap and full-history
union-bound results are reused directly. Public sources checked on
16 September2026 include BBMST [1811.03547](https://arxiv.org/abs/1811.03547),
its scalar potential in Section6, the geometry optimization in Section5.3
of [1901.11465](https://arxiv.org/abs/1901.11465), and Hough--Nielsen
[1703.02133](https://arxiv.org/abs/1703.02133), Lemmas5--6. No directly
applicable arbitrary-height11/13 endpoint was found in those statements;
no literature-priority claim is made for the refinement.

### All integer schedules through23 for the fixed scalar feature map

Fix the probability law and exact mean, square and hinge bounds in
`saturated_convex_profile_certificate.json`, SHA-256
82b5211366625c3c9eed79d8124db700f7b24bd7a43f088d9b4487492c32d940.
The numerical statement below concerns the SH27--SH28 upper-certificate
functional built from these data. It does not lower-bound actual covering
probabilities or refute the existence of better supported laws.

For each p in 11,13,17,19,23 allow every integer 1<=T_p<=p-2. There are
9*11*15*17*21=530145 schedules. Put d=p-1-T, c=(p-1)/d,
a=(3p-1)/(p-1)^2 and k=1+ac. Every listed choice has d>=1,c<=p, so the
normalized full-history AP kernel and its auxiliary law exist.

#### The exact scalar feature map

Use the source's refined hinge2, H1=M-1, and its stated H3,H4,H5,H6,H8,
H10,H12. Put H7=(H6+H8)/2, H9=(H8+H10)/2, H11=(H10+H12)/2 and
Hj=H12 for 13<=j<=21. These are respectively convex interpolation and
monotonicity of the actual hinge transform. No separate law, uniform
comparator, altered source threshold or empirical fit is substituted.

Let w_n=Pr(N=n), n<22, and E=E N be the complete auxiliary mean for the
chosen earlier prime kernels. For 1<=n<T define

    r_(p,T,n)=n*H(T/n)-n*M+T>=0,

where H(T/n) is interpolation between its two adjacent integer knots.
For the charge hinge this is the exact positive-part representation on
integer initial test loads, with each hinge expectation then replaced
by its specified upper bound. The scalar charge coefficient is

    u_(p,T)=[M E-T+sum_(n<T)w_n r_(p,T,n)]/d.           (SO1)

For the non-charge part of SH27 put

    g(j)=a[(p-1)/(p-1-min(nj,T))-c], K=ceil(T/n),
    v_(p,T,n)=g(1)+(g(2)-g(1))(M-1)
             +sum_(j=2)^K[g(j+1)-2g(j)+g(j-1)]Hj.

It vanishes for n>=T. This is an affine-intercept calculation, not a
claim that the possibly nonconvex g has this expectation bound by itself.
The final SH27 combined cost has nonnegative feature coefficients under
its stated final-W condition. Define v_(p,T)=sum_(n<T)w_n v_(p,T,n).

Starting with B=0 and Z=G, update

    B_new=B+u_(p,T),       Z_new=k Z+v_(p,T).            (SO2)

The final SH28 certificate is exactly

    cert(W)-W=(Z-1)+(B-1)W.                            (SO3)

The multiplication in (SO2) accounts for all future square multipliers
on the earlier cost intercepts. The replay independently checks its
11/T4,13/T5 rational slope and intercept against the published SH29
fields, so the enumerated functional matches that published consumer.

The auxiliary update is exact divisor convolution:

    Pr(F=1)=1-c/p, Pr(F=f)=c(p-1)p^(-f) for f>=2,
    w'_n=sum_(m|n)w_m Pr(F=n/m), E'=E(1+1/d).          (SO4)

All divisors of n<22 are themselves below22. Higher states cannot
return to the stored range because F>=1. Their contribution to (SO1)
is exactly the affine full-mean term, and their contribution to v is
zero. No auxiliary mean or high-state contribution is truncated.

#### Directed integer bounds

Let S=10^18. All grid integers represent their value divided by S.
The verifier keeps lower and upper bounds on each low probability,
a lower complete mean, a lower accumulated B and a lower accumulated Z.
Initial lower constants are floor(SM),floor(SG); probability and mean
start exactly at one.

The fixed r values are nonnegative and rounded downward. In (SO1), use
the lower mean, lower probability and lower r in every positive product,
round every division downward, and subtract the exact integer T*S.
The result is a lower bound on the exact scalar certificate coefficient.
Taking max(0,lower) remains valid because that exact coefficient is
nonnegative. Adding these step lower bounds bounds B downward.

For the intercepts v_n, round each exact rational down. If this rounded
value is negative, multiply by the UPPER probability; otherwise multiply
by the LOWER probability. Floor each product after dividing by S. In
either case the result is <=w_n*v_n. Multiplying the previous lower Z
by the exact positive k and flooring, then adding these signed lower
products, bounds the new Z downward.

Convolution uses exact rational factor probabilities. Sum floor(w^-*Pr)
for each lower output and ceil(w^+*Pr) for each upper output. The full
mean update uses floor(E^-*(d+1)/d). These preserve the intervals by
induction, including all negative-intercept signs. They are bounds on
the exact certificate functional, not bounds on the actual physical
law's unknown charge or deficits.

#### Finite conclusion

The verifier visits exactly 9,99,1485,25245,530145 prefixes at the five
successive depths, with no pruning. Across every terminal schedule it
finds the uniform lower bounds

    B >=515109547377609039/500000000000000000 >103/100,
    Z-1>=10102503029019284371/100000000000000000 >101.

The grid-bound minimizers occur at thresholds (4,4,8,8,12) and
(1,1,1,1,1), respectively. They need not be the same schedule: both
lower bounds hold for every schedule, so they may be combined to give

    cert(W)-W >101+(3/100)W>0 for every W>0.

Consequently none of these 530145 schedules can satisfy SH28 using this
specific scalar feature upper bound. This is stronger than failing one
chosen W or one greedy policy. It remains a bounded numerical strategy
obstruction, not an impossibility theorem for SH28 with sharper whole
costs, other initial laws, noninteger thresholds, or different blocks.

#### The missing observation

The existing feature map takes separate maxima for M and each H_j, and
then another separate maximum for every auxiliary N. A next observation
that preserves original labels is

    F_mu(g_(p,b)),
    g_(p,b)(z)=E[1_(b<=K) h_p(Nz)/N],

where b is one fixed original earlier-prime exponent label. Its head
test cannot vary with N. The conditional comparison/Jensen step gives
the sum of these support functions; the current scalar map replaces
them by sums of independent feature maxima. The zero original label is
always active and is the cheapest initial query. The existing FL1--FL4
label-retention calculation supplies the finite-observation bookkeeping;
it must be evaluated on the same SH18 probability, including its actual
higher357 conditioning. Another possible new observation is the joint
weighted pair deficit E[(c_p-c_actual)A_e A_f], whose present proof only
uses A_e A_f>=1. Neither missing value is determined by the listed
separate scalar upper bounds.

The adjacent `verify_combined_schedule_obstruction.py` reconstructs
`combined_schedule_obstruction_certificate.json` using only the Python
standard library. Run it with `python3 -I -O`; the source profile is a
hash-bound prerequisite. All 530145 schedules are visited without
pruning. Directed-grid arithmetic bounds exact rational expressions;
it does not rely on floating optimization or a solver. This result
is an experimental strategy obstruction with the ordinary derivation
(SO1)--(SO4), not a new Lean declaration.

### Higher hinge observations on the same supported law

Keep exactly the (SH18) probability, original-label comparison, 270-depth
box and same-law survival denominator. Applying (SH20)--(SH21) at the
nine further integer thresholds gives the following simultaneous bounds;
the displayed decimals are rounded upward.

| t | H_nu(t) upper bound |
|---:|---:|
|13|0.189271|
|14|0.161741|
|15|0.135712|
|16|0.112043|
|17|0.095693|
|18|0.079571|
|19|0.069949|
|20|0.060411|
|21|0.053283|

Each finite-box numerator maximizes over all 280-by-280 base layouts,
with both singleton45 labels restored exactly by (SH21). The entire
outside box is included through t*V_out/(4t^2-1), then divided by the
same positive q_* as in (SH20). No original high exponent is truncated
and no new supported probability is chosen.

These values improve the preceding monotonicity bound H_nu(t)<=H_nu(12)
for every listed threshold. Replace those nine constant extensions in
the existing (SH27) scalar feature map, keeping all its other features
and the integer schedule domain unchanged. The complete directed
enumeration again checks all 530145 threshold schedules through23 and
obtains the same uniform bounds

    B>=515109547377609039/500000000000000000>103/100,
    Z-1>=10102503029019284371/100000000000000000>101.

Hence its combined certificate still satisfies
cert(W)-W=(Z-1)+(B-1)W>101+(3/100)W for every W>0. Improving the flat hinge
extension by these nine same-law observations does not remove this
bounded strategy obstruction. This does not exclude sharper joint
costs, further improvements of the individual hinge bounds, another
initial probability, noninteger thresholds or a different prime block.

The separate `saturated_high_hinges_certificate.json` binds both prior
certificates by their hashes and retains all 2430 new integer maxima,
the complete geometric remainders and the enhanced schedule replay.
Three of those maxima are independently checked without (SH21), using
all 4480^2 ordered full-layout pairs at each selected depth/threshold:
(2,1,1)/13, (3,0,2)/17 and (8,5,4)/21. Their exact weighted numerators
are 79299012, 80659542 and 1403702325, respectively. The existing
low-law normalization supplies their common denominator.

Run `python3 -I -O docs/reports/erdos7-odd-covering/verify_saturated_high_hinges.py`.
The verifier reuses the current convex-query and directed-schedule
implementations, checks the three dense independent calculations, and
compares every computed certificate field. NumPy is required only for
the finite convex observations and the dense checks. These are ordinary
all-height estimates with exact numerical verification, not a new Lean
endpoint or a solution of unrestricted #7.

### Whole convex costs with one fixed original exponent label

Retain exactly the77-point carrier, nonuniform low probability, uniform
higher-digit lift and actual conditioning event of(SH18). The full original
3/5/7 heights remain arbitrary finite ones. Let nu be that same probability,
q0=2577991831/4799999616 its established conditioning denominator, and

    M=19618622895502373704/3964266656997890625=2+H2,
    G=2512626164927510733601/70505216618162484375.

These bound every complete old test on one fixed nu. The actual11/13
kernels, full physical periods, original labels and parameters are those
of(SH25): T11=4,T13=5,delta11=1/3,delta13=4/11. In particular no new
probability is chosen to optimize a separate cost. Set W=3049/20 and use
the complete increasing convex costs h_p of(SH27), with f11=61/42,f13=1.

#### Conditioning a complete cost

For any increasing convex h, put g(l)=(h(l)-h(2))_+. Since
h(l)<=h(2)+g(l), the unchanged actual conditioned law obeys

    max_L E_nu h(L) <= h(2)+[max_L E_lambda g(L)]/q0.

Only the nonnegative cut cost is divided by the lower denominator. The
constant h(2), which may be negative, is retained exactly once.
Use(SH19)--(SH21) to bound the entire g on one weighted low layout at each
auxiliary depth, before taking its maximum. This retains the relations
between all slopes and hinges of h.

The same270-depth box as(SH18) suffices. Let beta be its probability and

    Eout=U_B-sum_(z in box)Pr(z)F_square(z)-(1-beta).

For any a>=sup_(integer k>=2)g(k)/(k^2-1), the complete omitted contribution
is at most a Eout. Hence, if V_g(z) is the exact maximum of the whole
low cost at depth z,

    max_L E_nu h(L)
      <=h(2)+[sum_(z in box)Pr(z)V_g(z)+a Eout]/q0.

This does not truncate the original heights or the auxiliary tail.
For the costs below, g is affine from a known integer k0 onward, with
g(k)=A k-B and2A<=B<=k0 A. The ratio to k^2-1 is decreasing for real
k>=2k0, since its derivative numerator is at most
-A k(k-2k0)-A<0. A finite integer scan therefore computes the global
quadratic coefficient exactly.

#### An original zero label across every auxiliary outcome

At the13 step write N=1+K11. Its full comparison distribution satisfies

    Pr(N=1)=28/33,
    Pr(N=n)=50/(3*11^n) for n>=2,
    E N=7/6.

The old11 exponent label zero is active in every outcome. Its completed
head test at each current13 depth is fixed before N is sampled. The
original-label Jensen comparison from(FL1)--(FL4) and(SH27) assigns weight
1/N to each of the N active old exponent labels. Thus, for any simultaneous
upper bounds B_n>=max_L E_nu h13(nL), the zero label may be collected first:

    cost13 <= max_L E_nu g0(L)
                 +E[(1-1/N)B_N],
    g0(l)=E[h13(Nl)/N].

The current13-depth weights sum to one. Their zero-label tests may differ
with that depth; the supremum of the same g0 bounds their weighted average.
This argument does not interchange an unrestricted expectation and maximum.

For n>=5, h13(nl)=W(nl-5)/7 for every integer l>=1. Put p_n=Pr(N=n),
Ptail=Pr(N>=5)=5/43923 and Etail=E[N;N>=5]=17/29282, and define

    gtilde(l)=sum_(n=1..4)(p_n/n)h13(nl)+(W/7)Ptail*l.

The omitted constant in g0 is -(5W/7)E[1/N;N>=5]. It cancels exactly
against the same constant from the other original labels. Therefore

    cost13 <= max_L E_nu gtilde(L)
      +sum_(n=1..4)p_n(1-1/n)B_n
      +(W/7)[M(Etail-Ptail)-5Ptail].

Every coefficient multiplying an unknown moment or test cost is
nonnegative. The remaining negative constant is exact; no reciprocal
moment approximation or omitted multiplier mass is used.

The n=1 residual coefficient is zero. Bound B2 by the complete-cost
calculation above. For n=3,4, h13(nl) is increasing and affine from l=2
onward, so for every integer l>=1,

    h13(nl)<=h13(2n)+(Wn/7)(l-2)_+.

Consequently B_n=W(nM-5)/7 is valid using M=2+H2. These bounds continue
to concern the same nu. At11 there is no old-tail multiplier, so its
entire cost is bounded directly by the whole h11 calculation.

#### Exact consumer

The three complete costs are h11(l),h13(2l),gtilde(l). Their cut costs
have exact common denominators17640,1680,5488560, respectively. No
quantization is needed. The singleton45 elimination evaluates all810
new depth-cost maxima over280^2 base-layout pairs per query. Its convex
increment identity bounds every intermediate nonnegative sum by an
attainable or dominated complete cost, so the integer range is at most
D times the largest point cost. The largest certified range is
5467332906913332456, below2^63.

The resulting complete13 cost is

    4078973908904062879587704261867
      /108352191282098927867550000000.

Together with the complete11 cost, J=(1403/630)G and the unchanged
criterion(SH28), the exact positive margin is

    W-[J-1+cost11+cost13]
      =44282704320696511600648227253
         /108352191282098927867550000000 >0.

Write C=J-1+cost11+cost13. The computed margin gives 0<C<W, and for
every final complete test the proof of(SH28) gives

    E L^2-1+W B<=C.

Since B>=0 and C<=W, this also gives E L^2-1+C B<=C. Applying the
universal square floor and final conditioning as in(SH28) yields

    Gamma<=1+C=16582361047917383969674899272747
                 /108352191282098927867550000000
               <153.041308.                            (SH30)

The convex costs are still evaluated at W=3049/20; no convexity claim
at C or new kernel is needed. In particular the original target
Gamma<=3069/20=153.45 also holds. No independent scalar charge premise
is required. The old low-geometry hypothesis and all original3/5/7/11/13
physical heights remain as in(SH25). This supplies another exact head
input for later primes; it does not prove an unrestricted tail continuation.

`verify_saturated_whole_cost.py` replays the separate
`saturated_whole_cost_certificate.json`. The existing(SH18) and(SH24)
certificates are hash-bound prerequisites. This new replay owns only the
810 whole-cost observations, exact tables, full geometric and multiplier
tails, and the strict final criterion. Run it with `python3 -I -O`.
All conclusions here are ordinary mathematics with exact arithmetic,
not new Lean declarations or a solution of unrestricted#7.

### Actual seven-digit positions at arbitrary357 heights

Fix the following eleven distinct low forbidden modulus/residue pairs:

```
(3,0), (9,4), (5,0), (15,11), (45,37), (7,0),
(21,8), (35,9), (63,59), (105,74), (315,89).
```

Their actual complement Ω in Z/315Z has75points. The certificate lists these points in increasing order and assigns each a nonnegative integer weight with total N=1000000007. Let μ be this probability law. No deleted point is filled, no digit is moved, and the weights need not be constant within an old45 fibre.

For arbitrary finite nonnegative n3,n5,n7, lift μ independently and uniformly in the additional prime-power digits to period Q=3^(2+n3)5^(1+n5)7^(1+n7). Call this law λ. Above the eleven fixed low classes, allow any forbidden family with at most one original residue class for each distinct divisor of Q that does not divide315. Let F be the complement of precisely these actual higher forbidden classes. The conclusion concerns ν=λ(.|F). It does not assume that ν has unchanged low marginals or is an ambient uniform law.

When this law is used before additional primes, Q includes the full
3/5/7 part of the original common period, including heights appearing
only in moduli with later prime factors.

For a complete test family consisting of one arbitrary class C_m modulo every divisor m of Q, including C_1=the whole space, write L=Σ_(m|Q)1_Cm. The certificate and the argument below give

    sup_test E_ν L² ≤ 105976769844774468812903/2920804491373837228125
                    < 3849/106.                         (PG1)

This is a result for the specified low family; it does not assert a bound for every other low315 configuration or settle unrestricted Erdős #7. All-height validity follows from the analytic estimates below. The finite verifier recomputes their coefficients and the two low geometry bounds.

#### Saturated common-layout reduction and the full geometric tail

Put h=(2,1,1). Each original exponent vector a has the unique saturated projection d=Π_p p^min(a_p,h_p), together with its extra exponents a_p−h_p where these are positive. These extra exponents remain part of the original modulus label. Equal projected d never identify different original moduli.

Let Z3,Z5,Z7 be independent auxiliary geometric variables with

    Pr(Z_p=k)=(p−1)/p^(k+1),  k≥0.

For d|315 set w_d(z)=Π_(p:v_p(d)=h_p)(1+z_p). Define the genuine low-layout maximum

    F_μ(z)=max_(one cylinder C_d modulo each d|315)
                E_μ (Σ_d w_d(z)1_Cd)².

The standard saturated-prefix argument gives E_λL²≤E_Z F_μ(Z). Indeed, conditionally on the low point, higher-prefix intersections are bounded by nested-prefix intersections p^−max(e,f); centering the added coordinates realizes this dominating kernel. At a fixed geometric height, the projected cylinders belonging to one d average to a point of their convex hull. Convexity of the square bounds that average by an extreme layout with one cylinder per d. Finite physical heights are truncated versions; completing labels and auxiliary heights only increases these nonnegative bounds. This centering is solely a moment bound under λ and does not alter the actual deletion event F.

Let m_d=max_a μ(a mod d) and P(z)=Σ_(d,e|315)w_d(z)w_e(z)m_lcm(d,e). For each fixed low layout, its weighted-square increment from z=0 is at most P(z)−P(0), because every weight product increment is nonnegative and μ(C_d∩C_e)≤m_lcm(d,e). Therefore

    F_μ(z) ≤ F_μ(0)+P(z)−P(0).

Let H(z) be any valid upper bound for F_μ(z), let B=[0,8]×[0,5]×[0,4], and let β=Pr(Z∈B). Using H inside B and H(0) outside gives

    E_λL² ≤ U_B
      := (1−β)H(0)+Σ_(z∈B)Pr(Z=z)H(z)+Σ_d η_out(d)m_d.

Here η_out(d) is the coefficient of m_d in E[1_(Z∉B)(P(Z)−P(0))]. All coefficients are nonnegative. The full expectation of each pair weight product is the product of the one-prime factors1 (neither exponent saturated), p/(p−1) (exactly one saturated), and p(p+1)/(p−1)² (both saturated). Subtract1 and subtract the finite-box contribution to obtain η_out exactly. No tail is discarded. In particular, this argument does not require P(0)−H(0)≥0 or monotonicity of a relaxed deficit.

#### Pure7 anchored upper bound

Identify Ω with its actual pairs (x,y), where x is an old45 point and y∈{1,…,6} its7digit. Write R_x=Σ_y μ_(x,y) and v_x=max_y μ_(x,y). Put C=(1,3,5,9,15,45), b=(1,1,1+z5,1+z3,1+z5,(1+z3)(1+z5)), and u=1+z7.

Let A and B range independently over all complete old45 layouts with weights b, including their unit labels. Then a valid upper bound is

    H_pure7(z)=max_(A,B,j) Σ_x [
        R_x A_x²
        +v_x(2u A_x(B_x−1)+u²(B_x−1)²)
        +μ_(x,j)(2u A_x+u²(2B_x−1)) ].

To prove it, fix a genuine low315 layout. Its non-seven part is A. Keep the actual global digit j of its pure7 label. Let B−1 be the sum of the other five high-label old cylinders. Bound every low/high term not using the pure7 label, and every high/high term not using it, by the fibre maximum v_x. Terms involving the pure7 label have mass at most μ_(x,j). Expanding the square gives the displayed expression. Maximizing over actual old layouts preserves validity.

There are4480 complete old layouts and280 after omitting the45singleton. Let s=(1+z3)(1+z5). For fixed base A,B and j, adding s at singleton rows i,k gives an A-only gain a_i, B-only gain b_k, and an additional nonnegative cross gain2u v_i s² only when i=k. Hence the exact best singleton gain is

    max(max_i a_i+max_k b_k, max_i(a_i+b_i+2u v_i s²)).

If the independent maxima occur at the same row, the coincident term dominates them; if they occur at different rows, the independent sum is realized. This explains the verifier's280² base-pair calculation without losing any of the4480² full-layout maxima. The six digits used are the actual surviving digits; the excluded digit0 has zero mass and cannot improve a nonnegative maximum.

#### Fixed-low-layout digit partition upper bound

Keep a single complete old low layout A and write its load as a_A(x). For each high label7e, e∈C, and actual digit y define

    R_e^A(y)=max_(old cylinder D modulo e)
        Σ_(x∈D) μ_(x,y)[u²b_e²+2ub_e a_A(x)],

    M_(c,y)=max_(old cylinder D modulo c) Σ_(x∈D) μ_(x,y),

    J_(e,f)(y)=2u²b_e b_f M_(lcm(e,f),y),   e<f.

The diagonal and all cross terms with the common low A use one common old cylinder inside R_e^A(y). For two high labels on the same digit, their old intersection is empty or a cylinder modulo their lcm, so J bounds their pair contribution. Labels on different digits have zero intersection. Only this high/high old-cylinder compatibility is relaxed.

For a subset T of the six high labels put

    H_y^A(T)=Σ_(e∈T)R_e^A(y)+Σ_(e<f in T)J_(e,f)(y).

Partition the six labels among the six surviving digits. The subset recurrence

    D_y(S)=max_(T⊆S)[D_(y−1)(S\T)+H_y^A(T)]

computes the exact maximum of this relaxation. Initialize D_1(S)=H_1^A(S), and permit empty subsets at all digits. Digit0 has no mass; assigning a label from it to a surviving digit cannot decrease the relaxed nonnegative objective. Thus

    H_DP(z)=max_A [Σ_(x,y)μ_(x,y)a_A(x)² + D_6(C)]

is a valid upper bound for F_μ(z). The verifier evaluates all4480 A with64 subset states. The employed bound is H(z)=min(H_pure7(z),H_DP(z)) at the one fixed law μ. This minimum is a pointwise upper bound; no convexity or optimization property is claimed for the minimum.

#### Actual grouped deletion bound for the same law

Use the selected one-extra-prime blocks

    E3={9,45}, E5={5,15,45,35}, E7={7,21,35,63,105,315}.

For p∈{3,5,7}, the block with low projection d∈Ep includes the original moduli d p^e, e≥1. The summed conditional prefix mass is α_p=1/(p−1). The three selected blocks use independent added prime coordinates conditionally on the low point. Their true union is bounded by the maximum over their low cylinders of

    G_group(μ)=max E_μ[1−Π_p(1−α_p A_p)],

where A_p is the count of the selected low cylinders for p. The bounds |E3|≤2, |E5|≤4, |E7|≤6 ensure that each factor is nonnegative. For the original labels at different e, take their geometric convex averages, padding absent exponents by zero. The displayed expression is affine separately in each such average and increasing in each group count within these ranges. Maximizing selects one low cylinder for each projected label, which proves this upper bound without merging original labels or changing F.

Set γ_d=Π_(p:v_p(d)=h_p)p/(p−1)−1 and ρ_d=γ_d−Σ_(p:d∈Ep)α_p. All ρ_d are nonnegative. Every unselected original higher label is bounded by the ordinary union bound, giving

    λ(F) ≥ q := 1−G_group(μ)−Σ_d ρ_d m_d.

The verifier maximizes G_group exactly on the actual75points. To describe its elimination, write A for the two E3 indicators, B for the three old E5 indicators at5,15,45, I for the extra35indicator, and C for the six E7 indicators. The pointwise numerator of the union with denominator48 is

    24A+12B−6AB+6(2−A)I+(2−A)(4−B−I)C.

For each A,B,I choice the six E7 cylinders maximize independently, since their coefficients are nonnegative. The verifier enumerates all A,B,I choices, computes these six maxima, and independently checks the final witness against the product-union formula point by point. All caps and this union maximum use the same integer weights as both numerator bounds.

#### Exact values and conditioning

The standalone verifier reproduces

    q = 25428074957/48000000336 > 0,
    U_B = 54284750870997693017389/2756768194297377225000.

Since C_1 is the whole space, L≥1. Thus L²−1≥0, and conditioning the actual higher surviving event gives

    E_ν L² ≤ 1+(E_λ L²−1)/λ(F) ≤ 1+(U_B−1)/q
            = 105976769844774468812903/2920804491373837228125.

Its difference below3849/106 is the positive rational

    8638883751805796885407/309605276085626746181250.

`verify_point_geometry.py` reads `point_geometry_certificate.json`, reconstructs the actual carrier, checks all weights and arithmetic bounds, recomputes both integer geometry maxima at every one of270depths, recomputes all actual cylinder caps and the grouped union maximum, and performs the geometric-tail and final comparisons with exact rational arithmetic. The largest common bound on intermediate square sums is213444001494108, below2^63. The verifier needs Python3 and NumPy; it imports no optimizer or scratch module. This is a finite computational certificate combined with the ordinary all-height proof above, not a Lean kernel verification.

### Complete low315 carrier classification for actual digit bounds

Fix one of the six existing canonical old45 survivor sets S. The fixed old forbidden classes are modulo3,9,5,15,45. The pure7 forbidden digit is normalized to0. The five mixed labels are7d with d=(3,5,9,15,45), with one class per original modulus. Missing or low-redundant labels may be represented by a class on digit0. This note classifies their low surviving carriers. It does not evaluate the new moment bound on all carriers, prove a universal numerical target, or replace the existing justification for reducing old45 families to these six shapes.

#### Labelled digits:203 patterns, with the pure digit distinguished

Fix the five old residue choices a_d modulo d. Each mixed label chooses a digit t_d∈Z/7Z independently by CRT. Include the distinguished pure label with t_0=0. Two such assignments are equivalent under one common permutation of the six nonzero7digits if and only if the six labelled objects {0,3,5,9,15,45} have the same equality partition by their digit.

The forward direction preserves equality and the zero block. Conversely, map the nonzero digits attached to corresponding blocks to one another, then extend the resulting partial bijection to the unused nonzero digits. Since there are only five mixed labels, no partition needs more than six total blocks. Every partition of six labelled objects is realizable. Therefore the exact labelled digit-orbit count is Bell(6)=203, not203 entire carrier cases on S.

The numbers of patterns with k=1,…,6 total blocks are1,31,90,65,15,1. A pattern with k blocks has6!/(7−k)! concrete digit assignments when t_0=0. Their sum is7^5=16807. The classifier independently normalizes all16807 tuples and recovers precisely the203 restricted-growth strings.

If all mixed digits are required nonzero, the pure label is a singleton and the count becomes Bell(5)=52. The existing code uses52 partitions together with the option that each old cylinder is empty. Moving every label whose digit is0 into that empty-cylinder option gives the same low carrier. Conversely, an empty-cylinder label can be placed at digit0 with any old residue. Thus the current52-partition construction covers all actual low carriers, including pure-digit coincidences. It does not preserve the full description of redundant original labels, which is unnecessary when the only required input is their complement.

Before taking effects on S, the five old residue choices number3·5·9·15·45=91125. Hence a direct labelled enumeration at one fixed S has91125·203=18498375 digit orbits. Many have identical carrier effects. Replacing old residues by their distinct masks on S gives12960 old-mask choices for each17point shape and12240 for each16point shape. The resulting203-pattern products over six shapes contain15346800 entries; the equivalent52-plus-empty enumeration contains3931200 entries. These are labelled enumeration counts, not distinct carrier counts.

#### Exact carrier state and what the deletion vector forgets

For each surviving digit y∈{1,…,6}, let

    U_y = union of (S∩{x≡a_d mod d}) over labels whose t_d=y.

The carrier is exactly Ω={(x,y): x∈S\U_y, y∈{1,…,6}}. Represent it by the sorted multiset of its nonempty masks U_y; repeated masks retain their multiplicity. The number of omitted empty masks is6 minus the multiset length. At most five masks are nonempty, so there is a globally unused nonzero digit.

Two carriers on the same fixed S are equivalent under one common7digit permutation fixing0 if and only if their mask multisets are equal. One direction is immediate. For the other, match equal nonempty masks with their multiplicities and match the remaining empty masks; these matches define a single permutation of the six digits. This is a statement about carriers; different original labelled forbidden families may have the same carrier and need not be equivalent as labelled families.

The existing deletion vector is only

    b(x)=#{y:x∈U_y},    r(x)=6−b(x).

It forgets which old points are deleted together at a common digit. Its161375 states are therefore insufficient as the input to an arbitrary75point weighting or to an oracle retaining actual digit positions. The richer state above preserves exactly the information these methods need. It can be realized by assigning the sorted masks to digits1,…,k and treating the remaining digits as empty-deletion columns.

Completeness has a small successive-label recursion. Start with the empty multiset. For each of the five original labels, choose any of its old-cylinder masks, including the empty one. An empty mask leaves the state unchanged. A nonempty mask either occupies a fresh digit, appending that mask, or uses an existing digit, replacing one U by U∪C. Sort the resulting multiset and deduplicate. The inductive alternatives cover exactly every assignment of the labels seen so far. Since there are only five labels and six available nonzero digits, a fresh digit always exists when needed. The resulting states agree in count and projected b digest with the existing two-enumeration certificate.

#### Allowed common CRT coordinate maps

A7digit permutation must be common to every old point x. Independent permutations in separate old45 fibres generally send a single cylinder modulo7d to a union of cylinders and are not allowed in this equivalence.

Every common permutation of the7roots fixing0 extends to every finite7power by permuting the first digit and leaving all later digits unchanged. It sends every prefix cylinder to a prefix cylinder of the same depth and preserves uniform suffix measure. Likewise, any old ternary rooted-tree permutation preserving the mod3 and mod9 cylinder families, and any common permutation of the five5roots, extends to arbitrary finite additional heights. Their coordinatewise CRT product preserves every original modulus label and sends its residue class to another single class of that same modulus. No primality label, projected cofactor label, or original high exponent is merged.

For the six normalized old carriers, the surviving mod9 rows are (1,7) in the short ternary root and (2,5,8) in the long root. The surviving mod5 columns are(1,2,3,4). Candidate old coordinate maps form

    S_{ {1,7} } × S_{ {2,5,8} } × S_{ {1,2,3,4} },

of size2!·3!·4!=288. Keep exactly those maps preserving S. They preserve each old cofactor-cylinder family d∈{3,5,9,15,45}; the classifier checks this for every map. The short and long roots cannot be interchanged in a map preserving S, because they have different numbers of surviving mod9 rows. The excluded root0 and deleted child4 carry no old points; the listed maps extend to the full rooted tree by fixing them. Thus these maps are allowed global coordinate changes, not arbitrary permutations of S.

Act with each such old map on every mask U_y, then sort the masks. The combined old-coordinate and common7digit quotient is complete for this stated group. Transport an actual law along the corresponding bijection of Ω, and extend the coordinate map to the additional physical digits. Every cylinder cap, all selected original deletion blocks, complete test-family moment, and resulting actual conditional law is transported coherently. Consequently one exact feasible certificate on each carrier orbit would suffice for this finite classification, provided its analytic all-height estimates are valid. Reusing a law after a coordinate map means pushing forward every point weight and every actual event together.

#### Measured classification

`verify_seven_digit_classification.py` regenerates the mask states by the successive-label recursion, verifies the exact existing b-set hashes, checks each old map preserves all five cylinder families, and enumerates the combined orbits. It performs no LP or moment sweep. The result file is `seven_digit_classification_certificate.json`. The only external input is the canonical adjacent `actual_deletion_profile_certificate.json`; the classifier reads its six old geometries, checks their exact original classes and complements, and binds the used input fields by SHA-256. It imports no other program, optimizer, or policy cache.

| Old45 shape | b vectors | Digit-union carriers | Old maps | Carrier orbits | b orbits |
|---|---:|---:|---:|---:|---:|
| root1, same root / other column |27679|165141|12|31833|5281|
| root1, other root / same column |28939|168517|24|15451|2829|
| root1, other root / other column |28735|168695|8|40281|7082|
| root2, same root / other column |25813|157010|8|36152|6063|
| root2, other root / same column |25238|152235|36|12692|2268|
| root2, other root / other column |24971|153997|12|34160|5718|
| Total |161375|965595| |170569|29241|

Some b vectors have 37 distinct digit-union states even before old-coordinate symmetries. The old-coordinate quotient leaves170569 exact carrier cases; it is the relevant complete finite domain for applying the new actual-point geometry language.

A concrete loss-of-information witness on the first17point shape is retained in the result: the same b has union multiset(66576,103278) and union multiset(8,65828,104018), where bit i refers to the listed ith old point. These use respectively two and three nonempty digit masks. No common digit permutation or old-coordinate bijection can change that number, so the carriers are inequivalent even under the combined allowed group, despite having exactly the same b.

#### What a complete next step would require

Use a carrier representative, not one arbitrary realization of b. Expand its masks to the actual315points, choose and certify a law on that actual support, and evaluate the pure7 bound, fixed-low digit-partition bound, all caps, actual grouped deletion bound, and full geometric tail on that one law. Coordinate symmetries then transport the certificate to its orbit. Existing bounds that depend only on b can settle all richer states above a certified b without reevaluation; unresolved b states must retain the mask multiset before using the new digit-sensitive bounds.

The present result certifies the finite coverage and equivalence statement and the measured state counts. It does not show that all 170569 carrier orbits meet 3849/106.


#### Reproduction and verification boundary

Place the new classifier and result certificate beside the existing canonical `actual_deletion_profile_certificate.json`, then run:

```sh
python3 -I -O verify_seven_digit_classification.py
```

Alternatively pass the canonical input path through `--source-certificate` and the result path through `--check`. The program uses only the Python standard library, with unbounded integer arithmetic and explicit guards unaffected by optimization. It checks raw types on all consumed integer geometry fields, pins the six canonical shapes and their original old classes, reconstructs all carrier states, checks the old maps form a group preserving every cofactor-cylinder family, checks disjoint orbit coverage, and compares the complete deterministic result. It records hashes of all reconstructed state sets and orbit-representative sets without storing the large sets. It also verifies the displayed two-carrier witness and the exact203 digit-orbit sizes against all16807 digit tuples. The results are finite arithmetic certificates with the ordinary equivalence and all-height transport proofs above; no Lean kernel verification or universal numerical moment bound is claimed.

### Fixed convex potentials for the actual-cap charge

This result uses the same normalized physical kernels, supported head law,
original modulus labels and complete test loads as AP1–AP5 and W1 in
`Problems/erdos-7-odd-covering-systems.md`. It is an ordinary analytic bridge.
No new Lean declaration or unrestricted-prime endpoint is asserted.

#### Fixed-potential envelope

Fix an integer 2≤T<p−1 and W>0. Put

    d=p−1−T, a=(3p−1)/(p−1)², c=(p−1)/d,
    κ(z)=(p−1)/(p−1−min(z,T)), z≥1,
    H0(z,y)=W(z−T)_+/d+aκ(z)y², z,y≥1.

Choose real knots q1,…,qT with q1=0 and

    0≤q2−q1≤q3−q2≤…≤qT−q_(T−1)≤W/d.                (1)

Let P_q interpolate these knots linearly, and extend it for z≥T by

    P_q(z)=qT+W(z−T)/d.

Define

    V_q(y)=max_(1≤k≤T) {aκ(k)y²−qk}.                 (2)

Then P_q and V_q are nonnegative, increasing and convex on[1,∞), and

    H0(z,y)≤P_q(z)+V_q(y)                            (3)

for all real z,y≥1. More precisely,

    V_q(y)=sup_(z≥1) [H0(z,y)−P_q(z)].               (4)

For each fixed y, the expression on the right is convex in z inside each
unit cell belowT: κ is convex there and P_q is affine. Its maximum on each
cell is attained at an endpoint. For z≥T the expression is constantly
acy²−qT. This proves(4). Equation(2) then makes V_q an increasing convex
maximum of positive quadratics minus constants; its k=1 term is positive.
Condition(1) gives the assertions for P_q.

The global z-convexity of H0 is NOT needed. In particular this result does
not require the stronger W bound needed for the clipped joint cost H_K.

Define diagonal integer potentials by u(1)=v(1)=0 and

    u(k+1)−u(k)=H0(k+1,k)−H0(k,k),
    v(k+1)−v(k)=H0(k+1,k+1)−H0(k+1,k),

with linear interpolation. Supermodularity bounds H0 by H0(1,1)+u+v
on the integer grid; separate convexity inside every unit cell extends
that bound to real arguments. The u increments beforeT are
ak²[κ(k+1)−κ(k)], followed by W/d; those of v are
aκ(k+1)(2k+1). Thus u is convex provided
W≥a(T−1)²(p−1)/(d+1), while v is convex automatically.
These diagonal potentials are included. Whenever u is convex, choose
qk=u(k); this diagonal majorant implies V_q≤H0(1,1)+v. Thus this
family weakly improves that majorant. A different fixed q can improve it
strictly, as the exact p11 calculation below demonstrates.

#### Physical scalar comparison and finite survivor criterion

Let ν be the actual full old law at this prime. Let R be its original
weighted mixed load, w=c_actual its natural prefix-cap multiplier, and b
its conditional assigned mixed-union probability. The existing AP/SH26
estimates say

    w≤κ(1+R), b≤(1+R−T)_+/d.

For every complete old test A,

    Wb+a w A²≤P_q(1+R)+V_q(A).                        (5)

Let μ be the fixed full head law, and let N be the AP auxiliary multiplier
from the preceding tail primes. Write F_μ(g)=max_L E_μg(L), over complete
head tests fixed before sampling the head point. Applying the existing
scalar original-label comparison and Jensen separately to P_q and V_q gives

    Wβ+aΓ(wν)≤C_p(q),
    C_p(q)=E_N[F_μ(L↦P_q(NL))+F_μ(L↦V_q(NL))],       (6)

where β=E_νb. Both scalar comparisons use the same actual law and the same
distribution of N. No physical independence of R and A is asserted.
W1 then proves

    Γ_new+Wβ≤Γ_old+C_p(q).                            (7)

For a finite schedule with one fixed admissible q_p at each prime, summing
(7) gives

    Γ_final+WΣ_pβ_p≤G_head+Σ_pC_p(q_p).               (8)

Consequently

    G_head−1+Σ_pC_p(q_p)≤W                            (9)

is sufficient for positive final survivor mass and Γ_conditioned≤1+W,
using the existing SH28 witness and final conditioning. The full positive
cap energy is already included in C_p. Criterion(9) is a finite supported
probability result, not an infinite-prime noncoverage endpoint. A separate
valid tail theorem is needed to continue it to all remaining primes.

The feasible knot set(1) is compact. For a fixed full head law, C_p(q) is
convex in q: P_q(z) is affine in q and V_q(y) is a maximum of affine
functions of q; expectations and suprema preserve convexity. Quadratic
moment bounds give a uniform integrable envelope. Rational candidate knots
can therefore be checked independently of any numerical optimizer.

#### Order of optimization and conditioning

In(5)–(6), q is fixed BEFORE scalar conditional comparison. Therefore

    inf_q E_N C(q,N)

is a valid optimized upper bound. The smaller expression

    E_N inf_q C(q,N)

does not follow from that proof. Choosing separate q_n after observing the
auxiliary N requires a genuine prior comparison of the physical JOINT cost
to a cost under that common auxiliary. Introducing an independent random q
only produces a second independent auxiliary variable in the scalar proof;
it does not justify matching the two indices.

All finite-n head observations must use the full actual head law. In the
SH18 construction write μ=λ(.|F), with λ(F)≥ρ0>0. For g=P_q or g=V_q,
if B_g(n) bounds max_L E_λg(nL), then

    F_μ(L↦g(nL))≤g(n)+[B_g(n)−g(n)]/ρ0.             (10)

Every complete L≥1 and g is increasing, so the numerator is nonnegative.
This saves the minimum cost on the deleted event. The original low315 law
cannot replace the conditional low marginal without this lifting and
conditioning argument. A scalar finite-cost representation with signed
hinge coefficients must use the correct upper/lower bounds for each sign.

#### Complete auxiliary tail; the threshold depends on q

Set

    R_q=max_(1≤k<T) (qT−qk)/[a(c−κ(k))],
    m_q=min{m∈positive integers : m²≥R_q},
    B_q=max(T,m_q).

The denominators are positive. For y≥m_q, the k=T term in(2) dominates,
so V_q(y)=acy²−qT. For every integer n≥B_q, all complete L≥1 satisfy

    P_q(nL)=qT+W(nL−T)/d,
    V_q(nL)=acn²L²−qT.

Thus, for M≥max_LE_μL and G≥Γ(μ),

    F_μ(P_q(nL))+F_μ(V_q(nL))
        ≤W(nM−T)/d+acn²G.                           (11)

The qT constants cancel. Equality holds with exact M,G. Generic optimized
knots do NOT guarantee m_q≤T; assuming the old cutoff T without checking
R_q is invalid. The diagonal knots satisfy m_q≤T−1.

Let π_n=Pr(N=n), and form the exact tail probability and moments

    P_tail=1−Σ_(n<B_q)π_n,
    M_tail=E N−Σ_(n<B_q)nπ_n,
    S_tail=E N²−Σ_(n<B_q)n²π_n.

With certified finite costs U_n,V_n from(10) or a stronger whole-cost
calculation, a complete bound is

    C_p(q)≤Σ_(n<B_q)π_n(U_n+V_n)
       +W(M M_tail−T P_tail)/d+acG S_tail.            (12)

No auxiliary tail is discarded. AP supplies

    E N=Π_(r<p)[1+c_r/(r−1)],
    E N²=Π_(r<p)[1+c_r(3r−1)/(r−1)²].

#### Original zero and unit labels remain available

The fixed-q route also permits the existing FL1–FL4 order of operations.
Let h be an original old-tail exponent tuple and let A_h be the event
h≤K for the auxiliary height vector. Keep that tuple's head layout fixed
across every auxiliary outcome. Define

    g_h^P(z)=E[1_(A_h) P_q(Nz)/N],
    g_h^V(z)=E[1_(A_h) V_q(Nz)/N].

Collecting each original layout before maximizing yields the valid bounds

    Wβ+aΓ(wν)≤C_p^labels(q)
      :=Σ_h[F_μ(g_h^P)+F_μ(g_h^V)]≤C_p(q).            (13)

The mixed current-depth weights sum to1, exactly as in AP3–AP4. The tested
family has one completed head layout per old-tail tuple. No q depending
on the sampled N is introduced. Selected tuples, including the always
active zero tuple, can be evaluated before relaxing the remainder.

No new inverse-moment constant is necessary. Define

    Pcor(n,z)=P_q(nz)−Wnz/d−qT+WT/d,
    Vcor(n,z)=V_q(nz)−acn²z²+qT.

These are nonnegative; Pcor vanishes for n≥T and Vcor for n≥m_q. With
w_h=Pr(A_h), r_h=E[N1_(A_h)], and π_h(n)=Pr(A_h,N=n), put

    f_h^P(z)=(W/d)w_h z+Σ_(n<T)π_h(n)Pcor(n,z)/n,
    f_h^V(z)=ac r_h z²+Σ_(n<m_q)π_h(n)Vcor(n,z)/n.

They differ from g_h^P,g_h^V only by constants, hence retain convexity and
monotonicity. The identity Σ_h1_(A_h)=N gives exactly

    C_p^labels(q)=Σ_h[F_μ(f_h^P)+F_μ(f_h^V)]−WT/d.    (14)

The inverse-N constants cancel globally. This is a reorganization of the
existing original-label Jensen proof, not a new independence assertion.

#### A separate valid route allowing q_n

For a cutoff K0≥0 satisfying W≥aK0(p−1)/d, define

    H_K0(z,y)=W(z−T)_+/d
      +a[cy²−(c−κ(z))min(y²,K0)].

This majorizes H0 and is increasing, separately convex and supermodular;
it is also jointly convex under that condition. At a fixed head point,
form a tagged union of original mixed labels and NONUNIT test labels,
keeping the test unit class as a fixed offset1. The set functional is
H_K0(1+Σmixed,1+Σnonunit_test), so every intermediate subset remains in
the domain z,y≥1. Each tag adds a nonnegative amount to only one coordinate.
Separate convexity and
increasing differences make this Boolean set functional supermodular.
The existing `KernelChain.comparison` therefore compares both families
with ONE common vector of auxiliary heights.

After AP3 completion the coordinates are bounded by
Σ_(j,e)w_e L_(j,e) and Σ_j B_j on the same N active tuples. Joint Jensen,
or successive separate Jensen, proves

    E_νH0(1+R,A)
      ≤E_N max_(L,B) E_μH_K0(NL,NB).                 (15)

At this stage q_n MAY be selected separately for each n. Its right-hand
potential must majorize H_K0, namely

    V_(q,K0)(y)=max_(k≤T)
       {a[cy²−(c−κ(k))min(y²,K0)]−qk}.               (16)

Using the cutoff-free V_q in(16)'s place is not justified: it majorizes
H0, not necessarily H_K0. For n≥T the actual joint cost in(15) is already
exactly W(nL−T)/d+acn²B², so its tail uses(11) directly without potentials.
This distinguishes the valid clipped common-N route from the fixed-q
cutoff-free scalar route; it does not reject adaptive potentials wholesale.

#### Exact improvement at11 on the SH18 probability

Fix `p=11,T=4,W=10000,a=8/25,c=5/3,d=6` and

    kappa(z)=10/(10-min(z,4)),
    q=(0,56/315,128/315,512/315).

Let `Pq` interpolate these four values linearly on[1,4], then continue
with slope `W/d`. Its consecutive slopes are56/315,72/315,384/315,W/d,
which are nonnegative and increasing. Define

    Vq(y)=max_(k=1,2,3,4) [a kappa(k)y²-q_k].

It is the maximum of four nonnegative-leading-coefficient increasing
quadratics and therefore increasing convex on y>=1. Its exact branches are

    (16/45)y²,                     1<=y<=2,
    (16/35)y²-128/315,             2<=y<=4,
    (8/15)y²-512/315,              y>=4.

The middle k=2 candidate only touches the maximum at y=2. In particular
`Vq(1)=16/45` and `Vq(y)-(8/15)y²` is nonincreasing.

For every real z,y>=1,

    W(z-4)_+/6 + a kappa(z)y² <= Pq(z)+Vq(y).

At integer z from1 to4 this follows from the definition ofVq. On each
unit interval below4, `a kappa(z)y²-Pq(z)` is convex in z, so its
maximum lies at an endpoint. Above4 both sides have identical z slope.
This proves the majorant on the actual pair, without a bivariate
conditional-comparison assertion. The q values are fixed before any
auxiliary outcome is sampled.

At the first later prime11 there are no earlier-prime multipliers.
The existing scalar original-label comparison therefore bounds the
same-law combined charge and weighted-cap contribution by

    C11=F_nu[Pq(L)]+F_nu[Vq(L)].

Here nu is exactly the77-point SH18 probability extended and conditioned
as specified by its hash-bound certificate, at arbitrary finite3/5/7
heights. The actual low weights and the survival denominator remain those of SH18.

For Pq, use centerPq(2), the nonnegative increasing convex cut
`(Pq(L)-Pq(2))_+`, and the existing exact affine-tail ratio toL²-1.
For Vq, use centerVq(1)=16/45. Each branch ofVq minus`(8/15)y²` is
nonincreasing, so their maximum is too. Consequently

    0<=Vq(L)-Vq(1)<=(8/15)(L²-1).

The complete omitted-depth square-minus-one budget is multiplied by8/15.
Only the nonnegative cuts are divided by the positive SH18 survival
denominator. Both finite-box maxima use the existing exact280²
singleton-elimination evaluator. All cost entries, maxima, geometric
remainders and final comparisons are rational or bounded integers,
without quantization or optimizer dependence.

The verifier also recomputes the previous diagonal-potential contribution
on the identical law. It establishes a strict improvement of thep11
upper-certificate contribution; it does not assert optimization over all
potentials or close the five-prime continuation. The five-step W=10000
experiment remains unsuccessful.

Run from any working directory with Python3 and NumPy:

    python3 -I -O verify_fixed_q_p11.py

The adjacent source directory (or an explicit --source-dir) must contain the three canonical prerequisites
named and SHA256-bound in`fixed_q_p11_certificate.json`. The verifier
imports only the bound canonical whole-cost module plus the standard
library and NumPy. It reconstructs both candidates'1080 depth-cost
observations and compares the full small certificate. No scratch module,
optimizer or saved floating search state is used.

The exact new contribution and saving are

    C11 ≤ 123671919835372486258252472/51821334214349426015625
        < 2386.505900,
    old diagonal bound − new bound
        = 310704719600900799682/4441828646944236515625
        > 0.069949731.

The largest integer intermediate bound is8015014558798784, below2^63.
This compares two upper-certificate formulas; it is not a decrease of the
actual system's assigned charge or a claim of optimality over all potentials.

### Support dominance reduces the complete actual315 carrier task

Fix one of the six canonical old45 survivor sets S used by the existing actual-carrier classification. The pure7 digit0 is forbidden. The five distinct mixed labels are7d for d in(3,5,9,15,45); each may choose its own old cylinder and7digit. A carrier is encoded by the sorted multiset of its nonempty deletion masks U_y⊆S, y∈{1,…,6}. Repeated masks retain multiplicity and absent masks are empty. Its support is Ω_U={(x,y):x∈S\U_y}. The canonical classification contains965595 such states and170569 orbits under the permitted common CRT root maps.

The following finite reduction leaves56966 inclusion-minimal carrier orbits. It does not claim a moment bound for these remaining cases. The already proved PG1 law certifies232 carrier orbits by support inclusion, including exactly one of the56966 minimal orbits.

#### Support inclusion and the actual higher family

For two carriers A,B on the same S, there exists one common7digit permutation with Ω_A⊆Ω_B after transport if and only if the nonempty masks of B inject into distinct nonempty masks of A, with B_i⊆A_j on each matched pair. Necessity follows by taking complements at each digit. Conversely, use those matched digits and then biject the remaining empty B masks to the remaining A digit positions. Padding to six digits makes this a permutation. A nonempty B mask cannot be assigned to an empty A mask. Duplicate masks remain distinct matching vertices.

Thus a Boolean matching problem on at most five nonempty vertices decides inclusion. The checker represents each target's eligible source digits by a bitmask and exhaustively chooses distinct eligible bits. It also considers the permitted old3/5 root maps. These preserve every cylinder family and extend to every finite higher prime-power depth, as established by the canonical classification.

The moment-bound transfer requires its quantifiers in the correct order. Suppose PG1 supplies a fixed low law μ_A on Ω_A and the stated bound for its uniform higher-digit lift, conditioned on **every** admissible actual higher357 forbidden family. Let T be an allowed coordinate map with TΩ_A⊆Ω_B. Now fix an arbitrary physical height Q and an arbitrary actual higher forbidden family H_B for the larger carrier. Pull H_B back through the extension of T to obtain H_A=T^−1H_B. Each residue cylinder is still a single cylinder of the same original modulus, so the original labels remain distinct and H_A is an admissible higher family.

Apply PG1 to μ_A and this H_A. Push the resulting conditional law forward by T. The pushed law is supported on Ω_B and avoids the actual H_B. It is precisely the uniform higher-digit lift of T_*μ_A conditioned on avoiding H_B. Complete test families pull back to complete test families with the same original modulus labels, so the same moment bound holds. This does not identify higher classes belonging to different carriers: their relation is explicitly the pullback through T, followed by the universal PG1 theorem.

The base law T_*μ_A may give zero mass to the extra points of Ω_B. All cylinder caps, selected higher deletion groups, and geometric-tail estimates are transported with that law. Their dependence is on the law, cylinder families, and original higher-modulus labels; they do not require retaining the source carrier's particular low forbidden residues as the target low family. No ambient uniform-density alternative is used and no geometric tail is truncated.

#### Every carrier contains an essential one

An original mixed label is redundant if its old mask is empty, its digit is0, or its old mask is contained in the union of the other masks at its digit. There is always an unused nonzero digit: only five mixed labels can occupy six available digits.

Move a redundant label to a nonempty old cylinder at an unused nonzero digit. Its old deletion was already supplied by the pure7 exclusion or other labels, so no old deletion is lost. At least one new actual low point is deleted. The original modulus label is unchanged. Repeating strictly increases an integer deletion count in a finite space, so the process terminates. At termination, every label has a private deleted point at its digit. The final carrier is a subset of the original carrier.

For a nonempty label subset J⊆{0,…,4}, enumerate its old cylinder choices. Retain a union U only when every chosen cylinder has a point outside the union of the other cylinders in that block. Partition all five labels into nonempty blocks and collect the resulting sorted union multisets. This enumerates exactly the carriers admitting an all-essential labelled realization. Taking the same old-coordinate quotient yields107695 essential carrier orbits. Any support theorem proved on those carriers applies to all170569 original carrier orbits by the preceding subset transfer. This is a sufficient reduction even when a carrier admits several different labelled realizations.

#### Exact five-label resource DP

The essential reduction is not minimal: a carrier whose five labels are all essential can still contain another realizable carrier obtained by reallocating the coarse and fine original labels. The following DP decides this exactly.

For each nonempty label subset J, let V_J be all old masks obtainable as a union of one cylinder for each label in J. For a required nonempty target mask B define

    c_J(B)=max {|U|: U∈V_J and B⊆U},

with value infeasible if no such union exists. The program retains an actual union and original cylinder assignment attaining every finite maximum. Empty old cylinders need not be added when maximizing c_J: replacing one with a nonempty cylinder only increases its union and remains a valid choice of that original label.

Let B_1,…,B_k be the nonempty target digit masks, k≤5. Assign each B_i a nonempty label subset J_i, disjoint from all the others. The labels in J_i will occupy that target digit. If label j is left over, place it at a fresh unused nonzero digit and choose an old cylinder of maximum size m_j. The total number of occupied digits is at most

    k + (5−Σ_i |J_i|) ≤ 5 < 6.

Thus this completion is always physically realizable. It also handles labels that were originally absent, had empty old masks, or occupied digit0: their original deletion contributes nothing, and the maximization may place them on a fresh surviving digit.

The exact largest deletion count among all realizable carriers whose support lies inside Ω_B, up to one common7digit permutation, is

    D_max(B)=max_(disjoint nonempty J_i)
              [Σ_i c_(J_i)(B_i)+Σ_(j left over)m_j].

For the upper bound, align any containing-deletion carrier with the k target digits. The original labels occupying those digits form the disjoint nonempty J_i. Its deletion at digit i is at most c_(J_i)(B_i). All remaining digit unions together have cardinality at most the sum of the individual maxima m_j of their labels. For attainment, take a maximizing union for each J_i and place each remaining label at its own unused digit. CRT realizes every chosen old cylinder/digit pair with its original modulus7d. This proves equality, rather than merely an upper bound.

The recurrence uses a remaining-label mask R of size32:

    M((),R)=Σ_(j∈R)m_j,
    M((B_1,…,B_k),R)=max_(nonempty J⊆R)
                        [c_J(B_1)+M((B_2,…,B_k),R\J)].

A branch with fewer available labels than required nonempty digits is infeasible. Infeasible c_J terms are omitted. The result is D_max(B)=M((B_1,…,B_k),{0,…,4}). Replacing all c_J realizations by their maximizing union is valid because distinct digits have disjoint physical point sets and the rest of the recurrence depends only on the unused original labels.

Write D(B)=Σ_i|B_i|. The target carrier is feasible in its own maximization, so D_max(B)≥D(B). It is inclusion-minimal exactly when equality holds. If D_max(B)>D(B), a maximizing realization has a strictly smaller support contained in Ω_B. Every maximizing realization is itself inclusion-minimal: a still smaller realizable support would delete more than D_max(B), a contradiction.

Here the initial definition of minimality fixes S pointwise and allows one common7digit permutation. The resulting feasible carrier class is closed under the allowed old3/5 maps. Therefore allowing an old map in the domination relation gives the same minimality criterion: its image is already another feasible carrier in the DP domain. Minimality is consequently well defined on the combined old-map/global7digit orbits. No independent digit relabelling at separate old points is used.

#### Complete finite counts

| Canonical old45 shape | All carrier orbits | Essential orbits | Inclusion-minimal orbits |
|---|---:|---:|---:|
| root1, same root / other column |31833|20144|9793|
| root1, other root / same column |15451|9593|5495|
| root1, other root / other column |40281|25613|15233|
| root2, same root / other column |36152|22987|12362|
| root2, other root / same column |12692|7834|3529|
| root2, other root / other column |34160|21524|10554|
| Total |170569|107695|56966|

The essential family has640932 states before old-coordinate quotienting. The resource DP finds strict support dominators for50729 of its107695 orbits. Since every original carrier first contains an essential one, these56966 minimal orbits are a complete sufficient domain for any universally transferable supported-law theorem at these six old geometries. Their numerical target remains to be proved casewise or by further uniform arguments.

For an explicit example in the root2, other-root/same-column shape, the carrier with deletion masks(1,16,16,1160,22866) has83 points and contains a79point carrier with masks(16,16,1160,5155,22866), after a common digit permutation. Its maximizing construction allocates each of the original cofactors3,5,9,15,45 exactly once. The certificate records corresponding actual cylinder masks by digit; their union and label-disjointness are checked.

#### The PG1 law covers232 carrier orbits

The canonical PG1 certificate gives the75point carrier in the root2, other-root/other-column shape and the exact bound

    Γ ≤ 105976769844774468812903/2920804491373837228125 < 3849/106.

Its nonempty deletion masks are(2320,32768,33808,38032,44378), with bit order given by that canonical old45 geometry. All75 supplied point weights are strictly positive. The checker reads the existing PG1 certificate, reconstructs its actual support, verifies the original low modulus set and raw integer weights, pins this inherited bound and target, and pins the canonical JSON representation of the complete published source certificate by SHA-256. The numerical PG1 proof is reused from the existing canonical `verify_point_geometry.py`; this dominance entry does not recompute its two moment oracles.

Considering the12 old-coordinate images and testing the exact digit-mask inclusion matching covers1648 carrier states, or232 combined carrier orbits. The PG1 carrier is itself inclusion-minimal, so exactly one of the56966 minimal orbits is covered by this inherited certificate. The other covered carriers are larger supports to which the quantifier-preserving transfer applies. This does not assert numerical bounds for the remaining minimal orbits.

#### Reproduction and verification boundary

Keep this entry point separate from the existing classifier and its certificate. With its files beside the canonical geometry classifier, canonical old-profile certificate, canonical PG1 certificate, and the mod3-conditioned certificate below, run

```sh
python3 -I -O verify_carrier_dominance.py
```

An external canonical directory can be selected with `--canonical-directory`; `--check` selects the small result certificate. The entry uses the canonical geometry module through an explicit adjacent path, which works under isolated Python. It imports only standard-library modules, uses unbounded integers and explicit guards, validates all consumed integer inputs, and pins the geometric domain and inherited PG1 bound.

The checker reconstructs all essential carrier states, verifies root-group orbit closure and accounting, recomputes the six exact resource DPs, verifies label-disjoint constructive witnesses, and hashes the reconstructed state/orbit sets without retaining large lists. For one minimal and one dominated target in each shape, it independently scans every essential carrier using only the injection matcher and confirms the DP's maximum deletion count. It also recomputes all232 PG1-covered orbits. The small certificate retains counts, hashes, and explicit witnesses. These are finite arithmetic results and ordinary support/all-height transport proofs; no new Lean admission or resolution of unrestricted Erdős #7 is claimed.

### Retaining the original mod3 test in higher-deletion energy

The actual probability in PG1 admits the stronger bound Γ≤69/2=34.5.
A second actual75point carrier admits Γ≤35, below3849/106, at arbitrary
finite original3/5/7 heights. The new estimate keeps the original mod3
test class in both the square bound and the energy removed by higher
forbidden classes. The signed deletion identity is the same one used
in(SD5); its present application retains a nonuniform actual315law and
the three-coordinate grouped deletion bound(SH15).

#### Same original test class on both sides

Let μ be a probability on an actual low315survivor carrier Ω, let λ be
its independent uniform lift in all additional3/5/7digits, and let F
avoid every actual higher forbidden class. Write q_actual=λ(F).
All original exponent labels remain distinct. Let R_E(σ) be the
grouped deletion bound in(PG1), now evaluated on any nonnegative finite
low measure σ, without renormalizing it. The proof of(SH15) gives

    ∫_(Fᶜ) h(x) dλ ≤ R_E(h μ)                         (M3-1)

for every nonnegative function h of the low point. Indeed, the proof
is a pointwise conditional union bound followed by nonnegative sums
and maxima of linear integrals. It does not require that h μ have
mass one. Its cylinder caps and all three grouped contributions use
precisely h μ. Independently, R_E(μ)<1 ensures q_actual>0.

Fix a complete original test family L and let i be its residue for
the original modulus3. Then

    b_i=1+1_(x≡i mod3),       L≥b_i.

For K≥4, put h_i=K−b_i²=K−1−3·1_(x≡i mod3)≥0. If U_i bounds E_λL²
for every complete test whose original mod3 class is i, the exact
deletion identity and(M3-1) give

    q_actual(E_(λ|F)L²−K)
      = E_λL²−K + ∫_(Fᶜ)(K−L²)dλ
      ≤ U_i−K+R_E(h_i μ).                              (M3-2)

Consequently the finite criterion

    R_E(μ)<1,    U_i+R_E((K−1−3·1_(x≡i mod3))μ)≤K
                 for every original test root i       (M3-3)

implies Γ_(λ|F)≤K. The higher forbidden classes are arbitrary and
are not identified with the test classes. In particular their
maximizers in R_E are not constrained to the test root i.

#### Why the all-height comparison preserves this label

The saturated thresholds are h=(2,1,1). Projection d=3 has ternary
exponent1<2 and the other two exponents0<1, so it comes from exactly
one original label, modulus3, and w_3(Z)=1. Thus the saturated-prefix
comparison and the convex-hull maximization can keep this cylinder
fixed. For each fixed i the valid square comparison is

    E_λ L² ≤ E_Z F_i(Z),
    F_i(z)=max_(low layouts with C_3=i mod3)
                 E_μ(Σ_(d|315)w_d(z)1_Cd)².           (M3-4)

Other low cylinders may maximize separately at each z. The same i
is retained throughout the expectation and in(M3-2). One cannot
replace it by a z-dependent test root in the deletion term.

The two finite relaxations from(PG1) apply with only their non-seven
low layout A constrained to mod3 root i. The cofactor3 in B refers
to the original modulus21 and remains unrestricted. Denote their
pointwise minimum at the fixed law by H_i(z). No convexity of this
minimum is asserted. The genuine-layout increment gives

    F_i(z)≤F_i(0)+P(z)−P(0),

with the same complete nonnegative pair-cap polynomial P as in(PG1).
Therefore for B=[0,8]×[0,5]×[0,4], β=Pr(Z∈B), the exact full-tail bound is

    U_i=(1−β)H_i(0)+Σ_(z∈B)Pr(Z=z)H_i(z)
                         +Σ_d η_out(d)m_d.             (M3-5)

The coefficients η_out include all omitted geometric depths. Finite
physical heights, including heights appearing only in later-prime
moduli, are bounded by these infinite geometric moments. Both
specified carriers omit root0 at3; changing a test from that empty
root to either nonempty root increases L pointwise, even after
conditioning. It is therefore sufficient to check i=1,2.

For probability optimization, fix K and choose one of the two square
relaxations at each root and depth before optimizing μ. Each chosen
relaxation, each cylinder cap, and R_E(h_i μ) is a maximum of linear
functions of μ, with nonnegative combination coefficients. Thus
(M3-3) gives a finite convex feasibility problem on the actual point
weights. The pointwise minimum may still be used to evaluate a fixed
law, as in the certificate; it is not used as a convex outer oracle.

More generally, if g is increasing, V_i≥E_λg(L) and C≥g(2), the same
proof replaces h_i by

    C−g(b_i)=(C−g(1))−(g(2)−g(1))1_(x≡i mod3).

If g is also convex and has finite geometric expectation, the
fixed-i saturated comparison supplies V_i by the same convex-hull
argument. This general statement does not supply new numerical
hinge bounds by itself.

#### Two exact actual-law certificates

The first case uses the unchanged PG1 family and its75 integer
weights of total1000000007. The second family is

```
(3,0),(9,4),(5,0),(15,11),(45,1),(7,0),
(21,5),(35,4),(63,50),(105,59),(315,44).
```

Its actual complement has75points. The adjacent certificate lists
every point and nonnegative integer weight, with total999999994.
For each case the law λ|F is supported on this actual low carrier
and avoids every higher forbidden class, at every finite3/5/7height.

| Low carrier | Same-law unit-loss bound | New K | Independent lower bound for λ(F) |
|---|---:|---:|---:|
| PG1 |36.2834178589…|69/2|25428074957/48000000336|
| Second75point family above |36.7917311533…|35|25170030757/47999999712|

The minimum margins K−U_i−R_E(h_i μ) over both roots are respectively

    2637433975198231346789/55135363885947544500000 >0,
    697199872596794233/91892271948646365000 >0.

Thus both improve3849/106. Each comparison holds on one unchanged
probability: there is no root-dependent choice of μ or conditioning
event. The existing support-inclusion transport applies because
the result holds for every admissible higher forbidden family.

The second carrier lies in `root2_other_same_column`. Its canonical
nonempty deletion masks are(1,1057,1160,5155,42669), and it is another
inclusion-minimal orbit. Its18 old-coordinate images transfer the
Γ≤35 bound to2291 carrier states and152 carrier orbits. The source's
original-label realization is reconstructed from the eleven classes
above; support containment uses the same injective mask matcher as
the preceding dominance result.

These152 orbits are disjoint from the232 PG1 orbits, giving3939states
and384orbits with Γ≤35, including two of the56966minimal orbits.
An exact6×6 old-support embedding table has zero off-diagonal
entries. To verify completeness, the old projection has two ternary
roots with respectively two and three nonempty mod9 children, and
uses all four nonzero5columns. A cylinder-preserving embedding must
preserve these root types; its restrictions are among2!·3!·4!=288
row/column maps. Their exhaustive checks show that the two source
shapes cannot overlap or transfer to a third canonical old shape.
The revised dominance entry recomputes this table and both covered
sets, pins the complete mod3 source certificate, and retains its
original PG1 fields unchanged. It inherits the two numerical
endpoints from the new moment verifier; it does not reprove them.
The other56964minimal orbits and unrestricted-prime continuation
remain unresolved by these two certificates.

`verify_mod3_conditioned_geometry.py` reconstructs both actual
families and weights, both fixed-root square bounds at all270depths,
the independent survival bounds, the four nonnormalized weighted
deletion bounds, and the full geometric remainders. It uses the
adjacent geometry evaluator with optional original-root restriction;
the original PG1 verifier retains its unrestricted default behavior.
Run the new entry with `python3 -I -O`. Every final comparison is
integer or rational and all NumPy arithmetic has explicit signed64
range guards. These certificates accompany the ordinary all-height
proof above; they are not Lean kernel proofs of the new endpoints.

### Separating an original saturated test from its higher labels

The unchanged PG1 probability satisfies the stronger all-height bound

    Γ ≤ 492647095380812739054683/14604022456869186140625
      <135/4=33.75.                                    (M9-1)

On this same probability, the threshold-two hinge is at most3 and
the mean is at most5, as established below.

Here the low geometry, all original3/5/7 exponent quantifiers and the
actual higher forbidden family are exactly those of(PG1). This bound
also transfers to its232 containing-carrier orbits. The improvement
keeps both the original mod3 test i and the original mod9 test j.
Unlike modulus3, modulus9 is a saturated projection. Its original
class must be separated from its descendants before applying the
convex-hull step.

#### The original class and the projected aggregate are different

Fix the original test classes C_3=i mod3 and C_9=j mod9. Projection9
has the original modulus9 and the higher pure ternary moduli27,81,….
After the additional-coordinate prefix comparison, its active terms
are bounded by

    1_(C_9) + min(Z_3,n_3)·1_(D_9),                   (M9-2)

inside the convex maximization. The first class stays fixed. Only
the active higher labels enter the convex average whose extreme
cylinder is D_9. At zero matching depth there are no such labels,
so the second term is zero. Increasing min(Z_3,n_3) to Z_3 gives the
uniform-in-height bound. Each higher exponent remains a different
original modulus; the averaging step only bounds the cost.

For a low layout θ of all remaining projected cylinders, put

    L_ij(z,θ)=1_(j mod9)+z_3·1_(D_9)
                       +Σ_(d|315,d≠9)w_d(z)1_(C_d),
    C_3=i mod3,
    F_ij(z)=max_θ E_μ L_ij(z,θ)².                    (M9-3)

The coefficient of the original unit label is one. Prefix comparison
followed by Jensen on the higher9 labels and the other projected
families gives E_λL²≤E_ZF_ij(Z). Both i and j are fixed across Z;
θ may maximize separately at each Z. Taking an aggregate cylinder
from(SH10) and calling it the original9 class would not justify this
formula.

In the pure7 and fixed-A relaxations, the low A load is therefore

    A_z=1+1_(i mod3)+(1+z_5)1_(C_5)+1_(j mod9)
        +z_3·1_(D_9)+(1+z_5)1_(C_15)
        +(1+z_3)(1+z_5)1_(C_45).                      (M9-4)

The high B load is unchanged: its cofactor9 belongs to original
modulus63 and its descendants, and retains coefficient1+z_3.
Both45 singleton coefficients remain(1+z_3)(1+z_5), so the existing
two-singleton elimination applies with different low and high base
loads. The fixed-A digit partition uses the same modified A and the
unchanged high-label coefficients.

#### Complete tail and actual deleted energy

The same pair-cap polynomial P still controls the omitted depths:

    F_ij(z)≤F_ij(0)+P(z)−P(0).                         (M9-5)

For proof fix θ, write L_ij(z,θ)=L_ij(0,θ)+Δ with Δ≥0, and expand
2L_ij(0,θ)Δ+Δ². Every coefficient is nonnegative. Each pair of low
cylinders has mass at most m_lcm(d,e), including a pair involving
the fixed original9 and its separately chosen higher D_9. Upon
grouping by projected labels, the coefficient increments sum to
w_d(z)w_e(z)−1. This proves the increment bound for the same θ.
Maximizing its zero-depth part gives(M9-5). No common residue between
original9 and D_9 is assumed.

Let H_ij be the pointwise minimum of the two finite relaxations at
the fixed μ. Equation(M3-5), with H_ij in place of H_i, gives U_ij,
including every geometric depth outside[0,8]×[0,5]×[0,4]. For the
actual complete test,

    L≥b_ij=1+1_(i mod3)+1_(j mod9).

For any reference C≥9, the positive finite measure(C−b_ij²)μ can be
used directly in the same grouped deletion bound. Consequently

    q_actual(E_(λ|F)L²−C)
                    ≤ U_ij+R_E((C−b_ij²)μ)−C.          (M9-6)

If q_actual≥q_0>0 and

    E=max(0,max_(i,j)[U_ij+R_E((C−b_ij²)μ)−C]),

then Γ_(λ|F)≤C+E/q_0. The reference C need not itself be a valid
moment bound. Here C=33 and the computed positive excess is

    E=5357177152064798207029/13783840971486886125000,
    q_0=25428074957/48000000336.

Their exact value33+E/q_0 is(M9-1). Its gap below135/4 is
954650154089172765643/58416089827476744562500>0. Thus this certificate
does not claim Γ≤33. The maximum excess occurs at i=2,j=2.

The PG1 support has two nonempty mod3 roots and five nonempty mod9
roots. A test class empty on that support can be moved to a nonempty
class, increasing the complete load pointwise before and after the
same conditioning. All ten remaining pairs are checked. The
probability weights and forbidden family are independent of that
test pair.

#### A threshold-two bound on the same probability

For the actual low weights define R_x=Σ_yμ_(x,y) and
v_x=max_yμ_(x,y). For any increasing convex g, a valid common-layout
upper bound is

    max_(A,B) Σ_x[(R_x−v_x)g(A_x)
                      +v_x g(A_x+(1+z_7)B_x)].         (M9-7)

Here A is(M9-4), with i,j fixed, and B retains the unchanged old45
weights. To prove the bound, fix all old cylinders and at each row
let t_y be the high-label load on digit y, with Σ_y t_y=t=(1+z_7)B_x.
The convex chord inequality gives
g(A_x+t_y)≤g(A_x)+(t_y/t)(g(A_x+t)−g(A_x)) for t>0.
Since Σ_yμ_(x,y)t_y≤v_xt, summing proves(M9-7). The case t=0 is
immediate. The bound allows rowwise concentration only as a cost
upper bound; no actual test cylinder or forbidden digit is moved.

For g(l)=(l−2)_+, the high term is linear because A≥1 and B≥1.
The maximizing B mean is the sum of its six weighted cylinder caps
under v, independent of A. Thus full enumeration of A suffices for
an exact maximum of this relaxation. The one-Lipschitz property of
g gives the complete outside-box estimate

    F_g,ij(z)≤F_g,ij(0)+Σ_d(w_d(z)−1)m_d.             (M9-8)

Its omitted coefficients are the exact first geometric moments
E[1_(Z∉B)(w_d(Z)−1)], all nonnegative. This includes the separated
higher9 term z_3; the fixed original9 contributes no increment.

The original test satisfies

    g(L)≥g(b_ij)=1_(i mod3)·1_(j mod9).

Applying the deleted-energy identity to g, with reference C=3, gives

    q_actual(E_(λ|F)(L−2)_+−3)
       ≤ U_g,ij+R_E((3−1_(i mod3)1_(j mod9))μ)−3.     (M9-9)

All ten right-hand sides are negative in the exact certificate, with
minimum margin43684194883477173419/1531537885720765125000>0.
The measure inside R_E uses the same low μ as the square bounds;
it is not normalized or averaged over j. Therefore

    sup_test E_(λ|F)(L−2)_+≤3,
    sup_test E_(λ|F)L≤5.                              (M9-10)

The second conclusion uses the pointwise inequality
L≤2+(L−2)_+. Both bounds hold together with(M9-1) for every actual
higher forbidden family, on exactly the same conditioned law.

`verify_original9_conditioned_geometry.py` binds the existing PG1
probability source by hash, reconstructs its support, and recomputes
both integer square maxima at all270depths for all ten pairs. It also
recomputes the threshold-two maxima, the independent positive mass,
the corresponding weighted deletion bounds, and the complete first
and second geometric remainders. The adjacent certificate
stores these finite arithmetic data and the exact excess conversion.
Run it with `python3 -I -O`. The proof above is an ordinary all-height
argument with an exact certificate; no new Lean endpoint, global
low-configuration bound or unrestricted-prime continuation is claimed.

### A uniform 86-point profile has all-height moment bound 35

Fix the old forbidden classes

```text
(3,0), (9,4), (5,0), (15,1), (45,37)
```

and the pure-seven class `(7,0)`. The old complement, in increasing order, is

```text
X = [2,7,8,11,14,17,19,23,26,28,29,32,34,38,41,43,44].
b = [0,3,0,0,1,0,3,0,0,1,1,0,4,0,0,2,1].
```

For any actual choice of the five remaining original low classes, with moduli
21, 35, 63, 105 and 315, record the deletion mask in each nonzero seven digit.
Its coordinate sum is the deletion vector. Consider every actual carrier whose
vector is an image of `b` under an allowed old-coordinate automorphism. The
complete carrier classification gives six mask states, in three old-coordinate
orbits, represented by the full nonempty mask multisets

```text
[2,4160,36866,37442,70736]
[4160,36866,37442,70738]
[4162,36866,37442,70736].
```

Each is inclusion-minimal and has 86 points. The certificate gives an original
five-label realization of each representative. The verifier reconstructs all
actual states of this old shape, selects the entire vector orbit, and checks
these counts and realizations; it does not infer the full carrier from `b`
alone.

For every carrier in this profile let μ be the uniform probability law on all
its 86 actual points. For arbitrary finite nonnegative integers n3, n5, n7,
lift μ uniformly in the added prime-power digits to
`Q = 3^(2+n3) 5^(1+n5) 7^(1+n7)`, obtaining λ. Choose arbitrary actual higher
forbidden classes, at most one for each distinct original divisor of Q which
does not divide 315, and let F be their surviving event. Then λ(F)>0, and for
every complete test family with one residue class C_m for each m dividing Q,
including the unit class, its load L satisfies

```text
E_[λ(.|F)] L² ≤ 35.
```

The quantified higher family is arbitrary; its cylinders are not required to
be centered or nested. The proof uses a moment domination and a separate bound
on the actual deletion event.

For the moment bound, let independent auxiliary geometric variables have
`Pr(Z_p=k)=(p−1)/p^(k+1)`, for p in {3,5,7}. Saturate exponents at (2,1,1), and
put

```text
w_d(z) = product of (1+z_p) over p for which v_p(d) is saturated.
```

The saturated-prefix moment argument bounds E_λ L² by the expectation of the
largest weighted low-layout square. Original higher modulus labels retain
their extra exponents: equal saturated cofactors do not identify them. Keep
the original mod-3 test root i fixed, for i=1 or 2. At each height z write
`u=1+z7`, and let A_i and B range over complete old-45 test layouts with
cofactor weights

```text
cofactors:  1, 3, 5,       9,       15,      45
weights:   1, 1, 1+z5,    1+z3,    1+z5,    (1+z3)(1+z5).
```

Only A_i has its cofactor-3 root fixed to i. The pure-seven upper bound keeps
one common digit j for the pure-seven test class. With old-fibre masses R_x,
maximum point masses v_x and point masses μ_(x,j), it is the maximum of

```text
Σ_x [ R_x A_i(x)²
    + v_x (2u A_i(x)(B(x)−1) + u²(B(x)−1)²)
    + μ_(x,j) (2u A_i(x) + u²(2B(x)−1)) ].
```

This follows by expanding the square: terms involving the pure-seven class
use its one actual digit, while the other seven-divisible intersections are
bounded by v_x. All coefficients multiplying μ_(x,j) are nonnegative. Every
profile carrier has at most five occupied deletion digits, leaving a nonzero
digit untouched. Uniformity therefore gives `R_x=(6−b_x)/86`, `v_x=1/86`, and
a single digit attaining `μ_(x,j)=1/86` for every x. Consequently, at every
height and for both roots, the pure-seven upper bound is exactly

```text
H_i(z) = (1/86) max_(A_i,B) Σ_x [
              (6−b_x) A_i(x)² + 2u A_i(x)B(x) + u²B(x)² ].
```

This is an identity for the stated upper bound, not an assertion that every
relaxed intersection is jointly realizable. It explains why the same integer
moment computation applies to all three carrier orbits, at all heights.

Ordinary caps and the weighted caps used below also depend only on this
profile. For any nonnegative weight f(x) independent of the seven digit, and
e dividing 45, the caps of the finite measure fμ are

```text
m_e(fμ)  = (1/86) max_a Σ_(x≡a mod e) (6−b_x) f(x),
m_7e(fμ) = (1/86) max_a Σ_(x≡a mod e) f(x).
```

The second equality is attained at an untouched digit. Old-coordinate maps
preserve these cylinder families and the two mod-3 roots; common seven-digit
permutations preserve all relevant intersections. Thus moments and caps
transport to all six states.

The full geometric tail is retained. Put `B0=[0,8]×[0,5]×[0,4]`, with 270
heights, and β=Pr(Z∈B0). For ordinary caps m_d define
`P(z)=Σ_(d,e|315) w_d(z)w_e(z)m_lcm(d,e)`. The square increment of any fixed
layout is at most P(z)−P(0), since all weight-product increments are
nonnegative. For each root this yields

```text
U_i = (1−β)H_i(0) + Σ_(z∈B0) Pr(Z=z)H_i(z) + Σ_d η_out(d)m_d,
E_λ L² ≤ U_i.
```

Here η_out(d) is the exact coefficient of m_d in
`E[1_(Z∉B0)(P(Z)−P(0))]`. Its computation uses the one-prime pair moments
1, p/(p−1), or p(p+1)/(p−1)² according as neither, one, or both cofactors are
saturated. Subtracting the zero-height term and the finite-box contribution
leaves the nonnegative full remainder. No physical height or geometric tail
is discarded.

For deletions use the original one-extra-prime blocks

```text
E3={9,45}, E5={5,15,45,35}, E7={7,21,35,63,105,315}.
```

For a positive finite measure σ on the actual carrier define

```text
G(σ) = max_(selected low cylinders) ∫ [1−Π_p(1−A_p/(p−1))] dσ,
ρ_d  = E[w_d(Z)]−1−Σ_(p:d∈Ep) 1/(p−1).
```

Here A_p counts the selected cylinders in block p. The factors are
nonnegative, and all ρ_d are nonnegative. Independence of the added prime
coordinates, geometric averaging within each original projected label, and
separate affinity of the product give this grouped bound. Applying the union
bound to the remaining original labels yields

```text
∫_(Fᶜ) f dλ ≤ G(fμ) + Σ_d ρ_d m_d(fμ)
```

for each nonnegative low weight f used here. In particular,
`λ(F) ≥ 1−G(μ)−Σ_d ρ_d m_d(μ)`.

Equality of deletion vectors alone does not establish equality of grouped
maxima. The verifier enumerates all actual masks in the profile, reduces them
to the three representatives, and computes three independent group maxima
on each representative: f=1 and the two weights
`h_i=35−1−3·1_(x≡i mod3)`. These nine exact maximizations give the same results
on each carrier:

```text
86·48 G(μ)     = 1546,
86·48 G(h_1μ) = 52012,
86·48 G(h_2μ) = 48502,
q = 1−G(μ)−Σ_d ρ_d m_d(μ) = 2333/4128 > 0.
```

Taking the maximum over all three checked representatives therefore covers
the entire actual profile. The common final values are

| Root i | U_i | R_i = G(h_iμ)+Σ_d ρ_d m_d(h_iμ) | 35−U_i−R_i |
| --- | --- | --- | --- |
| 1 | 183628451886661/10976021437500 | 30233/2064 | 159032185718981/43904085750000 |
| 2 | 32905/1548 | 14095/1032 | 265/3096 |

Both margins are positive. The unit class and the original cofactor-3 test
class imply `L²≥1+3·1_(x≡i mod3)`. Therefore

```text
∫_F (L²−35) dλ
 = E_λ(L²−35) + ∫_(Fᶜ)(35−L²) dλ
 ≤ U_i−35 + ∫_(Fᶜ) h_i dλ
 ≤ U_i−35+R_i < 0.
```

Dividing by the independently verified λ(F)>0 proves the claimed conditional
bound. A mod-3 test root 0 is empty on the carrier; replacing it by root 1
only increases L, so the two checked roots cover every test family.

Finally, the exact support-inclusion matching covers 821 common-seven-digit
mask states, or 355 old-coordinate orbits, and exactly three minimal orbits.
For a containing carrier and any of its higher forbidden families, pull that
family back through the allowed coordinate map, apply the source result,
and push the source law forward. Extra low points receive zero mass. Thus
these 355 orbits inherit a supported law with the same all-height bound 35;
they are not claimed to satisfy this bound under their own full-support
uniform laws. The matching preserves complete deletion-mask multisets and
original modulus labels.

`verify_uniform_profile_geometry.py` and
`uniform_profile_geometry_certificate.json` reproduce the profile, the
270-height pure-seven computation, all nine actual group maxima, rational
tails and margins, and support counts. This is a finite exact computational
certificate with the all-height argument above; it is not a Lean kernel
verification or a claim about the remaining low-carrier profiles.

The old-support embedding matrix from the complete carrier reduction
separates this old45 shape from both preceding sources. Thus these355
orbits are disjoint from their384, giving739 carrier orbits and five
inclusion-minimal sources with an inherited bound35. The stronger PG1
bounds still apply to its own232 containing orbits. Among the56966
minimal orbits,56961 remain outside these five sources; the general
continuation through11,13,17 and all later primes remains unresolved.

#### A deletion bound determined by row counts, with an exactness criterion

The grouped deletion cost admits a sufficient upper observation even when
the deletion vector does not determine the actual carrier. Fix a finite
old-coordinate set X⊆Z/45Z, numbers f_x≥0 for every x∈X, and N>0.
Let S be a subset of X×{1,…,6}, with exactly6−b_x retained points in row x,
and let the nonnegative finite measure σ give every retained point in
that row mass f_x/N. No probability normalization is required.
Keep the same original projected blocks E3,E5,E7 defined above. Write
A for a choice of the two old cylinders at9,45, and B for a choice of
the three old cylinders at5,15,45. Set T=2−A and M=T(4−B), pointwise on X.
For each choice define

    J_f(b;A,B) = Σ_x(6−b_x)f_x(24A_x+6T_xB_x)
                  +6 max_(a mod5) Σ_(x≡a mod5) f_xT_x
                  +Σ_(c|45) max_(a modc) Σ_(x≡a modc) f_xM_x.

Then the actual grouped cost satisfies

    48N G(σ) ≤ max_(A,B) J_f(b;A,B).                  (UP-1)

Thus this upper bound uses only X,b,f,N. If there are at least two
distinct digits y with X×{y} contained in S, equality holds in(UP-1).

To prove the upper bound, let I be the extra original mod35 cylinder
and C the sum of the six original E7 cylinders. The exact product-union
expansion on the actual carrier has numerator

    24A+6TB+6TI+MC−TIC.

All of T,I,C and f are nonnegative. Dropping the last term increases
the integral. The old-coordinate part integrates with row multiplicity
6−b_x. The single I cylinder is bounded by the displayed mod5 maximum;
each of the six C cylinders is bounded by its displayed old-cofactor
maximum. This proves(UP-1), without moving the actual forbidden family
or replacing its measure.

For equality, choose maximizing old A,B. Put I on one wholly retained
digit and all six C cylinders on the other. Choose each old residue to
attain its own maximum. These are allowed choices of the distinct
original projected labels, their digit supports are disjoint, and every
row used by any of them is retained. Hence TIC=0 and every preceding
upper comparison is an equality. This construction concerns the
maximization defining G; it does not identify or move actual higher
forbidden cylinders.

There is a weaker, layout-dependent equality criterion. Keep one wholly
retained digit for the six C cylinders. For some maximizing A,B and a
maximizing old mod5 residue a for I, it suffices that a different digit y
has zero missing fT mass on that old cylinder:

    Σ_(x≡a mod5, (x,y)∉S) f_xT_x = 0.                 (UP-2)

The same construction then attains the I maximum, while the two digit
supports still make TIC=0. All other upper comparisons are unchanged.

For the preceding profile, the three measures f=1,h_1,h_2 give exactly
1546,52012,48502 in the right-hand side of(UP-1). The two four-mask
representatives have two wholly retained digits. In the five-mask
representative, digit6 is wholly retained and digit5 is missing only
x=7. All three computed maximizers use old mod5 residue4 for I, so
(UP-2) holds on digit5. Thus the row-count formula independently
recovers all nine actual grouped maxima, including the five-mask case.

The verifier enumerates every distinct old cylinder, including one
representative of the empty cylinder when that cofactor has an empty
residue class. This is necessary for the general relaxed maximum:
dropping TIC does not justify assuming monotonicity in A or B.
Its witness check uses the reconstructed original-family carriers to
verify(UP-2). With only one wholly retained digit and no such witness,
(UP-1) remains an upper bound; equality is not asserted. This separates
sufficiency for a numerical upper bound from reconstruction of the
full carrier.

### Uniform35 bounds on a full deletion-profile box

Fix the canonical old45 shape `root1_same_other_column`, its17 old points X,
and the source deletion profile

    b*=(0,3,0,0,1,0,3,0,0,1,1,0,4,0,0,2,1).

For every actual original-label carrier whose deletion profile satisfies
0≤b≤b* coordinatewise, use its own uniform probability measure μ: each
surviving low315 point has mass1/N, where r=6−b and N=Σ_x r_x. The same
conclusion applies after an allowed old-coordinate map; these preserve
both named mod3 roots. There are exactly two images of b*.

Every such actual carrier has an untouched nonzero7 digit, since there are
only five mixed original labels and six available nonzero digits. Thus the
pure7 upper bound, for each original mod3 root i and every geometric depth z,
has unnormalized form

    H_i(r,z)=max_(A with original mod3 root i, B)
             [Σ_x r_x A_x² + Σ_x (2u A_xB_x+u²B_x²)],  u=1+z7.

The layout sets and second sum do not depend on r. Hence H_i is a maximum
of affine functions of r and is convex. Retaining the canonical270-depth
box and its entire exact geometric tail gives

    P_i(r)=(1−β)H_i(r,0)+Σ_(z in box)Pr(Z=z)H_i(r,z)
             +Σ_d η_out(d) C_d(r,1),

where the unnormalized caps are

    C_e(r,f)=max_a Σ_(x≡a mod e) r_x f_x,
    C_7e(r,f)=max_a Σ_(x≡a mod e) f_x,                  e|45.

All coefficients are nonnegative. P_i is therefore convex. Let V(r,f) be
the existing UP-1 old-coordinate group upper bound, written with row counts r.
It too is a maximum of affine functions, since its extra35/E7 contribution
is independent of r. Put h_i(x)=34−3·1_(x≡i mod3) and retain the canonical
nonnegative residual coefficients ρ_d. Define the unnormalized slacks

    S(r)=N−V(r,1)/48−Σ_d ρ_d C_d(r,1),
    M_i(r)=35N−P_i(r)−V(r,h_i)/48−Σ_d ρ_d C_d(r,h_i).

S and both M_i are concave functions of r. At any actual carrier, S/N is a
lower bound for the same-law higher survival probability and M_i/N is the
slack in the same original-mod3 signed35 criterion. There is no renormalization
of h_i μ. The measure and its independent higher-prime lift belong to the
actual carrier being certified; the convexity argument does not substitute
a supported measure or a mixture of source laws.

The box6−b*≤r≤6 has eight varying coordinates and256 vertices. At each vertex,
the retained program evaluates both270-depth moment maxima, all full-tail
coefficients, all caps, and the UP-1 maximum exactly. All256 vertices satisfy
S>0 and M_1,M_2≥0. The smallest normalized slacks are

    S/N  ≥ 2357/4176,
    M_1/N ≥ 159032185718981/43904085750000,
    M_2/N ≥ 265/3096.

For any constant c equal to one of these minima, S−cN or M_i−cN remains
concave and is nonnegative at every vertex. Every box point is a convex
combination of vertices, so the corresponding normalized lower bound holds
throughout the box. In particular, every actual carrier in the stated
profile region satisfies the same35 target on its own full-support uniform
law. This establishes inheritance throughout this source box, not global
coordinatewise monotonicity of the numerical objective.

Geometry-only enumeration of all165141 actual carrier states for this old
shape, followed by exact profile membership and old-map orbit reduction,
gives1339 states in562 orbits with477 distinct profiles. The existing
original-label resource criterion identifies8 inclusion-minimal orbits.
The former source-support region821 states/355 orbits is contained in this
box region. Thus the new region adds518 states/207 orbits and5 minimal
orbits. Membership uses no numerical query on individual carriers.

The verifier `verify_uniform_profile_box.py` pins the parent
`uniform_profile_geometry_certificate.json` by SHA-256. It imports only the
adjacent canonical point, classification and dominance algorithms. Its
certificate retains the rational corner values and hashes of all270-depth
root maxima. It reconstructs all actual carrier states and checks both
containment of former support coverage and the new minimal representatives.

For the moment computation, each old layout consists of a base layout L on
cofactors1,3,5,9,15 plus an old45 singleton of weight
s=(1+z3)(1+z5). For fixed base layouts L_a,L_b and A-singleton location i,
the constant part after eliminating the B-singleton is

    2u<L_a,L_b>+u²||L_b||²+2us L_b(i)
      +max_j[2us L_a(j)+u²(2sL_b(j)+s²)+2us²·1_(j=i)].

The inner maximum equals the larger of its unmodified maximum and its
value at i plus2us². The remaining row-dependent contribution is
Σ_x r_x L_a(x)²+r_i(2sL_a(i)+s²). Maximizing over i and both base layouts,
with only A's originalmod3 root fixed, computes H_i(r,z) exactly. The source
corner reproduces both parent270-depth hashes.
The grouped bound enumerates77760 old A/B pairs, retaining each nonempty
cylinder and one representative of an empty cylinder when present. It
precomputes each affine row coefficient and its r-independent extra35/E7
term, then evaluates every corner. Its nonnegative integer dot products
are bounded by1692,56856,53796 for1,h1,h2, so binary64 arithmetic is exact
below2^53; integers are checked before they enter rational calculations.
The moment calculation itself uses int64 arrays with the present finite
parameters. All guards use explicit exceptions and remain active under-O.

The two other certified old45 geometries are disjoint from this region.
Together the three geometries now cover946 carrier orbits and10
inclusion-minimal orbits at Gamma≤35. Of the56966 minimal orbits,
56956 remain outside these certified sources. The PG1 bounds retain
their stronger values on its232 containing orbits.

Replay the certificate from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/verify_uniform_profile_box.py

This is finite arithmetic verification plus the concavity argument above,
not a Lean kernel result. The stated profile region is a hypothesis;
no bound for another old shape is asserted here.

### Original9 higher hinges and a fixed 11/13 continuation

Keep exactly the PG1 low probability, lift lambda and actual higher
survival event F from(M9-1)--(M9-10). Let nu=lambda(.|F) and
H_t=sup_test E_nu(L-t)_+. All original3/5/7 heights remain arbitrary.
The unchanged square and threshold-two bounds, together with the new
observations below, hold on this one probability:

    G=492647095380812739054683/14604022456869186140625,
    H_2<=3,
    H_4<=2394156525804976633271/1622669161874354015625,
    H_6<=4106398428533515693477/4868007485623062046875.    (M9C1)

The last two bounds are respectively less than1.475444 and0.843549.
They use no numerical observation from the different(SH18) probability.
The meaning of the common-law profile and its interpolation is the same
as in[SH22--SH24](#a-direct-threshold-two-correction-and-simultaneous-bounds).

#### Fixed original classes and the complete first-moment tail

For every pair i,j of nonempty original3/original9 roots, retain the
separated A load in(M9-4) and the unchanged B load. In particular, i,j
are fixed across all auxiliary depths Z; only the higher projected9
cylinder varies. At each depth use the row relaxation(M9-7), now with
g_t(l)=(l-t)_+, t=4,6. Write its maximum as H_t,ij(z).

The exact two-singleton elimination(SH21) applies with low weight
R_x-v_x and high weight v_x. The same convex-increment argument permits
these unequal nonnegative weights. If1+z_7>=t-1, then
A+(1+z_7)B>=t, and the high hinge is linear, so its A and B maxima
separate. Otherwise the two-singleton calculation retains their common
old layouts. It allows rowwise high-digit concentration only as an
upper relaxation, and moves no actual forbidden class.

For the true fixed-root maximum F_t,ij(z), the one-Lipschitz property
of the hinge gives, for each fixed layout and hence after maximization,

    F_t,ij(z)<=F_t,ij(0)+sum_d(w_d(z)-1)m_d(mu).         (M9C2)

This argument uses the true maximum on the left, not increments of a
maximized row relaxation. For B=[0,8]×[0,5]×[0,4], put beta=Pr(Z in B)
and eta_out(d)=E[1_(Z notin B)(w_d(Z)-1)]. All eta_out(d) are evaluated
by the full geometric moments and are nonnegative. Thus

    U_t,ij=(1-beta)H_t,ij(0)
            +sum_(z in B)Pr(Z=z)H_t,ij(z)
            +sum_d eta_out(d)m_d(mu)                  (M9C3)

bounds the unconditioned hinge expectation. The last sum is exactly
2330295100792072343/3063075771441530250000; no physical height or
omitted auxiliary depth is truncated.

The same independently certified survival lower bound is
q_0=25428074957/48000000336. Since b_ij=1+I_i+I_j<=3,
g_t(b_ij)=0 for both thresholds. The signed-deletion criterion therefore
has R_E((C-g_t(b_ij))mu)=C R_E(mu) and reduces to U_t,ij<=C q_0.
There is no additional deleted-energy rebate here. Dividing(M9C3) by
q_0 and maximizing over all ten pairs gives(M9C1); both maxima occur
at(i,j)=(2,8). Empty original roots are dominated by nonempty roots
pointwise, as in(M9-6).

#### One actual two-prime consumer

Apply the existing[SH25 consumer](#a-same-law-two-prime-consumer) with
T_11=4,T_13=5 to(M9C1), using the valid chords
H_3<=(H_2+H_4)/2 and H_5<=(H_4+H_6)/2. The auxiliary11 multiplier has
Pr(N=1)=28/33, Pr(N=2)=50/363 and E N=7/6. Its entire N>=3 tail is
retained: for integers L>=1,

    (2L-5)_+=(L-2)_++(L-3)_+,
    (NL-5)_+<=N(L-2)_++2N-5  for N>=3.                (M9C4)

The second inequality includes L=1; no unsupported replacement by a
mean is made. Let h_2=3 and let h_4,h_6 be the rational upper bounds
in(M9C1), with h_3=(h_2+h_4)/2 and h_5=(h_4+h_6)/2.
With the actual physical charges of(AP2), the full
arbitrary-height transfers(AP3)--(AP5), and one final conditioning(AP6),

    b_11<=B_11:=h_4/6,
    b_13<=B_13:=[131h_2/726+50h_3/363+28h_5/33+2/121]/7,
    q_13>=1-B_11-B_13
        =6058911665321144261668772/12369607020968200661109375,
    Gamma_13<=1+[(1403/630)G-1]/q_13
        <=83065286271124677944190495859/545302049878902983550189480
        <152329/1000.                                 (M9C5)

The survival lower bound exceeds0.489822. The11/13 physical exponents
are the full exponents in the original family's period, including
moduli assigned to future primes; all residues and finite heights at
these two primes are permitted. The output is one supported head
probability for the specified low geometry.

#### Why the resulting square bound does not restart scalar T6 at17

The existing[joint-load transfer(T6)](../../../Problems/erdos-7-odd-covering-systems.md#arbitrary-head-transfer-by-the-joint-load-invariant)
is a useful explicit boundary for this output. Write its scalar input
after13 as f. At17,

    R_17(f,delta)=
      f delta(1-delta+25/128)/(delta(1-delta)-f/1024).   (M9C6)

Every denominator must be positive. The following19 step requires
R_17(f,delta)<324, because4delta_19(1-delta_19)18²<=324.
For f<256 this would require

    (324-f)delta(1-delta)-(25/128)f delta-324f/1024>0.

Its maximum even over all real delta is positive only if

    P(f)=(44145/16384)f²-(9477/8)f+104976>0.           (M9C7)

The smaller root r of P lies strictly between123.058769468748 and
123.058769468749. Exact signs at these rational endpoints, the negative
derivative there, and P(256)<0 show that this two-step scalar certificate
requires f<r. For f>=256 the17 denominator already fails.

The particular upper seed in(M9C5) exceeds r by more than29.270176093753.
Its P value is strictly negative. A second exact quadratic check with
324 replaced by500 shows that every admissible17 output from this
supplied scalar seed exceeds500, above the19 necessary limit324.
Thus changing only the two scalar delta choices cannot repair this
continuation. This conclusion concerns the stated upper-seed recurrence;
it is not a lower bound on the actual best head moment or an obstruction
to retaining a richer convex profile, coupling later blocks, or another
head probability.

`verify_original9_convex_transfer.py` binds the canonical original9/H2
and mod3 probability certificates by hash. It recomputes all5400 hinge
observations, the complete first-moment geometric remainder, the independent
survival bound, the fixed two-prime consumer, and the exact scalar
boundary. Eight direct complete-layout pair checks independently
verify its nonlinear singleton maxima. All comparisons are rational
or range-guarded integers. The adjacent
`original9_convex_transfer_certificate.json` retains the exact data;
replay it from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/verify_original9_convex_transfer.py

These are ordinary all-height arguments with exact arithmetic certificates,
not Lean kernel results or an unrestricted prime continuation for#7.

### PG1 joint final-root floor and whole-cost transfer through 11/13

The fixed PG1 law now satisfies

\[
 \Gamma_{13}\le
 \frac{15072118232557475077441399589}
      {101205875626103459954531250}
 <148.926
\]

for the same thresholds \(T_{11}=4,T_{13}=5\), arbitrary finite original
\(3,5,7\) heights and arbitrary finite \(11,13\) heights.  The low probability
\(\mu\), its uniform higher357 lift \(\lambda\), the actual higher357
survival event \(F\), and \(\nu=\lambda(\cdot\mid F)\) are unchanged.
`verify_pg1_joint_tail.py` recomputes the rational certificate
`pg1_joint_tail_certificate.json`; its inputs are the hash-bound canonical
mod3, original9 and convex-transfer certificates.  This is a supported
square bound for the stated PG1 family, not a resolution of the general
odd-covering problem.  It remains above the existing square-only 17/19
necessary threshold \(123.058769468749\).

The direct whole-cost comparison on exactly these inputs gives
\(\Gamma_{13}<150.396\).  Keeping the final test's original3/original9 floor
in the deleted energy and keeping the common source-survival denominator
through the final inequality gives the stated stronger bound.

Write \(Q=\lambda(F)\), where the independent source certificate supplies

\[
 Q\ge q_0=\frac{25428074957}{48000000336}>0.
\]

Let \(e_{ij}\) be the original9 certificate's square criterion excess for
fixed original roots \((i,j)\), at reference square 33, and let
\(e_*=\max_{i,j}e_{ij}\).  The signed criterion retains the actual common
\(Q\):

\[
 G_{ij}(Q)\le33+\frac{e_{ij}}Q,\qquad
 G(Q)\le33+\frac{e_*}Q.
\]

These inequalities are used jointly; a negative excess is not divided by
\(q_0\) and then asserted to be a separate unconditional upper bound.

For the final test's original roots \((i,j)\), put

\[
 b_{ij}(x)=1+\mathbf1_{x\equiv i\pmod3}
             +\mathbf1_{x\equiv j\pmod9},\qquad
 W_{ij}(x)=149-b_{ij}(x)^2.
\]

Thus \(0\le W_{ij}\le148\).  These original head summands remain present in
the final full test load \(Y\), so \(Y\ge b_{ij}\) throughout the physical
11/13 extension.  The zero auxiliary tail tuple is always active and
carries these same fixed roots.  Jensen's square comparison therefore
retains its contribution separately:

\[
 J_{ij}(Q)\le M G_{ij}(Q)+(P-M)G(Q),\qquad
 M=\frac43,\quad P=\frac{1403}{630}.
\]

Here \(M\) and \(P\) are the first and second auxiliary multiplier moments
from the fixed two-prime schedule.  The other active head tests use the
common square bound; their total coefficient is \(P-M\).

Let \(E\) be the final good event and let \(r\) be its probability under the
physical extension starting from \(\nu\).  Subtracting the deleted energy
and using \(Y\ge b_{ij}\) gives

\[
 r\bigl(\mathbb E[Y^2\mid E]-149\bigr)
 \le J_{ij}(Q)-149+
       \int W_{ij}\,\mathbf1_{B_{11}\cup B_{13}}.
\]

The existing independent 11/13 survival certificate ensures \(r>0\).
The original-label comparison applies after multiplication by
\(W_{ij}(x)\), because this factor depends only on the old head and is
unchanged by the fresh-prime kernels.  \(W_{ij}\nu\) is only a finite
measure used in this inequality: it is not renormalized, and neither the
physical kernels nor \(\nu\) are replaced.

For each weighted measure, retain the charge test's original roots
independently of \((i,j)\).  Define its uniform observations

\[
 H_t^W=\sup_L\mathbb E_\nu W(L-t)_+,\qquad
 G_n^W=\sup_L\mathbb E_\nu W(nL-5)_+,\qquad
 m_W=\mathbb E_\nu W.
\]

The charge at 11 is at most \(H_4^W/6\).  At 13 the auxiliary multiplier
\(N=1+K_{11}\) has

\[
 \Pr(N=1)=\frac{28}{33},\qquad
 \Pr(N=n)=\frac{50}{3\,11^n}\ (n\ge2),\qquad
 \mathbb EN=\frac76.
\]

For integer \(L\ge1\) and \(n\ge3\),
\((nL-5)_+\le n(L-2)_++2n-5\).  The complete \(N\ge3\) tail consequently
has mean \(31/726\), mass \(5/363\), and mass coefficient \(2/121\).
No multiplier tail is omitted:

\[
 \operatorname{charge}_{13}^W\le\frac17
 \left(\frac{28}{33}G_1^W+\frac{50}{363}G_2^W
       +\frac{31}{726}H_2^W+\frac{2}{121}m_W\right).
\]

The row oracle computes \(H_4^W,G_1^W,G_2^W\) directly.  It fixes the
charge original9 class in the A layout before averaging auxiliary
heights, while the B layout's cofactor9 remains unrestricted.  For
\((nL-5)_+\), the singleton increment is multiplied by \(n\), as are the
remaining load coefficients.  The depth box \((8,5,4)\) is supplemented
by the complete first-moment geometric remainder; its contribution to
\(G_n^W\) is \(n\) times the weighted first-moment remainder.  Exhaustive
full-layout comparisons independently check selected maxima without
singleton elimination.

The signed weighted hinge uses the existing higher357 deletion bound
\(R_{F^c}\).  For a charge pair \((a,c)\), its original baseline gives
\((b_{ac}-2)_+=\mathbf1_{a\bmod3}\mathbf1_{c\bmod9}\).  Taking
\(D=3\cdot148\), the measure

\[
 \bigl[D-W\mathbf1_{a\bmod3}\mathbf1_{c\bmod9}\bigr]\mu
\]

is nonnegative.  If \(U_2^W\) is the corresponding unconditional hinge
bound, then

\[
 QH_2^W\le DQ+e_W,\qquad
 e_W=\max_{a,c}\left[
 U_{2,a,c}^W+
 R_{F^c}\bigl((D-W\mathbf1_{a\bmod3}\mathbf1_{c\bmod9})\mu\bigr)-D
 \right].
\]

The ordinary source hinge has a strictly negative maximal excess
\(e_H\), so \(QH_2\le3Q+e_H\).  The weighted calculation can therefore
use \(\widehat e_W=\min(e_W,148e_H)\).  Its mass also retains a signed
source observation:

\[
 \delta_{ij}=\max\left(0,
   \mathbb E_\mu(b_{ij}^2-1)-
   R_{F^c}((b_{ij}^2-1)\mu)\right),\qquad
 Qm_W\le148Q-\delta_{ij}.
\]

Denote the unconditional selected bounds for the remaining three costs
by \(U_4,U_1,U_2\), respectively.  Multiplying the final criterion by the
same \(Q\), substituting the preceding observations, and dividing only
at the end yields

\[
 J_{ij}-149+\operatorname{charge}_{11}^W+
 \operatorname{charge}_{13}^W
 \le A+\frac{B_{ij}}Q,
\]

where

\[
 A=33P-149+\frac{148}{7}
     \left(3\frac{31}{726}+\frac{2}{121}\right)
   =-\frac{1840997}{25410},
\]

\[
 B_{ij}=(P-M)e_*+Me_{ij}+\frac{U_4}{6}
  +\frac17\left(\frac{28}{33}U_1+\frac{50}{363}U_2
    +\frac{31}{726}\widehat e_W-\frac{2}{121}\delta_{ij}\right).
\]

Every selected \(B_{ij}\) is positive.  Thus the common-denominator
criterion is maximized at \(Q=q_0\); no optimization over an unknown
conditional law is needed.  Seven final-root pairs already satisfy the
criterion using the uniform weight bound \(W\le148\).  The three weighted
pairs are \((1,1),(2,2),(2,8)\), each retaining all ten independent charge
root pairs.  The largest final excess occurs at \((2,2)\) and equals

\[
 \varepsilon=-\frac{7557235731940455783756661}
                    {101205875626103459954531250}<0.
\]

Consequently \(r(\mathbb E[Y^2\mid E]-149)\le\varepsilon\).  Since
\(0<r\le1\), the negative excess gives
\(\mathbb E[Y^2\mid E]\le149+\varepsilon\), proving the displayed
supported square bound.

### A shared-row probability crosses a uniform-profile separation

The uniform row-profile criterion does not cover every actual carrier in
the old45 shape `root1_same_other_column`, even after taking the convex
hull of all profiles that pass that criterion. This boundary is crossed
by changing the probability on the same carrier.

Consider the original low family

    (3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
    (21,5),(35,18),(63,38),(105,2),(315,92).

Its77 survivors have nonempty deletion masks
`(1,2081,9225,41604,93629)` on digits1 through5; digit6 is untouched.
In the old-point order

    X=(2,7,8,11,14,17,19,23,26,28,29,32,34,38,41,43,44),

the deletion profile is

    b=(4,0,2,2,1,2,0,2,1,1,2,2,0,3,1,1,1).

The mixed original labels at21,35,63,105,315 delete respectively
12,5,4,3,1 points, the largest possible old-cylinder sizes in this
geometry. Distinct digits make these25 deletions disjoint. No actual
carrier in this old shape can have fewer than102−25=77 points, so this
carrier is inclusion-minimal.

#### An affine separation for the uniform sufficient criterion

For the uniform probability on these77 points, the existing pure7 moment
upper bound with its full geometric remainder and the UP-1 deletion bound
give

    q=1021/1848>0,
    U_2=91023462067327/4332064275000,
    R_2=13477/924,
    35−U_2−R_2=−2586526548577/4332064275000<0.           (RW1)

The first originalmod3 root passes, with margin
2097148836808489/1061355747375000. Equation(RW1) is failure of this
specified sufficient upper-bound test; it is not a lower bound on the
actual conditional moment and does not refute Gamma≤35 for this carrier.

Write r=6−b. For the uniform profile functions from the preceding box
argument, define

    F_2(r)=P_2(r)+V(r,h_2)/48+Σ_d ρ_d C_d(r,h_2)−35Σ_x r_x.

Each maximum has a fixed choice attaining it at the displayed r. Keep
one such original-root2 A/B layout at every auxiliary depth, together
with the maximizing old group cylinders and residual-cap cylinders.
Their affine evaluations sum to a support function ell(r)=a·r+c with

    ell(r')≤F_2(r') for every admissible row profile r',
    ell(r)=F_2(r)=2586526548577/56260575000>0.           (RW2)

The certificate retains all exact rational coefficients of ell, an
equivalent primitive integer coefficient vector, and the hashes of the
active moment layouts. Every profile passing the unchanged sufficient
criterion has ell≤0, and so does every convex combination of such
profiles. Equation(RW2) excludes this actual minimal profile from that
entire convex hull. The conclusion concerns the uniform criterion on
this fixed old geometry.

The three uniform grouped costs attain their UP-1 bounds, with
48·77 times G equal to1405,45822,45922 for1,h_1,h_2. All three extra
old5 maximizers have residue4. Digit1 misses only x=2, outside that
cylinder, and digit6 is untouched. Put the extra35 class at residue29
on digit1 and every E7 class on digit6. The retained actual-cylinder
witnesses verify equality point by point. Thus the discarded
extra35/E7 overlap term itself cannot remove the deficit in(RW1).

#### A positive row law satisfying both signed criteria

Assign every surviving point in old row x the mass f_x/D, where, in the
displayed order X,

    f=(85000015,85000015,92897922,114999985,85000015,
       114999985,113531563,85000015,88133380,114999985,
       85000015,114999985,113531563,102747938,95423755,
       114999985,85000015),
    D=Σ_x(6−b_x)f_x=7699999993.

All masses are positive and satisfy

    17/(20·77) ≤ f_x/D ≤ 23/(20·77).

Thus this is a full-support law on the same77-point carrier, constant
within each surviving old row. The globally untouched digit gives the
weighted pure7 observation

    D H_i(z)=max_(A with originalmod3 root i,B)
               Σ_x f_x[(6−b_x)A_x²+2uA_xB_x+u²B_x²],
    u=1+z7.                                           (RW3)

All coefficients used to select that digit are nonnegative. The ordinary
and signed caps and UP-1 costs are evaluated with these same point masses.
The auxiliary box remains[0,8]×[0,5]×[0,4], and the complete nonnegative
geometric remainder is retained. Original modulus labels and actual
higher forbidden classes remain unchanged.

For the independent uniform lift lambda of this low law and its actual
higher survivor event F, the exact survival certificate is

    lambda(F)≥q=14536679681/26399999976>0.               (RW4)

The two root results are

| Originalmod3 root | U_i | R_i for h_i mu | 35−U_i−R_i |
| --- | --- | --- | --- |
| 1 | 10321649656260777208162/530677873205065569375 | 338173190555/23099999979 | 483200161247896160588/530677873205065569375 |
| 2 | 262061474318903335813313/13266946830126639234375 | 2713457477845/184799999832 | 59842230563635719352871/106135574641013113875000 |

Both margins are positive, respectively greater than0.910533 and0.563828.
As before, the unit class and the same originalmod3 test imply
L²≥1+3·1_(root i). With h_i=34−3·1_(root i), without renormalizing h_i mu,

    ∫_F(L²−35)d lambda
       ≤U_i−35+∫_(Fᶜ)h_i d lambda
       ≤U_i−35+R_i<0.

Equation(RW4) therefore gives Gamma(lambda(.|F))≤35 for every finite
original3/5/7 height and every higher forbidden family above this low
carrier. An empty originalmod3 root is dominated pointwise by a nonempty
root. This supplies a new law; it makes no assertion that the uniform
law's actual optimal moment exceeds35.

#### Original-label support transport and replay

The six old-map images of this source form one minimal orbit. Exact
deletion-mask matching transports its law to3715 actual states in531
carrier orbits. Pulling each higher forbidden family back through the
same allowed coordinate map preserves the original modulus labels and
the all-height estimate. Extra low points in a containing carrier
receive zero mass.

Of these orbits,16 lie in the existing uniform-box region. The new source
therefore adds3668 states and515 orbits, including one additional minimal
orbit. The union for this old shape has5007 states and1077 orbits. With
the384 certified orbits in the other two old shapes, the total is1461
carrier orbits and11 inclusion-minimal orbits at Gamma≤35. Of the56966
minimal orbits,56955 remain outside the certified sources; the general
prime-tail continuation remains unresolved.

`verify_row_weighted_geometry.py` and
`row_weighted_geometry_certificate.json` reconstruct the actual family,
both uniform and weighted270-depth calculations, the complete tails,
the affine separation, the original-cylinder equality witnesses and
all transport counts. The verifier uses range-guarded integer arithmetic
and exact rational comparison; it has no optimization dependency.
Replay from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/verify_row_weighted_geometry.py

These are finite arithmetic certificates and ordinary all-height proofs,
not Lean kernel results or a bound on all remaining low profiles.

### PG1 signed original-root floor for the second whole cost

On the unchanged PG1 law and fixed 11/13 schedule, the supported square
bound improves to

\[
 \Gamma_{13}\le
 \frac{165486462221025969000254660209}
      {1113264631887138059499843750}
 <148.650.
\]

`verify_pg1_signed_g2.py` checks `pg1_signed_g2_certificate.json` by
hash-bound consumption of `pg1_joint_tail_certificate.json` and its three
canonical inputs. The source geometry remains the result of
`verify_pg1_joint_tail.py`. The extension recomputes 40 signed deletion
observations, reuses 40 already certified hinge-deletion observations,
and evaluates the complete common-denominator criteria. The preceding
148.926 bound remains a separately verified comparison. The probability,
physical kernels, thresholds and all-height scope are unchanged.

For a charge test with original roots \((a,c)\), write
\(b_{ac}=1+\mathbf1_{a\bmod3}+\mathbf1_{c\bmod9}\) and
\(g_{ac}=\mathbf1_{a\bmod3}\mathbf1_{c\bmod9}\). Its whole cost and hinge
have the same original-root floor:

\[
 (2b_{ac}-5)_+=(b_{ac}-2)_+=g_{ac}.
\]

Fix the final-root weight \(W=149-b_{ij}^2\le148\). For either
\(D=148\) or \(D=444\), the measure \((D-Wg_{ac})\mu\) is nonnegative.
Using the source geometry's unconditional bound \(U_{2,a,c}\) for
\(W(2L-5)_+\), subtraction on the same higher357 deletion event gives

\[
 QG_2^W\le DQ+e_{2,ij}^{(D)},\qquad
 e_{2,ij}^{(D)}=\max_{a,c}\left[
 U_{2,a,c}+R_{F^c}((D-Wg_{ac})\mu)-D\right].
\]

For \(D=148\), the verifier recomputes the displayed deletion bounds.
For \(D=444\), the parent hinge certificate already records, at each
individual charge pair,

\[
 e_{H,a,c}=U_{H,a,c}+R_{F^c}((444-Wg_{ac})\mu)-444.
\]

Consequently it gives the exact reusable expression

\[
 e_{2,ij}^{(444)}
   =\max_{a,c}(U_{2,a,c}-U_{H,a,c}+e_{H,a,c}).
\]

The subtraction is performed separately at every charge pair before the
maximum; a difference of separate maxima is not used. For branches
using \(W\le148\), the ordinary formulas at targets1 and3 are multiplied
by148. Original charge roots remain independent of the final test roots.
Every deletion bound retains its complete higher357 remainder.

The prior complete criterion \(A+B_{ij}/Q\) remains available. Each
signed choice supplies a second complete inequality, valid for every
\(Q\in[q_0,1]\):

\[
 A_D+\frac{B_{D,ij}}Q,\qquad
 A_D=A+\frac{50D}{2541},\qquad
 B_{D,ij}=B_{ij}+\frac{50}{2541}(e_{2,ij}^{(D)}-U_2).
\]

All three inverse-\(Q\) coefficients are positive in every final-root
branch. Each entire criterion is maximized at \(q_0\), and the verifier
selects the smallest of these global bounds. This keeps one common
source probability throughout the inequality.

The largest selected excess occurs at final roots \((2,5)\):

\[
 \varepsilon_*=-\frac{389967930157601865222058541}
                     {1113264631887138059499843750}<0.
\]

The independently positive final retained mass \(r\le1\) gives
\(\Gamma_{13}\le149+\varepsilon_*\). This still exceeds the existing
square-only 17/19 necessary threshold; the general odd-covering problem
remains open. Replay from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/verify_pg1_signed_g2.py

### Complete original low-test anchoring at arbitrary prime-power heights

Retaining one complete original low test gives an all-height square
estimate in terms of its weighted cylinder caps.  Its PG1 specialization
below certifies the aligned2 test branch at \(\Gamma_{13}<146.919\).
The uniform PG1 bound over all low tests remains \(\Gamma_{13}<148.650\).

Let \(M_0=\prod_{p\in\mathcal P}p^{h_p}\), where \(\mathcal P\) is a finite
set of primes and \(h_p\ge1\).  Let \(\mu\) be any probability on a subset
of \(\mathbb Z/M_0\mathbb Z\), and let \(\lambda\) be its uniform independent
lift in the additional digits to any finite heights \(H_p\ge h_p\).
Fix one original low class \(C_d\) for every \(d\mid M_0\), including the
unit class, and put

\[
 B=\sum_{d\mid M_0}\mathbf1_{C_d},\qquad
 m_d(\sigma)=\max_{a\bmod d}\sigma(a\bmod d).
\]

Every complete fine test extending those classes has \(L=B+R\), where
\(R\) contains precisely its higher original modulus labels.  Set

\[
 S(d)=\{p:v_p(d)=h_p\},\quad
 a_d=\prod_{p\in S(d)}\frac p{p-1},\quad \gamma_d=a_d-1,
\]

\[
 b_{de}=\prod_{p\in S(d)\cap S(e)}\frac{p(p+1)}{(p-1)^2}
         \prod_{p\in S(d)\triangle S(e)}\frac p{p-1},\qquad
 \kappa_{de}=b_{de}-a_d-a_e+1.
\]

Then, uniformly over all those finite heights and higher test residues,

\[
 \mathbb E_\lambda L^2\le
 U(B):=\mathbb E_\mu B^2+
       2\sum_{d\mid M_0}\gamma_d m_d(B\mu)+
       \sum_{d,e\mid M_0}\kappa_{de}m_{\operatorname{lcm}(d,e)}(\mu).
 \tag{AF1}
\]

For proof, a higher label has the unique form
\(m=d\prod_p p^{t_p}\), with \(d=\gcd(m,M_0)\), \(t\ne0\), and
\(\operatorname{supp}(t)\subseteq S(d)\).  Its cross term with \(B\) is
at most \(\prod_p p^{-t_p}m_d(B\mu)\).  Two higher labels have either
empty intersection or a low cylinder modulo \(\operatorname{lcm}(d,e)\),
and their extra-digit intersection probability is at most
\(\prod_p p^{-\max(t_p,s_p)}\).  The sum over one nonzero exponent vector
is \(\gamma_d\).  Including both zero vectors and then removing their
two faces gives the double coefficient \(\kappa_{de}\), using

\[
 \sum_{r,s\ge0}p^{-\max(r,s)}=\frac{p(p+1)}{(p-1)^2}.
\]

All summands are nonnegative, so replacing finite exponent ranges by
these infinite sums is an upper bound.  Expanding \((B+R)^2\) proves
(AF1).  Original labels with equal low projection remain distinct.

This uses the moment framework of BBMST,
[arXiv:1811.03547, Theorem 3.2](https://arxiv.org/abs/1811.03547), and the
repository's saturated-label calculations (SH1)–(SH3), (SH8).  The
retained observation here is \(m_d(B\mu)\), with one fixed complete
\(B\), in place of separate low-cylinder intersection maxima.

#### The same complete floor inside and outside a finite depth box

Let the auxiliary variables be independent with
\(\Pr(Z_p=k)=(p-1)/p^{k+1}\), and set

\[
 w_d(z)=\prod_{p\in S(d)}(1+z_p),\qquad r_d(z)=w_d(z)-1,
\]

\[
 S_B(z)=\max_{(D_d)}\int
      \left(B+\sum_{d\mid M_0}r_d(z)\mathbf1_{D_d}\right)^2d\mu.
\]

Only the higher projected cylinders \(D_d\) vary.  Centering the
additional prefixes bounds their intersection probabilities as above.
At each auxiliary depth, average the active higher labels within each
projection and apply convexity only to that average, leaving \(B\)
fixed.  This gives

\[
 \mathbb E_\lambda L^2\le\mathbb E_Z S_B(Z). \tag{AF2}
\]

This is the full-low-label extension of the original9 separation in
(M9-2)–(M9-5).  The maximizing \(D_d\)'s may depend on \(z\); the upper
bound does not assert that one actual higher family attains all of them.
In particular, replacing the expression by
\(\sum_d w_d(z)\mathbf1_{C_d}\) with freely changing original \(C_d\)'s
would lose the fixed original test needed in the deleted energy.

For any finite depth box \(\mathcal B\), define

\[
 \epsilon=\Pr(Z\notin\mathcal B),\quad
 A_d=\mathbb E[\mathbf1_{Z\notin\mathcal B}r_d(Z)],\quad
 K_{de}=\mathbb E[\mathbf1_{Z\notin\mathcal B}r_d(Z)r_e(Z)].
\]

Expanding the square for the same \(B\) outside the box yields

\[
 \mathbb E_\lambda L^2\le
 \sum_{z\in\mathcal B}\Pr(Z=z)S_B(z)+\epsilon\mathbb E_\mu B^2
 +2\sum_d A_d m_d(B\mu)
 +\sum_{d,e}K_{de}m_{\operatorname{lcm}(d,e)}(\mu). \tag{AF3}
\]

Every tail coefficient is a nonnegative rational remainder of complete
geometric moments.  This formula still requires certified bounds for
its inside-box maxima.  The coefficient calculation alone does not
certify those maxima or optimize over all original low tests.

The same fixed test can also weight future charge observations.  Put
\(W_B=(C-B^2)_+\).  For an increasing convex \(\ell\)-Lipschitz cost
\(g\), with charge cylinders independent of the final test, define

\[
 H_{B,g}(z)=\max_{(D_d)}\int W_B\,
   g\left(\sum_d w_d(z)\mathbf1_{D_d}\right)d\mu.
\]

The usual auxiliary comparison applies after multiplication by the
nonnegative old-point weight \(W_B\).  Comparing a fixed charge layout
to its zero-depth load gives

\[
 H_{B,g}(z)\le H_{B,g}(0)+\ell\sum_d r_d(z)m_d(W_B\mu).
\]

Thus its complete outside contribution is bounded by
\(\epsilon H_{B,g}(0)+\ell\sum_d A_d m_d(W_B\mu)\).  The charge layout
remains independent of the fixed final \(B\); \(W_B\mu\) is not
renormalized.  These observations are under \(\lambda\), and the actual
higher-deletion transfer is still required before using them under
\(\nu=\lambda(\cdot\mid F)\).

#### A concrete aligned2 consumer on the same PG1 law

Take \(M_0=315\), \(h=(2,1,1)\), and the unchanged canonical PG1
probability on its75 actual points.  For all twelve original low labels,
fix \(C_d=2\bmod d\).  The exact calculation gives

\[
 \mathbb E_\mu B^2=\frac{10606504844}{1000000007},\quad
 2\sum_d\gamma_dm_d(B\mu)=\frac{4754413927}{1000000007},
\]

\[
 \sum_{d,e}\kappa_{de}m_{\operatorname{lcm}(d,e)}(\mu)
   =\frac{74198115637}{24000000168},\qquad
 U(B)=\frac{442860166141}{24000000168}.
\]

The saved cross-term amount relative to independent intersection caps
is \(3949851830/3000000021\).  For every nonnegative low function \(f\),
the original higher-label union bound gives

\[
 \int_{F^c}f\,d\lambda\le\mathcal R(f\mu)
       :=\sum_d\gamma_dm_d(f\mu).
\]

Because \(L\ge B\), a head reference \(K\) satisfies

\[
 Q(\mathbb E_\nu L^2-K)
 \le U(B)+\mathcal R((K-B^2)_+\mu)-K,
 \qquad Q=\lambda(F).
 \tag{AF4}
\]

At \(K=29\), the positive part is necessary since \(B\) can equal12.
The exact deletion upper bound is \(37233260707/3000000021\), giving

\[
 e_B=\frac{14908748975}{8000000056},\qquad
 G_B(Q)\le29+\frac{e_B}{Q}.
\]

The existing source survival lower bound
\(q_0=25428074957/48000000336\) therefore gives
\(G_B\le826866667603/25428074957<32.517864\).

For the 11/13 consumer, the zero-tail tuple carries this complete
original \(B\).  Keep the existing unrestricted square bound for the
other tuples.  With \(M=4/3\) and \(P=1403/630\), its preconditioning
square bound is \(M G_B+(P-M)G\).  Using only the independent final
survival certificate gives \(\Gamma_{13,B}<149.020\).

The stronger current signed-charge criterion uses the same actual
source \(Q\).  In its final-root \((2,2)\) branch, replace only the
zero-tail contribution:

\[
 A_{\rm new}=A_{\rm old}+\frac43(29-33),\qquad
 B_{\rm new}=B_{\rm old}+\frac43(e_B-e_{22}),
\]

where \(e_{22}\) is the original9 square excess at reference33.  This
retains the already certified charge bounds and physical kernels.  The
resulting whole criterion is \(A_{\rm new}+B_{\rm new}/Q\), with

\[
 A_{\rm new}=-\frac{584839}{8470},\qquad
 B_{\rm new}=\frac{9318930413060408641498726373}
                   {262685549314111332327187500}>0.
\]

Its maximum is at \(q_0\) and is negative.  Applying the existing
positive final surviving mass gives the concrete consumer

\[
 \Gamma_{13,B}\le
 \frac{163558856448790578417793670359}
      {1113264631887138059499843750}<146.919. \tag{AF5}
\]

This fixes all twelve original low classes, not just roots \((2,2)\).
All higher original test residues and all finite physical heights
remain unrestricted.  Equation(AF5) does not replace the uniform
\(\Gamma_{13}<148.650\) bound over arbitrary low tests.

#### Boundary of the inexpensive relaxation and replay

The ordinary union-bound version of(AF4) does not uniformly dominate
the existing global head square bound.  The genuine low test
\(C_d=68\bmod d\), evaluated at reference33, gives

\[
 U(B)=\frac{463549739429}{24000000168},\qquad
 \mathcal R((33-B^2)_+\mu)=\frac{340267738535}{24000000168}.
\]

The resulting value of the explicit upper-bound functional is
\(862761418421/25428074957>33.929\), above the existing head bound
\(33.73365775325071\).  This is a boundary fixture for that inexpensive
relaxation, not a lower bound on the actual test moment.  A global
improvement must control the combined objective for every independent
low-test layout, or use a stronger observation.

`verify_pg1_anchored_square.py` and
`pg1_anchored_square_certificate.json` recompute these exact observations,
both consumers, the boundary fixture, and all first/second outside-box
coefficients for \((8,5,4)\).  Direct depth summation is checked against
factored one-prime moments.  The aligned2 outside square contribution
in(AF3) is \(26237873570245030831/918922731432459075000\); its inside
maxima are not evaluated by this certificate.  Existing survival and
charge inputs are separately verified hash-bound prerequisites.

These are ordinary general inequalities and exact rational consumers;
no new Lean declaration or general odd-covering resolution is claimed.
Replay from the repository root:

    python3 -I -O docs/reports/erdos7-odd-covering/verify_pg1_anchored_square.py

### Exact signed digit optimization with the old load fixed

`ExactSignedDigitDP` optimizes the six original labels
`7,21,35,63,105,315` independently. Its input is the old support `X`, one
fixed load `A[x]`, and exact integer or rational tables `scores[y][i][k]`.
The returned maximum is over every original residue of those six labels.
`labels` gives a realizing residue modulo each original modulus; the
program recomputes its score directly. All seven digits participate,
and one representative of every distinct old cylinder, including an
empty cylinder when realizable, is retained.

For example, after importing the adjacent module:

```python
oracle = ExactSignedDigitDP(old_points)
result = oracle.optimize(old_loads, scores)
maximum = result['value']
original_residues = result['labels']
```

Each table row is indexed by the total load, including the old load;
provide entries from zero through `A[i]+6`. Zero tables represent absent
points. The constructor's old-cylinder states can be reused for multiple
queries. The production dependency is Python's standard library only.

For digit `y` and label subset `S`, the program computes exactly

\[
g_y(S)=\max_{(b_c)_{c\in S}}
 \sum_{x\in X}\phi_{xy}\left(A_x+
       \sum_{c\in S}1_{x\equiv b_c\pmod c}\right).
\]

Every original label belongs to precisely one digit block. Conditional
on this partition, different blocks have disjoint labels and physical
point sets, so their old-residue choices are independent. Conversely,
CRT realizes every block choice separately for each original modulus.
Thus `D[0]=0`, unreachable entries are `None`, and the recurrence
`new[S]=max(old[S xor T]+g_y[T] for T subset S)` gives exactly the
maximum. The nonzero baseline `g_y[empty]` is included once for each
digit. This is a finite optimization argument and an exact arithmetic
implementation; no Lean formalization is claimed.

The old-modulus label is a singleton on the old support. After fixing
the other old residues, its additional score is the largest pointwise
increment. Zero is also a candidate exactly when an empty old cylinder
exists. In particular, a full old carrier cannot replace a negative
singleton increment by zero. On PG1 the cylinder counts are
`1,3,5,6,8,17`; eliminating that singleton leaves 3024 old states across
all subset masks. Seven stages use 5103 subset transitions. The full
old-test search has 12240 mask combinations and 11808 distinct load
vectors; only this count, not an optimization over all those vectors,
is included here.

The existing `verify_point_geometry.FixedADP` supports the nonnegative
square bound. It adds independently maximized unary and pair terms to
form each block, with old-residue compatibility relaxed, and processes
digits 1 through 6. Its `point_fixedA_dp_exact.py` replay certifies those
integer upper-bound calculations, not the exact signed block problem.
The new program reuses the subset-partition structure while computing
each block by compatible old-residue enumeration.

After placing the files beside the canonical PG1 source, replay the
deterministic certificate with:

```text
python3 -I -O verify_exact_signed_digit_dp.py
```

The verifier reads the adjacent
`mod3_conditioned_geometry_certificate.json`, selects PG1, and binds
that source file's SHA-256. `--source PATH` selects another location
for the same canonical source. `--write` generates
`exact_signed_digit_dp_certificate.json`; the default operation compares
the complete exact recomputation with the stored certificate and does
not write. The certificate contains no timing fields. Twelve seeded
rational, signed, nonconvex fixtures agree with brute-force enumeration
of the original modulus residues. Other checks cover the nonzero
empty-block baseline, absent digit zero, empty singleton gain zero, and
the unavoidable gain −1 on a full old carrier.

On the actual PG1 law, fix each old residue to 2 modulo its cofactor.
At actual points 1 and 46, set the score to
`-mu(t)*(B(t)-A(t mod45)-1)^2`, and zero elsewhere. Both points have
weight numerator 14690784 and common denominator 1000000007. The
unrestricted optimum is 0; a common-digit restriction gives exactly
`-14690784/1000000007`. A realizing independent choice uses residues
4 modulo7 and 1 modulo21, with the other four labels at digit zero.
This gives a strict counterexample on the original carrier and law.

The concrete joint fixture is

\[
 E_\mu[\tfrac43(B+R)^2+\tfrac16(149-B^2)(L-4)_+].
\]

At depth `(1,1,1)`, `R` uses each higher-label multiplicity `w_d-1`
and `L` uses each full multiplicity `w_d`. Their fixed auxiliary
comparison residues are given in the certificate. These are independent
of the fixed original low classes defining `B`. Three points have negative
quadratic coefficient. With the old load fixed as above, the exact
optimum is `223040367109/3000000021`. The common-digit restriction gives
`223011181693/3000000021`, so independent digits improve the objective
by `9728472/1000000007`. A maximizing witness assigns digits5 to the
first five labels and digit4 to the old45 label, with original
residues `(5,5,12,5,47,32)` modulo `(7,21,35,63,105,315)`. The checker
replays those residues on all 75 actual points. This is a one-depth,
fixed-auxiliary instance with coefficients `4/3`, `1/6` and threshold4;
it is not a final continuation or all-height bound.

For the whole original315 floor objective, collect the moment and
weighted-charge terms into one point score table before this query.
This implementation then exactly eliminates the six original7 label
choices for one fixed old load and one fixed auxiliary profile. A
global certificate still needs every old load and a complete bound
over the auxiliary moment/charge profiles, including the omitted
depth tail. At each fixed collection of auxiliary depths, finite maxima over old
loads, auxiliary profiles, and final residues commute. This does not
interchange a maximum with an expectation over depths, and sampled
auxiliary profiles supply no upper bound for the complete maximum. No global-floor improvement follows
from the two fixtures above.

### Exact optimization of arbitrary point scores over all twelve low labels

Fix the 75-point PG1 carrier and its original probability law from
`mod3_conditioned_geometry_certificate.json`. Its projection modulo 45 has
16 points. Put

\[
\mathcal C=\{1,3,5,9,15,45\},\qquad
\mathcal D=\mathcal C\cup7\mathcal C.
\]

For each \(d\in\mathcal D\), independently choose an original residue
\(a_d\bmod d\), and let

\[
B(x)=\sum_{d\in\mathcal D}\mathbf1_{x\equiv a_d\pmod d}.
\]

The \(d=1\) label is the constant low-test term; it is not a proposed
admissible modulus in an odd covering. For any supplied integer tables
\(s_x(k)\), \(x\) in the PG1 carrier and \(0\le k\le12\), the new oracle
computes exactly

\[
\max_{(a_d)_{d\in\mathcal D}}\sum_x s_x(B(x)).
\tag{AL1}
\]

Scores may have either sign and arbitrary curvature. Empty residue classes
and all seven digits, including zero, remain legal. This quantifies over all
twelve low-test labels for the supplied score table. It does not quantify
over an external family of auxiliary profiles or arbitrary physical heights;
those obligations remain with the caller.

Write \(x_i\) for the 16 old points. The old load is
\(A_i=\sum_{c\in\mathcal C}\mathbf1_{x_i\equiv a_c\pmod c}\).
Keeping one original residue for each distinct old-cylinder mask gives
\(1,3,5,6,8,17\) choices for the six cofactors, including empty masks.
The 12,240 combinations yield exactly 11,808 distinct realizable vectors
\(A\); one actual residue witness is retained for each vector.

For fixed \(A\), each label \(7c\) independently chooses a digit
\(y\bmod7\) and an old residue modulo \(c\). Coprimality makes these
choices equivalent to one original residue modulo \(7c\). For a subset
\(S\subseteq\mathcal C\), define

\[
H_y(S;A)=
\max_{(b_c)_{c\in S}}
\sum_i s_{y,i}\left(A_i+
  \sum_{c\in S}\mathbf1_{x_i\equiv b_c\pmod c}\right),
\tag{AL2}
\]

where absent physical points have identically zero tables. For subsets not
containing 45, the implementation enumerates all 3,024 old-residue states
across the 32 subsets. Adding label 45 either hits one old point or a legal
empty class. At a given state with loads \(k_i\), its exact best increment is

\[
\max\left(0,\max_i[s_{y,i}(k_i+1)-s_{y,i}(k_i)]\right).
\tag{AL3}
\]

The zero option is justified by an actual empty modulo-45 class on PG1.
It is not a monotonicity assumption.

Partition the six labels among the seven digits using

\[
V_0(\varnothing)=0,\qquad
V_{y+1}(S)=\max_{T\subseteq S}
  \bigl[V_y(S\setminus T)+H_y(T;A)\bigr],
\tag{AL4}
\]

with other initial states unreachable. The empty block
\(H_y(\varnothing;A)\) retains its actual score, which need not be zero.
Every original residue assignment induces exactly such a partition and
old-residue choices, and every choice in this recurrence lifts by CRT to
original residues. Thus \(V_7(\mathcal C)\) is the exact fixed-\(A\)
maximum. Maximizing it over all 11,808 realizable \(A\) proves (AL1).

`pg1_signed_score_oracle.py` accepts either `point_scores[75][13]`, in the
source PG1 point order, or `scores[7][16][13]`, in digit then old-point
order. The optional positive integer `denominator` gives the common score
denominator. It returns the exact maximum, twelve original residue labels,
and all 75 maximizing loads. The original Python signed optimizer checks
the maximizing old load, and a separate literal twelve-label evaluation
checks the reported score. The C++ executable is compiled temporarily from
the adjacent source, or supplied with `--binary`; raw inputs and complete
value tables are temporary. The driver checks

\[
4\sum_{y,i}\max_k|s_{y,i}(k)|<2^{61},
\]

which bounds all signed 64-bit score, difference, and recurrence
intermediates. The C++ raw-input format is an internal contract of this
guarded driver.

For the existing actual-coefficient fixture at depth \((1,1,1)\), retain
exactly the moment and charge auxiliary residues in
`exact_signed_digit_dp_certificate.json`. Reconstruct its objective as

\[
\mathbb E_\mu\left[
  \frac43(B+R)^2+\frac16(149-B^2)(L-4)_+
\right].
\tag{AL5}
\]

Here \(\mu\) is the same PG1 law with denominator \(N=1000000007\).
The integer score table is
\(w_x[8(k+R(x))^2+(149-k^2)(L(x)-4)_+]\), with denominator \(6N\).
Three actual points have negative quadratic coefficient. The exact
all-low-label maximum is

\[
\frac{80520608091}{1000000007}
=80.52060752735575\ldots .
\tag{AL6}
\]

One maximizing witness has residues
\((0,2,3,5,8,23)\) at moduli \((1,3,5,9,15,45)\), and
\((5,5,33,5,68,68)\) at moduli \((7,21,35,63,105,315)\).
The latter six all have digit 5. The maximum after restricting them to a
common digit, while still maximizing over every old \(A\), equals (AL6).
Thus the global independent-versus-common-digit gap for this particular
fixed auxiliary profile is zero.

The earlier fixed-\(A\) counterexample is unchanged: at old residues
\((0,2,2,2,2,2)\), the independent and common-digit maxima remain
\(223040367109/(3N)\) and \(223011181693/(3N)\), respectively, with
strict gap \(9728472/N>0\). Equality of the two maxima after optimizing
over all old loads does not imply equality at each old load, or validate a
common-digit restriction for other score tables.

`verify_pg1_all_low_scores.py` reconstructs (AL5) from the original
auxiliary residues and source weights, runs the complete optimization,
and compares 32 spread old loads, including the earlier fixed load, against
the original Python optimizer. It compares the deterministic
`pg1_all_low_scores_certificate.json` by default; only `--write` rewrites
the certificate. This is an exact finite optimization program and
certificate, not a Lean formalization or a solution of unrestricted #7.

### A reference-optimal boundary for the old PG1 anchored functional

Keep the actual PG1 low probability \(\mu\), its higher357 lift, the
original modulus labels and the actual survival event \(F\) unchanged.
Write \(Q=\Pr(F)\). The existing independent survival certificate gives

\[
 q_0=\frac{25428074957}{48000000336}\le Q\le1.
\]

For every \(d\mid315\), select the genuine original low class
\(47\pmod d\), including the constant class at \(d=1\), and let
\(B=\sum_{d\mid315}\mathbf1_{47\bmod d}\). The all-height AF1 estimate is

\[
 U(B)=\mathbb E_\mu B^2+
  2\sum_{d\mid315}\gamma_d m_d(B\mu)+K_{\rm high}
  =\frac{156034880279}{8000000056},
 \qquad K_{\rm high}=\frac{74198115637}{24000000168}.
\]

Here, with \(S(d)=\{p:v_p(d)=h_p\}\) and \(h=(2,1,1)\),

\[
 a_d=\prod_{p\in S(d)}\frac p{p-1},\quad \gamma_d=a_d-1,
 \quad
 b_{de}=\prod_{p\in S(d)\cap S(e)}\frac{p(p+1)}{(p-1)^2}
          \prod_{p\in S(d)\triangle S(e)}\frac p{p-1},
\]

and \(K_{\rm high}=\sum_{d,e}(b_{de}-a_d-a_e+1)
m_{\operatorname{lcm}(d,e)}(\mu)\). These are complete geometric moments,
with no finite-height cutoff.

Let \(R_{\rm old}\) be the existing grouped-deletion operator, including
its complete nonnegative remainder. Explicitly its groups are
\((9,45)\), \((5,15,45)\), the extra class at \(35\), and
\((7,21,35,63,105,315)\); its remaining cylinder coefficients are

\[
 \rho_d=\gamma_d-\frac12\mathbf1_{d\in\{9,45\}}
  -\frac14\mathbf1_{d\in\{5,15,45,35\}}
  -\frac16\mathbf1_{7\mid d}\ge0.
\]

The exact mass calculation is

\[
 R_{\rm old}(\mu)=\frac{22571925379}{48000000336}=1-q_0.
\]

For every real reference \(K\), define

\[
 e(K)=U(B)+R_{\rm old}\bigl((K-B^2)_+\mu\bigr)-K,
 \qquad H(K)=\max_{q_0\le Q\le1}\left(K+\frac{e(K)}Q\right).
\]

Then the exact result is

\[
 \boxed{\min_{K\in\mathbb R}H(K)
       =\frac{853585952201}{26129684197}
       =32.66728927014747\ldots.}                                      \tag{RB1}
\]

This is a boundary for **fixed AF1, fixed \(R_{\rm old}\), and the
independent interval \([q_0,1]\)**. It is not a lower bound for a true
moment or an upper bound over all low tests. It does not apply to a new
deletion operator, a larger certified survival, a stronger AF1 bound,
or a whole-cost criterion coupling other costs to the same \(Q\).
In particular it leaves open an improvement of the current uniform
head bound \(33.73365775325071\ldots\) to a value above (RB1).

For completeness, monotonicity, subadditivity and positive homogeneity
of \(R_{\rm old}\) give, whenever \(K_2-K_1=\Delta>0\),

\[
 -\Delta\le e(K_2)-e(K_1)\le-q_0\Delta.                              \tag{RB2}
\]

Indeed the difference of the positive-part inputs lies pointwise between
zero and \(\Delta\), and \(R_{\rm old}(\Delta\mu)=\Delta(1-q_0)\).
Thus \(e\) is continuous, strictly decreasing, and tends to opposite
infinities at the ends of the real line. It has a unique zero \(K_*\).
For \(e(K)\ge0\), \(H(K)=K+e(K)/q_0\) is nonincreasing by (RB2).
For \(e(K)\le0\), \(H(K)=K+e(K)=U(B)+R_{\rm old}((K-B^2)_+\mu)\)
is nondecreasing. Therefore the global minimum is \(H(K_*)=K_*\).
The negative excess retains the actual common denominator; it is not
independently divided by \(q_0\).

On \([32,33]\) the positive-part support is fixed to \(B\le5\).
Every feasible combined deletion witness is consequently affine in \(K\).
The exact endpoint oracles and one feasible original-residue witness give

\[
 R_{\rm old}((K-B^2)_+\mu)=\alpha K-\beta\quad(32\le K\le33),
 \quad\alpha=\frac{21870316139}{48000000336},\quad
 \beta=\frac{82623329473}{48000000336}.                              \tag{RB3}
\]

To see why the interior equality follows, the maximum of the witness
lines is convex and lies above this feasible line. Equality at both
endpoints forces equality throughout the interval by convexity. The
endpoint signed excesses are

\[
 e(32)=\frac{5812019299}{16000000112}>0,\qquad
 e(33)=-\frac{2173406575}{12000000084}<0.
\]

The unique zero is therefore in this interval, and (RB3) gives
\(K_*=(U(B)-\beta)/(1-\alpha)\), proving (RB1).

`verify_pg1_anchored_reference_boundary.py` reconstructs the law, AF1
coefficients, complete deletion remainder, exact endpoint maxima and
the realizing group and cylinder residues. It binds both canonical
PG1 and original9 source certificates by SHA256. It reuses the existing
`group_setup` and `group_oracle`; no depth-box square maxima are rerun.
The certificate contains rational results and witnesses, with no timing
or exploratory-search data. The default operation compares the entire
recomputation; `--write` explicitly regenerates it:

```text
python3 -I -O verify_pg1_anchored_reference_boundary.py
```

This is an ordinary proof with an exact arithmetic verifier; no new Lean
formalization is claimed.

### Probability-capped deletion and a joint observation beyond this boundary

On a finite support, the old operator has the form
\(R(v)=\max_{g\in\mathcal G}v\cdot g\) for nonnegative finite-measure
vectors \(v\), where \(\mathcal G\) is finite, nonempty and nonnegative.
Define

\[
 R_{\rm cap}(v)=\min_{0\le\sigma\le v}
       [\mathbf1\cdot(v-\sigma)+R(\sigma)].                           \tag{RC1}
\]

Using \(v=\mu f\) and \(\sigma=\mu h\) handles zero masses without any
division: conversely set \(h_x=\sigma_x/\mu_x\) only when \(\mu_x>0\),
and set \(h_x=0\) otherwise. If \(\theta\) is the actual conditional
deletion vector, \(0\le\theta\le1\) and \(\theta\cdot\sigma\le R(\sigma)\)
give \(\theta\cdot v\le R_{\rm cap}(v)\). The actual event is unchanged.

Finite LP duality gives

\[
 R_{\rm cap}(v)=\max_{r\in P}v\cdot r,\qquad
 P=\{r:0\le r\le1,\ \exists\bar g\in\operatorname{conv}\mathcal G,
       \ r\le\bar g\}.                                               \tag{RC2}
\]

In detail, use primal variables \(t,\sigma\ge0\), constraints
\(\sigma\le v\), \(g\cdot\sigma\le t\), and objective
\(\mathbf1\cdot v-\mathbf1\cdot\sigma+t\). Its dual has multipliers
\(\lambda_g,y_x\ge0\), \(\sum_g\lambda_g\le1\),
\(y_x+\sum_g\lambda_g g_x\ge1\). Both programs are feasible.
Minimizing \(y_x\) and filling any missing nonnegative \(\lambda\) mass
gives \(\max_{\bar g\in\operatorname{conv}\mathcal G}
\sum_x v_x\min(1,\bar g_x)\), equivalent to (RC2).
The downward closure in \(P\) is necessary; \(\operatorname{conv}
\mathcal G\cap[0,1]^X\) alone can be empty. The existing formal
prerequisite is `FiniteStrongDuality.ValidELP.strong_duality_of_both_feasible`
in `D5/S3/Analytic/Convexity/FiniteStrongDuality.lean`.

The capped operator is monotone and sublinear. For nonnegative costs
\(Z_j\ge b_j(x)\), coefficients \(a_j\ge0\), a common event \(F\), and
\(\mathbb E\sum_j a_jZ_j\le U\), put \(b=\sum_j a_jb_j\). Then

\[
 Q\left(\mathbb E\left[\sum_j a_jZ_j\mid F\right]-K\right)
 \le U-K+R_{\rm cap}((K-b)_+\mu).                                    \tag{RC3}
\]

If \(K=\sum_j a_jK_j\), the last deletion term is at most
\(\sum_j a_jR_{\rm cap}((K_j-b_j)_+\mu)\). Taking the positive part
after summing can exploit cancellation, and one maximizing deletion
vector can replace several independent maximizers. This proves a
comparison of bounds, not a strict PG1 improvement.

Since \(P\) is downward closed, its support function at a signed vector
equals its support function at that vector's positive part. If
\(q_{\rm cap}=1-R_{\rm cap}(\mu)>0\), the unique zero of
\(U-K+R_{\rm cap}((K-b)_+\mu)\) is therefore exactly

\[
 \max_{r\in P}
 \frac{U-\sum_x\mu_xb_xr_x}{1-\sum_x\mu_xr_x}.                       \tag{RC4}
\]

All denominators are at least \(q_{\rm cap}\); the same vector \(r\)
appears in the numerator and the survival probability. The maximization
is an upper relaxation, not an assertion of physical attainability.

For the AF1 head objective alone, fixing cross-cap witnesses produces
a nonnegative linear coefficient \(a_x\). Its capped point score obeys

\[
 k^2+a_xk+r_x(K-k^2)_+
 =\max\{k^2+a_xk,(1-r_x)k^2+a_xk+r_xK\},                             \tag{RC5}
\]

which is increasing and convex for \(k\ge0\), \(0\le r_x\le1\).
This permits removal of empty original classes from that head-only
maximization. It does not establish common-digit alignment or convexity
of a full joint charge objective containing additional negative
quadratic terms.

### An auxiliary majorant covering every original low test

Another sufficient global bound retains the old operator. Express
\(U(B)+R_{\rm old}((K-B^2)_+\mu)\) as

\[
 K_{\rm high}+\max_{z_j\in Z_j}\sum_x
       [\mu_xB_x^2+\sum_j c_{j,x}(B_x)z_{j,x}],                        \tag{MX1}
\]

where cross-cap terms have \(c_{j,x}(k)=2\gamma_d\mu_xk\), remainder
caps have \(c_{j,x}(k)=\rho_d\mu_x(K-k^2)_+\), and the grouped term
has \(c_{j,x}(k)=\mu_x(K-k^2)_+\). Each \(Z_j\) is its complete cylinder
or grouped-witness family. These auxiliary maxima are independent in
the old upper functional; no joint physical realization is assumed.

Each separate witness satisfies \(0\le z_{j,x}\le1\). For the grouped
term, writing \(A\in\{0,1,2\}\), \(B_5\in\{0,1,2,3\}\),
\(E\in\{0,1\}\), \(S\in\{0,\ldots,6\}\), and \(b=B_5+E\), its
numerator is

\[
 24A+(2-A)[6b+(4-b)S]\le24A+24(2-A)=48.
\]

The complete old vector after adding remainders need not be bounded by
one and must remain separated into these auxiliary terms.
Choose nonnegative vectors \(q_j=(q_{j,x})_x\), fixed throughout the
maximization over \(B\), and put \(h_j(q)=\max_{z\in Z_j}q\cdot z\).
The pointwise inequality \(cz\le(c-q)_++qz\) yields

\[
 \max_B[U(B)+R_{\rm old}((K-B^2)_+\mu)]\le V(K;q),
\]
\[
 V(K;q)=K_{\rm high}+\max_B\sum_x
 [\mu_xB_x^2+\sum_j(c_{j,x}(B_x)-q_{j,x})_+]+\sum_jh_j(q_j).           \tag{MX2}
\]

The middle term can be evaluated by the exact independent-digit and
all-old-layout optimizer; every \(h_j\) needs its complete cap or group
oracle. Sampled witnesses give no upper certificate for \(h_j\).
For the actual same survival \(Q\), the resulting uniform head bound is

\[
 \Gamma\le
 \begin{cases}
 K+(V-K)/q_0,&V\ge K,\\
 V,&V\le K.
 \end{cases}                                                         \tag{MX3}
\]

In particular, \(V(T;q)\le T\) suffices for \(\Gamma\le T\).
Neither (RC1)--(RC5) nor (MX1)--(MX3) asserts that a concrete all-low-test
threshold has been met; each specifies an observation beyond the fixed
functional whose limitation is certified by (RB1).

### A finite dual obstruction to the reference33 price family

For every nonnegative price vector in (MX2), at the fixed reference
\(K=33\), the unchanged PG1 law satisfies

\[
 V(33;q)\ge
 \frac{824892275704058867603}{24000000168000000000}
 >34.3705112470.                                                     \tag{MX4}
\]

Improving the existing uniform head bound \(G\) at this reference
would require

\[
 V(33;q)<33+q_0(G-33)
 =\frac{460223929211132040332029}{13783840971486886125000}
 <33.388656338.                                                       \tag{MX5}
\]

Thus this entire price family cannot improve that head bound at
reference33. This is a limitation of the upper-envelope family, not
a lower bound for an actual moment. Another reference, a different
majorant, and costs combined on one actual event remain outside it.

Here is the finite certificate argument. Prices can be restricted to
\(0\le q_{j,x}\le\max_{1\le k\le12}c_{j,x}(k)\): reducing a price
above that endpoint leaves its positive part zero and cannot increase
the nonnegative support function. Retain 34 actual twelve-label tests
in the maximum over \(B\), 60 actual group profiles in its support
function, and all original residues in every other cylinder support.
Restricting either maximum decreases (MX2), giving a lower relaxation
of its best achievable value.

The epigraph formulation of this relaxation has 15617 variables and
15677 inequalities. Positive-part variables are bounded by their
coefficient maxima, cylinder and group epigraphs by the supports of
those maxima, and the test epigraph by
\(144+\sum_{j,x}\max_k c_{j,x}(k)\). After normalization all variables
lie in \([0,1]\); these bounds preserve the minimum. For the negated
objective \(c^Tx\), integer constraints \(Ax\le b\), and any
nonnegative rational multiplier vector \(z\),

\[
 c^Tx\le b^Tz+\sum_j\max\{c_j-(A^Tz)_j,0\}
 \qquad(0\le x_j\le1).                                               \tag{MX6}
\]

The retained dual has 1536 nonzero entries. Exact evaluation of every
residual in (MX6), followed by negation and restoration of
\(K_{\rm high}\), gives (MX4). This argument requires the retained
profiles to be feasible; their completeness is unnecessary for a
lower relaxation. In contrast, evaluating an upper certificate in
(MX2) requires complete maximization.

`verify_pg1_maxplus_obstruction.py` reconstructs every test load and
group profile as original congruence classes on the 75 actual points,
the complete geometric coefficients, the epigraph matrix, and the
integer dual calculation. Its adjacent certificate binds both source
files by SHA256. The replay uses only the Python standard library,
with no numerical optimizer or floating-point premise:

```text
python3 -I -O verify_pg1_maxplus_obstruction.py
```

This is an ordinary finite dual argument with exact arithmetic evidence,
not a new Lean theorem or an improved uniform PG1 constant.

### Transfer of the PG1 law after a bounded loss of low mass

The all-height moment bound \(35\) now covers \(1,172\) carrier orbits
on the PG1 old45 shape, including \(53\) inclusion-minimal orbits.
The former support-containment transfer covered \(232\) orbits and one
minimal orbit. The increase follows from restricting the existing PG1
probability to another actual carrier while controlling the discarded
probability mass.

Let \(A\) be the fixed PG1 low carrier, \(\mu\) its certified law,
and \(\lambda\) its uniform lift to arbitrary finite physical 3/5/7
heights. For an arbitrary higher forbidden family with distinct original
moduli, let \(F\) be its actual survivor event. The source certificate
gives, simultaneously for every original-label test load \(L\),

\[
 Q=\lambda(F)\ge q_0=\frac{25428074957}{48000000336}>0,
 \qquad \mathbb E_\lambda[L^2\mid F]\le
 G=\frac{492647095380812739054683}{14604022456869186140625}.
\]

For another actual low carrier \(B\), write \(t=\mu(A\setminus B)<q_0\).
More generally, any same-law observation \(\mathbb E_\lambda[Z\mid F]\le C\)
with a pointwise floor \(Z\ge c\) transfers on this one target law as
\[
 \mathbb E_\lambda[Z\mid F\cap B]
 \le c+(C-c)\frac{q_0}{q_0-t}.                                     \tag{WL0}
\]
The proof below uses \(Z=L^2,c=1\); replacing \(L^2-1\) by \(Z-c\)
proves (WL0). The coordinate map and target law are chosen once per
carrier, independently of the test and of which observation is consumed.

The unit test class gives \(L\ge1\). Use the target's higher
forbidden family in the source theorem, so the higher event \(F\) is
unchanged. With \(s=\lambda(F\cap B^c)\le t\),

\[
 \mathbb E_\lambda[(L^2-1)\mathbf1_{F\cap B}]
 \le \mathbb E_\lambda[(L^2-1)\mathbf1_F]\le(G-1)Q.
\]

Since \(Q-s\ge q_0-t>0\), this proves

\[
 \mathbb E_\lambda[L^2\mid F\cap B]
 \le1+(G-1)\frac{Q}{Q-s}
 \le1+(G-1)\frac{q_0}{q_0-t}.                                      \tag{WL1}
\]

The target low law is \(\mu(\cdot\mid B)\); its uniform high lift,
conditioned on \(F\), is exactly \(\lambda(\cdot\mid F\cap B)\).
Under that normalized lift the survival lower bound is

\[
 q_{\rm target}\ge\frac{q_0-t}{1-t}>0.                              \tag{WL2}
\]

This normalization is separate from the actual \(Q\) and \(s\) used in
(WL1). The source and target low forbidden lists are not combined into
a new distinct-modulus family; the restricted measure is simply
supported on the target's allowed low points.

In particular the source bounds \(\mathbb E L\le5\) and
\(\mathbb E(L-2)_+\le3\) from the same original9 certificate become
\(\mathbb E L\le1+4q_0/(q_0-t)\) and
\(\mathbb E(L-2)_+\le3q_0/(q_0-t)\). Any existing source bounds
\(H_4\le C_4\), \(H_6\le C_6\) likewise transfer to
\(H_4\le C_4q_0/(q_0-t)\), \(H_6\le C_6q_0/(q_0-t)\), using floor
zero. These observations and the square bound hold on the same target
law and remain available to a subsequent 11/13 argument.

For target moment \(35\), (WL1) requires only

\[
 t\le t_{35}:=\frac{q_0(35-G)}{34}
  =\frac{2311711326201096983399}{117162648257638532062500}
  =0.019730787589554016\ldots.                                     \tag{WL3}
\]

With source denominator \(N=1000000007\), this is equivalent to an
integer discarded numerator at most \(19730787\). All \(75\) single
points and \(251\) of the \(2775\) unordered pairs meet the threshold.
Three points can meet it, but no four points can; the unrestricted
weighted matching below includes the three-point possibility.

The permitted old-coordinate maps preserve the old45 support and
permute mod9 children within their mod3 roots and mod5 columns. They
extend to full mod9/mod5 permutations by filling the missing children
and columns. A single common permutation of the six nonzero mod7
digits fixes digit zero. For each prime with baseline height \(h_0\),
extend the low permutation by
\(a+p^{h_0}z\mapsto\pi(a)+p^{h_0}z\). This preserves every lower
prefix and leaves higher digits unchanged. CRT therefore maps every
original cylinder to a cylinder of the **same original modulus**, at
every finite height, and preserves uniform high fibers. Pulling back
the target's higher family and tests makes (WL1)--(WL2) valid after
every permitted coordinate map. Row-dependent mod7 permutations are
not used.

For exact computation, write \(w_{s,i}\) for the PG1 weight numerator
at seven digit \(s\) and old row \(i\), with zero for absent points.
Let \(M_1,\ldots,M_6\) be the target's deletion masks, padded with
empty masks. For an allowed old map \(p\), the assignment cost is

\[
 C_p(s,j)=\sum_iw_{s,i}\mathbf1_{p(i)\in M_j}.
\]

The minimum discarded numerator is exactly
\(\min_p\min_{\pi\in S_6}\sum_sC_p(s,\pi(s))\). The verifier
evaluates all \(12\) old maps and all \(720\) digit permutations using
integers, then replays every chosen minimum on the \(75\) original
source points. The old-map group and the complete digit permutations
make eligibility invariant across each target orbit, justifying the
state counts from orbit sizes.

The complete domain is \(153,997\) actual mask states in \(34,160\)
orbits. It contains \(102,083\) essential states in \(21,524\) orbits
and \(10,554\) inclusion-minimal orbits. The essential and minimal
domains are independently reconstructed and checked against the
existing classification hashes. The resulting counts are:

| Admitted source loss | Actual states | Carrier orbits | Essential orbits | Minimal orbits |
|---|---:|---:|---:|---:|
| Zero | 1,648 | 232 | 1 | 1 |
| At most one point | 6,871 | 1,146 | 70 | 50 |
| At most two points, subject to (WL3) | 7,073 | 1,172 | 73 | 53 |
| Full weighted threshold (WL3) | 7,073 | 1,172 | 73 | 53 |

Thus the full weighted search adds \(5,425\) actual states, \(940\)
carrier orbits and \(52\) minimal orbits. The equality of the last two
rows is a computed result, not an assumption excluding three-point loss.

One newly covered minimal carrier has canonical deletion masks
\((1,2320,8456,25352,44378)\). Its certificate gives all eleven original
low modulus/residue pairs, reconstructs their actual complement, and
gives an allowed coordinate map under which only source point \(271\)
is lost. Its exact estimates are

\[
 t=\frac{14288471}{1000000007},\qquad
 \Gamma\le
 \frac{492253195359590634804683}{14210122435647081890625}
 <34.642<35.
\]

For the combined count, the existing C2 law covers \(152\) orbits and
one minimal orbit on `root2_other_same_column`. On
`root1_same_other_column`, the uniform box and row-weighted law cover
\(562+531-16=1077\) orbits and \(8+1=9\) minimal orbits; their overlap
is subtracted using their existing certificate. These two shapes and
the PG1 shape are distinct. Thus the combined target35 count increases
from \(1461\) to \(2401\) carrier orbits and from \(11\) to \(63\)
minimal orbits. Of the \(56966\) minimal orbits in the six-shape
classification, \(56903\) remain outside these certified domains.
These are conditional higher357 results; they do not complete the
unrestricted-prime continuation or settle the general odd-covering problem.

`verify_pg1_weighted_carrier_transfer.py` binds the six canonical source
certificates by SHA256, rebuilds the entire matching domain, and compares
the summary, witnesses and domain hashes with
`pg1_weighted_carrier_transfer_certificate.json`. It retains no duplicate
table of all \(34,160\) orbit calculations. Existing moment certificates
on the other two shapes are inherited, not rerun as new moment bounds.
No optimizer or network is needed. The default operation only compares;
`--write` explicitly regenerates the certificate:

```text
python3 -I -O verify_pg1_weighted_carrier_transfer.py
```

The conditioning and lifting arguments are ordinary all-height proofs
with an exact finite matching verifier. No new Lean finite-instance
endpoint is claimed.

Within the larger family of all \(2!3!4!=288\) normalized old-coordinate
maps, dropping the source-stabilizer restriction cannot extend this
particular transfer to another old shape. These maps fix the mod3 roots,
missing mod9 child4 and mod5 column0. The source mass on old rows mapped
outside the target old support is lost before any mod7 choice. Exact
enumeration gives the following minimum lost numerators, all with
denominator \(1000000007\):

| Target old shape | Minimum lost numerator |
|---|---:|
| `root1_same_other_column` | 120057768 |
| `root1_other_same_column` | 145937820 |
| `root1_other_other_column` | 87566988 |
| `root2_same_other_column` | 32378894 |
| `root2_other_same_column` | 83395212 |

Every value exceeds the permitted \(19730787\), independently of
subsequent mod7 permutations or mixed-label choices. On the source
shape exactly its twelve stabilizers pass this necessary old-row test.
The same verifier reconstructs all \(6\times288\) old-row losses and
checks each against the original 75-point calculation. This boundary
concerns the fixed PG1 probability, bound35 and specified normalized
map family; other probabilities and transfer constructions remain open.

### Exact zero-depth geometry strengthens the same PG1 law

Keeping one realizable layout for all twelve original low labels gives
the all-height bounds

\[
 G_{\rm new}=
 \frac{491665320264992331169931}{14604022456869186140625}
 <33.666432,\qquad
 \Gamma_{13}\le
 \frac{165356424839074723126151405953}
      {1113264631887138059499843750}<148.532901.                 \tag{ZD1}
\]

These use the same PG1 low probability, its uniform higher357 lift,
the target's actual higher357 survival event, and the same subsequent
11/13 kernels. All finite physical exponents and complete auxiliary tails
remain included. The mean and hinge estimates on this law still apply.
The improvement does not settle the other low geometries or the
unrestricted prime continuation.

For the original roots \((i,j)\), let \(H_{ij}(z)\) be the previously
certified minimum of the pure7 and fixed-A square relaxations. At
\(z=(0,0,0)\), there are no higher auxiliary labels. The all-low-label
integer oracle therefore computes the exact value

\[
 h_{ij}=\max_{\substack{\text{all twelve original low classes}\\
                         C_3=i,\ C_9=j}}
             \mathbb E_\mu B^2.                              \tag{ZD2}
\]

All 11808 distinct old loads are evaluated. The restriction to each
root pair is reconstructed from every original old-cylinder choice
before deduplication, so a load with several original-label realizations
retains every admissible root pair. The six seven-divisible labels keep
their independent digits, including digit zero and empty cylinders.
Each of the ten maximizing witnesses is independently evaluated by the
Python subset recurrence and by its literal twelve congruences on all
75 points. All ten values improve their previous relaxations. For the
source's worst pair \((2,2)\),

\[
 H_{22}(0)=\frac{11408985958}{1000000007},\qquad
 h_{22}=\frac{11331111635}{1000000007}.                         \tag{ZD3}
\]

At this depth each root's unrestricted digit optimum equals its common
digit optimum. Thus this particular gain comes from retaining the
realizable old-cylinder geometry, without requiring a strict gap between
those two digit maxima. Other signed costs have the distinct behavior
documented above.

The complete outside-box estimate (M9-5) remains valid with its exact
zero-depth term: for each actual layout its nonnegative square increment
is bounded by the same pair-cap polynomial increment, after which its
zero-depth square is at most \(h_{ij}\). For
\(\mathcal B=[0,8]\times[0,5]\times[0,4]\), write

\[
 p_0=\Pr(Z=0)=\frac{16}{35},\qquad
 \beta=\Pr(Z\in\mathcal B)
  =(1-3^{-9})(1-5^{-6})(1-7^{-5}).
\]

Replacing only that depth and the outside-box anchor therefore gives

\[
 U'_{ij}=U_{ij}-(p_0+1-\beta)(H_{ij}(0)-h_{ij}).               \tag{ZD4}
\]

The other 269 depth bounds and every outside increment coefficient are
unchanged. With the original deletion functional and reference33, put
\(e'_{ij}=U'_{ij}+R((33-b_{ij}^2)\mu)-33\). The common positive survival
bound is still \(q_0=25428074957/48000000336\). Applying (M9-6) gives
\(G_{\rm new}=33+\max(0,\max e'_{ij})/q_0\), the first value in (ZD1).
The maximum remains at \((2,2)\).

For the signed 11/13 consumer, let \(e_*\) and \(e'_*\) denote the old
and new root maxima. In each of its three complete criterion candidates,
replace the inverse-\(Q\) coefficient \(B_{ij}\) by

\[
 B'_{ij}=B_{ij}-(P-M)(e_*-e'_*)-M(e_{ij}-e'_{ij}),\qquad
 M=\frac43,\quad P=\frac{1403}{630}.                          \tag{ZD5}
\]

Every resulting coefficient remains positive. Consequently each complete
criterion is still largest at \(Q=q_0\); its constant and all charge
observations remain unchanged. Selecting complete candidates and then
maximizing over all final roots gives the second value in (ZD1), now
with worst roots \((2,5)\). Positive final survival is supplied by the
same independent bound as before. This remains above the square-only
17/19 seed threshold; it is an improved upper bound, not a lower bound
on the actual moment.

The bounded-loss transfer also permits the larger sufficient budget

\[
 t\le\frac{q_0(35-G_{\rm new})}{34}
  =\frac{143201953863449880529}{6891920485743443062500}
  =0.020778236510371237\ldots.                                \tag{ZD6}
\]

For the integer source weights this is a lost numerator of at most
20778236. The previously certified carrier counts remain valid; no
new complete orbit count is asserted for the larger budget.

`verify_pg1_exact_zero_depth.py` and
`pg1_exact_zero_depth_certificate.json` reconstruct (ZD2), the original
root domains, all complete geometric coefficients, (ZD4)--(ZD6), and the
prior rational criteria from hash-bound source certificates. The 269
nonzero-depth maxima and earlier charge geometry are inherited, separately
verified prerequisites. This is an ordinary all-height argument with an
exact arithmetic certificate, without a new Lean endpoint.

### Combining all original-root floors on one source event

The square and charge estimates can retain all their original-root floors
before using the higher357 deletion functional. Fix the final root pair
\(i\), put \(C=149\), \(W_i=C-b_i^2\), and write
\(g_j=(b_j-2)_+\). Because \(b_j\in\{1,2,3\}\), this also equals
\((2b_j-5)_+\), the floor for the second whole charge cost. Let

\[
 M=\frac43,\quad P=\frac{1403}{630},\quad
 c_1=\frac4{33},\quad c_2=\frac{50}{2541},\quad
 c_h=\frac{31}{5082},\quad c_0=\frac2{847}.
\]

The coefficients \(c_h,c_0\) include the complete multiplier tail from
13. Retain independent original-root pairs \(h,u,v\) for the other head
square, second whole charge and threshold-two hinge. Their joint floor is

\[
 f_{i,h,u,v}=M b_i^2+(P-M)b_h^2
                +c_2W_i g_u+c_hW_i g_v+c_0W_i.              \tag{JF1}
\]

The threshold-four and first whole costs have nonnegative floor zero;
their upper contributions remain present. Denote their existing
unconditional weighted upper bounds by \(U_{4,i}\) and \(U_{1,i}\),
and denote the second whole and hinge upper bounds by
\(U_{2,i,u}\) and \(U_{H,i,v}\). The ordinary source square bounds
\(U'_i,U'_h\) are those of (ZD4). Put

\[
 V_{i,h,u,v}=MU'_i+(P-M)U'_h+\frac{U_{4,i}}6+c_1U_{1,i}
               +c_2U_{2,i,u}+c_hU_{H,i,v}
               +c_0\mathbb E_\mu W_i.                     \tag{JF2}
\]

For each set of actual tests realizing these roots, its nonnegative
combined source cost \(Z\) satisfies \(Z\ge f_{i,h,u,v}\) and
\(\mathbb E_\lambda Z\le V_{i,h,u,v}\). These are bounds on the
same source law. No simultaneous attainment of the individual upper
bounds is assumed. Auxiliary mixtures are covered by their pure-root
vertices: their integral bound is affine, and the positive-part deletion
bound below is convex, in each such mixture. Empty original classes may
first be moved to nonempty classes at the nonnegative actual-cost level;
no monotonicity of the resulting signed criterion is assumed.

For any source reference \(K\), use the actual common event \(F\),
\(Q=\lambda(F)\), and the existing nonnegative deletion functional \(R\):

\[
 \begin{aligned}
 Q(\mathbb E_\nu Z-K)
 &=\mathbb E_\lambda Z-K
       +\mathbb E_\lambda[(K-Z)\mathbf1_{F^c}]\\
 &\le V_{i,h,u,v}-K+
       R\bigl((K-f_{i,h,u,v})_+\mu\bigr).                  \tag{JF3}
 \end{aligned}
\]

Thus all ten choices of each of \(h,u,v\) must be retained for each
of the ten final pairs. Combining their floors before the positive part
and deletion support can improve over taking separate deletion bounds.
This argument uses the published \(R\); it does not require the further
probability-capped functional \(R_{\rm cap}\).

Let \(\delta\) upper-bound the right side of (JF3) for all 10000
combinations. Since \(q_0\le Q\le1\), a valid source bound is

\[
 T=\begin{cases}K+\delta/q_0,&\delta\ge0,\\
                 K+\delta,&\delta<0.\end{cases}           \tag{JF4}
\]

The physical 11/13 estimate still uses \(C=149\), independently of
the auxiliary source reference \(K\). Its positive final survival
\(r\le1\) satisfies
\(r(\Gamma_{13}-C)\le\mathbb E_\nu Z-C\le T-C\).
When \(T<C\), this gives \(\Gamma_{13}\le T\); a negative source
excess is never divided by the smaller lower bound \(q_0\).

Keeping the separate criterion as a second bound sharpens (JF4). Put
\(E^S_j=U'_j+R((33-b_j^2)\mu)-33\), and for the final weight define

\[
 \begin{aligned}
 E^N_{i,u}&=U_{2,i,u}+R((444-W_i g_u)\mu)-444,\\
 E^H_{i,v}&=U_{H,i,v}+R((444-W_i g_v)\mu)-444,\\
 E^W_i&=\mathbb E_\mu W_i+R((b_i^2-1)\mu)-148.
 \end{aligned}
\]

All deletion inputs here are nonnegative. Applying the separate signed
inequalities on the same event gives

\[
 Q(\mathbb E_\nu Z-K)\le A Q+B_{i,h,u,v},\qquad
 A=33P+444(c_2+c_h)+148c_0-K,
\]
\[
 B_{i,h,u,v}=ME^S_i+(P-M)E^S_h+\frac{U_{4,i}}6+c_1U_{1,i}
                 +c_2E^N_{i,u}+c_hE^H_{i,v}+c_0E^W_i.       \tag{JF5}
\]

For the fixed \(K=297/2\), \(A=-803146/12705<0\). Hence
\(Aq_0+B_{i,h,u,v}\) is a rigorous upper bound on the source excess.
It also bounds the joint expression in (JF3): expand \(K-f\) as the
sum of the preceding nonnegative deletion costs and the nonnegative
constant \(-A\), and use the positive homogeneity and subadditivity
of \(R\), with \(R(\mu)=1-q_0\). In decreasing order of these separate
bounds, a combination can be skipped once its bound is no larger than
the greatest joint expression already evaluated. This covers all 10000
combinations with ten direct joint evaluations and 9990 justified skips.
Sixteen new distinct grouped-deletion evaluations suffice, with other
queries inherited from their hash-bound prior certificates.

Exact calculation with the new source squares gives

\[
 \delta=-\frac{167157392171127017840563}
                 {3898857874792004932500000},\qquad
 B_*:=\max B_{i,h,u,v}
   =\frac{35204985686553987468638773289}
          {1050742197256445329308750000}>0.
\]

Both inequalities apply for every \(Q\in[q_0,1]\). Therefore

\[
 \mathbb E_\nu Z\le
 \max_{q_0\le Q\le1}
 \left[K+\frac{\min(\delta,AQ+B_*)}{Q}\right].              \tag{JF6}
\]

The two terms inside this minimum are monotone after division by \(Q\):
\(\delta/Q\) increases because \(\delta<0\), whereas
\(A+B_*/Q\) decreases because \(B_*>0\). The maximum is consequently
found among the two endpoints and the unique crossing, if it lies in
the interval. Here the crossing

\[
 Q_* =\frac{19341582772973446474593583}
                 {36445882274521174135800000}
\]

lies in that interval and supplies the largest of the three exact
values. It follows that the same physical 11/13 law satisfies

\[
 \boxed{\displaystyle
 \Gamma_{13}\le
 \frac{3452976366440462440938598284408403}
      {23265022838471110091964891311550}
 <148.419213.}                                              \tag{JF7}
\]

`verify_pg1_common_source_floor.py` and
`pg1_common_source_floor_certificate.json` reconstruct the original
root domain, every pruning bound, the new grouped-deletion evaluations
and the three complete \(Q\) candidates. They bind the original
charge tables and the zero-depth certificate by hash; the full prior
profile geometry is a separately verified prerequisite. The remaining
arbitrary-prime continuation is open. This certificate supplies ordinary
exact arithmetic, not a new Lean theorem.

### Joint-observation guidance from the polynomial closed graphs

[RRO section43 at dev34c829dfb0](https://github.com/the-omega-institute/trureturing/blob/34c829dfb0791b4a40bbf98c232db6f2d49efba4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#43-增补乘法满闭图与有限多项式联合闭图的定向判据)
gives a concrete boundary for assembling observations. Under its stated
phase assumptions, theorem43.11 characterizes joint polynomial limits by
a common phase preimage and one error vector satisfying every required
strict sign. Theorem43.13 exhibits two full marginal nonlinear graphs
whose joint circuit still obeys the relation \(a(b+1)=ab+a\); even all
linear phase identities can leave an impossible combination of boundary
directions. The ordinary polynomial equidistribution input is Weyl's
theorem, in the scalar form stated in
[Tao's Corollary6](https://terrytao.wordpress.com/2010/03/28/254b-notes-1-equidistribution-of-polynomial-sequences-in-torii/).

For the covering problem this motivates retaining the actual joint
configuration before maximizing, as in (ZD2), and retaining one deletion
event and probability when combining costs. Separate maxima remain valid
upper bounds but need not have a simultaneous actual maximizer. The
Zeckendorf phase and directional-cone theorems do not themselves provide
a CRT survivor probability, a charge estimate, or a uniform positive
residual for arbitrary prime support. No quantitative #7 bridge or Lean
formalization of the new RRO section is claimed here.

### Exact weighted geometry at the first nonzero auxiliary depth

Keep the PG1 probability, the actual higher357 survival event \(F\), and
the original3/original9 roots from (ZD1)--(ZD4). At auxiliary depth
\(z=(1,0,0)\), retain the old load in the form

\[
 A=1+\mathbf1_{C(i,3)}+\mathbf1_{C(j,9)}
   +\mathbf1_{C_5}+\mathbf1_{C_{15}}
   +2\mathbf1_{C_{45}}+\mathbf1_{C_{\mathrm{higher}9}}.       \tag{WD1}
\]

The original mod9 residue \(j\) stays fixed. The higher9 cylinder is
independently free. The six seven-label cofactors \((1,3,5,9,15,45)\)
have weights \((1,1,1,2,1,2)\) and independent seven digits.
Equal-cofactor free cylinders can be pooled for this pure square maximum:
for \(r\ge0\), convexity gives

\[
 (H+\mathbf1_C+r\mathbf1_D)^2
 \le\frac{(H+(1+r)\mathbf1_C)^2
          +r(H+(1+r)\mathbf1_D)^2}{1+r}.                    \tag{WD2}
\]

Each term on the right is a permitted pooled choice; conversely the
pooled choice is realized by \(C=D\). Thus the maxima agree. This
argument only pools free labels. It neither identifies fixed original9
with higher9 nor applies to an arbitrary signed score.

The exact weighted optimizer checks 3972 old-load vectors for each of
the ten root pairs, hence 39720 rooted layouts. It retains all 3024
labeled subset states, empty classes and digit zero, with maximum load
15 or16 according to root compatibility. It strictly improves the
inherited depth100 square bound at every root. Let \(h^{(1)}_{ij}\) be
the new maximum and \(H_{ij}(1,0,0)\) the inherited minimum of the
pure7 and fixed-old estimates. Since this depth has probability
\(16/105\), replace

\[
 U''_{ij}=U'_{ij}-s_{ij},\qquad
 s_{ij}=\frac{16}{105}
          \bigl(H_{ij}(1,0,0)-h^{(1)}_{ij}\bigr)>0.          \tag{WD3}
\]

Keep the exact zero-depth value, the other268 inside-box observations,
the complete outside coefficients and the root-specific deletion costs.
The same actual source law consequently satisfies

\[
 \boxed{\displaystyle
 \Gamma\le
 \frac{491316187201313799169931}{14604022456869186140625}
 <33.642525.}                                               \tag{WD4}
\]

The worst roots remain \((2,2)\). This is an improvement of
\(4255298304/177996524699\) over the source bound in (ZD1).

For the common-source continuation (JF1)--(JF7), every one of the10000
root combinations decreases its unconditional source cost by at least

\[
 \eta=\frac{1403}{630}\min_{i,j}s_{ij}
      =\frac{65098504112}{11025000077175}>0.                 \tag{WD5}
\]

Subtract \(\eta\) from both \(\delta\) and \(B_*\) in (JF6).
The actual \(Q\), its interval, and the crossing are unchanged.
Checking the same two endpoints and crossing yields

\[
 \boxed{\displaystyle
 \Gamma_{13}\le
 \frac{3452717513949582813397269113208403}
      {23265022838471110091964891311550}
 <148.408087.}                                              \tag{WD6}
\]

`verify_pg1_exact_depth100.py` and
`pg1_exact_depth100_certificate.json` retain these exact comparisons.
`pg1_weighted_score_oracle.py` and its C++ implementation support signed,
nonmonotone score tables in the weighted total load. The verifier
independently reconstructs every old domain and subset load from raw
residues, checks each rooted winner by all \(7^6\) digit assignments,
and evaluates its literal75-point realization. Signed comparisons
include a case where independent digits strictly beat a common digit,
a necessary digit-zero choice, and overflow/domain rejection checks.
The common-digit maximum happens to agree for (WD1)'s square; it is
not imposed on other objectives.

The sufficient target35 mass-loss budget also increases to
\(2478074848638464468993/117162648257638532062500\), with integer
lost-weight limit21150724 at denominator1000000007. No new complete
carrier count is inferred from this enlarged scalar budget. The
arbitrary-prime continuation remains open; these are ordinary exact
certificates, with no new Lean declaration.

### Joint low and high deletion enlarges the transported support domain

Let \(\mu\) be the same PG1 low probability, \(\lambda\) its uniform
lift to arbitrary finite3/5/7 heights, and \(F\) any admissible actual
higher357 survivor event. The unchanged bound is
\(\lambda(F)\ge q_0=25428074957/48000000336\). Fix a low loss set
\(S\), put \(t=\mu(S)\), and condition on \(A=F\cap S^c\).
Then \(\rho=\lambda(A)\ge q_0-t\). For each original test root pair,
write \(b_{ij}=1+\mathbf1_{C(i,3)}+\mathbf1_{C(j,9)}\) and
\(f_{ij}=35-b_{ij}^2>0\). The complete grouped-deletion bound \(R\)
applies to any nonnegative, possibly unnormalized low weight. Using
the exact-zero-depth source bounds \(U'_{ij}\) gives

\[
 \boxed{\displaystyle
 \rho\bigl(\mathbb E[L^2\mid A]-35\bigr)
 \le U'_{ij}-35
       +\mu(f_{ij}\mathbf1_S)
       +R(f_{ij}\mu\mathbf1_{S^c}).}                        \tag{JT1}
\]

Indeed, the removed set is the disjoint union
\(S\sqcup(S^c\cap F^c)\). Subtract its actual square energy from
\(\lambda(L^2)\), bound that energy below by \(b_{ij}^2\), and apply
the weighted grouped-deletion bound only on \(S^c\). The intersection
\(S\cap F^c\) is charged once. Every term uses the same physical
law and event. All higher deletion coefficients and the full auxiliary
square tail remain present. Empty test-root branches are dominated by
the same nonempty-root extensions as in the source estimate.

Four fixed low losses pass (JT1) strictly at every one of the ten roots:

| Lost source points \(S\) | Lost weight numerator | Retained support | Maximum right side of (JT1) |
| --- | ---: | ---: | ---: |
| \(88,208,313\) | 24940311 | 72 | \(<-0.21149\) |
| \(43,88,253\) | 25521977 | 72 | \(<-0.19666\) |
| \(2,128\) | 25865521 | 73 | \(<-0.19738\) |
| \(38,143\) | 26142429 | 73 | \(<-0.14937\) |

The weight denominator is1000000007. All four lost-weight numerators
exceed both scalar limits20778236 and21150724, while each lost mass
\(t\) is below \(q_0\). Therefore each
conditioned law has positive survival and \(\Gamma\le35\).
One original target family is
\((3,0),(5,0),(7,0),(9,4),(15,11),(21,5),(35,18),(45,37),
(63,50),(105,94),(315,79)\); its low carrier has76 points and contains
the mapped72-point support. The certificate specifies all four actual
families, their full coordinate maps, and exact rational criteria.

More generally, let \(T\) be a permitted CRT coordinate permutation
and let a target carrier contain \(T(\operatorname{supp}\mu\setminus S)\).
Transport \(\mu|_{S^c}/(1-t)\) to that carrier. The low maps preserve
the mod3 parent of each mod9 child. Extending them by leaving subsequent
prime-adic digits unchanged preserves every original residue class at
every height. Thus any target high event pulls back to an admissible
source \(F\), with target high survival at least
\((q_0-t)/(1-t)>0\), and (JT1) still applies. The target need only
contain the retained support, not the entire initial target carrier.
Source and target forbidden families are never merged.

The four supports have48 distinct old-coordinate images. Reconstructing
all34160 same-shape target orbits and checking inclusion gives701 orbits,
21 inclusion-minimal orbits, and4892 normalized digit-union states.
For these701 targets, exact matching over12 old maps and720 seven-digit
permutations determines their overlap with the previously published
scalar threshold19730787. The disjoint addition is242 orbits,9 minimal
orbits, and1782 states. Thus the PG1-shape union is1414 orbits,62 minimal
orbits, and8855 states. Including the unchanged other-shape results, the
combined supported \(\Gamma\le35\) region is

\[
 \boxed{2643\text{ carrier orbits},\quad
        72\text{ minimal orbits},\quad
        16153\text{ normalized states}.}                  \tag{JT2}
\]

There remain56894 of the56966 minimal orbits outside this certified
region. `verify_pg1_joint_carrier_transfer.py` and
`pg1_joint_carrier_transfer_certificate.json` check all40 criteria,
literal transport, support containment, minimality, and exact old overlap.
The inherited complete weighted count is hash-bound; matching is newly
computed only for included targets. The enlarged scalar budgets are not
silently substituted into that old count. An independent coordinate
enumeration and bipartite matching calculation agrees on the covered
sets. These are all-height moment bounds on the specified region, not
noncoverage for arbitrary prime support or a resolution of #7.

### Arithmetic admission requires a common numerical witness

[RRO section44 at devc33851543c](https://github.com/the-omega-institute/trureturing/blob/c33851543ce6ef8cc2e821a1d4fda7a49159b4f5/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#44-arithmetic-admission-order-and-euclidean-division-in-zeckendorf-observation)
sharpens the preceding guidance. Under its phase assumptions44.1,
theorem44.5 gives a full closed graph for variable-divisor Euclidean
division. Theorem44.11 exhibits two locally dense success constraints
whose conjunction is empty: one requires \(r<b\), the other \(b<r\).
Each separate finite-prefix image is full. Requiring one common
numerical witness before projecting detects the incompatibility.

For a literally fixed divisor \(c\), theorem44.8 retains the remainder,
the equation \(H(x)=cH(y)+[r\phi]\), and compatible approach sides.
Theorems44.9 and44.13 show, under those assumptions, why a finite
Zeckendorf prefix cannot serve as the exact residue observation needed
for #7: each completed dividend admits every remainder, and for
\(c\ge2\) no nonconstant finite-discrete output observer descends
continuously. The existing CRT observations retain those distinctions.
This is an obstruction to replacing them with a fixed digit prefix;
it is not an obstruction to exact finite integer conversion.

The dev increment contains theoretical text and digestion atoms, with
no new D5 theorem. Its topological closures and equidistribution along
one polynomial curve supply neither the finite CRT probability used
here nor a quantitative positive residual. In (WD1)--(WD6) and
(JT1)--(JT2), the useful implementation of the common-witness principle
is to keep the actual labeled layout and one source event throughout
the calculation. A uniform extension over the remaining carriers and
arbitrary later primes is still required.

### Complete integer hinges on the unchanged PG1 survivor law

Keep the PG1 probability, the actual higher357 event \(F\), and its
positive lower bound \(q_0=25428074957/48000000336\). For a complete
original test load \(L\), let \(H_t=\sup_L\mathbb E[(L-t)_+]\) on
this one conditional law. The following simultaneous bounds improve
the previously supplied interpolation or threshold4/6 estimates:

| Threshold \(t\) | Exact upper bound for \(H_t\) | Decimal upper bound |
| ---: | --- | ---: |
| 3 | \(10162026053915069246357/4868007485623062046875\) | 2.087512414 |
| 4 | \(1433737384346892410897/973601497124612409375\) | 1.472612141 |
| 6 | \(4033254968714385651877/4868007485623062046875\) | 0.828522755 |
| 7 | \(9648458629766273805119/14604022456869186140625\) | 0.660671309 |
| 8 | \(212159150814634558117/417257784481976746875\) | 0.508460618 |

The existing direct unweighted \(n=1\) cost already supplies
\(H_5\le1093534028247938362241/973601497124612409375\).
It is reused, not a new threshold5 calculation. The earlier
\(H_2\le3\), \(\mathbb E L\le5\), and square bound (WD4)
hold on this same probability.

For each of the ten fixed original3/original9 root pairs, evaluate the
convex row bound at thresholds3,7,8 on all270 auxiliary depths in
\([0,8]\times[0,5]\times[0,4]\). Threshold4/6 reuse their existing
complete arrays. Write \(h_{t,ij}(z)\) for these bounds,
\(\beta=\Pr(Z\text{ in the box})\), and \(h^*_{t,ij}(0)\) for
the exact zero-depth maximum over the actual twelve original labels.
Original-root realizations are retained before identical old loads
are deduplicated. The six seven-divisible labels have independent
digits; their maximizers need not use a common digit.

The true fixed-root hinge maximum obeys (M9C2), by its one-Lipschitz
increment bound. Thus replacing both the inside zero term and the
outside anchor in (M9C3) gives

\[
 U^{\rm new}_{t,ij}=U^{\rm old}_{t,ij}
 -\left(\Pr(Z=0)+1-\beta\right)
       \left(h_{t,ij}(0)-h^*_{t,ij}(0)\right),\qquad
 \Pr(Z=0)+1-\beta=\frac{12507116753}{27348890625}.       \tag{IH1}
\]

The other269 depth terms and the entire first-moment remainder
\(2330295100792072343/3063075771441530250000\) remain included.
Since the hinge is nonnegative and
\((1+I_3+I_9-t)_+=0\) for these thresholds,
\(H_t\le\max_{i,j}U^{\rm new}_{t,ij}/q_0\).
This comparison covers every original finite3/5/7 height. It changes
the observation bounds, not the actual probability or forbidden event.

`verify_pg1_integer_hinges.py` reconstructs the new depth arrays and
full tail, reuses hash-bound threshold4/6 data, and checks all50 rooted
zero maxima with the integer oracle. Each maximizing load is replayed
by the Python digit optimizer and literal twelve-label evaluation on
the75 source points. Selected nonlinear row values are also checked
by complete old-layout enumeration. The exact results are retained in
`pg1_integer_hinges_certificate.json`.

### A complete scalar schedule consumer and its remaining gap

Insert (IH1), the reused \(H_5\), \(H_2\le3\), mean5 and
\(G=491316187201313799169931/14604022456869186140625\)
into the existing actual-kernel criterion (SH28). Fix11/4 and13/5,
and consider all255 pairs \(1\le T_{17}\le15\),
\(1\le T_{19}\le17\). For any required integer \(j>8\), use
\(H_j\le\min(H_8,G/(4j))\); the second inequality follows from
\((L-j)_+\le L^2/(4j)\). Also \(H_1\le4\) since \(L\ge1\).

For each prime, the auxiliary multiplier distribution below \(T_p\)
is calculated exactly by divisor convolution. Its remaining mass and
first moment account for all \(N\ge T_p\), where the entire combined
cost is \(W(NL-T_p)/d_p\). No exponent or auxiliary tail is discarded.
The integer hinge expansion of (SH27) has nonnegative coefficients at
the final \(W\); its constant may be negative and is retained exactly.

The existing direct13/5 observation for \((2L-5)_+\) improves the
\(n=2\) charge term, but cannot simply be subtracted from an arbitrary
signed expansion. Put \(W_0=f_{13}a_{13}c_{13}\), the convexity
threshold. The valid decomposition is

\[
 h_W(2L)=h_{W_0}(2L)
       +\frac{W-W_0}{d_{13}}(2L-5)_+ .                 \tag{IH2}
\]

Bound the first summand by its nonnegative integer hinge coefficients,
and the second by the smaller of the direct cost and \(H_2+H_3\).
Both coefficients have the required sign because \(W\ge W_0\).
The resulting total cost has the form \(AW+B\). With
\(P=\prod_p(1+a_pc_p)\), (SH28) becomes
\(PG-1+B\le(1-A)W\). The final value must also satisfy every
prime's convexity condition.

Of these255 schedules,83 give a finite sufficient bound with the
supplied features. The best is11/4,13/5,17/8,19/8, giving

\[
 \Gamma_{19}\le
 \frac{4328407686313602732003920846923406469670769}
      {3525794087392122703309813353800433137280}
 <1227.640520.                                         \tag{IH3}
\]

Here \(P=7367153/1814400\), \(A<0.889741\), and equality holds
in (SH28). At the fixed17/7,19/8 thresholds the bound is
\(<1248.112850\). The remaining172 schedules have \(A\ge1\)
and strictly fail the affine criterion already at their smallest
convexity-admissible \(W\); increasing \(W\) cannot repair them.
None of these supplied-feature bounds is below484, the necessary
input threshold for the scalar23 continuation. This is a limitation
of this explicitly evaluated upper-bound criterion, not a lower bound
on actual moments and not an obstruction to other head laws or joint
observations.

`verify_pg1_scalar_schedule.py` and
`pg1_scalar_schedule_certificate.json` retain the complete255-case
calculation. Every successful row is checked at its final \(W\),
including the discrete feature identity, coefficient signs, full tail
and (SH28); each unsuccessful row retains its positive affine defect.
An independent rational convolution and convex-base decomposition
agrees on all255 outcomes. These are ordinary all-height estimates
and exact experimental certificates, not new Lean theorems or a
resolution of unrestricted #7.

### What the latest finite-quotient and observer results contribute

[RRO section45 at devd3774401e0](https://github.com/the-omega-institute/trureturing/blob/d3774401e080a6c4dfc7b73b86e94d4ad782166b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#45-稠密自然数紧半环的有限商强制性与阈值超自然周期分类)
assumes a compact Hausdorff unital semiring, jointly continuous
addition and multiplication, and a dense natural core. Under these
hypotheses it classifies finite natural quotients by a threshold and
period. Their common refinement takes the maximum threshold and the
least common multiple of the periods. In particular, the CRT residue
observations used here belong to a family closed under the required
arithmetic and finite intersections. The classification does not
give a uniform finite period sufficient for arbitrary input moduli,
nor does it attach survivor probabilities to these observations.
Section45.18 explicitly distinguishes existence of suitable finite
quotients from sufficiency of an arbitrary chosen finite observation.

[The ML observation companion section44](https://github.com/the-omega-institute/trureturing/blob/d3774401e080a6c4dfc7b73b86e94d4ad782166b/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md#44-精度切换后的严格区间捕获与可重复双轨观察)
proves finite capture of a valid new interval for its specified binary
hidden-state model. Its proof uses the same future reports, contraction
between two exact trajectories, and a strictly positive inward margin;
output accuracy alone does not supply interval membership. For #7,
no corresponding contraction or uniform inward survivor margin is
established. The useful design requirement is to prove that an
improved observation supports the next actual update, including its
positivity premise. The new dev increment contains no D5 declaration.
Neither result supplies the missing quantitative correlation between
the current test and the actual mixed bad union.

### Equal row charges do not determine the actual test update

For a row's pure-power survivor probability \(m\), mixed bad union
\(B\), \(\alpha=m(B)\), and clipping parameter \(0\le\delta<1\),
the actual distortion kernel has density \(g-h\mathbf1_B\), where

\[
 g=\frac1{1-\min(\alpha,\delta)},\qquad
 h=\begin{cases}
 \dfrac{\min(\alpha,\delta)}{\alpha(1-\min(\alpha,\delta))},
       &\alpha>0,\\
 0,&\alpha=0.
 \end{cases}
\]

In particular, \(g-h\alpha=1\), the old marginal is preserved, and
the assigned bad mass is \((\alpha-\delta)_+/(1-\delta)\).
For every fixed test cost \(Z\), the exact update is

\[
 \mathbb E_{\rm new}Z
 =g\mathbb E_mZ-h\mathbb E_m[Z\mathbf1_B].             \tag{PO1}
\]

This is the actual kernel from
[BBMST, section2](https://arxiv.org/abs/1811.03547), with its bad-set
term retained. The following two original arithmetic families show
why that term cannot be recovered from row charges and test marginals.

Use the existing PG1 low family and source probability \(\mu\),
and put \(x_0=2\), whose weight is
\(13119398/1000000007>0\). Add the pure class \(0\bmod17\),
so \(m\) is uniform on the16 roots \(1,\ldots,16\).
Index the nine distinct low divisors

\[
 (d_1,\ldots,d_9)=(3,5,7,9,15,21,35,45,315).
\]

Family A adds one class for each original modulus \(17d_i\), with
CRT coordinates \(x\equiv2\pmod{d_i}\), \(y\equiv i\pmod{17}\).
Family B instead uses \(y\equiv i+1\pmod{17}\), keeping the same
low residues. Each family has21 distinct odd moduli greater than one
and full period5355. Because the nine high roots are distinct in each
family, every low row has the same \(\alpha(x)\), natural cap, and
assigned charge in both families. Set \(T_{17}=8\), so the (SH26)
convention is \(\delta=7/15\).

Keep one fixed complete24-label test: for every \(d\mid315\), its
old class is \(2\bmod d\), and its \(17d\) class has the same low
residue and high root10. With
\(A(x)=\sum_{d\mid315}\mathbf1_{x\equiv2\bmod d}\), its load is

\[
 L(x,y)=A(x)(1+\mathbf1_{y=10}),\qquad
 Z=L^2-A^2=3A(x)^2\mathbf1_{y=10}.                    \tag{PO2}
\]

The source probability, all pre-kernel test moments, and the complete
old test load are identical. In Family A, however, \(B_x\) uses
only roots1 through9, so \(Z\mathbf1_{B_x}=0\) in every row.
In Family B, root10 is bad exactly when \(x\equiv2\pmod{315}\),
namely at \(x=x_0\). At that point,

\[
 A(x_0)=12,\quad \alpha=\frac9{16},\quad
 g=\frac{15}{8},\quad h=\frac{14}{9},\quad
 \text{charge}=\frac{23}{128},\quad c_{\rm actual}=2=c_{17}.
\]

Applying each family's own kernel to the same test gives row square
expectations \(1557/8\) and \(1221/8\), respectively. Hence the
global fixed-test square expectations differ by exactly

\[
 42\mu(2)=\frac{551014716}{1000000007}>0.               \tag{PO3}
\]

Thus row bad densities, natural caps, charges and pre-kernel test
marginals do not determine the test update. The natural-cap deficit
also vanishes at the distinguished row. The literal height-one
good-cylinder multiplier relative to \(17^{-1}\) is \(255/128\),
not2; the latter is the all-height natural upper cap. This small
pure-coordinate relaxation is separate from the overlap distinction.

Family A also rules out a universally strictly positive bad-overlap
bound for the new-coordinate increment \(Z\) without additional
residue-coupling hypotheses. It does not make the full-square overlap
zero: the old baseline \(A^2\) still overlaps the bad union. Neither
family is asserted to cover, and this example does not refute an
overlap bound with additional global-cover assumptions. It gives no
lower bound on the supremal \(\Gamma_{19}\).

An exact joint observation sufficient for (PO1) retains both
\(\mathbb E_mZ\) and \(\mathbb E_m[Z\mathbf1_B]\), along with
\(\alpha\), on one common CRT refinement. For a fixed finite
original family and test this is a finite computation. A bound usable
in the unrestricted continuation still requires uniform control over
all allowed tests and all heights. In particular, a test-specific
deficit cannot be subtracted from a uniform supremum unless its
infimum over the stated test domain is bounded, or that same test is
retained through the entire expansion. Formula (SH26) uses the valid
universal floor \(A_eA_f\ge1\) and is unaffected by this distinction.

`verify_pg1_physical_overlap.py` reconstructs both original families,
their common test and all literal residues modulo5355. It compares
direct row integration with (PO1), checks normalization and preserved
old marginals, and records (PO2)--(PO3) in
`pg1_physical_overlap_certificate.json`. This is a counterexample to
the specified compressed observation, with an ordinary proof and
exact arithmetic replay; no new Lean declaration is claimed.

For a finite next-step optimization, the full joint observation can be
written as a pair matrix. Fix the actual forbidden family and old law
\(\nu\). For original labels \(\ell,k\), retain their old test
cylinders \(C_\ell,C_k\) and current-prime test prefixes \(u,v\),
using the full current cylinder for an exponent-zero label.
With the actual row base laws \(m_x\), define

\[
 \begin{aligned}
 K_{\ell k}(u,v)=\mathbb E_{x\sim\nu}\bigl[
 \mathbf1_{C_\ell\cap C_k}(x)\bigl(&g_xm_x([u]\cap[v])\\
                  &-h_xm_x(B_x\cap[u]\cap[v])\bigr)\bigr].
 \end{aligned}                                         \tag{PO4}
\]

This is precisely the post-kernel intersection mass, hence nonnegative.
For one fixed complete test \(\mathcal T\), summing (PO4) over its
ordered original-label pairs gives \(\mathbb E_{\rm new}L_{\mathcal T}^2\).
Compatible current-prime prefixes intersect in their deeper prefix;
incompatible prefixes have empty intersection. A finite forbidden
family therefore permits exact evaluation from its actual finite
prefix antichain and a common old CRT refinement.

For a downstream factor \(f\ge0\) and charge weight \(W\ge0\),
the finite support function to estimate is
\(\max_{\mathcal T}\{f\mathbb E_{\rm new}L_{\mathcal T}^2+
W\mathbb E_\nu\operatorname{charge}(x)\}\), with one globally
legal test retained in every row and every matrix entry. If forbidden
families are also optimized, each family's kernel, charge and test
cost must remain together. Separate maximization of the positive
part and minimization of the subtracted overlap loses that constraint.
The pair matrix is an exact representation, not a proved compression
or a newly evaluated upper bound. Physical antichain depth is
unbounded across input families. The bounds below control complete
test tails for a fixed actual family and, separately, both forbidden
and test tails when the entire old cofactor inventory is small.

### Latest dev: finite solutions and a common actual witness

[RRO section46 at devdbbe3c44b8](https://github.com/the-omega-institute/trureturing/blob/dbbe3c44b82a352d5d1380cdd10e7b8d7ef491e7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#46-增补有限算术解共同自然见证与有效性边界)
distinguishes the actual image of simultaneous natural solutions,
the intersection of separately attained images, and solutions of
the quotient equations. These sets need not agree. Its system
\(x^2=x,\ x=z+2\) has compatible solutions in every stated finite
arithmetic quotient, but no natural solution. Sections46.7--46.8
identify a uniform bound on the natural witnesses as a sufficient
way to recover an actual witness from those approximations.

For the present optimization, this requires every pair entry, row
charge and test load to come from one actual original-label layout.
Separately attainable extrema cannot be assembled into a fictitious
joint witness. Conversely, an explicit finite CRT construction does
supply the needed actual witness; the comb below provides one.
Section46's H10 statements concern uniformly arbitrary polynomial
systems. They give no undecidability conclusion for #7 or for checking
one finite covering family: the latter is exactly decidable on its
finite least-common-multiple period. The inspected increment after
devd3774401e0 adds305 theory lines and digestion records, with no D5
change. It supplies neither a new survivor probability nor the missing
quantitative bound for unrestricted #7.

The subsequent [RRO section47 at dev947f585f61](https://github.com/the-omega-institute/trureturing/blob/947f585f613318920f48aa35859b360649e22409/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#47-全阈值周期完成中的自然锚边界环与判定边界)
identifies its completion as natural anchors together with a closed
profinite-integer boundary, with different internal and ambient zero
and unit elements. It separates logical definability of natural anchors
from continuous finite observation and effective membership decisions.
For any fixed finite covering family, however, all congruence conditions
factor through its one full period \(M\). A surviving profinite point
projects to a residue modulo \(M\), whose integer representative in
\([0,M-1]\) survives the same family. This finite CRT lifting has no
natural-anchor obstruction. Section47.10 adopts a published decision
theorem for the common first-order theory of all finite residue rings;
it does not supply a quantitative bound for the varying original-label
inventories here. This later increment adds407 theory lines and45 new
atom/residual pairs, with no D5 change or new #7 probability estimate.

There is an exact fixed-cardinality connection to the decision theorem
adopted in section47.10. In the language of rings put
\(D(u,v)\iff\exists t\ (v=ut)\), and let \(\Phi_N\) say

\[
 \exists u,d_1,\ldots,d_N,a_1,\ldots,a_N\quad
 2u=1\ \land\ \bigwedge_i\neg D(d_i,1)
 \ \land\ \bigwedge_{i<j}\neg(D(d_i,d_j)\land D(d_j,d_i))
 \ \land\ \forall x\ \bigvee_i D(d_i,x-a_i).
\]

For each fixed \(N\ge1\), some \(\mathbb Z/m\mathbb Z\),
\(m>1\), satisfies \(\Phi_N\) if and only if there exists an
\(N\)-class distinct odd-modulus cover. Forward, take integer
representatives and \(n_i=\gcd(d_i,m)\). The unit condition makes
\(m\) odd; proper, pairwise different principal ideals give distinct
odd \(n_i>1\). Ideal membership is exactly congruence modulo
\(n_i\), so the last clause covers every integer. Reverse, use
\(m=\operatorname{lcm}(n_1,\ldots,n_N)\) and \(d_i=n_i\)
as ring elements. Thus, conditional on the external common-theory
decision theorem adopted there, applying it to \(\neg\Phi_N\)
decides existence at that fixed class count, uniformly in \(N\).
This exact reduction does not decide the unrestricted quantifier over
all \(N\) in one call, give a bound on \(N\), or improve the
survivor estimates. The cited Cambridge primary text returned HTTP503
in this source check; the external algorithm is not independently
implemented or formally replayed here. No new Lean wrapper is added.

### A clean cylinder makes all current-prime pair caps exact

The fixed-test distinction (PO3) need not survive maximization over
all tests. At height one, suppose a root avoids both the pure forbidden
root and every actual mixed bad class. Fix arbitrary independent old
complete test loads \(A_0,A_1\). Placing every positive-depth test
label on that root simultaneously attains all current-prefix caps,
so the maximal new square for these old loads is

\[
 \mathbb E_\mu\left[A_0^2+
       \frac{g_x}{p-1}(2A_0A_1+A_1^2)\right].          \tag{CS1}
\]

The exponent-zero term follows from preserved old marginals; the
other terms are supported in the clean root. The same expression is
an upper bound for every current-root assignment, since the actual
kernel density is at most \(g_x\). Both families in (PO3) have a
common clean root and the same \(g_x\). Maximizing (CS1) over their
identical old test domain therefore gives identical complete-test
suprema, although their common fixed test has different values.

A common clean path does not suffice for this argument: every shallow
test cylinder on that path must itself be clean to attain its cap.
For example, at17 delete pure root0 and, for \(2\le e\le17\),
use the original mixed modulus \(3\cdot17^e\), old class1 modulo3,
and current residue \(e-1\) modulo \(17^e\). Each surviving root
contains some bad mass on that old row, although their total Haar
mass is less than \(\sum_{e\ge2}17^{-e}\) and a positive-measure
common clean set remains. This does not assert that every complete
test has positive overlap: a test can instead sacrifice shallow
energy on deleted cylinders.

Here is an exact arbitrary-height construction that also allows the
old layouts to vary independently with depth. Let \(M\) be odd,
\(p\nmid M\) prime, and

\[
 D=\{d>1:d\mid M\},\qquad K=|D|\le p-3.
\]

Fix one old probability \(\mu\). At each \(1\le e\le H\),
fix arbitrary old forbidden cylinders \(C_{d,e}\) for every
\(d\in D\). Independently, at every \(0\le e\le H\), fix
a complete old test layout with load \(A_e\). No old residues need
agree across depths or between forbidden and test layouts. The new
forbidden inventory contains exactly one class of each modulus
\(p^e\) and \(dp^e\), \(d\in D\), \(1\le e\le H\).
If an input omits some of these moduli, this is an enlarged admissible
inventory, not an assertion of equality within that smaller inventory.

Assign distinct spokes \(j_d\in\{1,\ldots,K\}\), reserve the
spine digit \(s=p-2\) and the test root \(r=p-1\). Digits below
are least significant first. Choose forbidden prefixes

\[
 p^e:\ s^{e-1}0,\qquad
 dp^e:\ (C_{d,e},s^{e-1}j_d).                         \tag{CS2}
\]

CRT realizes each pair as a residue modulo the stated original
modulus. No moduli are identified: \(p\nmid d\) separates current
exponents, and the old divisors are distinct. All current forbidden
prefixes are disjoint. At different depths they differ where the
shorter prefix leaves the spine; at the same depth their final digits
differ. The whole first-level cylinder \([r]\) is clean. Put

\[
 \begin{aligned}
 s_H&=\sum_{e=1}^H p^{-e},&\lambda_H&=1-s_H,\\
 R_e(x)&=\sum_{d\in D}\mathbf1_{C_{d,e}}(x),&
 b_H(x)&=\sum_{e=1}^H p^{-e}R_e(x),&
 \alpha_H(x)&=b_H(x)/\lambda_H.
 \end{aligned}                                       \tag{CS3}
\]

These are actual pure-survivor and mixed-union masses, not union
relaxations. In particular \(\lambda_H>(p-2)/(p-1)>0\) and
\(\alpha_H<K/(p-2)<1\) when \(K>0\); for \(K=0\) it is zero.
Fix \(0\le\delta<1\). For the normalized kernel (PO1), let

\[
 c_H=\frac1{\max\{\lambda_H-b_H,\lambda_H(1-\delta)\}},
 \qquad \beta_H=\frac{(\alpha_H-\delta)_+}{1-\delta}.
                                                               \tag{CS4}
\]

Thus \(c_H=g_H/\lambda_H\), and \(\beta_H\) is its actual
assigned bad mass. Place every depth-\(e\) test prefix at
\(r00\cdots0\), independently of its old label. Define

\[
 Q_H(x)=\sum_{\substack{0\le e,f\le H\\(e,f)\ne(0,0)}}
                  p^{-\max(e,f)}A_e(x)A_f(x).
\]

Every positive-depth pair intersection is then a nested clean prefix
of Haar mass \(p^{-\max(e,f)}\). The entire new square increment
vanishes on the actual bad union, while the old baseline is preserved.
Consequently

\[
 \mathbb E_{\rm new}[L_H^2\mid x]=A_0(x)^2+c_H(x)Q_H(x).
                                                               \tag{CS5}
\]

This is also the maximum over all current-prime forbidden residues
and all current-prime test prefixes with the specified old layouts.
Indeed, for any alternative, its pure-survivor Haar mass \(\lambda\)
and conditional mixed density \(\alpha\) obey
\(\lambda\ge\lambda_H\) and \(\lambda\alpha\le b_H\).
Its kernel cap therefore satisfies

\[
 \frac g\lambda=
 \frac1{\max\{\lambda(1-\alpha),\lambda(1-\delta)\}}
 \le c_H,
\]

and its charge is at most \(\beta_H\). Expanding every original
test-label pair gives the upper bound in (CS5). Construction (CS2)
attains it and the charge simultaneously, at every old point. For
any \(f,W\ge0\), the exact joint maximum is thus

\[
 \mathbb E_\mu\left[f(A_0^2+c_HQ_H)+W\beta_H\right]. \tag{CS6}
\]

The current-prime optimization has been eliminated in this specified
domain; the old forbidden and test layouts still have to be optimized
together. The count \(K\) is the number of actual original old
cofactors, not their number after projection to315 and not the number
active at one old point. Higher old prime powers, and previously
introduced11/13 labels, cannot be discarded to meet this hypothesis.

For the specialization \(R_e=R\) and \(A_e=A\) at every depth,
write \(C=1+R\), \(\delta=(T-1)/(p-2)\),
\(1\le T<p-1\), and \(d_p=p-1-T\). Then

\[
 \begin{aligned}
 Q_H&=a_H A^2,&a_H&=\sum_{j=1}^H(2j+1)p^{-j},\\
 a_H&\uparrow a_p=\frac{3p-1}{(p-1)^2},&
 a_p-a_H&=p^{-H}\left(\frac{2H}{p-1}+a_p\right),\\
 c_H&\uparrow\kappa(C)=\frac{p-1}{p-1-\min(C,T)},&
 \beta_H&\uparrow\frac{(C-T)_+}{d_p}.
 \end{aligned}                                       \tag{CS7}
\]

Hence the supremum over legitimate finite heights, with these old
layouts repeated, is exactly

\[
 \mathbb E_\mu\left[f(1+a_p\kappa(C))A^2+
                         \frac W{d_p}(C-T)_+\right]. \tag{CS8}
\]

This is a limit of finite actual families, not an infinite covering
system. Repeated old layouts are only a specialization of (CS6);
no claim that they optimize its full old-layout domain is made.

For PG1 at \(M=315\), \(K=11\), so both17 and19 admit the
construction. Including its eleven original old forbidden classes
gives exactly \(11+12H\) distinct odd moduli. Center both old
layouts at2, so \(R(2)=11\) and \(A=1+R\). At \(T=8\),
already at \(H=1\),

\[
 \beta_{17}(2)=53/128,\qquad \beta_{19}(2)=61/180.
\]

The global charge is at least these constants times
\(\mu(2)=13119398/1000000007>0\), yet new-square bad overlap is
exactly zero for every height. This rules out a universal positive
extra-overlap rebate under the local hypotheses alone. It does not
saturate the later (SH26) unit-floor relaxation, Jensen comparisons,
the scalar certificate or the final17/19 criterion, and it imposes
no eventual-cover assumption. The useful remaining target is the
joint old-layout energy and charge in (CS6), and control when the
actual cofactor inventory exceeds this construction's range.

`verify_pg1_comb_sharpness.py` and its adjacent certificate retain
exact finite realizations and kernel checks for this obstruction.
The all-height and optimization statements above have ordinary
proofs; no new Lean declaration or unrestricted resolution is claimed.

### Effective truncation of both forbidden and test layouts

In the precise small-inventory domain of (CS2)--(CS6), let \(M_H\)
be the maximum of (CS6) over every old forbidden and complete test
layout through height \(H\). Keep the same old law, cofactor inventory,
\(\delta,f,W\) at all heights. Suppose
\(\mathbb E_\mu A^2\le J\) for every complete old layout; the
elementary choice \(J=(K+1)^2\) always works here. Define

\[
 \begin{aligned}
 \lambda_*&=\frac{p-2}{p-1},& c_*&=\frac1{\lambda_*(1-\delta)},\\
 t_k&=\frac{p^{-k}}{p-1},&
 \varepsilon_k&=p^{-k}\left(\frac{2k+3}{p-1}
                                      +\frac2{(p-1)^2}\right).
 \end{aligned}
\]

For every extension from \(k\) to \(H\ge k\),
\(\lambda_k-\lambda_H\le t_k\) and
\(b_H-b_k\le Kt_k\). Both arguments of the maximum in the
denominator of (CS4) decrease, and its decrease is at most
\((K+1)t_k\). Its reciprocal never exceeds \(c_*\). Therefore

\[
 0\le c_H-c_k\le c_*^2(K+1)t_k,\qquad
 0\le\beta_H-\beta_k\le
                  \frac{Kt_k}{\lambda_*^2(1-\delta)}. \tag{CS9}
\]

For the second inequality, first bound
\(b_H/\lambda_H-b_k/\lambda_k\) by
\(Kt_k/\lambda_*+Kt_k/((p-1)\lambda_*^2)
=Kt_k/\lambda_*^2\), and then use the Lipschitz constant
\((1-\delta)^{-1}\) of the positive-part charge function.
For arbitrary independent old test loads, Cauchy--Schwarz gives
\(\mathbb E A_eA_f\le J\). Counting the \(2n+1\) ordered
exponent pairs with maximum \(n\) yields

\[
 \mathbb E Q_k\le a_pJ,\qquad
 0\le\mathbb E(Q_H-Q_k)\le J\varepsilon_k.
\]

Use the positive decomposition
\(c_HQ_H-c_kQ_k=c_H(Q_H-Q_k)+(c_H-c_k)Q_k\). Taking maxima gives
the effective enclosure

\[
 \boxed{M_k\le\sup_{H<\infty}M_H\le M_k+E_k},\qquad
 E_k=fJ\left[c_*\varepsilon_k+c_*^2(K+1)a_pt_k\right]
             +\frac{WKt_k}{\lambda_*^2(1-\delta)}.     \tag{CS10}
\]

The lower side follows by extending any maximizing old layouts;
all added terms and changes in (CS9) are nonnegative. The upper side
holds for each such extension before maximizing. For finite old period
and rational source data, \(M_k\) is a finite rational optimization,
and \(E_k\to0\). This is an algorithm for an arbitrary prescribed
precision, not a claim that a finite height attains the supremum or
that the finite optimization has been evaluated on PG1. Unlike a test
tail estimate, (CS10) also truncates the varying actual forbidden
families. The hypothesis \(K\le p-3\) and fixed old probability
are essential to the exact reduction used here. No bound on the
unrestricted old inventories or resulting \(\Gamma_{19}\) follows.

### Complete test tails for one arbitrary actual forbidden family

A separate estimate applies without the small-inventory hypothesis,
provided the actual forbidden family is fixed. Let \(P\) be its
minimal pure-prefix antichain, \(B_x\) its actual mixed union, and
\(\lambda\) Haar prefix mass. Put \(s=\lambda(P^c)>0\),
\(m=\lambda|_{P^c}/s\), and take the row coefficients \(g_x,h_x\)
from (PO1). For any prefix \(C\), write
\(R_F(C)=\lambda(C\setminus F)\). The exact kernel table is

\[
 K_x(C)=\frac{(g_x-h_x)R_P(C)+h_xR_{P\cup B_x}(C)}s.   \tag{KT1}
\]

Both coefficients are nonnegative. Reducing each actual union to
its minimal forbidden-prefix antichain makes (KT1) a finite residual
calculation as in (P13.2); forbidden descendants deeper than the query
remain in the calculation. This computes actual nonnegative pair
masses directly rather than assigning separate signed tail bounds.

Let \(D_0\) be the maximum actual forbidden depth. Above it extend
the actual law by uniform independent suffixes; below it use its
marginals. These consistent finite laws define every expectation
below. A complete test through \(H\) retains one independently chosen
CRT class per original label \(dp^e\), \(d\mid M\),
\(0\le e\le H\). If \(H>D_0\), these are auxiliary tests on
the extended period. Their supremum is an upper domain for the
original finite-period tests; a lower bound for the extended supremum
is not a lower bound for the original finite-period maximum.

Suppose \(K_x(C_e)\le c(x)p^{-e}\) for every positive-depth
prefix, and \(\mathbb E_\mu[cA^2]\le G_c\) for every complete
old layout. One may always use \(c=g/s\). For any test through
\(H\ge k\), retain its original labels through \(k\), with load
\(U=L_{\le k}\). Expanding the actual nonnegative pair masses gives

\[
 0\le\mathbb E L_H^2-\mathbb E U^2\le G_c\varepsilon_k.
                                                               \tag{KT2}
\]

Indeed, a pair of exponents \(e,f\) has mass at most
\(p^{-\max(e,f)}\mathbb E[cA_eA_f]\), bounded by
\(p^{-\max(e,f)}G_c\) by weighted Cauchy--Schwarz. Sum precisely
the pairs with maximum above \(k\). This is the complete-tail
application of the existing
`PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le`
pair estimate; no new Lean wrapper is needed. Consequently the exact
finite maximum \(\Gamma_k\), computed with the entire actual
forbidden family, satisfies

\[
 \Gamma_k\le\sup_{H<\infty}\Gamma_H
                  \le\Gamma_k+G_c\varepsilon_k.       \tag{KT3}
\]

Here only tests are truncated. Dropping deeper forbidden prefixes
would change the actual kernel and is not justified by (KT2).

A correlated finite support function can sharpen this tail. Take
\(k\ge D_0\), fix one truncated test \(U\), and let \(V\)
range over the finite set of loads

\[
 V(x,a)=\sum_{d\mid M}\mathbf1_{x=u_d\bmod d}
                        \mathbf1_{a=v_d\bmod p^k}.
\]

Each pair \((u_d,v_d)\) is chosen globally for its original label,
before sampling \((x,a)\); these are not pointwise choices in each
old row. For the actual joint law \(\nu_k\), define

\[
 b(V)=\mathbb E_{\nu_k}UV,\quad s(V)=\mathbb E_{\nu_k}V^2,
 \qquad h_U(t)=\max_V\{2b(V)+ts(V)\}.
\]

Uniformity after \(k\) implies that, for any independent projected
layers \(V_1,\ldots,V_n\), the largest extra energy equals

\[
 2\sum_{j=1}^np^{-j}\langle U,V_j\rangle+
 \sum_{j,l=1}^np^{-\max(j,l)}\langle V_j,V_l\rangle.  \tag{KT4}
\]

The intersection cap supplies the upper bound. It is simultaneously
attained by setting every additional test suffix to zero, leaving its
old residue and first \(k\) digits unchanged. Equal first prefixes
then have compatible suffixes, while unequal first prefixes still
have empty intersection. This alignment applies only beyond the
complete actual forbidden depth; it does not identify the independent
\(V_j\)'s or their old layouts.

Let \(T(U)\) be the supremum of (KT4) over all finite lengths and
allowed layers. Repeating one layer gives the lower bound below;
\(2\langle V_j,V_l\rangle\le s(V_j)+s(V_l)\) gives the upper:

\[
 \frac{h_U((p+1)/(p-1))}{p-1}\le T(U)
 \le\sum_{j\ge1}p^{-j}h_U\left(j+\frac1{p-1}\right)
 \le G_c\varepsilon_k.                              \tag{KT5}
\]

For the last step use
\(\max_V b(V)\le(k+1)p^{-k}G_c\) and
\(\max_V s(V)\le p^{-k}G_c\), proved by the same original-pair
expansion as (KT2). Maximizing \(\mathbb E U^2\) plus a chosen
side of (KT5) must keep the same \(U\) in both terms. Repeating
one \(V\) is a lower construction, not a proved optimizer.

For rational source data, \(h_U\) is a finite upper envelope of
rational lines. If \(S=\max s(V)\) and
\(b_* =\max\{b(V):s(V)=S\}\), choose an integer \(N\ge1\)
at least every
\(2(b(V)-b_*)/(S-s(V))-1/(p-1)\) with \(s(V)<S\).
For \(j\ge N\), the line \((b_*,S)\) dominates, so the remaining
sum in (KT5) is exactly geometric. With \(r=1/p\) and
\(a=2b_*+S/(p-1)\), it is

\[
 \sum_{j=N}^{\infty}r^j(a+Sj)
 =r^N\left[\frac a{1-r}
       +S\left(\frac N{1-r}+\frac r{(1-r)^2}\right)\right].
\]

The finite support enumeration or a valid dominance certificate must
cover every realizable \(V\); a sampled support function gives no
upper certificate. These formulas give a complete-tail optimization
framework for a fixed actual family. Uniform maximization over all
forbidden families with unrestricted old inventories remains unresolved.

### Original-label coloring extends the exact comb reduction

The small total inventory condition in (CS2) has a useful sufficient
replacement. At each depth \(e\), form the graph on the original
nonunit old cofactors, joining \(d,d'\) when
\(\mu(C_{d,e}\cap C_{d',e})>0\). Suppose it has a proper coloring
with at most \(q\le p-3\) colors. Each coloring is chosen globally
before sampling the old point; it may vary with depth. Assign its colors
to the spokes of (CS2), retaining every original modulus \(dp^e\).
Same-color old cylinders are disjoint almost everywhere, and different
depths leave the spine at different digits. Thus

\[
 R_e\le q\quad\mu\text{-a.e.},\qquad
 b_H=\sum_{e=1}^Hp^{-e}R_e,\qquad
 \max\mathbb E[fL_H^2+W\beta]
 =\mathbb E_\mu[f(A_0^2+c_HQ_H)+W\beta_H].             \tag{CC1}
\]

The coefficients are exactly (CS4). The same union and pair-cap proof
gives the upper bound for arbitrary alternative current residues;
the colored comb attains it. The complete test layouts remain independent
of the forbidden layouts. The construction is a sufficient condition,
not a characterization of every exact arrangement.

This permits arbitrarily many original labels. On the uniform higher-3
lift of PG1, the cylinders \(2+3^{a-1}\bmod3^a\),
\(3\le a\le A\), are positive and pairwise disjoint: for \(a<b\),
the latter cylinder reduces to \(2\bmod3^a\). They use one color
for every \(A\). Other old divisors can take cylinders disjoint from
the old support. Their labels still occur in the complete test domain.
If \(J\) bounds every complete old test square for that full period,
(CS9)--(CS10) hold with \(q\) replacing \(K\):

\[
 E_k=fJ[c_*\varepsilon_k+c_*^2(q+1)a_pt_k]
       +\frac{Wqt_k}{\lambda_*^2(1-\delta)}.           \tag{CC2}
\]

This follows from \(R_e\le q\) in each tail estimate. It does not
replace \(J\) by a bound for only the colored or low-power labels.
For a supremum over colorable families and \(k\ge1\), repeating any
already admissible properly colored old forbidden layout preserves
the domain and supplies the lower truncation bound.

For a palette assignment that is not proper, put
\(N_{e,j}=\sum_{d:\,\mathrm{color}_e(d)=j}\mathbf1_{C_{d,e}}\),
\(U_e=\sum_j\mathbf1_{N_{e,j}>0}\), and
\(D_e=R_e-U_e=\sum_j(N_{e,j}-1)_+\). Its legal comb has actual
mixed mass \(b_1=\sum_ep^{-e}U_e\), while the counting relaxation
has \(b_0=\sum_ep^{-e}R_e\). For fixed \(\lambda=\lambda_H\),
write

\[
 \ell_< =\min(b_0,\delta\lambda)-\min(b_1,\delta\lambda),\qquad
 \ell_> =(b_0-\delta\lambda)_+-(b_1-\delta\lambda)_+.
\]

Their sum is \(b_0-b_1\). Subtracting the actual cost from the
counting-relaxation cost gives exactly

\[
 \mathbb E_\mu\left[
 \frac{fQ_H\ell_<}
 {(\lambda-\min(b_0,\delta\lambda))
  (\lambda-\min(b_1,\delta\lambda))}
 +\frac{W\ell_>}{\lambda(1-\delta)}\right].          \tag{CC3}
\]

This is an identity for that assigned comb, not an assertion that it
maximizes the unrestricted current-prefix problem. It locates losses
below and above the clipping threshold on the same actual old rows.

### A genuine seventeen-step collision with an exact charge correction

Use PG1 with denominator \(D=1000000007\), and independently uniform
coordinates modulo \(121\) and \(169\) conditional on nonzero
roots modulo \(11\) and \(13\). This is an actual old law for the
eleven PG1 classes and the four pure zero classes modulo
\(11,121,13,169\); its old period is \(6441435\).
The old cylinders
\(C_3=(2\bmod3),C_5=(4\bmod5),C_7=(4\bmod7)\)
have empty triple intersection on this support and pair masses

\[
 \mu_0(C_3\cap C_5)=\frac{106787589}{D},\qquad
 \mu_0(C_3\cap C_7)=\frac{81877150}{D},\qquad
 \mu_0(C_5\cap C_7)=\frac{28161457}{D}.                \tag{CC4}
\]

For each \(d\in\{3,5,7\}\) and
\(t\in\{1,11,13,121,143,169\}\), retain the original
cofactor \(dt\), with old condition \(C_d\) and residue \(1\)
modulo \(t\). These eighteen old events form \(K_{18}\), although
no old point activates more than twelve of them. Add pure zero modulo
\(17\) and one class of each original modulus \(17dt\), with
arbitrary current roots. This is a family of thirty-four distinct odd
moduli, with period \(109504395\). The sixteen surviving current
roots cannot make all eighteen labels pairwise disjoint on old support.

Let \(E_{ij}\) require \(C_i\cap C_j\) and the common deep slice
\(z_{11}=1\bmod121,z_{13}=1\bmod169\). These three events are
disjoint and each has mass at least
\(m=28161457/(17160D)\). If \(S_i\) is the set of nonpure
roots assigned to the six labels in group \(i\), set
\(d_{ij}=12-|S_i\cup S_j|\). With
\(D_i=6-|S_i|\), inclusion-exclusion gives

\[
 \sum_{i<j}d_{ij}=2\sum_iD_i+\sum_{i<j}|S_i\cap S_j|
 \ge18-\left|\bigcup_i S_i\right|\ge2.
\]

This also permits repeated roots within a group or assignments to the
deleted pure root. At \(\delta=7/15\), the ideal row charge on
\(E_{ij}\) is \(17/32\), and losing \(d_{ij}\) roots reduces
it by \(\min(15d_{ij},68)/128\). These are nonnegative integer
deficits whose sum is at least two; consequently their three charge
reductions sum to at least \(30/128\). Every current-root assignment
therefore satisfies

\[
 \mathbb E\beta_{\rm actual}
 \le\mathbb E\beta_{\rm count}-\Delta,\qquad
 \Delta=\frac{15m}{64}
       =\frac{28161457}{73216000512512}.              \tag{CC5}
\]

The bound is attained. Give one shared root to the pair
\((5\cdot121,7\cdot169)\), another to
\((5\cdot169,7\cdot121)\), and distinct roots to the other
fourteen labels. Only \(E_{57}\) loses roots, exactly two there.
The resulting exact maximum charge is
\(201659592817/1098240007687680\), compared with the counting
upper value \(12630125917/68640000480480\).

The minimum mean union-count loss is exactly \(2m\). To see the
lower bound, move pure-root labels to surviving roots and split groups
until sixteen roots are occupied; neither operation decreases any
row's union. A partition of eighteen labels into sixteen nonempty
groups has one triple or two disjoint pairs. Each pair intersection
has mass at least \(m\); a triple contributes its three pair masses
minus its triple mass, hence at least \(2m\). The displayed two
pairs attain that loss. There are precisely \(816+9180=9996\)
such partitions, all included in the exact verifier.

For this fixed inventory and these fixed old cylinders, \(W\Delta\)
may be subtracted from the union/cap joint upper functional for every
test and every \(f,W\ge0\). Optimal charge does not assert optimal
test square. Every row has density at most \(3/4\), so a pointwise
near-full-union overlap correction requiring density greater than
\(15/16\) detects none of this gain.

The graph alone supplies no positive height-uniform gap. For
\(N\ge0\), replace every multiplier \(t\) by \(11^Nt\),
preserving its compatible residue \(1\). Keep the fifteen old
forbidden classes and lift the old law uniformly through height
\(N+2\) at \(11\). The actual full period is now
\(315\cdot11^{N+2}\cdot13^2\cdot17\). The graph is still
\(K_{18}\), the maximum row activity is still twelve, and the
same two pairs attain

\[
 \min\mathbb E(R-U)=2m\,11^{-N},\qquad
 \min\mathbb E(\beta_{\rm count}-\beta_{\rm actual})
       =\Delta\,11^{-N}.                            \tag{CC6}
\]

Indeed the three common deep pair events now require
\(z_{11}=1\bmod11^{N+2}\); their masses scale by \(11^{-N}\).
Every pair intersection still has mass at least \(m11^{-N}\),
and the two chosen pairs intersect only on the smallest deep event.
The preceding lower and upper constructions apply unchanged. This
does not say that all other intersection masses scale equally.
Thus class count, row activity and unweighted overlap graph leave a
genuine quantitative gap: the intersection masses must be retained.

`verify_pg1_color_collision.py` checks the adjacent certificate with
exact arithmetic: all9996 partitions,55 reduced source states,
675 weighted old CRT representatives and10800 literal current-point
checks. It reconstructs the same actual probability, original residues
and normalized kernels. The coloring extension and (CC6) are ordinary
arguments above; the certificate covers the \(N=0\) instance.

### Repeating one diagonal old layout does not maximize the joint cost

Even within the low315 comb domain, identifying the forbidden and
test layouts loses possibilities. Fix \(p=17,T=8,f=59/45,W=483\),
and let \(A,C\) be independent complete old twelve-label loads,
each repeated at every current depth; \(C\) includes the unit term.
The limit of (CS6) is

\[
 \Phi(A,C)=\mathbb E_\mu\left[
 \frac{59}{45}\left(1+\frac{25}{128}
             \frac{16}{16-\min(C,8)}\right)A^2
 +\frac{483}{8}(C-8)_+\right].                      \tag{JL1}
\]

The existing complete twelve-label oracle enumerates every independent
old residue choice for a common load \(B\), not only coherent centers.
Round each whole weighted point cost upward at scale32768 and apply
that oracle. It gives the rigorous bound

\[
 \max_B\Phi(B,B)\le
 \frac{746858239119517}{32768000229376}
 =22.792304501083659\ldots.                           \tag{JL2}
\]

The maximum's rounding gap is less than
\(75/32768000229376\). This also bounds every finite-height
family with one such repeated common old layout and arbitrary current
prefixes. In fact \(s_H\le1/16\) and
\(a_H=\sum_{e=1}^H(2e+1)17^{-e}\le25/128\).
Both denominator branches of
\(c_H(B)=1/\max\{1-Bs_H,(1-s_H)8/15\}\) decrease with
\(s_H\), while \((B-1)s_H/(1-s_H)\) increases. They are
positive for \(1\le B\le12\). Thus the finite joint cost is
at most (JL1) with \(A=C=B\), and (CS6) covers arbitrary current
prefix choices for those old layouts.

Now choose the forbidden old center257 and test old center47:
\(C(x)=\sum_{d\mid315}\mathbf1_{x=257\bmod d}\) and
\(A(x)=\sum_{d\mid315}\mathbf1_{x=47\bmod d}\).
The actual height-three comb has47 distinct forbidden moduli,
48 complete test labels and period1547595. Its exact joint cost is

\[
 \frac{3843229007141107789887039465169}
      {168205257902111866972725489300}
 =22.848447516294048\ldots>\max_B\Phi(B,B).           \tag{JL3}
\]

Its limit is \(74868660065651/3276000022932\); the full
omitted tail difference is
\(440164771212699691855269553/84102628951055933486362744650\).
`verify_pg1_joint_layout_gap.py` reconstructs the directed full-domain
upper bound and all345450 supported CRT/kernel point evaluations for
the finite witness. Both the forbidden and test tails are retained.

This refutes domination by a single repeated diagonal old layout.
It does not compare against the larger class of common layouts
\(A_e=C_e\) varying independently with depth, nor optimize arbitrary
higher old powers or the later-prime continuation. Together with
(CC5)--(CC6), it identifies actual joint information required by the
next bound; no new global \(\Gamma\) improvement or unrestricted
noncoverage theorem follows. These are ordinary mathematical arguments
and exact experimental certificates, not new Lean conclusions.

### A common dual test law for redistributing charged bad mass

For one fixed actual forbidden family and one fixed old law \(\nu\),
the density in (PO1) has an additional admissible degree of freedom.
Write \(m_x\) for the normalized pure-survivor law on a finite
current fibre, \(B_x\) for its entire actual mixed bad union, and
\(\alpha_x=m_x(B_x)\). On rows with \(\alpha_x>\delta\), put

\[
 C=(1-\delta)^{-1},\quad
 \beta_x=\frac{\alpha_x-\delta}{1-\delta},\quad
 r_x=\frac{\beta_x}{\alpha_x},\qquad
 \frac{dq_{v,x}}{dm_x}=C\mathbf1_{B_x^c}+v_x\mathbf1_{B_x},
 \quad 0\le v_x\le1,\quad\int_{B_x}v_x\,dm_x=\beta_x.
                                                               \tag{KR1}
\]

The constant choice \(v_x=r_x\) is the existing kernel. Every
choice in (KR1) has total mass \(C(1-\alpha_x)+\beta_x=1\),
the same charge \(q_{v,x}(B_x)=\beta_x\), the same density cap
\(C\), and \(q_{v,x}(S)\le m_x(S)\) for \(S\subseteq B_x\).
Normalization preserves all old marginals. These are precisely the
pointwise cap and bad-subset properties used here from
[BBMST, section2, Lemma2.2](https://arxiv.org/html/1811.03547#S2.Thmtheorem2).
The existing `ConditionalComparison/Distortion` module fixes the
constant inside multiplier; it is reused as that special choice.

Keep uncharged and degenerate rows at their existing kernels by
definition. Nonconstant choices within this specified class require
\(0<\delta<\alpha_x<1\) and at least two positive-mass bad atoms.
No optimum over every possible physical law is asserted: the exterior
density and uncharged rows have deliberately been fixed.

Let \(\mathcal T\) be the finite set of all globally legal complete
tests at the chosen finite height, preserving every original modulus.
Let \(L_T\) be the actual load, \(Q_{\rm BB}(T)\) its square
expectation for the constant-inside kernel, and
\(V_{\rm BB}=\max_TQ_{\rm BB}(T)\). Choose one kernel before
the test is selected, and define
\(V_* =\min_v\max_T\mathbb E_{\nu q_v}L_T^2\).
For a single common distribution \(\pi\) on \(\mathcal T\), put
\(F_{\pi,x}(y)=\sum_T\pi_TL_T(x,y)^2\). On a flexible row,
the exact minimum bad contribution and its saving are

\[
 \begin{aligned}
 \ell_x(F)&=\min_{0\le v\le1,\,\int_Bv\,dm=\beta_x}
                     \int_BvF\,dm\\
 &=\max_{\tau\in\mathbb R}
       \left[\beta_x\tau-\int_B(\tau-F)_+\,dm\right],\\
 D_x(F)&=r_x\int_BF\,dm-\ell_x(F)\ge0.
 \end{aligned}                                                 \tag{KR2}
\]

This directly reuses `FractionalKnapsackDual.fractional_knapsack_strong_duality`
and `greedy_attains_duality`: on positive-mass bad atoms take item
weights \(m_x(y)\), values \(m_x(y)F(y)\), budget
\(\alpha_x-\beta_x\), and item variables \(1-v(y)\).
Since \(F\ge0\), unused budget can be filled without decreasing
the objective. Subtracting the resulting maximum from \(\int_BF\,dm\)
gives (KR2); negative prices cannot improve its right side. Thus fill
the lowest \(F\) levels with density one, the highest with zero,
and split at a boundary level to give exactly \(\beta_x\).
Set \(D_x=0\) on unchanged rows. No duplicate duality theorem is needed.

Finite minimax (the compact convex affine case of Mathlib's
`Sion.minimax'`), followed by this separate row minimization, gives

\[
 \begin{aligned}
 V_*&=\max_{\pi\in\Delta(\mathcal T)}
       \left[\sum_T\pi_TQ_{\rm BB}(T)
                         -\mathbb E_\nu D_x(F_{\pi,x})\right],\\
 V_{\rm BB}-V_*&=\min_{\pi\in\Delta(\mathcal T)}
       \left[V_{\rm BB}-\sum_T\pi_TQ_{\rm BB}(T)
                         +\mathbb E_\nu D_x(F_{\pi,x})\right].
 \end{aligned}                                                 \tag{KR3}
\]

Both terms on the second line are nonnegative. On a flexible row,
\(D_x(F)=0\) exactly when \(F\) is constant on the positive-mass
part of \(B_x\). One direct quantitative proof is to let
\(a=\mathbb E[F\mid B_x]\),
\(\omega=\max_{B_x}F-\min_{B_x}F>0\), taking extrema only on
positive-mass atoms, and choose
\(v=r_x-\min(r_x,1-r_x)(F-a)/\omega\). Its density lies in
\([0,1]\), its mass is \(\beta_x\), and hence

\[
 D_x(F)\ge
 \frac{\alpha_x\min(r_x,1-r_x)}{\omega}
                 \operatorname{Var}_{m_x(\cdot\mid B_x)}(F).
                                                               \tag{KR4}
\]

For constant \(F\) set this lower bound to zero. For nonconstant
\(F\) its right side is positive. Compactness of the finite simplex
in (KR3) now gives an exact strict-improvement criterion: \(V_*<V_{\rm BB}\)
if and only if there is no common mixture supported on
BBMST-maximizing tests for which \(F_{\pi,x}\) is constant on
every flexible bad fibre of positive \(\nu\)-mass. For rational
data, absence of such a mixture is a finite rational feasibility
question, using equations
\(\sum_T\pi_T(L_T(x,y)^2-L_T(x,z)^2)=0\) for positive-mass
bad atoms \(y,z\). The optimal values are rational.
Replacing each \(D_x\) in (KR3) by (KR4) also gives a sufficient
lower bound for the improvement, but it still requires minimizing
over that single common \(\pi\). Separate row mixtures or gains
against only one test do not supply it.

The threshold formula in (KR2) solves the inner problem for a
fixed \(\pi\). Arbitrary choices at tied threshold levels of a
dual optimum need not give a primal minimax kernel. A realizing law
must come from a saddle-compatible primal solution or be checked
against every legal test. The strict criterion above is finite;
an infinite test domain need not have a maximizing face.

The clean comb passes this test with equality. It has a maximizing
complete test whose positive-depth labels are all on the clean root.
On every actual bad fibre its load equals the old load \(A_0(x)\),
independent of the current point. The point mass on this test makes
every \(D_x\) zero, so (KR3) gives \(V_*=V_{\rm BB}\).
The coloring extension has the same property. Thus the new kernel
class does not contradict the sharpness obstruction.

Complete test tails remain controlled for an arbitrary fixed family.
Let \(D_0\) be its actual forbidden depth and \(k\ge D_0\).
Allow uniform independent suffix coordinates as in (KT2)--(KT3).
Project any feasible density to its conditional expectation on the
first \(k\) digits; since \(B_x\) is already measurable there,
this preserves all row constraints and every depth-at-most-\(k\)
test. Conversely, extend a finite feasible kernel uniformly in the
suffix. Let \(V_k^*\) be its finite minimax value and \(V_\infty^*\)
the infimum, over these full feasible densities, of the supremum
over all finite complete test heights. If
\(\mathbb E_\nu[cA^2]\le G_c\) for every complete old layout,
where \(c=g_x/s\) is the unchanged cap relative to Haar measure,
the same original-pair proof gives

\[
 V_k^*\le V_\infty^*\le V_k^*+
 G_cp^{-k}\left[\frac{2k+3}{p-1}+\frac2{(p-1)^2}\right].
                                                               \tag{KR5}
\]

For the upper bound, uniformly extend a finite minimizer and use
(KT2); the lower bound follows from projection. The old law and
complete forbidden antichain are fixed throughout. Tests beyond the
family's own period are auxiliary, so their supremum is an upper
domain, not a lower bound for the original finite-period problem.
This truncates tests only and gives no uniform family truncation.

At the final prime of a continuation, the new kernel can be consumed
without changing any earlier observation. Write \(B_{<p}\) for
accumulated earlier assigned charge and \(b_p=\mathbb E_\nu\beta_x\).
Here \(V_p^*\) denotes the attained finite minimax on the actual
family's full period; an upper certificate from an explicitly feasible
kernel with its complete tail may be substituted for it.
For \(W>0\), if a common history domain satisfies
\(V_p^*-1+W(B_{<p}+b_p)\le C_0<W\), then the same final
conditioning proof as (SH28) gives positive survivor mass and
\(\Gamma\le1+C_0\). Indeed \(V_p^*\ge1\) forces \(C_0\ge0\),
the total charge is at most \(C_0/W<1\), and
\(V_p^*-1\le C_0(1-B_{<p}-b_p)\). An earlier-prime change
requires recomputing any later statistics tied to the old law.

The optimized value concerns the physical law before final conditioning.
All admissible kernels agree on \(B_x^c\); therefore they agree on
the final survivor event, which is contained in that complement.
Its mass and its conditioned law, when that mass is positive, are
unchanged. At the last prime this procedure can sharpen the physical
moment/charge certificate, but cannot change the actual final supported
law or its true complete-test \(\Gamma\).
No bound \(C_0<483\) through19, uniform improvement over all
forbidden families, or unrestricted noncoverage conclusion is established here. These
are ordinary finite optimization and tail arguments, not new Lean
declarations or a claim of literature priority.

### The constant bad multiplier need not minimize the physical test square

There is an exact finite counterexample to universal optimality of the
constant inside multiplier. Use old period9, old forbidden classes
\(0\bmod3,0\bmod9\), and old probability concentrated at1.
This is a supplied supported old law, as permitted in (KR1); it is
not asserted to arise from an earlier standard distortion of Haar law.
At prime5 through height2 take the additional original classes

\[
 0\bmod5,\quad0\bmod25,\quad1\bmod15,\quad
 37\bmod45,\quad28\bmod75,\quad154\bmod225.          \tag{KR6}
\]

All eight moduli are distinct odd integers greater than one. On the
old row1, let \(y\) be the current residue modulo25. The pure law
is uniform on the twenty \(y\not\equiv0\pmod5\). The mixed bad
set consists of the ten leaves on roots1 and2, together with the
leaves3 and4 on the other two surviving roots. Thus
\(\alpha=3/5\). At \(\delta=2/5\) its assigned charge is
\(\beta=1/3\). The constant kernel gives each good leaf mass
\(1/12\) and each bad leaf mass \(1/36\).

An admissible alternative keeps each good leaf at \(1/12\), assigns
\(1/30\) to each of the ten leaves on roots1 and2, and assigns zero
to bad leaves3 and4. Its bad density relative to the pure law is
\(2/3\) or zero, so (KR1) holds with unchanged charge and cap.

The complete test domain has all nine original divisor labels
\(d5^e\), \(d\in\{1,3,9\},0\le e\le2\).
On the old atom, every inactive old residue can be made active without
reducing the load. Its zero layer can therefore be set to3.
For the three remaining root choices \(r_i\) and three leaf choices
\(s_j\), the full load divided by3 is the average of
\(1+\mathbf1_{y=r_i\bmod5}+\mathbf1_{y=s_j\bmod25}\)
over all nine pairs \((i,j)\). Convexity of the square and taking
all roots equal and all leaves equal consequently prove the exact
full-domain reduction

\[
 V(q)=9\max_{0\le r<5,\,0\le s<25}
     \mathbb E_q(1+\mathbf1_{y=r\bmod5}
                    +\mathbf1_{y=s\bmod25})^2.       \tag{KR7}
\]

All125 choices give

\[
 V_{\rm BB}=\frac{45}{2},\qquad
 V(q_*)=V_* =\frac{87}{4},\qquad
 V_{\rm BB}-V_* =\frac34.                            \tag{KR8}
\]

For the matching minimax lower bound, choose root3 and a good leaf
above it. Under every admissible kernel, its four good leaves retain
total mass \(1/3\), and that leaf retains mass \(1/12\).
The nested aligned test therefore has square at least
\(9[1+3/3+5/12]=87/4\); other bad contributions are nonnegative.
Thus the alternative attains the exact optimum of (KR1), with no
unexamined complete tests or sampled maximum.

Both laws condition on the same eight final good leaves to the same
uniform law. Its complete-test value, again by (KR7), is
\(9[1+3/2+5/8]=225/8\). The strict improvement in (KR8) is a
physical moment improvement before conditioning, not an improvement
in this final supported value. It occurs for a fixed small-inventory
family without a common clean root; the separate clean-comb worst
family obstruction remains intact.

`verify_bad_mass_rearrangement.py` reconstructs the actual eight-class
family and checks its adjacent exact certificate, including all125
aligned tests under both physical laws and the common final survivor
law. The full-domain reduction is (KR7); the minimax lower bound is
the fixed good-root test above. This refutes universal optimality of
the constant inside multiplier for the physical complete-test objective,
without asserting any full-family or later-prime improvement.

### Survivor invariance along a finite chain and density-cap saturation

Fix an initial law \(\nu_0\), an actual forbidden family, and any finite
sequence of prime-coordinate extensions. Let \(S_i\) be the event of
avoiding every forbidden class through stage\(i\). At an old prefix
\(h\), write \(m_i(h,y)\) for the fixed pure-survivor base and
\(B_i(h)\) for the entire current mixed bad set. Consider two normalized
kernel chains \(q_i^a\), \(a\in\{0,1\}\), with these same bases.
Suppose that whenever \(h\in S_{i-1}\) and \(y\notin B_i(h)\),
both kernels have the same good transition
\(q_i^a(h,y)=m_i(h,y)g_i(h,y)\). The common multiplier may depend on
the whole prefix and current point. For every \(z=(x_0,\ldots,x_i)\in S_i\),
successive multiplication of conditional probabilities gives

\[
 P_i^a(z)=\nu_0(x_0)\prod_{j=1}^i q_j^a(z_{<j},x_j)
        =\nu_0(x_0)\prod_{j=1}^i m_j(z_{<j},x_j)g_j(z_{<j},x_j).
                                                               \tag{SI1}
\]

Thus the restrictions \(P_i^0|_{S_i}\) and \(P_i^1|_{S_i}\) agree
pointwise at every stage. No agreement is required on bad transitions
or on any transition after an already bad prefix. In particular, arbitrary
rearrangements confined to bad sets throughout a finite continuation
preserve the final survivor mass and, when that mass is positive, its
entire conditioned law and true complete-test \(\Gamma\). Later physical
moments and expected assigned charges can change on already bad prefixes;
such changes can tighten certificates without changing this final law.

More generally, keep the same initial law, bases and final event \(S=S_n\),
but allow different good multipliers \(g_i^a\). Assume the baseline
\(g_i^0\) is strictly positive on positive-base good transitions, the
comparison \(g_i^1\) is finite and nonnegative, and both survivor masses
\(\rho_a=P_n^a(S)\) are positive. On the positive baseline survivor
support define

\[
 \begin{aligned}
 R(z)=\prod_{i=1}^n\frac{g_i^1(z_{<i},x_i)}{g_i^0(z_{<i},x_i)},
 &\qquad P_n^1(z)=R(z)P_n^0(z),\\
 P_n^1(\cdot\mid S)=P_n^0(\cdot\mid S)
 &\ \Longleftrightarrow\ R(z)\equiv\frac{\rho_1}{\rho_0}.
 \end{aligned}
                                                               \tag{SI2}
\]

This follows by dividing each survivor weight by its total mass. A common
factor can change survival probability while leaving the conditional law
unchanged. For the standard distortion, \(0\le\delta_i(h)<1\) and
\(\alpha_i(h)=m_i(h,B_i(h))\) give good multiplier
\((1-\min(\alpha_i(h),\delta_i(h)))^{-1}\). A common threshold rule
depending on the actual observed prefix therefore preserves (SI1).
A rule depending on the whole current physical law can change the
effective threshold at the same good prefix; it changes the final
conditional law only when the product ratio in (SI2) is nonconstant.
Changing between threshold values both at least \(\alpha_i(h)\) has
no good-side effect.

For the local obstruction, let \(m\) be a fixed finite probability,
\(B\) a bad set of mass \(\alpha\), and \(q=fm\) a normalized law
with density \(0\le f\le g\), where \(1\le g<\infty\). Define
the available good capacity \(A=g(1-\alpha)\) and its unused mass
\(\Delta=\int_{B^c}(g-f)\,dm\). Then

\[
 \begin{gathered}
 \min_f q(B)=\beta:=\max(0,1-A),\qquad
 q(B)=1-A+\Delta,\\
 A\le1\ \Longrightarrow
 \left[q(B)=\beta+\Delta,\quad
 q(B)=\beta\ \Longleftrightarrow\ f=g\quad m\text{-a.e. on }B^c\right].
 \end{gathered}
                                                               \tag{SI3}
\]

Indeed \(q(B)=1-q(B^c)\) and \(q(B^c)\le A\). If \(A<1\),
the minimum is attained by density \(g\) on the good set and
\(\beta/\alpha\) on the bad set; if \(A\ge1\), use density
\((1-\alpha)^{-1}\) on the good set and zero on the bad set.
Both constructions also obey \(f\le1\) on the bad set, if that
additional constraint is imposed. Equality for \(A\le1\) forces the
nonnegative good deficit to vanish at every positive-mass good atom.
Consequently any reduction of good mass in a saturated row increases
its actual bad charge by exactly the same amount. If \(A_x\le1\) in
every compared row, at fixed old law \(\nu\) the one-step charge increment is
\(\mathbb E_\nu\Delta_x\); this is not a telescoping comparison
between chains whose intermediate physical laws differ.

The strict branch \(A>1\) has \(\beta=0\) and
\(q(B)=\Delta-(A-1)\). Zero bad charge then leaves unused capacity
\(A-1\) and does not force good-side saturation. With at least two
positive-mass good atoms, nonconstant zero-charge perturbations are
possible. The distinction between the global cap and the natural cap
is therefore essential.
For \(0\le\delta<1\),

\[
 \begin{aligned}
 g_{\rm global}&=(1-\delta)^{-1},
 &A_{\rm global}>1&\ \Longleftrightarrow\ \alpha<\delta,\\
 g_{\rm natural}&=(1-\min(\alpha,\delta))^{-1},
 &A_{\rm natural}&\le1,\qquad
 \beta=\frac{(\alpha-\delta)_+}{1-\delta}.
 \end{aligned}                                                 \tag{SI4}
\]

Under the natural cap, minimum bad charge fixes the good side in every
row, including uncharged rows. Under only the global cap, strictly
uncharged rows with at least two positive-mass good atoms can retain
zero bad charge while changing their good density; (KR1) deliberately
kept those rows fixed. In a saturated row,
changing the good transition requires increasing bad charge as in (SI3),
or relaxing the prior cap to allow compensating density increases.
Together with (SI2), these identify ways to change the supported law;
they do not establish a better numerical \(\Gamma\), a uniform family
bound, or unrestricted noncoverage.

The product and conditioning identities reuse `Erdos7.FiniteLaw.joint`,
`condition_prob`, and `Erdos7.ThreePrime.KernelChain.law` in the existing
`ConditionalComparison/ThreePrime` modules. The natural multiplier is
`Erdos7.outsideMultiplier_eq_natural` in `CappedGainDistortion`;
saturation is the finite instance of Mathlib's
`MeasureTheory.integral_eq_iff_of_ae_le`. These are ordinary consequences
of existing APIs, with no new Lean declarations.

### A common clean-path test blocks the natural-cap charge tradeoff

Fix one finite CS2 comb of height \(H\ge1\), its old probability
\(\mu\), and its complete original old inventory of \(K\le p-3\)
nonunit labels. Old forbidden cylinders may vary independently at every
depth. Besides the pure root0, the \(K\) spoke roots and spine root
\(p-2\), designate the remaining \(r=p-K-2\ge1\) roots. Their
union \(R\) is disjoint from every forbidden prefix, on every old row.
There can be additional clean roots; only this fixed subset is used.
Write \(\lambda_H=1-\sum_{e=1}^Hp^{-e}\), let \(m_x\) be the
normalized pure-survivor law, and put
\(\alpha_x=m_x(B_x)\), \(g_x=(1-\min(\alpha_x,\delta))^{-1}\),
\(\beta_x=(\alpha_x-\delta)_+/(1-\delta)\), with
\(0\le\delta<1\). Thus \(m_x(R)=r/(p\lambda_H)\),
\(\alpha_x<1\), and the BBMST law saturates all good points.

Allow the larger honest row domain
\(0\le\rho_x\le g_x\) on \(B_x^c\),
\(0\le\rho_x\le1\) on \(B_x\), and
\(\int\rho_x\,dm_x=1\). In particular its actual charge
\(b_x=\int_{B_x}\rho_x\,dm_x\) may exceed \(\beta_x\).
For fixed \(f\ge0,W>0\), minimize over this one kernel the maximum
of \(f\mathbb E L_T^2+W\mathbb E_\mu b_x\) over all complete tests.

Fix any old complete-test sequence \(A_0,\ldots,A_H\), independently
of the forbidden layouts. Choose a root uniformly among the designated
\(r\) roots, then an independent uniform suffix of length \(H-1\).
Put every depth-\(e\) original test label on the corresponding prefix
of this one path. This is one common finite mixture \(\pi\) of legal
tests, shared across all old rows. For a point in \(R\), its depth-\(j\)
prefix is selected with probability \(1/(rp^{j-1})\); outside \(R\)
no positive-depth test hits. Hence, using \(Q_H\) defined before (CS5),

\[
 F_{\pi,x}(y):=\mathbb E_{T\sim\pi}L_T(x,y)^2
 =A_0(x)^2+\frac p r Q_H(x)\mathbf1_R(y),\qquad
 Q_H=\sum_{\substack{0\le e,j\le H\\(e,j)\ne(0,0)}}
                      p^{-\max(e,j)}A_eA_j.
                                                               \tag{HC1}
\]

Set \(c_H=g_x/\lambda_H\),
\(d_x=fpQ_H(x)/r\), \(h_x=g_xr/(p\lambda_H)\), and
\(\tau_x=\min(h_x,\alpha_x-\beta_x)\). There is an exact row identity
for this fixed common mixture:

\[
 \min_{\rho_x}\left[f\int F_{\pi,x}\rho_x\,dm_x+Wb_x\right]
 =f\bigl(A_0(x)^2+c_HQ_H(x)\bigr)+W\beta_x
                     -\tau_x(d_x-W)_+.
                                                               \tag{HC2}
\]

To prove it, let \(u\) be the lost mass from \(R\) relative to
the saturated BBMST law, and \(v\) the lost mass from \(B_x^c\setminus R\).
The cap makes \(u,v\ge0\), and (SI3) gives
\(b_x=\beta_x+u+v\). Also \(u\le h_x\) and
\(u+v\le\alpha_x-\beta_x\), because bad density is at most1.
The objective change is exactly
\((W-d_x)u+Wv\). Its minimum is
\(-\tau_x(d_x-W)_+\), attained with \(v=0\), by moving either
zero mass or \(\tau_x\) from \(R\) to unused bad capacity.
Fractional atom densities permit that transfer even on a finite fibre.
If the unused bad capacity is zero, \(\tau_x=0\) and no transfer is
needed. If \(d_x<W\), equality with the BBMST value forces
\(u=v=0\), so every positive-mass good atom remains saturated.
Strict improvement against this fixed mixture occurs precisely when
\(\tau_x>0\) and \(d_x>W\).

At fixed \(H\) the old layout set is finite. Choose a sequence maximizing
the BBMST complete-test objective. By (CS5), each of its nested designated
clean-path tests attains the pair caps, so the mixture in (HC1) is
supported on BBMST-maximizing tests. If \(d_x\le W\) on every
positive-\(\mu\) row, (HC2) supplies a lower bound against every honest
kernel equal to the BBMST maximum. BBMST itself is feasible. Therefore

\[
 V_{\rm honest}(H)=V_{\rm BB}(H).
                                                               \tag{HC3}
\]

If all those row inequalities are strict, every honest minimizer agrees
with BBMST on all positive-mass good transitions. It has the same current
survivor subprobability and, when its mass is positive, conditioned law. Bad-side choices can still
differ; later policies that read them must be assessed under (SI1)--(SI2).
The common maximizing mixture is essential: improving one deterministic
test is insufficient to improve this maximum.

For a pointwise old-load bound \(A_e(x)\le R_0\), the full geometric
sum, without identifying layouts across depths, gives

\[
 Q_H(x)\le R_0^2\sum_{j=1}^H(2j+1)p^{-j}
 \le R_0^2\frac{3p-1}{(p-1)^2}.
 \quad
 W\ge\frac{fpR_0^2}{p-K-2}\frac{3p-1}{(p-1)^2}
 \ \Longrightarrow\ \text{(HC3) for every finite }H.
                                                               \tag{HC4}
\]

In the PG1 low315 comb at17, \(K=11\), \(R_0=12\), \(r=4\),
\(f=59/45\), and \(W=483\). All original \(11+12H\) forbidden
moduli and \(12(H+1)\) test labels are retained. Exactly,

\[
 d_x\le\frac{59}{45}\frac{17}{4}\,144\frac{25}{128}
       =\frac{5015}{32}<483,
 \qquad 483-\frac{5015}{32}=\frac{10441}{32}.
                                                               \tag{HC5}
\]

Thus allowing good-side mass reductions with their actual charge cost
cannot improve this family's complete-test objective at any finite
height, even with independent old layouts at every depth. This includes
the off-diagonal layouts left essential by (JL1)--(JL3). It does not
evaluate the remaining old-layout maximum or improve a global bound.
The cap here is the natural row cap: replacing it on uncharged rows by
the larger global cap invalidates \(u,v\ge0\) relative to BBMST and is
outside this obstruction. General original inventories with higher
3/5/7 powers and earlier11/13 labels need not admit these designated
clean roots. Changing the reference thresholds or the old law is also
outside this fixed-cap comparison. This is an ordinary finite saddle argument with a complete
geometric bound, not a new Lean theorem or a literature-priority claim.


### A global-cap perturbation improves the actual survivor law at every finite height

The natural-cap obstruction (HC3) does not persist when strictly uncharged
rows may use the global cap. There is an explicit actual-family construction
whose physical complete-test square and final supported \(\Gamma\) both
strictly decrease, with a lower bound on the gain independent of height.
This is a fixed low315 family, not a bound over unrestricted old inventories.

Use the canonical PG1 probability \(\mu\) on its75 actual old survivors,
with denominator \(D=1000000007\). In particular,
\(\mu(2)=13119398/D\) and \(\mu(314)=16622259/D=:\mu_*\).
For each finite \(H\ge1\), keep its11 original old forbidden classes and
add the CS2 comb at \(p=17\), with all old forbidden cylinders centered
at2. The ordered nonunit old divisors
\((3,5,7,9,15,21,35,45,63,105,315)\) have respective spokes1 through11;
the spine is15. Thus all \(11+12H\) forbidden moduli are distinct odd
integers, the period is \(315\cdot17^H\), and all \(12(H+1)\) original
test labels retain independent residues. Fix \(\delta=7/15\).

Write \(s_H=\sum_{e=1}^H17^{-e}\), \(\lambda_H=1-s_H\),
\(n(x)=\sum_{d>1,\,d\mid315}\mathbf1_{x\equiv2\bmod d}\), and
\(c_H(x)=[\max(1-(n(x)+1)s_H,\lambda_H(1-\delta))]^{-1}\).
This is the BBMST good density relative to current-coordinate Haar measure.
At \(x_*=314\), only the old divisor3 matches2, so \(n(x_*)=1\).
The entire current root2, assigned to old divisor5, is good there.
This row is strictly uncharged for every \(H\), and
\(c_H(x_*)=(1-2s_H)^{-1}\le8/7\).

Let \(R_H=\{12,13,14,15,16\}\) when \(H=1\), and
\(R_H=\{12,13,14,16\}\) when \(H\ge2\); put \(r_H=|R_H|\).
These whole roots are globally clean. Let \(U_{j,H}\) denote the uniform
probability on current points congruent to \(j\bmod17\). Change only
row \(x_*\), with \(t=1/8192\):

\[
 q'_H(x_*,\cdot)=q_H(x_*,\cdot)+tU_{2,H}
                   -\frac{t}{r_H}\sum_{j\in R_H}U_{j,H}.
                                                               \tag{GC1}
\]

Every donor root has mass \(c_H(x_*)/17\ge1/17>t/r_H\).
The global density cap relative to Haar is
\(C/\lambda_H\), where \(C=15/8\). The recipient's unused root
capacity is at least
\((15/8-8/7)/17=41/952>t\). Thus (GC1) is nonnegative, preserves
normalization and the old marginal, obeys the global cap, and changes
no bad mass or bad-subset bound. The final survivor mass is unchanged
and satisfies \(\rho_H\ge r_H/17\ge4/17>0\), using the globally
clean roots and \(c_H\ge1\). The two conditioned survivor laws differ on root2 above
\(x_*\). Keeping the natural cap on this row would forbid this change.

Here is a bound against every complete test, without enumerating its
residues or identifying its layouts across depths. For a test \(T\),
let \(A_e(x)\le12\) be its complete old load at depth\(e\), and let
\(z\) be the first digit of its original pure17 test. Denote by \(U_H(T)\)
the BBMST pair-cap value with these old layouts, attained by aligning all
current prefixes along one nested globally clean path:

\[
 U_H(T)=\mathbb E_\mu[A_0^2+c_HQ_H],\qquad
 U_H(T)\le V_{{\rm BB},H}:=\max_T\mathbb E_{\mu q_H}L_T^2.
                                                               \tag{GC2}
\]

For the restriction to actual survivors, the corresponding value is
\(U_H^S(T)=\mathbb E_\mu[(1-\beta_H)A_0^2+c_HQ_H]
\le\rho_H\Gamma_{{\rm BB},H}\). The same aligned test attains that cap value;
the positive-depth pair caps are unchanged. Every gap used below holds
for both physical and survivor-restricted square integrals.

First suppose \(z\notin R_H\). A spoke root is entirely bad on the
positive-mass old row2. On that row the Haar-density difference between
the good cap and the physical bad density is
\(\delta/[(1-\delta)11s_H]\ge14/11\). Its pure17 test and its
cross terms with the old baseline, whose load is at least1, lose at least
\(G_{\rm spoke}=3\mu(2)14/187\) from (GC2). Root0 is pure forbidden,
giving \(G_0=3/17\). If \(H\ge2\), the spine root contains the whole
pure forbidden depth-two cylinder, giving \(G_{\rm spine}=3/289\).
For the survivor restriction the spoke loses still more, so the same
lower bounds remain valid. These cases exhaust roots outside \(R_H\).

Next suppose \(z\in R_H\), but some depth-one test label active at
\(x_*\) has another root. Its intersection with the original pure17
label is empty, while the two ordered cap terms in (GC2) total at least
\(G_{\rm split}=2\mu_*/17\).

For either of these cases, a uniform probability inside any one current
root gives, for every test and every height,

\[
 \mathbb E_{U_{j,H}}L_T(x_*,\cdot)^2
 \le12^2\left(1+17\sum_{e\ge1}(2e+1)17^{-e}\right)
 =\frac{4977}{8}=:M.
                                                               \tag{GC3}
\]

Indeed each intersection with maximal positive depth\(e\) has conditional
mass at most \(17^{1-e}\). Discarding the removed nonnegative square
cost, (GC1) can increase the integral by at most \(\mu_*tM\).
Exact rational arithmetic gives, for all four gaps above,

\[
 G-\mu_*tM>\varepsilon,
 \qquad \varepsilon:=\frac{3\mu_*t}{5}
   =\frac{49866777}{40960000286720}>0.
                                                               \tag{GC4}
\]

It remains to handle \(z\in R_H\) when every depth-one label active
at \(x_*\) has root\(z\). Removing donor mass loses a shallow square
increment of at least
\(\mu_*t(2A_0A_1+A_1^2)/r_H\ge3\mu_*t/r_H\), since both old
loads include their unit label. The baseline square cancels because the transferred masses total zero.
The recipient has only the baseline and possible deeper test hits. Let \(a_e\le12\) count the labels
active at \(x_*\) whose current prefix starts with2, for \(e\ge2\),
and put \(S=\sum_{e=2}^H17^{-e}a_e\). All these are original labels.
For any such nonnegative sequence, grouping pairs by their earlier depth
and bounding later coefficients by12 gives

\[
 \sum_{e,j=2}^H17^{-\max(e,j)}a_ea_j
 \le12\left(1+\frac2{16}\right)S.
                                                               \tag{GC5}
\]

Consequently the recipient's extra square cost is at most
\(\mu_*t\,17[2A_0+12(18/16)]S\le\mu_*t(1275/2)S\).
But every one of these deeper labels is disjoint from the original
pure17 test on row \(x_*\). Their missing cross terms already give
\(U_H(T)-\mathbb E L_T^2\ge2\mu_*c_H(x_*)S\ge2\mu_*S\).
Since \(t(1275/2)<2\), this gap absorbs the entire recipient gain.
The remaining donor decrease is at least \(\varepsilon\), as \(r_H\le5\).
This also covers \(H=1\), when \(S=0\). No infinite-family minimax
exchange or finite-height truncation is used.

Taking maxima over the original complete test domain in all three cases
therefore proves, for every finite \(H\ge1\),

\[
 V'_H\le V_{{\rm BB},H}-\varepsilon,
 \qquad
 \Gamma'_H\le\Gamma_{{\rm BB},H}-\frac{\varepsilon}{\rho_H}.
                                                               \tag{GC6}
\]

The second statement follows by applying the same argument to the killed
subprobabilities and dividing by their common positive mass. In particular
this is an improvement of the true supported test supremum, not merely
of a bound before final conditioning. Any objective \(fV+Wb\), with
\(f>0\), improves by at least \(f\varepsilon\), since charge is fixed.
The entire proof uses one explicitly defined probability before any test
is chosen. It refutes optimality of the BBMST law in this larger global-cap
class at every finite height. It does not give a gain uniform over all
forbidden families, treat unrestricted old3/5/7 and11/13 inventories, or
prove unrestricted noncoverage. These are ordinary probability and
original-label pair estimates, not new Lean declarations.

The [exact verifier](verify_pg1_global_cap_improvement.py) binds the canonical
PG1 source and reconstructs the [certificate](pg1_global_cap_improvement_certificate.json).
It checks the rational constants, cap slack and gap margins, five exact
height fixtures, and 22,950 literal supported CRT points across heights1
and2 under both laws, including unchanged charge and an actual change in
the conditioned survivor law. Run from any directory:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_pg1_global_cap_improvement.py
```

These finite arithmetic checks do not enumerate the complete test domain
or establish the universal height quantifier; those are proved in
(GC2)--(GC6), including the full geometric tail.


### Higher moments retain the full old inventory in a law-changing perturbation

A bounded second moment does not justify replacing the pointwise bound12
in (GC5) by its square root. To see this on actual original labels, let
\(M_N=315\cdot3^N\), retain the PG1 low family, and put every additional
old forbidden class at0. Each new modulus contains27, so these new classes
lie in the already forbidden class0 modulo3. Lift PG1 uniformly to this
period, and condition only for this comparison on the slice
\(E=\{x:x\equiv314\pmod{315}\}\). Its probability \(\eta_N\) is
uniform on \(3^N\) points. For every old divisor choose test residue314.
The resulting load is \(A_N=4(3+Z_N)\), where
\(\Pr(Z_N\ge j)=3^{-j}\) for \(1\le j\le N\). Nested prefix
intersections simultaneously attain every pair cap, so the exact maximum
second moment over all complete old tests is

\[
 \Gamma(\eta_N)=208-16(N+4)3^{-N}\le208.
 \quad
 \frac{\mathbb E_{\eta_N}[A_N\mathbf1_{C_N}]}{\eta_N(C_N)}
 =4(N+3),\qquad C_N=\{x:x\equiv314\pmod{3^{N+2}}\}.
                                                               \tag{FI1}
\]

Here \(\eta_N(C_N)=3^{-N}>0\). Thus no constant depending only on
that second-moment bound controls all these conditional loads. The
indicator of \(C_N\) is itself an original old label, and multiplying
it by a current prefix uses the original label \(3^{N+2}17^e\).
This obstruction concerns the proposed moment substitution, not (GC6).

A third-moment tail supplies a different estimate. Define a full old period

\[
 M=3^{N_3+2}5^{N_5+1}7^{N_7+1}11^{A_{11}}13^{A_{13}},\qquad
 N_3,N_5,N_7\ge0,\quad A_{11},A_{13}\ge1.
                                                               \tag{FI2}
\]

Keep the eleven PG1 forbidden classes and add0 modulo11 and13.
Complete the forbidden old inventory to one class for every \(d\mid M\),
\(d>1\), as follows. For any remaining \(d\) divisible by11 or13,
use residue0; its class lies in a corresponding pure forbidden root.
For any remaining divisor using only3,5,7, put
\(d_0=\gcd(d,315)\) and use the PG1 forbidden residue \(a_{d_0}\)
also modulo\(d\). It lies in the old forbidden class modulo\(d_0\).
The old survivor set is therefore exactly the PG1 survivors, arbitrary
extra3/5/7 digits, and nonzero first11/13 digits with arbitrary suffixes.
Let \(\nu\) be PG1 times those uniform independent coordinates.
This is one actual supported probability; in particular
\(\nu(E)=\mu_*=16622259/1000000007\).

At17, for every \(1\le e\le H\), keep the pure and eleven low-cofactor
CS2 classes from (GC1). Every other original label \(d17^e\),
\(d\mid M\), is forbidden at residue0, hence already lies in the pure
forbidden root0 modulo17. This completes the actual forbidden inventory
to all divisors greater than one of \(M17^H\), without changing the
current bad masks from the low comb. All original complete-test labels
remain independent, including the higher old powers and11/13 cofactors.
The specified extra forbidden residues are part of this construction;
they are not arbitrary-residue hypotheses.

Use the same clipping parameter \(\delta=7/15\). Its actual current
BBMST kernel \(q_0\) depends only on the low point. On every row in
\(E\), transfer mass \(t=2^{-24}\) from the designated clean roots
\(R_H\), equally, to the whole root2 as in (GC1). Call the kernel
\(q_t\). The cap and support checks of (GC1) apply on each such row;
old marginals, bad masses and survivor normalizers remain unchanged.

For completeness, the higher-moment bound keeps every original label.
Let \(G_p\) be independent nonnegative geometric variables with
\(\Pr(G_p\ge j)=p^{-j}\). For11 and13 also use independent
\(B_p\) of probability \(1/(p-1)\). Conditional on any fixed low315
point, and with the current coordinate uniform in a specified first root,
the complete-test moments of orders \(k=2,3\) are bounded by

\[
 Y_{\rm root}=(3+G_3)(2+G_5)(2+G_7)
 \bigl(1+B_{11}(1+G_{11})\bigr)
 \bigl(1+B_{13}(1+G_{13})\bigr)(2+G_{17}),\qquad
 K_k=\mathbb E[Y_{\rm root}^k],
\]

where the expectation is of the kth power of the displayed random
product. To prove the bound, expand the kth power as ordered original-label
tuples. Compatible prefixes intersect at their greatest depth; incompatible
ones have zero mass. Conditional on the low point, every tuple is bounded
by the corresponding product of prefix caps. Nested test residues attain
all those caps in the enlarged infinite suffix model. Summing gives the
stated geometric product. Completing finite heights adds only nonnegative
terms. This comparison is for test moments; the actual forbidden masks
and law have not been centered or changed. Exact values are

\[
 K_2=\frac{638455140323}{248832000},\qquad
 K_3=\frac{104829447952912991}{402653184000},\qquad
 17tK_3<\frac3{10}.
                                                               \tag{FI3}
\]

Fix an arbitrary complete test \(T\), let \(z\) be the root of its
original pure17 label, and keep all its old layouts. Their pair-cap upper
value \(U(T)\), as in (GC2), is still attained by a single nested clean
path. The size of the old inventory is irrelevant to this attainment,
since all its additional forbidden classes were placed in the pure root.
For the killed law use the same baseline replacement
\((1-\beta)A_0^2\) as after (GC2).

If \(z\notin R_H\), the spoke, pure-root or spine gaps from (GC4)
remain \(3\mu(2)14/187\), \(3/17\) or \(3/289\).
The increase under the transfer is at most \(\mu_*tK_2\). Each gap
exceeds that quantity plus \(3\mu_*t/10\).

If \(z\in R_H\), the donor decrease after canceling the old-only
baseline is at least \(3\mu_*t/r_H\): use just the original pure17
label and its two ordered cross terms with the unit label. At the recipient
write its complete load as \(X=A_0+Z\), where \(Z\) includes all
positive17-depth labels that hit there. Their first root is2, so each
is disjoint from the pure17 test on root\(z\). Their missing ordered
pairs supply a cap deficit at least \((2/p)\mu_*\mathbb E Z\),
where \(p=17\) and this expectation uses \(\nu(\cdot\mid E)\)
and the uniform recipient root. The recipient square increment is
\(\mu_*t\mathbb E(2A_0Z+Z^2)\). Pointwise,

\[
 t(2A_0Z+Z^2)-\frac2pZ
 \le tX^2\mathbf1_{X>1/(pt)}\le pt^2X^3.
                                                               \tag{FI4}
\]

Indeed the left side is \(Z[t(2A_0+Z)-2/p]\), nonpositive when
\(X\le1/(pt)\); otherwise it is at most \(tX^2\).
The final inequality is the elementary third-moment tail estimate.
Thus the missing pairs pay for the recipient gain except at a cost
at most \(\mu_*pt^2K_3\). By (FI3), the net decrease is at least
\(3\mu_*t/5-3\mu_*t/10\). No conditional pointwise old-load bound,
depth-one alignment assumption, or omission of a high label is needed.

Taking maxima, both the physical and killed complete-test suprema decrease
by at least

\[
 \varepsilon_0=\frac{3\mu_*t}{10}
 =\frac{49866777}{167772161174405120}>0.
                                                               \tag{FI5}
\]

This bound is uniform over every finite exponent vector in (FI2) and every
finite \(H\ge1\). The conditioned maximum decreases by at least
\(\varepsilon_0/\rho\), with the common \(\rho\ge4/17\).
The conclusion concerns all original test labels on this explicitly
constructed family, not a restriction to its low315 tests.

### Rare old cylinders remove every globally clean root without losing the improvement

The full-inventory improvement is stable when the actual current forbidden
masks change on a sufficiently small old event. Keep \(\nu\), the original
inventory, and all pure17 classes fixed. Change any of the mixed forbidden
residues, subject to the requirement that the resulting bad mask on the fixed
pure-survivor base equals the base mask for every old row outside \(F\). Write \(q=\nu(F)\).
Let \(\widetilde q_0\) be the new family's actual BBMST kernel and let
\(\widetilde q_t\) apply the same transfer on \(E\setminus F\),
with no transfer on \(F\). This is feasible: outside \(F\) the original
support and capacity checks apply; on \(F\) the new normalized BBMST
kernel is retained. The pair have equal old marginals, actual bad charge
and survivor mass, with
\(\widetilde\rho\ge4(1-q)/17>0\) when \(q<1\).

All four physical kernels have density at most2 relative to the uniform
current Haar coordinate: the pure survivor mass is at least15/16 and
the global pure-base cap is15/8. Their killed restrictions also have
this cap. Each new-versus-base comparison is supported on old rows\(F\),
and its pointwise density difference has absolute value at most2.

Under \(\nu\) times current Haar measure, the same ordered-tuple
argument bounds every complete-test fourth moment by

\[
 \begin{aligned}
 Y_{\rm Haar}&=(3+G_3)(2+G_5)(2+G_7)
 (1+B_{11}(1+G_{11}))(1+B_{13}(1+G_{13}))(1+G_{17}),\\
 K_4^{\rm Haar}&=\mathbb E[Y_{\rm Haar}^4]
 =\frac{3528039728534972593}{637009920000}.
 \end{aligned}
                                                               \tag{FI6}
\]

As in (FI3), the power is inside the expectation. The current Haar factor
is \(1+G_{17}\), whose fourth moment is17595/8192; it differs from
the conditioned-root factor in (FI3). Cauchy--Schwarz gives, uniformly over
all complete tests, the following bound for each physical or killed
new-versus-base comparison:

\[
 |J_{\rm new}(T)-J_{\rm base}(T)|
 \le2\int\mathbf1_F L_T^2\,d(\nu\otimes\lambda)
 \le2\sqrt{qK_4^{\rm Haar}}=:\eta.
                                                               \tag{FI7}
\]

Apply (FI7) once to the perturbed kernels and once to the BBMST kernels,
using the same full test domain throughout. Combining with (FI5), the
new-family physical and killed suprema improve by at least
\(\varepsilon_0-2\eta\). In particular,

\[
 q\le3^{-64},\qquad
 64K_4^{\rm Haar}<3^{64}\varepsilon_0^2
 \quad\Longrightarrow\quad
 \widetilde\Gamma_t
 \le\widetilde\Gamma_0-\frac{\varepsilon_0}{2\widetilde\rho}.
                                                               \tag{FI8}
\]

The same positive \(\varepsilon_0/2\) saving holds before conditioning.
This estimate uses comparisons with a fully evaluated geometric moment,
not an assumption that a pair-cap upper bound for the new masks is attained.

There are actual families satisfying (FI8) with no globally clean current
root. Take \(N_3\ge64\), set \(Q=3^{66}\), and let
\(F=\{x:x\equiv314\pmod Q\}\). Under \(\nu\), its probability
is \(\mu\{x\equiv314\pmod9\}3^{-64}\le3^{-64}\), independently
of the higher physical heights. At current depth one, replace just the
five previously redundant mixed classes with old cofactors

\[
 (Q,5Q,7Q,35Q,11Q)
\]

by the CRT classes with old residues314 and respective17 roots
\((12,13,14,15,16)\). Every new old cylinder lies in \(F\); the
removed residue-zero current classes were contained in the pure forbidden
root, so the masks are unchanged outside \(F\). The five moduli are
pairwise distinct and present in the full inventory for every allowed
height. Their old cylinders have positive \(\nu\)-mass, witnessed by
old point314, whose first11 and13 digits are6 and2, both nonzero.
Root0 is already pure forbidden; every spoke1 through11 is bad on the
positive-mass low row2; these five additional classes put forbidden mass
in each other root. Thus no first-level cylinder is globally clean,
including at height one, and this remains so for every finite height.
All original moduli and all their test labels are retained.

This gives a uniform actual-law improvement for a full-inventory,
arbitrary-height family with no globally clean root. Its extra residues
and its small old-event budget are specified hypotheses. No improvement
uniform over arbitrary old/current residues, no improved unrestricted
continuation constant, and no unrestricted noncoverage theorem follow.
The arguments are ordinary moment and CRT proofs; no Lean declaration or
literature-priority claim is made.

The moment estimates reuse the original-label saturated-prefix expansion
(SH19) and the common clean-path comparison (GC2); (FI7) is the finite
Cauchy--Schwarz inequality, also supplied by pinned Mathlib's
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`. BBMST's normalized
clipping kernel and actual-measure optimization remain the public inputs
([1811.03547](https://arxiv.org/abs/1811.03547), section2;
[1901.11465](https://arxiv.org/abs/1901.11465), section5.3). The cubic
absorption and its full-inventory arithmetic construction are the ordinary
proof above; no generic moment or conditioning wrapper is added to Lean.

The [exact moment and family verifier](verify_pg1_lifted_global_cap.py)
reconstructs the [certificate](pg1_lifted_global_cap_certificate.json).
It checks the PG1 source, rational second/third/fourth moment factors,
finite original-label tuple sums with their explicit tails, capacity and
strict-gain constants, and the rare-cylinder CRT witnesses. The symbolic
proofs (FI1)--(FI8) establish the full height and test quantifiers; the
finite arithmetic fixtures do not enumerate that domain. Reproduce from
any directory with:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_pg1_lifted_global_cap.py
```

### Joint mask stability permits arbitrary high old and current residues

The old-event hypothesis in (FI8) can be replaced by an averaged joint
mask budget. This also permits arbitrary high old forbidden residues,
using one explicitly conditioned old law. The fixed finite core remains
a hypothesis; this is not a uniform improvement over arbitrary cores.

Retain the finite original inventory, reference old probability \(\nu_0=\nu\)
and pure17 comb of (FI2). Let \(\ell_H\) be uniform current Haar measure,
\(\lambda_H=\ell_H(P_H)\ge15/16\) the pure-survivor mass, and
\(m_H=\ell_H(\cdot\mid P_H)\). For the reference and new mixed masks
\(B_x,B'_x\subseteq P_H\), set

\[
 h(x)=\ell_H(B_x\mathbin\triangle B'_x),\qquad
 d(x)=m_H(B_x\mathbin\triangle B'_x)=h(x)/\lambda_H,\qquad
 \epsilon=\mathbb E_{\nu_0}h(x).
                                                               \tag{AM1}
\]

The old projection of this symmetric difference can have full mass.
Neither (AM1) nor the estimates below require that projection to be small.
All budgets are measured using \(\nu_0\), before any old conditioning.

First the BBMST kernel is Lipschitz in its actual bad mask. On any finite
probability space \((P,m)\), fix \(\delta=7/15\), \(C=15/8\),
and write its physical and killed densities as

\[
 k_B=a(\alpha)\mathbf1_{B^c}+b(\alpha)\mathbf1_B,\quad
 k_B^-=a(\alpha)\mathbf1_{B^c},\quad \alpha=m(B),\qquad
 a(u)=\frac1{1-\min(u,\delta)},\quad
 b(u)=\begin{cases}C(u-\delta)_+/u,&u>0,\\0,&u=0.\end{cases}
\]

Both coefficients are increasing, \(a\le C\), \(b\le1\), and
\(\int k_B\,dm=1\). If \(B\subseteq B'\), the negative part of
\(k_{B'}-k_B\) is supported on \(B'\setminus B\), where its absolute
value is at most \(C\). Equal total masses therefore give the physical
bound below. For the killed densities, the negative part has mass at most
\(C(\alpha'-\alpha)\), and the positive part has mass
\((1-\alpha')[a(\alpha')-a(\alpha)]\le C(\alpha'-\alpha)\),
as follows directly in the three cases separated by \(\delta\).
For arbitrary masks, apply the nested bounds through \(B\cup B'\):

\[
 \|k_{B'}-k_B\|_{L^1(m)},\quad
 \|k_{B'}^--k_B^-\|_{L^1(m)}
 \le2C\,m(B\mathbin\triangle B').
                                                               \tag{AM2}
\]

In the original current Haar coordinate, integrating (AM2) over old rows
bounds each physical or killed reference/new BBMST difference by
\((2C/\lambda_H)\epsilon\le4\epsilon\).

The improving transfer itself can be repaired. Keep \(t=2^{-24}\),
\(E=\{x\equiv314\pmod{315}\}\) and the roots \(R_H\) from (FI3).
On a row in \(E\) with \(d(x)\le1/68\), replace each uniform root
probability \(U_{j,H}\), for \(j\in\{2\}\cup R_H\), by its
conditioning \(U'_{j,x,H}\) on the new good set. Define

\[
 q'_{t,x}=q'_{0,x}+tU'_{2,x,H}
                  -\frac{t}{r_H}\sum_{j\in R_H}U'_{j,x,H}.
                                                               \tag{AM3}
\]

Here \(q'_0\) is the new mask's actual BBMST kernel. On all other rows
use \(q'_t=q'_0\). This rule is fixed before selecting any test.
Every indicated root was wholly good in the reference row. Its new good
Haar mass is at least \(1/17-h(x)\ge3/68\). The reference good Haar
mass on \(E\) is at least \(7/8\), so the new mass is at least
\(117/136\). Also \(\alpha'\le1/15+1/68<\delta\), and the
new BBMST row is uncharged. Its good Haar density \(c'\) satisfies
\(1\le c'\le136/117\). The following strict margins prove feasibility:

\[
 \frac{136}{117}+\frac{68}{3}t<C,\qquad
 1-\frac{17}{3}t>0.
\]

The first bounds the recipient density below the allowed Haar cap
\(C/\lambda_H\); the second bounds the remaining donor density, using
\(r_H\ge4\). The transfer has zero total mass and is entirely good.
Thus it preserves each old marginal, the new family's actual bad charge,
and its survivor mass. It does not posit a separate test-dependent law.
All physical and killed kernels still have Haar density at most2.

Here is the quantitative repair error. If \(h_j\) is the new bad Haar
mass removed from root \(j\), then
\(\|U'_{j,x,H}-U_{j,H}\|_1=34h_j\). The roots are disjoint, so on
retained rows the change in the signed transfer is at most \(34t h(x)\).
On skipped rows in \(E\) it is \(2t\le136t d(x)\). Combining these
disjoint row cases gives at most \(136t\mathbb E_{\nu_0}d\).
The signed transfers are supported on the respective good sets, so this
same comparison applies to physical and killed kernels. With (AM2),

\[
 \|q'_t-q_t\|_1,\quad\|(q'_t)^--q_t^-\|_1
 \le A\epsilon,\qquad
 A=4+\frac{2176}{15}t=\frac{7864337}{1966080}<5.
                                                               \tag{AM4}
\]

These are joint-law norms under the unchanged \(\nu_0\).
For every complete original test \(T\), (FI6) supplies
\(\mathbb E_{\nu_0\otimes\ell_H}L_T^4\le K_4^{\rm Haar}\).
If a density difference has absolute value at most2 and \(L^1\) norm
at most \(D\), Cauchy--Schwarz bounds its test-square integral by
\(\sqrt{2D K_4^{\rm Haar}}\). Consequently the two comparisons needed
to transfer (FI5) cost at most
\((\sqrt8+\sqrt{10})\sqrt{K_4^{\rm Haar}\epsilon}
\le6\sqrt{K_4^{\rm Haar}\epsilon}\). This bound is uniform over all
test residues and all finite heights, with no truncated test domain.
The new common survivor mass is at least \(4/17-\epsilon\): every
reference row has good Haar mass at least \(4/17\), the new mask removes
at most \(h(x)\) of it, and BBMST good Haar density is at least one.

Old high residues may also change. Let \(S\) be the event that the old
point avoids all new old forbidden classes, set
\(q=\nu_0(S^c)\), and use the single supported probability
\(\nu_S=\nu_0(\cdot\mid S)\). Assume \(q\le1/2\).
For either fixed new row kernel in (AM3), the joint density change caused
by \(\nu_0\to\nu_S\) has \(L^1\) norm at most \(2q\).
Its absolute value relative to \(\nu_0\otimes\ell_H\) is at most2:
on \(S^c\) it is the old density, and on \(S\) it is that density
times \(q/(1-q)\). This bounds the difference, although the conditioned
joint density itself can exceed2. Each physical or killed test-square
comparison costs at most \(2\sqrt{qK_4^{\rm Haar}}\).
The two maxima therefore lose at most \(4\sqrt{qK_4^{\rm Haar}}\).

Let \(V_{S,0},V_{S,t}\) be the new family's physical maxima under
\(\nu_S q'_0,\nu_S q'_t\), and let \(V^-\) denote their killed
maxima. Combining the comparisons gives both inequalities

\[
 \begin{aligned}
 V_{S,t}&\le V_{S,0}-\varepsilon_0
       +6\sqrt{K_4^{\rm Haar}\epsilon}+4\sqrt{K_4^{\rm Haar}q},\\
 V^-_{S,t}&\le V^-_{S,0}-\varepsilon_0
       +6\sqrt{K_4^{\rm Haar}\epsilon}+4\sqrt{K_4^{\rm Haar}q}.
 \end{aligned}
                                                               \tag{AM5}
\]

Their actual bad charges agree pointwise, and their common survivor mass
satisfies
\(\rho_S\ge(4/17-\epsilon-q)/(1-q)\).
In particular, the exact constants in (FI5)--(FI6) satisfy

\[
 \theta=2^{-100},\qquad
 400K_4^{\rm Haar}\theta<\varepsilon_0^2.
 \quad
 q,\epsilon\le\theta
 \ \Longrightarrow\quad
 \Gamma_{S,t}\le\Gamma_{S,0}
              -\frac{\varepsilon_0}{2\rho_S},\qquad \rho_S>0.
                                                               \tag{AM6}
\]

The physical and killed maxima each improve by at least
\(\varepsilon_0/2\). The conditioning is on actual new old survivors;
the two laws being compared have the same old marginal \(\nu_S\).

The pure17 residues need not remain fixed above the finite core either.
For a new pure-survivor set \(P'_H\), its mass is still at least
\(15/16\): there is only one pure forbidden class at each positive
17-depth. In this paragraph let \(D_x,D'_x\) be the raw mixed unions
before restriction to a pure-survivor set, and define

\[
 \kappa=\ell_H(P_H\mathbin\triangle P'_H),\quad
 \eta=\mathbb E_{\nu_0}\ell_H(D_x\mathbin\triangle D'_x),\quad
 \zeta=\kappa+\eta.
\]

The symmetric difference of the full good sets
\(P_H\setminus D_x\) and \(P'_H\setminus D'_x\) has Haar mass
\(h_G(x)\le\kappa+\ell_H(D_x\mathbin\triangle D'_x)\).
To compare the two actual BBMST kernels, first change the pure probability
while holding the raw mixed set fixed, then change that mixed set.
The pure probabilities have \(L^1\) distance
\(r\le(32/15)\kappa\). For a fixed bad set their bad probabilities
therefore differ by at most \(r/2\). The coefficients \(a,b\) in
(AM2) have Lipschitz constants at most \(225/64,225/56\), respectively,
including the break at \(\delta\). Decomposing the kernel difference
into a change of probability and a change of coefficients gives, for both
physical and killed kernels,

\[
 \|q_{m',D}-q_{m,D}\|_1
 \le\left(C+\frac{225}{112}\right)r
 =\frac{435}{112}r\le4r.
\]

Here \(435/112<4\), and when \(r=0\) the norm is zero.
Together with (AM2), the joint new/reference BBMST difference is at most
\((128/15)\kappa+4\eta\le9\zeta\).
Now apply (AM3) on rows in \(E\) for which \(h_G(x)\le1/68\),
conditioning each selected root on the full new good set. The same
\(117/136\) good-mass bound makes the row uncharged, since
\(\alpha'\le1-117/136<\delta\). The same capacity margins apply.
The repair difference is at most \(136t\mathbb E h_G\), so the
candidate physical and killed differences are at most
\((9+136t)\zeta\le10\zeta\), since \(9+136t<10\).
Every current row kernel again has Haar density at most2.
The two current square comparisons cost at most
\((\sqrt{18}+\sqrt{20})\sqrt{K_4^{\rm Haar}\zeta}
\le9\sqrt{K_4^{\rm Haar}\zeta}\).
Combining with the same old conditioning gives

\[
 \begin{gathered}
 V_{S,t}\le V_{S,0}-\varepsilon_0
       +9\sqrt{K_4^{\rm Haar}\zeta}+4\sqrt{K_4^{\rm Haar}q},\\
 V^-_{S,t}\le V^-_{S,0}-\varepsilon_0
       +9\sqrt{K_4^{\rm Haar}\zeta}+4\sqrt{K_4^{\rm Haar}q},\\
 676K_4^{\rm Haar}2^{-100}<\varepsilon_0^2,\qquad
 q,\zeta\le2^{-100} \Longrightarrow\quad
 \Gamma_{S,t}\le\Gamma_{S,0}-\frac{\varepsilon_0}{2\rho_S},\qquad
 \rho_S\ge\frac{4/17-\zeta-q}{1-q}>0.
 \end{gathered}
                                                               \tag{AM7}
\]

Here both compared kernels use the new full pure-survivor base and the
same actual old probability \(\nu_S\). This extension changes the
pure normalization explicitly; it does not silently count pure holes as
mixed holes on the old base.

This budget holds for arbitrary forbidden residues beyond an explicit
finite exponent box. For every period in (FI2) and current height \(H\),
keep the reference forbidden residue on each original label whose six
prime exponents are all at most65. On every other original label allow an
arbitrary residue, including old labels, pure17 labels and mixed labels.
Keep every original test label and its independent test residue.

The reference old probability has density, relative to uniform old Haar,
at most

\[
 C_{\rm old}=315\max_x\mu(x)\frac{11}{10}\frac{13}{12}
 =\frac{49916643777}{8000000056}.
\]

For a common box depth \(b\), define the complete geometric sums

\[
 \begin{aligned}
 S_\infty&=\prod_{p\in\{3,5,7,11,13\}}\frac p{p-1}
          =\frac{1001}{384},\\
 S_b&=\prod_{p\in\{3,5,7,11,13\}}
             \frac p{p-1}(1-p^{-(b+1)}),\\
 T_{\rm old}(b)&=S_\infty-S_b,\qquad
 T_{\rm pure}(b)=\frac{17^{-b}}{16},\\
 T_{\rm mixed}(b)&=\frac{S_\infty-1}{16}
                    -\frac{(S_b-1)(1-17^{-b})}{16}.
 \end{aligned}
\]

These are sums over all original labels outside the box, with old depth
starting at zero and current depth starting at one; \(d=1\) is excluded
only from the mixed sum, because its pure labels have their own sum.
They majorize every finite physical exponent vector by adding nonnegative
terms. For old labels only the new classes can delete reference mass.
For current labels, the symmetric difference of the unions lies in the
union of all removed and added classes. The actual cylinder cap
\(\nu_0(a\bmod d)\le C_{\rm old}/d\) and CRT therefore give

\[
 q\le C_{\rm old}T_{\rm old}(b),\qquad
 \zeta\le2T_{\rm pure}(b)+2C_{\rm old}T_{\rm mixed}(b).
                                                               \tag{AM8}
\]

At \(b=65\), exact rational arithmetic gives both right sides less
than \(2^{-100}\). Their ratios to \(2^{-100}\) are respectively
less than0.668 and0.084. Thus (AM7) applies to **every assignment outside
this fixed core**, uniformly over all finite heights, with gain at least
\(\varepsilon_0/(2\rho_S)\) in the actual conditioned supremum.
The full tails have been evaluated, not discarded; no enumeration of a
large but finite height substitutes for this argument.

The stronger joint-mask condition has examples beyond the small-old-event
condition. For \(H\ge67\), change the two original classes with labels
\(3\cdot17^{66}\) and \(3\cdot17^{67}\) to old residues1 and2
modulo3, respectively, and current residue12 at their respective depths.
Every reference old survivor has residue1 or2 modulo3. Root12 was globally
clean, so every old row gains a forbidden current point. The old projection
of the changed mask is therefore the entire old support. Both labels lie
outside the exponent65 core, so (AM8) still bounds their small joint mass.
This construction is an illustration of the strict extension, not an
extra assumption in the arbitrary-tail conclusion.

The remaining restrictions matter. The six allowed primes are fixed and
the original finite core residues are specified by (FI2); arbitrary cores
and additional prime support remain outside this result. The supported old
law is the explicitly constructed \(\nu_S\), not an unspecified prior
BBMST output. Its quantitative reference cylinder cap is used in (AM8),
and its reference fourth moment is used in (AM5)--(AM7). No better bound
for the unrestricted17/19 continuation follows merely from this local
strict improvement.

The proof reuses the original-label moment expansion (FI6), the actual
BBMST clipping coefficients, finite conditioning and Cauchy--Schwarz.
Pinned Mathlib provides `ProbabilityTheory.cond_apply` and
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`; these standard
primitives are not presented as new Lean declarations. The repaired
probability and its full original-label comparison above are ordinary
mathematical proofs. They have not been formalized in Lean.

### The same complete second moment can hide an unbounded fourth moment

The fourth-moment hypothesis in (AM5)--(AM7) cannot be replaced by a
bound on the complete original-test second moment alone, even with an
unchanged exact value. For \(N\ge2\), take every original old modulus
\(3^j\), \(1\le j\le N\), with forbidden residue1. These distinct
odd classes have union exactly1 modulo3. Let \(\beta_N\) be uniform on
the actual survivors \(x\not\equiv1\pmod3\), and define

\[
 \nu_{N,u}=(1-u)\beta_N+u\delta_0,\qquad 0\le u\le1.
\]

Every original divisor, including the unit divisor, retains an independent
test residue. A cylinder at depth \(j\ge1\) has \(\nu_{N,u}\)-mass
at most \((1-u)/(2\cdot3^{j-1})+u\), attained by the zero cylinder.
Expanding the kth power of the complete load into ordered original-label
tuples, an intersection is empty or a cylinder at the maximum depth.
The coherent zero tests attain all those caps simultaneously. Thus

\[
 \Gamma_k(\nu_{N,u})=(1-u)B_{k,N}+u(N+1)^k,\qquad
 B_{k,N}=1+\sum_{j=1}^N
                 \frac{(j+1)^k-j^k}{2\cdot3^{j-1}}.
\]

In particular \(B_{2,N}=4-(N+2)/(2\cdot3^{N-1})<4\). Put

\[
 u_N=\frac{5-B_{2,N}}{(N+1)^2-B_{2,N}}.
 \qquad
 \Gamma_2(\nu_{N,u_N})=5,\qquad
 \Gamma_4(\nu_{N,u_N})>(N+1)^2\longrightarrow\infty.
                                                               \tag{AM9}
\]

Indeed \(0<u_N<1\) and \(u_N>1/(N+1)^2\); the atom at zero alone
supplies the displayed fourth-moment lower bound. These laws give positive
weight to every actual old survivor. This excludes any height-uniform
fourth-moment bound depending only on \(\Gamma_2\) for arbitrary
supported old probabilities. It does not assert that these spike laws are
produced by the prior BBMST kernels. Their Haar density cap is at least
\(3^Nu_N>3^N/(N+1)^2\), so they violate the extra uniform domination
used in (AM8). The original-label base moment formula is the same geometric
prefix calculation as (FI3); the added spike keeps the second maximum
exactly fixed while forcing the higher maximum to diverge.

The [joint-mask and complete-tail verifier](verify_average_mask_tails.py)
reconstructs its [exact certificate](average_mask_tails_certificate.json)
from the pinned FI inputs. It checks the rational margins and full tail
sums, all65536 ordered masks on an eight-point space through165 intersection
types, literal current repair and pure-base comparisons, and the original-label
full-projection example. For (AM9), it enumerates all27 and729 independent
test layouts at heights2 and3; the unbounded conclusion follows from the
ordered-tuple proof above. Reproduce from any directory with:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_average_mask_tails.py
```

## Actual BB kernels with fixed old second moment need not be uniformly continuous

The obstruction in (AM9) persists when both current kernels are actual
BBMST kernels for their respective forbidden masks. Keep its old family,
old probability \(\nu_N\), and put \(n=N+1\),

\[
 w_N=\nu_N(\{0\})
     =u_N+\frac{1-u_N}{2\cdot3^{N-1}},\qquad
 w_N\to0,\qquad w_Nn^2>1.
\]

Add the pure forbidden class zero modulo17 and every mixed original
class zero modulo \(3^j17\), \(1\le j\le N\). All mixed classes
are redundant inside the pure class. The actual pure-survivor BB kernel
is therefore uniform on roots1 through16 in every old row. In a second
family change only the original class labelled \(3^N17\) to the CRT
residue \((0\bmod3^N,3\bmod17)\). Only old row zero acquires a mixed
bad root, of pure-base mass \(1/16<7/15\). At distortion parameter
\(7/15\), the actual BB kernel in that row becomes uniform on the other
15 roots. Every other row is unchanged.

Both actual kernels preserve the same old law, charge zero bad mass and
have complete survivor mass one. The same two laws also arise from full-Haar
T4 at delta=1/2, since the raw bad masses are 1/17 and 2/17. Their pure-base density caps are at most
\(16/15<15/8\). If their joint probabilities are \(P_N,P'_N\),

\[
 \|P'_N-P_N\|_1=w_N/8\longrightarrow0.
\]

Retain every original divisor test, including the unit. Write a complete
load as \(L=A+Z\), where \(A\) is its old-only load and \(Z\) is
its positive17 block. The old projections of the latter form another
complete old load \(C\). By (AM9) and Cauchy--Schwarz,
\(E A^2,E C^2,E AC\le5\). Uniform current roots give
\(E_yZ\le C/16\), \(E_yZ^2\le C^2/16\); hence
\(E_{P_N}L^2\le95/16\). Coherent zero old tests with every current
test at root2 attain this bound.

For an arbitrary fixed layout set \(a=A(0)\), \(z_r=Z(0,r)\).
Then \(a\le n\), \(\sum_{r\ne3,\,1\le r\le16}z_r\le n\),
and the exact change is

\[
 \frac{w_N}{240}
 \left(2a\sum_{r\ne3}z_r+\sum_{r\ne3}z_r^2\right)
 -\frac{w_N}{16}(2az_3+z_3^2)
 \le\frac{w_Nn^2}{80}.
\]

The same coherent zero/root2 layout attains this inequality and the
baseline maximum simultaneously. Therefore the complete maxima are

\[
 \Gamma_2(P_N)=95/16,\qquad
 \Gamma_2(P'_N)=95/16+w_Nn^2/80,
 \qquad \Gamma_2(P'_N)-\Gamma_2(P_N)>1/80.             \tag{AC1}
\]

The ratio of this gap to the joint L1 distance is exactly \(n^2/10\).
Thus an unchanged complete old second moment, a common current density
cap and unchanged charge/normalizer do not imply a height-uniform L1
continuity modulus. The old spike law is still not asserted to be
BBMST-generated. Its unbounded Haar density is precisely the premise
excluded by the actual-law construction below. The finite-core verifier
checks the exact formulas at eight finite heights; the ordered-label
argument above proves the full maxima and the unbounded conclusion.

## Uniform cylinder and fourth-moment bounds for arbitrary old families through13

This statement covers arbitrary forbidden residues and arbitrary finite
heights on the prime support {3,5,7,11,13}. It specifies one admissible
law for each such family. It does not claim the bounds for every
supported law, an arbitrary low-square spike, or every BBMST schedule.

All original labels are retained. Start with the full physical357
period Q, including heights needed by moduli with later primes. Let
S be its actual complete survivor set and take mu=Unif(S). At11 and13
use the T4 normalized BBMST kernels on the FULL uniform current fibre,
with delta=1/2 at both steps. Their bad masks include both pure and
mixed classes assigned to that step. Do not condition between steps.
Finally condition once on avoiding both new forbidden unions. Call the
physical law xi and the final supported law nu.

### Existing source facts and a positive actual normalizer

Problems/erdos-7-odd-covering-systems.md supplies the following ordinary
mathematical facts with exact certificates:

* CM8: every such finite357 family has Haar survivor density s>53/432.
* SD1--SD6: the SAME uniform complete-survivor law has complete-test
  square supremum at most G=3849/106, including all missing-class and
  small-height branches.
* T1--T5: each normalized delta=1/2 full-Haar BBMST step has pointwise
  Haar density at most2, square multiplier
  1+2*(3p-1)/(p-1)^2, and actual assigned violation probability at most
  the incoming physical square bound divided by(p-1)^2. The old
  marginal is preserved on every history, including all-bad fibres.

Consequently D0=432/53 is a valid initial Haar density bound. The
actual sequence has

    J11=(41/25)*G,
    b11<=G/100=3849/10600,
    b13<=J11/144=52603/127200,
    J13=(55/36)*J11=578633/6360.

The retained actual probability is therefore at least

    rho*=1-b11_bound-b13_bound=28409/127200>0.          (AO1)

This is a proved lower bound for the specified chain, not an assumed
normalizer. Later normalized kernels preserve the earlier violation
probability, so a union bound applies to the two violations under the
one final physical law. Conditioning is well-defined. Since every
complete test load L includes the unit label and L^2>=1,

    Gamma2(nu)<=1+(J13-1)/rho*
              =11473869/28409 <403.882.                (AO2)

The physical law xi is bounded by Dpre=4D0=1728/53 times the entire
old Haar law. The final supported law is therefore bounded by

    D=Dpre/rho*=4147200/28409 <145.982                 (AO3)

times that SAME Haar law. Thus every original cylinder satisfies
nu(C(a,d))<=min(1,D/d). This statement uses the full original d, not
its projection to a fixed low period.

The T4 charge bound used here belongs to the full-Haar kernel. It
must not be combined with AP's different pure-survivor caps5/3 and
2 while retaining the same charge denominator. Those are a
different actual chain. No PG1-specific hypothesis is used here.

### The Haar fourth moment and the original-label transfer

For a prime p define

    F4(p)=sum_(j>=0)[(j+1)^4-j^4]*p^(-j)
         =p*(p^3+11p^2+11p+1)/(p-1)^4.

At any finite height, expand an original complete load to its fourth
power as ordered quadruples of original divisor labels. For each
prime, compatible prefixes intersect with Haar probability p^(-j),
where j is their maximum depth; incompatible tuples have probability0.
There are (j+1)^4-j^4 exponent quadruples with maximum j. Summing the
caps over all tuples therefore gives product_p F4(p). Coherent nested
test residues attain the finite-height version. No labels are merged.

In particular,

    F4(3)=30, F4(5)=285/32, F4(7)=140/27,
    F4(11)=1914/625, F4(13)=2275/864,
    H4_357=16625/12,
    H4_3571113=19304285/1728.

For the initial uniform actual357 survivor law, apply the density
bound to L^4-1>=0, rather than spending density on the unit:

    E_mu L^4 =1+s^(-1)*integral_S(L^4-1) dHaar
             <=1+D0*(H4_357-1)
             =598121/53=:K0.                         (AO4)

Here the positivity and density bound for S are precisely CM8.

More generally, suppose every complete old test has fourth moment
at most K, and a normalized next-prime kernel has cylinder caps
c*p^(-e) at every full old history. Its complete new test fourth
moment is at most

    K*[1+c*(F4(p)-1)].                               (AO5)

To prove this, keep one arbitrary new test fixed and expand its
fourth power. The four current depths are e1,e2,e3,e4. If all are
zero, normalization preserves the old fourth moment. Otherwise the
current intersection is empty or one cylinder at their maximum
depth, to which the cap applies. After that bound, summing the four
old labels leaves the product A_e1*A_e2*A_e3*A_e4 of four complete
old test loads. Holder gives

    E(A_e1*A_e2*A_e3*A_e4)
       <=product_i(E A_ei^4)^(1/4)<=K.

The current residues may depend on the original old label. They
have already been bounded tuple by tuple, so this dependence causes
no old-layout identification. Counting the current exponent tuples
gives AO5. No independence of the actual sequential coordinates is
assumed.

For the specified full-Haar chain c=2 at both primes. Hence

    Kphysical13=K0*(2F4(11)-1)*(2F4(13)-1)
               =3530785420609/14310000.

Now use the actual final survival lower bound AO1 and L^4>=1 again:

    Gamma4(nu)<=1+(Kphysical13-1)/rho*
               =7061548613243/6392025
               <1104743.585.                         (AO6)

The two unit-floor savings occur at different operations: AO4 at
initial uniform-survivor conditioning and AO6 at final BBMST-chain
conditioning. Omitting the initial saving gives a valid but larger
bound. The endpoint is uniform over all finite original heights and
all forbidden old residues for this specified constructed law.

### A concrete next observation: full original-label tails

For k>=1 let

    Fk(p,h)=sum_(j=0)^h[(j+1)^k-j^k]*p^(-j),
    Hk=product_(p=3,5,7,11,13) Fk(p,infinity).

Let L_h contain exactly those original test labels whose exponent
at every p is at most h_p. Expanding the nonnegative difference of
powers and applying the SAME original-label intersection bounds gives

    E_nu(L^k-L_h^k)
       <=D*[Hk-product_p Fk(p,h_p)].                 (AO7)

In particular this supplies explicit uniformly vanishing errors for
the complete-square objective and fourth moment. It justifies keeping
finite joint residue observations while charging every omitted
original high label. It does not treat a finite enumeration as the
unrestricted theorem. The moments are evaluated under one actual law;
there is no separate law chosen for each test.

A more focused observation for the17 weighted charge retains the
energy inside an original old cylinder. If d=product p^(a_p), then

    sup_(T,b) E_nu[L_T^2*1_(C(b,d))]
      <=(D/d)*product_p[(a_p+1)^2+2(a_p+1)/(p-1)
                                      +(p+1)/(p-1)^2].  (AO8)

Indeed conditional Haar on C(b,d) fixes its a_p initial digits;
the complete-label square bound is the product of the displayed
fixed-prefix geometric moments. Multiply by Haar(C)=1/d and D.
This retains the polynomial growth in queried depth together with
its exponentially decreasing cylinder probability. Summing AO8
over any omitted old cofactor region yields a convergent explicit
bound on its contribution to E[alpha17*L_T^2]. The remaining finite
cofactor observations can retain the actual charge/test intersection,
which the scalar Gamma2 bound discarded.

These bounds remove the arbitrary-spike obstruction within this
specified family of actual admissible laws. They do not by themselves
lower the scalar17/19 continuation seed to its required range: the
square seed AO2 is still above that range, and the root's tested
Haar hinge relaxation at17 did not improve its second-moment charge
bound. The next missing estimate is on the retained finite joint
charge/test data, with AO7--AO8 paying the complete high-label tails.

### Source and validation scope

The report clauses CM8, SD1--SD6 and T1--T5 are ordinary source
proofs with exact arithmetic certificates; they are not asserted to
have an end-to-end Lean proof. The existing frozen declaration
SequentialKernelCylinder.selected_cylinder_bound supplies the
history-dependent selected-cylinder step. FI6 supplies the already
used ordered original-label moment expansion, and pinned Mathlib
MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg supplies Holder
instances. The BBMST source is arXiv:1811.03547, sections2 and6;
no new theorem of that paper or literature-priority claim is asserted.

The [finite-core verifier](verify_finite_core_approximation.py)
independently checks rational constants,
the positive two-prime normalizer, both unit-floor steps, finite
coherent-prefix Haar moments and explicit infinite tails. It does
not enumerate all forbidden families or all test layouts. AO1--AO8
are ordinary proofs; no Lean declaration is added.

## Uniform finite-core approximation of the actual supported law through13

Use exactly the AO full-Haar construction above for each arbitrary finite
forbidden family F on primes3,5,7,11,13, and denote its actual supported law
by nu_F. Its source density bound is D0=432/53, its proved final survival
lower bound is s*=28409/127200, and its final density is at most
D=4147200/28409. Its construction preserves the old marginal at11 and13
and conditions only after both steps. This subsection does not change
to the different pure-survivor construction used in (PP1).

### Complete Haar moments and original-test tails

Let G_p have P(G_p>=j)=p^-j. Ordered original-label tuples are bounded in
Haar measure by the cylinder at their maximum exponent in each coordinate.
Thus the complete Haar second and fourth moments are bounded by the products
of E(1+G_p)^2 and E(1+G_p)^4. The five fourth factors are

    30, 285/32, 140/27, 1914/625, 2275/864,
    H4=19304285/1728.

They include every original cofactor and every higher power. The density bound
therefore gives Gamma4(nu_F)<=D*H4=46330284000/28409. The sharper actual
quartic transfer in the companion moment result is compatible with this
bound; it is not needed for the approximation argument.

For a box b=(b3,b5,b7,b11,b13), retain the original test labels whose exponent
vectors lie in the box, including the unit. Set

    S_p(b)=1+sum_(j=1)^b (2j+1)p^-j,
    S_p(infinity)=p(p+1)/(p-1)^2,
    H2=product_p S_p(infinity), H2_box=product_p S_p(b_p).

For any density bounded byD, expanding L_full^2-L_box^2 keeps exactly the
ordered label pairs with at least one member outside the box. Their Haar
intersections are at most1/lcm, so

    0<=Gamma_full(nu)-Gamma_box(nu)<=D*(H2-H2_box).

No test label disappears from the target maximum: outside pairs enter the
explicit nonnegative bound. For finite physical exponents a use min(a,b)
in the box; the infinite product remains a valid uniform bound. The exact
one-coordinate remainder is

    S_p(infinity)-S_p(b)
      =p^-b[(2b+1)/(p-1)+2p/(p-1)^2].

### Continuity of the actual construction in the forbidden core

Compare two forbidden families F,F' agreeing at all original moduli inside
b. Uniformly lift their constructions to a common finite physical period.
Partition the omitted reciprocal sums by largest prime:

    D3=35/16,
    B3=product_(p=3,5,7) [p/(p-1)*(1-p^(-b_p-1))],
    B4=B3*(11/10)*(1-11^(-b11-1)),
    T357=D3-B3,
    T11=D3/10-B3*(1-11^-b11)/10,
    T13=(77/32)/12-B4*(1-13^-b13)/12.

These exact tails partition the full five-prime original-divisor tail:
T357+T11+T13=1001/384-product_p[p/(p-1)*(1-p^(-b_p-1))].
Every original divisor is counted once; pure11 and13 classes are included.

The symmetric difference of the two357 survivor sets has ambient mass at
most2T357. Both densities are at least1/D0. Their normalized uniform laws
therefore differ in L1 by at most4D0T357.

For any two bad masks on a fixed Haar fibre, the physical and killed T4
kernels at delta=1/2 have L1 difference at most4 times the mask symmetric
mass. This follows by the nested-mask argument through their union: at a
newly bad point the lost density is at most2; normalization controls the
opposite sign. The same bound for killed laws follows from the monotone
good coefficient. A change of old probability contracts under a fixed
normalized kernel. At11 the old density is at mostD0 and the mask average
is at most2D0T11. At13 the physical old density is at most2D0, giving mask
average at most4D0T13. Hence the two physical13 laws differ in L1 by at most

    D0*(4T357+8T11+16T13).

Their full survivor events have Haar symmetric difference at most
2(T357+T11+T13), and both physical densities are at most4D0. Restricting
physical measures to those events therefore gives killed L1 difference at
mostD0*(12T357+16T11+24T13). Both killed masses are at leasts*. Normalizing
them costs at most2/s*, proving

    ||nu_F-nu_F'||_1
      <=L(b):=D*(6T357+8T11+12T13).

Total variation in the probability convention is half this L1 quantity.
This argument uses the actual BB construction, not density domination alone;
bounded-density high-digit oscillations would prevent a uniform TV claim for
arbitrary supported probabilities.

Now take F' to consist of precisely the original forbidden classes of F
inside the box. Its actual law is computed on the finite core and lifted
with independent uniform higher digits. This core law need not avoid F's
omitted high classes: it approximates the actual supported nu_F with the
proved L1 error. The full law nu_F retains all forbidden classes.

### Approximating the actual complete maximum

Both final densities f,g are at mostD, so |f-g|<=D. For every complete test,
Cauchy--Schwarz and the Haar fourth moment give

    |E_f L_T^2-E_g L_T^2|
      <=sqrt(||f-g||_1 * integral |f-g|L_T^4)
      <=sqrt(D*H4*L(b)).

The same bound holds for inside-box tests. Combine it with the original-test
tail estimate and take maxima over the same respective test domains:

    |Gamma_full(nu_F)-Gamma_box(nu_core)|
      <=D*(H2-H2_box)+sqrt(D*H4*L(b)).

For the lower direction, extend every box layout to the full original test
inventory; the added indicators are nonnegative. Thus the bound does not
assume that full and truncated maxima have the same maximizing layout.

Uniform cutoffs in all five coordinates give the certified accuracies

    cutoff20: absolute Gamma2 error <1,
    cutoff24: absolute Gamma2 error <1/10,
    cutoff28: absolute Gamma2 error <1/100.

For each row the verifier checks R<tolerance and
D*H4*L(b)<(tolerance-R)^2 exactly, with R=D*(H2-H2_box). It also checks that
the previous uniform cutoff fails this sufficient bound. No optimality among
nonuniform boxes or lower bound on the true approximation error is claimed.
All heights below a chosen cutoff use the intersection with the physical
inventory. Nonnegative geometric tails prove monotonicity at every height.

The core law and its finite maximum are computable rational objects, but the
certificate does not enumerate a particular family-specific core maximum.
It verifies the uniform error modulus. This theorem applies to arbitrary
residues through13; it neither extends to unrestricted prime support nor
settles the remaining17/19 continuation bounds. The argument is ordinary
mathematics supported by exact arithmetic, not an end-to-end Lean theorem.

### A cubic tail for queried original cylinders

For an arbitrary queried old cylinder C(a,d), where d=product p^h_p, its
Haar conditional law fixes those h_p digits. The complete original test
square therefore satisfies

    E_nu[L_T^2*1_C(a,d)] <=(D/d)*product_p Phi_p(h_p),
    Phi_p(h)=(h+1)^2+2(h+1)/(p-1)+(p+1)/(p-1)^2.

The query residue may differ from the original old forbidden residue; it
represents an old projection of a subsequent current-prime forbidden label.
It may be chosen independently for every current depth.

Summing this bound over queried original old labels outside a box preserves
both complete test-label axes. Put

    T_p=F3_Haar(p)=p*(p^2+4p+1)/(p-1)^3,
    U_p(b)=p^-b*((b+2)^2/(p-1)+(4b+7)/(p-1)^2
                        +3*(p+1)/(p-1)^3),
    K_box=product_p T_p-product_p(T_p-U_p(b_p)).

Indeed p^-h Phi_p(h)=sum_(i,j>=0)p^-max(i,j,h), while U_p(b) is its
sum over h>b. In the following identity Fk(p,b) denotes the finite
Haar moment already defined above, not the fixed-prefix quantity Phi_p(b). The third exponent alone is
restricted. Equivalently its inside sum is F3(p,b)+(b+1)*(F2_Haar(p)-F2(p,b)); this identity follows
by splitting the common maximum at b. Products of the complete nonnegative
sums give

    sum_(queried d outside box) E_nu[L_T^2*1_Cd] <=D*K_box.

The full five-prime cubic sum is10110619519/44236800. If the query-unit
label is excluded exactly, subtract H2, leaving9464854399/44236800. No
assumption identifies different original test or forbidden residues.

For17 let alpha_high be the Haar fraction covered by the high-old-cofactor
new classes. Summing positive current depths gives

    E_nu[L_old^2*alpha_high]<=D*K_box/16.

For the complete current test load and the actual union B_high, its two
current test exponents are unrestricted while the current query exponent
is positive. Their exact sum is F3_Haar(17)-F2_Haar(17)=595/2048. A full-Haar
T4 BB kernel has density at most1 on all its actual bad points, so

    E_nuK17[L_full^2*1_B_high]<=D*K_box*(595/2048).

For a merely c-capped kernel without bad-subset domination one must retain
an additional factor c. This claim concerns bad subsets, not the full
change in BB charge when additional classes are inserted.

In fact beta_delta(alpha)=(alpha-delta)_+/(1-delta) is monotone and
1/(1-delta)-Lipschitz. For the same old law and the masks from a core and
its full extension, alpha_core<=alpha_full<=alpha_core+alpha_high, hence

    E_nu[L_old^2*(beta_delta(alpha_full)-beta_delta(alpha_core))]
       <=D*K_box/[16*(1-delta)].

The unweighted charge increment uses the smaller reciprocal old-label
tail in place of K_box. The coefficient is necessary to account for changes
in density on already bad core points. At delta=1/2 the denominator is8.

These identities give explicit error budgets for finite same-law joint
charge/test observations. They do not supply the missing low-cofactor
observations or a strict improvement of the full17 bad charge. All finite
heights are bounded by the complete nonnegative geometric sums; the
verifier retains literal small three-label checks and45 prefix-moment
fixtures without presenting them as a proof of the universal quantifiers.


## An arbitrary-residue supported seed below256 after13

For every finite distinct odd family supported on {3,5,7,11,13}, with
arbitrary original heights and residues, there is one explicit supported
law with

    Gamma13 <= 42035473165849976389/171474522380088889
             <245.141218.                            (PP1)

The construction starts with the uniform actual357 survivor law and
uses AP's pure-survivor BBMST kernels with thresholds T11=4,T13=6,
followed by one final conditioning. This is a different law from the
two full-Haar delta=1/2 kernels in AO1--AO8. The assertion retains
all original divisor test labels and all finite physical exponents.

### One source law and its simultaneous observations

Let mu be the uniform complete actual357 survivor law. CM8, SD1--SD6
and BS10 in Problems/erdos-7-odd-covering-systems.md give on this SAME
law, including missing head classes and arbitrary residues/heights,

    dmu/dHaar <=D0=432/53,
    E_mu L^2 <=G=3849/106,
    E_mu L <=M=1+R,  R=1649/360,

for every complete original test load L. Here R is the sum of the
nonunit cylinder maxima; BS10 explicitly identifies its arbitrary
actual-head and uniform-law scope. No nonuniform two-root-law
estimate is substituted.

Let A=(1+G3)(1+G5)(1+G7), with independent geometric variables
P(Gp=n)=(p-1)/p^(n+1). Then E A=35/16. Successively centering all
test prefixes in each independent Haar coordinate makes those
indicators nested and maximizes every nonnegative increasing convex
cost. At zero fixed low depth this is the comonotone comparison in
the report following SH4. It changes test residues only for this
upper comparison; it changes no forbidden class or actual law.
Completion of the finite heights adds nonnegative terms. Consequently

    H(h):=sup_L E_mu(L-h)_+ <=D0 E(A-h)_+.             (PP2)

For an integer h, this expectation is exactly

    E A-h+sum_(n<h)(h-n)*P(A=n).

Only finitely many product probabilities are needed; its entire
infinite tail is included through the exact mean35/16.

For h=2,3 the following positive-integer inequalities improve PP2:

    (L-2)_+ <=(L^2+17L-18)/30,
    (L-3)_+ <=(L^2+2L-3)/15.

Above the respective thresholds, the differences are
(L-6)(L-7)/30 and(L-6)(L-7)/15, nonnegative for every integer L.
Below the thresholds the displayed polynomials are nonnegative
for L>=1. All their moment coefficients are nonnegative. Thus the
simultaneous profile needed below is

    H1<=R,
    H2<=h2=2159489/572400,
    H3<=h3=424267/143100,
    H4<=h4=4733643/2272375,
    H5<=h5=121526801/79533125,
    H6<=h6=8571397321/8350978125.                      (PP3)

The first two nontrivial bounds are(G-1+17R)/30 and(G-1+2R)/15;
h4,h5,h6 come from PP2. All are bounds for every original layout on
one mu. For h in [j,j+1], the chord of the two integer upper bounds
is valid. For h<=1, H(h)<=M-h because L>=1.

### The actual normalized11/13 chain

Use the actual pure-power survivor bases at11 and13 and AP's
normalized kernel with

    T11=4, delta11=1/3, c11=5/3;
    T13=6, delta13=5/11, c13=2.

Here c_p bounds conditional Haar cylinder densities at every full
earlier history, and c_p<=p as required by AP1--AP5. The pure
survivor bases are nonempty by their geometric exclusion sums.
The actual kernels are normalized even on completely mixed-bad
rows. There is no intermediate conditioning.

At11 the actual assigned bad probability is at most b11=h4/6.
For13 let N=1+K11 be AP's independent comparison multiplier:

    P(N=1)=28/33,
    P(N=n)=50/(3*11^n) for n>=2,
    E N=7/6.

For N=1,2,3, use respectively H6,2H3,3H2. Since L is a positive
integer, the exact identities at N=4,5 are

    E(4L-6)_+ =2(E L-1)+2E(L-2)_+,
    E(5L-6)_+ =4(E L-1)+E(L-2)_+.

For N>=6, NL-6>=0 and E(NL-6)_+<=NM-6. The full N>=6 tail has
probability5/483153 and first moment61/966306. AP2 therefore gives

    b13 <= [ (28/33)h6+(100/363)h3+(19300/483153)h2
                         +(887/322102)R+1/966306 ]/6
         =153632313644558711/498009616542900000.

The actual common final surviving mass is at least

    rho*=1-b11_bound-b13_bound
         =171474522380088889/498009616542900000>0.      (PP4)

Normalized later kernels preserve earlier violations, so this sum
is a union bound under the same final physical law. AP5 gives

    J13<=G*(23/15)*(55/36)=324599/3816.

One final conditioning on the actual survivor event, retaining
the unit-floor saving, now yields

    Gamma13 <=1+(J13-1)/rho*,

which is PP1. No profile observation is taken from a different law.

### Density, fourth moment and a concrete next prime

The physical Haar density cap is D0*c11*c13=1440/53. The same
supported law therefore has

    D13<=13530827317392000000/171474522380088889.

Using AO4's K0=598121/53 and the original-label quartic transfer
AO5, its physical fourth moment is at most

    Kphysical=K0*(1664/375)*(1843/432)=114643048312/536625.

The supported fourth moment is at most

    1+(Kphysical-1)/rho*
      =106393040395571160497689/171474522380088889
      <620459.757.                                   (PP5)

These caps belong to the new AP(4,6) law, not the earlier AO law.

There is also a concrete admissible17 continuation. Start with the
supported PP1 law and use a FULL-Haar T4 BBMST kernel at17 with
delta17=1/2, whose bad mask includes all pure and mixed17 classes.
Writing f for the exact bound in PP1, its actual retained mass is
at least

    1-f/256=1862004563452779195/43897477729302755584>0.

Its physical square is at most(89/64)f. Conditioning once and using
the unit floor gives

    Gamma17<=1+[(89/64)f-1]/(1-f/256)
            =2984518594775348323619/372400912690555839
            <8014.263.                               (PP6)

Thus the construction supplies actual survivors for every finite
family supported on {3,5,7,11,13,17}. This does not prove an
unrestricted tail continuation: the supplied17 bound does not
pass the19 scalar condition, and PP1 remains above the joint17/19
threshold near123.059. No literature-priority claim is made.

### Verification and parameter-search boundary

The adjacent exact verifier reconstructs PP2--PP6 using rational
arithmetic and full auxiliary tails. It also evaluates120 endpoint
threshold pairs from the fixed integer profile: integers1..9 and
100/11 at11; integers1..11 and144/13 at13. The chosen(4,6) pair
has the smallest certified supported square among those pairs.
The comparison concerns this specified profile upper certificate,
not the actual best law or all possible observations.

For this chord-based certificate, after multiplying by
(10-T11)(12-T13), its numerator and denominator are separately
affine on each integer threshold interval. The13 breaks are still
integers because T13/N crosses an integer only at an integer T13.
On positive-denominator intervals the ratio is monotone or constant;
a zero-denominator boundary has positive numerator. Thus endpoints
suffice for this certificate. This observation is not needed for
the validity of the concrete(4,6) result.

The construction reuses CM8, SD1--SD6, BS10, AP1--AP6 and the
report's Haar comonotone comparison. It is an ordinary proof with
an exact arithmetic certificate, not a new Lean declaration or
an end-to-end Lean verification of the arbitrary-family extraction.

The [arbitrary-head profile verifier](verify_arbitrary_head_profile.py)
reconstructs the [exact certificate](arbitrary_head_profile_certificate.json)
from pinned numerical inputs for CM8, SD and the joint density bound.
The finite-core and moment estimates for the AO law have their own
[certificate](finite_core_approximation_certificate.json). Both programs
are independent of the working directory:

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_arbitrary_head_profile.py
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_finite_core_approximation.py
```

## Weighted forbidden-mask tails for the actual AP(4,6) restart

The following ordinary proof controls changes of the forbidden masks
at17 and19. From the full supported AP(4,6) law at13, retain old
cofactor exponents through20 and current prime depths through8 in
those two masks. For the actual thresholds T17=T19=8, the total error
in the SH28 functional at W=483 is less than377/1000. Every original
test label and every original ambient height is retained.

This is a continuity bound and a sufficient criterion. It does not
produce the required reference correlation certificate. In particular,
it neither truncates the incoming13 law nor makes its joint marginals
computable from a finite initial family. Its arbitrary-height statement
is ordinary mathematics; the accompanying exact program verifies
constants and finite coefficient fixtures, not Lean-kernel proofs.

### 1. Same-law inputs and definitions

Fix an arbitrary finite family of distinct odd moduli supported on
3,5,7,11,13,17,19, with at most one actual forbidden class per modulus.
All residues, missing classes and finite exponent heights are arbitrary.
Work on its full product residue space, enlarged by harmless unused
coordinates if necessary. A complete test on an old period Q is

    A(x)=sum_(d|Q) 1_{x=a_d mod d},

with an independently chosen test residue at each original divisor,
including the unit divisor. Test residues need not be forbidden
residues. Deleting a forbidden constraint does not delete its test
label. At a current prime p, different p-exponent blocks of a complete
test may use different old test layouts.

Let nu13 be the actual supported law supplied by PP1--PP5: start with
the uniform actual357 survivor law, apply the pure-survivor AP kernels
at thresholds T11=4,T13=6, then condition once on all actual survivors.
The exact certificate `arbitrary_head_profile_certificate.json` gives

    rho13 >=171474522380088889/498009616542900000>0,
    dnu13/dHaar <=D=13530827317392000000/171474522380088889,
    sup_A E_nu13 A^2 <=J=42035473165849976389/171474522380088889.

These are three observations of the same law. The separate PP6
full-Haar T4 step at17 is not used here. In this proof the next steps
are pure-survivor AP17/8 and AP19/8, with no conditioning between them.

At a current prime p, let P be the actual pure-power survivor set,
lambda its Haar mass, and m=Haar restricted to P divided by lambda.
At most one pure forbidden class occurs at each positive depth, so

    lambda >=1-sum_(e>=1)p^-e=(p-2)/(p-1)=s_* >0.

The finite-height bound is in fact strict. For a mixed forbidden mask
B_x in the current fibre, set alpha(x)=m(B_x). Put

    delta=7/(p-2), C=1/(1-delta),
    a(alpha)=1/(1-min(alpha,delta)),
    b(alpha)=C(1-delta/alpha)_+, with b(0)=0.

The normalized physical kernel has m-density
`a(alpha) 1_(B_x^c)+b(alpha) 1_(B_x)`. Its killed kernel retains only
the first summand. Physical kernels exist on every old history,
including alpha=1; killed kernels are subprobability kernels.
Their conditional full-Haar density cap is c=C/s_*.

The exact constants are

| p | delta | C | s_* | c | L_p=max(C^2,C/delta) |
|---|---|---|---|---|---|
|17|7/15|15/8|15/16|2|225/56|
|19|7/17|17/10|17/18|9/5|289/70|

### 2. Localized complete-test energy

For a prime q and nonnegative integer a define

    Phi_q(a)=(a+1)^2+2(a+1)/(q-1)+(q+1)/(q-1)^2.

If nu<=D Haar on an old product space, then, for every complete old
test A and cylinder C(r),

    integral_(C(r)) A^2 dnu
      <=D/r product_(q old) Phi_q(v_q(r)).               (WT1)

Indeed, expand A^2 over two original test labels. Their intersection
with C(r) is empty or a cylinder of modulus lcm(r,d,e). At each old
prime, enlarge the finite pair of exponents to all nonnegative ones:

    sum_(i,j>=0) q^-max(a,i,j)=q^-a Phi_q(a).

The terms through max(i,j)=a contribute (a+1)^2q^-a; the remaining
terms contribute sum_(j>a)(2j+1)q^-j. Summing this geometric tail gives
the displayed identity. Product factorization proves WT1, independently
of test residue compatibility.

The fully summed coefficient and its finite part are

    Sigma_q=sum_(a>=0)q^-a Phi_q(a)
           =q(q^2+4q+1)/(q-1)^3,
    Sigma_(q,b)=sum_(a=0)^b q^-a Phi_q(a).              (WT2)

All sums in the estimates below use this full infinite value; no
truncated probability distribution is normalized.

### 3. Mixed-mask and pure-base stability

The functions a and b are globally Lipschitz with constants C^2 and
C/delta respectively. Below the clipping point a'=1/(1-alpha)^2;
above it a is constant. Below the clipping point b=0; above it
b'=C delta/alpha^2. Continuity at delta and the explicit endpoint
values give the bounds on the closed unit interval.

First fix one pure base m and nested mixed masks B0 subset B. Put
E=B\B0. On the common good and common bad regions the kernel
coefficient changes by at most L_p m(E). On E, both physical
coefficients lie in [0,C], so the change is at most C; the killed
version satisfies the same bound. Thus, for either kernel,

    |k_B-k_B0| <=C 1_E+L_p m(E).                        (WT3)

Suppose E is contained in a union of actual mixed cylinders indexed
by (r,e), namely C_old(r) times C_current(p^e). Conversion from m to
Haar in WT3 is essential: the point term costs C/lambda and the
average term costs L_p/lambda^2. Expand a full test L and use WT1,
first with a current cylinder and then with the whole current space.
For a common old law nu<=D Haar this yields

    integral L^2 d|Q_B-Q_B0|
      <=sum_(r,e) [D/r product_(q old)Phi_q(v_q(r))] p^-e
          *[(C/s_*)Phi_p(e)+(L_p/s_*^2)Phi_p(0)].       (WT-mixed)

For the average term, m(E_x)<=lambda^-1 sum_(r,e)
1_(C_old(r))(x)p^-e. Integrating a current test pair then contributes
Phi_p(0), proving the second coefficient without optimizing a
different test on each old row. Both physical and killed versions
hold for masks depending on the entire earlier history.

Next fix the raw mixed mask in the full current ambient space and
compare nested pure bases P subset P0. Write lambda=Haar(P),
lambda0=Haar(P0), and kappa=lambda0-lambda. The total variation distance
(supremum over events, half the L1 distance) between their normalized
uniform laws is kappa/lambda0, so |alpha-alpha0|<=kappa/lambda0.
On P0\P the Haar density difference is at most C/s_*. On P the
coefficient and normalization changes give

    |f(alpha)/lambda-f(alpha0)/lambda0|
      <=L_p kappa/(lambda lambda0)+C kappa/(lambda lambda0)
      <=(L_p+C)kappa/s_*^2,

for f=a or b. The same estimates hold after killing because the raw
mixed mask remains fixed. If P0\P is covered by pure cylinders at
depths e in E, and every complete old test has square expectation at
most J, then

    integral L^2 d|Q_P-Q_P0|
      <=J [(C/s_*)sum_(e in E)p^-e Phi_p(e)
         +((L_p+C)/s_*^2)Phi_p(0)sum_(e in E)p^-e].    (WT-pure)

To justify use of J rather than D, expand each current test pair.
Its old factors A_i,A_j obey E A_i A_j<=J by Cauchy--Schwarz, even
though their original residues differ. For the changed pure region
the current pair sum is p^-e Phi_p(e); for the normalization term it
is Phi_p(0). No future survivor normalization is assumed.

### 4. An explicit reference and fully summed tails

At17 and19 keep actual pure constraints of depth e<=8. Keep actual
mixed constraints only when the current depth is e<=8 and every old
cofactor exponent is at most20. Directly delete the other forbidden
constraints in the reference, retaining the full original ambient
space and every original test label. First delete mixed tails on the
fixed actual pure base; then delete pure tails with the remaining raw
mixed mask fixed. WT-mixed and WT-pure bound these two changes.

If a retained actual pure class modulo p exists, one may instead
place the removed forbidden classes redundantly inside that class
while retaining every original forbidden-modulus label. This optional
construction must use an actual retained class. If modulus p is
absent, use direct deletion; no new pure class is invented.

For old prime set S, box b=20 and current depth h=8, write

    U_S=product_(q in S) Sigma_q,
    V_S=product_(q in S) Sigma_(q,20),
    Z_S=product_(q in S) Phi_q(0),
    R_S=U_S-V_S,
    H_S=V_S-Z_S,
    t0_p=1/[(p-1)p^8],
    tPhi_p=Sigma_p-Sigma_(p,8),
    Theta_p=(C/s_*)[Sigma_p-Phi_p(0)]
              +(L_p/s_*^2)Phi_p(0)/(p-1).

The unit old cofactor has weight Z_S, not1. The discarded mixed
indices split disjointly into old cofactors outside the box (all
positive current depths) and old cofactors inside the box but current
depth above8. The latter exclude the unit cofactor. Consequently

    old_error   =D R_S Theta_p,
    mixed_error =D H_S [(C/s_*)tPhi_p
                         +(L_p/s_*^2)Phi_p(0)t0_p],
    pure_error  =J [(C/s_*)tPhi_p
                         +((L_p+C)/s_*^2)Phi_p(0)t0_p],
    epsilon_p=old_error+mixed_error+pure_error.          (WT4)

At17 use S={3,5,7,11,13} and the D,J of section1. At19 use
S={3,5,7,11,13,17} and the unconditioned physical17 bounds

    D17<=2D,
    J17<=(89/64)J.

The second follows by keeping the zero-current-exponent test pair at
coefficient1 and applying the cap2 to every other pair:
1+2(Phi17(0)-1)=89/64. These same bounds apply to either reference
or actual physical17 law. The killed17 measure is dominated by its
physical17 law, so it also obeys the required D,J bounds.

The exact all-depth coefficients are Theta17=6613/7168 and
Theta19=2869/3780. Exact rational recomputation gives the following
display decimals (the JSON fractions, not the decimals, are used):

| step | old cofactor error | mixed depth error | pure depth error | epsilon |
|---|---:|---:|---:|---:|
|17|0.000153431002431096|0.000031881166792166|0.000000468509674939|0.000185780678898201|
|19|0.000375105420972540|0.000031542144531736|0.000000213990105974|0.000406861555610249|

The errors are uniform in the original finite heights and arbitrary
forbidden/test residues. Missing forbidden classes only reduce the
nonnegative sums.

### 5. Propagation, assigned charges, and the W483 criterion

For two old finite positive measures define

    Delta2(sigma,tau)=sup_(complete old A) integral A^2 d|sigma-tau|.

For a common current kernel K of mass at most1 and full-Haar prefix
cap c p^-e, expansion over the current test exponents gives

    Delta2(sigma K,tau K)
      <=[1+c(Phi_p(0)-1)] Delta2(sigma,tau).             (WT5)

Indeed, total variation is dominated by |sigma-tau|K. The zero-zero
pair costs at most Delta2 because the kernel has mass at most1.
Every other pair costs at most c p^-max(i,j) Delta2 by
Cauchy--Schwarz under |sigma-tau|. Summing those positive pairs
gives c(Phi_p(0)-1). This proves WT5 for physical or killed kernels
and history-dependent masks. At19 its factor is59/45.

Let mu17=nu13 K17 be the actual physical17 law, eta17=nu13 K17^-
its killed law, and use a superscript0 for the corresponding reference.
Compare actual and reference17 kernels under the same nu13. Then
compare the19 kernels under the actual mu17, and separately under
eta17. The latter is dominated by mu17, so WT4 is valid there too.
Propagate the old-law difference through a common reference19 kernel.
Thus both the final physical and final killed weighted differences
are at most

    epsilon_square=(59/45)epsilon17+epsilon19.           (WT6)

For clarity, b17 and b19 below denote actual assigned mixed-event
probabilities, not arbitrary scalar upper bounds. With the physical
prefix laws they are

    b17=1-(nu13 K17^-)(1),
    b19=1-(mu17 K19^-)(1),
    B=b17+b19.

Since every complete test contains the unit, WT4 also bounds plain
L1 error. Hence |b17-b17^0|<=epsilon17. For b19, split the comparison
by first changing the19 kernel under actual mu17 (cost epsilon19),
then changing mu17 to mu17^0 under the same reference killed19
kernel (cost epsilon17 by L1 contraction). Therefore

    |B-B0|<=2epsilon17+epsilon19.                        (WT7)

These assigned charges are taken under physical prefix laws; later
normalized kernels preserve their expectations. Their sum bounds
the actual final bad-event union, even though the last killed law
also removes the earlier bad event.

At W=483 the exact arithmetic in the certificate gives

    epsilon_square+483(2epsilon17+epsilon19)
      =0.3766287078433556... <377/1000.                 (WT8)

Consequently it suffices to establish, for the reference and every
complete original test L,

    E_ref[L^2-1]+483 B0 <=483-377/1000.                  (WT9)

The physical laws are probabilities, so subtraction of the constant1
introduces no extra error. Put eta=377/1000 minus the exact WT8
allowance; the certificate proves eta>0. WT6--WT8 imply for the actual
full masks

    E_actual[L^2-1]+483 B <=483-eta<483.                (WT10)

This implies the full-test criterion used in SH28. Since L^2-1>=0,
the strict margin already gives B<=1-eta/483<1, without an additional
positivity premise. The final actual survivor mass rho is at least
1-B>0. Discarding the bad union and conditioning once gives

    E_survivor L^2
      =1+rho^-1 integral_survivors(L^2-1)dmu
      <=1+rho^-1 E_actual(L^2-1)<=484.

Thus a certificate of WT9 would supply actual17/19 continuation with
positive survival and supported complete-square bound484. WT9 has
not been established by this tail calculation; unrestricted Erdős #7
also requires the remaining prime continuation or another full proof.

### 6. Exact computational scope

Only the17/19 forbidden masks were reduced above. The incoming nu13
is the full actual AP(4,6) law, and the complete test inventory remains
untruncated. True finite joint marginals of nu13 can be inputs to a
reference calculation, but this proof supplies neither their exact
finite computation nor a continuity bound for truncating that AP law.
The existing finite-core approximation for the different AO
full-Haar11/13 law cannot be substituted for it.

If a further computation truncates the test exponents to a vector h,
that is a separate approximation. Through unconditioned AP17/19
the full physical Haar density is at most(18/5)D. Writing L_h for the
sum of the retained original test indicators, direct pair expansion
gives the optional uniform bound

    E(L^2-L_h^2) <=(18D/5)
      *[product_p sum_(a>=0)(2a+1)p^-a
           -product_p sum_(a=0)^(h_p)(2a+1)p^-a],       (WT11)

over p in{3,5,7,11,13,17,19}. A discarded pair has at least one
exponent exceeding h, so the product difference counts all such
pairs using their nonnegative Haar intersection bounds. WT11 is not
included in the377/1000 allowance and must be paid separately.

The exact verifier pins the upstream AP source certificate by SHA-256,
checks all rational factors and tails, and compares the entire saved
JSON to recomputation. Its default mode only validates; `--write`
explicitly regenerates the certificate. Duplicate JSON keys and
changed numeric fields are rejected, including under `python3 -I -O`.
Finite coefficient and prefix fixtures check the implementations of
the formulas; they are not substitutes for the arbitrary-height proofs
above. No canonical formal status is asserted by these files.

Reproduce the [weighted-kernel tail certificate](weighted_kernel_tails_certificate.json)
with the [standalone verifier](verify_weighted_kernel_tails.py):

```sh
python3 -I -O /absolute/path/to/docs/reports/erdos7-odd-covering/verify_weighted_kernel_tails.py
```

## A stronger generic profile from actual pure exclusions

For the same actual supported AP(4,6) law considered in PP1--PP5,
the complete-test square bound improves to

    Gamma13 <=8416748733302130673/43949004608153173
             =191.511703355864... .                       (PR1)

The previous bound was245.141217379656... . The law and its thresholds
are unchanged. Every original finite exponent height, arbitrary actual
residue and missing class is included. The proof uses twelve cases
according to actual low pure exclusions, then takes a single common
profile. No forbidden residue is changed or added and no test label
is removed. This is an ordinary proof with exact arithmetic, not an
unrestricted Erdős7 solution or an end-to-end Lean proof.

### Actual source law and twelve exhaustive cases

Let S be the full actual survivor set for an arbitrary finite family
of distinct nonunit moduli supported on3,5,7. Its uniform probability
nu is the source law. The same-law observations CM8, BS10 and SD1--SD6
give

    s:=Haar(S)>=53/432,
    sup_L E_nu L^2<=G=3849/106,
    sup_L E_nu(L-1)<=R=1649/360.                          (PR2)

Here L is a complete original-divisor test with its own independently
chosen residue at every divisor, including the unit. The R bound is
the stronger sum of cylinder maxima, so it bounds every such test.

Partition the actual family into three ternary cases:

* A: the actual modulus3 class is absent;
* B: the actual modulus3 class is present, while the actual modulus9
  class is absent or is contained in that forbidden modulus3 root;
* C: the actual modulus3 and9 classes are present and the modulus9
  class lies outside the forbidden modulus3 root.

Cross these with presence or absence of the actual modulus5 class,
and presence or absence of the actual modulus7 class. These twelve
cases are disjoint and exhaustive, including all small finite heights.

The actual pure-power survivor densities have lower bounds

| ternary case | pure3 lower l3 | same uniform35 R35 upper | same uniform357 square upper |
|---|---:|---:|---:|
|A|5/6|17/12|5273/258|
|B|11/18|47/24|14543/438|
|C|1/2|15/7|3849/106|

For A, only ternary exponents at least2 can remove pure mass, whose
sum is1/6. For B the root exclusion costs1/3, an ineffective9 class
adds no mass, and exponents at least3 cost at most1/18. For C the
full positive-exponent geometric sum costs at most1/2. The pair R35
bounds and the A/B square bounds are exactly the same-uniform-law
fallback cases of P11--P12, N9 and SD6; no balanced or PG1 law is used.

The quinary lower l5 is3/4 when modulus5 is present and19/20 when it
is absent. The septenary lower l7 is5/6 when modulus7 is present and
41/42 when absent. These again follow from the full remaining pure
geometric sums, not a finite truncation.

### Stronger density in missing-class cases

Let s35 be the actual uniform ambient survivor density on3,5, and let
x,z be its actual pure3 and pure5 survivor densities. All mixed35
classes together have ambient density at most

    sum_(a,b>=1)3^-a5^-b=1/8,

so s35>=l3*l5-1/8=:s35_*>0. The uniform actual35 law has the R35
bound of the table. At7, the actual pure survivors have mass at least
l7; every new mixed class d7^e costs at most its old cylinder mass
times7^-e. Thus

    s>=s35(l7-R35/6)
      >=s35_*(l7-R35_upper/6).                          (PR3)

The bracket is positive in every case. This is the ambient-density
version of the same-law recurrence in N9; no conditioning on individual
old cells is involved.

A second useful estimate is the actual linear numerator bound proved
in CM2, including its missing-class fallback paragraphs:

    (s35-s35*R35/5)/(xz)>=53/135.

In particular, if modulus7 is absent, adding the extra pure7 mass
1/7 relative to5/6 gives

    s >=(5s35-s35*R35)/6+s35/7
      >=(53/162)l3*l5+s35_*/7.                         (PR4)

With modulus7 present the same formula holds without the final
s35_*/7 term. This conclusion uses CM2's linear numerator itself;
it does not infer it from the weaker final scalar CM8 statement.
In case C with modulus5 present and modulus7 absent, PR4 is

    s>=53/432+1/28=479/3024.

For completeness the verifier also compares CM8, the bound
(53/135)l3*l5*l7 from CM1 under the actual pure-survivor product,
and the ordinary reciprocal-sum bound
`s>=-3/16+sum_(missing p in{3,5,7})1/p`.
Taking the strongest of these valid bounds and PR3--PR4 gives:

| ternary case | 5 absent,7 absent | 5 absent,7 present | 5 present,7 absent | 5 present,7 present |
|---|---:|---:|---:|---:|
|A|373/756|43/108|373/1008|43/144|
|B|5371/18144|2993/12960|655/3024|73/432|
|C|13/60|1/6|479/3024|53/432|

Denote the bound in the relevant cell by s_* and put D=1/s_*.
All bounds apply to the same original uniform357 law nu.

### Complete-test comparison inside the retained pure geometry

Retain only the following exclusions when defining a reference
product set P. These are actual exclusions, used as geometric
information about S subset P; they do not alter the actual family.

In case A, impose no reference ternary exclusion. In B retain the
actual modulus3 exclusion. In C retain the actual modulus3 and9
exclusions. At5 and7 retain the actual first-root class when it exists
and impose no reference exclusion when it is absent. The reference
coordinate Haar masses are therefore

    u3=1 in A, 2/3 in B, 5/9 in C;
    u5=1 if absent, 4/5 if present;
    u7=1 if absent, 6/7 if present.                      (PR5)

In C the extra modulus9 class lies in one of the two surviving3 roots,
so removing it costs exactly1/9; the other surviving3 root remains
entirely available. For every coordinate p and exponent e>=1, every
test cylinder has conditional reference probability at most
`c_p p^-e`, where c_p=1/u_p and c_p<=p. The unit prefix has probability1.

Let independent nonnegative integer variables K_p satisfy

    Pr(K_p>=e)=c_p p^-e, e>=1,
    V=product_(p=3,5,7)(1+K_p).

Then for every complete original test and every increasing convex
function f,

    E_(Haar conditioned on P) f(L)<=E f(V).              (PR6)

The comparison is the capped version of the report's comonotone
comparison following SH4. To see why every original label is retained,
fix the other coordinates and view the test as a nonnegative weighted
sum of current-coordinate prefix indicators, one per original label.
An increasing convex cost is maximized when indicators of given
probabilities are nested. Enlarging each probability to its cap can
only increase the cost. Use a common nested indicator for each exponent,
then repeat at the next coordinate. The resulting full labelled sum
is the product of the three prefix counts. For finite original heights
these counts are truncated; extending each count to K_p adds only
nonnegative terms. This argument neither uses row-dependent test choices
under nu nor moves any actual forbidden residue.

For t>=1, apply PR6 to the nonnegative hinge f(v)=(v-t)_+ and use
S subset P:

    H_nu(t):=sup_L E_nu(L-t)_+
      <=D*(u3*u5*u7)*E(V-t)_+.                         (PR7)

This differs from encoding an old scalar count: the actual root
exclusions give a smaller integration domain before the comparison.
Missing roots are explicitly kept as u_p=1.

The exact comparator probabilities and mean are

    Pr(1+K_p=1)=1-c_p/p,
    Pr(1+K_p=v)=c_p(p-1)p^-v, v>=2,
    E V=product_p(1+c_p/(p-1)).                         (PR8)

For an integer h>=1,

    E(V-h)_+=E V-h+sum_(n<h)(h-n)Pr(V=n).              (PR9)

Only finitely many product probabilities enter the correction; its
omitted tail is supplied by the full mean, with no renormalization.

The existing integer majorants used in PP3 further give, in each branch
with its own same-law square bound G_branch,

    H_nu(1)<=R,
    H_nu(2)<=(G_branch-1+17R)/30,
    H_nu(3)<=(G_branch-1+2R)/15.                        (PR10)

These follow pointwise for positive integer L from
`(L-2)_+<=(L^2+17L-18)/30` and
`(L-3)_+<=(L^2+2L-3)/15`. Take the minimum of PR7 and the applicable
PR10 bound, then the maximum over all twelve branches. The exact
verifier checks that case C with5 and7 present dominates all twelve
branches at every retained integer h=1,...,12.

The common first six hinge bounds are

    h1=1649/360,
    h2=2159489/572400,
    h3=6759/2597,
    h4=776841/454475,
    h5=20500987/15906625,
    h6=1501750547/1670195625.                           (PR11)

The JSON retains h7 through h12 too. For noninteger t between retained
integers, the chord joining the upper values bounds the actual convex
hinge. For t<=1, use H_nu(t)<=1+R-t. No global optimality of these
profiles is asserted.

### The unchanged AP(4,6) continuation

Start with the original uniform357 law nu. Apply the same actual
pure-survivor AP kernels as in PP4, with thresholds T11=4 and T13=6,
caps c11=5/3,c13=2, and no intermediate conditioning. In particular
the law has not been chosen differently for different branches.

The existing AP full-tail comparison with PR11 gives

    b11<=h4/6,
    b13<=[(28/33)h6+(100/363)h3+(19300/483153)h2
                 +(887/322102)R+1/966306]/6.

The second formula retains the complete auxiliary11 multiplier tail.
It is PP4's identical expression with the stronger same-source profile.
Consequently final survivor mass is at least

    rho13=1-b11_bound-b13_bound
         =43949004608153173/99601923308580000>0.        (PR12)

The unchanged unconditioned physical square bound is324599/3816, and
its Haar density bound is1440/53. Deleting the actual bad union saves
at least its mass from every test square because L>=1. One final
conditioning therefore gives

    Gamma13<=1+[(324599/3816)-1]/rho13
            =8416748733302130673/43949004608153173,
    dnu13/dHaar<= (1440/53)/rho13
            =2706165463478400000/43949004608153173.    (PR13)

These are stronger observations of the same full actual AP13 law.
They do not establish a17/19 joint correlation criterion or later-prime
continuation. Further restrictions on actual pure powers may improve
the profile in additional cases, but arbitrary higher pure classes can
also be redundant inside the retained exclusions; no uniform extra
deletion is assumed.

### Existing consumers of the stronger same-law observations

The physical fourth-moment bound in PP5 is unchanged:
Kphysical13=114643048312/536625. Substituting PR12 in the existing
unit-floor conditioning argument gives

    Gamma4_13<=1+(Kphysical13-1)/rho13.                 (PR14)

The exact resulting fraction is in the new certificate. This is a
stronger bound on the same law; it does not select a different kernel.

The separate PP6 full-Haar T4 step at17, with delta=1/2, also admits
the same direct substitution. Put g=PR1's square bound. Its assigned
charge is at most g/256, its survival is at least1-g/256>0, and its
supported complete square is at most

    1+[(89/64)g-1]/(1-g/256)
      =1054.2479524075604... .                          (PR15)

This17 kernel is distinct from the pure-base AP17/8 kernel below;
its conditioned output is not substituted into the WT17/19 chain.

Finally, the previously proved WT4 bounds for the pure-base AP17/8
and AP19/8 mask truncations are linear in their incoming D,J. Let
Dold,Jold be PP's previous bounds on the same actual supported13
law, and Dnew,Jnew be PR13,PR1. In each old WT step, multiply the
old-cofactor and mixed-current errors by Dnew/Dold, and the pure-current
error by Jnew/Jold. The common unconditioned17 multipliers2 and89/64
remain unchanged. Thus the exact rescaled errors are

    epsilon17=0.0001449714082004838...,
    epsilon19=0.0003174881146077773... .

The old weighted propagation factor59/45 and charge bound
2epsilon17+epsilon19 are unchanged. At W=483 the total allowance is

    (59/45)epsilon17+epsilon19
       +483(2epsilon17+epsilon19)
      =0.2938967014159167... <294/1000.                 (PR16)

Accordingly the sufficient reference criterion becomes
`E_ref[L^2-1]+483 B_ref<=483-.294` for every complete original test.
The remaining strictly positive arithmetic slack gives B_actual<1
and the same supported-square bound484 if that reference criterion
is proved. It has not been proved here. Only the17/19 forbidden masks
are truncated; the incoming AP13 law and all original test labels
remain full, exactly as in WT1--WT11. The earlier WT certificate is
an immutable pinned input, not overwritten with new bounds.

The adjacent verifier pins the five source certificates by SHA-256,
reconstructs all twelve branches and complete geometric means, and
checks the independent closed13 charge formula. Default mode compares
the entire saved JSON; `--write` explicitly regenerates it. Its finite
one-coordinate fixtures test the prefix comparison implementation.
These numerical checks do not replace the ordinary arbitrary-height
argument above or claim a new Lean declaration.

The [pure-root profile verifier](verify_pure_root_profile.py) reconstructs the
[exact certificate](pure_root_profile_certificate.json) with the same full-law
source certificates. It can be run from any working directory:

```sh
python3 -I -O /absolute/path/to/verify_pure_root_profile.py
```

## Exact equality in the killed unit floor for genuine BB17 and BB19

For each `p in {17,19}`, there is a uniform complete actual357 survivor law, an actual pure-base BBMST step with `delta=7/(p-2)`, positive assigned bad mass, and one complete original test `L` such that

`integral_bad L^2 dP = P(bad) > 0`,

equivalently `integral_bad (L^2-1) dP=0`. Thus no universal testwise replacement of the killed unit floor by `(1+epsilon) P(bad)`, for any fixed `epsilon>0`, follows from actual357 uniformity and the genuine current kernel. This statement concerns a complete fixed test; it does not assert that this test maximizes the current square supremum.

### The full original rectangle and actual old law

Put `Q=315=3^2*5*7`, and let

`D=(1,3,5,7,9,15,21,35,45,63,105,315)`.

At every original nonunit modulus `d|315`, put the forbidden class `0 mod d`. The eleven original classes are retained, including redundant ones. Their complete actual survivor set is

`S={x mod315:gcd(x,315)=1}`,

which has144 points. Let `nu` be uniform on `S`. It is the product of the uniform laws on the six units modulo9, four nonzero residues modulo5, and six nonzero residues modulo7.

At the current prime put the pure forbidden class `0 mod p`. List the eleven nonunit divisors increasingly as `d_1,...,d_11`. At the distinct original mixed modulus `d_i p`, put the CRT class

`x=1 mod d_i`, `y=i mod p`.

There are exactly23 original forbidden labels: eleven old, one pure-current, and eleven mixed. The period is exactly `315p`. Every nonunit divisor of this period has its one original forbidden label. The certificate stores all23 literal modulus/residue pairs for each prime.

The normalized actual pure-current survivor base `m` is uniform on `y=1,...,p-1`. The mixed roots1 through11 are distinct. Define the independent complete old layouts

`C(x)=sum_(d|315) 1_(x=1 mod d)`,

`A(x)=sum_(d|315) 1_(x=2 mod d)`.

Their residues differ already modulo3,5,7. No identification of the test and forbidden layouts is used.

The actual row union has exact base mass

`alpha(x)=(C(x)-1)/(p-1)`.

This is an exact union identity because every active original mixed label uses a distinct current root. The unit cofactor is absent exactly once.

### Genuine current kernels and positive charge

The complete forbidden load factors as

`C(x)=(1+1_(x=1 mod3)+1_(x=1 mod9))`
`     *(1+1_(x=1 mod5))*(1+1_(x=1 mod7))`.

At `x=1 mod315` it equals12. At every other old row it is at most8: a missing depth-two ternary match gives at most `2*2*2`, and a missing5 or7 match gives at most `3*1*2`. Hence `alpha>delta=7/(p-2)` occurs precisely at row1. Elsewhere `C-1<=7`, and `7/(p-1)<7/(p-2)`.

Use the actual BBMST density relative to `m`:

`k_x(y)=1/(1-min(alpha(x),delta))` on the actual mixed good set,

`k_x(y)=(alpha(x)-delta)_+/(alpha(x)*(1-delta))` on the actual mixed bad set,

with zero bad density when `alpha=0`. Each row is normalized. Its assigned bad mass is `beta(x)=(alpha(x)-delta)_+/(1-delta)`. At row1 the actual bad roots are1 through11, so

| p | delta | beta(1) | b=E_nu beta |
|---|---|---|---|
|17|`7/15`|`53/128`|`53/18432`|
|19|`7/17`|`61/180`|`61/25920`|

Both charges are strictly positive. Actual mixed bad points exist in other rows too, but the kernel assigns them zero mass. The full physical probability is `P=nu k`; no conditioning or change of the old marginal occurs before this step.

### One complete common test realizes the unit floor

At every original old test modulus `d|315`, choose residue2 modulo `d`. At every original current test modulus `dp`, including `d=1`, choose CRT residue `(2 mod d,p-1 mod p)`. This gives exactly24 test labels, the full exponent rectangle

`(a_3,a_5,a_7,a_p) in {0,1,2}*{0,1}*{0,1}*{0,1}`.

All choices are fixed before sampling the old row. The full test load is

`L(x,y)=A(x)*(1+1_(y=p-1))`.

Every bad point with positive physical mass lies at old row1 and current root in1 through11. At row1, every nonunit divisor test centered at2 fails, since every such divisor has a factor among3,5,7. Thus `A(1)=1`. Also `p-1` is outside1 through11. It follows that `L=1` on every bad point of positive physical mass. This proves

`integral_bad L^2 dP=b`, `integral_bad(L^2-1)dP=0`.

If `P^-` is the killed subprobability and `P^s=P^-/(1-b)` is its supported normalization, the exact identity is

`E_(P^s) L^2=1+(E_P L^2-1)/(1-b)`.

The final unit-floor conditioning formula is therefore exact for this full test as well.

### The same geometry has nontrivial joint cap information

The old square is `E_nu A^2=35/4`, and this is the exact complete old square maximum. Indeed, the one-prime ordered-pair cap sums are `10/3`, `7/4`, and `3/2`; multiplying gives `35/4`. Each pair of arbitrary original test cylinders has at most its corresponding product cap. The coherent surviving center2 attains all these caps simultaneously.

For the independent layout pair above, the three one-prime values of `E[A_p^2 C_p]` are4,2, and5/3. Hence

`E_nu[A^2 C]=40/3`, `E_nu[A^2(C-1)]=55/12`,

and the exact mixed-union cross energies are

`E_nu[A^2 alpha17]=55/192`, `E_nu[A^2 alpha19]=55/216`.

This old maximizing test can therefore be almost disjoint from the rows causing charge. It is not the diagonal `A=C` construction excluded by JL3.

For comparison with SH26, use precisely its cap envelope

`c_SH(x)=(p-1)/((p-2)*(1-min(alpha(x),delta)))`,

`c=(p-1)/(p-9)`, `D=E_nu[c-c_SH]`.

The extra testwise cap saving discarded by the SH26 unit-floor relaxation is

`Z=E_nu[(c-c_SH)(A^2-1)]`,

so `E_nu[c_SH A^2]=c*(35/4)-D-Z`. Exact computation gives

| p | `c*(35/4)-D` | `E[c_SH A^2]` | `Z` |
|---|---|---|---|
|17|`811780951/48648600`|`471459931/48648600`|`436309/62370`|
|19|`199838033/13224640`|`31651727/3306160`|`1331475/240448`|

These are values of the same SH26 cap envelope; they are not a new exact-current-maximum assertion. The strict positive covariance saving and zero excess killed loss coexist on the same source, mask, kernel and complete test. Any refinement must retain that joint geometry; a universally larger killed floor is false. No numerical bound for all generic17/19 layouts or unrestricted tails follows from this example.

The [killed-floor verifier](verify_killed_unit_floor.py) reconstructs the
[exact certificate](killed_unit_floor_certificate.json), including both finite
original families and all24 full test labels. It evaluates every physical
CRT point above the144 old survivors and recomputes the square moments,
charges, cross energy and cap covariance using exact fractions. Default mode
compares the entire saved certificate; `--write` regenerates it. These are two
separate one-step constructions from the actual357 law, not a17/19 chain
from the supported AP13 law. No Lean declaration is added.

```sh
python3 -I -O /absolute/path/to/verify_killed_unit_floor.py
```

## Shared actual-cell hinge bounds for the uniform357 law

For the same uniform complete actual357 survivor law used in CM8, SD1--SD6,
BS10 and PR, the following ordinary bounds hold for every complete original
test L, every original choice of residues and every finite exponent height:

|h|upper bound for E(L-h)+|decimal|
|--|--|--|
|3|1318076/584325|2.2557241261284386|
|4|94745926/61354125|1.5442470412543574|
|6|578163435166/676429228125|0.8547286414110404|

All three improve PR11. The same-law square bound remains3849/106. These
are maxima of a parameter relaxation, with no actual-family sharpness or
Lean verification claim. No forbidden or test label is deleted or merged.

### The actual five-cell input

First suppose the actual modulus3 and9 exclusions are effective. Reuse
exactly SD's five cells, with root map r(l)=(0,0,1,1,1), and parameters

    d_l=z-alpha_r(l)-beta_l,
    n_l=w_l d_l/9-t_l,   s=sum n_l,   x=sum w_l/9.

The parameter domain is

    w_l=1-D_l, D_l>=0, sum D_l<=1/2;
    alpha>=0, sum alpha<=1/4;
    beta>=0, sum beta<=1/4;
    t>=0, sum t<=1/72;   3/4<=z<=1.

Here n_l is the actual raw complete35 survivor mass of cell l. Its
remaining5 availability before deeper mixed deletions is d_l. For any
original pure3 test prefix at depth a>=3 lying in cell l, its raw
complete35 mass is at most d_l*3^-a. Under the raw actual pure3 survivor
measure eta, its mass is at most3^-a and cell masses are w_l/9. These are
the established SD2 input bounds. Inactive root3 or cell9 test choices may
be completed to a surviving root or cell, pointwise increasing the load.
This does not change any actual forbidden residue.

### Arbitrary monotone ternary cost

For a fixed original root/cell test choice (r,j), set

    b_l=1+1_(r(l)=r)+1_(l=j),
    Delta_a(g,b)=max_(0<=i<=a-3)[g(b+i+1)-g(b+i)], a>=3,
    P_g(r,j;m,v)=sum_l m_l g(b_l)
                 +sum_(a>=3)3^-a max_l[v_l Delta_a(g,b_l)].

For every nondecreasing g used below, this bounds its raw ternary-test
integral with cell masses m and depth caps v_l*3^-a. Add the original
depth-a indicator after depths3,...,a-1. On that indicator the preceding
deep count is an integer between0 and a-3. Its cost increment is at most
Delta_a(g,b_l). That cylinder has one fixed cell l, so integrating the
increment gives the displayed maximum. Summing proves the bound without
assuming the original prefixes are nested or coherently centered.

Write

    P^A_g(r,j)=P_g(r,j;n,d),
    P^eta_g(r,j)=P_g(r,j;(w_l/9)_l,(1)_l),
    M_eta=max_(r,j)P^eta_id(r,j).

Constants are exact in this bound: adding a constant c to g adds c times
the measure's mass. This fact is used in the complete multiplier tails.

### A positive5 convex increment retaining the actual zero5 integral

Put f_t(v)=(v-t)+. A complete35 test consists of its original zero5
ternary block A0 and all its positive5 original blocks. The actual35
survivor set S35 is contained in the product P3*P5 of actual pure survivors.
Since every added label is nonnegative,

    integral_S35 f_t(A)
      <= integral_S35 f_t(A0)
           +integral_(P3*P5)[f_t(A)-f_t(A0)].            (HC1)

The first integral retains the actual35 cell masses. Only the nonnegative
increment is enlarged to the pure product. For each fixed3 coordinate,
comonotone comparison of the5-prefix indicators bounds the second
integral by a nested family with conditional probabilities5^-e/z. All
original3 roots in each5 block are unchanged. The resulting block count
N has raw positive-tail probabilities

    z Pr(N=n)=4/5^n, n>=2.

The zero-tail event makes no increment. On an outcome with N=n, convex
Jensen gives

    f_t(A0+...+A_(n-1))-f_t(A0)
      <= g_(t,n)(A0)+(1/n)sum_(e=1)^(n-1) f_t(n A_e),
    g_(t,n)(v)=f_t(nv)/n-f_t(v).                        (HC2)

The function g_(t,n) is nonnegative and nondecreasing: it is zero below
t/n, then v-t/n through t, then the constant t(1-1/n). It need not be
convex; the ternary bound above was explicitly proved for monotone costs.
Independently maximizing each positive5 block is a valid upper bound,
not a statement that different blocks have a common maximizing layout.

Consequently the raw actual35 cost has the valid bound

    F_t=max_(r,j){P^A_(f_t)(r,j)
       +sum_(n>=2) (4/5^n)
          [P^eta_(g_(t,n))(r,j)
             +(n-1)/n max_(r',j')P^eta_(f_t(n .))(r',j')]}.   (HC3)

The original zero5 root/cell stays outside its multiplier sum. This is
the convex-cost extension of the same decomposition that yields ZG2 and
SD2 for the square. No full-Haar old law is substituted.

For the raw old first moment, the same argument specializes to

    M=max_(r,j)P^A_id(r,j)+M_eta/4.                    (HC4)

### Complete tails, with no cutoff of original heights

Only thresholds t in {1,6/5,4/3,3/2,2,3,4,6} are needed. Let
N_t=max(2,ceil(t)). For n>=N_t and v>=1,

    f_t(nv)=nv-t,
    g_(t,n)(v)=min(v,t)-t/n.

Thus the entire n>=N_t contribution inside HC3 is exactly bounded by

    5^(1-N_t)[P^eta_(min(.,t))(r,j)-t*x
                       +(N_t-3/4) M_eta].             (HC5)

This uses the full geometric mass and first moment, not a renormalized
finite sample. For the ternary coefficient sums, all cost breakpoints
are at most6. Delta_a is therefore constant for a>=10 in every cost
appearing here. The program sums depths3 through10 and adds the exact
remaining coefficient1/(2*3^10). Every original depth remains covered.
When a finite physical height omits later labels, complete them with
arbitrary fixed test residues before these nonnegative comparisons;
the added indicators only increase the load and all displayed geometric
sums remain valid upper bounds for the original finite test.

### Pure7 comparison and actual mixed7 deletion

Under the actual pure7 survivor probability, every positive depth-e
test prefix has probability at most(6/5)7^-e. Comonotone comparison and
Jensen therefore use the complete auxiliary count

    Pr(N7=1)=29/35,
    Pr(N7=n)=36/(5*7^n), n>=2.

On the product of the actual uniform35 law and actual pure7 law, a
complete full test satisfies, for integer h in {3,4,6},

    s E f_h(L) <= B_h,
    B_h=(29/35) F_h
          +sum_(2<=n<h)36*n/(5*7^n) F_(h/n)
          +(6/5)7^(1-h)[(h+1/6)M-h*s].               (HC6)

The final term includes every N7>=h. Each coefficient F_(h/n) uses the
same actual five-cell parameters. Its independent maxima only enlarge
the expectation; they do not authorize adaptive original test residues.

The raw nonunit35 cylinder cap from SD3 with constant unit weight is

    T=max_r sum_(r(l)=r)n_l+max_l n_l+max_l d_l/18
       +sum_l w_l/36+max_r sum_(r(l)=r)w_l/36
       +max_l w_l/36+1/72.                            (HC7)

Let B be the actual mixed7 forbidden union. The same-family bound is
Pr(B)<=T/(5s), and the existing SD parameter domain guarantees s-T/5>0.
The signed conditioning identity gives

    s E[(f_h(L)-C)1_(B^c)]
      <= B_h-C*s+(C/5)T.                              (HC8)

Indeed L is at least the retained root/cell load b_l<=3. At the current
thresholds f_h(b_l)=0, so the safe deletion weight is exactly C. The
two-anchor signed rebate vanishes; no nonexistent hinge rebate is
claimed. The actual deletion union and the same s,T remain in the
denominator, and conditioning gives exactly the original uniform357 law.
Therefore C(s-T/5)>=B_h suffices.

### Continuous parameter domain and all missing-class branches

For each fixed original root/cell and each selected branch of every
maximum in HC3--HC7, each expression is affine separately in the five
groups D,alpha,beta,t,z. Terms such as w_l d_l use different groups. All
maxima in F,M,T have nonnegative coefficients; the subtracted tail terms
are affine. Hence the target margin C(s-T/5)-B_h is concave separately
in each group. Repeated convex interpolation proves its nonnegativity
throughout the product domain if it is nonnegative at every product
vertex. There are6*3*6*6*2=1296 vertices. The exact verifier checks every
one for the three stated targets, with minimum margin zero in each case.
The scaled denominator(5/6)(s-T/5) has minimum53/432>0.

The five-cell domain covers all four effective9 branches, including
missing modulus5 or7 and arbitrary higher pure exclusions. For the eight
cases where modulus3 is absent or modulus9 absent/ineffective, reuse the
established corresponding PR profile. The verifier reads and checks all
twelve branches. Every fallback at3,4,6 lies below the stated respective
generic bounds; no branch is omitted.

### Reuse and verification scope

The source inputs are CM2, SD1--SD6, ZG2 and PR1--PR11. The repository
ArbitraryRootEventMoment module supplies the square-specialized root-tail
estimate; the present monotone-cost increment is proved directly above.
The repository ConditionalComparison/Supermodular supplies the finite
comonotone comparison, and pinned Mathlib Analysis/Convex/Jensen supplies
ConvexOn.map_sum_le. No exact current shared-cell hinge endpoint was found
in those searched declarations or the ordinary report. The BBMST source
arXiv1811.03547 was reachable (HTTP200); no literature-priority claim is
made. This argument and its exact coefficient checks are ordinary
mathematics, not an end-to-end Lean formalization.

### Consumer on the same actual AP(4,6) law (HC9)

Pointwise translation of the new third hinge, and convexity in the
threshold, also give the same-law bounds

    h1<=2+h3=2486726/584325,
    h2<=1+h3=1902401/584325,
    h5<=(h4+h6)/2=811368634658/676429228125.

In particular E L<=1+h1=3071051/584325. These lower the complete-test
first moment, not the distinct sum of individually maximized cylinder
masses; that latter observation is left unchanged. Retain PR's original
AP kernels and physical square324599/3816. Substitution of this stronger
same-law profile into the established full-tail charge formula gives

    b11 <= 47372963/184062375,
    b13 <= 9492718910453/38266567762500,
    rho13 >= 18925009844347/38266567762500
           >0.4945572846,
    Gamma13 <= 6471426752685569/37850019688694
             <170.975518796,
    supported_Haar_density <=1039695426000000/18925009844347.

The raw physical Haar density remains1440/53. The supported Haar density
is consequently at most(1440/53)/rho13. These are improved observations
of the same full actual AP13 law. They do not themselves provide a17/19
joint certificate or a later-prime continuation. The preceding PR
certificate is kept intact and is a pinned input of this separate result.

The [shared-cell verifier](verify_shared_cell_hinges.py) reconstructs the
[exact certificate](shared_cell_hinges_certificate.json), including all1296
parameter vertices, all12 original-class branches and the same-law AP13 consumer.
Its preceding PR input is pinned by SHA-256; default mode compares every
certificate field, while `--write` regenerates the certificate.

## Complete hinges and actual continuation from supported AP13

For the same actual AP(4,6) supported13 law, the shared-cell source
profile gives a complete-load mean bound

    M13<=2621130891614589/246025127976511
         =10.653915366989825... .                        (SP1)

Its complete hinge profile supplies two positive continuations:

    Gamma17<=71411032739803777721269/176909701938094610544
             =403.65809199538637...;
    Gamma19<=14309324828593686784688579/6107986643845861414296
             =2342.7236605062217... .                    (SP2)

The first applies actual pure-base AP17/T8 and then conditions. The
second starts from supported13, applies AP17/T8 and AP19/T8 physically,
and conditions only after19. It does not use the first construction's
conditioned17 output. Every original label, arbitrary residue and
finite height is retained. These are ordinary mathematical results,
not Lean declarations or an unrestricted Erdős7 solution.

### Same actual source law and unbounded initial profile

Let nu357 be uniform on the full actual357 survivor set. The unchanged
square bound is G=3849/106. HC1--HC8 strengthen its complete-test hinges
at3,4,6. The elementary inequalities

    H357(1)<=2+H357(3),
    H357(2)<=1+H357(3),
    H357(5)<=[H357(4)+H357(6)]/2

give the source complete-load mean M=1+H357(1)<=3071051/584325.
M bounds the complete-load mean; it does not rename the earlier
independently stated cylinder-sum bound. The shared-cell certificate
retains the stronger1--12 profile, including PR's other knots and all
original missing-class branches.

PR7--PR11 supply arbitrary further thresholds. For each of its twelve
branches let u3,u5,u7 be the reference pure masses and D the same-law
Haar density bound. Let V be the product of three independent prefix
counts with tails Pr(Kp>=e)=p^-e/u_p. Then

    E_nu357(L-t)_+<=D*u3*u5*u7*E(V-t)_+.

At an integer h, the exact identity

    E(V-h)_+=E V-h+sum_(n<h)(h-n)Pr(V=n)

uses the full geometric mean and finitely many lower product
probabilities. Take the maximum over twelve branches, and the minimum
with valid same-law moment bounds. Consecutive integer chords bound
the actual convex hinge between integers; for t<=1 use H357(t)<=M-t.
No distribution is truncated or renormalized.

For positive integer-valued L and integer h>=1, the unit-floor bound

    E(L-h)_+<=(G-1)h/(4h^2-1)                           (SP3)

also holds. For L<=h it is immediate. For L>h the pointwise difference
after clearing the denominator is `(L-2h)(h(L-2h)+1)>=0`, since L-2h
is an integer. The same formula applies below with the supported13
square bound. The numerical consumer only needs knots through17, so
the verifier extends1--12 through17 by these full-tail formulas. The
underlying profile construction applies at every real threshold.

### Full physical11/13 comparison and one conditioning

Apply actual pure-survivor AP11/T4 and AP13/T6 without intermediate
conditioning. Their physical law mu13, conditioned once on all actual
survivors after13, is precisely the same nu13 used in PR. The
shared-cell certificate strengthens its observations to

    rho13>=r=18925009844347/38266567762500>0,
    Gamma13<=g=6471426752685569/37850019688694.           (SP4)

AP1--AP5 compare full labelled tests to independent auxiliary factors
N11,N13 with caps c11=5/3,c13=2 and

    Pr(Np=1)=1-cp/p,
    Pr(Np=v)=cp(p-1)p^-v, v>=2,
    E Np=1+cp/(p-1).

Put N=N11*N13; its complete mean is49/36. The prefix caps hold on
every physical history, so for all t>=1,

    E_mu13(L-t)_+<=U(t):=E_N[N H357(t/N)].              (SP5)

These are comparison variables, not independent actual forbidden
events. No adaptive original test residues are chosen. Since
H357(t/n)=M-t/n for n>=t, the exact full-tail formula is

    U(t)=sum_(n<t)Pr(N=n)*n*H357(t/n)
             +M E[N;N>=t]-t Pr(N>=t).                  (SP6)

Subtract finite parts from the full probability1 and mean49/36 to
evaluate both tails. Every real t>=1 has a finite low-part evaluation
with the complete remaining tail retained.

For a>=t>=1, `(L-t)_+<=a-t+(L-a)_+`. Nonnegativity of the hinge and
the proved positive lower normalizer r give

    H13(t):=sup_L E_nu13(L-t)_+
       <=inf_(a>=t)[a-t+U(a)/r],
    sup_L E_nu13 L<=a+U(a)/r, a>=1.                    (SP7)

The second bound at a=6 gives SP1. Use a=6 for retained integer t<=6,
a=t for retained integers above6, and the minimum with SP3 at G=g.
The program checks the selected witnesses among1,...,17; it does not
claim a global minimum over every real a.

|t|H13(t) upper bound|
|---|---:|
|1|9.653915366989825...|
|2|8.653915366989825...|
|4|6.653915366989826...|
|6|4.653915366989826...|
|8|3.296496079559025...|
|12|1.845797624615341...|
|17|1.0561291774771513...|

In particular,

    H13(6)<=1144980123755523/246025127976511,
    H13(8)<=2583101470464529227/783590032605187535.       (SP8)

The certificate retains all17 consumer knots and every auxiliary tail
mass and mean. Chords give intermediate bounds; SP5--SP7 give a full
function beyond the table. These are simultaneous observations of one
actual law, without asserting that the upper envelope is itself a
comparator probability distribution.

### Single17 continuation

From nu13 use actual pure-base AP17/T8, delta=7/15 and full-Haar cap2.
Its assigned charge is at most H13(8)/8<1; the unconditioned square
is at most(89/64)g. The ordinary AP bound gives

    Gamma17<=1+[(89/64)g-1]/[1-H13(8)/8]
             =403.70034396394783... .                   (SP9)

Keeping SH26's natural-cap deficit improves this to SP2. The exact
combined SH27 charge and energy cost is

    h17,W(z)=W(z-8)_+/8
               +(50/256)[16/(16-min(z,8))-2].

Above its convexity threshold it is increasing and convex. Its
integer values expand as a constant and nonnegative coefficients of
L-1 and (L-j)_+. Substitute SP1 and SP8, then solve the affine SH28
inequality in W. The verifier checks the coefficients and criterion
at the resulting W. Among integer thresholds1,...,15, threshold8 gives
the smallest bound from this functional. No other-kernel or
real-threshold optimality is claimed. The resulting actual17 law has
positive survival at arbitrary original17 heights and residues.

### Two distinct17/19 continuations

The consumer checks all255 pairs T17 in{1,...,15}, T19 in{1,...,17}
in each of two constructions:

* Restart: form nu13 as in SP4, then apply17 and19 physically and
  condition only after19. Source observations are g, SP1 and SP7.
* One final conditioning: start from uniform nu357, physically apply
  11/T4,13/T6,17/T17,19/T19, and condition only after19. Use the
  shared-cell357 profile with M,G; no supported13 observation or
  normalizer is inserted midway.

At p set d=p-1-T, cp=(p-1)/d, ap=(3p-1)/(p-1)^2, and let fp be the
product of later square-growth factors. The existing SH27 cost is

    hp,W(z)=W(z-T)_+/d
              +fp*ap[(p-1)/(p-1-min(z,T))-cp].

It is increasing and convex for W>=fp*ap*cp. Its complete integer
expansion has nonnegative mean and hinge coefficients. Earlier
auxiliary products use individual probabilities below T and the
full tail mass and mean for every remaining affine cost, as in SP6.

Write AW+B for the sum of certified costs. The SH28 residual is
I+(A-1)W, with

    I=G_source*product_p(1+ap*cp)-1+B.

Every tested schedule has I>0. If A>=1 the functional has no finite
solution. Otherwise set W=max(W_min,I/(1-A)) and check the full
criterion there; SH28 gives positive actual survival and supported
square at most1+W. The program separately verifies the complete
integer identity and residual at W=483 in all510 schedules.

There are72 finite sufficient bounds for the supported13 restart and
59 for four physical steps. The best in each uses T17=T19=8:

    Gamma19_restart<=14309324828593686784688579
                         /6107986643845861414296
                    =2342.7236605062217...,
    Gamma19_once<=81121527504111209187751525
                         /33163008211196445012696
                    =2446.1450236207183... .            (SP10)

Both yield actual positive survival for arbitrary finite original
families supported on3,5,7,11,13,17,19. No literature-priority claim
is made for this prime-support consequence. The first does not pass
through the conditioned single17 law from SP2.

|construction|minimum A among255|minimum residual at W=483|
|---|---:|---:|
|supported13 restart|0.8650551339908986...|242.74759569039884...|
|four physical steps, one conditioning|0.9354945670061158...|121.19490304202002...|

The least W483 defect in both is at T17=6,T19=8, distinct from the
best finite-bound schedule. All residuals are positive; no stated
integer schedule reaches484 through this upper functional. This does
not lower-bound actual charges or moments, exclude noninteger
schedules, refute the covering theorem, or exclude a certificate
using actual joint bad-set/test observations.

The implementation reuses generic `build_step` and `verify_at` from
the pinned `verify_pg1_scalar_schedule.py`. Its PG1 data loader and
13/T5 whole-N2 improvement are never called: the source is the
shared-cell strengthening of actual AP13 and all13 steps have
threshold6. A check rejects any different-law improvement in a row.
Source certificates and reused code are SHA-256 pinned. Default mode
validates the entire JSON; `--write` regenerates it. Duplicate keys
and changed fractions are rejected under `python3 -I -O`.

Published PR certificates remain unchanged. The finite computations
verify displayed constants and schedule outcomes; arbitrary-height
claims use the ordinary argument above.

The [supported13 profile verifier](verify_supported13_hinges.py) checks the
[exact profile and continuation certificate](supported13_hinges_certificate.json).
It uses the generic coefficient routines of the preceding pinned program,
without its PG1 law-specific data or threshold5 improvement.

## Finite-core stability for the actual pure-base AP law

For every finite original family on3,5,7,11,13, use its actual uniform357
survivors, its actual pure-base AP11/4 and13/6 kernels, and one final
conditioning. Let nu_F be this supported law. Let F_b retain exactly its
original forbidden labels whose five exponents are at most b, with all
residues unchanged. Construct nu_b by the identical rule applied to F_b.
Both probabilities are lifted to one common finite physical period.

There is an explicit uniform bound E_b, proved below, such that

    |Gamma_full(nu_F)-Gamma_box_b(nu_b)| <= E_b.          (APC1)

The exact certificate gives

| b | E_b upper |
|---|---:|
|11|0.803401658|
|14|0.042600351|
|16|0.005840800|

Every omitted original forbidden class and every omitted test pair enters
a complete positive tail. This result concerns the pure-base AP(4,6)
probability, not the earlier AO full-Haar probability. The core law need
not avoid the omitted forbidden classes; the full nu_F does avoid them.
The finite core maximum is not computed by this error estimate.

The source constants are those of PR2 and the stronger shared-cell
hinge continuation (HC9):

    G0=3849/106, D0=432/53,
    r=18925009844347/38266567762500,
    G=6471426752685569/37850019688694,
    D=1039695426000000/18925009844347.

Every complete actual357 uniform law has square at most G0 and Haar
density at most D0. Both actual AP13 probabilities have square at most G,
Haar density at most D, and unconditioned final retained mass at least r.
These bounds hold for every original finite height, including missing
classes and uniform padding to a larger common physical period.

### Weighted variation before the current-prime steps

For two finite positive measures on one old period, put

    Delta2(sigma,tau)=sup_A integral A^2 d|sigma-tau|,
    Delta0(sigma,tau)=integral d|sigma-tau|,

where A ranges over complete old divisor tests with independently chosen
residues at each original label. Delta0 is L1, twice the probability
convention for total variation when both measures are probabilities.

Use the previously proved localized two-test/one-query factor

    Phi_p(a)=(a+1)^2+2(a+1)/(p-1)+(p+1)/(p-1)^2,
    Sigma_p=p(p^2+4p+1)/(p-1)^3.

For a prime set S, define complete query-label tails

    T0(S,b)=product_(p in S)p/(p-1)
             -product_(p in S)sum_(a=0..b)p^-a,
    T2(S,b)=product_(p in S)Sigma_p
             -product_(p in S)sum_(a=0..b)p^-a Phi_p(a).

The second sum truncates only the queried forbidden label. Both test
axes remain complete, as in the cubic-tail result preceding PP1.

Let S_full subset S_core be the actual357 survivor sets for F and F_b,
with Haar masses s and s0. Put delta=s0-s. Their uniform laws mu,mu0
satisfy the exact identity

    integral A^2 d|mu-mu0|
      = (delta/s0) E_mu A^2
          +(1/s0) integral_(S_core\S_full) A^2 dHaar.

The removed set is contained in the union of omitted original357
cylinders. Their probability sum is bounded by T0, and their localized
square sum by T2. Since s0>=1/D0, this proves simultaneously

    Delta2(mu,mu0)<=e0w=D0[G0*T0(357,b)+T2(357,b)],
    Delta0(mu,mu0)=2delta/s0<=e0m=2D0*T0(357,b).        (APC2)

The square expectation in the first term is under the full actual
uniform law. The second term is an unnormalized Haar integral over the
removed set; no observation from a different supported law is inserted.

### Physical and killed kernel comparisons at11 and13

The weighted WT4 proof applies with any fixed admissible pure-base
threshold T, rather than only T=8. Set

    s_*=(p-2)/(p-1), delta=(T-1)/(p-2),
    C=1/(1-delta), ell=max(C^2,C/delta).

Use T=4 at11 and T=6 at13. The pairs (C/s_*) are respectively5/3 and2.
All delta lie strictly between zero and one. The actual pure survivor
bases have Haar mass at least s_*, in both full and core families.

For a source probability bounded by D_* times Haar and with every
complete square at most J_*, define for i=0,2

    z0(p)=1,       u0(p)=p/(p-1),
    z2(p)=Phi_p(0),u2(p)=Sigma_p,
    t0(p,b)=sum_(a>b)p^-a,
    t2(p,b)=sum_(a>b)p^-a Phi_p(a),
    H_i(S,b)=product_(q in S)[u_i(q)-t_i(q,b)]
                 -product_(q in S)z_i(q).

Here H_i excludes the unit old cofactor exactly once. Put J_0=1,
J_2=J_*. The error for the i-th weighted comparison is

    e_p,i = D_* T_i(S,b)
             [(C/s_*)(u_i(p)-z_i(p))
                    +(ell/s_*^2)z_i(p)/(p-1)]
           + D_* H_i(S,b)
             [(C/s_*)t_i(p,b)+(ell/s_*^2)z_i(p)t0(p,b)]
           + J_i[(C/s_*)t_i(p,b)
                    +((ell+C)/s_*^2)z_i(p)t0(p,b)].    (APC3)

The three terms respectively cover old cofactors outside the box at
all positive current depths; nonunit old cofactors inside the box at
current depth above b; and omitted pure current classes. These regions
are disjoint and exhaust all omitted current forbidden labels.

For i=2 this is exactly WT4's weighted proof with the stated thresholds.
For i=0, repeat its pointwise physical or killed kernel comparison with
weight1. A mixed query of old modulus d then has old mass at most D_*/d,
and the current Haar query mass is p^-a; the two full test axes are absent.
This replaces Phi by1, Sigma by p/(p-1), and J_* by1. The pure-base
comparison still pays both the common-region coefficient variation and
the changed region, hence the coefficient ell+C remains. L1 is not
replaced by probability total variation in APC3.

At11 use S={3,5,7},D_*=D0,J_*=G0. At13 use S={3,5,7,11},
D_*=(5/3)D0,J_*=(23/15)G0. These are unconditioned physical11 bounds
under either construction. Its killed measure is dominated by its
physical measure, so the same direct error estimates apply to killed
chains as well.

For a common physical or killed kernel of mass at most1, WT5 gives
Delta2 propagation factor1+c(Phi_p(0)-1); these are23/15 at11 and55/36
at13. Delta0 contracts with factor1. Comparing the two kernels under the
full old measure, then propagating the change of old measure through the
same core kernel, yields for both physical and killed final measures

    ew=(55/36)[(23/15)e0w+e11,2]+e13,2,
    em=e0m+e11,0+e13,0.                                (APC4)

The killed chain is mu K11^- K13^-; it retains exactly those points that
avoid the old family and both actual current masks. No intermediate
conditioning is introduced. The physical chain is normalized on every
history, including histories previously marked bad.

### Final normalization and the complete original test tail

Let eta,eta0 be the two killed13 measures, with masses q,q0>=r. Their
normalizations are nu_F and nu_b. The exact decomposition

    nu_F-nu_b=(eta-eta0)/q + ((q0-q)/q)nu_b

and |q-q0|<=em give, for every complete old test A,

    Delta2(nu_F,nu_b)<=eNw=(ew+G*em)/r,
    Delta0(nu_F,nu_b)<=eNm=2em/r.                      (APC5)

The bound G is valid for nu_b because F_b is itself an arbitrary actual
five-prime family using the identical construction. Thus the two terms
in APC5 do not mix the AO and AP probabilities. The first inequality
bounds integrals against absolute measure difference, not merely the
difference between two separately maximizing tests.

For any probability of Haar density at most D, the previously proved
full original two-test tail is

    tail_test(S,b,D)
       =D{product_(p in S)p(p+1)/(p-1)^2
                 -product_(p in S)[1+sum_(a=1..b)(2a+1)p^-a]}.

It bounds E(L_full^2-L_box^2) for every complete layout. Applying it
to nu_b and APC5 to the identical full layout gives APC1 with

    E_b=eNw+tail_test({3,5,7,11,13},b,D).              (APC6)

For the opposite direction, extend each box test to the complete
original inventory. Its extra indicators are nonnegative, so APC5 alone
bounds Gamma_box(nu_b)-Gamma_full(nu_F). No equality of maximizing
layouts is assumed.

All tests are lifted to the same period before comparison. A core
kernel depends only on retained low coordinates, so the construction
from F_b is a rational law on that finite core lifted by independent
uniform higher digits. If an original height is below b, intersect the
box with the physical inventory; uniform padding yields the same bounds.

### A completely finite reference for the17/19 joint criterion

Start with the full actual nu_F at13 and the two actual pure-base
AP17/8,AP19/8 kernels, with no intermediate conditioning. First apply
WT1--WT11 with the stronger same-law HC9 density and square bounds: keep old cofactor exponents at most20 and current
forbidden depths at most8 in both future masks, including pure depth8.
This costs the exact allowance

    e_mask=0.26221638911048406... .

At this intermediate stage the incoming probability and all tests
remain full. Now replace only the incoming probability by the actual
AP13 core law nu_20, holding the two reference kernels fixed.
For a common two-kernel continuation, the weighted variation factor is

    k17*k19=(89/64)(59/45)=5251/2880.

Each assigned charge is the expectation, under the initial probability,
of a fixed function with values in[0,1]. For the19 charge this function
already integrates the normalized reference17 kernel. Two probabilities
have difference of total mass zero, so each such expectation changes
by at most half their L1 distance. The sum of the two charge changes
is at most their L1 distance, not twice that distance. Thus changing
the incoming law costs at most

    e_incoming=(5251/2880)eNw_20+483eNm_20.             (APC7)

Finally retain only test labels with all seven exponents at most20.
The final reference physical density is at most(18/5)D. Its test-tail
cost is

    e_test=tail_test({3,5,7,11,13,17,19},20,(18/5)D)
          =8.512798422966208e-06... .

Every ordered test pair with an omitted label is included in this
positive tail. The exact complete allowance is

    e_mask+e_incoming+e_test
        =0.2624239752577702... <263/1000.             (APC8)

Consequently, it suffices to prove on this finite reference

    E_finite[L_box^2-1]+483 B_finite<=483-263/1000       (APC9)

for every complete box20 test and every retained original family
pattern. The reference is fully specified: actual incoming AP13 core20
law; actual future kernels with old-cofactor box20 and current/pure
depth8; and test box20. All are computable on a common finite period
dividing (3*5*7*11*13*17*19)^20. The surviving family pattern still
records every retained original modulus and its original residue.

If APC9 holds for a given retained pattern, APC8 gives a strict
positive slack for the full functional E_actual(L^2-1)+483B_actual<483.
As in WT10 this implies B_actual<1 and a supported complete-square
bound484 after one final conditioning. No assumption of final survival
was made to construct any of the physical kernels.

APC9 has not been proved uniformly or evaluated over all finite
patterns. The period and number of patterns are not claimed small.
Further prime continuation is also still required for unrestricted
Erdős7. The finite reduction is an ordinary mathematical result with
an exact arithmetic certificate; it is not an end-to-end Lean theorem.

The adjacent exact verifier reconstructs these bounds from the shared-cell
hinge, pure-root and weighted-kernel certificates, each pinned by SHA-256.
It checks every whole certificate field. The displayed decimals are for
reading; all acceptance comparisons use rational arithmetic.

The [AP-core verifier](verify_ap_core_stability.py) checks the
[exact certificate](ap_core_stability_certificate.json). Its three source
certificates are pinned by SHA-256. Default mode verifies; `--write` regenerates.

## Full original heights can make both SH26 joint savings vanish

At each of p17 and p19 there is a genuine pure-base BBMST step at threshold `T=8`, starting from a uniform complete actual357 survivor law, for which one complete original test has all of the following properties:

* its zero-current-exponent old block is nonconstant;
* all positive-current-exponent old layouts are distinct from each other and from the zero block;
* the actual assigned bad mass is strictly positive;
* the entire cap-covariance correction dropped by SH26 is zero;
* the actual killed excess `integral_bad(L^2-1)` is zero.

The construction retains all original test labels through its actual highest current exponent. The cap statement refers specifically to SH26's generic pure-density envelope. The actual pure density provides a separate strictly positive cap improvement, displayed below. The test is not a current-square maximizer; this example does not decide a tradeoff restricted to maximizing tests or their common dual mixtures.

### Actual old source and current pure law

Use the following parameters:

| p | current height H | old Q | old source size | full original period |
|---|---|---|---|---|
|17|4|`945=3^3*5*7`|432|78927345|
|19|8|`2835=3^4*5*7`|1296|48148401221235|

For every original nonunit divisor d of Q, keep the forbidden class `0 mod d`. The complete actual old survivor set is `S=(Z/QZ)^*`; let nu be uniform on S. Set `x0=1`, `x1=1+Q/3`, so `x1=316` or946. Both points belong to S.

The only current pure forbidden class is `0 mod p^H`. The actual pure base m is uniform on the `n=p^H-1` other current points; its Haar mass is `lambda=1-p^-H`. Set

`delta=7/(p-2)`, `C=1/(1-delta)`.

For these heights `M=delta*n` is an integer. Its H base-p digits, from the coefficient of `p^(H-1)` downward, are

| p | M | base-p digits |
|---|---|---|
|17|38976|`(7,15,14,12)`|
|19|6993231840|`(7,15,12,5,11,3,6,13)`|

Write these digits as b1,...,bH. Decompose M into disjoint current prefix cylinders as follows. At depth1 use roots1,...,7. The remaining prefixes lie inside root8. Starting with prefix r=8, at depth e>=2 use the b_e children `r+j p^(e-1)`, `0<=j<b_e`, and then continue inside the unused child `r+b_e p^(e-1)`. A depth-e cylinder contains `p^(H-e)` current points. These cylinders are pairwise disjoint and their total size is exactly M. All avoid the excluded pure leaf0 and the clean root p-1.

### Original mixed labels and the exact threshold row

At depth1 assign roots1,...,7 respectively to old divisors

`(3,5,7,9,15,21,35)`,

with old residue1. All seven divide Q/3. At each depth e>=2, assign its b_e disjoint current prefixes to the first b_e nonunit divisors of Q in increasing order, also with old residue1. There are15 or19 available old nonunit labels, so every depth budget fits. Different current exponents remain different original modulus labels.

Finally add the original modulus Qp with old residue x1 and current root9. Its old cofactor was not used among the seven depth1 classes. This extra current cylinder is disjoint from all preceding cylinders. Thus original moduli remain distinct, and every actual mixed current cylinder is globally disjoint from every other one, even when the old projections overlap.

There are65 forbidden classes at17 and93 at19, including all original old classes and the one current pure class. The certificate gives every literal CRT modulus/residue pair. No original forbidden label is silently merged.

For every old row x, the actual mixed fraction is therefore the exact positive sum

`alpha(x)=n^-1 sum_(d,a,e,r) p^(H-e) 1_(x=a mod d)`.

At x0 every original prefix in the M decomposition is active and the extra Qp class is inactive. Hence `alpha(x0)=M/n=delta` exactly.

At x1 all seven original depth1 classes remain active. At a deeper exponent, only old cofactors having the maximum ternary exponent can cease to match; there are exactly four such possible old labels. Thus the total lost current mass is at most

`4 sum_(e=2)^H p^(H-e) < 4 p^(H-1)/(p-1)`.

The new root9 adds `p^(H-1)` current points. Since p-1>4, `alpha(x1)>delta`. The exact fractions are

| p | alpha(x0) | alpha(x1) | beta(x1) | assigned mass b |
|---|---|---|---|---|
|17|`7/15`|`1067/2088`|`463/5568`|`463/2405376`|
|19|`7/17`|`2612524913/5661187680`|`281447633/3330110400`|`281447633/4315823078400`|

Here `beta=(alpha-delta)_+/(1-delta)`. In fact only x1 has positive beta: without the extra Qp cylinder every row's active subset has at most M points, and that extra class is active only at x1.

Every actual bad set is contained in current roots1,...,9. In particular alpha<1 in every row. Use the genuine normalized BB density relative to m,

`k_x=a(alpha) 1_(B_x^c)+[beta(alpha)/alpha] 1_(B_x)`,

where `a(alpha)=1/(1-min(alpha,delta))` and the bad coefficient is zero at alpha=0. Its row mass is exactly1. Let P=nu k and let B be the actual mixed bad event. The old marginal remains nu and `P(B)=b>0`.

### Complete independent old test blocks

For the zero-current-exponent test block, use residue0 at every nonunit old divisor except Q, where the test residue is1. Its complete old load is

`A0(x)=1+1_(x=x0)` on S.

For each positive current exponent e, use old residue0 at every nonunit divisor except Q, where the residue is3e. Each of these residues is divisible by3, so every nonunit test in that block is inactive on S. Thus

`Ae(x)=1` for every x in S and every e>=1.

The layouts are nevertheless independent and distinct: their Q-label residues are `1,3,6,...,3H`. This is a concrete choice of different original layouts, not an assumption identifying the arbitrary blocks in SH26.

At every positive current exponent e and every old test divisor d, choose current prefix `p-1 mod p^e`. This specifies one literal CRT test at every original divisor `dp^e`, `d|Q`, `0<=e<=H`. There are80 tests at17 and180 at19. The full test load is exactly

`L(x,y)=A0(x)+sum_(e=1)^H 1_(y=p-1 mod p^e)`.

All positive current test prefixes lie inside the clean root p-1, whereas every actual mixed bad prefix lies on roots1 through9. Consequently L=A0 on B. Since beta(x0)=0 and A0=1 away from x0,

`integral_B(L^2-1)dP=E_nu[beta(A0^2-1)]=0`.

The zero block is nonconstant, with

`E_nu(A0-1)=1/432` at17 and `1/1296` at19.

### The complete SH26 cap-covariance sum

Use precisely SH26's generic envelope

`c=(p-1)/(p-9)`,

`c_actual(x)=(p-1)/[(p-2)(1-min(alpha(x),delta))]`.

Its nonnegative discarded covariance correction, before any all-height enlargement, is

`Z=sum_((e,f)!=(0,0), 0<=e,f<=H) p^-max(e,f)`
`    * E_nu[(c-c_actual)(Ae Af-1)]`.

If both exponents are positive, Ae Af-1=0. If exactly one exponent is zero, Ae Af-1 is the indicator of x0. At x0, alpha=delta and hence c_actual=c. Every ordered-pair summand is therefore zero, so Z=0 exactly. This uses every original current depth and every original old test label. It does not truncate either inventory or take a limiting probability.

Combining the two results gives `Z=integral_B(L^2-1)dP=0` with positive b and nonconstant A0. A positive height-uniform lower bound on their sum cannot follow merely from these observations. In particular the discrete alpha gap for one current digit does not survive the full original current-height domain.

### Two limits on the conclusion

The actual pure mass lambda is much larger than SH26's generic lower bound `(p-2)/(p-1)`. Reading it gives the stronger actual full-Haar cap `C/lambda`, which remains strictly below c even at alpha=delta:

| p | SH26 ceiling c | actual pure-density ceiling C/lambda | difference |
|---|---|---|---|
|17|2|`83521/44544`|`5567/44544`|
|19|`9/5`|`16983563041/9990331200`|`999033119/9990331200`|

This separate pure-density saving is positive. The simultaneous-zero result does not remove it and does not rule out a stronger tradeoff that retains actual pure geometry.

The displayed full test is also not maximizing. Its original zero-layer modulus3 test is residue0, inactive on S. Changing that single test to residue1 adds the indicator of a set of old mass1/2. Since L>=1, its physical square rises by at least3/2. Thus no assertion about a common maximizing test or a dual mixture is supplied. Whether those extra optimizing constraints force a useful uniform saving remains unverified here.

### Exact verification

The adjacent verifier reconstructs every original forbidden and test class, checks all current-prefix intersections for disjointness, and computes every old row's exact mask count. This covers all current points by exact disjoint-cylinder cardinalities, including the entire period48148401221235 at19. It does not sample that period or normalize a truncated current law.

It checks every row's genuine kernel normalization, all distinct old block layouts and their loads, the entire ordered-exponent covariance sum, positive charge, and exact killed excess. It also reconstructs the full physical and killed test squares using the exact clean-prefix first and second count sums. Default operation compares `certificate.json`; `--write` explicitly regenerates it. Run `python3 -I -O /tmp/erdos7-0916/current-joint-tradeoff/verify.py`. This is ordinary mathematics and exact finite verification, with no new Lean declaration or canonical status claim.

The [joint-zero verifier](verify_current_joint_zero.py) reconstructs the
[complete-label certificate](current_joint_zero_certificate.json). Default
mode verifies every field; `--write` regenerates. It evaluates the whole
current period by exact disjoint-prefix cardinalities, without sampling.

## RRO53 and the current-prime root-overlap interface

[RRO53.5](https://github.com/the-omega-institute/trureturing/blob/387d32951f23706f94532f9165699764966ea655/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L22220) classifies the
complete graph of unit-pair sums, including pairs on either side of any
chosen bipartition. The finite-core current-prime interface keeps only
the overlap between forbidden roots and test roots. Its exact capacity
is different.

Let L and R be finite sets of distinct original labels at one fixed
current-prime depth, and let Omega be the alphabet of effective roots,
of size q. Given maps a:L->Omega and b:R->Omega, put an edge ij exactly
when a(i)=b(j). Labels remain distinct even when their roots coincide.
For a proposed bipartite graph G on these fixed sides, let c_+(G) count
its components containing an edge; let i_L and i_R indicate whether it
has an isolated vertex on the respective side. Then such root maps
exist if and only if

    every component containing an edge is complete bipartite
        with the specified left and right sides, and
    c_+(G)+i_L+i_R <= q.                              (CR1)

Proof. Every edge equates its two root labels, so all vertices of a
connected component containing an edge have the same root. Every
cross-side pair in that component must therefore be an edge. Two such
components cannot use the same root, since each contains both a left
and a right vertex, which would create cross-component edges. An
isolated vertex cannot use a root already used by any edge component.
If isolated vertices occur on both sides, their two sets of used roots
must be disjoint, or an edge would join an isolated left/right pair.
This proves necessity. For sufficiency, give each edge component one
distinct root; give all left isolated vertices one additional root if
needed, and all right isolated vertices another distinct additional
root if needed. This realizes exactly every edge and nonedge. Empty
sides and empty graphs are covered by the same rule.

At depth1, if the actual pure modulus-p forbidden root a0 exists, its
entire root is absent from the pure base. Keep every original label in
the inventory; mark labels with that root inactive, with zero current
contribution. Apply CR1 only to the remaining effective left/right
vertices, with q=p-1. The inactive labels are not ordinary isolated
vertices and do not consume colors in CR1. If the pure modulus-p class
is absent, the safe full alphabet has q=p. Thus the respective generic
depth1 capacities are16 or17 at17 and18 or19 at19.

For active depth1 roots with a0 removed, the signed embedding

    u_i=a(i)-a0,  v_j=-(b(j)-a0)

uses units and satisfies u_i+v_j=0 exactly on the cross edges. It does
not specify the same-side pairs. Consequently RRO53's capacity
(p-1)/2 for the complete unit-sum graph cannot be imposed on this
projection. For example, take both sides to list every nonzero residue
once. The cross graph is(p-1)K2 and is actually realized, although its
number of edge components exceeds(p-1)/2.

The shape condition in CR1 can equivalently be enforced by excluding
induced bipartite P4s: three edges of a cross rectangle force its fourth
edge, since three root equalities imply the fourth. Together with CR1's
q-capacity this is an exact feasibility cut for an oracle that relaxes
unknown same-depth root-overlap matrices. Direct enumeration of actual
roots already satisfies these relations.

The edges here record only current-root equality. Old-cofactor
compatibility, activation, same-law mass and AP weights must remain
separate data. Distinct original labels with equal current roots cannot
be merged merely because CR1 puts them in one component. At a larger
fixed depth the same lemma uses its actual effective residue alphabet.
Across different depths, additional residue-prefix compatibility is
required. Refining to a common depth turns a shallower original label
into a union of leaves; selecting one leaf would change the event.

This elementary in-text consequence of residue labeling provides
finite-core feasibility pruning. It supplies no quantitative improvement
of the current same-law square/charge bound by itself and adds no Lean
declaration.

## Exact limit of the joint integer-moment refinement at W=483

For the two fixed schedules selected in SP, the simultaneous mean,
square and H1--H17 observations improve the SH27 cost bounds by exactly

    restart:  600111216928696/4705230572550772875
               =0.00012754129849227924...;
    fourstep: 13638891293834/216227850226171875
               =0.00006307647825924308... .             (JM1)

The resulting W483 defects are respectively
242.74746814910034... and 121.19483996554176..., both positive. Exact
dual majorants and matching abstract load distributions show that no
further tightening of these SH27 costs follows from this particular
set of univariate moment constraints. The separate SH26 physical-square
term is held fixed. This conclusion is specific to two schedules and
does not determine the best schedule among all255 choices.

### Fixed sources, schedules and relaxed moment problem

The restart route uses the actual supported AP(4,6)13 source of SP,
then physical steps17/T6 and19/T8. The fourstep route uses uniform
actual357 survivors, then physical steps11/T4,13/T6,17/T6,19/T8 with
one final conditioning. Source laws, every original labelled test,
residue and missing-class branch remain as in SP. The source bounds
apply at arbitrary finite original prime heights.

For each route write M,G,Hj for its simultaneous source bounds

    E L<=M, E L^2<=G, E(L-j)_+<=Hj, 1<=j<=17,          (JM2)

where L is a complete positive integer-valued labelled load. For the
fourstep source M=3071051/584325 and G=3849/106. For restart,
M=2621130891614589/246025127976511 and
G=6471426752685569/37850019688694. All17 hinge fractions are in the
source-pinned certificate. In particular M is a complete-load mean
bound, not a renamed cylinder-sum bound.

We maximize each SH27 cost over all positive integer distributions
satisfying JM2. Such an abstract distribution need not arise from an
actual congruence family or from the physical construction. This
enlargement gives valid upper bounds for the actual source loads.

Let d=p-1-T, c=(p-1)/d, a=(3p-1)/(p-1)^2 and let f be the product of
the later factors1+ac. For a given earlier auxiliary multiplier n,
the cost as a function of the source load is

    h(p,T,n;x)=483(nx-T)_+/d
       +f*a[(p-1)/(p-1-min(nx,T))-c].                  (JM3)

Different p,n terms may concern different actual complete test
layouts. Each bound is applied separately using JM2; no common
actual layout or common maximizer is assumed.

### Exact dual bounds for the only changed term

Only p=19,T=8,n=1 changes. Its future multiplier is1 and its cost is

    F(x)=483(x-8)_+/10
           +(14/81)[18/(18-min(x,8))-9/5].             (JM4)

Define

    QR(x)=-7/135+(7/270)(x-6)_+
                        +(6517/135)(x-8)_+;
    QF(x)=-14/135+(2/135)(x-3)_++(1/270)(x-4)_+
                     +(1/135)(x-6)_+
                        +(6517/135)(x-8)_+.           (JM5)

Both majorize F for every x>=1. Below the first knot, the constant
equals F at that knot and F is increasing. Between consecutive knots
the majorant is a chord of the convex function F on[1,8]. For QR the
knots are6,8; for QF they are3,4,6,8. At and above8 each majorant is
exactly483(x-8)/10: its value at8 is zero and its slope is483/10.
Thus the entire unbounded load tail is proved by identity. The exact
verifier checks integers1,...,8 and that affine identity, which
suffices for the positive integer moment problem.

All hinge coefficients in JM5 are nonnegative; the mean and square
coefficients are zero. Substituting the respective Hj in JM5 therefore
gives dual upper bounds valid for every distribution in JM2.

The old integer expansion of F has coefficient7/1485 at H7. All
savings come from the valid convexity constraint

    E(L-7)_+ <= [E(L-6)_+ + E(L-8)_+]/2.              (JM6)

Each old bound table has H7>(H6+H8)/2. The improvement of the
unweighted19/T8/N1 term is exactly

    (7/1485)[H7-(H6+H8)/2].                           (JM7)

Multiplying by Pr(N=1), namely77/85 for restart and2156/3315 for
fourstep, gives JM1. Using the mean, square and the other retained
hinges simultaneously yields no additional gain for these costs,
as the feasible equality witnesses below demonstrate.

### Matching abstract distributions

For restart put r=(H6-H8)/2 and use the distribution

    Pr(L=13)=H8-4r,
    Pr(L=12)=r-Pr(L=13),
    Pr(L=6)=1-r.                                      (JM8)

For fourstep put q=H3-H4, v=(H4-H6)/2, r=(H6-H8)/2 and use

    Pr(L=12)=H8-3r,
    Pr(L=11)=r-Pr(L=12),
    Pr(L=6)=v-r,
    Pr(L=4)=q-v,
    Pr(L=3)=1-q.                                      (JM9)

Substitution of the certified rational Hj gives nonnegative masses
summing to1. In each route E L=M, E L^2<=G, and every one of the17
hinge inequalities in JM2 holds. These are exact finite rational
inequalities checked and retained in the certificate. The dual
hinges with positive coefficients attain their upper bounds, and
QR=F or QF=F on the corresponding support, so these laws attain JM5.

For every other retained finite auxiliary multiplier, the old SH27
bound is already attained by the same law of its route. Explicitly,
if vj=h(p,T,n;j) and e=ceil(T/n), then on positive integers

    h(p,T,n;x)=v1+(v2-v1)(x-1)
        +sum_(j=2)^e(v_(j+1)-2vj+v_(j-1))(x-j)_+.    (JM10)

The slope after e is exactly483n/d. The existing helper checks the
finite identity, the final affine slope and nonnegativity of all
moment coefficients. The new verifier substitutes JM8 or JM9 in
every such cost and verifies equality with its retained upper bound.
This establishes the maximum for each term without a numerical LP
oracle or a finite load cutoff.

### Complete auxiliary tails and the precise limitation

For each earlier physical prime q with its cap cq, the comparison
factor Nq has

    Pr(Nq=1)=1-cq/q,
    Pr(Nq=v)=cq(q-1)q^(-v), v>=2,
    E Nq=1+cq/(q-1).

The auxiliary product N uses independent comparison factors; this
does not assert independence of the actual forbidden events. The
probabilities Pr(N=n) for n<T are computed exactly. The full tail
probability and first moment are obtained by subtracting that finite
part from1 and product_q(1+cq/(q-1)). For every n>=T and x>=1, JM3 is
exactly483(nx-T)/d. Thus the complete tail cost is

    (483/d)[M E(N;N>=T)-T Pr(N>=T)].                 (JM11)

JM8 and JM9 have mean exactly M, so they attain JM11 as well. Every
tail probability, full auxiliary mean, tail mean and matching tail
cost is included in the certificate. No auxiliary height or product
distribution is truncated or renormalized.

Consequently the sum of optimized SH27 costs is the exact optimum
of the listed univariate moment relaxation for each fixed schedule.
This remains true if a single abstract law is required for all its
terms, since JM8 or JM9 attains all of them simultaneously. The
statement for actual layouts is only the separate valid upper bounds.

The W483 defect uses

    G*product_p(1+ap*cp)-1-483 + sum(SH27 costs).       (JM12)

The coefficient of G in JM12 is held fixed in this calculation.
Both matching laws have square slack, so they do not certify
attainment of the entire physical-square contribution or of the
full actual defect. They also do not identify an actual covering
layout, exclude further information about joint square/bad-mask
geometry, or settle unrestricted Erdős7. The reusable conclusion
is that improving only these SH27 cost terms through JM2 is exhausted
at the positive defects reported above.

The standard-library verifier pins the SP profile and the generic
`build_step`, `feature_value`, `verify_at` helper by SHA-256. The
helper's PG1 loader is not called and its13/T5-specific improvement
does not occur; an exact check rejects any such foreign-law input.
Default mode recomputes and compares the entire certificate;
`--write` regenerates it. All mathematical checks survive `-I -O`.

The [joint-moment verifier](verify_joint_moment_limits.py) reconstructs
the [primal/dual certificate](joint_moment_limits_certificate.json) using
only exact rational arithmetic and the pinned SP source.

## Direct killed-law comparison and a smaller complete finite core

Use the actual supported AP(4,6)13 law of HC9 and SP4. Extend it through
actual pure-base AP17/T8 and AP19/T8, with normalized physical kernels on
every history and no intermediate conditioning. If Kp denotes a physical
kernel, its killed version Kp^- keeps just the actual mixed-good summand.
The final killed measure is

    eta=nu13 K17^- K19^-,  Q_eta(L)=integral(L^2-484)d eta.  (KC1)

The complete original test L includes its unit label, so L>=1. Strict
Q_eta(L)<0 for every complete test implies eta(1)>0, since the zero
measure would give Q=0. One final normalization then gives every complete
square below484. Final survival is a consequence, not a premise.

The following bounds concern Q, not APC's physical-square-plus-assigned-
charge functional. They approximate the same underlying AP construction.
At the previous box20/current-depth8 cutoffs, the complete Q error is
less than0.000667. There is also a complete unequal box with4,889,808 test
labels and error less than0.263. Neither statement evaluates the finite
core inequality or completes the continuation beyond19.

### Independent mass and square errors for each omitted mask

Let B=(b_q) be the vector of old original-cofactor cutoffs. The current
pure and mixed cutoff k need not equal any b_q. For i=0,2 put

    z0(p)=1, u0(p)=p/(p-1), t0(p,k)=1/[(p-1)p^k],
    z2(p)=Phi_p(0), u2(p)=Sigma_p,
    t2(p,k)=sum_(a>k)p^-a Phi_p(a),

where Phi and Sigma are the complete two-test/one-query factors in APC2.
Define

    U_i(B)=product_q u_i(q),
    V_i(B)=product_q[u_i(q)-t_i(q,b_q)],
    Z_i(B)=product_q z_i(q), R_i(B)=U_i(B)-V_i(B).

The queried-label tail R_i includes every label with any old exponent
outside B. In its weighted version the two test axes remain complete.
The complement of an unequal box can equivalently be partitioned by
its first coordinate exceeding its cutoff; the product difference is
exact and contains no finite-height restriction.

For threshold T at p set

    s_*=(p-2)/(p-1), delta=(T-1)/(p-2),
    C=1/(1-delta), ell=max(C^2,C/delta), c=C/s_*.

If the source probability has Haar density at most D_* and complete
square at most J_*, use J_0=1 and J_2=J_*. The direct physical or killed
kernel error is bounded by

    epsilon_p,i = D_* R_i(B)
       [c(u_i(p)-z_i(p))+(ell/s_*^2)z_i(p)/(p-1)]
      +D_*[V_i(B)-Z_i(B)]
       [c t_i(p,k)+(ell/s_*^2)z_i(p)t0(p,k)]
      +J_i[c t_i(p,k)+((ell+C)/s_*^2)z_i(p)t0(p,k)].   (KC2)

This is APC3 with separate old cutoffs and current cutoff. Its three
terms cover old-cofactor tails at every positive current depth, retained
nonunit cofactors at omitted current depths, and pure-current tails.
For i=0 the weight is1: old and current query masses are D_*/d and
p^-a. For i=2 the original complete test-pair weights give Phi. The
pure-base coefficient ell+C still pays both the changed region and the
common-region density change. Thus epsilon_0 is an L1 error in its own
right; it is not inferred by paying the much larger square-weighted
error as mass.

At17 use (D_*,J_*)=(D,G), where

    D=1039695426000000/18925009844347,
    G=6471426752685569/37850019688694.

At19 use (2D,(89/64)G), valid for the unconditioned physical17 measure.
The killed17 input is dominated by this physical measure, so it has the
same direct error bounds. For box20/current8, exact evaluation gives

|error|upper bound, decimal display|
|---|---:|
|epsilon17,2|0.0001293444399147029...|
|epsilon19,2|0.0002832646182242736...|
|epsilon17,0|0.000000010898327478914162...|
|epsilon19,0|0.000000014506721280970769...|

All four values use the same actual HC13 source bounds.

### Comparing the two killed steps

First change only the17/19 forbidden masks, retaining the full incoming
nu13. Write eta_mask for the resulting killed reference measure.
Triangle comparison and the common-kernel bounds in WT5/APC4 give

    Delta2(eta,eta_mask)<=(59/45)epsilon17,2+epsilon19,2,
    Delta0(eta,eta_mask)<=epsilon17,0+epsilon19,0.       (KC3)

For the first inequality, the17 difference is propagated through the
common reference19 kernel, whose weighted factor is59/45. For the
second, every killed kernel is a positive subprobability kernel and
contracts L1. The19 direct error may be integrated under the full
killed17 input, dominated by the physical source used in KC2. There is
one propagated17 mass error, not the two appearances arising when
separate physical-prefix assigned charges are compared.

For positive measures sigma,tau and any L>=1,

    |Q_sigma(L)-Q_tau(L)|
       <=integral(L^2-1)d|sigma-tau|
                           +483|sigma(1)-tau(1)|
       <=Delta2(sigma,tau)+483 Delta0(sigma,tau).       (KC4)

Consequently the mask part of the Q error is

    e_mask=(59/45)epsilon17,2+epsilon19,2
                          +483(epsilon17,0+epsilon19,0).

At box20/current8 it is0.0004651201891079085..., with only
0.000012270638551024422... from the mass term. This comparison neither
changes nor contradicts the earlier APC error for its different
physical/assigned-charge functional.

### Replacing the incoming law and retaining the complete test box

Now replace the incoming probability by the actual AP13 law nu_B of
its retained original five-prime family. Construct it by precisely the
same uniform357, AP11/T4, AP13/T6 and one-conditioning rule. Keep the
reference17/19 kernels fixed. APC2--APC5 give

    Delta2(nu13,nu_B)<=eNw,
    Delta0(nu13,nu_B)<=eNm,                           (KC5)

also for unequal B, replacing each product cutoff by b_q and using
b11,b13 as the respective current cutoffs. Both full and core laws
have the same HC lower normalizer and upper square bound. Uniform
padding to a common physical period preserves the construction.

For a fixed common killed continuation, the weighted difference in
final square integrals is at most

    (89/64)(59/45)eNw=(5251/2880)eNw.

Its final survival probability, as a function of the incoming point,
is a fixed h with0<=h<=1. The two incoming measures are probabilities,
so their difference has total mass zero. Therefore

    |eta_mask(1)-eta_core(1)|<=eNm/2.

Using the raw form Q=integral L^2-484 mass gives the sufficient incoming
error

    e_incoming=(5251/2880)eNw+242eNm.                 (KC6)

There is no assumption that either final killed mass is positive. In
particular nu_B need not avoid omitted full-family constraints; their
effect is already included in KC2 and KC5.

Finally keep every original test label in the chosen seven-prime box H.
The final reference killed law is bounded by its physical law of Haar
density at most(18/5)D. The complete two-test tail gives

    e_test=(18/5)D {product_p p(p+1)/(p-1)^2
               -product_p[1+sum_(a=1..h_p)(2a+1)p^-a]}. (KC7)

Every omitted ordered test pair is included. For one original complete
layout, restrict its labels to the box, without altering any retained
residue. Then

    Q_actual(L)<=Q_core(L_box)+e_mask+e_incoming+e_test. (KC8)

If an actual exponent is smaller than a listed cutoff, use the
intersection with its inventory and uniform padding. Larger finite
exponents are paid by the full tails. Original forbidden and test
labels remain distinct throughout the comparison.

### Two fully specified finite cores

In the following table the five-prime incoming core and each old-
cofactor box use the corresponding entries of H. Pure and mixed current
cutoffs are listed separately. The full finite reference is the actual
AP construction for those retained original residues, followed by the
two specified reference kernels, and the complete test box H.

|H, ordered by3,5,7,11,13,17,19|current17/19|complete test labels|total Q error|safe allowance|
|---|---|---:|---:|---:|
|`(20,20,20,20,20,20,20)`|`(8,8)`|1801088541|0.0006664579809979847...|0.000667|
|`(17,10,8,7,6,6,6)`|`(6,6)`|4889808|0.2563651750935413...|0.263|

Thus the finite sufficient condition is

    Q_core(L_box)<=-safe_allowance                  (KC9)

for every retained original family pattern and every complete box test.
The error is strictly below its safe allowance, so KC8 then makes every
full Q strictly negative and KC1 gives positive survival and square<484.
KC9 itself has not been proved or evaluated uniformly.

The second core has at most99791 old five-prime forbidden labels,
598752 labels whose largest prime is17, and4191264 whose largest prime
is19:4889807 in total. Adding the test unit gives4889808. Its common
period may be taken as

    3^17*5^10*7^8*11^7*13^6*17^6*19^6
     =776550560750774609700229544439786533325582744140625.

This remains a51-digit period, and the number of residue assignments is
not asserted small. The core is a feasible cutoff choice, not a proof
of optimal cutoffs or feasible exhaustive enumeration.

### A source square-hinge observation with full comparison tails

For the same actual supported13 law define

    T13(tau)=sup_A E_nu13(A^2-tau)_+.

For each of the twelve PR original-root branches, let u3,u5,u7 and
D_branch be its certified reference pure masses and actual uniform357
Haar-density bound. Use independent comparison counts with caps

    (c3,c5,c7,c11,c13)=(1/u3,1/u5,1/u7,5/3,2),
    Pr(Xp=1)=1-cp/p,
    Pr(Xp=n)=cp(p-1)p^-n, n>=2.

Let M be their product. The nonnegative increasing convex function
(z^2-tau)_+ permits the PR restriction to the actual pure reference,
the complete labelled AP11/13 comparison, and finally division by the
same HC retained mass r. Hence

    T13(tau)<=max_branch (D_branch*u3*u5*u7/r)
                                      E(M^2-tau)_+.  (KC10)

The old uniform law is never replaced by a different supported law.
The comparison variables are independent; the actual forbidden events
need not be. For integer tau>=1, the entire product tail is evaluated
by the exact identity

    E(M^2-tau)_+=E M^2-tau
                    +sum_(n^2<tau)(tau-n^2)Pr(M=n),
    E M^2=product_p[1+cp(3p-1)/(p-1)^2].

All omitted product probabilities are accounted for by the full second
moment. Checking all twelve branches gives

    T13(81)<=27462732511027063792077002926276002
                    /234516374824438312292389830652525
             =117.10368852318302...,
    T13(1024)<=29.592792472449865... .                (KC11)

The largest value in each is the effective9 branch with5 and7 present.
Appending a complete cap2 comparison factor X17 gives, for the
unconditioned physical mu17=nu13 K17,

    sup_A E_mu17(A^2-1024)_+<=64.10180348992289... .

The bounds also apply to the core's actual AP13 source and its
normalized reference17 continuation: these are members of the same
arbitrary-family and cap-bounded construction. No conditioned single17
law is inserted.

### A killed pair frontier that retains actual test/mask overlap

For one globally fixed complete current test, index its original labels
by ell,k. Let C_ell,C_k be their old test cylinders and I_ell,k their
current-prefix intersection. Let m_x be the actual pure base, B_x the
actual mixed forbidden union, alpha_x=m_x(B_x), and

    a_x=1/(1-min(alpha_x,delta)).

The exact killed pair entry under old input sigma is

    P^-_(ell,k)=E_sigma[1_(C_ell intersect C_k)(x)
                         a_x m_x(I_ell,k outside B_x)]. (KC12)

Summing every ordered pair gives the killed square of that fixed test.
If b_x is the physical bad-side density, the physical entry exceeds
KC12 by exactly

    E_sigma[1_(C_ell intersect C_k) b_x m_x(I_ell,k intersect B_x)].

In PO notation b_x=g_x-h_x; here b means the bad-side density itself.
This avoids identifying two different coefficient conventions. The
actual overlap can vanish; no uniformly increased killed floor is used.

Let Xi_p^-(sigma) be the supremum of the sum of KC12 over pairs with
at least one positive current exponent, over globally legal complete
tests. Each original old block and current residue remains independent
of the forbidden layout. Set F_p^-(W;sigma)=W b_p+Xi_p^-(sigma), where
b_p is the assigned bad mass under the normalized physical input.
For0<=tau<=484 and W=484-tau,

    Q_eta(L)<=T13(tau)-W
                   +F17^-(W;nu13)+F19^-(W;mu17).      (KC13)

To prove this, expand L^2=A13^2+R17+R19, where R17 contains the ordered
pairs in the19-zero block with a positive17 exponent and R19 contains
pairs with a positive19 exponent. Both R terms are nonnegative. Since
eta17<=mu17 and every killed kernel has mass at most1, their integrals
are bounded by the respective Xi17^- and Xi19^-. The marginal of eta
through13 is dominated by nu13. Thus integral(A13^2-tau)d eta<=T13(tau).
Finally eta(1)>=1-b17-b19, and W>=0. These give KC13. Its two independent
suprema need not be attained by one common test; they are upper bounds
for the one test used in the expansion.

For each finite core, F17 here uses nu_B and its reference K17; F19
uses the normalized physical input mu17,B=nu_B K17, not killed or
conditioned17. Both Xi suprema use every complete test label in that
row's box H. In particular the uniform row retains test depths20 even
though the two current forbidden-mask cutoffs are8.

Taking tau=81,W=403, KC11 and the two safe allowances give sufficient
finite reference bounds, respectively,

    F17^-(403)+F19^-(403)<=285.895  [box20/current8],
    F17^-(403)+F19^-(403)<=285.633  [the unequal box].   (KC14)

For each row these constants are strictly smaller than403-T13(81)
minus its safe allowance. Therefore KC13 implies KC9. Neither frontier
bound is supplied by the tail computation.

### Pointwise clipped covariance and its exact scope

A relaxation of Xi^- keeps

    J_p(sigma)=sup_A E_sigma[kappa_p(alpha) A^2],
    kappa_p(alpha)=((p-1)/(p-2))/(1-min(alpha,delta)).

The killed current-prefix mass is bounded by the same physical cap.
Weighted Cauchy--Schwarz for every pair of independent old blocks then
gives Xi_p^-(sigma)<=a_p J_p(sigma), with

    a17=25/128, a19=14/81.

Keeping J_p retains the cap covariance discarded in SH26. If this is
further bounded with the existing common-vector clipped cost H_K,
K=1024 is admissible at W403: its required thresholds a_p K c_p are
400 and14336/45, both below403. This is a pointwise stronger majorant
than SH27's unit-floor cap replacement; no universal strict numerical
improvement of the subsequent auxiliary comparison is asserted.

For the original row variables, the loss from clipping y^2 at1024 is

    a_p(c_p-kappa_p(alpha))(y^2-1024)_+.

Since kappa_p>=(p-1)/(p-2), its expectations under nu13 at17 and mu17
at19 sum to at most

    (35/192)T13(1024)
       +(98/765)sup_A E_mu17(A^2-1024)_+
          =13.606253764407912... <13.607.              (KC15)

This controls the pointwise original-row clip loss only. It does not
bound the additional errors of comonotone comparison, Jensen,
independently maximizing layouts, or every relaxation of KC14. The
actual joint frontier still requires its own upper bound.

The proof reuses PR, HC, APC, WT, PO and the existing H_K comparison;
it adds no Lean wrapper or formalization claim. Its exact verifier
checks the complete geometric tails, twelve root branches, both finite
reference specifications and all rational budget comparisons. Ordinary
proofs and certificates do not settle the unrestricted problem.

The [killed-core verifier](verify_killed_core_continuity.py) reconstructs
the [full-tail certificate](killed_core_continuity_certificate.json). It
pins the existing HC, PR and APC sources. Default mode compares every
field; `--write` regenerates. Numeric, duplicate-key and source-hash
changes are rejected under `python3 -I -O`.

## Shared actual-cell square hinges improve the same AP13 law

For the same actual supported AP(4,6)13 probability used in HC9, SP4 and KC, every complete original test obeys

    E L^2 <= 148878188597300778613/914721425816667898
          =162.75795493079391...,
    E(L^2-81)_+
       <=7950179084001887172777104410541784715667
          /76933096761156988347518483945560826250
        =103.33886738868257... .                         (SQ1)

The previous observations were170.9755187952681... and117.10368852318302..., respectively. The probability itself is unchanged: start with uniform actual357 survivors, apply the original pure-survivor AP11/T4 and AP13/T6 kernels, and condition once on all actual survivors. Its same HC lower normalizer is

    r=18925009844347/38266567762500.

All residues, missing classes, complete original labels and arbitrary finite heights remain in the domain. These are ordinary full-tail and continuous-parameter bounds, not exact maxima over actual families or Lean declarations.

### Reuse of the actual five cells

In the effective3/9 case use HC's five cells, roots r(l)=(0,0,1,1,1), and exactly its parameter domain

    w_l=1-D_l, D>=0, sum D<=1/2;
    alpha>=0, sum alpha<=1/4;
    beta>=0, sum beta<=1/4;
    t>=0, sum t<=1/72; 3/4<=z<=1.

Set d_l=z-alpha_r(l)-beta_l, n_l=w_l d_l/9-t_l, s=sum n_l and x=sum w_l/9. The raw complete35 cell masses are n_l; a depth-a ternary query in cell l has raw mass at most d_l 3^-a. The actual pure3 measure has masses w_l/9 and depth caps3^-a. Reuse the same-family mixed7 bound T from HC7, so its retained denominator is s-T/5>0.

For a fixed original root/cell choice c=(r,j), write b_l=1+1_(r(l)=r)+1_(l=j). For any nondecreasing cost g define exactly HC's monotone bound

    Delta_a(g,b)=max_(0<=i<=a-3)[g(b+i+1)-g(b+i)],
    P_g(c;m,v)=sum_l m_l g(b_l)
                +sum_(a>=3)3^-a max_l[v_l Delta_a(g,b_l)].

It follows by adding the original depth-a indicator: on its cylinder the previous deep count lies between0 and a-3. This requires neither convexity nor coherent nesting of the original ternary prefixes. Let P^A_g use masses n and caps d, and P^eta_g use masses w/9 and caps1. Constants integrate exactly. Inactive root/cell test choices are completed to active ones, increasing the load; no forbidden residue is changed.

### Square-cost positive5 increment and its complete tail

Let f_tau(v)=(v^2-tau)_+ for tau>=0. It is nonnegative, increasing and convex for v>=1. HC1's actual-zero-block decomposition remains valid for this cost. For a positive5 multiplier n>=2, Jensen gives

    f_tau(A0+...+A_(n-1))-f_tau(A0)
      <=g_n(A0)+(1/n)sum_(e=1)^(n-1)f_tau(n A_e),
    g_n(v)=f_tau(nv)/n-f_tau(v).                       (SQ2)

The cost g_n is nonnegative and nondecreasing. Below sqrt(tau)/n it is0, between sqrt(tau)/n and sqrt(tau) it is n v^2-tau/n, and above sqrt(tau) it is (n-1)v^2+tau(1-1/n). Its derivative is nonnegative on each interval, and it is continuous at both endpoints. It need not be convex, so its finite-n terms use the monotone P_g formula, not a convex specialization.

The complete raw35 upper bound is therefore

    F_tau=max_c {P^A_f_tau(c)
       +sum_(n>=2)4/5^n [P^eta_g_n(c)
            +(n-1)/n max_d P^eta_(f_tau(n .))(d)]}.     (SQ3)

The same original zero5 choice c stays outside the whole sum. Positive blocks may be maximized independently only as an upper bound. The raw probabilities4/5^n arise from the actual pure5 prefix comparison, with its pure mass canceling exactly as in HC2-HC3.

Put Q_c=P^eta_(v^2)(c), Qmax=max_c Q_c, E_c=P^eta_f_tau(c), and

    N=max(2,ceil(sqrt(tau))+1).

For every integer n>=N and integer v>=1, f_tau(nv)=n^2 v^2-tau. Also g_n has nondecreasing integer increments: every second integer difference of f_tau is at most max(2,2ceil(sqrt(tau))+1), whereas that of n v^2 is2n. Thus the running maximum in Delta_a occurs at its last increment. Since all eta depth caps equal1, the largest b_l maximizes the increments of g_n, f_tau and v^2 simultaneously. Consequently

    P^eta_g_n(c)=n Q_c-E_c-(tau/n)x,
    max_d P^eta_(f_tau(n .))(d)=n^2 Qmax-tau x.

The complete n>=N portion inside SQ3 is exactly

    5^(1-N)[(N+1/4)Q_c
       +(N^2-N/2+1/8)Qmax-E_c-tau x].                (SQ4)

It uses the full geometric mass, first moment and second moment. Taking only n>=ceil(sqrt(tau)) would not justify the discrete-convex specialization at the boundary; the finite preceding terms are retained in SQ3.

### Every original ternary height is paid

For f_tau, Delta_a is its last increment because the cost is convex. Once b+a-3>=ceil(sqrt(tau)), that increment is2a+2b-5. At a fixed parameter vertex the tail integrand is therefore the maximum of five affine functions d_l(2a+2b_l-5). Choose its eventual line by largest slope and then largest intercept, and start the tail only after it dominates every other line. This finite crossing calculation proves the entire subsequent envelope, not merely a sampled range.

For a finite g_n term, once the queried integer is above sqrt(tau), its increment equals(n-1)(2a+2b-5). The verifier extends its finite prefix until this current increment dominates every preceding increment for every present b. The later increments strictly increase, so that condition remains true forever. Equal eta caps then select the largest b.

In both cases the remaining exact affine tail uses

    sum_(a>=A)3^-a = 3^(1-A)/2,
    sum_(a>=A)a 3^-a = (2A+1)/(4*3^(A-1)).

Thus no original height is hard-truncated. The finite checks establish entrance into a proved affine tail; they do not replace an infinite probability law by a normalized finite sample.

### The complete7 comparison and actual conditioning

Use HC6's full pure7 comparator, with probability29/35 at1 and36/(5*7^n) at n>=2. Since f_tau(nv)=n^2 f_(tau/n^2)(v), put M=max(2,ceil(sqrt(tau))). The raw cost before actual mixed7 deletion is bounded by

    B_tau=(29/35)F_tau
       +sum_(2<=n<M)36 n^2/(5*7^n) F_(tau/n^2)
       +(36/5)[F_0 sum_(n>=M)n^2 7^-n
                       -tau s sum_(n>=M)7^-n].       (SQ5)

For the last term tau/n^2<=1 and v>=1, so F_(tau/n^2)=F_0-(tau/n^2)s exactly. This equality follows from SQ3's exact treatment of constants; the positive5 increment of a shifted square is unchanged.

All added costs are nonnegative before expansion. Discarding the mixed7 union therefore gives the valid uniform357 bound B_tau/(s-T/5). This uses the original actual deletion union and the same denominator; it does not replace the conditioned marginal by a product law.

For any proposed constant C, the target margin C(s-T/5)-B_tau is separately concave in D,alpha,beta,t,z. Each branch of P^A is affine separately in those groups. All maxima have nonnegative coefficients. The negative tail term involving E_c in SQ4 is affine in w for its fixed zero5 choice, while the negative multiples of s in SQ5 are separately affine. Repeated vertex interpolation therefore reduces the whole continuous parameter domain to exactly6*3*6*6*2=1296 product vertices.

For each needed tau, the verifier evaluates the infinite-tail expressions at every vertex and takes the largest ratio. These shared-cell bounds cover all four effective9 missing5/7 branches. For each of the other eight branches it uses PR's actual pure-reference product comparator. In every branch that fallback for the square hinge is evaluated from its full second moment plus the finite correction at integer products m with m^2<tau. The resulting twelve upper bounds are all included. Finally the pointwise unit-floor inequality

    (L^2-tau)_+ <= L^2-min(tau,1), L>=1

permits taking the minimum with G-min(tau,1), where G=3849/106 is the established same-law uniform357 square bound. Denote the resulting simultaneous source observation by H357^(2)(tau).

### The same physical AP11/13 chain and one final normalization

Let N=N11*N13 use the unchanged complete comparison factors with caps5/3 at11 and2 at13. They are auxiliary counts, not independent actual forbidden events. For tau=h^2,

    U2(tau)=sum_(n<h)Pr(N=n)n^2 H357^(2)(tau/n^2)
                  +G E[N^2;N>=h]-tau Pr(N>=h)         (SQ6)

bounds every physical13 square hinge. The high-n formula is exact for its bounding costs because tau/n^2<=1. Both tails are obtained by subtracting finite parts from the full probability1 and

    E N^2=(23/15)(55/36)=253/108.

The same original labelled AP comparison proves SQ6 before the sole conditioning. Nonnegativity then gives T13(tau)<=U2(tau)/r. The pointwise inequality L^2<=tau+(L^2-tau)_+ gives the further same-law observation

    Gamma13 <= tau+U2(tau)/r.                         (SQ7)

At tau16 the exact physical bound is2899096118869109/39943338435000, and SQ7 yields the first result in SQ1. At tau81 the exact physical bound is7950179084001887172777104410541784715667/155559525971351670013360122780046875000, yielding the second result in SQ1. No global optimization over all real shifts is claimed; tau16 is a sufficient witness. The stronger square observation changes neither the underlying kernels nor the HC charge and Haar-density observations.

The adjacent verifier checks both1296-vertex targets, all12 missing-class branches, the complete geometric and AP tails, and exact rational comparisons with the prior constants. It pins the existing pure-root and shared-cell-hinge certificates by SHA-256 and compares its complete output certificate. Run it with `python3 -I -O`, supplying `--source-directory` if its pinned inputs are elsewhere. This result does not prove the finite17/19 joint frontier or the unrestricted covering statement.

### Complete continuations and the larger killed-frontier allowance

The new square observation and the earlier SP profile hold on the same
actual AP13 probability. For every positive integer h retain

    H13(h)<=min(SP_H13(h),(Gamma13-1)h/(4h^2-1)).

Reuse SP's complete auxiliary first-moment tails and fixed scalar-cost
formula with this stronger square input. Exact rational evaluation gives

    Gamma17<=9720067404606638015016317/25298087377147529307792
             =384.22143380637726...,
    Gamma19<=1947596368885525589065961707/873442090069958182244328
             =2229.7945004339476... .                 (SQ8)

The first bound uses a single AP17/T8 step. The second starts again from
supported13, applies normalized physical AP17/T8 and AP19/T8 kernels,
and conditions only after19. Both give positive survival by the SP
sufficient criterion. The single17 conditioned output is not inserted
in the two-step chain. Every original residue and finite height remains
allowed on the stated prime support.

The255 integer restart schedules1<=T17<=15,1<=T19<=17 still all have a
positive W483 defect for this upper functional. Its least value is
228.60653787361616... at T17=6,T19=8. This is a limitation of that
functional, not a lower bound on actual test moments. No different-law
PG1 observation is used by the reused generic helper.

The actual AP probability and KC reference constructions are unchanged,
so the earlier KC safe error allowances remain valid. Substituting the
stronger T13(81) into KC13 yields these sufficient finite bounds:

    F17^-(403)+F19^-(403)<=299.660  [box20/current8],
    F17^-(403)+F19^-(403)<=299.398  [the unequal box].   (SQ9)

They are strictly below403-T13(81) minus the respective KC safe allowance.
The available exact budgets are299.6604656113174... and
299.3981326113174... . The two finite frontier inequalities themselves
remain unproved; the extra allowance is not a computed saving in F.

The [shared-cell square verifier](verify_shared_cell_square.py) checks
the [SQ certificate](shared_cell_square_certificate.json), and the
[continuation verifier](verify_shared_square_continuation.py) checks
its [same-law consumers](shared_square_continuation_certificate.json).
They retain complete tails and pinned source identities. No Lean
formalization, actual-family sharpness or unrestricted resolution follows
from these ordinary proofs and exact arithmetic checks.

## Common original prefixes across depths from RRO55

The ordinary cross-difference construction in RRO55.2--55.5 supplies
an exact extension of CR1 for fully specified finite prefix observations.
It is reused here for the original-label interface, without a new Lean
wrapper. The finite criterion excludes joint patterns that independent
per-depth checks admit; it does not evaluate the killed objective.

### Finite prefix criterion

Fix a prime p and two sets of distinct original labels L,R. First suppose
all labels are read to a common finite height H. Let

    E_t(i,j)=1 iff a_i=b_j mod p^t, 0<=t<=H.

These bits concern the same a_i,b_j at every depth. E0 is complete and
E_(t+1)<=E_t. At each t, every component with an edge in the bipartite
graph E_t must be complete bipartite. For each such component C, let
c be the number of edge-containing components of E_(t+1) restricted to C,
and let iL,iR indicate isolated vertices on its two sides. Then

    c+iL+iR<=p.                                       (CR2)

All vertices in C share one p^t-prefix, which has only p next digits.
Different mixed child components need different digits. Left-only and
right-only isolated groups, if present, require separate digits outside
the mixed groups. This proves necessity. Conversely, assign different
digits to these groups and recurse inside mixed groups. Same-side
isolated vertices can share all remaining digits because no cross
condition connects them at greater depth. After H steps this constructs
one simultaneous mod p^H witness for the complete prefix data. Equality
at H means only congruence modulo p^H; no infinity label is asserted.

This is the finite-prefix specialization of
[RRO55.2--55.5](https://github.com/the-omega-institute/trureturing/blob/ba8142cf990037c2af6a709ac82d6769cd0381e2/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L23169).
Its exactness concerns this free cross-prefix realization problem.
Pinned residues, activation constraints, old-cofactor compatibility and
source-law conditions are additional constraints and remain attached.

At depth1 the effective alphabet is p-1 when a pure root is removed,
and p when it is absent, as in CR1. Inside a specified retained root,
the generic next-digit bound is p. Further pure restrictions may reduce
the available set; one cannot automatically use p-1 at every depth.

### Strict separation from independent-depth CR1

Take p=3, six labels L0,L1,L2,R0,R1,R2, each of height2. Require all
nine cross pairs equal modulo3. At modulo9 require just L0=R0 and
L1=R1, and require the other seven cross pairs unequal:

    E1 = [1 1 1]       E2 = [1 0 0]
         [1 1 1]            [0 1 0]
         [1 1 1]            [0 0 0].                  (CR3)

E1 independently uses one root. E2 independently uses four roots: two
matched pairs plus one left isolate and one right isolate. Even after
removing root0, the depth2 alphabet has6 residues, so both independent
CR1 tests pass. Explicit independent witnesses are all roots1 for E1,
and L=(1,2,4), R=(1,2,5) modulo9 for E2; all six are nonzero modulo3.

Together E1 forces all vertices into one mod3 root. Inside it E2 needs
four distinct children although only three exist. Thus CR2 rejects the
array. In valuation language its diagonal observations are **at least2**
and all other entries are **exactly1**. It neither requires nor assumes
an exact valuation2 on the two diagonal pairs.

The [prefix verifier](verify_prefix_obstruction.py) independently enumerates all729 choices
of the six next digits under the common root1, finding no witness.
Every one-label deletion has a genuine modulo9 witness, retained in the [prefix certificate](prefix_obstruction_certificate.json).
The ordinary pigeonhole proof above is independent of that finite check.

For arbitrary p, the analogous obstruction has p labels on each side:
one common parent, p-1 matched diagonal child pairs, and all remaining
cross child pairs unequal. It requires p+1 children. This is F_(p,t)
from RRO55.5; it uses2p labels regardless of the depth t.

For an integer-programming relaxation, write z_ij=E_(t+1)(i,j) and
x_ij=E_t(i,j). On the selected p-by-p submatrix one valid linear cut is

    sum_(i=1..p-1) z_ii + sum_(other pairs)(1-z_ij)
       <=p^2-1 + sum_(all pairs)(1-x_ij),             (CR4)

where the first sum contains exactly p-1 diagonal entries. If all parent
bits are1, the forbidden child pattern cannot have score p^2. If any
parent bit is0, the right side is at least p^2 and the inequality is
trivial. All variables refer to the same original labels across depths.

### Unequal original heights and shared contexts

An original label of height h carries a residue only modulo p^h. Two
labels of heights h,k have actual cylinder overlap according to equality
modulo p^min(h,k). Prefix observations exist only to this minimum height.
An observed first split below that height fixes a finite valuation; a
match at the minimum height gives a lower bound, not equality to infinity
and not a chosen finite valuation.

For unequal heights the exact feasibility question is therefore an
**interval/partial-prefix completion** problem. Unobserved deeper entries
remain unknown. CR2 or CR4 may reject a candidate only when the required
parent equalities and child equalities/inequalities are actually forced.
Alternatively, one can seek a full nested prefix completion respecting
all observed intervals and then apply the constructive finite criterion.

An auxiliary extension of a shallow residue used in such a feasibility
argument must not replace its cylinder by a single high-level leaf in
the killed calculation. The original cylinder is the union of all its
extensions and retains its original mass and AP weight. Distinct
original moduli stay distinct even when their prefixes coincide.

The2p induced-obstruction bound is for a **complete specified** cross
array. It is not an automatic bound for arbitrary partial input. For
example, a long even cycle with equality constraints on all but its
closing edge and an inequality on that edge is inconsistent, while
every proper induced restriction of those partial constraints is
consistent. Missing chords must not be interpreted as nonedges.

For the killed frontier, use one master prefix variable for each
original label and prime, reused across source cells, masks and test
blocks. A label may be active in several cells, but its original residue
cannot be reselected separately in each. The local graph cuts are
necessary restrictions on that common assignment. They do not by
themselves compute the same-law killed expectation, preserve all
test-test/source interactions, or prove the required484 barrier.

The source is RRO55 at devba8142cf990037c2af6a709ac82d6769cd0381e2.
The compared dev increment adds no D5 declaration for this criterion.
Dovgoshey--Petrov, [Subdominant pseudoultrametric on graphs,
Lemma2.1 and Theorem3.3](https://arxiv.org/html/1110.6802v1), supplies
the repeated cycle extremum condition for pseudoultrametric extension;
it does not impose the p-child capacity. Bradley,
[From image processing to topological modelling with p-adic numbers,
Section2](https://www2.ipf.kit.edu/Personen/bradley/CV/hier2vis.pdf),
describes the p residue children of a p-adic disk. Neither reference
supplies a weighted covering-system positivity bound.

### Translated observations and shared inputs from RRO56 and RRO57

The relevant new interface is a joint observation of the same actual
point. [RRO57.10--57.14](https://github.com/the-omega-institute/trureturing/blob/902112b9c6e74cf8232c2f30962db749ac6ac573/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L24478)
distinguishes exact translated observations, shared representatives and
independent resampling. It supplies an observation design for KC; it
does not supply its missing numerical inequality.

For a fixed original congruence label i with modulus
m_i=product_p p^e(i,p) and fixed residue a_i, its indicator is exactly

    I_i(x)=product_(p dividing m_i)
                1_{v_p(x_p-a_i)>=e(i,p)}.             (TC1)

Only the truncated valuation min(v_p(x_p-a_i),e(i,p)) is needed. The
representative a_i is a fixed constant, and each occurrence reads the
same x. To use RRO57.11's nonnegative queries, choose0<=n_i<m_i with
n_i=-a_i modulo m_i; x+n_i has the same required truncated valuations.
This identity is independent of the probability assigned to x.
For finite periods it is simply the CRT membership test, including all
extensions of each original cylinder. RRO57.11 also shows how a finite
set of translated valuation queries recovers the full residue modulo
any specified finite period. That is a sufficient representation, not
a compression theorem or a uniform finite state for every period.

In particular the killed entries

    P_ij=integral I_i I_j d eta                        (TC2)

must use the one fixed actual killed measure eta. Before integration,
the test indicators, original forbidden indicators, actual union mask
and pure-prefix normalization all share their actual coordinates and
context. Retaining their separate distributions, or even a chosen
collection of pair distributions, does not authorize replacing their
joint law by a product. A repeated original label is one input reused,
not an additional sample. Its literal residue cannot be reselected in
different old rows, test pairs or auxiliary branches.

This requirement is substantive for the row factor
g_x=1/(1-min(alpha_x,delta)): alpha_x is the actual union mass in that
same old row. Thus evaluating g_x, the surviving test intersection and
the row weight requires their common context. The already retained
KC pair formula provides this exact evaluation. TC1 identifies finite
queries from which the underlying membership data can be obtained;
it does not replace the union by a sum or remove the incoming AP law.

[RRO56.6--56.7](https://github.com/the-omega-institute/trureturing/blob/902112b9c6e74cf8232c2f30962db749ac6ac573/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#L23844)
allows resampling an intermediate orbit in an independent expression
tree under its stated invariant-law hypotheses, but gives a strict
failure for reused inputs: three pairwise independent outputs can
assign zero mass to an event to which the product of their marginals
assigns1/8. RRO57.14 further distinguishes a complete joint law of
valuation labels from the coupling of representatives within those
labels. Neither result establishes Haar invariance of the present
AP13 law or conditional independence of its source, masks and tests.
The Haar orbit convolution is therefore a separate construction and
is not substituted for nu13 or normalized physical mu17.

The finite core can consequently use TC1 jointly with CR2--CR4 and
actual row weights. Full translated observations would recover the
entire finite problem. Selecting a smaller collection that proves the
KC bound remains open. In particular these representation results
alone neither exclude every abstract scalar load law nor establish
the sufficient299.398 frontier. The source increment at dev902112b9c6
adds theory and digestion atoms, with no D5, Blueprint or frozen-state
changes relative to devba8142cf99. This application is an ordinary
mathematical explanation, not a new Lean result.

### Actual maximizing tests constrain the killed pair matrix

Fix one finite actual family, its normalized physical incoming law
sigma and its actual killed kernel K_p^-. Set eta=sigma K_p^- and
z=eta(1). The finite complete original test-label set J includes the
unit label. Partition it into J0 and J+ according to whether the
current exponent is zero or positive. For one globally legal test put

    A=sum_(i in J0) I_i, C=sum_(i in J+) I_i,
    L=A+C, P_ij=integral I_i I_j d eta,
    X(P)=integral(2AC+C^2)d eta
        =sum_(i or j in J+)P_ij.                     (KB1)

The sum in KB1 is over ordered pairs in J times J.
The finite residue choices give an actual maximizing test for X(P).
Assigned bad mass b is fixed while its test residues vary, so this
also maximizes F_p^-(W)=Wb+X(P). The measure eta, forbidden union and
physical normalization do not change when one test residue changes.
All statements below hold at arbitrary finite original heights.

For ell in J+, replacing I_ell by any other legal residue indicator J
changes X(P) by exactly

    integral (J-I_ell)(2(L-I_ell)+1)d eta.            (KB2)

At a maximum the chosen score is at least each replacement score.
Average over all m_ell classes of this original modulus, whose
indicators sum to1. This yields

    m_ell[2 sum_(j!=ell)P_(ell,j)+P_(ell,ell)]
        >=2 sum_(j!=ell)P_(j,j)+z.                   (KB3)

For a positive current height e, retain that label's old residue and
its literal current parent prefix of depth e-1, with indicator V.
Its p next-digit siblings partition V. Averaging the same replacement
scores over those p alternatives gives

    p[2 sum_(j!=ell)P_(ell,j)+P_(ell,ell)]
        >=2 sum_(j!=ell)P_(V,j)+P_(V,V).              (KB4)

Entries involving V use the same eta. V is the virtual parent of
this particular original label; it is not the independently chosen
original test at a smaller modulus. A shallow cylinder retains all
its extensions. A sibling may be omitted from the averaging only
when its score is identically zero under the whole actual measure;
being killed in some old rows is insufficient.

Zero-current labels have a different score because KB1 omits A^2.
For ell in J0 the replacement change is

    2 integral (J-I_ell) C d eta.                    (KB5)

Full residue averaging and literal old-coordinate sibling averaging
therefore give, respectively,

    m_ell sum_(j in J+)P_(ell,j)
        >=sum_(j in J+)P_(j,j),                      (KB6)

    p sum_(j in J+)P_(ell,j)
        >=sum_(j in J+)P_(V,j).                      (KB7)

In KB7, p is an old prime with positive exponent in that label; the
unit label has no sibling refinement. Applying
KB3 to a zero-current label would optimize an extra A^2 term and is
not justified. Every legal replacement comparison occurs after
integrating across all old rows, with one replacement residue used
throughout those rows.

For an upper optimization let R contain the exact b, chosen P and
virtual-parent entries of every actual candidate, with any retained
source, union and CR constraints. Let g_r(P) be the left side minus
right side of any KB3--KB7 constraint. Every actual maximizing test
satisfies g_r(P)>=0. Thus, for fixed lambda_r>=0,

    sup_(actual families)F_p^-(W)
      <=sup_((b,P) in R)
          [Wb+X(P)+sum_r lambda_r g_r(P)].           (KB8)

Indeed at the actual maximum the added term is nonnegative, and
its data belong to R. The positive sign is required: an outer
candidate with negative optimality residual is penalized. One may
instead impose g_r>=0 directly. These constraints do not permit
independent maximization of separate Gram entries.

At17 the incoming probability is nu13; at19 it is normalized physical
mu17=nu13 K17. KC takes separate Xi suprema, so each step may use
its own maximizing complete test for this upper bound. A common
maximizer for the two steps is not assumed. The existing generic Gram
projection is unchanged. KB3--KB7 add the correct objective's actual
optimality conditions; their numerical improvement to the unrestricted
KC frontier has not been computed. No new Lean declaration is added.

### A scalar countermodel for every square shift in the fixed17/19 continuation

The21 scalar observations currently retained for the supported AP(4,6)13
law do not close the following fixed17/T8,19/T8 common-N functional,
even after optimizing the square shift and choosing any pointwise-majorizing
clip. There is one abstract positive integer-valued source satisfying all21
observations for which the direct functional has minimum

    67033659073176343/16899387908832000
        =3.966632367681379... >0.                         (ASB1)

The minimum occurs at shift121. This is a countermodel to the specified
scalar relaxation. It is not an actual congruence family or an asserted
realization under the AP13 construction, and it gives no lower bound on
an actual killed frontier. Other schedules and additional observations
are outside the conclusion.

#### The fixed functional and its pointwise majorants

For p in{17,19}, keep threshold8 and define

    a_p=(3p-1)/(p-1)^2,
    c_p=(p-1)/(p-9),
    kappa_p(z)=(p-1)/(p-1-min(z,8)).

For a real square shift0<=tau<=484 put W=484-tau. The direct cost and
the clipped cost, for z,y>=0 and K>=0, are

    H_direct(p,W;z,y)=W(z-8)_+/(p-9)+a_p kappa_p(z)y^2,
    H_K(p,W;z,y)=W(z-8)_+/(p-9)
             +a_p[c_p y^2-(c_p-kappa_p(z))min(y^2,K)].  (ASB2)

The notation H_direct does not mean the K=0 instance of H_K. Since
min(z,8)<=8 and p>9, every denominator is positive and kappa_p(z)<=c_p.
Thus the exact identity

    H_K-H_direct
       =a_p(c_p-kappa_p(z))(y^2-min(y^2,K))>=0           (ASB3)

holds for every K>=0, including choices of K depending on the row or
on tau. More generally, any pointwise majorant of H_direct has the same
lower-bound obstruction established below.

Let N be independent of the abstract source X, with the complete
auxiliary law for the capped17 step:

    Pr(N=1)=15/17,
    Pr(N=n)=32/17^n for every integer n>=2.             (ASB4)

The independence in ASB4 belongs only to this auxiliary scalar model.
It is not an independence assertion about original forbidden congruences.
Use z=y=X at17 and z=y=NX at19. The scalar functional under consideration is

    D(tau)=E(X^2-tau)_+ - W
       +E H_direct(17,W;X,X)
       +E H_direct(19,W;NX,NX).                        (ASB5)

The same source X is used in all three terms. Replacing either direct
cost in ASB5 by a pointwise majorant can only increase D(tau).

#### One source satisfying the complete stated observation set

Take

    Pr(X=1)=7/100,  Pr(X=11)=93/100.                   (ASB6)

This is a normalized positive probability. Its observations are

    E X=103/10,  E X^2=563/5,
    E(X-h)_+=(93/100)(11-h) for1<=h<=10,
    E(X-h)_+=0 for11<=h<=17,
    E(X^2-16)_+=1953/20,
    E(X^2-81)_+=186/5.                                 (ASB7)

Every value in ASB7 is at most the corresponding published scalar upper
bound: mean, square and H1--H17 from
[the continuation certificate](shared_square_continuation_certificate.json), and the two square hinges
from [the square certificate](shared_cell_square_certificate.json). The verifier checks all21
inequalities separately and retains their exact slacks. In particular,
the close comparison at H6 has strictly positive slack

    1144980123755523/246025127976511-93/20
        =19265573294937/4920502559530220 >0.

The source-square bound is the same improved Gamma13 used by the
continuation certificate. The SQ16 shift identity and the SQ81 source
identity are checked against the pinned source files. The certificate's
statement is exactly these21 upper observations; no additional conditional
profile, original-label relation, or probability-construction constraint
has been checked for ASB6.

#### Complete auxiliary tails and exact cost coefficients

For a diagonal input t>=1, the direct cost splits into an affine function
of W:

    H_direct(p,W;t,t)=W b_p(t)+s_p(t),
    b_p(t)=(t-8)_+/(p-9),
    s_p(t)=a_p kappa_p(t)t^2.

The geometric law ASB4 has total probability1 and exact moments

    E N=9/8,  E N^2=89/64.

For either source atom x in{1,11}, every n>=8 satisfies nx>=8. Therefore
the complete19 tail, without any truncation or renormalization, is

    sum_(n>=8) Pr(N=n)b19(nx)
       =[x E(N;N>=8)-8 Pr(N>=8)]/10,
    sum_(n>=8) Pr(N=n)s19(nx)
       =(14/45)x^2 E(N^2;N>=8).                        (ASB8)

The exact tail moments in ASB8 are

    Pr(N>=8)=2/410338673,
    E(N;N>=8)=129/3282709384,
    E(N^2;N>=8)=8329/26261675072.

They follow by writing n=8+k in the three convergent geometric sums
sum r^k, sum k r^k and sum k^2 r^k, with r=1/17. The verifier also derives
them by subtracting the finite n<8 part from the full moments, and checks
a second complete decomposition at cutoff16. The two decompositions agree
separately for each source atom and for both coefficients of the cost.
For x=11, all n>=1 already lie in the upper branch, supplying the further
independent identities

    E b19(11N)=[11 E N-8]/10,
    E s19(11N)=(14/45)121 E N^2.

Writing B for the total coefficient of W and S for the direct square
contribution, the exact results are

    E b17(X)=279/800,
    E b19(NX)=667826190311/1641354692000,
    B=620124319573/820677346000
        =0.7556250000021324...,

    E s17(X)=168851/3840,
    E s19(NX)=20576332556971219/422484697720800,
    S=313229334820050587/3379877581766400
        =92.67475736690733... .                         (ASB9)

#### Every square shift and every pointwise-majorizing clip

Substituting ASB9 into ASB5 gives the exact expression

    D(tau)=E(X^2-tau)_+ + S-(484-tau)(1-B).             (ASB10)

The two source values have squares1 and121. Consequently D is continuous
and affine on each of[0,1],[1,121],[121,484], with slopes respectively

    -B,  7/100-B,  1-B.

The exact inequalities7/100<B<1 make these slopes negative, negative and
positive. Hence the global minimum over every real admissible shift is
at tau121, where the square hinge vanishes. Direct substitution gives

    D(121)=S-363(1-B)
           =67033659073176343/16899387908832000>0.

This proves ASB1 over the entire continuous shift interval, rather than
only an integer grid. ASB3 then proves the same strict obstruction for
every pointwise-majorizing clip, for each shift. Changing the clip cannot
make this already positive direct value negative.

Therefore an argument that enlarges the source to all abstract laws
satisfying just the21 stated observations cannot certify negativity of
this fixed17/T8,19/T8 common-N functional. A successful continuation must
exclude ASB6 by additional information, change the functional, or use a
different schedule or construction. This conclusion does not say that
ASB6 arises from compatible original prefixes, that the actual AP13 law
has these moments, or that an actual legal test attains any of these
costs. In particular ASB1 is not a refutation of the finite killed-frontier
requirements or a settlement of unrestricted Erdős7.

The [standard-library verifier](verify_scalar_all_shift_barrier.py) pins both observation certificates,
recomputes all21 comparisons and complete tails, and compares its entire
[output certificate](scalar_all_shift_barrier_certificate.json). Its rational piecewise calculation supports the
ordinary proof above; neither finite checks nor stored certificate fields
are represented as a Lean proof. Use `python3 -I -O` with
`--source-directory` if the pinned inputs are in a different directory.

### Actual AP13 zero-block equality and a positive killed maximum gap

For a concrete actual AP13 source, zero-current anchoring can give exactly the physical global maximum, even with a nonconstant old test, a varying natural cap and positive mixed charge. The same example has a strictly smaller killed maximum. Thus retaining the original zero block alone need not improve the physical charge-plus-square upper bound; retaining the actual killed overlap addresses a different loss and is quantitatively relevant here.

The full original test domains have288 labels. Their exact physical maxima and rigorous killed-maximum intervals are listed below. The later RS calculation proves that each killed lower endpoint is the exact maximum.

| p | physical global square maximum | killed global square maximum, lower and upper bounds |
|---|---:|---:|
|17|20.744427331665257...|[20.740224222517096...,20.7407634733786...]|
|19|20.2733090180926...|[20.269665723218274...,20.27021145401735...]|

Every bound concerns the entire original complete-test domain, including independently chosen zero and positive current blocks. The killed maximum is bracketed, not claimed to have been computed exactly. The source's exact old square is795613/46656=17.052747770919066... and its Haar density is1001/384. It satisfies the published SQ observations by strict margins. These are ordinary finite-family results, not a generic17/19 certificate or a covering-system resolution.

#### What zero-current anchoring can preserve

Fix any old probability mu, one actual normalized current kernel, all old complete labels and a finite current height H. Suppose its depth-e prefix cap is gamma(x)p^-e. Write

    Gamma(w)=sup_A E_mu[w A^2],
    s_H=sum_(e=1..H)p^-e,
    a_H=sum_(j=1..H)(2j+1)p^-j.

Expanding every original ordered pair and applying2uv<=u^2+v^2 gives

    Gamma_new <= Gamma(1+s_H gamma)
                         +(a_H-s_H)Gamma(gamma).       (ZB1)

Indeed, the coefficient of A0^2 is1+s_H gamma. The coefficient of a positive old block Ae^2 is gamma times

    p^-e+sum_(f=1..H)p^-max(e,f),

and those positive coefficients sum to a_H-s_H. No old layout or residue is identified in this inequality. Since Gamma(1+s_H gamma)<=Gamma(1)+s_H Gamma(gamma), ZB1 preserves a nonnegative support-function gain over Gamma(1)+a_H Gamma(gamma). That gain is zero if one old test simultaneously maximizes the two weighted squares. The all-height limits are s=1/(p-1) and a-s=2p/(p-1)^2; these are exact complete coefficient sums, not truncated auxiliary laws.

For a fixed actual mask its charge b is independent of the test. Adding Wb to ZB1 therefore preserves the same gain and the same equality cases for every W>=0. The shared-cell SQ observations bound univariate old costs; they do not themselves assert that the two weighted maxima have different optimizing layouts.

#### One genuine actual AP13 source

Take Q=3^8*5*7*11*13=32837805. For every nonunit divisor d of Q include the single actual forbidden class0 modulo d. Their union is exactly the nonunits. The actual uniform357 source is uniform on its units. At11 and13 all mixed classes with residue0 are inactive on the previous unit source; the pure class0 removes its zero root. Consequently the prescribed AP11/T4 and AP13/T6 kernels, followed by the single final conditioning, give exactly the uniform unit law mu on Z/QZ. The final conditioning has mass1. This is an instance of the actual AP13 construction, not an independently chosen atomic law.

Let x denote the ternary coordinate and

    E_j={x=1 mod3^j}, 1<=j<=8,
    R=sum_(j=1..8)1_Ej.

Under the ternary unit law,

    Pr(R=0)=1/2,
    Pr(R=j)=3^-j for1<=j<=7,
    Pr(R=8)=1/(2*3^7).

The other four coordinates are independent uniform nonzero roots. For a complete old test centered at1, the ternary load is1+R. Its other-prime factor has square expectation

    S=product_(q=5,7,11,13)(1+3/(q-1))=273/64.

Every unweighted prefix-pair cap is attained by this centered test, so the exact old complete-square maximum is

    S E(1+R)^2=795613/46656.

The actual source density is Q/phi(Q)=1001/384. For the fixed centered test, its square-hinge at81 is64423/14580, computed by the finite ternary and four-Bernoulli product law. No convex-cost maximum is needed: the exact square bound G implies E A<=sqrt(G), E(A-h)_+<=G/(4h) for h>0, and E(A^2-tau)_+<=G for tau>=0. These prove all21 published source upper observations, each with positive slack recorded in the certificate.

#### The actual current masks and exact charges

For p=17 or19 add the actual pure class0 modulo p and the eight distinct original mixed labels3^j p, j=1,...,8. Their CRT residues satisfy

    old coordinate=1 modulo3^j,
    current coordinate=j modulo p.

There are152 distinct actual forbidden moduli in total. In row R=j the actual mixed union is exactly the j roots1,...,j among the p-1 pure survivors. Thus

    alpha_j=j/(p-1), delta=7/(p-2),
    g_j=1/(1-min(alpha_j,delta)),
    beta_j=(alpha_j-delta)_+/(1-delta).

Only beta_8 is positive, and beta_8=1/(p-1). The exact global charges are

    b17=1/69984, b19=1/78732.                           (ZB2)

Put t_j=g_j/(p-1) and q_j=1-beta_j. The good-root physical and killed masses both equal t_j; the physical bad roots each have mass beta_j/j. These row masses sum to1. The entire current root p-1 is clean on every old row.

The literal actual pure mass is(p-1)/p. Its full-Haar cap is p g_j/(p-1), whereas SH26's generic pure envelope is(p-1)g_j/(p-2). The strictly positive difference

    g_j/[(p-2)(p-1)]

is retained separately. No claim that generic pure-density savings vanish is made.

#### Global physical maximality, not only a favorable test

For any fixed independent old blocks A0,A1, putting every current-positive original label on the common clean root simultaneously attains all its current pair caps. Their exact largest physical and killed squares for those old layouts are

    E[A0^2+t(2A0 A1+A1^2)],
    E[q A0^2+t(2A0 A1+A1^2)],                         (ZB3)

respectively. These are upper bounds for arbitrary current-root assignments by the actual kernel cap, including cases in which roots vary with the original old divisor. Thus the current optimization is eliminated over the full domain, as in the existing clean-root result CS1.

The function g_R is a nondecreasing step function of the nested E_j. Hence

    mu g =g_0 mu+sum_(j=1..8)(g_j-g_(j-1)) mu|E_j

is a positive combination of uniform laws restricted to those actual nested cylinders. For each such component, every old modulus-cylinder mass is maximized by the residue1. Expanding pairs proves that the same complete centered test simultaneously maximizes E A^2 and E t A^2. In particular ZB1 at H1 is an equality:

    Gamma_phys=Gamma(1)+3Gamma(t).                    (ZB4)

The maximizing zero and positive old blocks are equal to that centered test, but no such equality was assumed in the optimization domain. The zero-block gain Gamma(1)+Gamma(t)-Gamma(1+t) is exactly0, despite g varying and b>0. Adding any fixed Wb preserves equality for the whole physical cost.

#### Exact removal of the independent other-prime axes

The current kernel depends only on x and the current prime coordinate. For either its physical or killed measure, the full complete-square maximum equals S times the maximum on the3^8 p subproblem.

For the upper bound, first replace every other-prime test-root choice by the common root1. Conditional on the ternary/current coordinates, each original pair has nonnegative mass, and this replacement attains its other-prime cylinder-intersection cap simultaneously. It therefore increases or preserves the square. Group the resulting labels by their original other-prime divisor d. Each group is a complete3^8 p test L_d, with its own ternary/current residues. Cauchy-Schwarz under the positive physical or killed submeasure gives E L_d L_e<=Gamma_(3,p). Summing the remaining other-prime pair masses gives S. Conversely, taking the same maximizing3^8 p test in every group attains this upper bound. Finite maxima exist.

This argument retains every original label, and it applies specifically because the four other coordinates are independent of this actual kernel. It is not a reduction for an arbitrary AP13 source.

#### A full-domain killed upper bound and a better killed witness

Work on the ternary subproblem. Let

    G3=E(1+R)^2,
    Jt=E[t_R(1+R)^2],
    w_j=q_j+t_j.

From ZB3 and2A0 A1<=A0^2+A1^2,

    Gamma_killed^(3,p)<=Gamma_3(w)+2Jt.              (ZB5)

The weight w_j increases for j=0,...,7; its value at8 may fall. For a ternary depth a>=1, every nonspine prefix has constant R<=a-1. The greatest such mass is its ordinary prefix mass times w_(a-1). The spine prefix has weighted mass sum_(j>=a)Pr(R=j)w_j. Thus its exact maximal weighted cylinder mass is

    C_a=max{w_(a-1)/(2*3^(a-1)),
                          sum_(j=a..8)Pr(R=j)w_j},
    C_0=E w.

Every ordered pair of old3^a labels has intersection either empty or a prefix of its maximal depth. There are2a+1 ordered exponent pairs of maximal depth a. Therefore

    Gamma_3(w)<=sum_(a=0..8)(2a+1)C_a.              (ZB6)

This is a rigorous upper bound over every complete old layout, including nonnested ones. It does not assume that the maximizing cylinders for different depths are compatible; in this example the separate caps at depths7 and8 are off-spine and need not be jointly attained. Combining ZB5-ZB6 and multiplying by S gives the displayed killed upper bounds.

For a lower bound choose a single old center z=1+Q/3. Its other-prime coordinates are1, its ternary prefixes through depth7 remain on the spine, and its depth8 prefix is a different child of E7. Use this old layout in both current blocks and the same clean current root. On the two off-spine children of E7 its ternary loads are9 and8, while on E8 its load is8. Formula ZB3 evaluates this complete literal test exactly and gives the displayed lower bound.

This new test has a strictly larger killed square than the physically maximizing centered test: the improvements are26299/35831808 at17 and137683/184757760 at19. Thus the physical maximizer is demonstrably not a killed maximizer. The killed maximum remains within intervals of widths0.000539250862 and0.000545730800, respectively; no exact-max claim is made.

The global maximum loss is nevertheless bounded below sharply enough to be nontrivial:

    Gamma_phys-Gamma_killed >=49231/13436928
                 =(49231/192)b17 at17,
    Gamma_phys-Gamma_killed >=572299/184757760
                 =(1716897/7040)b19 at19.             (ZB7)

The factors exceed256 and243. This is a forced loss over the full test domain, not the killed loss of only one selected test.

#### An explicit normalized17 history for the19 fixture

The direct19 fixture above has original17 height0; its intervening17 step is the identity. No original17 labels were removed. To make17 explicitly present, retain the identical actual AP13 source and include every nonunit old divisor of Q*17 with residue0 before the19 step. The additional actual17 pure class is0; all actual mixed17 classes are inactive on the unit input. Thus the prescribed normalized AP17/T8 law is mu17=nu13 times uniform nonzero17 roots, with mixed charge0 and no intermediate conditioning.

Apply the same eight19 mixed classes to this actual mu17. All19 square values, its Xi frontier, and the upper/lower maximum-loss bounds above multiply exactly by19/16, the complete17 test-square factor. The charge b19 remains1/78732. The original domain now contains576 complete test labels and296 distinct forbidden moduli; its full period is Q*17*19. The certificate records the entire extension. This is a legitimate KC19 normalized physical input with a nontrivial pure17 step; it is not a claim for a preceding17 step having positive mixed charge. The positive17-charge fixture and this19 fixture are separate actual families and their displayed F values must not be summed as one chain.

#### What this says about the KC frontier

For this fixed actual family the positive-current killed frontier is exactly

    Xi_p^-=3S Jt,
    F_p^-(403)=403b_p+3S Jt.                          (ZB8)

The clean current root makes every positive pair survive; the common centered old test simultaneously attains the weighted caps. These exact F values are3.6974380198225503... and3.2256798774636306.... The example therefore does not threaten the numerical KC target. It shows that a physical zero-block gain and a killed saving have distinct behavior: the former can vanish at a genuine global maximum while the latter is forced and the optimal full killed test changes.

The shared-cell source observations alone do not provide the missing general weighted correlations. A generic improvement must control actual mask/test structure, or retain a quantitative relation between the killed baseline and the positive-current frontier; the finite explicit relation here uses special nested geometry and independent other-prime axes.

The [verifier](verify_actual_zero_block.py) reconstructs every old divisor and every literal current CRT class, checks all152 forbidden labels and288 test labels, all row normalizations, source moments, physical global-max formulas, the full-domain killed upper bound and the complete moved-test lower bound. All rational constants and test-inventory digests are compared against its [certificate](actual_zero_block_certificate.json). The global claims are supported by the ordinary arguments above; no Lean declaration or unrestricted endpoint is asserted.

### The common original test and the losses in the KC comparison

The exact killed kernel already retains the zero-block square, as in
GC2 and ZB3. The following algebra identifies which quantities must
remain coupled when tightening KC13. It is an optimization interface,
not a new Lean declaration or a proved uniform improvement.

Use nu=nu13, normalized physical K=K17, killed K-=K17^-, and the
nonnegative removed kernel D=K-K-. Set

    beta17=D1, mu=nu K, xi=nu K-,
    beta19=1-K19^-1, eta=xi K19^-.

For a single complete original test L, let B be its literal zero19
block and A the literal zero17 block of B. Their inherited residues
are fixed throughout. Define

    R17=B^2-A^2, R19=L^2-B^2,
    G17=K- R17, G19=K19^- R19.

Both R terms and both G terms are nonnegative. Kernel expansion gives
the exact identity

    Q_eta(L)=nu(A^2-484)
       +nu[G17+beta17(484-A^2)]
       +xi[G19+beta19(484-B^2)].                     (CT1)

The final bracket f19 is signed. Its physical-input replacement is
xi f19=mu f19-nu D f19. The domination xi<=mu alone does not permit
dropping the last term. In particular a negative f19 on removed17
mass reverses the desired comparison.

For0<=tau<=484 set W=484-tau, h=(A^2-tau)_+,
j=(tau-A^2)_+, b17=nu beta17, b19=mu beta19, and
d=beta17+K- beta19. Another exact expansion is

    Q_eta(L)=nu h-W+W(b17+b19)+nu G17+mu G19
                -Delta_tau(L),                     (CT2)

    Delta_tau(L)=nu[d h]+eta j
       +xi[beta19 R17]+nu D G19+W nu D beta19 >=0.   (CT3)

Indeed eta(A^2-tau)=nu h-nu[d h]-eta j,
eta R17=nu G17-xi[beta19 R17], eta R19=mu G19-nu D G19,
and eta1=1-b17-b19+nu D beta19. Substituting proves CT2--CT3
without a positivity assumption on the final mass or any cutoff of
original labels. At tau0, the first term and the R17 correction
together equal nu[beta17 A^2]+xi[beta19 B^2].

For a fixed family one can take the supremum of
nu h+nu G17+mu G19-Delta_tau(L) over the same original L.
Separately maximizing its positive terms and subtracting the deficit
of one selected test is invalid. Even CT3 is not the entire gap in
KC13: replacing nu h by T13 and the two actual G integrals by their
separate Xi suprema can introduce further gaps.

KB3--KB7 apply to maxima of the separate positive-current Xi objective.
They cannot be imposed without proof on maxima of this new joint
objective. For the full Q objective, every label instead uses the
full-square replacement score integral_eta J(2(L-I_ell)+1), including
zero-current labels. Its whole-residue best-response condition is

    m_ell[2 sum_(j!=ell)P_(ell,j)+P_(ell,ell)]
         >=2 sum_(j!=ell)P_(j,j)+eta1,               (CT4)

where all entries now use the final eta. This is the same elementary
replacement argument with the correct objective, not a new abstract
theorem.

A useful task-specific observation is the actual surviving low-load
band E={A^2<=c}, c<tau. CT3 gives

    Delta_tau(L)>=(tau-c)eta(E),
    eta(E)>=nu(E)-nu[1_E beta17]-mu[1_E beta19].      (CT5)

Only nonnegative restricted bad masses use xi<=mu here. Thus a bound
on the bad mass inside the same inherited test's low-load band has
a quantitative use. The existing21 scalar upper observations do not
supply those conditional masses, and CT5 has not yet yielded a
uniform KC bound.

There is no height-independent positive lower bound for eta(A=1).
For any H>=1 take distinct actual moduli3^n,1<=n<=H, with residues
a_n=3^(n-1)-1. At those same test moduli choose
b_n=2*3^(n-1)-1 and retain the unit test. The two classes at depth n
are the two side children of the common ternary branch whose earlier
digits are all2. Each family consists of mutually disjoint classes,
and their combined union leaves exactly -1 modulo3^H.

The actual survivor fraction is (1+3^-H)/2. The test load on its
uniform survivor law takes only values1 and2, with

    Pr(A=1)=2/(3^H+1) tending to0.                   (CT6)

Absent11/13/17/19 exclusions preserve this observation under the AP
construction. All original test labels are present. Hence even this
genuine family rules out a uniform positive unit-load mass, while a
larger band such as A^2<=4 has full mass. A successful CT5 argument
must control an appropriate band and its actual deletions, or split
the families into cases with proved additional hypotheses.

### Actual radial families retain a strict common-test loss

For the two previously pinned actual AP13 fixtures, the complete killed-square maxima are exactly

| current prime | complete killed-square maximum |
|---|---:|
| 17 | 5109223159/246343680 |
| 19 | 127329253189/6281763840 |

These are the earlier literal spur lower bounds, now also upper bounds over every original complete test. Each zero and positive block retains all144 independently selected old labels. The intermediate ternary optimization retains two independently selected labels at each depth; it does not restrict all depths to a single nested chain.

More generally, a positive separation between independently maximizing the killed baseline and positive-current frontier holds for the explicit radial actual families at every ternary height H>=2 and every prime p>max(13,H+1), with threshold T=H. The quantitative statement below does not assert an exact general maximum or a uniform inequality for arbitrary AP13 sources.

#### An actual family at arbitrary finite height

Take Q_H=3^H*5*7*11*13, and forbid0 modulo every divisor d>1 of Q_H. The actual uniform357 source and the prescribed pure-base AP11/T4 and AP13/T6 steps, followed by one final conditioning, give exactly uniform measure mu on the units of Q_H: all mixed classes are inactive, and the pure classes remove only zero roots.

At the current prime p, forbid pure root0 and, for j=1,...,H, one class modulo3^j p whose old residue is1 and current residue is j. These are distinct original moduli; root p-1 is clean on every row. The full original current height is1. No higher original test labels exist or are discarded.

Let R be the number of nested old cylinders E_j={x=1 mod3^j} containing x. Its probabilities under the ternary unit law are

    P_0=1/2,
    P_j=3^-j for1<=j<H,
    P_H=1/(2*3^(H-1)).

Choose delta=(H-1)/(p-2), the threshold-H parameter. The physical assigned bad mass is positive only at R=H:

    beta_H=1/(p-1),  beta_j=0 for j<H,
    b=P_H/(p-1).

Here b is also the full actual charge because the other four coordinates are independent. Put q_j=1-beta_j and let t_j be the probability of the common clean current root:

    t_j=1/(p-1-j) for0<=j<H,
    t_H=(p-2)/[(p-1)(p-H-1)].

All t_j are strictly increasing when H>=2. The source's other four prime axes contribute the exact square factor

    S=product_(r=5,7,11,13)(1+3/(r-1))=273/64.

The previously established clean-root and independent-axis arguments apply unchanged: replacing current residues by the common clean root maximizes every positive-current pair, and aligning the independent other-prime roots maximizes their pair masses. Grouping by their original other-prime divisor and applying Cauchy-Schwarz then gives an exact factor S, while preserving every original label.

Thus the full killed maximum is S times

    K=sup_(A0,A1) E[q A0^2+t(2A0 A1+A1^2)],

where each A_i=1+sum_(d=1..H)1_(x=a_(i,d) mod3^d) and every a_(i,d) is independently chosen.

For any nonnegative radial weight w write Gamma_3(w)=sup_A E[w A^2], and put

    G3=E(1+R)^2,   Jt=E[t_R(1+R)^2].

Uniform ternary pair caps and the common opposite root2 give

    Gamma_3(q)=G3-b.

The constant label contributes E q=1-b; every positive-depth pair avoids E_H and attains its unweighted cylinder cap when centered at2. Monotonicity of t shows that all weighted t-pair caps are attained by centering every label at1, so Gamma_3(t)=Jt. Consequently

    Gamma_full(q)=S(G3-b),
    Xi_p^-=3S Jt.

The factor S multiplies b in the first formula. Writing Gamma_full(1)-b would be incorrect for this complete old domain.

#### A general strictly positive common-test loss

For depth a>=1 define

    m_a=1/(2*3^(a-1)),
    Delta_a=sum_(j=a..H)P_j(t_j-t_(a-1))>0.

The maximal q-prefix mass is m_a, the maximal t-prefix mass is m_a t_(a-1)+Delta_a. A nonspine depth-a prefix has R<=a-1 constant; among these, R=a-1 maximizes its q+t mass. The spine prefix contains the whole charged leaf. Therefore its exact maximal q+t prefix mass is

    max{m_a(1+t_(a-1)),
        m_a(1+t_(a-1))+Delta_a-b}.

The difference between the sum of the separate q and t prefix maxima and their joint prefix maximum is exactly min(b,Delta_a).

There are2a+1 ordered old-label pairs of maximum exponent a. Gamma_3(q) and Gamma_3(t) attain all their respective pair caps simultaneously. Gamma_3(q+t) is at most the sum of its pair caps; this upper bound does not assume that those caps can be simultaneously realized. Since2A0 A1<=A0^2+A1^2,

    K<=Gamma_3(q+t)+2Gamma_3(t).

It follows that

    Gamma_full(q)+Xi_p^- - sup_L integral L^2 d(mu K_p^-)
      >= S sum_(a=1..H)(2a+1)min(b,Delta_a)>0.       (RS1)

In particular the depth1 contribution alone is3S min(b,Delta_1)>0. This is a general same-family inequality for the explicit actual radial construction. It proves that independently sharp baseline and positive-frontier estimates need not be jointly sharp. It does not supply a numerical bound for all actual KC layouts.

For H=8,p=17 or19, the right side of RS1 is exactly the difference between the independently optimized baseline-plus-Xi and the previously published ZB killed upper bound. The exact optimization below improves that separation further.

#### First-exit normal form preserves all independent labels

A label selecting residue0 modulo3 has zero mass on the source. Moving that label to a unit cylinder cannot decrease the objective, whose expanded pair coefficients are nonnegative. Hence restrict to unit residues.

For a depth-d label, either its cylinder is the spine E_d, denoted r=0, or it first differs from the spine at a unique depth r in{1,...,d}. Its representative can be chosen as

    a(d,0)=1,
    a(d,r)=1+3^(r-1) for1<=r<=d.

For r=1 the other unit root is2. For r>=2 the two off-spine children have identical uniform measures and the same radial q and t values. All labels with the same first-exit depth r can be moved to this one representative path. Their individual weighted cylinder masses are preserved and all pair intersections within this group become maximal. Intersections with a spine label depend only on whether that spine's depth is less than r, and are therefore preserved. Labels with different nonzero first-exit depths lie in disjoint branches, and remain disjoint.

Thus this simultaneous replacement never decreases any expanded nonnegative pair contribution. Conversely every resulting collection is an actual legal complete test. This proves an exact reduction to independent choices

    r_(i,d) in{0,...,d}, i=0,1, d=1,...,H.

Different depths may choose different offshoots. No globally nested-chain claim is used; such a claim is false for general radial weights.

For a radial w, the mass of the representative cylinder is

    C_w(d,0)=sum_(j=d..H)P_j w_j,
    C_w(d,r)=w_(r-1)/(2*3^(d-1)) for r>0.

Two representative cylinders meet precisely when their explicit residues agree modulo3^min(d,e). If compatible, their intersection is the deeper representative cylinder; otherwise it is empty. These are the exact table entries used below.

#### Exact integer optimization and exhaustive branch coverage

For H=8 there are16 independently selected positive-depth labels, with total domain

    [product_(d=1..8)(d+1)]^2=(9!)^2=131681894400.

The two depth0 labels are constant1. Expanding the ternary objective gives a constant E(q+3t), one unary term per label, and one term per unordered pair. For a zero-block label the unary weight is3q+2t; for a positive-block label it is5t. A pair of zero-block labels has weight2q; every other pair has weight2t. The representative-cylinder formulas therefore determine a finite quadratic table exactly.

The verifier multiplies all nonconstant rational coefficients by their common denominator. The integer scales are25219434240 at17 and53591297760 at19. It supplies the literal spur candidate

    r_(i,d)=0 for d<=7,  r_(i,8)=8, for both i.

The integer objective values excluding the constant term are respectively92418259287 and191714857884.

The branch-bound calculation is exact over an arbitrary finite unary/pair table. At a partially assigned node, `current` is the exact contribution already assigned; `adj_i(r)` is the original unary plus interactions with assigned labels. If U is the remaining label set, then every completion is at most

    current+sum_(i in U)max_r adj_i(r)
           +sum_(unordered i,j in U)max_(r,s)V_ij(r,s).

Conditioning on one candidate i=r gives the stronger valid bound

    current+adj_i(r)
      +sum_(j in U\{i})max_s[adj_j(s)+V_ij(r,s)]
      +sum_(unordered j,k in U\{i})max_(s,t)V_jk(s,t).

Every termwise maximum bounds the corresponding term in every completion. If all choices of any selected variable are bounded by the incumbent, the whole node closes. Otherwise every still-viable choice is recursively visited. Every excluded choice and every terminal node contributes its exact product of remaining domain sizes to a disjoint coverage count. The final count is131681894400 for each prime.

The deterministic replay visits9 nodes per prime, computes all screening bounds as integers and reaches no assignment exceeding the literal spur candidate. The [certificate](actual_radial_maximum_certificate.json) includes trace-event counts, a SHA-256 of the recomputed exact bound trace, and the full domain-coverage count. The trace hash identifies the replay; soundness follows from the inequalities and exhaustive branch partition, not from trusting the hash. No external optimization solver is part of this certificate.

#### Exact separation and its two contributions

At the maximizing spur test the killed baseline and Xi losses are both positive:

| p | baseline loss from its own supremum | Xi loss from its own supremum | total split-sup loss |
|---|---:|---:|---:|
| 17 | 637/165888 | 10829/35831808 | 148421/35831808 |
| 19 | 637/186624 | 10829/61585920 | 221039/61585920 |

The old unweighted square is G=S G3=795613/46656. On the charged leaf, the spur's ternary old load is8, so its deleted old square is64S b=273b. Its baseline loss is therefore(273-S)b. Switching the last test cylinder from E8 to one off-spine child of E7 changes E[t A^2] by17 P8(t8-t7); hence the Xi loss is3S*17P8(t8-t7). These exact formulas add to the displayed gaps.

The baseline alone is maximized by moving all positive-depth ternary labels to root2. Xi alone is maximized by centering both old blocks on the spine. The common killed maximizer uses the different spur arrangement. The calculation retains one actual source, one kernel and one globally legal complete test at every stage.

For the pinned explicit normalized17 history in the19 construction, the independent extra17 coordinate multiplies the complete-square maximum and split-sup loss by19/16. It has576 original test labels and zero17 mixed charge. This is a valid same-chain extension of the19 fixture, not a license to add the separate positive-charge17 fixture to it.

#### Correlation is not the only discarded information

The same globally maximizing spur test also has strict losses when a signed old term is replaced by its positive part. Its old source hinge at81 is64423/14580: moving the full centered test to the spur preserves its distribution under the uniform unit source. This is a value of this specific test, without asserting that it maximizes every convex cost.

Write A for this full old load and beta for the actual row charge. The two additional nonnegative terms are

    D=E_mu[beta(A^2-81)_+],
    N=E_mu[(1-beta)(81-A^2)_+].

Their exact values on the same killed-maximizing test are

| p | D | N |
|---|---:|---:|
| 17 | 4283/1492992 | 510347321/7464960 |
| 19 | 4283/1679616 | 574140853/8398080 |

To compute them, let B be the other-prime old-load factor. Then E B^2=S and Pr(B=1)=33/64. On the charged leaf A=8B, so E(64B^2-81)_+=12849/64 and E(81-64B^2)_+=561/64. Thus D=(12849/64)b and N=H81-G+81-(561/64)b. All values are exact under the same source and kernel.

These terms are distinct from the split-sup mismatch. In particular the positive-part step already loses information even if a later bound manages the baseline/Xi correlation perfectly. The general multi-prime signed telescope must also retain its killing, transport and mass terms; this finite example does not identify any one loss as the only remaining obstruction.

The [radial maximum verifier](verify_actual_radial_maximum.py) hash-pins the already published actual-family certificate and verifier, reconstructs the full finite table, recomputes every integer bound and domain count, checks all new maxima against the literal pinned lower witnesses, and checks the displayed separations and hinge losses. These are ordinary mathematical and exact finite computational results, not a Lean declaration or an unrestricted Erdős #7 endpoint.

### Positive radial weights do not justify a nested-chain restriction

The first-exit reduction above retains different offshoots for different original depth labels. Positivity and radiality alone cannot justify replacing these independent choices by a single nested chain.

On Z/9Z give residues0 through8 the positive weights

    (28,48,28,28,1,28,28,1,28)/218.

This probability is radial about1, with shell weights28 outside1 mod3,1 inside1 mod3 but outside1 mod9, and48 at1 mod9. Select one cylinder at each original depth0,1,2:

    A_(a,b)=1+1_(x=a mod3)+1_(x=b mod9),
    a in{0,1,2}, b in{0,...,8}.

There are27 original layouts, of which9 are nested. Write w_b for the unnormalized point weight and W_a for the mod3 cylinder weight. Then W0=W2=84, W1=50, and direct expansion gives

    218 E A_(a,b)^2
      =218+3W_a+(3+2*1_(b=a mod3))w_b.              (RC1)

For a=0 or2, the best nonnested numerator is218+3*84+3*48=614, at b=1; the best nested numerator is218+3*84+5*28=610. For a=1 the largest numerator is218+3*50+5*48=608, at b=1. Hence

    max_(a,b) E A_(a,b)^2=307/109,
    max_(b=a mod3) E A_(a,b)^2=305/109.             (RC2)

The only global maximizers are(a,b)=(0,1),(2,1), both nonnested. The [27-layout verifier](verify_radial_chain_counterexample.py) independently compares the direct pointwise loads with RC1 and reproduces the [full table](radial_chain_counterexample_certificate.json).

The restriction also fails for two independently chosen blocks. For every epsilon>0, Cauchy-Schwarz and RC2 give

    max_(A0,A1) E[A0^2+epsilon*(2A0*A1+A1^2)]
      =(1+3epsilon)*307/109,                       (RC3)

attained when both blocks equal a nonnested maximizer. Restricting both blocks to chains gives exactly(1+3epsilon)*305/109 by the same argument. Thus neither independent block choices nor positive coefficients repair the restriction.

The shell sequence28,1,48 is not monotone. This does not contradict the common-center maximum for a nonnegative combination of nested spine restrictions used for Gamma_3(t). It refutes an extension to arbitrary positive radial coefficients, the situation for which the first-exit optimizer must retain independent offshoot choices. This probability is not asserted to arise from the actual AP13 construction; the result is a counterexample to a proposed optimization reduction, not a covering system or an unrestricted noncoverage theorem.

### Sparse prefix certificates and the actual weighted objective

[RRO Section58 at dev11036b0baf](https://github.com/the-omega-institute/trureturing/blob/11036b0baf142c8e6535e61f29d2cae83ecf7bba/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#58-二进制估值标签下的精度跳跃构造可核验证书与展开输出障碍) constructs sparse ordinary integer witnesses for a complete unit-sum valuation array. Its finite split forest has fewer than n events for n original vertices; binary-encoded jump depths replace traversal through every intermediate digit. Successful witnesses and induced obstructions remain bound to every original input label. The section's polynomial bit bound concerns constructing or checking one complete array, not optimizing over all arrays. This dev increment adds theory and digestion inputs, with no corresponding D5, Blueprint or frozen-state change.

There is an explicit bridge from odd-prime congruence centers to its input language. For each integer center a_i take the two units

    z_i^+=1+p*a_i,  z_i^-=-(1+p*a_i).

Every same-sign sum has valuation0, while

    v_p(z_i^++z_j^-)=1+v_p(a_i-a_j),               (SC1)

with infinity for equal centers. Thus the complete difference-prefix geometry can be expressed using a common unit-sum array. Reconstructing some integer tuple realizing this array does not, by itself, reconstruct the fixed original residues or the actual AP probability.

For the #7 objective, a valid compression must retain all named forbidden and test cylinders, their original depths and identities, and their shared centers across stages. Jump lengths affect mass: a unit cylinder at depth d has uniform unit mass1/[(p-1)*p^(d-1)]. The same unlabelled tree with a different jump depth can therefore have different weighted integrals. Replacing an expanded integer by a sparse digit table neither deletes that factor nor makes its fully expanded rational denominator short.

One sufficient transport contract is a product of measure-preserving prime-coordinate tree isomorphisms that maps every named cylinder to its counterpart and commutes with the stage projections. The physical AP kernels must be transported by those same maps: their row masks, row normalizations and assigned deletion weights then have identical values at corresponding rows. Induction over the stages preserves the complete actual law and the final killed integrals, including every CT loss term. A tree for the test centers alone, or independently chosen witnesses for separate subarrays, does not meet this contract. No such uniform reduction of the full KC optimization is established here.

The sign issue belongs to the objective rather than the sparse syntax. The integer branch-bound inequalities above remain valid for an exact finite unary/pair table with signed entries, because each term is bounded by its own maximum. In contrast, the first-exit consolidation argument uses nonnegative pair coefficients; an intersection-increasing replacement does not justify moving the negative CT correction in the same direction. One must either preserve the full joint integral exactly or supply a valid lower bound for the correction on every branch under consideration.

Equivalently, the direct same-law objective is

    Q_eta(L)=sum_(i,j) integral I_i*I_j d eta-484*eta(1). (SC2)

Its pair entries are nonnegative, but eta is the complete actual killed law. General eta need not have the radial symmetry used by RS1 and the finite first-exit optimization. Sparse realizability certificates do not provide that symmetry or a numerical upper bound on SC2.

Consequently the applicable search improvement is event-based checking of complete prefix candidates and rejection by obstructions whose entire induced input is fixed. Unspecified entries in a partial candidate remain unspecified; Section58 does not authorize filling them independently or applying its small complete-array obstruction claim to arbitrary partial input. The remaining numerical obligation is still the same-test weighted bound, including conditional low-load deletion in CT5 or a complete upper-bound certificate for all KC layouts. Neither the299.398 criterion nor the ASB scalar obstruction is settled by this representation change.

### The actual positive-current frontier can approach its weighted cap bound

Fix p in{17,19}, delta=7/(p-2), and a finite current height H>=2. There is a genuine actual AP13 input and current forbidden family, with positive assigned charge, such that the global maximum over every original complete test satisfies

    Xi_(p,H)^-=a_(p,H) J_(g,H)/lambda_(p,H),
    Xi_(p,H)^-/(a_p J_p)
      =(a_(p,H)/a_p)(p-2)/(p-2+p^-H) -> 1.          (CSH1)

Here a_(p,H)=sum_(e=1..H)(2e+1)p^-e and a_p=(3p-1)/(p-1)^2. The argument uses one actual probability for each finite family and retains all its original labels. It concerns the positive-current objective Xi, not the full killed square or the signed KC objective.

#### Actual labels and probability

Set Q=3^8. The only old forbidden class is0 modulo Q, so sigma is uniform on the6560 nonzero residues of Z/QZ. There are no5,7,11 or13 labels. The AP11 and AP13 steps are identities at their original height0, and final conditioning changes nothing. For the direct19 family, the absent17 step is likewise an identity. These are legitimate missing-class branches of the actual AP construction.

Use one actual pure forbidden class at each current exponent e=1,...,H. Its least-significant-first digits are0 at e=1 and

    (9, 1,...,1, 0)

at e>=2, with e-2 middle ones. Equivalently its residue is9+sum_(j=1..e-2)p^j. The pure cylinders are disjoint: different positive depths first differ where the shorter prefix ends in0 and the longer one has1. They avoid current roots1,...,8 and p-1. The exact pure-survivor Haar mass is

    lambda_(p,H)=1-sum_(e=1..H)p^-e
                =(p-2+p^-H)/(p-1).                (CSH2)

For each i=1,...,8 add one actual mixed class of modulus3^i p, with old residue1 and current root i. CRT gives an integer residue for each class. All H+9 actual moduli are distinct; their least common multiple is3^8 p^H. Every divisor3^j p^e, 0<=j<=8 and0<=e<=H, is an independent complete-test label, including those absent from the forbidden inventory. There are9(H+1) such labels.

Let k(x) be the largest j<=8 with x=1 modulo3^j. Its exact multiplicities on sigma are

    (n0,...,n8)=(4373,1458,486,162,54,18,6,2,1).

The actual mixed union in row k is precisely the k whole current roots1,...,k. Under the normalized pure-survivor base m_H its mass is

    alpha_H(k)=k/(p lambda_(p,H)).

This is an equality for the actual union, not a union bound. Set

    g_H(k)=1/(1-min(alpha_H(k),delta)),
    beta_H(k)=(alpha_H(k)-delta)_+/(1-delta).

For k<=7, alpha_H(k)<delta. For k=8 it exceeds delta: lambda_(p,H)<=(p-1)/p and8/(p-1)>7/(p-2) because p>9. The normalized physical row law has good density g_H relative to m_H and bad total mass beta_H. Its killed restriction keeps the good density and deletes the bad side. Thus the global assigned bad mass is

    b_H=beta_H(8)/6560>0,
    b_H -> (p-8)/[6560 p(p-9)]>0.                 (CSH3)

The limits are9/892160 at17 and11/1246400 at19.

#### The old weighted maximum and the complete current maximum

Write A=1+sum_(j=1..8)1_(x=a_j mod3^j), with all original old residues independent. For depth m>=1, the spine cylinder D_m={x=1 mod3^m} has exactly3^(8-m) old survivors, each with k>=m. Every other depth-m cylinder has k=t<m constant and at most the same number of survivors. The cylinder containing0 has one fewer survivor. Since g_H is nondecreasing, D_m maximizes the g_H-weighted mass among all depth-m cylinders.

Any pair of old test cylinders is disjoint or intersects in one cylinder of their maximum depth. Their weighted mass is consequently bounded by the corresponding D_m mass. All these maxima are simultaneously attained by the coherent old test A_*=1+k. Therefore

    J_(g,H)=sup_A E_sigma[g_H A^2]
           =(1/6560)sum_(k=0..8)n_k g_H(k)(k+1)^2.  (CSH4)

The current KC coefficient is exactly kappa_p(alpha)=((p-1)/(p-2))g(alpha), so on this same actual family

    J_p=((p-1)/(p-2))J_(g,H).                      (CSH5)

For an arbitrary full complete test, let A_e be its independently selected old block at current exponent e. Every positive current pair at depths e,f has pure-base intersection mass at most p^-max(e,f)/lambda_(p,H). Killing can only reduce it. Summing the original old-label pairs and using weighted Cauchy-Schwarz bounds its total by

    [p^-max(e,f)/lambda_(p,H)] E_sigma[g_H A_e A_f]
      <=[p^-max(e,f)/lambda_(p,H)]J_(g,H).

There are2t+1 ordered current-exponent pairs with maximum t>0. Summing gives Xi_(p,H)^-<=a_(p,H)J_(g,H)/lambda_(p,H).

For equality, choose A_e=A_* for every current exponent, including0, and choose the literal nested current prefixes p-1 modulo p^e for all positive original labels. The entire root p-1 avoids both actual pure and mixed classes. Each relevant intersection therefore has exactly its Haar mass p^-max(e,f), divided by the same lambda_(p,H), and survives killing. The old weighted Cauchy-Schwarz inequalities are equalities as well. This is one globally legal complete test attaining every bound; no independence restriction has been imposed on the optimization domain. It proves the first equality in CSH1.

#### Exact limiting boundary and its scope

The complete coefficient tail is

    a_p-a_(p,H)
      =p^-H[(2H+3)p-(2H+1)]/(p-1)^2.

Combining this with CSH2 and CSH5 proves the ratio formula in CSH1. Also J_p<=81(p-1)/(p-9), uniformly in H, because A_*<=9 and g_H<=(p-2)/(p-9). Consequently

    a_p J_p-Xi_(p,H)^- ->0,
    (a_p J_p-Xi_(p,H)^-)/b_H ->0.                  (CSH6)

Thus no fixed positive epsilon, absolute rebate c, or charge coefficient c can make any of the following valid for all these actual finite families:

    Xi_p^-<=(1-epsilon)a_p J_p,
    Xi_p^-<=a_p J_p-c,
    Xi_p^-<=a_p J_p-c b_p.

The examples already satisfy common-prefix feasibility, have an actual mixed union of original labels, have strictly positive charge, and attain the global Xi maximum with every positive-current pair disjoint from the bad union. A uniformly positive saving from only these hypotheses is therefore impossible.

This uses the existing clean-prefix cap-attainment mechanism and adds the old global maximization and limiting comparison with the stated J_p bound. It differs from the earlier nonmaximizing joint-zero tests and from the height-one ZB/RS examples, whose actual pure mass stays separated from the generic all-height lower bound.

The conclusion does not rule out savings conditional on large J_p, larger charge, specific old geometry or actual joint-energy observations. It also does not remove the killed-baseline and transport terms in CT. At the maximizing test above, A_*=9 on the charged row, so its deleted old square is81 b_H and its total killed excess above the unit floor is80 b_H. Only its positive-current overlap is zero. No assertion about the299.398 joint target or an unrestricted covering-system endpoint follows.

### Mask-energy localization requires a valid actual tail bound

An event decomposition can retain some old-side mask-energy information. On one actual input law sigma, write

    G=sup_A E A^2, T(tau)=sup_A E(A^2-tau)_+,
    pi_p(r)=Pr_sigma(alpha_p>r),
    kappa_p(z)=((p-1)/(p-2))/(1-min(z,delta)),
    c_p=((p-1)/(p-2))/(1-delta).

For0<=r<delta and tau>=0, monotonicity of kappa and splitting at the actual event E={alpha_p>r} give

    J_p<=kappa_p(r)G
       +(c_p-kappa_p(r))*min{G,tau*pi_p(r)+T(tau)}. (MT1)

Indeed kappa_p(alpha)<=kappa_p(r)+(c_p-kappa_p(r))*1_E, and for every original A, E[A^2 1_E] is bounded both by G and by tau*pi_p(r)+T(tau). Taking the supremum proves MT1. This is a direct application of the existing event and hinge bounds, not a new Lean declaration. It only improves the estimate after its actual tail premise is supplied.

The proposed universal premise pi_p(1/4)<=1/20 is false, including on a single actual17-to19 chain. Reuse the complete315 unit family above: eleven old forbidden classes0 modulo each nonunit divisor of315 give the uniform law nu on144 units. At each of p=17,19, add pure0 modulo p and, for the increasing list d_1,...,d_11 of nonunit divisors of315, the original CRT class

    x=1 mod d_i, y_p=i mod p, at modulus d_i*p.

These35 forbidden moduli are distinct, with period315*17*19=101745. All48 divisor test labels of that period remain present; the missing17*19 mixed exclusions are not fabricated. There are no11 or13 exclusions, so nu is the actual AP13 law. Each current pure base is uniform on its nonzero roots. For the original forbidden load

    C=(1+I3+I9)(1+I5)(1+I7),
    I_d=1_(x=1 mod d),

the exact current union mass is alpha_p=(C-1)/(p-1), since its active mixed labels use different current roots.

For both primes the event alpha_p>1/4 is exactly C>=6. Among the six ternary units the factor1+I3+I9 has values1,2,3 with counts3,2,1. The factors1+I5 and1+I7 have counts(3,1) and(5,1) at values(1,2). Thus C=6,8,12 have respectively8,2,1 original unit rows, and

    nu(alpha17>1/4)=11/144>1/20.                  (MT2)

The normalized physical K17 preserves the old315 marginal row by row. The19 forbidden masks have no17 coordinate, hence their alpha19 is the same function of x after this actual17 step. Consequently

    mu17(alpha19>1/4)=11/144,
    b17=53/18432>0, b19=61/25920>0.                (MT3)

This uses one explicitly combined original family and its normalized physical17 law. It does not transfer the assertion to the differently conditioned17 law or to the final killed measure. The charge values follow from the same row1 formulas already established for the315 family; K17's preserved old marginal also preserves the19 charge integral.

For this threshold, kappa17(1/4)=64/45,c17=2 and kappa19(1/4)=24/17,c19=9/5. These constants make MT1 a valid conditional estimate, but MT2--MT3 exclude the1/20 premise on the whole allowed class. Conditional estimates restricted by additional actual geometry or energy remain possible. Existing AP3--AP4 hinge comparisons for upper tails are still valid; they do not supply new joint statistics merely by being substituted into MT1, and the fixed scalar ASB obstruction remains in force.

### Source-only energy conditions do not force a positive-current rebate

Fix p in{17,19}, threshold T=8, and one actual incoming probability mu on its full old period Q, with p not dividing Q. Assume Q has at least eight distinct divisors greater than1. This can be the prescribed supported AP13 law for p=17, or an already fixed normalized physical mu17 for p=19. All earlier actual exclusions, heights and kernels remain fixed.

For this very source there is a sequence of legitimate finite current-prime completions with positive assigned charge and complete current height H such that

    Xi_(p,H)^-/(a_p J_(p,H)) ->1,
    a_p J_(p,H)-Xi_(p,H)^- ->0,
    [a_p J_(p,H)-Xi_(p,H)^-]/b_H ->0.              (SPF1)

The source law mu, its complete original old-test domain, G_mu=sup_A E_mu A^2, and the distribution of every individually specified old test are exactly unchanged with H. Thus a positive uniform Xi rebate cannot be forced by imposing only conditions on this source or its old energy profile, whenever the proposed class contains such an actual source. This is conditional on the existence of a source satisfying the proposed restrictions; it does not assert that an arbitrary numerical high-energy class is nonempty.

#### An actual completion preserving the full old period

Choose eight distinct nonunit divisors d_1,...,d_8 of Q and a point x0 with mu(x0)>0. Include Q itself among the d_i if the earlier actual exclusions do not already have old least common multiple Q. This ensures that the new complete family's old part is exactly Q even when its original heights had been set by later-prime padding. No old label is lost through a smaller least common multiple.

Add the eight mixed classes of original moduli d_i p, with old residue x0 modulo d_i and current root i. For every H>=2 add the pure p-classes0 modulo p and, at exponent e=2,...,H, the least-significant-first prefix(9,1,...,1,0). Their residues are9+sum_(j=1..e-2)p^j. These pure cylinders are pairwise disjoint, avoid roots1,...,8, and leave the whole root p-1 clean. All original moduli are distinct and the full new period is Q p^H.

The actual pure-survivor Haar mass and old row count are

    lambda_H=(p-2+p^-H)/(p-1),
    k(x)=sum_(i=1..8)1_(x=x0 mod d_i).

The current mixed union consists of exactly k(x) distinct whole roots, so its conditional pure-base mass is alpha_H(x)=k(x)/(p lambda_H). Put

    delta=7/(p-2),
    g_H=1/(1-min(alpha_H,delta)),
    beta_H=(alpha_H-delta)_+/(1-delta),
    r_p=(p-1)/(p-2),
    J_(p,H)=sup_A E_mu[r_p g_H A^2].

These are the prescribed actual normalized physical and killed kernel quantities. For k<=7 one has alpha_H<delta, whereas k=8 implies alpha_H>delta. If

    C={x:x=x0 mod lcm(d_1,...,d_8)},

then the assigned bad mass is exactly

    b_H=mu(C)*[8/(p lambda_H)-delta]/(1-delta)
      ->mu(C)*(p-8)/[p(p-9)]>0.                   (SPF2)

The event C has positive mass since it contains x0. If Q was included among the d_i, then C is the single residue x0 modulo Q. The current step is normalized row by row; mu itself is the same incoming law for every H.

#### Global Xi equality needs no coherent old maximizer

There is one complete old block A_e for every current exponent e=0,...,H, and every divisor label of Q remains independently selected within every block. For arbitrary current residues, the killed intersection of a pair of labels of current exponents e,f has pure-base mass at most

    p^-max(e,f)/lambda_H

when max(e,f)>0. Expanding every original old-label pair and then applying weighted Cauchy-Schwarz gives

    positive pair-block(e,f)
       <=[p^-max(e,f)/lambda_H]E_mu[g_H A_e A_f]
       <=[p^-max(e,f)/lambda_H]sup_A E_mu[g_H A^2].

Set a_(p,H)=sum_(t=1..H)(2t+1)p^-t. Summing all ordered current-exponent pairs gives the corresponding upper bound a_(p,H) sup_A E_mu[g_H A^2]/lambda_H.

The old domain is finite, so let A_H be any actual complete old test attaining sup_A E_mu[g_H A^2]. It need not be nested, centered, radial, or equal to the forbidden layout. Select this very old test in every current block, and put every positive current test prefix at p-1 modulo p^e. All those prefixes are nested within the globally clean root. Each positive pair then attains its exact pure-base cap and survives killing; the weighted Cauchy-Schwarz inequalities are equalities because the old blocks coincide with A_H. Hence

    Xi_(p,H)^-=a_(p,H) sup_A E_mu[g_H A^2]/lambda_H,
    Xi_(p,H)^-/(a_p J_(p,H))
      =(a_(p,H)/a_p)*(p-2)/(p-2+p^-H),             (SPF3)

where a_p=(3p-1)/(p-1)^2. This is a global maximum over the full independent original test domain. Selecting repeated old blocks proves attainment, rather than restricting the optimization domain in advance.

#### Exact consequences for conditional energy strategies

The coefficient tail is

    a_p-a_(p,H)=p^-H[(2H+3)p-(2H+1)]/(p-1)^2.

The ratio in SPF3 therefore tends to1, independently of mu or the shape of its maximizing old tests. Moreover

    r_p G_mu<=J_(p,H)<=c_p G_mu,
    c_p=(p-1)/(p-9),

so J_(p,H) is bounded by one fixed finite constant. This proves the additive limit in SPF1. SPF2 proves its charge-normalized limit. The quantitative pure-height convergence is O(H p^-H), with a bound proportional to the fixed G_mu.

In particular, even allowing the proposed rebate constant to depend on this source, no strictly positive epsilon(mu), c(mu), or d(mu) can make respectively

    Xi_p^-<=(1-epsilon(mu))a_p J_p,
    Xi_p^-<=a_p J_p-c(mu),
    Xi_p^-<=a_p J_p-d(mu)b_p

hold for every legitimate current completion of this source. Restricting G_mu, a source-only hinge profile, or the high-load probability of an identified old test cannot change this counterexample construction: each of those observations is exactly preserved. If G_mu>64, the required eight nonunit old divisors follow automatically, since a period with at most eight divisors has A<=8 for every complete old test and hence G_mu<=64.

A condition on J_p itself is different, because the mask weights vary with H. Precisely,

    J_(p,H) -> J_infinity
      =r_p sup_A E_mu[g_infinity A^2],
    g_infinity(x)
      =1/(1-min(k(x)(p-1)/[p(p-2)],delta)),
    J_infinity>=r_p G_mu.

The convergence follows uniformly on the finite old carrier and test domain. A strict condition J_p>J0 is preserved eventually if J_infinity>J0; it is not claimed for every arbitrary high-J threshold. In particular G_mu>J0/r_p is a sufficient condition for this completion to remain above J0. Conditions involving the actual relation between a maximizing test and the weighted mask, or the joint old/new objective, contain information beyond the preserved source alone.

#### The19 input and the remaining common-test loss

For p=19, start with one already specified normalized physical mu17 from its actual AP13-to17 construction, including all original17 heights. The new d_i may contain17 factors; choosing Q among them preserves those exact heights in the full family. The19 source is then exactly that same mu17. No conditioning is inserted and no independently chosen17 family is substituted. This establishes a source-preserving19 statement without asserting that the17 and19 Xi maxima can be attained by one final common test.

Finally, the optimizing A_H can have substantial energy on the charged event C. The deleted old-square term E_mu[beta_H A_H^2] is retained in the full killed objective and need not tend to0. The CT terms, their shared-label correlations, and the gap between separately maximizing the stages are not bounded by SPF1. Thus the useful remaining conditional target is a bound on the full same-test killed or signed objective, rather than a positive standalone Xi rebate inferred only from high old-source energy. No general KC numerical bound or unrestricted Erdős #7 endpoint is claimed.

### A positive unit-load event can be completely deleted

Source density and positive low-load mass do not, by themselves, give a positive conditional survival fraction in CT5. Fix H>=16 and reuse the actual ternary family from CT6: the forbidden class at3^n is3^(n-1)-1, while the inherited test at3^n is2*3^(n-1)-1, for1<=n<=H. Include the unit test. There are no5,7,11 or13 exclusions, so the actual AP13 law nu is uniform on the complete old survivor set S_H. Its Haar mass is(1+3^-H)/2 and its density is strictly below2.

On that source the complete old test A takes values1 and2. Its unit-load event is precisely E={-1 mod3^H}, with

    nu(E)=2/(3^H+1)>0.                            (CB1)

Add pure0 modulo17 and, for n=1,...,16, the original mixed class of modulus3^n*17 with CRT residues

    x=-1 mod3^n,  y=n mod17.

All H+17 actual moduli are distinct. Their period is3^H*17, and every one of its2(H+1) complete test labels remains available. At H16 every nonunit divisor has its actual forbidden class. For larger H the additional mixed exclusions are absent, but their test labels are retained. An explicit full test extends the inherited A by choosing its old residues in each positive17 label and current root16.

On every old point of E, all16 mixed masks are active. They cover all16 nonzero roots of the actual pure17 base, giving alpha17=1. The prescribed threshold delta=7/15 therefore gives

    beta17=(alpha17-delta)_+/(1-delta)=1,
    K17^-1=0 on E,
    nu(1_E beta17)=nu(E),  eta(E)=0.               (CB2)

Here the19 factor is absent, so its step is identity. In particular no universal estimate nu(1_E beta17)<=theta*nu(E) with theta<1 follows even with the source density below2 and nu(E)>0. The family does not cover all integers: on the positive source cylinder1 mod3 none of these mixed masks is active, so every nonzero17 root survives there.

The example concerns E={A=1}. The wider band A<=2 is the entire source, and CB2 does not exclude a useful conditional estimate for such broader bands or a tradeoff with the same test's positive-current energy. It specifies the extra deletion information required by CT5, without replacing that obligation by a source-density bound.

### Conditional deletion controlled by the same315 head cells

There is a positive conditional estimate when the current mixed forbidden classes use only old cofactors dividing315. At p=17 or19 assume every actual mixed forbidden modulus is d*p^e, where d>1 divides315 and e>=1. All residues, finite current heights, missing classes and pure p-power exclusions remain arbitrary. At17 this hypothesis excludes old11/13 factors; at19 it also excludes17 factors. It is a restriction on forbidden classes, not on the complete test inventory, which retains all original divisor labels and their cross factors.

Let sigma be the normalized actual incoming probability on the old coordinates, padding unused315 digits uniformly if needed. For any old event E set

    w_E(u)=sigma(E intersect {x=u mod315}).

Then the AP/T8 assigned bad mass satisfies

    integral_E beta_p d sigma <=4/(p-9)*max_u w_E(u). (HBD1)

Indeed the actual pure-survivor Haar mass lambda is at least(p-2)/(p-1). At current depth e let B_e(u) count the active original nonunit315 cofactor cylinders. There are at most11, each with its own fixed residue. With t_e=(p-1)p^-e and all absent depths assigned B_e=0, the actual mixed union obeys

    alpha_p(u)<=(1/(p-2))*sum_e t_e B_e(u),
    beta_p(u)<=(1/(p-9))*sum_e t_e(B_e(u)-7)_+.

The second inequality uses delta=7/(p-2) and convexity of the positive part; sum_e t_e=1 includes the entire current tail. Complete each 1+B_e upward to a315 comparison load C_e. The existing endpoint identity(2), extended homogeneously to every nonnegative head measure w, gives

    sum_u w(u)(C_e(u)-8)_+<=4 max_u w(u).

Applying this to the one measure w_E proves HBD1. No source probability or test residue is reselected by depth. The comparison loads C_e bound the original masks; they do not identify the masks with the inherited test defining E. If the largest current height is H, the right side can additionally be multiplied by1-p^-H.

#### Joint deletion and the two largest event cells

Under this cofactor restriction beta17 and beta19 are functions of the same315 head alone. For the normalized physical mu17=nu13 K17, the old marginal remains nu13. Consequently the final killed measure satisfies the exact identity

    eta(E)=sum_u w_E(u)(1-beta17(u))(1-beta19(u)).

Let w1>=w2 be the two largest entries of w_E. The argument for HBD1 applied to counting measure, rather than the probability sigma, gives

    sum_u beta17(u)<=1/2,  sum_u beta19(u)<=2/5.

These bounds imply

    nu13(E)-eta(E)
      <=max{(7/10)w1,(1/2)w1+(2/5)w2}
      <=(9/10)w1.                                 (HBD2)

To check the first inequality, maximize sum_u w_E(u)(b_u+c_u-b_uc_u) on the two nonnegative simplices sum b<=1/2 and sum c<=2/5. The objective is affine in either variable with the other fixed, so a maximizing pair of simplex vertices exists. Vertices on the same cell give at most(7/10)w1; vertices on different cells give at most(1/2)w1+(2/5)w2. Zero vertices give no larger value. This upper optimization does not assert that all its vertices are actual masks. It retains the two deletion events on one actual head and accounts for their overlap.

Now assume the actual357 period divides315. Its full original survivor set S in this head has N>=74 points by the existing315 counting result. Start with the uniform law on S, apply the actual physical11/T4 and13/T6 kernels, and condition once, with retained mass rho>=r=18925009844347/38266567762500. Each physical kernel preserves the incoming head marginal; restriction and division by rho therefore give

    max_u w_E(u)<=1/(N rho)<=1/(74r).               (HBD3)

This uses the full actual source, not a replacement by the canonically pruned law or another supported probability. Source11/13 masks may have arbitrary permitted old cofactors, residues and finite heights.

For every inherited complete test A, the same-law mean bound M=2621130891614589/246025127976511 and integer A>=1 imply nu13(A<=10)>=(11-M)/10. Write m=nu13(E) and c0=1/(74r). Since w1<=c0 and w1+w2<=m, HBD2 gives

    eta(E)>=min{m-(7/10)c0,(3/5)m-(1/10)c0}.

Both expressions increase with m. At m=(11-M)/10 the first is smaller, so

    eta(A<=10)>=704627631753217/45514648675654535>0,
    Delta_121(L)>=21 eta(A<=10)
      >=14797180266817557/45514648675654535
       =0.3251080849215137... .                    (HBD4)

The bound holds for the inherited block of every complete final test in this restricted actual family, with no assumption of positive final mass. For the ASB candidate marginal with nu13(A=1)=7/100, the same conditional calculation gives Delta_121>=120*(7/100-9/(740r))>5.4489577146. If its positive terms also obey the stated ASB upper functional, this exceeds that functional's defect3.96663236768. It does not exclude the source marginal by itself or assert an unrestricted improvement of the299.398 target.

An exact actual-family check uses the existing86-survivor315 family, eleven mixed11 classes, seven mixed13 classes involving11, and three current heights at both17 and19. Its103 distinct forbidden moduli have period1517938437015 and768 complete test labels. Direct physical AP(4,6) integration gives rho=819/860. Exact prefix unions, independently counted as finite bitsets, give positive charges at both current primes; the same inherited tests satisfy HBD1--HBD4 on all checked bands. The universal statement rests on the proof above, not this single instance.

The existing DV1 construction supplies a different supported law with a stronger315-source square bound. It cannot replace the particular actual AP(4,6) probability used here. The useful addition is the event-conditioned head observation and its CT consumer, not a new noncoverage endpoint for this subfamily. Extending HBD1 to arbitrary old cofactors requires another estimate: the excluded old exponents and11/13/17 factors cannot be omitted as an unpaid tail.

### Highest-digit CRT contrasts give signed common-test cuts

Fix the actual source nu on Z/QZ, Q>1, and project the complete killed17/19 output eta to this old coordinate. Define the actual deleted and surviving point masses

    u(x)=nu(x)[beta17+K17^- beta19](x),
    v(x)=eta({x}),  u(x)+v(x)=nu(x).

For a complete inherited test A and integer s>=2, the first two CT3 losses are

    D_s(A)=sum_x u(x)(A(x)^2-s^2)_+,
    N_s(A)=sum_x v(x)(s^2-A(x)^2)_+.

These retain the same original source and the same test. Original modulus uniqueness supplies an additional discrete constraint on their sum.

Write Q=product_i p_i^h_i with r>=1 distinct primes, and let a be the residue selected by the original full-modulus test label Q. In each coordinate choose one alternative to a_i that agrees modulo p_i^(h_i-1) but differs modulo p_i^h_i. The2^r CRT corners x_epsilon independently choose the original or alternative coordinate. Then

    sum_epsilon (-1)^|epsilon| A(x_epsilon)=1.      (CCD1)

Every proper-divisor indicator is constant in at least one cube direction, so cancels from the alternating sum, irrespective of its independently chosen residue. The unique Q indicator contributes1 at the all-original corner and0 elsewhere. This proves CCD1 without aligning any proper-divisor labels.

Let C+ and C- be the even and odd corners. They have equal cardinality. CCD1 forces at least one even corner with A>=s+1 or one odd corner with A<=s-1: otherwise the alternating sum is at most0. Hence

    D_s(A)+N_s(A)
      >=min({(2s+1)u(x):x in C+}
               union {(2s-1)v(x):x in C-}).         (CCD2)

Strict positivity requires deleted mass at every even corner and surviving mass at every odd corner. Positive total charge alone does not suffice. For s=9 the coefficients are19 and17.

Several cubes for the same assigned Q residue can be combined. Choose nonnegative rational lambda_C satisfying the separate point capacities

    sum_(C:x in C+)lambda_C<=(2s+1)u(x),
    sum_(C:x in C-)lambda_C<=(2s-1)v(x).

Each cube has a qualifying high or low corner. Weight these clauses and use the capacities to obtain

    sum_C lambda_C<=D_s(A)+N_s(A)<=Delta_(s^2)(L).   (CCD3)

Thus overlapping cubes have a finite fractional-packing certificate that does not charge any point beyond its own actual mass. Once the literal Q label is assigned, the certificate holds uniformly over every remaining independent original test label. A global optimization must cover every Q residue or justify its branch exclusions using the full objective; Xi-only optimality conditions do not authorize exclusions here.

For an actual nonempty branch, take Q=3^9 and forbid0 modulo3^j for1<=j<=9. The old source is uniform on its13122 units. At17 add pure0 and eight classes3^j*17 with old residue1 and current root j,1<=j<=8. Other source-prime steps and19 have height0. The full family has18 distinct forbidden moduli and20 complete test labels. On E8={x=1 mod3^8}, alpha17=1/2 and beta17=1/16; outside E8 the assigned charge vanishes.

Assign the original Q test residue a=1. Its two highest-digit corners1 and6562 lie in E8 and have

    u(1)=1/209952,  v(6562)=15/209952.

The one-cube certificate at s=9 gives Delta81(L)>=19/209952 for every complete test in this branch. Centering every old label at1 gives A(1)=10,A(6562)=9 and attains this restricted two-corner cost; it need not minimize the full CT loss. This is a usable branch constraint, not a uniform bound across all source geometries or full-modulus residues. Cube weights can vanish in other branches and become arbitrarily small with growing periods.

The endpoint identity(2), existing AP comparison, and CT decomposition are reused directly in these conditional arguments. The CRT cut follows from cancellation of the original proper-divisor indicators and finite point capacities. These are ordinary proofs with exact arithmetic checks; they add no Lean declaration, frozen status or unrestricted Erdős #7 conclusion.

### Eliminating current heights with a common old-test distance profile

Fix a finite actual old carrier, a finite nonnegative measure sigma and its complete old-test domain D. Each original divisor remains an independently chosen label. Let R_x be the actual killed current-prime kernel, q(x)=R_x(1), and choose a full-Haar density cap c(x): every depth-e current prefix has mass at most c(x)p^-e. Assume0<=q<=c and finite integrals. The literal actual cap g/lambda and the larger generic AP cap are both allowed. The following upper bound uses these quantities on their one actual source; it requires no normalization of sigma.

Define

    <A,B>_c=integral c A B d sigma,
    ||A||_c^2=<A,A>_c,
    Gamma=max_(A in D)||A||_c^2,
    d(A)=Gamma-||A||_c^2,
    M={A in D:d(A)=0}.

The domain D and M are finite and nonempty. For a fixed literal zero-current block A0, keep the joint profile

    psi_t(A0)=min_(A in D){t d(A)+||A-A0||_c^2},
    t>0.                                          (OBE1)

This minimum couples norm deficit and distance to the same old test. It cannot in general be recovered from marginal moments or independently maximized Gram entries.

#### Finite original heights and the retained deficits

For original current height H, put s_e=p^-e and

    S_H=sum_(e=1..H)s_e,
    a_H=sum_(e=1..H)(2e+1)s_e,
    t_(e,H)=e+1+sum_(f=e+1..H)s_f/s_e,
    B_H(A0)=integral q A0^2 d sigma+S_H||A0||_c^2,
    Psi_H(A0)=sum_(e=1..H)s_e psi_(t_(e,H))(A0).

For independent old blocks A0,...,AH, the current-prefix pair caps give

    integral L^2 d(sigma R)<=Phi_H,
    Phi_H=integral q A0^2 d sigma
       +sum_((e,f)!=(0,0),0<=e,f<=H)
                             s_max(e,f)<Ae,Af>_c.

The following is an exact identity for this cap functional:

    Phi_H=B_H(A0)+(a_H-S_H)Gamma-Psi_H(A0)
      -sum_(e=1..H)s_e[
          t_(e,H)d(Ae)+||Ae-A0||_c^2
                           -psi_(t_(e,H))(A0)]
      -sum_(1<=e<f<=H)s_f||Ae-Af||_c^2.             (OBE2)

To prove it, expand each pair by2<A,B>_c=||A||_c^2+||B||_c^2-||A-B||_c^2. The coefficient of||Ae||_c^2 is(e+1)s_e+sum_(f>e)s_f=s_e t_(e,H), and these coefficients sum to a_H-S_H. Substitute||Ae||_c^2=Gamma-d(Ae), then add and subtract the minimum OBE1. Every displayed bracket and distance is nonnegative. Thus

    sup_L integral L^2 d(sigma R)
      <=(a_H-S_H)Gamma
         +max_(A0 in D){B_H(A0)-Psi_H(A0)}.         (OBE3)

No equality between positive blocks is imposed. If one common current root and all its relevant prefixes avoid every pure and mixed exclusion, c=g/lambda is simultaneously attained by assigning all positive labels to that root. At H1, OBE3 is then exact: there are no positive-to-positive distances and the sole positive block can attain OBE1. At higher H, OBE3 remains an upper bound; it discards those distances and possible incompatibility of the separate minima.

#### Complete tails and finite affine intervals

Set S=1/(p-1), a=(3p-1)/(p-1)^2 and

    B(A0)=integral q A0^2 d sigma+S||A0||_c^2,
    Psi(A0)=sum_(e>=1)p^-e psi_(e+1+S)(A0).

For every finite original current height with these same q,c and D,

    sup_L integral L^2 d(sigma R)
      <=(a-S)Gamma+max_(A0 in D){B(A0)-Psi(A0)}.    (OBE4)

Indeed extend the finite block tuple by arbitrary complete old tests in the cap functional. All added pair terms are nonnegative, and the full series converges absolutely since every inner product is at most Gamma and the coefficient sum is a. Apply the expansion used for OBE2 to this series. The resulting norm coefficient is p^-e(e+1+S). This adds comparison terms, not original forbidden classes, and does not identify the finite coefficients with the infinite ones.

The complete tail of Psi has a finite description. Let

    D_*(A0)=min_(A in M)||A-A0||_c^2,
    T_*(A0)=max_(A not in M)
       (D_*(A0)-||A-A0||_c^2)_+/d(A),

with maximum0 when there are no nonmaximal tests. Then

    psi_t(A0)=D_*(A0) for every t>=T_*(A0).         (OBE5)

Every nonmaximal test contributes at least D_* after this threshold, while a nearest member of M attains D_*. Zero seminorm differences cause no difficulty: tests equal c-sigma almost everywhere have the same norm, and q<=c makes their baseline terms agree too. Original labels are not removed from the admissible domain.

Before the threshold, psi_t is the lower envelope of the finitely many affine functions t d(A)+||A-A0||_c^2. Its breakpoints partition the integer depths e into at most|D| active intervals. On each interval the sum defining Psi is a combination of sum p^-e and sum e p^-e; the last interval is exactly geometric by OBE5. With rational actual data, crossings, integer interval endpoints and sums admit exact rational computation. No iteration through every depth up to T_* is necessary.

The old domain can still be very large, and its nonzero norm gaps can be arbitrarily small. This finite interface supplies no uniform complexity bound on the original family search. It eliminates the independent current-height layout choices from this particular valid upper estimate, using the actual old norm/Gram profile and q-weighted baseline.

#### When the complete bound improves strictly

Relative to U0=max_D B+(a-S)Gamma, the gain in OBE4 is

    delta_profile=min_(A0 in D){max_D B-B(A0)+Psi(A0)}.

For t>0, psi_t(A0)=0 exactly when A0 itself maximizes the c-weighted norm, allowing the same null-space identification. Finiteness therefore gives

    delta_profile>0 iff argmax_D B and M are disjoint. (OBE6)

This is a condition on two observations under the same actual source and kernel. Its numerical size must be supplied by that source's profile.

The strict case occurs in an actual family at every finite current height. Use uniform units modulo3^8 as source, forbid0 modulo3, and take prime p>=17, threshold8, pure0 modulo p, and the eight classes3^j p with old residue1 and current root j. Include the redundant pure classes0 modulo p^e to retain any desired higher current height. The original3^8 height is retained by its mixed class; every original test remains present. All5/7/11/13 factors are absent, so their source steps are identities.

Write R for the nested old depth count, P8=1/4374, and u_j=g_j/(p-1). The same actual row calculation as RS gives

    q_j=1 (j<=7),  q8=(p-2)/(p-1),
    u7=1/(p-8),  u8=(p-2)/[(p-1)(p-9)],
    c_j=p u_j.

The strictly increasing c_j make the spine prefix the unique maximal c-weighted cylinder at every old depth. Expanding the complete square gives the unique norm-maximizing load A_*=1+R. For the full-height baseline weight w_j=q_j+[p/(p-1)]u_j, move just the last old cylinder to another child of the depth7 spine. The resulting complete spur test A' satisfies

    B(A')-B(A_*)=17 P8(w7-w8)>0,
    w7-w8=[1-p(u8-u7)]/(p-1),
    u8-u7=7/[(p-1)(p-9)(p-8)].                    (OBE7)

Positivity follows from(p-1)(p-9)(p-8)>7p for p>=17. Thus the norm maximum does not maximize B, proving OBE6 is nonvacuous for actual kernels, without assuming repeated positive blocks. This example establishes a strict comparison gain; it is not a new numerical bound for arbitrary AP13 families.

For the final KC objective one can apply OBE3 or OBE4 directly at19 with sigma=nu13 K17^- and R=K19^-; the output is exactly eta and the old domain contains every original17 label. Subtract the test-independent484 integral q d sigma from the bound. This is the actual killed input, with its mass retained; no normalized physical or separately conditioned source is substituted. Uniform numerical control of its norm/Gram profile over the full original family remains open. The identities, envelope computation and strict-gain argument here are ordinary mathematics, not Lean verification.

### Incompatible actual current prefixes give a uniform test correction

Let R be one actual unnormalized killed row on Z/p^H Z, let q=R1, and let M_e be its largest depth-e prefix mass. All original current heights and prefixes remain literal. Define

    Omega_H(R)=min_(v_e at depth e,1<=e<=H) [
      sum_e(2e+1)(M_e-R(v_e))
        +2 sum_(e<f)R(v_f)1_(v_f not subset v_e)].  (CPI1)

The minimum is over independent prefixes, including nonnested choices. Omega is nonnegative and equals0 precisely when one nested chain attains all the M_e. For a nonempty row every M_e is positive, so zero cost forces maximality and pairwise compatibility. For an empty row every term is0 and any chain works. Set Omega_0=0.

At a fixed old history, let a0,...,aH be the literal complete-test block amplitudes, and put m=min_e a_e. Each a_e>=1 because its old-cofactor-one label is retained. With

    c_e(a)=2a0*a_e+a_e^2+2a_e sum_(1<=d<e)a_d,
    U_M(a)=q a0^2+sum_e c_e(a)M_e,

the actual square obeys

    integral L^2 dR<=U_M(a)-m^2 Omega_H(R)
                  <=U_M(a)-Omega_H(R).             (CPI2)

To prove this, fix all depths except e. The square integral is convex in the nonnegative vector assigning its a_e active labels to depth-e prefixes. A simplex vertex concentrates all of them on one prefix and does not decrease the maximum. Repeat for each depth. This is an upper relaxation within the row; globally consistent choices across different old histories are not assumed.

For concentrated prefixes, direct expansion gives the exact deficit

    U_M(a)-integral(a0+sum_e a_e 1_(v_e))^2 dR
      =sum_e c_e(a)(M_e-R(v_e))
        +2 sum_(e<f)a_e a_f R(v_f)
                                    1_(v_f not subset v_e).

Here c_e(a)>=(2e+1)m^2 and a_e a_f>=m^2, proving CPI2. The list of separate maxima alone does not give the incompatibility terms.

A smaller certificate uses any1<=r<s<t<=H:

    Omega_H(R)>=min_(u at depth r,v at depth s) [
      (2r+1)(M_r-R(u))+(2s+1)(M_s-R(v))
       +1_(v not subset u)(2R(v)+2M_t)].            (CPI3)

If u,v are disjoint, a depth-t prefix z can lie below at most one. Its two incompatibility terms cost at least2R(z), and its own mass deficit adds(2t+1)(M_t-R(z)). Their sum is at least2M_t. If u,v are compatible, simply discard the nonnegative depth-t terms. Retain the r,s terms and minimize to obtain CPI3.

#### Integration together with the old-block profile

For a fixed actual old measure sigma and its actual rows R_x, write omega_H=integral Omega_H(R_x)d sigma. This quantity is independent of the original complete test. It can be subtracted from the supremum of the same C1 envelope U_M, and hence from C5 with these actual prefix masses:

    sup_L integral L^2 d(sigma R)
      <=Gamma(q sigma)+sum_e(2e+1)Gamma(M_e sigma)
                                                    -omega_H.

It also combines with OBE without counting a loss twice. If M_e<=c p^-e, the explicit chain is

    integral L^2 d(sigma R)
       <=integral U_M(A)d sigma-omega_H
       <=Phi_H(A)-omega_H
       <=U_OBE-omega_H.                            (CPI4)

The first loss concerns current-prefix geometry; OBE2 is an exact identity inside the subsequent cap functional. U_OBE can be either OBE3 or the complete-tail OBE4. In the latter case only the comparison cap is extended; the actual row, height and Omega_H are not padded. At19 take sigma=nu13 K17^- and R=K19^-, then subtract484 integral q d sigma to bound the original signed objective. A CPI3 certificate may replace Omega in the same chain.

CPI4 does not authorize appending a subtraction to CT3 while leaving its exact transported increments unchanged. Nor can the loss of one chosen family be subtracted from a supremum over all families. The corrected envelope and its actual source/mask data must remain together. Clean nested rows from SPF have Omega=0.

#### A literal arithmetic witness and an equal-readout comparison

Take Q=3^4*5^2*7*11*13=2027025 and forbid0 modulo every nonunit divisor of Q. There are120 old test labels and777600 old units. The prescribed actual source construction gives the uniform unit law; all mixed11/13 exclusions are inactive. At17 retain current height3 by the pure classes0 modulo17,17^2,17^3, the latter two redundant. Add the following current residues, assigning them at each depth to distinct nonunit d|Q with old residue1 modulo d:

| depth | current residues | count |
|---|---|---:|
| 1 | 3,...,16 | 14 |
| 2 | 1+17j for6<=j<=16; 2+17j for1<=j<=16 | 27 |
| 3 | 1+17j+289k for0<=j<=5,1<=k<=16; 2+289k for3<=k<=16 | 110 |

There are119 available nonunit cofactors, so each assignment is possible. Reusing a cofactor at different depths retains distinct original moduli. The actual CRT residue for current y and cofactor d is1+d((y-1)d^-1 mod17^e), modulo d17^e. In total the family has273 distinct forbidden moduli and480 complete test labels.

At old point x0=1 the surviving current leaves are

    S={1,2,18,35,52,69,86,291,580}.

There are4624 pure-surviving leaves before mixed deletion. The AP/T8 killed mass of each retained leaf is w=15/36992, and

    (q,M1,M2,M3)=(9,6,3,1)w,
    Omega_3(R_x0)=8w.                              (CPI5)

Root1 has six leaves in six distinct depth2 children; root2 has three leaves in one child. For compatible depth1/depth2 choices, their prefix deficits alone are at least9w. For incompatible choices, their deficits plus pair loss are at least6w, and depth3 contributes at least2w by CPI3. Choosing root1, the depth2 prefix2 and any retained leaf attains total loss8w. Equivalently the unit-amplitude envelope is49w and the actual maximum is41w. All126 nonempty-prefix triples reproduce this maximum, with nine maximizing triples. Zero-mass choices cannot improve the maximum of the nonnegative square.

Consequently omega_3>=8w/777600=1/239708160 for this entire family, uniformly over every complete test. Adding pure0 modulo19 and no mixed19 exclusions gives an actual two-stage continuation. Polarization of its two19 blocks gives weights19/18 and1/9, so applying the same bound to each yields a correction7/1438248960 to the corresponding composed envelope. The full signed mass term remains unchanged.

The alternative retained set

    S'={1,290,579,18,35,52,2,19,36}

has exactly the same(q,M1,M2,M3) but Omega_3=0: root1, its child1 and leaf1 simultaneously attain all three maxima. It has the same two occupied roots, seven occupied depth2 children and nine leaves. Delete the other14 roots,27 children and110 leaves using distinct old cofactors at each depth as above. This realizes S' in another actual family with the same source and original label inventory. At x0 its pure mass, assigned charge and all separate prefix maxima agree with those for S. Its unit-amplitude maximum is49w instead of41w. Unit amplitudes are legitimate at this row: center every nonunit old test at2 so only the old unit term is active at x0=1.

Thus the new observation is the ancestry relation between actual maximizing prefixes, which is not determined by their separate masses. This is a row-level distinction, not a claim that the two entire families have identical laws on every old row. The ordinary proof and exact CRT/prefix counts verify the mechanism without a uniform positive Omega bound over unrestricted families or a Lean endpoint.

### A uniform four-block loss in one actual charged17-to19 family

Take the actual uniform144-unit source nu modulo315, from exclusions0 modulo3,5,7. Its ternary height2 is retained by the later original moduli. At each p=17,19 add pure0 and eight mixed classes with old residue1 modulo

    (d_i)=(3,9,15,21,45,63,105,315)

and current root i,1<=i<=8. This is one family of21 distinct odd forbidden moduli, period101745, and48 complete test labels. There are no11/13 exclusions. In particular the19 masks have no17 factor.

Write I_d=1_(x=1 mod d). The number of bad roots is

    k=I3(1+I9)(1+I5)(1+I7) in{0,1,2,4,8}.

For each p put alpha_p=k/(p-1), delta_p=7/(p-2), beta_p=(alpha_p-delta_p)_+/(1-delta_p), g_p=1/(1-min(alpha_p,delta_p)), t_p=g_p/(p-1) and q_p=1-beta_p. Only x=1 has k8, giving beta17=1/16 and beta19=1/18 there. Thus the actual charges are b17=1/2304 and b19=1/2592. The second charge is under the normalized physical17 input, whose old marginal is nu.

The final killed row is the product of the two actual killed rows, because the19 masks depend only on x. Define q=q17*q19, u=t17*q19, v=t19*q17, w=t17*t19. Their exact values are

| k | q | u | v | w |
|---|---|---|---|---|
| 0 | 1 | 1/16 | 1/18 | 1/288 |
| 1 | 1 | 1/15 | 1/17 | 1/255 |
| 2 | 1 | 1/14 | 1/16 | 1/224 |
| 4 | 1 | 1/12 | 1/14 | 1/168 |
| 8 | 85/96 | 85/768 | 17/192 | 17/1536 |

Separate a complete test into independent old blocks A,B,C,D for current exponent pairs(0,0),(1,0),(0,1),(1,1). Pairwise current-cylinder bounds give

    integral L^2 d eta<=E_nu F(A,B,C,D),
    F=q A^2+u(2AB+B^2)+v(2AC+C^2)
                      +w(2AD+2BC+2BD+2CD+D^2).    (BQC1)

For each fixed four old layouts this bound is attained by setting their positive current roots to16 and18, respectively. These roots are globally clean. Thus the current-residue optimization is exact, and all four old layouts remain independently variable.

#### Centered-cylinder coefficients retain the actual atom energy

Let Gamma(f)=max_A E_nu[f A^2], and C=sum_(d|315) I_d. Every intersection of a centered I_e and two arbitrary original test cylinders is empty or a residue class modulo their LCM. Under the uniform unit law its mass is at most that of the class centered at1. Expanding the square therefore gives

    E_nu[I_e A^2]<=E_nu[I_e C^2] for every e|315.

For f=u,v,w the table gives the expansion

    f=f0+(f1-f0)I3
       +(f2-f1)(I9+I15+I21)
       +(f4-2f2+f1)(I45+I63+I105)+c_f I315,
    c_f=f8-3f4+3f2-f1,
    (c_u,c_v,c_w)=(223/26880,67/22848,817/304640).  (BQC2)

All coefficients are nonnegative. Hence C simultaneously maximizes u,v,w and all their nonnegative linear combinations. Its value at the actual atom x=1 is12.

The baseline is q=1-epsilon I315 with epsilon=11/96. If G=E_nu C^2, the complete test centered at2 has unweighted square G and value1 at x=1. All tests have A(1)>=1 and unweighted square at most G, so

    Gamma(q)=G-epsilon/144,
    Gamma(q)-E_nu[q A^2]
                          >=epsilon(A(1)^2-1)/144. (BQC3)

#### One positive rational matrix controls all four old layouts

Set A0=A,A1=B,A2=C,A3=D and use the symmetric table

    H=[[0,u,v,w],[u,u,w,w],[v,w,v,w],[w,w,w,w]].

Its row sums R_i are u+v+w,2u+2w,2v+2w,4w. Define

    S=Gamma(q)+sum_i Gamma(R_i)
     =Gamma(q)+3Gamma(u)+3Gamma(v)+9Gamma(w).

Polarization is an exact identity on these same four tests:

    S-E_nu F=Gamma(q)-E_nu[q A0^2]
       +sum_i[Gamma(R_i)-E_nu[R_i Ai^2]]
       +sum_(i<j)E_nu[H_ij(Ai-Aj)^2].              (BQC4)

The atom coefficients of R_i in BQC2 are

    lambda=(12713/913920,10033/456960,733/65280,817/76160).

Every other centered-cylinder deficit is nonnegative, so with a_i=Ai(1),

    Gamma(R_i)-E_nu[R_i Ai^2]>=lambda_i(144-a_i^2)/144.

Retain the same actual atom in the nonnegative squared differences of BQC4 and apply BQC3. This yields

    144(S-E_nu F)>=144 sum_i lambda_i-epsilon+a^T M a,

    M=[[8881/28560, -85/768, -17/192, -17/1536],
       [-85/768, 50657/456960, -17/1536, -17/1536],
       [-17/192, -17/1536, 541/5440, -17/1536],
       [-17/1536, -17/1536, -17/1536, 6847/304640]].

There is an exact rational positivity certificate:

    r=(1,4/3,5/4,9/5),
    Mr=(17981/548352,7403/2193408,427/391680,
                                           43703/54835200)>0.

For e_ij=-M_ij>=0 and every real a, direct expansion gives

    a^T M a=sum_(i<j)e_ij r_i r_j(a_i/r_i-a_j/r_j)^2
                 +sum_i ((Mr)_i/r_i)a_i^2.

Every original old block contains its unit indicator, so a_i>=1. Substitution gives the uniform full-test loss

    Gamma(q)+3Gamma(u)+3Gamma(v)+9Gamma(w)
       -max_L integral L^2 d eta
       >=16283037949/284265676800
        =0.05728105528707995...>0.057281.           (BQC5)

All maxima retain the48 original test labels. There is no assumption that A,B,C,D coincide or that their extrema have a prescribed form. The factors q19 in u, q17 in v and both in q preserve the actual two-stage killing. Subtracting484 eta1 on both sides gives the same loss for the signed objective, but this benchmark is not the separate KC sum of the17 and19 frontiers.

The literal21-class construction,144 source rows, both physical/killed kernels, every cylinder coefficient and the matrix certificate have been recomputed with exact rational arithmetic. The arbitrary-layout conclusion follows from BQC1--BQC4 and the displayed matrix identity. This proves a same-family strict loss with positive charge at both stages; it does not supply a uniform0.057281 subtraction over other original families, the299.398 target, later-prime continuation or Lean verification.

### Prefix-tree optimization and branch-price certificates

This is ordinary mathematics with exact rational computation, not Lean
verification. All masses belong to one actual unnormalized killed row. No
probability replacement, original-modulus deletion, or repeated-block hypothesis
is used. The method evaluates CPI's row relaxation; it does not make the original
complete test independently selectable at different old histories.

#### 1. Tree score

Let R be a finite nonnegative measure on Z/p^H Z. Its prefix tree has one
node v=(e,a) for each current residue a modulo p^e, with mass m(v)=R(v).
Let M_e=max_(depth v=e)m(v), q=R1, and

    C_H = sum_(e=1)^H (2e+1) M_e.

Select one node v_e at each depth. Let anc_S(v) be the number of selected
strict ancestors of a selected node v. Laminarity of residue cylinders gives

    J(S) = integral[(sum_(v in S)1_v)^2 + 2 sum_(v in S)1_v] dR
         = sum_(v in S) [3+2 anc_S(v)] m(v),

because distinct incomparable nodes are disjoint and the intersection of an
ancestor with v has mass m(v). Rewriting CPI1 gives exactly

    Omega_H(R) = C_H - max_(one node per depth) J(S).                 (PT1)

Thus the quantity to optimize is a positive tree score. Nodes of zero mass can
be omitted for this maximum when q>0. Any selected zero-mass node has no
positive-mass descendant; replacing it by any positive-mass node at the same
depth cannot decrease the original pointwise nonnegative square. Repeating
leaves a tuple of positive nodes. For q=0, Omega_H=0 separately.

If s full-height leaves carry positive mass, the positive tree has at most
1+Hs nodes. Constructing all its masses costs O(Hs) additions, when the leaf list
is already available. This does not give a bound on the size or discovery cost
of that actual row representation.

#### 2. Exact subset-of-depths dynamic program

For a node v of depth d, an integer a in [0,d-1], and a subset D of
{d,...,H}, let F_v(a,D) maximize the score of choosing exactly one node at each
depth in D, all inside v's subtree, with a already selected strict ancestors.
These are the only external effects on the subtree score.

Put epsilon=1_(d in D), D'=D\{d}, a'=a+epsilon. Then

    F_v(a,D) = epsilon(3+2a)m(v)
        + max_(disjoint union_c D_c = D') sum_c F_c(a',D_c).        (PT2)

Here c runs over the positive children of v. An empty subtree allocation gives
zero. An allocation requesting a depth unavailable below a leaf is infeasible.
At the virtual depth-zero root, epsilon=0 and a=0; D={1,...,H} gives max J.

Proof: v is the only depth-d node of its subtree, so its inclusion is forced by
D. Every other chosen node lies in exactly one child subtree; its depth is
allocated to that child, with no duplicated depth. Selections from different
children have zero interaction. Selected ancestors contribute only through a'.
This proves both inequalities in PT2 and gives reconstruction of a maximizing
tuple. It does not impose that all selected nodes form a chain.

Combine children by max-plus subset convolution. For a fixed state a, the total
number of disjoint-pair trials on a future-depth set of size k is 3^k. A simple
uniform upper bound is O(H N 3^H) arithmetic operations and O(H N 2^H) stored
score entries for a tree of N positive nodes; the depth-dependent bound can be much
smaller. This is exponential in H, but has no product of level widths. Literal
tuple enumeration has product_e n_e candidates, where n_e is the positive
width at depth e. The implementation caches one whole table per (node, ancestor
count), sharing each convolution across all requested masks. It does not rerun
the convolution separately for each final mask. The subset program is not
claimed faster on every small row; its advantage is dependence on H versus the
product of widths. The reference implementation retains witness tuples of length
at most H beside each score entry; tuple-copy operations and witness storage
therefore carry an additional factor at most H. Arithmetic bit complexity and
actual old-state enumeration are additional costs.

#### 3. Depth prices give small checkable lower certificates

Fix real prices lambda_1,...,lambda_H. Drop the one-node-per-depth restriction
inside an auxiliary maximization, allowing any subset S of positive nodes. Put

    B_v(a) = max over selections in v's subtree
               [subtree score with a selected ancestors - sum selected prices].

It obeys the binary tree recurrence

    B_v(a) = max {
        sum_c B_c(a),
        (3+2a)m(v) - lambda_d + sum_c B_c(a+1)
      }.                                                         (PT3)

At the virtual root use B_root(0)=sum_(depth1 v)B_v(0). Every feasible PT1 tuple
has total price sum_e lambda_e, so

    max J <= sum_e lambda_e + B_root(0),
    Omega_H >= C_H - sum_e lambda_e - B_root(0).                   (PT4)

The maximum of the latter expression with zero is also a valid lower bound.
Prices of either sign are valid. Computing PT3 uses O(HN) arithmetic operations
and O(HN) states, since at depth d only a=0,...,d-1 can arise. Root and edge
traversals are included in this bound. A rational upper table need only satisfy
both inequalities corresponding to PT3; exact equality is unnecessary. Such a
table is a short certificate checked with additions, comparisons, and the actual
prefix masses. Floating-point optimization may propose prices but cannot certify
the bound without this exact evaluation.

PT4 is a Lagrangian upper relaxation of max J, not an assertion of strong
duality for the integral one-node-per-depth problem.

#### 4. Branching enforces a few actual depth constraints

Choose some depths to fix. A branch specifies one positive node at every fixed
depth, with no nesting restriction between the specified nodes. In PT3, force
the inclusion action for that node and force the exclusion action for all its
peers. Set its depth price to zero and price only the remaining free depths.
The resulting recurrence exactly maximizes the priced unrestricted score within
that branch. For any such branch b and any branch-specific price vector,

    J_b <= sum_(free e) lambda_(b,e) + B_(b,root)(0) = U_b.

All positive-node tuples are covered by the branches. These suffice for the
original maximum by PT1's zero-node replacement argument, hence

    max J <= max_b U_b,
    Omega_H >= C_H - max_b U_b.                                  (PT5)

Each branch takes O(HN) arithmetic. Exhausting r fixed depths costs at most the
product of their positive widths times that per-branch work. Branch selection
and price discovery are separate from certificate validity. Fixing more depths
can only improve the best possible upper certificate, because existing prices
restrict to the finer branch; it does not guarantee a particular chosen price
vector improves. Fixing every depth reduces to the literal exact problem.

#### 5. Exact tests on the actual S / S' fixtures

Use unit leaf masses first, multiplying the conclusions by the actual common
weight w=15/36992 afterwards. For

    S = {1,2,18,35,52,69,86,291,580}

the positive widths are (2,7,9), masses (M1,M2,M3)=(6,3,1), and C3=40.
The subset program gives max J=32, so Omega3=8, reproducing the independent
literal-square maximum 41 after adding q=9. There are 126 complete positive
tuples. For S' from CPI5, the program gives max J=40 and Omega3=0.

The unbranched price vector (18,6,6) gives B_root(0)=3 and upper score 33,
therefore Omega3>=7. This is the best possible scalar-depth-price certificate,
not a failure to search prices long enough. Consider three unrestricted subsets:

    A = {root1, root2, child2, leaf2, leaf291, leaf580},
    B = {child2},
    C = {root1, child2}.

Their depth-count vectors and scores are

    A: (2,1,3), score63;
    B: (0,1,0), score9;
    C: (1,1,0), score27.

The equally weighted mixture has mean count (1,1,1) and mean score33. For every
price vector lambda, the unrestricted maximum priced score is at least its
average over this mixture, namely 33-sum lambda. Thus no scalar-price bound is
below33. It leaves an exact integrality gap of1 in this fixture.

Two root branches remove that gap with explicit integer prices:

    selected root1: lambda2=9,  lambda3=5; upper J=32;
    selected root2: lambda2=15, lambda3=7; upper J=31.

Both bounds follow directly from PT3 with lambda1=0 and the depth-one actions
fixed. Hence max J<=32 and Omega3>=8. A feasible original tuple attains J=32,
so this lower certificate is exact. This uses two tree recurrences, not an
assumption that the maximizing prefixes form a chain. In particular the winning
root1 branch uses the incompatible depth-two child2.

The actual arithmetic realization, original 480 test labels, actual row factor
w, and full old measure remain those of CPI5. Integrating a row certificate uses
its actual weight and does not give a positive uniform correction for families
whose rows have a common nested sequence of maxima.

#### Exact verification

verify_prefix_correction.py uses exact integers/Fractions and does not rely on Python assertions.
It checks both fixtures against direct literal leaf squares; compares PT2 with
all 256 binary depth-three support sets; compares another 80 rational weighted
rows at binary depth4 and ternary depth3; and checks PT3 against exhaustive
arbitrary-node-subset maximization on 20 small rational rows. Root-branch upper
bounds are independently checked on the 80 weighted rows. The exact dual-gap
mixture and branch-price constants are separately checked.

The script also reconstructs both literal odd-modulus families from scratch:
it generates all old divisors, all 273 distinct forbidden moduli and their CRT
residues, the 480 complete original labels, and checks every current leaf at
old x=1 against the actual congruences. It reconstructs the uniform old-unit
count 777600 and the AP/T8 killed leaf weight 15/36992. Its adjacent
prefix_correction_certificate.json pins the exact counts, masses, all observed
survivors, and a digest of each original arithmetic family. Normal verification
recomputes these fields and rejects any mismatch or duplicate JSON key.

These checks establish reproducible computational evidence for the new mechanism
and its examples. The general mathematical justification is PT1--PT5 above;
no Lean validation or unrestricted #7 numerical improvement is claimed.

The [prefix certificate](prefix_correction_certificate.json) also reconstructs both273-modulus arithmetic realizations from their literal CRT classes, all480 complete test labels, the pure current base, and the actual killed leaf mass. Altered numerical values and duplicate JSON keys are rejected.

### Prefix corrections survive height extension and controlled law changes

Let R be a finite nonnegative measure on the leaves of a p-ary prefix tree of actual height H. Me=max_(depth e nodes v) R(v), q=R1. For a selection v1,...,vh of one node at every depth, set N_v(y)=sum_e1_(y in ve). CPI gives exactly

  Omega_h(R)=U_h(R)-J_h(R),
  U_h=sum_e=1..h(2e+1)Me,
  J_h=max_v integral(N_v^2+2N_v)dR.                 (PCS1)

All quantities at h use the projection of the same actual row; J_h removes the common unit q from the square. Direct expansion proves PCS1, with no nested-selection restriction. Both U_h and J_h are nonnegative, positively homogeneous, monotone under adding positive measure, and bounded by C_h R1, where C_h=h(h+2). Omega_h is nonnegative and homogeneous but is NOT asserted monotone in R.

For h<=H,

  0<=Omega_H(R)-Omega_h(R)
    <=2 sum_e=h+1..H (e-1)Me
    <=2c p^(-h) [h/(p-1)+1/(p-1)^2]               (PCS2)

whenever Me<=c p^-e. The first inequality follows because every summand in the original CPI1 cost is nonnegative and restricting a full selection gives a legal h-selection. For the upper bound, extend a minimizing h-selection by choosing a maximal-mass node at each later depth. All new individual deficits vanish. For depth e there are e-1 earlier choices, each causing incompatibility cost at most2Me. This proves the finite sum; summing the entire geometric tail proves the final formula. It also covers h=0. At actual height0 both corrections are0.

For two nonnegative measures R,S on the SAME finite height-h tree, with epsilon=||R-S||_1 (full L1, not half),

  |Omega_h(R)-Omega_h(S)|<=C_h epsilon.            (PCS3)

Write R-S=delta_plus-delta_minus with masses a,b. A maximizing cylinder in R gives Me(R)-Me(S)<=a, and swapping gives >=-b. Thus -C_h b<=U_h(R)-U_h(S)<=C_h a. Every function N_v^2+2N_v takes values in[0,C_h], so the same bounds hold for J_h(R)-J_h(S). Subtracting gives [-C_h(a+b),C_h(a+b)]. This proves PCS3, including different total row masses and empty rows. No normalized conditional probability or division by a row mass is used.

For a joint nonnegative measure zeta on a finite old carrier X times current prefixes, let zeta_x be its unnormalized current row, and

  omega_h(zeta)=sum_x Omega_h(zeta_x).

By positive homogeneity this equals integral Omega_h(R_x) dsigma when zeta=sigma R, even on zero-mass rows. Therefore, on the SAME old carrier and prefix tree,

  |omega_h(zeta)-omega_h(zeta')|<=C_h||zeta-zeta'||_1. (PCS4)

In particular for actual height H>=h, any certified lower value B_h<=omega_h(zeta') gives

  omega_H(zeta)>=max(0,B_h-C_h epsilon).           (PCS5)

Only the one full joint L1 discrepancy is charged: incoming-law change and kernel change must not be counted separately after already included in epsilon. The larger actual current height costs NOTHING in this lower certificate because PCS2 is monotone. A two-sided approximation additionally pays the geometric upper tail of PCS2; with c(x) caps its integrated coefficient is integral c dsigma.

At p19,T8, sigma=nu13 K17^-, R=K19^-, zeta=eta. The generic full-Haar cap is c<=18/10=9/5 and sigma1<=1. Thus for h=6,

  0<=omega_H-omega_6<=2*(9/5)*19^-6*(6/18+1/18^2)
       =109/(90*19^6).

The joint-law sensitivity is48 epsilon. At p17 the cap2 similarly gives tail97/(64*17^6) and sensitivity48 epsilon. If H<6 use h=H: extra original test depths cannot be fabricated just to claim a larger correction.

For the KC lifted finite reference on the common original carrier, existing positive-kernel contractions give

  ||eta-eta_core||_1<=epsilon17,0+epsilon19,0+eNm.    (PCS6)

Consequently its depth-h correction can be transported by PCS5 with this error. This only transports a supplied certificate, not its unknown uniform minimum over original residue families. The core must be lifted to the common carrier; simply averaging or forgetting old rows is not covered by PCS4.

There are two distinct legitimate uses. To correct an independently established ACTUAL envelope U, combine CPI4 and PCS5: Q_eta<=U-484 eta1-max(0,B_h-C_h epsilon). Alternatively evaluate the full REFERENCE corrected objective using its own row data, then apply KC8's already-paid full-objective comparison. In the latter use no second PCS5 error is required. Neither route appends a new subtraction to the exact CT identity or changes299.398 without the missing uniform optimization.

The common-old-carrier condition is necessary. Split CPI5's S row into its six leaves below root1 and three below root2. Each separate row has Omega3=0, while their sum has Omega3=8 at unit leaf mass. Forgetting which old row occurred can therefore invent a positive correction. Positive homogeneity does not authorize averaging old histories. The ordinary proof above was independently checked, with exact tests on256 support sets,80 rational row pairs and all32,640 pairs of those support sets; this is not Lean verification.

### Conditional head deletion with a priced arbitrary cofactor tail

Ordinary mathematics and exact rational checks; no Lean verification or new
noncoverage endpoint. The preserved-law theorem permits all original old
cofactors and all finite current heights at17 and19. Its numerical corollary
still needs an explicit bound on one new actual tail observable.

#### 1. Actual tail residuals on the unchanged pure bases

Fix the actual AP13 probability nu, the normalized actual physical K17,
its killed restriction R17=K17^-, and the actual R19=K19^-. Let eta=nu R17 R19.
No conditioning is inserted. An old event E is lifted unchanged through17.
Pad the through13 old space uniformly to include315 if necessary.

At p=17,19 split the ACTUAL mixed forbidden labels (d,p^e) into the head
labels d>1 dividing315 and all the remaining labels d not dividing315.
The latter are called tail labels even at small exponent; in particular11,
13, and the19 step's17 factors are paid. Unit cofactors are pure constraints,
not mixed tail labels. Let P_p be the ACTUAL pure survivor set with Haar
mass lambda_p. Both head and full mixed unions below use this same P_p,
including all actual pure depths. Let alpha_p^h(u) be the pure-base
probability of the head mixed union, alpha_p(x) that of the full mixed union.
Define delta_p=7/(p-2) and

    b_p(u)=(alpha_p^h(u)-delta_p)_+/(1-delta_p),
    r_p(x)=beta_p(x)-b_p(u)>=0.

These are observations on one actual family. No reference physical process
is constructed, and the19 input remains exactly nu R17 in killed expectations.
The head estimates already proved in HBD give

    sum_(u mod315)b17(u)<=1/2,
    sum_(u mod315)b19(u)<=2/5.                    (CHT1)

Write ell_p(x) for the labelled tail union upper bound

    ell_p(x)=lambda_p^-1
      sum_(actual tail(d,e)) p^-e 1_(x=a_(d,e) mod d).

Each original label occurs once; all actually present finite depths remain.
The actual extra union mass z_p=alpha_p-alpha_p^h satisfies0<=z_p<=ell_p.
Consequently, setting

    s_p(x)=min(1-b_p(u),
      [(alpha_p^h(u)+ell_p(x)-delta_p)_+
       -(alpha_p^h(u)-delta_p)_+]/(1-delta_p)),    (CHT2)

we have the pointwise bounds

    0<=r_p<=s_p<=ell_p/(1-delta_p).               (CHT3)

Indeed beta is an increasing hinge, and r_p is its exact increment under
z_p. The additional clip uses beta_p<=1. If alpha_p^h<delta_p, every tail
load ell_p<=delta_p-alpha_p^h costs zero in CHT2. This is the actual head
slack, not the result of selecting a different head layout for each row.
The possible coincidence of head and tail current prefixes only improves
z_p<=ell_p; no independence or disjointness is assumed.

#### 2. Exact same-event two-step identity and upper certificate

Let w_E(u)=nu(E intersect {head=u}). The exact identity is

    eta(E)=sum_u w_E(u)(1-b17(u))(1-b19(u))-P_E,

    P_E=nu[1_E(1-b19)r17]+nu R17[1_E r19].       (CHT4)

Proof: R19(1)=1-b19-r19. The functions1_E and b19 depend only on the
inherited coordinates. Thus nu R17[1_E(1-b19)] is
nu[1_E(1-b19)(1-beta17)]; substitute beta17=b17+r17.
The second term stays under the actual R17. This explicitly retains the
head19 survival discount on17 tail loss and the prior killing on19 tail loss.

Define the nonnegative computable upper price

    T_E=nu[1_E(1-b19)s17]+nu R17[1_E s19].        (CHT5)

Then P_E<=T_E, and T_E<=T_Omega. Replacing R17 by K17 produces a valid,
usually weaker upper bound; equality of those source laws is NOT asserted.
If w1>=w2 are the two greatest actual w_E entries, CHT1 and the existing
two-simplex vertex argument give

    eta(E)>=nu(E)
      -max{(7/10)w1,(1/2)w1+(2/5)w2}-T_E.       (CHT6)

This theorem has no restriction on current mixed old cofactors or finite
heights. With arbitrary original357 exponents the event head weights w1,w2
remain actual required inputs; no generic1/(74 rho) cap is asserted there.

#### 3. Conditional numerical threshold with arbitrary current cofactors

For the corollary only, require the original357 period to divide315.
Allow arbitrary original11/13 classes and heights and ALL current17/19 old
cofactors and finite heights. Use the actual AP11/T4, AP13/T6 source with
one final conditioning, so the established constants are

    M=2621130891614589/246025127976511,
    r=18925009844347/38266567762500,
    c0=1/(74r),  m0=(11-M)/10.

For EVERY inherited complete test A, E={A<=10} satisfies nu(E)>=m0 and
w1<=c0. Also w1+w2<=nu(E). CHT6 therefore yields

    eta(A<=10)>=mstar-T_E,
    mstar=min(m0-(7/10)c0,(3/5)m0-(1/10)c0)
          =704627631753217/45514648675654535
          =0.01548133737721494... .              (CHT7)

The two arguments of the minimum increase with nu(E), so substitution of
m0 is legitimate. Using CT5 with tau121,c100 gives on the SAME full test

    Delta_121(L)>=21(mstar-T_E)
       >=0.3251080849215137... -21 T_Omega.       (CHT8)

Thus T_Omega<mstar is a distribution-specific certificate uniformly over
all original final test labels, with17 tails containing11/13 and19 tails
containing17 permitted. A negative displayed lower bound is merely vacuous;
nonnegativity of eta and Delta remains available. Nothing in CHT7/8 proves
T_Omega<mstar for every unrestricted family, nor transfers this tau121
certificate to the tau81 KC threshold.

#### 4. Actual arithmetic family distinguishes gated and linear tail prices

Let Q=315*11*13. For every d|Q,d>1, forbid0 modulo d. The AP13 construction
is exactly uniform on the units of Q: all mixed old exclusions are inactive
on previous units, the pure0 classes remove zero roots, and conditioning
has mass1. No other law is substituted. Let d_0,...,d_11 be the ascending
divisors of315, with d_0=1. At17 and19 add pure0 modulo p, and for i=1..11
add the head class of modulus d_i*p with old residue1 and current residue i.

At17 also add, for i=0..11:

    modulus d_i*11*17: head residue1, 11 residue1,
                         17 residue13+(i mod4);
    modulus d_i*13*17: head residue1, 13 residue1,
                         17 residue12.

At19 add for i=0..11:

    modulus d_i*17*19: head residue1, 17 residue16,
                         19 residue12+(i mod7).

CRT makes each listed class a literal original residue. The107 moduli are
all distinct odd integers>1. The period is14549535 and all192 divisor-test
labels, with independent residues allowed, are retained.

Exact grouped enumeration of the actual source and physical17 rows gives

    T_Omega=7041421/663552000=0.01061170940634645... <mstar.

The grouping only identifies values on which every actual mask and the
one checked centered test agree: for11 and13 it separates1,2,and every
other unit. Source masses are their exact counts, not a new law. For the
whole-space price there is no test in the integrand, so T_Omega itself is
uniform over the complete test domain without enumerating test layouts.
CHT8 consequently proves a positive CT121 loss for EVERY full test in
this family, using generic same-law constants M,r. The exact resulting
loss is0.1022621873882... .

The corresponding un-gated linear union price on the SAME killed chain is

    30855578893/448345497600=0.06882098528516593...,

which exceeds mstar. Thus retaining threshold slack establishes a
certificate that the direct Lipschitz/union tail price fails to establish.
The exact actual residual price P_Omega is smaller still:

    P17=20983/13271040=0.0015811119550540123...,
    P19=2590579/995328000=0.0026027389965920782... .

Replacing the latter killed expectation by its actual physical17 counterpart
gives15960467/5971968000=0.00267256405258702..., a strict loss of information.
The exact identity CHT4 is checked on seven bands of the literal inherited
complete test centered at2, including A<=10. The [exact verifier](verify_conditional_head_tail.py) and [certificate](conditional_head_tail_certificate.json) use explicit
raise-on-failure checks and pass under python3 -I -O. This finite family is
neither a universal tail bound nor a newly solved noncoverage subclass;
older supported-law results dominate existence conclusions in this class.

#### 5. Exact barrier for the unconditioned Haar-density shortcut

A generic estimate based only on nu<=D Haar, where
D=1039695426000000/18925009844347, and physical17<=2D Haar, gives the following
all-height linear tail upper prices after discarding the discounts in CHT5:

    U17=D/8*(product_(q=3,5,7,11,13)q/(q-1)-208/105)
       =650660582446875/151400078754776
       =4.297623804415291...,

    U19=2D/10*(product_(q=3,5,7,11,13,17)q/(q-1)-208/105)
       =2624163406239375/302800157509552
       =8.666321140062797... .

Here208/105=sum_(d|315)1/d. The constants use lambda_p>=(p-2)/(p-1),
1/(1-delta_p)=(p-2)/(p-9), and sum_(e>=1)p^-e=1/(p-1).
Every old and current tail is summed; this is a comparison against the
actual law via its density, not a substitution of Haar as the source.
Both prices exceed1 and cannot prove CHT7 positivity. These are exact
values of this particular sufficient estimate, not a counterexample to
better conditional tail estimates or to an unrestricted CHT7 premise.

An independent reconstruction enumerates all17280 actual old units, groups their48 literal mask-incidence patterns, and obtains the same four rational totals for the gated price, linear price, and two residual costs. The grouping changes no measure.

### Exact charged common-test maximum at every current height

These are ordinary mathematical arguments with exact standard-library verification, not Lean verification. The scope is the same actual source and mixed masks as BQC, extended only by redundant pure current classes. They do not provide a uniform correction for arbitrary AP13 source families.

#### Literal family and one actual law

Let Q = 315. Exclude 0 modulo 3, 5 and 7. The actual old source is uniform on the 144 units modulo Q. For each p = 17, 19 exclude 0 modulo p and, for i = 1,...,8, use the distinct mixed modulus d_i p, with old residue 1 modulo d_i and current residue i modulo p, where

    d_i = (3, 9, 15, 21, 45, 63, 105, 315).

The actual residue is CRT(1 modulo d_i, i modulo p). There are 21 distinct odd forbidden moduli, period 101745, and 48 complete original divisor-test labels.

Set k(x) = sum_i 1_(x = 1 modulo d_i), alpha_p = k/(p-1), delta_p = 7/(p-2), g_p = 1/(1-min(alpha_p,delta_p)), beta_p = (alpha_p-delta_p)_+/(1-delta_p), t_p = g_p/(p-1), and q_p = 1-beta_p. The killed row puts mass g_p/(p-1) on each actual surviving nonzero current root. Put

    q = q17 q19, u = t17 q19, v = t19 q17, w = t17 t19.

This is the same final killed law eta, because the 19 masks have no 17 factor. Both assigned charges remain positive: b17 = 1/2304 and b19 = 1/2592, with the latter measured under the physical 17 input. The actual final mass is eta(BQX1) = 13813/13824. No source is renormalized or replaced.

The four complete old blocks A, B, C, D remain independently chosen, each containing all 12 old divisor labels. BQC1 gives the exact maximum over current residues as the maximum of

    E[q A^2 + u(2AB+B^2) + v(2AC+C^2)
                  + w(2AD+2BC+2BD+2CD+D^2)].       (BQX1)

For any prescribed old layouts, current roots 16 and 18 attain all pair caps simultaneously. This is exact current optimization, not a restriction on the independent old choices.

#### Product first-exit consolidation

The following reduction uses symmetry of this actual measure and these actual weights, not arbitrary source symmetry. It also gives a reusable reduction for nonnegative quadratic cylinder objectives with the stated invariance.

Under the uniform unit source, q, u, v and w are invariant under permutations of off-spine children of the distinguished paths x = 1 in the 3-, 5- and 7-coordinate trees. For each old divisor d and each coordinate p^a dividing it, a unit residue is classified by its first digit at which it differs from 1, or by never differing. Replace every off-spine choice at first-exit depth r by 1 + p^(r-1); for p = 3, exponent 1 this gives representative 2. At exponent 2 the representatives are 1, 2 and 4. At p = 5, 7 the representatives are 1 and 2.

Make this replacement independently for every original label and combine the coordinate representatives by CRT. A cylinder's weighted mass is unchanged: the transformation retains its coordinate depths and first exits, and those specify its orbit under measure- and weight-preserving tree permutations. If two original cylinders intersect, their replacements still intersect, their intersection has the same coordinate first exits and depths, and its weighted mass is unchanged. If they were disjoint, the new intersection has nonnegative weighted mass. Thus every nonnegative unary or pair term stays the same or increases. A cylinder with a nonunit residue initially vanishes on the actual source; changing it to a unit cylinder can only increase this objective.

Consequently the maximum over all original residue choices equals the maximum over these independent representative choices. No common center or nested chain was assumed. All choices remain legal original test labels; the reduction only consolidates equivalent off-spine positions for this nonnegative objective.

There are 11 nonconstant labels per old block. Their representative-domain product is 5,308,416. Four independent blocks therefore have

    5,308,416^4 = 794,071,845,499,378,503,449,051,136

representative assignments. Their four unit labels are constant 1 and are retained in every quadratic coefficient.

#### Exact finite maximum

Expand (BQX1) into a constant, one unary table per original label, and one pair table per unordered pair of labels. For a symmetric matrix of actual row weights H, a label in block g has unary weight H_gg + 2 sum_h H_gh; labels in blocks g,h have pair weight 2 H_gh. Here

    H = [[q,u,v,w], [u,u,w,w], [v,w,v,w], [w,w,w,w]].

The [exact verifier](verify_exact_bqc.py) reconstructs every rational table entry by summing over the actual 144 old points. It multiplies by the exact common denominator and uses the existing RS arbitrary-table branch inequalities. At a partial assignment with remaining variables U, current exact value c and adjusted unary tables a_i,

    c + sum_i max_r a_i(r) + sum_(i<j) max_(r,s) V_ij(r,s)

bounds every completion. Conditioning on i = r replaces each remaining unary maximum by max_s(a_j(s)+V_ij(r,s)). Pruned branches are disjoint and contribute their full product of remaining domain sizes to the coverage count; unpruned branches are recursively exhausted. The certificate carries this coverage and exact integer scale/value. The correctness claim uses the inequalities and complete branch partition, not the search-node count.

The result is

    max_(A,B,C,D) E F = 7061549/548352.             (BQX2)

All four old blocks centered at 1 attain it. This is a proved outcome of optimization, not a premise. The verifier also independently scans the literal surviving points modulo 101745 with their actual killed weights and computes the same value for the maximizing original test.

Let C_* = sum_(d|315) 1_(x=1 modulo d), with the d=1 summand understood as constant 1. The exact values are

    E q C_*^2 = 829/96,
    Gamma(u) = 8261/12096,
    Gamma(v) = 160813/274176,
    Gamma(w) = 79309/1645056,
    Gamma(q) = 120949/13824.

For u,v,w, C_* is maximizing by the nonnegative centered-cylinder expansion BQC2, directly rechecked on every actual row. For q, the old test centered at 2 attains Gamma(q). Hence the same final-law split benchmark is

    S = Gamma(q)+3 Gamma(u)+3 Gamma(v)+9 Gamma(w)
      = 10685917/822528,

and its exact, uniform-over-all-original-tests loss is

    S - max E F = 1573/13824
                = 0.11378761574074074... .        (BQX3)

This improves the earlier BQC5 lower bound 0.057281... to the exact answer for that same family and benchmark. In particular the full maximizer accepts the entire available baseline mismatch to maximize the coupled objective.

A separate old-weight calculation, useful as a direct comparison, gives R0 = u+v+w,

    Gamma(R0) = 103223/78336,
    Gamma(q+R0) = 109340767/10967040,
    Gamma(q)+Gamma(R0)-Gamma(q+R0)
                = 3189979/32901120 = 0.096956547... .

The merged weight maximizer is centered at 226 modulo315 (1 modulo9, 1 modulo5 and 2 modulo7), whereas the full four-block optimum centers at1. This is a concrete distinction between an optimum of the merged one-block envelope and the actual coupled optimum. The stronger exact conclusion (BQX3) does not rely on this subadditivity bound.

#### All original current heights and complete geometric tails

For arbitrary finite H,K >= 1, add the redundant pure classes 0 modulo17^e for 2 <= e <= H and 0 modulo19^f for 2 <= f <= K. The family has 19+H+K distinct forbidden moduli and exactly 12(H+1)(K+1) complete original test labels. It keeps the same old law, alpha, beta, q,u,v,w and both charges. The new digits are uniform within each surviving root under the same actual killed kernels.

For p = 17,19 define

    b_p(h) = sum_(e=1..h)(2e+1) p^(1-e).

The exact full original-test maximum is

    M_HK = E q C_*^2 + b17(H) Gamma(u) + b19(K) Gamma(v)
                                  + b17(H)b19(K) Gamma(w).       (BQX4)

Proof: decompose every test by its literal exponent pair (e,f). Retain the four blocks indexed by {0,1} x {0,1}. Their full contribution is at most (BQX2). Every remaining pair coefficient is a nonnegative scalar multiple of u, v or w: a positive current maximum depth m contributes t_p p^(1-m), and a coordinate of depth0 at both endpoints contributes q_p. For each f in {u,v,w}, BQC2 and Cauchy-Schwarz give

    E[f A B] <= sqrt(E[f A^2] E[f B^2]) <= Gamma(f)

for arbitrary independent complete old blocks A,B. Therefore all added terms are bounded termwise by their centered values. Taking every old block equal to C_* and all positive current prefixes along the globally clean roots16 and18 attains every bound, including the retained four-block maximum. Summing the pair coefficients yields (BQX4), because exactly 2e+1 ordered pairs have maximum depth e. This proves all finite H,K with no removal or identification of original labels.

The split comparison with coefficients b17(H), b19(K) therefore has the same exact gap1573/13824 at every H,K. Subtracting484 eta(BQX1) preserves this gap for the original signed final-law objective. It remains a split comparison for this final eta, not KC's separately optimized two-frontier sum.

The complete tails are explicit:

    b_p(infinity) = p(3p-1)/(p-1)^2,
    b17(infinity) = 425/128,
    b19(infinity) = 266/81,
    b_p(infinity)-b_p(h)
      = p^(1-h)[(2h+3)/(p-1)+2/(p-1)^2].

Thus the supremum of the finite-height maxima is exactly

    sup_(H,K>=1) M_HK = 113889776093/8527970304
                     = 13.354851392901848... .     (BQX5)

This is a same-family all-height result. No arbitrary old-source, arbitrary new mixed-depth geometry, 299.398 KC target, later-prime continuation or unrestricted covering-system conclusion follows.

The [certificate](exact_bqc_certificate.json) records both actual charges, full signed mass, every first-exit domain, exact maxima and all-height coefficients. A separate calculation partitions by the first zero-block original label not centered at1 and refines its two insufficient bounds;45 disjoint exact cuts cover the same full representative domain and give the same maximum. Both methods use integer bounds rather than floating optimization.

### Finite translated queries locate the original point but do not integrate it

[RRO section60 at dev dd264421a2](https://github.com/the-omega-institute/trureturing/blob/dd264421a2a26cf8b84202d5082f880ddebffd4b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)
sharpens the observation-cost interface. Its oracle fixes one unknown point x
and, for a chosen integer n, returns the ENTIRE vector
(min(v_p(x+n),e_p))_(p|M), where M=product p^e_p and the factorization is supplied.
Each complete vector costs one call. CRT and all finite arithmetic are outside
this query count. For deterministic zero-error recovery of x modulo M, the
ordinary proofs in60.5--60.8 give

    C_nonadaptive(M)=max_(p|M)(p-1)p^(e_p-1),
    C_adaptive(M)=max_(p|M)e_p(p-1).             (TQ1)

The local nonadaptive condition is to query all but at most one leaf in each
final sibling group. The adaptive strategy eliminates at most p-1 child balls
per digit; the adversary can force that many. CRT combines one selected center
per prime into one integer query each round, so global costs are maxima, not
sums. The M=1 boundary costs0 queries.

For5040=2^4*3^2*5*7 the two costs are8 and6. For its odd part315 both are6.
For the existing unequal KC period

    M=3^17*5^10*7^8*11^7*13^6*17^6*19^6,

local adaptive costs are(34,40,48,70,72,96,108), so the global value is108;
the nonadaptive value on the full finite residue space is86,093,442. On the
actual surviving support108 remains an upper bound; the whole-space lower
bound need not remain sharp after that restriction.

For a fixed actual family and original test, a successful same-point transcript
determines every literal mask/test indicator and hence both signs of L^2-484.
It preserves their common witness. This does not compute actual transcript
masses, row union sizes or normalizations, nor bound the number of transcript
cells or family/test assignments to optimize. If an exact enumerator already
knows x, these queries supply no additional information. The costs therefore
do not imply a108-operation expectation or an enumeration speedup.

The useful search discipline is to branch on actual translated observations
and retain each branch's actual weight and original labels. A target-specific
pruning bound must still be proved. Section60 adds theory and digestion input;
this increment contains no new D5 Lean or frozen-pin result for #7. Neither
TQ1 nor the earlier sparse-feasibility classification gives the299.398 bound
or later-prime continuation.

### A literal obstruction to uniform gated-tail thresholds, with its CHT6 consumer

Ordinary mathematics and exact standard-library verification, not Lean
verification. This result refutes the proposed unrestricted inequalities
T_Omega < mstar and T_{A<=10} < mstar (uniformly over every original complete
test), where mstar is the fixed generic CHT7 intercept. It does not refute CHT6,
CHT7's conditional implication, noncoverage, or a stronger joint estimate.

#### 1. One actual191-modulus family

Let Q=315*11*13=45045. For every nonunit d|Q, forbid0 modulo d. There are47
such original constraints. Their union removes precisely the nonunits. The
specified AP11/T4, AP13/T6 construction produces the uniform17280-unit source:
the pure zero classes delete zero roots, and every other old zero class is
inactive on the existing units. Its single final conditioning has mass1.
No reference probability is substituted.

Write the12 divisors of315 as d_0,...,d_11 in ascending order, with d_0=1.
At each p=17,19 retain pure0 modulo p and, for i=1,...,11, the head constraint

    old residue1 modulo d_i, current residue i modulo p.

For every d|Q not dividing315, add at17 the tail constraint

    old residue1 modulo d, current residue12 modulo17.

At19 add all remaining mixed cofactors of Q*17:

    d|Q, d not dividing315: old residue1 modulo d, current residue12 modulo19;
    d|Q: old residue1 modulo d, 17 residue16, current residue12 modulo19,
         with original cofactor17d.

Each class is combined by ordinary CRT. The family has47+48+96=191 distinct
odd forbidden moduli, precisely every nonunit divisor of Q*17*19. Its period
is14549535 and all192 original final divisor-test labels are retained; the
inherited through13 complete test has48 labels. There are36 mixed tail labels
at17 and84 at19, including every original17 factor. Both charges are positive:

    b17=779/245760,
    b19=1089821/398131200,

with b19 measured under the actual normalized physical17 input.

#### 2. Closed-form row prices from the literal labels

At an old unit x, put

    C(x)=sum_(d|315)1_(x=1 mod d),
    A1(x)=sum_(d|Q)1_(x=1 mod d)
         =C(x)(1+1_(x=1 mod11))(1+1_(x=1 mod13)).

Thus C-1 head labels are active. Their current residues1,...,11 are distinct.
The active17 tail-label count is A1-C, all at current residue12. The full
current bad set is therefore the head bad set together with12 iff A1>C.
Current root16 is globally clean. The actual killed17 mass q and its root16
mass t are

    k=C-1+1_(A1>C),
    beta17=(k/16-7/15)_+/(8/15),
    q=1-beta17,
    t=1/[16(1-min(k/16,7/15))].

At19 the active tail-label count is

    A1-C+A1 1_(current17=16).

Define the literal head charge h_p(n)=(n/(p-1)-7/(p-2))_+/(1-7/(p-2)) and
the CHT2 gate, in label-count notation,

    s_p(n,l)=min(1-h_p(n), h_p(n+l)-h_p(n)).

The old-point integrand whose expectation is T_Omega is exactly

    (1-h19(C-1)) s17(C-1,A1-C)
      +(q-t)s19(C-1,A1-C)+t s19(C-1,2A1-C).       (GTO1)

The t term is under the actual killed17 row. No physical-source replacement is
made. Formula GTO1 retains every label in the CHT2 union price; all coincident
tail current residues remain part of that labelled price.

The C distribution under uniform units modulo315 has counts

    C:      1   2   3   4   6   8  12
    count: 45  54  15  19   8   2   1

out of144. The11 and13 indicator probabilities are1/10 and1/12, independently
under this actual source. Thus GTO1 is a finite exact rational sum, yielding

    T_Omega = 889799/43545600 = 0.02043372924015...
             > mstar = 704627631753217/45514648675654535.

This family satisfies CHT7's original357-period restriction. Consequently a
universal upper bound T_Omega<mstar in that class is false, not merely absent.

#### 3. Two original tests distinguish what the event remembers

Let A_j=sum_(d|Q)1_(x=j mod d), j=1,2. Both are legitimate complete inherited
tests with all48 original labels. Put E_j={A_j<=10}. Exact values are

| event | nu(E) | greatest two head masses | T_E |
|---|---|---|---|
| E1 | 4229/4320 | 1/144,1/144 | 300761/70761600 |
| E2 | 4229/4320 | 1/144,1/144 | 889799/43545600 |

The entire sorted head-mass profiles agree, not just the greatest two entries.
Indeed multiplication by2 permutes the actual old unit source and carries the
center1 test to the center2 test, with the corresponding permutation of head
cells. The actual mask placement is held fixed, so the tail prices differ.

There is also a short structural reason that E2 contains all the priced support.
The possible A1 values are1,2,3,4,6,8,12,16,24,32,48. A positive17 term in GTO1
requires A1>=9, hence A1>=12. A positive19 term requires 2A1-1>126/17, hence
A1>=6 in that spectrum. In each prime coordinate the two centered loads have
product at most3 in the3^2 coordinate and at most2 in every other coordinate.
The reason is that residues1 and2 are already distinct at the first digit, so
both coordinate loads cannot exceed1 simultaneously. Hence pointwise

    A1 A2 <= 3*2*2*2*2=48.

Every positively priced point therefore has A2<=8 and belongs to E2. This proves
T_E2=T_Omega without assuming independent masks or changing the event.

For E1, A1<=10 forces A1<=8 and the17 term vanishes. The exact19 expectation is
300761/70761600=0.00425034199339...<mstar. Thus retaining the same event can change
the certificate, but event retention alone does not imply the uniform numerical
premise T_E<mstar: E2 is an actual counterexample to that premise as well.

#### 4. The actual CHT6 intercept remains large and succeeds

For both E1 and E2, the CHT6 head cost is

    max{(7/10)(1/144),(1/2+2/5)(1/144)}=1/160.

Their actual intercept nu(E)-headcost is2101/2160, rather than the much smaller
generic mstar. Consequently CHT6 gives the positive same-event surplus

    E1: eta(E1)>=68527999/70761600,
    E2: eta(E2)>=41466361/43545600.                (GTO2)

CT5 with tau121,c100 then gives, for every complete current-test extension of
the corresponding original inherited block,

    E1: Delta121>=68527999/3369600,
    E2: Delta121>=41466361/2073600.               (GTO3)

These are lower bounds from CHT6, not claims of equality for Delta. Direct
same-law calculation gives eta(E1)=152233/155520 and
eta(E2)=7756553/7962624, consistent with both lower bounds.

The exact residual prices illustrate the remaining loss in the labelled proxy:

    P_E1=11/155520,
    P_E2=P_Omega=22319/39813120.

The literal tails share current residue12. Their labelled loads can be large
while the actual extra union adds only one root. This explains why T can be
substantially larger than P in this witness; it is not evidence that actual
tail deletion universally exceeds mstar.

#### 5. A consumer uniform over every original test in this same family

The successful CHT6 conclusion is not restricted to the two centered tests.
For any complete inherited test A, every nonconstant cylinder has actual source
mass at most1/phi(d). Nonunit residue choices have mass0; unit residue choices
have exactly1/phi(d). Therefore, without assuming a common center,

    E_nu A <= sum_(d|Q) 1/phi(d)=5005/1728.

Since A>=1 and A>10 implies A>=11,

    nu(A<=10) >= (11-5005/1728)/10=14003/17280.

Every actual head cell has mass1/144, so every event has CHT6 head cost at most
1/160. Using T_E<=T_Omega on this same family yields, uniformly over all original
inherited and final test labels,

    eta(A<=10) >= 14003/17280-1/160-889799/43545600
                 =34125601/43545600 >0,

    Delta121 >= 34125601/2073600.                (GTO4)

The uniformity in GTO4 is justified by the per-original-label mean bound and
CHT6, not by enumerating finitely many chosen test layouts. This remains a
same-family result and not a new noncoverage subclass beyond prior results.

#### 6. Consequence for the unrestricted next obligation

Both overly strong candidate obligations are now excluded: T_Omega<mstar for
every family, and T_{A<=10}<mstar for every family and original test. The original
CHT6 route remains viable because the needed quantity is the joint surplus

    nu(E)-max{(7/10)w1,(1/2)w1+(2/5)w2}-T_E.

The exact counterexample shows why replacing its actual intercept by mstar
before controlling the tail can lose a working certificate. To obtain a general
positive surplus one still needs a quantitative coupling between the same
test's event mass/head cells and its actual tail geometry, or a stronger
observable for the actual extra union r. The present result supplies neither
that unrestricted inequality nor the KC tau81/later-prime continuation.

The standalone verifier reconstructs every191 original congruence by CRT,
enumerates all17280 actual old units, checks the1296 mask/test incidence groups,
and evaluates each physical17/killed17 row and every19 original tail condition.
It checks the exact CHT4 identities, all stated fractions, the original test
inventory, and the uniform consumer's numeric premise. All checks use explicit
raise-on-failure conditions and exact fractions, including under Python -I -O.

### Actual mask weights and an all-height square certificate

Ordinary proof with exact rational coefficient checks; no Lean verification.
Fix the actual killed19 input sigma=xi=nu13 K17^- and R=K19^-, so eta=sigma R.
The following argument also applies to any finite actual old measure sigma
and current prime p>=3 with row mass q and nonnegative prefix cap c satisfying
0<=q<=c. Neither input is normalized or replaced by the physical17 law.
For the actual flat killed row, R_x=c(x)1_(G_x)u_p; here c includes the actual
pure-survivor density, and q/c is its actual surviving Haar fraction.

Let D be the complete original old-test domain, with all divisor labels and
independently chosen original residues. For any nonnegative old weight f, put

    G(f)=max_(A in D) integral f A^2 d sigma,
    d_f(A)=G(f)-integral f A^2 d sigma.

Set S=1/(p-1), a=(3p-1)/(p-1)^2, b=a-S=2p/(p-1)^2,
theta=1/(2+S), and h=c-q. Choose 0<=r<=theta and define

    lambda=S/(S+r), rho=1-lambda, k=rho/theta, kappa=S k,
    w=c-theta h, v=q+lambda h,
    g=q+S c+r lambda c h/v, z=c/v.               (MW1)

The quotients are defined as0 on c=0, where every weighted term vanishes.
For c>0, v>=lambda c>0. In particular g,w,v are nonnegative and

    g<=q+Sc+rh<=(1+S)c,  w<=c,  k<=2+S.

Every original full test then satisfies the general bound

    integral L^2 d(sigma R)<=U_r,
    U_r=G(g)+(b-kappa)G(c)+kappa G(w).           (MW2)

At r=0 this is exactly the ordinary split cap
G(q+Sc)+b G(c). Thus minimizing U_r over its allowed parameter never worsens
that cap. No domination of the stronger OBE distance-profile bound is asserted.
The new observations are actual mask-weighted old square maxima, not another
encoding of the source-only scalar moments.

#### Exact identity and its retained losses

Write A_e for the literal old block of a full test at current exponent e,
including A_0. For finite actual current height H, the original prefix caps give

    integral L^2 d(sigma R)<=Phi_H,
    Phi_H=||A0||_q^2
      +sum_((e,f)!=(0,0),0<=e,f<=H) p^-max(e,f)<Ae,Af>_c.

This cap includes independent original current prefixes; it does not suppose
that they are compatible. Extend only the comparison sequence by A_e=A_0 for
e>H. It does not add original forbidden or test labels. The extra tail is

    Phi_infinity-Phi_H
      =p^-H[2S sum_(e=0..H)<Ae,A0>_c+(a-2S)||A0||_c^2]
      <=p^-H(a+2HS)G(c).                        (MW3)

It is nonnegative. Polarization, with s_e=p^-e and t_e=e+1+S, gives

    Phi_infinity=||A0||_(q+Sc)^2+sum_(e>=1)s_e t_e||Ae||_c^2
      -sum_(e>=1)s_e||Ae-A0||_c^2
      -sum_(1<=e<f)s_f||Ae-Af||_c^2.

Since r lambda=S rho, v=c-rho h and k theta=rho,

    Sc+g-(q+Sc)=Sc^2/v.

Completing squares pointwise therefore yields the exact nonnegative identity

    U_r-integral L^2 d(sigma R)
      =Lambda(L)+d_g(A0)
       +sum_(e>=1)s_e[(t_e-k)d_c(Ae)+k d_w(Ae)]
       +sum_(e>=1)s_e||Ae-z A0||_v^2
       +sum_(1<=e<f)s_f||Ae-Af||_c^2,            (MW4)

where Lambda=Phi_infinity-integral L^2 d(sigma R)>=0. All infinite
sums converge: the actual old domain is finite and the comparison tail repeats
A0. Also sum s_e t_e=b and sum s_e k=kappa, proving MW2.

The finite part of Lambda is the ordered original-label sum

    integral Ii Ij [c p^-max(ei,ej)-R_x(Ci intersect Cj)] d sigma,

excluding two zero-current labels. A compatible pair pays its actual deleted
prefix intersection; an incompatible pair pays the full cap. The comparison
tail MW3 supplies the rest. Thus MW4 retains both actual mask intersections
and original-test incompatibility on the same law.

If a test has square at least U_r-epsilon, MW4 forces each displayed
nonnegative loss to be at most epsilon. In particular

    sum_(e>=1)p^-e||Ae-z A0||_v^2<=epsilon,
    integral (c^2/v) A0^2 d sigma
      <=(sqrt(G(v))+sqrt(epsilon/S))^2.          (MW5)

The second statement follows from the triangle inequality in the direct sum
of the weighted spaces, using sum s_e=S. This specifies the extra near-maximum
condition: the positive old blocks must approximate the actual row-dependent
amplification z of the same baseline. No assumption of centered maximizers is
made, and a source-only high-energy condition does not supply MW5.

#### A three-value curvature alternative

Let E(t)=G(c-th), t0=1/(1+S), and define the nonnegative convexity gap

    C=theta E(0)+(1-theta)E(t0)-E(theta).

Here theta=(1-theta)t0. Write
V=(E(0)-E(theta))/theta and U=(E(theta)-E(t0))/(t0-theta).
Convexity and 0<=h<=c give 0<=U<=V<=E(0) and V-U=C/theta^2.
Since g<=q+Sc+rh, interpolation between t0 and theta gives

    U_r<=U_0-r[S V/(S+r)-U].

If V>0 choose r=S(V-U)/(2V), which lies in [0,theta]. The bracket is
at least(V-U)/2. If V=0 then C=0 and use r=0. Consequently, for E(0)>0,

    sup_L integral L^2 d(sigma R)
      <=U_0-S C^2/[4 theta^4 E(0)].             (MW6)

When E(0)=0 the full square is0. This does not assert positive C for every
family. If A_theta maximizes E(theta), then exactly

    C=theta d_c(A_theta)+(1-theta)d_(c-t0 h)(A_theta).

Thus C=0 supplies a common endpoint maximizer, while C>0 supplies the
quantitative saving MW6. Which alternative the actual family realizes remains
part of the joint optimization.

#### The unchanged19 input and complete old-test tails

At p=19 and r=theta=18/37 the weights and coefficients are

    w=(19c+18q)/37,
    g=q+c/18+18c(c-q)/(37c+324q),
    kappa=37/361, b-kappa=865/58482,
    z=361c/(37c+324q).

Therefore

    sup_L eta(L^2-484)
      <=G(g)+(37/361)G(w)+(865/58482)G(c)-484 eta(1). (MW7)

The actual caps c<=9/5 and K17's cap2, together with the existing same-AP13
bound, give

    G(c)<=(9/5)(89/64) Gamma13
      <=119251429066437923669013/292710856261333727360,
    (865/58482)G(c)<6.025855.

The comparison xi<=mu17 is used here only to bound a nonnegative square;
the weighted maxima in MW7 stay under xi. With this cap the coefficient of
C^2 in MW6 is greater than0.0006086; no uniform positive C is established.

For a finite box B in the original old test exponents at primes
P={3,5,7,11,13,17}, keep the actual sigma,c,q completely unchanged and optimize
only the test labels in that box, intersected with the actual inventory.
Write G_B for this maximum. The actual density bound sigma<=110 u_old gives,
for 0<=f<=F,

    0<=G(f)-G_B(f)<=110 F T_B,
    T_B=product_(p in P) p(p+1)/(p-1)^2
       -product_(p in P) sum_(j=0..B)(2j+1)p^-j. (MW8)

Indeed the square difference is a sum of omitted ordered label pairs;
each is at most110 F/lcm(d,e). The full pair sum factors by prime.
Every core assignment extends to the original labels, so the optimization
inequality has the stated direction. The exact single-prime tail is

    p^-B[(2B+3)p-(2B+1)]/(p-1)^2.

Using g<=19/10 and w,c<=9/5, the TOTAL MW7 error is at most

    (2090/9) T_B,
    B16: error<0.000564917,
    B20: error<0.000008522461.                   (MW9)

This truncates the original test inventory only. It does not bound the cost
of replacing forbidden masks or the actual input law by a finite reference.
Those changes still require KC's separate common-law estimates.

Rational upper certificates U_g,U_w,U_c for the three actual box16 maxima
would therefore give

    sup_L eta(L^2-484)
      <U_g+(37/361)U_w+(865/58482)U_c
       +0.000564917-484 eta(1).                 (MW10)

The arbitrary-label message certificates below can bound these weighted
maxima using their own exact unary/pair tables. No uniform such certificates
are currently supplied. MW10, the299.398 frontier and later-prime continuation
remain unresolved; the inequality is a reusable actual-mask reduction, not
an unrestricted #7 conclusion. The standalone verifier checks1296 rational
finite-array identities with complete comparison tails and the exact constants
in MW7--MW9. This is finite corroboration of the ordinary proof, not a kernel
verification of its universal quantifiers.

### Same-law original-label conflict cuts and rational message certificates

These are ordinary mathematical results, with exact standard-library certificate checks, not Lean verification. All bounds below apply to the entire final signed objective under one actual killed law. The numerical fixture is evidence of a nonzero cut and an attained message certificate; it is not a uniform improvement to the existing Gamma split, KC299.398, or unrestricted Erdős #7.

#### 1. General actual-law statement and original labels

Fix any finite actual family and one finite nonnegative final measure

    eta = nu13 K17^- K19^- .

At the second step its incoming measure is literally `nu13 K17^-`. Neither the normalized physical input `nu13 K17` nor a fresh supported law is substituted. Let `J` be the complete original divisor-test label set, including the single modulus-one label. Every other original modulus `m_i` has one globally selected residue `r_i mod m_i`, reused in every factor and every old row. Write `I_i=1_(x=r_i mod m_i)`, `L=1+sum_i I_i`, and `z=eta 1`.

The exact full objective is

    Q_eta(L) = eta(L²)-484 z
             = -483 z + sum_i u_i(r_i) + sum_(i<j) v_ij(r_i,r_j),
    u_i(r) = 3 eta C(r,m_i),
    v_ij(r,s) = 2 eta(C(r,m_i) intersect C(s,m_j)).              (LC1)

Every intersection is evaluated on the same eta. Generalized CRT makes it zero when the residues disagree modulo the gcd, otherwise the mass of the unique combined class modulo the lcm. There is no independent choice of a residue for separate entries containing the same label.

Put

    B0(eta) = -483 z + sum_i max u_i + sum_(i<j) max v_ij.

This is the entrywise pair envelope. It is generally different from, and can be weaker than, existing old-block Gamma envelopes.

#### 2. Arithmetic stars detect information erased by separate pair maxima

Choose one original central label d and distinct neighboring original labels m in N. For each central residue a define

    J_m(a) = max_(r mod m) eta(C(a,d) intersect C(r,m)).

For every global test,

    sum_(m in N) 2 eta(I_d I_m) <= 2 max_a sum_m J_m(a).

Consequently the exact lost amount in independently maximizing just these star factors is

    kappa_(d;N) = 2 [sum_m max_a J_m(a) - max_a sum_m J_m(a)] >= 0. (LC2)

This is a quantified constraint on the selected original label, not merely a condition on an abstract Gram matrix. It costs only one table per neighbor and one maximization over residues of d. The result holds for arbitrary actual eta, arbitrary residues, and all finite original heights. No radial symmetry, common center, nested-chain maximizer, or zero charge is assumed.

If d divides m, this simplifies to

    J_m(a) = max_(r mod m, r=a mod d) eta C(r,m).                (LC3)

A version spending the unary factor of d has

    kappa = max_a u_d(a) + 2 sum_m max_a J_m(a)
            - max_a [u_d(a)+2 sum_m J_m(a)].                   (LC4)

The same label d is chosen only once. In particular, pair maxima that require conflicting residues modulo d cannot all be attained.

For a finite collection of such stars, assign rational weights lambda_C >= 0. For each original unordered pair, the total weight of stars using that pair must be at most1. If LC4 is used, impose the same capacity1 for its original unary factor. Then

    sup_L Q_eta(L) <= B0(eta) - sum_C lambda_C kappa_C(eta).    (LC5)

Proof: each original factor has nonnegative loss `max f-f`. Within each star their sum is at least kappa_C. Multiply and sum, using factor capacities to avoid charging any individual loss more than once. The constant `-483 z` is retained exactly. The certificate holds uniformly over every complete original test, although kappa depends on the actual family law. A bound valid for all families still requires an outer argument controlling these quantities; LC5 does not supply that missing argument.

These cuts may also be taken for any small factor tree. Its minimum total loss is computed by eliminating leaves, storing at each original separator label its complete residue table. A disconnected or cyclic collection is not silently converted into independent trees; either its exact joint minimum is verified or a legitimate fractional packing is used.

#### 3. Law stability of a selected cut and finite-core use

Let eta and eta' be two finite nonnegative measures on a common lifted carrier, with full L1 discrepancy epsilon. A star spending t pair factors and h unary factors, h in {0,1}, has

    |kappa(eta)-kappa(eta')| <= (2t+3h) epsilon.                (LC6)

To prove this write eta-eta'=delta_plus-delta_minus with masses a,b. Every spent nonnegative factor has amplitude bounded by its coefficient c in {2,3}; its integral changes between -c b and c a. The independent-max sum and the joint star maximum each change between -C b and C a, where C=2t+3h. Their difference changes between -C(a+b) and C(a+b). No normalization or equal-mass premise is needed.

Thus a depth/core reference certificate B_C implies the actual correction

    kappa_C(eta) >= max(0, B_C-(2t+3h)epsilon).                (LC7)

Only selected factors are charged. This does not incur the number of all original labels. The core must be lifted to the same carrier and the discrepancy must include the actual incoming-law and killed-kernel change once. If the full reference objective is already transported by KC's full-objective comparison, do not pay the same discrepancy a second time. Conversely LC7 may only be subtracted from an actual factor envelope whose spent factors are present; it cannot be attached to an unrelated Gamma bound or to the exact CT identity.

All original depths and tails remain in LC1. Selecting a finite set of star factors does not truncate L. If a separate full-objective finite-core reduction is used, its already established omitted-label and law errors remain necessary. LC2 alone provides no tail deletion.

#### 4. Arbitrary signed rational messages

For each original pair i<j choose arbitrary rational functions h_ij,i(r_i) and h_ij,j(r_j). Define

    u_i^h(r) = u_i(r) + sum_(e incident i) h_e,i(r),
    v_ij^h(r,s) = v_ij(r,s)-h_ij,i(r)-h_ij,j(s).

The messages cancel exactly, assignment by assignment. Therefore

    sup_L Q_eta(L)
       <= -483 z + sum_i max_r u_i^h(r)
                  + sum_(i<j) max_(r,s) v_ij^h(r,s).           (LC8)

No sign restriction on the reparameterized factors or messages is required. The same algebra works for any exact finite unary/pair table, including signed factors obtained from an independently proved full-objective decomposition. A verifier checks all finite maxima using rational arithmetic. It need not trust LP convergence, floating dual feasibility, a branch count, or a solver's status. Missing messages mean zero messages and are valid, so one can work on selected stars or cycles without storing the full factor graph.

An LP using one candidate unary marginal per original residue, one pair marginal per literal residue pair, normalization, and agreement of pair projections with those unary marginals can generate h. This is the standard local marginal-polytope relaxation. Its optimality is not needed for LC8: every rational h is a valid upper certificate, and an actual assignment with equal value proves exactness for the stated input. The benchmark corrected by LC8 remains B0 for the same full objective. The method is a reusable certificate route; it does not assert the relaxation is exact on arbitrary arithmetic families.

For a chosen sparse message support, let G_h=B0-U_h. If only factor set F* has nonzero reparameterization, then

    |G_h(eta)-G_h(eta')| <= (sum_(f in F*) c_f) epsilon.

Indeed each factor's perturbations lie between -c_f b and c_f a; the difference of its original and shifted maximum changes by at most c_f(a+b). Messages must be held fixed during this comparison. The nonnegative improvement is max(0,G_h).

#### 5. A literal nonradial actual family

Take Q=315 and forbid old classes

    0 mod3, 0 mod5, 0 mod7, 2 mod9, 4 mod15.

Their 102 survivors modulo315 carry the uniform actual old law. Use cofactor list

    (3,9,15,21,45,63,105,315,5,7,35).

For p=17 and19 forbid pure0 modp and, at current residues i+1 for i=0,...,10, the mixed class with that cofactor. The first eight old residues are1. The last three old residues are2 at17 and3 at19. The full forbidden classes are their literal CRT combinations. Thus there are29 distinct odd forbidden moduli and common period101745. The complete divisor-test inventory is12*2*2=48 original labels.

At old x let k_p be the number of matching mixed masks, alpha_p=k_p/(p-1), delta_p=7/(p-2), g_p=1/(1-min(alpha_p,delta_p)), beta_p=(alpha_p-delta_p)_+/(1-delta_p), t_p=g_p/(p-1), q_p=1-beta_p. The actual killed row puts mass t_p on each unmasked nonzero root. Current19 masks have no17 factor, so the actual final law has row products, and the physical17 input has the same old marginal. The exact charges and final mass are

    b17 = 1/1632, b19 under physical17 = 1/1836,
    eta1 = 9781/9792.

Define q=q17q19, u=t17q19, v=q17t19, w=t17t19. For four independent complete old blocks A,B,C,D, retaining each block's unit label as constant1, the exact current maximum is

    E[q A²+u(2AB+B²)+v(2AC+C²)
         +w(2AD+2BC+2BD+2CD+D²)].                              (LC9)

Every prescribed old assignment attains all current pair caps simultaneously by putting every17-positive label at globally clean root16 and every19-positive label at globally clean root18. This is why no independent current label is dropped. Positive current unit-cofactor labels also take those roots and supply the three additional block constants. Before current maximization the original modulus-one test is unique; LC9's four constants arise from four distinct original labels1,17,19,323.

For LC9, H=[[q,u,v,w],[u,u,w,w],[v,w,v,w],[w,w,w,w]]. Expanding the four blocks gives constant E(sum H_gh), unary coefficient H_gg+2 sum_h H_gh, and pair coefficient2H_gh. All11 nonconstant old divisor labels in each block remain independent. A residue whose entire old cylinder is empty has zero contribution in every term; changing it to a nonempty residue cannot decrease a nonnegative objective. The verifier keeps EVERY nonempty original residue, yielding1004 unary choices in total. There is no first-exit consolidation, permutation orbit quotient, or assumed centered maximum.

The rational message certificate gives

    entrywise bound = 317481153727/19995655680,
    exact maximum = 846619/55488,
    entrywise improvement = 12393530887/19995655680
                          = 0.6198111772546786... .

The all-block old assignment centered at1 attains the bound. This is an output of exact upper/lower matching, not an input restriction. A separate scan of all literal surviving triples (x,y17,y19) under their actual killed weights gives the same mass and square integral. The signed final objective is

    max Q_eta = -77938211/166464.

For the tiny original-label cut d=3, neighbors9 and15, only the old marginal of the same eta is needed. The complete profile tables are

| a mod3 | M9(a) | M15(a) |
|---|---:|---:|
|0|0|0|
|1|3/17|3/17|
|2|4/17|2/17|

Thus

    kappa_(3;9,15) = 2[(4/17)+(3/17)-(6/17)] = 2/17.

The two best pair observations individually choose different residues for the SAME original modulus3 test. This is nonzero genuinely joint information. With any actual common-carrier L1 perturbation epsilon, this selected cut retains at least max(0,2/17-4epsilon), positive for epsilon<1/34. The coefficient4 here belongs to the two original pair factors 2 eta(I3 I9), 2 eta(I3 I15) in LC1. It is not the general variation coefficient of all LC9 factors.

#### 6. Reproduction and limits

The standard-library verifier `verify_original_label_messages.py` rebuilds the literal source/masks, every nonempty original-domain table, the rational message upper bound, the attaining assignment, the tiny divisibility-star profile, and the literal point scan. It runs with `python3 -I -O`. The file `original_label_message_certificate.json` contains the exact rational messages and result data. The verifier rejects duplicate JSON keys, duplicate original pairs, and inconsistent reported values. An optimizer is unnecessary to check the certificate.

The remaining unresolved step is an outer, all-family constraint sufficient to control LC5/LC8 or a stronger common-law envelope on the full AP13 core and all paid tails. The unrestricted299.398 continuation and later primes remain open.

#### 7. Existing results and public basis

The repository search for common/shared original labels, star cuts, pair compatibility, marginal polytopes, and message reparameterization found the current KB maximizing-label comparisons, RS signed unary/pair branch envelopes, OBE common-old-block distances, CPI/PT current-prefix incompatibility, and BQX exact four-block optimization. Those results are reused as context, but none of the searched report sections states LC3's old-divisibility profile cut or verifies the nonradial rational message certificate. The repository's `FiniteCompatibleCrt` and `CompatibleResidueJointImage` already provide the CRT compatibility structure; it is not reproved in new Lean. The finite response-law obstruction in `CompleteMediatorCutSharpBounds.three_cycle_complete_mediation_sharp` and the Boolean gluing example in `LocalLawGluingObstruction` are different finite input problems, not this weighted arbitrary-source cut. Text searches in the pinned Mathlib combinatorics and convex-analysis trees did not locate an exact weighted original-residue certificate theorem. This is a searched-scope statement, not a claim that the method is new.

Public source: David Sontag, Talya Meltzer, Amir Globerson, Tommi Jaakkola, Yair Weiss, [Tightening LP Relaxations for MAP using Message Passing](https://people.csail.mit.edu/dsontag/papers/sontag_uai08.pdf), UAI2008, sections2–3. The downloaded author-hosted PDF confirms the local marginal polytope, dual message upper bounds, exact assignment/dual matching, and the cluster gain `sum max b_e - max sum b_e` in equation4. Thus the message relaxation and general incompatibility gain are established methods. LC1–LC7 supply their explicit full-signed-killed-law, original-modulus CRT, factor-capacity, and L1 application here. No new Lean wrapper, claim of an invented LP method, or standalone positive finite-instance formalization is proposed.
