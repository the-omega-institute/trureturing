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
