# Five-prime cores with singly attached trees or cacti

This is an ordinary mathematical proof supported by exact rational parameter
certificates. It is not a Lean proof or a solution of unrestricted Erdős #7.
The cylinder-profile argument is reused from
[P3–P5 of the four-prime head theorem](10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md#a-four-prime-head-and-a-restricted-noncoverage-theorem).
The self-contained Python 3 standard-library
[parameter certificate](../frontier/cover-geometry/five_core_cylinder_profiles.py)
and its [exact data](../frontier/cover-geometry/five_core_cylinder_profiles.json)
reconstruct that baseline before evaluating the four changed-domain cases.

## 1. Statements and exact meaning of attachment

Let D be a finite set of distinct odd integers greater than one, with one
original class a_d modulo d for each d in D. Its original prime graph G has
one vertex for each prime dividing Q = lcm D, and an edge pq whenever some
original d is divisible by pq.

**Theorem A.** Suppose G is obtained from an arbitrary graph on at most five
original prime vertices by attaching finitely many finite trees, each meeting
the retained graph in exactly one vertex. Then the original classes do not
cover the integers.

**Theorem B.** Let S = {3,5,7,u,v}, with original primes 11 ≤ u < v. Suppose G
is obtained from an arbitrary graph on S by attaching finitely many finite
cactus graphs, each meeting S in exactly one vertex. Then the original
classes do not cover the integers.

In both statements the attached graphs have pairwise disjoint private
interiors and there are no additional edges between these interiors. In B,
the **whole attached graph including its attachment vertex** must be a
cactus: every nontrivial block is an edge or a simple cycle. Merely requiring
the graph induced outside S to be a cactus is not the same hypothesis.
Disconnected retained graphs and isolated vertices are allowed. Original
residues, finite heights, and the numbers and sizes of attachments are
unrestricted. In particular, every original four- or five-prime label in
the core, and every original triple label in a cactus triangle, is retained.

The quantitative assertion below is a conditional projection reserve greater
than 1/2048. Its exact conversion to original Haar mass includes the extension
weights; it is not a full-Haar lower bound of 1/2048.

## 2. Original coordinates and exact elimination

For every original prime p put X_p = Z/p^{h_p}Z, h_p = v_p(Q), with uniform
probability H_p. The CRT identifies the original period with the product of
these spaces; an original p-prefix of exponent e has mass p^{-e}.

In B retain K = S. In A, first enlarge a nonempty S to exactly five original
vertices if |S| < 5 and at least five original vertices occur: successively
absorb a tree vertex adjacent to the current retained graph. Every remaining
attachment is still a singly attached tree. Such a next vertex exists while
any vertex remains outside, because every original component meets S. If 3
occurs outside this enlarged S, also retain the unique path from 3 to S.
Let K be this union. If 3 is in S or absent altogether, take K = S. Thus every
eliminated prime is at least 5. The case of at most four total primes is
handled at the end of Section 4.

For p in K define V_p ⊆ X_p to consist of precisely those words that avoid
the original pure p-power classes and have avoiding extensions into every
eliminated component attached at p. Let δ_p = H_p(V_p), and put

    V = ∏_{p∈K} V_p,
    R = V minus all original mixed classes supported entirely in K,
    ν = ⊗_{p∈K} H_p(· | V_p).

The proof below establishes that every δ_p is positive. Exact elimination gives

    R = projection onto X_K of the full original avoiding set.       (1)

Indeed, necessity follows by restricting an avoiding assignment. Conversely,
each retained word in R avoids the retained labels and has a witness in each
attached component. Their interiors are disjoint and no original constraint
crosses between them, so these witnesses glue simultaneously.

Every original support is a clique of G. In A any mixed label meeting an
eliminated vertex is supported on one tree edge. In B such a label belongs
to a unique cactus block, with triple labels possible only inside triangles.
Consequently all original labels are assigned exactly once, without changing
their moduli, residues, or exponents. ν is the conditional **product** law on
the actual domains; it is not the marginal law of global Haar survivors.

## 3. Cylinder profiles on arbitrary actual domains

The following is the domain-loss version of the existing P3–P5 induction.
Let actual distinct primes p_i satisfy p_i ≥ t_i, where t_i are fixed numerical
reference primes, and suppose H_{p_i}(V_{p_i}) ≥ d_i > 0. References are used
only in inequalities; they do not replace any original prime or modulus.

For a coordinate subset A let μ_A be uniform on the complete set of points
in ∏_{i∈A}V_{p_i} avoiding all original mixed classes supported in A. A profile
c_A(T), with c_A(∅) = 1, asserts for every original prefix cylinder on T that

    μ_A(cylinder with exponents e_i on T)
       ≤ c_A(T) / ∏_{i∈T} p_i^{e_i}.                    (2)

Only exponents within the original heights are asserted in (2). Define

    u_A(e) = min_{T⊆supp(e)} c_A(T) / ∏_{i∈T} t_i^{e_i},
    R_A = Σ_{e≠0} u_A(e).                               (3)

This infinite exponent sum majorizes the original finite range. It introduces
no additional original classes. Start with c_∅(∅)=1, R_∅=0, f_∅=1, where f_A
lower-bounds the survivor fraction relative to the actual product domains.

To adjoin i, start from the one law μ_A × H_{p_i}(·|V_{p_i}). Each new class
has an original modulus d p_i^e with d>1 supported in A and e>0. Distinct
moduli give at most one class for each complete exponent tuple. Its old
cylinder probability is bounded by u_A, because p_j ≥ t_j. Its new cylinder
probability is at most p_i^{-e}/δ_{p_i}. Thus the new forbidden union has mass
at most

    b_{A,i} = R_A / ((t_i−1)d_i).                       (4)

If b_{A,i}<1, conditioning leaves positive mass and gives

    c_{A∪{i}}^(i)(T) = c_A(T\{i})/(1−b_{A,i})
                       × [d_i^{-1} if i∈T, else 1]   (T≠∅),
    f_{A∪{i}} ≥ f_A(1−b_{A,i}).                         (5)

The empty-support coefficient is kept separately at c_{A∪{i}}(∅)=1.

The product before conditioning is uniform on its finite support, so after
conditioning it is uniform on the complete actual survivor set. Every
admissible last-coordinate order therefore produces the **same** μ_{A∪{i}}.
Taking the minimum of (5)'s profile coefficients separately for each T, and
the maximum of the valid f-bounds, is legitimate. There is no multiplication
of survival fractions associated with different optimized laws.

For exact evaluation of (3), choose L_i ≥ 0 with

    t_i^{L_i+1} ≥ max_{T not containing i} c(T∪{i})/c(T).

If e_i>L_i, adding i to a candidate minimizing support cannot increase its
value. A minimizing support can therefore include every tail coordinate.
Partition each exponent into 0,…,L_i and one infinite tail. In a cell with
tail set J and positive bounded set I, the envelope equals

    (∏_{i∈J}t_i^{-e_i})
      min_{T⊆I} c(J∪T)/∏_{i∈T}t_i^{e_i}.

The tails sum exactly by Σ_{e>L}t^{-e}=1/[t^L(t−1)]. This proves that the
finite cell certificate evaluates the full infinite sum, not a height cutoff.

## 4. Theorem A: trees and all prime configurations

We reuse the quantitative tree blocker estimate and exact elimination in
[PB1–PB7 of the retained hanging-tree proof](06-block-saturation-and-the-actual-crossing-budget.md#full-fibre-blocking-and-exact-hanging-tree-elimination).
If an actual child domain at prime q≥5 has density at least 1/2, then the
parent words whose entire child fibre is blocked satisfy

    H_p(B_{q→p}) ≤ p^{(3−q)/2}/(p−1).                  (6)

For clarity, its cutoff is r=(q−1)/2: shallow child cylinders have total
unconditional mass at most (r−1)/(q−1), and the integrated deep sum is at most
p^{1−r}/[(p−1)(q−1)]. On a blocked fibre the deep sum is at least 1/(q−1).
This gives (6). Arbitrary original exponents and residues are included.

Writing a_p=1/(p−1), the exact subtree recursion and pure-power union bound
give, by induction,

    δ_p ≥ 1−a_p−a_p²                                  (7)

at every nonternary removed or retained vertex. The right side is at least
11/16 for p≥5, so the child-density premise of (6) is established recursively.
We may improve (7) by excluding primes known to lie in K from the child sum.

### A1. The five-vertex core contains 3, 5 and 7

Every removed prime is at least 11. Overcounting them by all odd integers
q≥11 gives

    δ_p ≥ D(p) := 1−1/(p−1)−1/[p³(p−1)²],             (8)

since Σ_{odd q≥11}p^{(3−q)/2}=1/[p³(p−1)]. In particular D(3)=53/108.
The function D increases with p. The ordered actual core primes dominate
(3,5,7,11,13), so Section 3 applies with these references and domains D(t_i).
The independent rational certificate gives

    R_4 < 273/25,           f_4 > 67/500.

Adjoining the fifth coordinate gives

    ν(R) > (67/500)(1−(273/25)/(12D(13)))
         = 504443/517862500 > 1/2048.                  (9)

### A2. The core contains 3 but misses 5 or 7

Let J⊆{5,7} be the nonempty set of those two primes absent from S. A valid
overestimate of all possible child-prime costs now gives

    δ_p ≥ d_J(p)
      := 1−1/(p−1)−[1_{5∈J}/p+1_{7∈J}/p²
                         +1/(p³(p−1))]/(p−1).          (10)

Under the actual product law, a complete original support T has total class
cost at most ∏_{p∈T} x_p, where x_p=a_p/δ_p. All exponents are summed and
all supports are retained, so the complete mixed-class cost is bounded by

    F(x_1,…,x_5)=∏_i(1+x_i)−1−Σ_i x_i.

Every coefficient of F is positive. Also
1/[(p−1)d_J(p)] decreases with p, because its denominator is p−2 minus a
positive decreasing function. The following reference cases therefore cover
all actual primes in their respective configurations:

| Missing primes J | Reference primes | Strict upper bound for F |
|---|---|---|
| {7} | 3,5,11,13,17 | 39/40 |
| {5} | 3,7,11,13,17 | 24/25 |
| {5,7} | 3,11,13,17,19 | 3/4 |

All three exact rational inequalities are in the independent certificate.
Their complements are greater than 1/2048.

### A3. Prime 3 is outside S, or absent entirely

If 3 occurs outside S, let q be its next vertex on the retained path to S.
Excluding q from the removed-child sum at 3 improves (7) to

    δ_3 ≥ 1/4+(1/2)3^{(3−q)/2}.

For p≥5 put

    z_p := a_p/(1−a_p−a_p²)
          = (p−1)/[(p−1)²−(p−1)−1].

The edge incident to 3 has total original-label cost at most

    z_q/[1/2+3^{(3−q)/2}] ≤ 24/55.                    (11)

For q=5 the bound is 24/55; for q=7 it is 108/319; for q≥11 it is at most
2z_11=20/89. This is an exhaustive partition of possible q.

The function z_p decreases with p, and z_p<1/(p−3). Summing exactly over
p=5,7,11,13,17,19,23 and bounding the remaining primes by 29,31,33,… gives

    Σ := Σ_{p≥5 prime}z_p²
       < Σ_{p∈{5,7,11,13,17,19,23}}z_p²+1/26²+1/52
       < 57/250.                                      (12)

After deleting 3, every retained vertex has degree at most four, except
possibly the junction of the path with S, which has degree at most five.
Thus 2ab≤a²+b² bounds all remaining edge costs by

    Σ_{edges pq}z_pz_q ≤ 2Σ+(1/2)z_5².

Every support of size at least three lies entirely in S. Since S contains
five primes at least 5, their total cost is at most

    T_5 := Σ_{j=3}^5 e_j(z_5,z_7,z_11,z_13,z_17),

where e_j is the elementary symmetric polynomial. Hence the complete mixed
cost is strictly less than

    24/55+2(57/250)+(1/2)z_5²+T_5
      = 1216679188913/1222229001125 < 249/250.          (13)

Its complement is greater than 1/2048. If 3 is absent, there is no added
path or ternary-edge cost, and the same displayed upper bound remains valid.
These arguments also allow a disconnected core: the degree and support bounds
apply to its complete retained graph, and the path to 3 lies in one component.

This exhausts every five-core configuration. If at most four total primes
occur, retain all of them. Their actual pure-power domains have densities at
least (p−2)/(p−1). The same profile recursion with the first n reference primes
among (3,5,7,11), n≤4, gives respectively the survivor-fraction bounds

    1, 2/3, 1/3, 58/405.

All are greater than 1/2048. The empty family has survivor mass one. This
also closes the small-total-prime case in the original at-most-five statement.

## 5. Theorem B: a five-prime core with cactus attachments

Use [the original cactus fee theorem, CA1–CA25](06b-arbitrary-odd-cactus-graphs-are-noncovering.md#arbitrary-odd-cactus-graphs-are-noncovering). Its descendant domains have density
at least 2/3.
For a child block, it supplies parameters λ,K and a cutoff r for which

    F_{p,r}(λ,K)
      = p^{1−r}λ/[(p−1)(1−K−(r−1)λ)]
      = [2/(p−1)](3/p)^{r−1} F_{3,r}(λ,K).

At parent 3, a bridge is charged to its child prime, and a cycle to one or
two distinct child primes. Different child blocks have disjoint child sets.
For child primes q≥11 the original fee is f(q)=2^{−(q−1)/2}; the theorem
supplies r≥2 because the smallest child prime is at least 11. Consequently
the root loss at any p∈S is bounded by

    [6/(p(p−1))] Σ_{charged outside primes q} f(q).     (14)

All off-core primes are at least 11. Descendant invariants below the retained
root are supplied by the already-proved cactus recursion, which includes all
triangle labels. The factor in (14) uses p≥3 and r≥2. No five-core reserve is
used recursively as a fee.

The five core primes cannot simultaneously be charged as outside primes.
Over all odd q≥11 the fee sum is 1/16. Removing the composite 15 gives the
valid prime-only upper bound 7/128. Thus these exhaustive pools suffice:

| Core configuration | References | Available fee pool ρ |
|---|---|---|
| u=11, v=13 | 3,5,7,11,13 | 1/128 |
| u=11, v≥17 | 3,5,7,11,17 | 3/128 |
| u≥13, v≥17 | 3,5,7,13,17 | 7/128 |

The first row sums all odd integers starting at 17. The second subtracts
f(11)=1/32 from 7/128. The third keeps the looser complete prime pool.
These are numerical upper bounds, so further excluded actual core primes
can only improve them.

For every actual retained p, the domain therefore satisfies

    δ_p ≥ d_ρ(p):=1−1/(p−1)−6ρ/[p(p−1)].              (15)

The same upper pool may be used for each retained root: each inequality
holds simultaneously for the same family, with no assertion that the worst
losses are simultaneously attainable. Since d_ρ increases with p, Section 3
applies at the listed references. The exact results are

| References | R_4 upper bound | f_4 lower bound | Resulting f_5 lower bound |
|---|---|---|---|
| 3,5,7,11,13 | 10931/1000 | 67/500 | 455667/571812500 |
| 3,5,7,11,17 | 12221/1000 | 23/200 | 8666837/407775000 |
| 3,5,7,13,17 | 12715/1000 | 109/1000 | 6717343/407475000 |

Each inequality is strict, and every final fraction exceeds 1/2048. The
independent program verifies every subset recurrence and every positive
conditioning denominator. In all four critical calculations, including A1,
the four-coordinate cutoff is (2,1,0,0), giving 48 exact infinite-tail cells.
A separate direct sum on 0≤e_i≤8 with a rigorous raw-support tail majorant
also lies below each displayed R_4 ceiling. Thus these calculations supply
parameters for the all-height proof, not bounded-height experiments.

## 6. Exact transport to original Haar mass

For retained p let W_p(x_p) be the exact probability, under original Haar
on the eliminated coordinates attached at p, that all assigned original
classes are avoided, multiplied by the indicator of pure p-power avoidance.
Then V_p={x_p:W_p(x_p)>0}. Disjoint private interiors give the exact identity

    H(full original avoiding set)
      = ∫_{X_K} 1_R(x_K)∏_{p∈K}W_p(x_p) dH_K(x_K).    (16)

Let Q_off=∏_{p∉K}p^{h_p}. Every x_K∈R has at least one full extension, so
∏W_p(x_p)≥1/Q_off on R. Also H_K(R)=ν(R)∏δ_p. Therefore both theorems give

    H(full original avoiding set)
      > (∏_{p∈K}δ_p)/(2048 Q_off) > 0.                (17)

This proves noncoverage. Replacing the W_p by indicators would retain only
existence and would not give the correct Haar mass. The conditional fraction
1/2048 in particular is not a summable bound for dead fibres of a parent
prime. It does not permit a five-core to be substituted for a child block in
the cactus or four-vertex-block recursion.

The independently constructed finite controls in
[the weighted AP control](../frontier/cover-geometry/five_core_weighted_ap_controls.py)
and its [exact data](../frontier/cover-geometry/five_core_weighted_ap_controls.json)
test (16) against a full original-period sieve:

| Original geometry | Original period | Distinct labels | Uncovered residues |
|---|---:|---:|---:|
| Five-prime core with ternary height two, plus tree edge 3–17 | 765765 | 50 | 151656 |
| Five-prime core with triangle attached at 5, including its triple label | 4849845 | 37 | 1198144 |

Every retained fibre is checked: respectively 45045 and 15015 fibre counts.
The actual product-domain reserves are 3287/4800 and 2159/2880; the full
Haar masses are 50552/255255 and 1198144/4849845. Both examples have effective
original five-prime labels, and the second has an effective original triple
label on the attached triangle. The JSON contains all literal labels,
domains, and extension weights. These finite controls check the exact
measure bookkeeping; the all-height assertions follow from Sections 3–5.

## 7. Structural consequence and remaining boundary

**Consequence.** A minimum-cardinality distinct odd whole cover, if one exists,
has at least six original prime vertices in its graph's 2-core.

Its prime graph must be connected: otherwise the original avoiding set is
the product of the component avoiding sets, and if that product is empty, one component is already a cover with
strictly fewer original classes. For a finite connected graph, deleting
the 2-core leaves trees singly attached to it when the core is nonempty. If
the core is empty, the graph is a tree; seed one original vertex as retained.
If a nonempty core has at most five vertices, retain it and apply A, enlarging
by adjacent tree vertices as in Section 2 if needed. In either case A gives
noncoverage. The at-most-four-total-prime base uses the ordinary P3–P5 profile
recursion, without assuming a kernel replay of an external eight-prime result.

This is a statement about the size of the graph's recursively pruned core,
not a claim that some original modulus must have six prime factors.

The inspected external theorem with at most three prime factors per original
modulus does not directly supply A or B: their core labels may have five
prime factors, while total prime support is unbounded. The repository's
four-prime-head theorem permits unrestricted larger support only from 67;
these statements permit smaller attachment primes but impose geometry.
The four-vertex-block theorem permits arbitrary repetitions of its small
blocks; these five-core results instead allow only trees or specified cactus
attachments. No comprehensive priority or domination claim is made.

The remaining general obstruction is unchanged in type: an arbitrary child
block needs a summable bound on the original parent words whose complete
actual fibre is blocked, under descendant invariants established below that
block. A positive joint five-core reserve alone does not give that estimate.
For shared two-prime interfaces one instead needs a compatible joint-relation
or kernel invariant. Neither unrestricted arithmetic closure is proved here.
