[Index](../../marked_head_profile.md) · [Joint retained square](245-the-actual-j-survivor-mass-and-h-column-sharpen-the-complete-square.md) · [J prime-path caps](248-the-complete-j-factorial-tail-retains-both-prime-paths.md) · [Complete square partition](241-one-original-j-head-controls-complete-square-and-factorial-moments.md)

# Two complete prime-path blocks sharpen the J square

On both entire actual saturated J faces, every independently labelled
complete original357 test A satisfies

    integral A^2 dmu <=5509/1200=4.590833333333... .       (QS1)

This improves245's5539/1200 by1/40. The measure is the same actual
unnormalized survivor mu of mass3/20. The complete mean16/25 and
factorial bound6313/7200 remain available from241 and248, respectively.
The square improvement replaces two disjoint complete blocks in one
original layout; every other layout and every infinite tail is retained.

A full52-cost comparison must be recomputed by a separate consumer.
This result does not assert an off-face theorem, actual attainment,
Lean verification or an unrestricted Erdos7 resolution.

## One original head and two disjoint square blocks

Retain245's original controlling layout and six-label head

    ell=(r3,c9,s5,r15,s15,c45,s45)=(1,4,2,1,2,4,2),
    B=1+I3+I9+I5+I15+I45.

Write the complete test as A=B+O+Z, where O is the old tail outside
those six labels and Z consists of all positive-seven labels. Inside O
put

    R3=sum_(a>=3) I_(3^a),
    R5=sum_(b>=2) I_(5^b).

The replaced blocks are precisely

    X3=integral(2B*R3+R3^2) dmu,
    X5=integral(2B*R5+R5^2) dmu.                       (QS2)

They consist of different terms of the square expansion. The mixed
term2R3*R5, all other old-old terms, all old/positive-seven terms and
the complete positive-seven square remain. The single-label diagonals
inside R3^2 and R5^2 belong to(QS2), not to a second remainder payment.

The retained head-square bound is245's unchanged exact joint result

    integral B^2 dmu <=2593/1800.                       (QS3)

Its101-variable model keeps the raw source, actual survivor, both
complete projected deletion families and exact source-free H column.
The canonical checker reconstructs that entire model and verifies its
same rational dual in every101 column. Its late coordinate is a true
LP variable and covers the whole interval[1/135,1/90].

## The original source supplies weighted crosses and density caps

Use241's normalized deep-three table p(c,s), absolute descendant-five
table d(c,s) and retained density w(c,s). With the same B throughout,

    A3_c=sum_s p(c,s)*w(c,s)*B(c,s),
    A5_s=sum_c d(c,s)*w(c,s)*B(c,s).                   (QS4)

For this controller the exact coefficient vectors are

    A3=(18/25,53/100,11/25,31/25,93/50),
    A5=(0,1/9,4/3,8/9,49/90).

These coefficients bound integral B times each deep test cylinder
in its own cell or first-five slot. The normalized p table is not
replaced by the smaller absolute raw-source cap table.

The cell and slot density caps proved in248 are

    c3=(11/20,2/5,1/5,2/5,2/5),
    c5=(0,1/10,29/90,13/30,4/15).                     (QS5)

Thus a pure-three cylinder of depth a>=3 in cell c has surviving
mass at most c3_c*3^-a. A pure-five cylinder of depth b>=2 in slot s
has mass at most c5_s*5^-b. These are original-survivor caps on both
whole J faces. They retain the first beta source cell, source-slot
exclusions and distinct saturated forbidden deletions; no K-domain
numerical bound or forced27 condition is imported.

## A complete discounted bound allows the path to change

At one prime p, let j denote the cell or slot chosen by the current
original label. Earlier labels assigned to other cells or slots are
disjoint from it. An intersection with any earlier label assigned to j
is either empty or contained in the current deeper cylinder, so its
mass is at most c_j*p^-depth. No nesting or shared residue between
original labels is assumed.

If n_j is the number of earlier labels assigned to j, the new term
in2BR+R^2 is therefore bounded by

    p^-depth * [2A_j+c_j+2c_j*n_j].                   (QS6)

The c_j term pays its diagonal once;2c_j*n_j pays both orders of its
pairs with earlier labels. Define r=1/p, a_j=2A_j+c_j, d_j=2c_j and

    V_j(n)=(a_j+d_j*n_j)/(1-r)+d_j*r/(1-r)^2,
    V(n)=max_j V_j(n).

For a choice k, the k component satisfies the exact identity

    a_k+d_k*n_k+r*V_k(n+e_k)=V_k(n).

Every other component is unchanged by n->n+e_k, and

    a_k+d_k*n_k <=(1-r)*V_k(n).

Consequently, for every choice k,

    a_k+d_k*n_k+r*V(n+e_k)<=V(n).                    (QS7)

Iteration bounds every sequence of independently changing cells or
slots. The terminal discounted potential is O(N*r^N), tending to zero.
Multiplying by the first-depth factors3^-3 and5^-2 gives

    X3<=Q3=max_c(A3_c+c3_c)/9,
    X5<=Q5=max_s(A5_s/10+3c5_s/40).                  (QS8)

The checker verifies the constant and count coefficients of the
Bellman identity and the nonnegative unchanged-component slack.
These affine checks apply to every count, not a finite sample of paths.

## Remove and replace each complete old block exactly once

In245's inherited241 partition, the old cross contributions for(QS2)
were max A3/9 and max A5/10. Its complete square-tail partition included
both unordered-pair subseries twice and restored every diagonal.
The precise removed terms are

| Block | Twice the head cross | Ordered distinct pairs | Diagonal | Old total | New total |
| --- | ---: | ---: | ---: | ---: | ---: |
|Pure3|31/150|11/360|11/360|241/900|113/450|
|Pure5|2/15|13/1200|13/600|199/1200|63/400|

For example the pure-three ordered distinct series is

    (11/20)*sum_(a>=3)2(a-3)*3^-a=11/360,

and its diagonal is(11/20)*sum_(a>=3)3^-a=11/360.
The corresponding pure-five values are13/1200 and13/600.
These match the original241 tail's two named pure-prime pair subseries
and its old diagonal decomposition. Hence the exact changes are

    Delta3=113/450-241/900=-1/60,
    Delta5=63/400-199/1200=-1/120.                    (QS9)

All other old diagonals, all other ordered distinct pairs and the
entire positive-seven diagonal remain nonnegative. The checker
reconstructs the complete241 tail5947/3600 before removing precisely
the four entries in the two middle columns above. Adding(QS8) to the
remaining old crosses, remaining complete tail and(QS3) gives, at
either late endpoint, exactly the old complete controller plus(QS9).
This is a replacement inside the original square expansion, not a
saving deducted from a separately optimized downstream comparison.

Both Delta terms are independent of theta. The unchanged positive-seven
raw cross is a sum of maxima of affine functions of the one common theta,
so its endpoint maximum bounds the whole interval. Combining with the
uniform joint head(QS3) yields

    controller upper=5539/1200-1/60-1/120=5509/1200.     (QS10)

## Complete layout coverage and tail scope

The pinned245 result already checks all12,500 original layouts. Its
complete bound for the other12,499 layouts, excluding precisely ell,
is

    16439/3600 <5509/1200,
    5509/1200-16439/3600=11/450.                       (QS11)

The new helper directly consumes that checked complementary-layout
result and its complete component digest; it does not rerun245's full
layout scan. It recomputes the original controller, both endpoint
crosses, the101-column dual, both path blocks and the complete tail
partition. Equation(QS11) then supplies the remaining layouts without
assuming that a controller found on a sample is globally maximizing.

All original test residues remain independent. Monotone convergence
extends the nonnegative finite expansions to complete tests. For varying
finite-source approximants, the uniform original-cylinder bounds dominate
omitted ordered pairs by convergent polynomial-geometric series, as in241.
The new two prime-path blocks retain all depths; their omitted remainders
are O(sum_(a>N)a*3^-a) and O(sum_(b>N)b*5^-b). The root1 permutations
and root0 exchange transport sources, tests and deletions together, giving
both whole J orientations and the inherited limiting-face interpretation.

The [canonical helper](../../frontier/j-geometry/j_face_pure_path_square.py) and
[certificate](../../certificates/source_norms/j-geometry/j_face_pure_path_square.json)
pin245,248 and their full mathematical input closures. Every calculation
uses standard-library exact rational arithmetic, including under -O.
The factorial result6313/7200 is reused from248 without a new factorial
argument or a square-to-factorial substitution.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-geometry/j_face_pure_path_square.py --check
```
