[Index](../../marked_head_profile.md) · [Complete layout duality](400-literal-layout-mixtures-and-exact-tree-rank-duality.md) · [Separate-depth loss](423-exact-roots-do-not-repair-separately-maximized-depth-tails.md)

# Layout rank need not respect the target increment at each height

A mixture of seventeen complete original layouts has tree rank 243/100
at height one and 89/25 at height two. Its rank increment exceeds the
target increment 10/9 by exactly 17/900. The old and new costs come from
the same mixture, retaining every old load and its correlation with both
new phases. Thus exact layout information does not make the proposed
scalar rank-increment inequality true.

A separate, valid one-step upper bound retains seven fields of costs and
conditional increment budgets on the parent prefixes. Its proof applies
to every mixture of original layouts. A four-layout example also shows
why that bound alone does not establish the global target in report 400:
replacing the positions of seven child increments by their total budget
can lose enough information to exceed the target.

These are repository-derived counterexamples and an elementary analytic
interface using the existing tree-rank and conditional-layout machinery.
No literature-originality or Lean-certification claim is made. Neither
counterexample refutes the global source inequality or unrestricted
Erdős #7.

## The exact rank and the fixed-increment assertion

For h>=0 let X_h={1,2,3,4} times Z/7^h. Original labels are all
7^j and 5*7^j, 0<=j<=h, each with its own independently selected residue;
the labels 1 and 5 are included. For a literal layout lambda put

    ell_lambda(r,y)=sum_(d | 5*7^h) [x(r,y)=a_d mod d],
    f_theta(r,y)=E_(lambda~theta) ell_lambda(r,y)^2.

Here x(r,y) is its CRT representative modulo 5*7^h, and theta is a
probability on whole layouts. For a real function g on Z/7^h define

    U_b^h(g)=max_(complete b-ary trees T of height h) min_(y in T) g(y).

Trees read the lowest seven-adic digit first. At an internal node U_b
takes the b-th largest of the seven child values. At height zero it is
the sole leaf value. With

    G={ (A,3): A subset {1,2,3,4}, |A|=2 }
          union { ({1,2,3,4},5) },

report 400's rank is

    B_h(f)=min_((A,b) in G) U_b^h(y -> max_(r in A) f(r,y)).     (P1)

The target is 2t_h=6-2(h+2)3^-h. Report 400 identifies the universal
admissible-source inequality with B_h(f_theta)<=2t_h for every theta.

For a mixture theta at height K>=1, delete its last two phases to obtain
its actual marginal mixture theta^- at height K-1. A sufficient induction
would be the assertion

    B_K(f_theta) <= B_(K-1)(f_(theta^-))+2(2K+1)3^-K.           (P2)

Indeed the final term is 2t_K-2t_(K-1), and B_0<=2 for every layout
mixture: the height-zero row costs are 1+3Pr(a_5=r), and their third
largest is at most two. P2 is false already for K=2.

## A complete literal counterexample

The following are the integer weights and all six original phases,
ordered by moduli (1,5,7,35,49,245). Divide the weights by 100.

| Weight | a_1 | a_5 | a_7 | a_35 | a_49 | a_245 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 0 | 2 | 3 | 17 | 4 | 53 |
| 3 | 0 | 2 | 1 | 22 | 29 | 29 |
| 1 | 0 | 2 | 0 | 7 | 0 | 98 |
| 9 | 0 | 1 | 1 | 18 | 25 | 123 |
| 10 | 0 | 1 | 2 | 18 | 11 | 158 |
| 4 | 0 | 2 | 0 | 28 | 21 | 168 |
| 5 | 0 | 2 | 1 | 29 | 29 | 29 |
| 4 | 0 | 2 | 1 | 29 | 1 | 99 |
| 3 | 0 | 1 | 0 | 14 | 28 | 224 |
| 8 | 0 | 1 | 1 | 8 | 22 | 218 |
| 8 | 0 | 2 | 3 | 18 | 4 | 53 |
| 1 | 0 | 2 | 3 | 18 | 25 | 123 |
| 10 | 0 | 2 | 3 | 18 | 18 | 18 |
| 10 | 0 | 1 | 2 | 18 | 32 | 228 |
| 4 | 0 | 1 | 1 | 1 | 1 | 99 |
| 8 | 0 | 1 | 0 | 28 | 0 | 168 |
| 10 | 0 | 2 | 0 | 14 | 0 | 224 |

Every phase is in its indicated residue range. The old mixture uses
the first four entries of every row with exactly the same probability.
Direct evaluation of the complete 28-point old carrier and 196-point
new carrier gives the seven terms in P1:

| Row set A | b | Old term | New term |
| --- | ---: | ---: | ---: |
| 12 | 3 | 359/100 | 363/100 |
| 13 | 3 | 89/25 | 91/25 |
| 14 | 3 | 89/25 | 89/25 |
| 23 | 3 | 359/100 | 91/25 |
| 24 | 3 | 359/100 | 363/100 |
| 34 | 3 | 243/100 | 89/25 |
| 1234 | 5 | 64/25 | 89/25 |

Consequently

    B_1(f_(theta^-))=243/100,
    B_2(f_theta)=89/25,
    B_2-B_1=113/100=10/9+17/900.                 (P3)

These are exact ranks, not separate maxima of squared-load shells.
They satisfy B_1<4 and B_2<46/9, so P3 does not violate the global target.
It shows that an old-level deficit below its target can be consumed at
the next level; an induction cannot require the target increment itself
to bound every actual mixture's rank increment.

The program below checks P3 twice. One calculation forms CRT integers,
evaluates original congruences, and contracts by b-th-largest values.
The other uses row/prefix indicators and tests every candidate value by
Boolean superlevel-tree contraction. The complete cost tables and all
seven ranks agree. No optimizer is part of either verification.

## A valid parent-prefix recurrence for arbitrary mixtures

Fix K>=1 and an arbitrary whole-layout mixture theta. Let z denote an
entire old layout, alpha_z its marginal probability, and A_z(r,u) its
old load at row r and parent prefix u in Z/7^(K-1). These loads are
nonnegative and are constant on each of that parent's seven children.
Write

    f^-(r,u)=sum_z alpha_z A_z(r,u)^2.

The new pure phase has a full prefix Y_P in Z/7^K. The new mixed phase
has row R_M in {0,1,2,3,4} and full prefix Y_M in Z/7^K. Define the
unnormalized joint probabilities

    q_z(y)=Pr(old=z, Y_P=y),
    v_z(r,y)=Pr(old=z, R_M=r, Y_M=y),
    h_z(r,y)=Pr(old=z, R_M=r, Y_P=Y_M=y).         (P4)

Thus sum_y q_z(y)=sum_(r,y) v_z(r,y)=alpha_z. They are taken from this
same actual joint distribution; unrelated feasible marginal arrays are
not substituted. Report 400 supplies a realizability criterion when
such arrays are given directly.

For y above parent u, expansion of the last two indicators gives exactly

    f^+(r,y)-f^-(r,u)
      =sum_z [(2A_z(r,u)+1)(q_z(y)+v_z(r,y))+2h_z(r,y)].         (P5)

Every increment is nonnegative. Aggregate only the new full prefixes
inside a specified parent:

    Q_z(u)=sum_(y=u mod7^(K-1)) q_z(y),
    V_z(r,u)=sum_(y=u mod7^(K-1)) v_z(r,y),
    H_z(r,u)=sum_(y=u mod7^(K-1)) h_z(r,y).       (P6)

The last quantity retains coincidence at the **same full child prefix**.
Agreement merely at the parent does not contribute to H.

For each of the seven (A,b) in G put

    a_A(u)=max_(r in A) f^-(r,u),
    W_A(u)=sum_z [
        (2 max_(r in A) A_z(r,u)+1) Q_z(u)
        +sum_(r in A)(2A_z(r,u)+1)V_z(r,u)
        +2sum_(r in A)H_z(r,u)].                 (P7)

Then the following upper bound holds for every such theta:

    B_K(f^+)
      <=min_((A,b) in G) U_b^(K-1)(u -> a_A(u)+W_A(u)/b).      (P8)

For the proof fix A,u, and index its children by c=0,...,6. Put
delta_r(c)=f^+(r,u+c7^(K-1))-f^-(r,u). By P5 and nonnegativity,

    sum_c max_(r in A) delta_r(c) <= W_A(u).     (P9)

For the pure part of each summand, replace its coefficient by the maximum
old load over A. For the mixed and coincidence parts, bound their row
maximum by the sum over rows in A. Sum over c and z to obtain P9.
No independence or interchange of a maximum with an expectation as an
equality is used.

Each child row maximum is at most a_A(u)+max_r delta_r(c). Since the
seven latter increments are nonnegative, their b-th largest is at most
their sum divided by b. Therefore the last-level contraction is bounded
by a_A(u)+W_A(u)/b. The remaining K-1 tree contractions are monotone;
applying them, and then taking the minimum over the seven groups, proves P8.

P8 preserves the dependence of the increment budgets on each complete
old load table and on its true joint extension probabilities. It is a
sufficient bound with seven different parent-prefix fields, not a scalar
update of B_(K-1). It uses the existing tree-rank recursion and elementary
nonnegative order-statistic bound, rather than asserting a new foundational
tree theorem.

On the seventeen-layout mixture above, the right side of P8 is exactly
89/25, attained by its row-pair 14 branch and its all-four-row branch.
Thus this interface controls that example sharply while the scalar
fixed-increment rule fails.

## Concentration in one child limits the parent-budget bound

At K=1 take four layouts of probability 1/4. For r=1,2,3,4 choose
a_5=r, a_7=0, and choose a_35 by CRT to have row r and column zero.
The divisor-one phase is zero. The old height-zero cost is 7/4 in every
row. The new cost is seven in column zero and 7/4 in every other column.
Consequently every term of P1, old and new, equals 7/4.

For a pair A, its pure contribution in P7 is four: the old load maximum
over A is two in half the layouts and one in the other half. The mixed
and coincidence contribution is 7/2. Hence

    a_A=7/4,       W_A=15/2,
    a_A+W_A/3=17/4.                             (P10)

For all four rows, the corresponding numbers are a_A=7/4 and W_A=12,
giving a_A+W_A/5=83/20. The right side of P8 is thus

    83/20>4=2t_1,

although the exact new rank is only 7/4. All new increments occupy the
same child. Their total divided by b discards this concentration and is
too large to certify the target.

This is a limitation of the upper bound P8, not a failure of its validity.
The valid conditional extension formula P5, the fixed-increment
counterexample P3, and the concentrated-child example separate the invalid
fixed increment for the old scalar rank from the loss caused by replacing
the seven new child increments by one parent total.
No uniform bound by 2t_K for the right side of P8 is asserted.

## Exact reusable verification

[`layout_rank_prefix_step.py`](../../frontier/cover-geometry/layout_rank_prefix_step.py)
retains all seventeen complete layouts and their integer weights. It exposes
literal-mixture validation, both independent cost evaluations, both tree-rank
checks, and the parent-prefix bound for arbitrary finite rational mixtures.
Its controls verify the exact seventeen-layout ranks and 17/900 violation,
the four-layout concentration example, row-zero mixed phases, and distinct
new children sharing a parent. Invalid masses, inexact weights and invalid
phases are rejected by explicit exceptions, including under `-O`.

It needs only the Python 3 standard library, imports no repository module,
does not depend on the current directory, and writes no files. Run:

    python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/layout_rank_prefix_step.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/layout_rank_prefix_step.py

The finite counterexamples are verified by complete exact computations.
The universal validity of P8 is supplied by the analytic proof P4--P9.
Report 400's global inequality for all whole-layout mixtures remains open.
