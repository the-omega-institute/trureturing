# A shared triangle tower preserves one common survivor law

Let P={3,5,7,11,13,17,19}. Consider any finite family of pairwise distinct
P-smooth numerical moduli greater than one, with arbitrary globally fixed
residues. Allow arbitrary pure-prime originals. Require every mixed modulus
to have one of the forms

    3^a*q^b,       a,b>=1, q in {5,7,11,13,17,19};
    3^a*5^b*7^c,   a,b,c>=1.

There is no bound on the family size or any exponent. Its complete actual
survivor U satisfies

    H(U)>=210595/2985984>0.

The ONE full-survivor law rho=H(.|U) belongs to the existing class G and has
complete nonunit query norm

    R_P(rho)<=2304369/210595<565/51.                    (ST1)

Arbitrary additional distinct originals touching 23 or 29, and otherwise
supported on P, preserve full Haar survivor mass at least

    365839/459841536>0.                               (ST2)

The new step extends [report547](547-all-height-stars-have-a-common-survivor-law.md)
from all star towers to one complete shared-support triangle tower. It keeps
the joint 5/7 avoidance on a three-level ternary boundary. Treating the
triangle as an independent seventh coordinate would not justify the bound.
These are ordinary arguments and exact finite computations, not Lean
verification or unrestricted Erdős #7.

## 1. Complete source and the all-height charge vectors

Fix one irredundant core with exactly the same full survivor U. All its
mixed labels still have the stated forms. Let S_p be its complete pure-p
survivor and define

    w_p=H_p(S_p), a_p=1/w_p,
    rho0=product_p H_p(.|S_p), Omega=product_p w_p.

The complete pure bounds give

    a_p<=(p-1)/(p-2), Omega>=935/4096.

Let ell be the union probability of all mixed core originals under THIS
rho0. The general actual-loss bridge SC1--SC3 of
[report541](541-shared-ternary-roots-certify-sixteen-mixed-heads.md) applies
once ell<173/250. It then puts the same uniform law on U in G and gives

    H(U)=Omega*(1-ell),
    R_P(rho)<=(4096/935-1)/(1-ell).                   (ST3)

Removed originals are unused numerical queries relative to the fixed core;
they have not been removed from the full query norm. No separate law is
chosen for different queries or ternary cells.

At any fixed positive ternary exponent r, sum all outside heights before
optimizing the ternary placement. For each star prime q the total charge is
at most u_q=1/(q-2). The triangle charge is at most

    sum_(b,c>=1) a5*a7/(5^b*7^c)<=1/15.

For r=1,2,3 distribute these actual charges among the ternary nodes v:

    x_(q,r,v)>=0, sum_v x_(q,r,v)<=1/(q-2);
    z_(r,v)>=0,   sum_v z_(r,v)<=1/15.               (ST4)

Every original contributes to its own fixed ternary node. Numerical
distinctness permits at most one original for each exponent tuple, which
is why each entire height sum is paid only once in ST4.

For a modulo-27 leaf j, let X_q(j) be the sum of its three ancestor star
charges and Z(j) the analogous triangle sum. In particular
0<=X_q(j)<=3/(q-2)<=1. Unite the star cylinders on each same q coordinate
first. The complement of the 5-stars and 7-stars has probability at least
(1-X5)(1-X7); the triangle union can remove at most Z from that same
rectangle. Therefore the actual low-depth outside avoidance is at least

    Cplus(j)=max(0,(1-X5(j))*(1-X7(j))-Z(j))
             * product_(q=11,13,17,19)(1-X_q(j)).    (ST5)

Only the four remaining independent prime coordinates are multiplied
against this joint 5/7 block. Set g(j)=1-Cplus(j). It lies in [0,1] and is
nondecreasing in every charge coordinate.

## 2. Every pure ternary mask reduces to two 14-cell trees

In the irredundant core the pure ternary cylinders are disjoint. The
possible originals at 3,9,27 remove at most one root, one middle node and
one leaf. Let J be the remaining modulo-27 leaves and N=|J|. All deeper
pure originals lie within these leaves. Their scaled deficits satisfy

    delta_j>=0, delta=sum_j delta_j<=1/2,
    rho3(j)=(1-delta_j)/(N-delta).

The complete geometric pure tail is used here: 27*sum_(e>=4)3^(-e)=1/2.
For any nonnegative coefficients g_j, the same deficit argument as in
report542 gives

    sum_j rho3(j)*g_j
      <=[sum_j g_j-(1/2)min_j g_j]/(N-1/2).          (ST6)

Regard this envelope as a weighted mean, with weight 1/2 on a minimum
cell and weight one elsewhere. If three roots remain, delete a root with
least weighted mean. If six middle nodes remain, delete a middle node
with least weighted mean. A retained half-weight cell keeps its weight;
if it was deleted, the new half-minimum envelope is at least the retained
uniform mean. Hence neither operation decreases the upper envelope.

After the root deletion there are five or six middle nodes and at most
one missing leaf. After the possible middle-node deletion there are five
middle nodes and 14 or 15 leaves. If 15 remain, delete a minimum leaf.
Writing S=sum g and m=min g, this last step is justified by

    (S-m)/(N-1)-(S-m/2)/(N-1/2)
      =(S-N*m)/[2*(N-1)*(N-1/2)]>=0.

At each deletion, move every charge supported entirely on the removed
block to a surviving node at the same depth. This respects all ST4 budgets
and can only increase the retained g values. Charges on surviving ancestor
nodes need not move. The comparison is performed on Cplus, before any
signed relaxation; its monotonicity is essential to this argument.
After charge moves, a retained half-weight cell need not still minimize g.
The new half-minimum envelope is at least that retained fixed-weight mean,
which is the domination required above.

Exactly two tree shapes remain, up to within-level symmetries:

    I:  (2,3) | (3,3,3);
    II: (3,3) | (2,3,3).                             (ST7)

Each parenthesis lists the leaf counts of one root's middle nodes. Both
shapes have two roots, five middle nodes and 14 leaves. These are dominating
comparison masks, not modified original families.

## 3. Signed joint avoidance and all off choices

On either 14-cell tree, replace Cplus by the smaller signed expression

    Clin(j)=((1-X5(j))*(1-X7(j))-Z(j))
             * product_(q=11,13,17,19)(1-X_q(j)).

All four outside factors are nonnegative, so Clin<=Cplus even when the
first factor is negative. The envelope ST6 is a maximum over positive
anchor weights. Consequently this replacement gives a valid upper bound
on deletion. Equivalently, minimize the anchored avoidance

    (1/2)*Clin(h)+sum_(j!=h) Clin(j).

For fixed anchor h it is separately affine in each of the 21 vectors
in ST4: seven role types at three depths. Each vector lies in a compact
simplex. Its vertices are zero and the placements of its entire cap on
one node. At a global minimum, successively replace each vector by one
of its minimizing vertices. The value remains globally minimal.

Thus each role at each depth is either OFF or placed wholly on exactly
one node. Saturation cannot be assumed: the signed objective need not be
monotone in every block.

Use role order E=(5,7,11,13,17,19,T), with T the triangle. For role masks
A,B,C at a leaf's three ancestors, put

    n_e=1_(e in A)+1_(e in B)+1_(e in C),
    D=3*5*9*11*15*17=378675,
    F(A,B,C)=((3-n5)*(5-n7)-nT)
               *(9-n11)*(11-n13)*(15-n17)*(17-n19). (ST8)

Then Clin=F/D. Negative leaf values are retained in the optimization.
Double all weights: an anchor leaf has weight one and every other leaf
has weight two. The resulting deletion bound is 1-W/(27D).

## 4. The exact optimizer and its six anchor orbits

For a middle node with leaf weights mu_i, define

    Node_mu(A,B,C)=min_(C=disjoint_union_i C_i)
                       sum_i mu_i*F(A,B,C_i).

For a root with those middle nodes, define

    Root(A,B,C)=min_(B=disjoint_union_i B_i,
                     C=disjoint_union_i C_i)
                       sum_i Node_i(A,B_i,C_i).     (ST9)

Finally minimize Root0(A0,B0,C0)+Root1(A1,B1,C1), requiring disjointness
at each depth but NOT requiring either union to fill E. Every global off
choice is included. Induction over leaves, middle nodes and roots proves
that ST9 examines exactly the extreme allocations from Section 3.

The implementation computes a subset minimum of the second root's table.
For each first-root triple it then reads that minimum on the three
complement masks. This includes all choices to leave any remaining role
off; it is not a saturation shortcut.

| Shape | Anchor location | Minimum including off | Minimum with all roles on |
| --- | --- | ---: | ---: |
| I | Two-leaf node in first root | 3510150 | 3510150 |
| I | Three-leaf node in first root | 3577860 | 3577860 |
| I | Second root | 3586365 | 3586365 |
| II | First root | 3676920 | 3676920 |
| II | Two-leaf node in second root | 3725466 | 3725466 |
| II | Three-leaf node in second root | 3748782 | 3748782 |

Here is one literal global minimizer. In shape I use
A0={a0,a1}, A1={a2,a3,a4}, B0={b0,b1,b2}, B1={b3,b4,b5},
B2={b6,b7,b8}, with anchor a0.

| Role | Depth 1 | Depth 2 | Depth 3 |
| --- | --- | --- | --- |
| 5 | B | B1 | b0 |
| 7 | B | B2 | b1 |
| 11 | A | A1 | a1 |
| 13 | A | A1 | a1 |
| 17 | A | A1 | a4 |
| 19 | A | A1 | a1 |
| T | B | B2 | b4 |

The leaf numerators in order a0,...,a4,b0,...,b8 are

    268800,198450,184275,184275,170100,
    75735,126225,176715,75735,50490,75735,
    100980,100980,100980.

Their anchored sum is 268800+2*1620675=3510150. All are positive, so
this same layout also attains the positive-part relaxation's minimum:
the signed lower bound and this positive feasible endpoint coincide.
This does not require all signed minimizers to have nonnegative leaves.
Neither relaxed optimum is asserted to be realized by actual originals.

It follows that the complete ternary depths one through three satisfy

    ell_(a<=3)<=1-3510150/(27*378675)=89521/136323.    (ST10)

## 5. Every deeper original and the one supported law

All remaining mixed labels have ternary height a>=4. Under the SAME
complete pure-product source their total saturated charge is bounded by

    star_tail <=(1/27)*sum_q 1/(q-2)=7244/227205;
    triangle_tail <=(1/27)*(1/15)=1/405.

The factor 1/27 is 2*sum_(a>=4)3^(-a), using the complete ternary pure
bound a3<=2. There is no cutoff on either outside exponent. Therefore

    ell<=89521/136323+7244/227205+1/405
        =8564/12393<173/250,
    173/250-ell>=2989/3098250>0.                      (ST11)

Substitute ST11 in ST3. This proves ST1, the Haar lower bound, and

    565/51-2304369/210595=1463356/10740345>0.

For the additional 23/29 originals, tensor this ONE rho with fresh Haar
coordinates. Their full labels d*23^j*29^k, j+k>0, retain arbitrary
P-smooth d and arbitrary phases. The unit old cofactor contributes one.
The complete union bound is

    added_loss <=(1+R_P(rho))*sum_(j+k>0)23^(-j)*29^(-k)
               <=(1+2304369/210595)*(51/616).

Thus the remaining relative mass is at least 365839/32431630. Multiplying
by H(U)>=210595/2985984 gives ST2. The old law is used once; ST1 is not
asserted for the newly conditioned extended survivor.

## 6. Verification and the remaining support boundary

The [standalone driver](../../frontier/cover-geometry/all_height_star_triangle_depth3.py)
compiles the adjacent [integer optimizer](../../frontier/cover-geometry/all_height_star_triangle_depth3.cpp)
and produces [exact data](../../frontier/cover-geometry/all_height_star_triangle_depth3.json).
The recurrence evaluates 143327232 middle-node candidates and 6122200320
root-convolution candidates, then includes the off states by subset minima.
Its 14 integer checks verify all six orbit values and both candidate counts.
The driver passes 21 exact checks and separately
checks all 598 disjoint pure3/9/27 masks, the two pruned shapes, the literal
global layout and every downstream fraction. All failures remain active
under Python optimization. A separately written integer optimizer reproduced
all six off-inclusive and saturated minima. The result SHA256 is
`f18e1107f0bac8e7c50b5a34bfc12a3bc4810139885fa6904de47bb5068e408d`.

The program requires a C++17 compiler, selected by CXX or defaulting to
c++, and the Python standard library. Compilation uses a temporary directory;
no binary is retained. No old producer, old data, original-period enumeration
or Lean build is used.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/all_height_star_triangle_depth3.py
```

The ordinary aggregation, mask domination, signed vertex reduction and
complete-tail arguments are needed in addition to the finite optimizer.
The base theorem excludes P-only mixed classes 5^b*7^c without 3 and
arbitrary additional P-smooth mixed supports. Such labels remain allowed
as cofactors of originals that genuinely touch23 or29 in ST2. Further
outside-prime supports are not covered. Uniform
common-law control for those original families, and unrestricted Erdős #7,
remain unresolved.
