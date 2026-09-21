# 04b. Arbitrary star-head residues with unrestricted tails

These are ordinary mathematical noncoverage deductions, supported by exact
arithmetic. Their analytic inputs are Schroeder's conditional comparison
and the BBMST continuation used in [04](04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md) (US1--US12). The published inputs are [Schroeder, Section 3](../../../../Library/Arith/schroeder2026noncoverage.md) and [BBMST, Theorem 6.1](../../../../Library/Arith/balister2018covering.md). They
are not end-to-end Lean proofs, unrestricted Erdős #7, or a claim of
public-literature originality.

## Two concrete noncoverage theorems

Let a finite family have pairwise distinct odd numerical moduli greater
than one. Let P contain 3 and all primes at most 73 occurring anywhere
in the family, and contain only odd primes at most 73. Set

    Q = product_{p in P} p^{H_p},

where every H_p >= 1 resolves every original exponent, including head
factors in later-ending classes. An unused coordinate may be padded.
The original head labels are those whose modulus divides Q. Missing
head moduli are permitted. For these labels, either of the following
conditions suffices to prove that the whole family does not cover:

1. All original head labels with modulus not divisible by 27 have their
   canonical star residues. Labels with modulus divisible by 27 have
   completely arbitrary residues.
2. All original head labels having fewer than four distinct prime factors
   have their canonical star residues. Labels having at least four
   distinct prime factors have completely arbitrary residues.

In either case, all tail-containing original labels have arbitrary
residues, exponents, supports and interactions. Their tail primes exceed
73, and their number is unrestricted. Neither conclusion bounds the
original finite heights or the number of reassigned head labels.
The two conditions are alternative sufficient hypotheses; their union
of freely changeable labels is not claimed to obey the same budget.

## The fixed reference law and its actual head loss

On X_p = Z/p^{H_p}Z, define

    F_{p,e} = {x_p = p^{e-1}-1 mod p^e},
    C_{p,e} = {x_p = 2p^{e-1}-1 mod p^e},
    C_p = union_{e=1..H_p} C_{p,e},
    D_p = X_p minus union_{e=1..H_p}(F_{p,e} union C_{p,e}).

The canonical star class is F_{p,e} at pure powers, C_{3,i} x C_{p,j}
at modulus 3^i p^j with p >= 5 and i,j >= 1, and zero modulo every
other mixed head modulus. Define these reference classes on the complete
divisor set even when some original head labels are absent.

Use the actual finite product law

    nu_b = Unif(C_3) tensor product_{p in P minus {3}} Unif(D_p).

It avoids every reference star class. Let A_H be the ACTUAL original
head forbidden union, including the reassigned labels, and put

    epsilon = nu_b(A_H).

The common sufficient condition proved below is epsilon <= 9/20. This
does not assert that an arbitrary original head satisfies that inequality.

The supports have coordinate Haar densities

    s_3 = (1-3^{-H_3})/2,
    s_p = (p-3+2p^{-H_p})/(p-1), p >= 5.

Every actual depth-e coordinate cylinder consequently has probability
at most p^{-e}/s_p under the reference law. In particular the genuine
finite ternary cap is 2*3^{-e}/(1-3^{-H_3}), not 2*3^{-e}. The finite
auxiliary ternary height is increasing-convex dominated by the infinite
height with tails 2*3^{-e}, by the existing US3 argument: its convex
increment expectation is the weighted average over the first H_3
increasing increments, while the infinite law includes all increments.
Both auxiliary heights have mean one. This replacement occurs after
the conditional comparison creates independent auxiliary coordinates.

For p >= 5 the infinite auxiliary cap is (p-1)/(p-3). Thus the initial
comparison profile is exactly the one used for the complete-star law,
regardless of whether the actual original head avoids nu_b.

## Same-law tail processing with the head loss paid once

For each tail prime q, at its full original height, let U_q be uniform
on the actual pure-q-power survivors. Distinct original moduli imply
their total Haar mass is at most 1/(q-1), so U_q is a probability.
Given the entire earlier history x, let B_q(x) be the union of the
actual q-ending mixed cylinders and alpha_q(x) = U_q(B_q(x)).

Use delta = 2/5 and the US4 kernel, of density

    1/(1-min(alpha_q,delta)) off B_q,
    (alpha_q-delta)_+/(alpha_q(1-delta)) on B_q,

where the second expression is zero when alpha_q = 0. This kernel
normalizes on every full-history row, including alpha_q = 1, without
requiring that the earlier history survived the original head. Its
conditional cylinder caps are

    (q-1)/[(q-2)(1-delta)] * q^{-e}.

Start from nu_b and keep the normalized physical law. Each later kernel
preserves every earlier marginal, so A_H continues to have probability
exactly epsilon. No head or intermediate tail-survival conditioning is
performed during these steps.

Retain each original q-ending label as d*q^e with its own actual old
cylinder. The weights w_e = (q-1)q^{-e} have sum at most one for each
fixed old cofactor d, using uniqueness of the original full modulus
(d,e). Repeated projected cofactors are allowed. The unit cofactor is
absent from this mixed load because pure powers have been handled by U_q.
Schroeder's conditional comparison, followed by the same finite-ternary
convex-order argument, gives

    P(B_q) <= b_q
      = E[D_q-1-(q-2)delta]_+ / [(q-2)(1-delta)],

where D_q is the product of the independent old auxiliary factors 1+K_p.
The same comparison for every complete original test layout gives

    E L^2 <= J_B
      = product_{3<=p<=B prime}(1+c_p(3p-1)/(p-1)^2),

with c_3=2 auxiliary-only, c_p=(p-1)/(p-3) for 5<=p<=73, and
c_p=5(p-1)/(3(p-2)) for p>73. Absent prime factors may be included
as unused coordinates: they only increase the comparison loads.

Neither derivation uses initial avoidance of A_H. Both hold for this
same unconditioned physical law, with actual full-family heights and
original label provenance intact.

Let E_B avoid A_H and all actual tail labels ending at primes at most B.
Pure-tail exclusions have probability zero. By the union bound and
prefix-marginal preservation,

    lambda = P(E_B) >= 1-epsilon-C_B,   C_B = sum_{73<q<=B} b_q.

Every complete layout includes the unit divisor, so L^2>=1 everywhere.
Condition ONCE on E_B. Whenever the displayed lower bound is positive,
the resulting actual supported law simultaneously satisfies

    Gamma <= 1+(J_B-1)/lambda
           <= 1+(J_B-1)/(1-epsilon-C_B).                (1)

No independent optimization of a source, charge or square has been
combined here. In particular the extra head loss does not alter the
preconditioning C_B or J_B estimates.

## Exact stop at B = 16384

The prime list through B has global length 1900 and last prime 16381.
There are 1879 processed tail primes above 73. The exact program uses
the existing US directed product-state arithmetic with scale 10^18
and retained states 1<=d<=6553. For each auxiliary multiplier f=1+K_p,

    P(f=1)=1-c_p/p,
    P(f>=2 has value f)=c_p(p-1)/p^f.

Every atom and every nonnegative convolution sum is rounded upward.
Thus the stored low-state probability weights dominate the true weights
by induction. A larger multiplier cannot contribute to a retained
product state because all multipliers are at least one.

The exact full mean and square moment factors are propagated separately,
also upward. No high-exponent mass is discarded from either moment.
At q the positive-part calculation uses

    E(D-T)_+ = E D-T + sum_{d<=T}(T-d)P(D=d),
    T = 1+(q-2)delta = (2q+1)/5.

All approximated quantities on the right have nonnegative coefficients.
The largest queried integer state is 6552, within the retained 6553.
This proves the direction of every b_q upper bound. The program yields

    C_B <= 55386439412229727/125000000000000000,
    J_B <= 4344363876475156387651/500000000000000000.

At epsilon=9/20, equation (1) therefore gives

    Gamma <= 4343917330717507468743/53454242351081092
          = 81264.22038099756... .

A short rational lower bound suffices for the BBMST stopping threshold.
For x>=1 write t=(x-1)/(x+1); every partial sum of
2 sum_{j>=0} t^{2j+1}/(2j+1) is a lower bound for log x.
Three terms give log2>=842/1215. Hence

    log1900 = 10log2+log(475/256)
      >= 10*842/1215 + 2*(219/731+(219/731)^3/3)
      = 716376267476/94920147513 > 377/50 > 15/2.

Consequently

    loglog1900 >= log(15/2) = 2log2+log(15/8)
      >= 2*842/1215 + 2*(7/23+(7/23)^3/3)
      = 29765348/14782905 > 201/100.

The bracket 377/50+201/100-3=131/20 is positive, so

    1900(log1900+loglog1900-3)^2
      > 1900(131/20)^2 = 326059/4 = 81514.75.

The exact difference between this lower bound and the Gamma upper bound
is 3347967742569993841/13363560587770273 > 0. The actual supported
law thus meets BBMST Theorem 6.1's stopping criterion. Continue beyond
this point with that theorem's standard uniform-base kernels, not by
assuming the earlier pure-survivor bases for the continuation. Global
index 1900 includes 2 and absent primes. The initial head heights and
processed prime heights still resolve all later original cofactors.

If the family ends earlier, its already positive avoiding mass suffices.
Otherwise BBMST continuation retains positive mass through all remaining
original prime stages. Finite CRT yields an integer avoiding every
original label. This proves the common condition epsilon<=9/20.

## The two original-label head budgets

For the first head class there is nothing to pay if H_3<3. Otherwise,
original-modulus distinctness and the product cylinder caps bound the
actual union of all reassigned head classes by

    epsilon <= [sum_{e=3}^{H_3} 3^{-e}/s_3]
       product_{p in P minus {3}}[1+sum_{j=1}^{H_p}p^{-j}/s_p].

The actual finite ternary factor is

    (3^{-2}-3^{-H_3})/(1-3^{-H_3}) <= 1/9.

Each other factor is at most (p-2)/(p-3). Adding omitted primes increases
the upper bound, and exact arithmetic gives

    epsilon <= (1/9)product_{5<=p<=73 prime}(p-2)/(p-3)
      = 27291063632391/67345087201280
      = 0.4052420861944075... < 9/20.                 (2)

All exponents and all prime supports are included. The remaining
canonical original head labels have zero probability under nu_b.
This proves the first concrete theorem.

For the second class, sum coordinate caps over positive exponents:
the ternary sum is exactly one at EVERY finite H_3>=1, while the sum at
p>=5 is at most 1/(p-3). Therefore the coefficient of z^k in

    P(z)=(1+z)product_{5<=p<=73 prime}(1+z/(p-3))

bounds the total cap weight of original head moduli with exactly k
distinct prime factors. The constant choice in (1+z) explicitly includes
supports without 3. For each support its positive-exponent sum includes
all original heights; labels of the same support remain separate by
their exponent vectors. Uniqueness is used only for original full moduli.
It follows that

    epsilon <= sum_{k>=4}[z^k]P(z)
      = 288440010638780744436573/670918019074091909120000
      = 0.4299184139320713... < 9/20.                 (3)

This proves the second concrete theorem. The analogous envelopes for
all multiples of 9 or all supports of size at least three exceed 9/20;
these estimates alone give no conclusion for those next larger classes.
This is not a statement that their actual bad mass exceeds the budget.

## Actual examples and the remaining boundary

The first class strictly enlarges star geometry. On head period 27*25,
take every canonical head label and change only the pure-27 residue from
8 to 1. The mixed-15 residue remains 1. These two classes are disjoint
before the change and intersect afterward. Their labelled intersection
relation cannot be changed by a coordinate-tree relabelling. The actual
reference branch has 169 points; 13 are hit by the changed head class,
so epsilon=1/13. Arbitrary tails above 73 remain covered by the theorem.

For the second class, use squarefree head period 3*5*7*11=1155 and keep
all proper head labels canonical. Change the full-period residue from
zero to 772, whose residues are 1 modulo3 and 2 at the other three
primes. The reference branch has 135 points and precisely one is hit.
This head is admitted by the four-prime-support theorem and is not in
the multiples-of-27 class. The pure-27 change has support one and gives
the converse separation of the two sufficient head conditions.

No bound is proved here for the reference bad mass of an arbitrary head.
The unresolved structural task is to obtain a sufficient actual source
and a small enough original-head forbidden union beyond these classes.
The full-cover cut identities of Reports 340/342 are unchanged; cut
normalization alone still does not supply a new reciprocal gap.

The [exact checker](../frontier/source-budgets/star_head_perturbation.py) independently rebuilds the complete prime
list, all 1879 charges and the final moments, verifies the short rational
logarithm lower bounds and the two head budgets, and enumerates both
literal original-label examples. All checks remain active under -O.
The arbitrary-family comparison and analytic continuation are the
ordinary proof inputs above, not conclusions of finite enumeration.

The checker uses the existing directed `star_block/stoploss.py` API and
retains a small exact result in
[star_head_perturbation.json](../certificates/source_norms/source-budgets/star_head_perturbation.json).
It binds this proof, the US supplier, the arithmetic API and the two
literature entries. Reproduce it with

    python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/star_head_perturbation.py --check

## Automorphic reference laws and exact coordinate responses

This is ordinary finite mathematics, not a Lean result or a resolution of
unrestricted Erdős #7. It uses the arbitrary-head continuation criterion proved above. Original numerical moduli and residues remain the
actual data; optimization moves only the reference law.

### 1. The full rooted-tree orbit has an exact one-coordinate recurrence

Identify Z/p^H Z with the leaves of the depth-H rooted p-ary tree, with
least significant digits read first. A rooted-tree automorphism permutes
children independently at every node. It preserves Haar measure and maps
every depth-e congruence cylinder to another depth-e cylinder.

The canonical C_H is the union, over e=1,...,H, of the cylinders
2p^(e-1)-1 mod p^e. The canonical D_H is the complement of those cylinders
and p^(e-1)-1 mod p^e. C_H is used at p=3; D_H is used at p>=5.
At every node C selects one complete child and continues into a different
child; D discards two complete children, retains p-3 complete children,
and continues into the one remaining child. At height zero C is empty and
D is the singleton leaf. These rules characterize the entire two orbits:
an automorphism gives such choices, and conversely every such choice is
implemented by a permutation of the node's children and the recursively
chosen automorphism in the continuation child. Permutations in complete
or discarded children may be arbitrary.

Consequently every C_H shape has c_H=(p^H-1)/(p-1) leaves, and every D_H
shape has d_H=((p-3)p^H+2)/(p-1) leaves. These sizes are independent of
the chosen automorphism. They agree with the finite Haar densities above.

Give the actual leaves arbitrary rational costs f. For a node v let W(v)
be the sum of costs on all leaves below it. Write its children as v_j.
Let C(v),D(v) be the minimum sums over the respective orbit shapes rooted
there. At a leaf x, C(x)=0 and D(x)=f(x). At every nonleaf,

    C(v) = min_b [ C(v_b) + min_(a!=b) W(v_a) ],

    D(v) = min_b [ D(v_b) + sum_(j!=b) W(v_j)
                            - max_(a<c; a,c!=b)(W(v_a)+W(v_c)) ].

The orbit characterization proves both directions of these equalities:
each permissible shape has exactly one of these costs, and each minimizing
choice can be realized by a genuine tree automorphism. No independence of
the costs and no positivity assumption is needed. Keep the chosen children
and recursive witnesses to recover an optimal shape. The two smallest and
three largest child totals suffice to evaluate the inner extrema for all b.
Thus the arithmetic work is linear in the finite tree size when these
small extrema are maintained during one scan per node. This is an
arithmetic-operation count, not a bit-complexity or sublinear-input claim.

For a fixed product reference law in all other coordinates, take
f_i(x_i)=sum_(x_-i in selected product) 1_A(x_i,x_-i), where A is the SAME
actual head forbidden union. All other coordinates are uniform on their
selected shapes. The normalization denominator is the fixed product of
all shape sizes. Therefore this recurrence is the exact best response for
coordinate i. The implementation constructs A from the original distinct
numerical moduli and verifies its count by a separate integer CRT scan.
It never optimizes against separately replaced marginal constraints.

For a finite head, cycle through coordinates and accept only strict
improvements. Every accepted move decreases the nonnegative integer
covered-leaf count. Hence the procedure terminates at a coordinatewise
minimum. Its final value is a FEASIBLE upper bound on the global minimum;
coordinatewise optimality is not a global lower-bound certificate.

### 2. An actual trap for strict updates of at most two coordinates

Use the seven original residue classes

    0 mod3, 0 mod5, 0 mod7, 11 mod15,
    16 mod21, 18 mod35, 29 mod105.

Their moduli are odd, greater than one, pairwise distinct, and divide105.
Use height one at3,5,7. Admissible reference supports are one ternary
digit, three of the five digits, and five of the seven digits. There are
3*C(5,2)*C(7,2)=630 complete product shapes.

Consider the uniform law on

    {2} x {2,3,4} x {2,3,4,5,6}.

Only the class18 mod35 meets this product, at the coordinate tuple(2,3,4),
whose actual CRT integer is53. The forbidden mass is1/15. Every change of
AT MOST TWO coordinates has forbidden mass at least1/15. Such a change
keeps at least one coordinate fixed, so the following three cases prove
the assertion.

* Keep the ternary digit2. Any zero-loss candidate must omit quinary0
  because of0 mod5 and quinary1 because of11 mod15, forcing {2,3,4}.
  It must also omit seven-digit0. Of the six remaining seven-digits it
  selects five, but18 mod35 requires omitting4 and29 mod105 requires
  omitting1. Both cannot be omitted, so a hit remains.
* Keep the quinary set {2,3,4}. Ternary0 makes all points forbidden.
  Ternary2 is covered by the preceding case. At ternary1, a zero-loss
  seven-set would have to omit0 by the pure class,2 by16 mod21, and4
  by18 mod35. A five-subset of seven digits cannot omit all three.
* Keep the seven-set {2,3,4,5,6}. Ternary0 makes every point forbidden;
  ternary1 has at least three hits from16 mod21 at seven-digit2. With
  ternary2, zero loss again forces quinary {2,3,4}, retaining the hit
  from18 mod35.

All covered counts are integers, so the absence of a zero-loss move gives
the lower bound1/15. The displayed starting law attains it in each case.
Exhaustive original-label evaluation gives the sharper finite counts:

| Fixed coordinate | Product shapes checked | Minimum covered count | Minimizers |
|---|---:|---:|---:|
| Ternary {2} | 210 | 1 | 2 |
| Quinary {2,3,4} | 63 | 1 | 3 |
| Seven-coordinate {2,3,4,5,6} | 30 | 1 | 1 |

But the reference law on

    {1} x {1,2,4} x {1,3,4,5,6}

has forbidden mass zero: it avoids the pure zero classes, the two classes
whose ternary digit is2, the21-class whose seven-digit is2, and the35-class
whose quinary digit is3. Hence the global minimum is exactly zero.
Thus optimality against every strict update of at most two coordinates
does not certify joint optimality on actual legal congruence families.
Tied moves can escape: changing the ternary and seven-coordinates to

    {1} x {2,3,4} x {1,3,4,5,6}

keeps covered count one, now at the actual integer88. Changing only the
quinary set to {1,2,4} then reaches the zero-loss law above. The example
does not obstruct algorithms that permit this tied move. It is neither a
covering counterexample nor a refutation of the9/20 reference-law wish;
both1/15 and0 are below9/20.

With deterministic coordinate order3,5,7 and strict-only updates, the
canonical reference law starts at covered count4 and terminates at this
one-hit coordinatewise minimum. The exhaustive630-shape comparison
independently supplies the unique zero-hit global witness.

### 3. The existing unrestricted-tail consumer transports to this orbit

Use exactly the preceding finite head and height conditions: head primes
are odd and at most73, with3 padded, and H_p resolves every exponent in
the ENTIRE original family, including later cofactors. Choose any product
g of rooted coordinate-tree automorphisms, and use g_*nu_b as reference.
If its actual head forbidden mass is at most9/20, the original family
does not cover, with completely unrestricted tail primes above73.

To prove this, take the CRT bijection g^-1 on the full finite period,
extended by identity on the tail coordinates. Each original class modulo
d is carried to exactly one residue class modulo the SAME d, since each
head prime-power cylinder is mapped to one cylinder of the same depth.
Numerical distinctness, all heights, all supports, and covering status are
preserved. The inverse image of the actual head union has nu_b-mass equal
to the original union's g_*nu_b-mass. Apply the existing common9/20
criterion to this one transformed family and transport a surviving point
back. The transformed residues are all obtained from this ONE bijection;
no separately optimized prefix law or artificial projected-label
distinctness is introduced. The continuation criterion imposes no residue restriction on
tail classes, so their transformed residues remain in its scope.

Equivalently, same-depth cylinder caps and Haar densities are unchanged
by g. The pure-survivor capped tail kernels and the common-source moment
proof then have the same initial comparison constants. This transport is
a reuse of the existing consumer, not a new continuation constant.

The recurrence supplies an exact finite search primitive for a given
head. The 78-label counterexample below also rules out a universal
qualifying g: every product tree-orbit law obeys the numerical-order
full-prefix caps, so the proved lower bound for that larger class applies
to all such products. A failed coordinate descent alone remains
insufficient to certify this obstruction.

### 4. Relation to the5040 optimization

The existing frozen theorem [golden_resource_unique_optimum](../../../../D5/S3/Arith/GoldenResourceOptimalInteger.lean) uses the separable objective

    log(sigma(n)/n) - (1/25)log n
      = sum_p [ log(sum_(e=0..a_p)p^-e) - a_p log(p)/25 ].

Strict marginal-price crossings independently determine exponents
(4,2,1,1) at2,3,5,7. Separability allows coordinate optimality to certify
the whole integer optimum. The actual head-loss objective above is
multilinear in the coordinate laws and contains genuine cross-coordinate
congruence events. The explicit seven-label example disproves that same
local-to-global inference for this layout problem. Marginal optimization
remains useful as an algorithmic step, but a global certificate requires
additional interaction control. This is a precise comparison of the
objectives, not a claimed reduction of odd covering to Robin's criterion.

### Exact finite checks

The exact program compares its tree recurrence with independent orbit
enumeration on C(3,2), C(3,3), D(5,1), D(5,2), D(7,2): respectively
18,108,10,300,2205 shapes and512,80,32,80,24 score tables. The two smallest
cases cover every binary leaf-cost table; the other tables include signed
integer costs. Its actual example uses all630 product shapes and original
integer congruence predicates.

The [reference_tree_optimizer.py](../frontier/source-budgets/reference_tree_optimizer.py)
program retains the exact response routine and witness recovery, independent
small-orbit enumeration, genuine original congruence tensor construction,
coordinate descent and a reproducible search for coordinate traps. These
functions form a usable finite research tool. Its canonical regression
output retains the proved orbit sizes, exact comparisons, original labels
and both local/global witnesses.
The [complete exact output](../certificates/source_norms/source-budgets/reference_tree_optimizer.json)
is reproduced from the repository root by

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/reference_tree_optimizer.py --check
```

## Continued in 04c

[Chapter 04c](04c-full-history-capped-laws-and-exact-global-optimization.md) gives full-history capped laws, exact global optimization, and the complete counterexamples to the universal 9/20 threshold.
