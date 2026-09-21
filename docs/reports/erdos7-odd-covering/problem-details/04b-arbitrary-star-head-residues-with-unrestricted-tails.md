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

## Full-history capped laws and exact global optimization

Retain a finite family of pairwise distinct odd numerical moduli greater
than one, with arbitrary original residues. Let P be the odd primes at
most73 occurring anywhere in the family, with3 added if absent. For each
p choose H_p>=1 resolving its exponent in the ENTIRE family, including
later-ending cofactors. Set N_p=p^H_p and

    k_3=(3^H_3-1)/2,
    k_p=((p-3)p^H_p+2)/(p-1) for p>=5.

These are positive integers at most N_p. Write A_H for the union of the
actual original classes supported wholly on P, as a subset of the full
CRT head product. No original label is discarded or replaced by its
radical. The statements below are ordinary mathematics and exact finite
algorithms; they assert no new Lean result or solution of unrestricted#7.

Three data must be distinguished. The arithmetic input fixes one residue
for each original numerical modulus, hence one actual CRT forbidden set.
The strategy knows that whole input in advance and may read every already
sampled coordinate when choosing its next conditional row. The prescribed
coordinate order determines which coordinates form that available prefix.
It changes the cap-constrained strategy class; it neither changes the
original congruences nor asserts a physical causal order among them.
Residues cannot be selected anew in different branches of the strategy.

### 1. A correlated head has the same unrestricted-tail consumer

Fix any permutation sigma of P before generating the law. Admit every
head joint law mu satisfying

    mu(X_p=a | full preceding coordinates) <= 1/k_p

for every leaf a at every positive-probability prefix IN THAT ORDER. On zero-probability
prefixes choose a uniform row; this obeys the same cap since k_p<=N_p.
Equivalently the source is built by normalized full-history kernels with
these pointwise bounds. Marginal bounds alone are not the assumption.

If mu(A_H)<=9/20, Chapter04b's same-law continuation proves noncoverage
for the entire original family, including arbitrary tail primes above73.
The initial coordinates need not be independent or related by one product
of rooted-tree automorphisms.

For a depth-e cylinder there are exactly p^(H_p-e) leaves. Its conditional
probability is therefore at most

    p^(H_p-e)/k_p = p^-e/s_p,     s_p=k_p/N_p.

These are exactly Chapter04b's finite reference caps. In particular the
ternary cap is 2*3^-e/(1-3^-H_3); replacing it directly by2*3^-e would be
invalid. For p>=5, s_p>=(p-3)/(p-1), so the old height-independent cap
(p-1)p^-e/(p-3) is valid.

Apply [Schroeder's published conditional convex comparison](../../../../Library/Arith/schroeder2026noncoverage.md) to the actual
original-label rectangles. It assumes deterministic caps conditional on
the entire earlier history, and does not assume independent actual
coordinates. The retained [Comparison.lean source](../../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean) expresses this with
`KernelChain`, `HasCaps`, and `convex_load_comparison`. Its Lean finite-law
signature is rational; arbitrary real laws here use the published ordinary
proposition, not an unclaimed change to that signature.

Only the auxiliary comparison coordinates are independent. After this
replacement, the same finite ternary auxiliary height is dominated in
increasing-convex order by the infinite auxiliary law with tail2*3^-e,
using Chapter04's US3. Its weighted-increment proof uses no independence
of the initial physical coordinates. The other auxiliary heights are
bounded by the same geometric tails as before.

After this entire head, append the identical actual normalized tail
kernels in increasing numerical order for primes above 73. They preserve the
entire old marginal, hence keep the actual head loss epsilon=mu(A_H)
unchanged. Complete original exponent tuples before using the positive
part and second-moment estimates; repeated projected cofactors remain
permitted. Before each tail prime q, the set of processed coordinates is
the full head together with the smaller tail primes, regardless of sigma.
The comparison theorem uses arbitrary ordered coordinate indices, so it
applies in the actual order sigma followed by the tail prefix. Its
independent auxiliary coordinates can then be permuted back to numerical
order: the completed products of factors 1+K_p and their distributions
are unchanged. The finite ternary convex-order argument applies at any
position after conditioning on all the other independent factors.
Thus the existing exact bounds at B=16384 remain

    C_B <= 55386439412229727/125000000000000000,
    J_B <= 4344363876475156387651/500000000000000000.

The existing directed-rounding calculation stays in its original
numerical order. It bounds this same independent auxiliary product
distribution. No assertion that rounded recurrences commute is needed.

The same physical source has common survivor mass at least1-epsilon-C_B.
Condition once on that actual survivor event. Since every complete layout
contains the unit divisor and its squared load is at least one, the
supported law has, simultaneously for every layout,

    Gamma <= 1+(J_B-1)/(1-epsilon-C_B).

At epsilon<=9/20, Chapter04b's unchanged strict BBMST stopping comparison
applies, and its unrestricted continuation handles all remaining primes.
This reuses the established numerical certificate; it is a broader class
of admissible head sources, not a new tail constant.

### 2. Backward averaging is the global optimum over all such laws

For a fixed actual head union, assign terminal cost1_A_H to every full
word. At a prefix immediately before coordinate p, let its N_p child
continuation values be v_1,...,v_N, ordered increasingly. Define

    V(prefix) = (v_1+...+v_k)/k,     k=k_p.

This is the exact row optimum over ALL real probability vectors
0<=a_i<=1/k, sum_i a_i=1. Indeed,

    sum_i a_i v_i - (sum_(i<=k) v_i)/k
      = sum_(i<=k)(a_i-1/k)(v_i-v_k)
          + sum_(i>k)a_i(v_i-v_k) >= 0.

The displayed terms are nonnegative, and a uniform choice of k cheapest
children attains equality. No discrete restriction on the competing row
probabilities was assumed. Backward induction first bounds every future
policy from below by its child values, then uses this row bound; selecting
the minimizing rows gives equality throughout. Consequently

    V(empty) = min_mu mu(A_H),

where mu ranges over the entire full-history capped class just defined.
In particular the minimum is attained by a rational law. At every reached
prefix it selects k_p children uniformly. Every reached full word then
has probability1/K, where K=product_p k_p, and exactly K words are reached.
The selected children may depend on the actual entire prefix. This law
generally has correlations.

All values can be computed with integers. Put K_i=product_(j>=i) k_j.
At a terminal word the numerator is0 or1. A parent sums the k_i smallest
child numerators and uses denominator K_i. Thus the integer optimum M
has V(empty)=M/K and its continuation test is exactly20M<=9K.

This is the finite backward-induction/linear-allocation principle applied
to the actual arithmetic head. A failed product-coordinate descent is not
its lower-bound certificate; the entire Bellman optimum is required.

### 3. Original-label signatures give an exact compressed computation

At layer i retain the IDs of all original head labels whose requirements
on earlier coordinates still match. A failed label can never become true
again. Each surviving label keeps its original future exponents and
residues. Therefore two prefixes with the same layer and surviving IDs
have exactly the same remaining forbidden union. Their future row-cap
constraints also agree because k_p depends only on the layer. They have
the same continuation problem and the same Bellman value. This proves
the state reduction; original labels with equal partial projections are
not identified with one another.

On the current coordinate, split all N_p=p^H_p leaves by their exact set
of matching current label requirements. These requirements are genuine
p-adic cylinders. A trie of their least-significant digit words supplies
the partition. At depth d, matching labels ending at that node are
retained for every descendant. Only children queried by deeper cylinders
need expansion. Each unqueried child has the current signature on exactly
p^(H_p-d-1) leaves; if no deeper query remains, the whole node contributes
p^(H_p-d) leaves. Sum multiplicities for equal signatures.

This partition includes every original exponent and every current leaf.
Its multiplicities sum to N_p. A group of size m contributes m copies of
its child continuation value to the row optimization. Sort groups by that
value and take their multiplicities until exactly k_p children have been
selected. A partial take from a tied-signature group is valid because any
chosen leaves in it have the same future original-label requirements.
The selected subsets need not themselves be p-adic cylinders.

Memoizing by (layer, surviving original IDs) implements the exact Bellman
recurrence without materializing the full CRT period. The number of states
may still grow exponentially in the original label count; no polynomial
bound in the bit length of the arithmetic input is asserted. Large
unqueried heights change the exact cardinalities and multiplicities even
when they add no new signature state. Compression does not truncate those
heights or grant permission to ignore old exponents appearing in the tail.

### 4. A genuine original head separates all three law classes

Use the seven original residue classes

    0 mod 3, 1 mod 9, 4 mod 27, 0 mod 7,
    1 mod 21, 2 mod 63, 59 mod 189.

Their numerical moduli are odd, greater than one, pairwise distinct, and
have least common multiple 189. The full head has coordinates Z/27 and
Z/7, in numerical prime order, with k_3=13 and k_7=5. The exact minima
of its actual forbidden mass are

| Admissible head law | Minimum forbidden mass |
|---|---:|
| Product of ternary C_(3,3) tree-orbit law and a uniform five-subset at 7 | 4/65 |
| Any independent product with leaf caps 1/13 and 1/5 | 3/65 |
| Any full-prefix conditional-cap law | 0 |

These values concern the same original classes and the same full heights.
They show both that the tree-orbit restriction can cost mass and that
correlation can strictly improve on every independent capped product.

The pure ternary classes leave exactly the 14 rows

    S={2,5,7,8,11,13,14,16,17,20,22,23,25,26}.

On these rows the pure seven-class forbids column 0. The additional
mixed conditions have the following disjoint row groups, obtained by
reducing each ORIGINAL residue modulo 27 or its required ternary power
and modulo 7:

| Original class | Surviving ternary rows | Additional forbidden column |
|---|---|---:|
| 1 mod 21 | 7,13,16,22,25 | 1 |
| 2 mod 63 | 2,11,20 | 2 |
| 59 mod 189 | 5 | 3 |

For a correlated law, choose any 13 rows of S uniformly. Each such row
forbids column 0 and at most one additional column, so it has at least
five good columns. Choose five of them uniformly, conditional on that
actual row. The joint law is uniform on 65 original CRT integers, obeys
both full-prefix caps, and avoids all seven original classes. Its loss
is zero, which proves the correlated global minimum.

For independent product laws, optimization over arbitrary real
probabilities reduces to uniform subsets without a discrete assumption.
The objective is bilinear in the two marginals on compact capped
simplices, so it has a global minimum. Fix its second marginal and use
the row inequality from Section 2 to replace the first by a uniform
13-subset without increasing the objective. Then fix that first marginal
and replace the second by a uniform five-subset the same way. The result
still attains the global minimum. Thus the 21 possible five-subsets of
columns, with the 13 cheapest of ALL 27 rows for each, suffice.

A column subset containing 0 incurs at least 13 forbidden points. A
subset excluding 0 omits exactly one of columns 1,...,6. All 13 rows
outside S then have cost five, and each row in S has cost zero or one,
so the best 13-row choice lies in S. Omitting columns 1, 2, 3, or one
of 4,5,6 leaves respectively 4, 6, 8, or 9 bad rows in S. A 13-subset
of S can discard only one row. The resulting minima are 3, 5, 7, and 8
forbidden points. Hence the exact independent-product minimum is 3/65,
attained by columns {2,3,4,5,6} and, for example, rows S minus {20}.

Finally restrict the ternary support to a C_(3,3) tree shape. Any shape
containing a pure-ternary forbidden row incurs at least five forbidden
points under every five-column choice. For a shape with no such row,
its full root child of nine leaves must be residue 2 modulo 3: residue 0
is wholly forbidden, while residue 1 includes rows forbidden by 1 mod 9
and 4 mod 27. The recursive four-leaf child lies in residue 1. Within
it, the full second-level child must be {7,16,25}, and the final leaf
must be 13 or 22. Consequently the only two zero-pure-loss shapes are

    {2,5,8,11,14,17,20,23,26} union {7,13,16,25},
    {2,5,8,11,14,17,20,23,26} union {7,16,22,25}.

Each has column bad-count vector (13,4,3,1,0,0,0). The sum of its five
smallest entries is four, attained at columns {2,3,4,5,6}. The four bad
original integers are 2,59,65,128. This proves the tree-orbit minimum
4/65 and the strict separation displayed above.

The exact producer checks all 21 column subsets and all 27 actual row
costs, all 108*21 tree-orbit products, and the actual CRT support of a
zero-loss correlated policy. All three minima are below 9/20. The example
does not refute the universal head-selection wish and does not claim a
new two-prime noncoverage theorem.

### 5. The head order can be selected before sampling

For each prescribed head order sigma, the preceding recursion computes
the global optimum V_sigma over that order's full-prefix capped laws.
The same unrestricted-tail consumer applies to every such fixed order.
One may therefore compare candidate orders or minimize V_sigma over all
fixed permutations. A single run certifies its specified order; a global
claim across orders needs all of them or a further valid reduction. No
efficient bound for that additional optimization is asserted.

Order changes the admissible-law class even for the original period-189
example. In the order 3 then 7 the exact optimum is zero as proved above.
In the order 7 then 3, first fix column b=0,...,6. Averaging its 13 cheapest
ternary terminal costs gives, respectively,

    (1, 4/13, 2/13, 0, 0, 0, 0).

Indeed, column 0 forbids all 27 ternary rows. Columns 1 and 2 leave only
9 and 11 good rows, while each other column leaves at least 13 good rows.
The initial seven-coordinate cap then averages the five smallest of the
displayed child values, yielding exactly 2/65. The real-row inequality
proves the lower bound, and uniform choices of the indicated five columns
and their 13 cheapest ternary rows attain it. The checker independently
constructs this full-period CRT policy and verifies both conditional caps.

A fixed joint law's mass of the actual union does not change when its
coordinates are renamed or displayed in another order. The values 0 and
2/65 differ because the full-prefix caps in the two orders describe
different feasible laws. Both optima are below 9/20. This argument allows
a prime permutation fixed before sampling; selecting the next prime
adaptively from already sampled values is outside its scope. Tail primes
above 73 retain their numerical processing order.

### 6. An explicit original head refutes the numerical-order universal bound

The claim that every original head admits bad mass at most 9/20 under
these caps in numerical prime order is false. Consider the following
complete fixed family; each entry m:a denotes the original class a mod m.

```text
3:0      5:0      7:2      9:4      11:7     13:2
15:14    17:6     19:1     21:14    25:21    27:10
33:20    35:27    39:22    45:43    49:43    51:35
55:11    57:5     63:7     65:33    75:53    77:67
81:46    85:36    91:12    95:76    99:70    105:17
117:7    119:39   121:41   125:26   133:68   135:109
143:47   147:68   153:97   165:143  169:135  171:25
175:66   187:50   189:28   195:143  209:93   221:123
225:79   231:32   243:100  245:197  247:127  255:8
273:173  275:206  285:158  289:251  297:181  315:52
323:150  325:206  343:78   351:154  357:26   361:170
363:323  375:308  385:277  399:257  405:154  425:368
429:245  441:232  455:318  459:190  475:161  495:394
```

These are 78 pairwise distinct odd numerical moduli greater than one,
exactly the odd 19-smooth integers between 3 and 500. Their actual prime,
height, carrier-size, and cap-cardinality vectors are

    P = (3,5,7,11,13,17,19),
    H = (5,3,3,2,2,2,2),
    N = (243,125,343,121,169,289,361),
    k = (121,63,229,97,141,253,321).

Each highest prime power in N is itself an original modulus. Thus H
records the full original exponents; it is not artificial height padding.
Every original residue in the table is fixed globally before any sampling.
Let A be this actual forbidden union and let mu range over ALL real joint
laws whose full-prefix leaf probabilities, in the order P displayed above,
are at most 1/k_p. The exact optimum is

    Q = product_p N_p = 22227341715203625,
    K = product_p k_p = 1938999971129067,
    min_mu mu(A) = 875843233809638 / 1938999971129067.

Writing b=875843233809638, the decisive strict comparison is

    20b - 9K = 65864936031157 > 0.

This is the global optimum over the specified conditional-cap class, not
the result of coordinate descent. It follows from the capped-row theorem
and two exact finite evaluations of the original input. The compressed
Bellman routine minimizes bad mass. A separate routine uses no trie:
for every actual leaf in each coordinate it tests each original label
modulo gcd(m,p^H), retaining only the IDs still matching the revealed
prefix. A label already completed makes survival zero; if no label
remains, every future tuple survives. Otherwise it computes the largest
possible survivor numerator by summing the k_p LARGEST child numerators.
Every child has the same remaining denominator. The capped-row inequality
with signs reversed proves this survival recurrence over all real rows,
and uniform choices of the maximizing children attain it.

The two evaluations agree on

    maximum_survivor_numerator = 1063156737319429 = K-b.

The independent leaf recurrence uses 2,481 states and 237,164 explicit
coordinate-leaf evaluations. On the same original-label states, summing
ALL N_p child counts, instead of selecting k_p, counts every actual CRT
survivor exactly once. It gives

    |R| = 1157800229415935.

Direct original-label membership also verifies that the integer 19 is
uncovered. Consequently the input is not a covering system. What fails
is the stronger requirement that the fixed conditional-cap class put
at least 55 percent of its mass on actual survivors. Appending unused
head primes after 19 in numerical order cannot repair this marginal
optimization: future normalized rows preserve the original head law.

The result does not settle other fixed prime orders for this input or
refute the existential choice of an order for every head. Its survivor
count even passes the order-independent necessary counting condition:

    20|R| - 11K = 1827004905898963 > 0.

Thus cardinality alone does not explain this example's numerical-order
obstruction; the full-prefix constraints carry additional restrictions.
The same-law conditional continuation and the exact Bellman algorithm
remain valid. Their numerical-order universal success premise is refuted.

### 7. A complete survivor-count obstruction defeats every fixed order

A second actual family refutes the weaker claim that choosing a suitable
fixed order always restores bad mass at most 9/20. It even defeats the
larger class of ALL joint laws having atom mass at most 1/K, without any
sequential-kernel restriction. The complete original input is:

```text
3:0       5:0       7:2       9:4       11:7      13:2
15:14     17:6      19:1      21:14     23:6      25:21
27:10     29:17     31:23     33:20     35:27     37:20
39:22     41:20     43:17     45:43     47:12     49:43
51:35     53:25     55:11     57:5      59:20     61:60
63:7      65:33     67:19     69:35     71:10     73:37
75:53     77:67     81:46     85:17     87:50     91:12
93:8      95:76     99:70     105:17    111:8     115:21
117:1     119:39    121:41    123:59    125:26    129:118
133:68    135:109   141:14    143:47    145:142   147:68
153:97    155:78    159:35    161:36    165:143   169:135
171:25    175:66    177:59    183:55    185:111   187:50
189:28    195:143   201:155   203:15    205:32    207:43
209:90    213:187   215:91    217:207   219:215   221:123
225:79    231:32    235:132   243:100   245:197   247:127
253:201   255:8     259:138   261:124   265:6     273:173
275:206   279:25    285:158   287:200   289:251   295:183
297:181   299:70    301:11    305:196   315:52    319:303
323:150   325:206   329:57    333:250   335:277   341:170
343:78    345:41    351:154   355:117   357:26    361:170
363:2     365:3     369:367   371:64    375:308   377:354
385:277   387:352   391:333   399:257   403:188   405:154
407:104   413:284   423:7     425:368   427:166   429:245
435:161   437:45    441:232   451:258   455:318   459:190
465:398   469:243   473:96    475:161   477:226   481:235
483:53    493:126   495:394   497:197
```

These are 154 distinct odd numerical moduli greater than one, exactly
all odd 73-smooth integers from 3 through 500. Their largest modulus is
497. The family is its own literal input: for example, its residues at
85,117,209,363 are 17,1,90,2. It must not be reconstructed by simply
appending labels to the preceding 78-label input.

The prime vector consists of the 20 odd primes from 3 through 73, and
its actual full-height vector is

    H=(5,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1).

The first seven prime coordinates are 3,5,7,11,13,17,19; the remaining
ones are 23,29,31,37,41,43,47,53,59,61,67,71,73. Every highest prime
power is present as an original modulus. Exact original-label counting
and the same cap-cardinality formulas give

    Q = 93334171363271157468761359267761115875,
    K =  4385364744027208669814574741078700875,
    |R|= 2254630674715456873605308528779445940.

Here R is the actual set of uncovered CRT residues modulo Q. The
survivor count is obtained by the independent full-leaf recurrence from
Section 6, summing all child counts in all 20 coordinates. Each state
continues to retain the original label IDs and complete exponents.

For ANY probability law mu on these Q actual residues satisfying
mu({x})<=1/K at every point, summing over R gives

    mu(R) <= |R|/K,
    mu(A) >= 1-|R|/K.

The strict integer gap is

    11K-20|R| = 3146398689990157895854151576276790825 > 0.

Therefore every such law has bad mass strictly greater than 9/20. More
explicitly its bad mass is at least

    15783215328235198490439008979994481
    /32484183289090434591219072156138525.

This bound applies simultaneously to every fixed-order full-prefix
capped law. For any full word of positive mass, the chain rule multiplies
its conditional leaf probabilities, each at most 1/k_p, giving atom mass
at most product_p(1/k_p)=1/K. Zero-mass words satisfy the bound as well.
The product K is independent of the chosen permutation. Thus no choice
of fixed order, no additional dependence among coordinates, and no other
law construction that retains this same atom cap can meet the proposed
55 percent survival target on this family. This is a statement about a
probability constraint on one fixed arithmetic set, not a physical causal
claim or a permission to choose different original residues by branch.

The exact numerical-order Bellman calculation is stronger:

    minimum_bad_numerator = 2412632030500994251235961799423987575,
    minimum_bad_mass = minimum_bad_numerator/K.

The trie minimum and the independent full-leaf maximum agree on this
value. The latter calculation uses 45,029 states and 3,363,080 explicit
coordinate-leaf evaluations and also returns the stated survivor count.
The universal-order obstruction needs only the cardinality inequality,
not a separate DP run for every permutation.

Finally, direct evaluation shows that 34 is uncovered by all 154 original
classes. This family is not a cover. It refutes the universal fixed-cap
head-selection premise, including its order-optimized variant, while
leaving the conditional continuation criterion and the exact optimizer
valid for inputs on which their sufficient threshold is met.

### 8. Verification scope and the remaining mathematical target

The implementation compares the compressed optimum with an independent
full-period CRT construction and uncompressed backward recursion on24
actual two- and three-prime families. It also checks each queried signature
partition against all current leaves. The constructed finite optimal law
has exactly k_p equally weighted children at every reached full prefix;
its actual original-label union mass agrees with the computed optimum.
Two fixtures have positive optimal costs1/20 and2/65, so the checks include
heads that cannot be completely avoided at the prescribed caps.
The additional period-189 check in the reversed fixed order has exact
cost2/65 and checks all current leaves against their original CRT classes.

For the seven-label coordinate-trap example from the preceding reference
optimization result, complete height padding to H=2,3,8,20 in all three
coordinates leaves the exact optimum zero and uses17 signature states.
The H=20 ambient period is105^20, while the least common multiple of those
original labels remains105. A separate fixture adds actual classes of
moduli 3^20,5^20,7^20; its original period is105^20, its exact optimum is
zero, and it uses22 signature states. These are exact finite tests, not
a proof of the same value at all untested heights or for arbitrary labels.

The [exact Bellman program](../frontier/source-budgets/capped_head_bellman.py)
retains the compressed optimizer, full-period CRT checks, exact signatures,
finite policy witnesses, the three-class comparison, both complete literal
counterexamples, and their independent local-leaf survival and cardinality
checks. All original labels are literal input to the producer. Its
[complete exact output](../certificates/source_norms/source-budgets/capped_head_bellman.json)
is reproduced from the repository root by

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/capped_head_bellman.py --check
```

Both proposed universal statements are now refuted: numerical order by
the 78-label family, and existence of a qualifying fixed order by the
154-label family. The latter obstruction already holds in the larger
class of all joint laws with the same atom bound. Better optimization or
more available information cannot alter that counting inequality while
the original input and the atom cap remain fixed.

The conditional theorem has a different quantifier: whenever an actual
admissible law meets the sufficient mass threshold, its same-source tail
continuation is valid. The counterexamples leave that implication intact.
The exact Bellman program likewise continues to compute the right answer;
its answers need not always satisfy the desired threshold.

Within this route, a universal replacement would need to change the
head-law constraints or the survival-versus-moment budget. Enlarging caps
changes the auxiliary distributions and therefore requires new justified
tail-charge and moment bounds; the old C_B and J_B cannot simply be kept.
No universal replacement is established here. Ordinary arithmetic
noncoverage is weaker than a fixed quantitative survival target, as the
explicit uncovered integers 19 and 34 demonstrate.
