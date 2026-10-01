# Uniform shared-deficit credits lower the depth-two prime-tail cutoff to1300

Let C be a finite family of pairwise-distinct odd numerical moduli greater
than one, with one globally fixed residue for each modulus. Let R be ALL
actual support primes at most1300, and assume |R|<=8. Suppose only that each
original whose complete support lies in R has v3(m)<=2. Then C is
noncovering. A constructed distorted survivor measure has mass greater
than1/3000.

Every original touching a prime above1300 may have arbitrary ternary depth,
arbitrary other finite exponents and arbitrary mixed support. There is no
bound on the finite number of tail primes. The mass1/3000 is not the Haar
density of the final survivor. These are ordinary mathematical arguments
and complete finite exact comparisons, not new Lean verification.

The source is the actual five-leaf construction of
[Report789](789-eight-small-primes-local-ternary-depth-two-and-complete-tail.md).
Its old cutoff was2000. The improvement here is uniform: shared first-order
deficits strengthen every star profile, and an exact cancellation preserves
separate concavity for one fixed weight law. This supplies a complete
vertex reduction instead of extrapolating a favorable individual profile.

## 1. The actual source and its signed support response

Use the benchmark head

    P=(3,5,7,11,13,17,19,23),        Q=P minus{3}.

Report789 first avoids the actual pure3 and9 originals, with an extra
source-only exclusion at an unused label or leaf if needed. It retains five
actual nine-leaves, with root groups A={0,1} and B={2,3,4}, and fixes

    w=(33,33,28,28,28)/150.                             (U1)

The ternary digits above depth two are Haar. Each nonternary coordinate q
starts with its actual pure-power survivor probability lambdaq, with cap
Cq q^-e, where Cq=(q-1)/(q-2). Put bq=1/(q-2).

Complete the cap budgets for the distinct3q^e and9q^e star inventories,
once for the actual family, to root and leaf probability vectors u_q,v_q.
For leaf l the exact retained coordinate mass is

    m_ql=1-bq[u_q,group(l)+v_ql]>=1-2bq>0.               (U2)

The actual star-survivor restriction is downscaled to this exact mass,
remaining dominated by lambdaq. This is a genuine supported submeasure;
completing a cap budget does not add an original or change a phase.
Let

    g_l(U)=product_(q outside U)m_ql,       b_U=product_(q in U)bq,
    S0=sum_l w_l g_l(empty).

For a nonternary support D of size at least two, the complete distinct
inventories d,3d,9d have cap budget b_D each. Their shared root/leaf
allocation is theta_D=(x_D,y_D), with x_D and y_D probability vectors on
the two roots and five leaves respectively. Write

    c_Dl(theta_D)=1+x_D,group(l)+y_Dl.

The first, pair and triple terms in the weighted signed support response
are

    A_D(theta_D)=b_D sum_l w_l g_l(D)c_Dl,

    P_DE(theta_D,theta_E)
       =b_(D union E) sum_l w_l g_l(D union E)c_Dl c_El,

    T_DEF(theta_D,theta_E,theta_F)
       =b_(D union E union F)
          sum_l w_l g_l(D union E union F)c_Dl c_El c_Fl. (U3)

Pairs and triples here always consist of pairwise-disjoint supports.
There are no four disjoint mixed supports on the seven coordinates Q.
The one-clique Shearer argument in Report789 applies over the entire
completed cap domain. Consequently the same actual source, restricted to
avoid all remaining original classes, has mass at least

    S0-sum_D A_D+sum_{D,E} P_DE-sum_{D,E,F} T_DEF.       (U4)

The original shared theta_D appears in every term involving D. It is not
selected afresh for a different pair. The arguments below lower-bound this
one expression on its one physical source.

## 2. First-order deficits can be shared among all adjacent pairs

Let H be the set of120 supports D subset Q with |D|>=2. Connect D and E
when they are disjoint. There are546 unordered edges. The degree d_D is
26,11,4,1,0,0 for support sizes2,3,4,5,6,7 respectively.

At fixed star parameters let

    Abar_D=max_theta A_D,
    Punder_DE=min_thetaD,thetaE P_DE,
    Tbar_DEF=max_thetaD,thetaE,thetaF T_DEF.

The old response from Report789 is exactly

    G=S0-sum_D Abar_D+sum_edges Punder_DE-sum_triples Tbar_DEF. (U5)

Each actual first-order deficit Delta_D=Abar_D-A_D is nonnegative.
For an edge D,E define

    Gamma_DE=min_thetaD,thetaE
       [Delta_D/d_D+Delta_E/d_E+P_DE-Punder_DE].          (U6)

Every summand inside the minimum is nonnegative. A positive-degree
support contributes Delta_D/d_D to each of its d_D edges, for total
Delta_D. The eight zero-degree supports contribute no credit. Comparing
(U4) and(U5), and using the ordinary worst upper bound for each subtracted
triple, proves

    mass(actual survivor)>=Gpair:=G+sum_edges Gamma_DE. (U7)

This is the same deficit-allocation principle as the
[individual-profile pair credit](790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md).
Its budgets are never overspent: the same Delta_D is divided
among incident pairs, rather than reused in full at every pair.
Independent pair minima need not be jointly attained. For the actual
common theta, each edge expression is at least its own minimum, which is
all that(U7) uses. Zero-degree deficits are merely discarded, not assigned
to nonexistent edges.

Every expression minimized in(U6) is affine in each support's joint
root/leaf pair when the other support is fixed. Its minimum occurs among
the10^2 role choices

    c_l(r,t)=1+1_(group(l)=r)+1_(l=t),
    r in{A,B},       t in{0,...,4}.                     (U8)

Thus each Gamma has an exact finite evaluation without relaxing the two
shared allocations within that pair.

## 3. Exact cancellation makes the strengthened response concave

A positive correction alone would not establish the vertex reduction.
The relevant identity is the cancellation of the first-order maxima:

    Gpair
      =S0-sum_(D:d_D=0) Abar_D
        +sum_edges min_thetaD,thetaE
           [P_DE-A_D/d_D-A_E/d_E]
        -sum_triples Tbar_DEF.                         (U9)

Indeed,(U6) contributes Abar_D/d_D+Abar_E/d_E-Punder_DE outside its
minimum. The Punder terms cancel those in(U5). Summing over incident
edges cancels Abar_D precisely when d_D>0. This proves(U9) without an
inequality or an assumption of simultaneous extremizers.

Fix all star parameters except the pair(u_q,v_q) at one coordinate q.
Each g_l(U) is affine in this pair: it contains at most the one factor
m_ql, or is independent of it. Therefore, for fixed support role choices,
each bracket in(U9) is affine in(u_q,v_q). Its minimum is concave. Each
negative maximum in the zero-degree and triple terms is also concave,
and S0 is affine. Their sum Gpair is separately concave in every star
coordinate's joint allocation pair.

The leaf weights(U1) and the degree shares1/d_D are FIXED throughout
this argument. Optimizing them independently at each star vertex would
not prove the same reduction. No monotonicity in star budgets or prime
values is asserted.

Repeated concavity on the product of the root and leaf simplices gives

    Gpair(star parameters)
       >=min_(all star vertices) Gpair(vertex),        (U10)

where each q selects one of the ten roles(U8). Thus the full continuous
star domain reduces to10^7 vertices, as in Report789. This is the
additional uniformity argument needed to use the pair credit as a source
theorem for arbitrary old phases and all finite nonternary heights.

## 4. Complete integer comparison with a certified shortcut

Use Report789's S2 x S3 leaf symmetry, preserving(U1). There are7261
canonical leaf words and128 root assignments for each, for929408
canonical profiles covering all10^7 raw vertices. The sum of leaf-orbit
sizes is exactly5^7.

The baseline G has denominator

    D=150 product_(q in Q)(q-2)=1192826250.

All degree shares have denominator dividing

    lcm(26,11,4,1)=572.

Hence the complete refined response is computed with integers over
572D=682296615000. For each pair the program evaluates all100 role pairs;
the first deficits and pair surplus use the same five weighted entries.

Because Gamma_DE>=0, a profile with baseline G>=1/100 automatically has
Gpair>=1/100. A complete scan of the baseline therefore needs explicit
pair evaluation at only683 of the929408 canonical profiles. The other
928725 profiles are certified by that baseline inequality. This is an
exhaustive lower-bound comparison, not a sample of the difficult profiles.

The exact global minimum is

    min Gpair=4431234914/682296615000
             =2215617457/341148307500
             =0.0064945872756528335...=:m_pair.         (U11)

It is less than1/100, so it is attained within the explicitly refined
set and is also the global minimum. A canonical minimizing profile has roles in increasing q order

    ((B,2),(A,0),(A,1),(A,1),(A,1),(A,1),(A,1)).

At that profile the retained baseline and added credit are exactly

    G=1131518/596413125,
    sum_edges Gamma_DE=522796387/113716102500.           (U12)

A second independently written complete integer enumerator obtains the
same683 profiles and global fraction, with undefined-behavior sanitization.
An independent rational evaluation of(U9) at the minimizer agrees with
(U11)--(U12); it does not use leaf-permutation reduction for its pair or
triple role extrema.

The algebraic reduction(U9)--(U10), the source and signed-polynomial
premises, and this complete comparison together prove the uniform source
mass. Finite enumeration is not being used in place of those premises.

## 5. The same fourth envelope now pays the complete1300 tail

The source construction remains dominated by the product used in
Report789. The fixed ternary source has first-root cap14/25, depth-two
leaf cap11/50 and independent Haar higher digits. Its complete fourth
query factor is1423/25. With

    A4(p)=15t+50t^2+60t^3+24t^4,       t=1/(p-1),

the very same unnormalized source has complete mixed four-query bound

    K=(1423/25) product_(p in Q)[1+((p-1)/(p-2))A4(p)]
     =83957323825075240180209923/277054053281280000000.  (U13)

The stronger mass lower bound does not renormalize this measure. All four
queries use its one actual joint source, with arbitrary independent query
phases, including every later ternary cofactor depth. No pointwise
factorization of an arbitrary-phase query count into matching-prefix runs
is used; the fourth envelope follows the ordered-lcm expansion and the
same product domination.

Apply [Report734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md)
with k=4,delta=2/7,r=21,B=1300,ell=6. The coefficient comparison
1+(7/5)A4(p)<=(1+1/(p-1))^21 and its analytic range assumptions hold.
Its stated prime-product estimate gives total tail loss at most K tau,
where

    tau=(21609/10240)(73/71)^21 [1300/1299^4]
          sum_(j=0..21)21!/[(21-j)!18^j].

Exact rational arithmetic gives

    m_pair-K tau=0.000381983877163074...>1/3000.          (U14)

Every tail original is assigned to its greatest tail prime with its
complete earlier cofactor and one fixed phase. The actual live kernels
preserve avoidance. No head projection of a tail original is inserted
as an extra old forbidden class, so the old v3<=2 hypothesis is only
needed for originals wholly on R.

## 6. Actual small primes and missing3

Report789's source transport applies at the new cutoff1300. When3 is
present, pad R to eight distinct odd primes at most1300 using unused
primes. Keep the3 coordinate fixed and use benchmark-to-actual finite
prefix injections at every other coordinate. For each injection choose
its one actual benchmark source after pulling back only head originals;
then push forward and average. The mass lower bound(U11) and the common
fourth envelope(U13) both survive. Complete exponent labels and actual
phase consistency are retained, and sources are fixed before queries.
Dummy coordinates may be removed at the end.

When3 is absent from R, it is absent from the entire original support.
The direct pure-product construction on5,7,11,13,17,19,23,29 gives

    mno3=299974/530145,
    Kno3=7101326389957751920822379861/821055227980138905600000.

At the same cutoff1300,

    mno3-Kno3 tau=0.5656594142819605...>1/3000.           (U15)

Larger nonternary prime values decrease the cap factors, and unused
nonternary padding handles fewer small primes. This branch invokes no
ternary-height hypothesis and no theorem with a different hidden cutoff.

The final positive distorted measure lives on the finite CRT carrier of
the original family. It therefore gives an actual uncovered residue.
The number1/3000 is a bound on that constructed measure, not an assertion
that Haar probability of the uncovered set exceeds1/3000.

## 7. Verification and remaining scope

The [C++ producer](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_pair_source.cpp)
imports Report789's baseline response through a
main-function guard, then adds the new exact pair algorithm and the complete
filtered comparison. Its default invocation checks the raw and canonical
counts, the683 refined profiles and the exact minimum. The guard leaves
Report789's standalone invocation unchanged.

The [retained enumeration](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_pair_source_enumeration.json)
records the complete filtered comparison. The
[Python consumer](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_pair_source.py)
reuses the baseline's shared arithmetic helpers,
evaluates the minimizer by the cancelled affine-pair expression(U9), checks
it against baseline plus credit, and recomputes(U13)--(U15) using rational
arithmetic. It uses explicit exceptions under both normal and optimized
Python. Its default compares a fresh result with the retained JSON;
`--write-result PATH` regenerates the
[exact result](../../../frontier/cover-geometry/refined-capped-source/uniform_depth2_pair_source.json)
after the checks succeed.

```sh
clang++ -std=c++17 -O3 -Wall -Wextra -Werror docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/uniform_depth2_pair_source.cpp -o /tmp/e7_uniform_depth2_pair_source
/tmp/e7_uniform_depth2_pair_source > /tmp/e7_uniform_depth2_pair_source_enumeration.json
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/uniform_depth2_pair_source.py --enumeration /tmp/e7_uniform_depth2_pair_source_enumeration.json
```

These consumers check finite arithmetic, not Lean statements or the
external analytic prime-product input. The two complete enumerations and
the ordinary concavity proof provide the declared uniform finite source
comparison. The unchanged source transport and tail premises are inherited
at their stated scope.

The local ternary-height restriction remains essential to this proved
construction. More than eight actual support primes at most1300, arbitrary
old-head ternary height, and unrestricted Erdős#7 remain outside this
result. No claim of a uniform normalized first-query budget below28 is
made: the gain here strengthens unnormalized mass while retaining the
raw fourth envelope on the same source.
